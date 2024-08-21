import pynusmv
import sys
from pynusmv_lower_interface.nusmv.parser import parser 
from pynusmv.dd import BDD, State, Inputs
from pynusmv.fsm import BddFsm
from functools import reduce
from pynusmv.prop import Prop, Spec
from collections import deque
from typing import List, Tuple, TypedDict, Optional

specTypes = {'LTLSPEC': parser.TOK_LTLSPEC, 'CONTEXT': parser.CONTEXT,
    'IMPLIES': parser.IMPLIES, 'IFF': parser.IFF, 'OR': parser.OR, 'XOR': parser.XOR, 'XNOR': parser.XNOR,
    'AND': parser.AND, 'NOT': parser.NOT, 'ATOM': parser.ATOM, 'NUMBER': parser.NUMBER, 'DOT': parser.DOT,

    'NEXT': parser.OP_NEXT, 'OP_GLOBAL': parser.OP_GLOBAL, 'OP_FUTURE': parser.OP_FUTURE,
    'UNTIL': parser.UNTIL,
    'EQUAL': parser.EQUAL, 'NOTEQUAL': parser.NOTEQUAL, 'LT': parser.LT, 'GT': parser.GT,
    'LE': parser.LE, 'GE': parser.GE, 'TRUE': parser.TRUEEXP, 'FALSE': parser.FALSEEXP
}

basicTypes = {parser.ATOM, parser.NUMBER, parser.TRUEEXP, parser.FALSEEXP, parser.DOT,
              parser.EQUAL, parser.NOTEQUAL, parser.LT, parser.GT, parser.LE, parser.GE}
booleanOp = {parser.AND, parser.OR, parser.XOR, parser.XNOR, parser.IMPLIES, parser.IFF}

SimpleImplication = Tuple[BDD, BDD]
SpecList = List[Spec]
SpecImplication = Tuple[Spec]
SpecImplicationList = List[SpecImplication]
ImplicationList = List[SimpleImplication]
SimpleImplicationList = List[SimpleImplication]
CycleInfo = TypedDict('CycleInfo', {'Tail': [dict], 'Loop': [dict]})
Result = Tuple[bool, Optional[CycleInfo]]

def spec_to_bdd(model, spec) -> BDD:
    """
    Given a formula `spec` with no temporal operators, returns a BDD equivalent to
    the formula, that is, a BDD that contains all the states of `model` that
    satisfy `spec`.
    The `model` is a symbolic representation of the loaded smv program that can be
    obtained with `pynusmv.glob.prop_database().master.bddFsm`.
    """
    bddspec = pynusmv.mc.eval_simple_expression(model, str(spec))
    return bddspec
    
def is_boolean_formula(spec) -> bool:
    """
    Given a formula `spec`, checks if the formula is a boolean combination of base
    formulas with no temporal operators. 
    """
    if spec.type in basicTypes:
        return True
    if spec.type == specTypes['NOT']:
        return is_boolean_formula(spec.car)
    if spec.type in booleanOp:
        return is_boolean_formula(spec.car) and is_boolean_formula(spec.cdr)
    return False
    
def is_GF_formula(spec) -> bool:
    """
    Given a formula `spec` checks if the formula is of the form GF f, where f is a 
    boolean combination of base formulas with no temporal operators.
    Returns True if `spec` is in the correct form, False otherwise 
    """
    # check if formula is of type GF f_i
    if spec.type != specTypes['OP_GLOBAL']:
        return False
    spec = spec.car
    if spec.type != specTypes['OP_FUTURE']:
        return False
    return is_boolean_formula(spec.car)

def parse_implication(spec) -> bool:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a simple 
    reactivity formula, that is wether the formula is of the form
    
                    GF f -> GF g
    
    where f and g are boolean combination of basic formulas.
    """
    # the root of a reactive formula should be of type IMPLIES
    if spec.type != specTypes['IMPLIES']:
        return False
    # Check if lhs and rhs of the implication are GF formulas
    return is_GF_formula(spec.car) and is_GF_formula(spec.cdr)
    
def parse_react(spec) -> bool:
    """
    Visit the syntactic tree of the formula `spec` to check if it is a Reactivity 
    formula, that is wether the formula is of the form
    
        (GF f_1 -> GF g_1) & ... & (GF f_n -> GF g_n)
    
    where f_1, ..., f_n, g_1, ..., g_n are boolean combination of basic formulas.
    
    Returns True if `spec` is a Reactivity formula, False otherwise.
    """
    # the root of a spec should be of type CONTEXT
    if spec.type != specTypes['CONTEXT']:
        return None
    # the right child of a context is the main formula
    spec = spec.cdr
    # check all conjuncts of the main formula
    working = deque()
    working.append(spec)
    while working:
        # next formula to analyse
        head = working.pop()
        if head.type == specTypes['AND']:
            # push conjuncts into the queue
            working.append(head.car)
            working.append(head.cdr)
        else:
            # check if it is a GF f -> GF g formula
            if not parse_implication(head):
                return False
    # if we are here, all conjuncts are of the correct form
    
    return True

def deconstruct_conjuncts(spec: Spec) -> SpecList:

  """
  separates each implication

  """
  
  if spec.type == specTypes['CONTEXT']:

    spec = spec.cdr

  if(spec.type == specTypes['AND']):
    return deconstruct_conjuncts(spec.car) + deconstruct_conjuncts(spec.cdr)
  else:
    return [spec]


def process_implication_spec_list(specList: SpecList) -> ImplicationList:

  return [(spec.car, spec.cdr) for spec in specList]

def strip_temporal(spec: Spec) -> Spec:
  if spec.type != specTypes['OP_GLOBAL'] and spec.type != specTypes['OP_FUTURE']:
        return spec
  return strip_temporal(spec.car)

def strip_temporal_symbols_from_spec_list(spec: SpecImplicationList) -> SpecImplicationList:
  return [(strip_temporal(spec_left), strip_temporal(spec_right)) for (spec_left, spec_right) in spec]

def deconstruct_to_bdd(spec: Spec) -> SimpleImplicationList:
  
  """
  from a possibly composed reactivity formula returns a list of tuples containing
  the base formulae stripped of temporal operators
  """
  if not parse_react(spec):
    return None
  else:

    l = strip_temporal_symbols_from_spec_list(
        process_implication_spec_list(
          deconstruct_conjuncts(spec)
          )
        )
    
    model = pynusmv.glob.prop_database().master.bddFsm
    
    bdd_l = [(spec_to_bdd(model, spec_left), spec_to_bdd(model, spec_right)) for (spec_left, spec_right) in l]

    return bdd_l

def reacheable_states(model) -> BDD:

  reach = model.init

  n = model.init

  empty = pynusmv.dd.BDD.false(model)
  
  while not (n == empty):

    n = model.post(n).diff(reach) # not sure if ops are in place
    reach = reach.union(n)

  return reach

def build_tail(start: BDD, new_list: List[BDD], model: BddFsm) -> List[State | Inputs]:
  
  """
  Please God let me finish This Abhorrence of a script
  So that I may deliver yet another passable assignement in time
  """
  k = -1
  for i in range(len(new_list)):
      if start <= new_list[i]:
          k = i
          break

  tail = []
  curr = start

  for i in range(k-1, -1, -1):
    pred = model.pre(curr) & new_list[i]
    p_curr = model.pick_one_state(pred)
    inputs = model.get_inputs_between_states(p_curr, curr)
    tail = [p_curr, model.pick_one_inputs(inputs)] + tail
    curr = p_curr

  return tail



def build_cycle(start: BDD, new_list: List[BDD], model: BddFsm) -> List[State | Inputs]:
  
  k = 0
  for i in range(len(new_list)):
      if start.entailed(new_list[i]):
          k = i
          break
  
  path = [start]
  curr = start

  for i in range(k-1, -1, -1):
    pred = model.pre(curr) & new_list[i]
    p_curr = model.pick_one_state(pred)
    inputs = model.get_inputs_between_states(p_curr, curr)
    path = [p_curr, model.pick_one_inputs(inputs)] + path
    curr = p_curr

  inputs = model.get_inputs_between_states(start, curr)
  return [start, model.pick_one_inputs(inputs)] + path


def explain_loop(recur: BDD, reach: BDD, model: BddFsm) -> CycleInfo:
  
  start = model.pick_one_state(recur)
  tail_head = model.init
  reachTail = model.init

  new_list = []
  tailList = []

  """
  build the tail trace
  """

  tailList = [tail_head]
  while tail_head.isnot_false():
      tail_head = model.post(tail_head) - reachTail
      tailList = tailList + [tail_head]
      reachTail = reachTail | tail_head


  """
  build the loop trace
  """

  while True:
    
    R = BDD.false(model)

    new = model.post(start) & reach

    new_list.append(new)

    while new.isnot_false():

      R = R.union(new)

      new = model.post(new) & reach

      new = new - R

      new_list.append(new)
    
    R = R & recur

    if start <= R:
      loop = build_cycle(start, new_list, model)
      tail = build_tail(loop[0], tailList, model)
      return {"Tail": [State.get_str_values(x) for x in tail], "Loop": [State.get_str_values(x) for x in loop]}

    else:

      start = model.pick_one_state(R)      

  return ()

def find_circular_path(region : BDD, always_false: BDD, model : BddFsm) -> Result:

  """computing reach"""

  reach = reacheable_states(model)

  recur = reach & region & always_false # filtered states

  while recur.isnot_false():

    pre_reach = BDD.false() # States being expanded from the region

    n = model.pre(recur) & always_false # recur_1

    while n.isnot_false():

      pre_reach = pre_reach | n #expand the reach with the new states
    
      if recur <= pre_reach: # all the region is reacheable
        
        return (True, explain_loop(recur,pre_reach,model))
      
      n = (model.pre(n) & always_false) - pre_reach

    recur = recur & pre_reach # states of recur reacheable from recur

  return (False, None)

def verify_simple_reactivity_formula(implication: SimpleImplication) -> Result:

  model = pynusmv.glob.prop_database().master.bddFsm

  """
  A reactivity formula is simplified in the following way:

  G F y0 -> G F y1
  ! G F y0 || G F y1
  F ! F y0 || G F y1
  F G !y0 || G F y1

  then we check the negation

  ! (F G !y0 || G F y1)
  ! F G !y0 && ! G F y1

  G F y0 && F G !y1

  therefore we check for a cycle starting and ending in the base formula y0 && !y1
  while y1 must ALWAYS be False
  """

  an = find_circular_path(implication[0], implication[1].not_(), model)

  return an

def check_explain_react_spec(spec) -> Result:
    """
    Returns whether the loaded SMV model satisfies or not the reactivity formula
    `spec`, that is, whether all executions of the model satisfies `spec`
    or not. Returns also an explanation for why the model does not satisfy
    `spec`, if it is the case.

    The result is `None` if `spec` is not a reactivity formula, otherwise it is a 
    tuple where the first element is a boolean telling whether `spec` is satisfied, and the second element is either `None` if the first element is `True`, or an execution
    of the SMV model violating `spec` otherwise. 

    The execution is a tuple of alternating states and inputs, starting
    and ending with a state. The execution is looping: the last state should be 
    somewhere else in the sequence. States and inputs are represented by dictionaries
    where keys are state and inputs variable of the loaded SMV model, and values
    are their value.
    """
    if not parse_react(spec):
        return None
    
    verified_negations = [verify_simple_reactivity_formula(imp) for imp in deconstruct_to_bdd(spec)]

    is_respected = [x for x in filter(lambda x: x[0], verified_negations)]


    """
    The negation of a composite formula conjoined by AND is a formula
    conjoined by OR, that is, it suffices for any of the negations to have
    an infinite loop for the negation to be true
    """
    if len(is_respected) > 0:
      return (False, is_respected[0][1])
    else:
      return (True, None)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage:", sys.argv[0], "filename.smv")
        sys.exit(1)

    pynusmv.init.init_nusmv()
    filename = sys.argv[1]
    pynusmv.glob.load_from_file(filename)
    pynusmv.glob.compute_model()
    type_ltl = pynusmv.prop.propTypes['LTL']
    for prop in pynusmv.glob.prop_database():
        print("----------------- new -----------------")
        spec = prop.expr
        print(spec)
        if prop.type != type_ltl:
            print("property is not LTLSPEC, skipping")
            continue
        res = check_explain_react_spec(spec)
        if res == None:
            print('Property is not a Reactivity formula, skipping')
        elif res[0] == True:
            print("Property is respected")
        elif res[0] == False:
            print("Property is not respected")
            print("Counterexample:", res[1])

    pynusmv.init.deinit_nusmv()
