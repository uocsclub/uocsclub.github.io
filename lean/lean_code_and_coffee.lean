-- #eval is used to evaluate something
#eval "Hello, world!"

#eval 2 + 2

-- We can define variables like so:
def world : String := "world"

-- And functions are defined similarly
def greet (name : String) : String :=
  -- We could write:
  -- String.append (String.append "Hello, " name) "!"
  -- but Lean transforms `<string>.append x` into `String.append <string> x`
  -- and this is true for every class
  "Hello, ".append $ name.append "!"
  -- `f $ g x` is `f (g x)`

#eval greet world


-- Every natural number is either zero, or the successor of another natural number
inductive Nat' where
  | zero : Nat'
  | succ : Nat' → Nat'
  -- `succ` is a function which takes a Nat' and returns another Nat'
  -- → can be typed with \r
deriving Repr
-- `deriving Repr` just tells Lean how to display it

def naught  : Nat' := Nat'.zero
def yan     : Nat' := Nat'.succ naught
def tan     : Nat' := Nat'.succ yan
def tethera : Nat' := Nat'.succ tan

#eval tethera

-- This is a bit unwieldy, it would be nice if we could just use Arabic numerals

-- Let's write a function to convert Lean's Nat, which is defined the same way as ours, into our Nat'.
/-
def natToNat' (n : Nat) : Nat' :=
  match n with
  | 0     => Nat'.zero
  | k + 1 => Nat'.succ $ natToNat' k
-/
-- We can write this a bit more succinctly:
def natToNat' : Nat → Nat'
  | 0     => Nat'.zero
  | k + 1 => Nat'.succ $ natToNat' k

-- Tell Lean to translate Arabic numerals into Nat'
instance : OfNat Nat' n where
  ofNat := natToNat' n

#eval (10 : Nat')

-- Now, it would be nice if we could format it nicely
def Nat'.toNat : Nat' → Nat
  | zero    => 0
  | succ n' => 1 + n'.toNat

-- Tell Lean that, when stringifying Nat', first transform it into a Nat, then stringify *that*
instance : ToString Nat' where
  toString n := toString n.toNat

-- We can use s! to format a string, with the things inside {} being evaluated
-- #eval s!"Three is actually {(3 : Nat')}!"
-- if we leave off the `: Nat'`, Lean just assumes we're using a normal Nat.
#eval s!"Three is actually {tethera}!"

-- Addition
/-
def Nat'.plus (n : Nat') (m : Nat') : Nat' :=
  match n with
  -- 0+m = m
  | zero    => m
  -- (1+n')+m = 1+(n'+m)
  | succ n' => (n'.plus m).succ
-/
-- Again, we can condense this:
def Nat'.plus : Nat' → Nat' → Nat'
  | zero,   m => m
  | succ n, m => (n.plus m).succ

#eval s!"Three plus three is {tethera.plus tethera}"

-- Tell Lean to interpret Nat' + Nat' as Nat'.plus
instance : Add Nat' where
  add := Nat'.plus

#eval s!"Three plus three is {tethera + tethera}"

-- Multiplication
def Nat'.mul : Nat' → Nat' → Nat'
  -- 0 * anything = 0
  | zero,    _ => Nat'.zero
  -- (1+n') * m = m + n'*m
  | succ n, m => m + n.mul m

instance : Mul Nat' where
  mul := Nat'.mul

#eval s!"Three times three is {tethera * tethera}"

-- What about division? Now this one is harder.
-- We could define division by two something like this:
def Nat'.divTwo' : Nat' -> Nat'
  | zero   => Nat'.zero
  | succ n =>
    match n with
    | zero    => Nat'.zero
    | succ n' => n'.divTwo'.succ
#eval s!"9/2 is {(tethera * tethera).divTwo'}"
-- But it's not very elegant.


-- A list of natural numbers is either nil, or a Nat' appended to another list
inductive NatList where
  | nil  : NatList
  | cons : Nat' → NatList → NatList
deriving Repr

-- [3, 2, 1]
def myList : NatList :=
  NatList.cons 3 $ NatList.cons 2 $ NatList.cons 1 NatList.nil

def NatList.length : NatList → Nat'
  | nil       => 0
  | cons _ ns => 1 + ns.length
-- Note that Lean doesn't let us recurse infinitely

#eval s!"My list's length is {myList.length}"


inductive IntList where
  | nil  : IntList
  | cons : Int → IntList → IntList
deriving Repr

def IntList.length : IntList → Nat'
  | cons _ is => 1 + is.length
  | nil       => 0


inductive FloatList where
  | nil  : FloatList
  | cons : Float → FloatList → FloatList
deriving Repr

def FloatList.length : FloatList → Nat'
  | cons _ is => 1 + is.length
  | nil       => 0


-- List of any type. Greek letters are conventionally used to mean "any type". (α can be typed with \a).
-- `Type u` means α can be in any type universe (which I am not qualified to explain or even understand),
-- so you can just think of it as being any type
inductive List' (α : Type u) where
  | nil  : List' α
  | cons : α → List' α → List' α
deriving Repr

def myBoolList : List' Bool :=
  List'.cons True $ List'.cons False List'.nil
#eval myBoolList

-- This following line doesn't work, because it makes no sense.
-- #eval List'.cons 3.14 $ List'.cons "test" List'.nil

def List'.length : List' α → Nat'
  | cons _ is => 1 + is.length
  | nil       => 0

#eval s!"My boolean list's length is {myBoolList.length}"


-- Let's try to define a dot product!
-- This doesn't work:
/-
def List'.dot : List' Nat' → List' Nat' → Nat'
  | nil,       nil => 0
  | cons n ns, cons m ms => n*m + ns.dot ms
-/
-- Lean complains, saying that we haven't said what to do if the lists are different lengths.
-- And this is a good point, since it makes no sense to dot two lists of different lengths!
-- We need a way of ensuring that both lists are the same length.
-- How do we prevent asking Lean questions that make no sense?
-- Just like how a `List' Bool` type means that inserting a Float makes no sense, here we can also use types!


-- Vec α is a function from a natural number to a type
-- It is called a dependent type because the type depends on a value (the length, which is a Nat')
inductive Vec (α : Type u) : Nat' → Type u where
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α n.succ

-- u has length 2
def u : Vec Nat' 2 := Vec.cons 4 $ Vec.cons 2 Vec.nil
-- Doesn't work:
-- def v : Vec Nat' 2 := Vec.cons 1 $ Vec.cons 10 $ Vec.cons 3 Vec.nil
def v : Vec Nat' 2 := Vec.cons 10 $ Vec.cons 3 Vec.nil
def w : Vec Nat' 3 := Vec.cons 2 $ Vec.cons 5 $ Vec.cons 1 Vec.nil

-- Now, we can ensure that both vectors have the same length
def Vec.dot (u : Vec Nat' l) (v : Vec Nat' l) : Nat' :=
  match l, u, v with
  | Nat'.zero,   nil,        nil        => 0
  | Nat'.succ _, cons n1 us, cons n2 vs => n1*n2 + us.dot vs
-- If you're wondering where the `l : Nat` comes from, Lean takes it as an implicit parameter.

#eval s!"(4, 2).(10, 3) = {u.dot v}"
-- Doesn't work:
-- #eval s!"(4, 2).(2, 5, 1) = {u.dot w}"


-- Propositions as types.
variable (P Q S : Prop)
-- In Lean, we write `p : P` to mean "p is a proof (or a witness, or evidence) of the proposition P".
-- In other words, types are propositions, and values are proofs

-- To prove P ∧ Q, we need a proof of P and a proof of Q.
-- If hP is our hypothesis for P and hQ is our hypothesis for Q, we can hypothesize P ∧ Q
theorem p_and_q (hP : P) (hQ : Q) : P ∧ Q :=
  -- Each type has constructors, which introduce the type:
  -- And.intro hP hQ
  -- Conceptuatlly, grouping a proof of P and a proof of Q is just making a pair, so Lean provides some syntactic sugar:
  ⟨hP, hQ⟩
  -- These brackets can be typed with \< and \>.
  -- This is also referred to as a product type (think tuples/classes with multiple properties)

-- Each type also provides eliminators to access information. For And, we can use `And.left` and `And.right` to access the evidence of the conjunction.
theorem p_and_q_implies_p (h : P ∧ Q) : P := h.left
theorem p_and_q_implies_q (h : P ∧ Q) : Q := h.right
theorem p_and_q_implies_q_and_p (h : P ∧ Q) : Q ∧ P := ⟨h.right, h.left⟩


-- To prove a P ∨ Q, we need to either prove P, or prove Q.
-- Or provides the instructors inl and inr (introduce left, introduce right)
theorem p_implies_p_or_q (h : P) : P ∨ Q := Or.inl h
theorem q_implies_p_or_q (h : Q) : P ∨ Q := Or.inr h
theorem p_or_q_implies_q_or_p (h : P ∨ Q) : Q ∨ P :=
  -- Here, we don't know if we have a prof of P or a proof of Q, so we use the eliminator.
  -- The eliminator takes two functions: one for if we have a proof of P, and the other for if we have a proof of Q
  h.elim
    (fun hP : P => Or.inr hP)
    (fun hQ : Q => Or.inl hQ)
-- This is also called a sum type (think enums or unions)

-- Implications are just functions!
-- If we have evidence for P, and a function that transforms evidence for P into evidence for Q, we can use the function along with a evidence of P to get evidence of Q.
theorem modus_ponens (hPQ : P → Q) (hP : P) : Q := hPQ hP

-- P → Q → S parameterizes as P → (Q → S)
-- This is analogous to currying:
-- Each function takes exactly one argument. A two-argument function takes in an argument, and returns a function that takes in a "second" argument before returning its result.
example (hPQS : P → Q → S) (hP : P) (hQ : Q) : S :=
  hPQS hP hQ

-- We can always provide a witness for the statement `True`:
-- There are no eliminators since you can't do anything useful with information you can always construct.
def alwaysTrue : True := trivial
-- We can never provide a witness for the statement `False`. If we do, it's a contradiction.
-- def imPossible : False := _
-- To think about this another way, we can construct values of types representing true propositions, and we can never construct values of types representing false propositions.
-- If someone had told you that a type with no values in it was useful, you would have said they were crazy, right?

theorem p_and_true_implies_p (h : P ∧ True) : P := h.left
theorem p_and_false_implies_false (h : P ∧ False) : False := h.right

-- ¬P is the same as P → False. In other words, if ¬P and we somehow constructed a proof for P, we've messed up.
-- ¬ is typed \n
-- If we have hnP : ¬P and nP : P, we can produce False (a contradiction) with hnP nP
theorem contrapositive (hPQ : P → Q) (hnQ : ¬Q) : ¬P :=
  -- need to provide a value of type ¬P, ie P → False
  fun hP : P => hnQ (hPQ hP)
-- Just like how `True` only provides a single constructor `trivial` and no eliminator, `False` provides no constructor and a single eliminator `absurd`, which allows you to prove anything (principle of explosion)
theorem explode (hP : P) (hnP : ¬P) : Q := absurd hP hnP

-- The law of the excluded middle states that for any proposition P, P is either true or false.
-- theorem lem : P ∨ ¬P := _
-- In constructive type theory, this amounts to saying "give me any P, and I can give you either a proof of P, or a proof of ¬P". However, this is impossible (for example, the halting problem says it's impossible to decide in a finite amount of time whether an arbitrary Turing machine halts or not. Thus, you can't provide a proof that it halts, or a proof that it doesn't.)
-- Interestingly, you *can* prove ¬¬lem.

-- To prove an if and only if, we need to show that P implies Q, and that Q implies P.
theorem and_swap' : P ∧ Q ↔ Q ∧ P :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

-- `have` is one way of introducing a local binding
theorem discrete' : ((P → Q) → (Q → S)) ↔ (Q → S) :=
  -- ((P → Q) → (Q → S))  →  (Q → S)
  have forwards (h : (P → Q) → (Q → S)) (hQ : Q) : S :=
    have hPQ (_ : P) : Q := hQ
    have hQS : Q → S := h hPQ
    hQS hQ
  -- (Q → S)  →  ((P → Q) → (Q → S))
  have backwards (hQS : Q → S) (_ : P → Q) (hQ : Q) : S :=
      hQS hQ
  ⟨ forwards, backwards ⟩

-- These proofs can get hard to read, especially if for some reason it's written like
theorem discrete_ : ((P → Q) → (Q → S)) ↔ (Q → S) :=
  ⟨ fun h hQ => h (fun _ => hQ) hQ, fun hQS _ hQ => hQS hQ ⟩

-- Lean provides an alternate way to express these, called tactics.
-- Tactics are introduced by the keyword `by`. While in tactic mode, you must resolve a series of goals.
-- For each goal, you are provided with information about current types you can work with, and what you need to show.
theorem and_swap : P ∧ Q ↔ Q ∧ P := by
  -- introduce a conjunction
  apply Iff.intro
  -- prove the forwards direction (modus ponens)
  case mp =>
    -- introduce a variable (this is like adding a parameter)
    intro hPQ
    apply And.intro
    -- `exact` tells Lean that this expression solves the goal
    case left => exact hPQ.right
    case right => exact hPQ.left
  -- backwards direction (modus ponens reverse)
  case mpr =>
    intro hQP
    apply And.intro
    case left => exact hQP.right
    case right => exact hQP.left

theorem discrete : ((P → Q) → (Q → S)) ↔ (Q → S) := by
  apply Iff.intro
  case mp =>
    intro h
    intro hQ
    have hPQ (_ : P) := hQ
    exact h hPQ hQ
  case mpr =>
    intro hQS
    intro hPQ
    exact hQS


-- Now, let's discuss equality.
-- `x = y` is another dependent type. This expresses the proposition that `x` is equal to `y`.
-- `x = x` only has one constructor: `Eq.refl x`. Thus, it's impossible to construct evidence that two non-equal things are equal.
-- `refl` stands for reflexitivity, the idea that for all x, x = x.
-- Of course, equality is also symmetric and transitive:

theorem eq_symm (h : x = y) : (y = x) := h.symm
theorem eq_trans (h1 : x = y) (h2 : y = z) : (x = z) := Eq.trans h1 h2

-- Now, we can prove that 2 + 2 = 4!
-- theorem twoPlusTwo : (2 + 2 : Nat') = (4 : Nat') := Eq.refl (4 : Nat')
-- Behind the scenes, when `refl` is used, it reduces both terms. It applies our addition function and sees that both sides rewrite to 4, so `Eq.refl 4` is a witness of the statement `2 + 2 = 4`.
-- `Eq.refl` is used so much that there's a shorthand for it: `rfl`, where Lean will figure out what you mean by itself:
theorem twoPlusTwo : (2 + 2 : Nat') = (4 : Nat') := rfl


-- Well, that wasn't very exciting. Let's try proving something more interesting: n*2 + n*2 = n*4.
-- First, we'll need some lemmas.
-- To prove a ∀ (typed \forall), we need to show that the predicate holds for all input values.
-- In other words, evidence for a ∀ is a function of type (x : A) → P x. This dependent function type is also called a pi-type.
theorem Nat'.add_succ : ∀ a : Nat', ∀ b : Nat', a + b.succ = a.succ + b := by
  intro a
  intro b
  -- Induction allows us to prove statements about all natural numbers.
  -- If we show that the proposition holds for zero; and that if the proposition holds for n, it also holds for succ n; we have showed that it holds for all numbers.
  induction a
  case zero => rfl
  -- `congrArg h f`, where `h` is a proof that `a = b`, returns evidence that `f a = f b`
  case succ a' ih => exact (congrArg Nat'.succ ih)

theorem Nat'.succ_add : ∀ a : Nat', ∀ b : Nat', a.succ + b = Nat'.succ (a + b) := by
  intro a
  intro b
  rfl

theorem Nat'.add_comm : ∀ a : Nat', ∀ b : Nat', a + b = b + a := by
  intro a
  intro b
  induction a
  case zero =>
    induction b
    case zero => rfl
    case succ b' ih =>
      -- `rw` rewrites the terms, using certain rules
      -- However, this is a bit painstaking. Note that `rw` doesn't do any reductions on its own, while `exact` and `rfl` will reduce things like Nat'.plus.
      --rw [Nat'.add_succ]
      --rw [Nat'.succ_add]
      --rw [Nat'.succ_add]
      --rw [ih]
      exact (congrArg Nat'.succ ih)
  case succ a' ih =>
    induction b
    case zero => exact (congrArg Nat'.succ ih)
    case succ b' ih2 =>
      rw [Nat'.succ_add]
      rw [Nat'.succ_add]
      -- Here, we need to specify where in the term we want to rewrite.
      rw [Nat'.add_succ b' a']
      rw [ih]

theorem Nat'.add_assoc : ∀ a : Nat', ∀ b : Nat', ∀ c : Nat', a + (b + c) = (a + b) + c := by
  intro a
  intro b
  intro c
  induction a
  case zero => rfl
  case succ _ ih => exact (congrArg Nat'.succ ih)

theorem Nat'.succ_mul : ∀ a : Nat', ∀ b : Nat', a.succ * b = b + (a * b) := by
  intro a
  intro b
  rfl

theorem Nat'.left_distrib : ∀ a : Nat', ∀ b : Nat', ∀ c : Nat', a * (b + c) = a * b + a * c := by
  intro a
  intro b
  intro c
  induction a
  case zero => rfl
  case succ a' ih =>
    rw [Nat'.succ_mul]
    rw [Nat'.succ_mul]
    rw [Nat'.succ_mul]
    rw [Nat'.add_assoc]
    -- ← (typed \l) rewrites the other way
    rw [← Nat'.add_assoc b (a' * b)]
    -- If it's unambiguous, we can specify only part of where we're rewriting
    rw [Nat'.add_comm (a' * b)]
    rw [Nat'.add_assoc]
    rw [← Nat'.add_assoc (b + c)]
    rw [ih]

theorem moreTwoPlusTwo : ∀ n : Nat', n*2 + n*2 = n*4 := by
  intro n
  -- First, we need to rewrite `4` to `2 + 2`
  rw [← twoPlusTwo]
  -- Then, we can use distributivity of multiplication
  rw [Nat'.left_distrib n 2 2]


-- Now, let's talk about ∃ (typed \ex)
-- To show that there exists an `x : A` such that `P x`, we need to provide the `x`, and give a proof of `P x`.
-- In other words, we need to construct a pair of type (x : A, P x). This dependent pair type is also called a sigma-type.
def Even (x : Nat') := ∃ k, x = 2 * k
def Odd  (x : Nat') := ∃ k, x = 1 + 2 * k

def zeroIsEven' : Even 0 := by
  -- To create this pair/existential type, we can use `Exists.intro`
  apply Exists.intro
  -- w is the case where we show the element. In this case, 0 = 2 * 0, so k = 0.
  case w => exact 0
  -- h is the proof that the predicate holds. To show that 0 = 2*k with k = 0, it's just rfl.
  case h => rfl
-- Could also be defined without tactics like this:
def zeroIsEven : Even 0 := ⟨0, rfl⟩

-- If n = 2*k, n+1 = 1 + 2*k
def succEvenIsOdd : Even n → Odd (1 + n) := by
  intro ⟨ k, hEven ⟩
  apply Exists.intro
  case w => exact k
  case h => rw [hEven]

-- If n = 1 + 2*k, n+1 = 2 + 2*k = 2 * (1+k)
def succOddIsEven : Odd n → Even (1 + n) := by
  intro ⟨ k, hOdd ⟩
  apply Exists.intro
  case w => exact 1 + k
  case h =>
    rw [hOdd]
    rw [Nat'.add_assoc]
    rw [Nat'.left_distrib]
    rfl

-- Every number is either even or odd!
theorem EvenOrOdd : ∀ n : Nat', Even n ∨ Odd n := by
  intro n
  induction n
  case zero => exact (Or.inl zeroIsEven)
  case succ n' ih =>
    apply Or.elim ih
    case left =>
      intro hEven
      apply Or.inr
      exact (succEvenIsOdd hEven)
    case right =>
      intro hOdd
      apply Or.inl
      exact (succOddIsEven hOdd)

-- Let's think about what we've done here. This program doesn't only prove that every number is either even or odd,
-- it also divides the number in two! So, it both proves something useful and *does* something useful.

-- To have some fun learning tactics, try the Natural Numbers Game: https://adam.math.hhu.de/#/g/leanprover-community/nng4
-- Or, try the Lean Intro to Logic: https://adam.math.hhu.de/#/g/trequetrum/lean4game-logic
-- Happy proving!
