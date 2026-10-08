import SpinGlass.SupportEvaluation
import SpinGlass.AccuracyBudget

/-!
# Counted input and accuracy-budget preparation

The real-arithmetic model treats division, square root, exponential, logarithm,
and hyperbolic tangent as unit-cost elementary oracles. The construction below
computes and caches the scale once, then traverses only the `p`-edge array.
The log-cosh terms are obtained from exponentials and arithmetic. Every real
operation is counted by the syntax; cached real values are subsequently inputs.
-/

noncomputable section
namespace SpinGlass.InputPreparation
open Finset SpinGlass.ArithmeticEvaluation SpinGlass.SupportEvaluation

/-- Unit-cost elementary real operations, with the costs of their inputs. -/
def divide (x y : Computation) : Computation :=
  ⟨x.value/y.value, x.operations+y.operations+1⟩
def squareRoot (x : Computation) : Computation := ⟨Real.sqrt x.value, x.operations+1⟩
def exponential (x : Computation) : Computation := ⟨Real.exp x.value, x.operations+1⟩
def logarithm (x : Computation) : Computation := ⟨Real.log x.value, x.operations+1⟩
def hyperbolicTangent (x : Computation) : Computation :=
  ⟨Real.tanh x.value, x.operations+1⟩

/-- Cosh uses two exponentials, one sign change, one addition, and one division. -/
def hyperbolicCosine (x : ℝ) : Computation :=
  divide (add (exponential (literal x))
    (exponential (mul (literal (-1)) (literal x)))) (literal 2)

@[simp] theorem hyperbolicCosine_value (x : ℝ) :
    (hyperbolicCosine x).value = Real.cosh x := by
  simp [hyperbolicCosine, divide, add, exponential, mul, literal, Real.cosh_eq]

@[simp] theorem hyperbolicCosine_operations (x : ℝ) :
    (hyperbolicCosine x).operations = 5 := by rfl

/-- Integer power by the actual multiplication loop, followed by sqrt/division. -/
def scaleComputation (N p : ℕ) (β : ℝ) : Computation :=
  divide (literal β) (squareRoot (productFinset (range (p-1)) (fun _ => literal (N:ℝ))))

@[simp] theorem scaleComputation_value (N p : ℕ) (β : ℝ) :
    (scaleComputation N p β).value = SpinGlass.Disorder.pureScale N p β := by
  simp [scaleComputation, divide, squareRoot, literal, SpinGlass.Disorder.pureScale]

@[simp] theorem scaleComputation_operations (N p : ℕ) (β : ℝ) :
    (scaleComputation N p β).operations = p-1+2 := by
  simp [scaleComputation, divide, squareRoot, literal]

structure EdgeData where
  weight : ℝ
  logCosh : ℝ
  operations : ℕ

/-- The scaled coupling is computed once and shared by the two elementary terms. -/
def prepareEdge (a J : ℝ) : EdgeData :=
  let x := mul (literal a) (literal J)
  let w := hyperbolicTangent (literal x.value)
  let l := logarithm (hyperbolicCosine x.value)
  ⟨w.value, l.value, x.operations+w.operations+l.operations⟩

@[simp] theorem prepareEdge_weight (a J : ℝ) :
    (prepareEdge a J).weight = SpinGlass.Disorder.weight a J := by rfl
@[simp] theorem prepareEdge_logCosh (a J : ℝ) :
    (prepareEdge a J).logCosh = Real.log (Real.cosh (a*J)) := by
  simp [prepareEdge, logarithm, mul, literal]
@[simp] theorem prepareEdge_operations (a J : ℝ) :
    (prepareEdge a J).operations = 8 := by rfl

structure EdgeArray (E : Type*) where
  entries : List (E × EdgeData)
  operations : ℕ

/-- The input traversal reads exactly the listed edges. -/
def prepareEdges {E : Type*} (a : ℝ) (J : E → ℝ) : List E → EdgeArray E
  | [] => ⟨[], 0⟩
  | e::es =>
    let d := prepareEdge a (J e)
    let tail := prepareEdges a J es
    ⟨(e,d)::tail.entries, d.operations+tail.operations⟩

@[simp] theorem prepareEdges_entries {E : Type*} (a : ℝ) (J : E → ℝ) (es : List E) :
    (prepareEdges a J es).entries = es.map (fun e => (e,prepareEdge a (J e))) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [prepareEdges, ih]

@[simp] theorem prepareEdges_operations {E : Type*} (a : ℝ) (J : E → ℝ) (es : List E) :
    (prepareEdges a J es).operations = 8*es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [prepareEdges, ih]; omega

/-- A finite cached-array lookup. Unused indices have no physical meaning. -/
def lookupEdge {E : Type*} [DecidableEq E] (e : E) : List (E × EdgeData) → EdgeData
  | [] => ⟨0,0,0⟩
  | (e',d)::es => if e=e' then d else lookupEdge e es

/-- The associated finite scan performs at most one key comparison per entry. -/
def lookupVisits {E : Type*} [DecidableEq E] (e : E) : List (E × EdgeData) → ℕ
  | [] => 0
  | (e',_)::es => if e=e' then 1 else lookupVisits e es + 1

theorem lookupVisits_le {E : Type*} [DecidableEq E] (e : E) (es : List (E × EdgeData)) :
    lookupVisits e es ≤ es.length := by
  induction es with
  | nil => rfl
  | cons x es ih => simp only [lookupVisits, List.length_cons]; split_ifs <;> omega

theorem lookup_prepareEdges {E : Type*} [DecidableEq E] (a : ℝ) (J : E → ℝ)
    (es : List E) {e : E} (he : e∈es) :
    lookupEdge e (prepareEdges a J es).entries = prepareEdge a (J e) := by
  induction es with
  | nil => simp at he
  | cons e' es ih =>
    simp only [prepareEdges, lookupEdge]
    split_ifs with h
    · subst e'; rfl
    · exact ih ((List.mem_cons.mp he).resolve_left h)

/-- The log-prefactor sums cached log-cosh values, and computes `N log 2`. -/
def prefactorComputation {E : Type*} (N : ℕ) (es : List (E × EdgeData)) : Computation :=
  add (mul (literal N) (logarithm (literal 2)))
    (sumList (es.map (fun x => literal x.2.logCosh)))

@[simp] theorem prefactorComputation_value {E : Type*} (N : ℕ) (es : List (E × EdgeData)) :
    (prefactorComputation N es).value = N*Real.log 2 + (es.map (fun x => x.2.logCosh)).sum := by
  simp [prefactorComputation, add, mul, literal, logarithm, List.map_map, Function.comp_def]

@[simp] theorem prefactorComputation_operations {E : Type*} (N : ℕ)
    (es : List (E × EdgeData)) : (prefactorComputation N es).operations = es.length+3 := by
  simp [prefactorComputation, add, mul, literal, logarithm, List.map_map, Function.comp_def]
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]

structure PreparedInput (V : Type*) where
  scale : ℝ
  entries : List (Finset V × EdgeData)
  logPrefactor : ℝ
  operations : ℕ

/-- Preparation enumerates `choose(N,p)` input edges, not the ambient powerset. -/
def prepareInput (p : ℕ) (β : ℝ) (J : Finset V → ℝ) : PreparedInput V :=
  let a := scaleComputation (Fintype.card V) p β
  let es := prepareEdges a.value J ((univ : Finset V).powersetCard p).toList
  let l := prefactorComputation (Fintype.card V) es.entries
  ⟨a.value, es.entries, l.value, a.operations+es.operations+l.operations⟩

def preparedWeight (input : PreparedInput V) (e : Finset V) : ℝ :=
  (lookupEdge e input.entries).weight

@[simp] theorem prepareInput_scale (p : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (prepareInput p β J).scale = SpinGlass.Disorder.pureScale (Fintype.card V) p β := by
  simp [prepareInput]

theorem preparedWeight_value (p : ℕ) (β : ℝ) (J : Finset V → ℝ)
    {e : Finset V} (he : e∈(univ : Finset V).powersetCard p) :
    preparedWeight (prepareInput p β J) e =
      SpinGlass.Disorder.weight (SpinGlass.Disorder.pureScale (Fintype.card V) p β) (J e) := by
  unfold preparedWeight prepareInput
  rw [lookup_prepareEdges _ _ _ (by simpa using he), prepareEdge_weight, scaleComputation_value]

theorem prepareInput_logPrefactor_sum (p : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (prepareInput p β J).logPrefactor = (Fintype.card V:ℝ)*Real.log 2 +
      ∑ e∈(univ : Finset V).powersetCard p,
        Real.log (Real.cosh (SpinGlass.Disorder.pureScale (Fintype.card V) p β * J e)) := by
  simp [prepareInput, prefactorComputation_value, List.map_map, Function.comp_def]

theorem prepareInput_logPrefactor (p : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (prepareInput p β J).logPrefactor =
      Real.log (SpinGlass.Partition.prefactor (V:=V) ((univ : Finset V).powersetCard p)
        (fun e => SpinGlass.Disorder.pureScale (Fintype.card V) p β * J e)) := by
  rw [prepareInput_logPrefactor_sum, SpinGlass.Partition.prefactor,
    Real.log_mul (by positivity) (ne_of_gt (Finset.prod_pos (fun _ _ => Real.cosh_pos _))),
    Real.log_pow, Real.log_prod (fun _ _ => ne_of_gt (Real.cosh_pos _))]

/-- Exact cost from the scale loop, eight operations per edge, and the final sum. -/
theorem prepareInput_operations (p : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (prepareInput p β J).operations = p-1+5+9*(Fintype.card V).choose p := by
  simp [prepareInput]
  omega

theorem prepareInput_cost {p : ℕ} (hp : 0<p) (β : ℝ) (J : Finset V → ℝ) :
    (prepareInput p β J).operations ≤ (p+14)*(Fintype.card V+1)^p := by
  rw [prepareInput_operations]
  have hP : 1 ≤ (Fintype.card V+1)^p := Nat.one_le_pow _ _ (by omega)
  have hM : (Fintype.card V).choose p ≤ (Fintype.card V+1)^p :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hpP := Nat.mul_le_mul_left p hP
  have hsub : p-1 ≤ p := Nat.sub_le _ _
  nlinarith

theorem prepared_lookup_visits (p : ℕ) (β : ℝ) (J : Finset V → ℝ) (e : Finset V) :
    lookupVisits e (prepareInput p β J).entries ≤ (Fintype.card V).choose p := by
  have h := lookupVisits_le e (prepareInput p β J).entries
  simpa [prepareInput] using h

/-- The support evaluator depends on weights only at its actual input edges. -/
theorem higherEvaluator_congr (p cutoff : ℕ) {w w' : Finset V → ℝ}
    (hw : ∀ e∈(univ : Finset V).powersetCard p, w e=w' e) :
    (higherEvaluator p cutoff w).value = (higherEvaluator p cutoff w').value := by
  rw [higherEvaluator_value, higherEvaluator_value]
  apply Finset.sum_congr rfl
  intro Γ hΓ
  have hsub := Finset.mem_powerset.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hΓ).1).1
  apply Finset.prod_congr rfl
  intro e he
  exact hw e (hsub he)

/-- The exact evaluator has the same restriction property. -/
theorem exactEvaluator_congr (p : ℕ) {w w' : Finset V → ℝ}
    (hw : ∀ e∈(univ : Finset V).powersetCard p, w e=w' e) :
    (exactEvaluator p w).value = (exactEvaluator p w').value := by
  simp only [exactEvaluator, localEvaluator_value, SpinGlass.LocalCube.localGspin,
    SpinGlass.Expansion.spinMean]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.prod_congr rfl
  intro e he
  rw [hw e (Finset.mem_filter.mp he).1]

theorem prepared_higherEvaluator_value (p cutoff : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (higherEvaluator p cutoff (preparedWeight (prepareInput p β J))).value =
      SpinGlass.SupportMeanSquare.supportApproximation p cutoff
        (SpinGlass.Disorder.pureScale (Fintype.card V) p β) J := by
  rw [higherEvaluator_congr p cutoff (fun e he => preparedWeight_value p β J he),
    higherEvaluator_disorder_value]

theorem prepared_exactEvaluator_value (p : ℕ) (β : ℝ) (J : Finset V → ℝ) :
    (exactEvaluator p (preparedWeight (prepareInput p β J))).value =
      SpinGlass.Partition.normalizedPartition id ((univ : Finset V).powersetCard p)
        (fun e => SpinGlass.Disorder.pureScale (Fintype.card V) p β * J e) := by
  rw [exactEvaluator_congr p (fun e he => preparedWeight_value p β J he),
    exactEvaluator_disorder_value]

/-- The threshold is computed through the elementary exp/log formula for real powers. -/
def thresholdComputation (C δ s : ℝ) : Computation :=
  exponential (divide (logarithm (divide (literal δ) (mul (literal 2) (literal C))))
    (literal s))

@[simp] theorem thresholdComputation_value {C δ s : ℝ} (hC : 0<C) (hδ : 0<δ) :
    (thresholdComputation C δ s).value = SpinGlass.accuracyThreshold C δ s := by
  change Real.exp (Real.log (δ/(2*C))/s) = (δ/(2*C))^(1/s)
  rw [Real.rpow_def_of_pos (div_pos hδ (by positivity : 0 < 2*C))]
  congr 1
  ring

@[simp] theorem thresholdComputation_operations (C δ s : ℝ) :
    (thresholdComputation C δ s).operations = 5 := by rfl

structure PreparedBudget where
  z : ℝ
  u : ℝ
  operations : ℕ

/-- Once z is cached, u uses two squares, two products, and division by eight. -/
def prepareBudget (C δ ε s : ℝ) : PreparedBudget :=
  let z := thresholdComputation C δ s
  let z2 := mul (literal z.value) (literal z.value)
  let eps2 := mul (literal ε) (literal ε)
  let u := divide (mul (mul (literal δ) eps2) z2) (literal 8)
  ⟨z.value, u.value, z.operations+u.operations⟩

@[simp] theorem prepareBudget_z {C δ ε s : ℝ} (hC : 0<C) (hδ : 0<δ) :
    (prepareBudget C δ ε s).z = SpinGlass.accuracyThreshold C δ s := by
  exact thresholdComputation_value hC hδ

@[simp] theorem prepareBudget_u {C δ ε s : ℝ} (hC : 0<C) (hδ : 0<δ) :
    (prepareBudget C δ ε s).u = SpinGlass.accuracyMSEBudget C δ ε s := by
  simp only [prepareBudget, divide, mul, literal, thresholdComputation_value hC hδ,
    SpinGlass.accuracyMSEBudget, pow_two]

@[simp] theorem prepareBudget_operations (C δ ε s : ℝ) :
    (prepareBudget C δ ε s).operations = 10 := by rfl

end SpinGlass.InputPreparation
