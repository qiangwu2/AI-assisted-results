import SpinGlass.Mobius

/-!
# Restricting spin averages to the vertices actually used

A Boolean assignment on the ambient vertex set splits into assignments on a
specified finite subset and its complement. This explicit equivalence proves
that averaging a function of the restricted spins gives its local-cube mean.
The final theorem applies this identity to the induced interaction polynomial
in `Mobius.Gspin`. No assertion about evaluation cost is made.
-/

noncomputable section
open Finset
namespace SpinGlass.LocalCube

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Split ambient spin assignments into independent local and unused coordinates. -/
def splitSpins (U : Finset V) :
    (V → Bool) ≃ (U → Bool) × ({v : V // v ∉ U} → Bool) :=
  Equiv.piEquivPiSubtypeProd (fun v => v ∈ U) (fun _ => Bool)

/-- The unnormalized ambient sum is the local sum repeated once for each
assignment of the unused coordinates. -/
lemma sum_restrict (U : Finset V) (f : (U → Bool) → ℝ) :
    (∑ σ : V → Bool, f (fun v : U => σ v)) =
      (2 : ℝ) ^ Fintype.card {v : V // v ∉ U} * ∑ τ : U → Bool, f τ := by
  calc
    (∑ σ : V → Bool, f (fun v : U => σ v)) =
        ∑ τ : (U → Bool) × ({v : V // v ∉ U} → Bool), f τ.1 :=
      Fintype.sum_equiv (splitSpins U) _ _ (fun _ => rfl)
    _ = (2 : ℝ) ^ Fintype.card {v : V // v ∉ U} * ∑ τ : U → Bool, f τ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [Finset.mul_sum]

/-- The cube-size factorization follows from the actual splitting equivalence. -/
lemma cube_size_split (U : Finset V) :
    (2 : ℝ) ^ Fintype.card V =
      (2 : ℝ) ^ Fintype.card U * (2 : ℝ) ^ Fintype.card {v : V // v ∉ U} := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr (splitSpins U))
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- Uniform averaging commutes with restricting spins to a finite vertex set. -/
theorem spinMean_restrict (U : Finset V) (f : (U → Bool) → ℝ) :
    Expansion.spinMean (fun σ : V → Bool => f (fun v : U => σ v)) =
      Expansion.spinMean f := by
  unfold Expansion.spinMean
  rw [sum_restrict, cube_size_split U, mul_inv_rev]
  have hnonzero : (2 : ℝ) ^ Fintype.card {v : V // v ∉ U} ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  calc
    (2 ^ Fintype.card {v : V // v ∉ U})⁻¹ * (2 ^ Fintype.card U)⁻¹ *
        (2 ^ Fintype.card {v : V // v ∉ U} * ∑ τ, f τ) =
        (2 ^ Fintype.card U)⁻¹ *
          ((2 ^ Fintype.card {v : V // v ∉ U})⁻¹ *
            2 ^ Fintype.card {v : V // v ∉ U}) * ∑ τ, f τ := by ring
    _ = (2 ^ Fintype.card U)⁻¹ * ∑ τ, f τ := by
      rw [inv_mul_cancel₀ hnonzero, mul_one]

/-- The interaction incidence on the local vertex type. -/
def localIncidence (U : Finset V) (e : Finset V) : Finset U :=
  e.subtype (fun v => v ∈ U)

omit [Fintype V] in
/-- A supported interaction has the same character in ambient and local spins. -/
lemma edgeCharacter_restrict (U e : Finset V) (he : e ⊆ U) (σ : V → Bool) :
    Expansion.edgeCharacter (localIncidence U) (fun v : U => σ v) e =
      Expansion.edgeCharacter id σ e := by
  exact Finset.prod_subtype_of_mem (fun v => Expansion.spinSign (σ v))
    (fun v hv => he hv)

/-- The spin polynomial averaged over precisely the vertices of `U`, with all
interaction incidences restricted to that local vertex type. -/
def localGspin (edges : Hypergraph.FiniteHypergraph V)
    (weight : Finset V → ℝ) (U : Finset V) : ℝ :=
  Expansion.spinMean (fun σ : U → Bool =>
    ∏ e ∈ edges.filter (fun e => e ⊆ U),
      (1 + weight e * Expansion.edgeCharacter (localIncidence U) σ e))

/-- The ambient-cube definition in `Mobius` is exactly the local-cube spin
average on the induced interactions, for every finite vertex set `U`. -/
theorem Gspin_eq_localGspin (edges : Hypergraph.FiniteHypergraph V)
    (weight : Finset V → ℝ) (U : Finset V) :
    Mobius.Gspin edges weight U = localGspin edges weight U := by
  unfold Mobius.Gspin localGspin
  rw [← spinMean_restrict U]
  congr 1
  funext σ
  apply Finset.prod_congr rfl
  intro e he
  rw [edgeCharacter_restrict U e (Finset.mem_filter.mp he).2]

end SpinGlass.LocalCube
