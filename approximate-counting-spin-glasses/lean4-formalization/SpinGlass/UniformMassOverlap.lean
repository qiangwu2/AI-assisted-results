import SpinGlass.UniformMassEntropy
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Distinct-index overlap comparison

The interaction sum uses genuine `p`-element subsets. The ordered-tuple
multiplicity and repeated-index error are proved by finite combinatorics.
-/

noncomputable section
namespace SpinGlass.UniformMassOverlap
open Finset Real
open SpinGlass.Expansion SpinGlass.UniformMassEntropy

variable {V : Type*} [Fintype V] [DecidableEq V] (p : ℕ)

/-- The actual range of an ordered tuple with distinct coordinates. -/
def embeddingSupport (e : Fin p ↪ V) : {s : Finset V // s.card = p} :=
  ⟨Finset.univ.map e, by simp⟩

/-- A fiber over a fixed support is exactly the embeddings into that support. -/
def supportFiberEquiv (s : {s : Finset V // s.card = p}) :
    {e : Fin p ↪ V // embeddingSupport p e = s} ≃ (Fin p ↪ (s.val : Set V)) where
  toFun e :=
    { toFun := fun i => ⟨e.val i, by
        have hr : Finset.univ.map e.val = s.val := congrArg Subtype.val e.property
        rw [← hr]
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      inj' := fun i j h => e.val.injective (congrArg Subtype.val h) }
  invFun g :=
    ⟨g.trans (Function.Embedding.subtype fun v => v ∈ s.val), by
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
        exact (g i).property
      · simp only [embeddingSupport, Finset.card_map, Finset.card_univ, Fintype.card_fin]
        exact s.property.le⟩
  left_inv e := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv g := by
    apply Function.Embedding.ext
    intro i
    rfl

/-- Every support has precisely `p!` orderings. -/
theorem support_fiber_card (s : {s : Finset V // s.card = p}) :
    Fintype.card {e : Fin p ↪ V // embeddingSupport p e = s} = Nat.factorial p := by
  rw [Fintype.card_congr (supportFiberEquiv p s), Fintype.card_embedding_eq]
  have hc : Fintype.card (s.val : Set V) = s.val.card := by
    exact Fintype.card_ofFinset s.val (fun _ => Iff.rfl)
  rw [hc, s.property, Fintype.card_fin, Nat.descFactorial_self]

/-- The product on an embedding depends only on its support. -/
theorem embedding_prod_eq (w : V → ℝ) (e : Fin p ↪ V) :
    (∏ i, w (e i)) = ∏ v ∈ (embeddingSupport p e).val, w v := by
  exact (Finset.prod_map Finset.univ e w).symm

/-- Distinct ordered tuples have exactly the factorial multiplicity used in the paper. -/
theorem distinct_tuple_sum (w : V → ℝ) :
    (∑ e : Fin p ↪ V, ∏ i, w (e i)) =
      (Nat.factorial p : ℝ) * ∑ s ∈ (Finset.univ : Finset V).powersetCard p, ∏ v ∈ s, w v := by
  rw [← Fintype.sum_fiberwise (embeddingSupport p) (fun e : Fin p ↪ V => ∏ i, w (e i))]
  have hinner : ∀ s : {s : Finset V // s.card = p},
      (∑ e : {e : Fin p ↪ V // embeddingSupport p e = s}, ∏ i, w (e.val i)) =
      (Nat.factorial p : ℝ) * ∏ v ∈ s.val, w v := by
    intro s
    have hprod : ∀ e : {e : Fin p ↪ V // embeddingSupport p e = s},
        (∏ i, w (e.val i)) = ∏ v ∈ s.val, w v := by
      intro e
      rw [embedding_prod_eq p w, e.property]
    simp_rw [hprod]
    rw [Finset.sum_const, Finset.card_univ, support_fiber_card]
    simp only [nsmul_eq_mul]
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_subtype ((Finset.univ : Finset V).powersetCard p)
    (fun s => by simp) (fun s => ∏ v ∈ s, w v)).symm

/-- Every ordered tuple contributes to the power of the spin sum. -/
theorem tuple_sum_eq_power (w : V → ℝ) :
    (∑ f : Fin p → V, ∏ i, w (f i)) = (∑ v, w v)^p := by
  rw [← Fintype.prod_sum (fun (_i : Fin p) (v : V) => w v)]
  simp

/-- Injective tuples and embeddings are definitionally equivalent data. -/
def injectiveTupleEquiv : {f : Fin p → V // Function.Injective f} ≃ (Fin p ↪ V) where
  toFun f := ⟨f.val, f.property⟩
  invFun e := ⟨e, e.injective⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem injective_tuple_sum (w : V → ℝ) :
    (∑ f ∈ (Finset.univ : Finset (Fin p → V)).filter Function.Injective, ∏ i, w (f i)) =
      (Nat.factorial p : ℝ) * ∑ s ∈ (Finset.univ : Finset V).powersetCard p, ∏ v ∈ s, w v := by
  calc
    _ = ∑ f : {f : Fin p → V // Function.Injective f}, ∏ i, w (f.val i) :=
      Finset.sum_subtype _ (fun _ => by simp) _
    _ = ∑ e : Fin p ↪ V, ∏ i, w (e i) :=
      Fintype.sum_equiv (injectiveTupleEquiv p) _ _ (fun _ => rfl)
    _ = _ := distinct_tuple_sum p w

/-- A uniform birthday-collision bound obtained from the exact count of injections. -/
theorem pow_le_descFactorial_add (N p : ℕ) (hpN : p ≤ N) :
    (N : ℝ)^p ≤ (N.descFactorial p : ℝ) + (p.choose 2 : ℝ) * (N : ℝ)^(p-1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    by_cases hp0 : p = 0
    · subst p
      simp
    have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
    have hpN' : p ≤ N := by omega
    have hrec := mul_le_mul_of_nonneg_left (ih hpN') (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    have hdf : (N.descFactorial p : ℝ) ≤ (N : ℝ)^p := by
      exact_mod_cast Nat.descFactorial_le_pow N p
    have hprod := mul_le_mul_of_nonneg_left hdf (Nat.cast_nonneg p : (0:ℝ) ≤ p)
    have hexp : (N : ℝ) * (N : ℝ)^(p-1) = (N : ℝ)^p := by
      rw [← pow_succ']
      congr 1
      omega
    rw [mul_add, ← mul_assoc (N : ℝ), mul_comm (N : ℝ) (p.choose 2 : ℝ),
      mul_assoc, hexp] at hrec
    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hpN',
      Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.succ_sub_one, pow_succ]
    nlinarith

/-- The number of noninjective ordered tuples is bounded by the explicit collision term. -/
theorem repeated_tuple_card_le (p : ℕ) (hp : p ≤ Fintype.card V) :
    (((Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f)).card : ℝ) ≤
      (p.choose 2 : ℝ) * (Fintype.card V : ℝ)^(p-1) := by
  classical
  have hinj : ((Finset.univ : Finset (Fin p → V)).filter Function.Injective).card =
      (Fintype.card V).descFactorial p := by
    have hcard := Fintype.card_congr (injectiveTupleEquiv (V := V) p)
    rw [Fintype.card_embedding_eq, Fintype.card_fin] at hcard
    rw [Fintype.subtype_card ((Finset.univ : Finset (Fin p → V)).filter Function.Injective)
      (fun _ => by simp)] at hcard
    exact hcard
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin p → V)))
    Function.Injective
  rw [hinj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hsum
  have hs : ((Fintype.card V).descFactorial p : ℝ) +
      (((Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f)).card : ℝ) =
      (Fintype.card V : ℝ)^p := by exact_mod_cast hsum
  have hb := pow_le_descFactorial_add (Fintype.card V) p hp
  linarith

/-- Uniform ordered-tuple error for coefficients of absolute value at most one. -/
theorem distinct_sum_error (w : V → ℝ) (hw : ∀ v, |w v| ≤ 1)
    (hp : p ≤ Fintype.card V) :
    |(∑ v, w v)^p - (Nat.factorial p : ℝ) *
      ∑ s ∈ (Finset.univ : Finset V).powersetCard p, ∏ v ∈ s, w v| ≤
      (p.choose 2 : ℝ) * (Fintype.card V : ℝ)^(p-1) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin p → V))
    Function.Injective (fun f => ∏ i, w (f i))
  rw [injective_tuple_sum, tuple_sum_eq_power] at hsplit
  have heq : (∑ v, w v)^p - (Nat.factorial p : ℝ) *
      ∑ s ∈ (Finset.univ : Finset V).powersetCard p, ∏ v ∈ s, w v =
      ∑ f ∈ (Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f),
        ∏ i, w (f i) := by linarith
  rw [heq]
  calc
    _ ≤ ∑ f ∈ (Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f),
        |∏ i, w (f i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f ∈ (Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f),
        (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro f hf
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hw (f i))
    _ = (((Finset.univ : Finset (Fin p → V)).filter (fun f => ¬Function.Injective f)).card : ℝ) := by simp
    _ ≤ _ := repeated_tuple_card_le p hp

/-- The paper's explicit repeated-index constant. -/
def delta (p : ℕ) : ℝ := (p.choose 2 : ℝ) / (Nat.factorial p : ℝ)

/-- The actual pure p-spin auxiliary interaction, using unordered distinct indices. -/
def auxiliaryEnergy (p : ℕ) (σ : V → Bool) : ℝ :=
  (∑ e ∈ (Finset.univ : Finset V).powersetCard p, edgeCharacter id σ e) /
    (Fintype.card V : ℝ)^(p-1)

/-- The exact uniform repeated-index error from Lemma 4.2. -/
theorem auxiliaryEnergy_error (hp : 0 < p) (hpN : p ≤ Fintype.card V) (σ : V → Bool) :
    |auxiliaryEnergy p σ - (Fintype.card V : ℝ) * overlap σ ^ p / (Nat.factorial p : ℝ)| ≤
      delta p := by
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr (lt_of_lt_of_le hp hpN)
  have hfac : (0 : ℝ) < (Nat.factorial p : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpow : (Fintype.card V : ℝ)^p =
      (Fintype.card V : ℝ) * (Fintype.card V : ℝ)^(p-1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hraw := distinct_sum_error p (fun v => spinSign (σ v))
    (fun v => (abs_spinSign (σ v)).le) hpN
  have heq : auxiliaryEnergy p σ - (Fintype.card V : ℝ) * overlap σ^p / (Nat.factorial p : ℝ) =
      -((∑ v, spinSign (σ v))^p - (Nat.factorial p : ℝ) *
        ∑ s ∈ (Finset.univ : Finset V).powersetCard p, ∏ v ∈ s, spinSign (σ v)) /
        ((Nat.factorial p : ℝ) * (Fintype.card V : ℝ)^(p-1)) := by
    unfold auxiliaryEnergy overlap signSum edgeCharacter
    simp only [id_eq]
    rw [div_pow, hpow]
    field_simp
    <;> ring
  rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos hfac (pow_pos hN _))]
  calc
    _ ≤ ((p.choose 2 : ℝ) * (Fintype.card V : ℝ)^(p-1)) /
        ((Nat.factorial p : ℝ) * (Fintype.card V : ℝ)^(p-1)) :=
      div_le_div_of_nonneg_right hraw (mul_pos hfac (pow_pos hN _)).le
    _ = delta p := by
      unfold delta
      field_simp

end SpinGlass.UniformMassOverlap
