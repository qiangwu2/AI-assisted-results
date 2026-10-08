import SpinGlass.InputPreparation
import SpinGlass.CountingReduction

/-! Exact Section 9.2 reduction from an ordered SK matrix, including its
spin-independent diagonal term and probability normalization. -/
noncomputable section
namespace SpinGlass.OrderedSK
open scoped BigOperators
open Finset Real SpinGlass.Expansion

def upperPairs (N : ℕ) : Finset (Fin N × Fin N) := univ.filter (fun q => q.1 < q.2)
def pairEdge {N : ℕ} (q : Fin N × Fin N) : Finset (Fin N) := {q.1,q.2}

theorem pairEdge_injOn (N : ℕ) : Set.InjOn (pairEdge (N := N)) (↑(upperPairs N)) := by
  intro p hp q hq he
  have hp' := (mem_filter.mp hp).2
  have hq' := (mem_filter.mp hq).2
  have hs : ({p.1,p.2} : Set (Fin N))={q.1,q.2} := by
    simpa [pairEdge] using congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) he
  rcases Set.pair_eq_pair_iff.mp hs with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Prod.ext h1 h2
  · rw [h1,h2] at hp'
    exact False.elim ((lt_asymm hp' hq'))

theorem upperPairs_image (N : ℕ) : (upperPairs N).image pairEdge = (univ : Finset (Fin N)).powersetCard 2 := by
  ext e
  constructor
  · rintro he
    obtain ⟨q,hq,rfl⟩ := mem_image.mp he
    exact mem_powersetCard.mpr ⟨subset_univ _,card_pair (ne_of_lt (mem_filter.mp hq).2)⟩
  · intro he
    obtain ⟨i,j,hij,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp he).2
    rcases lt_or_gt_of_ne hij with h | h
    · exact mem_image.mpr ⟨(i,j),by simp [upperPairs,h],rfl⟩
    · exact mem_image.mpr ⟨(j,i),by simp [upperPairs,h],by simp [pairEdge,pair_comm]⟩

/-- The physical unordered coupling, extended by zero to unused edge indices. -/
def coupling {N : ℕ} (G : Fin N × Fin N → ℝ) (e : Finset (Fin N)) : ℝ :=
  ∑ q∈upperPairs N, if pairEdge q=e then (G q+G (q.2,q.1))/sqrt 2 else 0

theorem coupling_pair {N : ℕ} (G : Fin N × Fin N → ℝ) {q : Fin N × Fin N}
    (hq : q∈upperPairs N) : coupling G (pairEdge q) = (G q+G (q.2,q.1))/sqrt 2 := by
  unfold coupling
  rw [sum_eq_single q]
  · simp
  · intro r hr hrq
    have hn : pairEdge r≠pairEdge q := fun he => hrq (pairEdge_injOn N hr hq he)
    simp [hn]
  · exact fun h => False.elim (h hq)

/-- Ordered sums split into the diagonal and the two orientations of each pair. -/
theorem ordered_sum (N : ℕ) (F : Fin N → Fin N → ℝ) :
    (∑ i,∑ j,F i j) = (∑ i,F i i) + ∑ q∈upperPairs N,(F q.1 q.2+F q.2 q.1) := by
  have hsplit (i j : Fin N) : F i j =
      (if i=j then F i i else 0)+(if i < j then F i j else 0)+(if j < i then F i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,ne_of_lt h,not_lt_of_ge h.le]
    · subst j; simp
    · simp [h,ne_of_gt h,not_lt_of_ge h.le]
  calc
    (∑ i,∑ j,F i j) = ∑ i,∑ j,
        ((if i=j then F i i else 0)+(if i < j then F i j else 0)+(if j < i then F i j else 0)) := by
          apply sum_congr rfl; intro i hi; apply sum_congr rfl; intro j hj; exact hsplit i j
    _ = (∑ i,F i i)+(∑ i,∑ j,if i < j then F i j else 0)+
        (∑ i,∑ j,if i < j then F j i else 0) := by
      simp only [sum_add_distrib]
      rw [sum_comm (f := fun i j : Fin N => if j < i then F i j else 0)]
      simp
    _ = _ := by
      simp only [upperPairs,sum_filter,Fintype.sum_prod_type]
      rw [add_assoc,←sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro j hj
      split_ifs <;> ring

def diagonal {N : ℕ} (G : Fin N × Fin N → ℝ) : ℝ :=
  (∑ i,G (i,i))/sqrt (2*(N:ℝ))

def hamiltonian {N : ℕ} (G : Fin N × Fin N → ℝ) (σ : Fin N → Bool) : ℝ :=
  (∑ i,∑ j,G (i,j)*spinSign (σ i)*spinSign (σ j))/sqrt (2*(N:ℝ))

theorem hamiltonian_split {N : ℕ} (hN : 0<N) (G : Fin N × Fin N → ℝ) (σ : Fin N → Bool) :
    hamiltonian G σ =
      (∑ e∈(univ : Finset (Fin N)).powersetCard 2,
        SpinGlass.Disorder.pureScale N 2 1 * coupling G e * edgeCharacter id σ e) + diagonal G := by
  have hnr : (0:ℝ)<N := by exact_mod_cast hN
  have hsN : sqrt (N:ℝ) ≠ 0 := (sqrt_pos.mpr hnr).ne'
  have hs2 : sqrt (2:ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  unfold hamiltonian
  rw [ordered_sum,add_div,←upperPairs_image,sum_image (pairEdge_injOn N)]
  have hd : (∑ i,G (i,i)*spinSign (σ i)*spinSign (σ i)) = ∑ i,G (i,i) := by
    apply sum_congr rfl; intro i hi
    rw [mul_assoc,←pow_two,spinSign_sq,mul_one]
  rw [hd]
  have heq :
      (∑ q∈upperPairs N,
        (G (q.1,q.2)*spinSign (σ q.1)*spinSign (σ q.2)+
         G (q.2,q.1)*spinSign (σ q.2)*spinSign (σ q.1))) / sqrt (2*(N:ℝ)) =
      ∑ q∈upperPairs N,
        SpinGlass.Disorder.pureScale N 2 1*coupling G (pairEdge q)*edgeCharacter id σ (pairEdge q) := by
    rw [sum_div]
    apply sum_congr rfl
    intro q hq
    have hn : q.1≠q.2 := ne_of_lt (mem_filter.mp hq).2
    rw [coupling_pair G hq]
    simp only [SpinGlass.Disorder.pureScale,show 2-1=1 by omega,pow_one,
      edgeCharacter,id_eq,pairEdge,prod_pair hn,sqrt_mul (by norm_num : (0:ℝ)≤2)]
    field_simp [hsN,hs2]
  rw [heq]
  unfold diagonal
  ring

/-- Ordered model with the probability measure, rather than counting measure, on spins. -/
def probabilityPartition {N : ℕ} (β : ℝ) (G : Fin N × Fin N → ℝ) : ℝ :=
  ((2:ℝ)^N)⁻¹ * ∑ σ : Fin N → Bool,exp (β*hamiltonian G σ)

theorem partition_reduction {N : ℕ} (hN : 0<N) (β : ℝ) (G : Fin N × Fin N → ℝ) :
    probabilityPartition β G = ((2:ℝ)^N)⁻¹ * exp (β*diagonal G) *
      SpinGlass.Partition.partitionFunction id ((univ : Finset (Fin N)).powersetCard 2)
        (fun e => SpinGlass.Disorder.pureScale N 2 β*coupling G e) := by
  unfold probabilityPartition SpinGlass.Partition.partitionFunction
  have he (σ : Fin N → Bool) :
      β*hamiltonian G σ = β*diagonal G+
        ∑ e∈(univ : Finset (Fin N)).powersetCard 2,
          (SpinGlass.Disorder.pureScale N 2 β*coupling G e)*edgeCharacter id σ e := by
    rw [hamiltonian_split hN,mul_add,mul_sum]
    have hs : ∀ e : Finset (Fin N),
        β*(SpinGlass.Disorder.pureScale N 2 1*coupling G e*edgeCharacter id σ e) =
        (SpinGlass.Disorder.pureScale N 2 β*coupling G e)*edgeCharacter id σ e := by
      intro e
      unfold SpinGlass.Disorder.pureScale
      ring
    simp_rw [hs]
    ring
  simp_rw [he,exp_add]
  rw [←mul_sum]
  ring

theorem log_partition_reduction {N : ℕ} (hN : 0<N) (β : ℝ) (G : Fin N × Fin N → ℝ) :
    log (probabilityPartition β G) =
      SpinGlass.CountingReduction.targetLog 2 N β (coupling G) - N*log 2 + β*diagonal G := by
  rw [partition_reduction hN,log_mul,log_mul,log_inv,log_pow,log_exp]
  · unfold SpinGlass.CountingReduction.targetLog
    ring
  · positivity
  · exact (exp_pos _).ne'
  · positivity
  · exact (SpinGlass.Partition.partition_pos _ _ _).ne'

theorem logarithmic_error_preserved {N : ℕ} (hN : 0<N) (β F : ℝ) (G : Fin N × Fin N → ℝ) :
    |(F-N*log 2+β*diagonal G)-log (probabilityPartition β G)| =
      |F-SpinGlass.CountingReduction.targetLog 2 N β (coupling G)| := by
  rw [log_partition_reduction hN]
  congr 1
  ring

end SpinGlass.OrderedSK
