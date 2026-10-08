import SpinGlass.OrderedSK

/-! Explicit quadratic preprocessing of the ordered SK matrix. Every ordered
matrix position is inspected once; only strictly upper pairs are returned. -/
noncomputable section
namespace SpinGlass.OrderedSKPreparation
open SpinGlass.ArithmeticEvaluation SpinGlass.InputPreparation
open scoped BigOperators

structure PairArray (N : ℕ) where
  entries : List ((Fin N × Fin N) × ℝ)
  operations : ℕ

def pairAverage {N : ℕ} (G : Fin N × Fin N → ℝ) (s : ℝ) (q : Fin N × Fin N) : Computation :=
  divide (add (literal (G q)) (literal (G (q.2,q.1)))) (literal s)

@[simp] theorem pairAverage_operations {N : ℕ} (G : Fin N × Fin N → ℝ) (s : ℝ) (q : Fin N × Fin N) :
    (pairAverage G s q).operations=2 := rfl

/-- Every node charges its order test and iterator check. Accepted nodes also
charge two scalar operations and storage of the pair and its value. -/
def pairLoop {N : ℕ} (G : Fin N × Fin N → ℝ) (s : ℝ) : List (Fin N × Fin N) → PairArray N
  | [] => ⟨[],1⟩
  | q::qs =>
      let tail := pairLoop G s qs
      if q.1 < q.2 then
        let x := pairAverage G s q
        ⟨(q,x.value)::tail.entries,tail.operations+x.operations+4⟩
      else ⟨tail.entries,tail.operations+2⟩

theorem pairLoop_entries {N : ℕ} (G : Fin N × Fin N → ℝ) (s : ℝ) (qs : List (Fin N × Fin N)) :
    (pairLoop G s qs).entries = (qs.filter (fun q => decide (q.1 < q.2))).map
      (fun q => (q,(G q+G (q.2,q.1))/s)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    by_cases h : q.1 < q.2 <;> simp [pairLoop,h,ih,pairAverage,add,divide,literal]

theorem pairLoop_operations {N : ℕ} (G : Fin N × Fin N → ℝ) (s : ℝ) (qs : List (Fin N × Fin N)) :
    (pairLoop G s qs).operations ≤ 6*qs.length+1 := by
  induction qs with
  | nil => simp [pairLoop]
  | cons q qs ih =>
    simp only [pairLoop,List.length_cons]
    split_ifs <;> simp only [pairAverage_operations] <;> omega

/-- Row-major pair generation: one inner list per row, then append into the schedule. -/
def pairSchedule (N : ℕ) : List (Fin N × Fin N) :=
  (Finset.univ : Finset (Fin N)).toList.flatMap (fun i =>
    (Finset.univ : Finset (Fin N)).toList.map (fun j => (i,j)))

@[simp] theorem pairSchedule_length (N : ℕ) : (pairSchedule N).length=N^2 := by
  simp [pairSchedule,List.length_flatMap,pow_two]

theorem pairSchedule_mem (N : ℕ) (q : Fin N × Fin N) : q∈pairSchedule N := by
  rcases q with ⟨i,j⟩
  simp [pairSchedule]

theorem pairSchedule_nodup (N : ℕ) : (pairSchedule N).Nodup := by
  exact (Finset.univ.nodup_toList).product (Finset.univ.nodup_toList)

/-- Generator work counted recursively in the actual row schedule. -/
def rowWork {α : Type*} (columns : List α) : List α → ℕ
  | [] => 1
  | _::rows => rowWork columns rows+2*columns.length+2

theorem rowWork_exact {α : Type*} (columns rows : List α) :
    rowWork columns rows = rows.length*(2*columns.length+2)+1 := by
  induction rows with
  | nil => simp [rowWork]
  | cons i rows ih => simp [rowWork,ih]; ring

structure Prepared (N : ℕ) where
  entries : List ((Fin N × Fin N) × ℝ)
  diagonal : ℝ
  operations : ℕ

def prepare {N : ℕ} (G : Fin N × Fin N → ℝ) : Prepared N :=
  let s := squareRoot (literal 2)
  let denom := squareRoot (mul (literal 2) (literal N))
  let pairs := pairLoop G s.value (pairSchedule N)
  let diag := divide (sumFinset Finset.univ (fun i : Fin N => literal (G (i,i)))) (literal denom.value)
  ⟨pairs.entries,diag.value,s.operations+denom.operations+pairs.operations+diag.operations+
    rowWork (Finset.univ : Finset (Fin N)).toList (Finset.univ : Finset (Fin N)).toList+2*N+3⟩

@[simp] theorem prepare_diagonal {N : ℕ} (G : Fin N × Fin N → ℝ) :
    (prepare G).diagonal=OrderedSK.diagonal G := by
  simp [prepare,divide,squareRoot,mul,literal,OrderedSK.diagonal]

/-- Every returned entry is the exact transformed coupling and each upper pair appears. -/
theorem prepare_entry {N : ℕ} (G : Fin N × Fin N → ℝ) (q : Fin N × Fin N) (x : ℝ) :
    (q,x)∈(prepare G).entries ↔ q.1 < q.2 ∧ x=OrderedSK.coupling G (OrderedSK.pairEdge q) := by
  simp only [prepare,pairLoop_entries,squareRoot,literal,List.mem_map,List.mem_filter,
    decide_eq_true_eq,Prod.mk.injEq,exists_eq_left,pairSchedule_mem,true_and]
  by_cases h : q.1 < q.2
  · rw [OrderedSK.coupling_pair G (by simpa [OrderedSK.upperPairs] using h)]
    simp [h,eq_comm]
  · simp [h]

/-- The transformation charges arithmetic, comparisons, generation, and storage;
its cost is quadratic for every finite real ordered matrix. -/
theorem prepare_operations {N : ℕ} (hN : 0<N) (G : Fin N × Fin N → ℝ) :
    (prepare G).operations ≤ 30*N^2 := by
  have hp := pairLoop_operations G (Real.sqrt 2) (pairSchedule N)
  rw [pairSchedule_length] at hp
  simp only [prepare,squareRoot,literal,mul,divide,sumFinset_operations,
    Finset.sum_const_zero,Finset.card_univ,Fintype.card_fin,rowWork_exact,Finset.length_toList]
  have hh : 1≤N^2 := Nat.one_le_pow _ _ hN
  nlinarith

/-- No coupling is recomputed or stored twice: the cached pair keys are unique. -/
theorem prepare_keys_nodup {N : ℕ} (G : Fin N × Fin N → ℝ) :
    ((prepare G).entries.map Prod.fst).Nodup := by
  simp only [prepare,pairLoop_entries,List.map_map,Function.comp_def]
  change (List.map id ((pairSchedule N).filter (fun q => decide (q.1 < q.2)))).Nodup
  rw [List.map_id]
  exact (pairSchedule_nodup N).filter _

/-- The final output correction uses the cached diagonal and six elementary
operations, including the sign change of N. -/
def finish (N : ℕ) (β diagonal F : ℝ) : Computation :=
  add (add (literal F)
    (mul (mul (literal (-1)) (literal N)) (logarithm (literal 2))))
    (mul (literal β) (literal diagonal))

@[simp] theorem finish_value (N : ℕ) (β diagonal F : ℝ) :
    (finish N β diagonal F).value=F-(N:ℝ)*Real.log 2+β*diagonal := by
  simp [finish,add,mul,logarithm,literal]
  ring

@[simp] theorem finish_operations (N : ℕ) (β diagonal F : ℝ) :
    (finish N β diagonal F).operations=6 := rfl

/-- The efficient scan and final correction have a single quadratic total bound. -/
theorem transformation_operations {N : ℕ} (hN : 0<N) (G : Fin N × Fin N → ℝ)
    (β F : ℝ) :
    (prepare G).operations+(finish N β (prepare G).diagonal F).operations ≤ 36*N^2 := by
  have hp := prepare_operations hN G
  rw [finish_operations]
  have hh : 1≤N^2 := Nat.one_le_pow _ _ hN
  omega

/-- Executing the concrete correction preserves exactly the original error. -/
theorem finish_error {N : ℕ} (hN : 0<N) (G : Fin N × Fin N → ℝ) (β F : ℝ) :
    |(finish N β (prepare G).diagonal F).value-Real.log (OrderedSK.probabilityPartition β G)| =
      |F-CountingReduction.targetLog 2 N β (OrderedSK.coupling G)| := by
  rw [finish_value,prepare_diagonal]
  exact OrderedSK.logarithmic_error_preserved hN β F G

end SpinGlass.OrderedSKPreparation
