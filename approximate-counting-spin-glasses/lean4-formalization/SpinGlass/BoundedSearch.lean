import SpinGlass.CutoffSelection

/-! A literal bounded scan, with correctness, minimality, and evaluation count. -/

namespace SpinGlass.BoundedSearch

structure Result where
  found : Option ℕ
  evaluations : ℕ

def scan (test : ℕ → Bool) (start : ℕ) : ℕ → Result
  | 0 => ⟨none, 0⟩
  | fuel+1 => if test start then ⟨some start, 1⟩ else
      let rest := scan test (start+1) fuel
      ⟨rest.found, rest.evaluations+1⟩

theorem evaluations_le (test : ℕ → Bool) (start fuel : ℕ) :
    (scan test start fuel).evaluations ≤ fuel := by
  induction fuel generalizing start with
  | zero => simp [scan]
  | succ fuel ih =>
    simp only [scan]
    split
    · simp
    · exact Nat.add_le_add_right (ih (start+1)) 1

theorem found_spec (test : ℕ → Bool) {start fuel m : ℕ}
    (h : (scan test start fuel).found = some m) :
    start ≤ m ∧ m < start+fuel ∧ test m = true ∧
      ∀ j, start ≤ j → j < m → test j = false := by
  induction fuel generalizing start with
  | zero => simp [scan] at h
  | succ fuel ih =>
    simp only [scan] at h
    split at h
    next ht =>
      simp only [Option.some.injEq] at h
      subst m
      exact ⟨le_rfl, by omega, ht, fun j hj hjm => by omega⟩
    next ht =>
      obtain ⟨hs, hm, htest, hprev⟩ := ih h
      refine ⟨by omega, by omega, htest, ?_⟩
      intro j hj hjm
      by_cases heq : j = start
      · subst j
        simpa using ht
      · exact hprev j (by omega) hjm

theorem found_complete (test : ℕ → Bool) {start fuel : ℕ}
    (hex : ∃ j, start ≤ j ∧ j < start+fuel ∧ test j = true) :
    ∃ m, (scan test start fuel).found = some m := by
  induction fuel generalizing start with
  | zero => obtain ⟨j, hj, hj', _⟩ := hex; omega
  | succ fuel ih =>
    simp only [scan]
    split
    next ht => exact ⟨start, rfl⟩
    next ht =>
      obtain ⟨j, hj, hj', htest⟩ := hex
      have hne : j ≠ start := by intro heq; subst j; contradiction
      exact ih ⟨j, by omega, by omega, htest⟩

noncomputable section
open SpinGlass.CutoffTail SpinGlass.CutoffSelection

def cutoffScan (kap a alpha : ℝ) (N : ℕ) (Lambda : ℝ) : Result :=
  scan (fun m => decide (Lambda ≤ phi kap a N m)) 1 (Nat.floor (alpha*N))

theorem cutoffScan_correct {kap a alpha omega Lambda : ℝ} {N : ℕ}
    (hkap : 0 < kap) (ha : 0 < a) (halpha : 0 < alpha)
    (hgap : 2 ≤ kap * (Real.log (1/(a*alpha))-1))
    (hN : 2/alpha ≤ (N : ℝ)) (hLam : 0 < Lambda)
    (hsmall : Lambda < nu kap a alpha omega * N) :
    ∃ m, (cutoffScan kap a alpha N Lambda).found = some m ∧
      1 ≤ m ∧ m ≤ Nat.floor (alpha*N) ∧ Lambda ≤ phi kap a N m ∧
        ∀ j : ℕ, 1 ≤ j → j < m → phi kap a N j < Lambda := by
  obtain ⟨m, hm1, hmf, hmPhi, _⟩ := exists_first_omitted hkap ha halpha hgap hN hLam hsmall
  obtain ⟨found, hfound⟩ := found_complete (start := 1) (fuel := Nat.floor (alpha*N))
    (fun m => decide (Lambda ≤ phi kap a N m))
    ⟨m, hm1, by omega, by simpa using hmPhi⟩
  obtain ⟨hs, hf, ht, hp⟩ := found_spec _ hfound
  refine ⟨found, hfound, hs, by omega, by simpa using ht, ?_⟩
  intro j hj hjf
  simpa using hp j hj hjf

theorem cutoffScan_evaluations {kap a alpha Lambda : ℝ} {N : ℕ}
    (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1) :
    (cutoffScan kap a alpha N Lambda).evaluations ≤ N := by
  apply (evaluations_le _ _ _).trans
  have hf : (Nat.floor (alpha*N) : ℝ) ≤ alpha*N := Nat.floor_le (by positivity)
  have h : alpha*(N : ℝ) ≤ N := by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  exact_mod_cast hf.trans h

end
end SpinGlass.BoundedSearch
