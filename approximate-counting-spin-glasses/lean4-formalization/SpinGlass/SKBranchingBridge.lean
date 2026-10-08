import SpinGlass.SKBranchingMass
import SpinGlass.SKComponents

/-! Exact identification of the analytic and algorithmic branching-set definitions. -/
namespace SpinGlass.SKBranching
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem branchVertices_eq_branch (Γ : Finset (Finset V)) :
    SpinGlass.SKComponents.branchVertices id Γ = SpinGlass.Hypergraph.branch Γ := by
  ext v
  rw [mem_branch_iff_degree]
  simp only [SpinGlass.SKComponents.branchVertices, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rfl

end SpinGlass.SKBranching
