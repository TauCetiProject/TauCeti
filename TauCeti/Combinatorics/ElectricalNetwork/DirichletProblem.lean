/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ElectricalNetwork.Harmonic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The Dirichlet problem on a finite electrical network

Boundary values extend uniquely to a potential harmonic at the remaining vertices whenever the
boundary meets every connected component. The maximum principle gives a trivial kernel for the
linear system with boundary values and interior net currents as its coordinates. Since the system
is square, arbitrary boundary data with zero interior currents have a solution.

## References

* D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., Proposition 9.1 and
  Remark 9.3.
* R. Lyons and Y. Peres, *Probability on Trees and Networks*, §2.1.
-/

public section

namespace TauCeti.ElectricalNetwork

variable {V : Type*} [Fintype V]

/-- Read the potential on the boundary and the net inward current in the interior. -/
private noncomputable def dirichletSystem (N : ElectricalNetwork V) (B : Set V) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  let ev : V → (V → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj
  exact LinearMap.pi fun x => if x ∈ B then ev x else ∑ y, N.cond x y • (ev y - ev x)

variable (N : ElectricalNetwork V)

private theorem dirichletSystem_eq_indicator_iff (B : Set V) (f φ : V → ℝ) :
    dirichletSystem N B f = B.indicator φ ↔ Set.EqOn f φ B ∧ ∀ x ∉ B, N.HarmonicAt f x := by
  classical
  have row (x : V) : dirichletSystem N B f x = B.indicator φ x ↔
      (x ∈ B → f x = φ x) ∧ (x ∉ B → N.HarmonicAt f x) := by
    by_cases hx : x ∈ B <;> simp [dirichletSystem, hx, LinearMap.sum_apply, harmonicAt_def]
  simp [funext_iff, row, forall_and, Set.EqOn]

/-- **The Dirichlet problem.** If every vertex can reach the boundary, any prescribed boundary
values extend uniquely to a potential harmonic off the boundary. In particular this applies to
every nonempty boundary in a connected network. -/
theorem existsUnique_harmonicAt {B : Set V} (hB : ∀ v, ∃ b ∈ B, N.graph.Reachable v b)
    (φ : V → ℝ) : ∃! f : V → ℝ, Set.EqOn f φ B ∧ ∀ x ∉ B, N.HarmonicAt f x := by
  have hinj : Function.Injective (dirichletSystem N B) := by
    apply LinearMap.ker_eq_bot.mp
    refine LinearMap.ker_eq_bot'.mpr fun f hf => ?_
    obtain ⟨hb, hi⟩ := (dirichletSystem_eq_indicator_iff N B f 0).mp (by simpa using hf)
    funext x
    obtain ⟨b, hbB, hupper⟩ := N.exists_mem_le_of_harmonicAt hB hi x
    obtain ⟨c, hcB, hlower⟩ := N.exists_mem_le_of_harmonicAt hB (fun v hv => (hi v hv).neg) x
    exact le_antisymm (hupper.trans_eq (hb hbB)) (by simpa [hb hcB] using hlower)
  have hbij : Function.Bijective (dirichletSystem N B) :=
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  exact (existsUnique_congr (dirichletSystem_eq_indicator_iff N B · φ)).mp
    (hbij.existsUnique (B.indicator φ))

end TauCeti.ElectricalNetwork
