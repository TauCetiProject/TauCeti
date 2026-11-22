/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
import TauCeti.LinearAlgebra.Dual.Annihilator

/-!
# The dual representation on annihilators of invariant submodules

For a `G`-stable submodule `W`, the annihilator `W⁰` of linear forms vanishing on `W` is stable
under the dual representation. An element `g` moving every vector by an element of `W`,
`ρ g v - v ∈ W`, fixes `W⁰` pointwise. Under the identification `(V ⧸ W)* ≃ W⁰`, the dual
representation on `W⁰` is the dual of the quotient representation on `V ⧸ W`. For the adjoint
representation of a Lie group and the Lie algebra of a closed normal subgroup this is the
coadjoint action on the annihilator used in reduction in stages.

## Main results

* `Representation.dualAnnihilator_le_comap_dual`: if `W` is stable under `ρ g⁻¹`, its annihilator
  is stable under `ρ.dual g`.
* `Representation.dual_apply_eq_self_of_mem_dualAnnihilator`: an element moving every vector by
  an element of `W` fixes the annihilator `W⁰` pointwise.
* `Representation.dualQuotEquivDualAnnihilator_symm_dual_apply`: under `(V ⧸ W)* ≃ W⁰`, the dual
  representation on `W⁰` is the dual of the quotient representation on `V ⧸ W`.
-/

public section

namespace Representation

variable {k G V : Type*} [Group G]

/-- **The annihilator of an invariant submodule is invariant.** If `W` is stable under `ρ g⁻¹`,
its dual annihilator `W⁰` is stable under `ρ.dual g`, since `(ρ.dual g φ) w = φ (ρ g⁻¹ w)` vanishes
for `w ∈ W`. -/
theorem dualAnnihilator_le_comap_dual [CommSemiring k] [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) {W : Submodule k V} {g : G} (hW : W ≤ W.comap (ρ g⁻¹)) :
    W.dualAnnihilator ≤ W.dualAnnihilator.comap (ρ.dual g) := by
  rw [← Submodule.map_le_iff_le_comap, dual_apply, ← LinearMap.dualMap_def]
  exact (W.dualAnnihilator_map_dualMap_le (ρ g⁻¹)).trans (Submodule.dualAnnihilator_anti hW)

variable [CommRing k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}
  {W : Submodule k V} {g : G}

/-- An element `g` that moves every vector by an element of `W`, `ρ g v - v ∈ W`, fixes every
linear form vanishing on `W` under the dual representation. No invariance of `W` is needed. -/
theorem dual_apply_eq_self_of_mem_dualAnnihilator (hg : ∀ v, ρ g v - v ∈ W)
    {φ : Module.Dual k V} (hφ : φ ∈ W.dualAnnihilator) : ρ.dual g φ = φ := by
  ext v
  -- `φ` takes the same value at `v = ρ g (ρ g⁻¹ v)` and at `ρ g⁻¹ v`.
  have h := (Submodule.mem_dualAnnihilator φ).1 hφ _ (hg (ρ g⁻¹ v))
  rw [map_sub, self_inv_apply, sub_eq_zero] at h
  simp [Module.Dual.transpose_apply, ← h]

/-- **The dual of a quotient representation is the dual representation on the annihilator.** Under
the identification `(V ⧸ W)* ≃ W⁰` of `Submodule.dualQuotEquivDualAnnihilator`, the translate
`ρ.dual g φ` of `φ ∈ W⁰` corresponds to the translate under the dual of the quotient representation
on `V ⧸ W`. -/
theorem dualQuotEquivDualAnnihilator_symm_dual_apply (hW : ∀ g, W ≤ W.comap (ρ g)) (g : G)
    {φ : Module.Dual k V} (hφ : φ ∈ W.dualAnnihilator) :
    W.dualQuotEquivDualAnnihilator.symm
        ⟨ρ.dual g φ, ρ.dualAnnihilator_le_comap_dual (hW g⁻¹) hφ⟩ =
      (ρ.quotient W hW).dual g (W.dualQuotEquivDualAnnihilator.symm ⟨φ, hφ⟩) := by
  ext v
  simp [Module.Dual.transpose_apply]

end Representation
