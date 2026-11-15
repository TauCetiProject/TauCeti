/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Analysis.Normed.Module.Quotient

/-!
# Banach norms on algebraic simple modules

Every algebraic simple module over a unital Banach algebra admits a complete norm
with contractive algebra action. No topology on the module is assumed in advance.
The norm is transported from the quotient by a maximal left ideal; maximal left
ideals are closed, so the quotient seminorm is a norm. Scalar multiplication by
the base field has its usual norm equality.

This realization allows results about simple Banach modules to be applied to
algebraic simple modules, for instance when testing the Jacobson radical through
annihilators. The construction retains the given scalar and algebra actions.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5 and §2.6.
* The algebraic realization is Mathlib's `isSimpleModule_iff_quot_maximal`;
  closedness is `Ideal.IsMaximal.isClosed`.
-/

public section

namespace IsSimpleModule

variable {𝕜 A M : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A] [AddCommGroup M] [Module A M] [Module 𝕜 M]
  [IsScalarTower 𝕜 A M]

/-- Every algebraic simple module over a Banach algebra admits a complete norm
compatible with its given vector-space structure and making the algebra action
contractive. Neither a normalized identity norm nor a topology on the module is
required. -/
theorem exists_complete_norm (h : IsSimpleModule A M) :
    ∃ p : AddGroupNorm M, letI := p.toNormedAddCommGroup
      NormSMulClass 𝕜 M ∧ CompleteSpace M ∧ IsBoundedSMul A M := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  let : I.IsMaximal := hI
  let p : AddGroupNorm M :=
    let := NormedAddCommGroup.induced M (A ⧸ I) e e.injective
    normAddGroupNorm M
  refine ⟨p, ?_⟩
  let := p.toNormedAddCommGroup
  have hp (x : M) : ‖x‖ = ‖e x‖ := rfl
  have hn : NormSMulClass 𝕜 M :=
    ⟨fun c x => by
      have he : e (c • x) = c • e x := LinearMapClass.map_smul_of_tower e c x
      rw [hp, he, norm_smul, hp]⟩
  let ei : M ≃ᵢ A ⧸ I :=
    { e.toEquiv with
      isometry_toFun := (AddMonoidHomClass.isometry_iff_norm e).mpr fun x => (hp x).symm }
  refine ⟨hn, ei.completeSpace, .of_norm_smul_le fun a x => ?_⟩
  rw [hp, e.map_smul, hp]
  exact norm_smul_le a (e x)

end IsSimpleModule
