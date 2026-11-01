/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Pivotal
public import TauCeti.QuantumGroups.UqSl2.Antipode

/-!
# The pivotal category of finite-dimensional `U_q(sl₂)`-modules

For every nonzero parameter `q`, the antipode of `UqSl2 q` is bijective, so its finite-dimensional
modules have inverse-antipode left duals and antipode right duals. The group-like element `K⁻¹`
implements the square of the antipode. It therefore supplies the pivotal isomorphism
`j_V(v)(φ) = φ(K⁻¹ v)`.

The named structures `finiteModuleRigidCategory` and `finiteModulePivotalCategory` are installed
locally, retaining the inverse-antipode duals of the general finite Hopf module construction.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for pivotal
  structures on modules over a Hopf algebra.
* A. Virelizier, *Quantum groups*, Section 2.3, for the rank-one Hopf convention.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.UqSl2

variable (q : ℂ) [Fact (q ≠ 0)]

/-- The group-like element `K⁻¹`, whose conjugation implements the square of the antipode. -/
def pivotalElement : GroupLike ℂ (UqSl2 q) :=
  ⟨kInv q, counit_kInv q, comul_kInv q⟩

/-- The pivotal element is the inverse Cartan generator. -/
@[simp]
theorem pivotalElement_val : (pivotalElement q : UqSl2 q) = kInv q := (rfl)

/-- Finite-dimensional `U_q(sl₂)`-modules with their inverse-antipode left duals and
antipode right duals. -/
-- Expose the structure so public elementwise equations retain the canonical contragredient
-- right-dual carriers; instance reducibility alone does not identify those carriers.
@[expose, instance_reducible]
def finiteModuleRigidCategory : RigidCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) :=
  FiniteHopfModuleCat.rigidCategory (antipode_bijective q)

/-- The pivotal structure with pivot `K⁻¹` on finite-dimensional `U_q(sl₂)`-modules. -/
@[instance_reducible]
def finiteModulePivotalCategory :
    letI := finiteModuleRigidCategory q
    PivotalCategory (FiniteHopfModuleCat ℂ (UqSl2 q)) :=
  FiniteHopfModuleCat.pivotalCategory (antipode_bijective q)
    (pivotalElement q) (fun x => by simpa using antipode_antipode q x)

/-- The named pivotal structure specializes the group-like pivot construction at `K⁻¹`.
This equation transports results about that construction to the named structure. -/
theorem finiteModulePivotalCategory_def :
    letI := finiteModuleRigidCategory q
    finiteModulePivotalCategory q =
      FiniteHopfModuleCat.pivotalCategory (antipode_bijective q)
        (pivotalElement q) (fun x => by simpa using antipode_antipode q x) :=
  (rfl)

-- Keep this as a named rewrite: the generic rule simplifies it here, but does not match through
-- the opaque pivotal structure during ordinary importing simplification.
/-- The pivotal isomorphism evaluates a dual vector after the action of `K⁻¹`. -/
theorem dualEquiv_pivotalIsoApp_hom_apply (M : FiniteHopfModuleCat ℂ (UqSl2 q))
    (m : M) (φ : (Mᘁ : FiniteHopfModuleCat ℂ (UqSl2 q))) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    BialgebraModule.dualEquiv ℂ (UqSl2 q) (Mᘁ : FiniteHopfModuleCat ℂ (UqSl2 q))
      ((pivotalIsoApp M).hom.hom.hom m) φ =
        BialgebraModule.dualEquiv ℂ (UqSl2 q) M φ (kInv q • m) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  exact FiniteHopfModuleCat.dualEquiv_pivotalIsoApp_hom_apply _ _ _ M m φ

end TauCeti.UqSl2
