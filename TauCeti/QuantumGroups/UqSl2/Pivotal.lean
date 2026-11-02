/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Trace
public import TauCeti.QuantumGroups.UqSl2.Antipode

/-!
# The pivotal category of finite-dimensional `U_q(sl₂)`-modules

For every nonzero parameter `q`, the antipode of `UqSl2 q` is bijective, so its finite-dimensional
modules have inverse-antipode left duals and antipode right duals. The group-like element `K⁻¹`
implements the square of the antipode. It therefore supplies the pivotal isomorphism
`j_V(v)(φ) = φ(K⁻¹ v)`.

The named structures `finiteModuleRigidCategory` and `finiteModulePivotalCategory` are installed
locally, retaining the inverse-antipode duals of the general finite Hopf module construction.
The named trace equations identify the right and left pivotal traces with ordinary linear traces
twisted by `K⁻¹` and `K`, respectively.

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

/-- The square of the antipode is conjugation by the pivotal element. -/
theorem antipode_antipode_eq_pivotalElement_mul_mul_antipode (x : UqSl2 q) :
    HopfAlgebra.antipode ℂ (HopfAlgebra.antipode ℂ x) =
      (pivotalElement q : UqSl2 q) * x *
        HopfAlgebra.antipode ℂ (pivotalElement q : UqSl2 q) := by
  simpa using antipode_antipode q x

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
    (pivotalElement q) (antipode_antipode_eq_pivotalElement_mul_mul_antipode q)

/-- The named pivotal structure specializes the group-like pivot construction at `K⁻¹`.
This equation transports results about that construction to the named structure. -/
theorem finiteModulePivotalCategory_def :
    letI := finiteModuleRigidCategory q
    finiteModulePivotalCategory q =
      FiniteHopfModuleCat.pivotalCategory (antipode_bijective q)
        (pivotalElement q) (antipode_antipode_eq_pivotalElement_mul_mul_antipode q) :=
  (rfl)

/-- The pivotal isomorphism evaluates a dual vector after the action of `K⁻¹`. -/
@[simp↓]
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

/-- For the named pivotal structure, the right trace is the ordinary trace twisted by `K⁻¹`.
This formula requires only `q ≠ 0`. -/
@[simp↓]
theorem rightTrace_apply {M : FiniteHopfModuleCat ℂ (UqSl2 q)} (f : M ⟶ M)
    (c : (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q)) : FiniteHopfModuleCat ℂ (UqSl2 q))) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    (rightTrace f).hom.hom c =
      (BialgebraModule.trivialEquiv ℂ (UqSl2 q)).symm
        (LinearMap.trace ℂ M (Algebra.lsmul ℂ ℂ M (kInv q) ∘ₗ
          f.hom.hom.restrictScalars ℂ) * BialgebraModule.trivialEquiv ℂ (UqSl2 q) c) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  rw [finiteModulePivotalCategory_def]
  simpa only [pivotalElement_val] using
    FiniteHopfModuleCat.rightTrace_apply (antipode_bijective q) (pivotalElement q)
      (antipode_antipode_eq_pivotalElement_mul_mul_antipode q) f c

/-- For the named pivotal structure, the left trace is the ordinary trace twisted by `K`.
This formula requires only `q ≠ 0`. -/
@[simp↓]
theorem leftTrace_apply {M : FiniteHopfModuleCat ℂ (UqSl2 q)} (f : M ⟶ M)
    (c : (𝟙_ (FiniteHopfModuleCat ℂ (UqSl2 q)) : FiniteHopfModuleCat ℂ (UqSl2 q))) :
    letI := finiteModuleRigidCategory q
    letI := finiteModulePivotalCategory q
    (leftTrace f).hom.hom c =
      (BialgebraModule.trivialEquiv ℂ (UqSl2 q)).symm
        (LinearMap.trace ℂ M (Algebra.lsmul ℂ ℂ M (k q) ∘ₗ
          f.hom.hom.restrictScalars ℂ) * BialgebraModule.trivialEquiv ℂ (UqSl2 q) c) := by
  let := finiteModuleRigidCategory q
  let := finiteModulePivotalCategory q
  rw [finiteModulePivotalCategory_def]
  simpa only [pivotalElement_val, antipode_kInv] using
    FiniteHopfModuleCat.leftTrace_apply (antipode_bijective q) (pivotalElement q)
      (antipode_antipode_eq_pivotalElement_mul_mul_antipode q) f c

end TauCeti.UqSl2
