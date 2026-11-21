/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Unitization
public import TauCeti.RingTheory.TwoSidedIdeal.Annihilator

/-!
# Left `Unitization` module actions on two-sided ideals

Left `Unitization R A`-module structure `(r, a) • x = r • x + a * x` on `R`-invariant two-sided
ideals `I : TwoSidedIdeal A` and identification of `I.annihilator` as a pullback of
`(Module.annihilator (Unitization R A) I).toTwoSided`.
-/

public section

namespace TwoSidedIdeal

section CommSemiring

variable {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- Left `Unitization R A`-module structure `(r, a) • x = r • x + a * x` on an `R`-invariant
two-sided ideal `I : TwoSidedIdeal A`. Provided as an `@[instance_reducible]` definition taking the
scalar-absorption hypothesis explicitly rather than a global instance. -/
@[instance_reducible]
def unitizationModuleOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) : Module (Unitization R A) I :=
  (I.toSubmoduleOfSMulMem hsmul).unitizationModule I.mul_mem_left

@[simp]
theorem coe_unitizationModuleOfSMulMem_smul (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) (u : Unitization R A) (x : I) :
    (letI := I.unitizationModuleOfSMulMem hsmul; ((u • x : I) : A)) =
      u.fst • (x : A) + u.snd * (x : A) :=
  (I.toSubmoduleOfSMulMem hsmul).coe_unitizationModule_smul I.mul_mem_left u x

/-- Coercing `(r, a) • x` from `I` into `Unitization R A` agrees with multiplication in
`Unitization R A`. -/
theorem inr_coe_unitizationModuleOfSMulMem_smul (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) (u : Unitization R A) (x : I) :
    (letI := I.unitizationModuleOfSMulMem hsmul; (((u • x : I) : A) : Unitization R A)) =
      u * ((x : A) : Unitization R A) :=
  (I.toSubmoduleOfSMulMem hsmul).inr_coe_unitizationModule_smul I.mul_mem_left u x

/-- The left `Unitization R A`-module structure on an `R`-invariant two-sided ideal `I` is
compatible with any `R`-scalar action on `I` agreeing with scalar multiplication in `A`. -/
theorem isScalarTower_unitizationModuleOfSMulMem (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) [SMul R I]
    (hcoe : ∀ (r : R) (x : I), ((r • x : I) : A) = r • (x : A)) :
    letI := I.unitizationModuleOfSMulMem hsmul
    IsScalarTower R (Unitization R A) I := by
  let _ := I.unitizationModuleOfSMulMem hsmul
  have hL := (I.toSubmoduleOfSMulMem hsmul).isScalarTower_unitizationModule I.mul_mem_left
  refine ⟨fun r u x => Subtype.ext ?_⟩
  rw [hcoe]
  exact (congrArg Subtype.val (hL.smul_assoc r u x)).trans
    (Submodule.coe_smul (p := I.toSubmoduleOfSMulMem hsmul) r (u • x))

theorem mem_annihilator_unitizationOfSMulMem_iff (I : TwoSidedIdeal A)
    (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) {u : Unitization R A} :
    (letI := I.unitizationModuleOfSMulMem hsmul; u ∈ Module.annihilator (Unitization R A) I) ↔
      ∀ x ∈ I, u.fst • x + u.snd * x = 0 :=
  (I.toSubmoduleOfSMulMem hsmul).mem_annihilator_unitization_iff I.mul_mem_left

end CommSemiring

/-- For an `R`-invariant two-sided ideal `I` of a nonunital `R`-algebra `A`, `I.annihilator` is
the preimage of `(Module.annihilator (Unitization R A) I).toTwoSided` under
`Unitization.inrNonUnitalAlgHom R A`. -/
theorem annihilator_eq_comap_annihilator_unitization_of_smul_mem {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (I : TwoSidedIdeal A) (hsmul : ∀ (r : R) {x : A}, x ∈ I → r • x ∈ I) :
    letI := I.unitizationModuleOfSMulMem hsmul
    I.annihilator =
      TwoSidedIdeal.comap (Unitization.inrNonUnitalAlgHom R A)
        (Module.annihilator (Unitization R A) I).toTwoSided := by
  let _ := I.unitizationModuleOfSMulMem hsmul
  ext a
  rw [mem_annihilator, mem_comap, Ideal.mem_toTwoSided,
    I.mem_annihilator_unitizationOfSMulMem_iff hsmul]
  simp

end TwoSidedIdeal
