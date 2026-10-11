/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Defs
public import TauCeti.Algebra.Homology.DG.Module.Right.Hom.Basic

/-!
# Morphisms of differential graded bimodules

Degree-zero closed bimodule maps are the left-equivariant submodule of the existing DG right
module maps. This presentation reuses their grading, differential compatibility, and pointwise
module structure. Forgetting left equivariance is the submodule inclusion; no second copy of
an underlying map or its chain-map laws is stored. Identity and composition preserve both
actions, giving the maps needed for functorial tensor composition of bimodules.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
-/

public section

namespace TauCeti

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [Module A M] [Module Bᵐᵒᵖ M]
  [IsScalarTower R A M] [IsScalarTower R Bᵐᵒᵖ M] [SMulCommClass A Bᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
  [AddCommGroup P] [Module R P] [Module A P] [Module Bᵐᵒᵖ P]
  [IsScalarTower R A P] [IsScalarTower R Bᵐᵒᵖ P] [SMulCommClass A Bᵐᵒᵖ P]
  {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {ℳP : ℤ → Submodule R P}
  [DirectSum.Decomposition ℳ] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition ℳP]
  [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 𝒩] [SetLike.GradedSMul 𝒜 ℳP]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳP]
  {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P}

/-- The submodule of DG right-module maps that also preserve the left action. -/
def dgBimoduleHomSubmodule (hM : IsDGBimodule hA hB ℳ dM) (hN : IsDGBimodule hA hB 𝒩 dN) :
    Submodule R (DGRightModuleHom hM.isDGRightModule hN.isDGRightModule) where
  carrier := {f | ∀ a : A, ∀ x : M, f (a • x) = a • f x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a x
    simp only [DGRightModuleHom.add_apply, smul_add]
    rw [hf a x, hg a x]
  smul_mem' := by
    intro r f hf a x
    rw [DGRightModuleHom.smul_apply, hf a x, DGRightModuleHom.smul_apply, smul_comm a r]

/-- Membership in the bimodule-map submodule is left equivariance; right equivariance,
grade preservation, and differential compatibility are already built into the ambient space. -/
@[simp]
theorem mem_dgBimoduleHomSubmodule (hM : IsDGBimodule hA hB ℳ dM)
    (hN : IsDGBimodule hA hB 𝒩 dN)
    (f : DGRightModuleHom hM.isDGRightModule hN.isDGRightModule) :
    f ∈ dgBimoduleHomSubmodule hM hN ↔ ∀ a : A, ∀ x : M, f (a • x) = a • f x :=
  (Iff.rfl)

/-- A degree-zero closed morphism of DG `(A, B)`-bimodules. -/
abbrev DGBimoduleHom (hM : IsDGBimodule hA hB ℳ dM) (hN : IsDGBimodule hA hB 𝒩 dN) :=
  ↥(dgBimoduleHomSubmodule hM hN)

namespace DGBimoduleHom

variable {hM : IsDGBimodule hA hB ℳ dM} {hN : IsDGBimodule hA hB 𝒩 dN}
  {hP : IsDGBimodule hA hB ℳP dP}

instance : FunLike (DGBimoduleHom hM hN) M N where
  coe f := f.val
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

instance : GradedFunLike (DGBimoduleHom hM hN) ℳ 𝒩 where
  map_mem f := f.val.map_mem'

instance : LinearMapClass (DGBimoduleHom hM hN) Bᵐᵒᵖ M N where
  map_add f := map_add f.val
  map_smulₛₗ f := map_smul f.val

@[simp]
theorem coe_val (f : DGBimoduleHom hM hN) : ⇑f.val = f := (rfl)

/-- Bimodule morphisms are determined by their values on elements. -/
@[ext]
theorem ext {f g : DGBimoduleHom hM hN} (hfg : ∀ x, f x = g x) : f = g :=
  Subtype.ext (DGRightModuleHom.ext hfg)

/-- A bimodule morphism preserves the left action. -/
@[simp]
theorem map_smul_left (f : DGBimoduleHom hM hN) (a : A) (x : M) :
    f (a • x) = a • f x :=
  (mem_dgBimoduleHomSubmodule hM hN f.val).mp f.property a x

/-- A bimodule morphism commutes with the differential. -/
@[simp]
theorem map_d (f : DGBimoduleHom hM hN) (x : M) : dN (f x) = f (dM x) :=
  f.val.map_d x

@[simp]
theorem zero_apply (x : M) : (0 : DGBimoduleHom hM hN) x = 0 := (rfl)

@[simp]
theorem add_apply (f g : DGBimoduleHom hM hN) (x : M) : (f + g) x = f x + g x := (rfl)

@[simp]
theorem smul_apply (r : R) (f : DGBimoduleHom hM hN) (x : M) : (r • f) x = r • f x := (rfl)

@[simp]
theorem neg_apply (f : DGBimoduleHom hM hN) (x : M) : (-f) x = -f x := (rfl)

@[simp]
theorem sub_apply (f g : DGBimoduleHom hM hN) (x : M) : (f - g) x = f x - g x := (rfl)

/-- The identity bimodule morphism. -/
protected def id (hM : IsDGBimodule hA hB ℳ dM) : DGBimoduleHom hM hM :=
  ⟨DGRightModuleHom.id hM.isDGRightModule, by simp⟩

@[simp]
theorem id_val (hM : IsDGBimodule hA hB ℳ dM) :
    (DGBimoduleHom.id hM).val = DGRightModuleHom.id hM.isDGRightModule := (rfl)

@[simp]
theorem id_apply (hM : IsDGBimodule hA hB ℳ dM) (x : M) : DGBimoduleHom.id hM x = x :=
  DGRightModuleHom.id_apply hM.isDGRightModule x

/-- Composition of degree-zero closed bimodule maps. -/
def comp (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) : DGBimoduleHom hM hP :=
  ⟨g.val.comp f.val, by simp⟩

@[simp]
theorem comp_val (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) :
    (g.comp f).val = g.val.comp f.val := (rfl)

@[simp]
theorem comp_apply (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) (x : M) :
    g.comp f x = g (f x) :=
  DGRightModuleHom.comp_apply g.val f.val x

@[simp]
theorem comp_id (f : DGBimoduleHom hM hN) : f.comp (DGBimoduleHom.id hM) = f := by
  ext x
  simp

@[simp]
theorem id_comp (f : DGBimoduleHom hM hN) : (DGBimoduleHom.id hN).comp f = f := by
  ext x
  simp

/-- Composition of degree-zero closed bimodule morphisms is associative. -/
@[simp]
theorem comp_assoc {Q : Type*} [AddCommGroup Q] [Module R Q] [Module A Q] [Module Bᵐᵒᵖ Q]
    [IsScalarTower R A Q] [IsScalarTower R Bᵐᵒᵖ Q] [SMulCommClass A Bᵐᵒᵖ Q]
    {ℳQ : ℤ → Submodule R Q} [DirectSum.Decomposition ℳQ] [SetLike.GradedSMul 𝒜 ℳQ]
    [SetLike.GradedSMul (InternalGrading.ofDecomposition ℬ).opposite.piece ℳQ]
    {dQ : Q →ₗ[R] Q} {hQ : IsDGBimodule hA hB ℳQ dQ}
    (k : DGBimoduleHom hP hQ) (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) :
    (k.comp g).comp f = k.comp (g.comp f) := by
  ext x
  simp

/-- Bimodule composition is linear in the morphism applied last. -/
@[simp]
theorem add_comp (g g' : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) :
    (g + g').comp f = g.comp f + g'.comp f := by
  ext x
  simp

/-- Bimodule composition is linear in the morphism applied first. -/
@[simp]
theorem comp_add (g : DGBimoduleHom hN hP) (f f' : DGBimoduleHom hM hN) :
    g.comp (f + f') = g.comp f + g.comp f' := by
  ext x
  simp

/-- Scaling the last morphism scales the composite. -/
@[simp]
theorem smul_comp (r : R) (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) :
    (r • g).comp f = r • g.comp f := by
  ext x
  simp

/-- Scaling the first morphism scales the composite. -/
@[simp]
theorem comp_smul (r : R) (g : DGBimoduleHom hN hP) (f : DGBimoduleHom hM hN) :
    g.comp (r • f) = r • g.comp f := by
  ext x
  simp only [comp_apply, smul_apply]
  exact g.val.toLinearMap.map_smul_of_tower r (f x)

@[simp]
theorem zero_comp (f : DGBimoduleHom hM hN) : (0 : DGBimoduleHom hN hP).comp f = 0 := by
  ext x
  simp

@[simp]
theorem comp_zero (g : DGBimoduleHom hN hP) : g.comp (0 : DGBimoduleHom hM hN) = 0 := by
  ext x
  simp

end DGBimoduleHom

end TauCeti
