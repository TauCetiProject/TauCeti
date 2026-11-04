/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Bimodule.Hom.Components

/-!
# Cohomology maps and quasi-isomorphisms of A-infinity bimodules

The unary component of a bimodule morphism preserves degree and commutes with the
unary differentials. It therefore induces a map on total cohomology. A bimodule
quasi-isomorphism is a morphism for which this map is bijective. We prove the
identity, composition and two-out-of-three laws, and construct the induced linear
equivalence on cohomology.

Cohomology and its functoriality use the square-zero-endomorphism API
`LinearMap.homologyMap`. No invertibility of the bar map is asserted: a
quasi-isomorphism need not be a bimodule isomorphism.

## References

* V. Lyubashenko and O. Manzyuk, *A-infinity-bimodules and Serre A-infinity-functors*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 4--5.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti.AInfinityBimoduleHom

universe uR uA uB uM uN uP

variable {R : Type uR} {A : Type uA} {B : Type uB}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {AA : AInfinityAlgebra R A} {BB : AInfinityAlgebra R B}
  {M : Type uM} {N : Type uN} {P : Type uP}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  {MM : AInfinityBimodule AA BB M} {NN : AInfinityBimodule AA BB N}
  {PP : AInfinityBimodule AA BB P}

/-- The unary component of a bimodule morphism, evaluated on the two empty words. -/
def linearPart (f : AInfinityBimoduleHom MM NN) : M →ₗ[R] N :=
  f.taylor ∘ₗ (TensorProduct.mk R (TensorWords R A ⊗[R] M) (TensorWords R B)).flip 1 ∘ₗ
    TensorProduct.mk R (TensorWords R A) M 1

/-- The linear part is the Taylor map on the two empty words. -/
theorem linearPart_apply (f : AInfinityBimoduleHom MM NN) (x : M) :
    f.linearPart x = f.taylor ((1 ⊗ₜ x) ⊗ₜ 1) := (rfl)

/-- The Taylor map on the two empty words is the linear part. -/
@[simp]
theorem taylor_one_tmul_tmul_one (f : AInfinityBimoduleHom MM NN) (x : M) :
    f.taylor ((1 ⊗ₜ x) ⊗ₜ 1) = f.linearPart x := (rfl)

/-- The bar map carries the two empty words to the two empty words, applying the
linear part to the module input. -/
@[simp]
theorem barMap_one_tmul_tmul_one (f : AInfinityBimoduleHom MM NN) (x : M) :
    f.barMap ((1 ⊗ₜ x) ⊗ₜ 1) = (1 ⊗ₜ f.linearPart x) ⊗ₜ 1 := by
  rw [f.barMap_eq_bicofreeLift, Comodule.bicofreeLift_toLinearMap]
  simp [Comodule.cofreeCoact_def, Comodule.leftCoactRTensor_def,
    Comodule.leftCofreeCoact_def, TensorWords.comul_eq_deconcatenation,
    TensorWords.deconcatenation_one]

/-- The linear part preserves the original, unsuspended grading. -/
theorem linearPart_mem_piece (f : AInfinityBimoduleHom MM NN) {p : ℤ} {x : M}
    (hx : x ∈ MM.grading.piece p) : f.linearPart x ∈ NN.grading.piece p := by
  rw [linearPart_apply, ← f.component_zero_zero_apply x (fun i ↦ i.elim0) (fun i ↦ i.elim0)]
  simpa only [Fin.sum_univ_zero, zero_add, add_zero, Nat.cast_zero, sub_zero] using
    f.component_mem_piece 0 0 hx (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)
      (fun i ↦ i.elim0) (fun i ↦ i.elim0) (fun i ↦ i.elim0)

/-- The linear part is homogeneous of degree zero. -/
theorem isHomogeneous_linearPart (f : AInfinityBimoduleHom MM NN) :
    LinearMap.IsHomogeneous f.linearPart MM.grading.piece NN.grading.piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ by
    simpa only [add_zero] using f.linearPart_mem_piece hx

/-- The linear part commutes with the unary differentials. -/
theorem linearPart_comp_differential (f : AInfinityBimoduleHom MM NN) :
    f.linearPart ∘ₗ MM.differential = NN.differential ∘ₗ f.linearPart := by
  ext x
  have h := LinearMap.congr_fun f.taylor_comp_barMap ((1 ⊗ₜ x) ⊗ₜ 1)
  simpa only [LinearMap.comp_apply, barMap_one_tmul_tmul_one,
    AInfinityBimodule.barDifferential_one_tmul_tmul_one, ← linearPart_apply,
    ← AInfinityBimodule.differential_apply] using h.symm

/-- The linear part carries a unary differential to the unary differential of its image. -/
@[simp]
theorem linearPart_differential (f : AInfinityBimoduleHom MM NN) (x : M) :
    f.linearPart (MM.differential x) = NN.differential (f.linearPart x) :=
  LinearMap.congr_fun f.linearPart_comp_differential x

/-- The identity has identity linear part. -/
@[simp]
theorem linearPart_id (MM : AInfinityBimodule AA BB M) :
    (AInfinityBimoduleHom.id MM).linearPart = LinearMap.id := by
  ext x
  simp only [linearPart_apply, taylor_id, AInfinityBimodule.taylorProj_tmul,
    TensorWords.counit_eq_counit, TensorWords.counit_one, one_smul, LinearMap.id_apply]

/-- Linear parts preserve composition. -/
@[simp]
theorem linearPart_comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (g.comp f).linearPart = g.linearPart ∘ₗ f.linearPart := by
  ext x
  simp only [linearPart_apply, taylor_comp, LinearMap.comp_apply, barMap_one_tmul_tmul_one]

/-- The linear part of a bimodule morphism induces a linear map on total unary cohomology. -/
def cohomologyMap (f : AInfinityBimoduleHom MM NN) : MM.Cohomology →ₗ[R] NN.Cohomology :=
  LinearMap.homologyMap f.linearPart MM.differential_comp_self_eq_zero
    NN.differential_comp_self_eq_zero f.linearPart_comp_differential

/-- On cycle representatives, the cohomology map applies the linear part. -/
@[simp]
theorem cohomologyMap_mk (f : AInfinityBimoduleHom MM NN) (x : LinearMap.ker MM.differential) :
    f.cohomologyMap (Submodule.Quotient.mk x) = Submodule.Quotient.mk
      ⟨f.linearPart x, LinearMap.map_mem_ker_of_comp_eq f.linearPart
        f.linearPart_comp_differential x.2⟩ :=
  LinearMap.homologyMap_mk _ _ _ _ _

/-- The identity induces the identity on cohomology. -/
@[simp]
theorem cohomologyMap_id (MM : AInfinityBimodule AA BB M) :
    (AInfinityBimoduleHom.id MM).cohomologyMap = LinearMap.id := by
  simp only [cohomologyMap, linearPart_id, LinearMap.homologyMap_id]

/-- The map on cohomology preserves composition. -/
@[simp]
theorem cohomologyMap_comp (g : AInfinityBimoduleHom NN PP) (f : AInfinityBimoduleHom MM NN) :
    (g.comp f).cohomologyMap = g.cohomologyMap ∘ₗ f.cohomologyMap := by
  simp only [cohomologyMap, linearPart_comp]
  exact LinearMap.homologyMap_comp g.linearPart f.linearPart _
    NN.differential_comp_self_eq_zero _ f.linearPart_comp_differential
    g.linearPart_comp_differential

/-- A bimodule quasi-isomorphism induces a bijection on unary cohomology. -/
def IsQuasiIso (f : AInfinityBimoduleHom MM NN) : Prop :=
  Function.Bijective f.cohomologyMap

/-- Quasi-isomorphisms are exactly the morphisms bijective on unary cohomology. -/
theorem isQuasiIso_def (f : AInfinityBimoduleHom MM NN) :
    f.IsQuasiIso ↔ Function.Bijective f.cohomologyMap := Iff.rfl

/-- A bimodule morphism is a quasi-isomorphism exactly when its linear part detects boundaries
on cycles and every target cycle differs from the image of a source cycle by a boundary. -/
theorem isQuasiIso_iff (f : AInfinityBimoduleHom MM NN) :
    f.IsQuasiIso ↔
      (∀ x ∈ LinearMap.ker MM.differential,
        f.linearPart x ∈ LinearMap.range NN.differential → x ∈ LinearMap.range MM.differential) ∧
      ∀ y ∈ LinearMap.ker NN.differential, ∃ x ∈ LinearMap.ker MM.differential,
        y - f.linearPart x ∈ LinearMap.range NN.differential := by
  rw [isQuasiIso_def, Function.Bijective, cohomologyMap,
    LinearMap.homologyMap_injective_iff, LinearMap.homologyMap_surjective_iff]

/-- Identity bimodule morphisms are quasi-isomorphisms. -/
@[simp]
theorem isQuasiIso_id (MM : AInfinityBimodule AA BB M) :
    (AInfinityBimoduleHom.id MM).IsQuasiIso := by
  rw [isQuasiIso_def, cohomologyMap_id]
  exact Function.bijective_id

/-- Quasi-isomorphisms are closed under composition. -/
theorem IsQuasiIso.comp {g : AInfinityBimoduleHom NN PP} {f : AInfinityBimoduleHom MM NN}
    (hg : g.IsQuasiIso) (hf : f.IsQuasiIso) : (g.comp f).IsQuasiIso := by
  rw [isQuasiIso_def, cohomologyMap_comp, LinearMap.coe_comp]
  exact Function.Bijective.comp hg hf

/-- Cancel a quasi-isomorphism on the source side of a quasi-isomorphism. -/
theorem IsQuasiIso.of_precomp {g : AInfinityBimoduleHom NN PP} {f : AInfinityBimoduleHom MM NN}
    (hf : f.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) : g.IsQuasiIso := by
  rw [isQuasiIso_def, cohomologyMap_comp, LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff _ hf).mp hgf

/-- Cancel a quasi-isomorphism on the target side of a quasi-isomorphism. -/
theorem IsQuasiIso.of_postcomp {g : AInfinityBimoduleHom NN PP} {f : AInfinityBimoduleHom MM NN}
    (hg : g.IsQuasiIso) (hgf : (g.comp f).IsQuasiIso) : f.IsQuasiIso := by
  rw [isQuasiIso_def, cohomologyMap_comp, LinearMap.coe_comp] at hgf
  exact (Function.Bijective.of_comp_iff' hg _).mp hgf

/-- A bimodule quasi-isomorphism induces a linear equivalence on total unary cohomology. -/
def IsQuasiIso.cohomologyLinearEquiv {f : AInfinityBimoduleHom MM NN} (hf : f.IsQuasiIso) :
    MM.Cohomology ≃ₗ[R] NN.Cohomology :=
  LinearEquiv.ofBijective f.cohomologyMap hf

/-- The forward equivalence is the cohomology map. -/
@[simp]
theorem IsQuasiIso.cohomologyLinearEquiv_apply {f : AInfinityBimoduleHom MM NN}
    (hf : f.IsQuasiIso) (x : MM.Cohomology) :
    hf.cohomologyLinearEquiv x = f.cohomologyMap x := (rfl)

/-- The inverse equivalence cancels the cohomology map. -/
@[simp]
theorem IsQuasiIso.cohomologyLinearEquiv_symm_cohomologyMap
    {f : AInfinityBimoduleHom MM NN} (hf : f.IsQuasiIso) (x : MM.Cohomology) :
    hf.cohomologyLinearEquiv.symm (f.cohomologyMap x) = x :=
  hf.cohomologyLinearEquiv.symm_apply_apply x

/-- The cohomology map cancels the inverse equivalence. -/
@[simp]
theorem IsQuasiIso.cohomologyMap_cohomologyLinearEquiv_symm
    {f : AInfinityBimoduleHom MM NN} (hf : f.IsQuasiIso) (x : NN.Cohomology) :
    f.cohomologyMap (hf.cohomologyLinearEquiv.symm x) = x :=
  hf.cohomologyLinearEquiv.apply_symm_apply x

end TauCeti.AInfinityBimoduleHom
