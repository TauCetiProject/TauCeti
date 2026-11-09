/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Etale
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Cotangent
import Mathlib.RingTheory.RingHom.Etale
import TauCeti.Algebra.AlgebraicGroup.Tangent.FormallySmooth
import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Etale.Reduced

/-!
# Differentials of smooth affine isogenies

An isogeny between smooth affine groups of finite type over a field preserves Lie dimension.
Its differential is therefore bijective exactly when its scheme-theoretic kernel is étale.
In this case the differential gives a Lie algebra equivalence. The kernel need not be trivial:
this comparison applies, for example, to central isogenies with nontrivial étale kernel.

The cotangent-dual version is `cotangentDualLieEquivOfEtaleKernel`. In characteristic
zero, `cotangentDualLieEquivOfCharZero` supplies this equivalence without additional
smoothness or kernel hypotheses, using Cartier's theorem.

Dimension equality uses the finite injective coordinate map after passage to an algebraic
closure, where smoothness identifies Lie dimension with Krull dimension. The criterion then
uses the existing identification of the Lie algebra of the kernel with the kernel of the
differential. No connectedness, centrality, or restriction on the characteristic is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6 and 11.

The kernel criterion builds on `CommHopfAlgCat.algebraEtale_quotient_kernelHopfIdeal_iff`;
the Lie dimension comparison uses `HopfAlgebra.isRegularLocalRing_augmentationStalk_iff` and
`finrank_lie_baseChange`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}
  [Algebra.Smooth k H] [Algebra.Smooth k K]
  {f : H ⟶ K}

/-- An isogeny between smooth finite-type affine groups over any field preserves Lie dimension.
The coordinate arrow reverses the group-scheme arrow. -/
theorem finrank_lie_eq (hf : IsIsogeny f) :
    Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) =
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let L := AlgebraicClosure k
  let HL := CommHopfAlgCat.baseChange (K := L) H
  let KL := CommHopfAlgCat.baseChange (K := L) K
  let fL := baseChangeMap (K := L) f
  have hfL : IsIsogeny fL := hf.baseChange
  let _ : Algebra.Smooth L HL := Algebra.Smooth.baseChange k H L
  let _ : Algebra.Smooth L KL := Algebra.Smooth.baseChange k K L
  let _ : IsRegularRing HL := IsRegularRing.of_smooth (R := L)
  let _ : IsRegularRing KL := IsRegularRing.of_smooth (R := L)
  have hdim : ringKrullDim KL = ringKrullDim HL := by
    let _ := fL.hom.toAlgHom.toAlgebra
    let _ : Module.Finite HL KL := hfL.finite
    let _ : FaithfulSMul HL KL :=
      (faithfulSMul_iff_algebraMap_injective HL KL).mpr hfL.injective
    exact ringKrullDim_eq_of_isIntegral_of_faithfulSMul
  have hlie : Module.finrank L
      (Derivation L KL (Bialgebra.CounitAlgebra L KL L)) =
        Module.finrank L (Derivation L HL (Bialgebra.CounitAlgebra L HL L)) := by
    have hK := (HopfAlgebra.isRegularLocalRing_augmentationStalk_iff
      (k := L) (H := KL)).mp inferInstance
    have hH := (HopfAlgebra.isRegularLocalRing_augmentationStalk_iff
      (k := L) (H := HL)).mp inferInstance
    have h := hK.trans (hdim.trans hH.symm)
    exact_mod_cast h
  simpa only [HL, KL, CommHopfAlgCat.baseChange, finrank_lie_baseChange] using hlie

/-- The differential of an isogeny between smooth finite-type affine groups is bijective
exactly when its scheme-theoretic kernel is étale. This distinguishes separable isogenies
from inseparable ones in positive characteristic. -/
theorem algebraEtale_quotient_kernelHopfIdeal_iff_bijective_derivationCompLieHom
    (hf : IsIsogeny f) :
    Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal) ↔
      Function.Bijective (derivationCompLieHom (B := k) f.hom) := by
  rw [algebraEtale_quotient_kernelHopfIdeal_iff]
  have hsurj := LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (derivationCompLieHom (B := k) f.hom).toLinearMap) hf.finrank_lie_eq
  exact ⟨fun hinj ↦ ⟨hinj, hsurj.mp hinj⟩, fun hbij ↦ hbij.1⟩

/-- The differential of a smooth affine isogeny with étale kernel, as a Lie algebra
equivalence from the source group to the target group. -/
noncomputable def lieEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Derivation k K (Bialgebra.CounitAlgebra k K k) ≃ₗ⁅k⁆
      Derivation k H (Bialgebra.CounitAlgebra k H k) :=
  LieEquiv.ofBijective (derivationCompLieHom (B := k) f.hom)
    (hf.algebraEtale_quotient_kernelHopfIdeal_iff_bijective_derivationCompLieHom.mp hker)

/-- The forward Lie homomorphism of the equivalence is the differential. -/
@[simp]
theorem lieEquivOfEtaleKernel_toLieHom (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    (hf.lieEquivOfEtaleKernel hker).toLieHom = derivationCompLieHom (B := k) f.hom := by
  ext d a
  rfl

/-- The Lie equivalence acts by precomposition of counit-valued derivations with the
coordinate map. Use `rw` with this lemma: registering it for `simp` would prevent cancellation
of the equivalence with its inverse. -/
theorem lieEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (d : Derivation k K (Bialgebra.CounitAlgebra k K k)) :
    hf.lieEquivOfEtaleKernel hker d = derivationComp (B := k) f.hom d := by
  calc
    hf.lieEquivOfEtaleKernel hker d = derivationCompLieHom (B := k) f.hom d :=
      congrArg (fun g ↦ g d) (hf.lieEquivOfEtaleKernel_toLieHom hker)
    _ = derivationComp (B := k) f.hom d := derivationCompLieHom_apply _ _

/-- The Lie equivalence acts pointwise by precomposition, transporting the resulting value
between the two counit coefficient algebras through the ground field. -/
@[simp]
theorem lieEquivOfEtaleKernel_apply_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (d : Derivation k K (Bialgebra.CounitAlgebra k K k)) (a : H) :
    hf.lieEquivOfEtaleKernel hker d a =
      (Bialgebra.CounitAlgebra.algEquivSelf k H k).symm
        (Bialgebra.CounitAlgebra.algEquivSelf k K k (d ((f.hom : H →ₐ[k] K) a))) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf k H k).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [lieEquivOfEtaleKernel_apply]
  exact algEquivSelf_derivationComp_apply f.hom d a

omit [Algebra.Smooth k H] [Algebra.Smooth k K] in
/-- The differential of an isogeny with étale kernel is bijective on cotangent duals: the
coordinate map is then étale, hence formally unramified and formally smooth. Neither group needs
to be smooth or of finite type. -/
theorem dualCotangentMap_bijective_of_etaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Function.Bijective (Derivation.dualCotangentMap f.hom) := by
  have hetale := (CommHopfAlgCat.etale_iff_algebraEtale_quotient_kernelHopfIdeal f
    hf.faithfullyFlat).mpr hker
  have hsmooth := ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp hetale).2
  -- the differential on counit-valued derivations is bijective
  have hbij : Function.Bijective (derivationComp (B := k) f.hom) :=
    ⟨derivationComp_injective_of_formallyUnramified f.hom hetale.formallyUnramified,
      derivationComp_surjective_of_formallySmooth f.hom hsmooth.formallySmooth⟩
  let e := (Derivation.cotangentLinearEquiv (R := k) (A := K) (B := k)).trans
    ((LinearEquiv.ofBijective (derivationComp (B := k) f.hom) hbij).trans
      (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).symm)
  have he (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
      e x = Derivation.dualCotangentMap f.hom x := by
    apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
    rw [Derivation.cotangentLinearEquiv_dualCotangentMap]
    exact (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).apply_symm_apply _
  exact (funext he : ⇑e = _) ▸ e.bijective

/-- The differential of a smooth affine isogeny with étale kernel on the native
cotangent-dual Lie algebras. -/
noncomputable def cotangentDualLieEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Module.Dual k (Bialgebra.CotangentSpace k K) ≃ₗ⁅k⁆
      Module.Dual k (Bialgebra.CotangentSpace k H) :=
  (Derivation.cotangentDualLieEquiv (R := k) (H := K)).trans
    ((hf.lieEquivOfEtaleKernel hker).trans
      (Derivation.cotangentDualLieEquiv (R := k) (H := H)).symm)

/-- The cotangent-dual Lie equivalence acts by the existing differential. Use `rw`:
a simp rule here would prevent cancellation with the inverse equivalence. -/
theorem cotangentDualLieEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    hf.cotangentDualLieEquivOfEtaleKernel hker x = Derivation.dualCotangentMap f.hom x := by
  apply (Derivation.cotangentLinearEquiv (R := k) (A := H) (B := k)).injective
  simp only [cotangentDualLieEquivOfEtaleKernel, LieEquiv.trans_apply,
    Derivation.cotangentDualLieEquiv_apply,
    Derivation.cotangentDualLieEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    lieEquivOfEtaleKernel_apply, Derivation.cotangentLinearEquiv_dualCotangentMap]

/-- The forward linear map of the cotangent-dual Lie equivalence is the differential. -/
@[simp]
theorem cotangentDualLieEquivOfEtaleKernel_toLinearMap (hf : IsIsogeny f)
    (hker : Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    (hf.cotangentDualLieEquivOfEtaleKernel hker).toLinearMap =
      Derivation.dualCotangentMap f.hom := by
  apply LinearMap.ext
  intro x
  exact hf.cotangentDualLieEquivOfEtaleKernel_apply hker x

end TauCeti.CommHopfAlgCat.IsIsogeny

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u

variable {k : Type u} [Field k] [CharZero k]
  {H K : _root_.CommHopfAlgCat.{u} k} [Algebra.FiniteType k H] {f : H ⟶ K}

/-- In characteristic zero a finite-type affine isogeny identifies the actual
cotangent-dual Lie algebras. No connectedness or centrality hypothesis is needed. -/
noncomputable def cotangentDualLieEquivOfCharZero (hf : IsIsogeny f) :
    Module.Dual k (Bialgebra.CotangentSpace k K) ≃ₗ⁅k⁆
      Module.Dual k (Bialgebra.CotangentSpace k H) := by
  let _ := hf.finiteType_target
  let _ : Algebra.Smooth k H :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k H)
  let _ : Algebra.Smooth k K :=
    (smoothCommHopfAlgProperty_iff _).mp (smoothCommHopfAlgProperty_of_charZero k K)
  let Q := _root_.CommHopfAlgCat.quotient K (kernelHopfIdeal f)
  let _ : Module.Finite k Q := moduleFinite_quotient_kernelHopfIdeal hf.finite
  let _ : _root_.IsReduced Q := HopfAlgebra.isReduced_of_charZero k Q
  exact hf.cotangentDualLieEquivOfEtaleKernel (algebraEtale_of_finite_of_isReduced k Q)

/-- The characteristic-zero Lie equivalence acts by the differential on cotangent duals.
Use `rw` to retain cancellation of the equivalence and its inverse during simplification. -/
theorem cotangentDualLieEquivOfCharZero_apply (hf : IsIsogeny f)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    hf.cotangentDualLieEquivOfCharZero x = Derivation.dualCotangentMap f.hom x := by
  simp only [cotangentDualLieEquivOfCharZero, cotangentDualLieEquivOfEtaleKernel_apply]

/-- The forward linear map of the characteristic-zero Lie equivalence is the differential. -/
@[simp]
theorem cotangentDualLieEquivOfCharZero_toLinearMap (hf : IsIsogeny f) :
    hf.cotangentDualLieEquivOfCharZero.toLinearMap = Derivation.dualCotangentMap f.hom := by
  apply LinearMap.ext
  intro x
  exact hf.cotangentDualLieEquivOfCharZero_apply x

/-- The differential of a characteristic-zero finite-type affine isogeny is bijective on
cotangent duals. -/
theorem dualCotangentMap_bijective_of_charZero (hf : IsIsogeny f) :
    Function.Bijective (Derivation.dualCotangentMap f.hom) := by
  rw [← hf.cotangentDualLieEquivOfCharZero_toLinearMap]
  exact hf.cotangentDualLieEquivOfCharZero.bijective

end TauCeti.CommHopfAlgCat.IsIsogeny
