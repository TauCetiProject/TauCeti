/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Etale
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Cotangent
import Mathlib.RingTheory.RingHom.Etale
import TauCeti.Algebra.AlgebraicGroup.Tangent.FormallySmooth
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Tangent.Regularity
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.RingTheory.Etale.Reduced
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Differentials of affine isogenies

The differential of an isogeny with étale scheme-theoretic kernel is bijective, over any
commutative base ring and with no smoothness or finiteness hypothesis on either group: the
coordinate map is then étale. The differential therefore gives a Lie algebra equivalence
`lieEquivOfEtaleKernel`, and `cotangentDualLieEquivOfEtaleKernel` on the cotangent-dual Lie
algebras. The kernel need not be trivial: this comparison applies, for example, to central
isogenies with nontrivial étale kernel.

Over a field the converse holds too: the differential of an isogeny is bijective exactly when its
kernel is étale, which distinguishes separable from inseparable isogenies in positive
characteristic. The converse uses the identification of the Lie algebra of the kernel with the
kernel of the differential. In characteristic zero, `cotangentDualLieEquivOfCharZero` supplies
the equivalence without any kernel hypothesis, using Cartier's theorem.

An isogeny onto a smooth affine group over a field does not increase Lie dimension, and an
isogeny from a smooth affine group preserves it, with no hypothesis on the target. Smoothness
identifies Lie dimension with the Krull dimension of the coordinate ring, which an isogeny
preserves; after passage to an algebraic closure, Krull dimension bounds the Lie dimension of any
finite-type group from below. Smoothness of the source descends to the target, whose coordinate
ring embeds in that of the source. No connectedness, centrality, or restriction on the
characteristic is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2 and 10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§6 and 11.

The étale-kernel results build on `CommHopfAlgCat.etale_iff_algebraEtale_quotient_kernelHopfIdeal`
and the converse over a field on `CommHopfAlgCat.finrank_kernelLie`; the Lie dimension comparison
uses `HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim` and `IsIsogeny.ringKrullDim_eq`, and
descends smoothness with `geometricallyReducedCommHopfAlgProperty.of_injective`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat.IsIsogeny

universe u v

section CommRing

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R} {f : H ⟶ K}

/-- The differential of an isogeny with étale kernel is bijective on counit-valued derivations.
Neither group needs to be smooth or of finite type, and the base can be any commutative ring. -/
theorem derivationCompLieHom_bijective_of_etaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Function.Bijective (derivationCompLieHom (B := R) f.hom) := by
  have hetale := (CommHopfAlgCat.etale_iff_algebraEtale_quotient_kernelHopfIdeal f
    hf.faithfullyFlat).mpr hker
  have hsmooth := ((RingHom.etale_iff_formallyUnramified_and_smooth _).mp hetale).2
  rw [funext (derivationCompLieHom_apply (B := R) f.hom)]
  exact ⟨f.hom.derivationComp_injective_of_formallyUnramified hetale.formallyUnramified,
    derivationComp_surjective_of_formallySmooth f.hom hsmooth.formallySmooth⟩

/-- The differential of an isogeny with étale kernel, as a Lie algebra equivalence from the
source group to the target group. Neither group needs to be smooth or of finite type. -/
noncomputable def lieEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Derivation R K (Bialgebra.CounitAlgebra R K R) ≃ₗ⁅R⁆
      Derivation R H (Bialgebra.CounitAlgebra R H R) :=
  LieEquiv.ofBijective (derivationCompLieHom (B := R) f.hom)
    (hf.derivationCompLieHom_bijective_of_etaleKernel hker)

/-- The forward Lie homomorphism of the equivalence is the differential. -/
@[simp]
theorem lieEquivOfEtaleKernel_toLieHom (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    (hf.lieEquivOfEtaleKernel hker).toLieHom = derivationCompLieHom (B := R) f.hom := by
  ext d a
  rfl

/-- The Lie equivalence acts by precomposition of counit-valued derivations with the
coordinate map. Use `rw` with this lemma: registering it for `simp` would prevent cancellation
of the equivalence with its inverse. -/
theorem lieEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal))
    (d : Derivation R K (Bialgebra.CounitAlgebra R K R)) :
    hf.lieEquivOfEtaleKernel hker d = derivationComp (B := R) f.hom d := by
  calc
    hf.lieEquivOfEtaleKernel hker d = derivationCompLieHom (B := R) f.hom d :=
      congrArg (fun g ↦ g d) (hf.lieEquivOfEtaleKernel_toLieHom hker)
    _ = derivationComp (B := R) f.hom d := derivationCompLieHom_apply _ _

/-- The Lie equivalence acts pointwise by precomposition, transporting the resulting value
between the two counit coefficient algebras through the base ring. -/
@[simp]
theorem lieEquivOfEtaleKernel_apply_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal))
    (d : Derivation R K (Bialgebra.CounitAlgebra R K R)) (a : H) :
    hf.lieEquivOfEtaleKernel hker d a =
      (Bialgebra.CounitAlgebra.algEquivSelf R H R).symm
        (Bialgebra.CounitAlgebra.algEquivSelf R K R (d ((f.hom : H →ₐ[R] K) a))) := by
  apply (Bialgebra.CounitAlgebra.algEquivSelf R H R).injective
  rw [AlgEquiv.apply_symm_apply]
  rw [lieEquivOfEtaleKernel_apply]
  exact algEquivSelf_derivationComp_apply f.hom d a

/-- The differential of an isogeny with étale kernel on the native cotangent-dual Lie algebras.
Neither group needs to be smooth or of finite type. -/
noncomputable def cotangentDualLieEquivOfEtaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Module.Dual R (Bialgebra.CotangentSpace R K) ≃ₗ⁅R⁆
      Module.Dual R (Bialgebra.CotangentSpace R H) :=
  (Derivation.cotangentDualLieEquiv (R := R) (H := K)).trans
    ((hf.lieEquivOfEtaleKernel hker).trans
      (Derivation.cotangentDualLieEquiv (R := R) (H := H)).symm)

/-- The cotangent-dual Lie equivalence acts by the existing differential. Use `rw`:
a simp rule here would prevent cancellation with the inverse equivalence. -/
theorem cotangentDualLieEquivOfEtaleKernel_apply (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal))
    (x : Module.Dual R (Bialgebra.CotangentSpace R K)) :
    hf.cotangentDualLieEquivOfEtaleKernel hker x = Derivation.dualCotangentMap f.hom x := by
  apply (Derivation.cotangentLinearEquiv (R := R) (A := H) (B := R)).injective
  simp only [cotangentDualLieEquivOfEtaleKernel, LieEquiv.trans_apply,
    Derivation.cotangentDualLieEquiv_apply,
    Derivation.cotangentDualLieEquiv_symm_apply, LinearEquiv.apply_symm_apply,
    lieEquivOfEtaleKernel_apply, Derivation.cotangentLinearEquiv_dualCotangentMap]

/-- The forward linear map of the cotangent-dual Lie equivalence is the differential. -/
@[simp]
theorem cotangentDualLieEquivOfEtaleKernel_toLinearMap (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    (hf.cotangentDualLieEquivOfEtaleKernel hker).toLinearMap =
      Derivation.dualCotangentMap f.hom := by
  apply LinearMap.ext
  intro x
  exact hf.cotangentDualLieEquivOfEtaleKernel_apply hker x

/-- The differential of an isogeny with étale kernel is bijective on cotangent duals. Neither
group needs to be smooth or of finite type. -/
theorem dualCotangentMap_bijective_of_etaleKernel (hf : IsIsogeny f)
    (hker : Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal)) :
    Function.Bijective (Derivation.dualCotangentMap f.hom) := by
  rw [← hf.cotangentDualLieEquivOfEtaleKernel_toLinearMap hker]
  exact (hf.cotangentDualLieEquivOfEtaleKernel hker).bijective

end CommRing

section Field

variable {k : Type u} [Field k]

/-- The differential of an isogeny over a field is bijective exactly when its scheme-theoretic
kernel is étale. This distinguishes separable isogenies from inseparable ones in positive
characteristic. Neither group needs to be smooth or of finite type. -/
theorem algebraEtale_quotient_kernelHopfIdeal_iff_bijective_derivationCompLieHom
    {H K : _root_.CommHopfAlgCat.{u} k} {f : H ⟶ K} (hf : IsIsogeny f) :
    Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal) ↔
      Function.Bijective (derivationCompLieHom (B := k) f.hom) := by
  refine ⟨hf.derivationCompLieHom_bijective_of_etaleKernel, fun hbij ↦ ?_⟩
  let _ := moduleFinite_quotient_kernelHopfIdeal hf.finite
  rw [HopfAlgebra.algebraEtale_iff_finrank_lie_eq_zero, finrank_kernelLie,
    (LieHom.ker_eq_bot _).mpr hbij.1]
  exact Module.finrank_zero_of_subsingleton

variable {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K}

/-- An isogeny onto a smooth affine group over any field does not increase Lie dimension: the
Lie algebra of the target `Spec H` has dimension at most that of the source `Spec K`, which need
not be smooth. The coordinate arrow reverses the group-scheme arrow. -/
theorem finrank_lie_le [Algebra.Smooth k H] (hf : IsIsogeny f) :
    Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) ≤
      Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) := by
  let _ := hf.finiteType_target
  let L := AlgebraicClosure k
  have hK : ringKrullDim K ≤
      Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) := by
    rw [← finrank_lie_baseChange (K := L),
      ← ringKrullDim_tensorProduct_field_of_finiteType (k := k) L K]
    exact HopfAlgebra.ringKrullDim_le_finrank_lie (k := L)
  have h := (HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim.mp ‹Algebra.Smooth k H›).trans_le
    (hf.ringKrullDim_eq.symm.trans_le hK)
  exact_mod_cast h

/-- An isogeny from a smooth affine group over any field preserves Lie dimension: the Lie
algebras of the source `Spec K` and the target `Spec H` have the same dimension, with no
hypothesis on the target. The coordinate arrow reverses the group-scheme arrow. -/
theorem finrank_lie_eq [Algebra.Smooth k K] (hf : IsIsogeny f) :
    Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) =
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  have : Algebra.FiniteType k H := by
    let _ := f.hom.toAlgHom.toAlgebra
    have : IsScalarTower k H K := .of_algebraMap_eq fun x ↦ (f.hom.toAlgHom.commutes x).symm
    have : Module.Finite H K := hf.finite
    exact ⟨fg_of_fg_of_fg k H K Algebra.FiniteType.out Module.Finite.fg_top hf.injective⟩
  have : Algebra.Smooth k H := (smoothCommHopfAlgProperty_iff H).mp
    (smoothCommHopfAlgProperty_of_geometricallyReduced k H
      (geometricallyReducedCommHopfAlgProperty.of_injective.{u, v, 0} f.hom.toAlgHom hf.injective
        (geometricallyReducedCommHopfAlgProperty_of_smooth k K
          ((smoothCommHopfAlgProperty_iff K).mpr ‹_›))))
  have hK := HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim.mp ‹Algebra.Smooth k K›
  have hH := HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim.mp ‹Algebra.Smooth k H›
  exact_mod_cast hK.trans (hf.ringKrullDim_eq.trans hH.symm)

end Field

section CharZero

variable {k : Type u} [Field k] [CharZero k] {H K : _root_.CommHopfAlgCat.{v} k} {f : H ⟶ K}

/-- In characteristic zero the differential of an affine isogeny identifies the actual
cotangent-dual Lie algebras. Neither group needs to be of finite type, and no connectedness or
centrality hypothesis is needed. -/
noncomputable def cotangentDualLieEquivOfCharZero (hf : IsIsogeny f) :
    Module.Dual k (Bialgebra.CotangentSpace k K) ≃ₗ⁅k⁆
      Module.Dual k (Bialgebra.CotangentSpace k H) :=
  let Q := _root_.CommHopfAlgCat.quotient K (kernelHopfIdeal f)
  let _ : Module.Finite k Q := moduleFinite_quotient_kernelHopfIdeal hf.finite
  hf.cotangentDualLieEquivOfEtaleKernel (algebraEtale_iff_finite_and_isReduced.2
    ⟨‹_›, HopfAlgebra.isReduced_of_charZero k Q⟩)

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

/-- The differential of a characteristic-zero affine isogeny is bijective on cotangent duals. -/
theorem dualCotangentMap_bijective_of_charZero (hf : IsIsogeny f) :
    Function.Bijective (Derivation.dualCotangentMap f.hom) := by
  rw [← hf.cotangentDualLieEquivOfCharZero_toLinearMap]
  exact hf.cotangentDualLieEquivOfCharZero.bijective

end CharZero

end TauCeti.CommHopfAlgCat.IsIsogeny
