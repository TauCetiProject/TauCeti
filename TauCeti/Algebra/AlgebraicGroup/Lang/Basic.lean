/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FixedPointFree
public import TauCeti.Algebra.AlgebraicGroup.Connected.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Frobenius.FiniteField
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible
import TauCeti.Algebra.AlgebraicGroup.Frobenius.Differential
import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Map
import TauCeti.Algebra.Bialgebra.Quotient
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense
import TauCeti.GroupTheory.FixedSubgroup.Lang
import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints
import TauCeti.RingTheory.Ideal.Cotangent.Injectivity
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.RingTheory.TensorProduct.Reduced
import TauCeti.Topology.Constructible.Basic

/-!
# Lang's theorem for connected algebraic groups

For a connected finite-type affine algebraic group `G = Spec H` over an algebraically closed field
`K`, every endomorphism `F = Spec φ` of `G` whose differential at the identity vanishes has a
surjective Lang map `g ↦ g⁻¹ * F(g)` on `G(K)` (`TauCeti.Lang.surjective_inv_mul_mapDomain`).
Smoothness is not required: over an algebraically closed field `K`, passing to the reduced quotient
`H ⧸ (HopfIdeal.reduction K H).toIdeal` preserves `K`-points, connectedness, finite type, and
vanishing of the differential, reducing to the case of a Noetherian integral domain.

In the integral-domain case, the proof avoids explicit comultiplication coordinates by working in
the convolution group of algebra-valued points:

1. For each `a ∈ G(K)`, the twisted Lang morphism `x ↦ x * a * F(x)⁻¹` is represented by the
   coordinate endomorphism `TauCeti.Lang.twistedLangAlgHom φ a`. Precomposing with left translation
   by `a⁻¹` produces an identity-preserving endomorphism whose differential at the identity agrees
   with that of conjugation by `a⁻¹`, hence is an isomorphism on the cotangent space at the
   identity.
2. Since `H` is a Noetherian integral domain, surjectivity on the residue field and cotangent space
   implies injectivity of the twisted Lang comorphism (`TauCeti.Lang.twistedLangAlgHom_injective`)
   via Krull's intersection theorem and the Hopfian property of Noetherian quotients
   (`AlgHom.injective_of_surjective_mapCotangent`).
3. By Chevalley's constructibility theorem, the images of the twisted Lang morphisms for `1` and `a`
   contain dense open subsets of `Spec H`. Their intersection contains a `K`-rational point, giving
   `x₁, x₂ ∈ G(K)` with `x₁ * F(x₁)⁻¹ = x₂ * a * F(x₂)⁻¹`; then `g = x₁⁻¹ * x₂` satisfies
   `g⁻¹ * F(g) = a`.

Over a finite field `F` of cardinality `q`, every positive iterate of the geometric Frobenius
`id ⊗ Frob` on `K ⊗[F] H` has zero differential
(`TauCeti.FiniteField.derivationComp_geometricFrobeniusBialgHom_eq_zero`). Applying the general
theorem to the base change of a geometrically connected finite-type affine group scheme over `F`
yields Lang's theorem for every positive iterate `n ≠ 0`
(`TauCeti.Lang.surjective_inv_mul_frobeniusPoints`,
`TauCeti.Lang.surjective_commutatorMap_frobeniusPoints`, and `TauCeti.Lang.lang_surjective`),
vanishing of non-abelian Galois `H¹` for finite extensions `L / F`
(`TauCeti.Lang.exists_eq_inv_mul_mapValue_of_mul_eq_mul_mapValue`), and surjectivity on
`F`-rational points for exact sequences with geometrically connected finite-type kernel
(`TauCeti.Lang.mapDomain_surjective_of_surjective_of_range_eq_ker`).

## Main definitions

* `TauCeti.Lang.twistedLangAlgHom`: the coordinate-algebra endomorphism representing
  `x ↦ x * a * F(x)⁻¹`.

## Main results

* `TauCeti.Lang.twistedLangAlgHom_injective`: for a zero-differential bialgebra endomorphism of a
  Noetherian integral-domain Hopf algebra over a field, every twisted Lang comorphism is injective.
* `TauCeti.Lang.surjective_inv_mul_mapDomain` and `TauCeti.Lang.surjective_commutatorMap_mapDomain`:
  over an algebraically closed field, any zero-differential endomorphism of a connected finite-type
  group has surjective Lang map.
* `TauCeti.Lang.surjective_inv_mul_frobeniusPoints`,
  `TauCeti.Lang.surjective_commutatorMap_frobeniusPoints`, and `TauCeti.Lang.lang_surjective`:
  Lang's theorem for geometrically connected finite-type affine group schemes over finite fields
  and positive iterates of the Frobenius.
* `TauCeti.Lang.exists_eq_inv_mul_mapValue_of_mul_eq_mul_mapValue`: vanishing of non-abelian
  Galois 1-cocycles `H¹(F, H) = 1` over finite extensions of a finite field.
* `TauCeti.Lang.mapDomain_surjective_of_surjective_of_range_eq_ker`: an exact sequence on geometric
  points whose kernel is geometrically connected of finite type over a finite field `F` is
  surjective on `F`-points.

## References

* S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563.
* J. S. Milne, *Algebraic Groups*, version 2.00 (2015), Proposition 27.54, Corollary 27.55, and
  Corollary 27.56, pp. 487–488.
-/

public section

open WithConv Topology
open scoped TensorProduct

universe u v w

namespace TauCeti.Lang

/-! ### Twisted Lang comorphisms and their differential -/

section TwistedLang

variable {K : Type u} [CommSemiring K]
variable {H : Type v} [CommSemiring H] [_root_.HopfAlgebra K H]

/-- For a bialgebra endomorphism `φ : H →ₐc[K] H` (corresponding to an algebraic-group
endomorphism `F = Spec φ`) and a rational point `a : WithConv (H →ₐ[K] K)`, the twisted Lang
comorphism representing `x ↦ x * a * F(x)⁻¹`. -/
noncomputable def twistedLangAlgHom (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    H →ₐ[K] H :=
  (toConv (AlgHom.id K H) * AlgHom.mapValue (Algebra.ofId K H) a *
    (toConv (φ : H →ₐ[K] H))⁻¹).ofConv

/-- In the convolution group, `twistedLangAlgHom φ a` is `id * a * φ⁻¹`. -/
theorem toConv_twistedLangAlgHom (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    toConv (twistedLangAlgHom φ a) =
      toConv (AlgHom.id K H) * AlgHom.mapValue (Algebra.ofId K H) a *
        (toConv (φ : H →ₐ[K] H))⁻¹ :=
  toConv_ofConv _

/-- Precomposition with `twistedLangAlgHom φ a` acts on `A`-valued points by
`x ↦ x * a * F(x)⁻¹`. -/
theorem toConv_comp_twistedLangAlgHom {A : Type w} [CommSemiring A] [Algebra K A]
    (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) (x : WithConv (H →ₐ[K] A)) :
    toConv (x.ofConv.comp (twistedLangAlgHom φ a)) =
      x * AlgHom.mapValue (Algebra.ofId K A) a * (BialgHom.mapDomain φ x)⁻¹ := by
  have hmap := congrArg (AlgHom.mapValue (H := H) x.ofConv) (toConv_twistedLangAlgHom φ a)
  rw [map_mul, map_mul, map_inv, WithConv.mapValue_algebraOfId] at hmap
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv,
    BialgHom.mapDomain_apply] using hmap

end TwistedLang

section TwistedLangAtId

variable {K : Type u} [CommRing K]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra K H]

/-- The identity-preserving translate of `twistedLangAlgHom φ a`, representing
`x ↦ (a⁻¹ * x * a) * F(x)⁻¹`. -/
private noncomputable def twistedLangAtId (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    H →ₐ[K] H :=
  (twistedLangAlgHom φ a).comp (HopfAlgebra.leftTranslationAlgEquiv a⁻¹).toAlgHom

private theorem toConv_twistedLangAtId (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    toConv (twistedLangAtId φ a) =
      toConv (HopfAlgebra.pointConjugationAlgHom a⁻¹) * (toConv (φ : H →ₐ[K] H))⁻¹ := by
  have h := HopfAlgebra.toConv_comp_leftTranslationAlgEquiv a⁻¹ (toConv (twistedLangAlgHom φ a))
  rw [ofConv_toConv] at h
  rw [twistedLangAtId, h, toConv_twistedLangAlgHom, HopfAlgebra.toConv_pointConjugationAlgHom]
  have hinv : (AlgHom.mapValue (H := H) (Algebra.ofId K H) a⁻¹)⁻¹ =
      AlgHom.mapValue (H := H) (Algebra.ofId K H) a := by
    rw [← map_inv, inv_inv]
  rw [hinv]
  simp only [mul_assoc]

private theorem toConv_comp_twistedLangAtId {A : Type w} [CommSemiring A] [Algebra K A]
    (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) (x : WithConv (H →ₐ[K] A)) :
    toConv (x.ofConv.comp (twistedLangAtId φ a)) =
      toConv (x.ofConv.comp (HopfAlgebra.pointConjugationAlgHom a⁻¹)) *
        (BialgHom.mapDomain φ x)⁻¹ := by
  have hmap := congrArg (AlgHom.mapValue (H := H) x.ofConv) (toConv_twistedLangAtId φ a)
  rw [map_mul, map_inv] at hmap
  simpa only [AlgHom.mapValue_apply, ofConv_toConv, BialgHom.mapDomain_apply] using hmap

private theorem counit_comp_twistedLangAtId (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    (_root_.Bialgebra.counitAlgHom K H).comp (twistedLangAtId φ a) =
      _root_.Bialgebra.counitAlgHom K H := by
  have hone : toConv (_root_.Bialgebra.counitAlgHom K H) = (1 : WithConv (H →ₐ[K] K)) := by
    rw [← TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom, toConv_ofConv]
  apply toConv_injective
  have hcomp := toConv_comp_twistedLangAtId φ a (toConv (_root_.Bialgebra.counitAlgHom K H))
  rw [ofConv_toConv] at hcomp
  rw [hcomp, HopfAlgebra.comp_pointConjugationAlgHom, hone, map_one, inv_one, mul_one, mul_one,
    mul_inv_cancel]

private theorem toConv_comp_twistedLangAtId_of_mapDomain_eq_one {A : Type w} [CommSemiring A]
    [Algebra K A] (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K))
    (x : WithConv (H →ₐ[K] A)) (hx : BialgHom.mapDomain φ x = 1) :
    toConv (x.ofConv.comp (twistedLangAtId φ a)) =
      toConv (x.ofConv.comp (HopfAlgebra.pointConjugationAlgHom a⁻¹)) := by
  rw [toConv_comp_twistedLangAtId, hx, inv_one, mul_one]

private theorem derivation_comp_twistedLangAtId (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) (a : WithConv (H →ₐ[K] K))
    (d : Derivation K H (Bialgebra.CounitAlgebra K H K)) (x : H) :
    d (twistedLangAtId φ a x) = d (HopfAlgebra.pointConjugationAlgHom a⁻¹ x) := by
  let ψ : tangentKer K H K := derivationMulEquivTangentKer K H K (Multiplicative.ofAdd d)
  have hφψ : BialgHom.mapDomain
      (A := DualNumber (Bialgebra.CounitAlgebra K H K)) φ ψ.val = 1 := by
    rw [← tangentKerMap_apply_val]
    have hker : tangentKerMap (B := K) φ ψ = 1 := by
      dsimp only [ψ]
      rw [tangentKerMap_derivationMulEquivTangentKer, toAdd_ofAdd, hφ, LinearMap.zero_apply,
        ofAdd_zero]
      exact map_one (derivationMulEquivTangentKer K H K)
    rw [hker, Subgroup.coe_one]
  have hcomp := toConv_comp_twistedLangAtId_of_mapDomain_eq_one φ a ψ.val hφψ
  have hval := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (toConv_injective hcomp) x)
  simpa only [AlgHom.comp_apply, ψ, derivationMulEquivTangentKer_apply_snd, toAdd_ofAdd] using hval

end TwistedLangAtId

section Injectivity

variable {K : Type u} [Field K]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra K H]

/-- The induced map of `twistedLangAtId φ a` on the cotangent space at the identity coincides with
that of conjugation by `a⁻¹`. -/
private theorem mapCotangent_twistedLangAtId (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) (a : WithConv (H →ₐ[K] K))
    (hfI : Bialgebra.AugmentationIdeal K H ≤
      (Bialgebra.AugmentationIdeal K H).comap (twistedLangAtId φ a)) :
    Ideal.mapCotangent (Bialgebra.AugmentationIdeal K H) (Bialgebra.AugmentationIdeal K H)
        (twistedLangAtId φ a) hfI =
      Bialgebra.cotangentSpaceMap (HopfAlgebra.pointConjugationBialgEquiv a⁻¹).toBialgHom := by
  let I : Ideal H := Bialgebra.AugmentationIdeal K H
  ext c
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective c
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro f
  rw [map_sub, sub_eq_zero, Ideal.mapCotangent_toCotangent,
    ← Bialgebra.cotangentMap_augmentation K H
      ⟨twistedLangAtId φ a x.val, Ideal.mem_comap.mp (hfI x.property)⟩,
    ← Bialgebra.cotangentMap_augmentation K H x, Bialgebra.cotangentSpaceMap_cotangentMap]
  let d := Derivation.cotangentLinearEquiv (R := K) (A := H) (B := K) f
  rw [← Derivation.algEquivSelf_cotangentLinearEquiv_apply f,
    ← Derivation.algEquivSelf_cotangentLinearEquiv_apply f]
  have he : ((HopfAlgebra.pointConjugationBialgEquiv a⁻¹).toBialgHom : H →ₐ[K] H) =
      HopfAlgebra.pointConjugationAlgHom a⁻¹ := by
    rw [BialgEquiv.toBialgHom_eq_coe]
    exact HopfAlgebra.pointConjugationBialgEquiv_toAlgHom a⁻¹
  have hex : (HopfAlgebra.pointConjugationBialgEquiv a⁻¹).toBialgHom x.val =
      HopfAlgebra.pointConjugationAlgHom a⁻¹ x.val := AlgHom.congr_fun he x.val
  rw [hex]
  exact congrArg (Bialgebra.CounitAlgebra.algEquivSelf K H K)
    (derivation_comp_twistedLangAtId φ hφ a d x.val)

/-- If `φ : H →ₐc[K] H` is a bialgebra endomorphism with zero differential on a Noetherian
integral-domain Hopf algebra over a field, then every twisted Lang comorphism
`twistedLangAlgHom φ a` is injective. -/
theorem twistedLangAlgHom_injective [IsNoetherianRing H] [IsDomain H]
    (φ : H →ₐc[K] H) (hφ : TauCeti.derivationComp (B := K) φ = 0)
    (a : WithConv (H →ₐ[K] K)) :
    Function.Injective (twistedLangAlgHom φ a) := by
  let I : Ideal H := Bialgebra.AugmentationIdeal K H
  have hI_ne_top : I ≠ ⊤ := RingHom.ker_ne_top (_root_.Bialgebra.counitAlgHom K H : H →+* K)
  have hcounit := counit_comp_twistedLangAtId φ a
  have hfI : I ≤ I.comap (twistedLangAtId φ a) := by
    intro x hx
    simp only [I, Ideal.mem_comap, Bialgebra.AugmentationIdeal, RingHom.mem_ker,
      AlgHom.coe_toRingHom] at hx ⊢
    rw [← AlgHom.comp_apply, hcounit]
    exact hx
  have hquot : Function.Surjective (Ideal.Quotient.mk I ∘ twistedLangAtId φ a) := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨x, ?_⟩
    simp only [I, Function.comp_apply, Ideal.Quotient.eq, Bialgebra.AugmentationIdeal,
      RingHom.mem_ker, AlgHom.coe_toRingHom, map_sub]
    rw [← AlgHom.comp_apply, hcounit, sub_self]
  let e : H ≃ₐc[K] H := HopfAlgebra.pointConjugationBialgEquiv a⁻¹
  have hcot : Function.Surjective (Ideal.mapCotangent I I (twistedLangAtId φ a) hfI) := by
    rw [mapCotangent_twistedLangAtId φ hφ a hfI]
    intro c
    obtain ⟨y, rfl⟩ := Bialgebra.cotangentMap_surjective K H c
    refine ⟨Bialgebra.cotangentMap K H (e.symm y), ?_⟩
    rw [Bialgebra.cotangentSpaceMap_cotangentMap]
    simp [e]
  have hinj_atId : Function.Injective (twistedLangAtId φ a) :=
    (twistedLangAtId φ a).injective_of_surjective_mapCotangent I hI_ne_top hfI hquot hcot
  intro x y hxy
  obtain ⟨x', rfl⟩ := (HopfAlgebra.leftTranslationAlgEquiv a⁻¹).surjective x
  obtain ⟨y', rfl⟩ := (HopfAlgebra.leftTranslationAlgEquiv a⁻¹).surjective y
  have hxy' : twistedLangAtId φ a x' = twistedLangAtId φ a y' := by
    simpa only [twistedLangAtId, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply] using hxy
  exact congrArg (HopfAlgebra.leftTranslationAlgEquiv a⁻¹) (hinj_atId hxy')

/-- Each twisted Lang comorphism of a finite-type Hopf algebra is of finite type. -/
private theorem twistedLangAlgHom_finiteType [Algebra.FiniteType K H]
    (φ : H →ₐc[K] H) (a : WithConv (H →ₐ[K] K)) :
    (twistedLangAlgHom φ a).FiniteType :=
  RingHom.FiniteType.of_comp_finiteType (f := algebraMap K H)
    (g := (twistedLangAlgHom φ a).toRingHom)
    ((twistedLangAlgHom φ a).comp_algebraMap.symm ▸
      RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType K H))

/-- For a zero-differential bialgebra endomorphism of a finite-type integral-domain Hopf algebra,
the spectral image of each twisted Lang comorphism has dense interior. -/
private theorem dense_interior_range_comap_twistedLangAlgHom
    [Algebra.FiniteType K H] [IsDomain H]
    (φ : H →ₐc[K] H) (hφ : TauCeti.derivationComp (B := K) φ = 0)
    (a : WithConv (H →ₐ[K] K)) :
    Dense (interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom))) := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  have hfp : (twistedLangAlgHom φ a).toRingHom.FinitePresentation :=
    AlgHom.FinitePresentation.of_finiteType.mp (twistedLangAlgHom_finiteType φ a)
  have hd : DenseRange (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom) :=
    RingHom.denseRange_comap_of_injective _ (twistedLangAlgHom_injective φ hφ a)
  exact (PrimeSpectrum.isConstructible_range_comap hfp).dense_interior hd

end Injectivity

/-! ### Lang's theorem for zero-differential endomorphisms over algebraically closed fields -/

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- A `K`-rational point `y` lying in the spectral image of `twistedLangAlgHom φ b` lifts to a
`K`-point `x` satisfying `y = x * b * F(x)⁻¹` in the convolution group. -/
private theorem exists_toConv_eq_mul_mul_inv_mapDomain_of_mem_range_comap
    {H : Type v} [CommRing H] [_root_.HopfAlgebra K H] [Algebra.FiniteType K H]
    (φ : H →ₐc[K] H) (b : WithConv (H →ₐ[K] K)) (y : H →ₐ[K] K)
    (hy : AlgHom.kernelPoint y ∈
      Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ b).toRingHom)) :
    ∃ x : WithConv (H →ₐ[K] K), toConv y = x * b * (BialgHom.mapDomain φ x)⁻¹ := by
  obtain ⟨P, hP⟩ := hy
  have hP' : PrimeSpectrum.comap (twistedLangAlgHom φ b).toRingHom P =
      ⟨RingHom.ker y.toRingHom, RingHom.ker_isPrime y.toRingHom⟩ := by
    apply PrimeSpectrum.ext
    exact (congrArg PrimeSpectrum.asIdeal hP).trans (AlgHom.kernelPoint_asIdeal y)
  obtain ⟨x, hx⟩ := _root_.AlgHom.exists_comp_eq_of_comap_eq_ker (twistedLangAlgHom φ b)
    (twistedLangAlgHom_finiteType φ b) y P hP'
  refine ⟨toConv x, ?_⟩
  have h := toConv_comp_twistedLangAlgHom φ b (toConv x)
  rw [ofConv_toConv, hx, Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] at h
  exact h

/-- Integral-domain case of `surjective_inv_mul_mapDomain`. -/
private theorem surjective_inv_mul_mapDomain_of_isDomain
    {H : Type v} [CommRing H] [_root_.HopfAlgebra K H] [Algebra.FiniteType K H] [IsDomain H]
    (φ : H →ₐc[K] H) (hφ : TauCeti.derivationComp (B := K) φ = 0) :
    Function.Surjective fun g : WithConv (H →ₐ[K] K) =>
      g⁻¹ * BialgHom.mapDomain φ g := by
  intro a
  have hU₁ := dense_interior_range_comap_twistedLangAlgHom φ hφ 1
  have hU₂ := dense_interior_range_comap_twistedLangAlgHom φ hφ a
  let U₁ := interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ 1).toRingHom))
  let U₂ := interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom))
  have hopen : IsOpen (U₁ ∩ U₂) := isOpen_interior.inter isOpen_interior
  have : Nonempty (PrimeSpectrum H) := ⟨AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom K H)⟩
  have hne : (U₁ ∩ U₂).Nonempty := (hU₁.inter_of_isOpen_left hU₂ isOpen_interior).nonempty
  obtain ⟨y, hy₁, hy₂⟩ :=
    (denseRange_kernelPoint (k := K) (A := H)).exists_mem_open hopen hne
  obtain ⟨x₁, hx₁⟩ :=
    exists_toConv_eq_mul_mul_inv_mapDomain_of_mem_range_comap φ 1 y (interior_subset hy₁)
  obtain ⟨x₂, hx₂⟩ :=
    exists_toConv_eq_mul_mul_inv_mapDomain_of_mem_range_comap φ a y (interior_subset hy₂)
  rw [mul_one] at hx₁
  have hrel := hx₁.symm.trans hx₂
  refine ⟨x₁⁻¹ * x₂, ?_⟩
  dsimp only
  rw [mul_inv_rev, inv_inv, map_mul, map_inv]
  calc
    x₂⁻¹ * x₁ * ((BialgHom.mapDomain φ x₁)⁻¹ * BialgHom.mapDomain φ x₂)
      = x₂⁻¹ * (x₁ * (BialgHom.mapDomain φ x₁)⁻¹) * BialgHom.mapDomain φ x₂ := by
          simp only [mul_assoc]
    _ = x₂⁻¹ * (x₂ * a * (BialgHom.mapDomain φ x₂)⁻¹) * BialgHom.mapDomain φ x₂ := by rw [hrel]
    _ = a := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

section Reduction

variable {H : Type v} [CommRing H] [_root_.HopfAlgebra K H]

/-- Every bialgebra endomorphism of `H` descends to the reduced quotient
`H ⧸ (HopfIdeal.reduction K H).toIdeal`, because it maps nilpotent elements to nilpotent
elements. -/
private noncomputable def reductionBialgHom (φ : H →ₐc[K] H) :
    H ⧸ (HopfIdeal.reduction K H).toIdeal →ₐc[K] H ⧸ (HopfIdeal.reduction K H).toIdeal :=
  let I := HopfIdeal.reduction K H
  let q := Bialgebra.Quotient.mkBialgHom I.toIdeal
  Bialgebra.Quotient.liftBialgHom I.toIdeal (q.comp φ) fun x hx => by
    have hnilx : IsNilpotent x := mem_nilradical.mp (HopfIdeal.reduction_toIdeal K H ▸ hx)
    exact (hnilx.map (q.comp φ).toAlgHom.toRingHom).eq_zero

private theorem reductionBialgHom_comp_mkBialgHom (φ : H →ₐc[K] H) :
    (reductionBialgHom φ).comp (Bialgebra.Quotient.mkBialgHom (HopfIdeal.reduction K H).toIdeal) =
      (Bialgebra.Quotient.mkBialgHom (HopfIdeal.reduction K H).toIdeal).comp φ :=
  Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom _ _ _

/-- The reduced endomorphism inherits vanishing of the differential at the identity. -/
private theorem derivationComp_reductionBialgHom_eq_zero (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) :
    TauCeti.derivationComp (B := K) (reductionBialgHom φ) = 0 := by
  let q : H →ₐc[K] H ⧸ (HopfIdeal.reduction K H).toIdeal :=
    Bialgebra.Quotient.mkBialgHom (HopfIdeal.reduction K H).toIdeal
  ext d : 1
  apply TauCeti.derivationComp_injective_of_surjective q
    (Bialgebra.Quotient.mkBialgHom_surjective (HopfIdeal.reduction K H).toIdeal)
  rw [LinearMap.zero_apply, map_zero, ← LinearMap.comp_apply, ← TauCeti.derivationComp_comp,
    reductionBialgHom_comp_mkBialgHom, TauCeti.derivationComp_comp, hφ, LinearMap.comp_apply,
    LinearMap.zero_apply]

variable (K H) in
/-- Every point of `H` valued in a reduced `K`-algebra factors uniquely through the reduced
quotient `H ⧸ (HopfIdeal.reduction K H).toIdeal`. -/
private noncomputable def reductionPointsMulEquiv (A : Type*) [CommRing A] [IsReduced A]
    [Algebra K A] :
    WithConv ((H ⧸ (HopfIdeal.reduction K H).toIdeal) →ₐ[K] A) ≃* WithConv (H →ₐ[K] A) :=
  let I := HopfIdeal.reduction K H
  let q := Bialgebra.Quotient.mkBialgHom I.toIdeal
  MulEquiv.ofBijective (BialgHom.mapDomain (A := A) q)
    ⟨BialgHom.mapDomain_injective_of_surjective q (Bialgebra.Quotient.mkBialgHom_surjective _),
      fun a => by
        have ha_ker : ∀ x ∈ I.toIdeal, a.ofConv x = 0 := fun x hx =>
          ((mem_nilradical.mp (HopfIdeal.reduction_toIdeal K H ▸ hx)).map
            a.ofConv.toRingHom).eq_zero
        refine ⟨toConv (Ideal.Quotient.liftₐ I.toIdeal a.ofConv ha_ker), ?_⟩
        rw [BialgHom.mapDomain_apply, ofConv_toConv, Bialgebra.Quotient.mkBialgHom_toAlgHom,
          Ideal.Quotient.liftₐ_comp, toConv_ofConv]⟩

private theorem reductionPointsMulEquiv_apply {A : Type*} [CommRing A] [IsReduced A]
    [Algebra K A] (g : WithConv ((H ⧸ (HopfIdeal.reduction K H).toIdeal) →ₐ[K] A)) :
    reductionPointsMulEquiv K H A g =
      BialgHom.mapDomain (A := A) (Bialgebra.Quotient.mkBialgHom (HopfIdeal.reduction K H).toIdeal)
        g :=
  rfl

private theorem reductionPointsMulEquiv_mapDomain_reductionBialgHom {A : Type*} [CommRing A]
    [IsReduced A] [Algebra K A] (φ : H →ₐc[K] H)
    (g : WithConv ((H ⧸ (HopfIdeal.reduction K H).toIdeal) →ₐ[K] A)) :
    reductionPointsMulEquiv K H A (BialgHom.mapDomain (reductionBialgHom φ) g) =
      BialgHom.mapDomain φ (reductionPointsMulEquiv K H A g) := by
  rw [reductionPointsMulEquiv_apply, reductionPointsMulEquiv_apply, ← MonoidHom.comp_apply,
    ← BialgHom.mapDomain_comp, reductionBialgHom_comp_mkBialgHom, BialgHom.mapDomain_comp,
    MonoidHom.comp_apply]

end Reduction

variable {H : Type v} [CommRing H] [_root_.HopfAlgebra K H]
  [Algebra.FiniteType K H] [ConnectedSpace (PrimeSpectrum H)]

/-- **General Lang's theorem**: for a connected finite-type affine algebraic group `Spec H` over an
algebraically closed field `K`, every endomorphism `F = Spec φ` with zero differential at the
identity has surjective Lang map `g ↦ g⁻¹ * F(g)` on `K`-points. -/
theorem surjective_inv_mul_mapDomain (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) :
    Function.Surjective fun g : WithConv (H →ₐ[K] K) =>
      g⁻¹ * BialgHom.mapDomain φ g := by
  let I := HopfIdeal.reduction K H
  have : Algebra.FiniteType K (H ⧸ I.toIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K I.toIdeal)
      (Ideal.Quotient.mkₐ_surjective K I.toIdeal)
  have hIrrH : IrreducibleSpace (PrimeSpectrum H) :=
    _root_.CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace K
      (_root_.CommHopfAlgCat.of K H)
  have : I.toIdeal.IsPrime :=
    HopfIdeal.reduction_toIdeal K H ▸ PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hIrrH
  have hsurj_red := surjective_inv_mul_mapDomain_of_isDomain (reductionBialgHom φ)
    (derivationComp_reductionBialgHom_eq_zero φ hφ)
  let e := reductionPointsMulEquiv K H K
  intro a
  obtain ⟨g_red, hg_red⟩ := hsurj_red (e.symm a)
  refine ⟨e g_red, ?_⟩
  have hcomm := (reductionPointsMulEquiv_mapDomain_reductionBialgHom φ g_red).symm
  dsimp only at hg_red ⊢
  rw [hcomm, ← map_inv, ← map_mul, hg_red, e.apply_symm_apply]

/-- Commutator-map (`g ↦ g / F(g)`) form of `surjective_inv_mul_mapDomain`. -/
theorem surjective_commutatorMap_mapDomain (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) :
    Function.Surjective (MonoidHom.commutatorMap (BialgHom.mapDomain (A := K) φ)) :=
  (MonoidHom.surjective_inv_mul_iff_surjective_commutatorMap _).mp
    (surjective_inv_mul_mapDomain φ hφ)

end AlgClosed

/-! ### Lang's theorem over finite fields -/

section FiniteField

variable {F : Type u} [Field F] [Fintype F]
variable {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K]

/-- **Lang's theorem** (unbundled form): for a geometrically connected finite-type affine group
scheme `Spec H` over a finite field `F`, an algebraically closed extension `K / F`, and any
positive integer `n ≠ 0`, the Lang map `g ↦ g⁻¹ * F^n(g)` of the `|F|^n`-Frobenius is surjective
on `K`-points. -/
theorem surjective_inv_mul_frobeniusPoints {H : Type v} [CommRing H] [_root_.HopfAlgebra F H]
    [Algebra.FiniteType F H] {n : ℕ} (hn : n ≠ 0)
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H)) :
    Function.Surjective fun g : WithConv (H →ₐ[F] K) =>
      g⁻¹ * FiniteField.frobeniusPoints F n g := by
  have : ConnectedSpace (PrimeSpectrum (K ⊗[F] H)) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange F K
      (_root_.CommHopfAlgCat.of F H)).mp hconn
  let ψ : K ⊗[F] H →ₐc[K] K ⊗[F] H := FiniteField.geometricFrobeniusBialgHom F K H
  let iter : ℕ → (K ⊗[F] H →ₐc[K] K ⊗[F] H) :=
    fun k => Nat.rec (BialgHom.id K _) (fun _ f => ψ.comp f) k
  have iter_succ (k : ℕ) : iter (k + 1) = ψ.comp (iter k) := rfl
  have hder : TauCeti.derivationComp (B := K) (iter n) = 0 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [iter_succ, TauCeti.derivationComp_comp,
      FiniteField.derivationComp_geometricFrobeniusBialgHom_eq_zero, LinearMap.comp_zero]
  have hsurj := surjective_inv_mul_mapDomain (iter n) hder
  let e := AlgHom.baseChangePointsMulEquiv (k := F) (K := K) (A := H) (R := K)
  have hcomm : ∀ (k : ℕ) (g' : WithConv (K ⊗[F] H →ₐ[K] K)),
      e.symm (BialgHom.mapDomain (A := K) (iter k) g') =
        FiniteField.frobeniusPoints F k (e.symm g') := by
    intro k
    induction k with
    | zero =>
      intro g'
      simp [iter]
    | succ k ih =>
      intro g'
      rw [iter_succ, BialgHom.mapDomain_comp, MonoidHom.comp_apply, ih]
      have h1 : e.symm (BialgHom.mapDomain (A := K) ψ g') =
          FiniteField.frobeniusPoints F 1 (e.symm g') :=
        DFunLike.congr_fun
          (FiniteField.baseChangePointsMulEquiv_symm_comp_mapDomain_geometricFrobeniusBialgHom
            (K := F) (k := K) (H := H) (R := K)) g'
      rw [h1, ← MonoidHom.comp_apply, ← FiniteField.frobeniusPoints_add]
  intro a
  obtain ⟨g', hg'⟩ := hsurj (e a)
  refine ⟨e.symm g', ?_⟩
  have hsymm := congrArg e.symm hg'
  rw [map_mul, map_inv, e.symm_apply_apply] at hsymm
  exact (congrArg ((e.symm g')⁻¹ * ·) (hcomm n g').symm).trans hsymm

/-- Commutator-map (`g ↦ g / F^n(g)`) form of Lang's theorem over a finite field. -/
theorem surjective_commutatorMap_frobeniusPoints {H : Type v} [CommRing H] [_root_.HopfAlgebra F H]
    [Algebra.FiniteType F H] {n : ℕ} (hn : n ≠ 0)
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H)) :
    Function.Surjective (MonoidHom.commutatorMap
      (FiniteField.frobeniusPoints F n (H := H) (A := K))) :=
  (MonoidHom.surjective_inv_mul_iff_surjective_commutatorMap _).mp
    (surjective_inv_mul_frobeniusPoints hn hconn)

/-- **Lang's theorem**: for a geometrically connected finite-type group over a finite field `F`,
an algebraically closed extension `K / F`, and the `|F|`-power Frobenius `σ : K →ₐ[F] K`, the Lang
map `g ↦ g⁻¹ * σ(g)` is surjective on `H(K)`. -/
theorem lang_surjective (H : FiniteTypeCommHopfAlgCat.{u, v} F)
    (hconn : geometricallyConnectedCommHopfAlgProperty F H.obj)
    (σ : K →ₐ[F] K) (hσ : ∀ z, σ z = z ^ Fintype.card F) :
    Function.Surjective fun g : WithConv (H →ₐ[F] K) =>
      g⁻¹ * toConv (σ.comp g.ofConv) := by
  have hF : ∀ g : WithConv (H →ₐ[F] K),
      toConv (σ.comp g.ofConv) = FiniteField.frobeniusPoints F 1 g :=
    FiniteField.toConv_comp_eq_frobeniusPoints σ (fun z => by rw [pow_one, hσ z])
  simpa only [hF] using
    surjective_inv_mul_frobeniusPoints (F := F) (K := K) (H := H) one_ne_zero hconn

end FiniteField

/-! ### Galois cohomology vanishing and rational-point lifting -/

section GaloisCohomology

/-- Every 1-cocycle satisfies `c 1 = 1`. -/
private theorem cocycle_one_eq_one {Γ M : Type*} [Group Γ] [Group M]
    (act : Γ → M →* M) (hact1 : act 1 = MonoidHom.id M)
    (c : Γ → M) (hc : ∀ γ δ, c (γ * δ) = c γ * act γ (c δ)) :
    c 1 = 1 := by
  have h1 := hc 1 1
  rw [mul_one, hact1, MonoidHom.id_apply] at h1
  exact mul_eq_left.mp h1.symm

/-- If a 1-cocycle `c` agrees (after pushing along an intertwining homomorphism `j`) with a
coboundary `b⁻¹ * F b` on an element `γ`, then it agrees with `b⁻¹ * F^[k] b` on every
nonnegative power `γ ^ k`. -/
private theorem map_cocycle_pow_eq_inv_mul_iterate
    {Γ M G : Type*} [Group Γ] [Group M] [Group G]
    (act : Γ → M →* M) (hact1 : act 1 = MonoidHom.id M)
    (c : Γ → M) (hc : ∀ γ δ, c (γ * δ) = c γ * act γ (c δ))
    (γ : Γ) (j : M →* G) (F : G →* G) (hj : ∀ m, j (act γ m) = F (j m))
    {b : G} (hb : b⁻¹ * F b = j (c γ)) (k : ℕ) :
    b⁻¹ * (⇑F)^[k] b = j (c (γ ^ k)) := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, inv_mul_cancel, pow_zero,
      cocycle_one_eq_one act hact1 c hc, map_one]
  | succ k ih =>
    rw [pow_succ', hc, map_mul, hj, ← ih, ← hb, Function.iterate_succ_apply']
    simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]

/-- **Vanishing of non-abelian Galois `H¹` over a finite field** (`H¹(F, H) = 1`, Lang's theorem):
for a geometrically connected finite-type affine group scheme `Spec H` over a field `F` and a finite
field extension `L / F`, every Galois 1-cocycle `c : (L ≃ₐ[F] L) → WithConv (H →ₐ[F] L)` is a
coboundary `γ ↦ b⁻¹ * γ(b)`. -/
theorem exists_eq_inv_mul_mapValue_of_mul_eq_mul_mapValue
    {F : Type u} [Field F]
    {L : Type w} [Field L] [Finite L] [Algebra F L]
    {H : Type v} [CommRing H] [_root_.HopfAlgebra F H] [Algebra.FiniteType F H]
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H))
    (c : (L ≃ₐ[F] L) → WithConv (H →ₐ[F] L))
    (hc : ∀ γ δ, c (γ * δ) = c γ * AlgHom.mapValue γ.toAlgHom (c δ)) :
    ∃ b : WithConv (H →ₐ[F] L), ∀ γ, c γ = b⁻¹ * AlgHom.mapValue γ.toAlgHom b := by
  have : Finite F := Finite.of_injective _ (algebraMap F L).injective
  have : Fintype F := Fintype.ofFinite F
  have : Fintype L := Fintype.ofFinite L
  let K := AlgebraicClosure L
  let ι : L →ₐ[F] K := IsScalarTower.toAlgHom F L K
  let φ : L ≃ₐ[F] L := _root_.FiniteField.frobeniusAlgEquivOfAlgebraic F L
  let act : (L ≃ₐ[F] L) → WithConv (H →ₐ[F] L) →* WithConv (H →ₐ[F] L) :=
    fun γ => AlgHom.mapValue γ.toAlgHom
  have hact1 : act 1 = MonoidHom.id _ := by
    have h1id : (1 : L ≃ₐ[F] L).toAlgHom = AlgHom.id F L := AlgHom.ext fun _ => rfl
    dsimp only [act]
    rw [h1id, AlgHom.mapValue_id]
  have hc1 : c 1 = 1 := cocycle_one_eq_one act hact1 c hc
  have hιφ : ∀ (k : ℕ) (x : WithConv (H →ₐ[F] L)),
      AlgHom.mapValue ι (AlgHom.mapValue (φ ^ k).toAlgHom x) =
        FiniteField.frobeniusPoints F k (AlgHom.mapValue ι x) := by
    intro k x
    have hφk : AlgHom.mapValue (φ ^ k).toAlgHom x = FiniteField.frobeniusPoints F k x := by
      rw [AlgHom.mapValue_apply]
      exact FiniteField.toConv_comp_eq_frobeniusPoints (φ ^ k).toAlgHom (fun z => by
        have hit := congrFun (_root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate F L k) z
        simpa [AlgEquiv.coe_pow] using hit) x
    rw [hφk]
    exact DFunLike.congr_fun (FiniteField.mapValue_comp_frobeniusPoints ι k) x
  have hfrob_iter : ∀ k : ℕ,
      (⇑(FiniteField.frobeniusPoints F 1 (H := H) (A := K)))^[k] =
        FiniteField.frobeniusPoints F k := by
    intro k
    induction k with
    | zero => ext g; simp [FiniteField.frobeniusPoints_zero]
    | succ k ih =>
      ext g
      rw [Function.iterate_succ_apply', ih, ← MonoidHom.comp_apply,
        ← FiniteField.frobeniusPoints_add, add_comm 1 k]
  obtain ⟨bK, hbK⟩ :=
    surjective_inv_mul_frobeniusPoints (F := F) (K := K) (H := H) one_ne_zero hconn
      (AlgHom.mapValue ι (c φ))
  dsimp only at hbK
  have hiter : ∀ k : ℕ,
      bK⁻¹ * FiniteField.frobeniusPoints F k bK = AlgHom.mapValue ι (c (φ ^ k)) := by
    intro k
    rw [← hfrob_iter k]
    exact map_cocycle_pow_eq_inv_mul_iterate act hact1 c hc φ
      (AlgHom.mapValue (H := H) ι) (FiniteField.frobeniusPoints F 1)
      (fun m => by simpa only [pow_one, act] using hιφ 1 m) hbK k
  have hfix : FiniteField.frobeniusPoints F (Module.finrank F L) bK = bK := by
    have hpow1 : φ ^ Module.finrank F L = 1 := by
      rw [← _root_.FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F L, pow_orderOf_eq_one]
    have h := hiter (Module.finrank F L)
    rw [hpow1, hc1, map_one] at h
    exact (inv_mul_eq_one.mp h).symm
  obtain ⟨b, hb⟩ : bK ∈ (AlgHom.mapValue (H := H) ι).range := by
    rw [FiniteField.range_mapValue]
    exact mem_fixedSubgroup.mpr hfix
  refine ⟨b, fun γ => ?_⟩
  obtain ⟨n, rfl⟩ := (_root_.FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F L).2 γ
  apply AlgHom.mapValue_injective ι.toRingHom.injective
  rw [map_mul, map_inv, hιφ n.val, hb]
  exact (hiter n.val).symm

end GaloisCohomology

section RationalPoints

variable {F : Type u} [Field F] [Finite F]
variable {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K]

/-- **Surjectivity on rational points for exact sequences with connected kernel** (a consequence
of Lang's theorem / `H¹(F, H₃) = 1`): if `Spec H₃ → Spec H₂ → Spec H₁` is exact at `Spec H₂` and
surjective at `Spec H₁` on `K`-points over an algebraically closed extension `K / F`, and
`Spec H₃` is geometrically connected of finite type over `F`, then `Spec H₂(F) → Spec H₁(F)` is
surjective. -/
theorem mapDomain_surjective_of_surjective_of_range_eq_ker
    {H₁ H₂ H₃ : Type*} [Semiring H₁] [Semiring H₂] [CommRing H₃]
    [_root_.HopfAlgebra F H₁] [_root_.HopfAlgebra F H₂] [_root_.HopfAlgebra F H₃]
    [Algebra.FiniteType F H₃]
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H₃))
    (φ : H₁ →ₐc[F] H₂) (ψ : H₂ →ₐc[F] H₃)
    (hsurj : Function.Surjective (BialgHom.mapDomain (A := K) φ))
    (hker : (BialgHom.mapDomain (A := K) ψ).range = (BialgHom.mapDomain (A := K) φ).ker) :
    Function.Surjective (BialgHom.mapDomain (A := F) φ) := by
  have : Fintype F := Fintype.ofFinite F
  intro y
  let e₁ := FiniteField.rationalPointsMulEquiv F H₁ K
  let e₂ := FiniteField.rationalPointsMulEquiv F H₂ K
  have hyK : FiniteField.frobeniusPoints F 1 (e₁ y : WithConv (H₁ →ₐ[F] K)) =
      (e₁ y : WithConv (H₁ →ₐ[F] K)) := mem_fixedSubgroup.mp (e₁ y).property
  obtain ⟨xK, hxK_fix, hxK_map⟩ :=
    MonoidHom.exists_fixed_lift_of_surjective_commutatorMap
      (BialgHom.mapDomain (A := K) φ) (BialgHom.mapDomain (A := K) ψ) hker
      (FiniteField.frobeniusPoints F 1) (FiniteField.frobeniusPoints F 1)
      (FiniteField.frobeniusPoints F 1)
      (fun g => DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints φ 1) g)
      (fun t => (DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints ψ 1) t).symm)
      hsurj (surjective_commutatorMap_frobeniusPoints (K := K) one_ne_zero hconn) hyK
  refine ⟨e₂.symm ⟨xK, mem_fixedSubgroup.mpr hxK_fix⟩, e₁.injective (Subtype.ext ?_)⟩
  rw [FiniteField.coe_rationalPointsMulEquiv_mapDomain, e₂.apply_symm_apply]
  exact hxK_map

end RationalPoints

end TauCeti.Lang
