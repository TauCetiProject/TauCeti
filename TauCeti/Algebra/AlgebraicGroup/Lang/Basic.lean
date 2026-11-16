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
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Tangent.DerivationMap
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible
import TauCeti.Algebra.AlgebraicGroup.Hopf.LeftTranslation
import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation
import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
import TauCeti.Algebra.AlgebraicGroup.Tangent.Map
import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense
import TauCeti.GroupTheory.FixedSubgroup.Lang
import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints
import TauCeti.RingTheory.Noetherian.RingHom
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.Topology.Constructible.Basic

/-!
# Lang's theorem for smooth connected algebraic groups

For a smooth connected finite-type affine algebraic group `G = Spec H` over an algebraically closed
field `K`, every endomorphism `F = Spec φ` of `G` whose differential at the identity vanishes has a
surjective Lang map `g ↦ g⁻¹ * F(g)` on `G(K)` (`TauCeti.Lang.surjective_inv_mul_mapDomain`).

The proof avoids explicit comultiplication coordinates by working in the convolution group of
algebra-valued points:

1. For each `a ∈ G(K)`, the twisted Lang morphism `x ↦ x * a * F(x)⁻¹` is represented by the
   coordinate endomorphism `TauCeti.Lang.twistedLangAlgHom φ a`. Precomposing with left translation
   by `a⁻¹` produces an identity-preserving endomorphism whose differential at the identity
   agrees with that of conjugation by `a⁻¹`, hence is an isomorphism on the cotangent space at the
   identity.
2. Since `H` is a Noetherian integral domain, surjectivity on the residue field and cotangent space
   implies injectivity of the twisted Lang comorphism (`TauCeti.Lang.twistedLangAlgHom_injective`)
   via Krull's intersection theorem and the Hopfian property of Noetherian quotients
   (`AlgHom.injective_of_surjective_mapCotangent`).
3. By Chevalley's constructibility theorem, the images of the twisted Lang morphisms for `1` and `a`
   contain dense open subsets of `Spec H`. Their intersection contains a `K`-rational point, giving
   `x₁, x₂ ∈ G(K)` with `x₁ * F(x₁)⁻¹ = x₂ * a * F(x₂)⁻¹`; then `g = x₁⁻¹ * x₂` satisfies
   `g⁻¹ * F(g) = a`.

Over a finite field `F` of cardinality `q`, the geometric Frobenius `id ⊗ Frob` on `K ⊗[F] H`
has zero differential (`TauCeti.FiniteField.derivationComp_geometricFrobeniusBialgHom`). Applying
the general theorem to the base change of a smooth geometrically connected finite-type affine group
scheme over `F` yields Lang's theorem (`TauCeti.Lang.surjective_inv_mul_frobeniusPoints` and
`TauCeti.Lang.lang_surjective`), together with surjectivity on `F`-rational points for exact
sequences with smooth geometrically connected kernel
(`TauCeti.Lang.surjective_rationalPoints_of_exact`).

## Main definitions

* `TauCeti.Lang.twistedLangAlgHom`: the coordinate-algebra endomorphism representing
  `x ↦ x * a * F(x)⁻¹`.

## Main results

* `TauCeti.Lang.twistedLangAlgHom_injective`: for a zero-differential bialgebra endomorphism of a
  Noetherian integral-domain Hopf algebra over a field, every twisted Lang comorphism is injective.
* `TauCeti.Lang.surjective_inv_mul_mapDomain`: over an algebraically closed field, any
  zero-differential endomorphism of a smooth connected finite-type group has surjective Lang map.
* `TauCeti.FiniteField.derivationComp_geometricFrobeniusBialgHom`: the geometric Frobenius
  `id ⊗ Frob` has zero differential.
* `TauCeti.Lang.surjective_inv_mul_frobeniusPoints` and `TauCeti.Lang.lang_surjective`: Lang's
  theorem for smooth geometrically connected finite-type affine group schemes over finite fields.
* `TauCeti.Lang.surjective_rationalPoints_of_exact`: an exact sequence on geometric points whose
  kernel is smooth and geometrically connected over a finite field `F` is surjective on `F`-points.

## References

* S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 27.54, Corollary 27.55, and Corollary 27.56.
-/

public section

open WithConv Topology
open scoped TensorProduct

universe u v w

namespace TauCeti

/-! ### Zero differential of the geometric Frobenius -/

namespace FiniteField

/-- The differential of the geometric Frobenius `id ⊗ Frob` on a base change `K ⊗[F] H` vanishes
identically: every `K`-derivation annihilates `q`-th powers because `q = |F|` is zero in `K`. -/
theorem derivationComp_geometricFrobeniusBialgHom
    (F : Type u) [Field F] [Fintype F]
    (K : Type w) [CommSemiring K] [Algebra F K]
    (H : Type v) [CommSemiring H] [_root_.Bialgebra F H]
    {B : Type*} [Semiring B] [Algebra K B] :
    TauCeti.derivationComp (B := B) (geometricFrobeniusBialgHom F K H) = 0 := by
  have hcardF : (Fintype.card F : F) = 0 := by
    have : CharP F (ringChar F) := ringChar.charP F
    obtain ⟨n, _, hq⟩ := _root_.FiniteField.card F (ringChar F)
    rw [hq, Nat.cast_pow, CharP.cast_eq_zero F (ringChar F), zero_pow n.pos.ne']
  have hcardK : (Fintype.card F : K) = 0 := by
    rw [← map_natCast (algebraMap F K), hcardF, map_zero]
  ext d x : 2
  rw [TauCeti.derivationComp_apply, LinearMap.zero_apply, zero_apply]
  induction x using TensorProduct.inductionOn with
  | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  | tmul s h =>
    have htmul :
        (geometricFrobeniusBialgHom F K H : K ⊗[F] H →ₐ[K] K ⊗[F] H) (s ⊗ₜ[F] h) =
          s • (((1 : K) ⊗ₜ[F] h) ^ Fintype.card F) := by
      rw [BialgHom.coe_toAlgHom, geometricFrobeniusBialgHom_tmul, Algebra.TensorProduct.tmul_pow,
        one_pow, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [htmul, Derivation.map_smul, d.leibniz_pow (a := (1 : K) ⊗ₜ[F] h) (Fintype.card F),
      ← Nat.cast_smul_eq_nsmul K, hcardK, zero_smul, smul_zero]

end FiniteField

namespace Lang

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
    rw [AlgHom.convOne_def]
    exact congrArg toConv (by ext x; simp)
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
      rw [tangentKerMap_derivationMulEquivTangentKer, toAdd_ofAdd, hφ, LinearMap.zero_apply]
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
      ⟨twistedLangAtId φ a x.1, Ideal.mem_comap.mp (hfI x.2)⟩,
    ← Bialgebra.cotangentMap_augmentation K H x, Bialgebra.cotangentSpaceMap_cotangentMap]
  let d := Derivation.cotangentLinearEquiv (R := K) (A := H) (B := K) f
  rw [← Derivation.algEquivSelf_cotangentLinearEquiv_apply f,
    ← Derivation.algEquivSelf_cotangentLinearEquiv_apply f]
  have he : ((HopfAlgebra.pointConjugationBialgEquiv a⁻¹).toBialgHom : H →ₐ[K] H) =
      HopfAlgebra.pointConjugationAlgHom a⁻¹ := by
    rw [BialgEquiv.toBialgHom_eq_coe]
    exact HopfAlgebra.pointConjugationBialgEquiv_toAlgHom a⁻¹
  have hex : (HopfAlgebra.pointConjugationBialgEquiv a⁻¹).toBialgHom x.1 =
      HopfAlgebra.pointConjugationAlgHom a⁻¹ x.1 := AlgHom.congr_fun he x.1
  rw [hex]
  exact congrArg (Bialgebra.CounitAlgebra.algEquivSelf K H K)
    (derivation_comp_twistedLangAtId φ hφ a d x.1)

/-- If `φ : H →ₐc[K] H` is a bialgebra endomorphism with zero differential on a Noetherian
integral-domain Hopf algebra over a field, then every twisted Lang comorphism
`twistedLangAlgHom φ a` is injective. -/
theorem twistedLangAlgHom_injective [IsNoetherianRing H] [IsDomain H]
    (φ : H →ₐc[K] H) (hφ : TauCeti.derivationComp (B := K) φ = 0)
    (a : WithConv (H →ₐ[K] K)) :
    Function.Injective (twistedLangAlgHom φ a) := by
  let I : Ideal H := Bialgebra.AugmentationIdeal K H
  have hI_ne_top : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : H) ∈ I := htop.symm ▸ Submodule.mem_top
    have hzero : (1 : K) = 0 := by
      simpa only [I, Bialgebra.AugmentationIdeal, RingHom.mem_ker, map_one] using h1
    exact one_ne_zero hzero
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
  exact congrArg (HopfAlgebra.leftTranslationAlgEquiv a⁻¹) (hinj_atId hxy)

/-- Each twisted Lang comorphism is of finite type and its induced map on `PrimeSpectrum H` has
image with dense interior. -/
private theorem twistedLangAlgHom_finiteType_and_dense_interior
    [Algebra.FiniteType K H] [IsDomain H] [IsNoetherianRing H]
    (φ : H →ₐc[K] H) (hφ : TauCeti.derivationComp (B := K) φ = 0)
    (a : WithConv (H →ₐ[K] K)) :
    (twistedLangAlgHom φ a).toRingHom.FiniteType ∧
      Dense (interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom))) := by
  have hft : (twistedLangAlgHom φ a).toRingHom.FiniteType :=
    RingHom.FiniteType.of_comp_finiteType (f := algebraMap K H)
      (g := (twistedLangAlgHom φ a).toRingHom)
      ((twistedLangAlgHom φ a).comp_algebraMap.symm ▸
        RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType K H))
  have hfp := RingHom.FinitePresentation.of_finiteType.mp hft
  have hd : DenseRange (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom) :=
    RingHom.denseRange_comap_of_injective _ (twistedLangAlgHom_injective φ hφ a)
  exact ⟨hft, (PrimeSpectrum.isConstructible_range_comap hfp).dense_interior hd⟩

end Injectivity

/-! ### Lang's theorem for zero-differential endomorphisms over algebraically closed fields -/

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {H : Type v} [CommRing H] [_root_.HopfAlgebra K H]
  [Algebra.FiniteType K H] [Algebra.Smooth K H] [ConnectedSpace (PrimeSpectrum H)]

/-- **General Lang's theorem**: for a smooth connected finite-type affine algebraic group `Spec H`
over an algebraically closed field `K`, every endomorphism `F = Spec φ` with zero differential at
the identity has surjective Lang map `g ↦ g⁻¹ * F(g)` on `K`-points. -/
theorem surjective_inv_mul_mapDomain (φ : H →ₐc[K] H)
    (hφ : TauCeti.derivationComp (B := K) φ = 0) :
    Function.Surjective fun g : WithConv (H →ₐ[K] K) =>
      g⁻¹ * BialgHom.mapDomain φ g := by
  -- Smooth + connected finite-type Hopf algebra over `K` is a Noetherian integral domain.
  have : IrreducibleSpace (PrimeSpectrum H) :=
    _root_.CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace K
      (_root_.CommHopfAlgCat.of K H)
  have : IsReduced H := isReduced_of_smooth K H
  have hnil : (nilradical H).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp ‹_›
  rw [nilradical_eq_zero, Ideal.zero_eq_bot] at hnil
  have : IsDomain H := IsDomain.of_bot_isPrime H
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing K H
  -- Intersect the dense open interiors of the images of the twisted Lang maps for `1` and `a`.
  intro a
  obtain ⟨hft₁, hU₁⟩ := twistedLangAlgHom_finiteType_and_dense_interior φ hφ 1
  obtain ⟨hft₂, hU₂⟩ := twistedLangAlgHom_finiteType_and_dense_interior φ hφ a
  let U₁ := interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ 1).toRingHom))
  let U₂ := interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ a).toRingHom))
  have hopen : IsOpen (U₁ ∩ U₂) := isOpen_interior.inter isOpen_interior
  have : Nonempty (PrimeSpectrum H) := ⟨AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom K H)⟩
  have hne : (U₁ ∩ U₂).Nonempty := (hU₁.inter_of_isOpen_left hU₂ isOpen_interior).nonempty
  obtain ⟨y, hy₁, hy₂⟩ :=
    (denseRange_kernelPoint (k := K) (A := H)).exists_mem_open hopen hne
  -- Lift the common rational point `y` along both twisted Lang morphisms.
  have lift_point : ∀ (b : WithConv (H →ₐ[K] K)),
      (twistedLangAlgHom φ b).toRingHom.FiniteType →
      AlgHom.kernelPoint y ∈
        interior (Set.range (PrimeSpectrum.comap (twistedLangAlgHom φ b).toRingHom)) →
      ∃ x : H →ₐ[K] K, x.comp (twistedLangAlgHom φ b) = y := by
    intro b hft hb
    obtain ⟨P, hP⟩ := interior_subset hb
    have hP' : PrimeSpectrum.comap (twistedLangAlgHom φ b).toRingHom P =
        ⟨RingHom.ker y.toRingHom, RingHom.ker_isPrime y.toRingHom⟩ := by
      apply PrimeSpectrum.ext
      exact (congrArg PrimeSpectrum.asIdeal hP).trans (AlgHom.kernelPoint_asIdeal y)
    exact _root_.AlgHom.exists_comp_eq_of_comap_eq_ker (twistedLangAlgHom φ b) hft y P hP'
  obtain ⟨x₁, hx₁⟩ := lift_point 1 hft₁ hy₁
  obtain ⟨x₂, hx₂⟩ := lift_point a hft₂ hy₂
  have hofId : AlgHom.mapValue (H := H) (Algebra.ofId K K) a = a :=
    ofConv_injective (by ext h; simp)
  have heq₁ : toConv y = toConv x₁ * (BialgHom.mapDomain φ (toConv x₁))⁻¹ := by
    have h := toConv_comp_twistedLangAlgHom φ 1 (toConv x₁)
    rw [ofConv_toConv, hx₁, map_one, mul_one] at h
    exact h
  have heq₂ : toConv y = toConv x₂ * a * (BialgHom.mapDomain φ (toConv x₂))⁻¹ := by
    have h := toConv_comp_twistedLangAlgHom φ a (toConv x₂)
    rw [ofConv_toConv, hx₂, hofId] at h
    exact h
  -- Solve `g⁻¹ * F(g) = a` with `g = x₁⁻¹ * x₂`.
  have hrel := heq₁.symm.trans heq₂
  refine ⟨(toConv x₁)⁻¹ * toConv x₂, ?_⟩
  dsimp only
  rw [mul_inv_rev, inv_inv, map_mul, map_inv]
  calc
    (toConv x₂)⁻¹ * toConv x₁ * ((BialgHom.mapDomain φ (toConv x₁))⁻¹ *
        BialgHom.mapDomain φ (toConv x₂))
      = (toConv x₂)⁻¹ * (toConv x₁ * (BialgHom.mapDomain φ (toConv x₁))⁻¹) *
          BialgHom.mapDomain φ (toConv x₂) := by simp only [mul_assoc]
    _ = (toConv x₂)⁻¹ * (toConv x₂ * a * (BialgHom.mapDomain φ (toConv x₂))⁻¹) *
          BialgHom.mapDomain φ (toConv x₂) := by rw [hrel]
    _ = a := by simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

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

/-- **Lang's theorem** (unbundled form): for a smooth geometrically connected finite-type affine
group scheme `Spec H` over a finite field `F` and an algebraically closed extension `K / F`, the
Lang map `g ↦ g⁻¹ * F(g)` of the `|F|`-Frobenius is surjective on `K`-points. -/
theorem surjective_inv_mul_frobeniusPoints {H : Type v} [CommRing H] [_root_.HopfAlgebra F H]
    [Algebra.FiniteType F H] [Algebra.Smooth F H]
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H)) :
    Function.Surjective fun g : WithConv (H →ₐ[F] K) =>
      g⁻¹ * FiniteField.frobeniusPoints F 1 g := by
  have : ConnectedSpace (PrimeSpectrum (K ⊗[F] H)) :=
    (geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace_baseChange F K
      (_root_.CommHopfAlgCat.of F H)).mp hconn
  have hsurj := surjective_inv_mul_mapDomain
    (FiniteField.geometricFrobeniusBialgHom F K H)
    (FiniteField.derivationComp_geometricFrobeniusBialgHom F K H)
  let e := AlgHom.baseChangePointsMulEquiv (k := F) (K := K) (A := H) (R := K)
  intro a
  obtain ⟨g', hg'⟩ := hsurj (e a)
  refine ⟨e.symm g', ?_⟩
  have hcomm : e.symm (BialgHom.mapDomain (A := K)
      (FiniteField.geometricFrobeniusBialgHom F K H) g') =
      FiniteField.frobeniusPoints F 1 (e.symm g') :=
    DFunLike.congr_fun
      (FiniteField.baseChangePointsMulEquiv_symm_comp_mapDomain_geometricFrobeniusBialgHom
        (K := F) (k := K) (H := H) (R := K)) g'
  have hsymm := congrArg e.symm hg'
  rw [map_mul, map_inv, e.symm_apply_apply] at hsymm
  exact (congrArg ((e.symm g')⁻¹ * ·) hcomm.symm).trans hsymm

/-- Commutator-map (`g ↦ g / F(g)`) form of Lang's theorem over a finite field. -/
theorem surjective_commutatorMap_frobeniusPoints {H : Type v} [CommRing H] [_root_.HopfAlgebra F H]
    [Algebra.FiniteType F H] [Algebra.Smooth F H]
    (hconn : geometricallyConnectedCommHopfAlgProperty F (_root_.CommHopfAlgCat.of F H)) :
    Function.Surjective (MonoidHom.commutatorMap
      (FiniteField.frobeniusPoints F 1 (H := H) (A := K))) :=
  (MonoidHom.surjective_inv_mul_iff_surjective_commutatorMap _).mp
    (surjective_inv_mul_frobeniusPoints hconn)

/-- **Lang's theorem**: for a smooth geometrically connected finite-type group over a finite field
`F`, an algebraically closed extension `K / F`, and the `|F|`-power Frobenius `σ : K →ₐ[F] K`,
the Lang map `g ↦ g⁻¹ * σ(g)` is surjective on `H(K)`. -/
theorem lang_surjective (H : FiniteTypeCommHopfAlgCat.{u, v} F)
    (hsm : smoothCommHopfAlgProperty F H.obj)
    (hconn : geometricallyConnectedCommHopfAlgProperty F H.obj)
    (σ : K →ₐ[F] K) (hσ : ∀ z, σ z = z ^ Fintype.card F) :
    Function.Surjective fun g : WithConv (H →ₐ[F] K) =>
      g⁻¹ * toConv (σ.comp g.ofConv) := by
  have : Algebra.Smooth F H := (smoothCommHopfAlgProperty_iff H.obj).mp hsm
  have hF : ∀ g : WithConv (H →ₐ[F] K),
      toConv (σ.comp g.ofConv) = FiniteField.frobeniusPoints F 1 g := by
    intro g
    apply ofConv_injective
    ext h
    rw [ofConv_toConv, AlgHom.comp_apply, hσ, FiniteField.frobeniusPoints_apply_apply, pow_one,
      Nat.card_eq_fintype_card]
  simpa only [hF] using surjective_inv_mul_frobeniusPoints (F := F) (K := K) (H := H) hconn

end FiniteField

section RationalPoints

variable {F : Type u} [Field F] [Finite F]
variable {K : Type w} [Field K] [Algebra F K] [IsAlgClosed K]

/-- **Surjectivity on rational points for exact sequences with smooth connected kernel**
(a consequence of Lang's theorem / `H¹(F, H₃) = 1`): if `Spec H₃ → Spec H₂ → Spec H₁` is exact
at `Spec H₂` and surjective at `Spec H₁` on `K`-points over an algebraically closed extension
`K / F`, and `Spec H₃` is smooth and geometrically connected of finite type over `F`, then
`Spec H₂(F) → Spec H₁(F)` is surjective. -/
theorem surjective_rationalPoints_of_exact
    {H₁ H₂ H₃ : Type*} [CommRing H₁] [CommRing H₂] [CommRing H₃]
    [_root_.HopfAlgebra F H₁] [_root_.HopfAlgebra F H₂] [_root_.HopfAlgebra F H₃]
    [Algebra.FiniteType F H₃] [Algebra.Smooth F H₃]
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
      (e₁ y : WithConv (H₁ →ₐ[F] K)) := (e₁ y).2
  obtain ⟨xK, hxK_fix, hxK_map⟩ :=
    MonoidHom.exists_fixed_lift_of_surjective_commutatorMap
      (BialgHom.mapDomain (A := K) φ) (BialgHom.mapDomain (A := K) ψ) hker
      (FiniteField.frobeniusPoints F 1) (FiniteField.frobeniusPoints F 1)
      (FiniteField.frobeniusPoints F 1)
      (fun g => DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints φ 1) g)
      (fun t => (DFunLike.congr_fun (FiniteField.mapDomain_comp_frobeniusPoints ψ 1) t).symm)
      hsurj (surjective_commutatorMap_frobeniusPoints (K := K) hconn) hyK
  refine ⟨e₂.symm ⟨xK, hxK_fix⟩, e₁.injective (Subtype.ext ?_)⟩
  rw [FiniteField.coe_rationalPointsMulEquiv_mapDomain, e₂.apply_symm_apply]
  exact hxK_map

end RationalPoints

end Lang

end TauCeti
