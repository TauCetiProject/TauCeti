/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SelmerGroupA
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.SquarefreeDiscriminant
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension

/-!
# The semilocal comparison of `2`-descent at the finite places

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal form
over a number field `F`, with étale algebra `W.A = F[X] ⧸ (f)` and square classes `W.M`, and let
`S` be a set of finite places of `F`. Two subgroups cut out by valuation conditions are in play:

* `W.selmerGroupA (𝓞 F) S` — the condition `A(S,2)` of being unramified outside `S`, a *global*
  condition at the primes of the rings of integers of the field factors of `W.A` not lying above
  `S`;
* `(W⁄F_v).toAffine.selmerGroupA 𝒪_v ∅` — the condition of being unramified, for the curve
  base-changed to the completion at a finite place `v`.

This file compares the two at the places outside `S`, in both directions: a class unramified
outside `S` localizes to an unramified class at each place `v ∉ S`, and conversely a class that
localizes to an unramified class at every place `v ∉ S` is unramified outside `S`. At a place `v`
at which `a₂`, `a₄` and `a₆` are integral and `disc f` has valuation at most `1`, Step 6 of weak
Mordell–Weil over the completion puts the local descent image among the unramified classes
(`range_μ_le_selmerGroupA_empty`). Combined with the local-to-global direction, a class whose
localization lies in the local descent image at every finite place outside `S` lies in `A(S,2)`,
for any `S` outside which these conditions hold.

## Main results

* `WeierstrassCurve.Affine.range_μ_le_selmerGroupA_empty`: at a finite place with integral
  coefficients and `disc f` of valuation at most `1`, the local descent image over the completion
  is unramified, in every residue characteristic.
* `WeierstrassCurve.Affine.localRes_mem_selmerGroupA` (global to local): a square class
  unramified outside `S` localizes to an unramified class at every finite place outside `S`.
* `WeierstrassCurve.Affine.mem_selmerGroupA_of_forall_localRes` (local to global): a square class
  that localizes to an unramified class at every finite place outside `S` is unramified outside
  `S`.

## Provenance

Adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache 2.0, by Michael Stoll) at commit
`66889eada51a`: `EllipticCurves/SelmerGroup.lean`, section `Semilocal`, together with
`AdjoinRoot.map_comp_algebraMap` from `EllipticCurves/Mathlib/Basic.lean`. The source states
square classes as its own `Units.modPow`; they are re-spelled here to this repository's single
spelling `Mˣ ⧸ (powMonoidHom n).range`, and `HeightOneSpectrum.below` is Mathlib's
`HeightOneSpectrum.under`. `range_μ_le_selmerGroupA_empty` is the source's
`range_μ_le_selmerGroupA_empty_of_exp_neg_one_le_discr` at its later revision `3bfe124`,
`EllipticCurves/SelmerGroup.lean`.

-/

public section

open IsDedekindDomain NumberField Polynomial


namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [NumberField F] (W : Affine F)

/- Notation local to this file: `F_[v]` and `𝒪_[v]` are the completion of `F` at the finite place
`v` and its valuation ring, `𝕎[v]` is the base change of `W` to `F_[v]` as an affine curve, and
`𝕃 p` is the field factor `F[X] ⧸ (p)` of the étale algebra attached to a factor `p` of `f`. -/
local notation:max "F_[" v "]" => HeightOneSpectrum.adicCompletion F v
local notation:max "𝒪_[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v
local notation:max "𝕎[" v "]" =>
  WeierstrassCurve.toAffine (W⁄(HeightOneSpectrum.adicCompletion F v))
local notation:max "𝕃" p:max => AdjoinRoot (p : F[X])

section Semilocal

open AdjoinRoot IsDedekindDomain.HeightOneSpectrum
open scoped AdicCompletionExtension

variable (v : HeightOneSpectrum (𝓞 F))

/- The instance found by unifying through the `ringOfIntegersFactor` abbreviation carries
mismatched `SMul` arguments; pin them to the `Algebra`-derived ones. -/
private instance instIsScalarTowerRingOfIntegersFactor (p : W.f.Factors) :
    @IsScalarTower (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq' rfl

/- The base-change map on a field factor is integral on the ring of integers. -/
private lemma isIntegral_mapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (x : W.ringOfIntegersFactor (𝓞 F) p) :
    _root_.IsIntegral 𝒪_[v] (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  refine ⟨P.map (algebraMap (𝓞 F) 𝒪_[v]), hPm.map _, ?_⟩
  have h2 := congrArg (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) hPe
  rw [map_zero, Polynomial.hom_eval₂] at h2
  rw [Polynomial.eval₂_map]
  exact (congrArg (fun φ ↦ Polynomial.eval₂ φ
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (x : 𝕃 p)) P)
    (AdjoinRoot.map_comp_algebraMap v hq)).symm.trans h2

/- The base-change map on the rings of integers of the field factors: the restriction of
`AdjoinRoot.map` to the integral closures. -/
private noncomputable def integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    W.ringOfIntegersFactor (𝓞 F) p →+* 𝕎[v].ringOfIntegersFactor 𝒪_[v] q :=
  ((AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
    (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p))).codRestrict
      (integralClosure 𝒪_[v] (AdjoinRoot (q : F_[v][X]))).toSubring
      fun x ↦ W.isIntegral_mapOfDvd v hq x

/- The square of ring homomorphisms defining `integerMapOfDvd`. -/
private lemma algebraMap_comp_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (algebraMap (𝕎[v].ringOfIntegersFactor 𝒪_[v] q) (AdjoinRoot (q : F_[v][X]))).comp
        (W.integerMapOfDvd v hq) =
      (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq).comp
        (algebraMap (W.ringOfIntegersFactor (𝓞 F) p) (𝕃 p)) :=
  RingHom.ext fun _ ↦ rfl

/- The square `𝓞 F → 𝒪_v → B_q` versus `𝓞 F → B_p → B_q` on the rings of integers. -/
private lemma integerMapOfDvd_comp_algebraMap {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) :
    (W.integerMapOfDvd v hq).comp (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) =
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)).comp
        (algebraMap (𝓞 F) 𝒪_[v]) := by
  ext c
  exact RingHom.congr_fun (AdjoinRoot.map_comp_algebraMap v hq) c

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/- The square `F → F_v → (F[X] ⧸ (p))_w` = `F → F[X] ⧸ (p) → (F[X] ⧸ (p))_w` of coefficient maps. -/
private lemma algebraMap_adicCompletion_comp (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap F_[v] (w.adicCompletion (𝕃 p))).comp (algebraMap F F_[v]) =
      (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).comp (algebraMap F (𝕃 p)) :=
  RingHom.ext fun c ↦ by
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_adicCompletionExtensionAlgebra]
    exact adicCompletionExtension_coe F (𝕃 p) v w c

/- Evaluating a base-changed polynomial at the image of the root in the completion. -/
private lemma aeval_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (g : F[X]) :
    Polynomial.aeval (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X])))
        (g.map (algebraMap F F_[v])) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (AdjoinRoot.mk (p : F[X]) g) := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← aeval_eq, Polynomial.aeval_def,
    Polynomial.hom_eval₂]
  exact congrArg (fun φ ↦ Polynomial.eval₂ φ
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) g)
    (W.algebraMap_adicCompletion_comp v p w)

/- The image of the root in the completion is integral over `F_v`. -/
private lemma isIntegral_root_adicCompletion (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    _root_.IsIntegral F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) := by
  refine ⟨(p : F[X]).map (algebraMap F F_[v]), p.monic.map _, ?_⟩
  rw [← Polynomial.aeval_def, W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_self, map_zero]

/- The local factor of `f` attached to a place `w` of the field factor `F[X] ⧸ (p)` above `v`: the
minimal polynomial over `F_v` of the image of the root in the completion at `w`. -/
private noncomputable def localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].f.Factors :=
  ⟨minpoly F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))),
    minpoly.irreducible (W.isIntegral_root_adicCompletion v p w),
    minpoly.monic (W.isIntegral_root_adicCompletion v p w), by
      rw [baseChange_f]
      refine minpoly.dvd _ _ ?_
      rw [W.aeval_root_adicCompletion v p w, AdjoinRoot.mk_eq_zero.mpr p.dvd, map_zero]⟩

private lemma coe_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactor v p w : F_[v][X]) =
      minpoly F_[v] (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) :=
  rfl

/- The embedding of the local field factor into the completion, sending the root of the local
factor to the image of the global root. -/
private noncomputable def localFactorEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    AdjoinRoot (W.localFactor v p w : F_[v][X]) →+* w.adicCompletion (𝕃 p) :=
  AdjoinRoot.lift (algebraMap F_[v] (w.adicCompletion (𝕃 p)))
    (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (root (p : F[X]))) (by
      rw [W.coe_localFactor v p w]
      exact minpoly.aeval _ _)

/- The square `𝒪_v → F_v[X] ⧸ (q) → (F[X] ⧸ (p))_w` = `𝒪_v → 𝒪_w → (F[X] ⧸ (p))_w`. -/
private lemma localFactorEmb_comp_algebraMap (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (W.localFactorEmb v p w).comp
        (algebraMap 𝒪_[v] (AdjoinRoot (W.localFactor v p w : F_[v][X]))) =
      (algebraMap (w.adicCompletionIntegers (𝕃 p)) (w.adicCompletion (𝕃 p))).comp
        (adicCompletionIntegersExtension F (𝕃 p) v w) := by
  ext c
  rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply 𝒪_[v] F_[v]
      (AdjoinRoot (W.localFactor v p w : F_[v][X])),
    AdjoinRoot.algebraMap_eq, localFactorEmb, AdjoinRoot.lift_of]
  rw [RingHom.comp_apply, algebraMap_adicCompletionExtensionAlgebra]
  exact congrArg _ (coe_adicCompletionIntegersExtension F (𝕃 p) v w c).symm

/- The embedding maps the local ring of integers into the integers of the completion. -/
private lemma localFactorEmb_mem_adicCompletionIntegers (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (x : 𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w)) :
    W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X])) ∈
      w.adicCompletionIntegers (𝕃 p) := by
  obtain ⟨P, hPm, hPe⟩ := x.2
  have h2 := congrArg (W.localFactorEmb v p w) hPe
  rw [map_zero, Polynomial.hom_eval₂, W.localFactorEmb_comp_algebraMap v p w] at h2
  have hint2 : _root_.IsIntegral (w.adicCompletionIntegers (𝕃 p))
      (W.localFactorEmb v p w (x : AdjoinRoot (W.localFactor v p w : F_[v][X]))) := by
    refine ⟨P.map (adicCompletionIntegersExtension F (𝕃 p) v w), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact h2
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint2
  rw [← hy]
  exact y.2

/- The restriction of `localFactorEmb` to the rings of integers. -/
private noncomputable def localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w) →+* w.adicCompletionIntegers (𝕃 p) :=
  ((W.localFactorEmb v p w).comp (algebraMap _ _)).codRestrict
    (w.adicCompletionIntegers (𝕃 p)).toSubring
    fun x ↦ W.localFactorEmb_mem_adicCompletionIntegers v p w x

private lemma algebraMap_comp_localFactorIntegerEmb (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (algebraMap (w.adicCompletionIntegers (𝕃 p)) (w.adicCompletion (𝕃 p))).comp
        (W.localFactorIntegerEmb v p w) =
      (W.localFactorEmb v p w).comp (algebraMap _ _) :=
  RingHom.ext fun _ ↦ rfl

/- The contraction of the maximal ideal of `𝒪_w` to the local ring of integers is nonzero. -/
private lemma comap_localFactorIntegerEmb_ne_bot (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal] :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p))).asIdeal.comap
      (W.localFactorIntegerEmb v p w) ≠ ⊥ := by
  refine Ideal.ne_bot_of_comap_ne_bot _ (FaithfulSMul.algebraMap_injective 𝒪_[v]
    (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) ?_
  have hsq0 : (W.localFactorIntegerEmb v p w).comp
      (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] (W.localFactor v p w))) =
      adicCompletionIntegersExtension F (𝕃 p) v w := by
    ext c : 2
    exact RingHom.congr_fun (W.localFactorEmb_comp_algebraMap v p w) c
  -- `comap_maximalIdeal_adicCompletionIntegersExtension` is stated for
  -- `IsLocalRing.maximalIdeal`, while contracting a prime lands on the `HeightOneSpectrum`
  -- wrapper's `asIdeal`. The two are the same term, but `rw` needs the goal written in the
  -- second spelling and no named equality bridges them, so the identification is `rfl` here.
  rw [Ideal.comap_comap, hsq0,
    show (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p))).asIdeal =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers (𝕃 p)) from rfl,
    comap_maximalIdeal_adicCompletionIntegersExtension]
  exact IsDiscreteValuationRing.not_a_field _

/- The embedding of the local field factor is compatible with the CRT projections. -/
private lemma localFactorEmb_projFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.A) :
    W.localFactorEmb v p w (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w) (W.mapA F_[v] a)) =
      algebraMap (𝕃 p) (w.adicCompletion (𝕃 p)) (projFactor W.f_ne_zero W.squarefree_f p a) := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [mapA_mk, projFactor_mk, projFactor_mk, localFactorEmb, AdjoinRoot.lift_mk]
  exact W.aeval_root_adicCompletion v p w g

/- Unfolding of the local unramifiedness condition into per-factor divisibilities. -/
private lemma localRes_mem_selmerGroupA_iff (a : W.Aˣ) :
    W.localRes F_[v] (QuotientGroup.mk a) ∈ 𝕎[v].selmerGroupA 𝒪_[v] ∅ ↔
      ∀ (q : 𝕎[v].f.Factors) (w' : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)),
        (2 : ℤ) ∣ Multiplicative.toAdd (w'.valuationOfNeZero
          (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toRingHom.toMonoidHom
            (Units.map (W.mapA F_[v]).toMonoidHom a))) := by
  rw [localRes_mk]
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff, HeightOneSpectrum.primesAbove_empty, Set.mem_empty_iff_false,
    not_false_eq_true, forall_const]

/- Transport of the divisibility from the contracted prime of the local factor to `w`. -/
private lemma dvd_toAdd_valuationOfNeZero_of_localFactor (p : W.f.Factors)
    (w : HeightOneSpectrum (W.ringOfIntegersFactor (𝓞 F) p)) [w.asIdeal.LiesOver v.asIdeal]
    (a : W.Aˣ)
    (h : (2 : ℤ) ∣ Multiplicative.toAdd ((HeightOneSpectrum.comapOfNeBot
        (W.localFactorIntegerEmb v p w) (IsDiscreteValuationRing.maximalIdeal _)
        (W.comap_localFactorIntegerEmb_ne_bot v p w)).valuationOfNeZero
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)))) :
    (2 : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero
      (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a)) := by
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (W.localFactorEmb v p w) (W.localFactorIntegerEmb v p w)
    (W.algebraMap_comp_localFactorIntegerEmb v p w)
    (IsDiscreteValuationRing.maximalIdeal _)
    (W.comap_localFactorIntegerEmb_ne_bot v p w) _ h
  have hunits : Units.map (W.localFactorEmb v p w : _ →* _)
      (Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f
        (W.localFactor v p w)).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a)) =
      Units.map (algebraMap (𝕃 p) (w.adicCompletion (𝕃 p))).toMonoidHom
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a) :=
    Units.ext (W.localFactorEmb_projFactor v p w (a : W.A))
  rw [hunits, HeightOneSpectrum.valuationOfNeZero_maximalIdeal_adicCompletionIntegers] at hkey
  exact hkey

/- The double contraction of a prime of the local ring of integers is `v`. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma comap_comap_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    (w.asIdeal.comap (W.integerMapOfDvd v hq)).comap
      (algebraMap (𝓞 F) (W.ringOfIntegersFactor (𝓞 F) p)) = v.asIdeal := by
  rw [Ideal.comap_comap, integerMapOfDvd_comp_algebraMap W v hq, ← Ideal.comap_comap]
  have h1 : w.asIdeal.comap (algebraMap 𝒪_[v] (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) =
      IsLocalRing.maximalIdeal 𝒪_[v] :=
    IsLocalRing.eq_maximalIdeal (HeightOneSpectrum.under 𝒪_[v] w).isMaximal
  rw [h1, ← Ideal.under_def, HeightOneSpectrum.under_maximalIdeal_adicCompletionIntegers]

/- The contraction of a prime of the local ring of integers to the global one is nonzero. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma comap_integerMapOfDvd_ne_bot {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    w.asIdeal.comap (W.integerMapOfDvd v hq) ≠ ⊥ := by
  refine Ideal.ne_bot_of_comap_ne_bot _ (FaithfulSMul.algebraMap_injective (𝓞 F)
    (W.ringOfIntegersFactor (𝓞 F) p)) ?_
  rw [W.comap_comap_integerMapOfDvd v hq w]
  exact v.ne_bot

/- The contracted prime lies over `v`. -/
omit [W.IsElliptic] [IsCharNeTwoNF W] in
private lemma under_comapOfNeBot_integerMapOfDvd {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v]))
    (w : HeightOneSpectrum (𝕎[v].ringOfIntegersFactor 𝒪_[v] q)) :
    HeightOneSpectrum.under (𝓞 F) (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w
      (W.comap_integerMapOfDvd_ne_bot v hq w)) = v :=
  HeightOneSpectrum.ext <| by
    simpa [HeightOneSpectrum.under, HeightOneSpectrum.comapOfNeBot_asIdeal] using
      W.comap_comap_integerMapOfDvd v hq w

/- The base-change maps of the field factors are compatible with the CRT projections. -/
private lemma map_projFactor {p : W.f.Factors} {q : 𝕎[v].f.Factors}
    (hq : (q : F_[v][X]) ∣ (p : F[X]).map (algebraMap F F_[v])) (a : W.A) :
    AdjoinRoot.map (algebraMap F F_[v]) _ _ hq (projFactor W.f_ne_zero W.squarefree_f p a) =
      projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q (W.mapA F_[v] a) := by
  obtain ⟨g, rfl⟩ := mk_surjective a
  rw [projFactor_mk, AdjoinRoot.map_mk, mapA_mk, projFactor_mk]

end Semilocal

variable [W.IsElliptic] [W.IsCharNeTwoNF]

open scoped Classical in
/-- **Step 6 over a completion**: at a finite place `v` of `F` at which `a₂`, `a₄` and `a₆` are
integral and `disc f` has valuation at most `1`, that is `exp (-1) ≤ v (disc f)`, the image of the
local descent map over the completion `F_v` consists of unramified square classes. The residue
characteristic is unrestricted, so this holds at a place above `2` as soon as the cubic `f` has
separable reduction there. -/
theorem range_μ_le_selmerGroupA_empty {v : HeightOneSpectrum (𝓞 F)}
    (ha₂ : v.valuation F W.a₂ ≤ 1) (ha₄ : v.valuation F W.a₄ ≤ 1) (ha₆ : v.valuation F W.a₆ ≤ 1)
    (hd : WithZero.exp (-1) ≤ v.valuation F W.f.discr) :
    (μ (W := 𝕎[v])).range ≤ 𝕎[v].selmerGroupA 𝒪_[v] ∅ := by
  have key (P : HeightOneSpectrum 𝒪_[v]) (z : F) :
      P.valuation F_[v] (algebraMap F F_[v] z) = v.valuation F z :=
    v.valuation_adicCompletion_algebraMap P z
  have : CharZero F_[v] := charZero_of_injective_algebraMap (algebraMap F F_[v]).injective
  refine 𝕎[v].range_μ_le_selmerGroupA_of_exp_neg_one_le (fun P _ ↦ ?_) (fun P _ ↦ ?_)
    (fun P _ ↦ ?_) fun P _ ↦ ?_
  · simpa [toAffine, key] using ha₂
  · simpa [toAffine, key] using ha₄
  · simpa [toAffine, key] using ha₆
  · rw [W.baseChange_discr_f, key]
    exact hd

open AdjoinRoot in
open scoped Classical in
/-- **Semilocal comparison, global to local**: a square class unramified outside `S` localizes to
an unramified class at every finite place outside `S`. -/
theorem localRes_mem_selmerGroupA {S : Set (HeightOneSpectrum (𝓞 F))}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {m : W.M} (hm : m ∈ W.selmerGroupA (𝓞 F) S) :
    W.localRes F_[v] m ∈ 𝕎[v].selmerGroupA 𝒪_[v] ∅ := by
  -- Each monic irreducible factor `q` of `f` over `F_v` divides the image of a factor `p` of `f`;
  -- the induced embedding `F[X] ⧸ (p) → F_v[X] ⧸ (q)` restricts to the rings of integers, the
  -- prime of the local ring of integers contracts to a prime `w ∣ v`, and the local valuation is
  -- the `w`-adic one raised to the ramification index, so evenness transfers.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply] at hm ⊢
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff] at hm
  rw [W.localRes_mem_selmerGroupA_iff v a]
  intro q w
  -- find the global factor `p` below the local factor `q`
  obtain ⟨p, hq⟩ := Polynomial.Factors.exists_dvd_map (algebraMap F F_[v]) W.f_ne_zero q.prime
    (q.dvd.trans (W.baseChange_f F_[v]).dvd)
  -- the prime of the global field factor below `w`
  have hne := W.comap_integerMapOfDvd_ne_bot v hq w
  have hunder := W.under_comapOfNeBot_integerMapOfDvd v hq w
  -- the global unramifiedness hypothesis at that prime
  have hdvd := hm p (HeightOneSpectrum.comapOfNeBot (W.integerMapOfDvd v hq) w hne) fun hmem ↦
    hv (hunder ▸ (HeightOneSpectrum.mem_primesAbove_iff (𝓞 F) _ _ _).mp hmem)
  -- transport along the embedding of field factors
  have hkey := HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
    (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq) (W.integerMapOfDvd v hq)
    (W.algebraMap_comp_integerMapOfDvd v hq) w hne _ hdvd
  have hunits : Units.map (projFactor 𝕎[v].f_ne_zero 𝕎[v].squarefree_f q).toRingHom.toMonoidHom
        (Units.map (W.mapA F_[v]).toMonoidHom a) =
      Units.map (AdjoinRoot.map (algebraMap F F_[v]) _ _ hq : _ →* _)
        (Units.map (projFactor W.f_ne_zero W.squarefree_f p).toRingHom.toMonoidHom a) :=
    Units.ext (W.map_projFactor v hq (a : W.A)).symm
  rw [hunits]
  exact hkey

open AdjoinRoot in
open scoped Classical in
/-- **Semilocal comparison, local to global**: a square class that localizes to an unramified class
at every finite place outside `S` is unramified outside `S`. -/
theorem mem_selmerGroupA_of_forall_localRes {S : Set (HeightOneSpectrum (𝓞 F))} {m : W.M}
    (hm : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → W.localRes F_[v] m ∈ 𝕎[v].selmerGroupA 𝒪_[v] ∅) :
    m ∈ W.selmerGroupA (𝓞 F) S := by
  -- Every prime `w` of a field factor `F[X] ⧸ (p)` above a place `v ∉ S` arises from a factor of
  -- `f` over `F_v`, namely the minimal polynomial of the image of the root in the completion at
  -- `w` (`localFactor`). Evenness transports from the primes of the local ring of integers
  -- through the completion `(F[X] ⧸ (p))_w` back to `w`.
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ m
  simp only [QuotientGroup.mk'_apply]
  simp only [mem_selmerGroupA_iff, AdjoinRoot.modPowEquivPiFactors_mk,
    mem_selmerGroupFactor_unit_iff]
  intro p w hw
  have hv : HeightOneSpectrum.under (𝓞 F) w ∉ S := fun h ↦
    hw ((HeightOneSpectrum.mem_primesAbove_iff (𝓞 F) _ _ _).mpr h)
  refine W.dvd_toAdd_valuationOfNeZero_of_localFactor (HeightOneSpectrum.under (𝓞 F) w) p w a ?_
  exact (W.localRes_mem_selmerGroupA_iff (HeightOneSpectrum.under (𝓞 F) w) a).mp
    (hm (HeightOneSpectrum.under (𝓞 F) w) hv) _ _

end WeierstrassCurve.Affine

end
