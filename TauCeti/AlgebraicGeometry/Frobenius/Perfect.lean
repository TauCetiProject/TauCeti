/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.FieldTheory.PerfectClosure
public import TauCeti.AlgebraicGeometry.Frobenius.Etale

/-!
# Perfect schemes

Let `p` be a prime. A scheme `X` over `𝔽_p` is *perfect* if its absolute Frobenius
`F_X : X ⟶ X` is an isomorphism. Since `F_X` is the identity on the underlying space and the
`p`-th power map on sections and on stalks, this says that every ring of sections, equivalently
every local ring, is a perfect ring: its `p`-th power map is bijective. Perfect schemes are the
setting for the perfection `X ↦ X^perf` of a scheme over `𝔽_p` and for perfectly finitely
presented and perfectly proper morphisms.

The characteristic is recorded as `(p : Γ(X, ⊤)) = 0` rather than through an `ExpChar` instance,
as for `AlgebraicGeometry.Scheme.frobenius`, so that the empty scheme, whose ring of global
sections is the zero ring, is perfect. Mathlib's `PerfectRing R p` only asks the `p`-th power map
of `R` to be bijective and so applies to every ring of sections, including the zero ring.

## Main definitions

* `AlgebraicGeometry.Scheme.IsPerfect X p`: `p` vanishes on `X` and `F_X` is an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.isPerfect_iff_perfectRing_stalk`: `X` is perfect if and only if `p`
  vanishes on `X` and every local ring of `X` is a perfect ring.
* `AlgebraicGeometry.Scheme.isPerfect_iff_perfectRing_affineOpens`: `X` is perfect if and only if
  `p` vanishes on `X` and the ring of sections over every affine open is a perfect ring.
* `AlgebraicGeometry.Scheme.IsPerfect.perfectRing_sections`: the ring of sections of a perfect
  scheme over every open is a perfect ring.
* `AlgebraicGeometry.Scheme.isPerfect_Spec_iff`: `Spec R` is perfect if and only if `p = 0` in `R`
  and `R` is a perfect ring.
* `AlgebraicGeometry.Scheme.IsPerfect.isReduced`: a perfect scheme is reduced.
* `AlgebraicGeometry.Scheme.IsPerfect.of_etale`: a scheme étale over a perfect scheme is perfect;
  in particular open subschemes of a perfect scheme are perfect.
* `AlgebraicGeometry.Scheme.IsPerfect.pullback`: a fibre product of perfect schemes over a perfect
  scheme is perfect.
* `AlgebraicGeometry.Scheme.not_isPerfect_Spec_polynomial`: the affine line `Spec R[X]` over a
  nonzero ring `R` is never perfect.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Section 3, Definitions 3.1 and 3.2 and Lemma 3.4.
* The Stacks Project, [Tag 0CC6](https://stacks.math.columbia.edu/tag/0CC6), for the absolute
  Frobenius of a scheme.
-/

public section

open CategoryTheory Limits MorphismProperty Polynomial

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is *perfect* (over `𝔽_p`) if the prime `p` vanishes on `X` and the absolute
Frobenius `F_X : X ⟶ X` is an isomorphism. Bhatt–Scholze 2017, Definition 3.1. -/
class IsPerfect (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] : Prop where
  /-- The prime `p` vanishes on a perfect scheme. -/
  natCast_eq_zero : (p : Γ(X, ⊤)) = 0
  /-- The absolute Frobenius of a perfect scheme is an isomorphism. -/
  isIso_frobenius : IsIso (X.frobenius p natCast_eq_zero)

attribute [instance] IsPerfect.isIso_frobenius

variable {X Y S : Scheme.{u}} {p : ℕ} [hp : Fact p.Prime]

/-- A scheme on which `p` vanishes is perfect exactly when its absolute Frobenius is an
isomorphism. -/
theorem isPerfect_iff_isIso (hX : (p : Γ(X, ⊤)) = 0) :
    IsPerfect X p ↔ IsIso (X.frobenius p hX) :=
  ⟨fun _ ↦ inferInstance, fun h ↦ ⟨hX, h⟩⟩

/-- The absolute Frobenius is an isomorphism exactly when every local ring is a perfect ring. -/
theorem isIso_frobenius_iff_perfectRing_stalk (hX : (p : Γ(X, ⊤)) = 0) :
    IsIso (X.frobenius p hX) ↔ ∀ x : X, PerfectRing (X.presheaf.stalk x) p := by
  rw [← isomorphisms.iff, isomorphisms_eq_stalkwise]
  refine ⟨fun h x ↦ ⟨(bijective_frobenius_stalkMap_iff hX x).1 (h.2 x)⟩,
    fun h ↦ ⟨?_, fun x ↦ (bijective_frobenius_stalkMap_iff hX x).2 (h x).1⟩⟩
  -- The image of `F_X` under `forgetToTop` is by definition its underlying continuous map, which
  -- is the identity.
  have : IsIso (X.frobenius p hX).base := by rw [frobenius_base]; infer_instance
  exact this

/-- The absolute Frobenius is an isomorphism exactly when the ring of sections over every affine
open is a perfect ring. -/
theorem isIso_frobenius_iff_perfectRing_affineOpens (hX : (p : Γ(X, ⊤)) = 0) :
    IsIso (X.frobenius p hX) ↔ ∀ U : X.affineOpens, PerfectRing Γ(X, U) p := by
  rw [← isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := isomorphisms Scheme)
    (f := X.frobenius p hX) _ (iSup_affineOpens_eq_top X)]
  refine forall_congr' fun U ↦ ?_
  -- `F_X` is integral, hence affine, so over the affine open `U` it is an isomorphism exactly
  -- when it is one on sections over `U`.
  rw [isomorphisms.iff, isIso_morphismRestrict_iff_isIso_app _ U.2, isIso_frobenius_app_iff]
  exact ⟨fun h ↦ ⟨h⟩, fun ⟨h⟩ ↦ h⟩

/-- **A scheme is perfect if and only if `p` vanishes on it and all its local rings are perfect
rings.** -/
theorem isPerfect_iff_perfectRing_stalk :
    IsPerfect X p ↔ (p : Γ(X, ⊤)) = 0 ∧ ∀ x : X, PerfectRing (X.presheaf.stalk x) p :=
  ⟨fun h ↦ ⟨h.natCast_eq_zero, (isIso_frobenius_iff_perfectRing_stalk _).1 inferInstance⟩,
    fun ⟨hX, h⟩ ↦ (isPerfect_iff_isIso hX).2 ((isIso_frobenius_iff_perfectRing_stalk hX).2 h)⟩

/-- **A scheme is perfect if and only if `p` vanishes on it and the ring of sections over every
affine open is a perfect ring.** -/
theorem isPerfect_iff_perfectRing_affineOpens :
    IsPerfect X p ↔ (p : Γ(X, ⊤)) = 0 ∧ ∀ U : X.affineOpens, PerfectRing Γ(X, U) p :=
  ⟨fun h ↦ ⟨h.natCast_eq_zero, (isIso_frobenius_iff_perfectRing_affineOpens _).1 inferInstance⟩,
    fun ⟨hX, h⟩ ↦
      (isPerfect_iff_isIso hX).2 ((isIso_frobenius_iff_perfectRing_affineOpens hX).2 h)⟩

namespace IsPerfect

/-- The ring of sections of a perfect scheme over every open is a perfect ring. -/
instance perfectRing_sections [h : IsPerfect X p] (U : X.Opens) : PerfectRing Γ(X, U) p :=
  ⟨(isIso_frobenius_app_iff h.natCast_eq_zero U).1 inferInstance⟩

/-- Every local ring of a perfect scheme is a perfect ring. -/
instance perfectRing_stalk [IsPerfect X p] (x : X) : PerfectRing (X.presheaf.stalk x) p :=
  (isPerfect_iff_perfectRing_stalk.1 ‹_›).2 x

variable (p) in
/-- A perfect scheme is reduced: a section `s` with `s ^ p = 0` vanishes by injectivity of the
`p`-th power map. -/
theorem isReduced [IsPerfect X p] : IsReduced X where
  component_reduced _ := (isReduced_iff_pow_one_lt p hp.out.one_lt).2 fun _ hs ↦
    PerfectRing.bijective_frobenius.1 (hs.trans (zero_pow hp.out.ne_zero).symm)

/-- **A scheme étale over a perfect scheme is perfect**: the absolute Frobenius of the source is
the base change of that of the target. This applies in particular to open immersions and
isomorphisms. -/
theorem of_etale (f : X ⟶ Y) [Etale f] [h : IsPerfect Y p] : IsPerfect X p :=
  (isPerfect_iff_isIso (natCast_eq_zero_of_hom f h.natCast_eq_zero)).2
    (f.isPullback_frobenius_of_etale p h.natCast_eq_zero).isIso_fst_of_isIso

/-- An open subscheme of a perfect scheme is perfect. -/
instance opens [IsPerfect X p] (U : X.Opens) : IsPerfect U p :=
  of_etale U.ι

/-- **A fibre product of perfect schemes over a perfect scheme is perfect**: its absolute Frobenius
is the map induced by the absolute Frobenii of the factors and of the base. -/
instance pullback (f : X ⟶ S) (g : Y ⟶ S) [hX : IsPerfect X p] [hY : IsPerfect Y p]
    [hS : IsPerfect S p] : IsPerfect (Limits.pullback f g) p := by
  have hP := natCast_eq_zero_of_hom (pullback.fst f g) hX.natCast_eq_zero
  have hF : (Limits.pullback f g).frobenius p hP =
      pullback.map f g f g (X.frobenius p hX.natCast_eq_zero) (Y.frobenius p hY.natCast_eq_zero)
        (S.frobenius p hS.natCast_eq_zero)
      (frobenius_naturality _ _ f).symm (frobenius_naturality _ _ g).symm := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, frobenius_naturality]
    · rw [pullback.lift_snd, frobenius_naturality]
  exact (isPerfect_iff_isIso hP).2 (hF ▸ inferInstance)

end IsPerfect

/-- **`Spec R` is perfect if and only if `p = 0` in `R` and `R` is a perfect ring.** -/
theorem isPerfect_Spec_iff (R : Type u) [CommRing R] :
    IsPerfect (Spec (.of R)) p ↔ (p : R) = 0 ∧ PerfectRing R p := by
  let e := (ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have hpow (hR : (p : R) = 0) : ⇑(TauCeti.powRingHom R p hR) = fun x ↦ x ^ p :=
    funext (TauCeti.powRingHom_apply hR)
  have hp : (p : Γ(Spec (.of R), ⊤)) = 0 ↔ (p : R) = 0 := by
    rw [← map_eq_zero_iff e e.injective, map_natCast]
  refine ⟨fun h ↦ ⟨hp.1 h.natCast_eq_zero, ?_⟩, fun ⟨hR, _⟩ ↦ (isPerfect_iff_isIso (hp.2 hR)).2 ?_⟩
  · have := h.isIso_frobenius
    rw [← Spec_map_powRingHom (.of R) (hp.1 h.natCast_eq_zero), isIso_SpecMap_iff] at this
    exact ⟨by rwa [CommRingCat.hom_ofHom, hpow] at this⟩
  · rw [← Spec_map_powRingHom (.of R) hR, isIso_SpecMap_iff, CommRingCat.hom_ofHom, hpow]
    exact PerfectRing.bijective_frobenius

/-- The spectrum of a perfect ring of characteristic `p` is perfect. -/
instance isPerfect_Spec (R : Type u) [CommRing R] [CharP R p] [PerfectRing R p] :
    IsPerfect (Spec (.of R)) p :=
  (isPerfect_Spec_iff R).2 ⟨CharP.cast_eq_zero R p, inferInstance⟩

/-- **The affine line `Spec R[X]` over a nonzero ring `R` is not perfect**: if `X = q ^ p` with
`p = 0`, differentiating gives `1 = p • q ^ (p - 1) * q' = 0`. -/
theorem not_isPerfect_Spec_polynomial (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ IsPerfect (Spec (.of R[X])) p := by
  intro h
  obtain ⟨hR, hperf⟩ := (isPerfect_Spec_iff R[X]).1 h
  obtain ⟨q, hq⟩ := hperf.bijective_frobenius.2 X
  have := congrArg derivative hq
  simp only [derivative_pow, derivative_X, C_eq_natCast, hR, zero_mul] at this
  exact one_ne_zero this.symm

/-! ### Checks -/

/-- The empty scheme is perfect. -/
example : IsPerfect (∅ : Scheme.{u}) p :=
  (isPerfect_iff_isIso (Subsingleton.elim _ _)).2 inferInstance

/-- The spectrum of the prime field `𝔽_p` is perfect. -/
example : IsPerfect (Spec (.of (ZMod p))) p := inferInstance

/-- The spectrum of the perfect closure `𝔽_p[t^{1/p^∞}]` of the polynomial ring `𝔽_p[t]` is
perfect, whereas the affine line `Spec 𝔽_p[t]` itself is not. -/
example : IsPerfect (Spec (.of (PerfectClosure (ZMod p)[X] p))) p := inferInstance

example : ¬ IsPerfect (Spec (.of (ZMod p)[X])) p := not_isPerfect_Spec_polynomial _

/-- The dual numbers `𝔽_p[ε]/(ε²)` are not perfect, as `ε ^ p = 0`. -/
example : ¬ IsPerfect (Spec (.of (TrivSqZeroExt (ZMod p) (ZMod p)))) p := fun h ↦ by
  obtain ⟨-, hperf⟩ := (isPerfect_Spec_iff _).1 h
  set ε : TrivSqZeroExt (ZMod p) (ZMod p) := TrivSqZeroExt.inr 1
  have hε : ε ^ 2 = 0 := by ext <;> simp [ε, pow_two]
  have hεp : ε ^ p = 0 ^ p := by
    rw [zero_pow hp.out.ne_zero]
    exact pow_eq_zero_of_le hp.out.two_le hε
  simpa [ε] using congrArg TrivSqZeroExt.snd (hperf.bijective_frobenius.1 hεp)

end AlgebraicGeometry.Scheme
