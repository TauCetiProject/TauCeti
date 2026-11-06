/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import TauCeti.Algebra.CharP.Frobenius.PowRingHom
public import TauCeti.RingTheory.Perfect.IsPRadical

/-!
# Perfect rings and `p`-radical maps under localization

Let `p` be a prime. A localization of a perfect ring in which `p` vanishes is again perfect: the
`p`-th root of `r / m` is `r' / m` where `r' ^ p = r * m ^ (p - 1)`. Neither statement below asks
for an `ExpChar` instance, so both apply to the zero ring, which is perfect but has no exponential
characteristic `p`.

The second result says that perfect closures commute with localization. Let `A → B` and
`A' → B'` be `p`-radical maps into perfect rings, where `A'` is the localization of `A` at a
submonoid `M` and `p = 0` in `A`, and let `B → B'` be compatible with the localization `A → A'`.
Then `B'` is the localization of `B` at the image of `M`. Since the `p`-radical maps into perfect
rings are exactly the perfect closures, this is what makes the perfection of a scheme over `𝔽_p`
affine-locally the perfection of its rings of sections.

## Main results

* `IsLocalization.perfectRing`: a localization of a perfect ring in which `p` vanishes is perfect.
* `IsPRadical.isLocalization_map`: perfect closures commute with localization.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Section 3, for perfections of schemes, which are affine-locally given by perfect
  closures of rings.
-/

public section

variable {p : ℕ} [hp : Fact p.Prime]

namespace IsLocalization

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]

/-- **A localization of a perfect ring in which `p` vanishes is perfect.** The ring may be the zero
ring, so no `ExpChar` instance is assumed. -/
theorem perfectRing [IsLocalization M S] (hR : (p : R) = 0) [PerfectRing R p] :
    PerfectRing S p := by
  have hS : (p : S) = 0 := by rw [← map_natCast (algebraMap R S), hR, map_zero]
  refine ⟨⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩⟩
  · -- Write `x - y = r / m`; then `(r / m) ^ p = 0` gives `c * r ^ p = 0` for some `c ∈ M`, so
    -- `(c * r) ^ p = c ^ (p - 1) * (c * r ^ p) = 0` and `c * r = 0` by injectivity of `x ↦ x ^ p`.
    have h0 : (x - y) ^ p = 0 := by
      rw [← TauCeti.powRingHom_apply hS, map_sub, TauCeti.powRingHom_apply,
        TauCeti.powRingHom_apply, sub_eq_zero]
      exact hxy
    rw [← sub_eq_zero]
    obtain ⟨r, m, hrm⟩ := exists_mk'_eq M (x - y)
    rw [← hrm, ← mk'_pow, mk'_eq_zero_iff] at h0
    obtain ⟨c, hc⟩ := h0
    have hcr : (c * r : R) ^ p = 0 := by
      rw [mul_pow, ← Nat.sub_add_cancel hp.out.one_le, pow_succ, mul_assoc,
        Nat.sub_add_cancel hp.out.one_le, hc, mul_zero]
    rw [← hrm, mk'_eq_zero_iff]
    exact ⟨c, PerfectRing.bijective_frobenius.1 (hcr.trans (zero_pow hp.out.ne_zero).symm)⟩
  · -- `r / m = (r * m ^ (p - 1)) / m ^ p` is the `p`-th power of `r' / m`, where
    -- `r' ^ p = r * m ^ (p - 1)`.
    obtain ⟨r, m, rfl⟩ := exists_mk'_eq M x
    obtain ⟨r', hr'⟩ := (PerfectRing.bijective_frobenius (R := R) (p := p)).2 (r * m ^ (p - 1))
    refine ⟨mk' S r' m, ?_⟩
    beta_reduce at hr' ⊢
    rw [← mk'_pow, hr', mk'_eq_iff_eq, SubmonoidClass.coe_pow, mul_left_comm, ← pow_succ',
      Nat.sub_add_cancel hp.out.one_le, mul_comm]

end IsLocalization

namespace IsPRadical

variable {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B'] [Algebra A A']
  (M : Submonoid A) [IsLocalization M A'] (i : A →+* B) (i' : A' →+* B') (j : B →+* B')

/-- **Perfect closures commute with localization.** Let `A'` be the localization of `A` at `M`,
with `p = 0` in `A`, and let `i : A →+* B` and `i' : A' →+* B'` be `p`-radical maps into perfect
rings. If `j : B →+* B'` is compatible with `i`, `i'` and the localization map, then `j` exhibits
`B'` as the localization of `B` at `M.map i`. -/
theorem isLocalization_map (hA : (p : A) = 0) (h : j.comp i = i'.comp (algebraMap A A'))
    [IsPRadical i p] [IsPRadical i' p] [PerfectRing B p] [PerfectRing B' p] :
    letI := j.toAlgebra
    IsLocalization (M.map i) B' := by
  let := j.toAlgebra
  let Bₘ := Localization (M.map i)
  have hB : (p : B) = 0 := by rw [← map_natCast i, hA, map_zero]
  have hA' : (p : A') = 0 := by rw [← map_natCast (algebraMap A A'), hA, map_zero]
  have : PerfectRing Bₘ p := IsLocalization.perfectRing (M.map i) Bₘ hB
  -- The comparison map `e : B_M →+* B'` exists because elements of `M` become units in `A'`.
  have hunit (y : M.map i) : IsUnit (j y) := by
    obtain ⟨m, hm, hy⟩ := Submonoid.mem_map.1 y.2
    rw [← hy, ← RingHom.comp_apply, h, RingHom.comp_apply]
    exact (IsLocalization.map_units A' ⟨m, hm⟩).map i'
  let e : Bₘ →+* B' := IsLocalization.lift hunit
  have he : e.comp (algebraMap B Bₘ) = j := IsLocalization.lift_comp hunit
  -- The map `A' →+* B_M` induced by `i`.
  let k : A' →+* Bₘ := IsLocalization.map Bₘ i (M.le_comap_map) (S := A')
  have hk : k.comp (algebraMap A A') = (algebraMap B Bₘ).comp i := IsLocalization.map_comp _
  -- The inverse `e' : B' →+* B_M` extends `k` along the `p`-radical map `i'`.
  obtain ⟨e', he'⟩ := IsPRadical.bijective_comp i' p hA' (M := Bₘ) |>.2 k
  beta_reduce at he'
  have hek : e.comp k = i' := IsLocalization.ringHom_ext M <| by
    rw [RingHom.comp_assoc, hk, ← RingHom.comp_assoc, he, h]
  have he'j : e'.comp j = algebraMap B Bₘ := (IsPRadical.bijective_comp i p hA (M := Bₘ)).1 <| by
    change (e'.comp j).comp i = (algebraMap B Bₘ).comp i
    rw [RingHom.comp_assoc, h, ← RingHom.comp_assoc, he', hk]
  have h₁ : e.comp e' = RingHom.id B' := (IsPRadical.bijective_comp i' p hA' (M := B')).1 <| by
    change (e.comp e').comp i' = (RingHom.id B').comp i'
    rw [RingHom.comp_assoc, he', hek, RingHom.id_comp]
  have h₂ : e'.comp e = RingHom.id Bₘ := IsLocalization.ringHom_ext (M.map i) <| by
    rw [RingHom.comp_assoc, he, he'j, RingHom.id_comp]
  exact IsLocalization.isLocalization_of_algEquiv (M.map i)
    { RingEquiv.ofRingHom e e' h₁ h₂ with
      commutes' b := congr($he b) }

end IsPRadical
