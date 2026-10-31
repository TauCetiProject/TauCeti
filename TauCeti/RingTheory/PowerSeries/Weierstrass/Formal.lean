/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.DiscreteValuationRing
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation

/-!
# Formal and normed Weierstrass preparation near the unit radius

Let `O` be a local ring with maximal ideal `𝔪`, and let `φ : O →+* R` be a ring homomorphism
into a normed ring which maps `O` into the closed unit ball and `𝔪` into the open unit ball. The
model case is the valuation ring `O = 𝒪[K]` of a nonarchimedean field `K`, with `φ` the inclusion
`O → K`, where the two hypotheses are `Valued.integer.norm_le_one` and
`Valued.integer.mem_maximalIdeal_iff`. Then `φ` maps units of `O` to elements of norm one, so
for `x : O`

```text
‖φ x‖ = 1 ↔ x is a unit,    ‖φ x‖ < 1 ↔ x ∈ 𝔪.
```

A power series `g ∈ O⟦X⟧` has two notions of Weierstrass degree. The *formal* degree is the
order of its reduction modulo `𝔪`: the least index of a unit coefficient. It is the degree of the
distinguished polynomial in Mathlib's ideal-adic preparation theorem
(`PowerSeries.IsWeierstrassFactorization`). The *normed* degree at a radius `r > 0` is the
distinguished degree `TauCeti.PowerSeries.IsDistinguished` of the image series `g.map φ`, the last
index attaining its Gauss norm at `r`, which is the degree of the normed preparation polynomial
at `r`. This file compares the two.

Every series with coefficients in the closed unit ball is restricted at every radius `r` with
`|r| < 1`, but need not be restricted at `r = 1`. If the least unit coefficient of `g` has index
`s`, then for all `r < 1` sufficiently close to one the weighted coefficient `‖φ aₛ‖ rˢ = rˢ` is
the unique dominant one: the finitely many earlier coefficients have norm less than one, and the
later ones are weighted by strictly smaller powers of `r`. Thus the formal degree is the normed
distinguished degree, and also the lowest dominant degree, at those radii. Consequently a formal
Weierstrass factorization `g = P * h` maps to the normed preparation of `g.map φ` at every such
radius: the image of the formal unit `h` is a unit of the ring of series restricted at `r`, and by
uniqueness of normed preparation the image of `P` is the monic preparation polynomial.

At the radius one itself the two notions differ in general. When `g` has a unit coefficient, the
lowest dominant degree of `g.map φ` at radius one is still the formal degree, but its
distinguished degree is the *last* index of a unit coefficient, if there is one. The two agree
exactly when `g` has a single unit coefficient. For example, over `ℤ_p` the series `p + X + X²`
has formal degree one and distinguished degree two at radius one, while `∑ Xⁿ` is a formal unit
which is not restricted at radius one.

No completeness, discreteness or ultrametric hypothesis is needed for the comparison of degrees;
the comparison of factorizations uses the uniqueness theorem of normed preparation, over an
ultrametric ring with multiplicative norm, but no completeness. Over a discrete valuation ring,
dividing out the uniformiser power `π ^ μ(g)` reduces a nonzero series to the case of a unit
coefficient, whose least index is the λ-invariant.

## Main results

* `TauCeti.norm_map_eq_one_iff_isUnit` and `TauCeti.norm_map_lt_one_iff_mem_maximalIdeal`: units
  of `O` map to norm one and the maximal ideal is exactly the preimage of the open unit ball.
* `PowerSeries.isRestricted_map_of_abs_lt_one` and `TauCeti.PowerSeries.isUnit_mk_map`:
  series over `O` are restricted inside the unit disc, and formal units stay units of every
  ring of restricted series there.
* `TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant` and
  `TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant_map`: near the unit radius,
  the least coefficient of norm one, respectively the formal degree, is the unique dominant index.
* `PowerSeries.IsWeierstrassFactorization.eventually_isDistinguished_map` and
  `PowerSeries.IsWeierstrassFactorization.eventually_eq_map_of_mul_eq`: near the unit radius,
  the image of a formal Weierstrass factorization `g = P * h` is distinguished of degree `deg P`,
  and every normed preparation of `g.map φ` is the image of the formal one.
* `TauCeti.PowerSeries.isDistinguished_one_map_iff` and
  `TauCeti.PowerSeries.isLowestDominant_one_map_iff`: at the radius one, the distinguished degree
  is the last index of a unit coefficient and the lowest dominant degree is the formal degree.
* `TauCeti.PowerSeries.eventually_isDistinguished_and_isLowestDominant_map_lambdaInvariant`: over a
  discrete valuation ring, the λ-invariant of a series with μ-invariant zero is its distinguished
  degree near the unit radius.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
-/

public section

open Filter Topology IsLocalRing

namespace PowerSeries

variable {O R : Type*} [Semiring O] [NormedRing R] {φ : O →+* R}

/-- A series whose coefficients map into the closed unit ball of a normed ring is restricted at
every radius of absolute value less than one. -/
theorem isRestricted_map_of_abs_lt_one (hφ : ∀ x, ‖φ x‖ ≤ 1) (g : PowerSeries O) {r : ℝ}
    (hr : |r| < 1) :
    (g.map φ).IsRestricted r :=
  HasGaussNorm.isRestricted_of_abs_lt
    ⟨1, Set.forall_mem_range.mpr fun n ↦ by simpa using hφ (g.coeff n)⟩ hr

end PowerSeries

namespace TauCeti

section LocalRing

variable {O R : Type*} [CommRing O] [IsLocalRing O] [SeminormedRing R] [NormOneClass R]
  {φ : O →+* R}

/-- A ring homomorphism from a local ring into the closed unit ball of a normed ring, mapping the
maximal ideal into the open unit ball, maps exactly the units to elements of norm one. -/
theorem norm_map_eq_one_iff_isUnit (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1)
    {x : O} : ‖φ x‖ = 1 ↔ IsUnit x := by
  refine ⟨fun h ↦ by_contra fun hx ↦ (hm x (by rwa [mem_maximalIdeal, mem_nonunits_iff])).ne h,
    fun ⟨u, hu⟩ ↦ ?_⟩
  subst hu
  refine le_antisymm (hφ _) ?_
  calc (1 : ℝ) = ‖φ ↑u * φ ↑u⁻¹‖ := by rw [← map_mul, Units.mul_inv, map_one, norm_one]
    _ ≤ ‖φ ↑u‖ * ‖φ ↑u⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖φ ↑u‖ * 1 := mul_le_mul_of_nonneg_left (hφ _) (norm_nonneg _)
    _ = ‖φ ↑u‖ := mul_one _

/-- A ring homomorphism from a local ring into the closed unit ball of a normed ring, mapping the
maximal ideal into the open unit ball, pulls the open unit ball back to the maximal ideal. -/
theorem norm_map_lt_one_iff_mem_maximalIdeal (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) {x : O} : ‖φ x‖ < 1 ↔ x ∈ maximalIdeal O := by
  refine ⟨fun h ↦ ?_, hm x⟩
  rw [mem_maximalIdeal, mem_nonunits_iff, ← norm_map_eq_one_iff_isUnit hφ hm]
  exact h.ne

end LocalRing

namespace PowerSeries

section SeminormedRing

variable {R : Type*} [SeminormedRing R] {s : ℕ} {f : _root_.PowerSeries R}

/-- **The unique dominant coefficient near the unit radius.** If every coefficient of `f` has norm
at most one, the coefficient in degree `s` has norm one and every earlier coefficient has norm less
than one, then for all radii `r < 1` close enough to one, `s` is both the distinguished and the
lowest dominant degree of `f` at `r`: the weighted coefficient in degree `s` is the only one
attaining the Gauss norm `rˢ`. -/
theorem eventually_isDistinguished_and_isLowestDominant (h1 : ∀ n, ‖f.coeff n‖ ≤ 1)
    (hs : ‖f.coeff s‖ = 1) (hlt : ∀ n < s, ‖f.coeff n‖ < 1) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r s f ∧ IsLowestDominant r s f := by
  -- Near one, `rᵏ` exceeds each of the finitely many norms `‖aₙ‖ < 1` with `n < s`.
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ n ∈ Finset.range s, ‖f.coeff n‖ < r ^ (s - n) := by
    rw [Finset.eventually_all]
    intro n hn
    have ht : Tendsto (fun r : ℝ ↦ r ^ (s - n)) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_pow (s - n)).tendsto (1 : ℝ)
    exact nhdsWithin_le_nhds (ht.eventually (lt_mem_nhds (hlt n (Finset.mem_range.mp hn))))
  filter_upwards [hev, Ioo_mem_nhdsLT zero_lt_one] with r hr ⟨hr0, hr1⟩
  have key : ∀ m, m ≠ s → ‖f.coeff m‖ * r ^ m < r ^ s := by
    intro m hm
    rcases hm.lt_or_gt with h | h
    · calc ‖f.coeff m‖ * r ^ m < r ^ (s - m) * r ^ m :=
            mul_lt_mul_of_pos_right (hr m (Finset.mem_range.mpr h)) (pow_pos hr0 _)
        _ = r ^ s := by rw [← pow_add, Nat.sub_add_cancel h.le]
    · calc ‖f.coeff m‖ * r ^ m ≤ 1 * r ^ m :=
            mul_le_mul_of_nonneg_right (h1 m) (pow_nonneg hr0.le _)
        _ < r ^ s := by rw [one_mul]; exact pow_lt_pow_right_of_lt_one₀ hr0 hr1 h
  have hg : f.gaussNorm norm r = r ^ s := by
    rw [gaussNorm_eq_of_forall_le (s := s) fun m ↦ ?_, hs, one_mul]
    rcases eq_or_ne m s with rfl | hm
    · exact le_rfl
    · rw [hs, one_mul]
      exact (key m hm).le
  have hss : ‖f.coeff s‖ * r ^ s = f.gaussNorm norm r := by rw [hg, hs, one_mul]
  exact ⟨⟨hss, fun m hm ↦ hg ▸ key m hm.ne'⟩,
    ⟨hg ▸ pow_pos hr0 s, hss, fun m hm ↦ hg ▸ key m hm.ne⟩⟩

end SeminormedRing

section Restricted

variable {O R : Type*} [Semiring O] [NormedRing R] {φ : O →+* R}

/-- **A formal unit is a unit of every ring of series restricted inside the unit disc.** If `φ`
maps into the closed unit ball, the image of a unit `u` of `O⟦X⟧` is a unit of the ring of series
restricted at any radius of absolute value less than one, with inverse the image of `u⁻¹`. -/
theorem isUnit_mk_map [IsUltrametricDist R] (hφ : ∀ x, ‖φ x‖ ≤ 1) {u : _root_.PowerSeries O}
    (hu : IsUnit u) {r : ℝ} (hr : |r| < 1) :
    IsUnit (⟨u.map φ, u.isRestricted_map_of_abs_lt_one hφ hr⟩ :
      _root_.PowerSeries.IsRestricted.subring (R := R) r) := by
  obtain ⟨u, rfl⟩ := hu
  exact ⟨⟨⟨_, _root_.PowerSeries.isRestricted_map_of_abs_lt_one hφ _ hr⟩,
    ⟨_, _root_.PowerSeries.isRestricted_map_of_abs_lt_one hφ (↑u⁻¹ : _root_.PowerSeries O) hr⟩,
    Subtype.ext (by simp [← map_mul]), Subtype.ext (by simp [← map_mul])⟩, rfl⟩

end Restricted

section LocalRing

variable {O R : Type*} [CommRing O] [IsLocalRing O] [SeminormedRing R] [NormOneClass R]
  {φ : O →+* R} {g : _root_.PowerSeries O} {s : ℕ}

/-- **The formal degree is the normed degree near the unit radius.** If `φ` maps `O` into the
closed unit ball and the maximal ideal into the open unit ball, and the reduction of `g` modulo
the maximal ideal has order `s`, then for all radii `r < 1` close enough to one, `s` is both the
distinguished and the lowest dominant degree of `g.map φ` at `r`. -/
theorem eventually_isDistinguished_and_isLowestDominant_map (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hs : (g.map (residue O)).order = s) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r s (g.map φ) ∧ IsLowestDominant r s (g.map φ) := by
  rw [_root_.PowerSeries.order_eq_nat] at hs
  simp only [_root_.PowerSeries.coeff_map, ne_eq, residue_eq_zero_iff] at hs
  refine eventually_isDistinguished_and_isLowestDominant (fun n ↦ ?_) ?_ fun n hn ↦ ?_
  · simpa using hφ (g.coeff n)
  · rw [_root_.PowerSeries.coeff_map, norm_map_eq_one_iff_isUnit hφ hm]
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hs.1
  · rw [_root_.PowerSeries.coeff_map]
    exact hm _ (hs.2 n hn)

/-- If `φ` maps into the closed unit ball and `g` has a unit coefficient, the Gauss norm of
`g.map φ` at the radius one is one. -/
theorem gaussNorm_one_map_eq_one (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1)
    (hg : g.map (residue O) ≠ 0) : (g.map φ).gaussNorm norm 1 = 1 := by
  obtain ⟨n, hn⟩ := _root_.PowerSeries.exists_coeff_ne_zero_iff_ne_zero.mpr hg
  rw [_root_.PowerSeries.coeff_map, residue_ne_zero_iff_isUnit] at hn
  rw [gaussNorm_eq_of_forall_le (s := n) fun m ↦ ?_]
  · simp [norm_map_eq_one_iff_isUnit hφ hm |>.mpr hn]
  · simpa [norm_map_eq_one_iff_isUnit hφ hm |>.mpr hn] using hφ (g.coeff m)

/-- **The distinguished degree at the radius one.** If `φ` maps `O` into the closed unit ball and
the maximal ideal into the open unit ball, and `g` has a unit coefficient, then `g.map φ` is
distinguished of degree `s` at the radius one exactly when `s` is the last index of a unit
coefficient of `g`. -/
theorem isDistinguished_one_map_iff (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1)
    (hg : g.map (residue O) ≠ 0) :
    IsDistinguished 1 s (g.map φ) ↔
      IsUnit (g.coeff s) ∧ ∀ m, s < m → g.coeff m ∈ maximalIdeal O := by
  have h1 := gaussNorm_one_map_eq_one hφ hm hg
  refine ⟨fun ⟨heq, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩, fun ⟨hu, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩⟩
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using heq
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm] using hu
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'

/-- **The lowest dominant degree at the radius one is the formal degree.** If `φ` maps `O` into
the closed unit ball and the maximal ideal into the open unit ball, and `g` has a unit
coefficient, then `s` is the lowest dominant degree of `g.map φ` at the radius one exactly when
the reduction of `g` modulo the maximal ideal has order `s`. -/
theorem isLowestDominant_one_map_iff (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hg : g.map (residue O) ≠ 0) :
    IsLowestDominant 1 s (g.map φ) ↔ (g.map (residue O)).order = s := by
  have h1 := gaussNorm_one_map_eq_one hφ hm hg
  rw [_root_.PowerSeries.order_eq_nat]
  simp only [_root_.PowerSeries.coeff_map, ne_eq, residue_eq_zero_iff]
  refine ⟨fun ⟨_, heq, hlt⟩ ↦ ⟨?_, fun m hm' ↦ ?_⟩, fun ⟨hu, hlt⟩ ↦ ⟨?_, ?_, fun m hm' ↦ ?_⟩⟩
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm, mem_maximalIdeal, mem_nonunits_iff] using heq
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'
  · rw [h1]
    exact one_pos
  · simpa [h1, norm_map_eq_one_iff_isUnit hφ hm, mem_maximalIdeal, mem_nonunits_iff] using hu
  · simpa [h1, norm_map_lt_one_iff_mem_maximalIdeal hφ hm] using hlt m hm'

end LocalRing

section DiscreteValuationRing

open IsDiscreteValuationRing

variable {O R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [SeminormedRing R]
  [NormOneClass R] {φ : O →+* R} {g : _root_.PowerSeries O}

/-- **The λ-invariant is the normed degree near the unit radius.** Over a discrete valuation ring,
if `φ` maps `O` into the closed unit ball and the maximal ideal into the open unit ball, and `g`
has μ-invariant zero, then for all radii `r < 1` close enough to one, the λ-invariant of `g` is
both the distinguished and the lowest dominant degree of `g.map φ` at `r`. -/
theorem eventually_isDistinguished_and_isLowestDominant_map_lambdaInvariant
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) (hg : g.muInvariant = 0) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r g.lambdaInvariant (g.map φ) ∧
      IsLowestDominant r g.lambdaInvariant (g.map φ) :=
  eventually_isDistinguished_and_isLowestDominant_map hφ hm
    (_root_.PowerSeries.order_map_residue_eq_lambdaInvariant hg)

end DiscreteValuationRing

end PowerSeries

end TauCeti

namespace PowerSeries.IsWeierstrassFactorization

open TauCeti.PowerSeries

variable {O : Type*} [CommRing O] [IsLocalRing O] {g : PowerSeries O} {P : Polynomial O}
  {h : PowerSeries O}

section SeminormedRing

variable {R : Type*} [SeminormedRing R] [NormOneClass R] {φ : O →+* R}

/-- If `φ` maps `O` into the closed unit ball and the maximal ideal into the open unit ball, and
`g = P * h` is a formal Weierstrass factorization over `O`, then for all radii `r < 1` close enough
to one, the degree of `P` is both the distinguished and the lowest dominant degree of `g.map φ`
at `r`. -/
theorem eventually_isDistinguished_map (H : g.IsWeierstrassFactorization P h)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), IsDistinguished r P.natDegree (g.map φ) ∧
      IsLowestDominant r P.natDegree (g.map φ) := by
  refine eventually_isDistinguished_and_isLowestDominant_map hφ hm ?_
  rw [H.natDegree_eq_toNat_order_map, ENat.natCast_toNat]
  exact _root_.PowerSeries.order_finite_iff_ne_zero.mpr H.map_ne_zero |>.ne

end SeminormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormMulClass R] [NormOneClass R]
  {φ : O →+* R}

/-- **Formal preparation is normed preparation near the unit radius.** Let `φ` map `O` into the
closed unit ball and the maximal ideal into the open unit ball, and let `g = P * h` be a formal
Weierstrass factorization over `O`, with `P` distinguished at the maximal ideal and `h` a unit.
For all radii `r < 1` close enough to one, any factorization of `g.map φ` as a unit `e` of the
ring of series restricted at `r` times a monic polynomial `ω` of degree `deg P` is the image of
the formal one: `e = h.map φ` and `ω = P.map φ`. Such a factorization exists when `R` is
complete, by `TauCeti.PowerSeries.IsDistinguished.existsUnique_isUnit_isMonicOfDegree_mul_eq`
applied to `PowerSeries.IsWeierstrassFactorization.eventually_isDistinguished_map`. -/
theorem eventually_eq_map_of_mul_eq (H : g.IsWeierstrassFactorization P h)
    (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) :
    ∀ᶠ r in 𝓝[<] (1 : ℝ), ∀ (e : PowerSeries.IsRestricted.subring (R := R) r) (ω : Polynomial R),
      IsUnit e → ω.IsMonicOfDegree P.natDegree → (e : PowerSeries R) * (ω : PowerSeries R) =
        g.map φ → (e : PowerSeries R) = h.map φ ∧ ω = P.map φ := by
  filter_upwards [H.eventually_isDistinguished_map hφ hm, Ioo_mem_nhdsLT zero_lt_one]
    with r ⟨hd, _⟩ ⟨hr0, hr1⟩ e ω he hω heq
  have hr : |r| < 1 := by rwa [abs_of_pos hr0]
  have : Nontrivial R := NormOneClass.nontrivial
  have hP : (P.map φ).IsMonicOfDegree P.natDegree :=
    ⟨H.isDistinguishedAt.monic.natDegree_map φ, H.isDistinguishedAt.monic.map φ⟩
  have hformal : ((⟨h.map φ, h.isRestricted_map_of_abs_lt_one hφ hr⟩ :
      PowerSeries.IsRestricted.subring (R := R) r) : PowerSeries R) *
        ((P.map φ : Polynomial R) : PowerSeries R) = g.map φ := by
    rw [H.eq_mul, map_mul, Polynomial.polynomial_map_coe, mul_comm]
  obtain ⟨h1, h2⟩ := hd.eq_and_eq_of_mul_eq_mul hr0 he (isUnit_mk_map hφ H.isUnit hr) hω hP heq
    hformal
  exact ⟨congrArg Subtype.val h1, h2⟩

end NormedCommRing

end PowerSeries.IsWeierstrassFactorization
