/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible
public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.NumberTheory.NewtonPolygon.Irreducible
public import TauCeti.NumberTheory.NewtonPolygon.Roots

/-!
# Newton polygons of irreducible and minimal polynomials over a complete field

Let `K` be a complete nontrivially normed field with an ultrametric norm, and let `v` be a real
additive valuation with `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `b > 1`. Then every irreducible
polynomial `f` over `K` is *pure*: its Newton polygon is a single segment, from `(0, v a₀)` to
`(d, v a_d)`, so that every finite slope equals `(v a_d - v a₀) / d`. When `a₀ = 0` the
polynomial is a scalar multiple of `X`, which has no finite slopes.

The input is the computation of the spectral value of a monic irreducible polynomial,
`Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible`: after dividing by the leading
coefficient, every coefficient satisfies `‖aᵢ‖ ≤ ‖a₀‖ ^ ((d - i) / d)`, which is the Gauss form
`Polynomial.forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le` of purity. Completeness is
essential: over `ℚ` with the `p`-adic norm, `(X - 1) (X - p) + p ^ 3` has negative discriminant
`(p - 1) ^ 2 - 4 p ^ 3`, so it is irreducible, but its Newton polygon has the slopes `-1` and `0`.

For the minimal polynomial of a nonzero element `α` integral over `K`, the slope is determined by
`α` itself. Its Newton polygon is pure of slope `-w α` for every real additive valuation `w` on
the field of `α` extending `v`, which is the root-valuation description of the slopes without
assuming that the minimal polynomial splits. In particular all such `w` agree at `α`. Without
any choice of a valuation on the extension, the slope is the base-`b` logarithm of the spectral
norm of `α`, the canonical extension of the norm of `K`.

Purity does not imply irreducibility; see `Polynomial.irreducible_of_forall_mem_newtonSlopes_eq`
for the criterion in the converse direction over a discretely valued field.

Since every irreducible factor of a polynomial `f` is pure, and the finite slopes of a product are
those of its factors together, the irreducible factors of `f` are sorted by slope: the
multiplicity of a slope `m` of `f` is the sum of the degrees of the irreducible factors of slope
`m`, so each slope of `f` is the slope of at least one irreducible factor. When the valuation takes
integer values on nonzero elements, an irreducible factor of rational slope `q` has degree a
positive multiple of the denominator `e` of `q`. Hence if `q` has multiplicity `d` there are at
most `d / e` irreducible factors of slope `q`, counted with multiplicity, and exactly one when
`d = e`. Otherwise the polygon alone need not decide the number of factors: over `ℚ_[p]`, the
polynomial `X ^ 4 - p ^ 2 = (X ^ 2 - p) (X ^ 2 + p)` has the single slope `-1 / 2`, with
multiplicity four, and two irreducible factors, while the minimal polynomial of an element of
valuation `1 / 2` generating an extension of degree four has the same polygon and is irreducible.

## Main results

* `Polynomial.forall_mem_newtonSlopes_eq_of_irreducible`: an irreducible polynomial over a
  complete field is pure.
* `minpoly.newtonSlopes_eq_replicate`: the minimal polynomial of `α ≠ 0` of degree `d` has the
  slope `-w α` with multiplicity `d`, for every valuation `w` extending `v`.
* `minpoly.newtonSlopes_eq_replicate_logb_spectralNorm`: the same slope is
  `Real.logb b (spectralNorm K L α)`.
* `Polynomial.count_newtonSlopes_eq_sum_natDegree_filter_normalizedFactors`: the multiplicity of a
  slope is the total degree of the irreducible factors of that slope.
* `Polynomial.exists_mem_normalizedFactors_of_mem_newtonSlopes` and
  `Polynomial.card_toFinset_newtonSlopes_le_card_normalizedFactors`: every slope is the slope of an
  irreducible factor, so there are at least as many irreducible factors as distinct slopes.
* `Polynomial.den_dvd_natDegree_of_irreducible`: for an integer-valued valuation, the denominator
  of the slope of an irreducible polynomial divides its degree.
* `Polynomial.card_filter_normalizedFactors_mul_den_le_count_newtonSlopes` and
  `Polynomial.card_filter_normalizedFactors_eq_one`: a slope of multiplicity `d` and denominator
  `e` is carried by at most `d / e` irreducible factors, and by exactly one when `d = e`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.2.1.
-/

public section

namespace Polynomial

/-- An irreducible polynomial over a field vanishing at zero is a scalar multiple of `X`, so it has
no finite slopes. -/
theorem newtonSlopes_eq_zero_of_irreducible_of_coeff_zero_eq_zero {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℝ)) {f : F[X]} (hf : Irreducible f) (hc : f.coeff 0 = 0) :
    f.newtonSlopes u = 0 := by
  obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hc
  obtain ⟨c, -, rfl⟩ :=
    Polynomial.isUnit_iff.mp ((hf.isUnit_or_isUnit rfl).resolve_left not_isUnit_X)
  rw [X_mul_C, C_mul_X_eq_monomial, newtonSlopes_monomial]

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {v : AddValuation K (WithTop ℝ)} {b : ℝ}

/-- **Irreducible polynomials over a complete field are pure.** Let `K` be complete with an
ultrametric norm `‖x‖ = b ^ (-v x)` for `x ≠ 0`, where `1 < b`. Every finite slope of an
irreducible polynomial `f` of degree `d` equals `(v a_d - v a₀) / d`, where `a_d` is its leading
and `a₀` its constant coefficient. -/
theorem forall_mem_newtonSlopes_eq_of_irreducible (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} (hf : Irreducible f) :
    ∀ s ∈ f.newtonSlopes v,
      s = ((v f.leadingCoeff).untop₀ - (v (f.coeff 0)).untop₀) / f.natDegree := by
  by_cases hc : f.coeff 0 = 0
  · simp [newtonSlopes_eq_zero_of_irreducible_of_coeff_zero_eq_zero v hf hc]
  have hl0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.ne_zero
  have hb0 : 0 < b := zero_lt_one.trans hb
  set m := ((v f.leadingCoeff).untop₀ - (v (f.coeff 0)).untop₀) / f.natDegree
  -- The constant term has norm `‖a_d‖ (b ^ m) ^ d`.
  have hconst : ‖f.leadingCoeff‖ * (b ^ m) ^ f.natDegree = ‖f.coeff 0‖ := by
    rw [hv _ hl0, hv _ hc, ← Real.rpow_mul_natCast hb0.le, ← Real.rpow_add hb0]
    congr 1
    simp only [m]
    field_simp [Nat.cast_ne_zero.mpr hf.natDegree_pos.ne']
    ring
  have htr : f.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero (by simpa using hc)
  refine (forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le hb hv).mpr
    ⟨?_, fun n => ?_⟩ <;> rw [trailingCoeff, htr, pow_zero, mul_one]
  · exact hconst
  · exact norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible hf hconst n

/-- Over a complete field, all finite slopes of an irreducible polynomial equal any one of them. -/
theorem forall_mem_newtonSlopes_eq_of_irreducible_of_mem (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} (hf : Irreducible f) {m : ℝ}
    (hm : m ∈ f.newtonSlopes v) : ∀ s ∈ f.newtonSlopes v, s = m := fun s hs =>
  (forall_mem_newtonSlopes_eq_of_irreducible hb hv hf s hs).trans
    (forall_mem_newtonSlopes_eq_of_irreducible hb hv hf m hm).symm

/-- Over a complete field, an irreducible polynomial of degree `d` with a finite slope `m` has
the slope `m` with multiplicity `d`. -/
theorem newtonSlopes_eq_replicate_of_irreducible (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} (hf : Irreducible f) {m : ℝ}
    (hm : m ∈ f.newtonSlopes v) : f.newtonSlopes v = Multiset.replicate f.natDegree m := by
  have hc : f.coeff 0 ≠ 0 := fun hc => by
    simp [newtonSlopes_eq_zero_of_irreducible_of_coeff_zero_eq_zero v hf hc] at hm
  exact newtonSlopes_eq_replicate_of_forall_eq (fun _ => v.top_iff.mp) hc
    (forall_mem_newtonSlopes_eq_of_irreducible_of_mem hb hv hf hm)

/-- Over a complete field whose valuation takes integer values on nonzero elements, the degree of
an irreducible polynomial with rational slope `q` is a multiple of the denominator of `q`. -/
theorem den_dvd_natDegree_of_irreducible
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} (hf : Irreducible f) {q : ℚ}
    (hq : (q : ℝ) ∈ f.newtonSlopes v) : q.den ∣ f.natDegree := by
  have h := den_dvd_card_newtonSlopes hint
    (forall_mem_newtonSlopes_eq_of_irreducible_of_mem hb hv hf hq)
  rwa [newtonSlopes_eq_replicate_of_irreducible hb hv hf hq, Multiset.card_replicate] at h

section NormalizedFactors

open UniqueFactorizationMonoid

variable [DecidableEq K]

/-- **Slope multiplicities and irreducible factors.** Over a complete field, the multiplicity of a
slope `m` of a polynomial `f` is the sum of the degrees of the irreducible factors of `f` of
slope `m`, counted with multiplicity. -/
theorem count_newtonSlopes_eq_sum_natDegree_filter_normalizedFactors (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (f : K[X]) (m : ℝ) :
    (f.newtonSlopes v).count m =
      (((normalizedFactors f).filter (m ∈ ·.newtonSlopes v)).map natDegree).sum := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨u, hu⟩ := prod_normalizedFactors hf
  obtain ⟨c, hc, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hslopes : f.newtonSlopes v = (normalizedFactors f).prod.newtonSlopes v := by
    conv_lhs => rw [← hu, ← hcu, mul_comm]
    exact newtonSlopes_C_mul _ v (v.ne_top_iff.mpr hc.ne_zero)
  rw [hslopes, newtonSlopes_multiset_prod v _ fun p hp => newtonPolygon_ne_top_of_ne_zero
      (fun _ => v.top_iff.mp) (ne_zero_of_mem_normalizedFactors hp), Multiset.count_sum]
  -- Each irreducible factor contributes its degree when it has slope `m`, and nothing otherwise.
  have hcount : ∀ p ∈ normalizedFactors f, (p.newtonSlopes v).count m =
      if m ∈ p.newtonSlopes v then p.natDegree else 0 := fun p hp => by
    split_ifs with hm
    · rw [newtonSlopes_eq_replicate_of_irreducible hb hv
        (irreducible_of_normalized_factor p hp) hm, Multiset.count_replicate_self]
    · exact Multiset.count_eq_zero.mpr hm
  rw [Multiset.map_congr rfl hcount]
  induction normalizedFactors f using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    by_cases hm : m ∈ p.newtonSlopes v <;>
      simp [Multiset.filter_cons_of_pos, Multiset.filter_cons_of_neg, hm, ih]

/-- **At least one irreducible factor of each slope.** Over a complete field, every finite slope
`m` of a polynomial `f` is the slope of some irreducible factor of `f`. -/
theorem exists_mem_normalizedFactors_of_mem_newtonSlopes (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} {m : ℝ}
    (hm : m ∈ f.newtonSlopes v) : ∃ p ∈ normalizedFactors f, m ∈ p.newtonSlopes v := by
  have hpos := Multiset.count_pos.mpr hm
  rw [count_newtonSlopes_eq_sum_natDegree_filter_normalizedFactors hb hv] at hpos
  obtain ⟨p, hp⟩ : ∃ p, p ∈ (normalizedFactors f).filter fun p : K[X] => m ∈ p.newtonSlopes v :=
    Multiset.exists_mem_of_ne_zero fun h => by simp [h] at hpos
  exact ⟨p, (Multiset.mem_filter.mp hp).1, (Multiset.mem_filter.mp hp).2⟩

/-- Over a complete field, a polynomial has at least as many irreducible factors, counted with
multiplicity, as it has distinct finite slopes. -/
theorem card_toFinset_newtonSlopes_le_card_normalizedFactors (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (f : K[X]) :
    (f.newtonSlopes v).toFinset.card ≤ (normalizedFactors f).card := by
  classical
  -- An irreducible factor determines its slope, so the slopes are the image of the factors.
  refine (Finset.card_le_card_of_surjOn
    (fun p : K[X] => ((v p.leadingCoeff).untop₀ - (v (p.coeff 0)).untop₀) / p.natDegree)
    fun m hm => ?_).trans (Multiset.toFinset_card_le _)
  obtain ⟨p, hp, hmp⟩ :=
    exists_mem_normalizedFactors_of_mem_newtonSlopes hb hv (Multiset.mem_toFinset.mp hm)
  exact ⟨p, Multiset.mem_toFinset.mpr hp,
    (forall_mem_newtonSlopes_eq_of_irreducible hb hv (irreducible_of_normalized_factor p hp) m
      hmp).symm⟩

/-- **At most `d / e` irreducible factors of each slope.** Over a complete field whose valuation
takes integer values on nonzero elements, if the rational slope `q` of `f` has multiplicity `d`
and denominator `e`, then `f` has at most `d / e` irreducible factors of slope `q`, counted with
multiplicity: each has degree a positive multiple of `e`. -/
theorem card_filter_normalizedFactors_mul_den_le_count_newtonSlopes
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (f : K[X]) (q : ℚ) :
    ((normalizedFactors f).filter ((q : ℝ) ∈ ·.newtonSlopes v)).card * q.den ≤
      (f.newtonSlopes v).count (q : ℝ) := by
  rw [count_newtonSlopes_eq_sum_natDegree_filter_normalizedFactors hb hv, ← smul_eq_mul,
    ← Multiset.sum_replicate, ← Multiset.map_const']
  refine Multiset.sum_map_le_sum_map _ _ fun p hp => ?_
  obtain ⟨hpf, hqp⟩ := Multiset.mem_filter.mp hp
  have hirr := irreducible_of_normalized_factor p hpf
  exact Nat.le_of_dvd hirr.natDegree_pos (den_dvd_natDegree_of_irreducible hint hb hv hirr hqp)

/-- Over a complete field whose valuation takes integer values on nonzero elements, if the
rational slope `q` of `f` has multiplicity equal to its denominator, then `f` has exactly one
irreducible factor of slope `q`, and it occurs with multiplicity one. -/
theorem card_filter_normalizedFactors_eq_one
    (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ)) (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} {q : ℚ}
    (hq : (f.newtonSlopes v).count (q : ℝ) = q.den) :
    ((normalizedFactors f).filter ((q : ℝ) ∈ ·.newtonSlopes v)).card = 1 := by
  have hle := card_filter_normalizedFactors_mul_den_le_count_newtonSlopes hint hb hv f q
  rw [hq] at hle
  have hmem : (q : ℝ) ∈ f.newtonSlopes v := Multiset.count_pos.mp (hq ▸ q.den_pos)
  obtain ⟨p, hp, hqp⟩ := exists_mem_normalizedFactors_of_mem_newtonSlopes hb hv hmem
  refine le_antisymm (Nat.le_of_mul_le_mul_right (by simpa using hle) q.den_pos) ?_
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨p, Multiset.mem_filter.mpr ⟨hp, hqp⟩⟩

end NormalizedFactors

end Polynomial

namespace minpoly

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {v : AddValuation K (WithTop ℝ)} {b : ℝ} {L : Type*} [Field L] [Algebra K L] {α : L}

/-- **Slopes of a minimal polynomial and root valuations.** Over a complete field with norm
`‖x‖ = b ^ (-v x)`, the minimal polynomial of a nonzero element `α` integral over `K`, of degree
`d`, has the single finite slope `-w α` with multiplicity `d`, for every real additive valuation
`w` on `L` extending `v`. The minimal polynomial need not split over `L`. -/
theorem newtonSlopes_eq_replicate (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
    {w : AddValuation L (WithTop ℝ)} (hw : ∀ x, w (algebraMap K L x) = v x)
    (hα : IsIntegral K α) (hα0 : α ≠ 0) :
    (minpoly K α).newtonSlopes v = Multiset.replicate (minpoly K α).natDegree (-(w α).untop₀) := by
  have hpure := Polynomial.forall_mem_newtonSlopes_eq_of_irreducible hb hv (irreducible hα)
  have hwα := Polynomial.addValuation_eq_neg_of_forall_mem_newtonSlopes_eq
    (fun x => w.top_iff.mp) (algebraMap K L) hw
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective |>.mpr (ne_zero hα)) hpure hα0
    (by rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, aeval])
  refine Polynomial.newtonSlopes_eq_replicate_of_forall_eq (fun _ => v.top_iff.mp)
    (coeff_zero_ne_zero hα hα0) fun s hs => ?_
  rw [hpure s hs, hwα, WithTop.untop₀_coe, neg_neg]

/-- **Slopes of a minimal polynomial and the spectral norm.** Over a complete field with norm
`‖x‖ = b ^ (-v x)`, the minimal polynomial of a nonzero element `α` integral over `K`, of degree
`d`, has the single finite slope `logb b ‖α‖` with multiplicity `d`, where `‖α‖` is the spectral
norm of `α` over `K`. -/
theorem newtonSlopes_eq_replicate_logb_spectralNorm (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (hα : IsIntegral K α) (hα0 : α ≠ 0) :
    (minpoly K α).newtonSlopes v =
      Multiset.replicate (minpoly K α).natDegree (Real.logb b (spectralNorm K L α)) := by
  have hpure := Polynomial.forall_mem_newtonSlopes_eq_of_irreducible hb hv (irreducible hα)
  rw [(monic hα).leadingCoeff, v.map_one, WithTop.untop₀_zero, zero_sub] at hpure
  have hb0 : 0 < b := zero_lt_one.trans hb
  -- The spectral norm of `α` is `‖a₀‖ ^ (1 / d) = b ^ (-v a₀ / d)`.
  have hspec : spectralNorm K L α = b ^ (-(v ((minpoly K α).coeff 0)).untop₀ /
      (minpoly K α).natDegree) := by
    rw [spectralNorm, Polynomial.spectralValue_eq_norm_coeff_zero_rpow_of_irreducible (monic hα)
      (irreducible hα), hv _ (coeff_zero_ne_zero hα hα0), ← Real.rpow_mul hb0.le, mul_one_div]
  refine Polynomial.newtonSlopes_eq_replicate_of_forall_eq (fun _ => v.top_iff.mp)
    (coeff_zero_ne_zero hα hα0) fun s hs => ?_
  rw [hpure s hs, hspec, Real.logb_rpow hb0 hb.ne']

end minpoly
