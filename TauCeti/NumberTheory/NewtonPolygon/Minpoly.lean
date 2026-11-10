/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Irreducible
public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
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

## Main results

* `Polynomial.forall_mem_newtonSlopes_eq_of_irreducible`: an irreducible polynomial over a
  complete field is pure.
* `minpoly.newtonSlopes_eq_replicate`: the minimal polynomial of `α ≠ 0` of degree `d` has the
  slope `-w α` with multiplicity `d`, for every valuation `w` extending `v`.
* `minpoly.newtonSlopes_eq_replicate_logb_spectralNorm`: the same slope is
  `Real.logb b (spectralNorm K L α)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §6.
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.2.1.
-/

public section

namespace Polynomial

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
  · -- `f` is a scalar multiple of `X`, which has no finite slopes.
    obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hc
    obtain ⟨c, -, rfl⟩ :=
      Polynomial.isUnit_iff.mp ((hf.isUnit_or_isUnit rfl).resolve_left not_isUnit_X)
    rw [X_mul_C, C_mul_X_eq_monomial, newtonSlopes_monomial]
    simp
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
  · exact norm_coeff_mul_pow_le_norm_coeff_zero_of_irreducible hf
      (Real.rpow_pos_of_pos hb0 m).le hconst n

end Polynomial

namespace minpoly

/-- The minimal polynomial of a nonzero integral element of degree `d` has `d` finite slopes, so
if they all equal `m` its slope multiset is `d` copies of `m`. -/
private theorem newtonSlopes_eq_replicate_of_forall_eq {F L : Type*} [Field F] [Field L]
    [Algebra F L] {u : AddValuation F (WithTop ℝ)} {α : L} (hα : IsIntegral F α) (hα0 : α ≠ 0)
    {m : ℝ} (hm : ∀ s ∈ (minpoly F α).newtonSlopes u, s = m) :
    (minpoly F α).newtonSlopes u = Multiset.replicate (minpoly F α).natDegree m := by
  refine Multiset.eq_replicate.mpr ⟨?_, hm⟩
  rw [Polynomial.card_newtonSlopes _ u fun x => u.top_iff.mp,
    Polynomial.natTrailingDegree_eq_zero_of_constantCoeff_ne_zero
      (by simpa using coeff_zero_ne_zero hα hα0), Nat.sub_zero]

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
  refine newtonSlopes_eq_replicate_of_forall_eq hα hα0 fun s hs => ?_
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
  refine newtonSlopes_eq_replicate_of_forall_eq hα hα0 fun s hs => ?_
  rw [hpure s hs, hspec, Real.logb_rpow hb0 hb.ne']

end minpoly
