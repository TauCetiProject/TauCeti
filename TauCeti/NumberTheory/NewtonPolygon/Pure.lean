/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.NumberTheory.NewtonPolygon.Irreducible

/-!
# Pure polynomials and Eisenstein polygons

A polynomial `f` is *pure of slope `m`* when every finite slope of its Newton polygon equals
`m`. Write `a` for the order of vanishing of `f` at zero and `d` for its degree. If only zero has
infinite valuation, the polygon runs from the trailing point `(a, v (coeff a f))` to the leading
point `(d, v (coeff d f))`, so purity says that the polygon is the segment joining these two
points. Purity of slope `m` is therefore equivalent to two conditions on the coefficients: the
line of slope `m` through the trailing point passes through the leading point, and every
coefficient point lies on or above that line. Interior coefficient points may lie on the line;
for instance `1 + p X + p ^ 2 X ^ 2` is pure of slope `1` for the `p`-adic valuation. When the
valuation comes from a norm with `‖x‖ = b ^ (-v x)`, the same criterion says that at the radius
`b ^ m` the weighted leading and trailing terms have equal norms and bound all other weighted terms.

The basic example is an Eisenstein polynomial. If the leading coefficient of `f` has valuation
zero, its constant coefficient has valuation one and its other coefficients below the degree have
valuation at least one, then its polygon is the segment from `(0, 1)` to `(d, 0)` and every finite
slope equals `-1 / d`. For a valuation taking integer values on nonzero elements, `-1` is coprime
to `d`, and the Newton polygon irreducibility criterion
`Polynomial.irreducible_of_forall_mem_newtonSlopes_eq_div` recovers the Eisenstein criterion over
the field. Mathlib's `Polynomial.irreducible_of_eisenstein_criterion` is the corresponding
statement over a ring for a prime ideal, for primitive polynomials.

## Main results

* `Polynomial.forall_mem_newtonSlopes_eq_iff`: the purity criterion. Every finite slope equals `m`
  exactly when the leading point lies on the line of slope `m` through the trailing point and no
  coefficient point lies below that line.
* `Polynomial.forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le`: the same criterion in
  terms of weighted coefficient norms at the radius `b ^ m`.
* `Polynomial.newtonSlopes_eq_replicate_of_eisenstein`: an Eisenstein polynomial of degree `d`
  has `d` finite slopes, all equal to `-1 / d`.
* `Polynomial.irreducible_of_eisenstein`: the Eisenstein criterion over a field with a valuation
  taking integer values on nonzero elements, as a consequence of the Newton polygon
  irreducibility criterion.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II §6,
  Proposition 6.3 and its corollary.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

open TauCeti

namespace Polynomial

section Ring

variable {R : Type*} [Ring R] {v : AddValuation R (WithTop ℝ)} {f : R[X]}

/-- If only zero has infinite valuation and every finite slope of a nonzero polynomial `f`
equals `m`, the Newton polygon of `f` lies on the line of slope `m` through the trailing point,
between the order of vanishing at zero and the degree. -/
private theorem newtonPolygon_eq_of_forall_mem_newtonSlopes_eq (hv : ∀ x, v x = ⊤ → x = 0)
    (hf : f ≠ 0) {m : ℝ} (hm : ∀ s ∈ f.newtonSlopes v, s = m) {n : ℕ}
    (han : f.natTrailingDegree ≤ n) (hnd : n ≤ f.natDegree) :
    f.newtonPolygon v n =
      (((v f.trailingCoeff).untop₀ + m * ((n : ℝ) - f.natTrailingDegree) : ℝ) : WithTop ℝ) := by
  have hn : f.newtonPolygon v n ≠ ⊤ := (newtonPolygon_ne_top_iff v hv hf).mpr ⟨han, hnd⟩
  have hsum : ∑ k ∈ Finset.Ico f.natTrailingDegree n, unitSlope (f.newtonPolygon v) k =
      ∑ _k ∈ Finset.Ico f.natTrailingDegree n, m := by
    refine Finset.sum_congr rfl fun k hk => hm _ ((mem_newtonSlopes f v).mpr ⟨k, ?_, rfl⟩)
    rw [finiteEdges_newtonPolygon f v hv, Set.mem_Ico]
    have := Finset.mem_Ico.mp hk
    omega
  rw [eq_coe_add_sum_unitSlope hn han, newtonPolygon_natTrailingDegree, hsum, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub han]
  ring_nf

/-- **Purity criterion.** If only zero has infinite valuation, every finite slope of `f` equals
`m` exactly when the line of slope `m` through the trailing point `(a, v (coeff a f))`, where `a`
is the order of vanishing of `f` at zero, passes through the leading point and lies on or below
every coefficient point. -/
theorem forall_mem_newtonSlopes_eq_iff (hv : ∀ x, v x = ⊤ → x = 0) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      (v f.leadingCoeff).untop₀ =
          (v f.trailingCoeff).untop₀ + m * ((f.natDegree : ℝ) - f.natTrailingDegree) ∧
        ∀ n : ℕ, (((v f.trailingCoeff).untop₀ + m * ((n : ℝ) - f.natTrailingDegree) : ℝ) :
          WithTop ℝ) ≤ v (f.coeff n) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  constructor
  · intro hm
    refine ⟨?_, fun n => ?_⟩
    · rw [← WithTop.untop₀_coe (_ + _), ← newtonPolygon_eq_of_forall_mem_newtonSlopes_eq hv hf hm
        (natTrailingDegree_le_natDegree f) le_rfl, newtonPolygon_natDegree]
    · by_cases han : f.natTrailingDegree ≤ n
      · by_cases hnd : n ≤ f.natDegree
        · exact (newtonPolygon_eq_of_forall_mem_newtonSlopes_eq hv hf hm han hnd).symm.trans_le
            (f.newtonPolygon_le v n)
        · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hnd), v.map_zero]
          exact le_top
      · rw [coeff_eq_zero_of_lt_natTrailingDegree (not_le.mp han), v.map_zero]
        exact le_top
  · rintro ⟨hlead, hle⟩ s hs
    obtain ⟨k, hk, rfl⟩ := (mem_newtonSlopes f v).mp hs
    rw [finiteEdges_newtonPolygon f v hv, Set.mem_Ico] at hk
    -- The line of slope `m` through the trailing point, in the form `c + m * n`.
    have hH : (fun n : ℕ => (((v f.trailingCoeff).untop₀ - m * f.natTrailingDegree + m * n : ℝ) :
        WithTop ℝ)) ≤ f.newtonPolygon v :=
      le_newtonPolygon (isConvexSeq_affine _ m) fun n => by
        convert hle n using 2
        ring
    have htrail : f.newtonPolygon v f.natTrailingDegree = (((v f.trailingCoeff).untop₀ -
        m * f.natTrailingDegree + m * f.natTrailingDegree : ℝ) : WithTop ℝ) := by
      rw [newtonPolygon_natTrailingDegree, sub_add_cancel,
        WithTop.coe_untop₀_of_ne_top (mt (hv _) (trailingCoeff_nonzero_iff_nonzero.mpr hf))]
    have hlead' : f.newtonPolygon v f.natDegree = (((v f.trailingCoeff).untop₀ -
        m * f.natTrailingDegree + m * f.natDegree : ℝ) : WithTop ℝ) := by
      rw [newtonPolygon_natDegree,
        ← WithTop.coe_untop₀_of_ne_top (mt (hv _) (leadingCoeff_ne_zero.mpr hf)), hlead,
        WithTop.coe_eq_coe]
      ring
    have hon {n : ℕ} (han : f.natTrailingDegree ≤ n) (hnd : n ≤ f.natDegree) :=
      (f.isConvexSeq_newtonPolygon v).eq_affine_of_affine_le htrail hlead' han hnd (hH n)
    rw [unitSlope_def, hon (by omega) hk.2, hon hk.1 hk.2.le, WithTop.untop₀_coe,
      WithTop.untop₀_coe]
    push_cast
    ring

/-- A polynomial whose leading coefficient has valuation zero and whose constant coefficient has
valuation one has positive degree. -/
private theorem natDegree_pos_of_addValuation (hlead : v f.leadingCoeff = 0)
    (h0 : v (f.coeff 0) = 1) : 0 < f.natDegree := by
  refine Nat.pos_of_ne_zero fun hd => ?_
  rw [leadingCoeff, hd, h0] at hlead
  exact one_ne_zero hlead

/-- **Eisenstein polygons.** If only zero has infinite valuation, and `f` has leading coefficient
of valuation zero, constant coefficient of valuation one, and all other coefficients below the
degree of valuation at least one, then the Newton polygon of `f` is the segment from `(0, 1)` to
`(d, 0)`, where `d` is the degree of `f`: it has `d` finite slopes, all equal to `-1 / d`. -/
theorem newtonSlopes_eq_replicate_of_eisenstein (hv : ∀ x, v x = ⊤ → x = 0)
    (hlead : v f.leadingCoeff = 0) (h0 : v (f.coeff 0) = 1)
    (hmem : ∀ n, 0 < n → n < f.natDegree → 1 ≤ v (f.coeff n)) :
    f.newtonSlopes v = Multiset.replicate f.natDegree (-(f.natDegree : ℝ)⁻¹) := by
  have hc0 : f.coeff 0 ≠ 0 := fun h => by simp [h] at h0
  have ha : f.natTrailingDegree = 0 := natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hc0
  have hd := natDegree_pos_of_addValuation hlead h0
  have htrail : (v f.trailingCoeff).untop₀ = 1 := by
    rw [trailingCoeff, ha, h0, WithTop.untop₀_one]
  refine Multiset.eq_replicate.mpr ⟨by rw [card_newtonSlopes f v hv, ha, Nat.sub_zero], ?_⟩
  refine (forall_mem_newtonSlopes_eq_iff hv).mpr ⟨?_, fun n => ?_⟩
  · rw [hlead, htrail, ha, WithTop.untop₀_zero]
    field_simp
    ring
  rw [htrail, ha, Nat.cast_zero, sub_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h0]
  rcases lt_trichotomy n f.natDegree with hnd | rfl | hnd
  · refine le_trans ?_ (hmem n hn hnd)
    rw [← WithTop.coe_one, WithTop.coe_le_coe]
    have : (0 : ℝ) ≤ (f.natDegree : ℝ)⁻¹ * n := by positivity
    linarith
  · rw [← leadingCoeff, hlead, ← WithTop.coe_zero, WithTop.coe_le_coe]
    field_simp
    simp
  · rw [coeff_eq_zero_of_natDegree_lt hnd, v.map_zero]
    exact le_top

end Ring

section Field

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℝ)}

/-- **Eisenstein criterion.** If the valuation takes integer values on nonzero elements, a
polynomial whose leading coefficient has valuation zero, whose constant coefficient has
valuation one, and whose other coefficients below the degree have valuation at least one, is
irreducible. This is the Newton polygon irreducibility criterion for the single slope `-1 / d`. -/
theorem irreducible_of_eisenstein (hint : ∀ x, x ≠ 0 → ∃ n : ℤ, v x = ((n : ℝ) : WithTop ℝ))
    {f : K[X]} (hlead : v f.leadingCoeff = 0) (h0 : v (f.coeff 0) = 1)
    (hmem : ∀ n, 0 < n → n < f.natDegree → 1 ≤ v (f.coeff n)) : Irreducible f := by
  have hc0 : f.coeff 0 ≠ 0 := fun h => by simp [h] at h0
  refine irreducible_of_forall_mem_newtonSlopes_eq_div hint hc0
    (natDegree_pos_of_addValuation hlead h0) (a := -1) (by simp) fun m hm => ?_
  rw [newtonSlopes_eq_replicate_of_eisenstein
    (AddValuation.eq_zero_of_eq_top_of_forall_ne_zero hint) hlead h0 hmem] at hm
  rw [Multiset.eq_of_mem_replicate hm]
  push_cast
  ring

end Field

section Norm

variable {K : Type*} [NormedDivisionRing K] {v : AddValuation K (WithTop ℝ)} {b : ℝ}

/-- **Purity criterion, Gauss form.** Let the norm be `‖x‖ = b ^ (-v x)` for `x ≠ 0`, with
`1 < b`. Every finite slope of `f` equals `m` exactly when, at the radius `b ^ m`, the weighted
leading and trailing terms have the same norm and every weighted term has norm at most that of
the trailing term. -/
theorem forall_mem_newtonSlopes_eq_iff_norm_coeff_mul_rpow_pow_le (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K[X]} {m : ℝ} :
    (∀ s ∈ f.newtonSlopes v, s = m) ↔
      ‖f.leadingCoeff‖ * (b ^ m) ^ f.natDegree =
          ‖f.trailingCoeff‖ * (b ^ m) ^ f.natTrailingDegree ∧
        ∀ n, ‖f.coeff n‖ * (b ^ m) ^ n ≤ ‖f.trailingCoeff‖ * (b ^ m) ^ f.natTrailingDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hnorm {n : ℕ} (hn : f.coeff n ≠ 0) :
      ‖f.coeff n‖ * (b ^ m) ^ n = b ^ (-((v (f.coeff n)).untop₀ - m * n)) := by
    simpa using (f : PowerSeries K).norm_coeff_mul_rpow_pow_eq v hb hv (by simpa using hn) m
  rw [forall_mem_newtonSlopes_eq_iff fun x => v.top_iff.mp, ← coeff_natDegree, trailingCoeff,
    hnorm (coeff_natTrailingDegree_ne_zero.mpr hf),
    hnorm (by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hf),
    Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne']
  refine and_congr ⟨fun h => by rw [h]; ring, fun h => by linarith⟩ (forall_congr' fun n => ?_)
  have hle := PowerSeries.norm_coeff_mul_rpow_pow_le_iff (f : PowerSeries K) v hb hv n m
    ((v (f.coeff f.natTrailingDegree)).untop₀ - m * f.natTrailingDegree)
  rw [coeff_coe] at hle
  rw [hle]
  convert Iff.rfl using 3
  ring

end Norm

end Polynomial
