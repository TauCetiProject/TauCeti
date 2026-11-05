/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Entire
public import TauCeti.NumberTheory.NewtonPolygon.Slopes

/-!
# Slope multiplicities of Newton polygons of power series

The Newton polygon of a power series can have infinitely many finite unit edges, so its finite
slopes do not form a multiset. Instead, the *multiplicity* of a real slope `σ`,
`PowerSeries.newtonSlopeMultiplicity f v σ`, is the number of finite unit edges of slope `σ`.
When the polygon has a finite face of slope `σ`, the multiplicity is the width of that face
(`PowerSeries.newtonSlopeMultiplicity_eq_of_isFiniteFace`). For a polynomial it is the
multiplicity of `σ` in the finite slope multiset `Polynomial.newtonSlopes`
(`Polynomial.newtonSlopeMultiplicity_coe`). The substitution `X ↦ c X` shifts every slope by
the valuation of `c`, with the same multiplicities (`PowerSeries.newtonSlopeMultiplicity_rescale`).

Fix a real additive valuation `v` on a normed division ring and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. A nonzero entire series has a finite face of every
slope (`PowerSeries.IsEntire.exists_isFiniteFace_newtonPolygon`), and the Newton polygon of a
product of entire series is the Minkowski sum of those of the factors. Hence multiplicities of
slopes add under multiplication of nonzero entire series
(`PowerSeries.IsEntire.newtonSlopeMultiplicity_mul`).

Fredholm determinants `det (1 - T u)` of compact operators are nonzero entire series, and these
multiplicities are the slope multiplicities of their Newton polygons.

## Main definitions

* `PowerSeries.newtonSlopeMultiplicity f v σ`: the number of finite unit edges of slope `σ` of
  the Newton polygon of `f`.

## Main results

* `PowerSeries.newtonSlopeMultiplicity_eq_of_isFiniteFace`: the multiplicity is the width of the
  finite face.
* `Polynomial.newtonSlopeMultiplicity_coe`: comparison with the finite slope multiset of a
  polynomial.
* `PowerSeries.newtonSlopeMultiplicity_rescale`: rescaling the variable shifts the slopes.
* `PowerSeries.IsEntire.newtonSlopeMultiplicity_mul`: multiplicities add under multiplication.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

open TauCeti

namespace PowerSeries

section Ring

variable {R : Type*} [Ring R] (f : R⟦X⟧) (v : AddValuation R (WithTop ℝ))

/-- The multiplicity of a real slope `σ` in the Newton polygon of `f`: the number of its finite
unit edges of slope `σ`. It is `0` when `σ` is not a finite slope. If infinitely many unit edges
have slope `σ`, as along a terminal ray, it is the junk value `0` of `Set.ncard`; this does not
happen for nonzero entire series. -/
noncomputable def newtonSlopeMultiplicity (σ : ℝ) : ℕ :=
  {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n = σ}.ncard

/-- The multiplicity of a slope counts the finite unit edges of that slope. -/
theorem newtonSlopeMultiplicity_def (σ : ℝ) :
    f.newtonSlopeMultiplicity v σ =
      {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n = σ}.ncard :=
  (rfl)

/-- The zero series has no finite slopes. -/
@[simp]
theorem newtonSlopeMultiplicity_zero (σ : ℝ) : (0 : R⟦X⟧).newtonSlopeMultiplicity v σ = 0 := by
  simp [newtonSlopeMultiplicity_def]

variable {f v}

/-- The multiplicity of the slope of a finite face is the width `u - l` of the face. -/
theorem newtonSlopeMultiplicity_eq_of_isFiniteFace {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    f.newtonSlopeMultiplicity v σ = u - l :=
  hface.ncard_setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)

end Ring

section CommRing

variable {R : Type*} [CommRing R] {v : AddValuation R (WithTop ℝ)}

/-- The substitution `X ↦ c X` shifts every finite slope by the valuation of `c` and preserves
the multiplicities. -/
theorem newtonSlopeMultiplicity_rescale (f : R⟦X⟧) {c : R} (hc : v c ≠ ⊤) (σ : ℝ) :
    (rescale c f).newtonSlopeMultiplicity v (σ + (v c).untop₀) =
      f.newtonSlopeMultiplicity v σ := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
  have hpoly : (rescale c f).newtonPolygon v =
      fun n => f.newtonPolygon v n + ((0 + r * n : ℝ) : WithTop ℝ) := by
    simp only [f.newtonPolygon_rescale v hc, ← hr, ← WithTop.coe_nsmul, nsmul_eq_mul, zero_add,
      mul_comm]
  rw [newtonSlopeMultiplicity_def, newtonSlopeMultiplicity_def, hpoly, finiteEdges_add_affine]
  congr 1
  ext n
  refine and_congr_right fun hn => ?_
  rw [unitSlope_add_affine hn, ← hr, WithTop.untop₀_coe, add_left_inj]

end CommRing

section Entire

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f g : K⟦X⟧}

include hb hv

/-- **Multiplicities add under products.** For nonzero entire series, the multiplicity of every
slope in the Newton polygon of `f * g` is the sum of its multiplicities for `f` and `g`. -/
theorem IsEntire.newtonSlopeMultiplicity_mul (hf : f.IsEntire) (hg : g.IsEntire) (hf0 : f ≠ 0)
    (hg0 : g ≠ 0) (σ : ℝ) :
    (f * g).newtonSlopeMultiplicity v σ =
      f.newtonSlopeMultiplicity v σ + g.newtonSlopeMultiplicity v σ := by
  obtain ⟨l, u, hfσ⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  obtain ⟨l', u', hgσ⟩ := hg.exists_isFiniteFace_newtonPolygon v hb hv hg0 σ
  have hfgσ := hfσ.minkowskiSum hgσ
  rw [← hf.newtonPolygon_mul v hb hv hg] at hfgσ
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hfgσ,
    newtonSlopeMultiplicity_eq_of_isFiniteFace hfσ, newtonSlopeMultiplicity_eq_of_isFiniteFace hgσ]
  have := hfσ.left_le_right
  have := hgσ.left_le_right
  omega

end Entire

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] (p : R[X]) (v : AddValuation R (WithTop ℝ))

/-- The multiplicity of a slope in the Newton polygon of a polynomial, viewed as a power series,
is its multiplicity in the finite slope multiset. -/
@[simp]
theorem newtonSlopeMultiplicity_coe (σ : ℝ) :
    (p : PowerSeries R).newtonSlopeMultiplicity v σ = (p.newtonSlopes v).count σ := by
  simp_rw [PowerSeries.newtonSlopeMultiplicity_def, newtonPolygon_coe,
    Multiset.count_eq_card_filter_eq, card_filter_newtonSlopes, eq_comm]

end Polynomial

namespace PowerSeries

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- The constant series `1` has no finite slopes. -/
@[simp]
theorem newtonSlopeMultiplicity_one (σ : ℝ) : (1 : R⟦X⟧).newtonSlopeMultiplicity v σ = 0 := by
  rw [← Polynomial.coe_one, Polynomial.newtonSlopeMultiplicity_coe, ← Polynomial.C_1,
    Polynomial.newtonSlopes_C, Multiset.count_zero]

end PowerSeries
