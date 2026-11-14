/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Entire
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
import Mathlib.Data.Set.Card.Arithmetic
import TauCeti.NumberTheory.NewtonPolygon.Roots

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
A power `(X - C x) ^ h` has the single slope `-v x`, with multiplicity `h`
(`PowerSeries.newtonSlopeMultiplicity_X_sub_C_pow`). Mapping the coefficients along a ring
homomorphism compatible with the valuations preserves the multiplicities
(`PowerSeries.newtonSlopeMultiplicity_map`). When only finitely many finite unit edges have slope
at most `c`, their number is the sum of the multiplicities of the slopes at most `c`
(`PowerSeries.ncard_setOf_unitSlope_newtonPolygon_le`).

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
* `PowerSeries.newtonSlopeMultiplicity_map`: valuation-compatible coefficient maps preserve the
  multiplicities.
* `PowerSeries.ncard_setOf_unitSlope_newtonPolygon_le`: the number of finite unit edges of slope
  at most a cutoff is the sum of the multiplicities of the slopes below it.
* `PowerSeries.newtonSlopeMultiplicity_X_sub_C_pow`: the power `(X - C x) ^ h` has the slope
  `-v x` with multiplicity `h`.
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

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations preserves
the slope multiplicities. -/
theorem newtonSlopeMultiplicity_map {S : Type*} [Ring S] (φ : R →+* S)
    {w : AddValuation S (WithTop ℝ)} (hφ : ∀ x, w (φ x) = v x) (σ : ℝ) :
    (map φ f).newtonSlopeMultiplicity w σ = f.newtonSlopeMultiplicity v σ := by
  rw [newtonSlopeMultiplicity_def, newtonSlopeMultiplicity_def, newtonPolygon_map f v φ hφ]

variable {f v}

/-- The multiplicity of the slope of a finite face is the width `u - l` of the face. -/
theorem newtonSlopeMultiplicity_eq_of_isFiniteFace {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    f.newtonSlopeMultiplicity v σ = u - l :=
  hface.ncard_setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)

/-- **Cutoff counts.** If only finitely many finite unit edges of the Newton polygon of `f` have
slope at most `c`, their number is the sum of the multiplicities of the slopes at most `c`. -/
theorem ncard_setOf_unitSlope_newtonPolygon_le {c : ℝ}
    (hc : {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite) :
    {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.ncard =
      ∑ᶠ σ ∈ Set.Iic c, f.newtonSlopeMultiplicity v σ := by
  set P := f.newtonPolygon v
  have hfib {σ : ℝ} (hσ : σ ≤ c) :
      {n | n ∈ finiteEdges P ∧ unitSlope P n = σ} ⊆
        {n | n ∈ finiteEdges P ∧ unitSlope P n ≤ c} :=
    fun n hn ↦ ⟨hn.1, hn.2.trans_le hσ⟩
  -- Only the finitely many slopes of these edges have nonzero multiplicity.
  have hT : (Set.Iic c ∩ Function.support (f.newtonSlopeMultiplicity v)).Finite := by
    refine (hc.image (unitSlope P)).subset fun σ ⟨hσ, hm⟩ ↦ ?_
    obtain ⟨n, hn⟩ := Set.nonempty_of_ncard_ne_zero hm
    exact ⟨n, hfib hσ hn, hn.2⟩
  -- The edges of slope at most `c` are the disjoint union of the edges of each such slope.
  have hE : {n | n ∈ finiteEdges P ∧ unitSlope P n ≤ c} =
      ⋃ σ ∈ Set.Iic c ∩ Function.support (f.newtonSlopeMultiplicity v),
        {n | n ∈ finiteEdges P ∧ unitSlope P n = σ} := by
    refine subset_antisymm (fun n hn ↦ ?_) (Set.iUnion₂_subset fun σ hσ ↦ hfib hσ.1)
    have hm : f.newtonSlopeMultiplicity v (unitSlope P n) ≠ 0 :=
      Set.ncard_ne_zero_of_mem (s := {m | m ∈ finiteEdges P ∧ unitSlope P m = unitSlope P n})
        ⟨hn.1, rfl⟩ (hc.subset (hfib hn.2))
    exact Set.mem_biUnion
      (⟨hn.2, hm⟩ : unitSlope P n ∈ Set.Iic c ∩ Function.support (f.newtonSlopeMultiplicity v))
      ⟨hn.1, rfl⟩
  rw [← finsum_mem_inter_support, hE, Set.Finite.ncard_biUnion hT (fun σ hσ ↦ hc.subset (hfib hσ.1))
    fun σ _ τ _ hστ ↦ Set.disjoint_left.2 fun n h₁ h₂ ↦ hστ (h₁.2.symm.trans h₂.2)]
  exact finsum_mem_congr rfl fun σ _ ↦ (newtonSlopeMultiplicity_def f v σ).symm

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

namespace PowerSeries

variable {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ))

/-- If only zero has infinite valuation and `v x = -σ`, the power `(X - C x) ^ h` has the slope
`σ` with multiplicity `h`. -/
theorem newtonSlopeMultiplicity_X_sub_C_pow (hv : ∀ x, v x = ⊤ → x = 0) {x : R} {σ : ℝ}
    (hx : v x = ((-σ : ℝ) : WithTop ℝ)) (h : ℕ) :
    ((X - C x) ^ h : R⟦X⟧).newtonSlopeMultiplicity v σ = h := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact WithTop.top_ne_coe (v.map_zero ▸ hx)
  have hpoly : ((X - C x) ^ h : R⟦X⟧) =
      (((Multiset.replicate h x).map (Polynomial.X - Polynomial.C ·)).prod : Polynomial R) := by
    simp [Multiset.map_replicate, Multiset.prod_replicate]
  rw [hpoly, Polynomial.newtonSlopeMultiplicity_coe,
    Polynomial.newtonSlopes_multiset_prod_X_sub_C _ (fun α _ hα ↦ mt (hv α) hα),
    Multiset.filter_eq_self.mpr fun y hy ↦ (Multiset.eq_of_mem_replicate hy).symm ▸ hx0,
    Multiset.map_replicate, hx, WithTop.untop₀_coe, neg_neg, Multiset.count_replicate_self]

/-- If only zero has infinite valuation and `v x = -σ`, the linear factor `X - C x` has the slope
`σ` with multiplicity one. -/
theorem newtonSlopeMultiplicity_X_sub_C (hv : ∀ x, v x = ⊤ → x = 0) {x : R} {σ : ℝ}
    (hx : v x = ((-σ : ℝ) : WithTop ℝ)) :
    (X - C x : R⟦X⟧).newtonSlopeMultiplicity v σ = 1 := by
  simpa using newtonSlopeMultiplicity_X_sub_C_pow v hv hx 1

end PowerSeries
