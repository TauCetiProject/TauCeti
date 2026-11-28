/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Entire
public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Radius
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Entire.Product
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Strassmann
public import TauCeti.RingTheory.PowerSeries.Weierstrass.ZeroCount
import TauCeti.RingTheory.Polynomial.Roots
import TauCeti.RingTheory.Valuation.NormNormalization

/-!
# Counting zeros with multiplicity by Newton polygons

Let `K` be a normed field whose norm comes from a real additive valuation `v` with base `b > 1`,
so `‖x‖ = b ^ (-v x)` for `x ≠ 0` (making `K` ultrametric). Let `f` be a series restricted at
`b ^ σ`, prepared there as `f = u * P` with `u` a unit of the ring of series restricted at `b ^ σ`
and `P` a polynomial. The multiplicity of a zero `a` of `f` in the closed disc `‖a‖ ≤ b ^ σ`, the
order of the good zero `PowerSeries.IsGoodZero f a h`, is the root multiplicity of `a` in `P`
(`PowerSeries.isGoodZero_iff_rootMultiplicity_eq_of_isUnit_mul`), and every root of `P` lies in
that closed disc (`TauCeti.PowerSeries.IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul`), so
over a complete algebraically closed `K` the zeros of `f` there number the degree in which `f` is
distinguished (`TauCeti.PowerSeries.IsDistinguished.exists_card_eq_isGoodZero`), both proved with
Strassmann's theorem. Reading the roots of `P` off its Newton polygon turns this into
exact counts with multiplicity on spheres and open discs:

* when the Newton polygon of `f` has a finite face of slope `σ` and `P` splits, the multiplicity
  of the slope `σ` is the number of roots of `P` on the sphere `‖a‖ = b ^ σ`, counted with
  multiplicity (`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`). Over a
  complete algebraically closed `K` it is therefore the number of zeros of `f` of norm `b ^ σ`,
  counted with multiplicity (`PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`). If
  that face runs from `l` to `j` and `P` splits, then `P` has exactly `l` roots in the open disc
  `‖a‖ < b ^ σ` (`PowerSeries.card_filter_roots_norm_lt_of_isUnit_mul`), so over a complete
  algebraically closed `K` the zeros of `f` there number `l`, counted with multiplicity
  (`PowerSeries.exists_card_eq_isGoodZero_of_isFiniteFace`).

In any complete normed field extension `L` (without assuming `K` is complete) over which a prepared
polynomial `P` (or the canonical disc polynomial of `TauCeti.PowerSeries.IsDiscPreparation`)
splits, the endpoints `l ≤ u` of a finite face of slope `σ` are the lowest dominant and
distinguished degrees of `f` at `b ^ σ`
(`PowerSeries.isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon`), so
`PowerSeries.zeroMultiset f (b ^ σ) L` has `u` elements in the closed disc, `l` in the open disc,
and `newtonSlopeMultiplicity f v σ = u - l` on the sphere. Every finite face of slope `σ` lies
strictly inside `f.radius` (`PowerSeries.lt_radius_of_isFiniteFace_newtonPolygon`), so `f` is
automatically restricted at `b ^ σ` (`PowerSeries.isRestricted_of_isFiniteFace_newtonPolygon`), and
over an algebraically closed complete `L` these three counts hold unconditionally at every finite
face.

Conversely, at any radius `b ^ σ` strictly smaller than `f.radius`, a nonzero series has a finite
face of slope `σ` (`PowerSeries.exists_isFiniteFace_newtonPolygon_iff_lt_radius`), whose endpoints
are `f.order.toNat` plus the numbers of finite unit edges of slope `< σ` and `≤ σ`
(`PowerSeries.left_eq_toNat_order_add_ncard_unitSlope_lt`,
`PowerSeries.right_eq_toNat_order_add_ncard_unitSlope_le`). Hence inside `f.radius` — and in
particular for every nonzero entire series — the open-disc, closed-disc, and sphere zero counts in
an algebraically closed complete extension are read directly off the Newton polygon slopes. For a
canonical Weierstrass product `∏' i, (1 - αᵢ⁻¹ X)` with `‖α i‖ → ∞` cofinitely over any complete
ultrametric normed field `K` (not necessarily algebraically closed), the disc polynomial already
splits over `K`, so the multiplicity of each slope `σ` is `{i | ‖α i‖ = b ^ σ}.ncard`
(`TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_tprod_polynomialHom_one_sub_C_inv_mul_X`).
For the Fredholm series `det (1 - T u)` of a compact operator, a zero `a` gives the eigenvalue
`a⁻¹`, so this is the count by which the slopes of the Fredholm polygon describe the valuations of
eigenvalues with their algebraic multiplicities.

## Main results

* `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`,
  `PowerSeries.card_filter_roots_norm_lt_of_isUnit_mul`: when the prepared polynomial splits, a
  finite face of slope `σ` counts its roots on the sphere and in the open disc.
* `PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`,
  `PowerSeries.exists_card_eq_isGoodZero_of_isFiniteFace`,
  `PowerSeries.IsEntire.exists_card_eq_newtonSlopeMultiplicity_isGoodZero`: `IsGoodZero` counts
  over a complete algebraically closed base field.
* `PowerSeries.card_zeroMultiset_eq_of_isFiniteFace_of_isUnit_mul`,
  `PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace_of_isUnit_mul`,
  `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_isUnit_mul` (and
  `_of_isDiscPreparation` variants): closed-disc, open-disc, and sphere zero counts in any complete
  extension over which the prepared or canonical disc polynomial splits.
* `PowerSeries.card_zeroMultiset_eq_of_isFiniteFace`,
  `PowerSeries.card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace`,
  `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq`: closed-disc,
  open-disc, and sphere zero counts at a finite face in an algebraically closed complete extension.
* `PowerSeries.card_zeroMultiset_eq_toNat_order_add_ncard_unitSlope_le_of_lt_radius`,
  `PowerSeries.card_filter_zeroMultiset_norm_lt_eq_toNat_order_add_ncard_unitSlope_lt_of_lt_radius`,
  `PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_lt_radius` (and
  `PowerSeries.IsEntire` specialisations): zero counts inside `f.radius` directly in terms of the
  order at zero and Newton polygon slopes.
* `TauCeti.PowerSeries.IsEntire.newtonSlopeMultiplicity_tprod_polynomialHom_one_sub_C_inv_mul_X`:
  for a canonical product `∏' i, (1 - αᵢ⁻¹ X)` with `‖α i‖ → ∞` cofinitely, the multiplicity of
  slope `σ` is `{i | ‖α i‖ = b ^ σ}.ncard`.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, Springer,
  1984, §5.2.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))
  {f : K⟦X⟧} {σ : ℝ} {j : ℕ} {u : IsRestricted.subring (R := K) (b ^ σ)} {P : Polynomial K}

include hb hv

/-- **Slope multiplicity and roots on a sphere.** Suppose the Newton polygon of a series `f` has a
finite face of slope `σ` ending at `j`, and `f = u * P` with `u` a unit of the ring of series
restricted at `b ^ σ` and `P` a polynomial of degree at most `j` which splits. Then the
multiplicity of the slope `σ` is the number of roots of `P` of norm `b ^ σ`, counted with
multiplicity. -/
theorem newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) (hu : IsUnit u) (hPdeg : P.natDegree ≤ j)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (hP : P.Splits) :
    f.newtonSlopeMultiplicity v σ = (P.roots.filter fun α ↦ ‖α‖ = b ^ σ).card := by
  classical
  have hfd := isDistinguished_of_isFiniteFace v hb hv hface
  -- The finite unit edges of slope `σ` of `f` lie below `j`, where they are those of `P`.
  have hedges : {i | i ∈ finiteEdges (P.newtonPolygon v) ∧ unitSlope (P.newtonPolygon v) i = σ} =
      {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i = σ} := by
    ext i
    simp only [Set.mem_ofPred_eq, mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hfd hu
      hPdeg hmul]
    refine ⟨fun ⟨⟨hi, hij⟩, hσ⟩ ↦ ?_, fun ⟨hi, hσ⟩ ↦ ?_⟩
    · rw [unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd hu hPdeg hmul hi hij] at hσ
      exact ⟨hi, hσ⟩
    · have hij : i < j := ((hface.setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)).subset
        ⟨hi, hσ⟩).2
      rw [unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd hu hPdeg hmul hi hij]
      exact ⟨⟨hi, hij⟩, hσ⟩
  rw [newtonSlopeMultiplicity_def, ← hedges, ← Polynomial.card_filter_newtonSlopes P v (· = σ),
    Polynomial.card_filter_newtonSlopes_eq (fun _ ↦ v.top_iff.mp) hP]
  -- a point has norm `b ^ σ` exactly when it is nonzero of valuation `-σ`
  refine congrArg _ (Multiset.filter_congr fun α _ ↦ ⟨fun ⟨hα, hσ⟩ ↦ ?_, fun h ↦ ?_⟩)
  · rw [hv α hα]
    exact congrArg _ hσ
  · have hα : α ≠ 0 := by
      rintro rfl
      exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne (by simpa using h)
    exact ⟨hα, (Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne').mp ((hv α hα).symm.trans h)⟩

/-- **Roots in the open disc.** Under the hypotheses of
`PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul`, with the finite face of
slope `σ` running from `l` to `j`, the polynomial `P` has exactly `l` roots of norm less than
`b ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_norm_lt_of_isUnit_mul {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) (hu : IsUnit u) (hPdeg : P.natDegree ≤ j)
    (hmul : (u : K⟦X⟧) * (P : K⟦X⟧) = f) (hP : P.Splits) :
    (P.roots.filter fun α ↦ ‖α‖ < b ^ σ).card = l := by
  have hfd := isDistinguished_of_isFiniteFace v hb hv hface
  have hsphere := newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul v hb hv hface hu
    hPdeg hmul hP
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface] at hsphere
  -- the roots not in the open disc are those on the sphere, since all lie in the closed disc
  have hnot : (P.roots.filter fun α ↦ ¬‖α‖ < b ^ σ) = P.roots.filter fun α ↦ ‖α‖ = b ^ σ :=
    Multiset.filter_congr fun α hα ↦ ⟨fun h ↦ le_antisymm
      (hfd.norm_le_of_mem_roots_of_isUnit_mul (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hu
        hPdeg hmul hα) (not_lt.1 h),
      fun h ↦ h.not_lt⟩
  have hcard : Multiset.card P.roots = j := by
    rw [Polynomial.splits_iff_card_roots.1 hP, TauCeti.PowerSeries.natDegree_eq_of_isUnit_mul
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hfd hu hPdeg hmul]
  have h := congrArg Multiset.card (Multiset.filter_add_not (fun α ↦ ‖α‖ < b ^ σ) P.roots)
  rw [Multiset.card_add, hnot, ← hsphere, hcard] at h
  have := hface.left_le_right
  omega

variable [CompleteSpace K] [IsAlgClosed K] [DecidableEq K]

/-- **Zeros on a sphere, with multiplicity.** Over an algebraically closed field, if the Newton
polygon of a series `f` has a finite face of slope `σ`, the zeros of `f` of norm `b ^ σ`, counted
with multiplicity, form a multiset `Z` with as many elements as the multiplicity of the slope `σ`:
`f` has a good zero of order `Z.count a` at every `a` of norm `b ^ σ`. -/
theorem exists_card_eq_newtonSlopeMultiplicity_isGoodZero {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) :
    ∃ Z : Multiset K, Multiset.card Z = f.newtonSlopeMultiplicity v σ ∧
      (∀ a ∈ Z, ‖a‖ = b ^ σ) ∧ ∀ a, ‖a‖ = b ^ σ → f.IsGoodZero a (Z.count a) := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfd := isDistinguished_of_isFiniteFace v hb hv hface
  obtain ⟨u, P, hu, hP, hmul⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hfd.coeff_ne_zero.isUnit hc (isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface)
  refine ⟨P.roots.filter fun α ↦ ‖α‖ = b ^ σ,
    (newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul v hb hv hface hu
      hP.natDegree_eq.le hmul (IsAlgClosed.splits P)).symm,
    fun a ha ↦ (Multiset.mem_filter.1 ha).2, fun a ha ↦ ?_⟩
  rw [Multiset.count_filter_of_pos (p := fun α ↦ ‖α‖ = b ^ σ) ha]
  exact isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha.le

/-- **Zeros in an open disc, with multiplicity.** Over an algebraically closed field, if the Newton
polygon of a series `f` has a finite face of slope `σ` from `l` to `j`, the zeros of `f` of norm
less than `b ^ σ`, counted with multiplicity, form a multiset `Z` with exactly `l` elements: `f`
has a good zero of order `Z.count a` at every `a` of norm less than `b ^ σ`. -/
theorem exists_card_eq_isGoodZero_of_isFiniteFace {l : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l j) :
    ∃ Z : Multiset K, Multiset.card Z = l ∧ (∀ a ∈ Z, ‖a‖ < b ^ σ) ∧
      ∀ a, ‖a‖ < b ^ σ → f.IsGoodZero a (Z.count a) := by
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfd := isDistinguished_of_isFiniteFace v hb hv hface
  obtain ⟨u, P, hu, hP, hmul⟩ := hfd.exists_isUnit_isMonicOfDegree_mul_eq
    hfd.coeff_ne_zero.isUnit hc (isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface)
  refine ⟨P.roots.filter fun α ↦ ‖α‖ < b ^ σ,
    card_filter_roots_norm_lt_of_isUnit_mul v hb hv hface hu hP.natDegree_eq.le hmul
      (IsAlgClosed.splits P),
    fun a ha ↦ (Multiset.mem_filter.1 ha).2, fun a ha ↦ ?_⟩
  rw [Multiset.count_filter_of_pos (p := fun α ↦ ‖α‖ < b ^ σ) ha]
  exact isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha.le

/-- **Zeros of an entire series on a sphere, with multiplicity.** Over an algebraically closed
field, for every real `σ` the zeros of a nonzero entire series `f` of norm `b ^ σ`, counted with
multiplicity, form a multiset with as many elements as the multiplicity of the slope `σ` of the
Newton polygon of `f`. -/
theorem IsEntire.exists_card_eq_newtonSlopeMultiplicity_isGoodZero (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) :
    ∃ Z : Multiset K, Multiset.card Z = f.newtonSlopeMultiplicity v σ ∧
      (∀ a ∈ Z, ‖a‖ = b ^ σ) ∧ ∀ a, ‖a‖ = b ^ σ → f.IsGoodZero a (Z.count a) := by
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  exact PowerSeries.exists_card_eq_newtonSlopeMultiplicity_isGoodZero v hb hv hface

end PowerSeries

namespace PowerSeries

section ZeroMultiset

variable {K : Type*} [NormedField K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) (L : Type*) [NormedField L] [NormedAlgebra K L]
  [CompleteSpace L] {f : K⟦X⟧}

include hb hv

section IsUnitMul

variable [IsUltrametricDist K]

/-- **Closed-disc zero count at a finite face, split case.** Suppose the Newton polygon of `f` has
a finite face of slope `σ` from `l` to `u`, and `f = e * P` with `e` a unit of the ring of series
restricted at `b ^ σ` and `P` a polynomial splitting over `L`. Then `f` has `u` zeros in the closed
disc `‖x‖ ≤ b ^ σ` of `L`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_isFiniteFace_of_isUnit_mul {σ : ℝ} {l u : ℕ}
    {e : IsRestricted.subring (R := K) (b ^ σ)} {P : Polynomial K}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (he : IsUnit e) (hf : (e : K⟦X⟧) * (P : K⟦X⟧) = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    (f.zeroMultiset (b ^ σ) L).card = u :=
  (isDistinguished_of_isFiniteFace v hb hv hface).card_zeroMultiset_eq_of_isUnit_mul
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) he hf hs

/-- **Open-disc zero count at a finite face, split case.** Under the hypotheses of
`PowerSeries.card_zeroMultiset_eq_of_isFiniteFace_of_isUnit_mul`, `f` has `l` zeros in the open
disc `‖x‖ < b ^ σ` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace_of_isUnit_mul {σ : ℝ} {l u : ℕ}
    {e : IsRestricted.subring (R := K) (b ^ σ)} {P : Polynomial K}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (he : IsUnit e) (hf : (e : K⟦X⟧) * (P : K⟦X⟧) = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ < b ^ σ)).card = l :=
  (isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface).1.card_filter_zeroMultiset_norm_lt_eq_of_isUnit_mul
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) he hf hs

/-- **Sphere zero count at a finite face, split case.** Under the hypotheses of
`PowerSeries.card_zeroMultiset_eq_of_isFiniteFace_of_isUnit_mul`, the multiplicity of the slope `σ`
is the number of zeros of `f` on the sphere `‖x‖ = b ^ σ` of `L`, counted with multiplicity. -/
theorem newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_isUnit_mul {σ : ℝ}
    {l u : ℕ} {e : IsRestricted.subring (R := K) (b ^ σ)} {P : Polynomial K}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (he : IsUnit e) (hf : (e : K⟦X⟧) * (P : K⟦X⟧) = f)
    (hs : (P.map (algebraMap K L)).Splits) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  obtain ⟨hl, hu⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface,
    TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq_of_isUnit_mul hu hl
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) he hf hs]

end IsUnitMul

/-- **Closed-disc zero count for a split disc polynomial.** Suppose the Newton polygon of `f` has a
finite face of slope `σ` from `l` to `u`, and `f = P * U` is a normalised preparation on
`‖x‖ ≤ b ^ σ` whose polynomial `P` splits over `L`. Then `f` has `u` zeros in the closed disc
`‖x‖ ≤ b ^ σ` of `L`, counted with multiplicity. -/
theorem card_zeroMultiset_eq_of_isFiniteFace_of_isDiscPreparation {σ : ℝ} {l u d : ℕ}
    {P : Polynomial K} {U : K⟦X⟧} (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (hP : TauCeti.PowerSeries.IsDiscPreparation (b ^ σ) d f P U)
    (hs : (P.map (algebraMap K L)).Splits) :
    (f.zeroMultiset (b ^ σ) L).card = u := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  obtain ⟨_, hu⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface
  rw [hP.card_zeroMultiset_eq_of_splits (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hs,
    hP.isDistinguished.unique hu]

/-- **Open-disc zero count for a split disc polynomial.** Under the hypotheses of
`PowerSeries.card_zeroMultiset_eq_of_isFiniteFace_of_isDiscPreparation`, `f` has `l` zeros in the
open disc `‖x‖ < b ^ σ` of `L`, counted with multiplicity. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace_of_isDiscPreparation {σ : ℝ}
    {l u d : ℕ} {P : Polynomial K} {U : K⟦X⟧} (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (hP : TauCeti.PowerSeries.IsDiscPreparation (b ^ σ) d f P U)
    (hs : (P.map (algebraMap K L)).Splits) :
    ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ < b ^ σ)).card = l := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  obtain ⟨hl, _⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface
  exact hP.card_filter_zeroMultiset_norm_lt_eq_of_splits hl
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hs

/-- **Sphere zero count for a split disc polynomial.** Under the hypotheses of
`PowerSeries.card_zeroMultiset_eq_of_isFiniteFace_of_isDiscPreparation`, the multiplicity of the
slope `σ` is the number of zeros of `f` on the sphere `‖x‖ = b ^ σ` of `L`, counted with
multiplicity. -/
theorem newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_isDiscPreparation {σ : ℝ}
    {l u d : ℕ} {P : Polynomial K} {U : K⟦X⟧} (hface : IsFiniteFace (f.newtonPolygon v) σ l u)
    (hP : TauCeti.PowerSeries.IsDiscPreparation (b ^ σ) d f P U)
    (hs : (P.map (algebraMap K L)).Splits) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  obtain ⟨hl, hu⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface,
    hP.card_filter_zeroMultiset_norm_eq_eq_of_splits hl
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ) hs,
    hP.isDistinguished.unique hu]

variable [IsAlgClosed L]

/-- **Closed-disc zero count at a finite face.** If the Newton polygon of `f` has a finite face of
slope `σ` from `l` to `u`, then in any algebraically closed complete normed field extension `L` the
zeros of `f` in `‖x‖ ≤ b ^ σ`, counted with multiplicity, number `u`. -/
theorem card_zeroMultiset_eq_of_isFiniteFace {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    (f.zeroMultiset (b ^ σ) L).card = u := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  exact (isDistinguished_of_isFiniteFace v hb hv hface).card_zeroMultiset_eq
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)
    (isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface)

/-- **Open-disc zero count at a finite face.** If the Newton polygon of `f` has a finite face of
slope `σ` from `l` to `u`, then in any algebraically closed complete normed field extension `L` the
zeros of `f` in `‖x‖ < b ^ σ`, counted with multiplicity, number `l`. -/
theorem card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ < b ^ σ)).card = l := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  exact (isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface).1.card_filter_zeroMultiset_norm_lt_eq
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)
    (isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface)

/-- **Slope multiplicities count zeros on a sphere.** If the Newton polygon of `f` has a finite
face of slope `σ`, then in any algebraically closed complete normed field extension `L` the
multiplicity of the slope `σ` is the number of zeros of `f` with `‖x‖ = b ^ σ`, counted with
multiplicity. The face itself makes `f` restricted at `b ^ σ`. -/
theorem newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  have : IsUltrametricDist K := v.isUltrametricDist hb.le hv
  obtain ⟨hl, hu⟩ := isLowestDominant_and_isDistinguished_of_isFiniteFace_newtonPolygon f v hb hv
    hface
  rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface,
    TauCeti.PowerSeries.card_filter_zeroMultiset_norm_eq_eq hu hl
      (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ)
      (isRestricted_of_isFiniteFace_newtonPolygon f v hb hv hface)]

/-- **Sphere zero count inside the disc of convergence.** At every radius `b ^ σ` strictly smaller
than the radius of a nonzero series `f`, the multiplicity of the slope `σ` in the Newton polygon of
`f` is the number of zeros of `f` on `‖x‖ = b ^ σ` in `L`, counted with multiplicity. -/
theorem newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_lt_radius {σ : ℝ}
    (hf0 : f ≠ 0) (hσ : ‖b ^ σ‖ₑ < f.radius) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card := by
  obtain ⟨l, u, hface⟩ := (exists_isFiniteFace_newtonPolygon_iff_lt_radius f v hb hv hf0).mpr hσ
  exact newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq v hb hv L hface

/-- **Open-disc zero count inside the disc of convergence.** At every radius `b ^ σ` strictly
smaller than the radius of a nonzero series `f`, the number of zeros of `f` in `‖x‖ < b ^ σ` in
`L`, counted with multiplicity, is `f.order.toNat` plus the number of finite unit edges of the
Newton polygon of `f` of slope strictly less than `σ`. -/
theorem card_filter_zeroMultiset_norm_lt_eq_toNat_order_add_ncard_unitSlope_lt_of_lt_radius {σ : ℝ}
    (hf0 : f ≠ 0) (hσ : ‖b ^ σ‖ₑ < f.radius) :
    ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ < b ^ σ)).card =
      f.order.toNat +
        {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i < σ}.ncard := by
  obtain ⟨l, u, hface⟩ := (exists_isFiniteFace_newtonPolygon_iff_lt_radius f v hb hv hf0).mpr hσ
  rw [card_filter_zeroMultiset_norm_lt_eq_of_isFiniteFace v hb hv L hface,
    left_eq_toNat_order_add_ncard_unitSlope_lt (fun _ ↦ v.top_iff.mp) hface]

/-- **Closed-disc zero count inside the disc of convergence.** At every radius `b ^ σ` strictly
smaller than the radius of a nonzero series `f`, the number of zeros of `f` in `‖x‖ ≤ b ^ σ` in
`L`, counted with multiplicity, is `f.order.toNat` plus the number of finite unit edges of the
Newton polygon of `f` of slope at most `σ`. -/
theorem card_zeroMultiset_eq_toNat_order_add_ncard_unitSlope_le_of_lt_radius {σ : ℝ}
    (hf0 : f ≠ 0) (hσ : ‖b ^ σ‖ₑ < f.radius) :
    (f.zeroMultiset (b ^ σ) L).card =
      f.order.toNat +
        {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i ≤ σ}.ncard := by
  obtain ⟨l, u, hface⟩ := (exists_isFiniteFace_newtonPolygon_iff_lt_radius f v hb hv hf0).mpr hσ
  rw [card_zeroMultiset_eq_of_isFiniteFace v hb hv L hface,
    right_eq_toNat_order_add_ncard_unitSlope_le (fun _ ↦ v.top_iff.mp) hface]

/-- **Slope multiplicities of entire series count zeros.** For a nonzero entire series `f` and any
algebraically closed complete normed field extension `L`, the multiplicity of every slope `σ` of
the Newton polygon of `f` is the number of zeros of `f` in `L` with `‖x‖ = b ^ σ`, counted with
multiplicity. -/
theorem IsEntire.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) :
    f.newtonSlopeMultiplicity v σ = ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ = b ^ σ)).card :=
  PowerSeries.newtonSlopeMultiplicity_eq_card_filter_zeroMultiset_norm_eq_of_lt_radius v hb hv L
    hf0 (radius_eq_top_iff.mpr hf ▸ eNorm_lt_top)

/-- **Open-disc zero count for an entire series.** For a nonzero entire series `f` and any
algebraically closed complete normed field extension `L`, the number of zeros of `f` in `L` with
`‖x‖ < b ^ σ`, counted with multiplicity, is `f.order.toNat` plus the number of finite unit edges
of the Newton polygon of `f` of slope strictly less than `σ`. -/
theorem IsEntire.card_filter_zeroMultiset_norm_lt_eq_toNat_order_add_ncard_unitSlope_lt
    (hf : f.IsEntire) (hf0 : f ≠ 0) (σ : ℝ) :
    ((f.zeroMultiset (b ^ σ) L).filter (‖·‖ < b ^ σ)).card =
      f.order.toNat +
        {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i < σ}.ncard :=
  PowerSeries.card_filter_zeroMultiset_norm_lt_eq_toNat_order_add_ncard_unitSlope_lt_of_lt_radius
    v hb hv L hf0 (radius_eq_top_iff.mpr hf ▸ eNorm_lt_top)

/-- **Closed-disc zero count for an entire series.** For a nonzero entire series `f` and any
algebraically closed complete normed field extension `L`, the number of zeros of `f` in `L` with
`‖x‖ ≤ b ^ σ`, counted with multiplicity, is `f.order.toNat` plus the number of finite unit edges
of the Newton polygon of `f` of slope at most `σ`. -/
theorem IsEntire.card_zeroMultiset_eq_toNat_order_add_ncard_unitSlope_le (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) :
    (f.zeroMultiset (b ^ σ) L).card =
      f.order.toNat +
        {i | i ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) i ≤ σ}.ncard :=
  PowerSeries.card_zeroMultiset_eq_toNat_order_add_ncard_unitSlope_le_of_lt_radius v hb hv L hf0
    (radius_eq_top_iff.mpr hf ▸ eNorm_lt_top)

end ZeroMultiset

end PowerSeries

open scoped _root_.PowerSeries

namespace TauCeti.PowerSeries.IsEntire

section CanonicalProduct

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

private theorem newtonSlopeMultiplicity_tprod_of_ne_zero {ι : Type*} {α : ι → K}
    (hα : Filter.Tendsto (fun i ↦ ‖α i‖) Filter.cofinite Filter.atTop) (hα0 : ∀ i, α i ≠ 0)
    (σ : ℝ) :
    (((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧)).newtonSlopeMultiplicity v σ =
      {i : ι | ‖α i‖ = b ^ σ}.ncard := by
  classical
  have hr : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  have hfin : {i : ι | ‖α i‖ ≤ b ^ σ}.Finite := by
    simpa only [not_lt] using Filter.eventually_cofinite.mp (hα.eventually_gt_atTop (b ^ σ))
  set s : Finset ι := hfin.toFinset
  have hs : ∀ i, i ∈ s ↔ ‖α i‖ ≤ b ^ σ := fun i ↦ hfin.mem_toFinset
  set F : _root_.PowerSeries.IsEntire.subring K :=
    ∏' i, _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hF0 : (F : K⟦X⟧) ≠ 0 := by
    intro h
    have h1 : _root_.PowerSeries.constantCoeff (F : K⟦X⟧) = 1 := by simp [F]
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hFent : (F : K⟦X⟧).IsEntire := _root_.PowerSeries.IsEntire.mem_subring.mp F.property
  have hdisc := isDiscPreparation_tprod_polynomialHom_one_sub_C_inv_mul_X hα hα0 hr.le hs
  obtain ⟨l, j, hface⟩ := hFent.exists_isFiniteFace_newtonPolygon v hb hv hF0 σ
  have hfd := _root_.PowerSeries.isDistinguished_of_isFiniteFace v hb hv hface
  have hPeq := Polynomial.prod_one_sub_C_inv_mul_X_eq_C_mul_prod_X_sub_C s fun i _ ↦ hα0 i
  have hc0 : ∏ i ∈ s, (-α i)⁻¹ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ inv_ne_zero (neg_ne_zero.mpr (hα0 i))
  have hPsplits : (∏ i ∈ s, (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)).Splits := by
    rw [hPeq]
    exact (Polynomial.Splits.C _).mul
      (Polynomial.Splits.prod fun i _ ↦ Polynomial.Splits.X_sub_C (α i))
  rw [_root_.PowerSeries.newtonSlopeMultiplicity_eq_card_filter_roots_of_isUnit_mul v hb hv
      hface (hdisc.isUnit hr)
      (by rw [hdisc.natDegree_eq, hfd.unique hdisc.isDistinguished])
      (by rw [mul_comm]; exact hdisc.eq_mul.symm) hPsplits,
    hPeq, Polynomial.roots_C_mul_prod_X_sub_C s α hc0, Multiset.filter_map, Multiset.card_map]
  have hset : {i : ι | ‖α i‖ = b ^ σ} = ↑(s.filter fun i ↦ ‖α i‖ = b ^ σ) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hs]
    exact ⟨fun h ↦ ⟨h.le, h⟩, fun h ↦ h.2⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_def, Finset.filter_val]
  rfl

/-- **Newton-polygon slope multiplicities of the canonical Weierstrass product.** Let `K` be a
complete ultrametric normed field whose norm comes from a real additive valuation `v` with base
`b > 1`, and let `α : ι → K` satisfy `‖α i‖ → ∞` cofinitely. For every real slope `σ`, the
multiplicity of `σ` in the Newton polygon of `∏' i, (1 - αᵢ⁻¹ X)` is the number of indices `i` with
`‖α i‖ = b ^ σ`, without assuming `K` is algebraically closed or that `α` avoids `0`. -/
theorem newtonSlopeMultiplicity_tprod_polynomialHom_one_sub_C_inv_mul_X {ι : Type*} {α : ι → K}
    (hα : Filter.Tendsto (fun i ↦ ‖α i‖) Filter.cofinite Filter.atTop) (σ : ℝ) :
    (((∏' i, _root_.PowerSeries.IsEntire.polynomialHom
      (1 - Polynomial.C (α i)⁻¹ * Polynomial.X) :
        _root_.PowerSeries.IsEntire.subring K) : K⟦X⟧)).newtonSlopeMultiplicity v σ =
      {i : ι | ‖α i‖ = b ^ σ}.ncard := by
  let S : Set ι := {i : ι | α i ≠ 0}
  set φ : ι → _root_.PowerSeries.IsEntire.subring K := fun i ↦
    _root_.PowerSeries.IsEntire.polynomialHom (1 - Polynomial.C (α i)⁻¹ * Polynomial.X)
  have hsupp : Function.mulSupport φ ⊆ S := by
    intro i hi
    by_contra h0
    have hα0 : α i = 0 := not_not.mp h0
    exact hi (by simp [φ, hα0])
  rw [← tprod_subtype_eq_of_mulSupport_subset hsupp,
    newtonSlopeMultiplicity_tprod_of_ne_zero v hb hv
      (hα.comp Subtype.val_injective.tendsto_cofinite) (fun j : S ↦ j.property) σ]
  have himg : (Subtype.val : S → ι) '' {j : S | ‖α j.val‖ = b ^ σ} = {i : ι | ‖α i‖ = b ^ σ} := by
    ext i
    simp only [Set.mem_image, Set.mem_ofPred_eq, Subtype.exists]
    refine ⟨fun ⟨_, _, h, heq⟩ ↦ heq ▸ h, fun h ↦ ⟨i, ?_, h, rfl⟩⟩
    rintro h0
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne (by simpa [h0] using h)
  rw [← himg, Set.ncard_image_of_injective _ Subtype.val_injective]

end CanonicalProduct

end TauCeti.PowerSeries.IsEntire
