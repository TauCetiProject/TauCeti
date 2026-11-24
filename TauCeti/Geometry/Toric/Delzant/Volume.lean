/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Measure
public import TauCeti.Geometry.Toric.Delzant.CornerChop
public import TauCeti.Geometry.Toric.Delzant.Equiv
public import TauCeti.Geometry.Toric.Delzant.Hirzebruch
public import TauCeti.Geometry.Toric.Delzant.Interval
public import TauCeti.Geometry.Toric.Delzant.Prod
public import TauCeti.Geometry.Toric.Delzant.Simplex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Algebra.Group.Pi.Lemmas
import TauCeti.MeasureTheory.Measure.Lebesgue.RegionBetween
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Orthant

/-!
# Volumes of Delzant polytopes

The volume of a moment polytope `Δ ⊂ V*` is measured by the lattice-normalized Lebesgue measure
`TauCeti.Toric.IsIntegralLattice.dualMeasure`, for which the weight lattice has covolume one. This
is the volume in the formula `vol(M) = (2π)^n vol(Δ)` for a symplectic toric manifold `M` of
dimension `2n` with moment polytope `Δ`. This file proves the general properties of these volumes
and computes them for the basic examples.

A facet polyhedron is closed, hence measurable (`TauCeti.Toric.measurableSet_facetPolyhedron`).
Its volume is unchanged by translating it, which is the freedom of shifting a moment map by a
constant (`TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_add`), and by integral
changes of the lattice, under which the polyhedron of the mapped normals corresponds to the
original one (`TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_map`). The volume of a
product polyhedron is the product of the volumes
(`TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_prod`). A Delzant polytope has finite
positive volume (`TauCeti.Toric.IsDelzant.dualMeasure_facetPolyhedron_lt_top`,
`TauCeti.Toric.IsDelzant.dualMeasure_facetPolyhedron_pos`): it is compact, and it contains the
open set of points lying on none of its facets, which is nonempty.

For the standard lattices, the volume is Lebesgue measure in the coordinates `x (eⱼ)`. The
interval `[0, a]`, the moment polytope of the two-sphere, has length `a`
(`TauCeti.Toric.dualMeasure_facetPolyhedron_interval`). The Hirzebruch trapezoid
`{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}` with `0 ≤ a`, `0 ≤ b` and `k b ≤ a` has area
`a b - k b² / 2` (`TauCeti.Toric.dualMeasure_facetPolyhedron_hirzebruch`, which states the area as
`ENNReal.ofReal (a b - k b² / 2)`, so that it also covers the empty trapezoid of `b < 0`). For
`k = 0` this is the rectangle `[0, a] × [0, b]` of `S² × S²`, of area `a b`. The standard simplex
`{0 ≤ x(eₖ), ∑ k, x(eₖ) ≤ a}` of size `a ≥ 0` in `ℝⁿ`, the moment polytope of `ℂPⁿ`, has volume
`aⁿ / n!` (`TauCeti.Toric.dualMeasure_facetPolyhedron_simplex`).

Chopping a smooth vertex `v` off a polyhedron at a small depth `ε > 0`
(`TauCeti.Toric.cornerChopNormal`, `TauCeti.Toric.cornerChopSupport`), the polytope operation of
the toric symplectic blowup at the fixed point over `v`, removes `εⁿ / n!` from the volume
(`TauCeti.Toric.IsIntegralLattice.eventually_dualMeasure_facetPolyhedron_cornerChop_add`). The
removed part is the simplex `{y j ≥ 0, ∑ j, y j < ε}` in the coordinates `y j = ⟨x, u j⟩ - c j`
relative to `v`, whenever this simplex lies in the polyhedron
(`TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_cornerChop_add`). Since the normals
`u j` at `v` form a basis of the lattice, these coordinates carry the lattice-normalized measure to
Lebesgue measure, and the simplex has volume `εⁿ / n!`. For small `ε` the simplex does lie in the
polyhedron, as the constraints inactive at `v` stay inactive on it
(`TauCeti.Toric.IsSmoothVertex.eventually_forall_mem_facetPolyhedron`). For the corner `0` of the
standard simplex of size `a` it does so for every depth `ε ≤ a`, and the chopped simplex has volume
`(aⁿ - εⁿ) / n!` at every depth `ε > 0`; for `0 < ε < a` it is the polytope of `ℂPⁿ` blown up at a
point (`TauCeti.Toric.dualMeasure_facetPolyhedron_simplex_cornerChop`).

## Main results

* `TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_add`: translation invariance.
* `TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_map`: invariance under lattice
  isomorphisms.
* `TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_prod`: volumes of products.
* `TauCeti.Toric.IsDelzant.dualMeasure_facetPolyhedron_pos`,
  `TauCeti.Toric.IsDelzant.dualMeasure_facetPolyhedron_lt_top`: Delzant polytopes have finite
  positive volume.
* `TauCeti.Toric.dualMeasure_facetPolyhedron_interval`: the interval `[0, a]` has length `a`.
* `TauCeti.Toric.dualMeasure_facetPolyhedron_hirzebruch`: the Hirzebruch trapezoid has area
  `ENNReal.ofReal (a b - k b² / 2)`.
* `TauCeti.Toric.dualMeasure_facetPolyhedron_simplex`: the standard simplex of size `a` in `ℝⁿ`
  has volume `aⁿ / n!`.
* `TauCeti.Toric.IsIntegralLattice.dualMeasure_facetPolyhedron_cornerChop_add`: a corner chop
  whose removed simplex lies in the polyhedron removes volume `εⁿ / n!`.
* `TauCeti.Toric.IsIntegralLattice.eventually_dualMeasure_facetPolyhedron_cornerChop_add`: a small
  corner chop at a smooth vertex removes volume `εⁿ / n!`.
* `TauCeti.Toric.dualMeasure_facetPolyhedron_simplex_cornerChop`: the simplex of size `a` with the
  corner `0` chopped at depth `ε`, for `0 < ε < a` the polytope of `ℂPⁿ` blown up at a point, has
  volume `(aⁿ - εⁿ) / n!`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28–30.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 2.
-/

public section

open Filter MeasureTheory Module Set Topology
open scoped ENNReal

namespace TauCeti.Toric

section General

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-- A facet polyhedron is measurable. -/
theorem measurableSet_facetPolyhedron [MeasurableSpace (StrongDual ℝ V)]
    [OpensMeasurableSpace (StrongDual ℝ V)] : MeasurableSet (facetPolyhedron i u c) :=
  isClosed_facetPolyhedron.measurableSet

variable [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]

/-- **Translating a polyhedron does not change its volume.** Shifting the support constants by the
values `y (i (u j))` of a functional `y` translates the polyhedron by `y`. -/
theorem IsIntegralLattice.dualMeasure_facetPolyhedron_add (h : IsIntegralLattice i)
    (y : StrongDual ℝ V) :
    h.dualMeasure (facetPolyhedron i u fun j ↦ c j + y (i (u j))) =
      h.dualMeasure (facetPolyhedron i u c) := by
  rw [facetPolyhedron_add, measure_vadd]

namespace IsDelzant

/-- A Delzant polytope has finite volume, being compact. -/
theorem dualMeasure_facetPolyhedron_lt_top (hΔ : IsDelzant i u c) (h : IsIntegralLattice i) :
    h.dualMeasure (facetPolyhedron i u c) < ∞ := by
  have := h.finiteDimensional
  exact hΔ.isCompact.measure_lt_top

/-- **A Delzant polytope has positive volume.** The points lying on none of its facets form an
open subset of it, which is nonempty. -/
theorem dualMeasure_facetPolyhedron_pos [Finite ι] (hΔ : IsDelzant i u c)
    (h : IsIntegralLattice i) : 0 < h.dualMeasure (facetPolyhedron i u c) := by
  have := h.finiteDimensional
  obtain ⟨x, hx, hempty⟩ := hΔ.exists_activeSet_eq_empty h.injective
  let U : Set (StrongDual ℝ V) := {y | ∀ j, c j < y (i (u j))}
  have hU : IsOpen U := by
    simp only [U, ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦
      isOpen_lt continuous_const ((ContinuousLinearMap.apply ℝ ℝ (i (u j))).continuous)
  have hxU : x ∈ U := fun j ↦ (mem_facetPolyhedron.1 hx j).lt_of_ne fun hj ↦ by
    have : j ∈ activeSet (facetPairing i u) c x := by simpa [mem_activeSet] using hj.symm
    simp [hempty] at this
  have hUΔ : U ⊆ facetPolyhedron i u c := fun y hy ↦ mem_facetPolyhedron.2 fun j ↦ (hy j).le
  exact (hU.measure_pos h.dualMeasure ⟨x, hxU⟩).trans_le (measure_mono hUΔ)

end IsDelzant

variable {ι' N' V' : Type*} [AddCommGroup N'] [NormedAddCommGroup V'] [NormedSpace ℝ V']
  {i' : N' →+ V'} [MeasurableSpace (StrongDual ℝ V')] [BorelSpace (StrongDual ℝ V')]

/-- **Volumes are invariant under lattice isomorphisms.** If `f : N ≃+ N'` and `g : V ≃L[ℝ] V'`
are compatible, the polyhedron of the mapped normals `f ∘ u` has the volume of the polyhedron of
`u`. -/
theorem IsIntegralLattice.dualMeasure_facetPolyhedron_map (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') (f : N ≃+ N') (g : V ≃L[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n)) :
    h'.dualMeasure (facetPolyhedron i' (f ∘ u) c) = h.dualMeasure (facetPolyhedron i u c) := by
  have hg : Continuous fun y : StrongDual ℝ V' ↦ y.comp (g : V →L[ℝ] V') :=
    (ContinuousLinearMap.precomp ℝ (g : V →L[ℝ] V')).continuous
  rw [← h.map_comp_dualMeasure h' f g hfg, Measure.map_apply hg.measurable
    measurableSet_facetPolyhedron]
  congr 1
  ext y
  exact (comp_mem_facetPolyhedron_iff hfg).symm

variable {u' : ι' → N'} {c' : ι' → ℝ}
  [MeasurableSpace (StrongDual ℝ (V × V'))] [BorelSpace (StrongDual ℝ (V × V'))]

/-- **The volume of a product polyhedron** is the product of the volumes of its factors. -/
theorem IsIntegralLattice.dualMeasure_facetPolyhedron_prod (h : IsIntegralLattice i)
    (h' : IsIntegralLattice i') :
    (h.prod h').dualMeasure (facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c')) =
      h.dualMeasure (facetPolyhedron i u c) * h'.dualMeasure (facetPolyhedron i' u' c') := by
  have := h.finiteDimensional
  have := h'.finiteDimensional
  rw [h.dualMeasure_prod h', Measure.map_apply
    (ContinuousLinearMap.coprodEquivL ℝ).continuous.measurable measurableSet_facetPolyhedron]
  have hpre : ContinuousLinearMap.coprodEquivL ℝ ⁻¹'
      facetPolyhedron (i.prodMap i') (prodNormal u u') (Sum.elim c c') =
      facetPolyhedron i u c ×ˢ facetPolyhedron i' u' c' := by
    ext ⟨y, y'⟩
    exact coprod_mem_facetPolyhedron_prod_iff y y'
  rw [hpre, Measure.prod_prod]

/-- **The volume removed by a corner chop.** Let `Δ = {x | c j ≤ ⟨x, u j⟩}` be a polyhedron in an
integral lattice, let `s` index facets whose normals form a basis of the lattice, and let
`n = dim V`. If the simplex `{y j ≥ 0, ∑ j, y j ≤ ε}` of size `ε > 0` in the coordinates
`y j = ⟨x, u j⟩ - c j`, `j ∈ s`, lies in `Δ`, then chopping it off removes the volume `εⁿ / n!`,
since these coordinates carry the lattice-normalized measure to Lebesgue measure:

`vol(Δ chopped at depth ε) + εⁿ / n! = vol(Δ)`. -/
theorem IsIntegralLattice.dualMeasure_facetPolyhedron_cornerChop_add (h : IsIntegralLattice i)
    {s : Finset ι} (b : Basis s ℤ N) (hb : ∀ j, b j = u j) {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ x : StrongDual ℝ V, (∀ j ∈ s, c j ≤ x (i (u j))) →
      ∑ j ∈ s, (x (i (u j)) - c j) ≤ ε → x ∈ facetPolyhedron i u c) :
    h.dualMeasure (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)) +
        ENNReal.ofReal (ε ^ finrank ℝ V / (finrank ℝ V).factorial) =
      h.dualMeasure (facetPolyhedron i u c) := by
  -- The dual coordinates of the basis `b` are the pairings with the normals `u j`, `j ∈ s`.
  have he (x : StrongDual ℝ V) (j : s) : (h.dualBasis b).equivFun x j = x (i (u j)) := by
    simp [hb]
  have hcard : finrank ℝ V = Fintype.card s := by
    rw [← h.finrank_eq, finrank_eq_card_basis b]
  -- The chopped-off part is the simplex at the corner, which lies in `Δ`.
  let T : Set (s → ℝ) := {y | (∀ j : s, c j ≤ y j) ∧ ∑ j : s, (y j - c j) < ε}
  have hdiff : facetPolyhedron i u c \
      facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε) =
        (h.dualBasis b).equivFun ⁻¹' T := by
    ext x
    simp only [Set.mem_sdiff, mem_facetPolyhedron_cornerChop_iff, not_and, not_le, mem_preimage,
      mem_ofPred_eq, T, he, Finset.sum_coe_sort s fun j ↦ x (i (u j)) - c j]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨fun j ↦ mem_facetPolyhedron.1 hx j, hlt hx⟩
    · rintro ⟨hxs, hlt⟩
      exact ⟨hε x (fun j hj ↦ hxs ⟨j, hj⟩) hlt.le, fun _ ↦ hlt⟩
  -- Translated to the corner, it is the standard simplex of size `ε`.
  have hT : T = (· + -fun j : s ↦ c j) ⁻¹' {y | (∀ j, 0 ≤ y j) ∧ ∑ j, 1 * y j < ε} := by
    ext y
    simp [T, ← sub_eq_add_neg]
  rw [← measure_inter_add_sdiff (facetPolyhedron i u c)
      (measurableSet_facetPolyhedron (i := i) (u := cornerChopNormal u s)
        (c := cornerChopSupport c s ε)),
    inter_eq_right.2 facetPolyhedron_cornerChop_subset, hdiff,
    h.dualMeasure_preimage_dualBasis_equivFun, hT, measure_preimage_add_right,
    volume_setOf_forall_nonneg_and_sum_mul_lt (fun _ ↦ one_pos) hε0,
    hcard]
  simp

/-- **The volume removed by a small corner chop.** Let `v` be a smooth vertex of the polyhedron
`Δ = {x | c j ≤ ⟨x, u j⟩}` in an integral lattice, at which the facets indexed by `s` meet, and
let `n = dim V`. For every sufficiently small `ε > 0`, chopping the corner `v` off `Δ` at depth `ε`
removes the simplex `{y j ≥ 0, ∑ j, y j < ε}` in the coordinates `y j = ⟨x, u j⟩ - c j` relative to
`v`, which has volume `εⁿ / n!` since the normals `u j` at `v` form a basis of the lattice:

`vol(Δ chopped at depth ε) + εⁿ / n! = vol(Δ)`.

On the symplectic side, `(2π)ⁿ εⁿ / n!` is the volume of the ball of capacity `2π ε` removed by
the toric symplectic blowup at the fixed point over `v`. -/
theorem IsIntegralLattice.eventually_dualMeasure_facetPolyhedron_cornerChop_add [Finite ι]
    (h : IsIntegralLattice i) {s : Finset ι} {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v)
    (hvP : v ∈ facetPolyhedron i u c) (hs : (s : Set ι) = activeSet (facetPairing i u) c v) :
    ∀ᶠ ε in 𝓝[>] 0,
      h.dualMeasure (facetPolyhedron i (cornerChopNormal u s) (cornerChopSupport c s ε)) +
          ENNReal.ofReal (ε ^ finrank ℝ V / (finrank ℝ V).factorial) =
        h.dualMeasure (facetPolyhedron i u c) := by
  -- The normals at `v` form a basis of `N` indexed by `s`.
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hv
  let b' : Basis s ℤ N :=
    b.reindex (Equiv.subtypeEquivRight fun j ↦ by rw [← Finset.mem_coe, hs])
  filter_upwards [self_mem_nhdsWithin,
    (hv.eventually_forall_mem_facetPolyhedron h hvP hs).filter_mono nhdsWithin_le_nhds]
    with ε (hε0 : 0 < ε) hε
  exact h.dualMeasure_facetPolyhedron_cornerChop_add b' (fun j ↦ by simp [b', hb]) hε0 hε

end General

/-! ### Examples -/

/-- **The interval `[0, a]` has length `a`** for the lattice-normalized measure of `ℤ ⊂ ℝ`. -/
theorem dualMeasure_facetPolyhedron_interval (a : ℝ) :
    isIntegralLattice_castAddHom.dualMeasure
        (facetPolyhedron (Int.castAddHom ℝ) ![1, -1] ![0, -a]) = ENNReal.ofReal a := by
  let b := Basis.singleton (Fin 1) ℤ
  have hpre : facetPolyhedron (Int.castAddHom ℝ) ![1, -1] ![0, -a] =
      (isIntegralLattice_castAddHom.dualBasis b).equivFun ⁻¹' univ.pi fun _ ↦ Icc 0 a := by
    ext x
    rw [mem_facetPolyhedron_interval_iff, mem_preimage, mem_univ_pi]
    simp only [IsIntegralLattice.dualBasis_equivFun]
    simp [b]
  rw [hpre, isIntegralLattice_castAddHom.dualMeasure_preimage_dualBasis_equivFun, volume_pi_pi]
  simp

/-- **The area of a Hirzebruch trapezoid.** For `0 ≤ a` and `k b ≤ a`, the trapezoid
`{0 ≤ x(e₁), 0 ≤ x(e₂) ≤ b, x(e₁) + k x(e₂) ≤ a}` has area `ENNReal.ofReal (a b - k b² / 2)` for
the lattice-normalized measure of `ℤ² ⊂ ℝ²`: this is `a b - k b² / 2` when `0 ≤ b`, while for
`b < 0` the trapezoid is empty and has area zero. For `k = 0` it is the rectangle
`[0, a] × [0, b]`. -/
theorem dualMeasure_facetPolyhedron_hirzebruch {k : ℤ} {a b : ℝ} (ha : 0 ≤ a) (hkb : k * b ≤ a) :
    (isIntegralLattice_intCast 2).dualMeasure
        (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
          (hirzebruchSupport a b)) = ENNReal.ofReal (a * b - k * b ^ 2 / 2) := by
  let e := (isIntegralLattice_intCast 2).dualBasis (Pi.basisFun ℤ (Fin 2))
  -- In the coordinates `(x(e₂), x(e₁))` the trapezoid is the region below `t ↦ a - k t`.
  have hmp : MeasurePreserving (Prod.swap ∘ MeasurableEquiv.finTwoArrow ∘ e.equivFun)
      (isIntegralLattice_intCast 2).dualMeasure volume :=
    (Measure.measurePreserving_swap.comp (volume_preserving_finTwoArrow ℝ)).comp
      ((isIntegralLattice_intCast 2).measurePreserving_dualBasis_equivFun _)
  have hpre : facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin 2)) (hirzebruchNormal k)
      (hirzebruchSupport a b) = (Prod.swap ∘ MeasurableEquiv.finTwoArrow ∘ e.equivFun) ⁻¹'
        closedRegionBetween 0 (fun t ↦ a - k * t) (Icc 0 b) := by
    ext x
    simp only [mem_facetPolyhedron_hirzebruch_iff, mem_preimage, Function.comp_apply,
      MeasurableEquiv.finTwoArrow_apply, e, IsIntegralLattice.dualBasis_equivFun,
      Pi.basisFun_apply, AddMonoidHom.compLeft_single, Int.coe_castAddHom, Int.cast_one,
      Prod.fst_swap, Prod.snd_swap, mem_closedRegionBetween, Pi.zero_apply, mem_Icc]
    constructor
    · rintro ⟨h₀, h₁, h₂, h₃⟩
      exact ⟨⟨h₁, h₂⟩, h₀, by linarith⟩
    · rintro ⟨⟨h₁, h₂⟩, h₀, h₃⟩
      exact ⟨h₀, h₁, h₂, by linarith⟩
  rw [hpre, hmp.measure_preimage (measurableSet_closedRegionBetween measurable_zero (by fun_prop)
    measurableSet_Icc).nullMeasurableSet, volume_closedRegionBetween_zero_sub_mul ha hkb]

/-- **The volume of the standard simplex.** For `0 ≤ a`, the simplex
`{0 ≤ x(eₖ) for every k, ∑ k, x(eₖ) ≤ a}` of size `a` in `ℝⁿ`, the moment polytope of `ℂPⁿ`, has
volume `aⁿ / n!` for the lattice-normalized measure of `ℤⁿ ⊂ ℝⁿ`. For `n = 0` it is a point, of
volume one. -/
theorem dualMeasure_facetPolyhedron_simplex (n : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (isIntegralLattice_intCast n).dualMeasure
        (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
          (simplexSupport a)) = ENNReal.ofReal (a ^ n / n.factorial) := by
  have hpre : facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n)) (simplexNormal (Fin n))
      (simplexSupport a) =
        ((isIntegralLattice_intCast n).dualBasis (Pi.basisFun ℤ (Fin n))).equivFun ⁻¹'
          {y | (∀ j, 0 ≤ y j) ∧ ∑ j, 1 * y j ≤ a} := by
    ext x
    simp
  rw [hpre, IsIntegralLattice.dualMeasure_preimage_dualBasis_equivFun,
    volume_setOf_forall_nonneg_and_sum_mul_le (fun _ ↦ one_pos) ha]
  simp

/-- **The volume of a blown-up projective space.** Chopping the corner `0` off the standard simplex
of size `a ≥ 0` in `ℝⁿ` at a depth `ε > 0` gives the polytope
`{0 ≤ x(eₖ) for every k, ε ≤ ∑ k, x(eₖ) ≤ a}`, for `ε < a` the moment polytope of the blowup of
`ℂPⁿ` at a fixed point. Its volume is `(aⁿ - εⁿ) / n!` for the lattice-normalized measure of
`ℤⁿ ⊂ ℝⁿ`, which is `0` when `a < ε` and the polytope is empty. For `n = 2` and `ε ≤ a` this is the
area `(a² - ε²) / 2` of the Hirzebruch trapezoid with `k = 1` and `b = a - ε`. -/
theorem dualMeasure_facetPolyhedron_simplex_cornerChop (n : ℕ) {a ε : ℝ} (ha : 0 ≤ a)
    (hε : 0 < ε) :
    (isIntegralLattice_intCast n).dualMeasure
        (facetPolyhedron ((Int.castAddHom ℝ).compLeft (Fin n))
          (cornerChopNormal (simplexNormal (Fin n)) (Finset.univ.map .some))
          (cornerChopSupport (simplexSupport a) (Finset.univ.map .some) ε)) =
      ENNReal.ofReal ((a ^ n - ε ^ n) / n.factorial) := by
  -- The normals of the facets at the corner `0` are the coordinate vectors.
  have hu (k : Fin n) :
      (Int.castAddHom ℝ).compLeft (Fin n) (simplexNormal (Fin n) (some k)) = Pi.single k 1 := by
    simp
  rcases lt_or_ge a ε with haε | hεa
  · -- Beyond the depth `a` nothing is left, and `aⁿ - εⁿ ≤ 0`.
    rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.2 (pow_le_pow_left₀ ha haε.le n)) (Nat.cast_nonneg _))]
    refine measure_mono_null (t := ∅) (fun x hx ↦ ?_) measure_empty
    -- The chopped simplex is `{0 ≤ x(eₖ), ε ≤ ∑ k, x(eₖ) ≤ a}`.
    simp only [mem_facetPolyhedron_cornerChop_iff, mem_facetPolyhedron_simplex_iff, Finset.sum_map,
      Function.Embedding.some_apply, hu, simplexSupport_some, sub_zero] at hx
    exact absurd (hx.2.trans hx.1.2) (not_le.2 haε)
  let e : Fin n ≃ (Finset.univ.map .some : Finset (Option (Fin n))) :=
    (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (Finset.univ.equivMap .some)
  have hb (j) : (Pi.basisFun ℤ (Fin n)).reindex e j = simplexNormal (Fin n) j := by
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [Basis.reindex_apply, Equiv.symm_apply_apply, Pi.basisFun_apply]
    simp only [e, Equiv.trans_apply, Finset.equivMap_apply_coe, Equiv.subtypeUnivEquiv_symm_apply,
      Function.Embedding.some_apply, simplexNormal_some]
  -- The simplex of size `ε` at the corner lies in the simplex of size `a`.
  have h := (isIntegralLattice_intCast n).dualMeasure_facetPolyhedron_cornerChop_add
    (c := simplexSupport a) _ hb hε fun x hxs hxε ↦ by
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.some_apply,
        forall_exists_index, forall_apply_eq_imp_iff, hu, simplexSupport_some] at hxs
      simp only [Finset.sum_map, Function.Embedding.some_apply, hu, simplexSupport_some,
        sub_zero] at hxε
      exact mem_facetPolyhedron_simplex_iff.2 ⟨hxs, hxε.trans hεa⟩
  rw [dualMeasure_facetPolyhedron_simplex n ha, finrank_fin_fun] at h
  rw [ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top h, sub_div,
    ENNReal.ofReal_sub _ (by positivity)]

end TauCeti.Toric
