/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Measure
public import TauCeti.Geometry.Toric.Delzant.Equiv
public import TauCeti.Geometry.Toric.Delzant.Hirzebruch
public import TauCeti.Geometry.Toric.Delzant.Interval
public import TauCeti.Geometry.Toric.Delzant.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.RegionBetween

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
`k = 0` this is the rectangle `[0, a] × [0, b]` of `S² × S²`, of area `a b`.

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

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28–30.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 2.
-/

public section

open MeasureTheory Module Set
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
  rw [hpre, (isIntegralLattice_castAddHom.measurePreserving_dualBasis_equivFun b).measure_preimage
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).nullMeasurableSet, volume_pi_pi]
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
  have he (x : StrongDual ℝ (Fin 2 → ℝ)) (j : Fin 2) : e.equivFun x j = x (Pi.single j 1) := by
    simp only [e, IsIntegralLattice.dualBasis_equivFun, Pi.basisFun_apply]
    congr 1
    ext l
    simp [Pi.single_apply, apply_ite]
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
      MeasurableEquiv.finTwoArrow_apply, he, Prod.fst_swap, Prod.snd_swap,
      mem_closedRegionBetween, Pi.zero_apply, mem_Icc]
    constructor
    · rintro ⟨h₀, h₁, h₂, h₃⟩
      exact ⟨⟨h₁, h₂⟩, h₀, by linarith⟩
    · rintro ⟨⟨h₁, h₂⟩, h₀, h₃⟩
      exact ⟨h₀, h₁, h₂, by linarith⟩
  rw [hpre, hmp.measure_preimage (measurableSet_closedRegionBetween measurable_zero (by fun_prop)
    measurableSet_Icc).nullMeasurableSet, volume_closedRegionBetween_zero_sub_mul ha hkb]

end TauCeti.Toric
