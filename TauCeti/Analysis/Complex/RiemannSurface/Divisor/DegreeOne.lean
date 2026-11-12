/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.FiniteDimensional
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Torus
import TauCeti.Algebra.Module.ZLattice.Quotient
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap

/-!
# Sections of a point divisor

Let `X` be a compact connected Riemann surface and `x` a point of `X`. The constants are global
sections of `𝒪(x)`, so `h⁰(𝒪(x)) ≥ 1`. A second, independent section would be a meromorphic
function with at most a simple pole at `x` and no other poles, that is, a finite holomorphic map
`X → ℙ¹` of degree one. Such a map is unramified, so by Riemann–Hurwitz every canonical divisor
of `X` has degree `-2`. Hence `h⁰(𝒪(x)) = 1` whenever some canonical divisor has degree
different from `-2`, for instance on a complex torus, where the zero divisor is canonical.

The pole count rests on a general bound: a finite holomorphic map `F : X → ℙ¹` whose affine part
has order at least `-D` everywhere, for an effective divisor `D`, has degree at most `deg D`,
since the fibre of `∞` counted with multiplicity is bounded by `D`.

## Main declarations

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.meromorphicOrderAt_affineChart_comp_of_eq_infty`:
  at a pole the order of the affine part of `F` is minus the local multiplicity.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.degree_le_degree_of_neg_le_meromorphicOrderAt`:
  the degree of `F` is at most the degree of an effective divisor bounding its poles.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_eq_zero_of_degree_eq_one`:
  a map of degree one is unramified.
* `TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_of_degree_eq_one`: a degree-one
  map to `ℙ¹` forces `deg K = -2`.
* `TauCeti.RiemannSurface.finrank_divisorSections_ofPoint_eq_one`: `h⁰(𝒪(x)) = 1` when
  `deg K ≠ -2`.
* `TauCeti.RiemannSurface.finrank_divisorSections_ofPoint_torus`: `h⁰(𝒪(x)) = 1` on a complex
  torus.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-17.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V §3.
-/

public noncomputable section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

namespace FiniteHolomorphicMap

/-- **Order at a pole.** At a point `x` with `F x = ∞`, the affine part of a finite holomorphic
map `F : X → ℙ¹` has order `-m`, where `m` is the local multiplicity of `F` at `x`. -/
theorem meromorphicOrderAt_affineChart_comp_of_eq_infty [PreconnectedSpace X]
    (F : FiniteHolomorphicMap X (OnePoint ℂ)) {x : X} (hx : F x = ∞) :
    meromorphicOrderAt (fun y ↦ affineChart (F y)) x =
      ((-(localMultiplicity F x : ℤ) : ℤ) : WithTop ℤ) := by
  have h := MeromorphicFunction.meromorphicOrderAt_finitePart_comap F F.holomorphic
    F.nonconstant MeromorphicFunction.coordinate x
  have h0 : meromorphicOrderAt (affineChart : OnePoint ℂ → ℂ) ∞ = -1 := by
    rw [← MeromorphicFunction.finitePart_coordinate, ← MeromorphicFunction.order_apply,
      MeromorphicFunction.order_coordinate_infty]
  rw [MeromorphicFunction.finitePart_comap, MeromorphicFunction.finitePart_coordinate, hx, h0] at h
  rw [show (fun y ↦ affineChart (F y)) = (affineChart : OnePoint ℂ → ℂ) ∘ F from rfl, h]
  rw [← neg_one_mul (localMultiplicity F x : ℤ)]
  rfl

variable [CompactSpace X] [T2Space X] [PreconnectedSpace X]

omit [CompactSpace X] [T2Space X] in
/-- **Poles bounded by an effective divisor.** If the affine part of a finite holomorphic map
`F : X → ℙ¹` has order at least `-D` everywhere, then the fibre of `∞`, counted with
multiplicity, is bounded by `D`. -/
theorem divisorPullback_ofPoint_infty_le_of_neg_le_meromorphicOrderAt
    {D : WeilDivisor X} (hD : 0 ≤ D) (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (hF : ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun y ↦ affineChart (F y)) x) :
    divisorPullback F (WeilDivisor.ofPoint ∞) ≤ D := by
  intro x
  change WeilDivisor.coeff (divisorPullback F (WeilDivisor.ofPoint ∞)) x ≤ D x
  rw [coeff_divisorPullback]
  by_cases hx : F x = ∞
  · have h := hF x
    rw [meromorphicOrderAt_affineChart_comp_of_eq_infty F hx] at h
    rw [hx, WeilDivisor.coeff_ofPoint_self, mul_one]
    have h' : -D x ≤ -(localMultiplicity F x : ℤ) := by exact_mod_cast h
    omega
  · rw [WeilDivisor.coeff_ofPoint_of_ne hx, mul_zero]
    exact WeilDivisor.coeff_nonneg hD x

/-- **Degree bound from a pole divisor.** If the affine part of a finite holomorphic map
`F : X → ℙ¹` has order at least `-D` everywhere, for an effective divisor `D`, then
`deg F ≤ deg D`. -/
theorem degree_le_degree_of_neg_le_meromorphicOrderAt
    {D : WeilDivisor X} (hD : 0 ≤ D) (F : FiniteHolomorphicMap X (OnePoint ℂ))
    (hF : ∀ x, ((-D x : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun y ↦ affineChart (F y)) x) :
    (degree F : ℤ) ≤ WeilDivisor.degree D := by
  have hle := divisorPullback_ofPoint_infty_le_of_neg_le_meromorphicOrderAt hD F hF
  have h := WeilDivisor.degree_nonneg (sub_nonneg.mpr hle)
  rw [WeilDivisor.degree_sub, degree_divisorPullback_ofPoint] at h
  omega

end FiniteHolomorphicMap

section Compact

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y]

/-- **A degree-one map is unramified**: all its local multiplicities are `1`. -/
theorem FiniteHolomorphicMap.ramificationDegree_eq_zero_of_degree_eq_one
    (f : FiniteHolomorphicMap X Y) (hf : degree f = 1) : ramificationDegree f = 0 := by
  rw [ramificationDegree_def]
  refine finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_
  have := localMultiplicity_le_degree f x
  omega

variable [ConnectedSpace X]

/-- **Only the sphere admits a degree-one map to the sphere**, in the canonical-divisor form: if
a compact connected Riemann surface has a finite holomorphic map to `ℙ¹` of degree one, then
every canonical divisor has degree `-2`. -/
theorem IsCanonicalDivisor.degree_eq_neg_two_of_degree_eq_one {K : WeilDivisor X}
    (hK : IsCanonicalDivisor K) (F : FiniteHolomorphicMap X (OnePoint ℂ)) (hF : degree F = 1) :
    WeilDivisor.degree K = -2 := by
  rw [hK.degree_eq_neg_two_mul_degree_add_ramificationDegree F, hF,
    F.ramificationDegree_eq_zero_of_degree_eq_one hF]
  norm_num

end Compact

variable [CompactSpace X] [T2Space X] [ConnectedSpace X]

omit [T2Space X] in
/-- An effective divisor has the constants among its global sections, so `h⁰(𝒪(D)) ≥ 1`. -/
theorem one_le_finrank_divisorSections_of_nonneg {D : WeilDivisor X} (hD : 0 ≤ D) :
    1 ≤ Module.finrank ℂ (divisorSections D ⊤) := by
  obtain ⟨s, hs⟩ := (divisorSections.mem_range_toMeromorphic_iff (D := D) 1).mpr fun x ↦ by
    rw [AddValuation.map_one]
    exact_mod_cast neg_nonpos.mpr (WeilDivisor.coeff_nonneg hD x)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [map_zero] at hs
    exact zero_ne_one hs
  exact Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s, hs0⟩).ne'

/-- **A second section of `𝒪(x)` gives a degree-one map to `ℙ¹`.** If `h⁰(𝒪(x)) > 1`, there is a
finite holomorphic map `X → ℙ¹` of degree one; it has a simple pole at `x` and no other pole. -/
theorem exists_finiteHolomorphicMap_degree_eq_one_of_one_lt_finrank_divisorSections_ofPoint
    {x : X} (hx : 1 < Module.finrank ℂ (divisorSections (WeilDivisor.ofPoint x) ⊤)) :
    ∃ F : FiniteHolomorphicMap X (OnePoint ℂ), degree F = 1 := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_of_one_lt_finrank_divisorSections _ hx
  refine ⟨F, ?_⟩
  have hle := F.degree_le_degree_of_neg_le_meromorphicOrderAt (WeilDivisor.ofPoint_nonneg x) hF
  rw [WeilDivisor.degree_ofPoint] at hle
  have := degree_pos F
  omega

/-- **`h⁰(𝒪(x)) = 1` off genus zero.** On a compact connected Riemann surface with a canonical
divisor of degree different from `-2`, the divisor of a single point has exactly the constants as
global sections. -/
theorem finrank_divisorSections_ofPoint_eq_one {K : WeilDivisor X} (hK : IsCanonicalDivisor K)
    (hdeg : WeilDivisor.degree K ≠ -2) (x : X) :
    Module.finrank ℂ (divisorSections (WeilDivisor.ofPoint x) ⊤) = 1 := by
  refine le_antisymm (not_lt.mp fun hx ↦ ?_)
    (one_le_finrank_divisorSections_of_nonneg (WeilDivisor.ofPoint_nonneg x))
  obtain ⟨F, hF⟩ :=
    exists_finiteHolomorphicMap_degree_eq_one_of_one_lt_finrank_divisorSections_ofPoint hx
  exact hdeg (hK.degree_eq_neg_two_of_degree_eq_one F hF)

/-- **`h⁰(𝒪(x)) = 1` on a complex torus**, the `h⁰` half of the genus-one check that a degree-one
line bundle has `(h⁰, h¹) = (1, 0)`. -/
theorem finrank_divisorSections_ofPoint_torus (L : Submodule ℤ ℂ) [DiscreteTopology L]
    [IsZLattice ℝ L] (x : AddAction.orbitRel.Quotient L ℂ) :
    Module.finrank ℂ (divisorSections (WeilDivisor.ofPoint x) ⊤) = 1 :=
  finrank_divisorSections_ofPoint_eq_one (isCanonicalDivisor_zero_torus (L := L))
    (by rw [WeilDivisor.degree_zero]; decide) x

end TauCeti.RiemannSurface
