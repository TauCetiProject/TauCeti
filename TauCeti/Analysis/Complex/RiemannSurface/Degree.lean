/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem
import TauCeti.Analysis.Complex.RiemannSurface.OpenMapping
public import TauCeti.Analysis.Complex.RiemannSurface.LocalDegree
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The degree of a holomorphic map between compact Riemann surfaces

Let `f : X → Y` be a holomorphic map between Riemann surfaces which is constant near no point of
`X`. Its **fibre sum** at `y : Y` is the number of preimages of `y` counted with local
multiplicities, `TauCeti.RiemannSurface.fiberMultiplicitySum f y = ∑ᶠ x ∈ f ⁻¹' {y},
localMultiplicity f x`. When `X` is compact every fibre is finite, and the fibre sum is a locally
constant function of `y`: the local fibre count `exists_nhds_localMultiplicity_fiber_sum` gives,
at each of the finitely many points of a fibre, a neighbourhood on which nearby fibres carry
exactly the multiplicity of that point, while compactness of the complement of these
neighbourhoods keeps nearby fibres from having any further points. Over a connected `Y` the fibre
sum is therefore the same at every point, and this common value is the **degree**
`TauCeti.RiemannSurface.degree f`. The degree dominates every local multiplicity and is
multiplicative under composition; when `X` is nonempty (so that some fibre sum is nonzero) it is
positive and forces `f` to be surjective. Nonconstancy of the composite of two such maps comes
from the open mapping theorem for Riemann surfaces,
`TauCeti.RiemannSurface.not_eventuallyConst_comp` in
`TauCeti.Analysis.Complex.RiemannSurface.OpenMapping`.

Nonconstancy is spelled pointwise, as `∀ x, ¬ EventuallyConst f (𝓝 x)`, exactly as in the local
fibre count: this is the hypothesis the arguments use. The degree is defined for every map
`f : X → Y` as the supremum of its fibre sums, so that no point of `Y` needs to be chosen; for a
map with constant fibre sums this is that constant, and for other maps the value is junk.

The bundled carrier `TauCeti.RiemannSurface.FiniteHolomorphicMap X Y` collects a holomorphic map
which takes two distinct values and has finite fibres. On a connected `X` the identity theorem
(`TauCeti.RiemannSurface.not_eventuallyConst_of_ne` in
`TauCeti.Analysis.Complex.RiemannSurface.IdentityTheorem`) turns the two distinct values into
pointwise nonconstancy, so the results above apply to a finite holomorphic map with no side
hypotheses, and between compact connected Riemann surfaces every nonconstant holomorphic map is a
finite holomorphic map.

## Main declarations

* `TauCeti.RiemannSurface.finite_preimage_singleton`: fibre finiteness over a compact source.
* `TauCeti.RiemannSurface.fiberMultiplicitySum`: the fibre sum of local multiplicities, and
  `TauCeti.RiemannSurface.eventually_fiberMultiplicitySum_eq`, its local constancy.
* `TauCeti.RiemannSurface.degree`: the degree, with
  `TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree` saying that every fibre sum over a
  connected target equals it, `TauCeti.RiemannSurface.degree_pos_of_forall_not_eventuallyConst`,
  `TauCeti.RiemannSurface.surjective_of_forall_not_eventuallyConst` and
  `TauCeti.RiemannSurface.degree_comp_of_forall_not_eventuallyConst`, for maps carrying the
  pointwise nonconstancy hypothesis.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap`: the bundled finite holomorphic maps, with
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.ofMDifferentiable` and
  `TauCeti.RiemannSurface.FiniteHolomorphicMap.comp`, and the degree API on them with no side
  hypotheses: `TauCeti.RiemannSurface.localMultiplicity_pos`,
  `TauCeti.RiemannSurface.degree_eq_fiber_sum`, `TauCeti.RiemannSurface.degree_pos`,
  `TauCeti.RiemannSurface.localMultiplicity_comp`, `TauCeti.RiemannSurface.degree_comp` and
  `TauCeti.RiemannSurface.biholomorphOfDegreeEqOne`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §4, Theorem 4.24.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4, Proposition 4.8.
-/

public noncomputable section

open Filter Function Set Topology

open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] {f : X → Y} {g : Y → Z}

/-! ### The fibre sum -/

/-- The number of preimages of `y` under `f`, counted with local multiplicities: the sum of
`TauCeti.RiemannSurface.localMultiplicity f x` over the fibre `f ⁻¹' {y}`. Over a finite fibre it
is a finite sum (`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_sum`); by the convention for
`finsum`, it is `0` when infinitely many points of the fibre have nonzero local multiplicity.

For a holomorphic `f` on a compact Riemann surface which is constant near no point, this is a
locally constant function of `y` (`TauCeti.RiemannSurface.eventually_fiberMultiplicitySum_eq`), and
over a connected target it is the degree of `f`
(`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`). -/
def fiberMultiplicitySum (f : X → Y) (y : Y) : ℕ := ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity f x

theorem fiberMultiplicitySum_def (f : X → Y) (y : Y) :
    fiberMultiplicitySum f y = ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity f x :=
  (rfl)

/-- Over a finite fibre, the fibre sum is a finite sum. -/
theorem fiberMultiplicitySum_eq_sum {y : Y} (hy : (f ⁻¹' {y}).Finite) :
    fiberMultiplicitySum f y = ∑ x ∈ hy.toFinset, localMultiplicity f x :=
  finsum_mem_eq_finite_toFinset_sum _ hy

/-- Each local multiplicity at a point of a finite fibre is at most the fibre sum. -/
theorem localMultiplicity_le_fiberMultiplicitySum {x : X} {y : Y} (hy : (f ⁻¹' {y}).Finite)
    (hx : f x = y) : localMultiplicity f x ≤ fiberMultiplicitySum f y := by
  rw [fiberMultiplicitySum_eq_sum hy]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (hy.mem_toFinset.2 hx)

/-- The **degree** of a map `f : X → Y` between Riemann surfaces: the supremum of its fibre sums
`TauCeti.RiemannSurface.fiberMultiplicitySum f y`. For `f` holomorphic and constant near no point
of a compact `X`, with `Y` connected, every fibre sum equals the degree
(`TauCeti.RiemannSurface.fiberMultiplicitySum_eq_degree`): the degree is the number of preimages
of any point, counted with local multiplicities. The supremum only avoids choosing a point of
`Y`; for maps whose fibre sums are not constant the value is junk. -/
def degree (f : X → Y) : ℕ := ⨆ y, fiberMultiplicitySum f y

theorem degree_def (f : X → Y) : degree f = ⨆ y, fiberMultiplicitySum f y :=
  (rfl)

/-! ### Finite holomorphic maps -/

/-- A **finite holomorphic map** between Riemann surfaces: a holomorphic map which takes two
distinct values and has finite fibres. On a connected source it is constant near no point by the
identity theorem (`TauCeti.RiemannSurface.FiniteHolomorphicMap.not_eventuallyConst`), so the
degree theory of this file applies to it with no side hypotheses; between compact connected Riemann
surfaces every nonconstant holomorphic map is finite
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.ofMDifferentiable`). -/
structure FiniteHolomorphicMap (X Y : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] where
  /-- The underlying map. -/
  toFun : X → Y
  /-- The map is holomorphic. -/
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) toFun
  /-- The map takes two distinct values. -/
  nonconstant : ∃ x x', toFun x ≠ toFun x'
  /-- Every fibre of the map is finite. -/
  finite_fiber : ∀ y, (toFun ⁻¹' {y}).Finite

namespace FiniteHolomorphicMap

attribute [coe] toFun

instance : CoeFun (FiniteHolomorphicMap X Y) fun _ ↦ X → Y := ⟨toFun⟩

@[ext]
theorem ext {f g : FiniteHolomorphicMap X Y} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

end FiniteHolomorphicMap

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-! ### Fibre finiteness -/

/-- **Finiteness of fibres.** A holomorphic map from a compact Riemann surface which is constant
near no point has finite fibres: each fibre is compact, and each of its points has a neighbourhood
containing no other point of the fibre. -/
theorem finite_preimage_singleton [CompactSpace X] [T1Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) (y : Y) :
    (f ⁻¹' {y}).Finite := by
  refine (isClosed_singleton.preimage hf.continuous).isCompact.finite
    (isDiscrete_iff_forall_mem_exists_isOpen.2 fun x hx ↦ ?_)
  obtain ⟨U, hU, -, V, -, hUx, -⟩ :=
    exists_nhds_localMultiplicity_fiber_sum (.of_forall fun z ↦ hf z) (hne x) univ_mem
  have hfx : f x = y := hx
  rw [hfx] at hUx
  refine ⟨interior U, isOpen_interior, subset_antisymm (fun x' hx' ↦ ?_)
    (singleton_subset_iff.2 ⟨mem_interior_iff_mem_nhds.2 hU, hx⟩)⟩
  rw [← hUx]
  exact ⟨hx'.2, interior_subset hx'.1⟩

/-! ### Local constancy of the fibre sum -/

/-- **Local constancy of the fibre sum.** For a holomorphic map from a compact Riemann surface
which is constant near no point, the fibre sum of local multiplicities is the same at every point
near `y` as at `y`. -/
theorem eventually_fiberMultiplicitySum_eq [CompactSpace X] [T2Space X] [T2Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) (y : Y) :
    ∀ᶠ y' in 𝓝 y, fiberMultiplicitySum f y' = fiberMultiplicitySum f y := by
  have hS : (f ⁻¹' {y}).Finite := finite_preimage_singleton hf hne y
  -- Pairwise disjoint open neighbourhoods of the finitely many points of the fibre of `y`.
  obtain ⟨O, hO, hOdisj⟩ := hS.t2_separation
  -- The local fibre count at each point of the fibre, inside those neighbourhoods.
  have hloc : ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, U ⊆ O x ∧ ∃ V ∈ 𝓝 y, ∀ y' ∈ V,
      (f ⁻¹' {y'} ∩ U).Finite ∧
      (∑ᶠ x' ∈ f ⁻¹' {y'} ∩ U, localMultiplicity f x') = localMultiplicity f x := by
    intro x hx
    have hfx : f x = y := hx
    obtain ⟨U, hU, hUO, V, hV, -, hcount⟩ := exists_nhds_localMultiplicity_fiber_sum
      (.of_forall fun z ↦ hf z) (hne x) ((hO x).2.mem_nhds (hO x).1)
    exact ⟨U, hU, hUO, V, hfx ▸ hV, fun y' hy' ↦ ⟨(hcount y' hy').2.1, (hcount y' hy').2.2⟩⟩
  choose! U hU hUO V hV hcount using hloc
  -- Outside the interiors of the `U x` the map misses `y`, hence a whole neighbourhood of `y`.
  have hK : IsCompact (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ :=
    (isOpen_biUnion fun x _ ↦ isOpen_interior).isClosed_compl.isCompact
  have hyK : y ∉ f '' (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ := by
    rintro ⟨x, hxK, hfx⟩
    exact hxK (mem_iUnion₂.2 ⟨x, hfx, mem_interior_iff_mem_nhds.2 (hU x hfx)⟩)
  have hV₀ : (f '' (⋃ x ∈ f ⁻¹' {y}, interior (U x))ᶜ)ᶜ ∈ 𝓝 y :=
    (hK.image hf.continuous).isClosed.isOpen_compl.mem_nhds hyK
  filter_upwards [hV₀, (biInter_mem hS).2 hV] with y' hy'₀ hy'V
  have hy'V' : ∀ x ∈ f ⁻¹' {y}, y' ∈ V x := mem_iInter₂.1 hy'V
  -- The fibre of `y'` is the disjoint union of its pieces inside the `U x`.
  have hfib : f ⁻¹' {y'} = ⋃ x ∈ f ⁻¹' {y}, (f ⁻¹' {y'} ∩ U x) := by
    ext x'
    refine ⟨fun hx' ↦ ?_, fun hx' ↦ ?_⟩
    · have hx'U : x' ∈ ⋃ x ∈ f ⁻¹' {y}, interior (U x) := by
        by_contra h
        exact hy'₀ ⟨x', h, hx'⟩
      obtain ⟨x, hx, hx'U⟩ := mem_iUnion₂.1 hx'U
      exact mem_iUnion₂.2 ⟨x, hx, hx', interior_subset hx'U⟩
    · obtain ⟨x, -, hx'⟩ := mem_iUnion₂.1 hx'
      exact hx'.1
  have hdisj : (f ⁻¹' {y}).PairwiseDisjoint fun x ↦ f ⁻¹' {y'} ∩ U x :=
    hOdisj.mono_on fun x hx ↦ inter_subset_right.trans (hUO x hx)
  simp only [fiberMultiplicitySum_def]
  rw [hfib, finsum_mem_biUnion hdisj hS fun x hx ↦ (hcount x hx y' (hy'V' x hx)).1]
  exact finsum_mem_congr rfl fun x hx ↦ (hcount x hx y' (hy'V' x hx)).2

/-- For a holomorphic map from a compact Riemann surface which is constant near no point, the
fibre sum of local multiplicities is a locally constant function on the target. -/
theorem isLocallyConstant_fiberMultiplicitySum [CompactSpace X] [T2Space X] [T2Space Y]
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) :
    IsLocallyConstant (fiberMultiplicitySum f) :=
  (IsLocallyConstant.iff_eventually_eq _).2 (eventually_fiberMultiplicitySum_eq hf hne)

/-! ### The degree -/

section Degree

variable [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∀ x, ¬ EventuallyConst f (𝓝 x))
include hf hne

/-- **Fibre independence of the degree.** For a holomorphic map from a compact Riemann surface to
a connected Riemann surface which is constant near no point, the number of preimages of any point
counted with local multiplicities is the degree. -/
theorem fiberMultiplicitySum_eq_degree (y : Y) : fiberMultiplicitySum f y = degree f := by
  have : Nonempty Y := ⟨y⟩
  have h : fiberMultiplicitySum f = fun _ ↦ fiberMultiplicitySum f y :=
    funext fun y' ↦ (isLocallyConstant_fiberMultiplicitySum hf hne).apply_eq_of_preconnectedSpace
      y' y
  rw [degree_def, h, ciSup_const]

/-- Every local multiplicity of a holomorphic map from a compact Riemann surface to a connected
Riemann surface which is constant near no point is at most the degree. -/
theorem localMultiplicity_le_degree_of_forall_not_eventuallyConst (x : X) :
    localMultiplicity f x ≤ degree f :=
  (localMultiplicity_le_fiberMultiplicitySum (finite_preimage_singleton hf hne (f x)) rfl).trans
    (fiberMultiplicitySum_eq_degree hf hne (f x)).le

/-- **Positivity of the degree.** A holomorphic map from a nonempty compact Riemann surface to a
connected Riemann surface which is constant near no point has positive degree. -/
theorem degree_pos_of_forall_not_eventuallyConst [Nonempty X] : 0 < degree f :=
  ((localMultiplicity_pos_iff (.of_forall fun z ↦ hf z)).2 (hne (Classical.arbitrary X))).trans_le
    (localMultiplicity_le_degree_of_forall_not_eventuallyConst hf hne _)

/-- **Surjectivity.** A holomorphic map from a nonempty compact Riemann surface to a connected
Riemann surface which is constant near no point is surjective: its positive degree is the fibre
sum over every point, so no fibre is empty. -/
theorem surjective_of_forall_not_eventuallyConst [Nonempty X] : Surjective f := fun y ↦ by
  by_contra h
  have hemp : f ⁻¹' {y} = ∅ := eq_empty_iff_forall_notMem.2 fun x hx ↦ h ⟨x, hx⟩
  have h0 : fiberMultiplicitySum f y = 0 := by
    rw [fiberMultiplicitySum_def, hemp, finsum_mem_empty]
  exact (degree_pos_of_forall_not_eventuallyConst hf hne).ne'
    ((fiberMultiplicitySum_eq_degree hf hne y).symm.trans h0)

end Degree

/-! ### Composition -/

variable [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- **Multiplicativity of the degree.** For holomorphic maps `f : X → Y` and `g : Y → Z` of
compact Riemann surfaces with connected targets, both constant near no point, the degree of
`g ∘ f` is the product of the degrees: the fibre of `g ∘ f` over `z` is the disjoint union of the
fibres of `f` over the points of the fibre of `g` over `z`, and the local multiplicities
multiply. -/
theorem degree_comp_of_forall_not_eventuallyConst [IsManifold 𝓘(ℂ) 1 Z] [CompactSpace X]
    [T2Space X] [CompactSpace Y] [T2Space Y] [PreconnectedSpace Y] [T2Space Z]
    [PreconnectedSpace Z] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hne : ∀ x, ¬ EventuallyConst f (𝓝 x)) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hneg : ∀ y, ¬ EventuallyConst g (𝓝 y)) : degree (g ∘ f) = degree g * degree f := by
  classical
  rcases isEmpty_or_nonempty Z with hZ | ⟨⟨z⟩⟩
  · simp [degree_def]
  have hgf : ∀ x, ¬ EventuallyConst (g ∘ f) (𝓝 x) := fun x ↦
    not_eventuallyConst_comp (.of_forall fun w ↦ hf w) (hne x) (hneg (f x))
  have hT : (g ⁻¹' {z}).Finite := finite_preimage_singleton hg hneg z
  -- The fibre of `g ∘ f` over `z` is the disjoint union of the fibres of `f` over `g ⁻¹' {z}`.
  have hfib : (g ∘ f) ⁻¹' {z} = ⋃ y ∈ g ⁻¹' {z}, f ⁻¹' {y} := by
    ext x
    simp
  have hdisj : (g ⁻¹' {z}).PairwiseDisjoint fun y ↦ f ⁻¹' {y} := fun y _ y' _ hyy' ↦
    disjoint_left.2 fun x hx hx' ↦ hyy' ((mem_singleton_iff.1 hx).symm.trans hx')
  -- Over each point `y` of the fibre of `g`, the fibre of `f` contributes `e_g(y) * deg f`.
  have hpiece : ∀ y ∈ g ⁻¹' {z},
      ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity (g ∘ f) x = localMultiplicity g y * degree f := by
    intro y _
    have hS : (f ⁻¹' {y}).Finite := finite_preimage_singleton hf hne y
    calc ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity (g ∘ f) x
        = ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity g y * localMultiplicity f x :=
          finsum_mem_congr rfl fun x hx ↦ by
            rw [localMultiplicity_comp_of_eventually_mdifferentiableAt (.of_forall fun w ↦ hg w)
              (.of_forall fun w ↦ hf w), mem_singleton_iff.1 (mem_preimage.1 hx)]
      _ = localMultiplicity g y * fiberMultiplicitySum f y := by
          rw [fiberMultiplicitySum_eq_sum hS, finsum_mem_eq_finite_toFinset_sum _ hS,
            Finset.mul_sum]
      _ = localMultiplicity g y * degree f := by rw [fiberMultiplicitySum_eq_degree hf hne y]
  calc degree (g ∘ f)
      = fiberMultiplicitySum (g ∘ f) z := (fiberMultiplicitySum_eq_degree (hg.comp hf) hgf z).symm
    _ = ∑ᶠ y ∈ g ⁻¹' {z}, ∑ᶠ x ∈ f ⁻¹' {y}, localMultiplicity (g ∘ f) x := by
        rw [fiberMultiplicitySum_def, hfib,
          finsum_mem_biUnion hdisj hT fun y _ ↦ finite_preimage_singleton hf hne y]
    _ = ∑ᶠ y ∈ g ⁻¹' {z}, localMultiplicity g y * degree f := finsum_mem_congr rfl hpiece
    _ = fiberMultiplicitySum g z * degree f := by
        rw [fiberMultiplicitySum_eq_sum hT, finsum_mem_eq_finite_toFinset_sum _ hT, Finset.sum_mul]
    _ = degree g * degree f := by rw [fiberMultiplicitySum_eq_degree hg hneg z]

/-! ### The degree of a finite holomorphic map

The results above, restated on `TauCeti.RiemannSurface.FiniteHolomorphicMap` with no side
hypotheses: on a connected source the identity theorem supplies the pointwise nonconstancy. The
statements about `degree` and `localMultiplicity` keep the names of the theorems they restate and
live in the namespace of that head symbol; the theorems whose head symbol is generic
(`Function.Surjective`, `Filter.EventuallyConst`, the composite) live in the carrier's namespace. -/

section FiniteHolomorphicMap

variable (f : FiniteHolomorphicMap X Y)

/-- A finite holomorphic map from a connected Riemann surface is constant near no point: this is
the identity theorem. -/
theorem FiniteHolomorphicMap.not_eventuallyConst [PreconnectedSpace X] (x : X) :
    ¬ EventuallyConst f (𝓝 x) :=
  let ⟨_, _, h⟩ := f.nonconstant
  not_eventuallyConst_of_ne f.holomorphic h x

/-- The local multiplicity of a finite holomorphic map from a connected Riemann surface is positive
at every point. -/
theorem localMultiplicity_pos [PreconnectedSpace X] (x : X) : 0 < localMultiplicity f x :=
  (localMultiplicity_pos_iff (.of_forall fun z ↦ f.holomorphic z)).2 (f.not_eventuallyConst x)

/-- A holomorphic map from a compact connected Riemann surface which takes two distinct values is
a finite holomorphic map: its fibres are finite by
`TauCeti.RiemannSurface.finite_preimage_singleton`. -/
def FiniteHolomorphicMap.ofMDifferentiable [CompactSpace X] [PreconnectedSpace X] [T1Space Y]
    {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∃ x x', f x ≠ f x') :
    FiniteHolomorphicMap X Y where
  toFun := f
  holomorphic := hf
  nonconstant := hne
  finite_fiber :=
    let ⟨_, _, h⟩ := hne
    finite_preimage_singleton hf (not_eventuallyConst_of_ne hf h)

@[simp]
theorem FiniteHolomorphicMap.coe_ofMDifferentiable [CompactSpace X] [PreconnectedSpace X]
    [T1Space Y] {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hne : ∃ x x', f x ≠ f x') :
    ⇑(FiniteHolomorphicMap.ofMDifferentiable hf hne) = f :=
  (rfl)

section Compact

variable [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y] [PreconnectedSpace Y]

/-- A finite holomorphic map from a compact connected Riemann surface to a connected Riemann
surface is surjective. -/
theorem FiniteHolomorphicMap.surjective : Surjective f :=
  have : Nonempty X := f.nonconstant.nonempty
  surjective_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst

/-- **Fibre independence of the degree**, for a finite holomorphic map from a compact connected
Riemann surface to a connected Riemann surface: the degree is the sum of the local multiplicities
over any fibre. -/
theorem degree_eq_fiber_sum (y : Y) :
    degree f = ∑ x ∈ (f.finite_fiber y).toFinset, localMultiplicity f x :=
  (fiberMultiplicitySum_eq_degree f.holomorphic f.not_eventuallyConst y).symm.trans
    (fiberMultiplicitySum_eq_sum _)

/-- Every local multiplicity of a finite holomorphic map from a compact connected Riemann surface
to a connected Riemann surface is at most its degree. -/
theorem localMultiplicity_le_degree (x : X) : localMultiplicity f x ≤ degree f :=
  localMultiplicity_le_degree_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst x

/-- **Positivity of the degree** of a finite holomorphic map from a compact connected Riemann
surface to a connected Riemann surface. -/
theorem degree_pos : 0 < degree f :=
  have : Nonempty X := f.nonconstant.nonempty
  degree_pos_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst

/-- The composite of finite holomorphic maps, for a compact connected source and a connected
middle surface: the composite takes two distinct values because the first map is surjective, and
its fibres are finite unions of finite fibres. -/
def FiniteHolomorphicMap.comp (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) :
    FiniteHolomorphicMap X Z where
  toFun := g ∘ f
  holomorphic := g.holomorphic.comp f.holomorphic
  nonconstant := by
    obtain ⟨y, y', h⟩ := g.nonconstant
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨x', rfl⟩ := f.surjective y'
    exact ⟨x, x', h⟩
  finite_fiber z := by
    rw [preimage_comp, ← biUnion_preimage_singleton]
    exact (g.finite_fiber z).biUnion fun y _ ↦ f.finite_fiber y

@[simp]
theorem FiniteHolomorphicMap.coe_comp (g : FiniteHolomorphicMap Y Z)
    (f : FiniteHolomorphicMap X Y) : ⇑(g.comp f) = g ∘ f :=
  (rfl)

/-- **Multiplicativity of the local multiplicity** for finite holomorphic maps: the local
multiplicity of `g.comp f` at `x` is the product of that of `g` at `f x` and that of `f` at `x`.
The statement for maps, with holomorphy near the two points as hypotheses, is
`TauCeti.RiemannSurface.localMultiplicity_comp_of_eventually_mdifferentiableAt`. -/
theorem localMultiplicity_comp [IsManifold 𝓘(ℂ) 1 Z]
    (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) (x : X) :
    localMultiplicity (g.comp f) x = localMultiplicity g (f x) * localMultiplicity f x :=
  localMultiplicity_comp_of_eventually_mdifferentiableAt (.of_forall fun y ↦ g.holomorphic y)
    (.of_forall fun y ↦ f.holomorphic y)

/-- **Multiplicativity of the degree** for finite holomorphic maps `f : X → Y` and `g : Y → Z`
with `X` and `Y` compact and connected and `Z` connected. -/
theorem degree_comp [IsManifold 𝓘(ℂ) 1 Z] [CompactSpace Y] [T2Space Z] [PreconnectedSpace Z]
    (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) :
    degree (g.comp f) = degree g * degree f :=
  degree_comp_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst g.holomorphic
    g.not_eventuallyConst

/-- A finite holomorphic map of degree one between compact connected Riemann surfaces is a
biholomorphism. -/
noncomputable def biholomorphOfDegreeEqOne (f : FiniteHolomorphicMap X Y) (hf : degree f = 1) :
    X ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ Y := by
  classical
  have hinj : Injective f := by
    intro x x' hfx
    by_contra hxx'
    let s := (f.finite_fiber (f x)).toFinset
    have hxm : x ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff]
    have hx'm : x' ∈ s := by
      simp only [s, Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff, hfx]
    have hsum : ∑ z ∈ s, localMultiplicity f z = 1 := by
      rw [← degree_eq_fiber_sum f (f x), hf]
    have hsplit := s.add_sum_erase (fun z ↦ localMultiplicity f z) hxm
    rw [hsum] at hsplit
    have hxpos := localMultiplicity_pos f x
    have herase : ∑ z ∈ s.erase x, localMultiplicity f z = 0 := by omega
    have hx'erase : x' ∈ s.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxx', hx'm⟩
    have hx'zero : localMultiplicity f x' = 0 :=
      (Finset.sum_eq_zero_iff.mp herase) x' hx'erase
    exact (localMultiplicity_pos f x').ne' hx'zero
  have hhomeo : IsHomeomorph f :=
    ⟨f.holomorphic.continuous,
      isOpenMap_of_forall_not_eventuallyConst f.holomorphic f.not_eventuallyConst,
      hinj, f.surjective⟩
  exact
    { toEquiv := (hhomeo.homeomorph f).toEquiv
      contMDiff_toFun := f.holomorphic.contMDiff
      contMDiff_invFun := (hhomeo.mdifferentiable_symm f.holomorphic).contMDiff }

@[simp]
theorem biholomorphOfDegreeEqOne_toFun (f : FiniteHolomorphicMap X Y) (hf : degree f = 1) :
    ⇑(biholomorphOfDegreeEqOne f hf) = f :=
  (rfl)

end Compact

end FiniteHolomorphicMap

end TauCeti.RiemannSurface

end
