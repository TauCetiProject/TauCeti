/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Holomorphic factorization of germs of maps out of Riemann surfaces

Let `u₀ : X → N` and `u₁ : Y → N` be maps from Riemann surfaces, complex manifolds modelled on
`ℂ`, to a type `N`. The germ of `u₁` at `b` *factors holomorphically through* the germ of `u₀` at
`a` (`TauCeti.RiemannSurface.GermFactorsThrough u₁ b u₀ a`) when there is a map `φ : Y → X`,
holomorphic near `b`, with `φ b = a` and `u₁ = u₀ ∘ φ` near `b`. No condition is imposed on `φ`
away from `b`, and `φ` need not be locally invertible: the germ of `ζ ↦ ζ²` at `0` factors
through the germ of the identity at `0`, but not conversely.

For a single map `u : X → N` the relation `GermFactorsThrough u ζ u z` says that the branches of
`u` at `z` and at `ζ` differ by a holomorphic change of source coordinate. On the points where a
pseudoholomorphic curve `u` is immersed this is the equivalence relation `Γ₀` from which the
factorization of `u` through a simple curve is built (McDuff–Salamon, Proposition 2.5.1); the
properties of `Γ₀` that use the Cauchy–Riemann equation are in
`TauCeti.Geometry.Symplectic.JHolomorphic.RiemannSurface`. This file contains the part that holds
for maps into any type.

## Main declarations

* `TauCeti.RiemannSurface.GermFactorsThrough`: the germ of `u₁` at `b` factors holomorphically
  through the germ of `u₀` at `a`.
* `TauCeti.RiemannSurface.GermFactorsThrough.refl`,
  `TauCeti.RiemannSurface.GermFactorsThrough.trans`: the relation is reflexive and transitive.
* `TauCeti.RiemannSurface.GermFactorsThrough.apply_eq`: related points have the same value.
* `TauCeti.RiemannSurface.GermFactorsThrough.exists_eventually_germFactorsThrough`: a
  factorization `u₁ = u₀ ∘ φ` near `b` relates every point `y` near `b` to `φ y`.
* `TauCeti.RiemannSurface.GermFactorsThrough.eq_of_dense`: if no point of a dense set has its germ
  factoring through the germ of `u` at another point, then no point does.
* `TauCeti.RiemannSurface.exists_apply_ne_of_forall_germFactorsThrough_imp_eq`: a map from a
  nontrivial Riemann surface whose germs factor through no germ at another point is not constant.
* `TauCeti.RiemannSurface.GermFactorsThrough.eventually_mem_image`,
  `TauCeti.RiemannSurface.GermFactorsThrough.frequently_mem_image`: if the germ of `u₁` at `b`
  factors through the germ of `u₀` at `a`, then every point near `b` is mapped by `u₁` into the
  image under `u₀` of any given neighbourhood of `a`; in particular such points accumulate at `b`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Proposition 2.5.1.
-/

public section

open Set Filter Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y Z N : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- The germ of `u₁` at `b` *factors holomorphically through* the germ of `u₀` at `a` when there is
a map `φ`, holomorphic near `b`, with `φ b = a` and `u₁ = u₀ ∘ φ` near `b`. -/
def GermFactorsThrough (u₁ : Y → N) (b : Y) (u₀ : X → N) (a : X) : Prop :=
  ∃ φ : Y → X, φ b = a ∧ (∀ᶠ y in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) ∧ u₁ =ᶠ[𝓝 b] u₀ ∘ φ

variable {u₀ : X → N} {u₁ : Y → N} {u₂ : Z → N} {a : X} {b : Y} {c : Z}

/-- Unfold `TauCeti.RiemannSurface.GermFactorsThrough`. -/
theorem germFactorsThrough_iff :
    GermFactorsThrough u₁ b u₀ a ↔ ∃ φ : Y → X, φ b = a ∧
      (∀ᶠ y in 𝓝 b, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ y) ∧ u₁ =ᶠ[𝓝 b] u₀ ∘ φ :=
  Iff.rfl

/-- If the germ of `u₁` at `b` factors through the germ of `u₀` at `a`, then `u₁ b = u₀ a`. -/
theorem GermFactorsThrough.apply_eq (h : GermFactorsThrough u₁ b u₀ a) : u₁ b = u₀ a := by
  obtain ⟨φ, hφb, -, hφu⟩ := h
  rw [hφu.self_of_nhds, Function.comp_apply, hφb]

/-- Every germ factors through itself, by the identity. -/
theorem GermFactorsThrough.refl (u : X → N) (a : X) : GermFactorsThrough u a u a :=
  ⟨id, rfl, .of_forall fun _ ↦ mdifferentiableAt_id, .rfl⟩

/-- The set `{x | GermFactorsThrough u a u x}` is `{a}` exactly when the germ of `u` at `a` factors
holomorphically through the germ of `u` at no point other than `a`. -/
theorem setOf_germFactorsThrough_eq_singleton_iff {u : X → N} {a : X} :
    {x | GermFactorsThrough u a u x} = {a} ↔ ∀ x, GermFactorsThrough u a u x → x = a :=
  eq_singleton_iff_unique_mem.trans (and_iff_right (.refl u a))

/-- Holomorphic factorizations of germs compose. -/
theorem GermFactorsThrough.trans (h₂₁ : GermFactorsThrough u₂ c u₁ b)
    (h₁₀ : GermFactorsThrough u₁ b u₀ a) : GermFactorsThrough u₂ c u₀ a := by
  obtain ⟨ψ, hψc, hψd, hψu⟩ := h₂₁
  obtain ⟨φ, hφb, hφd, hφu⟩ := h₁₀
  -- `ψ` is continuous at `c` and sends it to `b`, so it pulls back the properties near `b`.
  have ht : Tendsto ψ (𝓝 c) (𝓝 b) := hψc ▸ hψd.self_of_nhds.continuousAt.tendsto
  refine ⟨φ ∘ ψ, by rw [Function.comp_apply, hψc, hφb], ?_, ?_⟩
  · filter_upwards [hψd, ht.eventually hφd] with z hz hφz
    exact hφz.comp z hz
  · filter_upwards [hψu, ht.eventually hφu] with z hz hφz
    rw [hz]
    exact hφz

/-- A holomorphic factorization of germs propagates to nearby points: if the germ of `u₁` at `b`
factors through the germ of `u₀` at `a`, then there is a map `φ`, continuous at `b` with `φ b = a`,
such that for every `y` near `b` the germ of `u₁` at `y` factors through the germ of `u₀` at
`φ y`. -/
theorem GermFactorsThrough.exists_eventually_germFactorsThrough
    (h : GermFactorsThrough u₁ b u₀ a) :
    ∃ φ : Y → X, φ b = a ∧ ContinuousAt φ b ∧ ∀ᶠ y in 𝓝 b, GermFactorsThrough u₁ y u₀ (φ y) := by
  obtain ⟨φ, hφb, hφd, hφu⟩ := h
  refine ⟨φ, hφb, hφd.self_of_nhds.continuousAt, ?_⟩
  filter_upwards [hφd.eventually_nhds, hφu.eventually_nhds] with y hyd hyu
  exact ⟨φ, rfl, hyd, hyu⟩

/-- **Branch degree one on a dense set gives branch degree one everywhere.** Let `u : X → N` be a
map from a Hausdorff Riemann surface, and let `s` be a dense set of points of `X` at each of which
the germ of `u` factors holomorphically through the germ of `u` at no other point. Then the germ of
`u` at any point `z` factors holomorphically through the germ of `u` at no other point. -/
theorem GermFactorsThrough.eq_of_dense [T2Space X] {u : X → N} {s : Set X} (hs : Dense s)
    (hd : ∀ z ∈ s, ∀ ζ, GermFactorsThrough u z u ζ → ζ = z)
    {z ζ : X} (h : GermFactorsThrough u z u ζ) : ζ = z := by
  by_contra hne
  -- A factorization `u = u ∘ φ` near `z` with `φ z = ζ` relates each `w` near `z` to `φ w`.
  obtain ⟨φ, hφz, hφc, hφr⟩ := h.exists_eventually_germFactorsThrough
  -- Since `φ z = ζ ≠ z`, also `φ w ≠ w` for `w` near `z`.
  obtain ⟨U, V, hU, hV, hζU, hzV, hUV⟩ := t2_separation hne
  have hφU : ∀ᶠ w in 𝓝 z, φ w ∈ U := hφc.preimage_mem_nhds (hφz ▸ hU.mem_nhds hζU)
  -- Some such `w` lies in `s`, where it can only be related to itself.
  obtain ⟨w, hws, hwr, hwU, hwV⟩ := (mem_closure_iff_frequently.1 (hs.closure_eq ▸ mem_univ z)
    |>.and_eventually (hφr.and (hφU.and (hV.mem_nhds hzV)))).exists
  rw [hd w hws (φ w) hwr] at hwU
  exact disjoint_left.1 hUV hwU hwV

/-- A map from a Riemann surface with two points, whose germ at a point factors holomorphically
through its germ at no other point, is not constant: the germs of a constant map all factor
through each other by constant changes of coordinate. -/
theorem exists_apply_ne_of_forall_germFactorsThrough_imp_eq [Nontrivial X] {u : X → N}
    (hd : ∀ z ζ, GermFactorsThrough u z u ζ → ζ = z) : ∃ x₁ x₂, u x₁ ≠ u x₂ := by
  by_contra! h
  obtain ⟨a, b, hab⟩ := exists_pair_ne X
  exact hab (hd b a (germFactorsThrough_iff.2 ⟨fun _ ↦ a, rfl,
    .of_forall fun _ ↦ mdifferentiableAt_const, .of_forall fun y ↦ h y a⟩))

/-- If the germ of `u₁` at `b` factors through the germ of `u₀` at `a`, then near `b` the map `u₁`
takes its values in the image under `u₀` of any neighbourhood of `a`. -/
theorem GermFactorsThrough.eventually_mem_image (h : GermFactorsThrough u₁ b u₀ a) {s : Set X}
    (hs : s ∈ 𝓝 a) : ∀ᶠ y in 𝓝 b, u₁ y ∈ u₀ '' s := by
  obtain ⟨φ, hφb, hφd, hφu⟩ := h
  have ht : Tendsto φ (𝓝 b) (𝓝 a) := hφb ▸ hφd.self_of_nhds.continuousAt.tendsto
  filter_upwards [hφu, ht.eventually hs] with y hy hφy
  exact ⟨φ y, hφy, hy.symm⟩

/-- If the germ of `u₁` at `b` factors through the germ of `u₀` at `a`, then the points `y ≠ b`
with `u₁ y` in the image under `u₀` of a given neighbourhood of `a` accumulate at `b`. -/
theorem GermFactorsThrough.frequently_mem_image (h : GermFactorsThrough u₁ b u₀ a) {s : Set X}
    (hs : s ∈ 𝓝 a) : ∃ᶠ y in 𝓝[≠] b, u₁ y ∈ u₀ '' s := by
  -- A Riemann surface has no isolated points.
  have : PerfectSpace Y := ChartedSpace.perfectSpace (H := ℂ)
  have : (𝓝[≠] b).NeBot := perfectSpace_iff_forall_not_isolated.1 this b
  exact ((h.eventually_mem_image hs).filter_mono nhdsWithin_le_nhds).frequently

end TauCeti.RiemannSurface
