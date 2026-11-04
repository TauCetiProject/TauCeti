/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.RepresentationTheory.Invariants

/-!
# The Poincaré lemma for differential forms invariant under a linear action

Let a group `G` act on a real normed space `E` through a continuous representation `ρ`, and let
`s ⊆ E` be a `ρ`-invariant set. A differential `k`-form `ω` on `E` is invariant on `s` when
`(ρ g)^* ω = ω` at every point of `s`, that is
`ω (ρ g x) (ρ g v₁, …, ρ g vₖ) = ω x (v₁, …, vₖ)` for all `g` and all `x ∈ s`.

Pullback along a continuous linear map `A` intertwines the Poincaré homotopy operators centred at
`y₀` and at `A y₀` (`TauCeti.poincareHomotopy_pullback_apply`). Hence the operator `K` centred at
a point `x₀` fixed by `A` sends `A`-invariant forms on a set star-convex with respect to `x₀` to
`A`-invariant forms (`StarConvex.compContinuousLinearMap_poincareHomotopy_eq`). When `G` is finite,
a nonempty invariant convex set always contains a point fixed by `G`: the average
`|G|⁻¹ ∑ g, ρ g x` of the orbit of any of its points (`Convex.averageMap_mem`). Centred there, the
homotopy formula `d K + K d = id` restricts to invariant forms, so a closed invariant form of
positive degree on an invariant convex set is the exterior derivative of an invariant form of the
same regularity (`Convex.exists_invariant_contDiffOn_forall_extDerivWithin_eq`). The same holds on
an invariant open set star-convex with respect to a fixed point
(`StarConvex.exists_invariant_contDiffOn_forall_extDeriv_eq`), for any monoid.

This is the vanishing of the positive-degree cohomology of invariant forms on the linear local
model of an orbifold: by Bochner linearization, a point with finite isotropy group `G` has a chart
onto a `G`-invariant ball on which `G` acts linearly, possibly with a nontrivial kernel. No
faithfulness of `ρ` is assumed, and every element of `G`, including those acting trivially, is
taken into account in the average.

## Main declarations

* `StarConvex.exists_invariant_contDiffOn_forall_extDeriv_eq`: the Poincaré lemma for invariant
  forms on an invariant open set star-convex with respect to a fixed point.
* `Convex.exists_invariant_contDiffOn_forall_extDerivWithin_eq`: the Poincaré lemma for forms
  invariant under a finite group on an invariant convex set with unique derivatives.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and Stringy Topology*, Cambridge Tracts in
  Mathematics 171, Cambridge University Press, 2007, Ch. 2, for invariant differential forms on
  orbifold charts and the de Rham theorem for orbifolds.
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Chapter I, Section 4, for the Poincaré lemma via a homotopy operator.
-/

public section

noncomputable section

open Set TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {n : ℕ}

namespace StarConvex

variable {x₀ : E} {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
  {G : Type*} [Monoid G] {ρ : ContRepresentation ℝ G E}

/-- **The Poincaré lemma for invariant forms.** Let a monoid `G` act on `E` through a continuous
representation `ρ`, fixing `x₀` and preserving an open set `s` star-convex with respect to `x₀`.
A closed `C^r` form of positive degree on `s`, `r ≥ 1`, invariant under every `ρ g` on `s`, is the
exterior derivative on `s` of an invariant `C^r` form vanishing at `x₀`. -/
theorem exists_invariant_contDiffOn_forall_extDeriv_eq (hs : StarConvex ℝ x₀ s) (hso : IsOpen s)
    (hρx₀ : ∀ g, ρ g x₀ = x₀) (hρs : ∀ g, MapsTo (ρ g) s s) {r : ℕ∞} (hr : 1 ≤ r)
    (hωr : ContDiffOn ℝ r ω s) (hclosed : ∀ y ∈ s, extDeriv ω y = 0)
    (hω : ∀ g, ∀ y ∈ s, (ω (ρ g y)).compContinuousLinearMap (ρ g) = ω y) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧ α x₀ = 0 ∧
      (∀ g, ∀ y ∈ s, (α (ρ g y)).compContinuousLinearMap (ρ g) = α y) ∧
      ∀ y ∈ s, extDeriv α y = ω y :=
  ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hso hωr, poincareHomotopy_self x₀ ω,
    fun g _ hy ↦ hs.compContinuousLinearMap_poincareHomotopy_eq hωr.continuousOn (hρx₀ g)
      (hρs g) (hω g) hy,
    fun _ hy ↦ hs.extDeriv_poincareHomotopy hso (hωr.of_le (by exact_mod_cast hr)) hclosed hy⟩

end StarConvex

namespace Convex

variable {G : Type*} [Group G] [Finite G] {ρ : ContRepresentation ℝ G E}
  {s : Set E} {ω : E → E [⋀^Fin (n + 1)]→L[ℝ] F}

/-- **The Poincaré lemma for forms invariant under a finite group.** Let a finite group `G` act on
`E` through a continuous representation `ρ` preserving a nonempty convex set `s` with unique
derivatives, which need not be open. A `C^r` form of positive degree, `r ≥ 1`, closed within `s`
and invariant under every `ρ g` on `s`, is the exterior derivative within `s` of an invariant
`C^r` form. The primitive is the Poincaré homotopy operator centred at the average of an orbit in
`s`, a point fixed by `G`. -/
theorem exists_invariant_contDiffOn_forall_extDerivWithin_eq (hs : Convex ℝ s)
    (hsu : UniqueDiffOn ℝ s) (hsne : s.Nonempty) (hρs : ∀ g, MapsTo (ρ g) s s) {r : ℕ∞}
    (hr : 1 ≤ r) (hωr : ContDiffOn ℝ r ω s) (hclosed : ∀ y ∈ s, extDerivWithin ω s y = 0)
    (hω : ∀ g, ∀ y ∈ s, (ω (ρ g y)).compContinuousLinearMap (ρ g) = ω y) :
    ∃ α : E → E [⋀^Fin n]→L[ℝ] F, ContDiffOn ℝ r α s ∧
      (∀ g, ∀ y ∈ s, (α (ρ g y)).compContinuousLinearMap (ρ g) = α y) ∧
      ∀ y ∈ s, extDerivWithin α s y = ω y := by
  have := Fintype.ofFinite G
  let : Invertible (Fintype.card G : ℝ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  obtain ⟨v, hv⟩ := hsne
  set x₀ := ρ.toRepresentation.averageMap v
  have hx₀ : x₀ ∈ s := hs.averageMap_mem hρs hv
  have hρx₀ (g : G) : ρ g x₀ = x₀ := ρ.toRepresentation.averageMap_invariant v g
  exact ⟨poincareHomotopy x₀ ω, hs.contDiffOn_poincareHomotopy hsu hx₀ hωr,
    fun g _ hy ↦ (hs.starConvex hx₀).compContinuousLinearMap_poincareHomotopy_eq
      hωr.continuousOn (hρx₀ g) (hρs g) (hω g) hy,
    fun _ hy ↦ hs.extDerivWithin_poincareHomotopy hsu hx₀ (hωr.of_le (by exact_mod_cast hr))
      hclosed hy⟩

end Convex
