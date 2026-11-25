/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import TauCeti.Topology.Homotopy.Extension.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.Topology.Homotopy.Extension.Prod

/-!
# Moving the image of a cofibrant point

Let `x` be a closed point of `X` with the homotopy extension property, such as any point of a
Hausdorff CW complex (`TauCeti.hasHomotopyExtensionProperty_singleton_of_cwComplex`). Two
constructions move the value of a map `X → Y` at `x` without losing control of what the map does
on fundamental groups.

* A map `f₀` is homotopic to a map `f` sending `x` to any point `y` joined to `f₀ x` by a path
  `γ`, by a homotopy whose trace at `x` is `γ`, and `f` induces on `π₁(X, x)` the map induced by
  `f₀` followed by the change of base point along `γ`
  (`TauCeti.HasHomotopyExtensionProperty.exists_mapOfEq_eq_fundamentalGroupMulEquivOfPath_map`).
* A homotopy between two maps sending `x` to `y` whose trace at `x` is a null-homotopic loop can be
  replaced by a homotopy relative to `x`
  (`TauCeti.HasHomotopyExtensionProperty.homotopicRel_singleton_of_homotopic_refl`).

These are the two steps that reduce statements about pointed maps out of a CW complex with an
arbitrary base point to the case where the base point is a `0`-cell, the case treated by Hatcher.
The target `Y` may lie in any universe, since `{x}` is closed.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, the section on the homotopy extension property, and Section 1.B, Proposition 1B.9,
  whose proof takes the base point to be a `0`-cell.
-/

public section

open Set unitInterval

universe u v

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] {x : X} {Y : Type v} [TopologicalSpace Y]

/-- **Moving the image of a cofibrant point along a path.** Let `x` be a closed point of `X` with
the homotopy extension property, `f₀ : X → Y` a map and `γ` a path from `f₀ x` to `y`. Then `f₀` is
homotopic to a map `f` with `f x = y`, by a homotopy whose trace at `x` is `γ`, and `f` induces on
`π₁(X, x)` the map induced by `f₀` followed by the change of base point along `γ`. -/
theorem HasHomotopyExtensionProperty.exists_mapOfEq_eq_fundamentalGroupMulEquivOfPath_map
    (h : HasHomotopyExtensionProperty ({x} : Set X)) (hx : IsClosed ({x} : Set X))
    (f₀ : C(X, Y)) {y : Y} (γ : Path (f₀ x) y) :
    ∃ (f : C(X, Y)) (hf : f x = y) (F : f₀.Homotopy f), (∀ t, F (t, x) = γ t) ∧
      ∀ g : FundamentalGroup X x, FundamentalGroup.mapOfEq f hf g =
        FundamentalGroup.fundamentalGroupMulEquivOfPath γ (FundamentalGroup.map f₀ x g) := by
  -- Extend the homotopy of `f₀` on `{x}` which runs along `γ`.
  let H : (f₀.restrict {x}).Homotopy (ContinuousMap.const _ y) :=
    { toFun := fun p ↦ γ p.1
      continuous_toFun := by fun_prop
      map_zero_left := fun a ↦ by
        rw [γ.source, ContinuousMap.restrict_apply, mem_singleton_iff.1 a.property]
      map_one_left := fun _ ↦ γ.target }
  obtain ⟨f, F, hF⟩ := h.exists_homotopy_of_restrict hx f₀ H
  have hf : f x = y := by
    rw [← F.apply_one, hF 1 ⟨x, rfl⟩]
    exact γ.target
  refine ⟨f, hf, F, fun t ↦ hF t ⟨x, rfl⟩, fun g ↦ ?_⟩
  subst hf
  -- The trace of `F` at `x` is `γ`.
  obtain rfl : F.evalAt x = γ := Path.ext <| funext fun t ↦ hF t ⟨x, rfl⟩
  rw [FundamentalGroup.mapOfEq_rfl]
  exact (F.fundamentalGroupMulEquivOfPath_evalAt_map x g).symm

section NullHomotopicTrace

variable (x) in
/-- The bottom, top and the segment over `x` of the cylinder `I × X`, where a homotopy relative to
`{x}` is prescribed. -/
private abbrev endsUnionTrace : Set (I × X) := ({0, 1} : Set I) ×ˢ univ ∪ univ ×ˢ {x}

open scoped Classical in
/-- On `{0, 1} × X ∪ I × {x}`, the map which follows `N` over `I × {x}` and `F` elsewhere is
continuous, provided `N` is constant at the ends `F (0, x)` and `F (1, x)` along each side. -/
private theorem continuous_ite_endsUnionTrace (hx : IsClosed ({x} : Set X)) {F : C(I × X, Y)}
    {N : C(I × I, Y)} (h₀ : ∀ u, N (u, 0) = F (0, x)) (h₁ : ∀ u, N (u, 1) = F (1, x)) :
    Continuous fun p : I × endsUnionTrace x ↦
      if p.2.val.2 = x then N (p.1, p.2.val.1) else F p.2.val := by
  rw [← continuousOn_univ]
  have hcover : (univ : Set (I × endsUnionTrace x)) =
      {p | p.2.val.1 ∈ ({0, 1} : Set I)} ∪ {p | p.2.val.2 = x} :=
    (eq_univ_of_forall fun p ↦ p.2.property.imp And.left And.right).symm
  rw [hcover]
  refine ContinuousOn.union_of_isClosed ?_ ?_
    ((toFinite _).isClosed.preimage (by fun_prop)) (hx.preimage (by fun_prop))
  · refine (F.continuous.comp (f := fun p : I × endsUnionTrace x ↦ p.2.val)
      (by fun_prop)).continuousOn.congr fun p (hs : p.2.val.1 ∈ ({0, 1} : Set I)) ↦ ?_
    obtain ⟨u, ⟨⟨s, x'⟩, _⟩⟩ := p
    simp only [Function.comp_apply]
    split_ifs with hx'
    · subst hx'
      rcases hs with rfl | rfl
      exacts [h₀ u, h₁ u]
    · rfl
  · refine (N.continuous.comp (f := fun p : I × endsUnionTrace x ↦ (p.1, p.2.val.1))
      (by fun_prop)).continuousOn.congr fun p (hp : p.2.val.2 = x) ↦ ?_
    simp only [hp, ↓reduceIte, Function.comp_apply]

/-- **A homotopy with a null-homotopic trace at a cofibrant point can be made stationary there.**
Let `x` be a closed point of `X` with the homotopy extension property, and `F` a homotopy between
maps `f g : X → Y` sending `x` to `y`. If the trace of `F` at `x` is a loop at `y` homotopic to the
constant loop, then `f` and `g` are homotopic relative to `{x}`. -/
theorem HasHomotopyExtensionProperty.homotopicRel_singleton_of_homotopic_refl
    (h : HasHomotopyExtensionProperty ({x} : Set X)) (hx : IsClosed ({x} : Set X))
    {f g : C(X, Y)} (F : f.Homotopy g) {y : Y} (hf : f x = y) (hg : g x = y)
    (hF : ((F.evalAt x).cast hf.symm hg.symm).Homotopic (Path.refl y)) :
    f.HomotopicRel g {x} := by
  obtain ⟨N⟩ := hF
  classical
  -- On `{0, 1} × X ∪ I × {x}`, deform `F` by the null-homotopy `N` of its trace over `I × {x}`,
  -- keeping it fixed over `{0, 1} × X`, and extend this deformation over `I × X`.
  let K : C(I × endsUnionTrace x, Y) :=
    ⟨fun p ↦ if p.2.val.2 = x then N (p.1, p.2.val.1) else F p.2.val,
      continuous_ite_endsUnionTrace hx (F := F.toContinuousMap) (N := N.toContinuousMap)
        (fun u ↦ by rw [N.coe_toContinuousMap, N.source, F.coe_toContinuousMap, F.apply_zero, hf])
        (fun u ↦ by rw [N.coe_toContinuousMap, N.target, F.coe_toContinuousMap, F.apply_one, hg])⟩
  obtain ⟨E, -, hE⟩ := (h.zero_one_prod_univ_union_univ_prod hx).exists_extension_of_isClosed
    (((toFinite _).isClosed.prod isClosed_univ).union (isClosed_univ.prod hx))
    F.toContinuousMap K fun ⟨⟨s, x'⟩, _⟩ ↦ by
      simp only [K, ContinuousMap.coe_mk]
      split_ifs with hx'
      · subst hx'
        simp
      · simp
  -- The end of the extension is a homotopy from `f` to `g` which is constant at `x`.
  refine ⟨{ toFun := fun p ↦ E (1, p)
            continuous_toFun := by fun_prop
            map_zero_left := fun x' ↦ ?_
            map_one_left := fun x' ↦ ?_
            prop' := fun s x' hx' ↦ ?_ }⟩
  · rw [hE 1 ⟨_, Or.inl ⟨by simp, trivial⟩⟩]
    simp only [K, ContinuousMap.coe_mk]
    split_ifs with hx' <;> simp [hx', hf]
  · rw [hE 1 ⟨_, Or.inl ⟨by simp, trivial⟩⟩]
    simp only [K, ContinuousMap.coe_mk]
    split_ifs with hx' <;> simp [hx', hg]
  · obtain rfl := mem_singleton_iff.1 hx'
    rw [ContinuousMap.coe_mk, hE 1 ⟨(s, x'), Or.inr ⟨trivial, mem_singleton x'⟩⟩]
    simp only [K, ContinuousMap.coe_mk, ↓reduceIte, N.apply_one, Path.coe_toContinuousMap,
      Path.refl_apply, hf]

end NullHomotopicTrace

end TauCeti
