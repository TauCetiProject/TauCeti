/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient

/-!
# The universal cover lifts equivariantly to the orientation cover

Let `E → B` be a real vector bundle over a locally path-connected, semilocally simply connected
base `B` with a base point `b₀`, and `B'` its orientation double cover. The universal cover
`UniversalCover b₀` is simply connected, so its projection to `B` lifts to a continuous map
`s : UniversalCover b₀ → B'`: a continuous choice of orientations of the fibres of `E` pulled back
to the universal cover. The fundamental group `π₁(B, b₀)` acts on the universal cover by deck
transformations, and `ℤˣ` acts on `B'`, `-1` by the deck involution exchanging the two orientations
of each fibre. The lift is equivariant along the orientation character
`w₁ : π₁(B, b₀) →* ℤˣ` of `E` (`TauCeti.VectorBundleOrientationCover.orientationCharacter`):
`s(g • x) = w₁(g) • s(x)`, so a deck transformation preserves all the lifted orientations or
reverses all of them, according to `w₁`.

This is the input that the Thom isomorphism of a cover lifting to the orientation cover
(`TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Lift`) needs for the universal cover.

## Main results

* `TauCeti.VectorBundleOrientationCover.exists_lift_universalCover`: the projection of the
  universal cover lifts to the orientation cover, equivariantly along the orientation character
  `π₁(B, b₀) →* ℤˣ` of `E`.
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti.VectorBundleOrientationCover

universe uB uE uι

variable {B : Type uB} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E : B → Type uE} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type uι} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)

include hι in
/-- **The universal cover lifts equivariantly to the orientation cover.** Let `B` be locally
path-connected and semilocally simply connected, with a base point `b₀`. The projection of the
universal cover `UniversalCover b₀ → B` lifts to a continuous map `s` to the orientation double
cover `B'` of `E` with `s(g • x) = w₁(g) • s(x)` for every deck transformation `g`, where
`w₁ : π₁(B, b₀) →* ℤˣ` is the orientation character of `E`: a deck transformation preserves all
the lifted orientations or reverses all of them, according to `w₁`. -/
theorem exists_lift_universalCover [LocallyPathConnectedSpace B]
    [SemilocallySimplyConnectedSpace B] (b₀ : B) :
    ∃ s : C(UniversalCover b₀, VectorBundleOrientationCover F E ι),
      (∀ x, (s x).proj = x.proj) ∧
        ∀ (g : FundamentalGroup B b₀) x, s (g • x) = orientationCharacter F E hι b₀ g • s x := by
  have hq := isCoveringMap_proj (F := F) (E := E) hι
  -- the universal cover is simply connected, so its projection lifts to the orientation cover
  let x₀ : UniversalCover b₀ := UniversalCover.basepointLift b₀
  obtain ⟨e₀, he₀⟩ := surjective_proj (F := F) (E := E) hι b₀
  obtain ⟨s, ⟨-, hs⟩, -⟩ := hq.existsUnique_continuousMap_lifts
    ⟨UniversalCover.proj, UniversalCover.continuous_proj b₀⟩ x₀ e₀
    (he₀.trans (UniversalCover.proj_basepointLift b₀).symm :)
  have hf : proj ∘ ⇑s = UniversalCover.proj := hs
  have hs' (x : UniversalCover b₀) : (s x).proj = x.proj := congrFun hs x
  -- `s` carries the monodromy of the universal cover along `g⁻¹`, which moves `x₀` to `g • x₀`,
  -- to the monodromy of the orientation cover, which the orientation character reads off
  have hx₀ (g : FundamentalGroup B b₀) : s (g • x₀) = orientationCharacter F E hι b₀ g • s x₀ := by
    let e := Function.fiberMap s hf b₀ (UniversalCover.basepointLift b₀)
    have he : (e : VectorBundleOrientationCover F E ι) = s x₀ :=
      Function.fiberMap_apply_coe s hf b₀ _
    have h := congrArg Subtype.val ((UniversalCover.isCoveringMap b₀).fiberMap_monodromy hq s hf
      (g⁻¹).toPath (UniversalCover.basepointLift b₀))
    rw [Function.fiberMap_apply_coe, UniversalCover.monodromy_basepointLift, inv_inv] at h
    have hχ : orientationCharacter F E hι b₀ g⁻¹ = orientationCharacter F E hι b₀ g := by
      rw [map_inv, Int.units_inv_eq_self]
    rcases Int.units_eq_one_or (orientationCharacter F E hι b₀ g) with h1 | h1
    · rw [h1, one_smul, h, (orientationCharacter_eq_one_iff_monodromy_eq hι _ e).1 (hχ.trans h1),
        he]
    · rw [h1, h, (orientationCharacter_eq_neg_one_iff hι _ e).1 (hχ.trans h1), he,
        neg_one_smul_eq_deck]
  -- `x ↦ s (g • x)` and `x ↦ w₁ g • s x` lift the same map and agree at `x₀`, so they are equal
  refine ⟨s, hs', fun g x ↦ congrFun (hq.eq_of_comp_eq
    (g₁ := fun x ↦ s (g • x)) (g₂ := fun x ↦ orientationCharacter F E hι b₀ g • s x)
    (s.continuous.comp (continuous_const_smul g)) ((continuous_const_smul _).comp s.continuous)
    (funext fun x ↦ (hs' _).trans ((UniversalCover.proj_smul g x).trans
      ((hs' x).symm.trans (proj_smul _ _).symm))) x₀ (hx₀ g)) x⟩

end TauCeti.VectorBundleOrientationCover
