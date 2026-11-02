/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.GroupTheory.GroupAction.Hom
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Nerve
public import TauCeti.Topology.Homotopy.Equivariant

/-!
# Equivariant homotopies and the classifying space of an action groupoid

Let a topological monoid `G` act on spaces `X` and `Y`. A continuous map `f : X → Y` that is
equivariant induces the functor `CategoryTheory.ActionCategory.map (MonoidHom.id G) f` of action
categories, which is continuous on total arrows (`TauCeti.ActionGroupoid.continuous_mapTotal_map`,
and jointly in a parameter `TauCeti.ActionGroupoid.continuous_uncurry_mapTotal_map`, both in
`TauCeti.Topology.CategoryTheory.ActionGroupoid.Basic`), and hence a map `B(G ⋉ X) → B(G ⋉ Y)` of
fat classifying spaces. This file proves that these maps are invariant under equivariant homotopy:
a homotopy `H` from `f₀` to `f₁` through equivariant maps induces a homotopy between the maps of
classifying spaces (`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopy`).

The main application is the local model of an orbifold chart. Suppose that `X` contracts onto a
point `x` through equivariant maps, so that `x` is a fixed point of `G`
(`ContinuousMap.Homotopy.mem_fixedPoints_of_map_smul`). Then the projection
`X → *` and the inclusion of `x` induce mutually inverse homotopy equivalences
`B(G ⋉ X) ≃ₕ B(G ⋉ *)` (`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopyEquivOfContraction`),
where `G ⋉ *` is the point presentation `[*/G]`. These results hold for any monoid `G`. When `G`
is moreover a group, so that `G ⋉ X` is a groupoid, the isotropy group of the fixed point `x` in
`G ⋉ X` is all of `G` (`CategoryTheory.ActionCategory.autMulEquivOfMemFixedPoints`), so this
identifies the classifying space of the chart with that of the isotropy group at its centre. Every
label is retained, including labels acting trivially, so the equivalence keeps ineffective
isotropy. A `G`-invariant subset of a real vector space with an action commuting with real
scaling, star-convex about `0`, such as an invariant ball of an equivariant linear chart, is such a
chart
(`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopyEquivOfStarConvex`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  Section 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 3 and 4.
-/

public noncomputable section

open CategoryTheory ContinuousMap MulAction
open CategoryTheory.ActionCategory
open MulActionHom (coe_constOfMemFixedPoints coe_toPUnit constOfMemFixedPoints
  constOfMemFixedPoints_apply toPUnit)

universe u

namespace TauCeti.ActionGroupoid

variable {G X Y : Type u} [Monoid G] [MulAction G X] [MulAction G Y] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace Y]

/-- **Equivariant homotopy invariance.** A homotopy `H` from `f₀` to `f₁` through `G`-equivariant
maps induces a homotopy between the maps of fat classifying spaces `B(G ⋉ X) → B(G ⋉ Y)` induced
by `f₀` and `f₁`. -/
def fatClassifyingSpaceHomotopy {f₀ f₁ : X →ₑ[MonoidHom.id G] Y} {hf₀ : Continuous f₀}
    {hf₁ : Continuous f₁} (H : Homotopy ⟨f₀, hf₀⟩ ⟨f₁, hf₁⟩)
    (hH : ∀ (s : unitInterval) (g : G) (x : X), H (s, g • x) = g • H (s, x)) :
    Homotopy (fatClassifyingSpaceMap (ActionCategory.map (MonoidHom.id G) f₀)
        (continuous_mapTotal_map continuous_id hf₀)).hom
      (fatClassifyingSpaceMap (ActionCategory.map (MonoidHom.id G) f₁)
        (continuous_mapTotal_map continuous_id hf₁)).hom :=
  -- The stage `s` of `H` is the equivariant map `H (s, ·)`; its functors vary continuously in `s`.
  let Hs (s : unitInterval) : X →ₑ[MonoidHom.id G] Y := ⟨fun x ↦ H (s, x), hH s⟩
  have h₀ : Hs 0 = f₀ := MulActionHom.ext H.apply_zero
  have h₁ : Hs 1 = f₁ := MulActionHom.ext H.apply_one
  (TauCeti.fatClassifyingSpaceHomotopy (fun s ↦ ActionCategory.map (MonoidHom.id G) (Hs s))
    (continuous_uncurry_mapTotal_map continuous_id (f := Hs) H.continuous)).cast
    (by simp only [h₀]) (by simp only [h₁])

/-- The homotopy of fat classifying spaces induced by an equivariant homotopy `H` applies, at time
`s`, the functor induced by the equivariant map `H (s, ·)` to the string of composable arrows of
each simplex. -/
theorem fatClassifyingSpaceHomotopy_apply_ι {f₀ f₁ : X →ₑ[MonoidHom.id G] Y}
    {hf₀ : Continuous f₀} {hf₁ : Continuous f₁} (H : Homotopy ⟨f₀, hf₀⟩ ⟨f₁, hf₁⟩)
    (hH : ∀ (s : unitInterval) (g : G) (x : X), H (s, g • x) = g • H (s, x))
    (s : unitInterval) (n : SemiSimplexCategory)
    (F : ComposableArrows (ActionCategory G X) (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatClassifyingSpaceHomotopy H hH (s, fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n (((ActionCategory.map (MonoidHom.id G)
        (⟨fun x ↦ H (s, x), hH s⟩ : X →ₑ[MonoidHom.id G] Y)).mapComposableArrows _).obj F, t) :=
  TauCeti.fatClassifyingSpaceHomotopy_apply_ι _ _ s n F t

variable (G) in
/-- **The local model of an orbifold chart.** If `H` is a contraction of `X` onto a point `x`
through `G`-equivariant maps, then `x` is fixed by `G` and the projection `X → *` induces a
homotopy equivalence `B(G ⋉ X) ≃ₕ B(G ⋉ *)` with the classifying space of the point presentation
`[*/G]`. Its inverse is induced by the inclusion of `x`. -/
def fatClassifyingSpaceHomotopyEquivOfContraction (x : X)
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))
    (hH : ∀ (s : unitInterval) (g : G) (y : X), H (s, g • y) = g • H (s, y)) :
    fatClassifyingSpace (ActionCategory G X) ≃ₕ
      fatClassifyingSpace (ActionCategory G PUnit.{u + 1}) where
  toFun := (fatClassifyingSpaceMap
    (ActionCategory.map (MonoidHom.id G) (toPUnit X (MonoidHom.id G)))
    (continuous_mapTotal_map continuous_id (by rw [coe_toPUnit]; exact continuous_const))).hom
  invFun := (fatClassifyingSpaceMap (ActionCategory.map (MonoidHom.id G)
      (constOfMemFixedPoints (H.mem_fixedPoints_of_map_smul hH)))
    (continuous_mapTotal_map continuous_id
      (by rw [coe_constOfMemFixedPoints]; exact continuous_const))).hom
  left_inv := by
    -- The composite is induced by the constant map onto `x`, which `H` joins to the identity.
    have hc : ActionCategory.map (MonoidHom.id G)
          (toPUnit X (MonoidHom.id G) : X →ₑ[MonoidHom.id G] PUnit.{u + 1}) ⋙
        ActionCategory.map (MonoidHom.id G)
          (constOfMemFixedPoints (H.mem_fixedPoints_of_map_smul hH)) =
        ActionCategory.map (MonoidHom.id G)
          (constOfMemFixedPoints (H.mem_fixedPoints_of_map_smul hH)) :=
      (map_comp _ _ _).trans (congrArg _ (MulActionHom.ext fun _ ↦ by simp))
    -- Read the endpoint `const X x` of `H` as the coercion of the constant equivariant map.
    have h₁ : ContinuousMap.const X x = ⟨constOfMemFixedPoints (φ := MonoidHom.id G)
        (H.mem_fixedPoints_of_map_smul hH),
          by rw [coe_constOfMemFixedPoints]; exact continuous_const⟩ :=
      ContinuousMap.ext fun _ ↦ (constOfMemFixedPoints_apply _ _).symm
    exact ⟨(fatClassifyingSpaceHomotopy (f₀ := MulActionHom.id G) (H.cast rfl h₁) hH).symm.cast
        (by rw [← TopCat.hom_comp, ← fatClassifyingSpaceMap_comp]; simp only [hc])
        (by simp only [map_id, fatClassifyingSpaceMap_id, TopCat.hom_id])⟩
  right_inv := by
    have hp : (toPUnit X (MonoidHom.id G) : X →ₑ[MonoidHom.id G] PUnit.{u + 1}).comp
        (constOfMemFixedPoints (φ := MonoidHom.id G) (H.mem_fixedPoints_of_map_smul hH)) =
          MulActionHom.id G :=
      MulActionHom.ext fun _ ↦ Subsingleton.elim _ _
    rw [← TopCat.hom_comp, ← fatClassifyingSpaceMap_comp]
    simp only [map_comp, hp, map_id, fatClassifyingSpaceMap_id, TopCat.hom_id]
    exact .refl _

/-- The homotopy equivalence `B(G ⋉ X) ≃ₕ B(G ⋉ *)` of a contraction onto a fixed point keeps the
labels of each string of composable arrows and forgets its points. -/
theorem fatClassifyingSpaceHomotopyEquivOfContraction_apply_ι
    (F : ComposableArrows (ActionCategory G X) (SemiSimplexCategory.toSimplexCategory.obj n).len) :
    fatClassifyingSpaceHomotopyEquivOfContraction G x H hH (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n
        ((nerveEquiv G PUnit.{u + 1} _).symm (PUnit.unit, (nerveEquiv G X _ F).2), t) :=
  (fatClassifyingSpaceMap_ι _ _ n F t).trans <| congrArg (fun F ↦ fatRealization.ι _ n (F, t)) <|
    (nerveEquiv G PUnit.{u + 1} _).eq_symm_apply.2 <| Prod.ext rfl <| funext fun _ ↦ by simp

/-- The inverse of the homotopy equivalence `B(G ⋉ X) ≃ₕ B(G ⋉ *)` of a contraction onto a fixed
point `x` sends a string of composable arrows of `G ⋉ *` to the string at `x` with the same
labels. -/
theorem fatClassifyingSpaceHomotopyEquivOfContraction_symm_apply_ι
    (F : ComposableArrows (ActionCategory G PUnit.{u + 1})
      (SemiSimplexCategory.toSimplexCategory.obj n).len) :
    (fatClassifyingSpaceHomotopyEquivOfContraction G x H hH).symm
        (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n ((nerveEquiv G X _).symm (x, (nerveEquiv G PUnit.{u + 1} _ F).2), t) :=
  (fatClassifyingSpaceMap_ι _ _ n F t).trans <| congrArg (fun F ↦ fatRealization.ι _ n (F, t)) <|
    (nerveEquiv G X _).eq_symm_apply.2 <| Prod.ext
      -- The first point of the image string is the value at that point of the map onto `x`.
      (by simp only [nerveEquiv_apply, Functor.mapComposableArrows_obj_obj, back_map_obj,
        constOfMemFixedPoints_apply])
      (funext fun _ ↦ by simp)

section StarConvex

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  [MulAction G E] [SMulCommClass ℝ G E]

variable (G) in
/-- Let `G` act on a real vector space `E`, commuting with real scaling. If a `G`-invariant subset
`U` of `E` contains `0` and is star-convex about `0`, as an invariant ball of an invariant norm is,
then the radial contraction `y ↦ (1 - s) • y` is equivariant, so `B(G ⋉ U) ≃ₕ B(G ⋉ *)`. -/
def fatClassifyingSpaceHomotopyEquivOfStarConvex (U : SubMulAction G E)
    (hU : StarConvex ℝ 0 (U : Set E)) (h0 : (0 : E) ∈ U) :
    fatClassifyingSpace (ActionCategory G U) ≃ₕ
      fatClassifyingSpace (ActionCategory G PUnit.{u + 1}) :=
  fatClassifyingSpaceHomotopyEquivOfContraction G ⟨0, h0⟩
    { toFun p := ⟨(unitInterval.symm p.1 : ℝ) • (p.2 : E),
        hU.smul_mem p.2.2 (unitInterval.symm p.1).2.1 (unitInterval.symm p.1).2.2⟩
      continuous_toFun := Continuous.subtype_mk
        ((continuous_subtype_val.comp (unitInterval.continuous_symm.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd)) _
      map_zero_left _ := Subtype.ext (by simp)
      map_one_left _ := Subtype.ext (by simp) }
    fun s g y ↦ Subtype.ext (smul_comm (unitInterval.symm s : ℝ) g (y : E))

/-- The homotopy equivalence `B(G ⋉ U) ≃ₕ B(G ⋉ *)` of a star-convex invariant subset keeps the
labels of each string of composable arrows and forgets its points. -/
theorem fatClassifyingSpaceHomotopyEquivOfStarConvex_apply_ι (U : SubMulAction G E)
    (hU : StarConvex ℝ 0 (U : Set E)) (h0 : (0 : E) ∈ U) (n : SemiSimplexCategory)
    (F : ComposableArrows (ActionCategory G U) (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    fatClassifyingSpaceHomotopyEquivOfStarConvex G U hU h0 (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n
        ((nerveEquiv G PUnit.{u + 1} _).symm (PUnit.unit, (nerveEquiv G U _ F).2), t) :=
  fatClassifyingSpaceHomotopyEquivOfContraction_apply_ι F

/-- The inverse of the homotopy equivalence `B(G ⋉ U) ≃ₕ B(G ⋉ *)` of a star-convex invariant
subset sends a string of composable arrows of `G ⋉ *` to the string at `0` with the same labels. -/
theorem fatClassifyingSpaceHomotopyEquivOfStarConvex_symm_apply_ι (U : SubMulAction G E)
    (hU : StarConvex ℝ 0 (U : Set E)) (h0 : (0 : E) ∈ U) (n : SemiSimplexCategory)
    (F : ComposableArrows (ActionCategory G PUnit.{u + 1})
      (SemiSimplexCategory.toSimplexCategory.obj n).len)
    (t : SemiSimplexCategory.toTop.obj n) :
    (fatClassifyingSpaceHomotopyEquivOfStarConvex G U hU h0).symm (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n
        ((nerveEquiv G U _).symm (⟨0, h0⟩, (nerveEquiv G PUnit.{u + 1} _ F).2), t) :=
  fatClassifyingSpaceHomotopyEquivOfContraction_symm_apply_ι F

end StarConvex

end TauCeti.ActionGroupoid
