/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.CategoryTheory.Groupoid.ActionCategory.Map
public import TauCeti.Topology.CategoryTheory.ActionGroupoid.Nerve

/-!
# Equivariant homotopies and the classifying space of an action groupoid

Let a topological monoid `G` act on spaces `X` and `Y`. A continuous map `f : X → Y` that is
equivariant induces the functor `CategoryTheory.ActionCategory.map (MonoidHom.id G) f` of action
groupoids, which is continuous on total arrows (`TauCeti.ActionGroupoid.continuous_mapTotal_map`),
and hence a map `B(G ⋉ X) → B(G ⋉ Y)` of fat classifying spaces. This file proves that these maps
are invariant under equivariant homotopy: a homotopy `H` from `f₀` to `f₁` through equivariant
maps induces a homotopy between the maps of classifying spaces
(`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopy`).

The main application is the local model of an orbifold chart. Suppose that `x` is a fixed point of
`G` in `X` and that `X` contracts onto `x` through equivariant maps. Then the projection
`X → *` and the inclusion of `x` induce mutually inverse homotopy equivalences
`B(G ⋉ X) ≃ₕ B(G ⋉ *)` (`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopyEquivOfContraction`),
where `G ⋉ *` is the point presentation `[*/G]`. Since `x` is fixed, the isotropy group of `x` in
`G ⋉ X` is all of `G` (`CategoryTheory.ActionCategory.autMulEquivOfMemFixedPoints`), so this
identifies the classifying space of the chart with that of the isotropy group at its centre. Every
label is retained, including labels acting trivially, so the equivalence keeps ineffective
isotropy. A `G`-invariant subset of a real vector space with a linear action, star-convex about
`0`, such as an invariant ball of an equivariant linear chart, is such a chart
(`TauCeti.ActionGroupoid.fatClassifyingSpaceHomotopyEquivOfStarConvex`).

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS **34** (1968), 105–112,
  Section 2.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 3 and 4.
-/

public noncomputable section

open CategoryTheory ContinuousMap MulAction
open CategoryTheory.ActionCategory

universe u

namespace TauCeti.ActionGroupoid

section Map

variable {M N X Y : Type*} [Monoid M] [Monoid N] [MulAction M X] [MulAction N Y]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace X] [TopologicalSpace Y]

/-- The functor of action groupoids induced by a continuous equivariant map along a continuous
monoid homomorphism is continuous on total arrows. -/
theorem continuous_mapTotal_map {φ : M →* N} (hφ : Continuous φ) {f : X →ₑ[φ] Y}
    (hf : Continuous f) : Continuous (ActionCategory.map φ f).toPrefunctor.mapTotal :=
  (arrowHomeomorph N Y).isInducing.continuous_iff.2 <|
    ((hφ.prodMap hf).comp (arrowHomeomorph M X).continuous).congr fun _ ↦ by simp

end Map

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
  have hHs_apply (s : unitInterval) (x : X) : Hs s x = H (s, x) := rfl
  have hHs : Continuous fun p : unitInterval × Quiver.Total (ActionCategory G X) ↦
      (ActionCategory.map (MonoidHom.id G) (Hs p.1)).toPrefunctor.mapTotal p.2 :=
    (arrowHomeomorph G Y).isInducing.continuous_iff.2 <|
      ((continuous_fst.comp ((arrowHomeomorph G X).continuous.comp continuous_snd)).prodMk
        (H.continuous.comp (continuous_fst.prodMk
          (continuous_snd.comp ((arrowHomeomorph G X).continuous.comp continuous_snd))))).congr
        fun _ ↦ by simp [hHs_apply]
  have h₀ : Hs 0 = f₀ := MulActionHom.ext H.apply_zero
  have h₁ : Hs 1 = f₁ := MulActionHom.ext H.apply_one
  (TauCeti.fatClassifyingSpaceHomotopy (fun s ↦ ActionCategory.map (MonoidHom.id G) (Hs s))
    hHs).cast (by simp only [h₀]) (by simp only [h₁])

variable (G) in
/-- **The local model of an orbifold chart.** If `x` is a fixed point of `G` in `X` and `H` is a
contraction of `X` onto `x` through `G`-equivariant maps, then the projection `X → *` induces a
homotopy equivalence `B(G ⋉ X) ≃ₕ B(G ⋉ *)` with the classifying space of the point presentation
`[*/G]`. Its inverse is induced by the inclusion of `x`. -/
def fatClassifyingSpaceHomotopyEquivOfContraction (x : X) (hx : x ∈ fixedPoints G X)
    (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))
    (hH : ∀ (s : unitInterval) (g : G) (y : X), H (s, g • y) = g • H (s, y)) :
    fatClassifyingSpace (ActionCategory G X) ≃ₕ
      fatClassifyingSpace (ActionCategory G PUnit.{u + 1}) := by
  let p : X →ₑ[MonoidHom.id G] PUnit.{u + 1} := ⟨fun _ ↦ PUnit.unit, fun _ _ ↦ rfl⟩
  let i : PUnit.{u + 1} →ₑ[MonoidHom.id G] X := ⟨fun _ ↦ x, fun g _ ↦ (hx g).symm⟩
  let c : X →ₑ[MonoidHom.id G] X := ⟨fun _ ↦ x, fun g _ ↦ (hx g).symm⟩
  have hi_apply (y : PUnit.{u + 1}) : i y = x := rfl
  have hc_apply (y : X) : c y = x := rfl
  have hp : Continuous p := continuous_const
  have hi : Continuous i := continuous_const
  -- Both composites are computed on each simplex: a string of `G ⋉ X` or `G ⋉ *` is determined
  -- by its first point and its labels, which the functors induced by `p` and `i` keep.
  have hpi : fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hi) ≫
      fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hp) =
        𝟙 (fatClassifyingSpace (ActionCategory G PUnit.{u + 1})) := by
    rw [← fatClassifyingSpaceMap_comp, ← fatClassifyingSpaceMap_id]
    exact fatClassifyingSpaceMap_eq_of_mapComposableArrows_obj _ _ fun n F ↦
      ComposableArrows.ext_of_back_obj_zero_of_hom_map rfl fun _ ↦ by simp
  have hip : fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hp) ≫
      fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hi) =
        fatClassifyingSpaceMap (ActionCategory.map (MonoidHom.id G) c)
          (continuous_mapTotal_map continuous_id continuous_const) := by
    rw [← fatClassifyingSpaceMap_comp]
    exact fatClassifyingSpaceMap_eq_of_mapComposableArrows_obj _ _ fun n F ↦
      ComposableArrows.ext_of_back_obj_zero_of_hom_map (by simp [hi_apply, hc_apply])
        fun _ ↦ by simp
  have hid : fatClassifyingSpaceMap (ActionCategory.map (MonoidHom.id G)
      (MulActionHom.id G : X →ₑ[MonoidHom.id G] X))
        (continuous_mapTotal_map continuous_id continuous_id) =
          𝟙 (fatClassifyingSpace (ActionCategory G X)) := by
    rw [← fatClassifyingSpaceMap_id]
    exact fatClassifyingSpaceMap_eq_of_mapComposableArrows_obj _ _ fun n F ↦
      ComposableArrows.ext_of_back_obj_zero_of_hom_map (by simp) fun _ ↦ by simp
  refine ⟨(fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hp)).hom,
    (fatClassifyingSpaceMap _ (continuous_mapTotal_map continuous_id hi)).hom, ?_, ?_⟩
  · -- The composite is induced by the constant map `c`, which `H` joins to the identity.
    rw [← TopCat.hom_comp, hip, ← TopCat.hom_id, ← hid]
    exact ⟨(fatClassifyingSpaceHomotopy (f₀ := MulActionHom.id G) (f₁ := c)
      (hf₁ := continuous_const) H hH).symm⟩
  · rw [← TopCat.hom_comp, hpi, TopCat.hom_id]

variable (x : X) (hx : x ∈ fixedPoints G X)
  (H : Homotopy (ContinuousMap.id X) (ContinuousMap.const X x))
  (hH : ∀ (s : unitInterval) (g : G) (y : X), H (s, g • y) = g • H (s, y))
  (n : SemiSimplexCategory) (t : SemiSimplexCategory.toTop.obj n)

/-- The homotopy equivalence `B(G ⋉ X) ≃ₕ B(G ⋉ *)` of a contraction onto a fixed point keeps the
labels of each string of composable arrows and forgets its points. -/
theorem fatClassifyingSpaceHomotopyEquivOfContraction_apply_ι
    (F : ComposableArrows (ActionCategory G X) (SemiSimplexCategory.toSimplexCategory.obj n).len) :
    fatClassifyingSpaceHomotopyEquivOfContraction G x hx H hH (fatRealization.ι _ n (F, t)) =
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
    (fatClassifyingSpaceHomotopyEquivOfContraction G x hx H hH).symm
        (fatRealization.ι _ n (F, t)) =
      fatRealization.ι _ n ((nerveEquiv G X _).symm (x, (nerveEquiv G PUnit.{u + 1} _ F).2), t) :=
  (fatClassifyingSpaceMap_ι _ _ n F t).trans <| congrArg (fun F ↦ fatRealization.ι _ n (F, t)) <|
    (nerveEquiv G X _).eq_symm_apply.2 <| Prod.ext
      -- The first point of the image string is the value at that point of the map onto `x`.
      (by simp only [nerveEquiv_apply, Functor.mapComposableArrows_obj_obj, back_map_obj]; rfl)
      (funext fun _ ↦ by simp)

section StarConvex

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]
  [DistribMulAction G E] [SMulCommClass ℝ G E]

variable (G) in
/-- Let `G` act linearly on a real vector space `E`. If a `G`-invariant subset `U` of `E` contains
`0` and is star-convex about `0`, as an invariant ball of an invariant norm is, then the radial
contraction `y ↦ (1 - s) • y` is equivariant, so `B(G ⋉ U) ≃ₕ B(G ⋉ *)`. -/
def fatClassifyingSpaceHomotopyEquivOfStarConvex (U : SubMulAction G E)
    (hU : StarConvex ℝ 0 (U : Set E)) (h0 : (0 : E) ∈ U) :
    fatClassifyingSpace (ActionCategory G U) ≃ₕ
      fatClassifyingSpace (ActionCategory G PUnit.{u + 1}) :=
  fatClassifyingSpaceHomotopyEquivOfContraction G ⟨0, h0⟩ (fun g ↦ Subtype.ext (smul_zero g))
    { toFun p := ⟨(unitInterval.symm p.1 : ℝ) • (p.2 : E),
        hU.smul_mem p.2.2 (unitInterval.symm p.1).2.1 (unitInterval.symm p.1).2.2⟩
      continuous_toFun := Continuous.subtype_mk
        ((continuous_subtype_val.comp (unitInterval.continuous_symm.comp continuous_fst)).smul
          (continuous_subtype_val.comp continuous_snd)) _
      map_zero_left _ := Subtype.ext (by simp)
      map_one_left _ := Subtype.ext (by simp) }
    fun s g y ↦ Subtype.ext (smul_comm (unitInterval.symm s : ℝ) g (y : E))

end StarConvex

end TauCeti.ActionGroupoid
