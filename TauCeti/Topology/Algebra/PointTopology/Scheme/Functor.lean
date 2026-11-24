/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import TauCeti.Topology.Algebra.PointTopology.Scheme.FiberProduct

/-!
# The point functor to topological spaces

Let `R` be a local topological `k`-algebra with continuous multiplication whose units are open
with continuous inversion. Sending a scheme `X` over `Spec k` to its `R`-points `X(R)`, the
morphisms `Spec R ⟶ X` over `Spec k`, with the chart topology
`TauCeti.SchemePointTopology.topology`, and a morphism over `Spec k` to composition with it, is a
functor `TauCeti.SchemePointTopology.pointsFunctor k R` from schemes over `Spec k` to topological
spaces. Its underlying set-valued functor is corepresented by `Spec R` over `Spec k`
(`TauCeti.SchemePointTopology.pointsFunctorForgetCorepresentableBy`).

When `R` is moreover a topological ring, the point functor sends pullback squares of schemes over
`Spec k` to pullback squares of topological spaces
(`TauCeti.SchemePointTopology.isPullback_pointsFunctor_map`), and it sends the terminal scheme
`Spec k` to a point, so it preserves all finite limits
(`TauCeti.SchemePointTopology.preservesFiniteLimits_pointsFunctor`):
fibre products, products and equalizers of schemes over `Spec k` have the corresponding limits of
point spaces as their points. No finiteness or separation hypothesis is imposed on the schemes.

For `k = R = ℂ` with its usual topology, `TauCeti.SchemePointTopology.complexPointsFunctor` is the
functor of classical complex points; on an affine scheme `Spec A` its points are homeomorphic to
`A →ₐ[ℂ] ℂ` with the evaluation topology (`TauCeti.SchemePointTopology.affineHomeomorph`).

## References

* A. Grothendieck, M. Raynaud, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII,
  §1.1, p. 239.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1 and its proof,
  pp. 3–4.
* J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956),
  §2 no. 5, pp. 8–9.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Topology
open scoped TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] [TopologicalSpace R]
  [IsLocalRing R] [IsOpenUnits R]

section Functor

variable [ContinuousMul R]

/-- The `R`-point functor from schemes over `Spec k` to topological spaces. A scheme `X` over
`Spec k` goes to its `R`-points, the morphisms `Spec R ⟶ X` over `Spec k`, with the chart
topology, and a morphism over `Spec k` acts on points by composition. -/
-- `@[expose]` lets the objects reduce to the point spaces `Points X.hom`, so that the morphisms of
-- the functor can be applied to points and characterised by `coe_pointsFunctor_map`.
@[expose] noncomputable def pointsFunctor : Over (Spec (.of k)) ⥤ TopCat.{u} where
  obj X := TopCat.of (Points (R := R) X.hom)
  map g := TopCat.ofHom ⟨map g.left (Over.w g), continuous_map g.left (Over.w g)⟩
  map_id _ := TopCat.ext fun x ↦ map_id x
  map_comp g h := TopCat.ext fun x ↦ (map_map g.left h.left (Over.w g) (Over.w h) x).symm

/-- The points of a scheme over `Spec k` under the point functor, with the chart topology. -/
@[simp]
theorem pointsFunctor_obj (X : Over (Spec (.of k))) :
    (pointsFunctor k R).obj X = TopCat.of (Points (R := R) X.hom) :=
  (rfl)

/-- The point functor acts on a morphism over `Spec k` by composition on points. -/
@[simp]
theorem coe_pointsFunctor_map {X Y : Over (Spec (.of k))} (g : X ⟶ Y) :
    ⇑((pointsFunctor k R).map g) = map (R := R) g.left (Over.w g) :=
  (rfl)

/-- **The `R`-points are corepresented by `Spec R`.** Forgetting the topology, the point functor
is corepresented by `Spec R` over `Spec k`: a point of `X` is a morphism `Spec R ⟶ X` over
`Spec k`, that is, a morphism of schemes over `Spec k`. -/
noncomputable def pointsFunctorForgetCorepresentableBy :
    (pointsFunctor k R ⋙ forget TopCat).CorepresentableBy (Over.mk (Spec.algebraMap k R)) where
  homEquiv {X} :=
    { toFun g := (⟨g.left, Over.w g⟩ : Points (R := R) X.hom)
      invFun x := Over.homMk (U := Over.mk (Spec.algebraMap k R)) (V := X) x.val x.property
      left_inv _ := rfl
      right_inv _ := rfl }
  homEquiv_comp f g := Subtype.ext (map_val (R := R) f.left (Over.w f) ⟨g.left, Over.w g⟩).symm

/-- The corepresenting bijection sends a morphism from `Spec R` over `Spec k` to its underlying
morphism of schemes. -/
-- Not `@[simp]`: `Functor.comp_obj` rewrites the type of `homEquiv`, so no statement of this
-- lemma has its left-hand side in simp normal form.
theorem pointsFunctorForgetCorepresentableBy_homEquiv_apply_val {X : Over (Spec (.of k))}
    (g : Over.mk (Spec.algebraMap k R) ⟶ X) :
    ((pointsFunctorForgetCorepresentableBy k R).homEquiv g :
      Points (R := R) X.hom).val = g.left :=
  (rfl)

/-- The inverse corepresenting bijection sends a point to the morphism over `Spec k` with the same
underlying morphism of schemes. -/
-- Not `@[simp]`, for the reason given at `pointsFunctorForgetCorepresentableBy_homEquiv_apply_val`.
theorem pointsFunctorForgetCorepresentableBy_homEquiv_symm_apply_left {X : Over (Spec (.of k))}
    (x : Points (R := R) X.hom) :
    ((pointsFunctorForgetCorepresentableBy k R).homEquiv.symm x).left = x.val :=
  (rfl)

/-- The points of a scheme whose structure morphism is an isomorphism, such as the terminal scheme
`Spec k` over itself, form a one-point space, which is terminal among topological spaces. -/
noncomputable def isTerminalPointsFunctorObj (X : Over (Spec (.of k))) [IsIso X.hom] :
    IsTerminal ((pointsFunctor k R).obj X) :=
  TopCat.isTerminalPUnit.ofIso
    (TopCat.isoOfHomeo (Homeomorph.homeomorphOfUnique (Points (R := R) X.hom) PUnit)).symm

/-- The point functor sends the terminal scheme `Spec k` over itself to a point. -/
instance preservesTerminal_pointsFunctor :
    PreservesLimit (Functor.empty.{0} (Over (Spec (.of k)))) (pointsFunctor k R) :=
  have : IsIso (Over.mk (𝟙 (Spec (.of k)))).hom := inferInstanceAs (IsIso (𝟙 _))
  preservesLimit_of_preserves_limit_cone Over.mkIdTerminal
    ((isLimitMapConeEmptyConeEquiv _ _).symm (isTerminalPointsFunctorObj k R _))

/-- The point functor preserves terminal objects. -/
instance preservesLimitsOfShape_pempty_pointsFunctor :
    PreservesLimitsOfShape (Discrete.{0} PEmpty) (pointsFunctor k R) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end Functor

section Pullback

variable [IsTopologicalRing R]

/-- **The point functor preserves fibre products.** Over a local topological ring with open units
and continuous inversion on the units, the point functor sends a pullback square of schemes over
`Spec k` to a pullback square of topological spaces. -/
theorem isPullback_pointsFunctor_map {P X Y Z : Over (Spec (.of k))} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    {g₁ : X ⟶ Z} {g₂ : Y ⟶ Z} (h : IsPullback p₁ p₂ g₁ g₂) :
    IsPullback ((pointsFunctor k R).map p₁) ((pointsFunctor k R).map p₂)
      ((pointsFunctor k R).map g₁) ((pointsFunctor k R).map g₂) := by
  have hS : IsPullback p₁.left p₂.left g₁.left g₂.left := h.map (Over.forget _)
  let e := pointsHomeomorphOfIsPullback (R := R) hS (Over.w p₁) (Over.w g₁) (Over.w g₂)
  let hlim := TopCat.pullbackConeIsLimit ((pointsFunctor k R).map g₁) ((pointsFunctor k R).map g₂)
  let c := (h.toCommSq.map (pointsFunctor k R)).cone
  -- The comparison map to the explicit pullback of point spaces is the fibre-product
  -- homeomorphism `e`, so it is an isomorphism of topological spaces.
  have he : ∀ x, (hlim.lift c x).val = (e x).val := fun x ↦ by
    rw [coe_pointsHomeomorphOfIsPullback]
    exact (pointsEquivOfIsPullback_apply_coe hS (Over.w p₁) (Over.w g₁) (Over.w g₂) x).symm
  have : IsIso (hlim.lift c) := by
    rw [TopCat.isIso_iff_isHomeomorph]
    exact (funext fun x ↦ Subtype.ext (he x) : ⇑(hlim.lift c) = ⇑e) ▸ e.isHomeomorph
  exact .of_isLimit' (h.toCommSq.map _) (IsLimit.ofPointIso hlim)

/-- The point functor preserves the chosen fibre product of two morphisms over `Spec k`. -/
instance preservesPullback_pointsFunctor {X Y Z : Over (Spec (.of k))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) (pointsFunctor k R) :=
  (IsPullback.of_hasPullback f g).preservesLimit_cospan_iff.mpr
    (isPullback_pointsFunctor_map k R (IsPullback.of_hasPullback f g))

/-- The point functor preserves all pullbacks of schemes over `Spec k`. -/
instance preservesLimitsOfShape_walkingCospan_pointsFunctor :
    PreservesLimitsOfShape WalkingCospan (pointsFunctor k R) :=
  ⟨fun {K} ↦ preservesLimit_of_iso_diagram _ (diagramIsoCospan K).symm⟩

/-- **The point functor preserves finite limits.** Over a local topological ring with open units
and continuous inversion on the units, the points of a finite limit of schemes over `Spec k` are
the corresponding limit of point spaces. -/
instance preservesFiniteLimits_pointsFunctor : PreservesFiniteLimits (pointsFunctor k R) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end Pullback

/-- The functor of classical complex points: a scheme `X` over `Spec ℂ` goes to its complex points
`X(ℂ)`, the morphisms `Spec ℂ ⟶ X` over `Spec ℂ`, with the classical topology, the chart topology
for `ℂ` with its usual topology. It preserves finite limits. -/
noncomputable abbrev complexPointsFunctor : Over (Spec (.of ℂ)) ⥤ TopCat.{0} :=
  pointsFunctor ℂ ℂ

end TauCeti.SchemePointTopology
