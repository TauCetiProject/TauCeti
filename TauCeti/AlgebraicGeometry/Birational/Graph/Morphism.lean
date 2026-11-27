/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Birational.Graph.Basic

/-!
# The graph of a morphism

For a rational map `f : X ⤏ Y` from a reduced scheme to a separated scheme which is defined
everywhere, `f.domain = ⊤`, the first projection `π_1 : Γ_f → X` of the graph is an isomorphism,
and the second projection is `π_2 = g ∘ π_1` for the morphism `g = f.toHom` representing `f`. So
`Γ_f ⊆ X × Y` is the image of the graph morphism `(𝟙, g) : X → X × Y`.

The rational map of a morphism `g : X ⟶ Y` is defined everywhere
(`AlgebraicGeometry.Scheme.Hom.domain_toRationalMap`) and `toHom` gives back `g`
(`AlgebraicGeometry.Scheme.Hom.toHom_toRationalMap`), so the above applies to the graph of `g`.
For `g = 𝟙` the graph is the diagonal of `X`.

## Main results

* `AlgebraicGeometry.Scheme.RationalMap.isIso_graphFst_of_domain_eq_top`,
  `AlgebraicGeometry.Scheme.RationalMap.graphSnd_eq_graphFst_comp_toHom`,
  `AlgebraicGeometry.Scheme.RationalMap.graphι_eq_graphFst_comp_lift`: for `f` defined
  everywhere, `π_1` is an isomorphism, `π_2 = f.toHom ∘ π_1`, and the closed immersion of the
  graph is `(𝟙, f.toHom) ∘ π_1`.
* `AlgebraicGeometry.Scheme.Hom.graphSnd_toRationalMap`: for a morphism `g`, `π_2 = g ∘ π_1`.
* `AlgebraicGeometry.Scheme.RationalMap.graphι_id`: the graph of the identity is the diagonal.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} [IsReduced X] [Y.IsSeparated]

namespace RationalMap

variable (f : X ⤏ Y)

/-- **The first projection of the graph of a rational map defined everywhere is an
isomorphism**, for `X` reduced and `Y` separated. -/
theorem isIso_graphFst_of_domain_eq_top (hf : f.domain = ⊤) : IsIso (graphFst f) := by
  have : QuasiCompact f.domain.ι := by
    rw [hf, ← Scheme.topIso_hom]
    infer_instance
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := .isomorphisms _) (fun _ : Unit ↦ f.domain)
    (by simp [hf]) fun _ ↦ isIso_graphFst_restrict f

/-- **The second projection of the graph of a rational map defined everywhere** is the first
projection followed by the morphism `f.toHom` representing `f`: `π_2 = g ∘ π_1`. -/
theorem graphSnd_eq_graphFst_comp_toHom (hf : f.domain = ⊤) :
    graphSnd f = graphFst f ≫ f.toHom hf := by
  have := isIso_graphFst_of_domain_eq_top f hf
  -- both sides agree on the domain of the representative, embedded through `π_1⁻¹`
  have hι : f.representative.domain.ι ≫ inv (graphFst f) = toGraph f := by
    rw [IsIso.comp_inv_eq, TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureFst]
  rw [← cancel_epi (inv (graphFst f)), IsIso.inv_hom_id_assoc]
  have := Opens.isDominant_ι f.representative.dense_domain
  refine ext_of_isDominant_of_isSeparated (terminal.from Y) (terminal.hom_ext _ _)
    f.representative.domain.ι ?_
  rw [representative_domain_ι_toHom, ← Category.assoc, hι,
    TauCeti.AlgebraicGeometry.toGraphClosure_graphClosureSnd]

/-- **The graph of a rational map defined everywhere is the image of the graph morphism**: the
closed immersion `Γ_f → X × Y` is `(𝟙, f.toHom) ∘ π_1`. -/
theorem graphι_eq_graphFst_comp_lift (hf : f.domain = ⊤) :
    graphι f = graphFst f ≫ pullback.lift (𝟙 X) (f.toHom hf) (terminal.hom_ext _ _) := by
  apply pullback.hom_ext
  · simp [graphFst, TauCeti.AlgebraicGeometry.graphClosureFst_def]
  · rw [Category.assoc, pullback.lift_snd, ← graphSnd_eq_graphFst_comp_toHom f hf]
    simp [graphSnd, TauCeti.AlgebraicGeometry.graphClosureSnd_def]

end RationalMap

/-- **The first projection of the graph of a morphism is an isomorphism.** -/
instance Hom.isIso_graphFst_toRationalMap (g : X ⟶ Y) :
    IsIso (RationalMap.graphFst g.toRationalMap) :=
  RationalMap.isIso_graphFst_of_domain_eq_top _ g.domain_toRationalMap

/-- **The graph of a morphism**: its second projection is the first followed by the morphism,
`π_2 = g ∘ π_1`, so `π_2 ∘ π_1⁻¹ = g`. -/
theorem Hom.graphSnd_toRationalMap (g : X ⟶ Y) :
    RationalMap.graphSnd g.toRationalMap = RationalMap.graphFst g.toRationalMap ≫ g := by
  rw [RationalMap.graphSnd_eq_graphFst_comp_toHom _ g.domain_toRationalMap, toHom_toRationalMap]

omit [Y.IsSeparated] in
/-- **The graph of the identity is the diagonal**: for `X` reduced and separated, the closed
immersion of `Γ_{id}` into `X × X` is the diagonal after the isomorphism `π_1`. -/
theorem RationalMap.graphι_id [X.IsSeparated] :
    graphι (RationalMap.id X) = graphFst (RationalMap.id X) ≫ pullback.diagonal _ := by
  rw [graphι_eq_graphFst_comp_lift _ (Hom.domain_toRationalMap (𝟙 X))]
  congr 1
  apply pullback.hom_ext <;> simp

end AlgebraicGeometry.Scheme
