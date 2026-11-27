/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.StalkDifferentials
public import TauCeti.AlgebraicGeometry.VectorBundle.Reduced
import TauCeti.AlgebraicGeometry.VectorBundle.Stalk

/-!
# Uniqueness of locally free quotients of the differentials

Let `X` be a scheme locally of finite presentation over `Spec k` and `q : Ω_{X/k} ⟶ E` a locally
free quotient of rank `d`. At a point `x` of the smooth locus of dimension `d`, `X_sm^{(d)}`, the
stalk map of `q` is a surjection `Ω[𝒪_{X,x}⁄k] → E_x` between free `𝒪_{X,x}`-modules of rank `d`,
hence bijective. If moreover `X` is reduced and `X_sm^{(d)}` is dense, then any two locally free
quotients `q₁ : Ω_{X/k} ⟶ E₁` and `q₂ : Ω_{X/k} ⟶ E₂` of rank `d` have the same kernel: there is a
unique isomorphism `E₁ ≅ E₂` carrying `q₁` to `q₂`. This is
`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.existsUnique_iso_comp_eq` applied to the
stalkwise injectivity on the dense subset `X_sm^{(d)}`.

Both hypotheses pass to open subschemes: the smooth locus of dimension `d` of an open subscheme
`U` is the trace of `X_sm^{(d)}`, hence dense in `U`, and `U` is reduced. So uniqueness holds on
every open subscheme, in particular on the overlaps of an open cover, which is what glueing
locally free quotients along a cover needs.

## Main declarations

* `TauCeti.AlgebraicGeometry.stalkₗ_bijective_of_mem_smoothLocusOfDim`: a locally free quotient
  of rank `d` of `Ω_{X/k}` is bijective on the stalks at the points of `X_sm^{(d)}`;
* `TauCeti.AlgebraicGeometry.existsUnique_iso_comp_eq_of_dense_smoothLocusOfDim`: on a reduced
  scheme with dense `X_sm^{(d)}`, two locally free quotients of rank `d` of `Ω_{X/k}` differ by a
  unique isomorphism of their targets.
* `TauCeti.AlgebraicGeometry.existsUnique_iso_comp_eq_of_isOpenImmersion`: on a reduced scheme
  with dense `X_sm^{(d)}`, uniqueness holds on every open subscheme.

## References

* A. Nobile, *Notes on Nash modification*, Section 2.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {k : Type u} [CommRing k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFinitePresentation (X ↘ Spec (.of k))] {d : ℕ}

/-- **Locally free quotients are bijective on the smooth locus of dimension `d`.** A locally free
quotient `q : Ω_{X/k} ⟶ E` of rank `d` is bijective on the stalk at every point of `X_sm^{(d)}`:
there it is a surjection between free modules of rank `d` over the local ring. -/
theorem stalkₗ_bijective_of_mem_smoothLocusOfDim (E : FiniteLocallyFreeSheaf.FixedRank X d)
    (q : X.relativeDifferentials k ⟶ E.obj.obj) [Epi q] {x : X}
    (hx : x ∈ smoothLocusOfDim k X d) : Function.Bijective (q.stalkₗ x) := by
  obtain ⟨e⟩ := nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim k hx
  let b := Module.finBasisOfFinrankEq _ _
    ((FiniteLocallyFreeSheaf.finrank_stalk E.obj x).trans (E.rank_apply x))
  -- Both stalks are free of rank `d`, so they are isomorphic; a surjection between isomorphic
  -- finitely generated modules is bijective.
  let ψ := (X.relativeDifferentialsStalkEquiv k x) ≪≫ₗ e ≪≫ₗ b.equivFun.symm
  exact OrzechProperty.bijective_of_surjective_of_injective ψ.toLinearMap (q.stalkₗ x)
    ψ.injective (q.stalkₗ_surjective_of_epi x)

/-- **Uniqueness of locally free quotients of the differentials.** On a reduced scheme `X` whose
smooth locus of dimension `d` is dense, two locally free quotients `q₁ : Ω_{X/k} ⟶ E₁` and
`q₂ : Ω_{X/k} ⟶ E₂` of rank `d` have the same kernel: there is a unique isomorphism `E₁ ≅ E₂`
carrying `q₁` to `q₂`. -/
theorem existsUnique_iso_comp_eq_of_dense_smoothLocusOfDim [IsReduced X]
    (hX : Dense (smoothLocusOfDim k X d : Set X)) (E₁ E₂ : FiniteLocallyFreeSheaf.FixedRank X d)
    (q₁ : X.relativeDifferentials k ⟶ E₁.obj.obj) (q₂ : X.relativeDifferentials k ⟶ E₂.obj.obj)
    [Epi q₁] [Epi q₂] : ∃! e : E₁.obj.obj ≅ E₂.obj.obj, q₁ ≫ e.hom = q₂ :=
  FiniteLocallyFreeSheaf.existsUnique_iso_comp_eq hX hX q₁ q₂
    (fun _ hx ↦ (stalkₗ_bijective_of_mem_smoothLocusOfDim E₁ q₁ hx).injective)
    (fun _ hx ↦ (stalkₗ_bijective_of_mem_smoothLocusOfDim E₂ q₂ hx).injective)

/-- **Uniqueness of locally free quotients on open subschemes.** On a reduced scheme `X` whose
smooth locus of dimension `d` is dense, two locally free quotients of rank `d` of `Ω_{U/k}`, for
an open subscheme `f : U ⟶ X` over `Spec k`, differ by a unique isomorphism of their targets.
Applied to the overlaps of an open cover, this makes local quotients agree on overlaps. -/
theorem existsUnique_iso_comp_eq_of_isOpenImmersion [IsReduced X]
    (hX : Dense (smoothLocusOfDim k X d : Set X)) {U : Scheme.{u}} [U.Over (Spec (.of k))]
    [LocallyOfFinitePresentation (U ↘ Spec (.of k))] (f : U ⟶ X) [IsOpenImmersion f]
    [f.IsOver (Spec (.of k))] (E₁ E₂ : FiniteLocallyFreeSheaf.FixedRank U d)
    (q₁ : U.relativeDifferentials k ⟶ E₁.obj.obj) (q₂ : U.relativeDifferentials k ⟶ E₂.obj.obj)
    [Epi q₁] [Epi q₂] : ∃! e : E₁.obj.obj ≅ E₂.obj.obj, q₁ ≫ e.hom = q₂ :=
  have := isReduced_of_isOpenImmersion f
  existsUnique_iso_comp_eq_of_dense_smoothLocusOfDim
    (dense_smoothLocusOfDim_of_isOpenImmersion f hX) E₁ E₂ q₁ q₂

end TauCeti.AlgebraicGeometry
