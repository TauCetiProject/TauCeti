/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.LocallyFreeQuotient
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
unique isomorphism `E₁ ≅ E₂` carrying `q₁` to `q₂`. The composite of the kernel of `q₁` with `q₂`
vanishes on the stalks at the dense subset `X_sm^{(d)}`, and a morphism into a finite locally free
sheaf on a reduced scheme vanishing there is zero
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.existsUnique_iso_comp_eq`).

## Main declarations

* `TauCeti.AlgebraicGeometry.stalkₗ_bijective_of_mem_smoothLocusOfDim`: a locally free quotient
  of rank `d` of `Ω_{X/k}` is bijective on the stalks at the points of `X_sm^{(d)}`;
* `TauCeti.AlgebraicGeometry.existsUnique_iso_comp_eq_of_dense_smoothLocusOfDim`: on a reduced
  scheme with dense `X_sm^{(d)}`, two locally free quotients of rank `d` of `Ω_{X/k}` differ by a
  unique isomorphism of their targets.

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
  refine ⟨?_, q.stalkₗ_surjective_of_epi x⟩
  obtain ⟨e⟩ := nonempty_linearEquiv_kaehlerDifferential_stalk_of_mem_smoothLocusOfDim k hx
  let b := Module.finBasisOfFinrankEq _ _
    ((FiniteLocallyFreeSheaf.finrank_stalk E.obj x).trans (E.rank_apply x))
  -- Transported to `𝒪_{X,x}^d → 𝒪_{X,x}^d`, the stalk map is a surjective endomorphism of a
  -- finitely generated module, hence injective.
  let φ := e.symm ≪≫ₗ (X.relativeDifferentialsStalkEquiv k x).symm
  let g := b.equivFun.toLinearMap ∘ₗ q.stalkₗ x ∘ₗ φ.toLinearMap
  have hg : Function.Surjective g :=
    b.equivFun.surjective.comp ((q.stalkₗ_surjective_of_epi x).comp φ.surjective)
  have hinj := OrzechProperty.injective_of_surjective_endomorphism g hg
  intro m₁ m₂ h
  have h' : g (φ.symm m₁) = g (φ.symm m₂) := by
    simp [g, h]
  simpa using hinj h'

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

end TauCeti.AlgebraicGeometry
