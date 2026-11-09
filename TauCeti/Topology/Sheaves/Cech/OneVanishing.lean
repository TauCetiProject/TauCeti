/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.LongExactSequence
public import TauCeti.Topology.Sheaves.Cech.Colimit

/-!
# Vanishing of degree one Čech cohomology from a left exact sequence

Let `0 ⟶ F ⟶ G ⟶ G'` be an exact sequence of presheaves of modules on a topological space `X`,
with `G` and `G'` sheaves. If `G` has no degree one Čech cohomology and the map `G(X) ⟶ G'(X)` on
global sections is surjective, then `F` has no degree one Čech cohomology either.

This is the argument by which the Dolbeault lemma computes `H¹(X, 𝒪) = 0` on a disc: there `F` is
the structure sheaf `𝒪`, `G = G'` is the fine sheaf `ℰ` of smooth functions, and `G ⟶ G'` is the
Cauchy-Riemann operator. A degree one cocycle of `F` becomes a coboundary in `G`. The image of the
cochain bounding it is a global section of `G'`, which lifts to a global section of `G`; correcting
the cochain by this lift gives a cochain of `F` bounding the cocycle.

The proof applies the long exact Čech cohomology sequence to the short exact sequence
`0 ⟶ F ⟶ G ⟶ im (G ⟶ G') ⟶ 0` of presheaves. The connecting map
`H⁰(im) ⟶ H¹(F)` is surjective, because `H¹(G) = 0`, and zero, because `H⁰(G) ⟶ H⁰(im)` is
surjective. The last surjectivity holds since `H⁰(im) ⟶ H⁰(G')` is injective and the composite
`H⁰(G) ⟶ H⁰(G')` is the surjection `G(X) ⟶ G'(X)` on global sections.

## Main results

* `TauCeti.Topology.epi_cechCohomology_zero_map_of_surjective`: a morphism of sheaves surjective
  on global sections is surjective on degree `0` Čech cohomology.
* `TauCeti.Topology.isZero_cechCohomology_one_of_exact`: the vanishing of `H¹(X, F)`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  proof of Theorem 13.4.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {R : Type u} [Ring R]

/-- A morphism of sheaves of modules which is surjective on global sections induces a surjection
on degree `0` Čech cohomology: under the identifications `cechCohomologyZeroIso` of degree `0`
Čech cohomology with global sections, the induced map is the map on global sections. -/
theorem epi_cechCohomology_zero_map_of_surjective
    {G G' : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (g : G ⟶ G')
    (hsurj : Function.Surjective (g.hom.app (op ⊤))) :
    Epi ((cechCohomology X (ModuleCat.{u} R) 0).map g.hom) := by
  have : Epi (g.hom.app (op ⊤)) := (ModuleCat.epi_iff_surjective _).2 hsurj
  rw [← (Iso.inv_comp_eq _).2 (cechCohomologyZeroIso_hom_naturality _ g)]
  infer_instance

/-- **Degree one Čech cohomology vanishes from a left exact sequence.** Let
`0 ⟶ F ⟶ G ⟶ G'` be an exact sequence of presheaves of modules on `X`, with `G` and `G'`
sheaves, such that `G` has zero degree one Čech cohomology and `G(X) ⟶ G'(X)` is surjective.
Then `F` has zero degree one Čech cohomology. -/
theorem isZero_cechCohomology_one_of_exact (S : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R))
    (hS : S.Exact) [Mono S.f] (hG : Presheaf.IsSheaf (Opens.grothendieckTopology X) S.X₂)
    (hG' : Presheaf.IsSheaf (Opens.grothendieckTopology X) S.X₃)
    (hsurj : Function.Surjective (S.g.app (op ⊤)))
    (h₁ : IsZero ((cechCohomology X (ModuleCat.{u} R) 1).obj S.X₂)) :
    IsZero ((cechCohomology X (ModuleCat.{u} R) 1).obj S.X₁) := by
  let E := PointOpenCover.toFormalCoproduct (X := X)
  have hE : ∀ ⦃U V : PointOpenCover X⦄, U ≤ V → Nonempty (E V ⟶ E U) := fun _ _ h ↦ h
  let H₀ := cechCohomology X (ModuleCat.{u} R) 0
  -- the short exact sequence `0 ⟶ F ⟶ G ⟶ im (G ⟶ G') ⟶ 0`
  let T : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk S.f (Abelian.factorThruImage S.g) (by
      rw [← cancel_mono (Abelian.image.ι S.g), Category.assoc, Abelian.image.fac, S.zero,
        zero_comp])
  have hT : T.ShortExact :=
    { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
        { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := Abelian.image.ι S.g
          comm₂₃ := (Category.id_comp _).trans (Abelian.image.fac S.g).symm } :
        T.Exact ↔ S.Exact).2 hS }
  have hT' (U : PointOpenCover X) : (T.map (cechComplexFunctor U.opens)).ShortExact :=
    hT.map_of_exact (cechComplexFunctor U.opens)
  -- `H⁰(im) ⟶ H⁰(G')` is injective
  let T₂ : ShortComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
    ShortComplex.mk (Abelian.image.ι S.g) (cokernel.π S.g) (by simp)
  have hT₂ : T₂.ShortExact := { exact := ShortComplex.exact_kernel (cokernel.π S.g) }
  have : Mono (H₀.map (Abelian.image.ι S.g)) :=
    TauCeti.CategoryTheory.mono_cechCohomology_map_zero E hE
      (S := T₂) fun U ↦ hT₂.map_of_exact (cechComplexFunctor U.opens)
  have : Epi (H₀.map S.g) :=
    epi_cechCohomology_zero_map_of_surjective (G := ⟨S.X₂, hG⟩) (G' := ⟨S.X₃, hG'⟩) ⟨S.g⟩ hsurj
  have hfac : H₀.map S.g = H₀.map (Abelian.factorThruImage S.g) ≫
      H₀.map (Abelian.image.ι S.g) := by
    rw [← Functor.map_comp, Abelian.image.fac]
  have : Epi (H₀.map (Abelian.factorThruImage S.g) ≫ H₀.map (Abelian.image.ι S.g)) :=
    hfac ▸ inferInstance
  have : Epi (H₀.map (Abelian.image.ι S.g)) := epi_of_epi (H₀.map (Abelian.factorThruImage S.g)) _
  have : IsIso (H₀.map (Abelian.image.ι S.g)) := isIso_of_mono_of_epi _
  have hepi : Epi (H₀.map T.g) := by
    have : Epi ((H₀.map (Abelian.factorThruImage S.g) ≫ H₀.map (Abelian.image.ι S.g)) ≫
        inv (H₀.map (Abelian.image.ι S.g))) := epi_comp _ _
    simpa using this
  -- the connecting map `H⁰(im) ⟶ H¹(F)` is zero and surjective
  let δ := TauCeti.CategoryTheory.cechCohomologyδ E hE hT' 0
  have hδ₀ : δ = 0 := by
    rw [← cancel_epi (H₀.map T.g), comp_zero]
    exact TauCeti.CategoryTheory.cechCohomology_comp_δ E hE hT' 0
  have hδ : Epi δ :=
    (ShortComplex.exact_iff_epi _ (h₁.eq_zero_of_tgt _)).1
      (TauCeti.CategoryTheory.cechCohomology_exact₁ E hE hT' 0)
  exact IsZero.of_epi_eq_zero δ hδ₀

end TauCeti.Topology
