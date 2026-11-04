/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech.Colimit
public import TauCeti.Topology.Sheaves.Skyscraper

import TauCeti.CategoryTheory.Limits.Lattice

/-!
# Čech cohomology of skyscraper presheaves

Let `M` be an object of a preadditive category `A` with a zero object, and let `M_p` be the
skyscraper presheaf on a topological space `X` with value `M` at a point `p`: its sections over
`V` are `M` if `p ∈ V` and `0` otherwise. This file shows that `M_p` has no Čech cohomology in
positive degrees, and Čech cohomology `M` in degree `0`, both for every family of opens one of
whose members contains `p`, and for the Čech cohomology of `X` defined as a colimit over covers.
No separation axiom is assumed on `X`, and no cover need be finite.

The proof is a direct computation, not an appeal to flasqueness (which would only give the result
for finite covers). Given a family `U`, enlarge each member that contains `p` to all of `X`,
obtaining a family `W`. A finite intersection of members of `U` contains `p` exactly when the
corresponding intersection of members of `W` does, so the restriction maps of `M_p` from the
intersections of `W` to those of `U` are isomorphisms, and the Čech complexes of `M_p` for `U` and
for `W` are isomorphic. The family `W` has `X` itself as a member, so its augmented Čech complex
is exact (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_of_hom`).

On a Riemann surface this is the vanishing `H¹(X, ℂ_p) = 0`, with `H⁰(X, ℂ_p) = ℂ`, that lets the
long exact sequence of `0 ⟶ 𝒪_D ⟶ 𝒪_{D+p} ⟶ ℂ_p ⟶ 0` end in degree one.

## Main results

* `TauCeti.Topology.quasiIso_cechAugmentation_skyscraperPresheaf`: for every family of opens one
  of whose members contains `p`, the augmented Čech complex `0 ⟶ M ⟶ Č⁰(U, M_p) ⟶ Č¹(U, M_p) ⟶ ⋯`
  is exact.
* `TauCeti.Topology.isZero_homology_cechComplex_skyscraperPresheaf`: the Čech cohomology of `M_p`
  for such a family vanishes in every positive degree.
* `TauCeti.Topology.homologyZeroCechComplexSkyscraperPresheafIso`: its degree `0` Čech cohomology
  for such a family is `M`.
* `TauCeti.Topology.isZero_cechCohomology_skyscraperPresheaf`: the Čech cohomology of `M_p` on
  `X` vanishes in every positive degree.
* `TauCeti.Topology.cechCohomologyZeroSkyscraperPresheafIso`: the degree `0` Čech cohomology of
  `M_p` on `X` is `M`, compatibly with the identifications for each cover
  (`TauCeti.Topology.cechCohomologyι_app_cechCohomologyZeroSkyscraperPresheafIso_hom`).

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16, where `H¹(X, ℂ_p) = 0` is used in the proof of the Riemann–Roch theorem.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe w v' u u'

namespace TauCeti.Topology

variable {X : TopCat.{u}} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)] {A : Type u'}
  [Category.{v'} A] [Preadditive A] [HasZeroObject A] (M : A)

section Cover

variable [HasProducts.{w} A] [CategoryWithHomology A] {ι : Type w} (U : ι → Opens X) {i₀ : ι}
  (h₀ : p₀ ∈ U i₀)

include h₀

/-- **Skyscraper presheaves are Čech-acyclic.** For every family `U` of opens one of whose members
contains `p₀`, the augmented Čech complex `0 ⟶ M ⟶ Č⁰(U, M_p₀) ⟶ Č¹(U, M_p₀) ⟶ ⋯` of the
skyscraper presheaf with value `M` at `p₀` is exact. -/
theorem quasiIso_cechAugmentation_skyscraperPresheaf :
    QuasiIso (cechAugmentation U isTerminalTop (skyscraperPresheaf p₀ M)) := by
  classical
  -- enlarge every member containing `p₀` to `⊤`
  let W : ι → Opens X := fun i ↦ if p₀ ∈ U i then ⊤ else U i
  have hW (i : ι) : p₀ ∈ W i ↔ p₀ ∈ U i := by by_cases h : p₀ ∈ U i <;> simp [W, h]
  let φ (i : ι) : U i ⟶ W i := homOfLE (by by_cases h : p₀ ∈ U i <;> simp [W, h])
  have hmem {n : ℕ} (V : ι → Opens X) (a : Fin (n + 1) → ι) :
      p₀ ∈ (∏ᶜ fun j ↦ V (a j) : Opens X) ↔ ∀ j, p₀ ∈ V (a j) := by
    rw [CompleteLattice.finite_product_eq_finset_image_inf, ← SetLike.mem_coe,
      Opens.coe_finset_inf]
    simp
  -- an intersection of members of `U` contains `p₀` iff the intersection in `W` does
  have : IsIso (cechComplexMap (skyscraperPresheaf p₀ M)
      (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)) :=
    isIso_cechComplexMap _ φ fun n a ↦ isIso_skyscraperPresheaf_map p₀ M _ fun h ↦
      (hmem U a).2 fun j ↦ (hW (a j)).1 ((hmem W a).1 h j)
  -- `W` has `⊤` as a member
  have : QuasiIso (cechAugmentation W isTerminalTop (skyscraperPresheaf p₀ M)) :=
    quasiIso_cechAugmentation_of_hom W isTerminalTop _ (i₀ := i₀) (eqToHom (by simp [W, h₀]))
  rw [← cechAugmentation_comp_cechComplexMap isTerminalTop _
    (⟨id, φ⟩ : FormalCoproduct.mk _ U ⟶ FormalCoproduct.mk _ W)]
  infer_instance

/-- The Čech cohomology of a skyscraper presheaf, for a family of opens one of whose members
contains the point, vanishes in every positive degree. -/
theorem isZero_homology_cechComplex_skyscraperPresheaf (n : ℕ) :
    IsZero (((cechComplexFunctor U).obj (skyscraperPresheaf p₀ M)).homology (n + 1)) :=
  (((quasiIso_cechAugmentation_iff U isTerminalTop _).1
    (quasiIso_cechAugmentation_skyscraperPresheaf p₀ M U h₀)).2 n).isZero_homology

/-- The degree `0` Čech cohomology of the skyscraper presheaf with value `M`, for a family of opens
one of whose members contains the point, is `M`: the augmentation identifies it with the global
sections. -/
def homologyZeroCechComplexSkyscraperPresheafIso :
    ((cechComplexFunctor U).obj (skyscraperPresheaf p₀ M)).homology 0 ≅ M :=
  have := quasiIso_cechAugmentation_skyscraperPresheaf p₀ M U h₀
  (asIso (HomologicalComplex.homologyMap
      (cechAugmentation U isTerminalTop (skyscraperPresheaf p₀ M)) 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
      ((skyscraperPresheaf p₀ M).obj (op ⊤)) ≪≫
      eqToIso (ite_eq_left (show p₀ ∈ (⊤ : Opens X) from trivial))

/-- The inverse of the identification of the degree `0` Čech cohomology of a skyscraper presheaf
with `M` is the augmentation, which sends a global section to its restrictions to the members of
the family. -/
@[reassoc]
theorem homologyZeroCechComplexSkyscraperPresheafIso_inv :
    (homologyZeroCechComplexSkyscraperPresheafIso p₀ M U h₀).inv =
      eqToHom (ite_eq_left (show p₀ ∈ (⊤ : Opens X) from trivial)).symm ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          ((skyscraperPresheaf p₀ M).obj (op ⊤))).inv ≫
          HomologicalComplex.homologyMap
            (cechAugmentation U isTerminalTop (skyscraperPresheaf p₀ M)) 0 := by
  simp only [homologyZeroCechComplexSkyscraperPresheafIso, Iso.trans_inv, Iso.symm_inv, asIso_hom]
  exact Category.assoc _ _ _

end Cover

section Colimit

variable [HasProducts.{u} A] [CategoryWithHomology A] [HasColimitsOfShape (PointOpenCover X) A]

/-- **The Čech cohomology of a skyscraper presheaf vanishes in positive degrees.** On any
topological space, the Čech cohomology of the skyscraper presheaf with value `M` at a point
vanishes in every positive degree. -/
theorem isZero_cechCohomology_skyscraperPresheaf (n : ℕ) :
    IsZero ((cechCohomology X A (n + 1)).obj (skyscraperPresheaf p₀ M)) :=
  (IsZero.iff_id_eq_zero _).2 (cechCohomology_obj_hom_ext fun V ↦
    (isZero_homology_cechComplex_skyscraperPresheaf p₀ M V.opens (V.mem_opens p₀) n).eq_of_src
      _ _)

/-- The degree `0` Čech cohomology of the skyscraper presheaf with value `M` at a point is `M`. -/
def cechCohomologyZeroSkyscraperPresheafIso :
    (cechCohomology X A 0).obj (skyscraperPresheaf p₀ M) ≅ M :=
  (TauCeti.CategoryTheory.cechCohomologyZeroIso PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h)
      isTerminalTop (skyscraperPresheaf p₀ M) fun V ↦
        (quasiIso_iff _).1 (quasiIso_cechAugmentation_skyscraperPresheaf p₀ M V.opens
          (V.mem_opens p₀)) 0).symm ≪≫
    eqToIso (ite_eq_left (show p₀ ∈ (⊤ : Opens X) from trivial))

/-- The identification of the degree `0` Čech cohomology of a skyscraper presheaf with `M`
restricts, along the structure map of each point-neighborhood cover `V`, to the identification
for `V`. -/
@[reassoc (attr := simp)]
theorem cechCohomologyι_app_cechCohomologyZeroSkyscraperPresheafIso_hom (V : PointOpenCover X) :
    (cechCohomologyι PointOpenCover.toFormalCoproduct (fun _ _ h ↦ h) 0 V).app
        (skyscraperPresheaf p₀ M) ≫ (cechCohomologyZeroSkyscraperPresheafIso p₀ M).hom =
      (homologyZeroCechComplexSkyscraperPresheafIso p₀ M V.opens (V.mem_opens p₀)).hom := by
  simp only [cechCohomologyZeroSkyscraperPresheafIso, homologyZeroCechComplexSkyscraperPresheafIso,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
  congr 1
  refine (Iso.comp_inv_eq _).2 ?_
  rw [TauCeti.CategoryTheory.cechCohomologyZeroIso_hom _ _ _ _ _ V]
  -- `simp` cannot cancel here: the source of the structure map is the Čech cohomology only up to
  -- unfolding `cechCohomologyDiagram`, so the cancellations are composed as a term
  exact ((Category.assoc _ _ _).trans <| (_ ≫= Iso.hom_inv_id_assoc _ _).trans <|
    Iso.inv_hom_id_assoc _ _).symm

end Colimit

end TauCeti.Topology
