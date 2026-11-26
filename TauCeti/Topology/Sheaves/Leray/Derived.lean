/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cohomology.Cech
import Mathlib.CategoryTheory.Abelian.ShortExact
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Exactness
import TauCeti.CategoryTheory.Limits.Lattice
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Leray covers compute Čech and derived cohomology on compact Hausdorff spaces

Let `X` be a compact normal space, for instance a compact Hausdorff space, and let `F` be a sheaf
of modules over a ring `R` on `X`. A finite open cover `U` of `X` is a *Leray cover* for `F` if
the underlying abelian sheaf of `F` has no cohomology in positive degrees on any nonempty finite
intersection of members of `U`. For such a cover, the canonical map
`TauCeti.Topology.toCechCohomology` from the cohomology `Hⁿ(U, F)` of the Čech complex of `U` to
the cover-colimit Čech cohomology `Hⁿ(X, F)` is an isomorphism in every degree
(`TauCeti.Topology.isIso_toCechCohomology_app_of_leray`). Composing with the comparison
`TauCeti.Topology.cechCohomologyIsoRightDerivedΓ` of cover-colimit Čech cohomology with the right
derived functors of global sections gives `Hⁿ(U, F) ≅ RⁿΓ(F)` as `R`-modules, for a commutative
ring `R` (`TauCeti.Topology.homologyCechComplexIsoRightDerivedΓ`).

The comparison is the canonical map, not merely an abstract isomorphism, so it is natural in the
sheaf. The proof is by dimension shifting along the embedding
`0 ⟶ F ⟶ G ⟶ Q ⟶ 0` of `F` into its flasque Godement sheaf `G`, for all Leray sheaves at once.

* On every finite intersection `V` of members of `U`, the sequence of sections
  `0 ⟶ F(V) ⟶ G(V) ⟶ Q(V) ⟶ 0` is exact, since `H¹(V, F) = 0`, so the Čech complexes for `U`
  form a short exact sequence; and `Q` is again Leray, since `Hᵏ(V, Q) ≅ Hᵏ⁺¹(V, F)` for `k ≥ 1`.
* The flasque sheaf `G` has no higher Čech cohomology, neither for the finite cover `U` nor in the
  colimit, so the connecting maps identify `Hⁿ⁺¹(-, F)` with `Hⁿ(-, Q)` for `n ≥ 1`, and in degree
  `1` with the cokernel of `H⁰(-, G) ⟶ H⁰(-, Q)`.
* The fixed-cover and cover-colimit connecting maps are compatible through `toCechCohomology`
  (`CategoryTheory.ShortComplex.ShortExact.δ_comp_toCechCohomology_app`), and in degree `0`
  `toCechCohomology` is an isomorphism for every cover
  (`TauCeti.Topology.isIso_toCechCohomology_app_zero`).

## Main results

* `TauCeti.Topology.isIso_toCechCohomology_app_of_leray`: for a finite Leray cover `U`, the map
  `Hⁿ(U, F) ⟶ Hⁿ(X, F)` to cover-colimit Čech cohomology is an isomorphism.
* `TauCeti.Topology.homologyCechComplexIsoRightDerivedΓ`: for a finite Leray cover `U`,
  `Hⁿ(U, F) ≅ RⁿΓ(F)`, with its naturality in `F`
  (`TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoRightDerivedΓ_hom`) and its
  description in degree `0` through the augmentation of the Čech complex
  (`TauCeti.Topology.homologyMap_cechAugmentation_comp_homologyCechComplexIsoRightDerivedΓ_hom`).

## References

* The Stacks Project, Cohomology of Sheaves, Lemma 20.11.6 (tag 01ET), for a cover whose finite
  intersections are acyclic, and Lemma 20.16.2 (tag 09V2), for Čech cohomology of sheaves on
  compact Hausdorff spaces.
* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.11.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} {U : ι → Opens X}

section Ring

variable {R : Type u} [Ring R]

variable (U) in
/-- The Leray condition: the underlying abelian sheaf of `F` has no cohomology in positive degrees
on any nonempty finite intersection of members of the cover. -/
private def IsLeray (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) : Prop :=
  ∀ s : Finset ι, s.Nonempty → ∀ k,
    Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
      (k + 1) (s.inf U))

/-- The embedding `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` of `F` into its Godement sheaf `G`, with cokernel `Q`. -/
private abbrev godementSeq (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :=
  ShortComplex.mk ((toGodement (ModuleCat.{u} R) X).app F) (cokernel.π _) (cokernel.condition _)

private lemma godementSeq_shortExact (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (godementSeq F).ShortExact :=
  { exact := ShortComplex.exact_cokernel _ }

/-- The underlying abelian sheaf of a Godement sheaf is flasque, so it has no cohomology in
positive degrees. -/
private lemma subsingleton_H'_godement (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (V : Opens X) (k : ℕ) :
    Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj
      ((godement (ModuleCat.{u} R) X).obj F)).H' (k + 1) V) :=
  have : TopCat.Presheaf.IsFlasque ((sheafCompose _
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj
        ((godement (ModuleCat.{u} R) X).obj F)).obj :=
    TopCat.Presheaf.isFlasque_comp ((godement (ModuleCat.{u} R) X).obj F).obj
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  inferInstance

/-- On the finite products of members of the cover, the sections of `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` are
short exact for a Leray sheaf `F`, so its Čech complexes form a short exact sequence. -/
private lemma shortExact_cechComplex_godementSeq
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (hF : IsLeray U F) :
    (((godementSeq F).map (sheafToPresheaf _ _)).map (cechComplexFunctor U)).ShortExact :=
  shortExact_map_cechComplexFunctor U _ fun _ a ↦
    -- exactness of sections is detected on the underlying abelian groups
    ShortExact.reflects_shortExact_of_faithful (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (_root_.CategoryTheory.Sheaf.H'.shortExact_map_sheafSections
        (Sheaf.shortExact_map_sheafCompose_forget₂_moduleCat (godementSeq_shortExact F)) _
        -- the product of the members `U (a j)` is their intersection
        (CompleteLattice.finite_product_of_forall_finset_inf
          (p := fun W ↦ Subsingleton (((sheafCompose _
            (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H' 1 W)) U
          (fun s hs ↦ hF s hs 0) a))

/-- The cokernel `Q` of the Godement embedding of a Leray sheaf is again Leray. -/
private lemma isLeray_cokernel {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (hF : IsLeray U F) : IsLeray U (cokernel ((toGodement (ModuleCat.{u} R) X).app F)) :=
  fun s hs k ↦ _root_.CategoryTheory.Sheaf.H'.subsingleton_X₃
    (Sheaf.shortExact_map_sheafCompose_forget₂_moduleCat (godementSeq_shortExact F)) _ (k + 1)
    (subsingleton_H'_godement F _ k) (hF s hs (k + 1))

variable [CompactSpace X] [NormalSpace X]

/-- In degree one, `toCechCohomology` is an isomorphism for a Leray sheaf: on both sides, the
connecting map of `0 ⟶ F ⟶ G ⟶ Q ⟶ 0` identifies degree one cohomology of `F` with the cokernel of
the degree zero map induced by `G ⟶ Q`, on which `toCechCohomology` is an isomorphism. -/
private lemma isIso_toCechCohomology_app_one [Finite ι] (hU : IsOpenCover U)
    {F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)} (hF : IsLeray U F) :
    IsIso ((toCechCohomology (ModuleCat.{u} R) 1 U hU).app F.obj) := by
  let hS := godementSeq_shortExact F
  let hSU := shortExact_cechComplex_godementSeq hF
  have := hSU.epi_δ 0 1 rfl
    (isZero_homology_cechComplex_succ_of_isFlasque U hU.iSup_eq_top
      ((godement (ModuleCat.{u} R) X).obj F) 0)
  have := hS.epi_cechCohomologyδ_zero_of_isFlasque
  have := isIso_toCechCohomology_app_zero (ModuleCat.{u} R) U hU (godementSeq F).X₂
  have := isIso_toCechCohomology_app_zero (ModuleCat.{u} R) U hU (godementSeq F).X₃
  have hsq := hS.δ_comp_toCechCohomology_app U hU hSU 0
  -- the map from the fixed-cover sequence `H⁰(U, G) ⟶ H⁰(U, Q) ⟶ H¹(U, F)` to the colimit one
  let φ : ShortComplex.mk _ _ (hSU.comp_δ 0 1 rfl) ⟶
      ShortComplex.mk _ _ (hS.cechCohomology_comp_δ 0) :=
    { τ₁ := (toCechCohomology (ModuleCat.{u} R) 0 U hU).app (godementSeq F).X₂.obj
      τ₂ := (toCechCohomology (ModuleCat.{u} R) 0 U hU).app (godementSeq F).X₃.obj
      τ₃ := (toCechCohomology (ModuleCat.{u} R) 1 U hU).app F.obj
      comm₁₂ := ((toCechCohomology (ModuleCat.{u} R) 0 U hU).naturality (godementSeq F).g.hom).symm
      comm₂₃ := hsq.symm }
  have : Mono φ.τ₃ := ShortComplex.mono_of_epi_of_epi_of_mono φ (hS.cechCohomology_exact₃ 0)
    (inferInstanceAs (Epi (hSU.δ 0 1 rfl))) inferInstance inferInstance
  have : Epi φ.τ₃ := by
    have : Epi (hSU.δ 0 1 rfl ≫ φ.τ₃) := by
      rw [show hSU.δ 0 1 rfl ≫ φ.τ₃ = φ.τ₂ ≫ hS.cechCohomologyδ 0 from hsq]
      infer_instance
    exact epi_of_epi (hSU.δ 0 1 rfl) φ.τ₃
  exact isIso_of_mono_of_epi φ.τ₃

/-- The induction behind `TauCeti.Topology.isIso_toCechCohomology_app_of_leray`, for all Leray
sheaves at once: degrees `0` and `1` are `isIso_toCechCohomology_app_zero` and
`isIso_toCechCohomology_app_one`, and degree `n + 2` is identified with degree `n + 1` of the
cokernel of the Godement embedding by the connecting maps. -/
private lemma isIso_toCechCohomology_app_aux [Finite ι] (hU : IsOpenCover U) :
    ∀ (n : ℕ) (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)), IsLeray U F →
      IsIso ((toCechCohomology (ModuleCat.{u} R) n U hU).app F.obj)
  | 0, F, _ => isIso_toCechCohomology_app_zero (ModuleCat.{u} R) U hU F
  | 1, _, hF => isIso_toCechCohomology_app_one hU hF
  | n + 2, F, hF => by
    let hS := godementSeq_shortExact F
    let hSU := shortExact_cechComplex_godementSeq hF
    have := hSU.isIso_δ (n + 1) (n + 1 + 1) rfl
      (isZero_homology_cechComplex_succ_of_isFlasque U hU.iSup_eq_top
        ((godement (ModuleCat.{u} R) X).obj F) n)
      (isZero_homology_cechComplex_succ_of_isFlasque U hU.iSup_eq_top
        ((godement (ModuleCat.{u} R) X).obj F) (n + 1))
    have := hS.isIso_cechCohomologyδ_succ_of_isFlasque n
    have := isIso_toCechCohomology_app_aux hU (n + 1) _ (isLeray_cokernel hF)
    have : IsIso ((toCechCohomology (ModuleCat.{u} R) (n + 1) U hU).app (godementSeq F).X₃.obj ≫
        hS.cechCohomologyδ (n + 1)) := inferInstance
    rw [← hS.δ_comp_toCechCohomology_app U hU hSU (n + 1)] at this
    -- `this` is stated for `(godementSeq F).X₁`, which instance search does not unfold to `F`
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (hSU.δ (n + 1) (n + 1 + 1) rfl)
      ((toCechCohomology (ModuleCat.{u} R) (n + 1 + 1) U hU).app F.obj) _ this

/-- **Leray covers compute Čech cohomology on compact Hausdorff spaces.** Let `X` be a compact
normal space, `F` a sheaf of modules on `X`, and `U` a finite open cover of `X` such that the
underlying abelian sheaf of `F` has no cohomology in positive degrees on any nonempty finite
intersection of members of `U`. Then the canonical map `Hⁿ(U, F) ⟶ Hⁿ(X, F)` from the cohomology of
the Čech complex of `U` to the cover-colimit Čech cohomology is an isomorphism for every `n`. -/
theorem isIso_toCechCohomology_app_of_leray [Finite ι] (hU : IsOpenCover U)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
        (k + 1) (s.inf U))) (n : ℕ) :
    IsIso ((toCechCohomology (ModuleCat.{u} R) n U hU).app F.obj) :=
  isIso_toCechCohomology_app_aux hU n F hF

end Ring

section Derived

variable [CompactSpace X] [NormalSpace X] {R : Type u} [CommRing R]

/-- **Leray covers compute derived global sections on compact Hausdorff spaces.** Let `U` be a
finite open cover of a compact normal space `X` such that the underlying abelian sheaf of the sheaf
of `R`-modules `F` has no cohomology in positive degrees on any nonempty finite intersection of
members of `U`. Then the cohomology `Hⁿ(U, F)` of the Čech complex of `U` is isomorphic, as an
`R`-module, to the right derived functor `RⁿΓ(F)` of global sections: the canonical map to
cover-colimit Čech cohomology (`TauCeti.Topology.isIso_toCechCohomology_app_of_leray`) followed by
`TauCeti.Topology.cechCohomologyIsoRightDerivedΓ`. -/
def homologyCechComplexIsoRightDerivedΓ [Finite ι] (hU : IsOpenCover U)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
        (k + 1) (s.inf U))) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology n ≅
      ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).obj F :=
  have := isIso_toCechCohomology_app_of_leray hU F hF n
  asIso ((toCechCohomology (ModuleCat.{u} R) n U hU).app F.obj) ≪≫
    (cechCohomologyIsoRightDerivedΓ n).app F

/-- The comparison `homologyCechComplexIsoRightDerivedΓ` is the canonical map to cover-colimit
Čech cohomology followed by `TauCeti.Topology.cechCohomologyIsoRightDerivedΓ`. -/
@[simp]
lemma homologyCechComplexIsoRightDerivedΓ_hom [Finite ι] (hU : IsOpenCover U)
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
        (k + 1) (s.inf U))) (n : ℕ) :
    (homologyCechComplexIsoRightDerivedΓ hU F hF n).hom =
      (toCechCohomology (ModuleCat.{u} R) n U hU).app F.obj ≫
        (cechCohomologyIsoRightDerivedΓ n).hom.app F := by
  rw [homologyCechComplexIsoRightDerivedΓ, Iso.trans_hom, asIso_hom, Iso.app_hom]

/-- **Degree-zero normalization of the Leray comparison.** In degree `0` the comparison
`H⁰(U, F) ≅ R⁰Γ(F)` matches the descriptions of both sides by global sections: preceded by the map
`Γ(F) ⟶ H⁰(U, F)` induced by the augmentation of the Čech complex of `U`, it is Mathlib's
canonical map `Γ(F) ⟶ R⁰Γ(F)`. -/
@[reassoc]
theorem homologyMap_cechAugmentation_comp_homologyCechComplexIsoRightDerivedΓ_hom [Finite ι]
    (hU : IsOpenCover U) (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
        (k + 1) (s.inf U))) :
    (Sheaf.ΓNatIsoSheafSections _ _ isTerminalTop).hom.app F ≫
        (HomologicalComplex.singleObjHomologySelfIso _ 0 (F.obj.obj (Opposite.op ⊤))).inv ≫
          HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop F.obj) 0 ≫
            (homologyCechComplexIsoRightDerivedΓ hU F hF 0).hom =
      (Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).toRightDerivedZero.app F := by
  rw [homologyCechComplexIsoRightDerivedΓ_hom,
    ← sectionsIsoCechZero_hom_comp_cechCohomologyIsoRightDerivedΓ_hom_app, sectionsIsoCechZero_hom,
    cechCohomologyZeroIso_hom_eq_toCechCohomology _ U hU]
  simp only [Category.assoc]

/-- **Naturality of the Leray comparison.** The isomorphism `Hⁿ(U, F) ≅ RⁿΓ(F)` commutes with the
maps induced by a morphism `F ⟶ G` of sheaves of modules for which `U` is a Leray cover. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoRightDerivedΓ_hom [Finite ι] (hU : IsOpenCover U)
    {F G : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)}
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).H'
        (k + 1) (s.inf U)))
    (hG : ∀ s : Finset ι, s.Nonempty → ∀ k,
      Subsingleton (((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj G).H'
        (k + 1) (s.inf U)))
    (f : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
        (homologyCechComplexIsoRightDerivedΓ hU G hG n).hom =
      (homologyCechComplexIsoRightDerivedΓ hU F hF n).hom ≫
        ((Sheaf.Γ (Opens.grothendieckTopology X) (ModuleCat.{u} R)).rightDerived n).map f := by
  rw [homologyCechComplexIsoRightDerivedΓ_hom, homologyCechComplexIsoRightDerivedΓ_hom,
    Category.assoc, ← (cechCohomologyIsoRightDerivedΓ n).hom.naturality f]
  exact (toCechCohomology (ModuleCat.{u} R) n U hU).naturality_assoc f.hom _

end Derived

end TauCeti.Topology
