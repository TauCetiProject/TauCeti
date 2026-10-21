/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Cech
public import TauCeti.Topology.Sheaves.Flasque

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Data.Fintype.Lattice
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Exact
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Leray's theorem: Čech cohomology of a Leray cover computes sheaf cohomology

Let `F` be a sheaf of abelian groups on a topological space `X` and let `U` be a finite open cover
of `X` such that `F` has no cohomology in positive degrees on any nonempty finite intersection of
members of `U` (a *Leray cover* for `F`). Then the Čech cohomology `Hⁿ(U, F)`, the cohomology of
the Čech complex `Č(U, F)`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)` in every degree.

The proof is by dimension shifting. Embed `F` into an injective sheaf `I`, with cokernel `Q`.

* On every finite intersection `V` of members of `U`, the sequence of sections
  `0 ⟶ F(V) ⟶ I(V) ⟶ Q(V) ⟶ 0` is exact, because `H¹(V, F) = 0`; so the Čech complexes form a
  short exact sequence `0 ⟶ Č(U, F) ⟶ Č(U, I) ⟶ Č(U, Q) ⟶ 0`.
* `I` is flasque, so `Č(U, I)` has no cohomology in positive degrees
  (`TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`), and neither has `I` sheaf cohomology.
  The two long exact sequences then give `Hⁿ⁺¹(U, F) ≅ Hⁿ(U, Q)` and `Hⁿ⁺¹(X, F) ≅ Hⁿ(X, Q)` for
  `n ≥ 1`, while in degree one both `H¹(U, F)` and `H¹(X, F)` are the cokernel of
  `I(X) ⟶ Q(X)`, since `H⁰(U, -)` and `H⁰(X, -)` are both global sections.
* `Q` is again acyclic on the finite intersections, as `Hᵏ(V, Q) ≅ Hᵏ⁺¹(V, F)` for `k ≥ 1`.

Induction on the degree, for all sheaves at once, concludes. The comparison is defined by this
recursion, using a fixed choice of the injective sheaf `I` for each `F`. It is natural in `F`: a
morphism `F ⟶ G` extends to a morphism of the chosen sequences
(`TauCeti.injectiveCokernelSequenceMap`), and the connecting maps of both long exact sequences
are natural. In particular the comparison commutes with every endomorphism of `F`, so it respects
any module structure on both sides that is induced by an action of a ring on `F`.

## Main results

* `TauCeti.Topology.homologyCechComplexIsoH`: for a finite Leray cover `U` of `X`,
  `Hⁿ(U, F) ≅ Hⁿ(X, F)` for every `n`;
* `TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom`: this isomorphism is natural
  in `F`;
* `TauCeti.Topology.homologyCechComplexIsoH_zero`: in degree `0` it is the identification of both
  groups with the global sections.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.11, and the proof of Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)

/-- The Leray condition in the form used by the induction: `F` has no cohomology in positive
degrees on the finite products `U (a 0) × ⋯ × U (a m)` of members of the cover. -/
private def IsLerayProd (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ), Subsingleton (F.H' (k + 1) (∏ᶜ fun j ↦ U (a j)))

variable {U}

/-- The Leray condition on nonempty finite intersections implies it on finite products. -/
private lemma isLerayProd_of_finset {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) :
    IsLerayProd U F := by
  classical
  intro m a k
  -- the product of the members `U (a j)` is their intersection
  have h : (∏ᶜ fun j ↦ U (a j)) = (Finset.univ.image a).inf U := by
    rw [Finset.inf_image, Finset.inf_univ_eq_iInf]
    exact (CompleteLattice.finite_limit_eq_finset_univ_inf _).trans <| by
      rw [Finset.inf_univ_eq_iInf]; exact discreteEquiv.iInf_comp (g := fun j ↦ U (a j))
  rw [h]
  exact hF _ (Finset.univ_nonempty.image a) k

variable (U) in
/-- The sequence of Čech complexes of `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` for the cover `U`. -/
private abbrev cechSeq (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  -- this is `((injectiveCokernelSequence F).map (sheafToPresheaf _ _)).map (cechComplexFunctor U)`,
  -- restated so that its objects are syntactically the Čech complexes of `F`, `I` and `Q`
  ShortComplex.mk ((cechComplexFunctor U).map (Injective.ι F).hom)
    ((cechComplexFunctor U).map (cokernel.π (Injective.ι F)).hom)
    (((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})).map
      (cechComplexFunctor U)).zero

/-- On the finite products of members of the cover, the sections of `0 ⟶ F ⟶ I ⟶ Q ⟶ 0` are
short exact for a Leray sheaf `F`, so its Čech complexes form a short exact sequence. -/
private lemma cechSeq_shortExact {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : IsLerayProd U F) : (cechSeq U F).ShortExact :=
  shortExact_map_cechComplexFunctor U
    ((injectiveCokernelSequence F).map (sheafToPresheaf _ AddCommGrpCat.{u})) fun m a ↦
      _root_.CategoryTheory.Sheaf.H'.shortExact_map_sheafSections
        (injectiveCokernelSequence_shortExact F) _ (hF m a 0)

/-- The cokernel `Q` of the chosen injective embedding of a Leray sheaf is again Leray. -/
private lemma isLerayProd_cokernel {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : IsLerayProd U F) : IsLerayProd U (cokernel (Injective.ι F)) :=
  fun m a k ↦ _root_.CategoryTheory.Sheaf.H'.subsingleton_X₃
    (injectiveCokernelSequence_shortExact F) _ (k + 1) inferInstance (hF m a (k + 1))

variable (U) in
/-- A morphism `F ⟶ G` induces a morphism of the sequences of Čech complexes of the chosen
injective cokernel sequences, through `TauCeti.injectiveCokernelSequenceMap`. -/
private def cechSeqMap {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) : cechSeq U F ⟶ cechSeq U G where
  τ₁ := (cechComplexFunctor U).map f.hom
  τ₂ := (cechComplexFunctor U).map (injectiveCokernelSequenceMap f).τ₂.hom
  τ₃ := (cechComplexFunctor U).map (injectiveCokernelSequenceMap f).τ₃.hom
  comm₁₂ := by
    simp only [injectiveCokernelSequenceMap_τ₂, ← Functor.map_comp, ← InducedCategory.comp_hom,
      Injective.comp_factorThru]
  comm₂₃ := by
    simp only [injectiveCokernelSequenceMap_τ₂, injectiveCokernelSequenceMap_τ₃,
      ← Functor.map_comp, ← InducedCategory.comp_hom, cokernel.π_desc]

variable (U)

include hU

/-- The injective sheaf `Injective.under F` is flasque, so it has no Čech cohomology in positive
degrees for a finite cover. -/
private lemma isZero_homology_cechComplex_under [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (k : ℕ) :
    IsZero (((cechComplexFunctor U).obj (Injective.under F).obj).homology (k + 1)) := by
  have : TopCat.Presheaf.IsFlasque (TopCat.Sheaf.presheaf (Injective.under F)) :=
    isFlasque_of_injective (Injective.under F)
  have : QuasiIso (cechAugmentation U isTerminalTop (Injective.under F).obj) :=
    TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque (Injective.under F) U hU
  exact (CochainComplex.exactAt_succ_single_obj _ k).isZero_homology.of_iso
    (asIso (HomologicalComplex.homologyMap
      (cechAugmentation U isTerminalTop (Injective.under F).obj) (k + 1))).symm

/-- The Čech connecting map `Hⁿ(U, Q) ⟶ Hⁿ⁺¹(U, F)` is onto. -/
private lemma epi_δ_cechSeq [Finite ι] {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : IsLerayProd U F) (n : ℕ) :
    Epi ((cechSeq_shortExact hF).δ n (n + 1) rfl) :=
  (cechSeq_shortExact hF).epi_δ n (n + 1) _ (isZero_homology_cechComplex_under U hU F n)

omit hU in
/-- The connecting map `H⁰(Q) ⟶ H¹(F)` is onto, since `H¹` of the injective sheaf vanishes. -/
private lemma epi_ofHom_δ_zero (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Epi (AddCommGrpCat.ofHom
      (_root_.CategoryTheory.Sheaf.H.δ (injectiveCokernelSequence_shortExact F) 0 1 rfl)) :=
  (AddCommGrpCat.epi_iff_surjective _).2 (_root_.CategoryTheory.Sheaf.H.δ_surjective
    (injectiveCokernelSequence_shortExact F) 0 1 rfl inferInstance)

/-- In degree one, Čech cohomology and sheaf cohomology of a Leray sheaf `F` are both the
cokernel of the degree `0` map induced by `I ⟶ Q`, through their connecting maps. -/
private def cechIsoOne [Finite ι] (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : IsLerayProd U F) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 1) :=
  have := epi_δ_cechSeq U hU hF 0
  have := epi_ofHom_δ_zero F
  have hC : HomologicalComplex.homologyMap ((cechComplexFunctor U).map
      (cokernel.π (Injective.ι F)).hom) 0 ≫ (cechSeq_shortExact hF).δ 0 1 rfl = 0 :=
    (cechSeq_shortExact hF).comp_δ 0 1 _
  have hH :
      AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map (cokernel.π (Injective.ι F)) 0) ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) 0 1 rfl) = 0 := by
    ext x
    exact (_root_.CategoryTheory.Sheaf.H.exact_map_δ (injectiveCokernelSequence_shortExact F) 0 1
      rfl).apply_apply_eq_zero x
  have hEC := (cechSeq_shortExact hF).homology_exact₃ 0 1 rfl
  have hEH := _root_.CategoryTheory.Sheaf.H.longSequence_exact₃'
    (injectiveCokernelSequence_shortExact F) 0 1 rfl
  { hom := hEC.desc
      ((homologyZeroCechIso U hU _).hom ≫ AddCommGrpCat.ofHom
        (_root_.CategoryTheory.Sheaf.H.δ (injectiveCokernelSequence_shortExact F) 0 1 rfl))
      (by rw [homologyMap_comp_homologyZeroCechIso_hom_assoc, hH, comp_zero])
    inv := hEH.desc
      ((homologyZeroCechIso U hU _).inv ≫ (cechSeq_shortExact hF).δ 0 1 rfl)
      (by
        simp only [(Iso.eq_inv_comp _).2 (homologyMap_comp_homologyZeroCechIso_hom U hU
          (cokernel.π (Injective.ι F))).symm, Category.assoc, Iso.hom_inv_id_assoc, hC,
          comp_zero])
    hom_inv_id := by
      rw [← cancel_epi ((cechSeq_shortExact hF).δ 0 1 rfl), hEC.g_desc_assoc, Category.assoc,
        hEH.g_desc, Iso.hom_inv_id_assoc, Category.comp_id]
    inv_hom_id := by
      rw [← cancel_epi (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
        (injectiveCokernelSequence_shortExact F) 0 1 rfl)), hEH.g_desc_assoc, Category.assoc,
        hEC.g_desc, Iso.inv_hom_id_assoc, Category.comp_id] }

/-- The degree-one comparison commutes with the Čech connecting map `H⁰(U, Q) ⟶ H¹(U, F)` and
`H⁰(Q) ⟶ H¹(F)`. -/
private lemma δ_comp_cechIsoOne_hom [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hF : IsLerayProd U F) :
    (cechSeq_shortExact hF).δ 0 1 rfl ≫ (cechIsoOne U hU F hF).hom =
      (homologyZeroCechIso U hU _).hom ≫ AddCommGrpCat.ofHom
        (_root_.CategoryTheory.Sheaf.H.δ (injectiveCokernelSequence_shortExact F) 0 1 rfl) := by
  have := epi_δ_cechSeq U hU hF 0
  exact ((cechSeq_shortExact hF).homology_exact₃ 0 1 rfl).g_desc _ _

/-- **Leray's theorem, in the form constructed by induction.** The comparison is defined by
dimension shifting along the chosen injective cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`: in degree
`0` both groups are the global sections, in degree `1` both are the cokernel of the degree `0`
map induced by `I ⟶ Q`, and in degree `n + 2` both are identified with degree `n + 1` of `Q` by
the connecting maps. -/
private def cechIsoAux [Finite ι] :
    (n : ℕ) → (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) → IsLerayProd U F →
      (((cechComplexFunctor U).obj F.obj).homology n ≅
        AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F n))
  | 0, F, _ => homologyZeroCechIso U hU F
  | 1, F, hF => cechIsoOne U hU F hF
  | n + 1 + 1, F, hF =>
    ((cechSeq_shortExact hF).δIso (n + 1) (n + 1 + 1) rfl
        (isZero_homology_cechComplex_under U hU F n)
        (isZero_homology_cechComplex_under U hU F (n + 1))).symm ≪≫
      cechIsoAux (n + 1) _ (isLerayProd_cokernel hF) ≪≫
      (AddEquiv.ofBijective _ (_root_.CategoryTheory.Sheaf.H.δ_bijective
        (injectiveCokernelSequence_shortExact F) (n + 1) (n + 1 + 1) rfl
        inferInstance inferInstance)).toAddCommGrpIso

/-- In positive degrees the comparison commutes with the connecting maps of the chosen injective
cokernel sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`. -/
@[reassoc]
private lemma δ_comp_cechIsoAux_hom [Finite ι] (n : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (hF : IsLerayProd U F) :
    (cechSeq_shortExact hF).δ n (n + 1) rfl ≫ (cechIsoAux U hU (n + 1) F hF).hom =
      (cechIsoAux U hU n _ (isLerayProd_cokernel hF)).hom ≫ AddCommGrpCat.ofHom
        (_root_.CategoryTheory.Sheaf.H.δ (injectiveCokernelSequence_shortExact F) n (n + 1)
          rfl) := by
  rcases n with _ | n
  · exact δ_comp_cechIsoOne_hom U hU F hF
  · have := (cechSeq_shortExact hF).isIso_δ (n + 1) (n + 1 + 1) rfl
      (isZero_homology_cechComplex_under U hU F n)
      (isZero_homology_cechComplex_under U hU F (n + 1))
    simp only [cechIsoAux, Iso.trans_hom, Iso.symm_hom, ShortComplex.ShortExact.δIso, asIso_inv,
      IsIso.hom_inv_id_assoc, AddEquiv.toAddCommGrpIso_hom]
    -- `AddEquiv.ofBijective δ _` has underlying homomorphism `δ` by construction; Mathlib states
    -- no lemma for its `toAddMonoidHom`
    rfl

/-- The comparison is natural in the sheaf. -/
private lemma cechIsoAux_naturality [Finite ι] (n : ℕ) :
    ∀ {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (hF : IsLerayProd U F)
      (hG : IsLerayProd U G) (f : F ⟶ G),
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
          (cechIsoAux U hU n G hG).hom =
        (cechIsoAux U hU n F hF).hom ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f n) := by
  induction n with
  | zero =>
    intro F G hF hG f
    exact homologyMap_comp_homologyZeroCechIso_hom U hU f
  | succ n ih =>
    intro F G hF hG f
    have := epi_δ_cechSeq U hU hF n
    rw [← cancel_epi ((cechSeq_shortExact hF).δ n (n + 1) rfl)]
    -- `f` extends to a morphism of the chosen injective cokernel sequences, with last component `g`
    let g : cokernel (Injective.ι F) ⟶ cokernel (Injective.ι G) :=
      (injectiveCokernelSequenceMap f).τ₃
    have hδC : (cechSeq_shortExact hF).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) (n + 1) =
          HomologicalComplex.homologyMap ((cechComplexFunctor U).map g.hom) n ≫
            (cechSeq_shortExact hG).δ n (n + 1) rfl :=
      HomologicalComplex.HomologySequence.δ_naturality (cechSeqMap U f) _ _ n (n + 1) rfl
    have hδH : AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g n) ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact G) n (n + 1) rfl) =
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ
          (injectiveCokernelSequence_shortExact F) n (n + 1) rfl) ≫
          AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f (n + 1)) := by
      ext x
      simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
        Function.comp_apply]
      have h := _root_.CategoryTheory.Sheaf.H.δ_naturality n (n + 1) rfl
        (injectiveCokernelSequence_shortExact F) (injectiveCokernelSequence_shortExact G)
        (injectiveCokernelSequenceMap f) x
      rwa [injectiveCokernelSequenceMap_τ₁] at h
    rw [reassoc_of% hδC, δ_comp_cechIsoAux_hom,
      reassoc_of% (ih (isLerayProd_cokernel hF) (isLerayProd_cokernel hG) g), hδH,
      ← δ_comp_cechIsoAux_hom_assoc]

/-- **Leray's theorem.** Let `U` be a finite family of opens covering a topological space `X`, and
let `F` be a sheaf of abelian groups on `X` with no cohomology in positive degrees on any nonempty
finite intersection of members of `U`. Then the Čech cohomology `Hⁿ(U, F)`, the cohomology of the
Čech complex of `F` for `U`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)`, for every `n`,
naturally in `F` (`TauCeti.Topology.homologyMap_comp_homologyCechComplexIsoH_hom`). -/
def homologyCechComplexIsoH [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) (n : ℕ) :
    ((cechComplexFunctor U).obj F.obj).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F n) :=
  cechIsoAux U hU n F (isLerayProd_of_finset hF)

/-- In degree `0`, the comparison of Leray's theorem is the identification of both groups with
the global sections. -/
@[simp]
lemma homologyCechComplexIsoH_zero [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) :
    homologyCechComplexIsoH U hU F hF 0 = homologyZeroCechIso U hU F := by
  rw [homologyCechComplexIsoH, cechIsoAux]

/-- **Naturality of Leray's theorem.** The comparison `Hⁿ(U, F) ≅ Hⁿ(X, F)` commutes with the maps
induced by a morphism `F ⟶ G` of sheaves which both satisfy the hypotheses of Leray's theorem. -/
@[reassoc]
theorem homologyMap_comp_homologyCechComplexIsoH_hom [Finite ι]
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U)))
    (hG : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (G.H' (k + 1) (s.inf U)))
    (f : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) n ≫
        (homologyCechComplexIsoH U hU G hG n).hom =
      (homologyCechComplexIsoH U hU F hF n).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map f n) :=
  cechIsoAux_naturality U hU n _ _ f

end TauCeti.Topology
