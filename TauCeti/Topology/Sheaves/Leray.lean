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
members of `U` (a *Leray cover* for `F`). Then the Čech cohomology `Ȟⁿ(U, F)`, the cohomology of
the Čech complex `Č(U, F)`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)` in every degree.

The proof is by dimension shifting. Embed `F` into an injective sheaf `I`, with cokernel `Q`.

* On every finite intersection `V` of members of `U`, the sequence of sections
  `0 ⟶ F(V) ⟶ I(V) ⟶ Q(V) ⟶ 0` is exact, because `H¹(V, F) = 0`; so the Čech complexes form a
  short exact sequence `0 ⟶ Č(U, F) ⟶ Č(U, I) ⟶ Č(U, Q) ⟶ 0`.
* `I` is flasque, so `Č(U, I)` has no cohomology in positive degrees
  (`TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`), and neither has `I` sheaf cohomology.
  The two long exact sequences then give `Ȟⁿ⁺¹(U, F) ≅ Ȟⁿ(U, Q)` and `Hⁿ⁺¹(X, F) ≅ Hⁿ(X, Q)` for
  `n ≥ 1`, while in degree one both `Ȟ¹(U, F)` and `H¹(X, F)` are the cokernel of
  `I(X) ⟶ Q(X)`, since `Ȟ⁰` and `H⁰` are both global sections.
* `Q` is again acyclic on the finite intersections, as `Hᵏ(V, Q) ≅ Hᵏ⁺¹(V, F)` for `k ≥ 1`.

Induction on the degree, for all sheaves at once, concludes.

The isomorphism is not claimed to be natural in `F`.

## Main results

* `TauCeti.Topology.nonempty_homology_cechComplex_iso_H`: for a finite Leray cover `U` of `X`,
  `Ȟⁿ(U, F) ≅ Hⁿ(X, F)` for every `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.11, and the proof of Theorem III.4.5.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.CategoryTheory

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) (hU : ⨆ i, U i = ⊤)

include hU

/-- A sheaf on `X` satisfies the sheaf condition for a family of opens covering `X`, in the form
used by the augmentation of the Čech complex. -/
private lemma isSheafFor_ofArrows (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (E : AddCommGrpCat.{u}ᵒᵖ) :
    (Presieve.ofArrows U fun i ↦ isTerminalTop.from (U i)).IsSheafFor
      (F.obj ⋙ coyoneda.obj E) := by
  rw [Presieve.isSheafFor_iff_generate]
  refine F.property E.unop _ fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  exact ⟨U i, isTerminalTop.from _, Sieve.le_generate _ _ _ (Presieve.ofArrows.mk i), hi⟩

/-- The degree `0` Čech cohomology of a sheaf for a cover of `X` is the group of global sections,
which is also the degree `0` sheaf cohomology. -/
private def homologyZeroCechIso (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ((cechComplexFunctor U).obj F.obj).homology 0 ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F 0) :=
  have : QuasiIsoAt (cechAugmentation U isTerminalTop F.obj) 0 :=
    (quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop F.obj).2
      (isSheafFor_ofArrows U hU F)
  (asIso (HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop F.obj) 0)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 _ ≪≫
      ((_root_.CategoryTheory.Sheaf.H.equiv₀ F isTerminalTop).symm.toAddCommGrpIso)

/-- The identification of degree `0` Čech cohomology with degree `0` sheaf cohomology is natural
in the sheaf. -/
private lemma homologyMap_comp_homologyZeroCechIso_hom
    {P Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (g : P ⟶ Q) :
    HomologicalComplex.homologyMap ((cechComplexFunctor U).map g.hom) 0 ≫
        (homologyZeroCechIso U hU Q).hom =
      (homologyZeroCechIso U hU P).hom ≫
        AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.map g 0) := by
  have hP : QuasiIsoAt (cechAugmentation U isTerminalTop P.obj) 0 :=
    (quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop P.obj).2 (isSheafFor_ofArrows U hU P)
  have hQ : QuasiIsoAt (cechAugmentation U isTerminalTop Q.obj) 0 :=
    (quasiIsoAt_cechAugmentation_zero_iff U isTerminalTop Q.obj).2 (isSheafFor_ofArrows U hU Q)
  rw [← cancel_epi (HomologicalComplex.homologyMap (cechAugmentation U isTerminalTop P.obj) 0)]
  simp only [homologyZeroCechIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    ← HomologicalComplex.homologyMap_comp_assoc, cechAugmentation_naturality]
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality_assoc]
  congr 1
  ext x
  exact (_root_.CategoryTheory.Sheaf.H.equiv₀_symm_naturality isTerminalTop g x).symm

/-- **Leray's theorem, in the form proved by induction.** If `F` has no cohomology in positive
degrees on the finite products `U (a 0) × ⋯ × U (a m)` of members of the cover, then
`Ȟⁿ(U, F) ≅ Hⁿ(X, F)`. -/
private lemma nonempty_homology_cechComplex_iso_H_aux [Finite ι] (n : ℕ) :
    ∀ F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      (∀ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ),
        Subsingleton (F.H' (k + 1) (∏ᶜ fun j ↦ U (a j)))) →
      Nonempty (((cechComplexFunctor U).obj F.obj).homology n ≅
        AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F n)) := by
  induction n with
  | zero => exact fun F _ ↦ ⟨homologyZeroCechIso U hU F⟩
  | succ n ih =>
    intro F hF
    -- embed `F` into an injective, hence flasque, sheaf `I = S.X₂` with cokernel `Q = S.X₃`
    let S := injectiveCokernelSequence F
    have hS : S.ShortExact := injectiveCokernelSequence_shortExact F
    -- the Čech complexes of `F`, `I` and `Q` form a short exact sequence
    have hC : ((S.map (sheafToPresheaf _ AddCommGrpCat.{u})).map
        (cechComplexFunctor U)).ShortExact :=
      shortExact_map_cechComplexFunctor U _ fun m a ↦
        _root_.CategoryTheory.Sheaf.H'.shortExact_map_sheafSections hS _ (hF m a 0)
    -- `I` has no Čech cohomology in positive degrees
    have hI (k : ℕ) : IsZero (((cechComplexFunctor U).obj S.X₂.obj).homology (k + 1)) := by
      have := TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque S.X₂ U hU
      exact (CochainComplex.exactAt_succ_single_obj _ k).isZero_homology.of_iso
        (asIso (HomologicalComplex.homologyMap
          (cechAugmentation U isTerminalTop S.X₂.obj) (k + 1))).symm
    -- `Q` is again acyclic on the finite intersections of members of the cover
    have hQ (m : ℕ) (a : Fin (m + 1) → ι) (k : ℕ) :
        Subsingleton (S.X₃.H' (k + 1) (∏ᶜ fun j ↦ U (a j))) :=
      _root_.CategoryTheory.Sheaf.H'.subsingleton_X₃ hS _ (k + 1) inferInstance (hF m a (k + 1))
    rcases n with _ | n
    · -- in degree one, both groups are the cokernel of `H⁰(I) ⟶ H⁰(Q)`
      have : Epi (hC.δ 0 1 (by simp)) := hC.epi_δ 0 1 (by simp) (hI 0)
      have : Epi (AddCommGrpCat.ofHom (_root_.CategoryTheory.Sheaf.H.δ hS 0 1 rfl)) :=
        (AddCommGrpCat.epi_iff_surjective _).2
          (_root_.CategoryTheory.Sheaf.H.δ_surjective hS 0 1 rfl inferInstance)
      exact ⟨(hC.homology_exact₃ 0 1 _).gIsCokernel.coconePointUniqueUpToIso
          (colimit.isColimit _) ≪≫
        cokernel.mapIso _ _ (homologyZeroCechIso U hU S.X₂) (homologyZeroCechIso U hU S.X₃)
          (homologyMap_comp_homologyZeroCechIso_hom U hU S.g) ≪≫
        ((_root_.CategoryTheory.Sheaf.H.longSequence_exact₃' hS 0 1
          rfl).gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)).symm⟩
    · -- in degree `n + 2`, both groups are degree `n + 1` cohomology of `Q`
      obtain ⟨e⟩ := ih S.X₃ hQ
      exact ⟨(hC.δIso (n + 1) (n + 2) (by simp) (hI n) (hI (n + 1))).symm ≪≫ e ≪≫
        (AddEquiv.ofBijective _ (_root_.CategoryTheory.Sheaf.H.δ_bijective hS (n + 1) (n + 2) rfl
          inferInstance inferInstance)).toAddCommGrpIso⟩

/-- **Leray's theorem.** Let `U` be a finite family of opens covering a topological space `X`, and
let `F` be a sheaf of abelian groups on `X` with no cohomology in positive degrees on any nonempty
finite intersection of members of `U`. Then the Čech cohomology `Ȟⁿ(U, F)`, the cohomology of the
Čech complex of `F` for `U`, is isomorphic to the sheaf cohomology `Hⁿ(X, F)`, for every `n`. -/
theorem nonempty_homology_cechComplex_iso_H [Finite ι]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ k, Subsingleton (F.H' (k + 1) (s.inf U))) (n : ℕ) :
    Nonempty (((cechComplexFunctor U).obj F.obj).homology n ≅
      AddCommGrpCat.of (_root_.CategoryTheory.Sheaf.H.{u} F n)) := by
  classical
  refine nonempty_homology_cechComplex_iso_H_aux U hU n F fun m a k ↦ ?_
  -- the product of the members `U (a j)` is their intersection
  have h : (∏ᶜ fun j ↦ U (a j)) = (Finset.univ.image a).inf U := by
    rw [Finset.inf_image, Finset.inf_univ_eq_iInf]
    exact le_antisymm (le_iInf fun j ↦ leOfHom (Pi.π _ j))
      (leOfHom (Pi.lift fun j ↦ homOfLE (iInf_le _ j)))
  rw [h]
  exact hF _ (Finset.univ_nonempty.image a) k

end TauCeti.Topology
