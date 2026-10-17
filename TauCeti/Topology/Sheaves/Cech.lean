/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Topology.Sheaves.Flasque
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Basic

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Data.Fintype.Lattice
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import TauCeti.CategoryTheory.Limits.Shapes.BinaryProducts
import TauCeti.CategoryTheory.Sites.IsSheafFor
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.AddCommGrp
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Comparison

/-!
# Čech complexes of flasque sheaves

Let `F` be a flasque sheaf of abelian groups on a topological space `X`. This file proves that
for every finite open cover `U` of `X` the augmented Čech complex
`0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact: flasque sheaves have no higher Čech cohomology
for finite covers. Together with the acyclicity of flasque sheaves for derived-functor cohomology
(`TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`), this is the input to the comparison of
Čech and derived-functor cohomology for covers whose finite intersections are acyclic.

The proof is by induction on the number of members of the cover, applied more generally to the
restricted presheaves `V ↦ F(Y ∩ V)` for opens `Y` contained in the union of the members. For a
cover by two opens `V 0`, `V 1`, exactness reduces to the Mayer–Vietoris sequence
`0 ⟶ F(Y) ⟶ F(Y ∩ V 0) ⊕ F(Y ∩ V 1) ⟶ F(Y ∩ V 0 ∩ V 1) ⟶ 0`, which is exact on the left by the
sheaf condition and on the right because `F` is flasque. A cover by the opens `U a` and `U i`,
`i ∈ s`, refines the two-member cover by `U a` and `⋃_{i ∈ s} U i`, so it is acyclic once its
restrictions to these two opens and to their intersection are
(`TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_fin_two`). The restrictions to `U a`
and to `U a ∩ ⋃_{i ∈ s} U i` have a member containing everything; the restriction to
`⋃_{i ∈ s} U i` is compared with the smaller cover by the `U i`, `i ∈ s`, which is acyclic by
induction (`TauCeti.CategoryTheory.quasiIso_cechAugmentation_iff_of_quasiIso_prod`).

## Main results

* `TopCat.Sheaf.quasiIso_cechAugmentation_prod_of_isFlasque`: for a flasque sheaf `F`, a
  finite family of opens `U i` and an open `Y` contained in their union, the augmented Čech
  complex of `V ↦ F(Y ∩ V)` for `U` is exact.
* `TopCat.Sheaf.quasiIso_cechAugmentation_of_isFlasque`: a flasque sheaf has an exact
  augmented Čech complex for every finite open cover.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.4.3.
* The Stacks Project, Lemma 20.11.4 (tag 01EW).
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TauCeti.CategoryTheory

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u}) [F.presheaf.IsFlasque]

/-- **Two-member covers.** For a flasque sheaf `F`, opens `V 0`, `V 1` and an open `Y` contained
in their union, the augmented Čech complex of `V ↦ F(Y ∩ V)` for the family `V 0`, `V 1` is
exact: sections over `Y ∩ V 0` and `Y ∩ V 1` agreeing on `Y ∩ V 0 ∩ V 1` glue uniquely, and
every section over `Y ∩ V 0 ∩ V 1` extends to `Y ∩ V 0` because `F` is flasque. -/
private lemma quasiIso_cechAugmentation_fin_two (Y : Opens X) (V : Fin 2 → Opens X)
    (hY : Y ≤ V 0 ⊔ V 1) :
    QuasiIso (cechAugmentation V isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  rw [quasiIso_cechAugmentation_fin_two_iff_isSheafFor_and_surjective,
    Presieve.isSheafFor_arrows_iff]
  refine ⟨fun x hx ↦ ?_, fun z ↦ ?_⟩
  · rw [Presieve.Arrows.compatible_homOfLE_iff] at hx
    refine F.existsUnique_gluing' (fun i ↦ Y ⨯ V i) (Y ⨯ ⊤)
      (fun i ↦ (prod.functor.obj Y).map (homOfLE le_top)) ?_ x fun i j ↦ ?_
    · simp only [CompleteLattice.prod_eq_inf, inf_top_eq]
      refine (le_inf le_rfl hY).trans ?_
      rw [inf_sup_left]
      exact sup_le (le_iSup (fun i ↦ Y ⊓ V i) 0) (le_iSup (fun i ↦ Y ⊓ V i) 1)
    · -- the two restrictions agree on `Y ∩ V i ∩ V j`, which contains `(Y ∩ V i) ∩ (Y ∩ V j)`
      have h : (Y ⨯ V i) ⊓ (Y ⨯ V j) ≤ (Y ⨯ (V i ⊓ V j)) := by
        simp only [CompleteLattice.prod_eq_inf]
        exact le_inf (inf_le_left.trans inf_le_left) (inf_le_inf inf_le_right inf_le_right)
      rw [show (Y ⨯ V i).infLELeft (Y ⨯ V j) =
          homOfLE h ≫ (prod.functor.obj Y).map (homOfLE inf_le_left) from Subsingleton.elim _ _,
        show (Y ⨯ V i).infLERight (Y ⨯ V j) =
          homOfLE h ≫ (prod.functor.obj Y).map (homOfLE inf_le_right) from Subsingleton.elim _ _,
        op_comp, op_comp, F.presheaf.map_comp, F.presheaf.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply]
      exact congrArg _ (hx i j)
  · -- a section over `Y ∩ V 0 ∩ V 1` extends to `Y ∩ V 0`, as `F` is flasque
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Presheaf.IsFlasque.epi
      (F := F.presheaf) ((prod.functor.obj Y).map (homOfLE inf_le_left : V 0 ⊓ V 1 ⟶ V 0)).op) z
    exact ⟨(y, 0), by simpa using hy⟩

/-- For a flasque sheaf `F`, a nonempty finite set `s` of indices of opens `U i` and an open `Y`
contained in the union of the `U i` with `i ∈ s`, the augmented Čech complex of `V ↦ F(Y ∩ V)` for
the subfamily indexed by `s` is exact. -/
private lemma quasiIso_cechAugmentation_prod_finset {ι : Type u} (U : ι → Opens X)
    {s : Finset ι} (hs : s.Nonempty) (Y : Opens X) (hY : Y ≤ s.sup U) :
    QuasiIso (cechAugmentation (fun i : s ↦ U i) isTerminalTop
      ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  induction hs using Finset.Nonempty.cons_induction generalizing Y with
  | singleton a =>
    exact quasiIso_cechAugmentation_prod_of_hom _ isTerminalTop _ Y
      (i₀ := ⟨a, Finset.mem_singleton_self a⟩) (homOfLE (by simpa using hY))
  | cons a s ha hs ih =>
    -- the cover refines the two-member cover by `U a` and `⋃_{i ∈ s} U i`
    let W : Finset.cons a s ha → Opens X := fun i ↦ U i
    let V : Fin 2 → Opens X := ![U a, s.sup U]
    let Q := (prod.functor.obj Y).op ⋙ F.presheaf
    have ha' : a ∈ Finset.cons a s ha := Finset.mem_cons_self a s
    have hW (k : Finset.cons a s ha) : ∃ i, Nonempty (W k ⟶ V i) := by
      obtain ⟨k, hk⟩ := k
      rcases Finset.mem_cons.1 hk with rfl | hk
      · exact ⟨0, ⟨𝟙 _⟩⟩
      · exact ⟨1, ⟨homOfLE (Finset.le_sup (f := U) hk)⟩⟩
    refine (quasiIso_cechAugmentation_iff_of_fin_two isTerminalTop Q V hW
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop Q (V 0) (i₀ := ⟨a, ha'⟩) (𝟙 _)) ?_
      (quasiIso_cechAugmentation_prod_of_hom W isTerminalTop Q (V 0 ⨯ V 1) (i₀ := ⟨a, ha'⟩)
        prod.fst)).2
      (quasiIso_cechAugmentation_fin_two F Y V (by simpa [V, Finset.sup_cons] using hY))
    -- the restriction to `⋃_{i ∈ s} U i` is compared with the cover by the `U i`, `i ∈ s`
    let W' : s → Opens X := fun i ↦ U i
    -- restricting to `V 1` and then to `Y` is restricting to `Y ∩ V 1`
    let e := Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp Y (V 1))) F.presheaf
    refine (quasiIso_cechAugmentation_iff_of_quasiIso_prod W isTerminalTop
      ((prod.functor.obj (V 1)).op ⋙ Q) W' (fun n b ↦ ?_) (fun n b ↦ ?_)).2 ?_
    · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ (Functor.isoWhiskerLeft _ e ≪≫
        Functor.isoWhiskerRight (NatIso.op (prod.functorLeftComp _ _)) F.presheaf)).2
        (ih _ (leOfHom (prod.fst ≫ prod.snd)))
    · exact quasiIso_cechAugmentation_prod_of_hom W isTerminalTop _ _
        (i₀ := ⟨b 0, Finset.mem_cons_of_mem (b 0).2⟩) (Pi.π _ 0)
    · exact (quasiIso_cechAugmentation_iff_of_iso _ _ _ e).2 (ih _ (leOfHom prod.snd))

/-- **Flasque sheaves are acyclic for finite covers, restricted to an open.** Let `F` be a flasque
sheaf of abelian groups on `X`, let `U i` be a finite family of opens, and let `Y` be an open
contained in their union. Then the augmented Čech complex of the presheaf `V ↦ F(Y ∩ V)` for the
family `U` is exact; that is, the cover of `Y` by the opens `Y ∩ U i` is acyclic for `F`. -/
theorem quasiIso_cechAugmentation_prod_of_isFlasque {ι : Type u} [Finite ι] (U : ι → Opens X)
    (Y : Opens X) (hY : Y ≤ ⨆ i, U i) :
    QuasiIso (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf)) := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    -- an empty family only covers the empty open, over which every section group is zero
    have hzero (V : Opens X) : IsZero (((prod.functor.obj Y).op ⋙ F.presheaf).obj (op V)) :=
      (isZero_zero _).of_iso ((isZero_zero _).isoIsTerminal (F.isTerminalOfEqEmpty
        (eq_bot_iff.2 ((leOfHom prod.fst).trans (hY.trans (by rw [iSup_of_empty])))))).symm
    have hL : IsZero ((cechComplexFunctor U).obj ((prod.functor.obj Y).op ⋙ F.presheaf)) :=
      Functor.map_isZero _ (Functor.isZero _ fun V ↦ hzero V.unop)
    have := (Functor.map_isZero (CochainComplex.single₀ _) (hzero ⊤)).isIso hL
      (cechAugmentation U isTerminalTop ((prod.functor.obj Y).op ⋙ F.presheaf))
    infer_instance
  | inr _ =>
    have := Fintype.ofFinite ι
    exact (quasiIso_cechAugmentation_congr isTerminalTop _
      ⟨fun i ↦ ⟨i, Finset.mem_univ i⟩, fun _ ↦ 𝟙 _⟩ ⟨Subtype.val, fun _ ↦ 𝟙 _⟩).2
      (quasiIso_cechAugmentation_prod_finset F U Finset.univ_nonempty Y
        (by rwa [Finset.sup_univ_eq_iSup]))

/-- **Flasque sheaves are acyclic for finite covers.** For a flasque sheaf `F` of abelian groups
on `X` and a finite family of opens `U i` covering `X`, the augmented Čech complex
`0 ⟶ F(X) ⟶ Č⁰(U, F) ⟶ Č¹(U, F) ⟶ ⋯` is exact: `F` has no Čech cohomology for `U` in positive
degrees, and its degree `0` Čech cohomology is `F(X)`. -/
theorem quasiIso_cechAugmentation_of_isFlasque {ι : Type u} [Finite ι] (U : ι → Opens X)
    (hU : ⨆ i, U i = ⊤) : QuasiIso (cechAugmentation U isTerminalTop F.presheaf) :=
  (quasiIso_cechAugmentation_iff_of_iso _ _ _
    (Functor.isoWhiskerRight (NatIso.op isTerminalTop.prodLeftUnitor) F.presheaf)).2
    (quasiIso_cechAugmentation_prod_of_isFlasque F U ⊤ hU.ge)

end TopCat.Sheaf
