/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Closeds
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Relative
public import TauCeti.Topology.Sheaves.Flasque

/-!
# Sheaf cohomology with closed supports

Let `F` be a sheaf of abelian groups on a topological space `X`, let `W` be an open subset and
let `S` be a closed subset. The sections of `F` over `W` *supported in `S`* are those whose
restriction to `W ∖ S` vanishes; they form the subgroup `Γ_S(W, F)` of `F(W)`, and a morphism of
sheaves maps supported sections to supported sections.

The cohomology of `F` on `W` with supports in `S` is the relative cohomology
`H_Sⁿ(W, F) = Hⁿ(W, W ∖ S; F) = Extⁿ(ℤ_{W, W ∖ S}, F)` of the inclusion `W ∖ S ⟶ W`
(`CategoryTheory.Sheaf.relativeH'`), where `ℤ_{W, W ∖ S}` is the cokernel of the map of free
abelian sheaves `ℤ_{W ∖ S} ⟶ ℤ_W`. In degree zero it is `Γ_S(W, F)`, and the long exact sequence of
the pair is the support sequence

`⋯ ⟶ H_Sⁿ(W, F) ⟶ Hⁿ(W, F) ⟶ Hⁿ(W ∖ S, F) ⟶ H_Sⁿ⁺¹(W, F) ⟶ ⋯`

(`CategoryTheory.Sheaf.relativeH'.exact_toH'_cohomologyPresheaf_map`,
`relativeH'.exact_cohomologyPresheaf_map_δ` and `relativeH'.exact_δ_toH'`). Flasque sheaves have
no cohomology with supports in positive degrees; this is the acyclicity input for computing
cohomology with supports by flasque resolutions.

For opens `W' ≤ W`, the inclusion of pairs `(W', W' ∖ S) ⟶ (W, W ∖ S)` induces restriction maps
`H_Sⁿ(W, F) ⟶ H_Sⁿ(W', F)`, which make `W ↦ H_Sⁿ(W, F)` a presheaf; sheafifying it gives the local
cohomology sheaves of `F` with supports in `S`. *Excision* says that cohomology with supports in
`S` only depends on a neighbourhood of `S`: if `S ∩ W ⊆ W'`, restriction is an isomorphism
`H_Sⁿ(W, F) ≃+ H_Sⁿ(W', F)`. The proof shows that the map of relative free sheaves
`ℤ_{W', W' ∖ S} ⟶ ℤ_{W, W ∖ S}` is already an isomorphism, by the Yoneda criterion
`TauCeti.CategoryTheory.isIso_relativeFreeYonedaSheafMap_iff`: a section over `W'` supported in `S`
glues with zero on `W ∖ S` to a unique section over `W` supported in `S`.

## Main declarations

* `CategoryTheory.Sheaf.supportedSections F S W`: the sections `Γ_S(W, F)` of `F` over `W`
  supported in `S`;
* `CategoryTheory.Sheaf.supportedH F S W n`: the cohomology `H_Sⁿ(W, F)` of `F` on `W` with
  supports in `S`;
* `CategoryTheory.Sheaf.supportedHZeroEquiv`: `H_S⁰(W, F) ≃+ Γ_S(W, F)`, natural in `F`
  (`CategoryTheory.Sheaf.supportedHZeroEquiv_naturality_right`);
* `CategoryTheory.Sheaf.relativeH'.subsingleton_succ_of_isFlasque`: a flasque sheaf has no relative
  cohomology in positive degrees for an inclusion of opens; in particular it has no cohomology with
  supports in positive degrees.
* `CategoryTheory.Sheaf.supportedHRestrict`: the restriction map `H_Sⁿ(W, F) ⟶ H_Sⁿ(W', F)` for
  `W' ≤ W`, and `CategoryTheory.Sheaf.supportedHPresheaf F S n`, the presheaf `W ↦ H_Sⁿ(W, F)`;
* `CategoryTheory.Sheaf.existsUnique_mem_supportedSections_map_eq`: excision for sections
  supported in `S`;
* `TopologicalSpace.Closeds.isIso_relativeFreeYonedaSheafMap_complInclusion`: excision for the
  relative free sheaves `ℤ_{W, W ∖ S}`;
* `CategoryTheory.Sheaf.supportedHExcisionEquiv`: excision `H_Sⁿ(W, F) ≃+ H_Sⁿ(W', F)` when
  `S ∩ W ⊆ W'`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* R. Hartshorne, *Algebraic Geometry*, Exercises III.2.3–2.4.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Opposite TopologicalSpace

universe u

/-- The inclusion `W ∖ S ⟶ W` of the complement of a closed subset `S` in an open `W`. -/
abbrev TopologicalSpace.Closeds.complInclusion {X : TopCat.{u}} (S : Closeds X) (W : Opens X) :
    W ⊓ S.compl ⟶ W :=
  homOfLE inf_le_left

namespace CategoryTheory

namespace Sheaf

open Abelian

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

noncomputable section

/-- The sections of `F` over `W` supported in the closed subset `S`, that is, whose restriction to
`W ∖ S` vanishes. -/
def supportedSections (S : Closeds X) (W : Opens X) : AddSubgroup (F.obj.obj (op W)) :=
  (F.obj.map (S.complInclusion W).op).hom.ker

@[simp]
lemma mem_supportedSections_iff {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)} :
    s ∈ F.supportedSections S W ↔ F.obj.map (S.complInclusion W).op s = 0 :=
  Iff.rfl

/-- A morphism of sheaves maps sections supported in `S` to sections supported in `S`. -/
lemma map_mem_supportedSections {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) {S : Closeds X} {W : Opens X} {s : F.obj.obj (op W)}
    (hs : s ∈ F.supportedSections S W) : f.hom.app (op W) s ∈ G.supportedSections S W := by
  rw [mem_supportedSections_iff] at hs ⊢
  simp [← NatTrans.naturality_apply, hs]

/-- The restriction of a section supported in `S` to a smaller open is supported in `S`. -/
lemma map_mem_supportedSections_of_le {S : Closeds X} {W' W : Opens X} (h : W' ≤ W)
    {s : F.obj.obj (op W)} (hs : s ∈ F.supportedSections S W) :
    F.obj.map (homOfLE h).op s ∈ F.supportedSections S W' := by
  rw [mem_supportedSections_iff] at hs ⊢
  -- both composites are the inclusion `W' ∖ S ⟶ W`
  simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp] using
    congr(F.obj.map (homOfLE (inf_le_inf_right S.compl h)).op $hs)

/-- The cohomology `H_Sⁿ(W, F)` of `F` on `W` with supports in the closed subset `S`: the relative
cohomology of the inclusion `W ∖ S ⟶ W`. -/
abbrev supportedH (S : Closeds X) (W : Opens X) (n : ℕ) : Type u :=
  F.relativeH' (S.complInclusion W) n

/-- Degree-zero cohomology with supports in `S` is the group of sections supported in `S`. -/
def supportedHZeroEquiv (S : Closeds X) (W : Opens X) :
    F.supportedH S W 0 ≃+ F.supportedSections S W :=
  relativeH'.zeroEquiv F (S.complInclusion W)

@[simp]
lemma coe_supportedHZeroEquiv_apply (S : Closeds X) (W : Opens X) (x : F.supportedH S W 0) :
    (F.supportedHZeroEquiv S W x : F.obj.obj (op W)) =
      relativeH'.zeroEquiv F (S.complInclusion W) x :=
  (rfl)

/-- The equivalence `supportedHZeroEquiv` is natural in the sheaf. -/
lemma supportedHZeroEquiv_naturality_right
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G) (S : Closeds X)
    (W : Opens X) (x : F.supportedH S W 0) :
    G.supportedHZeroEquiv S W (x.comp (Ext.mk₀ f) (add_zero 0)) =
      ⟨f.hom.app (op W) (F.supportedHZeroEquiv S W x),
        map_mem_supportedSections f (F.supportedHZeroEquiv S W x).2⟩ :=
  Subtype.ext (relativeH'.coe_zeroEquiv_naturality_right (S.complInclusion W) f x)

/-- The restriction map `H_Sⁿ(W, F) ⟶ H_Sⁿ(W', F)` of cohomology with supports in `S` to a smaller
open `W' ≤ W`, induced by the inclusion of pairs `(W', W' ∖ S) ⟶ (W, W ∖ S)`. -/
def supportedHRestrict (S : Closeds X) {W' W : Opens X} (h : W' ≤ W) (n : ℕ) :
    F.supportedH S W n →+ F.supportedH S W' n :=
  relativeH'.map F (S.complInclusion W) (S.complInclusion W')
    (homOfLE (inf_le_inf_right S.compl h)) (homOfLE h) rfl n

@[simp]
lemma supportedHRestrict_self (S : Closeds X) (W : Opens X) {n : ℕ} (x : F.supportedH S W n) :
    F.supportedHRestrict S (le_refl W) n x = x :=
  -- `homOfLE` of a reflexivity proof is the identity of the thin category `Opens X`
  relativeH'.map_id F (S.complInclusion W) x

@[simp]
lemma supportedHRestrict_supportedHRestrict (S : Closeds X) {W'' W' W : Opens X} (h' : W'' ≤ W')
    (h : W' ≤ W) {n : ℕ} (x : F.supportedH S W n) :
    F.supportedHRestrict S h' n (F.supportedHRestrict S h n x) =
      F.supportedHRestrict S (h'.trans h) n x :=
  relativeH'.map_map F _ _ _ _ _ _ _ _ _ x

/-- Under `supportedHZeroEquiv`, restriction of degree-zero cohomology with supports is the
restriction of sections. -/
lemma coe_supportedHZeroEquiv_supportedHRestrict (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (x : F.supportedH S W 0) :
    (F.supportedHZeroEquiv S W' (F.supportedHRestrict S h 0 x) : F.obj.obj (op W')) =
      F.obj.map (homOfLE h).op (F.supportedHZeroEquiv S W x) :=
  relativeH'.coe_zeroEquiv_map F _ _ _ _ _ x

/-- The presheaf `W ↦ H_Sⁿ(W, F)` of cohomology with supports in `S`, with the restriction maps
`CategoryTheory.Sheaf.supportedHRestrict`. -/
@[expose, simps map]
def supportedHPresheaf (S : Closeds X) (n : ℕ) : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj W := AddCommGrpCat.of (F.supportedH S W.unop n)
  map f := AddCommGrpCat.ofHom (F.supportedHRestrict S (leOfHom f.unop) n)
  map_id W := by
    ext x
    exact F.supportedHRestrict_self S W.unop x
  map_comp f g := by
    ext x
    exact (F.supportedHRestrict_supportedHRestrict S _ _ x).symm

@[simp]
lemma supportedHPresheaf_obj (S : Closeds X) (n : ℕ) (W : (Opens X)ᵒᵖ) :
    (F.supportedHPresheaf S n).obj W = AddCommGrpCat.of (F.supportedH S W.unop n) :=
  (rfl)

/-- Excision for sections with supports: if `W' ≤ W` and `S ∩ W ⊆ W'` (that is,
`W ≤ W' ⊔ (X ∖ S)`), then every section over `W'` supported in `S` is the restriction of a unique
section over `W` supported in `S`, namely the one gluing it with zero on `W ∖ S`. -/
theorem existsUnique_mem_supportedSections_map_eq {S : Closeds X} {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) {s : F.obj.obj (op W')} (hs : s ∈ F.supportedSections S W') :
    ∃! t : F.obj.obj (op W), t ∈ F.supportedSections S W ∧ F.obj.map (homOfLE h).op t = s := by
  -- restrictions of `s` to opens disjoint from `S` vanish
  have hzero (V : Opens X) (k : V ⟶ W') (hV : V ≤ S.compl) : F.obj.map k.op s = 0 := by
    rw [show k = homOfLE (le_inf k.le hV) ≫ S.complInclusion W' from Subsingleton.elim _ _, op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply, (F.mem_supportedSections_iff).1 hs, map_zero]
  let U : Bool → Opens X := fun b ↦ cond b W' (W ⊓ S.compl)
  let sf : ∀ b, F.obj.obj (op (U b)) := fun b ↦ match b with
    | true => s
    | false => 0
  have hsf : TopCat.Presheaf.IsCompatible F.obj U sf := by
    rintro (_ | _) (_ | _)
    · simp [sf]
    · exact (map_zero _).trans (hzero _ _ (inf_le_left.trans inf_le_right)).symm
    · exact (hzero _ _ (inf_le_right.trans inf_le_right)).trans (map_zero _).symm
    · -- the two inclusions `W' ⊓ W' ⟶ W'` coincide in the thin category `Opens X`
      rfl
  have hcover : W ≤ iSup U := fun x hx ↦ by
    rcases Opens.mem_sup.1 (hW hx) with hx' | hx'
    exacts [Opens.mem_iSup.2 ⟨true, hx'⟩, Opens.mem_iSup.2 ⟨false, hx, hx'⟩]
  obtain ⟨t, ht, ht'⟩ := TopCat.Sheaf.existsUnique_gluing' F U W
    (fun b ↦ homOfLE (by cases b; exacts [inf_le_left, h])) hcover sf hsf
  refine ⟨t, ⟨ht false, ht true⟩, fun t' ⟨h₁, h₂⟩ ↦ ht' t' ?_⟩
  rintro (_ | _)
  exacts [h₁, h₂]

end

end Sheaf

end CategoryTheory

namespace TopologicalSpace.Closeds

open TauCeti.CategoryTheory

/-- Excision for the relative free sheaves of closed supports: if `W' ≤ W` and `S ∩ W ⊆ W'` (that
is, `W ≤ W' ⊔ (X ∖ S)`), the map `ℤ_{W', W' ∖ S} ⟶ ℤ_{W, W ∖ S}` is an isomorphism. -/
theorem isIso_relativeFreeYonedaSheafMap_complInclusion {X : TopCat.{u}} (S : Closeds X)
    {W' W : Opens X} (h : W' ≤ W) (hW : W ≤ W' ⊔ S.compl) :
    IsIso (relativeFreeYonedaSheafMap (Opens.grothendieckTopology X) (S.complInclusion W')
      (S.complInclusion W) (homOfLE (inf_le_inf_right S.compl h)) (homOfLE h) rfl) :=
  (isIso_relativeFreeYonedaSheafMap_iff _ _ _ _ _ _).2 fun F _ hs ↦
    F.existsUnique_mem_supportedSections_map_eq h hW hs

end TopologicalSpace.Closeds

namespace CategoryTheory

namespace Sheaf

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- Excision for cohomology with supports: if `W' ≤ W` and `S ∩ W ⊆ W'` (that is,
`W ≤ W' ⊔ (X ∖ S)`), restriction is an isomorphism `H_Sⁿ(W, F) ≃+ H_Sⁿ(W', F)`. -/
noncomputable def supportedHExcisionEquiv (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) (n : ℕ) : F.supportedH S W n ≃+ F.supportedH S W' n :=
  haveI := S.isIso_relativeFreeYonedaSheafMap_complInclusion h hW
  relativeH'.mapAddEquiv F (S.complInclusion W) (S.complInclusion W')
    (homOfLE (inf_le_inf_right S.compl h)) (homOfLE h) rfl n

@[simp]
lemma supportedHExcisionEquiv_apply (S : Closeds X) {W' W : Opens X} (h : W' ≤ W)
    (hW : W ≤ W' ⊔ S.compl) {n : ℕ} (x : F.supportedH S W n) :
    F.supportedHExcisionEquiv S h hW n x = F.supportedHRestrict S h n x :=
  haveI := S.isIso_relativeFreeYonedaSheafMap_complInclusion h hW
  relativeH'.mapAddEquiv_apply F _ _ _ _ _ x

end Sheaf

end CategoryTheory

namespace CategoryTheory

namespace Sheaf

namespace relativeH'

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- A flasque sheaf has no relative cohomology in positive degrees for an inclusion of opens. In
particular, `H_Sⁿ⁺¹(W, F)` vanishes for a flasque sheaf `F`. -/
instance subsingleton_succ_of_isFlasque [TopCat.Presheaf.IsFlasque F.obj]
    {U V : Opens X} (i : U ⟶ V) (n : ℕ) : Subsingleton (F.relativeH' i (n + 1)) := by
  cases n with
  | zero =>
    refine subsingleton_one F i ?_ inferInstance
    rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  | succ n => exact subsingleton_add_two F i inferInstance inferInstance

end relativeH'

end Sheaf

end CategoryTheory
