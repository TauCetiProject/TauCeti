/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Stalks
public import TauCeti.Topology.Sheaves.SupportedCohomology

/-!
# Local cohomology sheaves

Let `F` be a sheaf of abelian groups on a topological space `X` and let `S` be a closed subset.
The groups `Γ_S(W, F)` of sections supported in `S` form a subsheaf `Γ_S(F)` of `F`
(`CategoryTheory.Sheaf.supportedSectionsSheaf`), and `Γ_S(F)` is flasque when `F` is: a section
over `U` supported in `S` glues with zero on `V ∖ S` and then extends from `U ∪ (V ∖ S)` to `V`.

The *local cohomology sheaf* `𝓗_Sⁿ(F)` is the sheafification of the presheaf
`W ↦ H_Sⁿ(W, F)` of cohomology with supports in `S`
(`CategoryTheory.Sheaf.supportedHSheaf`). In degree zero that presheaf is already the sheaf
`Γ_S(F)`, so `𝓗_S⁰(F) ≅ Γ_S(F)`. The sheaves `𝓗_Sⁿ(F)` are supported in `S`: their stalks
vanish off `S`, because `H_Sⁿ(W, F) = 0` for every open `W` disjoint from `S`. For a flasque
sheaf `F` they vanish in positive degrees, since then `H_Sⁿ⁺¹(W, F) = 0` for every `W`. More
generally, `𝓗_Sⁿ(F) = 0` exactly when, for every open `W`, every class in `H_Sⁿ(W, F)` vanishes
locally on `W` (`TopCat.Presheaf.isZero_presheafToSheaf_obj_iff`).

The sheaves `𝓗_Sⁿ(F)` are the coefficients of the local-to-global comparison for cohomology with
supports in `S`; for a closed submanifold `M` of codimension `n` in a manifold `X`, the sheaf
`𝓗_Mⁿ(ℤ_X)` is the relative orientation sheaf of `M` in `X`.

## Main declarations

* `CategoryTheory.Sheaf.supportedSectionsSheaf F S`: the sheaf `Γ_S(F)` of sections supported in
  `S`, which is flasque when `F` is;
* `CategoryTheory.Sheaf.supportedSectionsι F S`: the inclusion `Γ_S(F) ⟶ F`, a monomorphism;
* `CategoryTheory.Sheaf.supportedSectionsLift`: the factorization through `Γ_S(F)` of a
  morphism into `F` whose sections are supported in `S`;
* `CategoryTheory.Sheaf.supportedHSheaf F S n`: the local cohomology sheaf `𝓗_Sⁿ(F)`;
* `CategoryTheory.Sheaf.supportedHSheafZeroIso`: `𝓗_S⁰(F) ≅ Γ_S(F)`;
* `CategoryTheory.Sheaf.isZero_stalk_supportedHSheaf_of_notMem`: the stalks of `𝓗_Sⁿ(F)` at
  points outside `S` vanish;
* `CategoryTheory.Sheaf.isZero_supportedHSheaf_succ_of_isFlasque`: `𝓗_Sⁿ⁺¹(F) = 0` for a flasque
  sheaf `F`.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
* R. Hartshorne, *Algebraic Geometry*, Exercises II.1.20 and III.2.3.
* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.3 and §2.6.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace CategoryTheory

namespace Sheaf

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  (S : Closeds X)

noncomputable section

/-- The presheaf `W ↦ Γ_S(W, F)` of sections of `F` supported in the closed subset `S`, with the
restriction maps of `F`. -/
@[expose]
def supportedSectionsPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj W := AddCommGrpCat.of (F.supportedSections S W.unop)
  map f := AddCommGrpCat.ofHom <| AddMonoidHom.mk'
    (fun s ↦ ⟨F.obj.map f s, F.map_mem_supportedSections_of_le (leOfHom f.unop) s.2⟩)
    fun s t ↦ Subtype.ext (map_add _ _ _)
  map_id W := by
    ext s
    exact congr($(F.obj.map_id W) s.1)
  map_comp f g := by
    ext s
    exact congr($(F.obj.map_comp f g) s.1)

@[simp]
lemma supportedSectionsPresheaf_obj (W : (Opens X)ᵒᵖ) :
    (F.supportedSectionsPresheaf S).obj W = AddCommGrpCat.of (F.supportedSections S W.unop) :=
  (rfl)

@[simp]
lemma coe_supportedSectionsPresheaf_map_apply {W W' : (Opens X)ᵒᵖ} (f : W ⟶ W')
    (s : F.supportedSections S W.unop) :
    Subtype.val (p := (· ∈ F.supportedSections S W'.unop))
      ((F.supportedSectionsPresheaf S).map f s) = F.obj.map f s :=
  (rfl)

/-- The sections of `F` supported in a closed subset `S` form a sheaf: a gluing in `F` of
supported sections is supported, since its restriction to the complement of `S` vanishes
locally. -/
theorem isSheaf_supportedSectionsPresheaf : (F.supportedSectionsPresheaf S).IsSheaf := by
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2 fun ι U sf hsf ↦ ?_
  obtain ⟨s, hs, hs'⟩ := TopCat.Sheaf.existsUnique_gluing F U (fun i ↦ (sf i).1)
    fun i j ↦ congr_arg (Subtype.val : F.supportedSections S _ → F.obj.obj _) (hsf i j)
  -- the restriction of `s` to `(⋃ U i) ∖ S` vanishes on each `U i ∖ S`
  have hmem : s ∈ F.supportedSections S (iSup U) := by
    rw [mem_supportedSections_iff]
    refine TopCat.Sheaf.eq_of_locally_eq' F (fun i ↦ U i ⊓ S.compl) _
      (fun i ↦ homOfLE (inf_le_inf_right _ (le_iSup U i)))
      (fun x hx ↦ Opens.mem_iSup.2 ?_) _ _ fun i ↦ ?_
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx.1
      exact ⟨i, hi, hx.2⟩
    · have h := congr(F.obj.map (S.complInclusion (U i)).op $(hs i))
      rw [(F.mem_supportedSections_iff).1 (sf i).2] at h
      simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Opens.leSupr] using h
  refine ⟨⟨s, hmem⟩, fun i ↦ Subtype.ext (hs i), fun t ht ↦ Subtype.ext ?_⟩
  exact hs' t.1 fun i ↦ congr_arg (Subtype.val : F.supportedSections S _ → F.obj.obj _) (ht i)

/-- The sheaf `Γ_S(F)` of sections of `F` supported in the closed subset `S`. -/
@[expose]
def supportedSectionsSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ⟨F.supportedSectionsPresheaf S, F.isSheaf_supportedSectionsPresheaf S⟩

@[simp]
lemma supportedSectionsSheaf_obj :
    (F.supportedSectionsSheaf S).obj = F.supportedSectionsPresheaf S :=
  (rfl)

/-- The inclusion `Γ_S(F) ⟶ F` of the sheaf of sections supported in `S`. -/
def supportedSectionsι : F.supportedSectionsSheaf S ⟶ F :=
  ObjectProperty.homMk
    { app W := AddCommGrpCat.ofHom (F.supportedSections S W.unop).subtype
      naturality _ _ _ := rfl }

@[simp]
lemma supportedSectionsι_hom_app_apply (W : (Opens X)ᵒᵖ) (s : F.supportedSections S W.unop) :
    (F.supportedSectionsι S).hom.app W s = s :=
  (rfl)

/-- The sections of `F` in the image of the inclusion `Γ_S(F) ⟶ F` are exactly the sections
supported in `S`. -/
@[simp]
lemma range_supportedSectionsι_hom_app (W : (Opens X)ᵒᵖ) :
    ((F.supportedSectionsι S).hom.app W).hom.range = F.supportedSections S W.unop :=
  (F.supportedSections S W.unop).range_subtype

variable {F S} in
/-- A morphism `G ⟶ F` all of whose sections are supported in `S` factors through the inclusion
`Γ_S(F) ⟶ F`. -/
def supportedSectionsLift {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : G ⟶ F) (h : ∀ W s, φ.hom.app W s ∈ F.supportedSections S W.unop) :
    G ⟶ F.supportedSectionsSheaf S :=
  ObjectProperty.homMk
    { app W := AddCommGrpCat.ofHom ((φ.hom.app W).hom.codRestrict _ (h W))
      naturality _ _ f := by
        ext s
        exact Subtype.ext congr($(φ.hom.naturality f) s) }

variable {F S} in
@[reassoc (attr := simp)]
lemma supportedSectionsLift_ι {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (φ : G ⟶ F) (h : ∀ W s, φ.hom.app W s ∈ F.supportedSections S W.unop) :
    supportedSectionsLift φ h ≫ F.supportedSectionsι S = φ := by
  ext
  rfl

/-- The inclusion `Γ_S(F) ⟶ F` is a monomorphism, since it is injective on sections. -/
instance mono_supportedSectionsι : Mono (F.supportedSectionsι S) := by
  have (W : (Opens X)ᵒᵖ) : Mono ((F.supportedSectionsι S).hom.app W) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono (F.supportedSectionsι S).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The sheaf of sections supported in a closed subset of a flasque sheaf is flasque. -/
instance isFlasque_supportedSectionsSheaf [TopCat.Presheaf.IsFlasque F.obj] :
    TopCat.Presheaf.IsFlasque (F.supportedSectionsSheaf S).obj where
  epi {V U} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    have hUV : U.unop ≤ V.unop := leOfHom i.unop
    -- glue `s` with zero on `V ∖ S`, then extend from `U ∪ (V ∖ S)` to `V` using flasqueness
    obtain ⟨t₀, ⟨ht₀, ht₀s⟩, -⟩ := F.existsUnique_mem_supportedSections_map_eq
      (le_sup_left : U.unop ≤ U.unop ⊔ V.unop ⊓ S.compl)
      (sup_le le_sup_left (inf_le_right.trans le_sup_right)) s.2
    have hW : U.unop ⊔ V.unop ⊓ S.compl ≤ V.unop := sup_le hUV inf_le_left
    obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).1
      (TopCat.Presheaf.IsFlasque.epi (F := F.obj) (homOfLE hW).op) t₀
    have hres (W : Opens X) (h₁ : W ≤ U.unop ⊔ V.unop ⊓ S.compl) :
        F.obj.map (homOfLE (h₁.trans hW)).op t = F.obj.map (homOfLE h₁).op t₀ := by
      simp [← ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    refine ⟨⟨t, ?_⟩, Subtype.ext ?_⟩
    · rw [mem_supportedSections_iff]
      have h₁ : V.unop ⊓ S.compl ≤ U.unop ⊔ V.unop ⊓ S.compl := le_sup_right
      refine (hres _ h₁).trans ?_
      -- `V ∖ S` lies in the complement of `S` in `U ∪ (V ∖ S)`, where `t₀` vanishes
      have h₂ : V.unop ⊓ S.compl ≤ (U.unop ⊔ V.unop ⊓ S.compl) ⊓ S.compl :=
        le_inf h₁ inf_le_right
      rw [show homOfLE h₁ = homOfLE h₂ ≫ S.complInclusion _ from Subsingleton.elim _ _, op_comp,
        Functor.map_comp, ConcreteCategory.comp_apply, (F.mem_supportedSections_iff).1 ht₀,
        map_zero]
    · exact (hres _ le_sup_left).trans ht₀s

/-- The degree-zero cohomology with supports in `S` is the presheaf of sections supported in `S`,
through the equivalences `CategoryTheory.Sheaf.supportedHZeroEquiv`. -/
def supportedHPresheafZeroIso : F.supportedHPresheaf S 0 ≅ (F.supportedSectionsSheaf S).obj :=
  NatIso.ofComponents (fun W ↦ (F.supportedHZeroEquiv S W.unop).toAddCommGrpIso) fun f ↦ by
    ext x
    exact Subtype.ext (F.coe_supportedHZeroEquiv_supportedHRestrict S (leOfHom f.unop) x)

@[simp]
lemma coe_supportedHPresheafZeroIso_hom_app_apply (W : (Opens X)ᵒᵖ)
    (x : F.supportedH S W.unop 0) :
    Subtype.val (p := (· ∈ F.supportedSections S W.unop))
      ((F.supportedHPresheafZeroIso S).hom.app W x) =
      F.supportedHZeroEquiv S W.unop x :=
  (rfl)

/-- The local cohomology sheaf `𝓗_Sⁿ(F)` of `F` with supports in the closed subset `S`: the
sheafification of the presheaf `W ↦ H_Sⁿ(W, F)` of cohomology with supports in `S`. -/
abbrev supportedHSheaf (n : ℕ) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (F.supportedHPresheaf S n)

/-- The degree-zero local cohomology sheaf is the sheaf of sections supported in `S`:
`𝓗_S⁰(F) ≅ Γ_S(F)`. -/
def supportedHSheafZeroIso : F.supportedHSheaf S 0 ≅ F.supportedSectionsSheaf S :=
  (presheafToSheaf _ _).mapIso (F.supportedHPresheafZeroIso S) ≪≫
    (sheafificationIso (F.supportedSectionsSheaf S)).symm

/-- The isomorphism `𝓗_S⁰(F) ≅ Γ_S(F)` is compatible with the canonical maps from the presheaf
`W ↦ H_S⁰(W, F)`: composed with the sheafification map, it is
`CategoryTheory.Sheaf.supportedHPresheafZeroIso`. -/
@[reassoc (attr := simp)]
lemma toSheafify_supportedHSheafZeroIso_hom :
    toSheafify (Opens.grothendieckTopology X) (F.supportedHPresheaf S 0) ≫
        (F.supportedHSheafZeroIso S).hom.hom =
      (F.supportedHPresheafZeroIso S).hom := by
  simp [supportedHSheafZeroIso]

/-- The local cohomology sheaves `𝓗_Sⁿ(F)` are supported in `S`: their stalks at points outside
`S` vanish. -/
theorem isZero_stalk_supportedHSheaf_of_notMem {x : X} (hx : x ∉ S) (n : ℕ) :
    IsZero (TopCat.Presheaf.stalk (F.supportedHSheaf S n).obj x) := by
  rw [TopCat.Presheaf.isZero_stalk_sheafify_iff]
  -- a class on `W ∋ x` restricts to zero on `W ∖ S`, where cohomology with supports vanishes
  refine (TopCat.Presheaf.isZero_stalk_iff _ x).2 fun W s hxW ↦
    ⟨W ⊓ S.compl, inf_le_left, ⟨hxW, hx⟩, ?_⟩
  have := F.subsingleton_supportedH_of_le_compl S (inf_le_right : W ⊓ S.compl ≤ S.compl) n
  exact Subsingleton.elim (α := F.supportedH S (W ⊓ S.compl) n) _ _

/-- A flasque sheaf has no local cohomology sheaves in positive degrees. -/
theorem isZero_supportedHSheaf_succ_of_isFlasque [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    IsZero (F.supportedHSheaf S (n + 1)) :=
  (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).2 fun _ W _ hxW ↦
    ⟨W, le_rfl, hxW, Subsingleton.elim (α := F.supportedH S W (n + 1)) _ _⟩

end

end Sheaf

end CategoryTheory
