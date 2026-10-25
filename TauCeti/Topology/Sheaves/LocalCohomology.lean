/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Stalks
public import TauCeti.Topology.Sheaves.SupportedCohomology
import Mathlib.Topology.Sheaves.LocallySurjective

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

The sheaves `Γ_S(F)` form the left exact *supported-section functor* `Γ_S`
(`CategoryTheory.Sheaf.supportedSectionsFunctor`). For a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `𝓗_S¹(F₁) = 0`, the sequence `0 ⟶ Γ_S(F₁) ⟶ Γ_S(F₂) ⟶ Γ_S(F₃) ⟶ 0`
is short exact: a section of `F₃` supported in `S` defines a class in `H_S¹(W, F₁)` which vanishes
locally, so the section lifts locally. The main result is *support truncation*: if `𝓗_S^q(F) = 0`
for all `q < n`, then `H_S^q(W, F) = 0` for all `q < n` and every open `W`. It is proved by
dimension shifting along an embedding `F ⟶ I` into an injective sheaf, for the more general
statement where `Γ_S(F)` is only assumed flasque and `𝓗_S^q(F) = 0` for `0 < q < n`: the quotient
`I / F` again has `Γ_S(I / F)` flasque, as a quotient of the flasque sheaf `Γ_S(I)` by `Γ_S(F)`, and
the connecting maps `H_S^q(W, I / F) ⟶ H_S^{q+1}(W, F)` are bijective for `q > 0`. This is the
form in which purity of local cohomology, the vanishing of `𝓗_S^q(F)` below the codimension, gives
the vanishing of the global groups `H_S^q(W, F)`.

The *edge comparison* is the next step of the same argument. If `𝓗_S^q(F) = 0` for all `q < n`,
then the presheaf `W ↦ H_Sⁿ(W, F)` is already a sheaf, so the sheafification map identifies
`H_Sⁿ(W, F)` with the sections of `𝓗_Sⁿ(F)` over `W`. In degree one, for `Γ_S(F)` flasque, the
connecting maps identify `H_S¹(-, F)` with the cokernel sheaf of `Γ_S(I) ⟶ Γ_S(I / F)`, whose
sections are computed objectwise because `Γ_S(F)` and `Γ_S(I)` are flasque; in higher degrees the
connecting maps form an isomorphism of presheaves `H_Sⁿ(-, I / F) ≅ H_Sⁿ⁺¹(-, F)`. Together with
the long exact sequence of supports and support truncation this gives the degenerate edge
comparison `H_Zⁿ(W, F) ≃+ Γ_Z(W, 𝓗_Sⁿ(F))` for closed `Z ≤ S`, compatible with restriction: the
`j = 0` case of `H_Z^{n+j}(W, F) ≃ H_Z^j(W, 𝓗_Sⁿ(F))`, which holds when `𝓗_S^q(F) = 0` for all
`q ≠ n`. For a real-analytic manifold `M` of dimension `n` in a complexification, where purity
gives `𝓗_M^q(𝓞) = 0` for `q ≠ n`, this identifies the sections of `𝓗_Mⁿ(𝓞)` over `W` with
`H_Mⁿ(W, 𝓞)`.

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
* `CategoryTheory.Sheaf.supportedSectionsFunctor S`: the supported-section functor `Γ_S`, which
  is left exact (`CategoryTheory.Sheaf.exact_map_supportedSectionsFunctor`) and through which
  `H_S⁰(W, F) ≃+ Γ_S(W, F)` is natural in `F`
  (`CategoryTheory.Sheaf.supportedHZeroEquiv_naturality_right`);
* `CategoryTheory.Sheaf.shortExact_map_supportedSectionsFunctor`: `Γ_S` preserves a short exact
  sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` with `𝓗_S¹(F₁) = 0`;
* `CategoryTheory.Sheaf.subsingleton_supportedH_of_isZero_supportedHSheaf`: support truncation.
* `CategoryTheory.Sheaf.isSheaf_supportedHPresheaf_of_isZero_supportedHSheaf`: if `𝓗_S^q(F) = 0`
  for `q < n`, the presheaf `W ↦ H_Sⁿ(W, F)` is a sheaf;
* `CategoryTheory.Sheaf.supportedHSectionsEquiv`: under the same hypothesis,
  `H_Sⁿ(W, F) ≃+ 𝓗_Sⁿ(F)(W)`, given by the sheafification map;
* `CategoryTheory.Sheaf.supportedHEdgeEquiv`: the degenerate edge comparison
  `H_Zⁿ(W, F) ≃+ Γ_Z(W, 𝓗_Sⁿ(F))` for closed `Z ≤ S`.

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

/-- If the local cohomology sheaf `𝓗_S⁰(F)` vanishes, so does the presheaf of sections of `F`
supported in `S`. -/
theorem isZero_supportedSectionsSheaf_obj (h : IsZero (F.supportedHSheaf S 0)) :
    IsZero (F.supportedSectionsSheaf S).obj :=
  (sheafToPresheaf _ _).map_isZero (h.of_iso (F.supportedHSheafZeroIso S).symm)

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

/-- If the local cohomology sheaf `𝓗_Sⁿ(F)` vanishes, then every class in `H_Sⁿ(W, F)` vanishes
locally: each point `x ∈ W` has an open neighbourhood `V ≤ W` on which the class restricts to
zero. -/
theorem exists_supportedHRestrict_eq_zero_of_isZero_supportedHSheaf {n : ℕ}
    (h : IsZero (F.supportedHSheaf S n)) {W : Opens X} (c : F.supportedH S W n) {x : X}
    (hx : x ∈ W) : ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧ F.supportedHRestrict S hVW n c = 0 := by
  obtain ⟨V, hVW, hxV, hV⟩ := (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).1 h x W c hx
  simp only [supportedHPresheaf_map] at hV
  exact ⟨V, hVW, hxV, hV⟩

section functor

variable {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- The supported-section functor `Γ_S`, sending a sheaf `F` to the sheaf `Γ_S(F)` of sections
supported in the closed subset `S`, and a morphism of sheaves to its restriction to supported
sections. -/
@[simps obj]
abbrev supportedSectionsFunctor :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} where
  obj F := F.supportedSectionsSheaf S
  map {F G} f :=
    supportedSectionsLift (F.supportedSectionsι S ≫ f) fun W s ↦ map_mem_supportedSections f
      (range_supportedSectionsι_hom_app F S W ▸ AddMonoidHom.mem_range.2 ⟨s, rfl⟩)
  map_id F := by
    rw [← cancel_mono (F.supportedSectionsι S)]
    simp
  map_comp {_ _ H} f g := by
    rw [← cancel_mono (H.supportedSectionsι S)]
    simp

@[reassoc]
lemma supportedSectionsFunctor_map_ι (f : F ⟶ G) :
    (supportedSectionsFunctor S).map f ≫ G.supportedSectionsι S = F.supportedSectionsι S ≫ f :=
  supportedSectionsLift_ι _ _

@[simp]
lemma coe_supportedSectionsFunctor_map_hom_app_apply (f : F ⟶ G) (W : (Opens X)ᵒᵖ)
    (s : F.supportedSections S W.unop) :
    Subtype.val (p := (· ∈ G.supportedSections S W.unop))
      (((supportedSectionsFunctor S).map f).hom.app W s) = f.hom.app W s :=
  (rfl)

/-- The equivalence `supportedHZeroEquiv : H_S⁰(W, F) ≃+ Γ_S(W, F)` is natural in the sheaf. -/
lemma supportedHZeroEquiv_naturality_right (f : F ⟶ G) (W : Opens X) (x : F.supportedH S W 0) :
    G.supportedHZeroEquiv S W (x.comp (Abelian.Ext.mk₀ f) (add_zero 0)) =
      ((supportedSectionsFunctor S).map f).hom.app (op W) (F.supportedHZeroEquiv S W x) :=
  Subtype.ext <| (coe_supportedHZeroEquiv_apply G S W _).trans <|
    (relativeH'.coe_zeroEquiv_naturality_right (S.complInclusion W) f x).trans
      congr(f.hom.app (op W) $((coe_supportedHZeroEquiv_apply F S W x).symm))

instance mono_supportedSectionsFunctor_map (f : F ⟶ G) [Mono f] :
    Mono ((supportedSectionsFunctor S).map f) := by
  have : Mono ((supportedSectionsFunctor S).map f ≫ G.supportedSectionsι S) := by
    rw [supportedSectionsFunctor_map_ι]
    infer_instance
  exact mono_of_mono _ (G.supportedSectionsι S)

instance additive_supportedSectionsFunctor : (supportedSectionsFunctor S).Additive where
  map_add {F G f g} := (cancel_mono (G.supportedSectionsι S)).1 (by simp)

end functor

section truncation

open Abelian

variable {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- `Γ_S` applied to the first term of a short complex is flasque when `Γ_S(F₁)` is. -/
instance isFlasque_map_supportedSectionsFunctor_X₁
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj] :
    TopCat.Sheaf.IsFlasque (T.map (supportedSectionsFunctor S)).X₁ :=
  ‹_›

/-- `Γ_S` applied to the second term of a short complex is flasque when `Γ_S(F₂)` is. -/
instance isFlasque_map_supportedSectionsFunctor_X₂
    [TopCat.Presheaf.IsFlasque (T.X₂.supportedSectionsSheaf S).obj] :
    TopCat.Sheaf.IsFlasque (T.map (supportedSectionsFunctor S)).X₂ :=
  ‹_›

/-- The supported-section functor is left exact: it maps an exact sequence `F₁ ⟶ F₂ ⟶ F₃` whose
first map is a monomorphism to an exact sequence `Γ_S(F₁) ⟶ Γ_S(F₂) ⟶ Γ_S(F₃)`. -/
theorem exact_map_supportedSectionsFunctor (hT : T.Exact) [Mono T.f] :
    (T.map (supportedSectionsFunctor S)).Exact := by
  have hinj (W : (Opens X)ᵒᵖ) : Function.Injective (T.f.hom.app W) := by
    have := (Sheaf.Hom.mono_iff_presheaf_mono _ _ T.f).1 inferInstance
    exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hlift {Z} (φ : Z ⟶ T.X₂.supportedSectionsSheaf S)
      (hφ : φ ≫ (supportedSectionsFunctor S).map T.g = 0) :
      (φ ≫ T.X₂.supportedSectionsι S) ≫ T.g = 0 := by
    rw [Category.assoc, ← supportedSectionsFunctor_map_ι, reassoc_of% hφ, zero_comp]
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun {Z} φ hφ ↦ supportedSectionsLift (hT.lift _ (hlift φ hφ)) fun W s ↦ ?_)
    (fun φ hφ ↦ ?_) (fun φ hφ m hm ↦ ?_))
  · -- a section of `F₁` whose image in `F₂` is supported in `S` is supported in `S`
    rw [mem_supportedSections_iff]
    refine hinj _ ?_
    have hk := congr($(hT.lift_f _ (hlift φ hφ)).hom.app W s)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply] at hk
    rw [map_zero, NatTrans.naturality_apply, hk]
    exact (mem_supportedSections_iff _).1 (φ.hom.app W s).2
  · rw [← cancel_mono (T.X₂.supportedSectionsι S)]
    simp
  · rw [← cancel_mono (T.X₁.supportedSectionsι S), ← cancel_mono T.f]
    simp [← hm]

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and the local cohomology sheaf `𝓗_S¹(F₁)` vanishes,
then `Γ_S(F₂) ⟶ Γ_S(F₃)` is an epimorphism: a section of `F₃` supported in `S` lifts locally to a
section of `F₂` supported in `S`. -/
theorem epi_supportedSectionsFunctor_map_g (hT : T.ShortExact)
    (h : IsZero (T.X₁.supportedHSheaf S 1)) : Epi ((supportedSectionsFunctor S).map T.g) := by
  refine (TopCat.Sheaf.isLocallySurjective_iff_epi _).1 ?_
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro W s x hx
  -- the class `y` of `s` in `H_S⁰(W, F₃)` has image in `H_S¹(W, F₁)` vanishing near `x`
  obtain ⟨y, rfl⟩ := (T.X₃.supportedHZeroEquiv S W).surjective s
  obtain ⟨V, hVW, hxV, hV⟩ :=
    T.X₁.exists_supportedHRestrict_eq_zero_of_isZero_supportedHSheaf S h (y.comp hT.extClass rfl) hx
  rw [supportedHRestrict_comp] at hV
  -- so near `x` the class `y` comes from a section of `F₂` supported in `S`
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1) hV
  refine ⟨V, hVW, ⟨T.X₂.supportedHZeroEquiv S V z, ?_⟩, hxV⟩
  rw [← supportedHZeroEquiv_naturality_right, hz]
  exact Subtype.ext (coe_supportedHZeroEquiv_supportedHRestrict ..)

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and the local cohomology sheaf `𝓗_S¹(F₁)` vanishes,
then `0 ⟶ Γ_S(F₁) ⟶ Γ_S(F₂) ⟶ Γ_S(F₃) ⟶ 0` is short exact. -/
theorem shortExact_map_supportedSectionsFunctor (hT : T.ShortExact)
    (h : IsZero (T.X₁.supportedHSheaf S 1)) : (T.map (supportedSectionsFunctor S)).ShortExact :=
  have := hT.mono_f
  { exact := exact_map_supportedSectionsFunctor S hT.exact
    mono_f := mono_supportedSectionsFunctor_map S T.f
    epi_g := epi_supportedSectionsFunctor_map_g S hT h }

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` flasque and `𝓗_Sⁿ⁺²(F₁) = 0`, then
`𝓗_Sⁿ⁺¹(F₃) = 0`. -/
theorem isZero_supportedHSheaf_X₃_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] {n : ℕ} (h : IsZero (T.X₁.supportedHSheaf S (n + 2))) :
    IsZero (T.X₃.supportedHSheaf S (n + 1)) := by
  refine (TopCat.Presheaf.isZero_presheafToSheaf_obj_iff _).2 fun x W c hx ↦ ?_
  obtain ⟨V, hVW, hxV, hV⟩ :=
    T.X₁.exists_supportedHRestrict_eq_zero_of_isZero_supportedHSheaf S h (c.comp hT.extClass rfl) hx
  -- the connecting map commutes with restriction to `V`, where it is injective
  exact ⟨V, hVW, hxV, (relativeH'.extClass_postcomp_bijective_of_isFlasque hT
    (S.complInclusion V) n).1
    (((T.X₃.supportedHRestrict_comp S hVW c hT.extClass rfl).symm.trans hV).trans
      (map_zero _).symm)⟩

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` flasque, `Γ_S(F₁)` flasque and
`𝓗_S¹(F₁) = 0`, then `H_S¹(W, F₁) = 0` for every open `W`. -/
theorem subsingleton_supportedH_one_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj]
    (h : IsZero (T.X₁.supportedHSheaf S 1)) (W : Opens X) :
    Subsingleton (T.X₁.supportedH S W 1) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  -- `x` is the connecting image of a class `y` in `H_S⁰(W, F₃)`, which comes from `H_S⁰(W, F₂)`
  -- because `Γ_S(F₂) ⟶ Γ_S(F₃)` is surjective on sections, `Γ_S(F₁)` being flasque
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT x (Subsingleton.elim _ _) (zero_add 1)
  have hΓ := shortExact_map_supportedSectionsFunctor S hT h
  obtain ⟨t, ht⟩ := (AddCommGrpCat.epi_iff_surjective _).1
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact hΓ (U := W)) (T.X₃.supportedHZeroEquiv S W y)
  obtain ⟨z, rfl⟩ := (T.X₂.supportedHZeroEquiv S W).surjective t
  have hy : z.comp (Ext.mk₀ T.g) (add_zero 0) = y :=
    (T.X₃.supportedHZeroEquiv S W).injective
      ((supportedHZeroEquiv_naturality_right S T.g W z).trans ht)
  rw [← hy, Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]

/-- The dimension-shifting form of support truncation: if `Γ_S(F)` is flasque and the local
cohomology sheaves `𝓗_S^{q+1}(F)` vanish for `q < n`, then `H_S^{q+1}(W, F) = 0` for every
`q < n` and every open `W`. -/
theorem subsingleton_supportedH_succ_of_isZero_supportedHSheaf_succ
    [TopCat.Presheaf.IsFlasque (F.supportedSectionsSheaf S).obj] {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedHSheaf S (q + 1))) {q : ℕ} (hq : q < n) (W : Opens X) :
    Subsingleton (F.supportedH S W (q + 1)) := by
  induction n generalizing F q with
  | zero => omega
  | succ n ih =>
    -- embed `F` into an injective sheaf `F₂ = I(F)` with quotient `F₃`
    let T := TauCeti.injectiveCokernelSequence F
    have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    have h₁ : IsZero (T.X₁.supportedHSheaf S 1) := h 0 (by omega)
    -- `Γ_S(F₃)` is flasque, as the quotient of the flasque sheaf `Γ_S(F₂)` by `Γ_S(F)`
    have : TopCat.Presheaf.IsFlasque (T.X₃.supportedSectionsSheaf S).obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (shortExact_map_supportedSectionsFunctor S hT h₁)
    rcases q with _ | q
    · exact subsingleton_supportedH_one_of_shortExact S hT h₁ W
    · have := ih T.X₃ (fun q hq ↦ isZero_supportedHSheaf_X₃_of_shortExact S hT (h (q + 1)
        (by omega))) (q := q) (by omega)
      exact (relativeH'.extClass_postcomp_bijective_of_isFlasque hT (S.complInclusion W)
        q).2.subsingleton

/-- **Support truncation.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`,
then the cohomology groups `H_S^q(W, F)` with supports in `S` vanish for all `q < n` and every
open `W`. -/
theorem subsingleton_supportedH_of_isZero_supportedHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) {q : ℕ} (hq : q < n) (W : Opens X) :
    Subsingleton (F.supportedH S W q) := by
  have hΓ := F.isZero_supportedSectionsSheaf_obj S (h 0 (by omega))
  rcases q with _ | q
  · have : Subsingleton (F.supportedSections S W) :=
      AddCommGrpCat.subsingleton_of_isZero (hΓ.obj (op W))
    exact (F.supportedHZeroEquiv S W).injective.subsingleton
  · have := TopCat.Presheaf.IsFlasque.of_isZero hΓ
    exact subsingleton_supportedH_succ_of_isZero_supportedHSheaf_succ F S
      (fun q hq ↦ h (q + 1) (by omega)) (by omega : q < n - 1) W

end truncation

section edge

open Abelian

variable {T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}

/-- The connecting morphism `H_Sⁿ(-, F₃) ⟶ H_Sⁿ⁺¹(-, F₁)` of presheaves of cohomology with
supports attached to a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves. -/
def supportedHPresheafδ (hT : T.ShortExact) (n : ℕ) :
    T.X₃.supportedHPresheaf S n ⟶ T.X₁.supportedHPresheaf S (n + 1) where
  app W := AddCommGrpCat.ofHom (hT.extClass.postcomp _ rfl)
  naturality W W' f := by
    ext x
    exact (T.X₃.supportedHRestrict_comp S (leOfHom f.unop) x hT.extClass rfl).symm

/-- The connecting morphism of presheaves is the Yoneda product with the class of the short exact
sequence. -/
@[simp]
lemma supportedHPresheafδ_app_apply (hT : T.ShortExact) (n : ℕ) (W : (Opens X)ᵒᵖ)
    (x : T.X₃.supportedH S W.unop n) :
    (supportedHPresheafδ S hT n).app W x = x.comp hT.extClass rfl :=
  (rfl)

/-- If `F₂` is flasque, the connecting morphism `H_Sⁿ⁺¹(-, F₃) ⟶ H_Sⁿ⁺²(-, F₁)` is an
isomorphism of presheaves. -/
instance isIso_supportedHPresheafδ_succ (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    (n : ℕ) : IsIso (supportedHPresheafδ S hT (n + 1)) := by
  have (W : (Opens X)ᵒᵖ) : IsIso ((supportedHPresheafδ S hT (n + 1)).app W) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (relativeH'.extClass_postcomp_bijective_of_isFlasque hT (S.complInclusion W.unop) n)
  exact NatIso.isIso_of_isIso_app _

/-- Under `CategoryTheory.Sheaf.supportedHZeroEquiv`, the image of a supported section of `F₂`
in `F₃` corresponds to the image of its class. -/
private lemma supportedHZeroEquiv_symm_map_g (W : (Opens X)ᵒᵖ)
    (s : (T.X₂.supportedSectionsSheaf S).obj.obj W) :
    (T.X₃.supportedHZeroEquiv S W.unop).symm
        (((supportedSectionsFunctor S).map T.g).hom.app W s) =
      ((T.X₂.supportedHZeroEquiv S W.unop).symm s).comp (Ext.mk₀ T.g) (add_zero 0) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [supportedHZeroEquiv_naturality_right]
  exact congrArg _ (AddEquiv.apply_symm_apply _ s).symm

/-- The degree-zero connecting maps `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`, as a morphism of presheaves. -/
private abbrev supportedHPresheafδZero (hT : T.ShortExact) :
    (T.X₃.supportedSectionsSheaf S).obj ⟶ T.X₁.supportedHPresheaf S 1 :=
  (T.X₃.supportedHPresheafZeroIso S).inv ≫ supportedHPresheafδ S hT 0

private lemma supportedHPresheafδZero_app_apply (hT : T.ShortExact) (W : (Opens X)ᵒᵖ)
    (s : (T.X₃.supportedSectionsSheaf S).obj.obj W) :
    (supportedHPresheafδZero S hT).app W s =
      ((T.X₃.supportedHZeroEquiv S W.unop).symm s).comp hT.extClass (zero_add 1) :=
  (rfl)

/-- The short complex `Γ_S(W, F₂) ⟶ Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` of a short exact sequence
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`. -/
private abbrev supportedHδZeroComplex (hT : T.ShortExact) (W : Opens X) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk ((T.map (supportedSectionsFunctor S)).g.hom.app (op W))
    ((supportedHPresheafδZero S hT).app (op W)) <| by
      ext s
      refine (congrArg (fun z ↦ z.comp hT.extClass (zero_add 1))
        (supportedHZeroEquiv_symm_map_g S (op W) s)).trans ?_
      rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero]
      rfl

/-- If `F₂` is flasque, the degree-zero connecting map `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)` is surjective
with kernel the image of `Γ_S(W, F₂)`. -/
private lemma exact_supportedHδZeroComplex (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj] (W : Opens X) :
    (supportedHδZeroComplex S hT W).Exact ∧ Epi (supportedHδZeroComplex S hT W).g := by
  refine ⟨(ShortComplex.ab_exact_iff _).2 fun s hs ↦ ?_,
    (AddCommGrpCat.epi_iff_surjective _).2 fun c ↦ ?_⟩
  · obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ _ hT _ (zero_add 1) hs
    refine ⟨T.X₂.supportedHZeroEquiv S W z, ?_⟩
    apply (T.X₃.supportedHZeroEquiv S W).symm.injective
    refine (supportedHZeroEquiv_symm_map_g S (op W) _).trans ?_
    rw [AddEquiv.symm_apply_apply]
    exact hz
  · obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hT c (Subsingleton.elim _ _) (zero_add 1)
    refine ⟨T.X₃.supportedHZeroEquiv S W y, ?_⟩
    exact (supportedHPresheafδZero_app_apply S hT (op W) _).trans
      (by rw [AddEquiv.symm_apply_apply])

/-- If `F₂` is flasque, `H_S¹(W, F₁)` is the cokernel of `Γ_S(W, F₂) ⟶ Γ_S(W, F₃)`, through the
degree-zero connecting map. -/
private def isColimitSupportedHδZero (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    (W : Opens X) :
    IsColimit (CokernelCofork.ofπ _ (supportedHδZeroComplex S hT W).zero) :=
  have := (exact_supportedHδZeroComplex S hT W).2
  (exact_supportedHδZeroComplex S hT W).1.gIsCokernel

/-- If `F₂` and `Γ_S(F₁)` are flasque, the sections over `W` of the cokernel sheaf of
`Γ_S(F₂) ⟶ Γ_S(F₃)` are the cokernel of `Γ_S(W, F₂) ⟶ Γ_S(W, F₃)`. -/
private def isColimitCokernelπApp (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj] (W : Opens X) :
    IsColimit (CokernelCofork.ofπ (f := (T.map (supportedSectionsFunctor S)).g.hom.app (op W))
      ((cokernel.π (T.map (supportedSectionsFunctor S)).g).hom.app (op W))
      (by simp [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom])) :=
  have := hT.mono_f
  have : Mono (T.map (supportedSectionsFunctor S)).f := mono_supportedSectionsFunctor_map S T.f
  have hT' := exact_map_supportedSectionsFunctor S hT.exact
  have := TopCat.Sheaf.IsFlasque.epi_cokernel_π_app hT' W
  (TopCat.Sheaf.IsFlasque.exact_cokernel_π_app hT' W).gIsCokernel

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, `H_S¹(W, F₁)` is
the group of sections over `W` of the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)`. -/
private def supportedHOneIsoCokernel (hT : T.ShortExact) [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj] (W : Opens X) :
    (T.X₁.supportedHPresheaf S 1).obj (op W) ≅
      (cokernel (T.map (supportedSectionsFunctor S)).g).obj.obj (op W) :=
  IsColimit.coconePointUniqueUpToIso (isColimitSupportedHδZero S hT W)
    (isColimitCokernelπApp S hT W)

@[reassoc]
private lemma supportedHPresheafδZero_supportedHOneIsoCokernel (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj] (W : Opens X) :
    (supportedHPresheafδZero S hT).app (op W) ≫ (supportedHOneIsoCokernel S hT W).hom =
      (cokernel.π (T.map (supportedSectionsFunctor S)).g).hom.app (op W) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (isColimitSupportedHδZero S hT W)
    (isColimitCokernelπApp S hT W) WalkingParallelPair.one

/-- If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact with `F₂` and `Γ_S(F₁)` flasque, the presheaf
`W ↦ H_S¹(W, F₁)` is a sheaf: it is isomorphic to the cokernel of `Γ_S(F₂) ⟶ Γ_S(F₃)` in
sheaves. -/
theorem isSheaf_supportedHPresheaf_one_of_shortExact (hT : T.ShortExact)
    [TopCat.Presheaf.IsFlasque T.X₂.obj]
    [TopCat.Presheaf.IsFlasque (T.X₁.supportedSectionsSheaf S).obj] :
    (T.X₁.supportedHPresheaf S 1).IsSheaf := by
  refine (Presheaf.isSheaf_of_iso_iff (NatIso.ofComponents
    (fun W ↦ supportedHOneIsoCokernel S hT W.unop) fun {W W'} f ↦ ?_)).2
    (cokernel (T.map (supportedSectionsFunctor S)).g).property
  -- both composites agree after precomposing with the epimorphism `Γ_S(W, F₃) ⟶ H_S¹(W, F₁)`
  have := (exact_supportedHδZeroComplex S hT W.unop).2
  rw [← cancel_epi ((supportedHPresheafδZero S hT).app W), ← NatTrans.naturality_assoc,
    supportedHPresheafδZero_supportedHOneIsoCokernel,
    supportedHPresheafδZero_supportedHOneIsoCokernel_assoc]
  exact (cokernel.π (T.map (supportedSectionsFunctor S)).g).hom.naturality f

/-- The dimension-shifting form of the edge comparison: if `Γ_S(F)` is flasque and the local
cohomology sheaves `𝓗_S^{q+1}(F)` vanish for `q < n`, then the presheaf `W ↦ H_Sⁿ⁺¹(W, F)` is a
sheaf. -/
theorem isSheaf_supportedHPresheaf_succ_of_isZero_supportedHSheaf_succ
    [TopCat.Presheaf.IsFlasque (F.supportedSectionsSheaf S).obj] {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedHSheaf S (q + 1))) :
    (F.supportedHPresheaf S (n + 1)).IsSheaf := by
  induction n generalizing F with
  | zero =>
    exact isSheaf_supportedHPresheaf_one_of_shortExact (T := TauCeti.injectiveCokernelSequence F) S
      (TauCeti.injectiveCokernelSequence_shortExact F)
  | succ n ih =>
    -- embed `F` into an injective sheaf `F₂ = I(F)` with quotient `F₃`
    let T := TauCeti.injectiveCokernelSequence F
    have hT : T.ShortExact := TauCeti.injectiveCokernelSequence_shortExact F
    -- `Γ_S(F₃)` is flasque, as the quotient of the flasque sheaf `Γ_S(F₂)` by `Γ_S(F)`
    have : TopCat.Presheaf.IsFlasque (T.X₃.supportedSectionsSheaf S).obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (shortExact_map_supportedSectionsFunctor S hT (h 0 (by omega)))
    -- and `H_Sⁿ⁺¹(-, F₃) ≅ H_Sⁿ⁺²(-, F)` by the connecting isomorphism
    have := isIso_supportedHPresheafδ_succ S hT n
    exact (Presheaf.isSheaf_of_iso_iff (asIso (supportedHPresheafδ S hT (n + 1)))).1
      (ih T.X₃ fun q hq ↦ isZero_supportedHSheaf_X₃_of_shortExact S hT (h (q + 1) (by omega)))

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then the presheaf
`W ↦ H_Sⁿ(W, F)` of cohomology with supports in `S` is already a sheaf. -/
theorem isSheaf_supportedHPresheaf_of_isZero_supportedHSheaf {n : ℕ}
    (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) : (F.supportedHPresheaf S n).IsSheaf := by
  rcases n with _ | n
  · exact (Presheaf.isSheaf_of_iso_iff (F.supportedHPresheafZeroIso S)).2
      (F.isSheaf_supportedSectionsPresheaf S)
  · have : TopCat.Presheaf.IsFlasque (F.supportedSectionsSheaf S).obj :=
      TopCat.Presheaf.IsFlasque.of_isZero (F.isZero_supportedSectionsSheaf_obj S (h 0 (by omega)))
    exact F.isSheaf_supportedHPresheaf_succ_of_isZero_supportedHSheaf_succ S
      fun q hq ↦ h (q + 1) (by omega)

variable {n : ℕ}

/-- **Edge comparison.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, the
sheafification map identifies `H_Sⁿ(W, F)` with the sections of `𝓗_Sⁿ(F)` over `W`. -/
def supportedHSectionsEquiv (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) (W : Opens X) :
    F.supportedH S W n ≃+ (F.supportedHSheaf S n).obj.obj (op W) :=
  have := isIso_toSheafify _ (F.isSheaf_supportedHPresheaf_of_isZero_supportedHSheaf S h)
  (asIso ((toSheafify _ (F.supportedHPresheaf S n)).app (op W))).addCommGroupIsoToAddEquiv

/-- The edge comparison `H_Sⁿ(W, F) ≃+ 𝓗_Sⁿ(F)(W)` is the sheafification map. -/
@[simp]
lemma supportedHSectionsEquiv_apply (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) (W : Opens X)
    (x : F.supportedH S W n) :
    F.supportedHSectionsEquiv S h W x =
      (toSheafify (Opens.grothendieckTopology X) (F.supportedHPresheaf S n)).app (op W) x :=
  (rfl)

/-- The edge comparison `H_Sⁿ(W, F) ≃+ 𝓗_Sⁿ(F)(W)` is compatible with restriction to a smaller
open `W' ≤ W`. -/
lemma supportedHSectionsEquiv_supportedHRestrict (h : ∀ q < n, IsZero (F.supportedHSheaf S q))
    {W' W : Opens X} (hW : W' ≤ W) (x : F.supportedH S W n) :
    F.supportedHSectionsEquiv S h W' (F.supportedHRestrict S hW n x) =
      (F.supportedHSheaf S n).obj.map (homOfLE hW).op (F.supportedHSectionsEquiv S h W x) :=
  congr($((toSheafify _ (F.supportedHPresheaf S n)).naturality (homOfLE hW).op) x)

variable {S} {Z : Closeds X}

/-- If the local cohomology sheaves `𝓗_S^q(F)` vanish for all `q < n`, then enlarging the
support `H_Zⁿ(W, F) ⟶ H_Sⁿ(W, F)` is injective for every closed `Z ≤ S`. -/
theorem supportedHMap_injective_of_isZero_supportedHSheaf
    (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) (hZS : Z ≤ S) (W : Opens X) :
    Function.Injective (F.supportedHMap hZS W n) := by
  rcases n with _ | m
  · -- in degree zero, enlarging the support is the inclusion `Γ_Z(W, F) ≤ Γ_S(W, F)`
    intro x y hxy
    refine (F.supportedHZeroEquiv Z W).injective (Subtype.ext ?_)
    rw [← coe_supportedHZeroEquiv_supportedHMap F hZS, hxy, coe_supportedHZeroEquiv_supportedHMap]
  · -- the kernel is the image of `H_Sᵐ(W ∖ Z, F)`, which vanishes by support truncation
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (F.exact_supportedHδ_supportedHMap hZS W (add_comm 1 m) x).1 hx
    have := F.subsingleton_supportedH_of_isZero_supportedHSheaf S h (Nat.lt_succ_self m)
      (W ⊓ Z.compl)
    rw [Subsingleton.elim y 0, map_zero]

/-- **Degenerate edge comparison.** If the local cohomology sheaves `𝓗_S^q(F)` vanish for all
`q < n`, then for every closed `Z ≤ S` the cohomology `H_Zⁿ(W, F)` with supports in `Z` is the
group `Γ_Z(W, 𝓗_Sⁿ(F))` of sections of `𝓗_Sⁿ(F)` over `W` supported in `Z`, through enlarging
the support to `S` and the sheafification map. -/
def supportedHEdgeEquiv (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) (hZS : Z ≤ S)
    (W : Opens X) :
    F.supportedH Z W n ≃+ (F.supportedHSheaf S n).supportedSections Z W :=
  AddEquiv.ofBijective
    (((F.supportedHSectionsEquiv S h W).toAddMonoidHom.comp (F.supportedHMap hZS W n)).codRestrict
      _ fun x ↦ by
        -- the restriction to `W ∖ Z` of a class with supports in `Z` vanishes
        rw [mem_supportedSections_iff, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
          ← supportedHSectionsEquiv_supportedHRestrict F S h inf_le_left,
          (F.exact_supportedHMap_supportedHRestrict hZS W n).apply_apply_eq_zero, map_zero])
    ⟨fun x y hxy ↦ F.supportedHMap_injective_of_isZero_supportedHSheaf h hZS W
      ((F.supportedHSectionsEquiv S h W).injective (congrArg Subtype.val hxy)), fun s ↦ by
      obtain ⟨y, hy⟩ := (F.supportedHSectionsEquiv S h W).surjective s
      -- a class with supports in `S` comes from `Z` if it restricts to zero on `W ∖ Z`
      obtain ⟨x, rfl⟩ := (F.exact_supportedHMap_supportedHRestrict hZS W n y).1 <|
        (F.supportedHSectionsEquiv S h _).injective <| by
          rw [supportedHSectionsEquiv_supportedHRestrict, hy, map_zero]
          exact (mem_supportedSections_iff _).1 s.2
      exact ⟨x, Subtype.ext hy⟩⟩

/-- The degenerate edge comparison enlarges the support from `Z` to `S` and then applies the
sheafification map. -/
@[simp]
lemma coe_supportedHEdgeEquiv_apply (h : ∀ q < n, IsZero (F.supportedHSheaf S q)) (hZS : Z ≤ S)
    (W : Opens X) (x : F.supportedH Z W n) :
    (F.supportedHEdgeEquiv h hZS W x : (F.supportedHSheaf S n).obj.obj (op W)) =
      F.supportedHSectionsEquiv S h W (F.supportedHMap hZS W n x) :=
  (rfl)

/-- The degenerate edge comparison `H_Zⁿ(W, F) ≃+ Γ_Z(W, 𝓗_Sⁿ(F))` is compatible with
restriction to a smaller open `W' ≤ W`. -/
lemma coe_supportedHEdgeEquiv_supportedHRestrict (h : ∀ q < n, IsZero (F.supportedHSheaf S q))
    (hZS : Z ≤ S) {W' W : Opens X} (hW : W' ≤ W) (x : F.supportedH Z W n) :
    (F.supportedHEdgeEquiv h hZS W' (F.supportedHRestrict Z hW n x) :
        (F.supportedHSheaf S n).obj.obj (op W')) =
      (F.supportedHSheaf S n).obj.map (homOfLE hW).op (F.supportedHEdgeEquiv h hZS W x) := by
  simp only [coe_supportedHEdgeEquiv_apply, ← supportedHRestrict_supportedHMap,
    supportedHSectionsEquiv_supportedHRestrict]

end edge

end

end Sheaf

end CategoryTheory
