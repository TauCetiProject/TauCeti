/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Basic
public import TauCeti.CategoryTheory.Abelian.Subobject
public import TauCeti.CategoryTheory.Subobject.Basic
public import TauCeti.CategoryTheory.Subobject.Pullback
import Mathlib.CategoryTheory.Abelian.Refinements
import TauCeti.CategoryTheory.Subobject.Cokernel

/-!
# Subquotient presentations

A *subquotient presentation* of an object `X` inside an object `A` of an abelian category is a
pair of subobjects `B ≤ Z` of `A` together with an isomorphism from the cokernel of the inclusion
`B ⟶ Z` to `X`. The pages of a spectral sequence are presented this way inside its first page,
by the cycle and boundary subobjects (Stacks, Tag 011N, the construction after Definition 20.1;
Helle and Rognes, Lemma 2.2).

The projection `P.π : Z ⟶ X` of a presentation `P` is an epimorphism with kernel `B`, so by the
correspondence theorem taking preimages under `P.π` identifies the subobjects of `X` with the
interval `[B, Z]` of subobjects of `A` (`SubquotientPresentation.orderIso`), and this
identification carries greatest lower bounds and least upper bounds of nonempty families across in
both directions. Taking preimages of a presentation of `Y` inside `X` gives a presentation of `Y`
inside `A` (`SubquotientPresentation.trans`); in particular a pair `I ≤ K` of subobjects of `X`
gives a presentation of the cokernel of `I ⟶ K` inside `A` by the preimages of `I` and `K`
(`SubquotientPresentation.subquotient`). This composition is associative and has the identity
presentation `(⊥, ⊤)` of an object inside itself as a unit on both sides. For `I ≤ I′ ≤ K′ ≤ K`
in `X`, the presentation of the cokernel of `I′ ≤ K′` is, up to the identification of the
cokernels, the one obtained in two steps through the cokernel of `I ≤ K`.

## Main definitions

* `TauCeti.SubquotientPresentation A X`: a presentation of `X` as a subquotient of `A`.
* `TauCeti.SubquotientPresentation.π`: the projection `Z ⟶ X`.
* `TauCeti.SubquotientPresentation.ofEpi`: the presentation given by an epimorphism out of `Z`
  whose kernel is `B`.
* `TauCeti.SubquotientPresentation.preimage`, `TauCeti.SubquotientPresentation.image`: transport
  of subobjects between `X` and the interval `[B, Z]`.
* `TauCeti.SubquotientPresentation.orderIso`: the order isomorphism from the subobjects of `X`
  onto the interval `[B, Z]`.
* `TauCeti.SubquotientPresentation.trans`: the presentation inside `A` of an object presented
  inside `X`; `TauCeti.SubquotientPresentation.subquotient`: the presentation of the cokernel of a
  pair `I ≤ K` of subobjects of `X`.
* `TauCeti.SubquotientPresentation.refl`: the identity presentation `(⊥, ⊤)`.
* `TauCeti.SubquotientPresentation.mapIso`: transport along an isomorphism `X ≅ Y`.
* `TauCeti.SubquotientPresentation.isoOfEq`: the isomorphism between two objects presented by the
  same subobjects.

## Main results

* `TauCeti.SubquotientPresentation.isGLB_preimage_iff`,
  `TauCeti.SubquotientPresentation.isLUB_preimage_iff`: preimages preserve and reflect
  greatest lower bounds and least upper bounds of nonempty families; and
  `TauCeti.SubquotientPresentation.preimage_image_of_isGLB`,
  `TauCeti.SubquotientPresentation.preimage_image_of_isLUB`: such a bound of a family of preimages
  is itself a preimage.
* `TauCeti.SubquotientPresentation.preimage_trans`, `TauCeti.SubquotientPresentation.trans_assoc`:
  preimages compose, and composition of presentations is associative.
* `TauCeti.SubquotientPresentation.preimage_refl`, `TauCeti.SubquotientPresentation.trans_refl`,
  `TauCeti.SubquotientPresentation.refl_trans`: the identity presentation is a unit.
* `TauCeti.SubquotientPresentation.trans_subquotient_image`,
  `TauCeti.SubquotientPresentation.subquotient_subquotient_image`: naturality of the presentation
  of a cokernel.

## References

* [Stacks, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
* G. O. Helle and J. Rognes, *Boardman's whole-plane obstruction group for Cartan–Eilenberg
  systems*, Documenta Math. 24 (2019), 1855–1878, Lemma 2.2.
-/

public section

open CategoryTheory Limits Subobject

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A *subquotient presentation* of `X` inside `A`: subobjects `B ≤ Z` of `A` together with an
isomorphism from the cokernel of the inclusion `B ⟶ Z` to `X`. The isomorphism is data: two
presentations with the same subobjects may identify the quotient with `X` differently. -/
structure SubquotientPresentation (A X : C) where
  /-- The smaller subobject, which is divided out. -/
  B : Subobject A
  /-- The larger subobject, of which `X` is a quotient. -/
  Z : Subobject A
  /-- The smaller subobject lies below the larger one. -/
  le : B ≤ Z
  /-- The identification of the quotient `Z / B` with `X`. -/
  iso : cokernel (ofLE B Z le) ≅ X

namespace SubquotientPresentation

variable {A X Y W : C}

section Basic

variable (P : SubquotientPresentation A X)

/-- The projection of a subquotient presentation, from the larger subobject onto the presented
object. -/
noncomputable def π : (P.Z : C) ⟶ X :=
  cokernel.π (ofLE P.B P.Z P.le) ≫ P.iso.hom

@[reassoc (attr := simp)]
lemma cokernel_π_iso_hom : cokernel.π (ofLE P.B P.Z P.le) ≫ P.iso.hom = P.π := (rfl)

instance : Epi P.π := by
  rw [← cokernel_π_iso_hom]
  infer_instance

@[reassoc (attr := simp)]
lemma ofLE_π : ofLE P.B P.Z P.le ≫ P.π = 0 := by
  rw [← cokernel_π_iso_hom, cokernel.condition_assoc, zero_comp]

/-- The kernel of the projection is the smaller subobject, seen inside the larger one. -/
lemma kernelSubobject_π : kernelSubobject P.π = (Subobject.pullback P.Z.arrow).obj P.B := by
  rw [← cokernel_π_iso_hom, kernelSubobject_comp_mono, kernelSubobject_cokernel_π,
    pullback_arrow_of_le]

/-- The projection `P.π` exhibits `X` as the cokernel of the inclusion `P.B ⟶ P.Z`. -/
noncomputable def isColimit : IsColimit (CokernelCofork.ofπ P.π P.ofLE_π) :=
  IsColimit.ofIsoColimit (cokernelIsCokernel (ofLE P.B P.Z P.le)) (Cofork.ext P.iso rfl)

end Basic

/-- Two subquotient presentations are equal when they have the same subobjects and the same
projection. -/
@[ext (iff := false)]
lemma ext {P Q : SubquotientPresentation A X} (hB : P.B = Q.B) (hZ : P.Z = Q.Z)
    (hπ : P.π = ofLE P.Z Q.Z hZ.le ≫ Q.π) : P = Q := by
  obtain ⟨B, Z, le, iso⟩ := P
  obtain ⟨B', Z', le', iso'⟩ := Q
  obtain rfl : B = B' := hB
  obtain rfl : Z = Z' := hZ
  rw [ofLE_refl, Category.id_comp, ← cokernel_π_iso_hom, ← cokernel_π_iso_hom,
    cancel_epi] at hπ
  cases Iso.ext hπ
  rfl

section OfEpi

variable {B Z : Subobject A} (le : B ≤ Z) (g : (Z : C) ⟶ X) [Epi g]
  (hg : kernelSubobject g = (Subobject.pullback Z.arrow).obj B)

/-- The subquotient presentation given by an epimorphism `g` out of `Z` whose kernel is `B`. Its
projection is `g`. -/
@[expose] noncomputable def ofEpi : SubquotientPresentation A X where
  B := B
  Z := Z
  le := le
  iso := (cokernelIsCokernel _).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel _ (isLimitKernelForkOfLE le g hg))

@[simp]
lemma ofEpi_B : (ofEpi le g hg).B = B := (rfl)

@[simp]
lemma ofEpi_Z : (ofEpi le g hg).Z = Z := (rfl)

@[simp]
lemma π_ofEpi : (ofEpi le g hg).π = g :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom _ WalkingParallelPair.one

end OfEpi

/-- Every subquotient presentation is the one given by its projection. -/
lemma ofEpi_π (P : SubquotientPresentation A X) : ofEpi P.le P.π P.kernelSubobject_π = P :=
  ext rfl rfl (by
    rw [π_ofEpi]
    exact (ofLE_self_comp _ _).symm)

section Preimage

variable (P : SubquotientPresentation A X)

/-- The preimage of a subobject of `X` under the projection, as a subobject of `A`. -/
noncomputable def preimage (K : Subobject X) : Subobject A :=
  (map P.Z.arrow).obj ((Subobject.pullback P.π).obj K)

/-- The image of a subobject of `A`, intersected with the larger subobject, under the projection.
-/
noncomputable def image (S : Subobject A) : Subobject X :=
  («exists» P.π).obj ((Subobject.pullback P.Z.arrow).obj S)

/-- A morphism into the larger subobject lands in the preimage of `K` exactly when its composite
with the projection lands in `K`. -/
lemma factors_preimage_iff (K : Subobject X) (x : W ⟶ P.Z) :
    (P.preimage K).Factors (x ≫ P.Z.arrow) ↔ K.Factors (x ≫ P.π) := by
  rw [preimage, ← pullback_factors_iff, pullback_map_self, pullback_factors_iff]

/-- Seen inside the larger subobject, the preimage of `K` is the pullback of `K` along the
projection. -/
@[simp]
lemma pullback_Z_arrow_preimage (K : Subobject X) :
    (Subobject.pullback P.Z.arrow).obj (P.preimage K) = (Subobject.pullback P.π).obj K :=
  pullback_map_self _ _

lemma preimage_monotone : Monotone P.preimage :=
  fun _ _ h ↦ (map _).monotone ((Subobject.pullback _).monotone h)

lemma image_monotone : Monotone P.image :=
  fun _ _ h ↦ («exists» _).monotone ((Subobject.pullback _).monotone h)

lemma preimage_le_Z (K : Subobject X) : P.preimage K ≤ P.Z := by
  refine ((map _).monotone (le_top : _ ≤ ⊤)).trans_eq ?_
  rw [Subobject.map_top, mk_arrow]

@[simp]
lemma preimage_bot : P.preimage ⊥ = P.B := by
  rw [preimage, pullback_bot, kernelSubobject_π, map_pullback_arrow_of_le P.le]

@[simp]
lemma preimage_top : P.preimage ⊤ = P.Z := by
  rw [preimage, pullback_top, Subobject.map_top, mk_arrow]

lemma B_le_preimage (K : Subobject X) : P.B ≤ P.preimage K :=
  P.preimage_bot.symm.trans_le (P.preimage_monotone bot_le)

/-- The image of the preimage of a subobject of `X` is that subobject. -/
@[simp]
lemma image_preimage (K : Subobject X) : P.image (P.preimage K) = K := by
  rw [image, preimage, pullback_map_self, exists_pullback_eq_self_of_epi]

/-- A subobject of `A` in the interval `[B, Z]` is the preimage of its image. -/
lemma preimage_image {S : Subobject A} (h₁ : P.B ≤ S) (h₂ : S ≤ P.Z) :
    P.preimage (P.image S) = S := by
  rw [image, preimage, pullback_exists_eq_self_of_kernelSubobject_le,
    map_pullback_arrow_of_le h₂]
  rw [kernelSubobject_π]
  exact (Subobject.pullback _).monotone h₁

lemma preimage_injective : Function.Injective P.preimage :=
  Function.LeftInverse.injective P.image_preimage

@[simp]
lemma preimage_le_preimage_iff {K L : Subobject X} : P.preimage K ≤ P.preimage L ↔ K ≤ L :=
  ⟨fun h ↦ by simpa using P.image_monotone h, fun h ↦ P.preimage_monotone h⟩

@[simp]
lemma preimage_inj {K L : Subobject X} : P.preimage K = P.preimage L ↔ K = L :=
  P.preimage_injective.eq_iff

/-- Taking preimages under the projection is an order isomorphism from the subobjects of `X`
onto the interval `[B, Z]` of subobjects of `A`, with inverse the image. -/
noncomputable def orderIso : Subobject X ≃o Set.Icc P.B P.Z where
  toFun K := ⟨P.preimage K, P.B_le_preimage K, P.preimage_le_Z K⟩
  invFun S := P.image S
  left_inv := P.image_preimage
  right_inv S := Subtype.ext (P.preimage_image S.property.1 S.property.2)
  map_rel_iff' := P.preimage_le_preimage_iff

@[simp]
lemma coe_orderIso_apply (K : Subobject X) : (P.orderIso K : Subobject A) = P.preimage K := (rfl)

@[simp]
lemma orderIso_symm_apply (S : Set.Icc P.B P.Z) : P.orderIso.symm S = P.image S := (rfl)

end Preimage

section Bounds

variable (P : SubquotientPresentation A X) {s : Set (Subobject X)}

/-- A greatest lower bound of a nonempty family of preimages is itself a preimage. -/
lemma preimage_image_of_isGLB (hs : s.Nonempty) {S : Subobject A}
    (h : IsGLB (P.preimage '' s) S) : P.preimage (P.image S) = S := by
  obtain ⟨K, hK⟩ := hs
  exact P.preimage_image (h.2 (Set.forall_mem_image.2 fun L _ ↦ P.B_le_preimage L))
    ((h.1 (Set.mem_image_of_mem _ hK)).trans (P.preimage_le_Z K))

/-- A least upper bound of a nonempty family of preimages is itself a preimage. -/
lemma preimage_image_of_isLUB (hs : s.Nonempty) {S : Subobject A}
    (h : IsLUB (P.preimage '' s) S) : P.preimage (P.image S) = S := by
  obtain ⟨K, hK⟩ := hs
  exact P.preimage_image ((P.B_le_preimage K).trans (h.1 (Set.mem_image_of_mem _ hK)))
    (h.2 (Set.forall_mem_image.2 fun L _ ↦ P.preimage_le_Z L))

/-- Preimages preserve and reflect greatest lower bounds of nonempty families. -/
lemma isGLB_preimage_iff (hs : s.Nonempty) {K : Subobject X} :
    IsGLB (P.preimage '' s) (P.preimage K) ↔ IsGLB s K := by
  refine ⟨fun h ↦ h.of_image P.preimage_le_preimage_iff,
    fun h ↦ ⟨P.preimage_monotone.mem_lowerBounds_image h.1, fun S hS ↦ ?_⟩⟩
  -- `S ⊔ B` is still a lower bound, and it lies in the interval `[B, Z]`.
  obtain ⟨K₀, hK₀⟩ := hs
  have hlow : ∀ L ∈ s, S ⊔ P.B ≤ P.preimage L := fun L hL ↦
    sup_le (hS (Set.mem_image_of_mem _ hL)) (P.B_le_preimage L)
  have hmem := P.preimage_image le_sup_right ((hlow K₀ hK₀).trans (P.preimage_le_Z K₀))
  calc S ≤ S ⊔ P.B := le_sup_left
    _ = P.preimage (P.image (S ⊔ P.B)) := hmem.symm
    _ ≤ P.preimage K := P.preimage_monotone
      (h.2 fun L hL ↦ P.preimage_le_preimage_iff.1 (hmem.trans_le (hlow L hL)))

/-- Preimages preserve and reflect least upper bounds of nonempty families. -/
lemma isLUB_preimage_iff (hs : s.Nonempty) {K : Subobject X} :
    IsLUB (P.preimage '' s) (P.preimage K) ↔ IsLUB s K := by
  refine ⟨fun h ↦ h.of_image P.preimage_le_preimage_iff,
    fun h ↦ ⟨P.preimage_monotone.mem_upperBounds_image h.1, fun S hS ↦ ?_⟩⟩
  -- `S ⊓ Z` is still an upper bound, and it lies in the interval `[B, Z]`.
  obtain ⟨K₀, hK₀⟩ := hs
  have hup : ∀ L ∈ s, P.preimage L ≤ S ⊓ P.Z := fun L hL ↦
    le_inf (hS (Set.mem_image_of_mem _ hL)) (P.preimage_le_Z L)
  have hmem := P.preimage_image ((P.B_le_preimage K₀).trans (hup K₀ hK₀)) inf_le_right
  calc P.preimage K ≤ P.preimage (P.image (S ⊓ P.Z)) := P.preimage_monotone
        (h.2 fun L hL ↦ P.preimage_le_preimage_iff.1 ((hup L hL).trans_eq hmem.symm))
    _ = S ⊓ P.Z := hmem
    _ ≤ S := inf_le_left

end Bounds

section Trans

variable (P : SubquotientPresentation A X)

/-- The restriction of the projection to the preimage of `K`, as a morphism onto `K`. -/
noncomputable def preimageπ (K : Subobject X) : (P.preimage K : C) ⟶ (K : C) :=
  K.factorThru (ofLE _ _ (P.preimage_le_Z K) ≫ P.π)
    ((P.factors_preimage_iff K _).1 (by rw [ofLE_arrow]; exact factors_self _))

@[reassoc (attr := simp)]
lemma preimageπ_arrow (K : Subobject X) :
    P.preimageπ K ≫ K.arrow = ofLE _ _ (P.preimage_le_Z K) ≫ P.π :=
  factorThru_arrow _ _ _

@[reassoc]
lemma preimageπ_ofLE {K L : Subobject X} (h : K ≤ L) :
    P.preimageπ K ≫ ofLE K L h = ofLE _ _ (P.preimage_monotone h) ≫ P.preimageπ L := by
  rw [← cancel_mono L.arrow]
  simp [ofLE_comp_ofLE_assoc]

instance (K : Subobject X) : Epi (P.preimageπ K) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro W b
  obtain ⟨W', π', _, x, hx⟩ := surjective_up_to_refinements_of_epi P.π (b ≫ K.arrow)
  have hx' : (P.preimage K).Factors (x ≫ P.Z.arrow) :=
    (P.factors_preimage_iff K x).2 (by rw [← hx, ← Category.assoc]; exact factors_comp_arrow _)
  refine ⟨W', π', inferInstance, (P.preimage K).factorThru _ hx', ?_⟩
  have hy : (P.preimage K).factorThru _ hx' ≫ ofLE _ _ (P.preimage_le_Z K) = x := by
    rw [← cancel_mono P.Z.arrow, Category.assoc, ofLE_arrow, factorThru_arrow]
  rw [← cancel_mono K.arrow, Category.assoc, Category.assoc, preimageπ_arrow, reassoc_of% hy, hx]

/-- Seen inside the preimage of `K`, the preimage of `L` is the pullback along the restricted
projection of `L` seen inside `K`. -/
lemma pullback_arrow_preimage (K L : Subobject X) :
    (Subobject.pullback (P.preimage K).arrow).obj (P.preimage L) =
      (Subobject.pullback (P.preimageπ K)).obj ((Subobject.pullback K.arrow).obj L) := by
  rw [← pullback_comp, preimageπ_arrow, pullback_comp, ← ofLE_arrow (P.preimage_le_Z K),
    pullback_comp, pullback_Z_arrow_preimage]

/-- The subquotient presentation inside `A` of an object presented inside `X`: its subobjects
are the preimages of those of the presentation inside `X`. -/
@[expose] noncomputable def trans (Q : SubquotientPresentation X Y) : SubquotientPresentation A Y :=
  ofEpi (P.preimage_monotone Q.le) (P.preimageπ Q.Z ≫ Q.π) (by
    rw [← pullback_kernelSubobject, kernelSubobject_π, pullback_arrow_preimage])

variable (Q : SubquotientPresentation X Y)

@[simp]
lemma trans_B : (P.trans Q).B = P.preimage Q.B := (rfl)

@[simp]
lemma trans_Z : (P.trans Q).Z = P.preimage Q.Z := (rfl)

@[simp]
lemma π_trans : (P.trans Q).π = P.preimageπ Q.Z ≫ Q.π := π_ofEpi _ _ _

/-- The projection of a composite presentation, as a morphism out of `P.preimage Q.Z`. -/
lemma π_trans' :
    (P.trans Q).π = ofLE _ (P.preimage Q.Z) (P.trans_Z Q).le ≫ P.preimageπ Q.Z ≫ Q.π := by
  rw [π_trans]
  exact (ofLE_self_comp _ _).symm

/-- Taking preimages along a composite presentation is taking preimages twice. -/
@[simp]
lemma preimage_trans (K : Subobject Y) : (P.trans Q).preimage K = P.preimage (Q.preimage K) := by
  -- Inside `(P.trans Q).Z`, the preimage of `Q.Z`, both sides consist of the maps `x` with
  -- `x ≫ ρ ≫ Q.π` landing in `K`, where `ρ = P.preimageπ Q.Z` (read through `π_trans'`).
  have key : ∀ {V : C} (x : V ⟶ ((P.trans Q).Z : C)),
      ((P.trans Q).preimage K).Factors (x ≫ (P.trans Q).Z.arrow) ↔
        (P.preimage (Q.preimage K)).Factors (x ≫ (P.trans Q).Z.arrow) := fun x ↦ by
    rw [(P.trans Q).factors_preimage_iff, π_trans',
      ← ofLE_arrow ((P.trans_Z Q).le.trans (P.preimage_le_Z Q.Z)),
      ← ofLE_comp_ofLE _ _ _ (P.trans_Z Q).le (P.preimage_le_Z Q.Z)]
    simp only [← Category.assoc]
    rw [P.factors_preimage_iff]
    simp only [Category.assoc]
    rw [← preimageπ_arrow]
    simp only [← Category.assoc]
    rw [Q.factors_preimage_iff]
  have h₁ : (P.trans Q).preimage K ≤ (P.trans Q).Z := (P.trans Q).preimage_le_Z K
  have h₂ : P.preimage (Q.preimage K) ≤ (P.trans Q).Z :=
    (P.preimage_monotone (Q.preimage_le_Z K)).trans_eq (P.trans_Z Q).symm
  have k₁ := (key (ofLE _ _ h₁)).1
  have k₂ := (key (ofLE _ _ h₂)).2
  rw [ofLE_arrow] at k₁ k₂
  exact le_antisymm (le_of_factors (k₁ (factors_self _))) (le_of_factors (k₂ (factors_self _)))

/-- The restricted projection of a composite presentation is the composite of the restricted
projections. -/
lemma preimageπ_trans (K : Subobject Y) :
    (P.trans Q).preimageπ K =
      ofLE _ _ (P.preimage_trans Q K).le ≫ P.preimageπ (Q.preimage K) ≫ Q.preimageπ K := by
  rw [← cancel_mono K.arrow, preimageπ_arrow, π_trans', ofLE_comp_ofLE_assoc, Category.assoc,
    Category.assoc, preimageπ_arrow, P.preimageπ_ofLE_assoc (Q.preimage_le_Z K),
    ofLE_comp_ofLE_assoc]

/-- Composition of subquotient presentations is associative. -/
lemma trans_assoc {V : C} (R : SubquotientPresentation Y V) :
    (P.trans Q).trans R = P.trans (Q.trans R) :=
  ext (P.preimage_trans Q R.B) (P.preimage_trans Q R.Z) (by
    -- Both sides are the inclusion into `P.preimage (Q.preimage R.Z)` followed by
    -- `P.preimageπ (Q.preimage R.Z) ≫ Q.preimageπ R.Z ≫ R.π`.
    simp only [π_trans', preimageπ_trans, preimageπ_ofLE_assoc, ofLE_comp_ofLE_assoc,
      Category.assoc])

end Trans

section Subquotient

/-- The presentation of the cokernel of a pair `I ≤ K` of subobjects of `X` inside `X` itself,
with the identity identification. -/
@[expose] noncomputable def quotient (I K : Subobject X) (h : I ≤ K) :
    SubquotientPresentation X (cokernel (ofLE I K h)) where
  B := I
  Z := K
  le := h
  iso := Iso.refl _

@[simp]
lemma quotient_B (I K : Subobject X) (h : I ≤ K) : (quotient I K h).B = I := (rfl)

@[simp]
lemma quotient_Z (I K : Subobject X) (h : I ≤ K) : (quotient I K h).Z = K := (rfl)

@[simp]
lemma π_quotient (I K : Subobject X) (h : I ≤ K) :
    (quotient I K h).π = cokernel.π (ofLE I K h) :=
  Category.comp_id _

variable (P : SubquotientPresentation A X)

/-- The presentation inside `A` of the cokernel of a pair `I ≤ K` of subobjects of `X`, by the
preimages of `I` and `K`. -/
@[expose] noncomputable def subquotient (I K : Subobject X) (h : I ≤ K) :
    SubquotientPresentation A (cokernel (ofLE I K h)) :=
  P.trans (quotient I K h)

@[simp]
lemma subquotient_B (I K : Subobject X) (h : I ≤ K) : (P.subquotient I K h).B = P.preimage I :=
  rfl

@[simp]
lemma subquotient_Z (I K : Subobject X) (h : I ≤ K) : (P.subquotient I K h).Z = P.preimage K :=
  rfl

/-- Taking preimages along the presentation of a cokernel is taking preimages first along the
presentation of that cokernel inside `X`, which identifies its subobjects with the interval
`[I, K]`. -/
@[simp]
lemma preimage_subquotient (I K : Subobject X) (h : I ≤ K) (L : Subobject (cokernel (ofLE I K h))) :
    (P.subquotient I K h).preimage L = P.preimage ((quotient I K h).preimage L) :=
  P.preimage_trans _ L

/-- The presentation of a cokernel obtained in two steps: presenting first the cokernel of
`I ≤ K`, and then the cokernel of a pair `I₂ ≤ K₂` of its subobjects, is presenting inside `A` the
presentation of the second cokernel inside `X`. By `preimage_subquotient`, its subobjects are the
preimages of the subobjects of `X` corresponding to `I₂` and `K₂`. -/
lemma subquotient_subquotient (I K : Subobject X) (h : I ≤ K)
    (I₂ K₂ : Subobject (cokernel (ofLE I K h))) (h₂ : I₂ ≤ K₂) :
    (P.subquotient I K h).subquotient I₂ K₂ h₂ = P.trans ((quotient I K h).subquotient I₂ K₂ h₂) :=
  P.trans_assoc _ _

end Subquotient

section Refl

/-- The identity presentation of `X` inside itself, by `⊥ ≤ ⊤`, whose projection is the
(invertible) arrow of `⊤`. -/
@[expose] noncomputable def refl (X : C) : SubquotientPresentation X X :=
  ofEpi bot_le (⊤ : Subobject X).arrow (pullback_bot _).symm

@[simp]
lemma refl_B : (refl X).B = ⊥ := (rfl)

@[simp]
lemma refl_Z : (refl X).Z = ⊤ := (rfl)

/-- The projection of the identity presentation is the arrow of `⊤`. -/
@[simp]
lemma π_refl : (refl X).π = (refl X).Z.arrow := π_ofEpi _ _ _

/-- Transport along the identity presentation is the identity. -/
@[simp]
lemma preimage_refl (K : Subobject X) : (refl X).preimage K = K := by
  rw [preimage, π_refl, map_pullback_arrow_of_le (Z := (refl X).Z) le_top]

variable (P : SubquotientPresentation A X)

/-- The identity presentation is a right unit for composition. -/
@[simp]
lemma trans_refl : P.trans (refl X) = P :=
  ext P.preimage_bot P.preimage_top (by
    rw [π_trans', π_refl, preimageπ_arrow, ofLE_comp_ofLE_assoc])

/-- The identity presentation is a left unit for composition. -/
@[simp]
lemma refl_trans : (refl A).trans P = P :=
  ext (preimage_refl P.B) (preimage_refl P.Z) (by
    have h : (refl A).preimageπ P.Z = ofLE _ _ (preimage_refl P.Z).le := by
      rw [← cancel_mono P.Z.arrow, preimageπ_arrow, π_refl, ofLE_arrow, ofLE_arrow]
    rw [π_trans', h, ofLE_comp_ofLE_assoc])

end Refl

section MapIso

variable (P : SubquotientPresentation A X)

/-- Transport of a subquotient presentation along an isomorphism of the presented object. -/
@[expose] noncomputable def mapIso (e : X ≅ Y) : SubquotientPresentation A Y where
  B := P.B
  Z := P.Z
  le := P.le
  iso := P.iso ≪≫ e

@[simp]
lemma mapIso_B (e : X ≅ Y) : (P.mapIso e).B = P.B := (rfl)

@[simp]
lemma mapIso_Z (e : X ≅ Y) : (P.mapIso e).Z = P.Z := (rfl)

@[simp]
lemma π_mapIso (e : X ≅ Y) : (P.mapIso e).π = P.π ≫ e.hom :=
  (Category.assoc _ _ _).symm

/-- The projection of a transported presentation, as a morphism out of `P.Z`. -/
lemma π_mapIso' (e : X ≅ Y) : (P.mapIso e).π = ofLE _ P.Z (P.mapIso_Z e).le ≫ P.π ≫ e.hom := by
  rw [π_mapIso]
  exact (ofLE_self_comp _ _).symm

@[simp]
lemma preimage_mapIso (e : X ≅ Y) (K : Subobject Y) :
    (P.mapIso e).preimage K = P.preimage ((Subobject.pullback e.hom).obj K) := by
  rw [preimage, preimage, π_mapIso]
  exact congrArg (map P.Z.arrow).obj (pullback_comp P.π e.hom K)

/-- Composing with a presentation transported along an isomorphism is transporting the composite
along that isomorphism. -/
lemma trans_mapIso (Q : SubquotientPresentation X Y) (e : Y ≅ W) :
    P.trans (Q.mapIso e) = (P.trans Q).mapIso e :=
  ext (by simp) (by simp) (by
    simp only [π_trans', π_mapIso', preimageπ_ofLE_assoc, ofLE_comp_ofLE_assoc, Category.assoc])

/-- Transporting a presentation along two composable isomorphisms equals transporting along their
composite. -/
lemma mapIso_mapIso (e₁ : X ≅ Y) (e₂ : Y ≅ W) :
    (P.mapIso e₁).mapIso e₂ = P.mapIso (e₁ ≪≫ e₂) :=
  ext rfl rfl (by
    rw [π_mapIso', π_mapIso', π_mapIso']
    simp only [Category.assoc, ofLE_comp_ofLE_assoc, Iso.trans_hom])

/-- The isomorphism between two objects presented inside `A` by the same subobjects: it is
induced by the identity of the larger subobject. -/
noncomputable def isoOfEq (P' : SubquotientPresentation A Y) (hB : P.B = P'.B) (hZ : P.Z = P'.Z) :
    X ≅ Y :=
  P.iso.symm ≪≫ cokernel.mapIso _ _ (Subobject.isoOfEq _ _ hB) (Subobject.isoOfEq _ _ hZ)
    (by simp [ofLE_comp_ofLE]) ≪≫ P'.iso

/-- The projection of `P` followed by `P.isoOfEq P' hB hZ` is the projection of `P'`. -/
@[reassoc (attr := simp)]
lemma π_isoOfEq_hom (P' : SubquotientPresentation A Y) (hB : P.B = P'.B) (hZ : P.Z = P'.Z) :
    P.π ≫ (P.isoOfEq P' hB hZ).hom = ofLE P.Z P'.Z hZ.le ≫ P'.π := by
  simp [isoOfEq, ← cokernel_π_iso_hom]

/-- Transporting a presentation along the isomorphism to another presentation by the same
subobjects gives that presentation. -/
@[simp]
lemma mapIso_isoOfEq (P' : SubquotientPresentation A Y) (hB : P.B = P'.B) (hZ : P.Z = P'.Z) :
    P.mapIso (P.isoOfEq P' hB hZ) = P' :=
  ext hB hZ (by rw [π_mapIso', π_isoOfEq_hom, ofLE_comp_ofLE_assoc])

/-- If transporting `P` along `e : X ≅ Y` equals `P'`, then `e` equals `P.isoOfEq P'`. -/
lemma eq_isoOfEq_of_mapIso_eq {P' : SubquotientPresentation A Y} {e : X ≅ Y}
    (h : P.mapIso e = P') (hB : P.B = P'.B) (hZ : P.Z = P'.Z) :
    e = P.isoOfEq P' hB hZ := by
  subst h
  ext
  rw [← cancel_epi P.π, π_isoOfEq_hom, π_mapIso', Subobject.ofLE_comp_ofLE_assoc,
    Subobject.ofLE_refl, Category.id_comp]

/-- Composing `isoOfEq` isomorphisms between presentations of the same subobjects. -/
lemma isoOfEq_trans {P₁ : SubquotientPresentation A X} {P₂ : SubquotientPresentation A Y}
    {P₃ : SubquotientPresentation A W} (hB₁ : P₁.B = P₂.B) (hZ₁ : P₁.Z = P₂.Z)
    (hB₂ : P₂.B = P₃.B) (hZ₂ : P₂.Z = P₃.Z) :
    P₁.isoOfEq P₂ hB₁ hZ₁ ≪≫ P₂.isoOfEq P₃ hB₂ hZ₂ =
      P₁.isoOfEq P₃ (hB₁.trans hB₂) (hZ₁.trans hZ₂) := by
  ext
  rw [Iso.trans_hom, ← cancel_epi P₁.π, π_isoOfEq_hom_assoc, π_isoOfEq_hom,
    π_isoOfEq_hom, ofLE_comp_ofLE_assoc]

end MapIso

section Naturality

variable (P : SubquotientPresentation A X)

/-- For a presentation `Q` of `Y` inside `X` and subobjects `I′ ≤ K′` of `X` in the interval
`[Q.B, Q.Z]`, presenting inside `A` the cokernel of the images of `I′` and `K′` in `Y` is
presenting the cokernel of `I′ ≤ K′`, up to the identification of the two cokernels. -/
lemma trans_subquotient_image (Q : SubquotientPresentation X Y) {I' K' : Subobject X}
    (hI : Q.B ≤ I') (h' : I' ≤ K') (hK : K' ≤ Q.Z) :
    (P.trans Q).subquotient (Q.image I') (Q.image K') (Q.image_monotone h') =
      (P.subquotient I' K' h').mapIso ((quotient I' K' h').isoOfEq
        (Q.subquotient (Q.image I') (Q.image K') (Q.image_monotone h'))
        (by rw [quotient_B, subquotient_B, Q.preimage_image hI (h'.trans hK)])
        (by rw [quotient_Z, subquotient_Z, Q.preimage_image (hI.trans h') hK])) :=
  calc (P.trans Q).subquotient (Q.image I') (Q.image K') (Q.image_monotone h')
      _ = P.trans (Q.subquotient (Q.image I') (Q.image K') (Q.image_monotone h')) :=
        P.trans_assoc _ _
      _ = P.trans ((quotient I' K' h').mapIso _) := by rw [mapIso_isoOfEq]
      _ = _ := P.trans_mapIso _ _

/-- Naturality of the presentation of a cokernel: for `I ≤ I′ ≤ K′ ≤ K` in `X`, presenting the
cokernel of `I′ ≤ K′` directly inside `A`, and presenting it in two steps, first the cokernel of
`I ≤ K` and then inside it the cokernel of the images of `I′` and `K′`, agree up to the
identification of the two cokernels. -/
lemma subquotient_subquotient_image {I I' K' K : Subobject X} (h : I ≤ K) (hI : I ≤ I')
    (h' : I' ≤ K') (hK : K' ≤ K) :
    (P.subquotient I K h).subquotient ((quotient I K h).image I') ((quotient I K h).image K')
        ((quotient I K h).image_monotone h') =
      (P.subquotient I' K' h').mapIso ((quotient I' K' h').isoOfEq
        ((quotient I K h).subquotient ((quotient I K h).image I') ((quotient I K h).image K')
          ((quotient I K h).image_monotone h'))
        (by rw [quotient_B, subquotient_B, preimage_image _ hI (h'.trans hK)])
        (by rw [quotient_Z, subquotient_Z, preimage_image _ (hI.trans h') hK])) :=
  P.trans_subquotient_image _ hI h' hK

end Naturality

section Map

variable {A' A'' X' X'' : C}

/-- The presented object `X` is zero if and only if `P.B = P.Z`. -/
theorem isZero_iff_B_eq_Z (P : SubquotientPresentation A X) :
    IsZero X ↔ P.B = P.Z :=
  ⟨fun h ↦ (Subobject.isZero_cokernel_ofLE_iff P.le).mp (h.of_iso P.iso),
    fun h ↦ ((Subobject.isZero_cokernel_ofLE_iff P.le).mpr h).of_iso P.iso.symm⟩

/-- A morphism `f : A ⟶ A'` carrying `P.B` into `Q.B` and `P.Z` into `Q.Z` induces a canonical
morphism `X ⟶ X'` between the presented subquotients. -/
noncomputable def map (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f)) :
    X ⟶ X' :=
  P.iso.inv ≫ cokernel.map (ofLE P.B P.Z P.le) (ofLE Q.B Q.Z Q.le)
    (Q.B.factorThru (P.B.arrow ≫ f) hB) (Q.Z.factorThru (P.Z.arrow ≫ f) hZ) (by
      rw [← cancel_mono Q.Z.arrow]
      simp) ≫ Q.iso.hom

@[reassoc (attr := simp)]
lemma π_comp_map (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f)) :
    P.π ≫ P.map Q f hB hZ = Q.Z.factorThru (P.Z.arrow ≫ f) hZ ≫ Q.π := by
  rw [map, ← cokernel_π_iso_hom_assoc, Iso.hom_inv_id_assoc, cokernel.π_desc_assoc,
    Category.assoc, cokernel_π_iso_hom]

lemma map_eq_of_π_comp (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (f : A ⟶ A') (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f))
    {g : X ⟶ X'} (hg : P.π ≫ g = Q.Z.factorThru (P.Z.arrow ≫ f) hZ ≫ Q.π) :
    P.map Q f hB hZ = g := by
  rw [← cancel_epi P.π, π_comp_map, hg]

/-- `SubquotientPresentation.map` depends only on the ambient morphism, not on the choice of
`Factors` witnesses or definitional representative of the morphism. -/
lemma map_congr {P : SubquotientPresentation A X} {Q : SubquotientPresentation A' X'}
    {f f' : A ⟶ A'} (h : f = f')
    {hB : Q.B.Factors (P.B.arrow ≫ f)} {hZ : Q.Z.Factors (P.Z.arrow ≫ f)}
    {hB' : Q.B.Factors (P.B.arrow ≫ f')} {hZ' : Q.Z.Factors (P.Z.arrow ≫ f')} :
    P.map Q f hB hZ = P.map Q f' hB' hZ' := by
  subst h
  rfl

@[simp]
lemma map_id (P : SubquotientPresentation A X)
    (hB : P.B.Factors (P.B.arrow ≫ 𝟙 A)) (hZ : P.Z.Factors (P.Z.arrow ≫ 𝟙 A)) :
    P.map P (𝟙 A) hB hZ = 𝟙 X := by
  apply map_eq_of_π_comp
  have h1 : P.Z.factorThru (P.Z.arrow ≫ 𝟙 A) hZ = 𝟙 (P.Z : C) := by
    rw [← cancel_mono P.Z.arrow]
    simp
  rw [h1, Category.comp_id, Category.id_comp]

lemma map_comp (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (R : SubquotientPresentation A'' X'') (f : A ⟶ A') (g : A' ⟶ A'')
    (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f))
    (hB' : R.B.Factors (Q.B.arrow ≫ g)) (hZ' : R.Z.Factors (Q.Z.arrow ≫ g))
    (hB'' : R.B.Factors (P.B.arrow ≫ (f ≫ g))) (hZ'' : R.Z.Factors (P.Z.arrow ≫ (f ≫ g))) :
    P.map Q f hB hZ ≫ Q.map R g hB' hZ' = P.map R (f ≫ g) hB'' hZ'' := by
  symm
  apply map_eq_of_π_comp
  rw [π_comp_map_assoc, π_comp_map, ← Category.assoc]
  congr 1
  rw [← cancel_mono R.Z.arrow]
  simp

@[simp]
lemma map_mapIso_left (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (e : X ≅ Y) (f : A ⟶ A')
    (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f)) :
    (P.mapIso e).map Q f hB hZ = e.inv ≫ P.map Q f hB hZ := by
  apply map_eq_of_π_comp
  rw [π_mapIso', Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, π_comp_map]
  dsimp only [mapIso]
  rw [ofLE_refl, Category.id_comp]

@[simp]
lemma map_mapIso_right (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (e : X' ≅ Y) (f : A ⟶ A')
    (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f)) :
    P.map (Q.mapIso e) f hB hZ = P.map Q f hB hZ ≫ e.hom := by
  apply map_eq_of_π_comp
  rw [π_comp_map_assoc, π_mapIso]
  rfl

/-- Transporting both presentations along isomorphisms conjugates `SubquotientPresentation.map`. -/
lemma map_mapIso (P : SubquotientPresentation A X) (Q : SubquotientPresentation A' X')
    (e : X ≅ Y) {Y' : C} (e' : X' ≅ Y') (f : A ⟶ A')
    (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f)) :
    (P.mapIso e).map (Q.mapIso e') f hB hZ = e.inv ≫ P.map Q f hB hZ ≫ e'.hom :=
  (map_mapIso_left P (Q.mapIso e') e f hB hZ).trans
    (congrArg (e.inv ≫ ·) (map_mapIso_right P Q e' f hB hZ))

/-- The morphism induced by `f : A ⟶ A'` between identity presentations `refl A` and `refl A'`
is `f` itself. -/
lemma map_refl (f : A ⟶ A')
    (hB : (refl A').B.Factors ((refl A).B.arrow ≫ f))
    (hZ : (refl A').Z.Factors ((refl A).Z.arrow ≫ f)) :
    (refl A).map (refl A') f hB hZ = f := by
  apply map_eq_of_π_comp
  simp

/-- If `f : A ⟶ A'` induces `P.map Q f hB hZ : X ⟶ X'`, and `P.map Q f hB hZ` maps `S` into `S'`,
then `f` maps `P.preimage S` into `Q.preimage S'`. -/
lemma factors_preimage_of_factors_map (P : SubquotientPresentation A X)
    (Q : SubquotientPresentation A' X') (f : A ⟶ A')
    (hB : Q.B.Factors (P.B.arrow ≫ f)) (hZ : Q.Z.Factors (P.Z.arrow ≫ f))
    {S : Subobject X} {S' : Subobject X'}
    (hS : S'.Factors (S.arrow ≫ P.map Q f hB hZ)) :
    (Q.preimage S').Factors ((P.preimage S).arrow ≫ f) := by
  have h1 : ofLE (P.preimage S) P.Z (P.preimage_le_Z S) ≫ Q.Z.factorThru (P.Z.arrow ≫ f) hZ ≫
      Q.π = P.preimageπ S ≫ S.arrow ≫ P.map Q f hB hZ := by
    rw [← π_comp_map, ← Category.assoc, ← preimageπ_arrow, Category.assoc]
  have h2 : (Q.preimage S').Factors
      ((ofLE (P.preimage S) P.Z (P.preimage_le_Z S) ≫
        Q.Z.factorThru (P.Z.arrow ≫ f) hZ) ≫ Q.Z.arrow) := by
    rw [Q.factors_preimage_iff S', Category.assoc, h1]
    exact factors_of_factors_right (P.preimageπ S) hS
  simpa using h2

/-- Naturality of the restricted projection `preimageπ` with respect to
`SubquotientPresentation.map`. -/
@[reassoc]
lemma preimageπ_comp_factorThru (P : SubquotientPresentation A X)
    (P' : SubquotientPresentation A' X') (f : A ⟶ A')
    (hB : P'.B.Factors (P.B.arrow ≫ f)) (hZ : P'.Z.Factors (P.Z.arrow ≫ f))
    {S : Subobject X} {S' : Subobject X'}
    (hS : S'.Factors (S.arrow ≫ P.map P' f hB hZ)) :
    P.preimageπ S ≫ S'.factorThru (S.arrow ≫ P.map P' f hB hZ) hS =
      (P'.preimage S').factorThru ((P.preimage S).arrow ≫ f)
          (P.factors_preimage_of_factors_map P' f hB hZ hS) ≫
        P'.preimageπ S' := by
  rw [← cancel_mono S'.arrow, Category.assoc, factorThru_arrow, preimageπ_arrow_assoc,
    π_comp_map, Category.assoc, preimageπ_arrow]
  have hfac : ofLE (P.preimage S) P.Z (P.preimage_le_Z S) ≫
      P'.Z.factorThru (P.Z.arrow ≫ f) hZ =
      (P'.preimage S').factorThru ((P.preimage S).arrow ≫ f)
        (P.factors_preimage_of_factors_map P' f hB hZ hS) ≫
      ofLE (P'.preimage S') P'.Z (P'.preimage_le_Z S') := by
    rw [← cancel_mono P'.Z.arrow]
    simp
  rw [reassoc_of% hfac]

/-- Functoriality of composition of subquotient presentations: the morphism induced by `f : A ⟶ A'`
between `P.trans Q` and `P'.trans Q'` equals the morphism induced by `P.map P' f hB hZ` between
`Q` and `Q'`. -/
theorem trans_map (P : SubquotientPresentation A X) (P' : SubquotientPresentation A' X')
    (Q : SubquotientPresentation X Y) (Q' : SubquotientPresentation X' Y') (f : A ⟶ A')
    (hB : P'.B.Factors (P.B.arrow ≫ f)) (hZ : P'.Z.Factors (P.Z.arrow ≫ f))
    (hBQ : Q'.B.Factors (Q.B.arrow ≫ P.map P' f hB hZ))
    (hZQ : Q'.Z.Factors (Q.Z.arrow ≫ P.map P' f hB hZ)) :
    (P.trans Q).map (P'.trans Q') f
        (P.factors_preimage_of_factors_map P' f hB hZ hBQ)
        (P.factors_preimage_of_factors_map P' f hB hZ hZQ) =
      Q.map Q' (P.map P' f hB hZ) hBQ hZQ := by
  apply map_eq_of_π_comp
  rw [π_trans', π_trans', Category.assoc, Category.assoc, π_comp_map,
    preimageπ_comp_factorThru_assoc]
  let hZ_trans : (P'.trans Q').Z.Factors ((P.trans Q).Z.arrow ≫ f) :=
    P.factors_preimage_of_factors_map P' f hB hZ hZQ
  have hfac : ofLE (P.trans Q).Z (P.preimage Q.Z) (P.trans_Z Q).le ≫
      (P'.preimage Q'.Z).factorThru ((P.preimage Q.Z).arrow ≫ f)
        (P.factors_preimage_of_factors_map P' f hB hZ hZQ) =
      (P'.trans Q').Z.factorThru ((P.trans Q).Z.arrow ≫ f) hZ_trans ≫
      ofLE (P'.trans Q').Z (P'.preimage Q'.Z) (P'.trans_Z Q').le := by
    rw [← cancel_mono (P'.preimage Q'.Z).arrow, Category.assoc, Category.assoc, ofLE_arrow,
      factorThru_arrow, ofLE_arrow_assoc, factorThru_arrow]
  rw [reassoc_of% hfac]

/-- Naturality of `isoOfEq` with respect to `map`: comparing presentations with equal subobjects
commutes with the morphisms induced by `f : A ⟶ A'`. -/
lemma isoOfEq_hom_comp_map {P : SubquotientPresentation A X} {Q : SubquotientPresentation A Y}
    {P' : SubquotientPresentation A' X'} {Q' : SubquotientPresentation A' Y'}
    (hB : P.B = Q.B) (hZ : P.Z = Q.Z) (hB' : P'.B = Q'.B) (hZ' : P'.Z = Q'.Z) (f : A ⟶ A')
    (hBP : P'.B.Factors (P.B.arrow ≫ f)) (hZP : P'.Z.Factors (P.Z.arrow ≫ f))
    (hBQ : Q'.B.Factors (Q.B.arrow ≫ f)) (hZQ : Q'.Z.Factors (Q.Z.arrow ≫ f)) :
    (P.isoOfEq Q hB hZ).hom ≫ Q.map Q' f hBQ hZQ =
      P.map P' f hBP hZP ≫ (P'.isoOfEq Q' hB' hZ').hom := by
  have hfac : ofLE P.Z Q.Z hZ.le ≫ Q'.Z.factorThru (Q.Z.arrow ≫ f) hZQ =
      P'.Z.factorThru (P.Z.arrow ≫ f) hZP ≫ ofLE P'.Z Q'.Z hZ'.le := by
    rw [← cancel_mono Q'.Z.arrow]
    simp
  rw [← cancel_epi P.π, π_isoOfEq_hom_assoc, π_comp_map, π_comp_map_assoc, π_isoOfEq_hom,
    reassoc_of% hfac]

end Map

end SubquotientPresentation

end TauCeti
