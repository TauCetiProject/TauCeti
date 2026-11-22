/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Basic
public import TauCeti.CategoryTheory.Abelian.Subobject
public import TauCeti.CategoryTheory.Subobject.Pullback
import Mathlib.CategoryTheory.Abelian.Refinements
import TauCeti.CategoryTheory.Subobject.Basic
import TauCeti.CategoryTheory.Subobject.Image

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
* `TauCeti.SubquotientPresentation.π`: the projection `Z ⟶ X`; `desc`: universal property out
  of `Z`.
* `TauCeti.SubquotientPresentation.ofEpi`: the presentation given by an epimorphism out of `Z`
  whose kernel is `B`.
* `TauCeti.SubquotientPresentation.ofIsColimit`: the presentation given by a colimit cokernel
  cofork `B ⟶ Z ⟶ X`.
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
* `TauCeti.SubquotientPresentation.mapInduced`: the morphism `X ⟶ X'` induced by a morphism
  `f : A ⟶ A'` sending `P.Z` into `P'.Z` and `P.B` into `P'.B`.

## Main results

* `TauCeti.SubquotientPresentation.isZero_iff`: `X` is zero iff `P.B = P.Z`.
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
* `TauCeti.SubquotientPresentation.mapInduced_comp`,
  `TauCeti.SubquotientPresentation.mapInduced_trans`,
  `TauCeti.SubquotientPresentation.exists_preimage_le_preimage_iff`: functoriality and
  compatibility of `mapInduced`.

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

/-- A morphism out of `P.Z` that vanishes on `P.B` descends uniquely to `X`. -/
noncomputable def desc (f : (P.Z : C) ⟶ Y) (hf : ofLE P.B P.Z P.le ≫ f = 0) : X ⟶ Y :=
  P.iso.inv ≫ cokernel.desc (ofLE P.B P.Z P.le) f hf

@[reassoc (attr := simp)]
lemma π_desc (f : (P.Z : C) ⟶ Y) (hf : ofLE P.B P.Z P.le ≫ f = 0) :
    P.π ≫ P.desc f hf = f := by
  rw [← cokernel_π_iso_hom, Category.assoc, desc, Iso.hom_inv_id_assoc, cokernel.π_desc]

lemma hom_ext {g₁ g₂ : X ⟶ Y} (h : P.π ≫ g₁ = P.π ≫ g₂) : g₁ = g₂ :=
  (cancel_epi P.π).mp h

/-- The presented object `X` is zero if and only if the denominator equals the numerator. -/
lemma isZero_iff : IsZero X ↔ P.B = P.Z := by
  refine ⟨fun hX ↦ ?_, fun hBZ ↦ ?_⟩
  · have hB := P.kernelSubobject_π
    rw [hX.eq_of_tgt P.π 0, kernelSubobject_zero] at hB
    exact (map_pullback_arrow_of_le P.le).symm.trans
      (by rw [← hB, Subobject.map_top, mk_arrow])
  · have heq : ofLE P.B P.Z P.le = (Subobject.isoOfEq P.B P.Z hBZ).hom := by
      rw [← cancel_mono P.Z.arrow]; simp
    have : IsIso (ofLE P.B P.Z P.le) := heq ▸ inferInstance
    exact IsZero.of_iso (Limits.isZero_cokernel_of_epi _) P.iso.symm

end Basic

omit [Abelian C] in
/-- Composing with the inclusion of a subobject into itself does nothing. The hypothesis `S ≤ S`
is stated for a single `S`, so this applies wherever the source and target of `ofLE` agree only
after unfolding a definition: the larger subobjects of `ofEpi`, `trans` and `mapIso` are, by
definition, the subobjects they are built from, but cannot be rewritten in the source of a
morphism. -/
private lemma ofLE_self_comp {S : Subobject A} (h : S ≤ S) (f : (S : C) ⟶ X) :
    ofLE S S h ≫ f = f := by
  rw [ofLE_refl, Category.id_comp]

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

section OfIsColimit

variable {B Z : Subobject A} (le : B ≤ Z) (g : (Z : C) ⟶ X)
  (w : ofLE B Z le ≫ g = 0) (hc : IsColimit (CokernelCofork.ofπ g w))

/-- The subquotient presentation given by a cokernel colimit cocone `B ⟶ Z ⟶ X`. -/
@[expose] noncomputable def ofIsColimit : SubquotientPresentation A X where
  B := B
  Z := Z
  le := le
  iso := (cokernelIsCokernel _).coconePointUniqueUpToIso hc

@[simp]
lemma ofIsColimit_B : (ofIsColimit le g w hc).B = B := (rfl)

@[simp]
lemma ofIsColimit_Z : (ofIsColimit le g w hc).Z = Z := (rfl)

@[simp]
lemma π_ofIsColimit : (ofIsColimit le g w hc).π = g :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one

end OfIsColimit

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

@[simp]
lemma preimage_eq_Z_iff {K : Subobject X} : P.preimage K = P.Z ↔ K = ⊤ := by
  rw [← P.preimage_top, P.preimage_inj]

@[simp]
lemma preimage_eq_B_iff {K : Subobject X} : P.preimage K = P.B ↔ K = ⊥ := by
  rw [← P.preimage_bot, P.preimage_inj]

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

/-- Existence of a greatest lower bound for a nonempty family is preserved and reflected by
`P.preimage`. -/
lemma exists_isGLB_preimage_iff (hs : s.Nonempty) :
    (∃ M, IsGLB (P.preimage '' s) M) ↔ ∃ m, IsGLB s m :=
  ⟨fun ⟨M, hM⟩ ↦ ⟨P.image M, (P.isGLB_preimage_iff hs).1 <| by
      rwa [P.preimage_image_of_isGLB hs hM]⟩,
   fun ⟨m, hm⟩ ↦ ⟨P.preimage m, (P.isGLB_preimage_iff hs).2 hm⟩⟩

/-- Existence of a least upper bound for a nonempty family is preserved and reflected by
`P.preimage`. -/
lemma exists_isLUB_preimage_iff (hs : s.Nonempty) :
    (∃ M, IsLUB (P.preimage '' s) M) ↔ ∃ m, IsLUB s m :=
  ⟨fun ⟨M, hM⟩ ↦ ⟨P.image M, (P.isLUB_preimage_iff hs).1 <| by
      rwa [P.preimage_image_of_isLUB hs hM]⟩,
   fun ⟨m, hm⟩ ↦ ⟨P.preimage m, (P.isLUB_preimage_iff hs).2 hm⟩⟩

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
lemma mapIso_refl : P.mapIso (Iso.refl X) = P :=
  ext rfl rfl (by rw [π_mapIso', Iso.refl_hom, Category.comp_id])

@[simp]
lemma mapIso_trans (e₁ : X ≅ Y) (e₂ : Y ≅ W) :
    (P.mapIso e₁).mapIso e₂ = P.mapIso (e₁ ≪≫ e₂) :=
  ext rfl rfl (by
    simp only [π_mapIso', ofLE_comp_ofLE_assoc, Iso.trans_hom, Category.assoc])

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

lemma mapIso_injective : Function.Injective (P.mapIso (Y := Y)) := fun e₁ e₂ h ↦ by
  dsimp only [mapIso] at h
  injection h with _ _ hiso
  exact Iso.ext ((cancel_epi P.iso.hom).mp (congrArg Iso.hom hiso))

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

section MapInduced

variable {A' A'' X' X'' : C} (P : SubquotientPresentation A X)
  (P' : SubquotientPresentation A' X')

/-- Lift a morphism `f : A ⟶ A'` to `P.Z ⟶ P'.Z` when `(Subobject.exists f).obj P.Z ≤ P'.Z`. -/
noncomputable def liftZ (f : A ⟶ A') (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) :
    (P.Z : C) ⟶ (P'.Z : C) :=
  factorThruImageSubobject (P.Z.arrow ≫ f) ≫
    Subobject.ofLE _ P'.Z ((Subobject.exists_eq_imageSubobject f P.Z).symm.trans_le hZ)

@[reassoc (attr := simp)]
lemma liftZ_arrow (f : A ⟶ A') (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) :
    P.liftZ P' f hZ ≫ P'.Z.arrow = P.Z.arrow ≫ f := by
  rw [liftZ, Category.assoc, ofLE_arrow, imageSubobject_arrow_comp]

/-- The morphism `X ⟶ X'` induced by `f : A ⟶ A'` sending `P.Z` into `P'.Z` and `P.B` into
`P'.B`. -/
noncomputable def mapInduced (f : A ⟶ A') (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z)
    (hB : (Subobject.exists f).obj P.B ≤ P'.B) : X ⟶ X' :=
  P.desc (P.liftZ P' f hZ ≫ P'.π) (by
    let liftB : (P.B : C) ⟶ (P'.B : C) :=
      factorThruImageSubobject (P.B.arrow ≫ f) ≫
        Subobject.ofLE _ P'.B ((Subobject.exists_eq_imageSubobject f P.B).symm.trans_le hB)
    have hsq : ofLE P.B P.Z P.le ≫ P.liftZ P' f hZ = liftB ≫ ofLE P'.B P'.Z P'.le := by
      rw [← cancel_mono P'.Z.arrow, Category.assoc, Category.assoc, ofLE_arrow, liftZ_arrow,
        ofLE_arrow_assoc]
      dsimp only [liftB]
      rw [Category.assoc, ofLE_arrow, imageSubobject_arrow_comp]
    rw [reassoc_of% hsq, P'.ofLE_π, comp_zero])

@[reassoc (attr := simp)]
lemma π_mapInduced (f : A ⟶ A') (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z)
    (hB : (Subobject.exists f).obj P.B ≤ P'.B) :
    P.π ≫ P.mapInduced P' f hZ hB = P.liftZ P' f hZ ≫ P'.π :=
  P.π_desc _ _

lemma mapInduced_unique (f : A ⟶ A') (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z)
    (hB : (Subobject.exists f).obj P.B ≤ P'.B) {g : X ⟶ X'}
    (hg : P.π ≫ g = P.liftZ P' f hZ ≫ P'.π) : g = P.mapInduced P' f hZ hB :=
  P.hom_ext (by rw [hg, P.π_mapInduced])

/-- `mapInduced` is invariant under replacing the presentations or the morphism by equal ones. -/
lemma mapInduced_congr {P₁ P₂ : SubquotientPresentation A X}
    {P₁' P₂' : SubquotientPresentation A' X'} {f g : A ⟶ A'} (hp : P₁ = P₂) (hp' : P₁' = P₂')
    (hfg : f = g) (hZ₁ : (Subobject.exists f).obj P₁.Z ≤ P₁'.Z)
    (hB₁ : (Subobject.exists f).obj P₁.B ≤ P₁'.B) (hZ₂ : (Subobject.exists g).obj P₂.Z ≤ P₂'.Z)
    (hB₂ : (Subobject.exists g).obj P₂.B ≤ P₂'.B) :
    P₁.mapInduced P₁' f hZ₁ hB₁ = P₂.mapInduced P₂' g hZ₂ hB₂ := by
  subst hp hp' hfg; rfl

@[simp]
lemma mapInduced_id
    (hZ : (Subobject.exists (𝟙 A)).obj P.Z ≤ P.Z :=
      by simp [Subobject.exists_iso_map, Subobject.map_id])
    (hB : (Subobject.exists (𝟙 A)).obj P.B ≤ P.B :=
      by simp [Subobject.exists_iso_map, Subobject.map_id]) :
    P.mapInduced P (𝟙 A) hZ hB = 𝟙 X := by
  have hlift : P.liftZ P (𝟙 A) hZ = 𝟙 (P.Z : C) := by
    rw [← cancel_mono P.Z.arrow]; simp
  exact (P.mapInduced_unique P (𝟙 A) hZ hB (by rw [hlift, Category.comp_id, Category.id_comp])).symm

@[simp]
lemma refl_mapInduced_refl (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj (refl A).Z ≤ (refl A').Z)
    (hB : (Subobject.exists f).obj (refl A).B ≤ (refl A').B) :
    (refl A).mapInduced (refl A') f hZ hB = f :=
  ((refl A).mapInduced_unique (refl A') f hZ hB (by
    rw [π_refl, π_refl]
    exact ((refl A).liftZ_arrow (refl A') f hZ).symm)).symm

lemma mapInduced_comp (P'' : SubquotientPresentation A'' X'') (f : A ⟶ A') (g : A' ⟶ A'')
    (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) (hB : (Subobject.exists f).obj P.B ≤ P'.B)
    (hZ' : (Subobject.exists g).obj P'.Z ≤ P''.Z) (hB' : (Subobject.exists g).obj P'.B ≤ P''.B) :
    P.mapInduced P'' (f ≫ g)
        ((Subobject.exists_comp f g P.Z).symm ▸ ((Subobject.exists g).monotone hZ).trans hZ')
        ((Subobject.exists_comp f g P.B).symm ▸ ((Subobject.exists g).monotone hB).trans hB') =
      P.mapInduced P' f hZ hB ≫ P'.mapInduced P'' g hZ' hB' :=
  (P.mapInduced_unique P'' (f ≫ g) _ _ (by
    rw [P.π_mapInduced_assoc, P'.π_mapInduced, ← Category.assoc]
    congr 1; rw [← cancel_mono P''.Z.arrow]; simp)).symm

lemma mapInduced_mapIso (e : X ≅ Y) (e' : X' ≅ W) (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) (hB : (Subobject.exists f).obj P.B ≤ P'.B) :
    (P.mapIso e).mapInduced (P'.mapIso e') f hZ hB =
      e.inv ≫ P.mapInduced P' f hZ hB ≫ e'.hom :=
  ((P.mapIso e).mapInduced_unique (P'.mapIso e') f hZ hB (by
    have hlift :
        ofLE (P.mapIso e).Z P.Z (P.mapIso_Z e).le ≫ P.liftZ P' f hZ =
          (P.mapIso e).liftZ (P'.mapIso e') f hZ ≫
            ofLE (P'.mapIso e').Z P'.Z (P'.mapIso_Z e').le := by
      rw [← cancel_mono P'.Z.arrow, Category.assoc, Category.assoc, ofLE_arrow, liftZ_arrow,
        ofLE_arrow_assoc]
      dsimp only [mapIso]
      rw [liftZ_arrow]
    rw [π_mapIso', Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, P.π_mapInduced_assoc,
      π_mapIso', reassoc_of% hlift])).symm

/-- Compatibility of `mapInduced` with preimages. -/
lemma exists_preimage_le_preimage_iff (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) (hB : (Subobject.exists f).obj P.B ≤ P'.B)
    (S : Subobject X) (S' : Subobject X') :
    (Subobject.exists f).obj (P.preimage S) ≤ P'.preimage S' ↔
      (Subobject.exists (P.mapInduced P' f hZ hB)).obj S ≤ S' := by
  have hleZ' : (Subobject.exists f).obj (P.preimage S) ≤ P'.Z :=
    ((Subobject.exists f).monotone (P.preimage_le_Z S)).trans hZ
  have hiff : ∀ T : Subobject A', T ≤ P'.Z →
      (T ≤ P'.preimage S' ↔ P'.image T ≤ S') := fun T hT ↦ by
    rw [image, (existsPullbackAdj P'.π).gc.le_iff_le, ← P'.pullback_Z_arrow_preimage S']
    exact ⟨fun h ↦ (Subobject.pullback P'.Z.arrow).monotone h,
      fun h ↦ (map_pullback_arrow_of_le hT).symm.trans_le
        (((Subobject.map P'.Z.arrow).monotone h).trans_eq
          (map_pullback_arrow_of_le (P'.preimage_le_Z S')))⟩
  rw [hiff _ hleZ', image, pullback_arrow_of_le hleZ', exists_mk_eq_imageSubobject]
  conv_rhs => rw [Subobject.exists_eq_imageSubobject]
  have heq := Subobject.exists_eq_imageSubobject f (P.preimage S)
  have hle_img : imageSubobject ((P.preimage S).arrow ≫ f) ≤ P'.Z := heq.symm.trans_le hleZ'
  have hof : ofLE ((Subobject.exists f).obj (P.preimage S)) P'.Z hleZ' =
      (Subobject.isoOfEq _ _ heq).hom ≫
        ofLE (imageSubobject ((P.preimage S).arrow ≫ f)) P'.Z hle_img := by
    rw [Subobject.isoOfEq_hom, ofLE_comp_ofLE]
  have hfac : factorThruImageSubobject ((P.preimage S).arrow ≫ f) ≫
        ofLE (imageSubobject ((P.preimage S).arrow ≫ f)) P'.Z hle_img =
      ofLE (P.preimage S) P.Z (P.preimage_le_Z S) ≫ P.liftZ P' f hZ := by
    rw [← cancel_mono P'.Z.arrow, Category.assoc, Category.assoc, ofLE_arrow,
      imageSubobject_arrow_comp, liftZ_arrow, ofLE_arrow_assoc]
  conv_lhs =>
    rw [hof, Category.assoc, imageSubobject_comp_eq_of_epi (Subobject.isoOfEq _ _ heq).hom,
      ← imageSubobject_comp_eq_of_epi (factorThruImageSubobject ((P.preimage S).arrow ≫ f)),
      reassoc_of% hfac, ← P.π_mapInduced P' f hZ hB, ← Category.assoc, ← P.preimageπ_arrow S,
      Category.assoc, imageSubobject_comp_eq_of_epi (P.preimageπ S)]

/-- Compatibility of `mapInduced` with composition of subquotient presentations. -/
lemma mapInduced_trans (Q : SubquotientPresentation X Y)
    (Q' : SubquotientPresentation X' Y') (f : A ⟶ A')
    (hZ : (Subobject.exists f).obj P.Z ≤ P'.Z) (hB : (Subobject.exists f).obj P.B ≤ P'.B)
    (hZq : (Subobject.exists (P.mapInduced P' f hZ hB)).obj Q.Z ≤ Q'.Z)
    (hBq : (Subobject.exists (P.mapInduced P' f hZ hB)).obj Q.B ≤ Q'.B) :
    (P.trans Q).mapInduced (P'.trans Q') f
        ((P.exists_preimage_le_preimage_iff P' f hZ hB Q.Z Q'.Z).mpr hZq)
        ((P.exists_preimage_le_preimage_iff P' f hZ hB Q.B Q'.B).mpr hBq) =
      Q.mapInduced Q' (P.mapInduced P' f hZ hB) hZq hBq := by
  have hZpq : (Subobject.exists f).obj (P.trans Q).Z ≤ (P'.trans Q').Z :=
    (P.exists_preimage_le_preimage_iff P' f hZ hB Q.Z Q'.Z).mpr hZq
  symm; refine (P.trans Q).mapInduced_unique (P'.trans Q') f _ _ ?_
  have hliftP :
      ofLE (P.trans Q).Z P.Z ((trans_Z P Q).le.trans (P.preimage_le_Z Q.Z)) ≫ P.liftZ P' f hZ =
        (P.trans Q).liftZ (P'.trans Q') f hZpq ≫
          ofLE (P'.trans Q').Z P'.Z ((trans_Z P' Q').le.trans (P'.preimage_le_Z Q'.Z)) := by
    rw [← cancel_mono P'.Z.arrow, Category.assoc, Category.assoc, ofLE_arrow, liftZ_arrow,
      ofLE_arrow_assoc, liftZ_arrow]
  have hlift :
      ofLE (P.trans Q).Z (P.preimage Q.Z) (trans_Z P Q).le ≫ P.preimageπ Q.Z ≫
          Q.liftZ Q' (P.mapInduced P' f hZ hB) hZq =
        (P.trans Q).liftZ (P'.trans Q') f hZpq ≫
          ofLE (P'.trans Q').Z (P'.preimage Q'.Z) (trans_Z P' Q').le ≫ P'.preimageπ Q'.Z := by
    rw [← cancel_mono Q'.Z.arrow]
    simp only [Category.assoc, preimageπ_arrow, preimageπ_arrow_assoc, liftZ_arrow,
      ofLE_comp_ofLE_assoc]
    rw [P.π_mapInduced, reassoc_of% hliftP]
  rw [π_trans', Category.assoc, Category.assoc, Q.π_mapInduced, π_trans', reassoc_of% hlift]

end MapInduced

end SubquotientPresentation

end TauCeti
