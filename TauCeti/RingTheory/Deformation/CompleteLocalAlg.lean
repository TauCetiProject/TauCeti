/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.RingHom
public import TauCeti.RingTheory.Deformation.ArtinLocalAlg
public import TauCeti.RingTheory.Length
public import TauCeti.RingTheory.LocalRing.Quotient
import TauCeti.RingTheory.AdicCompletion.Nilpotent

/-!
# The complete local coefficient category

Fix a commutative ring `Λ` and a field `k` with a `Λ`-algebra structure. The category `\hat{C}_Λ`
has as objects the complete Noetherian local `Λ`-algebras `A` together with a surjective
`Λ`-algebra map `A → k`, and as morphisms the `Λ`-algebra maps compatible with these maps to `k`
(Stacks, Definition 90.4.1 (06GW)). As for the Artinian coefficient category `C_Λ` of
`TauCeti.RingTheory.Deformation.ArtinLocalAlg`, the kernel of the augmentation is the maximal ideal,
so the augmentation identifies the residue field with `k`, and every morphism is local. We realise
`\hat{C}_Λ` as a full subcategory of `Over (CommAlgCat.of Λ k)`, the ambient category of `C_Λ`.

An Artinian local ring is Noetherian, and complete since its maximal ideal is nilpotent, so `C_Λ`
is a full subcategory of `\hat{C}_Λ` (`TauCeti.Deformation.ArtinLocalAlg.toCompleteLocalAlg`).
Conversely, every object `A` of `\hat{C}_Λ` is assembled from objects of `C_Λ`: its truncations
`A ⧸ 𝔪_A ^ (n + 1)` are Artinian local with the induced augmentation, so they are objects of `C_Λ`,
indexed so that level `0` is the residue field `k`. Completeness of `A` says exactly that `A` is
the limit in `\hat{C}_Λ` of its truncations: a morphism `B ⟶ A` is the same as a compatible family
of morphisms from `B` to all truncations of `A`. On the other side, a morphism from `A` to an
object of `C_Λ` kills a power of `𝔪_A`, as the maximal ideal of the target is nilpotent, and so
factors through a truncation of `A`. These are the two facts used to evaluate a functor on `C_Λ`
at an object of `\hat{C}_Λ` through its truncations (Stacks, Section 90.7).

## Main definitions

* `TauCeti.Deformation.IsCompleteLocalAug Λ k`: the property of an object of
  `Over (CommAlgCat.of Λ k)` of being a complete Noetherian local algebra with surjective
  augmentation.
* `TauCeti.Deformation.CompleteLocalAlg Λ k`: the complete local coefficient category `\hat{C}_Λ`.
* `TauCeti.Deformation.ArtinLocalAlg.toCompleteLocalAlg`: the fully faithful inclusion of `C_Λ` in
  `\hat{C}_Λ`.
* `TauCeti.Deformation.CompleteLocalAlg.truncation A n`: the object `A ⧸ 𝔪_A ^ (n + 1)` of `C_Λ`,
  with the quotient morphism `TauCeti.Deformation.CompleteLocalAlg.toTruncation` and the
  transition morphisms `TauCeti.Deformation.CompleteLocalAlg.truncationMap`.
* `TauCeti.Deformation.CompleteLocalAlg.truncationDiagram A`: the tower of truncations of `A`,
  and `TauCeti.Deformation.CompleteLocalAlg.truncationCone A`: the cone over it with vertex `A`.

## Main results

* `TauCeti.Deformation.CompleteLocalAlg.ker_augmentation`: the kernel of the augmentation is the
  maximal ideal, and `TauCeti.Deformation.CompleteLocalAlg.isLocalHom`: morphisms of `\hat{C}_Λ` are
  local homomorphisms.
* `TauCeti.Deformation.CompleteLocalAlg.isLimitTruncationCone`: every object of `\hat{C}_Λ` is the
  limit of its truncations.
* `TauCeti.Deformation.CompleteLocalAlg.exists_toTruncation_comp_eq`: a morphism from an object
  of `\hat{C}_Λ` to an object of `C_Λ` factors through a truncation.

## References

* [Stacks Project, Definition 90.4.1 (06GW)](https://stacks.math.columbia.edu/tag/06GW)
* M. Schlessinger, *Functors of Artin rings*, Trans. Amer. Math. Soc. 130 (1968), 208–222.
-/

public section

open CategoryTheory Limits IsLocalRing

universe u v

namespace TauCeti.Deformation

variable (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k]

/-- An object `A → k` of `Over (CommAlgCat.of Λ k)` is a *complete local augmented algebra* if
`A` is a Noetherian local ring, complete and separated for its maximal-ideal-adic topology, and
the augmentation `A → k` is surjective. The augmentation then identifies the residue field of `A`
with `k` as a `Λ`-algebra. Stacks, Definition 90.4.1 (06GW). -/
structure IsCompleteLocalAug (A : Over (CommAlgCat.of Λ k)) : Prop where
  /-- The underlying ring is Noetherian. -/
  isNoetherianRing : IsNoetherianRing A.left
  /-- The underlying ring is local. -/
  isLocalRing : IsLocalRing A.left
  /-- The underlying ring is complete and separated for the adic topology of its maximal ideal. -/
  isAdicComplete : IsAdicComplete (maximalIdeal A.left) A.left
  /-- The augmentation `A → k` is surjective. -/
  surjective : Function.Surjective A.hom.hom

/-- The *complete local coefficient category* `\hat{C}_Λ`: complete Noetherian local `Λ`-algebras
`A` with a surjective `Λ`-algebra map `A → k`, and `Λ`-algebra maps compatible with these maps.
Stacks, Definition 90.4.1 (06GW). -/
abbrev CompleteLocalAlg := ObjectProperty.FullSubcategory (IsCompleteLocalAug Λ k)

namespace CompleteLocalAlg

variable {Λ k}

instance (A : CompleteLocalAlg Λ k) : IsNoetherianRing A.obj.left := A.property.isNoetherianRing

instance (A : CompleteLocalAlg Λ k) : IsLocalRing A.obj.left := A.property.isLocalRing

instance (A : CompleteLocalAlg Λ k) : IsAdicComplete (maximalIdeal A.obj.left) A.obj.left :=
  A.property.isAdicComplete

/-- The augmentation `A → k` of an object `A` of `\hat{C}_Λ`. -/
def augmentation (A : CompleteLocalAlg Λ k) : A.obj.left →ₐ[Λ] k :=
  A.obj.hom.hom

/-- The augmentation of an object of `\hat{C}_Λ` is the structure map of its underlying object of
`Over (CommAlgCat.of Λ k)`. -/
theorem augmentation_def (A : CompleteLocalAlg Λ k) : A.augmentation = A.obj.hom.hom :=
  (rfl)

/-- The augmentation of an object of `\hat{C}_Λ` is surjective. -/
theorem augmentation_surjective (A : CompleteLocalAlg Λ k) :
    Function.Surjective A.augmentation :=
  A.property.surjective

/-- The kernel of the augmentation of an object of `\hat{C}_Λ` is its maximal ideal. -/
theorem ker_augmentation (A : CompleteLocalAlg Λ k) :
    RingHom.ker A.augmentation = maximalIdeal A.obj.left :=
  eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ A.augmentation_surjective)

/-- An element of an object of `\hat{C}_Λ` has augmentation zero exactly when it lies in the maximal
ideal. -/
@[simp]
theorem augmentation_eq_zero_iff {A : CompleteLocalAlg Λ k} {a : A.obj.left} :
    A.augmentation a = 0 ↔ a ∈ maximalIdeal A.obj.left := by
  rw [← RingHom.mem_ker, ker_augmentation]

/-- Morphisms of `\hat{C}_Λ` are determined by their underlying `Λ`-algebra maps. -/
@[ext]
theorem hom_ext {A B : CompleteLocalAlg Λ k} {f g : A ⟶ B}
    (h : f.hom.left.hom = g.hom.left.hom) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (CommAlgCat.hom_ext h))

/-- Morphisms of `\hat{C}_Λ` are compatible with the augmentations. -/
@[simp]
theorem augmentation_comp {A B : CompleteLocalAlg Λ k} (f : A ⟶ B) :
    B.augmentation.comp f.hom.left.hom = A.augmentation :=
  congrArg CommAlgCat.Hom.hom f.hom.w

/-- The elementwise form of `augmentation_comp`. -/
@[simp]
theorem augmentation_hom_apply {A B : CompleteLocalAlg Λ k} (f : A ⟶ B) (a : A.obj.left) :
    B.augmentation (f.hom.left.hom a) = A.augmentation a :=
  DFunLike.congr_fun (augmentation_comp f) a

/-- Every morphism of `\hat{C}_Λ` is a local homomorphism. -/
instance isLocalHom {A B : CompleteLocalAlg Λ k} (f : A ⟶ B) : IsLocalHom f.hom.left.hom where
  map_nonunit a ha := by
    rw [← not_not (a := IsUnit a), ← mem_nonunits_iff, ← mem_maximalIdeal,
      ← augmentation_eq_zero_iff, ← augmentation_hom_apply f, augmentation_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ha

/-- The object of `\hat{C}_Λ` given by a complete Noetherian local `Λ`-algebra `A` and a surjective
`Λ`-algebra map `π : A → k`. -/
-- Exposed because the carrier of `mk' A π hπ` is `A` by definitional unfolding.
@[expose] def mk' (A : Type v) [CommRing A] [Algebra Λ A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (π : A →ₐ[Λ] k) (hπ : Function.Surjective π) :
    CompleteLocalAlg Λ k :=
  ⟨Over.mk (CommAlgCat.ofHom π), ⟨‹_›, ‹_›, ‹_›, hπ⟩⟩

/-- The augmentation of `mk' A π hπ` is `π`. -/
@[simp]
theorem augmentation_mk' (A : Type v) [CommRing A] [Algebra Λ A] [IsNoetherianRing A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] (π : A →ₐ[Λ] k)
    (hπ : Function.Surjective π) : (mk' A π hπ).augmentation = π :=
  (rfl)

/-- The underlying algebra map of a composite in `\hat{C}_Λ`. -/
@[simp]
theorem comp_hom_left_hom_apply {A B C : CompleteLocalAlg Λ k} (f : A ⟶ B) (g : B ⟶ C)
    (a : A.obj.left) : (f ≫ g).hom.left.hom a = g.hom.left.hom (f.hom.left.hom a) :=
  (rfl)

/-- The morphism of `\hat{C}_Λ` given by a `Λ`-algebra map compatible with the augmentations. -/
def homMk' {A B : CompleteLocalAlg Λ k} (f : A.obj.left →ₐ[Λ] B.obj.left)
    (h : B.augmentation.comp f = A.augmentation) : A ⟶ B :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom f) (CommAlgCat.hom_ext h))

/-- The underlying algebra map of `homMk' f h` is `f`. -/
@[simp]
theorem homMk'_hom_left_hom {A B : CompleteLocalAlg Λ k} (f : A.obj.left →ₐ[Λ] B.obj.left)
    (h : B.augmentation.comp f = A.augmentation) : (homMk' f h).hom.left.hom = f :=
  (rfl)

end CompleteLocalAlg

section Artinian

variable {Λ k}

/-- An Artinian local augmented algebra is a complete local augmented algebra: an Artinian ring is
Noetherian, and it is complete for its maximal ideal, which is nilpotent. -/
theorem IsArtinLocalAug.isCompleteLocalAug {A : Over (CommAlgCat.of Λ k)}
    (hA : IsArtinLocalAug Λ k A) : IsCompleteLocalAug Λ k A := by
  have := hA.isArtinianRing
  have := hA.isLocalRing
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal A.left) := by
    rw [← ringJacobson_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_jacobson _
  have hsmul : maximalIdeal A.left ^ n • (⊤ : Submodule A.left A.left) = ⊥ := by
    rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul]
  exact ⟨inferInstance, inferInstance, isAdicComplete_of_pow_smul_eq_bot hsmul, hA.surjective⟩

variable (Λ k) in
/-- The Artinian coefficient category `C_Λ` is contained in `\hat{C}_Λ`. -/
theorem isArtinLocalAug_le_isCompleteLocalAug : IsArtinLocalAug Λ k ≤ IsCompleteLocalAug Λ k :=
  fun _ hA ↦ hA.isCompleteLocalAug

variable (Λ k) in
/-- The inclusion of the Artinian coefficient category `C_Λ` in `\hat{C}_Λ`. -/
-- Exposed because an object of `C_Λ` and its image in `\hat{C}_Λ` have the same underlying object
-- of `Over (CommAlgCat.of Λ k)` by definitional unfolding.
@[expose] def ArtinLocalAlg.toCompleteLocalAlg : ArtinLocalAlg Λ k ⥤ CompleteLocalAlg Λ k :=
  ObjectProperty.ιOfLE (isArtinLocalAug_le_isCompleteLocalAug Λ k)

variable (Λ k) in
/-- The inclusion of `C_Λ` in `\hat{C}_Λ` is fully faithful, as both are full subcategories of
`Over (CommAlgCat.of Λ k)`. -/
def ArtinLocalAlg.fullyFaithfulToCompleteLocalAlg : (toCompleteLocalAlg Λ k).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

instance : (ArtinLocalAlg.toCompleteLocalAlg Λ k).Full :=
  (ArtinLocalAlg.fullyFaithfulToCompleteLocalAlg Λ k).full

instance : (ArtinLocalAlg.toCompleteLocalAlg Λ k).Faithful :=
  (ArtinLocalAlg.fullyFaithfulToCompleteLocalAlg Λ k).faithful

/-- The augmentation of an object of `C_Λ`, regarded as an object of `\hat{C}_Λ`, is its
augmentation in `C_Λ`. -/
@[simp]
theorem ArtinLocalAlg.augmentation_toCompleteLocalAlg_obj (A : ArtinLocalAlg Λ k) :
    ((toCompleteLocalAlg Λ k).obj A).augmentation = A.augmentation := by
  rw [CompleteLocalAlg.augmentation_def, ArtinLocalAlg.augmentation_def]
  rfl

/-- The underlying algebra map of a morphism of `C_Λ`, regarded as a morphism of `\hat{C}_Λ`, is
unchanged. -/
@[simp]
theorem ArtinLocalAlg.toCompleteLocalAlg_map_hom_left_hom {A B : ArtinLocalAlg Λ k}
    (f : A ⟶ B) : ((toCompleteLocalAlg Λ k).map f).hom.left.hom = f.hom.left.hom :=
  (rfl)

end Artinian

namespace CompleteLocalAlg

open ArtinLocalAlg

variable {Λ k} (A : CompleteLocalAlg Λ k)

section Truncation

/-- The augmentation of `A` kills every power `𝔪_A ^ (n + 1)` of its maximal ideal. -/
theorem augmentation_eq_zero_of_mem_maximalIdeal_pow (n : ℕ) {a : A.obj.left}
    (ha : a ∈ maximalIdeal A.obj.left ^ (n + 1)) : A.augmentation a = 0 :=
  augmentation_eq_zero_iff.mpr (Ideal.pow_le_self n.succ_ne_zero ha)

/-- The truncation `A ⧸ 𝔪_A ^ (n + 1)` of an object `A` of `\hat{C}_Λ`, an object of `C_Λ` with the
augmentation induced by that of `A`. Level `0` is the residue field `k`. -/
-- Exposed because the carrier of `truncation A n` is `A ⧸ 𝔪_A ^ (n + 1)` by definitional
-- unfolding.
@[expose] noncomputable def truncation (n : ℕ) : ArtinLocalAlg Λ k :=
  ArtinLocalAlg.mk' (A.obj.left ⧸ maximalIdeal A.obj.left ^ (n + 1))
    (Ideal.Quotient.liftₐ _ A.augmentation fun _ ↦ A.augmentation_eq_zero_of_mem_maximalIdeal_pow n)
    fun c ↦ by
      obtain ⟨a, rfl⟩ := A.augmentation_surjective c
      exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- The augmentation of the truncation `A ⧸ 𝔪_A ^ (n + 1)` takes the class of `a` to the
augmentation of `a`. -/
@[simp]
theorem augmentation_truncation_mk (n : ℕ) (a : A.obj.left) :
    (A.truncation n).augmentation (Ideal.Quotient.mk (maximalIdeal A.obj.left ^ (n + 1)) a) =
      A.augmentation a := by
  -- The augmentation of `truncation A n` is by construction the map induced by that of `A`.
  rw [ArtinLocalAlg.augmentation_def]
  rfl

/-- The quotient morphism `A ⟶ A ⧸ 𝔪_A ^ (n + 1)` of `\hat{C}_Λ`. -/
noncomputable def toTruncation (n : ℕ) : A ⟶ (toCompleteLocalAlg Λ k).obj (A.truncation n) :=
  homMk' (Ideal.Quotient.mkₐ Λ (maximalIdeal A.obj.left ^ (n + 1))) <| by
    ext a
    rw [augmentation_toCompleteLocalAlg_obj]
    exact A.augmentation_truncation_mk n a

/-- The quotient morphism `A ⟶ A ⧸ 𝔪_A ^ (n + 1)` takes `a` to its class. -/
@[simp]
theorem toTruncation_hom_left_hom_apply (n : ℕ) (a : A.obj.left) :
    (A.toTruncation n).hom.left.hom a = Ideal.Quotient.mk (maximalIdeal A.obj.left ^ (n + 1)) a :=
  DFunLike.congr_fun (homMk'_hom_left_hom _ _) a

/-- The quotient morphism `A ⟶ A ⧸ 𝔪_A ^ (n + 1)` is surjective. -/
theorem toTruncation_surjective (n : ℕ) :
    Function.Surjective (A.toTruncation n).hom.left.hom := fun x ↦ by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨a, A.toTruncation_hom_left_hom_apply n a⟩

variable {A} in
/-- An element of an object of `\hat{C}_Λ` is determined by its images in all truncations. -/
theorem eq_of_forall_toTruncation_eq {a b : A.obj.left}
    (h : ∀ n, (A.toTruncation n).hom.left.hom a = (A.toTruncation n).hom.left.hom b) : a = b := by
  refine (IsHausdorff.eq_iff_smodEq (I := maximalIdeal A.obj.left)).mpr fun n ↦ ?_
  rcases n with - | n
  · simp [SModEq, Ideal.Quotient.eq]
  · simp only [toTruncation_hom_left_hom_apply] at h
    simpa [SModEq.sub_mem] using Ideal.Quotient.eq.mp (h n)

/-- The transition morphism `A ⧸ 𝔪_A ^ (n + 1) ⟶ A ⧸ 𝔪_A ^ (m + 1)` of `C_Λ`, for `m ≤ n`. -/
noncomputable def truncationMap {m n : ℕ} (h : m ≤ n) : A.truncation n ⟶ A.truncation m :=
  ArtinLocalAlg.homMk' (Ideal.Quotient.factorₐ Λ
      (Ideal.pow_le_pow_right (I := maximalIdeal A.obj.left) (Nat.succ_le_succ h))) <| by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (A.augmentation_truncation_mk m a).trans (A.augmentation_truncation_mk n a).symm

/-- The transition morphism takes the class of `a` to the class of `a`. -/
@[simp]
theorem truncationMap_hom_left_hom_mk {m n : ℕ} (h : m ≤ n) (a : A.obj.left) :
    (A.truncationMap h).hom.left.hom (Ideal.Quotient.mk (maximalIdeal A.obj.left ^ (n + 1)) a) =
      Ideal.Quotient.mk (maximalIdeal A.obj.left ^ (m + 1)) a :=
  DFunLike.congr_fun (ArtinLocalAlg.homMk'_hom_left_hom _ _) _

/-- The transition morphisms between truncations are surjective. -/
theorem truncationMap_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (A.truncationMap h).hom.left.hom := fun x ↦ by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨_, A.truncationMap_hom_left_hom_mk h a⟩

/-- The transition morphism from a truncation to itself is the identity. -/
@[simp]
theorem truncationMap_refl (n : ℕ) : A.truncationMap le_rfl = 𝟙 (A.truncation n) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [truncationMap_hom_left_hom_mk, CategoryTheory.ObjectProperty.FullSubcategory.id_hom,
    Over.id_left, CommAlgCat.hom_id]
  exact (AlgHom.id_apply _).symm

/-- Transition morphisms between truncations compose. -/
@[reassoc (attr := simp)]
theorem truncationMap_comp_truncationMap {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    A.truncationMap hmn ≫ A.truncationMap hlm = A.truncationMap (hlm.trans hmn) := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (congrArg _ (A.truncationMap_hom_left_hom_mk hmn a)).trans
    ((A.truncationMap_hom_left_hom_mk hlm a).trans (A.truncationMap_hom_left_hom_mk _ a).symm)

/-- The quotient morphisms of `A` are compatible with the transition morphisms. -/
@[reassoc (attr := simp)]
theorem toTruncation_comp_truncationMap {m n : ℕ} (h : m ≤ n) :
    A.toTruncation n ≫ (toCompleteLocalAlg Λ k).map (A.truncationMap h) = A.toTruncation m := by
  ext a
  exact (congrArg _ (A.toTruncation_hom_left_hom_apply n a)).trans
    ((A.truncationMap_hom_left_hom_mk h a).trans (A.toTruncation_hom_left_hom_apply m a).symm)

/-- The tower `⋯ ⟶ A ⧸ 𝔪_A ^ 3 ⟶ A ⧸ 𝔪_A ^ 2 ⟶ A ⧸ 𝔪_A = k` of truncations of `A` in `C_Λ`. -/
-- Exposed so that its objects and maps are the truncations and transition morphisms by
-- definitional unfolding, as recorded by the generated `simps` lemmas.
@[expose, simps]
noncomputable def truncationDiagram : ℕᵒᵖ ⥤ ArtinLocalAlg Λ k where
  obj n := A.truncation n.unop
  map f := A.truncationMap (leOfHom f.unop)
  map_id _ := A.truncationMap_refl _
  map_comp _ _ := (A.truncationMap_comp_truncationMap _ _).symm

/-- The cone over the tower of truncations of `A`, regarded in `\hat{C}_Λ`, with vertex `A` and the
quotient morphisms as legs. -/
-- Exposed so that its vertex and legs are `A` and the quotient morphisms by definitional
-- unfolding, as recorded by the generated `simps` lemmas.
@[expose, simps]
noncomputable def truncationCone : Cone (A.truncationDiagram ⋙ toCompleteLocalAlg Λ k) where
  pt := A
  π :=
    { app n := A.toTruncation n.unop
      naturality _ _ f :=
        (Category.id_comp _).trans (A.toTruncation_comp_truncationMap (leOfHom f.unop)).symm }

end Truncation

section Limit

section Lift

variable {R B : Type*} [CommRing R] [Algebra Λ R] (I : Ideal R) [CommRing B] [Algebra Λ B]
  (g : ∀ n : ℕ, B →ₐ[Λ] R ⧸ I ^ (n + 1))
  (hg : ∀ {m n : ℕ} (h : m ≤ n),
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ h))).comp (g n) =
      g m)

include hg in
/-- A family of algebra maps to the quotients `R ⧸ I ^ (n + 1)`, compatible with the transitions,
gives a family to the quotients `R ⧸ I ^ n`, compatible as in `IsAdicComplete.liftAlgHom`. -/
private theorem factorₐ_comp_factorₐ_comp {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right (I := I) h)).comp
        ((Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right n.le_succ)).comp (g n)) =
      (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right m.le_succ)).comp (g m) := by
  ext x
  rw [← hg h, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (g n x)
  simp only [← ha, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]

variable [IsAdicComplete I R]

/-- The algebra map to an adically complete ring assembled from compatible algebra maps to its
quotients `R ⧸ I ^ (n + 1)`. -/
private noncomputable def liftSucc : B →ₐ[Λ] R :=
  IsAdicComplete.liftAlgHom I
    (fun n ↦ (Ideal.Quotient.factorₐ Λ (Ideal.pow_le_pow_right n.le_succ)).comp (g n))
    (factorₐ_comp_factorₐ_comp I g hg)

private theorem mk_liftSucc (n : ℕ) (x : B) :
    Ideal.Quotient.mk (I ^ (n + 1)) (liftSucc I g hg x) = g n x := by
  rw [liftSucc, IsAdicComplete.mk_liftAlgHom _ _ (factorₐ_comp_factorₐ_comp I g hg),
    AlgHom.comp_apply, ← hg n.le_succ, AlgHom.comp_apply]

end Lift

variable {A} {B : CompleteLocalAlg Λ k} (s : Cone (A.truncationDiagram ⋙ toCompleteLocalAlg Λ k))

/-- The leg at level `n` of a cone over the tower of truncations of `A`, as an algebra map to
`A ⧸ 𝔪_A ^ (n + 1)`. -/
private noncomputable def coneLeg (n : ℕ) :
    s.pt.obj.left →ₐ[Λ] A.obj.left ⧸ maximalIdeal A.obj.left ^ (n + 1) :=
  (s.π.app (.op n)).hom.left.hom

private theorem coneLeg_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Λ
        (Ideal.pow_le_pow_right (I := maximalIdeal A.obj.left) (Nat.succ_le_succ h))).comp
      (coneLeg s n) = coneLeg s m := by
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (coneLeg s n x)
  refine (congrArg _ ha.symm).trans ((A.truncationMap_hom_left_hom_mk h a).symm.trans ?_)
  exact (congrArg (A.truncationMap h).hom.left.hom ha).trans
    (congrArg (fun φ ↦ φ.hom.left.hom x) (s.w (homOfLE h).op))

/-- The algebra map from the vertex of a cone over the tower of truncations of `A` to `A`,
assembled from its legs by completeness of `A`. -/
private noncomputable def coneLift : s.pt.obj.left →ₐ[Λ] A.obj.left :=
  liftSucc (maximalIdeal A.obj.left) (coneLeg s) (coneLeg_compatible s)

private theorem mk_coneLift (n : ℕ) (x : s.pt.obj.left) :
    Ideal.Quotient.mk (maximalIdeal A.obj.left ^ (n + 1)) (coneLift s x) =
      (s.π.app (.op n)).hom.left.hom x :=
  mk_liftSucc _ _ _ n x

variable (A) in
/-- **Every object of `\hat{C}_Λ` is the limit of its truncations.** A compatible family of
morphisms from an object `B` of `\hat{C}_Λ` to the truncations `A ⧸ 𝔪_A ^ (n + 1)` comes from a
unique morphism `B ⟶ A`. -/
noncomputable def isLimitTruncationCone : IsLimit A.truncationCone where
  lift s := homMk' (coneLift s) <| by
    ext x
    exact (A.augmentation_truncation_mk 0 _).symm.trans
      ((congrArg (A.truncation 0).augmentation (mk_coneLift s 0 x)).trans
        ((DFunLike.congr_fun (augmentation_toCompleteLocalAlg_obj (A.truncation 0)).symm _).trans
          (augmentation_hom_apply (s.π.app (.op 0)) x)))
  fac s n := by
    ext x
    exact mk_coneLift s n.unop x
  uniq s f hf := by
    ext x
    refine eq_of_forall_toTruncation_eq fun n ↦ ?_
    exact (congrArg (fun φ ↦ φ.hom.left.hom x) (hf (.op n))).trans
      ((mk_coneLift s n x).symm.trans (A.toTruncation_hom_left_hom_apply n _).symm)

/-- Two morphisms into an object of `\hat{C}_Λ` agreeing after composition with every quotient
morphism to its truncations are equal. -/
theorem hom_ext_of_toTruncation {f g : B ⟶ A}
    (h : ∀ n, f ≫ A.toTruncation n = g ≫ A.toTruncation n) : f = g :=
  (isLimitTruncationCone A).hom_ext fun n ↦ h n.unop

end Limit

section Factorization

/-- A morphism of `\hat{C}_Λ` from `A` to an object of `C_Λ` kills a power of the maximal ideal of
`A`: it is local, and the maximal ideal of the Artinian target is nilpotent. -/
theorem exists_maximalIdeal_pow_le_ker {B : ArtinLocalAlg Λ k}
    (f : A ⟶ (toCompleteLocalAlg Λ k).obj B) :
    ∃ n, maximalIdeal A.obj.left ^ (n + 1) ≤ RingHom.ker f.hom.left.hom := by
  -- The underlying map of `f`, with target the underlying ring of `B`.
  let φ : A.obj.left →ₐ[Λ] B.obj.left := f.hom.left.hom
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal B.obj.left) := by
    rw [← ringJacobson_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_jacobson _
  have hle : maximalIdeal A.obj.left ≤ (maximalIdeal B.obj.left).comap φ := fun a ha ↦ by
    rw [Ideal.mem_comap, ← ArtinLocalAlg.augmentation_eq_zero_iff]
    exact (DFunLike.congr_fun (augmentation_toCompleteLocalAlg_obj B).symm _).trans
      ((augmentation_hom_apply f a).trans (augmentation_eq_zero_iff.mpr ha))
  have hker : maximalIdeal A.obj.left ^ (n + 1) ≤ RingHom.ker φ := by
    refine (Ideal.pow_le_pow_right n.le_succ).trans ?_
    calc maximalIdeal A.obj.left ^ n
        ≤ ((maximalIdeal B.obj.left).comap φ) ^ n := Ideal.pow_right_mono hle n
      _ ≤ (maximalIdeal B.obj.left ^ n).comap φ := Ideal.le_comap_pow _ n
      _ = RingHom.ker φ := by rw [hn, Ideal.zero_eq_bot, RingHom.ker_eq_comap_bot]
  exact ⟨n, hker⟩

/-- **Factorization through a truncation.** A morphism of `\hat{C}_Λ` from `A` to an object of `C_Λ`
factors through the quotient morphism to some truncation `A ⧸ 𝔪_A ^ (n + 1)`. -/
theorem exists_toTruncation_comp_eq {B : ArtinLocalAlg Λ k}
    (f : A ⟶ (toCompleteLocalAlg Λ k).obj B) :
    ∃ (n : ℕ) (g : A.truncation n ⟶ B), A.toTruncation n ≫ (toCompleteLocalAlg Λ k).map g = f := by
  obtain ⟨n, hn⟩ := A.exists_maximalIdeal_pow_le_ker f
  refine ⟨n, ArtinLocalAlg.homMk' (Ideal.Quotient.liftₐ _ f.hom.left.hom fun a ha ↦ hn ha) ?_, ?_⟩
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun (augmentation_toCompleteLocalAlg_obj B).symm _).trans
      ((augmentation_hom_apply f a).trans (A.augmentation_truncation_mk n a).symm)
  · ext a
    exact (congrArg _ (A.toTruncation_hom_left_hom_apply n a)).trans
      ((DFunLike.congr_fun (ArtinLocalAlg.homMk'_hom_left_hom _ _) _).trans
        (Ideal.Quotient.lift_mk _ _ _))

end Factorization

end CompleteLocalAlg

end TauCeti.Deformation
