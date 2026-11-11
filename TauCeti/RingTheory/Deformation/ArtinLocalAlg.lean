/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.LocalRing.Pullback
public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.RingTheory.Artinian.RestrictScalars

/-!
# The Artinian coefficient category

Fix a commutative ring `Λ` and a field `k` with a `Λ`-algebra structure. The *Artinian coefficient
category* `C_Λ` has as objects the Artinian local `Λ`-algebras `A` together with a surjective
`Λ`-algebra map `A → k`, and as morphisms the `Λ`-algebra maps compatible with these maps to `k`
(Stacks, Definition 90.3.1 (06GC), in the setting of Section 90.2 (06G9)). It is the source
category of the deformation functors of formal deformation theory: a deformation problem over `k`
is a functor `C_Λ ⥤ Type` recording the deformations over each Artinian thickening of `k`.

Since `A` is local and `A → k` is a surjection onto a field, the kernel of the augmentation is the
maximal ideal of `A` (`TauCeti.Deformation.ArtinLocalAlg.ker_augmentation`), so the augmentation
identifies the residue field of `A` with `k`. It follows that every morphism of `C_Λ` is a local
homomorphism (`TauCeti.Deformation.ArtinLocalAlg.isLocalHom`). We realise `C_Λ` as a full
subcategory of `Over (CommAlgCat.of Λ k)`.

The test objects of deformation theory are small extensions: surjections `A' → A` in `C_Λ` whose
kernel is a nonzero principal ideal killed by the maximal ideal of `A'` (Stacks, Definition 90.3.2
(06GD)). The basic one is the augmentation `k[ε] → k` of the dual numbers, the source of the
tangent space of a deformation functor.

Schlessinger's conditions compare the values of a deformation functor on a fibre product
`A' ×_A A''` with those on `A'` and `A''`. For `A'' → A` surjective this fibre product is again an
object of `C_Λ` (Stacks, Lemma 90.3.8 (06GH)): the subalgebra `AlgHom.pullback` of `A' × A''` is
local (`AlgHom.isLocalRing_pullback`), and it is Artinian, as it maps onto the residue fields of
the Artinian local rings `A'` and `A''`
(`TauCeti.isArtinian_of_isNilpotent_of_surjective_algebraMap_quotient`).

The Stacks Project assumes moreover that `Λ` is Noetherian and `k` is finite over `Λ`; neither
hypothesis is needed for the definitions and results here.

## Main definitions

* `TauCeti.Deformation.IsArtinLocalAug Λ k`: the property of an object of
  `Over (CommAlgCat.of Λ k)` of being an Artinian local algebra with surjective augmentation.
* `TauCeti.Deformation.ArtinLocalAlg Λ k`: the Artinian coefficient category `C_Λ`.
* `TauCeti.Deformation.ArtinLocalAlg.augmentation`: the augmentation `A → k` of an object.
* `TauCeti.Deformation.ArtinLocalAlg.residue Λ k`: the object `k`, augmented by the identity.
* `TauCeti.Deformation.ArtinLocalAlg.toResidue A`: the augmentation as a morphism `A ⟶ k`.
* `TauCeti.Deformation.ArtinLocalAlg.dualNumbers Λ k`: the dual numbers `k[ε]`, augmented by
  `ε ↦ 0`.
* `TauCeti.Deformation.ArtinLocalAlg.IsSmallExtension f`: the morphism `f` is a small extension.
* `TauCeti.Deformation.ArtinLocalAlg.pullback f g hg`: the fibre product `A' ×_A A''` of
  `f : A' ⟶ A` and a surjective `g : A'' ⟶ A`, with projections
  `TauCeti.Deformation.ArtinLocalAlg.pullbackFst` and
  `TauCeti.Deformation.ArtinLocalAlg.pullbackSnd`.

## Main results

* `TauCeti.Deformation.ArtinLocalAlg.ker_augmentation`: the kernel of the augmentation is the
  maximal ideal.
* `TauCeti.Deformation.ArtinLocalAlg.isLocalHom`: morphisms of `C_Λ` are local homomorphisms.
* `TauCeti.Deformation.ArtinLocalAlg.isTerminalResidue`: `k` is a terminal object of `C_Λ`.
* `TauCeti.Deformation.ArtinLocalAlg.isSmallExtension_iff`: a morphism is a small extension
  exactly when it is surjective with kernel spanned by a nonzero element killed by the maximal
  ideal.
* `TauCeti.Deformation.ArtinLocalAlg.isSmallExtension_toResidue_dualNumbers`: the augmentation
  `k[ε] → k` is a small extension.
* `TauCeti.Deformation.ArtinLocalAlg.not_isSmallExtension_toResidue_residue`: the identity of
  `k` is not a small extension, as its kernel is zero.
* `TauCeti.Deformation.ArtinLocalAlg.isArtinianRing_pullback`: the fibre product of
  Artinian local rings along a surjection, over a common residue field, is Artinian.
* `TauCeti.Deformation.ArtinLocalAlg.isPullback`: `A' ×_A A''` is a pullback in `C_Λ`.

## References

* [Stacks Project, Section 90.3 (06GB)](https://stacks.math.columbia.edu/tag/06GB)
* M. Schlessinger, *Functors of Artin rings*, Trans. Amer. Math. Soc. 130 (1968), 208–222.
-/

public section

open CategoryTheory Limits IsLocalRing

universe u v

namespace TauCeti.Deformation

variable (Λ : Type u) [CommRing Λ] (k : Type v) [Field k] [Algebra Λ k]

/-- An object `A → k` of `Over (CommAlgCat.of Λ k)` is an *Artinian local augmented algebra* if
`A` is an Artinian local ring and the augmentation `A → k` is surjective. The augmentation then
identifies the residue field of `A` with `k` as a `Λ`-algebra. Stacks, Definition 90.3.1 (06GC). -/
structure IsArtinLocalAug (A : Over (CommAlgCat.of Λ k)) : Prop where
  /-- The underlying ring is Artinian. -/
  isArtinianRing : IsArtinianRing A.left
  /-- The underlying ring is local. -/
  isLocalRing : IsLocalRing A.left
  /-- The augmentation `A → k` is surjective. -/
  surjective : Function.Surjective A.hom.hom

/-- The *Artinian coefficient category* `C_Λ`: Artinian local `Λ`-algebras `A` with a surjective
`Λ`-algebra map `A → k`, and `Λ`-algebra maps compatible with these maps. Stacks,
Definition 90.3.1 (06GC). -/
abbrev ArtinLocalAlg := ObjectProperty.FullSubcategory (IsArtinLocalAug Λ k)

namespace ArtinLocalAlg

variable {Λ k}

instance (A : ArtinLocalAlg Λ k) : IsArtinianRing A.obj.left := A.property.isArtinianRing

instance (A : ArtinLocalAlg Λ k) : IsLocalRing A.obj.left := A.property.isLocalRing

/-- The augmentation `A → k` of an object `A` of `C_Λ`. -/
def augmentation (A : ArtinLocalAlg Λ k) : A.obj.left →ₐ[Λ] k :=
  A.obj.hom.hom

/-- The augmentation of an object of `C_Λ` is surjective. -/
theorem augmentation_surjective (A : ArtinLocalAlg Λ k) : Function.Surjective A.augmentation :=
  A.property.surjective

/-- The kernel of the augmentation of an object of `C_Λ` is its maximal ideal. -/
theorem ker_augmentation (A : ArtinLocalAlg Λ k) :
    RingHom.ker A.augmentation = maximalIdeal A.obj.left :=
  have := RingHom.ker_isMaximal_of_surjective _ A.augmentation_surjective
  eq_maximalIdeal this

/-- An element of an object of `C_Λ` has augmentation zero exactly when it lies in the maximal
ideal. -/
@[simp]
theorem augmentation_eq_zero_iff {A : ArtinLocalAlg Λ k} {a : A.obj.left} :
    A.augmentation a = 0 ↔ a ∈ maximalIdeal A.obj.left := by
  rw [← RingHom.mem_ker, ker_augmentation]

/-- An element of an object of `C_Λ` is a unit exactly when its augmentation is nonzero. -/
theorem isUnit_iff_augmentation_ne_zero {A : ArtinLocalAlg Λ k} {a : A.obj.left} :
    IsUnit a ↔ A.augmentation a ≠ 0 := by
  rw [Ne, augmentation_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]

/-- Morphisms of `C_Λ` are determined by their underlying `Λ`-algebra maps. -/
@[ext]
theorem hom_ext {A B : ArtinLocalAlg Λ k} {f g : A ⟶ B}
    (h : f.hom.left.hom = g.hom.left.hom) : f = g :=
  ObjectProperty.hom_ext _ (Over.OverMorphism.ext (CommAlgCat.hom_ext h))

/-- Morphisms of `C_Λ` are compatible with the augmentations. -/
@[simp]
theorem augmentation_comp {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) :
    B.augmentation.comp f.hom.left.hom = A.augmentation :=
  congrArg CommAlgCat.Hom.hom f.hom.w

/-- The elementwise form of `augmentation_comp`. -/
@[simp]
theorem augmentation_hom_apply {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) (a : A.obj.left) :
    B.augmentation (f.hom.left.hom a) = A.augmentation a :=
  DFunLike.congr_fun (augmentation_comp f) a

/-- Every morphism of `C_Λ` is a local homomorphism. -/
instance isLocalHom {A B : ArtinLocalAlg Λ k} (f : A ⟶ B) : IsLocalHom f.hom.left.hom where
  map_nonunit a ha := by
    rw [isUnit_iff_augmentation_ne_zero, augmentation_hom_apply] at ha
    exact isUnit_iff_augmentation_ne_zero.mpr ha

/-- The object of `C_Λ` given by an Artinian local `Λ`-algebra `A` and a surjective `Λ`-algebra
map `π : A → k`. -/
-- Exposed because the carrier of `mk' A π hπ` is `A` by definitional unfolding.
@[expose] def mk' (A : Type v) [CommRing A] [Algebra Λ A] [IsArtinianRing A] [IsLocalRing A]
    (π : A →ₐ[Λ] k) (hπ : Function.Surjective π) : ArtinLocalAlg Λ k :=
  ⟨Over.mk (CommAlgCat.ofHom π), ⟨‹_›, ‹_›, hπ⟩⟩

/-- The augmentation of `mk' A π hπ` is `π`. -/
@[simp]
theorem augmentation_mk' (A : Type v) [CommRing A] [Algebra Λ A] [IsArtinianRing A]
    [IsLocalRing A] (π : A →ₐ[Λ] k) (hπ : Function.Surjective π) :
    (mk' A π hπ).augmentation = π :=
  (rfl)

/-- The morphism of `C_Λ` given by a `Λ`-algebra map compatible with the augmentations. -/
def homMk' {A B : ArtinLocalAlg Λ k} (f : A.obj.left →ₐ[Λ] B.obj.left)
    (h : B.augmentation.comp f = A.augmentation) : A ⟶ B :=
  ObjectProperty.homMk (Over.homMk (CommAlgCat.ofHom f) (CommAlgCat.hom_ext h))

/-- The underlying algebra map of `homMk' f h` is `f`. -/
@[simp]
theorem homMk'_hom_left_hom {A B : ArtinLocalAlg Λ k} (f : A.obj.left →ₐ[Λ] B.obj.left)
    (h : B.augmentation.comp f = A.augmentation) : (homMk' f h).hom.left.hom = f :=
  (rfl)

section Residue

variable (Λ k) in
/-- The residue field `k` as an object of `C_Λ`, augmented by the identity. -/
-- Exposed because the carrier of `residue Λ k` is `k` by definitional unfolding.
@[expose] def residue : ArtinLocalAlg Λ k :=
  mk' k (AlgHom.id Λ k) Function.surjective_id

/-- The augmentation of `residue Λ k` is the identity. -/
@[simp]
theorem augmentation_residue : (residue Λ k).augmentation = AlgHom.id Λ k :=
  (rfl)

/-- The augmentation of an object `A` of `C_Λ`, as a morphism `A ⟶ residue Λ k`. -/
def toResidue (A : ArtinLocalAlg Λ k) : A ⟶ residue Λ k :=
  homMk' A.augmentation (AlgHom.id_comp _)

/-- The underlying algebra map of `toResidue A` is the augmentation of `A`. -/
@[simp]
theorem toResidue_hom_left_hom (A : ArtinLocalAlg Λ k) :
    (toResidue A).hom.left.hom = A.augmentation :=
  (rfl)

/-- The augmentation morphism `A ⟶ residue Λ k` is surjective. -/
theorem toResidue_surjective (A : ArtinLocalAlg Λ k) :
    Function.Surjective (toResidue A).hom.left.hom :=
  A.augmentation_surjective

/-- Every morphism to `residue Λ k` is the augmentation. -/
theorem eq_toResidue {A : ArtinLocalAlg Λ k} (f : A ⟶ residue Λ k) : f = toResidue A := by
  ext a
  exact augmentation_hom_apply f a

variable (Λ k) in
/-- The residue field `k` is a terminal object of `C_Λ`. -/
def isTerminalResidue : IsTerminal (residue Λ k) :=
  IsTerminal.ofUniqueHom toResidue fun _ f ↦ eq_toResidue f

instance : HasTerminal (ArtinLocalAlg Λ k) :=
  (isTerminalResidue Λ k).hasTerminal

end Residue

section DualNumbers

open DualNumber TrivSqZeroExt

variable (Λ k) in
/-- The dual numbers `k[ε]` as an object of `C_Λ`, augmented by `a + bε ↦ a`. -/
-- Exposed because the carrier of `dualNumbers Λ k` is `k[ε]` by definitional unfolding.
@[expose] def dualNumbers : ArtinLocalAlg Λ k :=
  mk' k[ε] (fstHom Λ k k) fun a ↦ ⟨inl a, fst_inl k a⟩

/-- The augmentation of `dualNumbers Λ k` takes `a + bε` to `a`. -/
@[simp]
theorem augmentation_dualNumbers : (dualNumbers Λ k).augmentation = fstHom Λ k k :=
  (rfl)

end DualNumbers

section SmallExtension

open DualNumber TrivSqZeroExt

/-- A morphism `f : A' ⟶ A` of `C_Λ` is a *small extension* if it is surjective and its kernel is a
nonzero principal ideal annihilated by the maximal ideal of `A'`. Stacks, Definition 90.3.2
(06GD). -/
structure IsSmallExtension {A' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) : Prop where
  /-- A small extension is surjective. -/
  surjective : Function.Surjective f.hom.left.hom
  /-- The kernel of a small extension is nonzero. -/
  ker_ne_bot : RingHom.ker f.hom.left.hom ≠ ⊥
  /-- The kernel of a small extension is principal. -/
  ker_isPrincipal : (RingHom.ker f.hom.left.hom).IsPrincipal
  /-- The kernel of a small extension is annihilated by the maximal ideal. -/
  maximalIdeal_mul_ker : maximalIdeal A'.obj.left * RingHom.ker f.hom.left.hom = ⊥

/-- A morphism of `C_Λ` is a small extension exactly when it is surjective and its kernel is
spanned by a nonzero element annihilated by the maximal ideal. -/
theorem isSmallExtension_iff {A' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) :
    IsSmallExtension f ↔ Function.Surjective f.hom.left.hom ∧
      ∃ t : A'.obj.left, t ≠ 0 ∧ RingHom.ker f.hom.left.hom = Ideal.span {t} ∧
        ∀ x ∈ maximalIdeal A'.obj.left, x * t = 0 := by
  refine ⟨fun ⟨hsurj, hne, ⟨t, ht⟩, hmul⟩ ↦ ⟨hsurj, t, ?_, ht, fun x hx ↦ ?_⟩,
    fun ⟨hsurj, t, ht0, ht, hmul⟩ ↦ ⟨hsurj, ?_, ⟨t, ht⟩, ?_⟩⟩
  · rintro rfl
    exact hne (by simpa using ht)
  · rw [← Ideal.mem_bot, ← hmul, ht]
    exact Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self t)
  · rwa [ht, Ne, Ideal.span_singleton_eq_bot]
  · rw [ht, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [Ideal.mem_bot, mul_left_comm, hmul x hx, mul_zero]

/-- The augmentation `k[ε] → k` of the dual numbers is a small extension: its kernel is spanned by
`ε`, and `ε` is annihilated by the maximal ideal `(ε)`. -/
theorem isSmallExtension_toResidue_dualNumbers :
    IsSmallExtension (toResidue (dualNumbers Λ k)) := by
  have hker : RingHom.ker (dualNumbers Λ k).augmentation = Ideal.span {ε} := by
    rw [ker_augmentation]
    exact DualNumber.maximalIdeal_eq_span_singleton_eps
  have hε : (ε : k[ε]) ≠ 0 := fun h ↦ by simpa using congrArg snd h
  have hmul (c : k[ε]) : c * ε * ε = 0 := by rw [mul_assoc, eps_mul_eps, mul_zero]
  refine (isSmallExtension_iff _).mpr ⟨(dualNumbers Λ k).augmentation_surjective, ε, hε,
    by rwa [toResidue_hom_left_hom], fun x hx ↦ ?_⟩
  rw [← ker_augmentation, hker] at hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  exact hmul c

/-- The identity of `k` is not a small extension, as its kernel is zero. -/
theorem not_isSmallExtension_toResidue_residue :
    ¬ IsSmallExtension (toResidue (residue Λ k)) := fun h ↦
  h.ker_ne_bot ((RingHom.injective_iff_ker_eq_bot _).mp fun _ _ h ↦ h)

end SmallExtension

section Pullback

variable {A' A'' A : ArtinLocalAlg Λ k} (f : A' ⟶ A) (g : A'' ⟶ A)

/-- The underlying algebra map of a composite in `C_Λ`. -/
@[simp]
theorem comp_hom_left_hom_apply {B : ArtinLocalAlg Λ k} (φ : A' ⟶ A) (ψ : A ⟶ B)
    (a : A'.obj.left) : (φ ≫ ψ).hom.left.hom a = ψ.hom.left.hom (φ.hom.left.hom a) :=
  (rfl)

/-- The augmentation of the fibre product `AlgHom.pullback f g` of the underlying algebra maps,
through its first component. -/
def pullbackAugmentation : AlgHom.pullback f.hom.left.hom g.hom.left.hom →ₐ[Λ] k :=
  A'.augmentation.comp (AlgHom.pullbackFst _ _)

/-- The augmentation of the fibre product is that of its first component. -/
@[simp]
theorem pullbackAugmentation_apply (x : AlgHom.pullback f.hom.left.hom g.hom.left.hom) :
    pullbackAugmentation f g x = A'.augmentation x.1.1 :=
  (rfl)

/-- The two components of a point of the fibre product have the same augmentation. -/
theorem augmentation_snd_pullback (x : AlgHom.pullback f.hom.left.hom g.hom.left.hom) :
    A''.augmentation x.1.2 = A'.augmentation x.1.1 := by
  have hx : f.hom.left.hom x.1.1 = g.hom.left.hom x.1.2 :=
    AlgHom.congr_fun (AlgHom.pullback_comm_sq _ _) x
  rw [← augmentation_hom_apply g, ← hx, augmentation_hom_apply]

variable {f g}

/-- If `g` is surjective, the augmentation of the fibre product is surjective. -/
theorem pullbackAugmentation_surjective (hg : Function.Surjective g.hom.left.hom) :
    Function.Surjective (pullbackAugmentation f g) :=
  A'.augmentation_surjective.comp (AlgHom.surjective_pullbackFst_of_surjective _ _ hg)

/-- For a ring `R` mapping to an object `B` of `C_Λ` compatibly with a surjection `R → k`, the
composite `R → B → B ⧸ 𝔪_B` is surjective. -/
private theorem surjective_mk_maximalIdeal_comp {B : ArtinLocalAlg Λ k} {R : Type*} [CommRing R]
    (φ : R →+* B.obj.left) {π : R → k} (hπ : Function.Surjective π)
    (h : ∀ x, B.augmentation (φ x) = π x) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal B.obj.left)).comp φ) := fun y ↦ by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, hx⟩ := hπ (B.augmentation b)
  refine ⟨x, Ideal.Quotient.eq.mpr ?_⟩
  rw [← augmentation_eq_zero_iff, map_sub, h, hx, sub_self]

/-- If `g` is surjective, the fibre product of `f` and `g` is an Artinian ring: it maps onto the
residue fields of the Artinian local rings `A'` and `A''`, so these are Artinian modules over it,
and it is a submodule of their product. Stacks, Lemma 90.3.8 (06GH). -/
theorem isArtinianRing_pullback (hg : Function.Surjective g.hom.left.hom) :
    IsArtinianRing (AlgHom.pullback f.hom.left.hom g.hom.left.hom) := by
  set P := AlgHom.pullback f.hom.left.hom g.hom.left.hom
  have hP := pullbackAugmentation_surjective (f := f) hg
  have hnil (B : ArtinLocalAlg Λ k) : IsNilpotent (maximalIdeal B.obj.left) := by
    rw [← ringJacobson_eq_maximalIdeal]
    exact IsArtinianRing.isNilpotent_jacobson _
  let : Algebra P A'.obj.left := (AlgHom.pullbackFst _ _).toRingHom.toAlgebra
  let : Algebra P A''.obj.left := (AlgHom.pullbackSnd _ _).toRingHom.toAlgebra
  have : IsArtinian P A'.obj.left :=
    isArtinian_of_isNilpotent_of_surjective_algebraMap_quotient (hnil A')
      (surjective_mk_maximalIdeal_comp _ hP fun _ ↦ rfl)
  have : IsArtinian P A''.obj.left :=
    isArtinian_of_isNilpotent_of_surjective_algebraMap_quotient (hnil A'')
      (surjective_mk_maximalIdeal_comp _ hP (augmentation_snd_pullback f g))
  let ι : P →ₗ[P] A'.obj.left × A''.obj.left :=
    { toFun := Subtype.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : IsArtinian P (A'.obj.left × A''.obj.left) := isArtinian_prod
  exact isArtinian_of_injective ι Subtype.val_injective

/-- The fibre product `A' ×_A A''` in `C_Λ` of morphisms `f : A' ⟶ A` and `g : A'' ⟶ A` with `g`
surjective. Stacks, Lemma 90.3.8 (06GH). -/
-- Exposed because the carrier of `pullback f g hg` is
-- `AlgHom.pullback f.hom.left.hom g.hom.left.hom` by definitional unfolding.
@[expose] def pullback (f : A' ⟶ A) (g : A'' ⟶ A) (hg : Function.Surjective g.hom.left.hom) :
    ArtinLocalAlg Λ k :=
  have := isArtinianRing_pullback (f := f) hg
  have := AlgHom.isLocalRing_pullback f.hom.left.hom g.hom.left.hom
  mk' (AlgHom.pullback f.hom.left.hom g.hom.left.hom) (pullbackAugmentation f g)
    (pullbackAugmentation_surjective hg)

variable (f g) (hg : Function.Surjective g.hom.left.hom)

/-- The augmentation of the fibre product is that of its first component. -/
@[simp]
theorem augmentation_pullback : (pullback f g hg).augmentation = pullbackAugmentation f g :=
  (rfl)

/-- The first projection `A' ×_A A'' ⟶ A'`. -/
def pullbackFst : pullback f g hg ⟶ A' :=
  homMk' (AlgHom.pullbackFst f.hom.left.hom g.hom.left.hom) (rfl)

/-- The second projection `A' ×_A A'' ⟶ A''`. -/
def pullbackSnd : pullback f g hg ⟶ A'' :=
  homMk' (AlgHom.pullbackSnd f.hom.left.hom g.hom.left.hom)
    (AlgHom.ext (augmentation_snd_pullback f g))

/-- The first projection takes a pair to its first component. -/
@[simp]
theorem pullbackFst_hom_left_hom_apply (x : (pullback f g hg).obj.left) :
    (pullbackFst f g hg).hom.left.hom x = x.1.1 :=
  (rfl)

/-- The second projection takes a pair to its second component. -/
@[simp]
theorem pullbackSnd_hom_left_hom_apply (x : (pullback f g hg).obj.left) :
    (pullbackSnd f g hg).hom.left.hom x = x.1.2 :=
  (rfl)

/-- The fibre product square commutes. -/
theorem pullback_condition : pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g := by
  ext x
  simp only [comp_hom_left_hom_apply, pullbackFst_hom_left_hom_apply,
    pullbackSnd_hom_left_hom_apply]
  exact AlgHom.congr_fun (AlgHom.pullback_comm_sq _ _) x

/-- The fibre product of `f` and `g` along the two projections is a pullback square in `C_Λ`.
Stacks, Lemma 90.3.8 (06GH). -/
theorem isPullback : IsPullback (pullbackFst f g hg) (pullbackSnd f g hg) f g := by
  refine .of_isLimit (PullbackCone.IsLimit.mk (pullback_condition f g hg) (fun s ↦ homMk'
    ((s.fst.hom.left.hom.prod s.snd.hom.left.hom).codRestrict _ fun t ↦ ?_) ?_) (fun s ↦ ?_)
    (fun s ↦ ?_) fun s m hfst hsnd ↦ ?_)
  · simpa using congrArg (fun φ ↦ φ.hom.left.hom t) s.condition
  · ext t
    exact augmentation_hom_apply s.fst t
  -- The lift lands in the carrier of `AlgHom.pullback`, whose instances agree with those of
  -- `(pullback f g hg).obj.left` only after unfolding `pullback` and `mk'`, so neither
  -- `homMk'_hom_left_hom` nor `CommAlgCat.hom_ofHom` rewrites here. Both factorisations hold by
  -- unfolding `homMk'`, `AlgHom.codRestrict` and `AlgHom.prod`.
  · ext t
    rfl
  · ext t
    rfl
  · ext t
    have h₁ := congrArg (fun φ ↦ φ.hom.left.hom t) hfst
    have h₂ := congrArg (fun φ ↦ φ.hom.left.hom t) hsnd
    simp only [comp_hom_left_hom_apply, pullbackFst_hom_left_hom_apply,
      pullbackSnd_hom_left_hom_apply] at h₁ h₂
    exact Subtype.ext (Prod.ext h₁ h₂)

end Pullback

end ArtinLocalAlg

end TauCeti.Deformation
