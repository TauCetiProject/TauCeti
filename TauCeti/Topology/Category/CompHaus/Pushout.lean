/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Topology.ContinuousMap.Algebra
public import TauCeti.Topology.ContinuousMap.Compact
public import TauCeti.Topology.Instances.Shrink
public import TauCeti.Topology.TietzeExtension

/-!
# Continuous functions on a pushout of compact Hausdorff spaces

For maps `i : S ⟶ X` and `j : S ⟶ Y` of compact Hausdorff spaces, let `M = pushout i j` be their
pushout in `CompHaus`. Every point of `M` comes from `X` or from `Y`, and continuous maps
`f : X → T` and `g : Y → T` into a Hausdorff space `T` with `f ∘ i = g ∘ j` glue uniquely to a
continuous map on `M`. For a Hausdorff topological algebra `A`, this identifies the algebra
`C(M, A)` with the fibre product of `C(X, A)` and `C(Y, A)` over `C(S, A)`, the pairs of functions
that agree on `S`. For a normed ring `A` the identification preserves the supremum norm, and when
`i` is injective the restriction `C(X, A) → C(S, A)` is surjective for every `A` with the Tietze
extension property, such as `ℝ` and `ℂ`.

This is the function-algebra side of gluing compact spaces: the ring of continuous functions on a
space glued from `X` and `Y` along `S` is a fibre product of rings. When `i` is injective and `A`
has the Tietze extension property, one leg of this fibre product is surjective, so it is a Milnor
square, and by Milnor's patching theorem finitely generated projective modules over `C(M, A)`
correspond to modules over `C(X, A)` and `C(Y, A)` glued along `C(S, A)`.

## Main definitions

* `CompHaus.continuousMapPushoutDesc i j f g h`: the continuous map on `pushout i j` glued from
  `f : C(X, T)` and `g : C(Y, T)` agreeing on `S`, for a Hausdorff space `T`.
* `CompHaus.continuousMapPushoutAlgEquiv i j R A`: the `R`-algebra isomorphism of
  `C(pushout i j, A)` with the fibre product `AlgHom.pullback` of the restrictions
  `C(X, A) → C(S, A)` and `C(Y, A) → C(S, A)`.

## Main results

* `CompHaus.pushout_jointly_surjective`: every point of `pushout i j` lies in the image of `X` or of
  `Y`.
* `CompHaus.continuousMap_pushout_ext`: continuous maps on `pushout i j` are determined by their
  restrictions to `X` and `Y`.
* `CompHaus.norm_continuousMap_pushout_eq_max`: for a seminormed additive group `E`, the supremum
  norm of `f : C(pushout i j, E)` is the maximum of the norms of its restrictions to `X` and `Y`.
  `CompHaus.norm_coe_continuousMapPushoutAlgEquiv_apply` restates this for the algebra isomorphism.
* `CompHaus.surjective_comp_of_injective`: restriction along an injective map of compact Hausdorff
  spaces is surjective on continuous maps into a Tietze extension space;
  `CompHaus.surjective_compRightAlgHom_of_injective` is its algebra form. Both specialise the
  closed-embedding statements `ContinuousMap.surjective_comp_of_isClosedEmbedding` and
  `ContinuousMap.surjective_compRightAlgHom_of_isClosedEmbedding`.

## Implementation notes

The pushout in `CompHaus` is the Hausdorff quotient of the topological pushout, so the gluing of
maps is not read off from the topological pushout. It is obtained from the universal property in
`CompHaus`, applied to a copy of the compact image of the two maps in the universe of `X` and `Y`;
the target `T` may live in any universe.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society (2013), Chapter I, Clutching Construction 4.7
  and Exercise 4.9.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72, Princeton
  University Press (1971), §2.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace CompHaus

universe u

variable {X Y S : CompHaus.{u}} (i : S ⟶ X) (j : S ⟶ Y)

/-- Every point of a pushout of compact Hausdorff spaces comes from one of the two spaces. -/
theorem pushout_jointly_surjective (m : (pushout i j : CompHaus.{u})) :
    (∃ x, pushout.inl i j x = m) ∨ ∃ y, pushout.inr i j y = m := by
  let K := Set.range (ConcreteCategory.hom (pushout.inl i j)) ∪
    Set.range (ConcreteCategory.hom (pushout.inr i j))
  have : CompactSpace K := ContinuousMap.compactSpace_range_union
    (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inl i j))
    (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inr i j))
  let a : X ⟶ CompHaus.of K :=
    CompHausLike.ofHom _ ⟨fun x ↦ ⟨pushout.inl i j x, .inl ⟨x, rfl⟩⟩, by fun_prop⟩
  let b : Y ⟶ CompHaus.of K :=
    CompHausLike.ofHom _ ⟨fun y ↦ ⟨pushout.inr i j y, .inr ⟨y, rfl⟩⟩, by fun_prop⟩
  have hab : i ≫ a = j ≫ b := by
    ext s
    exact congr($(pushout.condition (f := i) (g := j)) s)
  let incl : CompHaus.of K ⟶ pushout i j :=
    CompHausLike.ofHom _ ⟨Subtype.val, continuous_subtypeVal⟩
  have hid : pushout.desc a b hab ≫ incl = 𝟙 _ := by
    apply pushout.hom_ext <;> ext <;> simp [a, b, incl]
  -- The pushout factors through the union `K` of the two images, so every point lies in `K`.
  have hm : incl (pushout.desc a b hab m) = m := congr($hid m)
  rw [← hm]
  exact (pushout.desc a b hab m).property

variable {i j} in
/-- Two continuous maps on a pushout of compact Hausdorff spaces that agree on both legs are
equal. -/
theorem continuousMap_pushout_ext {T : Type*} [TopologicalSpace T]
    {f g : C((pushout i j : CompHaus.{u}), T)}
    (hl : ∀ x, f (pushout.inl i j x) = g (pushout.inl i j x))
    (hr : ∀ y, f (pushout.inr i j y) = g (pushout.inr i j y)) : f = g := by
  ext m
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := pushout_jointly_surjective i j m
  exacts [hl x, hr y]

section Desc

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [Small.{u} K]

/-- The two maps into the copy `Shrink K` of `K` in the universe of `X` and `Y` agree on `S`. -/
private theorem shrink_comp_eq (a : C(X, K)) (b : C(Y, K)) (h : ∀ s, a (i s) = b (j s)) :
    i ≫ CompHausLike.ofHom (Y := Shrink.{u} K) _ (((Shrink.homeomorph K) : C(K, _)).comp a) =
      j ≫ CompHausLike.ofHom (Y := Shrink.{u} K) _ (((Shrink.homeomorph K) : C(K, _)).comp b) :=
  ConcreteCategory.hom_ext _ _ fun s ↦ by simp [h s]

/-- Gluing into a compact Hausdorff space `K` of an arbitrary universe: transport to the copy
`Shrink K` of `K` in the universe of `X` and `Y`, where the universal property of the pushout
applies. -/
private def descCompact (a : C(X, K)) (b : C(Y, K)) (h : ∀ s, a (i s) = b (j s)) :
    C((pushout i j : CompHaus.{u}), K) :=
  ((Shrink.homeomorph K).symm : C(Shrink.{u} K, K)).comp
    (ConcreteCategory.hom (pushout.desc _ _ (shrink_comp_eq i j a b h)))

private theorem descCompact_inl (a : C(X, K)) (b : C(Y, K)) (h : ∀ s, a (i s) = b (j s))
    (x : X) : descCompact i j a b h (pushout.inl i j x) = a x := by
  simp [descCompact]

private theorem descCompact_inr (a : C(X, K)) (b : C(Y, K)) (h : ∀ s, a (i s) = b (j s))
    (y : Y) : descCompact i j a b h (pushout.inr i j y) = b y := by
  simp [descCompact]

end Desc

section Glue

variable {T : Type*} [TopologicalSpace T] [T2Space T]

/-- Continuous maps `f : X → T` and `g : Y → T` into a Hausdorff space that agree on `S` glue to a
continuous map on the pushout `pushout i j`, restricting to `f` on `X` and to `g` on `Y`
(`CompHaus.continuousMapPushoutDesc_inl`, `CompHaus.continuousMapPushoutDesc_inr`). -/
def continuousMapPushoutDesc (f : C(X, T)) (g : C(Y, T)) (h : ∀ s, f (i s) = g (j s)) :
    C((pushout i j : CompHaus.{u}), T) :=
  -- Both maps take values in the compact set `range f ∪ range g`.
  haveI := ContinuousMap.compactSpace_range_union f g
  (ContinuousMap.mk ((↑) : ↥(Set.range f ∪ Set.range g) → T)).comp <|
    descCompact i j ⟨fun x ↦ ⟨f x, .inl ⟨x, rfl⟩⟩, f.continuous.subtype_mk _⟩
      ⟨fun y ↦ ⟨g y, .inr ⟨y, rfl⟩⟩, g.continuous.subtype_mk _⟩ fun s ↦ Subtype.ext (h s)

/-- The glued map restricts to `f` on `X`. -/
@[simp]
theorem continuousMapPushoutDesc_inl (f : C(X, T)) (g : C(Y, T)) (h : ∀ s, f (i s) = g (j s))
    (x : X) : continuousMapPushoutDesc i j f g h (pushout.inl i j x) = f x := by
  have := ContinuousMap.compactSpace_range_union f g
  exact congrArg Subtype.val (descCompact_inl i j _ _ _ x)

/-- The glued map restricts to `g` on `Y`. -/
@[simp]
theorem continuousMapPushoutDesc_inr (f : C(X, T)) (g : C(Y, T)) (h : ∀ s, f (i s) = g (j s))
    (y : Y) : continuousMapPushoutDesc i j f g h (pushout.inr i j y) = g y := by
  have := ContinuousMap.compactSpace_range_union f g
  exact congrArg Subtype.val (descCompact_inr i j _ _ _ y)

end Glue

/-- For a seminormed additive group `E`, the supremum norm of a function on the pushout is the
maximum of the supremum norms of its restrictions to `X` and `Y`. -/
theorem norm_continuousMap_pushout_eq_max {E : Type*} [SeminormedAddCommGroup E]
    (f : C((pushout i j : CompHaus.{u}), E)) :
    ‖f‖ = max ‖f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inl i j))‖
      ‖f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inr i j))‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (by positivity)).2 fun m ↦ ?_) (max_le ?_ ?_)
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := pushout_jointly_surjective i j m
    · exact ((f.comp _).norm_coe_le_norm x).trans (le_max_left _ _)
    · exact ((f.comp _).norm_coe_le_norm y).trans (le_max_right _ _)
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x ↦ f.norm_coe_le_norm _
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun y ↦ f.norm_coe_le_norm _

/-- Restriction along an injective map of compact Hausdorff spaces is surjective on continuous
maps into a space with the Tietze extension property, such as `ℝ` or `ℂ`: such a map is a closed
embedding (`ContinuousMap.surjective_comp_of_isClosedEmbedding`). -/
theorem surjective_comp_of_injective {T : Type*} [TopologicalSpace T] [TietzeExtension.{u} T]
    (hi : Function.Injective i) :
    Function.Surjective fun f : C(X, T) ↦ f.comp (ConcreteCategory.hom (C := CompHaus.{u}) i) :=
  ContinuousMap.surjective_comp_of_isClosedEmbedding
    ((ConcreteCategory.hom i).continuous.isClosedEmbedding hi)

section Algebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [IsTopologicalSemiring A]

/-- **Functions on a pushout of compact Hausdorff spaces.** For a Hausdorff topological
`R`-algebra `A`, restriction to the two legs identifies `C(pushout i j, A)` with the fibre product
of `C(X, A)` and `C(Y, A)` over `C(S, A)`: the subalgebra of pairs `(f, g)` with `f ∘ i = g ∘ j`
(`ContinuousMap.mem_pullback_compRightAlgHom_iff`). It sends a function to its two restrictions
(`CompHaus.coe_continuousMapPushoutAlgEquiv_apply`), and the inverse glues such a pair
(`CompHaus.continuousMapPushoutAlgEquiv_symm_apply_inl`,
`CompHaus.continuousMapPushoutAlgEquiv_symm_apply_inr`). -/
def continuousMapPushoutAlgEquiv [T2Space A] :
    C((pushout i j : CompHaus.{u}), A) ≃ₐ[R]
      AlgHom.pullback
        (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) i))
        (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) j)) where
  toFun f := ⟨(f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inl i j)),
    f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inr i j))),
    ContinuousMap.mem_pullback_compRightAlgHom_iff.2 fun s ↦ by
      simpa using congrArg f congr($(pushout.condition (f := i) (g := j)) s)⟩
  invFun p := continuousMapPushoutDesc i j p.val.1 p.val.2
    (ContinuousMap.mem_pullback_compRightAlgHom_iff.1 p.property)
  left_inv f := continuousMap_pushout_ext (by simp) (by simp)
  right_inv p := Subtype.ext (Prod.ext (by ext; simp) (by ext; simp))
  map_mul' f g := Subtype.ext (Prod.ext (f.mul_comp g _) (f.mul_comp g _))
  map_add' f g := Subtype.ext (Prod.ext (f.add_comp g _) (f.add_comp g _))
  commutes' r := Subtype.ext (Prod.ext (by ext; simp) (by ext; simp))

/-- `CompHaus.continuousMapPushoutAlgEquiv` sends a function to its restrictions to `X` and `Y`. -/
@[simp]
theorem coe_continuousMapPushoutAlgEquiv_apply [T2Space A]
    (f : C((pushout i j : CompHaus.{u}), A)) :
    (continuousMapPushoutAlgEquiv i j R A f : C(X, A) × C(Y, A)) =
      (f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inl i j)),
        f.comp (ConcreteCategory.hom (C := CompHaus.{u}) (pushout.inr i j))) :=
  (rfl)

/-- The function glued from a pair in the fibre product restricts to its first member on `X`. -/
@[simp]
theorem continuousMapPushoutAlgEquiv_symm_apply_inl [T2Space A]
    (p : AlgHom.pullback
      (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) i))
      (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) j))) (x : X) :
    (continuousMapPushoutAlgEquiv i j R A).symm p (pushout.inl i j x) =
      (p : C(X, A) × C(Y, A)).1 x :=
  continuousMapPushoutDesc_inl i j _ _
    (ContinuousMap.mem_pullback_compRightAlgHom_iff.1 p.property) x

/-- The function glued from a pair in the fibre product restricts to its second member on `Y`. -/
@[simp]
theorem continuousMapPushoutAlgEquiv_symm_apply_inr [T2Space A]
    (p : AlgHom.pullback
      (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) i))
      (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) j))) (y : Y) :
    (continuousMapPushoutAlgEquiv i j R A).symm p (pushout.inr i j y) =
      (p : C(X, A) × C(Y, A)).2 y :=
  continuousMapPushoutDesc_inr i j _ _
    (ContinuousMap.mem_pullback_compRightAlgHom_iff.1 p.property) y

/-- Restriction along an injective map of compact Hausdorff spaces is a surjective algebra map on
functions with values in a space with the Tietze extension property, such as `ℝ` or `ℂ`
(`ContinuousMap.surjective_compRightAlgHom_of_isClosedEmbedding`). -/
theorem surjective_compRightAlgHom_of_injective [TietzeExtension.{u} A]
    (hi : Function.Injective i) :
    Function.Surjective
      (ContinuousMap.compRightAlgHom R A (ConcreteCategory.hom (C := CompHaus.{u}) i)) :=
  ContinuousMap.surjective_compRightAlgHom_of_isClosedEmbedding R
    ((ConcreteCategory.hom i).continuous.isClosedEmbedding hi)

end Algebra

/-- For a normed ring `A`, the identification of `C(pushout i j, A)` with the fibre product is
isometric for the supremum norm of the product `C(X, A) × C(Y, A)`
(`CompHaus.norm_continuousMap_pushout_eq_max`). -/
theorem norm_coe_continuousMapPushoutAlgEquiv_apply (R : Type*) {A : Type*} [CommSemiring R]
    [NormedRing A] [Algebra R A] (f : C((pushout i j : CompHaus.{u}), A)) :
    ‖(continuousMapPushoutAlgEquiv i j R A f : C(X, A) × C(Y, A))‖ = ‖f‖ := by
  rw [coe_continuousMapPushoutAlgEquiv_apply, Prod.norm_mk, norm_continuousMap_pushout_eq_max]

end CompHaus
