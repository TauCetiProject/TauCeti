/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.SemidirectProduct
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.GroupTheory.SemidirectProduct

/-!
# Complements of a vector group with linear action are conjugate

Let `G = Spec H` be an affine group over a commutative ring `R` and let `N ⊆ G` be the closed
subgroup cut out by a Hopf ideal `I`. Let `T ⊆ G` be a closed diagonalizable subgroup `D(X)`,
given by a surjective coordinate map `π : H →ₐc[R] R[X]` onto the group algebra of a commutative
group `X`, and suppose that `T` acts linearly on `N`: there is a comodule `V` over `R[X]` and
identifications `A ⊗[R] V ≃ N(A)` of groups, natural in the commutative `R`-algebra `A`, which
carry the points action of `D(A)` on `A ⊗[R] V` to conjugation by `T(A)`. Thus `N` is the vector
group of `V` and `T` acts on it through the representation `V`.

This file proves the vector-group step in the conjugacy of maximal tori in a connected solvable
group (Milne, the proof of Theorem 16.33(d)): if a closed subgroup `T'` meets `N` trivially and
has the same image as `T` modulo `N`, in the sense that `N(A) ⊔ T(A) = N(A) ⊔ T'(A)` for every
`A`, then `T'` is the conjugate of `T` by a rational point of `N`. In the language of Hopf ideals,
the Hopf ideal of `T'` is the conjugate of the kernel of `π` by an `R`-point of `N`. No
hypothesis that `T` meets `N` trivially is needed: it follows from the conclusion.

The proof reads `T'` as a family of splittings of the points semidirect products
`(A ⊗[R] V) ⋊ D(A)`, natural in `A`: the identifications assemble into homomorphisms from these
semidirect products onto `N(A) ⊔ T(A)`, and the preimage of `T'(A)` is a complement of the normal
factor. By `TauCeti.Comodule.exists_splitting_eq_conj_of_naturality` such a
family is the conjugate of the standard splitting by a single vector `y : V`, so `T'(A)` is the
conjugate of `T(A)` by the image of `1 ⊗ y` for every `A`; the ideal of `T'` is then recognized
by its points (`TauCeti.HopfIdeal.eq_conjugate_of_forall_mem_iff`).

No hypothesis on the base ring is needed beyond commutativity, and the Hopf ideal `I` need not
be assumed normal: conjugation by `T(A)` preserves `N(A)` by the linearity hypothesis, and this is
all the proof uses. Over a commutative `ℚ`-algebra `R`, an action of an affine group on a vector
group `V(M)` by group automorphisms acts on the points `M →ₗ[R] A` by `A`-linear automorphisms
(`TauCeti.AdditiveGroup.linearAutOfNaturality`). That result provides no comodule `V` and no
identifications `ν`; it is the starting point for constructing them. Over an
algebraically closed field of arbitrary characteristic, a diagonalizable subgroup such as a torus
meets a smooth unipotent subgroup trivially
(`TauCeti.FiniteTypeCommHopfAlgCat.sup_eq_augmentation_of_groupLikeSpanned_of_smoothUnipotent`),
which supplies the trivial-intersection hypothesis on `T'`.

## Main results

* `TauCeti.HopfIdeal.exists_eq_conjugate_kerOfSurjective_of_vectorGroup`: a closed subgroup
  complementary to a vector group with linear action of a diagonalizable subgroup `T`, with the
  same image as `T` modulo the vector group, is the conjugate of `T` by a rational point of the
  vector group.

## References

* J. S. Milne, *Algebraic Groups* (2017), the proof of Theorem 16.33(d), p. 336.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.6.
-/

public section

open scoped TensorProduct
open WithConv SemidirectProduct

namespace TauCeti.HopfIdeal

universe u w

variable {R : Type u} [CommRing R] {H : Type u} [CommRing H] [HopfAlgebra R H]
  {X : Type u} [CommGroup X]
  {V : Type w} [AddCommGroup V] [Module R V] [Comodule R (MonoidAlgebra R X) V]

section Complement

variable {I J' : HopfIdeal R H} {π : H →ₐc[R] MonoidAlgebra R X} {hπ : Function.Surjective π}
  {ν : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Multiplicative (A ⊗[R] V) ≃*
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A)}

/-- The semidirect product `(A ⊗[R] V) ⋊ D(A)` of the points of the vector group by the points of
the diagonalizable group. -/
private abbrev PointSemidirect (A : Type u) [CommRing A] [Algebra R A] :=
  Multiplicative (A ⊗[R] V) ⋊[(Comodule.pointsRepresentation (R := R)
    (H := MonoidAlgebra R X) (A := A) V).toMulAut] WithConv (MonoidAlgebra R X →ₐ[R] A)

variable (ν) in
/-- The identification of `A ⊗[R] V` with the points of `N`, as a homomorphism to the points of
the ambient group. -/
private noncomputable def vectorHom (A : Type u) [CommRing A] [Algebra R A] :
    Multiplicative (A ⊗[R] V) →* WithConv (H →ₐ[R] A) :=
  (Subgroup.subtype _).comp (ν A).toMonoidHom

private theorem vectorHom_apply (A : Type u) [CommRing A] [Algebra R A]
    (v : Multiplicative (A ⊗[R] V)) :
    vectorHom ν A v = (ν A v : WithConv (H →ₐ[R] A)) :=
  rfl

private theorem vectorHom_injective (A : Type u) [CommRing A] [Algebra R A] :
    Function.Injective (vectorHom ν A) :=
  Subtype.val_injective.comp (ν A).injective

private theorem vectorHom_mem (A : Type u) [CommRing A] [Algebra R A]
    (v : Multiplicative (A ⊗[R] V)) :
    vectorHom ν A v ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A) :=
  (ν A v).property

private theorem exists_vectorHom_eq (A : Type u) [CommRing A] [Algebra R A]
    {n : WithConv (H →ₐ[R] A)}
    (hn : n ∈
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A)) :
    ∃ v, vectorHom ν A v = n :=
  ⟨(ν A).symm ⟨n, hn⟩, by simp [vectorHom_apply]⟩

variable (hlin : ∀ (A : Type u) [CommRing A] [Algebra R A]
    (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) (v : A ⊗[R] V),
    (ν A (.ofAdd (Comodule.endOfPoint V t.ofConv v)) : WithConv (H →ₐ[R] A)) =
      BialgHom.mapDomain π t * ν A (.ofAdd v) * (BialgHom.mapDomain π t)⁻¹)

variable (π) in
/-- The homomorphism `(v, t) ↦ ν(v) π^*(t)` from the points semidirect product to the points of
the ambient group. -/
private noncomputable def semidirectHom (A : Type u) [CommRing A] [Algebra R A] :
    PointSemidirect (R := R) (X := X) (V := V) A →* WithConv (H →ₐ[R] A) :=
  SemidirectProduct.lift (vectorHom ν A) (BialgHom.mapDomain π) fun t ↦
    MonoidHom.ext fun v ↦ by
      simpa [Representation.toMulAut_apply, vectorHom_apply] using hlin A t v.toAdd

/-- The points cut out by a Hopf ideal of `H` over a commutative `R`-algebra `A`. -/
private noncomputable abbrev pts (K : HopfIdeal R H) (A : Type u) [CommRing A] [Algebra R A] :
    Subgroup (WithConv (H →ₐ[R] A)) :=
  CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) K (CommAlgCat.of R A)

include hlin in
/-- `N(A) ⊔ T(A)` normalizes `N(A)`: the diagonalizable subgroup acts on `N` through `V`. -/
private theorem sup_le_normalizer (A : Type u) [CommRing A] [Algebra R A] :
    pts I A ⊔ pts (kerOfSurjective π hπ) A ≤ Subgroup.normalizer (pts I A : Set _) := by
  refine sup_le Subgroup.le_normalizer (Subgroup.le_normalizer_iff.mpr fun x hx n hn ↦ ?_)
  obtain ⟨t, rfl⟩ := (quotientPointsSubgroup_kerOfSurjective_eq_range π hπ _).le hx
  obtain ⟨v, rfl⟩ := exists_vectorHom_eq (ν := ν) A hn
  have h := hlin A t (Multiplicative.toAdd v)
  rw [ofAdd_toAdd] at h
  rw [vectorHom_apply, ← h]
  exact (ν A _).property

include hlin in
/-- Every point of `N(A) ⊔ T(A)` is `ν(v) π^*(t)`, the image of an element of the points
semidirect product. -/
private theorem exists_semidirectHom_eq (A : Type u) [CommRing A] [Algebra R A]
    {x : WithConv (H →ₐ[R] A)} (hx : x ∈ pts I A ⊔ pts (kerOfSurjective π hπ) A) :
    ∃ k, semidirectHom π hlin A k = x := by
  have hle := sup_le_normalizer (hπ := hπ) hlin A
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_sup_right.trans hle)] at hx
  obtain ⟨n, hn, y, hy, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := exists_vectorHom_eq (ν := ν) A hn
  obtain ⟨t, rfl⟩ := (quotientPointsSubgroup_kerOfSurjective_eq_range π hπ _).le hy
  exact ⟨⟨v, t⟩, by simp only [semidirectHom, lift_apply]⟩

variable (J') in
/-- The preimage of `T'(A)` in the points semidirect product. -/
private noncomputable def complement (A : Type u) [CommRing A] [Algebra R A] :
    Subgroup (PointSemidirect (R := R) (X := X) (V := V) A) :=
  (pts J' A).comap (semidirectHom π hlin A)

variable (hT' : I ⊔ J' = augmentation R H)

include hT' in
/-- An element of the complement is determined by its component in `D(A)`, since `N ∩ T'` is
trivial. -/
private theorem eq_of_mem_complement (A : Type u) [CommRing A] [Algebra R A]
    {k k' : PointSemidirect (R := R) (X := X) (V := V) A} (hk : k ∈ complement J' hlin A)
    (hk' : k' ∈ complement J' hlin A) (h : k.right = k'.right) : k = k' := by
  have hright : (k * k'⁻¹).right = 1 := by simp [h]
  have hΦ : semidirectHom π hlin A (k * k'⁻¹) = vectorHom ν A (k * k'⁻¹).left := by
    rw [semidirectHom, lift_apply, hright, map_one, mul_one]
  have hmem : semidirectHom π hlin A (k * k'⁻¹) ∈ pts J' A :=
    Subgroup.mem_comap.mp (mul_mem hk (inv_mem hk'))
  rw [hΦ] at hmem
  have h1 : vectorHom ν A (k * k'⁻¹).left = 1 := by
    refine CommHopfAlgCat.eq_one_of_mem_quotientPointsSubgroup_augmentation
      (_root_.CommHopfAlgCat.of R H) (CommAlgCat.of R A) ?_
    rw [← hT', CommHopfAlgCat.quotientPointsSubgroup_sup]
    exact ⟨vectorHom_mem A _, hmem⟩
  have hl : (k * k'⁻¹).left = 1 := vectorHom_injective A (h1.trans (map_one _).symm)
  exact mul_inv_eq_one.mp (SemidirectProduct.ext (by simp [hl]) (by simp [hright]))

variable (himage : ∀ (A : Type u) [CommRing A] [Algebra R A],
  CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A) ⊔
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) (kerOfSurjective π hπ)
        (CommAlgCat.of R A) =
    CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A) ⊔
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) J' (CommAlgCat.of R A))

include himage in
/-- Every point of `D(A)` is the component of an element of the complement, since
`T(A) ≤ N(A) ⊔ T'(A)`. -/
private theorem exists_mem_complement_right_eq (A : Type u) [CommRing A] [Algebra R A]
    (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) :
    ∃ k ∈ complement J' hlin A, k.right = t := by
  have hle := sup_le_normalizer (hπ := hπ) hlin A
  have ht : BialgHom.mapDomain π t ∈ pts I A ⊔ pts J' A := by
    rw [← himage A]
    exact Subgroup.mem_sup_right
      ((quotientPointsSubgroup_kerOfSurjective_eq_range π hπ _).ge ⟨t, rfl⟩)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (le_sup_right.trans ((himage A).ge.trans hle))] at ht
  obtain ⟨n, hn, t', ht', hnt⟩ := ht
  obtain ⟨w, rfl⟩ := exists_vectorHom_eq (ν := ν) A hn
  refine ⟨inl w⁻¹ * inr t, ?_, by simp⟩
  simp only [complement, Subgroup.mem_comap, map_mul, map_inv, semidirectHom, lift_inl, lift_inr]
  rwa [← hnt, inv_mul_cancel_left]

include hT' himage in
private theorem bijective_rightHom_comp_subtype (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective (rightHom.comp (complement J' hlin A).subtype) :=
  ⟨fun k k' h ↦ Subtype.ext (eq_of_mem_complement hlin hT' A k.property k'.property
      (by simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, rightHom_eq_right] using h)),
    fun t ↦ by
      obtain ⟨k, hk, rfl⟩ := exists_mem_complement_right_eq hlin himage A t
      exact ⟨⟨k, hk⟩, by simp only [MonoidHom.comp_apply, Subgroup.coe_subtype,
        rightHom_eq_right]⟩⟩

/-- The splitting of the points semidirect product whose image is the complement: it sends `t`
to the unique element of the complement with component `t` in `D(A)`. -/
private noncomputable abbrev complementSplitting (A : Type u) [CommRing A] [Algebra R A] :
    (toGroupExtension (Comodule.pointsRepresentation (R := R) (H := MonoidAlgebra R X)
      (A := A) V).toMulAut).Splitting :=
  GroupExtension.Splitting.ofBijective (complement J' hlin A)
    (bijective_rightHom_comp_subtype hlin hT' himage A)

variable (hν : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  (φ : A →ₐ[R] B) (v : A ⊗[R] V),
  AlgHom.mapValue φ (ν A (.ofAdd v) : WithConv (H →ₐ[R] A)) =
    ν B (.ofAdd (LinearMap.rTensor V φ.toLinearMap v)))

include hν in
/-- The homomorphism from the points semidirect product is natural in the value algebra. -/
private theorem mapValue_semidirectHom {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B) (k : PointSemidirect (R := R) (X := X) (V := V) A) :
    AlgHom.mapValue φ (semidirectHom π hlin A k) =
      semidirectHom π hlin B (Comodule.pointSemidirectMap V φ k) := by
  have h := hν A B φ k.left.toAdd
  rw [ofAdd_toAdd] at h
  have hl : (Comodule.pointSemidirectMap V φ k).left =
      Multiplicative.ofAdd (LinearMap.rTensor V φ.toLinearMap k.left.toAdd) :=
    Multiplicative.toAdd.injective (Comodule.toAdd_pointSemidirectMap_left φ k)
  have hr := DFunLike.congr_fun (BialgHom.mapValue_mapDomain π φ) k.right
  simp only [MonoidHom.comp_apply] at hr
  simp only [semidirectHom, lift_apply, map_mul, vectorHom_apply, h, hl,
    Comodule.pointSemidirectMap_right, hr]

include hν in
/-- The splittings defined by the complements are natural in the value algebra. -/
private theorem pointSemidirectMap_complementSplitting (A B : Type u) [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) :
    Comodule.pointSemidirectMap V φ (complementSplitting hlin hT' himage A t) =
      complementSplitting hlin hT' himage B (AlgHom.mapValue φ t) := by
  refine eq_of_mem_complement hlin hT' B ?_ (GroupExtension.Splitting.ofBijective_mem _ _ _) ?_
  · rw [complement, Subgroup.mem_comap, ← mapValue_semidirectHom hlin hν]
    exact CommHopfAlgCat.mapValue_mem_quotientPointsSubgroup _ _ φ
      (GroupExtension.Splitting.ofBijective_mem (complement J' hlin A) _ t)
  · rw [Comodule.pointSemidirectMap_right, right_splitting, right_splitting]

end Complement

/-- **Complements of a vector group with linear action are conjugate.** Let `N` and `T'` be the
closed subgroups of `Spec H` cut out by the Hopf ideals `I` and `J'`, and let `T` be the closed
diagonalizable subgroup `D(X)` with surjective coordinate map `π : H →ₐc[R] R[X]`. Suppose that
`T` acts linearly on `N`: the groups `A ⊗[R] V` of a comodule `V` over `R[X]` are identified with
the points `N(A)` by isomorphisms `ν A`, natural in the commutative `R`-algebra `A` (`hν`), which
carry the points action of `D(A)` to conjugation by the points of `T` (`hlin`). If `N ∩ T'` is
trivial (`hT'`) and `T'` has the same image as `T` modulo `N`, that is
`N(A) ⊔ T(A) = N(A) ⊔ T'(A)` for every `A` (`himage`), then `T'` is the conjugate of `T` by a
rational point `y` of `N`.

This is the vector-group step in the conjugacy of maximal tori in a connected solvable group
(Milne, the proof of Theorem 16.33(d)). -/
theorem exists_eq_conjugate_kerOfSurjective_of_vectorGroup (I J' : HopfIdeal R H)
    (π : H →ₐc[R] MonoidAlgebra R X) (hπ : Function.Surjective π)
    (ν : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Multiplicative (A ⊗[R] V) ≃*
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A))
    (hν : ∀ (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
      (φ : A →ₐ[R] B) (v : A ⊗[R] V),
      AlgHom.mapValue φ (ν A (.ofAdd v) : WithConv (H →ₐ[R] A)) =
        ν B (.ofAdd (LinearMap.rTensor V φ.toLinearMap v)))
    (hlin : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) (v : A ⊗[R] V),
      (ν A (.ofAdd (Comodule.endOfPoint V t.ofConv v)) : WithConv (H →ₐ[R] A)) =
        BialgHom.mapDomain π t * ν A (.ofAdd v) * (BialgHom.mapDomain π t)⁻¹)
    (hT' : I ⊔ J' = augmentation R H)
    (himage : ∀ (A : Type u) [CommRing A] [Algebra R A],
      CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A) ⊔
          CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H)
            (kerOfSurjective π hπ) (CommAlgCat.of R A) =
        CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I (CommAlgCat.of R A) ⊔
          CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) J'
            (CommAlgCat.of R A)) :
    ∃ y ∈ CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of R H) I
        (CommAlgCat.of R R),
      J' = (kerOfSurjective π hπ).conjugate y := by
  obtain ⟨y, hy⟩ := Comodule.exists_splitting_eq_conj_of_naturality
    (fun A _ _ ↦ complementSplitting hlin hT' himage A)
    (fun A B _ _ _ _ φ t ↦ pointSemidirectMap_complementSplitting hlin hT' himage hν A B φ t)
  refine ⟨vectorHom ν R (.ofAdd ((1 : R) ⊗ₜ[R] y)), vectorHom_mem R _, ?_⟩
  -- The rational point `g = ν(1 ⊗ y)` of `N`, seen over `A`, is `ν(1 ⊗ y)` over `A`.
  have hg (A : Type u) [CommRing A] [Algebra R A] :
      AlgHom.mapValue (Algebra.ofId R A) (vectorHom ν R (.ofAdd ((1 : R) ⊗ₜ[R] y))) =
        vectorHom ν A (.ofAdd ((1 : A) ⊗ₜ[R] y)) := by
    rw [vectorHom_apply, vectorHom_apply, hν]
    simp
  -- The image of the complement splitting is the conjugate of `T(A)` by `g`.
  have hconj (A : Type u) [CommRing A] [Algebra R A] (t : WithConv (MonoidAlgebra R X →ₐ[R] A)) :
      semidirectHom π hlin A (complementSplitting hlin hT' himage A t) =
        AlgHom.mapValue (Algebra.ofId R A) (vectorHom ν R (.ofAdd ((1 : R) ⊗ₜ[R] y))) *
          BialgHom.mapDomain π t *
            (AlgHom.mapValue (Algebra.ofId R A) (vectorHom ν R (.ofAdd ((1 : R) ⊗ₜ[R] y))))⁻¹ := by
    rw [hy A t]
    simp only [map_mul, map_inv, semidirectHom, lift_inl, lift_inr]
    rw [hg]
  refine eq_conjugate_of_forall_mem_iff _ fun A x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨k, hk⟩ := exists_semidirectHom_eq (hπ := hπ) hlin A
      ((himage A).ge (Subgroup.mem_sup_right hx))
    have hkmem : k ∈ complement J' hlin A := by
      rwa [complement, Subgroup.mem_comap, hk]
    rw [← GroupExtension.Splitting.ofBijective_rightHom (S := toGroupExtension _)
      (bijective_rightHom_comp_subtype hlin hT' himage A) hkmem, hconj, mul_left_inj,
      mul_right_inj] at hk
    exact (quotientPointsSubgroup_kerOfSurjective_eq_range π hπ _).ge ⟨_, hk⟩
  · obtain ⟨t, rfl⟩ := (quotientPointsSubgroup_kerOfSurjective_eq_range π hπ _).le hx
    rw [← hconj]
    exact GroupExtension.Splitting.ofBijective_mem (complement J' hlin A) _ t

end TauCeti.HopfIdeal
