/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Data.ZMod.QuotientRing
import TauCeti.RingTheory.Ideal.Quotient.Operations
import TauCeti.RingTheory.Unramified.Diagonal

/-!
# Étale neighbourhoods of a pair

An étale neighbourhood of a ring and ideal `(R, I)` is an étale `R`-algebra whose quotient by
`I` is canonically isomorphic to `R ⧸ I`. These algebras form the stages in the construction of
the henselization of the pair. This file defines their full subcategory and proves closure under
localization at an element invertible modulo the ideal, under tensor products, and under base
change along maps of pairs. It also shows that two `R`-algebra maps out of an étale
neighbourhood agree once `I` generates an ideal of the target inside its Jacobson radical.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02), the construction of the
  henselization of a pair.
-/

public section

open CategoryTheory TensorProduct

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical map on quotients induced by the structure map of an algebra. -/
def reducedMap (B : Type v) [CommRing B] [Algebra R B] :
    R ⧸ I →+* B ⧸ I.map (algebraMap R B) :=
  algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B))

@[simp]
theorem reducedMap_mk (B : Type v) [CommRing B] [Algebra R B] (r : R) :
    reducedMap I B (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R B)) (algebraMap R B r) :=
  (rfl)

/-- An étale neighbourhood induces an isomorphism on the closed subscheme defined by `I`. -/
def IsNeighbourhood : ObjectProperty (CommAlgCat.{v} R) :=
  fun B ↦ Algebra.Etale R B ∧ Function.Bijective (reducedMap I B)

/-- The category of étale neighbourhoods of the pair `(R, I)`. -/
abbrev Neighbourhood := (IsNeighbourhood.{u, v} I).FullSubcategory

/-- The two conditions defining an étale neighbourhood. -/
theorem isNeighbourhood_iff (B : CommAlgCat.{v} R) :
    IsNeighbourhood I B ↔ Algebra.Etale R B ∧ Function.Bijective (reducedMap I B) :=
  (Iff.rfl)

/-- An algebra isomorphic to the base ring is an étale neighbourhood of every ideal. -/
theorem isNeighbourhood_of_algEquiv {B : Type v} [CommRing B] [Algebra R B]
    (e : R ≃ₐ[R] B) : IsNeighbourhood I (CommAlgCat.of R B) := by
  refine ⟨Algebra.Etale.of_equiv e, ?_⟩
  have hmap : I.map (algebraMap R B) = I.map e.toRingHom := by
    congr 1
    exact RingHom.ext fun r ↦ by simp
  let q := Ideal.quotientEquiv I (I.map (algebraMap R B)) e.toRingEquiv hmap
  have hq : reducedMap I B = q.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    simp only [RingHom.comp_apply]
    calc
      reducedMap I B (Ideal.Quotient.mk I r) =
          Ideal.Quotient.mk (I.map (algebraMap R B)) (algebraMap R B r) := reducedMap_mk I B r
      _ = Ideal.Quotient.mk (I.map (algebraMap R B)) (e r) := by
        congr 1
        simp
      _ = q (Ideal.Quotient.mk I r) :=
        (Ideal.quotientEquiv_mk I (I.map (algebraMap R B)) e.toRingEquiv hmap r).symm
  rw [hq]
  exact q.bijective

/-- The identity algebra is an étale neighbourhood. -/
theorem isNeighbourhood_self : IsNeighbourhood I (CommAlgCat.of R R) :=
  isNeighbourhood_of_algEquiv I AlgEquiv.refl

/-- If the reduced map is injective, an element of `R` whose image lies in the extended ideal
already lies in `I`. -/
theorem mem_of_algebraMap_mem_map_of_reducedMap_injective {B : Type v} [CommRing B] [Algebra R B]
    (hB : Function.Injective (reducedMap I B)) {r : R}
    (hr : algebraMap R B r ∈ I.map (algebraMap R B)) : r ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply hB
  rwa [reducedMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]

/-- If the reduced map is surjective, every element of the algebra is congruent to the image of
an element of `R` modulo the extended ideal. -/
theorem exists_sub_algebraMap_mem_map_of_reducedMap_surjective {B : Type v} [CommRing B]
    [Algebra R B] (hB : Function.Surjective (reducedMap I B)) (b : B) :
    ∃ r : R, b - algebraMap R B r ∈ I.map (algebraMap R B) := by
  obtain ⟨t, ht⟩ := hB (Ideal.Quotient.mk _ b)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨r, Ideal.Quotient.eq.mp (by rw [← reducedMap_mk, ht])⟩

/-- Two maps out of an algebra whose reduced map is surjective (for instance, a neighbourhood)
agree after quotienting their target by the extended ideal. -/
theorem quotient_mk_eq_of_reducedMap_surjective {B : Type v} {C : Type*} [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (hB : Function.Surjective (reducedMap I B))
    (f g : B →ₐ[R] C) (b : B) :
    Ideal.Quotient.mk (I.map (algebraMap R C)) (f b) =
      Ideal.Quotient.mk (I.map (algebraMap R C)) (g b) := by
  exact DFunLike.congr_fun (I.algHom_ext_of_surjective_algebraMap_quotient B hB
    (S := C ⧸ I.map (algebraMap R C)) (by
      intro r hr
      rw [RingHom.mem_ker, ← Ideal.Quotient.mk_algebraMap]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr))
    ((Ideal.Quotient.mkₐ R _).comp f) ((Ideal.Quotient.mkₐ R _).comp g)) b

variable {I} in
/-- Two `R`-algebra maps out of an étale neighbourhood of `(R, I)` agree as soon as `I`
generates an ideal of the target inside its Jacobson radical. -/
theorem IsNeighbourhood.algHom_ext {B : CommAlgCat.{v} R} (hB : IsNeighbourhood I B)
    {S : Type*} [CommRing S] [Algebra R S] (hI : I.map (algebraMap R S) ≤ Ideal.jacobson ⊥)
    {f g : B →ₐ[R] S} : f = g := by
  obtain ⟨hEtale, hBij⟩ := (isNeighbourhood_iff I B).mp hB
  -- Both maps agree modulo `IS` because `B ⧸ IB ≅ R ⧸ I`, hence agree outright.
  refine Algebra.FormallyUnramified.ext_of_quotient_eq R B _ hI (AlgHom.ext fun b ↦ ?_)
  simpa only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using
    quotient_mk_eq_of_reducedMap_surjective I hBij.2 f g b

/-- Localization at elements which are units modulo `I` preserves the quotient by `I`. -/
theorem reducedMap_bijective_of_isLocalization (M : Submonoid R)
    (B : Type v) [CommRing B] [Algebra R B] [IsLocalization M B]
    (hM : M.map (Ideal.Quotient.mk I) ≤ IsUnit.submonoid (R ⧸ I)) :
    Function.Bijective (reducedMap I B) := by
  have hM' : Algebra.algebraMapSubmonoid (R ⧸ I) M ≤ IsUnit.submonoid (R ⧸ I) := by
    simpa only [Algebra.algebraMapSubmonoid, Ideal.Quotient.algebraMap_eq] using hM
  exact (IsLocalization.atUnits (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) M)
    (S := B ⧸ I.map (algebraMap R B)) hM').bijective

/-- Inverting an element that is a unit modulo the ideal gives an étale neighbourhood. -/
theorem isNeighbourhood_localization {x : R} (hx : IsUnit (Ideal.Quotient.mk I x))
    (B : Type v) [CommRing B] [Algebra R B] [IsLocalization.Away x B] :
    IsNeighbourhood I (CommAlgCat.of R B) := by
  refine ⟨Algebra.Etale.of_isLocalizationAway x, ?_⟩
  apply reducedMap_bijective_of_isLocalization I (Submonoid.powers x) B
  simpa only [Submonoid.map_powers, Submonoid.powers_le, IsUnit.mem_submonoid_iff] using hx

/-- Bijectivity on quotients composes in a tower of algebras. -/
theorem reducedMap_bijective_of_tower (B C : Type v) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
    (hB : Function.Bijective (reducedMap I B))
    (hC : Function.Bijective (reducedMap (I.map (algebraMap R B)) C)) :
    Function.Bijective (reducedMap I C) := by
  have he : (I.map (algebraMap R B)).map (algebraMap B C) = I.map (algebraMap R C) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let e := Ideal.quotientEquivAlgOfEq C he
  have hcomp : e.toRingEquiv.toRingHom.comp
      ((reducedMap (I.map (algebraMap R B)) C).comp (reducedMap I B)) = reducedMap I C := by
    ext r
    simp only [RingHom.comp_apply, reducedMap_mk, ← IsScalarTower.algebraMap_apply]
    exact Ideal.quotientEquivAlgOfEq_mk C he _
  rw [← hcomp]
  exact e.bijective.comp (hC.comp hB)

/-- An étale neighbourhood can be further localized at any element invertible on its quotient. -/
theorem isNeighbourhood_localization_of_isNeighbourhood (B : CommAlgCat.{v} R)
    (hB : IsNeighbourhood I B) {x : B}
    (hx : IsUnit (Ideal.Quotient.mk (I.map (algebraMap R B)) x)) :
    IsNeighbourhood I (CommAlgCat.of R (Localization.Away x)) := by
  obtain ⟨hEtale, hBij⟩ := (isNeighbourhood_iff I B).mp hB
  let := hEtale
  refine ⟨inferInstance, ?_⟩
  exact reducedMap_bijective_of_tower I B (Localization.Away x) hBij
    (isNeighbourhood_localization (I.map (algebraMap R B)) hx (Localization.Away x)).2

/-- Enlarging the ideal preserves bijectivity of the reduced map. -/
theorem reducedMap_bijective_of_le {J : Ideal R} (hIJ : I ≤ J) (B : Type v) [CommRing B]
    [Algebra R B] (hB : Function.Bijective (reducedMap I B)) :
    Function.Bijective (reducedMap J B) := by
  let e := RingEquiv.ofBijective (reducedMap I B) hB
  have he : (e : R ⧸ I →+* B ⧸ I.map (algebraMap R B)).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map (algebraMap R B))).comp (algebraMap R B) := by
    ext r
    exact reducedMap_mk I B r
  -- Modulo `IB`, the ideal `JB` is the image of `J ⧸ I` under `e`.
  have hJ : (J.map (Ideal.Quotient.mk I)).map (e : R ⧸ I →+* B ⧸ I.map (algebraMap R B)) =
      (J.map (algebraMap R B)).map (Ideal.Quotient.mk (I.map (algebraMap R B))) := by
    rw [Ideal.map_map, Ideal.map_map, he]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [reducedMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have hr : e (Ideal.Quotient.mk I r) ∈
        (J.map (Ideal.Quotient.mk I)).map (e : R ⧸ I →+* B ⧸ I.map (algebraMap R B)) := by
      rw [hJ, RingEquiv.ofBijective_apply, reducedMap_mk]
      exact Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply,
      Ideal.mem_quotient_iff_mem hIJ] at hr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
  · obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hB.2 (Ideal.Quotient.mk (I.map (algebraMap R B)) b)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [reducedMap_mk, Ideal.Quotient.eq] at hx
    exact ⟨Ideal.Quotient.mk J r, by
      rw [reducedMap_mk, Ideal.Quotient.eq]
      exact Ideal.map_mono hIJ hx⟩

/-- Base change along any algebra preserves bijectivity of the reduced map, for the extended
ideal. -/
theorem reducedMap_bijective_baseChange (S : Type*) [CommRing S] [Algebra R S]
    (B : Type v) [CommRing B] [Algebra R B] (hB : Function.Bijective (reducedMap I B)) :
    Function.Bijective (reducedMap (I.map (algebraMap R S)) (S ⊗[R] B)) := by
  let eB := AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom R (R ⧸ I) (B ⧸ I.map (algebraMap R B))) hB
  have hmap : (I.map (algebraMap R B)).map
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) =
      (I.map (algebraMap R S)).map (algebraMap S (S ⊗[R] B)) := by
    rw [← Ideal.map_coe, Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    exact Algebra.TensorProduct.includeRight.comp_algebraMap
  -- Identify `S ⧸ IS` with `S ⊗[R] (R ⧸ I) ≅ S ⊗[R] (B ⧸ IB) ≅ (S ⊗[R] B) ⧸ I(S ⊗[R] B)`.
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eB).trans
      ((Algebra.TensorProduct.tensorQuotientEquiv S B S (I.map (algebraMap R B))).trans
        (Ideal.quotientEquivAlgOfEq S hmap)))
  have he : reducedMap (I.map (algebraMap R S)) (S ⊗[R] B) = e.toRingEquiv.toRingHom := by
    ext s
    simp only [RingHom.comp_apply, reducedMap_mk, Ideal.Quotient.mk_algebraMap]
    exact (e.commutes s).symm
  rw [he]
  exact e.bijective

/-- The tensor product of two algebras inducing isomorphisms modulo `I` has the same property. -/
theorem reducedMap_bijective_tensor (B C : Type v) [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (hB : Function.Bijective (reducedMap I B))
    (hC : Function.Bijective (reducedMap I C)) :
    Function.Bijective (reducedMap I (B ⊗[R] C)) :=
  reducedMap_bijective_of_tower I B (B ⊗[R] C) hB (reducedMap_bijective_baseChange I B C hC)

/-- Tensor products provide common refinements of étale neighbourhoods. -/
theorem isNeighbourhood_tensor (B C : CommAlgCat.{v} R)
    (hB : IsNeighbourhood I B) (hC : IsNeighbourhood I C) :
    IsNeighbourhood I (CommAlgCat.of R (B ⊗[R] C)) := by
  obtain ⟨hBEtale, hBBij⟩ := (isNeighbourhood_iff I B).mp hB
  obtain ⟨hCEtale, hCBij⟩ := (isNeighbourhood_iff I C).mp hC
  let := hBEtale
  let := hCEtale
  exact ⟨Algebra.Etale.comp R B (B ⊗[R] C), reducedMap_bijective_tensor I B C hBBij hCBij⟩

/-- Base change along a map of pairs `(R, I) → (S, J)`, that is an `R`-algebra `S` with an ideal
`J` containing the image of `I`, carries étale neighbourhoods of `(R, I)` to étale neighbourhoods
of `(S, J)`. -/
theorem isNeighbourhood_baseChange {S : Type v} [CommRing S] [Algebra R S] {J : Ideal S}
    (hIJ : I.map (algebraMap R S) ≤ J) (B : CommAlgCat.{v} R) (hB : IsNeighbourhood I B) :
    IsNeighbourhood J (CommAlgCat.of S (S ⊗[R] B)) := by
  obtain ⟨hEtale, hBij⟩ := (isNeighbourhood_iff I B).mp hB
  let := hEtale
  exact ⟨inferInstance, reducedMap_bijective_of_le _ hIJ _
    (reducedMap_bijective_baseChange I S B hBij)⟩

/-- Any two étale neighbourhoods admit maps to a common étale neighbourhood. -/
theorem exists_common_target (B C : Neighbourhood.{u, v} I) :
    ∃ D : Neighbourhood.{u, v} I, Nonempty (B ⟶ D) ∧ Nonempty (C ⟶ D) := by
  refine ⟨⟨CommAlgCat.of R (B.obj ⊗[R] C.obj),
    isNeighbourhood_tensor I B.obj C.obj B.property C.property⟩, ?_, ?_⟩
  · exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeLeft)⟩
  · exact ⟨ObjectProperty.homMk (CommAlgCat.ofHom Algebra.TensorProduct.includeRight)⟩

-- Inverting two preserves the closed subscheme cut out by five.
example : IsNeighbourhood (Ideal.span {(5 : ℤ)})
    (CommAlgCat.of ℤ (Localization.Away (2 : ℤ))) := by
  apply isNeighbourhood_localization (x := 2)
  exact isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ 3, by
    rw [← map_mul]
    apply Ideal.Quotient.eq.mpr
    norm_num⟩

-- Inverting five destroys the nonzero quotient by five.
example : ¬ IsNeighbourhood (Ideal.span {(5 : ℤ)})
    (CommAlgCat.of ℤ (Localization.Away (5 : ℤ))) := by
  intro h
  let I : Ideal ℤ := Ideal.span {5}
  let B := Localization.Away (5 : ℤ)
  let J := I.map (algebraMap ℤ B)
  have h5 : Ideal.Quotient.mk J (algebraMap ℤ B 5) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
  have hu : IsUnit (Ideal.Quotient.mk J (algebraMap ℤ B 5)) :=
    (IsLocalization.Away.algebraMap_isUnit (5 : ℤ)).map (Ideal.Quotient.mk J)
  have hz : (0 : B ⧸ J) = 1 := by
    rw [h5] at hu
    exact (isUnit_zero_iff (M₀ := B ⧸ J)).mp hu
  have heq : (0 : ℤ ⧸ I) = 1 := h.2.1 (by simp only [map_zero, map_one]; exact hz)
  have := congrArg (Int.quotientSpanNatEquivZMod 5) heq
  exact (by decide : (0 : ZMod 5) ≠ 1) (by simpa only [map_zero, map_one] using this)

-- Two disjoint copies have two residue components, so the diagonal residue map is not onto.
example : ¬ IsNeighbourhood (Ideal.span {(5 : ℤ)}) (CommAlgCat.of ℤ (ℤ × ℤ)) := by
  intro h
  let I : Ideal ℤ := Ideal.span {5}
  let J := I.map (algebraMap ℤ (ℤ × ℤ))
  let f : ℤ × ℤ →+* ZMod 5 × ZMod 5 :=
    (Int.castRingHom (ZMod 5)).prodMap (Int.castRingHom (ZMod 5))
  have hf : J ≤ RingHom.ker f := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker]
    decide
  let q := Ideal.Quotient.lift J f hf
  obtain ⟨a, ha⟩ := h.2.2 (Ideal.Quotient.mk J (0, 1))
  obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective a
  have heq := congrArg q ha
  simp only [reducedMap_mk, q] at heq
  have h0 : (n : ZMod 5) = 0 := congrArg Prod.fst heq
  have h1 : (n : ZMod 5) = 1 := congrArg Prod.snd heq
  exact (by decide : (0 : ZMod 5) ≠ 1) (h0.symm.trans h1)

end TauCeti.Henselization
