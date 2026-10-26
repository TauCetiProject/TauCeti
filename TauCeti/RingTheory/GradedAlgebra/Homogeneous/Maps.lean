/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Graded coefficient inclusion and images of the irrelevant ideal

For a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` whose image contains every homogeneous element
of positive degree, in particular for a surjective one, the irrelevant ideal `ℬ₊` is contained
in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. This containment is the hypothesis under
which `f` induces `AlgebraicGeometry.Proj.map f : Proj ℬ ⟶ Proj 𝒜`. Nothing is required in
degree zero. An injective graded ring
homomorphism reflects homogeneity, so the inverse of a bijective one is again graded and the two
induce mutually inverse morphisms of `Proj`.

Degreewise rescaling by powers of a unit preserves the condition that a coordinate map
sends the irrelevant ideal to the unit ideal, allowing the rescaled coordinates to define
a morphism to `Proj` as well.

Coefficient inclusion also satisfies this containment, although it need not be surjective.
`TauCeti.GradedAlgebra.baseChangeMap` uses the same ring inclusion as Mathlib's
`GradedAlgHom.includeRight`, with the target grading over the extended coefficient ring.
This is the form needed for homogeneous localizations and projective coefficient projections.

More generally, a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over a coefficient extension `R → S`
induces the graded comparison `TauCeti.GradedAlgebra.baseChangeLift f : S ⊗[R] A → B`. When `f`
exhibits `B` as the base change of `A` (`IsBaseChange S f`), the comparison is bijective and its
inverse `TauCeti.GradedAlgebra.baseChangeLiftInv` is graded as well.

## Main results

* `HomogeneousIdeal.irrelevant_le_map_of_grade_subset_range`: `ℬ₊ ≤ 𝒜₊.map f` when the image of
  `f` contains every homogeneous element of positive degree.
* `HomogeneousIdeal.irrelevant_le_map_of_surjective`: `ℬ₊ ≤ 𝒜₊.map f` for a surjective `f`.
* `Graded.map_mem_iff_of_injective`: an injective graded ring homomorphism reflects homogeneity.
* `HomogeneousIdeal.irrelevant_le_map_baseChangeMap`: the same containment for extension
  of the coefficient ring.
* `HomogeneousIdeal.irrelevant_le_map_of_isBaseChange`: the same containment for a graded ring
  homomorphism exhibiting its target as a base change.
* `TauCeti.GradedAlgebra.bijective_baseChangeLift`: the graded comparison `S ⊗[R] A → B` of a
  graded ring homomorphism exhibiting `B` as the base change of `A` is bijective.
* `GradedRingHom.mem_of_map_mem`: an injective graded ring homomorphism reflects homogeneity, so
  the inverse of a bijective one is again graded.
-/

public section

namespace GradedRingHom

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- An injective graded ring homomorphism reflects homogeneity: if `f a` lies in `ℬ i`, then `a`
lies in `𝒜 i`. In particular, the inverse of a bijective graded ring homomorphism is graded. -/
theorem mem_of_map_mem (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Injective f) {a : A} {i : ι}
    (ha : f a ∈ ℬ i) : a ∈ 𝒜 i := by
  -- `f` carries the degree-`i` component of `a` to that of `f a`, which is `f a` itself
  have h : f (DirectSum.decompose 𝒜 a i) = f a := by
    rw [f.map_directSumDecompose, DirectSum.decompose_of_mem_same ℬ ha]
  exact hf h ▸ SetLike.coe_mem _

end GradedRingHom

namespace HomogeneousIdeal

variable {ι A B σ τ : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddCommMonoid ι]
  [PartialOrder ι] [CanonicallyOrderedAdd ι] {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- If the image of a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` contains every homogeneous element
of positive degree, then the irrelevant ideal `ℬ₊` is contained in the image `𝒜₊.map f` of the
irrelevant ideal `𝒜₊`. -/
theorem irrelevant_le_map_of_grade_subset_range (f : 𝒜 →+*ᵍ ℬ)
    (hf : ∀ i, 0 < i → (ℬ i : Set B) ⊆ Set.range f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  refine (irrelevant_le _).mpr fun i hi b hb ↦ ?_
  obtain ⟨a, rfl⟩ := hf i hi hb
  -- `f a` is homogeneous of degree `i`, so it is the image of the degree-`i` component of `a`
  rw [← DirectSum.decompose_of_mem_same ℬ (hb : f a ∈ ℬ i), ← f.map_directSumDecompose]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hi (SetLike.coe_mem _))

/-- For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the irrelevant ideal `ℬ₊` is
contained in the image `𝒜₊.map f` of the irrelevant ideal `𝒜₊`. -/
theorem irrelevant_le_map_of_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f :=
  irrelevant_le_map_of_grade_subset_range f fun _ _ ↦ hf.range_eq ▸ Set.subset_univ _

end HomogeneousIdeal

section Injective

variable {ι A B σ τ F : Type*} [Semiring A] [Semiring B] [SetLike σ A] [SetLike τ B]
  [AddSubmonoidClass σ A] [AddSubmonoidClass τ B] [DecidableEq ι] [AddMonoid ι]
  {𝒜 : ι → σ} {ℬ : ι → τ} [GradedRing 𝒜] [GradedRing ℬ]
  [FunLike F A B] [GradedFunLike F 𝒜 ℬ] [RingHomClass F A B]

/-- An injective graded ring homomorphism reflects homogeneity: `f x` is homogeneous of degree
`i` exactly when `x` is. In particular the inverse of a bijective graded ring homomorphism is
again graded. -/
theorem Graded.map_mem_iff_of_injective (f : F) (hf : Function.Injective f) {i : ι} {x : A} :
    f x ∈ ℬ i ↔ x ∈ 𝒜 i := by
  refine ⟨fun h ↦ ?_, Graded.map_mem f⟩
  -- `f` sends the degree-`i` component of `x` to that of `f x`, which is `f x` itself
  rw [← hf ((map_directSumDecompose 𝒜 ℬ f).trans (DirectSum.decompose_of_mem_same ℬ h))]
  exact SetLike.coe_mem _

end Injective

namespace TauCeti.HomogeneousIdeal

variable {A B σ : Type*} [Semiring A] [CommSemiring B] [SetLike σ A]
  [AddSubmonoidClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Unit rescaling in positive degrees preserves the condition that the irrelevant ideal maps
to the unit ideal. -/
theorem map_irrelevant_eq_top_of_unit_rescaling
    (f g : A →+* B) (c : Bˣ)
    (h : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, g a = c ^ n * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g = ⊤ := by
  have hle : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map g := by
    rw [Ideal.map_le_iff_le_comap, HomogeneousIdeal.toIdeal_irrelevant_le]
    intro n hn a ha
    exact (Ideal.unit_mul_mem_iff_mem _ (c.isUnit.pow n)).mp
      (h n hn a ha ▸ Ideal.mem_map_of_mem g (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha))
  rw [hf] at hle
  exact top_unique hle

end TauCeti.HomogeneousIdeal

namespace TauCeti.GradedAlgebra

open scoped TensorProduct

variable {ι R A : Type*}
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  (S : Type*) [CommSemiring S] [Algebra R S]
  (𝒜 : ι → Submodule R A)

/-- The coefficient inclusion as a graded ring map, using the grading over the extended
coefficient ring rather than its restriction of scalars. -/
-- The inclusion must compute in dependent types such as `Away ℬ (baseChangeMap S 𝒜 f)`.
@[expose]
def baseChangeMap : 𝒜 →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) where
  __ := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
  map_mem hx := Submodule.tmul_mem_baseChange_of_mem 1 hx

/-- The graded coefficient inclusion has the usual tensor-product inclusion as its ring map. -/
@[simp]
theorem baseChangeMap_toRingHom :
    (baseChangeMap S 𝒜).toRingHom =
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom := (rfl)

/-- Coefficient extension sends a homogeneous element to its pure tensor with one. -/
@[simp]
theorem baseChangeMap_apply (a : A) : baseChangeMap S 𝒜 a = 1 ⊗ₜ[R] a := (rfl)

section IsBaseChange

variable {S} {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜] {ℬ : ι → Submodule S B} [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)

/-- The graded comparison map `S ⊗[R] A → B`, `s ⊗ a ↦ s • f a`, of a graded ring homomorphism
`f` over the coefficient extension `R → S`. It is the graded ring homomorphism underlying
`GradedAlgHom.liftEquiv`, applied to `f` as a graded `R`-algebra homomorphism. -/
noncomputable def baseChangeLift : (fun n ↦ (𝒜 n).baseChange S) →+*ᵍ ℬ :=
  (GradedAlgHom.liftEquiv 𝒜 ℬ ⟨⟨f.toRingHom, hfR⟩, f.map_mem⟩).toGradedRingHom

/-- The graded comparison map sends a pure tensor `s ⊗ a` to `s • f a`
(`GradedAlgHom.liftEquiv_tmul`). -/
@[simp]
theorem baseChangeLift_tmul (s : S) (a : A) :
    baseChangeLift 𝒜 f hfR (s ⊗ₜ[R] a) = s • f a :=
  GradedAlgHom.liftEquiv_tmul _ s a

/-- The graded comparison map restricts to `f` along the coefficient inclusion. -/
@[simp]
theorem baseChangeLift_comp_baseChangeMap :
    (baseChangeLift 𝒜 f hfR).comp (baseChangeMap S 𝒜) = f :=
  GradedRingHom.ext fun a ↦ by simp

variable {𝒜 f hfR} in
/-- If `f` exhibits `B` as the base change of `A`, the graded comparison map `S ⊗[R] A → B` is
bijective. -/
theorem bijective_baseChangeLift
    (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) :
    Function.Bijective (baseChangeLift 𝒜 f hfR) := by
  have h : ⇑(baseChangeLift 𝒜 f hfR) = hf.equiv := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp [IsBaseChange.equiv_tmul]
    | add x y hx hy => simp [hx, hy]
  rw [h]
  exact hf.equiv.bijective

variable (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap)

/-- The inverse of the graded comparison map `S ⊗[R] A → B` of a graded ring homomorphism
exhibiting `B` as the base change of `A`, which is graded as well. -/
noncomputable def baseChangeLiftInv : ℬ →+*ᵍ (fun n ↦ (𝒜 n).baseChange S) where
  __ := (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).symm.toRingHom
  map_mem {n b} hb := (baseChangeLift 𝒜 f hfR).mem_of_map_mem
    (bijective_baseChangeLift hf).injective (by
      simpa [← RingEquiv.ofBijective_apply _ (bijective_baseChangeLift hf)] using hb)

/-- `baseChangeLiftInv` is a right inverse of the graded comparison map. -/
theorem baseChangeLift_baseChangeLiftInv :
    Function.RightInverse (baseChangeLiftInv 𝒜 f hfR hf) (baseChangeLift 𝒜 f hfR) :=
  (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).apply_symm_apply

/-- `baseChangeLiftInv` is a left inverse of the graded comparison map. -/
theorem baseChangeLiftInv_baseChangeLift :
    Function.LeftInverse (baseChangeLiftInv 𝒜 f hfR hf) (baseChangeLift 𝒜 f hfR) :=
  (RingEquiv.ofBijective _ (bijective_baseChangeLift hf)).symm_apply_apply

end IsBaseChange

end TauCeti.GradedAlgebra

namespace HomogeneousIdeal

open scoped TensorProduct
open TauCeti.GradedAlgebra

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (S : Type*) [CommSemiring S] [Algebra R S]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The irrelevant ideal after scalar extension lies in the ideal generated by the images
of the original positive-degree elements. In particular, coefficient extension defines a morphism
of `Proj`. -/
theorem irrelevant_le_map_baseChangeMap :
    irrelevant (fun n ↦ (𝒜 n).baseChange S) ≤ (irrelevant 𝒜).map (baseChangeMap S 𝒜) := by
  refine (irrelevant_le _).mpr fun n hn x hx ↦ ?_
  obtain ⟨y, hy⟩ := (𝒜 n).toBaseChange_surjective S ⟨x, hx⟩
  have hmem : ∀ y : S ⊗[R] 𝒜 n, ((𝒜 n).toBaseChange S y : S ⊗[R] A) ∈
      ((irrelevant 𝒜).map (baseChangeMap S 𝒜)).toIdeal := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simpa only [map_add, Submodule.coe_add] using add_mem hy hz
    | tmul s a =>
      rw [HomogeneousIdeal.toIdeal_map]
      have ha := Ideal.mem_map_of_mem (baseChangeMap S 𝒜)
        (mem_irrelevant_of_mem 𝒜 hn a.2)
      simpa only [Submodule.coe_toBaseChange_tmul, baseChangeMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] using
        Ideal.mul_mem_left _ (s ⊗ₜ[R] (1 : A)) ha
  -- `irrelevant_le` presents membership in the additive submonoid; the tensor induction
  -- uses membership in the ideal, with the same underlying carrier.
  change x ∈ ((irrelevant 𝒜).map (baseChangeMap S 𝒜)).toIdeal
  simpa only [hy] using hmem y

variable {S} {B : Type*} [CommSemiring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  {ℬ : ℕ → Submodule S B} [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ)
  (hfR : ∀ r : R, f (algebraMap R A r) = algebraMap R B r)

/-- If a graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ` over `R → S` exhibits `B` as the base change
`S ⊗[R] A`, then `ℬ₊ ≤ 𝒜₊.map f`, so that `f` induces a morphism `Proj ℬ ⟶ Proj 𝒜`. -/
theorem irrelevant_le_map_of_isBaseChange
    (hf : IsBaseChange S (AlgHom.mk f.toRingHom hfR).toLinearMap) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map f := by
  rw [← baseChangeLift_comp_baseChangeMap 𝒜 f hfR]
  exact irrelevant_le_map_comp (irrelevant_le_map_baseChangeMap S 𝒜)
    (irrelevant_le_map_of_surjective _ (bijective_baseChangeLift hf).surjective)

end HomogeneousIdeal
