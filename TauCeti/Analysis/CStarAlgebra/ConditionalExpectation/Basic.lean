/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Prod
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# C⋆-conditional expectations

A conditional expectation onto a unital inclusion `ι : B →⋆ₐ[ℂ] A` is a unital positive
complex-linear map `E : A → B` satisfying the left and right `B`-module identities. The
inclusion is a parameter, so the same interface applies to concrete subalgebras and to abstract
factor embeddings. The identities imply that `E` retracts `ι`, hence that `ι` is injective.

The centered-square identity gives the Schwarz inequality and contractivity. We also establish
positivity of the `B`-valued quadratic forms of the Gram matrices `E (aᵢ* aⱼ)`, and of their
centered versions. These are the positivity identities used to construct expectation-GNS
modules. No faithfulness or trace is assumed.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 2.
* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, §3.8.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A]
  [CStarAlgebra B] [PartialOrder B]

/-- A unital positive `B`-bimodule retraction of a unital inclusion `ι : B →⋆ₐ[ℂ] A`.
The retraction property follows from unitality and either module identity. -/
structure CStarConditionalExpectation (ι : B →⋆ₐ[ℂ] A)
    [StarOrderedRing A] [StarOrderedRing B] extends A →ₚ[ℂ] B where
  /-- The expectation preserves the unit. -/
  map_one' : toPositiveLinearMap 1 = 1
  /-- Multiplication by an included element on the left can be pulled out. -/
  map_mul_left' (b : B) (a : A) : toPositiveLinearMap (ι b * a) = b * toPositiveLinearMap a
  /-- Multiplication by an included element on the right can be pulled out. -/
  map_mul_right' (a : A) (b : B) : toPositiveLinearMap (a * ι b) = toPositiveLinearMap a * b

namespace CStarConditionalExpectation

variable [StarOrderedRing A] [StarOrderedRing B] {ι : B →⋆ₐ[ℂ] A}

instance : FunLike (CStarConditionalExpectation ι) A B where
  coe E := E.toPositiveLinearMap
  coe_injective E F h := by
    cases E
    cases F
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (CStarConditionalExpectation ι) ℂ A B where
  map_add E := map_add E.toPositiveLinearMap
  map_smulₛₗ E := map_smulₛₗ E.toPositiveLinearMap

instance : OrderHomClass (CStarConditionalExpectation ι) A B where
  map_rel E := fun {_ _} h => E.toPositiveLinearMap.monotone h

instance : OneHomClass (CStarConditionalExpectation ι) A B where
  map_one E := E.map_one'

/-- Conditional expectations are determined by their values. -/
@[ext]
theorem ext {E F : CStarConditionalExpectation ι} (h : ∀ a, E a = F a) : E = F :=
  DFunLike.ext E F h

@[simp]
theorem toPositiveLinearMap_apply (E : CStarConditionalExpectation ι) (a : A) :
    E.toPositiveLinearMap a = E a := rfl

/-- Pulling an included left factor out of an expectation. -/
@[simp]
theorem map_mul_left (E : CStarConditionalExpectation ι) (b : B) (a : A) :
    E (ι b * a) = b * E a := E.map_mul_left' b a

/-- Pulling an included right factor out of an expectation. -/
@[simp]
theorem map_mul_right (E : CStarConditionalExpectation ι) (a : A) (b : B) :
    E (a * ι b) = E a * b := E.map_mul_right' a b

/-- A conditional expectation fixes its target algebra. -/
@[simp]
theorem map_inclusion (E : CStarConditionalExpectation ι) (b : B) : E (ι b) = b := by
  simpa using E.map_mul_left b 1

/-- Existence of a conditional expectation forces the specified inclusion to be injective. -/
theorem inclusion_injective (E : CStarConditionalExpectation ι) : Function.Injective ι :=
  Function.LeftInverse.injective E.map_inclusion

/-- Including the expectation back into the ambient algebra gives an idempotent projection. -/
theorem isIdempotentElem_inclusion_comp (E : CStarConditionalExpectation ι) :
    IsIdempotentElem (ι.toLinearMap.comp E.toLinearMap) := by
  ext a
  simp

/-- The range of the ambient projection is precisely the included algebra. -/
theorem range_inclusion_comp (E : CStarConditionalExpectation ι) :
    Set.range (ι ∘ E) = Set.range ι := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨E x, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨ι b, by simp⟩

/-- The fixed points of the ambient projection are precisely the included algebra. -/
theorem inclusion_map_eq_self_iff (E : CStarConditionalExpectation ι) (a : A) :
    ι (E a) = a ↔ a ∈ Set.range ι := by
  constructor
  · intro h
    exact ⟨E a, h⟩
  · rintro ⟨b, rfl⟩
    simp

/-- Subtracting the expectation produces a centered element. -/
@[simp]
theorem map_sub_inclusion (E : CStarConditionalExpectation ι) (a : A) :
    E (a - ι (E a)) = 0 := by simp

/-- The quadratic form of the expectation Gram matrix is the expectation of a square.
Arguments within each summand retain their displayed noncommutative order. -/
theorem sum_star_mul_map_mul (E : CStarConditionalExpectation ι) {κ : Type*}
    (s : Finset κ) (a : κ → A) (b : κ → B) :
    (∑ i ∈ s, ∑ j ∈ s, star (b i) * E (star (a i) * a j) * b j) =
      E (star (∑ i ∈ s, a i * ι (b i)) * ∑ j ∈ s, a j * ι (b j)) := by
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← mul_assoc, map_mul_right]
  rw [← map_star ι, mul_assoc (ι (star (b j))), E.map_mul_left]

/-- Centered pairings are the differences between second moments and products of means. -/
theorem map_star_sub_mul_sub (E : CStarConditionalExpectation ι) (a c : A) :
    E (star (a - ι (E a)) * (c - ι (E c))) =
      E (star a * c) - star (E a) * E c := by
  simp [star_sub, sub_mul, mul_sub, ← map_star ι, map_star E]

/-- The Schwarz inequality for a conditional expectation. -/
theorem star_map_mul_map_le (E : CStarConditionalExpectation ι) (a : A) :
    star (E a) * E a ≤ E (star a * a) := by
  have h := map_nonneg E (star_mul_self_nonneg (a - ι (E a)))
  rwa [E.map_star_sub_mul_sub, sub_nonneg] at h

/-- Conditional expectations are contractive, without faithfulness or traciality. -/
theorem norm_map_le (E : CStarConditionalExpectation ι) (a : A) : ‖E a‖ ≤ ‖a‖ := by
  have h := (CStarAlgebra.norm_le_norm_of_le_of_nonneg (E.star_map_mul_map_le a)
    (star_mul_self_nonneg (E a))).trans
    (E.toPositiveLinearMap.norm_apply_le_of_nonneg (star a * a) (star_mul_self_nonneg a))
  simp only [CStarRing.norm_star_mul_self, toPositiveLinearMap_apply, map_one] at h
  have h1 : ‖(1 : B)‖ ≤ 1 := by
    by_cases hB : Nontrivial B
    · have := hB
      simp
    · have := not_nontrivial_iff_subsingleton.mp hB
      simp [Subsingleton.elim (1 : B) 0]
  nlinarith [norm_nonneg (E a), norm_nonneg a, sq_nonneg ‖a‖]

/-- Conditional expectations are Lipschitz with constant one. -/
theorem lipschitz (E : CStarConditionalExpectation ι) : LipschitzWith 1 E := by
  simpa using AddMonoidHomClass.lipschitz_of_bound E 1 (by simpa using E.norm_map_le)

/-- A conditional expectation as a bounded complex-linear map. -/
def toContinuousLinearMap (E : CStarConditionalExpectation ι) : A →L[ℂ] B :=
  ⟨E.toLinearMap, E.lipschitz.continuous⟩

@[simp]
theorem toContinuousLinearMap_apply (E : CStarConditionalExpectation ι) (a : A) :
    E.toContinuousLinearMap a = E a := (rfl)

/-- The continuous-linear-map view has norm one when the target algebra is nontrivial. -/
theorem norm_eq_one [Nontrivial B] (E : CStarConditionalExpectation ι) :
    ‖E.toContinuousLinearMap‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using E.norm_map_le)
  · have h := ContinuousLinearMap.le_opNorm E.toContinuousLinearMap 1
    have : Nontrivial A := E.inclusion_injective.nontrivial
    simpa using h

/-- Positivity of all `B`-valued quadratic forms of the matrix `E (aᵢ* aⱼ)`. -/
theorem sum_star_mul_map_mul_nonneg (E : CStarConditionalExpectation ι) {κ : Type*}
    (s : Finset κ) (a : κ → A) (b : κ → B) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, star (b i) * E (star (a i) * a j) * b j := by
  rw [E.sum_star_mul_map_mul]
  exact map_nonneg E (star_mul_self_nonneg _)

/-- The centered Gram matrix also has positive `B`-valued quadratic forms. This is the
positivity of the covariance remaining after projection onto the target algebra. -/
theorem sum_star_mul_covariance_mul_nonneg (E : CStarConditionalExpectation ι) {κ : Type*}
    (s : Finset κ) (a : κ → A) (b : κ → B) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      star (b i) * (E (star (a i) * a j) - star (E (a i)) * E (a j)) * b j := by
  simpa only [E.map_star_sub_mul_sub] using
    E.sum_star_mul_map_mul_nonneg s (fun i => a i - ι (E (a i))) b

/-- Convex averaging of the coordinates is a conditional expectation onto the diagonal copy
of a C⋆-algebra in its square. The endpoints are allowed, so faithfulness is not built in. -/
def prodConvex (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    CStarConditionalExpectation ((StarAlgHom.id ℂ B).prod (StarAlgHom.id ℂ B)) := by
  let φ : B × B →ₚ[ℂ] B :=
    { toFun a := (t : ℂ) • a.1 + ((1 - t : ℝ) : ℂ) • a.2
      map_add' a c := by simp [smul_add, add_add_add_comm]
      map_smul' c a := by simp [smul_add, smul_comm c]
      monotone' := fun x y h => add_le_add
        (smul_le_smul_of_nonneg_left h.1 (Complex.zero_le_real.mpr ht₀))
        (smul_le_smul_of_nonneg_left h.2 (Complex.zero_le_real.mpr (sub_nonneg.mpr ht₁))) }
  have hφ (a : B × B) : φ a = (t : ℂ) • a.1 + ((1 - t : ℝ) : ℂ) • a.2 := rfl
  exact
    { toPositiveLinearMap := φ
      map_one' := by
        rw [hφ]
        simp only [Prod.fst_one, Prod.snd_one]
        rw [← add_smul]
        simp
      map_mul_left' b a := by simp [hφ, mul_add]
      map_mul_right' a b := by simp [hφ, add_mul] }

@[simp]
theorem prodConvex_apply (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (a : B × B) :
    prodConvex t ht₀ ht₁ a = (t : ℂ) • a.1 + ((1 - t : ℝ) : ℂ) • a.2 := (rfl)

end CStarConditionalExpectation

end TauCeti

namespace StarAlgHom

open TauCeti

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {ι : B →⋆ₐ[ℂ] A}

/-- A star-algebra retraction is a conditional expectation. In particular this constructs
identity expectations and expectations onto direct factors. -/
def toCStarConditionalExpectation (π : A →⋆ₐ[ℂ] B) {ι : B →⋆ₐ[ℂ] A}
    (hπ : Function.LeftInverse π ι) :
    CStarConditionalExpectation ι where
  toPositiveLinearMap := PositiveLinearMap.ofClass π
  map_one' := map_one π
  map_mul_left' b a := (map_mul π _ _).trans (congrArg (· * π a) (hπ b))
  map_mul_right' a b := (map_mul π _ _).trans (congrArg (π a * ·) (hπ b))

@[simp]
theorem toCStarConditionalExpectation_apply (π : A →⋆ₐ[ℂ] B) {ι : B →⋆ₐ[ℂ] A}
    (hπ : Function.LeftInverse π ι) (a : A) :
    π.toCStarConditionalExpectation hπ a = π a := (rfl)

end StarAlgHom
