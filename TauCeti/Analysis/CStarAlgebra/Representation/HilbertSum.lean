/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.HilbertSum

/-!
# Hilbert direct sums of C⋆-algebra representations

A family of representations `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)` of a C⋆-algebra `A` is uniformly
bounded at each element `a` by `‖a‖`. Assembling the operators `π i a` coordinatewise on the
Hilbert direct sum `lp H 2` via `lp.mapCLM` and `lp.star_mapCLM` produces the direct-sum
representation `NonUnitalStarAlgHom.hilbertSum π : A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)`, following the
pattern of `ContRepresentation.hilbertSum` for unitary group representations.

This construction turns a point-separating family of representations (such as the GNS
representations of all states) into a single faithful nondegenerate representation.

## Main declarations

* `NonUnitalStarAlgHom.hilbertSum`: the Hilbert direct sum `⊕ i, π i` of a family of possibly
  nonunital representations on `lp H 2`, with coordinate, `lp.single`, norm, kernel, and
  injectivity lemmas.
* `NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`: `⊕ i, π i` is nondegenerate if and only if
  every summand `π i` is nondegenerate.
* `StarAlgHom.hilbertSum`: the corresponding unital direct-sum representation when `B` is a unital
  C⋆-algebra.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §II.1, §VIII.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, §3.4.
-/

public section

noncomputable section

open scoped ENNReal lp

namespace NonUnitalStarAlgHom

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The **Hilbert direct sum** `⊕ i, π i` of a family of representations of a C⋆-algebra `A`,
acting coordinatewise on `lp H 2`. -/
def hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) : A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i => π i a) (norm_nonneg a) fun i => norm_apply_le (π i) a
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
  map_star' a := by
    have hstar : ∀ i, ‖star (π i a)‖ ≤ ‖a‖ := fun i =>
      (norm_star _).trans_le (norm_apply_le (π i) a)
    rw [lp.star_mapCLM _ (norm_nonneg a) _ (norm_nonneg a) hstar]
    ext x i
    simp [map_star]

/-- The direct-sum representation evaluates at `a` to `lp.mapCLM 2 (fun i => π i a)`. -/
theorem hilbertSum_apply_eq_mapCLM (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    hilbertSum π a =
      lp.mapCLM 2 (fun i => π i a) (norm_nonneg a) (fun i => norm_apply_le (π i) a) :=
  (rfl)

/-- The direct-sum representation acts coordinatewise on `lp H 2`. -/
@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) (x : lp H 2)
    (i : ι) :
    hilbertSum π a x i = π i a (x i) :=
  (rfl)

/-- Coordinate evaluation intertwines `hilbertSum π a` with `π i a`. -/
@[simp]
theorem evalCLM_comp_hilbertSum_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π a = π i a ∘L lp.evalCLM ℂ H 2 i := by
  rw [hilbertSum_apply_eq_mapCLM]
  exact lp.evalCLM_comp_mapCLM _ _ _ i

/-- On a coordinate vector `lp.single 2 i v`, the direct-sum representation acts in coordinate `i`
by `π i a`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A)
    (i : ι) (v : H i) :
    hilbertSum π a (lp.single 2 i v) = lp.single 2 i (π i a v) := by
  rw [hilbertSum_apply_eq_mapCLM]
  exact lp.mapCLM_single _ _ _ i v

/-- The operator norm of `hilbertSum π a` is the supremum of the summand norms `‖π i a‖`. -/
theorem norm_hilbertSum_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    ‖hilbertSum π a‖ = ⨆ i, ‖π i a‖ := by
  rw [hilbertSum_apply_eq_mapCLM]
  exact lp.norm_mapCLM _ _ _

/-- An element lies in the kernel of `hilbertSum π` if and only if it lies in the kernel of every
summand `π i`. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    hilbertSum π a = 0 ↔ ∀ i, π i a = 0 := by
  classical
  refine ⟨fun h i => ContinuousLinearMap.ext fun v => ?_, fun h => ?_⟩
  · simpa using congr_arg (fun x : lp H 2 => x i) (congr($h (lp.single 2 i v)))
  · ext x i
    simp [h i]

/-- The direct sum `hilbertSum π` is injective if and only if the kernels of the summands `π i`
have trivial intersection. -/
theorem hilbertSum_injective_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ ⦃a⦄, (∀ i, π i a = 0) → a = 0 := by
  simp [injective_iff_map_eq_zero, hilbertSum_apply_eq_zero_iff]

/-- If one summand `π i` is injective, then `hilbertSum π` is injective. -/
theorem hilbertSum_injective_of_injective (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (i : ι)
    (hi : Function.Injective (π i)) : Function.Injective (hilbertSum π) :=
  (hilbertSum_injective_iff π).2 fun _ h => hi (by rw [h i, map_zero])

/-- **Nondegeneracy of Hilbert direct sums.** The direct-sum representation `hilbertSum π` is
nondegenerate if and only if every summand `π i` is nondegenerate. -/
@[simp]
theorem isNondegenerate_hilbertSum_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).IsNondegenerate ↔ ∀ i, (π i).IsNondegenerate := by
  classical
  simp only [isNondegenerate_iff_forall_apply_eq_zero]
  refine ⟨fun h i v hv => ?_, fun h ξ hξ => ?_⟩
  · have hsingle : lp.single 2 i v = 0 := h (lp.single 2 i v) fun a => by simp [hv a]
    simpa using congr_arg (fun x : lp H 2 => x i) hsingle
  · ext i
    exact h i (ξ i) fun a => by simpa using congr_arg (fun x : lp H 2 => x i) (hξ a)

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {B ι : Type*} {H : ι → Type*} [CStarAlgebra B]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The **Hilbert direct sum** `⊕ i, π i` of a family of unital representations of a unital
C⋆-algebra `B`, acting coordinatewise on `lp H 2`. -/
def hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) : B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) :=
  ((NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff
    (fun i => (π i).toNonUnitalStarAlgHom)).2 fun i =>
    NonUnitalStarAlgHom.isNondegenerate_of_map_one (map_one (π i))).toStarAlgHom

/-- Forgetting the unit of `StarAlgHom.hilbertSum π` gives `NonUnitalStarAlgHom.hilbertSum`. -/
@[simp]
theorem toNonUnitalStarAlgHom_hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.hilbertSum fun i => (π i).toNonUnitalStarAlgHom := by
  simp [hilbertSum]

/-- `StarAlgHom.hilbertSum π` evaluates at `b` to `lp.mapCLM 2 (fun i => π i b)`. -/
theorem hilbertSum_apply_eq_mapCLM (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    hilbertSum π b =
      lp.mapCLM 2 (fun i => π i b) (norm_nonneg b)
        (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) b) := by
  simpa [hilbertSum] using
    NonUnitalStarAlgHom.hilbertSum_apply_eq_mapCLM (fun i => (π i).toNonUnitalStarAlgHom) b

/-- The unital direct-sum representation acts coordinatewise on `lp H 2`. -/
@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) (x : lp H 2) (i : ι) :
    hilbertSum π b x i = π i b (x i) := by
  simp [hilbertSum]

/-- Coordinate evaluation intertwines `StarAlgHom.hilbertSum π b` with `π i b`. -/
@[simp]
theorem evalCLM_comp_hilbertSum_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π b = π i b ∘L lp.evalCLM ℂ H 2 i := by
  simp [hilbertSum]

/-- On a coordinate vector `lp.single 2 i v`, `StarAlgHom.hilbertSum π b` acts in coordinate `i`
by `π i b`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B)
    (i : ι) (v : H i) :
    hilbertSum π b (lp.single 2 i v) = lp.single 2 i (π i b v) := by
  simp [hilbertSum]

/-- The operator norm of `StarAlgHom.hilbertSum π b` is the supremum of `‖π i b‖`. -/
theorem norm_hilbertSum_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    ‖hilbertSum π b‖ = ⨆ i, ‖π i b‖ := by
  simpa [hilbertSum] using
    NonUnitalStarAlgHom.norm_hilbertSum_apply (fun i => (π i).toNonUnitalStarAlgHom) b

/-- An element lies in the kernel of `StarAlgHom.hilbertSum π` if and only if it lies in the kernel
of every summand `π i`. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    hilbertSum π b = 0 ↔ ∀ i, π i b = 0 := by
  simp [hilbertSum]

/-- `StarAlgHom.hilbertSum π` is injective if and only if the kernels of the summands `π i` have
trivial intersection. -/
theorem hilbertSum_injective_iff (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ ⦃b⦄, (∀ i, π i b = 0) → b = 0 := by
  simpa [hilbertSum] using
    NonUnitalStarAlgHom.hilbertSum_injective_iff fun i => (π i).toNonUnitalStarAlgHom

/-- If one summand `π i` is injective, then `StarAlgHom.hilbertSum π` is injective. -/
theorem hilbertSum_injective_of_injective (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (i : ι)
    (hi : Function.Injective (π i)) : Function.Injective (hilbertSum π) :=
  (hilbertSum_injective_iff π).2 fun _ h => hi (by rw [h i, map_zero])

end StarAlgHom
