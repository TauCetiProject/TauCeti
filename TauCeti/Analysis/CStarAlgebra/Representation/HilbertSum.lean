/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.HilbertSum

/-!
# Hilbert direct sums and ampliations of C⋆-algebra representations

Every `⋆`-representation `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)` of a possibly nonunital C⋆-algebra is
contractive (`NonUnitalStarAlgHom.norm_apply_le`), so any family of representations is uniformly
bounded at each element `a` by `‖a‖` and acts coordinatewise on the Hilbert direct sum `lp H 2`.
Compatibility of `lp.mapCLM` with algebraic operations and adjoints (`lp.adjoint_mapCLM`) makes this
coordinatewise action a `⋆`-representation `NonUnitalStarAlgHom.hilbertSum π` (and a unital
`⋆`-representation `StarAlgHom.hilbertSum π` when `A` and the summands are unital).

* `NonUnitalStarAlgHom.norm_hilbertSum_apply`: the operator norm of `hilbertSum π a` is
  `⨆ i, ‖π i a‖`.
* `NonUnitalStarAlgHom.hilbertSum_injective_iff`: the direct sum is faithful if and only if no
  nonzero element of `A` lies in the kernel of every summand.
* `NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`: the direct sum is nondegenerate if and only
  if every summand is nondegenerate.
* `NonUnitalStarAlgHom.ampliation` and `StarAlgHom.ampliation`: the diagonal ampliation of a single
  representation to `ℓ²(ι, K)`, preserving nondegeneracy for all `ι` and faithfulness for nonempty
  `ι`.

## References

* J. Dixmier, *C*-Algebras*, §2.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.4.
-/

public section

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace NonUnitalStarAlgHom

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The Hilbert direct sum `⊕ i, π i` of a family of representations of a C⋆-algebra `A`, acting
coordinatewise on `lp H 2`. -/
def hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) : A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) fun i ↦ norm_apply_le (π i) a
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_mul' a b := by ext x i; simp
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint, lp.adjoint_mapCLM _ _ _ (norm_nonneg a)
      fun i ↦ by simpa using norm_apply_le (π i) a]
    ext x i
    simp [← ContinuousLinearMap.star_eq_adjoint, map_star]

theorem hilbertSum_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    hilbertSum π a =
      lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) (fun i ↦ norm_apply_le (π i) a) := by
  rfl

@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) (x : lp H 2)
    (i : ι) : hilbertSum π a x i = π i a (x i) := by
  simp [hilbertSum_apply]

@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A)
    (i : ι) (ξ : H i) :
    hilbertSum π a (lp.single 2 i ξ) = lp.single 2 i (π i a ξ) := by
  simp [hilbertSum_apply]

@[simp]
theorem evalCLM_comp_hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π a = π i a ∘L lp.evalCLM ℂ H 2 i := by
  simp [hilbertSum_apply]

/-- The operator norm of a Hilbert direct sum at `a` is the supremum of the summand norms. -/
theorem norm_hilbertSum_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    ‖hilbertSum π a‖ = ⨆ i, ‖π i a‖ := by
  rw [hilbertSum_apply, lp.norm_mapCLM]

/-- A Hilbert direct sum vanishes at `a` if and only if every summand vanishes at `a`. -/
@[simp]
theorem hilbertSum_eq_zero_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) {a : A} :
    hilbertSum π a = 0 ↔ ∀ i, π i a = 0 := by
  rw [hilbertSum_apply, ← lp.mapCLM_zero (p := 2) (norm_nonneg a) (fun _ ↦ by simp),
    lp.mapCLM_inj, funext_iff]

/-- A Hilbert direct sum of representations is injective if and only if the summands jointly kill
only `0`. -/
theorem hilbertSum_injective_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ a, (∀ i, π i a = 0) → a = 0 := by
  simp_rw [injective_iff_map_eq_zero, hilbertSum_eq_zero_iff]

/-- If at least one summand is injective, the Hilbert direct sum is injective. -/
theorem hilbertSum_injective_of_exists (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) {i : ι}
    (hπ : Function.Injective (π i)) : Function.Injective (hilbertSum π) :=
  (hilbertSum_injective_iff π).2 fun a ha ↦ (injective_iff_map_eq_zero (π i)).1 hπ a (ha i)

/-- A Hilbert direct sum of representations is nondegenerate if and only if every summand is
nondegenerate. -/
@[simp]
theorem isNondegenerate_hilbertSum_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).IsNondegenerate ↔ ∀ i, (π i).IsNondegenerate := by
  classical
  simp only [isNondegenerate_iff_forall_apply_eq_zero]
  refine ⟨fun h i ξ hξ ↦ ?_, fun h x hx ↦ lp.ext <| funext fun i ↦
    h i (x i) fun a ↦ by simpa using congr_arg (fun y : lp H 2 ↦ y i) (hx a)⟩
  have h0 : lp.single 2 i ξ = 0 := h (lp.single 2 i ξ) fun a ↦ by simp [hξ a]
  simpa using congr_arg (fun y : lp H 2 ↦ y i) h0

section Ampliation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι) in
/-- Diagonal ampliation `a ↦ ⊕_{i : ι} ρ a` of a representation `ρ` of `A` to `ℓ²(ι, K)`. -/
def ampliation (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : A →⋆ₙₐ[ℂ] (ℓ²(ι, K) →L[ℂ] ℓ²(ι, K)) :=
  (lp.ampliationStarAlgHom ι ℂ K).toNonUnitalStarAlgHom.comp ρ

@[simp]
theorem ampliation_apply (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    ρ.ampliation ι a = lp.ampliation ι 2 (ρ a) := by
  simp [ampliation]

/-- Diagonal ampliation coincides with the constant-family Hilbert direct sum. -/
theorem ampliation_eq_hilbertSum (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ρ.ampliation ι = hilbertSum fun _ : ι ↦ ρ := by
  ext a x i
  simp

@[simp]
theorem ampliation_injective_iff [Nonempty ι] (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    Function.Injective (ρ.ampliation ι) ↔ Function.Injective ρ := by
  simpa [ampliation] using
    (lp.ampliationStarAlgHom_injective (ι := ι) (𝕜 := ℂ) (X := K)).of_comp_iff ρ

/-- Diagonal ampliation preserves nondegeneracy over every index type, including the empty one. -/
theorem IsNondegenerate.ampliation {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} (hρ : ρ.IsNondegenerate) :
    (ρ.ampliation ι).IsNondegenerate := by
  rw [ampliation_eq_hilbertSum, isNondegenerate_hilbertSum_iff]
  exact fun _ ↦ hρ

@[simp]
theorem isNondegenerate_ampliation_iff [Nonempty ι] (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    (ρ.ampliation ι).IsNondegenerate ↔ ρ.IsNondegenerate := by
  rw [ampliation_eq_hilbertSum, isNondegenerate_hilbertSum_iff, forall_const]

end Ampliation

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {B ι : Type*} {H : ι → Type*} [CStarAlgebra B]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The Hilbert direct sum `⊕ i, π i` of a family of unital `⋆`-representations of a unital
C⋆-algebra `B` on `lp H 2`. -/
def hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) : B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) :=
  ((NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2
    fun i ↦ (π i).isNondegenerate_toNonUnitalStarAlgHom).toStarAlgHom

theorem coe_hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    ⇑(hilbertSum π) = ⇑(NonUnitalStarAlgHom.hilbertSum fun i ↦ (π i).toNonUnitalStarAlgHom) :=
  NonUnitalStarAlgHom.IsNondegenerate.coe_toStarAlgHom _

@[simp]
theorem toNonUnitalStarAlgHom_hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.hilbertSum fun i ↦ (π i).toNonUnitalStarAlgHom :=
  NonUnitalStarAlgHom.IsNondegenerate.toNonUnitalStarAlgHom_toStarAlgHom _

@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) (x : lp H 2) (i : ι) :
    hilbertSum π b x i = π i b (x i) := by
  rw [coe_hilbertSum, NonUnitalStarAlgHom.hilbertSum_apply_apply]
  rfl

@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B)
    (i : ι) (ξ : H i) :
    hilbertSum π b (lp.single 2 i ξ) = lp.single 2 i (π i b ξ) := by
  rw [coe_hilbertSum, NonUnitalStarAlgHom.hilbertSum_apply_single]
  rfl

/-- The operator norm of a unital Hilbert direct sum at `b` is the supremum of the summand norms. -/
theorem norm_hilbertSum_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    ‖hilbertSum π b‖ = ⨆ i, ‖π i b‖ := by
  rw [coe_hilbertSum, NonUnitalStarAlgHom.norm_hilbertSum_apply]
  rfl

/-- A unital Hilbert direct sum is injective if and only if the summands jointly kill only `0`. -/
theorem hilbertSum_injective_iff (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ b, (∀ i, π i b = 0) → b = 0 := by
  rw [coe_hilbertSum, NonUnitalStarAlgHom.hilbertSum_injective_iff]
  rfl

section Ampliation

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (ι) in
/-- Diagonal ampliation `b ↦ ⊕_{i : ι} ρ b` of a unital `⋆`-representation `ρ` to `ℓ²(ι, K)`. -/
def ampliation (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) : B →⋆ₐ[ℂ] (ℓ²(ι, K) →L[ℂ] ℓ²(ι, K)) :=
  (lp.ampliationStarAlgHom ι ℂ K).comp ρ

@[simp]
theorem toNonUnitalStarAlgHom_ampliation (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (ρ.ampliation ι).toNonUnitalStarAlgHom = ρ.toNonUnitalStarAlgHom.ampliation ι := by
  ext; simp [ampliation]

@[simp]
theorem ampliation_apply (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    ρ.ampliation ι b = lp.ampliation ι 2 (ρ b) := by
  simp [ampliation]

/-- Diagonal ampliation coincides with the constant-family unital Hilbert direct sum. -/
theorem ampliation_eq_hilbertSum (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ρ.ampliation ι = hilbertSum fun _ : ι ↦ ρ := by
  ext b x i
  simp

@[simp]
theorem ampliation_injective_iff [Nonempty ι] (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    Function.Injective (ρ.ampliation ι) ↔ Function.Injective ρ := by
  rw [← coe_toNonUnitalStarAlgHom, toNonUnitalStarAlgHom_ampliation]
  exact ρ.toNonUnitalStarAlgHom.ampliation_injective_iff

end Ampliation

end StarAlgHom

end
