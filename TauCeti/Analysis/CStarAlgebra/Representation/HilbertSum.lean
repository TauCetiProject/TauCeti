/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.HilbertSum

/-!
# Hilbert direct sums of representations

A family of representations `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)` of a possibly nonunital
C⋆-algebra `A`, indexed by an arbitrary type, has a direct sum `⊕ π i` acting coordinatewise on
the Hilbert direct sum `lp H 2`, following the model of `ContRepresentation.hilbertSum`. Each
`π i a` has norm at most `‖a‖`, so the summands are uniformly bounded and `⊕ π i a` is Mathlib's
`lp.mapCLM`; its compatibility with adjoints (Tau Ceti's `lp.adjoint_mapCLM`) makes `⊕ π i` a
star homomorphism.

The direct sum has norm `‖(⊕ π i) a‖ = ⨆ i, ‖π i a‖`, it is injective (faithful) exactly when the
family jointly separates the points of `A`, and it is nondegenerate exactly when every summand is.
In particular, summing a point-separating family of nondegenerate representations (such as the GNS
representations of all states or positive functionals) yields a single faithful nondegenerate
representation.

## Main declarations

* `NonUnitalStarAlgHom.hilbertSum`: the direct sum `⊕ π i` of a family of representations, with
  coordinate, `lp.evalCLM`, `lp.single`, injectivity-on-families, and composition lemmas.
* `NonUnitalStarAlgHom.norm_hilbertSum_apply`: `‖(⊕ π i) a‖ = ⨆ i, ‖π i a‖`.
* `NonUnitalStarAlgHom.injective_hilbertSum_iff`: `⊕ π i` is faithful exactly when no nonzero
  `a` is killed by every `π i`.
* `NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`: `⊕ π i` is nondegenerate exactly when
  every `π i` is.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §II.1, §VIII.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, Section 3.4.
-/

public section

noncomputable section

namespace NonUnitalStarAlgHom

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

section

variable (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))

/-- The **Hilbert direct sum** `⊕ π i` of a family of representations of a C⋆-algebra, acting
coordinatewise on `lp H 2`: `(⊕ π i) a x = (π i a (x i))ᵢ`. -/
def hilbertSum : A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i => π i a) (norm_nonneg a) fun i => norm_apply_le (π i) a
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_mul' a b := by ext x i; simp
  map_star' a := by
    rw [ContinuousLinearMap.star_eq_adjoint, lp.adjoint_mapCLM _ _ _ (norm_nonneg a)
      fun i => by simpa using norm_apply_le (π i) a]
    ext x i
    simp [← ContinuousLinearMap.star_eq_adjoint, map_star]

/-- The direct sum `⊕ π i a` is the coordinatewise operator `lp.mapCLM` of the family `π i a`. -/
theorem hilbertSum_apply (a : A) :
    hilbertSum π a =
      lp.mapCLM 2 (fun i => π i a) (norm_nonneg a) fun i => norm_apply_le (π i) a :=
  (rfl)

/-- The direct sum of representations acts coordinatewise. -/
@[simp]
theorem hilbertSum_apply_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSum π a x i = π i a (x i) := by
  simp [hilbertSum_apply]

/-- Precomposing a Hilbert direct sum with a `⋆`-homomorphism is the Hilbert direct sum of the
precomposed summands. -/
@[simp]
theorem hilbertSum_comp {A' : Type*} [NonUnitalCStarAlgebra A'] (f : A' →⋆ₙₐ[ℂ] A) :
    (hilbertSum π).comp f = hilbertSum fun i => (π i).comp f := by
  ext a x i
  simp

/-- Coordinate evaluation intertwines `hilbertSum π a` with `π i a`. -/
@[simp]
theorem evalCLM_comp_hilbertSum_apply (a : A) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π a = π i a ∘L lp.evalCLM ℂ H 2 i := by
  rw [hilbertSum_apply]
  exact lp.evalCLM_comp_mapCLM _ _ _ i

/-- The direct sum of representations maps the coordinate vector `single i ξ` to
`single i (π i a ξ)`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (a : A) (i : ι) (ξ : H i) :
    hilbertSum π a (lp.single 2 i ξ) = lp.single 2 i (π i a ξ) := by
  simp [hilbertSum_apply]

/-- **Norm of a direct sum of representations.** `‖(⊕ π i) a‖ = ⨆ i, ‖π i a‖`, which is `0` for an
empty family. -/
theorem norm_hilbertSum_apply (a : A) : ‖hilbertSum π a‖ = ⨆ i, ‖π i a‖ := by
  simp [hilbertSum_apply, lp.norm_mapCLM]

/-- An element acts as zero in the direct sum exactly when it acts as zero in every summand. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff {a : A} : hilbertSum π a = 0 ↔ ∀ i, π i a = 0 := by
  rw [hilbertSum_apply, ← lp.mapCLM_zero (p := 2) (le_refl (0 : ℝ)) (fun i => by simp),
    lp.mapCLM_inj, funext_iff]

/-- **Faithfulness of a direct sum.** The direct sum of representations is injective exactly when
the summands jointly separate points: no nonzero `a` is killed by every `π i`. -/
theorem injective_hilbertSum_iff :
    Function.Injective (hilbertSum π) ↔ ∀ a, (∀ i, π i a = 0) → a = 0 := by
  simp [injective_iff_map_eq_zero]

/-- If one summand `π i` is injective, then `hilbertSum π` is injective. -/
theorem injective_hilbertSum_of_injective (i : ι) (hi : Function.Injective (π i)) :
    Function.Injective (hilbertSum π) :=
  (injective_hilbertSum_iff π).2 fun _ h => hi (by rw [h i, map_zero])

/-- **Nondegeneracy of a direct sum.** The direct sum of representations is nondegenerate exactly
when every summand is. -/
@[simp]
theorem isNondegenerate_hilbertSum_iff :
    (hilbertSum π).IsNondegenerate ↔ ∀ i, (π i).IsNondegenerate := by
  classical
  simp_rw [isNondegenerate_iff_forall_apply_eq_zero]
  refine ⟨fun h i ξ hξ => ?_, fun h x hx => ?_⟩
  · have := h (lp.single 2 i ξ) fun a => by simp [hξ a]
    simpa using congr($this i)
  · ext i
    exact h i (x i) fun a => by simpa using congr($(hx a) i)

end

/-- `hilbertSum` is injective as a map on families of representations. -/
theorem hilbertSum_injective :
    Function.Injective
      (hilbertSum : (∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) → A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)) := by
  intro π₁ π₂ h
  funext i
  refine NonUnitalStarAlgHom.ext fun a => ?_
  have ha : hilbertSum π₁ a = hilbertSum π₂ a := congr($h a)
  rw [hilbertSum_apply, hilbertSum_apply, lp.mapCLM_inj] at ha
  exact congrFun ha i

/-- Two families of representations have the same Hilbert direct sum if and only if they are
equal. -/
@[simp]
theorem hilbertSum_inj {π₁ π₂ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)} :
    hilbertSum π₁ = hilbertSum π₂ ↔ π₁ = π₂ :=
  hilbertSum_injective.eq_iff

/-- The Hilbert direct sum of zero representations is the zero representation. -/
@[simp]
theorem hilbertSum_zero :
    hilbertSum (fun _ => 0 : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) = 0 := by
  ext a x i
  simp

end NonUnitalStarAlgHom
