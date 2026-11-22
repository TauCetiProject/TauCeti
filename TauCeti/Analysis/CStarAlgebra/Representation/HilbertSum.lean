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

When `B` is a unital C⋆-algebra, a family of unital representations `π i : B →⋆ₐ[ℂ] (H i →L[ℂ] H i)`
similarly has a unital direct sum `StarAlgHom.hilbertSum π : B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)`,
extending the `ContRepresentation.hilbertSum` model to unital star-algebra homomorphisms by
promoting `NonUnitalStarAlgHom.hilbertSum` via `IsNondegenerate.toStarAlgHom`. Taking
multiplier extensions commutes with Hilbert direct sums
(`NonUnitalStarAlgHom.multiplierExtension_hilbertSum`).

## Main declarations

* `NonUnitalStarAlgHom.hilbertSum`: the direct sum `⊕ π i` of a family of representations, with
  coordinate, `lp.evalCLM`, `lp.single`, injectivity-on-families, and composition lemmas.
* `NonUnitalStarAlgHom.norm_hilbertSum_apply`: `‖(⊕ π i) a‖ = ⨆ i, ‖π i a‖`.
* `NonUnitalStarAlgHom.injective_hilbertSum_iff`: `⊕ π i` is faithful exactly when no nonzero
  `a` is killed by every `π i`.
* `NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`: `⊕ π i` is nondegenerate exactly when
  every `π i` is.
* `StarAlgHom.hilbertSum`: the corresponding unital direct-sum representation on `lp H 2`.
* `NonUnitalStarAlgHom.multiplierExtension_hilbertSum`: the multiplier extension of a nondegenerate
  direct sum is the unital direct sum of the summand multiplier extensions.

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

namespace StarAlgHom

variable {B ι : Type*} {H : ι → Type*} [CStarAlgebra B]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

section

variable (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i))

/-- The **Hilbert direct sum** `⊕ i, π i` of a family of unital representations of a unital
C⋆-algebra `B`, acting coordinatewise on `lp H 2`. -/
def hilbertSum : B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) :=
  ((NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff
    (fun i => (π i).toNonUnitalStarAlgHom)).2 fun i =>
    (π i).isNondegenerate_toNonUnitalStarAlgHom).toStarAlgHom

/-- Forgetting the unit of `StarAlgHom.hilbertSum π` gives `NonUnitalStarAlgHom.hilbertSum`. -/
@[simp]
theorem toNonUnitalStarAlgHom_hilbertSum :
    (hilbertSum π).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.hilbertSum fun i => (π i).toNonUnitalStarAlgHom := by
  simp [hilbertSum]

/-- Coercing `StarAlgHom.hilbertSum π` to a function gives `NonUnitalStarAlgHom.hilbertSum`. -/
theorem coe_hilbertSum :
    ⇑(hilbertSum π) = ⇑(NonUnitalStarAlgHom.hilbertSum fun i => (π i).toNonUnitalStarAlgHom) :=
  NonUnitalStarAlgHom.IsNondegenerate.coe_toStarAlgHom _

/-- `StarAlgHom.hilbertSum π` evaluates at `b` to `lp.mapCLM 2 (fun i => π i b)`. -/
theorem hilbertSum_apply (b : B) :
    hilbertSum π b =
      lp.mapCLM 2 (fun i => π i b) (norm_nonneg b)
        (fun i => NonUnitalStarAlgHom.norm_apply_le (π i) b) := by
  simp [coe_hilbertSum, NonUnitalStarAlgHom.hilbertSum_apply]

/-- The unital direct-sum representation acts coordinatewise on `lp H 2`. -/
@[simp]
theorem hilbertSum_apply_apply (b : B) (x : lp H 2) (i : ι) :
    hilbertSum π b x i = π i b (x i) := by
  simp [coe_hilbertSum]

/-- Precomposing a unital Hilbert direct sum with a unital `⋆`-homomorphism is the Hilbert direct
sum of the precomposed summands. -/
@[simp]
theorem hilbertSum_comp {B' : Type*} [CStarAlgebra B'] (f : B' →⋆ₐ[ℂ] B) :
    (hilbertSum π).comp f = hilbertSum fun i => (π i).comp f := by
  ext b x i
  simp

/-- Coordinate evaluation intertwines `StarAlgHom.hilbertSum π b` with `π i b`. -/
@[simp]
theorem evalCLM_comp_hilbertSum_apply (b : B) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π b = π i b ∘L lp.evalCLM ℂ H 2 i := by
  simp [coe_hilbertSum]

/-- On a coordinate vector `lp.single 2 i ξ`, `StarAlgHom.hilbertSum π b` acts in coordinate `i`
by `π i b`. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (b : B) (i : ι) (ξ : H i) :
    hilbertSum π b (lp.single 2 i ξ) = lp.single 2 i (π i b ξ) := by
  simp [coe_hilbertSum]

/-- The operator norm of `StarAlgHom.hilbertSum π b` is the supremum of `‖π i b‖`. -/
theorem norm_hilbertSum_apply (b : B) : ‖hilbertSum π b‖ = ⨆ i, ‖π i b‖ := by
  simp [coe_hilbertSum, NonUnitalStarAlgHom.norm_hilbertSum_apply]

/-- An element lies in the kernel of `StarAlgHom.hilbertSum π` if and only if it lies in the kernel
of every summand `π i`. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff {b : B} : hilbertSum π b = 0 ↔ ∀ i, π i b = 0 := by
  simp [coe_hilbertSum]

/-- `StarAlgHom.hilbertSum π` is injective if and only if the kernels of the summands `π i` have
trivial intersection. -/
theorem injective_hilbertSum_iff :
    Function.Injective (hilbertSum π) ↔ ∀ b, (∀ i, π i b = 0) → b = 0 := by
  simp [coe_hilbertSum, NonUnitalStarAlgHom.injective_hilbertSum_iff]

/-- If one summand `π i` is injective, then `StarAlgHom.hilbertSum π` is injective. -/
theorem injective_hilbertSum_of_injective (i : ι) (hi : Function.Injective (π i)) :
    Function.Injective (hilbertSum π) :=
  (injective_hilbertSum_iff π).2 fun _ h => hi (by rw [h i, map_zero])

end

/-- `StarAlgHom.hilbertSum` is injective as a map on families of unital representations. -/
theorem hilbertSum_injective :
    Function.Injective
      (hilbertSum : (∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) → B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2)) := by
  intro π₁ π₂ h
  have h' : (fun i => (π₁ i).toNonUnitalStarAlgHom) = fun i => (π₂ i).toNonUnitalStarAlgHom := by
    simpa using congrArg StarAlgHom.toNonUnitalStarAlgHom h
  funext i
  exact StarAlgHom.ext fun b => by simpa using congr($(congrFun h' i) b)

/-- Two families of unital representations have the same Hilbert direct sum if and only if they
are equal. -/
@[simp]
theorem hilbertSum_inj {π₁ π₂ : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)} :
    hilbertSum π₁ = hilbertSum π₂ ↔ π₁ = π₂ :=
  hilbertSum_injective.eq_iff

end StarAlgHom

namespace NonUnitalStarAlgHom

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The multiplier extension of a nondegenerate Hilbert direct sum is the unital Hilbert direct
sum of the summand multiplier extensions. -/
@[simp]
theorem multiplierExtension_hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))
    (h : (hilbertSum π).IsNondegenerate) :
    (hilbertSum π).multiplierExtension h =
      StarAlgHom.hilbertSum fun i =>
        (π i).multiplierExtension ((isNondegenerate_hilbertSum_iff π).1 h i) := by
  refine StarAlgHom.ext fun m => ((eq_multiplierExtension_iff h).2 fun a => ?_).symm
  ext x i
  simp

end NonUnitalStarAlgHom
