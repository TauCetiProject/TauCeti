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

A family of representations `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)` of a possibly nonunital C⋆-algebra
on Hilbert spaces `H i` is uniformly bounded at each `a : A` by `‖π i a‖ ≤ ‖a‖`, so it acts
coordinatewise on the Hilbert direct sum `lp H 2` via `lp.mapCLM`. Because adjoints commute with
coordinatewise direct sums on `lp H 2`, this assembles into a single representation
`NonUnitalStarAlgHom.hilbertSum π` (and `StarAlgHom.hilbertSum` in the unital setting).

Direct sums convert separating families of representations, such as the GNS representations of the
state space, into a single faithful representation, and preserve nondegeneracy in both directions:
the direct sum is nondegenerate if and only if every summand is. Taking a constant family yields
the ampliation `ρ.ampliation ι` on `ℓ²(ι, K)`.

## Main declarations

* `NonUnitalStarAlgHom.hilbertSum`, `StarAlgHom.hilbertSum`: the Hilbert direct sum of a family of
  C⋆-algebra representations on `lp H 2`.
* `NonUnitalStarAlgHom.hilbertSum_injective_iff`, `StarAlgHom.hilbertSum_injective_iff`: the
  direct sum is injective precisely when the summands jointly separate nonzero elements.
* `NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff`: the direct sum is nondegenerate if and
  only if every summand is nondegenerate.
* `NonUnitalStarAlgHom.ampliation`, `StarAlgHom.ampliation`: diagonal ampliation of a single
  representation to `ℓ²(ι, K)`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), §3.4.
* Dana Williams, *Crossed Products of C*-Algebras*, American Mathematical Society (2007), §2.1.
-/

public section

noncomputable section

open scoped ENNReal InnerProductSpace lp

namespace NonUnitalStarAlgHom

section HilbertSum

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The Hilbert direct sum of a family of representations of a C⋆-algebra, acting coordinatewise
on `lp H 2`. -/
def hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) : A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) fun i ↦ norm_apply_le (π i) a
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
  map_star' a := by
    rw [lp.star_mapCLM _ (norm_nonneg a) (fun i ↦ norm_apply_le (π i) a) (norm_nonneg (star a))
      fun i ↦ by simpa [map_star] using norm_apply_le (π i) (star a)]
    ext x i
    simp [map_star]

variable (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i))

/-- Operator-level unfolding of `hilbertSum` as `lp.mapCLM`. -/
theorem hilbertSum_def (a : A) :
    hilbertSum π a =
      lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) (fun i ↦ norm_apply_le (π i) a) :=
  (rfl)

/-- The Hilbert direct sum of representations acts coordinatewise on `lp H 2`. -/
@[simp]
theorem hilbertSum_apply_apply (a : A) (x : lp H 2) (i : ι) :
    hilbertSum π a x i = π i a (x i) :=
  (rfl)

/-- Coordinate evaluation intertwines the Hilbert direct sum with its `i`-th summand. -/
@[simp]
theorem evalCLM_comp_hilbertSum (a : A) (i : ι) :
    lp.evalCLM ℂ H 2 i ∘L hilbertSum π a = π i a ∘L lp.evalCLM ℂ H 2 i :=
  lp.evalCLM_comp_mapCLM _ (norm_nonneg a) (fun j ↦ norm_apply_le (π j) a) i

/-- On a single-coordinate vector, the Hilbert direct sum acts in that coordinate. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (a : A) (i : ι) (v : H i) :
    hilbertSum π a (lp.single 2 i v) = lp.single 2 i (π i a v) :=
  lp.mapCLM_single _ (norm_nonneg a) (fun j ↦ norm_apply_le (π j) a) i v

/-- The operator norm of `hilbertSum π a` is the supremum of the summand operator norms. -/
theorem norm_hilbertSum_apply (a : A) :
    ‖hilbertSum π a‖ = ⨆ i, ‖π i a‖ :=
  lp.norm_mapCLM _ (norm_nonneg a) fun j ↦ norm_apply_le (π j) a

variable {π}

/-- An element is killed by the Hilbert direct sum if and only if it is killed by every summand. -/
theorem hilbertSum_apply_eq_zero_iff {a : A} :
    hilbertSum π a = 0 ↔ ∀ i, π i a = 0 := by
  classical
  refine ⟨fun h i ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ ?_⟩
  · simpa using congr($h (lp.single 2 i v) i)
  · ext x i
    simp [h i]

/-- The Hilbert direct sum is injective if and only if the summands jointly separate `0`. -/
theorem hilbertSum_injective_iff :
    Function.Injective (hilbertSum π) ↔ ∀ a, (∀ i, π i a = 0) → a = 0 := by
  simp_rw [injective_iff_map_eq_zero, hilbertSum_apply_eq_zero_iff]

/-- **Nondegeneracy of a Hilbert direct sum.** The direct sum of a family of representations is
nondegenerate if and only if every summand is nondegenerate. -/
theorem isNondegenerate_hilbertSum_iff :
    (hilbertSum π).IsNondegenerate ↔ ∀ i, (π i).IsNondegenerate := by
  classical
  simp_rw [isNondegenerate_iff_forall_apply_eq_zero]
  refine ⟨fun h i v hv ↦ ?_, fun h x hx ↦ lp.ext <| funext fun i ↦ h i (x i) fun a ↦ ?_⟩
  · have hsingle : lp.single (E := H) 2 i v = 0 := h _ fun a ↦ by simp [hv a]
    simpa using congr(($hsingle : ∀ j, H j) i)
  · simpa using congr(($(hx a) : ∀ j, H j) i)

end HilbertSum

section Ampliation

variable {A K : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The diagonal **ampliation** of a representation `ρ` of a C⋆-algebra over an index type `ι`,
acting coordinatewise by `ρ` on `ℓ²(ι, K)`. -/
def ampliation (ι : Type*) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    A →⋆ₙₐ[ℂ] (ℓ²(ι, K) →L[ℂ] ℓ²(ι, K)) :=
  hilbertSum fun _ : ι ↦ ρ

theorem ampliation_eq_hilbertSum (ι : Type*) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ρ.ampliation ι = hilbertSum fun _ : ι ↦ ρ :=
  (rfl)

/-- The ampliation of `ρ` acts at `a` by the operator ampliation `lp.ampliation ι 2 (ρ a)`. -/
@[simp]
theorem ampliation_apply (ι : Type*) (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (a : A) :
    ρ.ampliation ι a = lp.ampliation ι 2 (ρ a) := by
  ext x i
  simp [ampliation_eq_hilbertSum]

/-- Over a nonempty index type, the ampliation of a representation is injective if and only if the
representation itself is injective. -/
theorem ampliation_injective_iff {ι : Type*} [Nonempty ι] {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} :
    Function.Injective (ρ.ampliation ι) ↔ Function.Injective ρ := by
  rw [ampliation_eq_hilbertSum, hilbertSum_injective_iff, injective_iff_map_eq_zero]
  simp

/-- The ampliation of a nondegenerate representation is nondegenerate. -/
theorem IsNondegenerate.ampliation (ι : Type*) {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (hρ : ρ.IsNondegenerate) : (ρ.ampliation ι).IsNondegenerate :=
  isNondegenerate_hilbertSum_iff.2 fun _ ↦ hρ

/-- Over a nonempty index type, the ampliation of a representation is nondegenerate if and only if
the representation itself is nondegenerate. -/
theorem isNondegenerate_ampliation_iff {ι : Type*} [Nonempty ι] {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)} :
    (ρ.ampliation ι).IsNondegenerate ↔ ρ.IsNondegenerate := by
  simp [ampliation_eq_hilbertSum, isNondegenerate_hilbertSum_iff]

end Ampliation

end NonUnitalStarAlgHom

namespace StarAlgHom

section HilbertSum

variable {B ι : Type*} {H : ι → Type*} [CStarAlgebra B]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The Hilbert direct sum of a family of unital representations of a unital C⋆-algebra, acting
coordinatewise on `lp H 2`. -/
def hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) : B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  __ := NonUnitalStarAlgHom.hilbertSum fun i ↦ (π i).toNonUnitalStarAlgHom
  map_one' := by ext x i; simp
  commutes' r := by ext x i; simp [Algebra.algebraMap_eq_smul_one]

variable (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i))

@[simp]
theorem toNonUnitalStarAlgHom_hilbertSum :
    (hilbertSum π).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.hilbertSum fun i ↦ (π i).toNonUnitalStarAlgHom :=
  (rfl)

/-- Operator-level unfolding of `StarAlgHom.hilbertSum` as `lp.mapCLM`. -/
theorem hilbertSum_def (b : B) :
    hilbertSum π b =
      lp.mapCLM 2 (fun i ↦ π i b) (norm_nonneg b)
        (fun i ↦ NonUnitalStarAlgHom.norm_apply_le (π i) b) :=
  (rfl)

/-- The Hilbert direct sum of unital representations acts coordinatewise on `lp H 2`. -/
@[simp]
theorem hilbertSum_apply_apply (b : B) (x : lp H 2) (i : ι) :
    hilbertSum π b x i = π i b (x i) :=
  (rfl)

/-- On a single-coordinate vector, the unital Hilbert direct sum acts in that coordinate. -/
@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (b : B) (i : ι) (v : H i) :
    hilbertSum π b (lp.single 2 i v) = lp.single 2 i (π i b v) :=
  lp.mapCLM_single _ (norm_nonneg b) (fun j ↦ NonUnitalStarAlgHom.norm_apply_le (π j) b) i v

variable {π}

/-- An element is killed by the unital Hilbert direct sum if and only if it is killed by every
summand. -/
theorem hilbertSum_apply_eq_zero_iff {b : B} :
    hilbertSum π b = 0 ↔ ∀ i, π i b = 0 :=
  NonUnitalStarAlgHom.hilbertSum_apply_eq_zero_iff

/-- The unital Hilbert direct sum is injective if and only if the summands jointly separate `0`. -/
theorem hilbertSum_injective_iff :
    Function.Injective (hilbertSum π) ↔ ∀ b, (∀ i, π i b = 0) → b = 0 :=
  NonUnitalStarAlgHom.hilbertSum_injective_iff

end HilbertSum

section Ampliation

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The diagonal **ampliation** of a unital representation `ρ` of a unital C⋆-algebra over an index
type `ι`, acting coordinatewise by `ρ` on `ℓ²(ι, K)`. -/
def ampliation (ι : Type*) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    B →⋆ₐ[ℂ] (ℓ²(ι, K) →L[ℂ] ℓ²(ι, K)) :=
  hilbertSum fun _ : ι ↦ ρ

@[simp]
theorem toNonUnitalStarAlgHom_ampliation (ι : Type*) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (ρ.ampliation ι).toNonUnitalStarAlgHom = ρ.toNonUnitalStarAlgHom.ampliation ι :=
  (rfl)

/-- The ampliation of `ρ` acts at `b` by the operator ampliation `lp.ampliation ι 2 (ρ b)`. -/
@[simp]
theorem ampliation_apply (ι : Type*) (ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    ρ.ampliation ι b = lp.ampliation ι 2 (ρ b) :=
  ρ.toNonUnitalStarAlgHom.ampliation_apply ι b

/-- Over a nonempty index type, the ampliation of a unital representation is injective if and only
if the representation itself is injective. -/
theorem ampliation_injective_iff {ι : Type*} [Nonempty ι] {ρ : B →⋆ₐ[ℂ] (K →L[ℂ] K)} :
    Function.Injective (ρ.ampliation ι) ↔ Function.Injective ρ :=
  NonUnitalStarAlgHom.ampliation_injective_iff (ρ := ρ.toNonUnitalStarAlgHom)

end Ampliation

end StarAlgHom
