/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
public import TauCeti.Analysis.InnerProductSpace.HilbertSum

/-!
# Hilbert direct sums and ampliations of C⋆-representations

For a family `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)` of Hilbert-space representations of a possibly
nonunital complex C⋆-algebra `A`, the uniform contractivity bound `‖π i a‖ ≤ ‖a‖` allows the
coordinatewise action on the Hilbert direct sum `lp H 2` to be bundled as a representation
`NonUnitalStarAlgHom.hilbertSum π` (and `StarAlgHom.hilbertSum` in the unital case). Taking a
constant family gives the diagonal ampliation `NonUnitalStarAlgHom.ampliation ι π` on
`lp (fun _ : ι ↦ H) 2` (and `StarAlgHom.ampliation`).

Hilbert direct sums assemble families of representations into a single representation whose kernel
is the intersection of the summand kernels—for instance, summing the GNS representations over all
states in the Gelfand–Naimark construction. Diagonal ampliations preserve faithfulness and
nondegeneracy (over nonempty index types) while forcing infinite-dimensional Hilbert carriers, such
as countable ampliations to `ℓ²(ℕ)`.

## Main definitions and results

* `NonUnitalStarAlgHom.hilbertSum` and `StarAlgHom.hilbertSum`: coordinatewise direct sum of a
  family of representations on `lp H 2`, with `norm_hilbertSum_apply`, `hilbertSum_injective_iff`,
  and `isNondegenerate_hilbertSum_iff`.
* `NonUnitalStarAlgHom.ampliation` and `StarAlgHom.ampliation`: diagonal ampliation of a single
  representation to `lp (fun _ : ι ↦ H) 2`, with `norm_ampliation_apply`,
  `ampliation_injective_iff`, and `isNondegenerate_ampliation_iff`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §VIII.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press, 1990, §3.4.
-/

public section

noncomputable section

open scoped CStarAlgebra ENNReal InnerProductSpace lp

namespace NonUnitalStarAlgHom

section HilbertSum

variable {A ι : Type*} {H : ι → Type*} [NonUnitalCStarAlgebra A]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- The **Hilbert direct sum** of a family of representations `π i : A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)`,
acting coordinatewise on `lp H 2`. -/
def hilbertSum (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    A →⋆ₙₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) where
  toFun a := lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) fun i ↦ norm_apply_le (π i) a
  map_zero' := by ext x i; simp
  map_add' a b := by ext x i; simp
  map_smul' c a := by ext x i; simp
  map_mul' a b := by ext x i; simp [mul_apply_eq_comp]
  map_star' a := by
    rw [lp.star_mapCLM _ _ _ (norm_nonneg a) fun i ↦ by simpa using norm_apply_le (π i) a]
    ext x i
    simp [map_star]

theorem hilbertSum_apply_eq_mapCLM (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    hilbertSum π a =
      lp.mapCLM 2 (fun i ↦ π i a) (norm_nonneg a) (fun i ↦ norm_apply_le (π i) a) :=
  (rfl)

@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) (x : lp H 2)
    (i : ι) : hilbertSum π a x i = π i a (x i) :=
  (rfl)

@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A)
    (i : ι) (ξ : H i) :
    hilbertSum π a (lp.single 2 i ξ) = lp.single 2 i (π i a ξ) := by
  rw [hilbertSum_apply_eq_mapCLM]
  exact lp.mapCLM_single _ _ _ i ξ

/-- The operator norm of `hilbertSum π a` is the supremum of the summand norms `‖π i a‖`. -/
theorem norm_hilbertSum_apply (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    ‖hilbertSum π a‖ = ⨆ i, ‖π i a‖ := by
  rw [hilbertSum_apply_eq_mapCLM]
  exact lp.norm_mapCLM _ _ _

/-- An element acts as zero in `hilbertSum π` if and only if it acts as zero in every summand. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (a : A) :
    hilbertSum π a = 0 ↔ ∀ i, π i a = 0 := by
  classical
  refine ⟨fun h i ↦ ContinuousLinearMap.ext fun ξ ↦ ?_, fun h ↦ ?_⟩
  · simpa using congr($(h) (lp.single 2 i ξ) i)
  · ext x i
    simp [h i]

/-- Forming the Hilbert direct sum of a family of representations is injective. -/
theorem hilbertSum_injective :
    Function.Injective (hilbertSum (A := A) (H := H)) := by
  classical
  intro π₁ π₂ h
  ext i a ξ
  simpa using congr($(h) a (lp.single 2 i ξ) i)

@[simp]
theorem hilbertSum_inj {π₁ π₂ : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)} :
    hilbertSum π₁ = hilbertSum π₂ ↔ π₁ = π₂ :=
  hilbertSum_injective.eq_iff

@[simp]
theorem hilbertSum_zero :
    hilbertSum (0 : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) = 0 := by
  ext a x i
  simp

/-- A Hilbert direct sum of representations is injective if and only if the summands jointly
separate `0` (no nonzero element of `A` lies in the kernel of every `π i`). -/
theorem hilbertSum_injective_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ ⦃a : A⦄, (∀ i, π i a = 0) → a = 0 := by
  rw [injective_iff_map_eq_zero]
  simp_rw [hilbertSum_apply_eq_zero_iff]

/-- A Hilbert direct sum is injective as soon as one of its summands is injective. -/
theorem hilbertSum_injective_of_injective (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) (i : ι)
    (hi : Function.Injective (π i)) : Function.Injective (hilbertSum π) :=
  (hilbertSum_injective_iff π).2 fun _ ha ↦ (injective_iff_map_eq_zero (π i)).1 hi _ (ha i)

/-- A Hilbert direct sum of representations is nondegenerate if and only if every summand is
nondegenerate. -/
@[simp]
theorem isNondegenerate_hilbertSum_iff (π : ∀ i, A →⋆ₙₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).IsNondegenerate ↔ ∀ i, (π i).IsNondegenerate := by
  classical
  simp_rw [isNondegenerate_iff_forall_apply_eq_zero]
  refine ⟨fun h i ξ hξ ↦ ?_, fun h x hx ↦ lp.ext <| funext fun i ↦ h i (x i) fun a ↦ ?_⟩
  · have hsingle : lp.single 2 i ξ = (0 : lp H 2) :=
      h (lp.single 2 i ξ) fun a ↦ by simp [hξ a]
    simpa using congr_fun (Subtype.ext_iff.1 hsingle) i
  · simpa using congr_fun (Subtype.ext_iff.1 (hx a)) i

end HilbertSum

section Ampliation

variable {A H : Type*} [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Diagonal **ampliation** of a representation `π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)` to the Hilbert sum
`lp (fun _ : ι ↦ H) 2` of copies of `H` indexed by `ι`. -/
def ampliation (ι : Type*) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    A →⋆ₙₐ[ℂ] (lp (fun _ : ι ↦ H) 2 →L[ℂ] lp (fun _ : ι ↦ H) 2) :=
  hilbertSum fun _ : ι ↦ π

theorem ampliation_apply_eq_ampliation (ι : Type*) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    π.ampliation ι a = lp.ampliation ι 2 (π a) := by
  ext x i
  simp [ampliation]

@[simp]
theorem ampliation_apply_apply (ι : Type*) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (x : lp (fun _ : ι ↦ H) 2) (i : ι) :
    π.ampliation ι a x i = π a (x i) :=
  (rfl)

@[simp]
theorem ampliation_apply_single {ι : Type*} [DecidableEq ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A)
    (i : ι) (ξ : H) :
    π.ampliation ι a (lp.single 2 i ξ) = lp.single 2 i (π a ξ) :=
  hilbertSum_apply_single (H := fun _ : ι ↦ H) (fun _ ↦ π) a i ξ

/-- Over a nonempty index type `ι`, diagonal ampliation preserves operator norms. -/
@[simp]
theorem norm_ampliation_apply (ι : Type*) [Nonempty ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (a : A) :
    ‖π.ampliation ι a‖ = ‖π a‖ := by
  rw [ampliation_apply_eq_ampliation, lp.norm_ampliation]

/-- Over a nonempty index type `ι`, an element acts as zero in `π.ampliation ι` if and only if it
acts as zero in `π`. -/
@[simp]
theorem ampliation_apply_eq_zero_iff (ι : Type*) [Nonempty ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : A) : π.ampliation ι a = 0 ↔ π a = 0 := by
  simp [ampliation]

/-- Over a nonempty index type `ι`, diagonal ampliation of representations is injective. -/
theorem ampliation_injective (ι : Type*) [Nonempty ι] :
    Function.Injective (ampliation ι : (A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) → _) := by
  intro π₁ π₂ h
  simpa using congr_fun (hilbertSum_injective h) (Classical.arbitrary ι)

@[simp]
theorem ampliation_inj (ι : Type*) [Nonempty ι] {π₁ π₂ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} :
    π₁.ampliation ι = π₂.ampliation ι ↔ π₁ = π₂ :=
  (ampliation_injective ι).eq_iff

@[simp]
theorem ampliation_zero (ι : Type*) :
    (0 : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)).ampliation ι = 0 :=
  hilbertSum_zero

/-- Over a nonempty index type `ι`, a diagonal ampliation `π.ampliation ι` is injective if and only
if `π` is injective. -/
@[simp]
theorem ampliation_injective_iff (ι : Type*) [Nonempty ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    Function.Injective (π.ampliation ι) ↔ Function.Injective π := by
  rw [ampliation, hilbertSum_injective_iff, injective_iff_map_eq_zero]
  simp

/-- Diagonal ampliation over any index type `ι` (including an empty index type) preserves
nondegeneracy. -/
theorem IsNondegenerate.ampliation {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} (hπ : π.IsNondegenerate)
    (ι : Type*) : (π.ampliation ι).IsNondegenerate :=
  (isNondegenerate_hilbertSum_iff _).2 fun _ ↦ hπ

/-- Over a nonempty index type `ι`, `π.ampliation ι` is nondegenerate if and only if `π` is
nondegenerate (whereas for empty `ι`, `IsNondegenerate.ampliation` holds vacuously regardless of
`π`). -/
@[simp]
theorem isNondegenerate_ampliation_iff (ι : Type*) [Nonempty ι] (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    (π.ampliation ι).IsNondegenerate ↔ π.IsNondegenerate := by
  simp [ampliation]

end Ampliation

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {B ι H₀ : Type*} {H : ι → Type*} [CStarAlgebra B]
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] [∀ i, CompleteSpace (H i)]

/-- Unital **Hilbert direct sum** of a family of unital representations on `lp H 2`. -/
def hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    B →⋆ₐ[ℂ] (lp H 2 →L[ℂ] lp H 2) :=
  ((NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun i ↦
    (π i).isNondegenerate_toNonUnitalStarAlgHom).toStarAlgHom

@[simp]
theorem toNonUnitalStarAlgHom_hilbertSum (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    (hilbertSum π).toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.hilbertSum fun i ↦ (π i).toNonUnitalStarAlgHom := by
  simp [hilbertSum]

theorem hilbertSum_apply_eq_mapCLM (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    hilbertSum π b =
      lp.mapCLM 2 (fun i ↦ π i b) (norm_nonneg b)
        (fun i ↦ NonUnitalStarAlgHom.norm_apply_le (π i) b) := by
  simp [hilbertSum, NonUnitalStarAlgHom.hilbertSum_apply_eq_mapCLM]

@[simp]
theorem hilbertSum_apply_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) (x : lp H 2) (i : ι) :
    hilbertSum π b x i = π i b (x i) := by
  simp [hilbertSum]

@[simp]
theorem hilbertSum_apply_single [DecidableEq ι] (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B)
    (i : ι) (ξ : H i) :
    hilbertSum π b (lp.single 2 i ξ) = lp.single 2 i (π i b ξ) := by
  simp [← coe_toNonUnitalStarAlgHom]

/-- The operator norm of `StarAlgHom.hilbertSum π b` is the supremum of the summand norms
`‖π i b‖`. -/
theorem norm_hilbertSum_apply (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    ‖hilbertSum π b‖ = ⨆ i, ‖π i b‖ := by
  simp [← coe_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.norm_hilbertSum_apply]

/-- An element acts as zero in `StarAlgHom.hilbertSum π` if and only if it acts as zero in every
summand. -/
@[simp]
theorem hilbertSum_apply_eq_zero_iff (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (b : B) :
    hilbertSum π b = 0 ↔ ∀ i, π i b = 0 := by
  simp [← coe_toNonUnitalStarAlgHom]

/-- Forming the unital Hilbert direct sum of a family of representations is injective. -/
theorem hilbertSum_injective :
    Function.Injective (hilbertSum (B := B) (H := H)) := by
  classical
  intro π₁ π₂ h
  ext i b ξ
  simpa using congr($(h) b (lp.single 2 i ξ) i)

@[simp]
theorem hilbertSum_inj {π₁ π₂ : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)} :
    hilbertSum π₁ = hilbertSum π₂ ↔ π₁ = π₂ :=
  hilbertSum_injective.eq_iff

/-- A unital Hilbert direct sum of representations is injective if and only if the summands jointly
separate `0`. -/
theorem hilbertSum_injective_iff (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) :
    Function.Injective (hilbertSum π) ↔ ∀ ⦃b : B⦄, (∀ i, π i b = 0) → b = 0 := by
  simp [← StarAlgHom.coe_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.hilbertSum_injective_iff]

/-- A unital Hilbert direct sum is injective as soon as one of its summands is injective. -/
theorem hilbertSum_injective_of_injective (π : ∀ i, B →⋆ₐ[ℂ] (H i →L[ℂ] H i)) (i : ι)
    (hi : Function.Injective (π i)) : Function.Injective (hilbertSum π) :=
  (hilbertSum_injective_iff π).2 fun _ hb ↦ (injective_iff_map_eq_zero (π i)).1 hi _ (hb i)

/-- Unital diagonal **ampliation** of a unital representation to `lp (fun _ : ι ↦ H₀) 2`. -/
def ampliation (ι : Type*) (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) :
    B →⋆ₐ[ℂ] (lp (fun _ : ι ↦ H₀) 2 →L[ℂ] lp (fun _ : ι ↦ H₀) 2) :=
  hilbertSum fun _ : ι ↦ π

@[simp]
theorem toNonUnitalStarAlgHom_ampliation (ι : Type*) (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) :
    (π.ampliation ι).toNonUnitalStarAlgHom = π.toNonUnitalStarAlgHom.ampliation ι := by
  simp [ampliation, NonUnitalStarAlgHom.ampliation]

theorem ampliation_apply_eq_ampliation (ι : Type*) (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) (b : B) :
    π.ampliation ι b = lp.ampliation ι 2 (π b) := by
  simp [← coe_toNonUnitalStarAlgHom, NonUnitalStarAlgHom.ampliation_apply_eq_ampliation]

@[simp]
theorem ampliation_apply_apply (ι : Type*) (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) (b : B)
    (x : lp (fun _ : ι ↦ H₀) 2) (i : ι) :
    π.ampliation ι b x i = π b (x i) := by
  simp [ampliation]

@[simp]
theorem ampliation_apply_single {ι : Type*} [DecidableEq ι] (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) (b : B)
    (i : ι) (ξ : H₀) :
    π.ampliation ι b (lp.single 2 i ξ) = lp.single 2 i (π b ξ) := by
  simp [← coe_toNonUnitalStarAlgHom]

/-- Over a nonempty index type `ι`, unital diagonal ampliation preserves operator norms. -/
@[simp]
theorem norm_ampliation_apply (ι : Type*) [Nonempty ι] (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) (b : B) :
    ‖π.ampliation ι b‖ = ‖π b‖ := by
  simp [← coe_toNonUnitalStarAlgHom]

/-- Over a nonempty index type `ι`, an element acts as zero in `π.ampliation ι` if and only if it
acts as zero in `π`. -/
@[simp]
theorem ampliation_apply_eq_zero_iff (ι : Type*) [Nonempty ι] (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀))
    (b : B) : π.ampliation ι b = 0 ↔ π b = 0 := by
  simp [← coe_toNonUnitalStarAlgHom]

/-- Over a nonempty index type `ι`, unital diagonal ampliation of representations is injective. -/
theorem ampliation_injective (ι : Type*) [Nonempty ι] :
    Function.Injective (ampliation ι : (B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) → _) := by
  intro π₁ π₂ h
  simpa using congr_fun (hilbertSum_injective h) (Classical.arbitrary ι)

@[simp]
theorem ampliation_inj (ι : Type*) [Nonempty ι] {π₁ π₂ : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)} :
    π₁.ampliation ι = π₂.ampliation ι ↔ π₁ = π₂ :=
  (ampliation_injective ι).eq_iff

/-- Over a nonempty index type `ι`, a unital diagonal ampliation `π.ampliation ι` is injective if
and only if `π` is injective. -/
@[simp]
theorem ampliation_injective_iff (ι : Type*) [Nonempty ι] (π : B →⋆ₐ[ℂ] (H₀ →L[ℂ] H₀)) :
    Function.Injective (π.ampliation ι) ↔ Function.Injective π := by
  simp [← StarAlgHom.coe_toNonUnitalStarAlgHom]

end StarAlgHom
