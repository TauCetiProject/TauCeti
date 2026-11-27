/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Diagonal

import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The row `0 → A → A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩ → 0`

Let `A` be a nonarchimedean commutative ring. For the full short exact row, assume moreover that
`A` is complete and separated; the individual constructions and injectivity use weaker
hypotheses. Wedhorn's ring of the overlap of a two-piece Laurent cover is

```text
A⟨ζ, ζ⁻¹⟩ = A⟨X, Y⟩ ⧸ (1 - XY),
```

the quotient of the restricted power series in two variables by `TauCeti.Huber.laurentIdeal`. In
it the class of `X` is a unit with inverse the class of `Y`
(`TauCeti.Huber.isUnit_mk_weightedX_zero`), which is what the notation `ζ⁻¹` refers to.

The two pieces `A⟨ζ⟩` and `A⟨η⟩` are copies of the restricted power series in one variable, mapped
into `A⟨X, Y⟩` by `ζ ↦ X` and `η ↦ Y` (`TauCeti.Huber.weightedRename` along `Fin.castSuccEmb` and
`Fin.succEmb 1`). This file assembles them into the row

```text
0 → A --ι--> A⟨ζ⟩ × A⟨η⟩ --λ--> A⟨ζ, ζ⁻¹⟩ → 0,
```

with `ι` the constants on both pieces — the structure map of the product `A`-algebra — and
`λ (g, h) = g(ζ) - h(ζ⁻¹)`, and proves that it is exact: `ι` is injective, `λ` is surjective, and
the kernel of `λ` is the image of `ι`. The two substantial inputs are the decomposition
`A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩` and the rigidity of the overlap — a series in `ζ` agreeing with a
series in `ζ⁻¹` is constant — both proved in
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Diagonal`; completeness of `A` enters only
through the first.

## Main definitions

* `TauCeti.Huber.laurentIdeal`: the ideal `(1 - XY)` of `A⟨X, Y⟩`.
* `TauCeti.Huber.laurentDiff`: the map `λ`. The map `ι` is the structure map of the product
  algebra `A⟨ζ⟩ × A⟨η⟩`, so it needs no definition of its own.

## Main results

* `TauCeti.Huber.algebraMap_prod_weightedRestrictedSubring_injective` and
  `TauCeti.Huber.laurentDiff_surjective`: the two ends of the row.
* `TauCeti.Huber.exact_algebraMap_laurentDiff`: exactness in the middle, `ker λ = im ι`.
* `TauCeti.Huber.isUnit_mk_weightedX_zero`: the class of `X` is a unit in `A⟨ζ, ζ⁻¹⟩`.
* `TauCeti.Huber.laurentIdeal_ne_top`: `A⟨ζ, ζ⁻¹⟩` is not the zero ring when `A` is not. In
  particular `1 - XY`, which is a unit in `A[[X, Y]]`, is not one in `A⟨X, Y⟩`.
* `TauCeti.Huber.apply_eq_apply_weightedRename` and
  `TauCeti.Huber.exists_sub_eq_of_surjective_of_map_laurentRelation_eq_zero`: continuous-square
  compatibility and diagram-chase surjectivity helpers for transferring `laurentDiff_surjective` to
  target models.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 6.39, (8.2.1) and the
  proof of Lemma 8.33, p. 84.

## Provenance

As recorded in the sibling file `…WeightedRestrictedSeries.Diagonal`, AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `37bbdaeb9`,
`projects/AdicSpaces/Adic spaces/LaurentCoverExact.lean`, assembles the same row for its
`LaurentTateAlgebra A := TateAlgebra₂ A ⧸ (XY - 1)`, out of homomorphisms `iotaHom` and
`lambdaMap` and the two statements `ker_lambdaMap_le_range_iotaHom` and `lambdaMap_surjective`.
Here the two inputs are the trivial-weight statements of `…Diagonal`, `ι` is the structure map of
the product algebra rather than a named homomorphism, and the row is packaged as
`Function.Exact`.
-/

public section

namespace TauCeti.Huber

variable (A : Type*) [CommRing A]

section Topological

variable [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The ideal `(1 - XY)` of `A⟨X, Y⟩`**, whose quotient is Wedhorn's ring `A⟨ζ, ζ⁻¹⟩` of the
overlap of a two-piece Laurent cover: killing `1 - XY` makes the class of `Y` inverse to the class
of `X`. -/
noncomputable def laurentIdeal :
    Ideal (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight) :=
  Ideal.span
    {1 - weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 *
      weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 1}

/-- Membership in `(1 - XY)` is divisibility by `1 - XY`. -/
theorem mem_laurentIdeal
    {u : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight} :
    u ∈ laurentIdeal A ↔ ∃ w, u =
      (1 - weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 *
        weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 1) * w :=
  Ideal.mem_span_singleton.trans dvd_def

/-- In `A⟨ζ, ζ⁻¹⟩`, the class of `Y` is a right inverse to the class of `X`. -/
@[simp]
theorem mk_weightedX_zero_mul_mk_weightedX_one :
    Ideal.Quotient.mk (laurentIdeal A)
        (weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 0) *
      Ideal.Quotient.mk (laurentIdeal A)
        (weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 1) = 1 := by
  rw [← map_mul, ← map_one (Ideal.Quotient.mk (laurentIdeal A)), Ideal.Quotient.eq,
    mem_laurentIdeal]
  exact ⟨-1, by ring⟩

/-- **The class of `X` is a unit in `A⟨ζ, ζ⁻¹⟩`**, with inverse the class of `Y`. This is what
makes the quotient a ring of Laurent, rather than of ordinary, restricted series. -/
theorem isUnit_mk_weightedX_zero :
    IsUnit (Ideal.Quotient.mk (laurentIdeal A)
      (weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 0)) :=
  IsUnit.of_mul_eq_one
    (Ideal.Quotient.mk (laurentIdeal A)
      (weightedX (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight 1))
    (mk_weightedX_zero_mul_mk_weightedX_one A)

/-- **Wedhorn's `λ : A⟨ζ⟩ × A⟨η⟩ → A⟨ζ, ζ⁻¹⟩`**, `(g, h) ↦ g(ζ) - h(ζ⁻¹)`: the difference of the
classes of `g` read in `X` and of `h` read in `Y`. It is additive but not multiplicative. -/
noncomputable def laurentDiff :
    ((weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) ×
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) →ₗ[A]
      (weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight ⧸
        laurentIdeal A) :=
  (Ideal.Quotient.mkₐ A (laurentIdeal A)).toLinearMap.comp
    ((weightedRenameAlgHom Fin.castSuccEmb isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ subset_rfl)).toLinearMap.comp
        (LinearMap.fst A _ _) -
      (weightedRenameAlgHom (Fin.succEmb 1) isWeightFamily_one_weight
          isWeightFamily_one_weight (fun _ ↦ subset_rfl)).toLinearMap.comp
        (LinearMap.snd A _ _))

@[simp]
theorem laurentDiff_apply
    (p : (weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) ×
      weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    laurentDiff A p = Ideal.Quotient.mk (laurentIdeal A)
      (weightedRename Fin.castSuccEmb isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ subset_rfl) p.1 -
        weightedRename (Fin.succEmb 1) isWeightFamily_one_weight isWeightFamily_one_weight
          (fun _ ↦ subset_rfl) p.2) := by
  simp [laurentDiff]

end Topological

section Separated

variable [TopologicalSpace A] [NonarchimedeanRing A] [T0Space A]

/-- **The row is exact in the middle**: a pair `(g, h)` with `g(ζ) = h(ζ⁻¹)` in `A⟨ζ, ζ⁻¹⟩` is a
pair of equal constants, and conversely. This is Wedhorn's `ker λ = im ι` in the proof of
Lemma 8.33. -/
theorem exact_algebraMap_laurentDiff :
    Function.Exact (algebraMap A
      ((weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) ×
        weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight))
      (laurentDiff A) := fun p ↦ by
  constructor
  · intro h
    rw [laurentDiff_apply, Ideal.Quotient.eq_zero_iff_mem, mem_laurentIdeal] at h
    obtain ⟨w, hw⟩ := h
    obtain ⟨c, hc₁, hc₂⟩ :=
      exists_eq_weightedC_of_weightedRename_sub_weightedRename_eq_one_sub_mul hw
    exact ⟨c, Prod.ext (by simp [hc₁]) (by simp [hc₂])⟩
  · rintro ⟨c, rfl⟩
    simp

/-- **`A⟨ζ, ζ⁻¹⟩` is not the zero ring** when `A` is not: the ideal `(1 - XY)` is proper. Note
that `1 - XY` *is* a unit in the ambient ring `A[[X, Y]]` of all power series, its inverse being
the series `∑ (XY)ⁿ`, which is not restricted. -/
theorem laurentIdeal_ne_top [Nontrivial A] : laurentIdeal A ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one, mem_laurentIdeal]
  rintro ⟨w, hw⟩
  obtain ⟨c, hc₁, hc₂⟩ :=
    exists_eq_weightedC_of_weightedRename_sub_weightedRename_eq_one_sub_mul
      (a := 1) (b := 0) (w := w) (by simpa using hw)
  rw [← map_one (weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight)] at hc₁
  rw [← map_zero (weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight)] at hc₂
  exact one_ne_zero ((weightedC_injective _ _ hc₁).trans (weightedC_injective _ _ hc₂).symm)

end Separated

section Square

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- A continuous ring homomorphism out of `A⟨T⟩` agrees with another out of `A⟨X, Y⟩` composed
with `weightedRename e` once they agree on constants `weightedC` and variables `weightedX`. -/
theorem apply_eq_apply_weightedRename {B B' : Type*} [Semiring B] [TopologicalSpace B]
    [Semiring B'] [TopologicalSpace B'] [T2Space B'] {e : Fin 1 ↪ Fin 2}
    {π : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+* B}
    {π' : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      B'} {ρ : B →+* B'} (hρ : Continuous ρ) (hπ : Continuous π) (hπ' : Continuous π')
    (hC : ∀ a, ρ (π (weightedC _ isWeightFamily_one_weight a)) =
      π' (weightedC _ isWeightFamily_one_weight a))
    (hX : ∀ i, ρ (π (weightedX _ isWeightFamily_one_weight i)) =
      π' (weightedX _ isWeightFamily_one_weight (e i)))
    (g : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ρ (π g) = π' (weightedRename e _ _ (fun _ ↦ subset_rfl) g) := by
  have key : ρ.comp π = π'.comp (weightedRename e _ _ (fun _ ↦ subset_rfl)) :=
    weightedRestrictedSubring_ringHom_ext_of_continuous _ (hρ.comp hπ)
      (hπ'.comp (continuous_weightedRename _ _ _ _)) (fun a ↦ by simp [hC]) (fun i ↦ by simp [hX])
  exact DFunLike.congr_fun key g

end Square

section Complete

variable [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A] [CompleteSpace A]
  [T0Space A]

/-- **`λ` is surjective**: every element of `A⟨ζ, ζ⁻¹⟩` is `g(ζ) - h(ζ⁻¹)`. This is Wedhorn's
decomposition `A⟨ζ, ζ⁻¹⟩ = A⟨ζ⟩ + ζ⁻¹A⟨ζ⁻¹⟩`, read through `λ`. -/
theorem laurentDiff_surjective : Function.Surjective (laurentDiff A) := by
  intro u
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  -- `u = a(X) + Y · b(Y) + (1 - XY) w`, and renaming carries `X · b` to `Y · b(Y)`, so `u` is
  -- the class of `λ (a, -X · b)`
  obtain ⟨a, b, w, hu⟩ :=
    exists_eq_weightedRename_add_weightedX_mul_weightedRename_add_one_sub_mul u
  refine ⟨(a, -(weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0 * b)), ?_⟩
  rw [laurentDiff_apply, Ideal.Quotient.eq, mem_laurentIdeal]
  have hsucc : (Fin.succEmb 1) 0 = 1 := by decide
  exact ⟨-w, by rw [hu, map_neg, map_mul, weightedRename_weightedX, hsucc]; ring⟩

end Complete

section

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [NonarchimedeanRing A]
  [CompleteSpace A] [T0Space A]

/-- Surjectivity of `(x₁, x₂) ↦ ρ₁ x₁ - ρ₂ x₂` transferred from `laurentDiff_surjective`: if
`π₁₂` is surjective, kills `1 - X₀ X₁`, and intertwines `π₁`, `π₂` with `ρ₁`, `ρ₂` via
`weightedRename`, then `(x₁, x₂) ↦ ρ₁ x₁ - ρ₂ x₂` is surjective. -/
theorem exists_sub_eq_of_surjective_of_map_laurentRelation_eq_zero
    {B₁ B₂ B₁₂ : Type*} [CommRing B₁] [CommRing B₂] [CommRing B₁₂]
    {π₁ : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      B₁}
    {π₂ : weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      B₂}
    {π₁₂ : weightedRestrictedSubring (fun _ : Fin 2 ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      B₁₂} {ρ₁ : B₁ →+* B₁₂} {ρ₂ : B₂ →+* B₁₂} (hπ₁₂ : Function.Surjective π₁₂)
    (hsq₁ : ∀ g, ρ₁ (π₁ g) = π₁₂ (weightedRename Fin.castSuccEmb _ _ (fun _ ↦ subset_rfl) g))
    (hsq₂ : ∀ h, ρ₂ (π₂ h) = π₁₂ (weightedRename (Fin.succEmb 1) _ _ (fun _ ↦ subset_rfl) h))
    (hXY : π₁₂ (1 - weightedX _ isWeightFamily_one_weight 0 *
      weightedX _ isWeightFamily_one_weight 1) = 0) (y : B₁₂) :
    ∃ (x₁ : B₁) (x₂ : B₂), ρ₁ x₁ - ρ₂ x₂ = y := by
  obtain ⟨u, rfl⟩ := hπ₁₂ y
  obtain ⟨⟨g, h⟩, hgh⟩ := laurentDiff_surjective A (Ideal.Quotient.mk (laurentIdeal A) u)
  rw [laurentDiff_apply, Ideal.Quotient.eq, mem_laurentIdeal] at hgh
  obtain ⟨w, hw⟩ := hgh
  exact ⟨π₁ g, π₂ h, by
    rw [hsq₁, hsq₂, ← map_sub, ← sub_eq_zero, ← map_sub, hw, map_mul, hXY, zero_mul]⟩

end

end TauCeti.Huber
