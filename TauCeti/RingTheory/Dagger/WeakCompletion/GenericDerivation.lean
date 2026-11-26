/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.CompletedGenericField.Derivation
public import TauCeti.RingTheory.Dagger.WeakCompletion.GenericFrobenius

/-!
# Weak-completion derivations on the completed generic field

Let `A` be a finitely generated `O`-algebra, `ϖ ∈ O` an element whose image `π` in `A` generates a
prime ideal, `A†` the Monsky–Washnitzer weak completion of `A` along `ϖ`, and `Ô` the completed
generic ring of `A` at `(π)`, with its canonical map `A† → Ô`. An `O`-derivation `D` of `A†`
restricts to an `O`-derivation `A → Ô`, which extends uniquely to a derivation of `Ô` and, when
`A` is Noetherian and `π` a nonzerodivisor, to a derivation of the completed generic field
`E = Ô[1/π]`, unique among those mapping the valuation ring into itself
(`eq_completedGenericFieldDerivationLift`). This extension is compatible with `D` on all of
`A†`, not only on `A`: the canonical maps `A† → Ô → E` intertwine `D` with the extended
derivations.

For a smooth affine lift `A` of a curve, with dagger algebra `A†`, this compares the derivation of
`A†` with its generic realisation on `E`, which is what scalar extension of a module with
connection over `A†` to the completed generic field requires. The Frobenius counterpart is
`TauCeti.Dagger.weakCompletion.completedGenericFieldFrobenius`.

No continuity of `D` is assumed: an `O`-derivation commutes with multiplication by `ϖ`, every
element of `A†` is congruent to an element of `A` modulo `ϖ ^ n A†`, and `Ô` is `π`-adically
separated.

## Main definitions and results

* `TauCeti.Dagger.weakCompletion.affineDerivation`: the restriction of a derivation of `A†` to `A`,
  with values in `Ô`.
* `TauCeti.Dagger.weakCompletion.completedGenericIntegersDerivationLift_toCompletedGenericIntegers`:
  the extended derivation of `Ô` agrees with `D` on the image of `A†`. Since the derivation of `E`
  restricts to that of `Ô`
  (`completedGenericFieldDerivationLift_algebraMap_completedGenericIntegers`), the same holds for
  `E` by `simp`.

## References

* [N. Tsuzuki, *Minimal slope conjecture of F-isocrystals*](https://arxiv.org/abs/1910.03871v3),
  §3.1.
-/

public section

namespace TauCeti.Dagger.weakCompletion

open TauCeti.AdicCompletion

variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O A]
  (ϖ : O) [Algebra.FiniteType O A] [(Ideal.span {algebraMap O A ϖ}).IsPrime]

local notation "π" => algebraMap O A ϖ
local notation "C" => completedGenericIntegers π
local notation "W" => Dagger.weakCompletion ϖ A

/-- The restriction of an `O`-derivation of the weak completion to the affine algebra, with
values in the completed generic ring through the canonical map. -/
noncomputable def affineDerivation (D : Derivation O W W) : Derivation O A C :=
  Derivation.mk' ((toCompletedGenericIntegers ϖ).toLinearMap ∘ₗ D.toLinearMap ∘ₗ
      (Dagger.weakCompletion.of ϖ A).toLinearMap) fun a b ↦ by
    simp [Algebra.smul_def]

/-- The affine restriction of `D` evaluates `D` on the weak completion. -/
@[simp]
theorem affineDerivation_apply (D : Derivation O W W) (a : A) :
    affineDerivation ϖ D a =
      toCompletedGenericIntegers ϖ (D (Dagger.weakCompletion.of ϖ A a)) :=
  (rfl)

/-- The extension to the completed generic ring of the affine restriction of a derivation `D` of
the weak completion agrees with `D` on the whole weak completion. -/
@[simp]
theorem completedGenericIntegersDerivationLift_toCompletedGenericIntegers
    (D : Derivation O W W) (z : W) :
    completedGenericIntegersDerivationLift π (affineDerivation ϖ D)
        (toCompletedGenericIntegers ϖ z) =
      toCompletedGenericIntegers ϖ (D z) := by
  let j := (toCompletedGenericIntegers ϖ (A := A)).toLinearMap
  -- the difference of the two sides is an `O`-linear map vanishing on `A`
  let Δ : W →ₗ[O] C :=
    (completedGenericIntegersDerivationLift π (affineDerivation ϖ D)).toLinearMap ∘ₗ j -
      j ∘ₗ D.toLinearMap
  have hΔ (a : A) : Δ (Dagger.weakCompletion.of ϖ A a) = 0 := by
    simp [Δ, j]
  suffices Δ z = 0 by simpa [Δ, j, sub_eq_zero] using this
  have := isAdicComplete_completedGenericIntegers π
  refine IsHausdorff.haus' (I := Ideal.span {algebraMap A C π}) _ fun n ↦ ?_
  -- write `z = a + ϖ ^ n * y` with `a ∈ A`
  obtain ⟨a, ha⟩ := Dagger.weakCompletion.exists_sub_mem_span_pow ϖ z n
  obtain ⟨y, rfl⟩ : ∃ y, z = Dagger.weakCompletion.of ϖ A a + ϖ ^ n • y := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨y, hy⟩ := ha
    exact ⟨y, by rw [Algebra.smul_def, map_pow, mul_comm, hy, add_sub_cancel]⟩
  -- `Δ` is `O`-linear and vanishes on `A`, so `Δ z = ϖ ^ n • Δ y`
  rw [map_add, hΔ, zero_add, map_smul, SModEq.zero, ← algebraMap_smul C (ϖ ^ n), map_pow,
    IsScalarTower.algebraMap_apply O A C]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) trivial

end TauCeti.Dagger.weakCompletion
