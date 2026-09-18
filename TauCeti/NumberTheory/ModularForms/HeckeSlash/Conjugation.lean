/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Independence

import Mathlib.Tactic.Group
import TauCeti.GroupTheory.DoubleCoset.Normalizer

/-!
# Conjugating a double-coset slash sum

Let `g` normalize `Γ₁` and `Γ₂`, and suppose that conjugation by `g` carries the double coset
`Γ₁ δ Γ₂` into itself, i.e. `g⁻¹ δ g ∈ Γ₁ δ Γ₂`. Then conjugation by `g` permutes the right cosets
`Γ₁ aᵥ` that `Γ₁ δ Γ₂` decomposes into, `Γ₁ aᵥ ↦ Γ₁ (g⁻¹ aᵥ g)`, and so for a `Γ₁`-invariant `f`

`(∑ᵥ f ∣[k] aᵥ) ∣[k] g = ∑ᵥ (f ∣[k] g) ∣[k] (g⁻¹ aᵥ g)`.

The right-hand side is again the slash sum of `Γ₁ δ Γ₂`, now applied to `f ∣[k] g`, which is
`Γ₁`-invariant because `g` normalizes `Γ₁`: the slash by `g` intertwines the Hecke operator
`[Γ₁ δ Γ₂]` with itself. This is the mechanism by which an operator given by an element of the
normalizer — an Atkin–Lehner or Fricke involution of `Γ₀(N)`, say — commutes with the Hecke
operators whose double cosets it fixes.

## Main results

* `HeckeRing.GL2.heckeSlashSum_slash_of_mem_normalizer`: for `g` normalizing `Γ₁` and `Γ₂` with
  `g⁻¹ δ g ∈ Γ₁ δ Γ₂`, `heckeSlashSum k D f ∣[k] g = heckeSlashSum k D (f ∣[k] g)`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix UpperHalfPlane DoubleCoset

open scoped ModularForm Pointwise

namespace HeckeRing.GL2

variable (k : ℤ) {Δ : Submonoid (GL (Fin 2) ℚ)} {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)}
  (D : HeckeCoset Δ Γ₁ Γ₂) [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
  {g : GL (Fin 2) ℚ}

/-- **The slash by an element of the normalizers commutes with a Hecke operator whose double
coset it fixes.** If `g` normalizes `Γ₁` and `Γ₂` and `g⁻¹ δ g ∈ Γ₁ δ Γ₂`, where `δ` represents
`D`, then for every `Γ₁`-invariant `f`,

`heckeSlashSum k D f ∣[k] g = heckeSlashSum k D (f ∣[k] g)`.

No positivity is asked of `g`: the slash action of `GL(2, ℚ)` is a monoid action whatever the
sign of the determinant, and that is all the comparison uses. -/
theorem heckeSlashSum_slash_of_mem_normalizer
    (hg₁ : g ∈ Subgroup.normalizer (Γ₁ : Set (GL (Fin 2) ℚ)))
    (hg₂ : g ∈ Subgroup.normalizer (Γ₂ : Set (GL (Fin 2) ℚ)))
    (hD : g⁻¹ * D.out * g ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ₁, f ∣[k] γ = f) :
    heckeSlashSum k D f ∣[k] g = heckeSlashSum k D (f ∣[k] g) := by
  classical
  let _ : Fintype (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹) := Fintype.ofFinite _
  have hdc : doubleCoset (g⁻¹ * D.out * g) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂ =
      doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂ :=
    doubleCoset_eq_of_mem hD
  -- `f ∣[k] g` is again `Γ₁`-invariant, since `g γ = (g γ g⁻¹) g`
  have hfg : ∀ γ ∈ Γ₁, (f ∣[k] g) ∣[k] γ = f ∣[k] g := fun γ hγ ↦ by
    have hmul : g * γ = g * γ * g⁻¹ * g := by group
    rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
      hf _ ((Subgroup.mem_normalizer_iff.mp hg₁ γ).mp hγ)]
  -- the conjugated representatives decompose the same double coset
  have hcover : doubleCoset (D.out : GL (Fin 2) ℚ) (Γ₁ : Set (GL (Fin 2) ℚ)) Γ₂ =
      ⋃ v, MulOpposite.op (g⁻¹ * rightCosetRep D v * g) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    ext x
    have hconj : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    simp only [Set.mem_iUnion, mem_rightCoset_conj_iff_of_mem_normalizer hg₁]
    rw [← Set.mem_iUnion (s := fun v ↦ MulOpposite.op (rightCosetRep D v) •
      (Γ₁ : Set (GL (Fin 2) ℚ))), ← doubleCoset_eq_iUnion_rightCosetRep,
      ← conj_mem_doubleCoset_conj_iff_of_mem_normalizer hg₁ hg₂ _ (g * x * g⁻¹), hdc,
      hconj]
  have hinj : Function.Injective fun v ↦
      MulOpposite.op (g⁻¹ * rightCosetRep D v * g) • (Γ₁ : Set (GL (Fin 2) ℚ)) := by
    refine fun v w h ↦ op_rightCosetRep_smul_injective D ?_
    have h' := (rightCoset_eq_iff Γ₁).mp h
    refine (rightCoset_eq_iff Γ₁).mpr ?_
    have hmem := (Subgroup.mem_normalizer_iff.mp hg₁ _).mp h'
    exact (congrArg (· ∈ Γ₁) (by group)).mp hmem
  rw [heckeSlashSum_eq_sum_of_rightCosets k D _ hcover hinj _ hfg, heckeSlashSum_def,
    SlashAction.sum_slash]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
  exact congrArg (f ∣[k] ·) (by group)

end HeckeRing.GL2
