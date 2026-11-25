/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.AlgebraicIndependent.BaseChange
import TauCeti.RingTheory.AlgebraicIndependent.ValuationRing
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Fibre dimensions of a flat finitely generated algebra over a valuation ring

Let `A` be a finitely generated torsion-free algebra over a valuation ring `R`, for instance a flat
finitely generated algebra over a discrete valuation ring. Every fibre `κ(p) ⊗[R] A` of
`Spec A → Spec R` has Krull dimension at most that of the generic fibre `K ⊗[R] A`, where `K` is
the fraction field of `R` (`Ideal.ringKrullDim_fiber_le_ringKrullDim_fiber_bot`).

The Krull dimension of a finitely generated algebra over a field is the largest number of its
elements algebraically independent over the field, and these can be chosen among any generators.
So if `κ(p) ⊗[R] A` has dimension `n`, there are `a₁, …, aₙ ∈ A` with the `1 ⊗ aᵢ` algebraically
independent over `κ(p)`. Over a valuation ring, the `aᵢ` are then algebraically independent over
`R` (`AlgebraicIndependent.of_comp_of_valuationRing`), and the `1 ⊗ aᵢ` are algebraically
independent over `K` in the generic fibre, since `K` is flat over `R`.

Geometrically, a scheme flat and locally of finite type over a valuation ring has no fibre of
larger dimension than its generic fibre. For models of curves over a discrete valuation ring this
bounds the dimension of the special fibre by one.

Torsion-freeness is necessary: `A = R ⧸ 𝔪` has a special fibre of dimension `0` and an empty
generic fibre. Finiteness is necessary too: a valuation ring `A` of rank two of `K(x)` with
`v(π) = (1, 0)` and `v(x) = (0, 1)` is torsion-free over a discrete valuation ring `R` with
uniformizer `π`, and its special fibre has dimension one while its generic fibre is a field.
-/

public section

open scoped TensorProduct

namespace Ideal

/-- **Fibre dimensions over a valuation ring.** Let `A` be a finitely generated torsion-free
algebra over a valuation ring `R`, for instance a flat finitely generated algebra over a discrete
valuation ring. Every fibre `κ(p) ⊗[R] A` of `Spec A → Spec R` has Krull dimension at most that
of the generic fibre `Frac R ⊗[R] A`. -/
theorem ringKrullDim_fiber_le_ringKrullDim_fiber_bot {R A : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [Module.IsTorsionFree R A] (p : Ideal R) [p.IsPrime] :
    ringKrullDim (p.Fiber A) ≤ ringKrullDim ((⊥ : Ideal R).Fiber A) := by
  rcases subsingleton_or_nontrivial (p.Fiber A) with h | h
  · simp [ringKrullDim_eq_bot_of_subsingleton]
  -- By Noether normalization, `dim (κ(p) ⊗[R] A)` is a natural number `n`.
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg p.ResidueField (p.Fiber A)
  have hn := TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g.toRingHom hinj hint
  rw [Nat.card_fin] at hn
  -- Some `n` elements `1 ⊗ aᵢ` of `κ(p) ⊗[R] A` are algebraically independent over `κ(p)`; then
  -- the `aᵢ` are algebraically independent over `R`, and the `1 ⊗ aᵢ` in the generic fibre over
  -- the fraction field `κ(⊥)` of `R`.
  obtain ⟨y, hys, hy⟩ := TauCeti.exists_algebraicIndependent_of_le_ringKrullDim p.ResidueField
    (Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := p.ResidueField) (Set.univ : Set A)
      (Algebra.adjoin_univ R A)) hn.ge
  simp only [Set.image_univ, Set.mem_range] at hys
  choose a ha using hys
  have hy' : AlgebraicIndependent p.ResidueField
      fun i ↦ (Algebra.TensorProduct.includeRight : A →ₐ[R] p.Fiber A) (a i) := by
    simpa [ha] using hy
  have := IsLocalization.flat (⊥ : Ideal R).ResidueField (nonZeroDivisors R)
  rw [hn]
  simpa using
    (hy'.of_comp_of_valuationRing.one_tmul (⊥ : Ideal R).ResidueField).natCard_le_ringKrullDim

end Ideal
