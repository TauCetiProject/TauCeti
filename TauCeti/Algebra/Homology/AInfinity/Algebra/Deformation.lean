/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Cohomology
import Mathlib.Algebra.Polynomial.Coeff

/-!
# Formal deformations of `A∞` structures and their obstructions

Let `m` be the suspended Taylor map of an `A∞` algebra `𝒜`, a suspended Hochschild cochain of
degree one satisfying the brace equation `m{m} = 0`.  Following Gerstenhaber, a formal deformation
of `𝒜` is a power series `mₜ = m + t φ₁ + t² φ₂ + ⋯` of suspended Hochschild cochains of degree one
which again satisfies the brace equation `mₜ{mₜ} = 0`.  Since the brace is bilinear, the
coefficient of `tᵏ` in `mₜ{mₜ}` is

`∑_{i + j = k} φᵢ{φⱼ}`,                                       (`deformationBrace`)

with `φ₀ = m`, so the brace equation is a sequence of equations in the cochains themselves.  A
family `φ` is a **deformation of order `n`** (`IsDeformationOfOrder`) when `φ₀ = m`, the
coefficients `φ₁, …, φₙ` have degree one, and these equations hold for `k ≤ n`, that is
`mₜ{mₜ} = 0` modulo `tⁿ⁺¹`.  It is a **formal deformation** (`IsFormalDeformation`) when it is a
deformation of every order.  Everything is phrased with braces, without any division, so it works
over every commutative ring.

The coefficient of `tⁿ⁺¹` splits as

`∑_{i + j = n + 1} φᵢ{φⱼ} = Oₙ + [m, φₙ₊₁]`,                         (`deformationBrace_succ`)

where `[m, -]` is the Hochschild differential and the **obstruction**
`Oₙ = ∑_{i + j = n + 1, 1 ≤ i, j ≤ n} φᵢ{φⱼ}` (`deformationObstruction`) is the coefficient of
`tⁿ⁺¹` in the brace square of the truncation `m + t φ₁ + ⋯ + tⁿ φₙ`.  Hence a deformation of order
`n` extends to order `n + 1` exactly when `[m, φₙ₊₁] = -Oₙ`
(`IsDeformationOfOrder.isDeformationOfOrder_succ_iff`).  For `n = 0` the obstruction vanishes:
first-order deformations are the Hochschild cocycles of degree one
(`isDeformationOfOrder_one_iff`).

The obstruction of a deformation of order `n` is a Hochschild cocycle of degree two
(`IsDeformationOfOrder.hochschildDifferential_deformationObstruction`).  So the obstruction has a
class in the positive-arity Hochschild cohomology of degree two
(`IsDeformationOfOrder.obstructionClass`), and the deformation extends to order `n + 1`, after
changing only `φₙ₊₁`, exactly when this class vanishes
(`IsDeformationOfOrder.obstructionClass_eq_zero_iff`).  In particular, if this cohomology group
vanishes then every deformation of order `n` extends to a formal deformation
(`IsDeformationOfOrder.exists_isFormalDeformation`).

Degrees are suspended degrees: an arity-`n` component of internal degree `r` has cochain degree
`r + n - 1`.  For an algebra concentrated in degree zero, a cochain of degree one has only an
arity-two component and a cochain of degree two only an arity-three component, so the
coefficients `φᵢ` are, up to the signs of the suspension, Gerstenhaber's two-cochains deforming
the multiplication, and the obstruction is his three-cochain.

## Main definitions

* `TauCeti.AInfinityAlgebra.deformationBrace`: the coefficient `∑_{i + j = k} φᵢ{φⱼ}` of the brace
  square of a power series of cochains.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder`: a deformation of order `n`.
* `TauCeti.AInfinityAlgebra.IsFormalDeformation`: a formal deformation.
* `TauCeti.AInfinityAlgebra.deformationObstruction`: the obstruction to extending a deformation of
  order `n` to order `n + 1`.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder.obstructionClass`: its Hochschild cohomology
  class.

## Main results

* `TauCeti.AInfinityAlgebra.deformationBrace_succ`: the coefficient of `tⁿ⁺¹` is the obstruction
  plus the Hochschild differential of `φₙ₊₁`.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder.isDeformationOfOrder_succ_iff`: a deformation of
  order `n` is one of order `n + 1` exactly when `[m, φₙ₊₁] = -Oₙ`.
* `TauCeti.AInfinityAlgebra.isDeformationOfOrder_one_iff`: first-order deformations are degree-one
  Hochschild cocycles.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder.hochschildDifferential_deformationObstruction`:
  the obstruction is a Hochschild cocycle.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder.obstructionClass_eq_zero_iff`: a deformation of
  order `n` extends to order `n + 1` exactly when its obstruction class vanishes.
* `TauCeti.AInfinityAlgebra.IsDeformationOfOrder.exists_isFormalDeformation`: if the Hochschild
  cohomology of degree two vanishes, every deformation of order `n` extends to a formal
  deformation.

## References

* M. Gerstenhaber, *On the deformation of rings and algebras*, Annals of Mathematics 79 (1964),
  59--103, Sections 1.1--1.4.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for braces and the coderivation description of the Hochschild complex.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  (𝒜 : AInfinityAlgebra R A)

/-! ### The brace square of a power series of cochains -/

/-- The coefficient `∑_{i + j = k} φ i {φ j}` of `tᵏ` in the brace square `mₜ{mₜ}` of the power
series `mₜ = ∑ tⁱ φ i` of suspended Hochschild cochains of degree one. -/
noncomputable def deformationBrace (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) (k : ℕ) :
    ReducedTensorWords R A →ₗ[R] A :=
  ∑ x ∈ Finset.antidiagonal k, brace (𝒜.grading.shift 1) (φ x.1) (φ x.2) 1

theorem deformationBrace_def (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) (k : ℕ) :
    𝒜.deformationBrace φ k =
      ∑ x ∈ Finset.antidiagonal k, brace (𝒜.grading.shift 1) (φ x.1) (φ x.2) 1 :=
  (rfl)

/-- The constant coefficient of the brace square is `φ₀{φ₀}`. -/
@[simp]
theorem deformationBrace_zero (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) :
    𝒜.deformationBrace φ 0 = brace (𝒜.grading.shift 1) (φ 0) (φ 0) 1 := by
  simp [deformationBrace_def]

/-- The coefficient of `tᵏ` only depends on the coefficients `φ 0, …, φ k`. -/
theorem deformationBrace_congr {φ ψ : ℕ → ReducedTensorWords R A →ₗ[R] A} {k : ℕ}
    (h : ∀ i ≤ k, φ i = ψ i) : 𝒜.deformationBrace φ k = 𝒜.deformationBrace ψ k := by
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [h x.1 (by omega), h x.2 (by omega)]

/-- If `φ 0, …, φ k` have degree one, the coefficient of `tᵏ` has degree two. -/
theorem deformationBrace_mem_cochains {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} {k : ℕ}
    (h : ∀ i ≤ k, φ i ∈ PositiveHochschild.cochains 𝒜 1) :
    𝒜.deformationBrace φ k ∈ PositiveHochschild.cochains 𝒜 2 := by
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [PositiveHochschild.mem_cochains, ← one_add_one_eq_two]
  exact isHomogeneous_brace ((PositiveHochschild.mem_cochains 𝒜).1 (h x.1 (by omega)))
    ((PositiveHochschild.mem_cochains 𝒜).1 (h x.2 (by omega)))

/-! ### Deformations of finite order and formal deformations -/

/-- The family `φ` is a **deformation of order `n`** of the `A∞` algebra `𝒜`: the power series
`mₜ = ∑ tⁱ φ i` has constant term the suspended Taylor map `m` of `𝒜`, its coefficients up to
order `n` are suspended Hochschild cochains of degree one, and it satisfies the brace equation
`mₜ{mₜ} = 0` modulo `tⁿ⁺¹`.  Only the coefficients `φ 0, …, φ n` matter
(`IsDeformationOfOrder.congr`). -/
structure IsDeformationOfOrder (n : ℕ) (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) : Prop where
  /-- The constant term is the Taylor map of `𝒜`. -/
  zero_eq : φ 0 = 𝒜.taylor
  /-- The coefficients up to order `n` have degree one. -/
  mem_cochains : ∀ i ≤ n, φ i ∈ PositiveHochschild.cochains 𝒜 1
  /-- The brace equation holds modulo `tⁿ⁺¹`. -/
  deformationBrace_eq_zero : ∀ k ≤ n, 𝒜.deformationBrace φ k = 0

/-- The family `φ` is a **formal deformation** of `𝒜`: the power series `mₜ = ∑ tⁱ φ i` has
constant term `m`, all its coefficients have degree one, and it satisfies `mₜ{mₜ} = 0`. -/
def IsFormalDeformation (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) : Prop :=
  ∀ n, 𝒜.IsDeformationOfOrder n φ

theorem isFormalDeformation_iff {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} :
    𝒜.IsFormalDeformation φ ↔ ∀ n, 𝒜.IsDeformationOfOrder n φ :=
  Iff.rfl

variable {𝒜}

/-- A deformation of order `n` is one of every smaller order. -/
theorem IsDeformationOfOrder.mono {n n' : ℕ} {φ : ℕ → ReducedTensorWords R A →ₗ[R] A}
    (h : 𝒜.IsDeformationOfOrder n' φ) (hn : n ≤ n') : 𝒜.IsDeformationOfOrder n φ :=
  ⟨h.zero_eq, fun i hi ↦ h.mem_cochains i (hi.trans hn),
    fun k hk ↦ h.deformationBrace_eq_zero k (hk.trans hn)⟩

/-- Being a deformation of order `n` only depends on the coefficients `φ 0, …, φ n`. -/
theorem IsDeformationOfOrder.congr {n : ℕ} {φ ψ : ℕ → ReducedTensorWords R A →ₗ[R] A}
    (h : 𝒜.IsDeformationOfOrder n φ) (hφψ : ∀ i ≤ n, φ i = ψ i) :
    𝒜.IsDeformationOfOrder n ψ :=
  ⟨hφψ 0 (Nat.zero_le n) ▸ h.zero_eq, fun i hi ↦ hφψ i hi ▸ h.mem_cochains i hi,
    fun k hk ↦ by
      rw [← 𝒜.deformationBrace_congr fun i hi ↦ hφψ i (hi.trans hk)]
      exact h.deformationBrace_eq_zero k hk⟩

/-- A deformation of order zero is just a family with constant term `m`: the brace equation
modulo `t` is `m{m} = 0`. -/
@[simp]
theorem isDeformationOfOrder_zero_iff {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} :
    𝒜.IsDeformationOfOrder 0 φ ↔ φ 0 = 𝒜.taylor := by
  refine ⟨fun h ↦ h.zero_eq, fun h ↦ ⟨h, fun i hi ↦ ?_, fun k hk ↦ ?_⟩⟩
  · rw [Nat.le_zero.1 hi, h]
    exact PositiveHochschild.taylor_mem_cochains 𝒜
  · rw [Nat.le_zero.1 hk, deformationBrace_zero, h, brace_taylor_taylor]

/-! ### The obstruction -/

variable (𝒜) in
/-- The **obstruction** to extending a deformation of order `n` to order `n + 1`: the coefficient
`∑_{i + j = n + 1, 1 ≤ i, j ≤ n} φ i {φ j}` of `tⁿ⁺¹` in the brace square of the truncated series
`∑_{i ≤ n} tⁱ φ i`. -/
noncomputable def deformationObstruction (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) (n : ℕ) :
    ReducedTensorWords R A →ₗ[R] A :=
  𝒜.deformationBrace (fun i ↦ if i ≤ n then φ i else 0) (n + 1)

theorem deformationObstruction_def (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) (n : ℕ) :
    𝒜.deformationObstruction φ n =
      𝒜.deformationBrace (fun i ↦ if i ≤ n then φ i else 0) (n + 1) :=
  (rfl)

/-- The obstruction only depends on the coefficients `φ 0, …, φ n`. -/
theorem deformationObstruction_congr {φ ψ : ℕ → ReducedTensorWords R A →ₗ[R] A} {n : ℕ}
    (h : ∀ i ≤ n, φ i = ψ i) : 𝒜.deformationObstruction φ n = 𝒜.deformationObstruction ψ n := by
  rw [deformationObstruction_def, deformationObstruction_def]
  refine 𝒜.deformationBrace_congr fun i _ ↦ ?_
  split_ifs with hi
  exacts [h i hi, rfl]

/-- There is no obstruction to first-order deformations. -/
@[simp]
theorem deformationObstruction_zero (φ : ℕ → ReducedTensorWords R A →ₗ[R] A) :
    𝒜.deformationObstruction φ 0 = 0 := by
  simp [deformationObstruction_def, deformationBrace_def, Finset.Nat.sum_antidiagonal_succ]

/-- If `φ 0, …, φ n` have degree one, the obstruction has degree two. -/
theorem deformationObstruction_mem_cochains {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} {n : ℕ}
    (h : ∀ i ≤ n, φ i ∈ PositiveHochschild.cochains 𝒜 1) :
    𝒜.deformationObstruction φ n ∈ PositiveHochschild.cochains 𝒜 2 :=
  𝒜.deformationBrace_mem_cochains fun i _ ↦ by
    split_ifs with hi
    exacts [h i hi, zero_mem _]

/-- **The coefficient of `tⁿ⁺¹` of the brace square** is the obstruction of the truncation at
order `n` plus the Hochschild differential `[m, φ (n + 1)] = m{φ (n + 1)} + φ (n + 1){m}`. -/
theorem deformationBrace_succ {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h₀ : φ 0 = 𝒜.taylor)
    (n : ℕ) :
    𝒜.deformationBrace φ (n + 1) =
      𝒜.deformationObstruction φ n + 𝒜.hochschildDifferential 1 (φ (n + 1)) := by
  set G := 𝒜.grading.shift 1
  -- Only the two extreme terms `m{φ (n + 1)}` and `φ (n + 1){m}` involve `φ (n + 1)`.
  have key : ∀ x ∈ Finset.antidiagonal (n + 1), brace G (φ x.1) (φ x.2) 1 =
      brace G (if x.1 ≤ n then φ x.1 else 0) (if x.2 ≤ n then φ x.2 else 0) 1 +
        ((if x = (0, n + 1) then brace G (φ 0) (φ (n + 1)) 1 else 0) +
          (if x = (n + 1, 0) then brace G (φ (n + 1)) (φ 0) 1 else 0)) := by
    rintro ⟨a, b⟩ hx
    rw [Finset.mem_antidiagonal] at hx
    dsimp only
    by_cases ha : a = 0
    · obtain rfl : b = n + 1 := by omega
      simp [ha]
    by_cases hb : b = 0
    · obtain rfl : a = n + 1 := by omega
      simp [hb]
    · simp [ha, hb, show a ≤ n by omega, show b ≤ n by omega]
  -- Split the sum into the truncated part and the two extreme terms.
  rw [deformationBrace_def, Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_add_distrib, deformationObstruction_def, deformationBrace_def]
  congr 1
  -- The extreme terms form the Hochschild differential of `φ (n + 1)`.
  simp [hochschildDifferential_eq_brace_sub, h₀, G]

/-- **Extending a deformation by one order.**  A deformation of order `n` is a deformation of
order `n + 1` exactly when `φ (n + 1)` has degree one and its Hochschild differential is minus
the obstruction. -/
theorem IsDeformationOfOrder.isDeformationOfOrder_succ_iff {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    𝒜.IsDeformationOfOrder (n + 1) φ ↔ φ (n + 1) ∈ PositiveHochschild.cochains 𝒜 1 ∧
      𝒜.hochschildDifferential 1 (φ (n + 1)) = -𝒜.deformationObstruction φ n := by
  refine ⟨fun h' ↦ ⟨h'.mem_cochains (n + 1) le_rfl, ?_⟩, fun ⟨hmem, hd⟩ ↦ ⟨h.zero_eq, ?_, ?_⟩⟩
  · rw [eq_neg_iff_add_eq_zero, add_comm, ← deformationBrace_succ h.zero_eq]
    exact h'.deformationBrace_eq_zero (n + 1) le_rfl
  · intro i hi
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    exacts [h.mem_cochains i (Nat.lt_succ_iff.1 hi), hmem]
  · intro k hk
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · exact h.deformationBrace_eq_zero k (Nat.lt_succ_iff.1 hk)
    · rw [deformationBrace_succ h.zero_eq, hd, add_neg_cancel]

/-- **First-order deformations are Hochschild cocycles.**  A family is a deformation of order one
exactly when its constant term is `m` and `φ 1` is a Hochschild cocycle of degree one. -/
theorem isDeformationOfOrder_one_iff {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} :
    𝒜.IsDeformationOfOrder 1 φ ↔ φ 0 = 𝒜.taylor ∧
      φ 1 ∈ PositiveHochschild.cochains 𝒜 1 ∧ 𝒜.hochschildDifferential 1 (φ 1) = 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨h₀, h₁⟩ ↦ ?_⟩
  · have := ((isDeformationOfOrder_zero_iff.2 h.zero_eq).isDeformationOfOrder_succ_iff).1 h
    rw [deformationObstruction_zero, neg_zero] at this
    exact ⟨h.zero_eq, this⟩
  · refine ((isDeformationOfOrder_zero_iff.2 h₀).isDeformationOfOrder_succ_iff).2 ?_
    rwa [deformationObstruction_zero, neg_zero]

/-- **The obstruction is a Hochschild cocycle.**  For a deformation of order `n`, the Hochschild
differential of the obstruction to extending it to order `n + 1` vanishes. -/
theorem IsDeformationOfOrder.hochschildDifferential_deformationObstruction {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    𝒜.hochschildDifferential 2 (𝒜.deformationObstruction φ n) = 0 := by
  -- We pass to the coderivations `Dᵢ` of the coefficients: the coderivation of
  -- `∑_{i + j = k} φᵢ{φⱼ}` is `∑_{i + j = k} Dᵢ ∘ Dⱼ`, which vanishes for `k ≤ n`.  Comparing the
  -- coefficients of `tⁿ⁺¹` in the two bracketings of the cube of the truncated series
  -- `D₀ + t D₁ + ⋯ + tⁿ Dₙ` shows that the bar differential `D₀` commutes with the coderivation
  -- of the obstruction.
  set G := 𝒜.grading.shift 1 with hG
  set φ' : ℕ → ReducedTensorWords R A →ₗ[R] A := fun i ↦ if i ≤ n then φ i else 0 with hφ'
  have hmem (i : ℕ) : φ' i ∈ PositiveHochschild.cochains 𝒜 1 := by
    by_cases hi : i ≤ n
    · simpa [hφ', hi] using h.mem_cochains i hi
    · simp [hφ', hi]
  -- The coderivations `Dᵢ` of the truncated coefficients, and the coefficients
  -- `Sₖ = ∑_{i + j = k} Dᵢ ∘ Dⱼ` of the square of their power series.
  set D : ℕ → Module.End R (ReducedTensorWords R A) := fun i ↦ gradedCoderiv G (φ' i) 1 with hD
  have hS (k : ℕ) : gradedCoderiv G (𝒜.deformationBrace φ' k) 2 =
      ∑ x ∈ Finset.antidiagonal k, D x.1 ∘ₗ D x.2 := by
    rw [← one_add_one_eq_two, deformationBrace_def]
    exact gradedCoderiv_sum_antidiagonal_brace
      (fun i _ ↦ (PositiveHochschild.mem_cochains 𝒜).1 (hmem i)) odd_one
  have hS_eq_zero {k : ℕ} (hk : k ≤ n) : ∑ x ∈ Finset.antidiagonal k, D x.1 ∘ₗ D x.2 = 0 := by
    rw [← hS, 𝒜.deformationBrace_congr (ψ := φ) fun i hi ↦ ite_eq_left (hi.trans hk),
      h.deformationBrace_eq_zero k hk, gradedCoderiv_zero_left]
  -- The power series `B = ∑_{i ≤ n} tⁱ Dᵢ`; the coefficients of `B * B` are the `Sₖ`.
  let B : Polynomial (Module.End R (ReducedTensorWords R A)) :=
    ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (D i)
  have hB (i : ℕ) : B.coeff i = D i := by
    by_cases hi : i ≤ n
    · simp [B, Polynomial.coeff_monomial, Nat.lt_succ_iff.2 hi]
    · simp [B, Polynomial.coeff_monomial, hi, hD, hφ', gradedCoderiv_zero_left]
  have hBB (k : ℕ) : (B * B).coeff k = ∑ x ∈ Finset.antidiagonal k, D x.1 ∘ₗ D x.2 := by
    simp only [Polynomial.coeff_mul, hB, Module.End.mul_eq_comp]
  have hBB_eq_zero {k : ℕ} (hk : k ≤ n) : (B * B).coeff k = 0 := by
    rw [hBB, hS_eq_zero hk]
  -- Comparing the coefficients of `tⁿ⁺¹` in `(B * B) * B` and `B * (B * B)`, all terms but one
  -- vanish on each side, so `S_{n + 1}` commutes with `D₀`.
  have hcomm : (B * B).coeff (n + 1) * D 0 = D 0 * (B * B).coeff (n + 1) := by
    have e := congrArg (Polynomial.coeff · (n + 1)) (mul_assoc B B B)
    simp only [Polynomial.coeff_mul (B * B) B, Polynomial.coeff_mul B (B * B)] at e
    rw [Finset.sum_eq_single (n + 1, 0) (fun x hx hne ↦ ?_) (by simp),
      Finset.sum_eq_single (0, n + 1) (fun x hx hne ↦ ?_) (by simp), hB] at e
    · exact e
    · rw [Finset.mem_antidiagonal] at hx
      rw [hBB_eq_zero (by grind), mul_zero]
    · rw [Finset.mem_antidiagonal] at hx
      rw [hBB_eq_zero (by grind), zero_mul]
  have hD₀ : D 0 = 𝒜.barDifferential := by
    simp [hD, hφ', hG, h.zero_eq, barDifferential_def]
  have hO : gradedCoderiv G (𝒜.deformationObstruction φ n) 2 = (B * B).coeff (n + 1) := by
    rw [hBB, deformationObstruction_def, hS]
  have hcomm' : 𝒜.barDifferential ∘ₗ (B * B).coeff (n + 1) =
      (B * B).coeff (n + 1) ∘ₗ 𝒜.barDifferential := by
    simpa only [hD₀, Module.End.mul_eq_comp] using hcomm.symm
  -- Hence `[m, O] = m{O} - O{m}` is the letter component of `D₀ ∘ S_{n + 1} - S_{n + 1} ∘ D₀`.
  have e₁ : brace G 𝒜.taylor (𝒜.deformationObstruction φ n) 2 =
      letter R A ∘ₗ (𝒜.barDifferential ∘ₗ (B * B).coeff (n + 1)) := by
    rw [brace_def, hO, barDifferential_def, ← LinearMap.comp_assoc, letter_comp_gradedCoderiv]
  have e₂ : brace G (𝒜.deformationObstruction φ n) 𝒜.taylor 1 =
      letter R A ∘ₗ ((B * B).coeff (n + 1) ∘ₗ 𝒜.barDifferential) := by
    rw [brace_def, ← barDifferential_def, ← hO, ← LinearMap.comp_assoc,
      letter_comp_gradedCoderiv]
  rw [hochschildDifferential_eq_brace_sub, negOnePowCast_even even_two, one_smul, e₁, e₂, hcomm',
    sub_self]

/-- The obstruction of a deformation of order `n` is a cocycle of the positive-arity Hochschild
complex. -/
theorem IsDeformationOfOrder.deformationObstruction_mem_cycles {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    (⟨𝒜.deformationObstruction φ n, deformationObstruction_mem_cochains h.mem_cochains⟩ :
      PositiveHochschild.cochains 𝒜 2) ∈ PositiveHochschild.cycles 𝒜 2 :=
  (PositiveHochschild.mem_cycles 𝒜).2 h.hochschildDifferential_deformationObstruction

/-- The **obstruction class** of a deformation of order `n`: the class of its obstruction in the
positive-arity Hochschild cohomology of degree two. -/
noncomputable def IsDeformationOfOrder.obstructionClass {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    PositiveHochschild.Cohomology 𝒜 2 :=
  Submodule.Quotient.mk ⟨_, h.deformationObstruction_mem_cycles⟩

theorem IsDeformationOfOrder.obstructionClass_def {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    h.obstructionClass = Submodule.Quotient.mk ⟨_, h.deformationObstruction_mem_cycles⟩ :=
  (rfl)

/-- **The obstruction class is the obstruction to extension.**  A deformation of order `n`
extends to a deformation of order `n + 1` with the same coefficients up to order `n` exactly when
its obstruction class vanishes. -/
theorem IsDeformationOfOrder.obstructionClass_eq_zero_iff {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    h.obstructionClass = 0 ↔
      ∃ ψ, 𝒜.IsDeformationOfOrder (n + 1) (Function.update φ (n + 1) ψ) := by
  have hagree (ψ : ReducedTensorWords R A →ₗ[R] A) :
      ∀ i ≤ n, φ i = Function.update φ (n + 1) ψ i := fun i hi ↦
    (Function.update_of_ne (a' := n + 1) (by omega) ψ φ).symm
  simp_rw [fun ψ ↦ (h.congr (hagree ψ)).isDeformationOfOrder_succ_iff, Function.update_self,
    ← deformationObstruction_congr (hagree _)]
  rw [obstructionClass_def, Submodule.Quotient.mk_eq_zero, PositiveHochschild.mem_range_toCycles]
  constructor
  · rintro ⟨⟨ψ, hψ⟩, hdψ⟩
    have hψ' : ψ ∈ PositiveHochschild.cochains 𝒜 1 := by simpa using hψ
    have hdψ' : 𝒜.hochschildDifferential 1 ψ = 𝒜.deformationObstruction φ n := by
      simpa using hdψ
    refine ⟨-ψ, neg_mem hψ', ?_⟩
    rw [← neg_one_smul R ψ, hochschildDifferential_smul, neg_one_smul, hdψ']
  · rintro ⟨ψ, hψ, hdψ⟩
    have hd : 𝒜.hochschildDifferential 1 (-ψ) = 𝒜.deformationObstruction φ n := by
      rw [← neg_one_smul R ψ, hochschildDifferential_smul, neg_one_smul, hdψ, neg_neg]
    exact ⟨⟨-ψ, by simpa using neg_mem hψ⟩, by simpa using hd⟩

/-- **Unobstructedness.**  If the positive-arity Hochschild cohomology of degree two vanishes,
every deformation of order `n` extends to a formal deformation with the same coefficients up to
order `n`. -/
theorem IsDeformationOfOrder.exists_isFormalDeformation
    [Subsingleton (PositiveHochschild.Cohomology 𝒜 2)] {n : ℕ}
    {φ : ℕ → ReducedTensorWords R A →ₗ[R] A} (h : 𝒜.IsDeformationOfOrder n φ) :
    ∃ φ', 𝒜.IsFormalDeformation φ' ∧ ∀ i ≤ n, φ' i = φ i := by
  -- Every deformation of order `m` extends by one order without changing its coefficients up to
  -- order `m`, since its obstruction class vanishes.
  have step (m : ℕ) (χ : {χ // 𝒜.IsDeformationOfOrder m χ}) :
      ∃ χ', 𝒜.IsDeformationOfOrder (m + 1) χ' ∧ ∀ i ≤ m, χ' i = χ.1 i := by
    obtain ⟨ψ, hψ⟩ := (χ.2.obstructionClass_eq_zero_iff).1 (Subsingleton.elim _ _)
    exact ⟨_, hψ, fun i hi ↦ Function.update_of_ne (a' := m + 1) (by omega) ψ χ.1⟩
  choose next hnext hagree using step
  -- Extend `φ` one order at a time.
  let seq : (j : ℕ) → {χ // 𝒜.IsDeformationOfOrder (n + j) χ} :=
    fun j ↦ Nat.rec ⟨φ, h⟩ (fun j χ ↦ ⟨next (n + j) χ, hnext (n + j) χ⟩) j
  have hseq (j : ℕ) : (seq (j + 1)).1 = next (n + j) (seq j) := rfl
  have hstable {j j' : ℕ} (hj : j ≤ j') : ∀ i ≤ n + j, (seq j').1 i = (seq j).1 i := by
    induction j', hj using Nat.le_induction with
    | base => exact fun _ _ ↦ rfl
    | succ j' hj ih =>
      intro i hi
      rw [hseq, hagree _ _ i (by omega), ih i hi]
  refine ⟨fun i ↦ (seq i).1 i, fun m ↦ ?_, fun i hi ↦ ?_⟩
  · exact ((seq m).2.mono (by omega)).congr fun i hi ↦ hstable hi i (by omega)
  · exact hstable (Nat.zero_le i) i (by omega)

end TauCeti.AInfinityAlgebra
