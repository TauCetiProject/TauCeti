/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Readout
import TauCeti.Algebra.BigOperators.Finprod
import Mathlib.Tactic.LinearCombination

/-!
# Count functionals in the raw and in the cochain grading

The generators of a capped Floer complex of a symplectic manifold of dimension `2n` carry a raw
grading `μ`, in which the differential lowers degrees by one, and the cochain grading `n - μ`, in
which `C^k = CF_(n-k)` with the same differential. Orientations of moduli spaces are read off from
determinant lines whose degrees are raw degrees, so a count of rigid pairs of pants is first a
functional `ψ` on the external kernel `C₁ ⊗ C₂ ⊗ C₀^∨` whose Koszul signs are computed with the raw
degrees `μ₁`, `μ₂`, `μ₀` of the generators. The operator calculus of
`TauCeti.Geometry.Symplectic.Floer.Cap.Product` and of `TauCeti.RingTheory.NovikovModule.Readout`
(the readout `TauCeti.NovikovModule.kernelReadout`, the total boundary
`TauCeti.NovikovModule.functionalBoundary` and the tensor differential
`TauCeti.NovikovModule.tensorDifferential`) is applied in the cochain grading, in which the product
has degree `0`. This file relates the two, at the level of kernels on generators.

Each identity is the kernel-level counterpart of a comparison of complexes: the regrading of
tensor products (`ChainComplex.regradeTensorIso`, with the sign `(-1)^(n q)` on `K_p ⊗ L_q`), of
duals and bidual maps (`ChainComplex.regradeLinearDualIso`, `ChainComplex.restrictionMap_bidualHom`)
and of the interchange of factors
(`ChainComplex.regradeTensorHom_comp_restrictionMap_tensorBraiding`, with the sign `(-1)^(n₁ n₂)`).

**Unary operations.** For an operation between two complexes both regraded by `n`, such as a
continuation map, the total boundary of a functional is the same in both gradings
(`TauCeti.NovikovModule.functionalBoundary_cochain`), since `(n - μ) + (n - μ₀)` and `μ + μ₀` have
the same parity, while the readout of a functional as an operator changes by the global sign
`(-1)^n` (`TauCeti.NovikovModule.kernelReadout_cochain`), the sign of the bidual map.

**The tensor differential.** In the Koszul tensor differential `δ₁ ⊗ 1 + (-1)^(d₁) ⊗ δ₂` of
`C₁ ⊗ C₂` the sign `(-1)^(n - μ₁)` of the cochain grading is `(-1)^n` times that of the raw
grading. Since `δ₂` changes `μ₂` by one, the two tensor differentials are conjugate by the sign
`(-1)^(n μ₂)` on generators (`TauCeti.NovikovModule.tensorDifferential_cochain`).

**The regraded functional.** The regrading of a product functional `ψ` is the functional
`(-1)^(n (μ₂ p₂ + μ₀ p₀)) ψ((p₁, p₂), p₀)` (`TauCeti.NovikovModule.regradeProductFunctional`):
the conjugating sign on the inputs, and on the output the sign that compensates the change of the
Koszul sign `(-1)^(d + d₀)` of the total differential. It commutes with the total boundaries: the
cochain boundary of the regraded functional is the regraded raw boundary
(`TauCeti.NovikovModule.functionalBoundary_regradeProductFunctional`). So a functional is closed,
or has a prescribed boundary, in the raw grading exactly when its regrading does in the cochain
grading.

**Readout.** The raw readout of an operator kernel `t` of raw degree `-n - ε`, regraded, is the
cochain readout of `(-1)^(n (μ₁ p₁ + ε)) t`
(`TauCeti.NovikovModule.regradeProductFunctional_kernelReadout`), an operator kernel of cochain
degree `ε`. Hence a raw count functional which is closed for the raw total differential yields a
product kernel satisfying the Leibniz rule `δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b` for `a` of
cochain degree `i`
(`NovikovModule.kernelMap_kernelProduct_eq_add_of_functionalBoundary_kernelReadout_eq_zero`).

**Input exchange.** Exchanging the inputs costs `(-1)^((n - μ₁)(n - μ₂))` in the cochain grading
and `(-1)^(μ₁ μ₂)` in the raw grading, and `(n - μ₁)(n - μ₂) ≡ μ₁ μ₂ + n (μ₁ + μ₂) + n` modulo `2`.
The regrading of the exchanged functional thus carries the cochain Koszul sign exactly when the
raw exchange carries the sign `(-1)^(n + μ₁ μ₂)`
(`TauCeti.NovikovModule.regradeProductFunctional_swap`). Consequently a raw exchange functional
whose boundary is the raw readout of the product minus `(-1)^(n + μ₁ μ₂)` times that of the
exchanged product yields the commutativity kernel identity with the cochain sign
`(-1)^((n - μ₁)(n - μ₂))`, by
`NovikovModule.sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`,
which `TauCeti.NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`
turns into graded commutativity on cohomology. This is the kernel-level form of the statement that
a product which is graded commutative up to `ε` for the raw degrees is graded commutative up to
`(-1)^n ε` for the cochain degrees.

**Continuation.** A continuation map between two Floer complexes regraded by the same `n` is the
same operator in both gradings, of degree `0`. Gluing continuation cylinders to the three ends of
a pair of pants gives a family whose count is a functional of degree `-1` on `C₁ ⊗ C₂ ⊗ C₀'^∨`,
with boundary the readout of the first product followed by the output continuation map minus the
readout of the input continuation maps followed by the second product. The cochain kernel of each
product is its raw kernel twisted by `(-1)^(n μ₁)` at the first input, and a continuation map
preserves raw degrees, so both composites are twisted by the same sign `(-1)^(n μ₁ p₁)`. Regrading
therefore turns such a raw functional into the continuation kernel identity of the cochain grading
(`kernelComp_sub_kernelComp_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`),
which `TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy`
turns into the chain homotopy between `φ₀ (a ⋆ b)` and `φ₁ a ⋆' φ₂ b`, and
`TauCeti.NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct` into the multiplicativity
of continuation maps on cohomology.

The functional identities in the raw grading are hypotheses: they are the boundary theorems for
the oriented one-dimensional moduli spaces, which are not constructed here.

## Main definitions

* `TauCeti.NovikovModule.regradeProductFunctional`: the regrading of a functional on
  `C₁ ⊗ C₂ ⊗ C₀^∨` from the raw to the cochain grading.

## Main results

* `TauCeti.NovikovModule.functionalBoundary_cochain`,
  `TauCeti.NovikovModule.kernelReadout_cochain`: boundaries and readouts of functionals of unary
  operations in the two gradings.
* `TauCeti.NovikovModule.tensorDifferential_cochain`: the tensor differentials of the two
  gradings are conjugate by `(-1)^(n μ₂)`.
* `TauCeti.NovikovModule.functionalBoundary_regradeProductFunctional`: regrading commutes with the
  total boundaries.
* `TauCeti.NovikovModule.regradeProductFunctional_kernelReadout`: the regrading of a raw readout is
  a cochain readout.
* `TauCeti.NovikovModule.regradeProductFunctional_swap`: the exchange signs of the two gradings.
* `NovikovModule.kernelMap_kernelProduct_eq_add_of_functionalBoundary_kernelReadout_eq_zero` and
  `NovikovModule.sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`
  give the Leibniz rule and the commutativity kernel identity in the cochain grading from
  functional identities in the raw grading.
* `kernelComp_sub_kernelComp_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`
  gives the continuation kernel identity in the cochain grading from a functional identity in the
  raw grading.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  cohomological regrading of Floer complexes and of their pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 11 and 12,
  on orientation lines and the signs of operations read off from them.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

variable {R S S₀ S₁ S₂ : Type*} [CommRing R]

section Unary

/-- **Boundaries of unary functionals do not see the regrading.** For an operation between two
complexes both regraded by `n`, the total boundary of a functional on `X ⊗ C₀^∨` is the same for
the cochain degrees `n - μ`, `n - μ₀` as for the raw degrees `μ`, `μ₀`. -/
theorem functionalBoundary_cochain (n : ℤ) (μ : S → ℤ) (μ₀ : S₀ → ℤ) (δ : S → S → R)
    (δ₀ : S₀ → S₀ → R) (φ : S → S₀ → R) :
    functionalBoundary (fun p => n - μ p) (fun p => n - μ₀ p) δ δ₀ φ =
      functionalBoundary μ μ₀ δ δ₀ φ := by
  funext x q
  rw [functionalBoundary_apply, functionalBoundary_apply,
    negOnePowCast_eq_of_even_sub (b := μ x + μ₀ q) ⟨n - μ x - μ₀ q, by ring⟩]

/-- **Readouts in the two gradings.** Reading a functional as an operator with the cochain degrees
`n - μ₀` of the outputs is `(-1)^n` times reading it with their raw degrees `μ₀`. -/
theorem kernelReadout_cochain (n : ℤ) (μ₀ : S₀ → ℤ) (φ : S → S₀ → R) :
    kernelReadout (fun p => n - μ₀ p) φ = negOnePowCast R n • kernelReadout μ₀ φ := by
  funext x q
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, kernelReadout_apply, kernelReadout_apply,
    ← mul_assoc, ← negOnePowCast_add]
  exact congrArg (· * φ x q) (negOnePowCast_eq_of_even_sub ⟨-μ₀ q, by ring⟩)

end Unary

section Regrade

variable (n : ℤ) (μ₂ : S₂ → ℤ) (μ₀ : S₀ → ℤ)

/-- The **regrading of a product functional** `ψ` on `C₁ ⊗ C₂ ⊗ C₀^∨` from the raw degrees `μ₁`,
`μ₂`, `μ₀` to the cochain degrees `n - μ₁`, `n - μ₂`, `n - μ₀`: the functional
`(-1)^(n (μ₂ p₂ + μ₀ p₀)) ψ((p₁, p₂), p₀)`. It intertwines the total boundaries of the two gradings
(`TauCeti.NovikovModule.functionalBoundary_regradeProductFunctional`). -/
def regradeProductFunctional (ψ : S₁ × S₂ → S₀ → R) (q : S₁ × S₂) (p₀ : S₀) : R :=
  negOnePowCast R (n * (μ₂ q.2 + μ₀ p₀)) * ψ q p₀

/-- A value of the regrading of a product functional. -/
theorem regradeProductFunctional_apply (ψ : S₁ × S₂ → S₀ → R) (q : S₁ × S₂) (p₀ : S₀) :
    regradeProductFunctional n μ₂ μ₀ ψ q p₀ = negOnePowCast R (n * (μ₂ q.2 + μ₀ p₀)) * ψ q p₀ :=
  (rfl)

/-- Regrading is an involution. -/
@[simp]
theorem regradeProductFunctional_regradeProductFunctional (ψ : S₁ × S₂ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀ (regradeProductFunctional n μ₂ μ₀ ψ) = ψ := by
  funext q p₀
  rw [regradeProductFunctional_apply, regradeProductFunctional_apply, ← mul_assoc,
    negOnePowCast_mul_self, one_mul]

/-- Regrading is injective. -/
theorem regradeProductFunctional_injective :
    Injective (regradeProductFunctional (R := R) (S₁ := S₁) n μ₂ μ₀) :=
  LeftInverse.injective (g := regradeProductFunctional n μ₂ μ₀)
    (regradeProductFunctional_regradeProductFunctional n μ₂ μ₀)

/-- Two functionals have equal regradings exactly when they are equal. -/
@[simp]
theorem regradeProductFunctional_inj {ψ ψ' : S₁ × S₂ → S₀ → R} :
    regradeProductFunctional n μ₂ μ₀ ψ = regradeProductFunctional n μ₂ μ₀ ψ' ↔ ψ = ψ' :=
  (regradeProductFunctional_injective n μ₂ μ₀).eq_iff

/-- The regrading of the zero functional is zero. -/
@[simp]
theorem regradeProductFunctional_zero :
    regradeProductFunctional (R := R) (S₁ := S₁) n μ₂ μ₀ 0 = 0 := by
  funext q p₀
  simp [regradeProductFunctional_apply]

/-- Regrading is additive. -/
@[simp]
theorem regradeProductFunctional_add (ψ ψ' : S₁ × S₂ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀ (ψ + ψ') =
      regradeProductFunctional n μ₂ μ₀ ψ + regradeProductFunctional n μ₂ μ₀ ψ' := by
  funext q p₀
  simp [regradeProductFunctional_apply, mul_add]

/-- Regrading commutes with negation. -/
@[simp]
theorem regradeProductFunctional_neg (ψ : S₁ × S₂ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀ (-ψ) = -regradeProductFunctional n μ₂ μ₀ ψ := by
  funext q p₀
  simp [regradeProductFunctional_apply]

/-- Regrading commutes with subtraction. -/
@[simp]
theorem regradeProductFunctional_sub (ψ ψ' : S₁ × S₂ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀ (ψ - ψ') =
      regradeProductFunctional n μ₂ μ₀ ψ - regradeProductFunctional n μ₂ μ₀ ψ' := by
  funext q p₀
  simp [regradeProductFunctional_apply, mul_sub]

/-- Regrading commutes with scalar multiplication. -/
@[simp]
theorem regradeProductFunctional_smul (c : R) (ψ : S₁ × S₂ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀ (c • ψ) = c • regradeProductFunctional n μ₂ μ₀ ψ := by
  funext q p₀
  simp only [regradeProductFunctional_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Regrade

section Product

variable {n : ℤ} {μ₁ : S₁ → ℤ} {μ₂ : S₂ → ℤ} {μ₀ : S₀ → ℤ}

/-- **The regraded functional of a readout.** Let `t` be an operator kernel of raw degree
`-n - ε`, so that `t((p₁, p₂), p₀) ≠ 0` only if `μ₀ p₀ = μ₁ p₁ + μ₂ p₂ - n - ε`, that is, of
cochain degree `ε`. The regrading of its readout with the raw output degrees is the readout with
the cochain output degrees of the operator kernel `(-1)^(n (μ₁ p₁ + ε)) t((p₁, p₂), p₀)`. -/
theorem regradeProductFunctional_kernelReadout {ε : ℤ} {t : S₁ × S₂ → S₀ → R}
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n - ε) :
    regradeProductFunctional n μ₂ μ₀ (kernelReadout μ₀ t) =
      kernelReadout (fun p => n - μ₀ p)
        fun q p₀ => negOnePowCast R (n * (μ₁ q.1 + ε)) * t q p₀ := by
  funext q p₀
  rw [regradeProductFunctional_apply, kernelReadout_apply, kernelReadout_apply]
  by_cases h : t q p₀ = 0
  · simp [h]
  simp only [← mul_assoc, ← negOnePowCast_add]
  congr 1
  apply negOnePowCast_eq_of_even_sub
  -- The two exponents differ by `n * n - n` modulo `2`, which is even since `n * n ≡ n`.
  rw [ht q p₀ h]
  simp only [Int.even_sub, Int.even_add, Int.even_mul]
  tauto

/-- **The exchange signs of the two gradings.** For a functional `ψ'` on `C₂ ⊗ C₁ ⊗ C₀^∨`, the
regrading of the exchanged functional `(-1)^(n + μ₁ p₁ μ₂ p₂) ψ'((p₂, p₁), p₀)` is the regrading of
`ψ'`, exchanged with the Koszul sign `(-1)^((n - μ₁ p₁) (n - μ₂ p₂))` of the cochain degrees. So
the cochain Koszul sign of an input exchange corresponds to the raw Koszul sign `(-1)^(μ₁ μ₂)`
twisted by `(-1)^n`. -/
theorem regradeProductFunctional_swap (ψ' : S₂ × S₁ → S₀ → R) :
    regradeProductFunctional n μ₂ μ₀
        (fun q p₀ => negOnePowCast R (n + μ₁ q.1 * μ₂ q.2) * ψ' q.swap p₀) =
      fun q p₀ => negOnePowCast R ((n - μ₁ q.1) * (n - μ₂ q.2)) *
        regradeProductFunctional n μ₁ μ₀ ψ' q.swap p₀ := by
  funext q p₀
  simp only [regradeProductFunctional_apply, Prod.snd_swap, ← mul_assoc, ← negOnePowCast_add]
  congr 1
  apply negOnePowCast_eq_of_even_sub
  -- The two exponents differ by `n * n - n` modulo `2`, which is even since `n * n ≡ n`.
  simp only [Int.even_sub, Int.even_add, Int.even_mul]
  tauto

/-- **The regraded functional of the readout of a product kernel.** Let `t` be an operator kernel
of raw degree `-n`, and `m(p₁, p₂, p₀) = (-1)^(n μ₁ p₁) t((p₁, p₂), p₀)`. The regrading of the
readout of `t` with the raw output degrees is the readout of `m` with the cochain output degrees.
This is `TauCeti.NovikovModule.regradeProductFunctional_kernelReadout` at `ε = 0`. -/
theorem regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul {t : S₁ × S₂ → S₀ → R}
    {m : S₁ → S₂ → S₀ → R}
    (hmt : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) p₀)
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n) :
    regradeProductFunctional n μ₂ μ₀ (kernelReadout μ₀ t) =
      kernelReadout (fun p => n - μ₀ p) fun q => m q.1 q.2 := by
  rw [regradeProductFunctional_kernelReadout (ε := 0) fun q p₀ hq => by rw [sub_zero, ht q p₀ hq]]
  simp only [add_zero]
  exact congrArg _ (funext fun q => funext fun p₀ => (hmt q.1 q.2 p₀).symm)

/-- **Cochain degrees of a product kernel.** If `t` is an operator kernel of raw degree `-n` and
`m(p₁, p₂, p₀) = (-1)^(n μ₁ p₁) t((p₁, p₂), p₀)`, then `m` has cochain degree `0`:
`m(p₁, p₂, p₀) ≠ 0` only if `n - μ₀ p₀ = (n - μ₁ p₁) + (n - μ₂ p₂)`. -/
theorem sub_eq_sub_add_sub_of_eq_negOnePowCast_mul {t : S₁ × S₂ → S₀ → R}
    {m : S₁ → S₂ → S₀ → R}
    (hmt : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) p₀)
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n) {p₁ : S₁} {p₂ : S₂} {p₀ : S₀}
    (h : m p₁ p₂ p₀ ≠ 0) : n - μ₀ p₀ = n - μ₁ p₁ + (n - μ₂ p₂) := by
  rw [hmt] at h
  rw [ht (p₁, p₂) p₀ (right_ne_zero_of_mul h)]
  ring

/-- Composing a degree-preserving tensor product of kernels `φ₁ ⊗ φ₂` with the twisted kernel
`m'(s₁, s₂, ·) = (-1)^(n ν₁ s₁) t'((s₁, s₂), ·)` moves the sign to the first input: the result is
`(-1)^(n μ₁ p₁)` times the composite with `t'`. -/
private theorem kernelComp_kernelTensor_eq_negOnePowCast_mul {T₁ T₂ T₀ : Type*} {ν₁ : T₁ → ℤ}
    {t' : T₁ × T₂ → T₀ → R} {m' : T₁ → T₂ → T₀ → R} {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R}
    (hmt' : ∀ s₁ s₂ t₀, m' s₁ s₂ t₀ = negOnePowCast R (n * ν₁ s₁) * t' (s₁, s₂) t₀)
    (hφ₁ : ∀ p s, φ₁ p s ≠ 0 → ν₁ s = μ₁ p) (q : S₁ × S₂) (t₀ : T₀) :
    kernelComp (kernelTensor φ₁ φ₂) (fun s : T₁ × T₂ => m' s.1 s.2) q t₀ =
      negOnePowCast R (n * μ₁ q.1) * kernelComp (kernelTensor φ₁ φ₂) t' q t₀ := by
  refine kernelComp_eq_mul_kernelComp
    (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self _)) fun s => ?_
  by_cases hs : φ₁ q.1 s.1 = 0
  · simp [hs]
  rw [kernelTensor_apply, hmt', hφ₁ _ _ hs]
  ring

variable [DecidableEq S₁] [DecidableEq S₂] {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R}
  {δ₀ : S₀ → S₀ → R}

/-- **The tensor differentials of the two gradings are conjugate.** If `δ₂` lowers the raw degree
`μ₂` by one, the Koszul tensor differential of `C₁ ⊗ C₂` built with the cochain degrees `n - μ₁` is
the one built with the raw degrees `μ₁`, conjugated by the sign `(-1)^(n μ₂)` on generators. No
condition on `δ₁` is needed. -/
theorem tensorDifferential_cochain (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (p q : S₁ × S₂) :
    tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂ p q =
      negOnePowCast R (n * (μ₂ p.2 + μ₂ q.2)) * tensorDifferential μ₁ δ₁ δ₂ p q := by
  rw [tensorDifferential_apply, tensorDifferential_apply, mul_add]
  congr 1
  · by_cases h : p.2 = q.2
    · rw [h, negOnePowCast_even (e := n * (μ₂ q.2 + μ₂ q.2)) ⟨n * μ₂ q.2, by ring⟩, one_mul]
    · simp [h]
  · by_cases h : p.1 = q.1
    · by_cases hδ : δ₂ p.2 q.2 = 0
      · simp [hδ]
      rw [ite_eq_left h, ite_eq_left h, ← negOnePowCast_eq_intCast, ← negOnePowCast_eq_intCast,
        ← mul_assoc, ← negOnePowCast_add]
      congr 1
      apply negOnePowCast_eq_of_even_sub
      rw [hδ₂ _ _ hδ]
      exact ⟨n - μ₁ p.1 - n * μ₂ p.2, by ring⟩
    · simp [h]

/-- **Regrading commutes with the total boundaries.** If `δ₂` and `δ₀` lower the raw degrees `μ₂`
and `μ₀` by one, the boundary of the regrading of a product functional `ψ`, for the cochain degrees
and the tensor differential built with them, is the regrading of the boundary of `ψ` for the raw
degrees and the tensor differential built with them. -/
theorem functionalBoundary_regradeProductFunctional
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → μ₀ q = μ₀ p - 1)
    (ψ : S₁ × S₂ → S₀ → R) :
    functionalBoundary (fun q : S₁ × S₂ => (n - μ₁ q.1) + (n - μ₂ q.2)) (fun p => n - μ₀ p)
        (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) δ₀ (regradeProductFunctional n μ₂ μ₀ ψ) =
      regradeProductFunctional n μ₂ μ₀
        (functionalBoundary (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) μ₀ (tensorDifferential μ₁ δ₁ δ₂)
          δ₀ ψ) := by
  funext x q
  -- At the input breakings the conjugating signs of the tensor differential cancel.
  have h₁ : kernelComp (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂)
      (regradeProductFunctional n μ₂ μ₀ ψ) x q =
      negOnePowCast R (n * (μ₂ x.2 + μ₀ q)) * kernelComp (tensorDifferential μ₁ δ₁ δ₂) ψ x q := by
    refine kernelComp_eq_mul_kernelComp
      (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self _)) fun x' => ?_
    rw [tensorDifferential_cochain hδ₂, regradeProductFunctional_apply,
      ← negOnePowCast_eq_of_even_sub (a := n * (μ₂ x.2 + μ₂ x'.2) + n * (μ₂ x'.2 + μ₀ q))
        (b := n * (μ₂ x.2 + μ₀ q)) ⟨n * μ₂ x'.2, by ring⟩, negOnePowCast_add]
    ring
  -- At the output breakings the output sign changes by `(-1)^n`.
  have h₂ : kernelComp (regradeProductFunctional n μ₂ μ₀ ψ) δ₀ x q =
      negOnePowCast R (n + n * (μ₂ x.2 + μ₀ q)) * kernelComp ψ δ₀ x q := by
    refine kernelComp_eq_mul_kernelComp
      (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self _)) fun p => ?_
    by_cases hp : δ₀ p q = 0
    · simp [hp]
    rw [regradeProductFunctional_apply, hδ₀ p q hp,
      show n + n * (μ₂ x.2 + (μ₀ p - 1)) = n * (μ₂ x.2 + μ₀ p) by ring]
    ring
  have hsign : negOnePowCast R (n - μ₁ x.1 + (n - μ₂ x.2) + (n - μ₀ q)) *
      negOnePowCast R (n + n * (μ₂ x.2 + μ₀ q)) =
      negOnePowCast R (μ₁ x.1 + μ₂ x.2 + μ₀ q) * negOnePowCast R (n * (μ₂ x.2 + μ₀ q)) := by
    rw [← negOnePowCast_add, ← negOnePowCast_add]
    exact negOnePowCast_eq_of_even_sub ⟨2 * n - μ₁ x.1 - μ₂ x.2 - μ₀ q, by ring⟩
  rw [functionalBoundary_apply, regradeProductFunctional_apply, functionalBoundary_apply, h₁, h₂]
  linear_combination (-kernelComp ψ δ₀ x q) * hsign

variable {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {C C₁ C₂ C₀ : ℝ} {m : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, m p₁ p₂ ∈ NovikovModule R F₀)
  (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + C₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + C₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

include hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin in
/-- **The Leibniz rule from a closed functional in the raw grading.** Let `t` be an operator
kernel of raw degree `-n` whose readout with the raw output degrees, a count functional on
`C₁ ⊗ C₂ ⊗ C₀^∨` with Koszul signs in the raw degrees, is annihilated by the total differential
built from the raw tensor differential. Suppose that the differentials lower the raw degrees by
one. Then the product kernel `m(p₁, p₂, p₀) = (-1)^(n μ₁ p₁) t((p₁, p₂), p₀)` satisfies the Leibniz
rule of the cochain grading: for a completed combination `a` of cochain degree `i` and any
completed combination `b`, `δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b`. -/
theorem kernelMap_kernelProduct_eq_add_of_functionalBoundary_kernelReadout_eq_zero
    {t : S₁ × S₂ → S₀ → R}
    (hmt : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) p₀)
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n)
    (hδ₂deg : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (hδ₀deg : ∀ p q, δ₀ p q ≠ 0 → μ₀ q = μ₀ p - 1)
    (hφ : ∀ q p₀, functionalBoundary (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) μ₀
      (tensorDifferential μ₁ δ₁ δ₂) δ₀ (kernelReadout μ₀ t) q p₀ = 0)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ (fun p => n - μ₁ p) i)
    (b : NovikovModule R F₂) :
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b) := by
  refine kernelMap_kernelProduct_eq_add_of_functionalBoundary_eq_zero hn hfin hδ₁ hδ₁fin hδ₂
    hδ₂fin hδ₀ hδ₀fin (d₁ := fun p => n - μ₁ p) (d₂ := fun p => n - μ₂ p) (d₀ := fun p => n - μ₀ p)
    (fun _ _ _ => sub_eq_sub_add_sub_of_eq_negOnePowCast_mul hmt ht) (fun q p₀ => ?_) ha b
  -- The cochain readout of `m` is the regrading of the raw readout of `t`.
  rw [← regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul hmt ht,
    functionalBoundary_regradeProductFunctional hδ₂deg hδ₀deg, regradeProductFunctional_apply, hφ,
    mul_zero]

/-- **The commutativity kernel identity from an exchange functional in the raw grading.** Let `t`
and `t'` be operator kernels of raw degree `-n` out of `C₁ ⊗ C₂` and `C₂ ⊗ C₁`, and `h` one of raw
degree `1 - n` out of `C₁ ⊗ C₂`, and suppose that the differentials lower the raw degrees by one.
If, in the raw grading, the boundary of the readout of `h` is the readout of `t` minus the readout
of the exchanged kernel `t'((p₂, p₁), ·)` with the sign `(-1)^(n + μ₁ p₁ μ₂ p₂)`, then the kernels
`m(p₁, p₂, ·) = (-1)^(n μ₁ p₁) t((p₁, p₂), ·)`, `m'(p₂, p₁, ·) = (-1)^(n μ₂ p₂) t'((p₂, p₁), ·)`
and `k = (-1)^(n (μ₁ p₁ - 1)) h` satisfy the commutativity kernel identity of the cochain grading,
`m(p₁, p₂, p₀) - (-1)^(e₁ e₂) m'(p₂, p₁, p₀) = ∑ k(q, p) δ₀(p, p₀) + ∑ δ⊗(q, q') k(q', p₀)` at
`q = (p₁, p₂)`, with the cochain degrees `e₁ = n - μ₁ p₁`, `e₂ = n - μ₂ p₂` and the tensor
differential `δ⊗` built with them, as consumed by
`TauCeti.NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`. -/
theorem sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout
    {m' : S₂ → S₁ → S₀ → R} {k t h : S₁ × S₂ → S₀ → R} {t' : S₂ × S₁ → S₀ → R}
    (hmt : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) p₀)
    (hmt' : ∀ p₂ p₁ p₀, m' p₂ p₁ p₀ = negOnePowCast R (n * μ₂ p₂) * t' (p₂, p₁) p₀)
    (hkh : ∀ q p₀, k q p₀ = negOnePowCast R (n * (μ₁ q.1 - 1)) * h q p₀)
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n)
    (ht' : ∀ q p₀, t' q p₀ ≠ 0 → μ₀ p₀ = μ₂ q.1 + μ₁ q.2 - n)
    (hh : ∀ q p₀, h q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n + 1)
    (hδ₂deg : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (hδ₀deg : ∀ p q, δ₀ p q ≠ 0 → μ₀ q = μ₀ p - 1)
    {q : S₁ × S₂} {p₀ : S₀}
    (hψ : functionalBoundary (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) μ₀
      (tensorDifferential μ₁ δ₁ δ₂) δ₀ (kernelReadout μ₀ h) q p₀ =
        kernelReadout μ₀ t q p₀ -
          negOnePowCast R (n + μ₁ q.1 * μ₂ q.2) * kernelReadout μ₀ t' q.swap p₀) :
    m q.1 q.2 p₀ - (((n - μ₁ q.1) * (n - μ₂ q.2)).negOnePow : R) * m' q.2 q.1 p₀ =
      kernelComp k δ₀ q p₀ +
        kernelComp (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) k q p₀ := by
  -- Each raw readout, regraded, is the cochain readout of the corresponding cochain kernel.
  have hm := regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul hmt ht
  have hm' := regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul hmt' ht'
  have hk : regradeProductFunctional n μ₂ μ₀ (kernelReadout μ₀ h) =
      kernelReadout (fun p => n - μ₀ p) k := by
    rw [regradeProductFunctional_kernelReadout (ε := -1) fun q p₀ hq => by
      rw [hh q p₀ hq]; ring]
    exact congrArg _ (funext fun q => funext fun p₀ => by rw [hkh, sub_eq_add_neg])
  have hm'q : kernelReadout (fun p => n - μ₀ p) (fun q => m' q.2 q.1) q p₀ =
      regradeProductFunctional n μ₁ μ₀ (kernelReadout μ₀ t') q.swap p₀ := by
    rw [hm', kernelReadout_apply, kernelReadout_apply, Prod.fst_swap, Prod.snd_swap]
  have hswap := congrFun (congrFun (regradeProductFunctional_swap (n := n) (μ₁ := μ₁)
    (μ₂ := μ₂) (μ₀ := μ₀) (kernelReadout μ₀ t')) q) p₀
  rw [regradeProductFunctional_apply] at hswap
  refine sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary
    (d₁ := fun p => n - μ₁ p) (d₂ := fun p => n - μ₂ p) (d₀ := fun p => n - μ₀ p)
    (fun q p₀ hq => ?_) ?_
  · rw [hkh] at hq
    have e := hh q p₀ (right_ne_zero_of_mul hq)
    rw [e]
    ring
  · -- Regrade the raw identity and read off each term in the cochain grading.
    rw [← hk, functionalBoundary_regradeProductFunctional hδ₂deg hδ₀deg,
      regradeProductFunctional_apply, hψ, ← hm, regradeProductFunctional_apply, hm'q,
      ← negOnePowCast_eq_intCast, ← hswap]
    ring

/-- **The continuation kernel identity from a functional of the continuation family, in the raw
grading.** Let `t` and `t'` be operator kernels of raw degree `-n`, of the products out of
`C₁ ⊗ C₂` and `C₁' ⊗ C₂'`, and let `φ₁`, `φ₂`, `φ₀` be operator kernels of raw degree `0` from
the inputs and the output of the first product to those of the second, as continuation maps are.
Let `h` be an operator kernel of raw degree `1 - n` from `C₁ ⊗ C₂` to the output `C₀'` of the
second product, and suppose that `δ₂` and `η₀` lower the raw degrees by one. If, in the raw
grading, the boundary of the readout of `h` is the readout of the composite `t φ₀` minus the
readout of the composite `(φ₁ ⊗ φ₂) t'`, then the kernels
`m(p₁, p₂, ·) = (-1)^(n μ₁ p₁) t((p₁, p₂), ·)`, `m'(s₁, s₂, ·) = (-1)^(n ν₁ s₁) t'((s₁, s₂), ·)`
and `k = (-1)^(n (μ₁ p₁ - 1)) h` satisfy the continuation kernel identity of the cochain grading,

`∑ₚ m(p₁, p₂, p) φ₀(p, t₀) - ∑ₛ φ₁(p₁, s₁) φ₂(p₂, s₂) m'(s₁, s₂, t₀) = (k η₀ + δ⊗ k)(q, t₀)`

at `q = (p₁, p₂)`, with the tensor differential `δ⊗` built with the cochain degrees `n - μ₁`, as
consumed by
`TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy`.
The continuation kernels are the same in both gradings: regrading is the identity on chain maps
between complexes regraded by the same `n`. -/
theorem kernelComp_sub_kernelComp_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout
    {T₁ T₂ T₀ : Type*} {ν₁ : T₁ → ℤ} {ν₂ : T₂ → ℤ} {ν₀ : T₀ → ℤ} {η₀ : T₀ → T₀ → R}
    {t : S₁ × S₂ → S₀ → R} {t' : T₁ × T₂ → T₀ → R} {h : S₁ × S₂ → T₀ → R}
    {m' : T₁ → T₂ → T₀ → R}
    {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R} {φ₀ : S₀ → T₀ → R} {k : S₁ × S₂ → T₀ → R}
    (hmt : ∀ p₁ p₂ p₀, m p₁ p₂ p₀ = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) p₀)
    (hmt' : ∀ s₁ s₂ t₀, m' s₁ s₂ t₀ = negOnePowCast R (n * ν₁ s₁) * t' (s₁, s₂) t₀)
    (hkh : ∀ q t₀, k q t₀ = negOnePowCast R (n * (μ₁ q.1 - 1)) * h q t₀)
    (ht : ∀ q p₀, t q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1 + μ₂ q.2 - n)
    (ht' : ∀ s t₀, t' s t₀ ≠ 0 → ν₀ t₀ = ν₁ s.1 + ν₂ s.2 - n)
    (hh : ∀ q t₀, h q t₀ ≠ 0 → ν₀ t₀ = μ₁ q.1 + μ₂ q.2 - n + 1)
    (hφ₁ : ∀ p s, φ₁ p s ≠ 0 → ν₁ s = μ₁ p) (hφ₂ : ∀ p s, φ₂ p s ≠ 0 → ν₂ s = μ₂ p)
    (hφ₀ : ∀ p t₀, φ₀ p t₀ ≠ 0 → ν₀ t₀ = μ₀ p)
    (hδ₂deg : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (hη₀deg : ∀ t t', η₀ t t' ≠ 0 → ν₀ t' = ν₀ t - 1)
    {q : S₁ × S₂} {t₀ : T₀}
    (hψ : functionalBoundary (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) ν₀
      (tensorDifferential μ₁ δ₁ δ₂) η₀ (kernelReadout ν₀ h) q t₀ =
        kernelReadout ν₀ (kernelComp t φ₀) q t₀ -
          kernelReadout ν₀ (kernelComp (kernelTensor φ₁ φ₂) t') q t₀) :
    kernelComp (fun q : S₁ × S₂ => m q.1 q.2) φ₀ q t₀ -
        kernelComp (kernelTensor φ₁ φ₂) (fun s : T₁ × T₂ => m' s.1 s.2) q t₀ =
      kernelComp k η₀ q t₀ +
        kernelComp (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) k q t₀ := by
  -- The cochain composites are the raw composites twisted by the sign of the first input.
  have hT (q : S₁ × S₂) (t₀ : T₀) : kernelComp (fun q : S₁ × S₂ => m q.1 q.2) φ₀ q t₀ =
      negOnePowCast R (n * μ₁ q.1) * kernelComp t φ₀ q t₀ := by
    exact kernelComp_eq_mul_kernelComp (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self _))
      fun p => by rw [hmt]; ring
  -- Both raw composites have raw degree `-n`.
  have hTdeg (q : S₁ × S₂) (t₀ : T₀) (hq : kernelComp t φ₀ q t₀ ≠ 0) :
      ν₀ t₀ = μ₁ q.1 + μ₂ q.2 - n := by
    rw [degree_eq_of_kernelComp_ne_zero (d₁ := fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) (d₀ := μ₀)
      (d₂ := ν₀) (a := -n) (b := 0) (fun p hp => by rw [ht q p hp, sub_eq_add_neg])
      (fun p hp => by rw [hφ₀ p t₀ hp, add_zero]) hq]
    ring
  have hT'deg (q : S₁ × S₂) (t₀ : T₀) (hq : kernelComp (kernelTensor φ₁ φ₂) t' q t₀ ≠ 0) :
      ν₀ t₀ = μ₁ q.1 + μ₂ q.2 - n := by
    rw [degree_eq_of_kernelComp_ne_zero (d₁ := fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2)
      (d₀ := fun s : T₁ × T₂ => ν₁ s.1 + ν₂ s.2) (d₂ := ν₀) (a := 0) (b := -n) (fun s hs => ?_)
      (fun s hs => by rw [ht' s t₀ hs, sub_eq_add_neg]) hq]
    · ring
    rw [kernelTensor_apply] at hs
    rw [hφ₁ _ _ (left_ne_zero_of_mul hs), hφ₂ _ _ (right_ne_zero_of_mul hs), add_zero]
  -- Regrading the raw readouts gives the cochain readouts of `k` and of the two composites.
  have hk : regradeProductFunctional n μ₂ ν₀ (kernelReadout ν₀ h) =
      kernelReadout (fun p => n - ν₀ p) k := by
    rw [regradeProductFunctional_kernelReadout (ε := -1) fun q t₀ hq => by
      rw [hh q t₀ hq]; ring]
    exact congrArg _ (funext fun q => funext fun t₀ => by rw [hkh, sub_eq_add_neg])
  have hTr := regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul
    (m := fun p₁ p₂ => kernelComp (fun q : S₁ × S₂ => m q.1 q.2) φ₀ (p₁, p₂))
    (fun p₁ p₂ t₀ => hT (p₁, p₂) t₀) hTdeg
  have hT'r := regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul
    (m := fun p₁ p₂ => kernelComp (kernelTensor φ₁ φ₂) (fun s : T₁ × T₂ => m' s.1 s.2) (p₁, p₂))
    (fun p₁ p₂ t₀ => kernelComp_kernelTensor_eq_negOnePowCast_mul hmt' hφ₁ (p₁, p₂) t₀) hT'deg
  refine ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
    (d := fun q : S₁ × S₂ => (n - μ₁ q.1) + (n - μ₂ q.2)) (d₀ := fun p => n - ν₀ p)
    (s := (fun q => kernelComp (fun q : S₁ × S₂ => m q.1 q.2) φ₀ (q.1, q.2)) -
      fun q => kernelComp (kernelTensor φ₁ φ₂) (fun s : T₁ × T₂ => m' s.1 s.2) (q.1, q.2))
    (fun q t₀ hq => ?_) q t₀).1 ?_).symm
  · rw [hkh] at hq
    rw [hh q t₀ (right_ne_zero_of_mul hq)]
    ring
  · -- Regrade the raw identity and read off each composite in the cochain grading.
    rw [← hk, functionalBoundary_regradeProductFunctional hδ₂deg hη₀deg,
      regradeProductFunctional_apply, hψ, kernelReadout_sub, ← hTr, ← hT'r, Pi.sub_apply,
      Pi.sub_apply, regradeProductFunctional_apply, regradeProductFunctional_apply]
    ring

end Product

end NovikovModule

end TauCeti
