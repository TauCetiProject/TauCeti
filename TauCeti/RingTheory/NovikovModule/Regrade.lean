/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Readout
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

**Associativity.** On the triple tensor product `(C₁ ⊗ C₂) ⊗ C₃` the cochain degrees of a
generator and of an output sum to `4 n` minus the raw ones, so the Koszul sign of the output
breakings does not change, and the two triple tensor differentials are conjugate by
`(-1)^(n μ₂)` alone (`TauCeti.NovikovModule.tensorDifferential_tensorDifferential_cochain`). The
regrading of a functional on `C₁ ⊗ C₂ ⊗ C₃ ⊗ C₀^∨` is therefore the multiplication by `(-1)^(n μ₂)`
(`TauCeti.NovikovModule.regradeTripleFunctional`), and it commutes with the total boundaries
(`TauCeti.NovikovModule.functionalBoundary_regradeTripleFunctional`). The cochain kernels of the
two nested products differ from the raw composites by `(-1)^(n (μ₂ + 1))` and `(-1)^(n (μ₁ + μ₂))`
(`TauCeti.NovikovModule.finsum_mul_eq_negOnePowCast_mul_finsum_left`,
`TauCeti.NovikovModule.finsum_mul_eq_negOnePowCast_mul_finsum_right`).
Consequently a raw associativity functional whose boundary is the raw readout of
`(a ⋆ b) ⋆' c` minus `(-1)^(n (μ₁ + 1))` times that of `a ⋆''' (b ⋆'' c)` yields the associativity
kernel identity of the cochain grading, by
`NovikovModule.finsum_sub_finsum_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`,
which
`TauCeti.NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`
turns into associativity up to homotopy. The sign `(-1)^(n μ₁)` is the Koszul sign of moving the
degree `-n` product past the first input.

The functional identities in the raw grading are hypotheses: they are the boundary theorems for
the oriented one-dimensional moduli spaces, which are not constructed here.

## Main definitions

* `TauCeti.NovikovModule.signTwist`: the twist of a functional by the signs `(-1)^(e(q, p₀))`;
  both regradings below are sign twists.
* `TauCeti.NovikovModule.regradeProductFunctional`: the regrading of a functional on
  `C₁ ⊗ C₂ ⊗ C₀^∨` from the raw to the cochain grading.
* `TauCeti.NovikovModule.regradeTripleFunctional`: the regrading of a functional on
  `C₁ ⊗ C₂ ⊗ C₃ ⊗ C₀^∨` from the raw to the cochain grading.

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
* `TauCeti.NovikovModule.tensorDifferential_tensorDifferential_cochain`,
  `TauCeti.NovikovModule.functionalBoundary_regradeTripleFunctional`: the triple tensor
  differentials of the two gradings are conjugate by `(-1)^(n μ₂)`, and regrading commutes with
  the total boundaries of triple functionals.
* `NovikovModule.finsum_sub_finsum_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout`
  gives the associativity kernel identity in the cochain grading from a functional identity in the
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

section SignTwist

variable (e : S → S₀ → ℤ)

/-- The **sign twist** of a functional `ψ` on `X ⊗ C₀^∨` by exponents `e`: the functional
`(-1)^(e(q, p₀)) ψ(q, p₀)`. The regradings of functionals from the raw to the cochain grading
(`TauCeti.NovikovModule.regradeProductFunctional`,
`TauCeti.NovikovModule.regradeTripleFunctional`) are sign twists. -/
def signTwist (ψ : S → S₀ → R) (q : S) (p₀ : S₀) : R :=
  negOnePowCast R (e q p₀) * ψ q p₀

/-- A value of a sign twist. -/
theorem signTwist_apply (ψ : S → S₀ → R) (q : S) (p₀ : S₀) :
    signTwist e ψ q p₀ = negOnePowCast R (e q p₀) * ψ q p₀ :=
  (rfl)

/-- A sign twist is an involution. -/
@[simp]
theorem signTwist_signTwist (ψ : S → S₀ → R) : signTwist e (signTwist e ψ) = ψ := by
  funext q p₀
  rw [signTwist_apply, signTwist_apply, ← mul_assoc, negOnePowCast_mul_self, one_mul]

/-- A sign twist is injective. -/
theorem signTwist_injective : Injective (signTwist (R := R) e) :=
  LeftInverse.injective (g := signTwist e) (signTwist_signTwist e)

/-- Two functionals have equal sign twists exactly when they are equal. -/
@[simp]
theorem signTwist_inj {ψ ψ' : S → S₀ → R} : signTwist e ψ = signTwist e ψ' ↔ ψ = ψ' :=
  (signTwist_injective e).eq_iff

/-- The sign twist of the zero functional is zero. -/
@[simp]
theorem signTwist_zero : signTwist (R := R) e 0 = 0 := by
  funext q p₀
  simp [signTwist_apply]

/-- A sign twist is additive. -/
@[simp]
theorem signTwist_add (ψ ψ' : S → S₀ → R) :
    signTwist e (ψ + ψ') = signTwist e ψ + signTwist e ψ' := by
  funext q p₀
  simp [signTwist_apply, mul_add]

/-- A sign twist commutes with negation. -/
@[simp]
theorem signTwist_neg (ψ : S → S₀ → R) : signTwist e (-ψ) = -signTwist e ψ := by
  funext q p₀
  simp [signTwist_apply]

/-- A sign twist commutes with subtraction. -/
@[simp]
theorem signTwist_sub (ψ ψ' : S → S₀ → R) :
    signTwist e (ψ - ψ') = signTwist e ψ - signTwist e ψ' := by
  funext q p₀
  simp [signTwist_apply, mul_sub]

/-- A sign twist commutes with scalar multiplication. -/
@[simp]
theorem signTwist_smul (c : R) (ψ : S → S₀ → R) : signTwist e (c • ψ) = c • signTwist e ψ := by
  funext q p₀
  simp only [signTwist_apply, Pi.smul_apply, smul_eq_mul]
  ring

end SignTwist

section Regrade

variable (n : ℤ) (μ₂ : S₂ → ℤ) (μ₀ : S₀ → ℤ)

/-- The **regrading of a product functional** `ψ` on `C₁ ⊗ C₂ ⊗ C₀^∨` from the raw degrees `μ₁`,
`μ₂`, `μ₀` to the cochain degrees `n - μ₁`, `n - μ₂`, `n - μ₀`: the functional
`(-1)^(n (μ₂ p₂ + μ₀ p₀)) ψ((p₁, p₂), p₀)`. It intertwines the total boundaries of the two gradings
(`TauCeti.NovikovModule.functionalBoundary_regradeProductFunctional`). It is the sign twist by
`n (μ₂ p₂ + μ₀ p₀)`, so the API of `TauCeti.NovikovModule.signTwist` (involution, injectivity,
linearity) applies to it. -/
abbrev regradeProductFunctional (ψ : S₁ × S₂ → S₀ → R) : S₁ × S₂ → S₀ → R :=
  signTwist (fun q p₀ => n * (μ₂ q.2 + μ₀ p₀)) ψ

/-- A value of the regrading of a product functional. -/
theorem regradeProductFunctional_apply (ψ : S₁ × S₂ → S₀ → R) (q : S₁ × S₂) (p₀ : S₀) :
    regradeProductFunctional n μ₂ μ₀ ψ q p₀ = negOnePowCast R (n * (μ₂ q.2 + μ₀ p₀)) * ψ q p₀ :=
  (rfl)

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
    rw [kernelComp_apply, kernelComp_apply, negOnePowCast_mul_finsum (n * (μ₂ x.2 + μ₀ q))]
    refine finsum_congr fun x' => ?_
    rw [tensorDifferential_cochain hδ₂, regradeProductFunctional_apply,
      ← negOnePowCast_eq_of_even_sub (a := n * (μ₂ x.2 + μ₂ x'.2) + n * (μ₂ x'.2 + μ₀ q))
        (b := n * (μ₂ x.2 + μ₀ q)) ⟨n * μ₂ x'.2, by ring⟩, negOnePowCast_add]
    ring
  -- At the output breakings the output sign changes by `(-1)^n`.
  have h₂ : kernelComp (regradeProductFunctional n μ₂ μ₀ ψ) δ₀ x q =
      negOnePowCast R (n + n * (μ₂ x.2 + μ₀ q)) * kernelComp ψ δ₀ x q := by
    rw [kernelComp_apply, kernelComp_apply, negOnePowCast_mul_finsum (n + n * (μ₂ x.2 + μ₀ q))]
    refine finsum_congr fun p => ?_
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

end Product

section Associativity

variable {S₃ S₁₂ S₂₃ : Type*} (n : ℤ) (μ₂ : S₂ → ℤ)

/-- The **regrading of a functional on a triple tensor product** `ψ` on `C₁ ⊗ C₂ ⊗ C₃ ⊗ C₀^∨`
from the raw degrees `μ₁`, `μ₂`, `μ₃`, `μ₀` to the cochain degrees `n - μ₁`, `n - μ₂`, `n - μ₃`,
`n - μ₀`: the functional `(-1)^(n μ₂ p₂) ψ(((p₁, p₂), p₃), p₀)`. It is the conjugating sign of the
tensor differentials alone: unlike for `C₁ ⊗ C₂ ⊗ C₀^∨`
(`TauCeti.NovikovModule.regradeProductFunctional`), the Koszul sign `(-1)^(d + d₀)` of the total
differential is the same in both gradings, since the cochain degrees sum to `4 n` minus the raw
ones. It intertwines the total boundaries of the two gradings
(`TauCeti.NovikovModule.functionalBoundary_regradeTripleFunctional`). It is the sign twist by
`n μ₂ p₂`, so the API of `TauCeti.NovikovModule.signTwist` (involution, injectivity, linearity)
applies to it. -/
abbrev regradeTripleFunctional (ψ : (S₁ × S₂) × S₃ → S₀ → R) : (S₁ × S₂) × S₃ → S₀ → R :=
  signTwist (fun q _ => n * μ₂ q.1.2) ψ

/-- A value of the regrading of a functional on a triple tensor product. -/
theorem regradeTripleFunctional_apply (ψ : (S₁ × S₂) × S₃ → S₀ → R) (q : (S₁ × S₂) × S₃)
    (p₀ : S₀) : regradeTripleFunctional n μ₂ ψ q p₀ = negOnePowCast R (n * μ₂ q.1.2) * ψ q p₀ :=
  (rfl)

variable {n μ₂} {μ₁ : S₁ → ℤ} {μ₃ : S₃ → ℤ} {μ₀ : S₀ → ℤ}

/-- **The regraded functional of a readout on a triple tensor product.** The regrading of the
readout of an operator kernel `t` with the raw output degrees is the readout with the cochain
output degrees of `(-1)^(n (μ₂ p₂ + 1)) t(((p₁, p₂), p₃), ·)`. No degree condition on `t` is
needed. -/
theorem regradeTripleFunctional_kernelReadout (t : (S₁ × S₂) × S₃ → S₀ → R) :
    regradeTripleFunctional n μ₂ (kernelReadout μ₀ t) =
      kernelReadout (fun p => n - μ₀ p)
        fun q p₀ => negOnePowCast R (n * (μ₂ q.1.2 + 1)) * t q p₀ := by
  funext q p₀
  rw [regradeTripleFunctional_apply, kernelReadout_apply, kernelReadout_apply, ← mul_assoc,
    ← mul_assoc, ← negOnePowCast_add, ← negOnePowCast_add]
  exact congrArg (· * t q p₀) (negOnePowCast_eq_of_even_sub ⟨μ₀ p₀ - n, by ring⟩)

/-- **Cochain kernels of a product with a product in its first input.** Let `t`, `t'` be operator
kernels out of `C₁ ⊗ C₂` and `C₁₂ ⊗ C₃`, with `t` of raw degree `-n`, and let
`l(p₁, p₂, ·) = (-1)^(n μ₁ p₁) t((p₁, p₂), ·)` and `l'(x, p₃, ·) = (-1)^(n μ₁₂ x) t'((x, p₃), ·)` be
the kernels of the cochain grading. Then the composite kernel `∑ₓ l(p₁, p₂, x) l'(x, p₃, ·)` of
`(a ⋆ b) ⋆' c` is `(-1)^(n (μ₂ p₂ + 1))` times the raw composite `∑ₓ t((p₁, p₂), x) t'((x, p₃), ·)`.
No degree condition on `t'` is needed. -/
theorem finsum_mul_eq_negOnePowCast_mul_finsum_left {μ₁₂ : S₁₂ → ℤ} {l : S₁ → S₂ → S₁₂ → R}
    {l' : S₁₂ → S₃ → S₀ → R} {t : S₁ × S₂ → S₁₂ → R} {t' : S₁₂ × S₃ → S₀ → R}
    (hlt : ∀ p₁ p₂ x, l p₁ p₂ x = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) x)
    (hlt' : ∀ x p₃ p₀, l' x p₃ p₀ = negOnePowCast R (n * μ₁₂ x) * t' (x, p₃) p₀)
    (ht : ∀ q x, t q x ≠ 0 → μ₁₂ x = μ₁ q.1 + μ₂ q.2 - n) (p₁ : S₁) (p₂ : S₂) (p₃ : S₃)
    (p₀ : S₀) :
    ∑ᶠ x, l p₁ p₂ x * l' x p₃ p₀ =
      negOnePowCast R (n * (μ₂ p₂ + 1)) * ∑ᶠ x, t (p₁, p₂) x * t' (x, p₃) p₀ := by
  rw [negOnePowCast_mul_finsum (n * (μ₂ p₂ + 1))]
  refine finsum_congr fun x => ?_
  rw [hlt, hlt']
  by_cases hx : t (p₁, p₂) x = 0
  · simp [hx]
  have he : negOnePowCast R (n * μ₁ p₁) * negOnePowCast R (n * μ₁₂ x) =
      negOnePowCast R (n * (μ₂ p₂ + 1)) := by
    rw [← negOnePowCast_add, ht (p₁, p₂) x hx]
    apply negOnePowCast_eq_of_even_sub
    -- The exponents differ by `2 n μ₁ - n (n + 1)`, which is even.
    simp only [Int.even_sub, Int.even_add, Int.even_mul]
    tauto
  linear_combination (t (p₁, p₂) x * t' (x, p₃) p₀) * he

/-- **Cochain kernels of a product with a product in its second input.** Let `v`, `v'` be operator
kernels out of `C₂ ⊗ C₃` and `C₁ ⊗ C₂₃`, and let `m(p₂, p₃, ·) = (-1)^(n μ₂ p₂) v((p₂, p₃), ·)` and
`m'(p₁, y, ·) = (-1)^(n μ₁ p₁) v'((p₁, y), ·)` be the kernels of the cochain grading. Then the
composite kernel `∑ᵧ m(p₂, p₃, y) m'(p₁, y, ·)` of `a ⋆''' (b ⋆'' c)` is `(-1)^(n (μ₁ p₁ + μ₂ p₂))`
times the raw composite `∑ᵧ v((p₂, p₃), y) v'((p₁, y), ·)`. No degree condition is needed. -/
theorem finsum_mul_eq_negOnePowCast_mul_finsum_right {m : S₂ → S₃ → S₂₃ → R}
    {m' : S₁ → S₂₃ → S₀ → R} {v : S₂ × S₃ → S₂₃ → R} {v' : S₁ × S₂₃ → S₀ → R}
    (hmv : ∀ p₂ p₃ y, m p₂ p₃ y = negOnePowCast R (n * μ₂ p₂) * v (p₂, p₃) y)
    (hmv' : ∀ p₁ y p₀, m' p₁ y p₀ = negOnePowCast R (n * μ₁ p₁) * v' (p₁, y) p₀) (p₁ : S₁)
    (p₂ : S₂) (p₃ : S₃) (p₀ : S₀) :
    ∑ᶠ y, m p₂ p₃ y * m' p₁ y p₀ =
      negOnePowCast R (n * (μ₁ p₁ + μ₂ p₂)) * ∑ᶠ y, v (p₂, p₃) y * v' (p₁, y) p₀ := by
  rw [negOnePowCast_mul_finsum (n * (μ₁ p₁ + μ₂ p₂))]
  refine finsum_congr fun y => ?_
  rw [hmv, hmv', mul_add, negOnePowCast_add]
  ring

variable [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃] {δ₁ : S₁ → S₁ → R}
  {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R} {δ₀ : S₀ → S₀ → R}

/-- **The triple tensor differentials of the two gradings are conjugate.** If `δ₂` lowers the raw
degree `μ₂` by one, the Koszul tensor differential of `(C₁ ⊗ C₂) ⊗ C₃` built with the cochain
degrees is the one built with the raw degrees, conjugated by the sign `(-1)^(n μ₂)` on generators.
Only the middle factor enters, because the sign `(-1)^(d₁ + d₂)` in front of `δ₃` is the same for
the cochain degrees `2 n - μ₁ - μ₂` as for the raw degrees `μ₁ + μ₂`. -/
theorem tensorDifferential_tensorDifferential_cochain
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) (p q : (S₁ × S₂) × S₃) :
    tensorDifferential (fun q : S₁ × S₂ => n - μ₁ q.1 + (n - μ₂ q.2))
        (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) δ₃ p q =
      negOnePowCast R (n * (μ₂ p.1.2 + μ₂ q.1.2)) *
        tensorDifferential (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) (tensorDifferential μ₁ δ₁ δ₂) δ₃
          p q := by
  rw [tensorDifferential_apply (fun q : S₁ × S₂ => n - μ₁ q.1 + (n - μ₂ q.2)),
    tensorDifferential_apply (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2), tensorDifferential_cochain hδ₂]
  by_cases h : p.1 = q.1
  · -- Along `δ₃` the first two inputs are fixed, so the conjugating sign is trivial there.
    have hs : (((n - μ₁ q.1.1 + (n - μ₂ q.1.2)).negOnePow : ℤ) : R) =
        negOnePowCast R (n * (μ₂ q.1.2 + μ₂ q.1.2)) *
          (((μ₁ q.1.1 + μ₂ q.1.2).negOnePow : ℤ) : R) := by
      rw [← negOnePowCast_eq_intCast, ← negOnePowCast_eq_intCast, ← negOnePowCast_add]
      exact negOnePowCast_eq_of_even_sub ⟨n - μ₁ q.1.1 - μ₂ q.1.2 - n * μ₂ q.1.2, by ring⟩
    rw [ite_eq_left h, ite_eq_left h, h, hs]
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    ring

/-- **Regrading commutes with the total boundaries of triple functionals.** If `δ₂` lowers the
raw degree `μ₂` by one, the boundary of the regrading of a functional `ψ` on
`C₁ ⊗ C₂ ⊗ C₃ ⊗ C₀^∨`, for the cochain degrees and the triple tensor differential built with them,
is the regrading of the boundary of `ψ` for the raw degrees and the triple tensor differential
built with them. No condition on `δ₁`, `δ₃` or `δ₀` is needed. -/
theorem functionalBoundary_regradeTripleFunctional (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1)
    (ψ : (S₁ × S₂) × S₃ → S₀ → R) :
    functionalBoundary (fun q : (S₁ × S₂) × S₃ => n - μ₁ q.1.1 + (n - μ₂ q.1.2) + (n - μ₃ q.2))
        (fun p => n - μ₀ p)
        (tensorDifferential (fun q : S₁ × S₂ => n - μ₁ q.1 + (n - μ₂ q.2))
          (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) δ₃) δ₀
        (regradeTripleFunctional n μ₂ ψ) =
      regradeTripleFunctional n μ₂
        (functionalBoundary (fun q : (S₁ × S₂) × S₃ => μ₁ q.1.1 + μ₂ q.1.2 + μ₃ q.2) μ₀
          (tensorDifferential (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) (tensorDifferential μ₁ δ₁ δ₂)
            δ₃) δ₀ ψ) := by
  funext x q
  -- At the input breakings the conjugating signs of the tensor differential cancel.
  have h₁ : kernelComp (tensorDifferential (fun q : S₁ × S₂ => n - μ₁ q.1 + (n - μ₂ q.2))
        (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) δ₃) (regradeTripleFunctional n μ₂ ψ) x q =
      negOnePowCast R (n * μ₂ x.1.2) *
        kernelComp (tensorDifferential (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2)
          (tensorDifferential μ₁ δ₁ δ₂) δ₃) ψ x q := by
    rw [kernelComp_apply, kernelComp_apply, negOnePowCast_mul_finsum (n * μ₂ x.1.2)]
    refine finsum_congr fun x' => ?_
    rw [tensorDifferential_tensorDifferential_cochain hδ₂, regradeTripleFunctional_apply,
      ← negOnePowCast_eq_of_even_sub (a := n * (μ₂ x.1.2 + μ₂ x'.1.2) + n * μ₂ x'.1.2)
        (b := n * μ₂ x.1.2) ⟨n * μ₂ x'.1.2, by ring⟩, negOnePowCast_add]
    ring
  -- At the output breakings the sign only depends on the fixed inputs.
  have h₂ : kernelComp (regradeTripleFunctional n μ₂ ψ) δ₀ x q =
      negOnePowCast R (n * μ₂ x.1.2) * kernelComp ψ δ₀ x q := by
    rw [kernelComp_apply, kernelComp_apply, negOnePowCast_mul_finsum (n * μ₂ x.1.2)]
    exact finsum_congr fun p => by rw [regradeTripleFunctional_apply, mul_assoc]
  -- The Koszul sign of the output breakings is the same in both gradings.
  have hsign : negOnePowCast R (n - μ₁ x.1.1 + (n - μ₂ x.1.2) + (n - μ₃ x.2) + (n - μ₀ q)) =
      negOnePowCast R (μ₁ x.1.1 + μ₂ x.1.2 + μ₃ x.2 + μ₀ q) :=
    negOnePowCast_eq_of_even_sub ⟨2 * n - μ₁ x.1.1 - μ₂ x.1.2 - μ₃ x.2 - μ₀ q, by ring⟩
  rw [functionalBoundary_apply, regradeTripleFunctional_apply, functionalBoundary_apply, h₁, h₂,
    hsign]
  ring

/-- **The associativity kernel identity from a functional in the raw grading.** Let `t`, `t'` be
operator kernels of raw degree `-n` for `(a ⋆ b) ⋆' c`, out of `C₁ ⊗ C₂` and `C₁₂ ⊗ C₃`, let `v`,
`v'` be those for `a ⋆''' (b ⋆'' c)`, out of `C₂ ⊗ C₃` and `C₁ ⊗ C₂₃`, and let `h` be an operator
kernel of raw degree `1 - 2 n` out of `(C₁ ⊗ C₂) ⊗ C₃`. Suppose that `δ₂` lowers the raw degree by
one. If, in the raw grading, the boundary of the readout of `h` is the readout of
`∑ₓ t((p₁, p₂), x) t'((x, p₃), ·)` minus the readout of `∑ᵧ v((p₂, p₃), y) v'((p₁, y), ·)` with the
sign `(-1)^(n (μ₁ p₁ + 1))`, then the kernels of the cochain grading

* `l(p₁, p₂, ·) = (-1)^(n μ₁ p₁) t((p₁, p₂), ·)` and `l'(x, p₃, ·) = (-1)^(n μ₁₂ x) t'((x, p₃), ·)`,
* `m(p₂, p₃, ·) = (-1)^(n μ₂ p₂) v((p₂, p₃), ·)` and `m'(p₁, y, ·) = (-1)^(n μ₁ p₁) v'((p₁, y), ·)`,
* `k(q, ·) = (-1)^(n (μ₂ p₂ + 1)) h(q, ·)` at `q = ((p₁, p₂), p₃)`,

the first four of the form of
`TauCeti.NovikovModule.regradeProductFunctional_kernelReadout_of_eq_negOnePowCast_mul`, satisfy the
associativity kernel identity of the cochain grading, as consumed by
`TauCeti.NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy`
with the cochain degrees `n - μ₁` and `n - μ₂`. So a product of raw degree `-n` which is associative
up to the sign `(-1)^(n (μ₁ + 1))` for the raw degrees is associative for the cochain degrees: the
sign is the Koszul sign of moving the degree `-n` product past the first input, twisted by
`(-1)^n`. -/
theorem finsum_sub_finsum_eq_kernelComp_add_kernelComp_of_functionalBoundary_kernelReadout
    {μ₁₂ : S₁₂ → ℤ} {l : S₁ → S₂ → S₁₂ → R} {l' : S₁₂ → S₃ → S₀ → R} {m : S₂ → S₃ → S₂₃ → R}
    {m' : S₁ → S₂₃ → S₀ → R} {k h : (S₁ × S₂) × S₃ → S₀ → R} {t : S₁ × S₂ → S₁₂ → R}
    {t' : S₁₂ × S₃ → S₀ → R} {v : S₂ × S₃ → S₂₃ → R} {v' : S₁ × S₂₃ → S₀ → R}
    (hlt : ∀ p₁ p₂ x, l p₁ p₂ x = negOnePowCast R (n * μ₁ p₁) * t (p₁, p₂) x)
    (hlt' : ∀ x p₃ p₀, l' x p₃ p₀ = negOnePowCast R (n * μ₁₂ x) * t' (x, p₃) p₀)
    (hmv : ∀ p₂ p₃ y, m p₂ p₃ y = negOnePowCast R (n * μ₂ p₂) * v (p₂, p₃) y)
    (hmv' : ∀ p₁ y p₀, m' p₁ y p₀ = negOnePowCast R (n * μ₁ p₁) * v' (p₁, y) p₀)
    (hkh : ∀ q p₀, k q p₀ = negOnePowCast R (n * (μ₂ q.1.2 + 1)) * h q p₀)
    (ht : ∀ q x, t q x ≠ 0 → μ₁₂ x = μ₁ q.1 + μ₂ q.2 - n)
    (hh : ∀ q p₀, h q p₀ ≠ 0 → μ₀ p₀ = μ₁ q.1.1 + μ₂ q.1.2 + μ₃ q.2 - 2 * n + 1)
    (hδ₂deg : ∀ p q, δ₂ p q ≠ 0 → μ₂ q = μ₂ p - 1) {q : (S₁ × S₂) × S₃} {p₀ : S₀}
    (hψ : functionalBoundary (fun q : (S₁ × S₂) × S₃ => μ₁ q.1.1 + μ₂ q.1.2 + μ₃ q.2) μ₀
      (tensorDifferential (fun q : S₁ × S₂ => μ₁ q.1 + μ₂ q.2) (tensorDifferential μ₁ δ₁ δ₂) δ₃)
      δ₀ (kernelReadout μ₀ h) q p₀ =
        kernelReadout μ₀ (fun q p₀ => ∑ᶠ x, t (q.1.1, q.1.2) x * t' (x, q.2) p₀) q p₀ -
          negOnePowCast R (n * (μ₁ q.1.1 + 1)) *
            kernelReadout μ₀ (fun q p₀ => ∑ᶠ y, v (q.1.2, q.2) y * v' (q.1.1, y) p₀) q p₀) :
    ∑ᶠ x, l q.1.1 q.1.2 x * l' x q.2 p₀ - ∑ᶠ y, m q.1.2 q.2 y * m' q.1.1 y p₀ =
      kernelComp k δ₀ q p₀ +
        kernelComp (tensorDifferential (fun q : S₁ × S₂ => n - μ₁ q.1 + (n - μ₂ q.2))
          (tensorDifferential (fun p => n - μ₁ p) δ₁ δ₂) δ₃) k q p₀ := by
  have hN := finsum_mul_eq_negOnePowCast_mul_finsum_left hlt hlt' ht q.1.1 q.1.2 q.2 p₀
  have hM := finsum_mul_eq_negOnePowCast_mul_finsum_right (μ₁ := μ₁) hmv hmv' q.1.1 q.1.2 q.2 p₀
  -- The cochain readout of `k` is the regrading of the raw readout of `h`.
  have hk : kernelReadout (fun p => n - μ₀ p) k =
      regradeTripleFunctional n μ₂ (kernelReadout μ₀ h) := by
    rw [regradeTripleFunctional_kernelReadout]
    exact congrArg _ (funext fun q => funext fun p₀ => hkh q p₀)
  have e₁ : negOnePowCast R (n * μ₂ q.1.2) * negOnePowCast R (μ₀ p₀) =
      negOnePowCast R (n - μ₀ p₀) * negOnePowCast R (n * (μ₂ q.1.2 + 1)) := by
    rw [← negOnePowCast_add, ← negOnePowCast_add]
    exact negOnePowCast_eq_of_even_sub ⟨μ₀ p₀ - n, by ring⟩
  have e₂ : negOnePowCast R (n * μ₂ q.1.2) * negOnePowCast R (n * (μ₁ q.1.1 + 1)) *
      negOnePowCast R (μ₀ p₀) =
      negOnePowCast R (n - μ₀ p₀) * negOnePowCast R (n * (μ₁ q.1.1 + μ₂ q.1.2)) := by
    simp only [← negOnePowCast_add]
    exact negOnePowCast_eq_of_even_sub ⟨μ₀ p₀, by ring⟩
  refine finsum_sub_finsum_eq_kernelComp_add_kernelComp_of_functionalBoundary
    (d₁ := fun p => n - μ₁ p) (d₂ := fun p => n - μ₂ p) (d₃ := fun p => n - μ₃ p)
    (d₀ := fun p => n - μ₀ p) (fun q p₀ hq => ?_) ?_
  · rw [hkh] at hq
    rw [hh q p₀ (right_ne_zero_of_mul hq)]
    ring
  · -- Regrade the raw identity and read off each term in the cochain grading.
    rw [hk, functionalBoundary_regradeTripleFunctional hδ₂deg, regradeTripleFunctional_apply, hψ]
    simp only [kernelReadout_apply]
    rw [hN, hM]
    linear_combination (∑ᶠ x, t (q.1.1, q.1.2) x * t' (x, q.2) p₀) * e₁ -
      (∑ᶠ y, v (q.1.2, q.2) y * v' (q.1.1, y) p₀) * e₂

end Associativity

end NovikovModule

end TauCeti
