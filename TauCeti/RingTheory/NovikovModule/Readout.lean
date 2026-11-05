/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Leibniz
public import TauCeti.RingTheory.NovikovModule.Tensor
import TauCeti.Algebra.BigOperators.Finprod
import Mathlib.Tactic.LinearCombination

/-!
# Operator readout of count functionals

Counts of rigid moduli spaces with inputs in a graded complex `X` (for instance the tensor product
`C₁ ⊗ C₂` of two Floer complexes) and output in a graded complex `C₀` are naturally functionals on
`X ⊗ C₀^∨`: the orientation of a moduli space is read off from an ordered determinant sequence in
which the inputs come first and the output enters through its dual. On generators such a
functional is a kernel `φ : S → S₀ → R`, where `φ(x, q)` is its value on `x ⊗ q^∨`. Operations,
on the other hand, are given by operator kernels `t : S → S₀ → R`, where `t(x, q)` is the
coefficient of `q` in the image of `x`, as in `TauCeti.NovikovModule.kernelMap`.

The two are related by a coefficientwise sign involution of kernels
(`NovikovModule.kernelReadout`): the coefficient at an output generator `q` of degree `d₀ q` is
multiplied by `(-1)^(d₀ q)`, and the same formula converts functionals back to operators. It is
not the ungraded transpose. The sign is the one of the graded bidual map
`p ↦ (f ↦ (-1)^(|p| |f|) f(p))`; when `C₀` is free of finite rank in each degree this map is an
isomorphism, and composing it with currying gives the identification
`Hom(X, C₀) ≅ Hom(X, C₀^∨∨) ≅ Hom(X ⊗ C₀^∨, R)`. For general complexes only the kernel-level
involution is used here; no duality isomorphism is claimed.

The differentials are the Koszul ones: `C₀^∨` carries `δ₀^∨ f = -(-1)^|f| f ∘ δ₀`, the tensor
product carries `δ ⊗ 1 + (-1)^|x| 1 ⊗ δ₀^∨`, and the value at `x ⊗ q^∨` of a functional `ψ`
composed with this total differential is

`∑ δ(x, x') ψ(x', q) - (-1)^(d x + d₀ q) ∑ ψ(x, p) δ₀(p, q)`

(`NovikovModule.functionalBoundary`). In a count, the first sum collects the breakings at the
inputs and the second the breakings at the output. Operators of degree `j` carry the Hom
differential `D t = δ₀ ∘ t - (-1)^j t ∘ δ`. The readout intertwines the two
(`NovikovModule.functionalBoundary_kernelReadout`):

`ψ ∘ D = (-1)^(j + 1) (readout of D t)`  for `ψ` the readout of `t`.

This is the precise sense in which the operator sign equations follow from the ordered functional
conventions, without multiplying any count by an extra sign afterwards. A closed functional of
degree `0` is the readout of a chain map
(`NovikovModule.functionalBoundary_kernelReadout_eq_zero_iff`). A
functional of degree `-1` whose boundary is the difference of two readouts is the readout of a
chain homotopy `K` between the two operators, `T - T' = δ₀ ∘ K + K ∘ δ`
(`NovikovModule.functionalBoundary_kernelReadout_eq_kernelReadout_iff`).

For the product, the source is `C₁ ⊗ C₂` with total degree `d₁ + d₂` and the Koszul tensor
differential `TauCeti.NovikovModule.tensorDifferential`. A closed count functional of degree `0`
then gives the Leibniz rule `δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b` on completed combinations,
with the `(-1)^i` of the tensor differential
(`NovikovModule.kernelMap_kernelProduct_eq_add_of_functionalBoundary_eq_zero`). For the exchange
of inputs, a degree `-1` functional whose boundary is the readout of `n` minus the readout of the
exchanged kernel `n'` with the Koszul sign `(-1)^(d₁ p₁ d₂ p₂)` gives the commutativity kernel
identity consumed by
`TauCeti.NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`
(`NovikovModule.sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary`).

The functional identities themselves are hypotheses: they are the boundary theorems for oriented
one-dimensional moduli spaces, which are not constructed here.

## Main definitions

* `TauCeti.NovikovModule.kernelReadout`: the graded identification of functional and operator
  kernels.
* `TauCeti.NovikovModule.functionalBoundary`: a functional kernel composed with the Koszul total
  differential of `X ⊗ C₀^∨`.

## Main results

* `TauCeti.NovikovModule.functionalBoundary_kernelReadout`: the readout intertwines the Hom
  differential of operators with the boundary of functionals.
* `TauCeti.NovikovModule.kernelMap_kernelProduct_eq_add_of_functionalBoundary_eq_zero`: the
  Leibniz rule from a closed product functional.
* `TauCeti.NovikovModule.sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary`:
  the commutativity homotopy identity from an exchange functional.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the pair-of-pants product and its orientations.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 11 and 12,
  on orientation lines and the signs of operations read off from them.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

variable {R S S₀ : Type*} [CommRing R]

section Readout

/-- The **operator readout** of a functional kernel `φ` on `X ⊗ C₀^∨`, for the degree function
`d₀` on the output generators: the operator kernel `(-1)^(d₀ q) φ(x, q)`. This is a
coefficientwise sign involution, with the sign of the graded bidual map
`p ↦ (f ↦ (-1)^(|p| |f|) f(p))`; when `C₀` is free of finite rank in each degree it induces the
identification `Hom(X ⊗ C₀^∨, R) ≅ Hom(X, C₀)`. The same formula converts operator kernels to
functionals (`NovikovModule.kernelReadout_kernelReadout`). -/
def kernelReadout (d₀ : S₀ → ℤ) (φ : S → S₀ → R) (x : S) (q : S₀) : R :=
  negOnePowCast R (d₀ q) * φ x q

/-- A coefficient of the readout of a functional kernel. -/
theorem kernelReadout_apply (d₀ : S₀ → ℤ) (φ : S → S₀ → R) (x : S) (q : S₀) :
    kernelReadout d₀ φ x q = negOnePowCast R (d₀ q) * φ x q :=
  (rfl)

/-- The readout is an involution: reading out twice returns the original kernel. -/
@[simp]
theorem kernelReadout_kernelReadout (d₀ : S₀ → ℤ) (φ : S → S₀ → R) :
    kernelReadout d₀ (kernelReadout d₀ φ) = φ := by
  funext x q
  rw [kernelReadout_apply, kernelReadout_apply, ← mul_assoc, negOnePowCast_mul_self, one_mul]

/-- The readout of the zero kernel is zero. -/
@[simp]
theorem kernelReadout_zero (d₀ : S₀ → ℤ) : kernelReadout (R := R) (S := S) d₀ 0 = 0 := by
  funext x q
  simp [kernelReadout_apply]

/-- The readout is additive. -/
@[simp]
theorem kernelReadout_add (d₀ : S₀ → ℤ) (φ ψ : S → S₀ → R) :
    kernelReadout d₀ (φ + ψ) = kernelReadout d₀ φ + kernelReadout d₀ ψ := by
  funext x q
  simp [kernelReadout_apply, mul_add]

/-- The readout commutes with negation. -/
@[simp]
theorem kernelReadout_neg (d₀ : S₀ → ℤ) (φ : S → S₀ → R) :
    kernelReadout d₀ (-φ) = -kernelReadout d₀ φ := by
  funext x q
  simp [kernelReadout_apply]

/-- The readout commutes with subtraction. -/
@[simp]
theorem kernelReadout_sub (d₀ : S₀ → ℤ) (φ ψ : S → S₀ → R) :
    kernelReadout d₀ (φ - ψ) = kernelReadout d₀ φ - kernelReadout d₀ ψ := by
  funext x q
  simp [kernelReadout_apply, mul_sub]

/-- The readout commutes with scalar multiplication. -/
@[simp]
theorem kernelReadout_smul (d₀ : S₀ → ℤ) (c : R) (φ : S → S₀ → R) :
    kernelReadout d₀ (c • φ) = c • kernelReadout d₀ φ := by
  funext x q
  simp only [kernelReadout_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The readout commutes with multiplication by a pointwise factor `c(x, q)`. -/
theorem kernelReadout_mul_left (d₀ : S₀ → ℤ) (c φ : S → S₀ → R) :
    kernelReadout d₀ (c * φ) = c * kernelReadout d₀ φ := by
  funext x q
  simp only [kernelReadout_apply, Pi.mul_apply]
  ring

/-- The readout is injective. -/
theorem kernelReadout_injective (d₀ : S₀ → ℤ) :
    Injective (kernelReadout (R := R) (S := S) d₀) :=
  LeftInverse.injective (g := kernelReadout d₀) (kernelReadout_kernelReadout d₀)

/-- Two kernels have equal readouts exactly when they are equal. -/
@[simp]
theorem kernelReadout_inj {d₀ : S₀ → ℤ} {φ ψ : S → S₀ → R} :
    kernelReadout d₀ φ = kernelReadout d₀ ψ ↔ φ = ψ :=
  (kernelReadout_injective d₀).eq_iff

/-- Two kernels have equal readouts at a pair of generators exactly when they agree there. -/
@[simp]
theorem kernelReadout_apply_eq_kernelReadout_apply_iff {d₀ : S₀ → ℤ} {φ ψ : S → S₀ → R} {x : S}
    {q : S₀} : kernelReadout d₀ φ x q = kernelReadout d₀ ψ x q ↔ φ x q = ψ x q := by
  refine ⟨fun h => ?_, fun h => by rw [kernelReadout_apply, kernelReadout_apply, h]⟩
  simpa [kernelReadout_apply, ← mul_assoc] using congrArg (negOnePowCast R (d₀ q) * ·) h

end Readout

section Boundary

/-- The **boundary of a functional kernel** `ψ` on `X ⊗ C₀^∨`: its value at `x ⊗ q^∨` after
composing with the Koszul total differential `δ ⊗ 1 + (-1)^|x| 1 ⊗ δ₀^∨`, where
`δ₀^∨ f = -(-1)^|f| f ∘ δ₀` and `q^∨` has degree `-d₀ q`. Explicitly it is
`∑ δ(x, x') ψ(x', q) - (-1)^(d x + d₀ q) ∑ ψ(x, p) δ₀(p, q)`. -/
def functionalBoundary (d : S → ℤ) (d₀ : S₀ → ℤ) (δ : S → S → R) (δ₀ : S₀ → S₀ → R)
    (ψ : S → S₀ → R) (x : S) (q : S₀) : R :=
  kernelComp δ ψ x q - negOnePowCast R (d x + d₀ q) * kernelComp ψ δ₀ x q

/-- A value of the boundary of a functional kernel. -/
theorem functionalBoundary_apply (d : S → ℤ) (d₀ : S₀ → ℤ) (δ : S → S → R) (δ₀ : S₀ → S₀ → R)
    (ψ : S → S₀ → R) (x : S) (q : S₀) :
    functionalBoundary d d₀ δ δ₀ ψ x q =
      kernelComp δ ψ x q - negOnePowCast R (d x + d₀ q) * kernelComp ψ δ₀ x q :=
  (rfl)

variable {d : S → ℤ} {d₀ : S₀ → ℤ} {δ : S → S → R} {δ₀ : S₀ → S₀ → R} {j : ℤ}

/-- **The readout intertwines the differentials.** Let `t` be an operator kernel of degree `j`,
so `t(x, p) ≠ 0` only if `d₀ p = d x + j`. Then the boundary of its readout is `(-1)^(j + 1)` times
the readout of its Hom differential `D t = δ₀ ∘ t - (-1)^j t ∘ δ`, with kernel
`∑ t(x, p) δ₀(p, q) - (-1)^j ∑ δ(x, x') t(x', q)`. No degree condition on `δ` or `δ₀` is needed. -/
theorem functionalBoundary_kernelReadout {t : S → S₀ → R}
    (ht : ∀ x p, t x p ≠ 0 → d₀ p = d x + j) (x : S) (q : S₀) :
    functionalBoundary d d₀ δ δ₀ (kernelReadout d₀ t) x q =
      negOnePowCast R (j + 1) * kernelReadout d₀
        (fun x q => kernelComp t δ₀ x q - negOnePowCast R j * kernelComp δ t x q) x q := by
  -- The input breakings carry the sign of the fixed output `q`.
  have h₁ : kernelComp δ (kernelReadout d₀ t) x q =
      negOnePowCast R (d₀ q) * kernelComp δ t x q := by
    rw [kernelComp_apply, kernelComp_apply,
      (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self (d₀ q))).mul_finsum]
    exact finsum_congr fun x' => by rw [kernelReadout_apply]; ring
  -- At the output breakings, `t` is supported in degree `d x + j`.
  have h₂ : kernelComp (kernelReadout d₀ t) δ₀ x q =
      negOnePowCast R (d x + j) * kernelComp t δ₀ x q := by
    rw [kernelComp_apply, kernelComp_apply,
      (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self (d x + j))).mul_finsum]
    refine finsum_congr fun p => ?_
    by_cases hp : t x p = 0
    · simp [kernelReadout_apply, hp]
    · rw [kernelReadout_apply, ht x p hp, mul_assoc]
  rw [functionalBoundary_apply, kernelReadout_apply, h₁, h₂]
  simp only [negOnePowCast_add, negOnePowCast_one]
  linear_combination
    (-(negOnePowCast R (d₀ q) * negOnePowCast R j * kernelComp t δ₀ x q)) *
      negOnePowCast_mul_self (R := R) (d x) +
    (-(negOnePowCast R (d₀ q) * kernelComp δ t x q)) * negOnePowCast_mul_self (R := R) j

/-- **Closed functionals are chain maps.** For an operator kernel `t` of degree `0`, the readout
of `t` is annihilated by the total differential at `x ⊗ q^∨` exactly when the composite kernels
`∑ t(x, p) δ₀(p, q)` and `∑ δ(x, x') t(x', q)` agree there. For all `x` and `q` this says that the
operator `T` of `t` satisfies `δ₀ ∘ T = T ∘ δ`. -/
theorem functionalBoundary_kernelReadout_eq_zero_iff {t : S → S₀ → R}
    (ht : ∀ x p, t x p ≠ 0 → d₀ p = d x) (x : S) (q : S₀) :
    functionalBoundary d d₀ δ δ₀ (kernelReadout d₀ t) x q = 0 ↔
      kernelComp t δ₀ x q = kernelComp δ t x q := by
  have ht' : ∀ x p, t x p ≠ 0 → d₀ p = d x + 0 := fun x p hp => by rw [add_zero, ht x p hp]
  rw [functionalBoundary_kernelReadout ht']
  simp only [kernelReadout_apply, zero_add, negOnePowCast_one, negOnePowCast_zero, one_mul,
    neg_one_mul, neg_eq_zero]
  refine ⟨fun h => sub_eq_zero.1 ?_, fun h => by rw [h, sub_self, mul_zero]⟩
  simpa [← mul_assoc] using congrArg (negOnePowCast R (d₀ q) * ·) h

/-- **Functionals with prescribed boundary are chain homotopies.** For an operator kernel `k` of
degree `-1`, the boundary of the readout of `k` at `x ⊗ q^∨` is the readout of `s` exactly when
`∑ k(x, p) δ₀(p, q) + ∑ δ(x, x') k(x', q) = s(x, q)`. For all `x` and `q` this says that the
operator `K` of `k` satisfies `δ₀ ∘ K + K ∘ δ = S`. A homotopy between operators `T` and `T'` is
the case `s = t - t'`, whose readout is the readout of `t` minus the readout of `t'`. -/
theorem functionalBoundary_kernelReadout_eq_kernelReadout_iff {k s : S → S₀ → R}
    (hk : ∀ x p, k x p ≠ 0 → d₀ p = d x - 1) (x : S) (q : S₀) :
    functionalBoundary d d₀ δ δ₀ (kernelReadout d₀ k) x q = kernelReadout d₀ s x q ↔
      kernelComp k δ₀ x q + kernelComp δ k x q = s x q := by
  have hk' : ∀ x p, k x p ≠ 0 → d₀ p = d x + -1 := fun x p hp => by
    rw [hk x p hp, sub_eq_add_neg]
  rw [functionalBoundary_kernelReadout hk', neg_add_cancel, negOnePowCast_zero, one_mul,
    kernelReadout_apply_eq_kernelReadout_apply_iff]
  simp only [negOnePowCast_neg, negOnePowCast_one, neg_one_mul, sub_neg_eq_add]

end Boundary

section Product

variable {S₁ S₂ : Type*} [DecidableEq S₁] [DecidableEq S₂]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {C C₁ C₂ C₀ : ℝ} {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  {δ₁ : S₁ → S₁ → R} (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + C₁)
  (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  {δ₂ : S₂ → S₂ → R} (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + C₂)
  (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  {δ₀ : S₀ → S₀ → R} (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀)
  (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
  {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ}

include hn hδ₁fin hδ₂fin in
/-- **The Leibniz kernel identity from a closed product functional.** Let the product kernel `n`
have cochain degree `0`. If the readout of `n`, a functional on `C₁ ⊗ C₂ ⊗ C₀^∨`, is annihilated
by the total differential built from the Koszul tensor differential of `C₁ ⊗ C₂`, then `n` obeys
the Leibniz identity between kernels
`∑ n(p₁, p₂, p) δ₀(p, p₀) = ∑ δ₁(p₁, p) n(p, p₂, p₀) + (-1)^(d₁ p₁) ∑ δ₂(p₂, p) n(p₁, p, p₀)`
of `TauCeti.NovikovModule.kernelMap_kernelProduct_eq_add`. -/
theorem kernelComp_eq_add_of_functionalBoundary_eq_zero
    (hdeg : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂)
    {p₁ : S₁} {p₂ : S₂} {p₀ : S₀}
    (hφ : functionalBoundary (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) d₀
      (tensorDifferential d₁ δ₁ δ₂) δ₀ (kernelReadout d₀ fun q => n q.1 q.2) (p₁, p₂) p₀ = 0) :
    kernelComp (n p₁) δ₀ p₂ p₀ =
      kernelComp δ₁ (fun p => n p p₂) p₁ p₀ +
        negOnePowCast R (d₁ p₁) * kernelComp δ₂ (n p₁) p₂ p₀ := by
  have hc := (functionalBoundary_kernelReadout_eq_zero_iff
    (fun q p₀ h => hdeg q.1 q.2 p₀ h) (p₁, p₂) p₀).1 hφ
  -- Only finitely many intermediate generators contribute, by the potential bounds.
  have h₁ : (support fun q₁ => δ₁ p₁ q₁ * n q₁ p₂ p₀).Finite :=
    finite_support_mul (κ := fun q₁ => n q₁ p₂ p₀) (T := F₀ p₀ - F₂ p₂ - C)
      (fun q₁ hq₁ => by linarith [hn q₁ p₂ p₀ hq₁]) ⟨δ₁ p₁, hδ₁fin p₁⟩
  have h₂ : (support fun q₂ => δ₂ p₂ q₂ * n p₁ q₂ p₀).Finite :=
    finite_support_mul (κ := fun q₂ => n p₁ q₂ p₀) (T := F₀ p₀ - F₁ p₁ - C)
      (fun q₂ hq₂ => by linarith [hn p₁ q₂ p₀ hq₂]) ⟨δ₂ p₂, hδ₂fin p₂⟩
  have h := hc.trans (kernelComp_tensorDifferential (fun q => n q.1 q.2) p₁ p₂ p₀ h₁ h₂)
  rw [negOnePowCast_eq_intCast]
  simpa only [kernelComp_apply] using h

include hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin in
/-- **The Leibniz rule from a closed product functional.** If the product kernel `n` has cochain
degree `0` and its readout is annihilated by the total differential of `C₁ ⊗ C₂ ⊗ C₀^∨`, as the
boundary count of one-dimensional product moduli spaces asserts, then for a completed combination
`a` of degree `i` and any completed combination `b`,
`δ₀ (a ⋆ b) = δ₁ a ⋆ b + (-1)^i a ⋆ δ₂ b`. -/
theorem kernelMap_kernelProduct_eq_add_of_functionalBoundary_eq_zero
    (hdeg : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ + d₂ p₂)
    (hφ : ∀ q p₀, functionalBoundary (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) d₀
      (tensorDifferential d₁ δ₁ δ₂) δ₀ (kernelReadout d₀ fun q => n q.1 q.2) q p₀ = 0)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b) :=
  kernelMap_kernelProduct_eq_add hn hfin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₀ hδ₀fin
    (fun _ _ _ => kernelComp_eq_add_of_functionalBoundary_eq_zero hn hδ₁fin hδ₂fin hdeg (hφ _ _))
    ha b

/-- **The commutativity homotopy from an exchange functional.** Let `n` and `n'` be product
kernels on `S₁ × S₂` and `S₂ × S₁`, and let `k` be a kernel of degree `-1` out of `C₁ ⊗ C₂`. If
the boundary of the readout of `k` is the readout of `n` minus the readout of the exchanged kernel
`(-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, ·)` with its Koszul sign, then `k` is a kernel homotopy
`n(p₁, p₂, p₀) - (-1)^(d₁ p₁ d₂ p₂) n'(p₂, p₁, p₀) = ∑ k(q, p) δ₀(p, p₀) + ∑ δ⊗(q, q') k(q', p₀)`
at `q = (p₁, p₂)`, where `δ⊗` is the tensor differential `tensorDifferential d₁ δ₁ δ₂`, as consumed
by
`TauCeti.NovikovModule.kernelProduct_sub_negOnePow_smul_kernelProduct_of_tensorDifferential`. -/
theorem sub_negOnePow_mul_eq_kernelComp_add_kernelComp_of_functionalBoundary
    {n' : S₂ → S₁ → S₀ → R} {k : S₁ × S₂ → S₀ → R}
    (hk : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1 + d₂ q.2 - 1)
    {q : S₁ × S₂} {p₀ : S₀}
    (hψ : functionalBoundary (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) d₀
      (tensorDifferential d₁ δ₁ δ₂) δ₀ (kernelReadout d₀ k) q p₀ =
        kernelReadout d₀ (fun q => n q.1 q.2) q p₀ -
          ((d₁ q.1 * d₂ q.2).negOnePow : R) * kernelReadout d₀ (fun q => n' q.2 q.1) q p₀) :
    n q.1 q.2 p₀ - ((d₁ q.1 * d₂ q.2).negOnePow : R) * n' q.2 q.1 p₀ =
      kernelComp k δ₀ q p₀ + kernelComp (tensorDifferential d₁ δ₁ δ₂) k q p₀ := by
  refine ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
    (s := (fun q => n q.1 q.2) -
      (fun q _ => ((d₁ q.1 * d₂ q.2).negOnePow : R)) * fun q => n' q.2 q.1)
    hk q p₀).1 ?_).symm
  rw [hψ, kernelReadout_sub, kernelReadout_mul_left]
  rfl

end Product

end NovikovModule

end TauCeti
