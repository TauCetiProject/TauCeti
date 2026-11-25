/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Readout
public import TauCeti.RingTheory.NovikovModule.Associativity
public import TauCeti.RingTheory.NovikovModule.Unit
public import TauCeti.RingTheory.NovikovModule.Continuation
public import TauCeti.RingTheory.NovikovModule.Comparison
import TauCeti.Algebra.BigOperators.Finprod
import Mathlib.Tactic.LinearCombination

/-!
# Coevaluation sewing of count functionals and operator homotopy readouts

In `TauCeti.RingTheory.NovikovModule.Readout`, counts of rigid moduli spaces from `X` to `C₀` are
represented as functional kernels `φ : S → S₀ → R` on `X ⊗ C₀^∨` and converted to operator kernels
by the graded bidual involution `NovikovModule.kernelReadout` (`q ↦ (-1)^(d₀ q)`). When a family of
punctured Riemann surfaces degenerates at a neck, the upstream output dual `p^∨ ∈ C₁^∨` contracts
with the downstream input `p ∈ C₁` along `1 ↦ ∑ₚ (-1)^(d₁ p) p^∨ ⊗ p`, dual to the right evaluation
`NovikovModule.evalFunctional` (`p ⊗ q^∨ ↦ (-1)^(d₁ p) [p = q]`). On functional kernels this gives
`NovikovModule.functionalSew`: `(φ # ψ)(x, q) = ∑ₚ (-1)^(d₁ p) φ(x, p) ψ(p, q)`.

Reading out a sewn functional composes the readouts of its factors (`functionalSew_kernelReadout`,
`kernelReadout_functionalSew`), satisfies both snake identities against `evalFunctional`, and obeys
a graded Leibniz law (`functionalBoundary_functionalSew`). Sewing into non-adjacent inputs inserts
the Koszul braiding sign of graded complexes:

* **Cap sewing and unit gluing:** `NovikovModule.combinationReadout` identifies a cap functional on
  `C₁^∨` with a combination via `(-1)^(d₁ p)`. Left sewing (`functionalSewCapLeft`) needs no swap;
  right sewing (`functionalSewCapRight`) braids `p₁ ∈ C₁` past `C₂^∨` with `(-1)^(d₁ p₁ d₂ t)`.
* **Product sewing and associativity:** Left sewing (`functionalSewProdLeft`) needs no swap; right
  sewing (`functionalSewProdRight`) braids `p₁` past `C₂ ⊗ C₃ ⊗ C₂₃^∨` with
  `(-1)^(d₁ p₁ (d₂ p₂ + d₃ p₃ - d₂₃ u))`.
* **Pair sewing, continuation, and PSS:** Sewing two one-input functionals into a product
  functional (`functionalSewPair`) braids `t₁ ∈ T₁` past `C₂ ⊗ T₂^∨` with
  `(-1)^(e₁ t₁ (d₂ p₂ - e₂ t₂))`, which is `+1` when the second map preserves degree parity.

Combining these comparisons with `functionalBoundary_kernelReadout_eq_kernelReadout_iff` derives
the unit, associativity, continuation, and multiplicative PSS homotopies on completed Novikov
modules directly from boundary identities of count functionals.

## Main definitions

* `TauCeti.NovikovModule.functionalSew`, `TauCeti.NovikovModule.evalFunctional`,
  `TauCeti.NovikovModule.combinationReadout`: coevaluation sewing, right evaluation, and no-input
  combination readout.
* `TauCeti.NovikovModule.functionalSewCapLeft`, `TauCeti.NovikovModule.functionalSewCapRight`,
  `TauCeti.NovikovModule.functionalSewProdLeft`, `TauCeti.NovikovModule.functionalSewProdRight`,
  `TauCeti.NovikovModule.functionalSewPair`: Koszul-braided cap, product, and input-pair sewings.

## Main results

* `TauCeti.NovikovModule.functionalSew_kernelReadout`,
  `TauCeti.NovikovModule.kernelReadout_functionalSew`,
  `TauCeti.NovikovModule.functionalBoundary_functionalSew`: readout functoriality and Leibniz law.
* `TauCeti.NovikovModule.kernelProduct_sub_kernelMap_right_of_functionalBoundary`,
  `TauCeti.NovikovModule.kernelProduct_sub_kernelMap_left_of_functionalBoundary`,
  `NovikovModule.kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_functionalBoundary`,
  `TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_functionalBoundary`,
  `TauCeti.NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct_of_functionalBoundary`:
  completed-module operator homotopies from count-functional boundaries.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995).
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 11 and 12.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

private theorem negOnePowCast_mul_finsum {R α : Type*} [CommRing R] (k : ℤ) (f : α → R) :
    negOnePowCast R k * ∑ᶠ x, f x = ∑ᶠ x, negOnePowCast R k * f x :=
  (isLeftRegular_of_mul_eq_one (negOnePowCast_mul_self (R := R) k)).mul_finsum f

private theorem eq_negOnePowCast_mul_kernelReadout {R α β : Type*} [CommRing R] {d₀ : β → ℤ}
    {f g : α → β → R} {x : α} {q : β} {k : ℤ}
    (h : kernelReadout d₀ f x q = negOnePowCast R k * g x q) :
    f x q = negOnePowCast R k * kernelReadout d₀ g x q := by
  rw [← kernelReadout_kernelReadout d₀ f, kernelReadout_apply, h, kernelReadout_apply]
  ring

section Sewing

variable {R S S₁ S₀ : Type*} [CommRing R]

/-- **Coevaluation sewing of functional kernels.** Contracts the intermediate dual generator `p^∨`
with `p` via `1 ↦ ∑ₚ (-1)^(d₁ p) p^∨ ⊗ p`, producing `∑ₚ (-1)^(d₁ p) φ(x, p) ψ(p, q)`. -/
def functionalSew (d₁ : S₁ → ℤ) (φ : S → S₁ → R) (ψ : S₁ → S₀ → R) (x : S) (q : S₀) : R :=
  ∑ᶠ p, negOnePowCast R (d₁ p) * φ x p * ψ p q

/-- A value of the coevaluation sewing of two functional kernels. -/
theorem functionalSew_apply (d₁ : S₁ → ℤ) (φ : S → S₁ → R) (ψ : S₁ → S₀ → R) (x : S) (q : S₀) :
    functionalSew d₁ φ ψ x q = ∑ᶠ p, negOnePowCast R (d₁ p) * φ x p * ψ p q := (rfl)

/-- Coevaluation sewing along `C₁` is kernel composition with the upstream readout applied first. -/
theorem functionalSew_eq_kernelComp_kernelReadout (d₁ : S₁ → ℤ) (φ : S → S₁ → R)
    (ψ : S₁ → S₀ → R) :
    functionalSew d₁ φ ψ = kernelComp (kernelReadout d₁ φ) ψ := by
  funext x q; simp only [functionalSew_apply, kernelComp_apply, kernelReadout_apply]

/-- Operator readout at the output commutes with precomposition by any input kernel. -/
@[simp]
theorem kernelComp_kernelReadout_right (d₀ : S₀ → ℤ) (t : S → S₁ → R) (s : S₁ → S₀ → R) :
    kernelComp t (kernelReadout d₀ s) = kernelReadout d₀ (kernelComp t s) := by
  funext x q
  rw [kernelComp_apply, kernelReadout_apply, kernelComp_apply, negOnePowCast_mul_finsum]
  exact finsum_congr fun p => by rw [kernelReadout_apply]; ring

@[simp]
theorem functionalSew_zero_left (d₁ : S₁ → ℤ) (ψ : S₁ → S₀ → R) :
    functionalSew (S := S) d₁ 0 ψ = 0 := by funext x q; simp [functionalSew_apply]

@[simp]
theorem functionalSew_zero_right (d₁ : S₁ → ℤ) (φ : S → S₁ → R) :
    functionalSew (S₀ := S₀) d₁ φ 0 = 0 := by funext x q; simp [functionalSew_apply]

theorem functionalSew_neg_left (d₁ : S₁ → ℤ) (φ : S → S₁ → R) (ψ : S₁ → S₀ → R) :
    functionalSew d₁ (-φ) ψ = -functionalSew d₁ φ ψ := by
  funext x q; simp only [functionalSew_apply, Pi.neg_apply, mul_neg, neg_mul, finsum_neg_distrib]

theorem functionalSew_neg_right (d₁ : S₁ → ℤ) (φ : S → S₁ → R) (ψ : S₁ → S₀ → R) :
    functionalSew d₁ φ (-ψ) = -functionalSew d₁ φ ψ := by
  funext x q; simp only [functionalSew_apply, Pi.neg_apply, mul_neg, finsum_neg_distrib]

/-- **Sewing the readouts of two operator kernels gives the readout of their composite.** Neither
degree hypotheses nor finiteness of the intermediate support are needed. -/
theorem functionalSew_kernelReadout (d₁ : S₁ → ℤ) (d₀ : S₀ → ℤ) (t : S → S₁ → R)
    (s : S₁ → S₀ → R) :
    functionalSew d₁ (kernelReadout d₁ t) (kernelReadout d₀ s) =
      kernelReadout d₀ (kernelComp t s) := by
  rw [functionalSew_eq_kernelComp_kernelReadout, kernelReadout_kernelReadout,
    kernelComp_kernelReadout_right]

/-- **Operator readout turns coevaluation sewing into kernel composition.** -/
@[simp]
theorem kernelReadout_functionalSew (d₁ : S₁ → ℤ) (d₀ : S₀ → ℤ) (φ : S → S₁ → R)
    (ψ : S₁ → S₀ → R) :
    kernelReadout d₀ (functionalSew d₁ φ ψ) =
      kernelComp (kernelReadout d₁ φ) (kernelReadout d₀ ψ) := by
  rw [functionalSew_eq_kernelComp_kernelReadout, ← kernelComp_kernelReadout_right]

section EvalFunctional

/-- **The right-evaluation functional** `γ_min : C ⊗ C^∨ → R`, taking value `(-1)^(d p)` on the
diagonal `p = q` and `0` elsewhere, with identity operator readout and two-sided snake laws. -/
def evalFunctional [DecidableEq S] (d : S → ℤ) (p q : S) : R :=
  if p = q then negOnePowCast R (d p) else 0

/-- A value of the right-evaluation functional. -/
theorem evalFunctional_apply [DecidableEq S] (d : S → ℤ) (p q : S) :
    evalFunctional d p q = if p = q then negOnePowCast R (d p) else 0 := (rfl)

/-- The operator readout of the right-evaluation functional is the identity kernel. -/
@[simp]
theorem kernelReadout_evalFunctional [DecidableEq S] (d : S → ℤ) :
    kernelReadout d (evalFunctional (R := R) d) = fun p q => if p = q then 1 else 0 := by
  funext p q
  obtain rfl | hpq := eq_or_ne p q <;> simp [kernelReadout_apply, evalFunctional_apply, *]

/-- **Left snake identity:** sewing `evalFunctional` on the left of `ψ` returns `ψ`. -/
@[simp]
theorem functionalSew_evalFunctional_left [DecidableEq S₁] (d₁ : S₁ → ℤ) (ψ : S₁ → S₀ → R) :
    functionalSew d₁ (evalFunctional d₁) ψ = ψ := by
  funext p q
  rw [functionalSew_apply, finsum_eq_single _ p fun r hr => by simp [evalFunctional_apply, hr.symm]]
  simp [evalFunctional_apply]

/-- **Right snake identity:** sewing `evalFunctional` on the right of `φ` returns `φ`. -/
@[simp]
theorem functionalSew_evalFunctional_right [DecidableEq S₀] (d₀ : S₀ → ℤ) (φ : S → S₀ → R) :
    functionalSew d₀ φ (evalFunctional d₀) = φ := by
  funext x q
  rw [functionalSew_apply, finsum_eq_single _ q fun r hr => by simp [evalFunctional_apply, hr]]
  simp only [evalFunctional_apply, ↓reduceIte]
  linear_combination φ x q * negOnePowCast_mul_self (R := R) (d₀ q)

/-- **Differential compatibility:** `evalFunctional` is closed under `functionalBoundary`. -/
@[simp]
theorem functionalBoundary_evalFunctional [DecidableEq S] (d : S → ℤ) (δ : S → S → R) :
    functionalBoundary d d δ δ (evalFunctional d) = 0 := by
  funext p q
  rw [functionalBoundary_apply, kernelComp_apply, kernelComp_apply,
    finsum_eq_single _ q fun r hr => by simp [evalFunctional_apply, hr],
    finsum_eq_single _ p fun r hr => by simp [evalFunctional_apply, hr.symm]]
  simp only [evalFunctional_apply, ↓reduceIte, negOnePowCast_add, Pi.zero_apply]
  linear_combination (-(negOnePowCast R (d q) * δ p q)) * negOnePowCast_mul_self (R := R) (d p)

end EvalFunctional

/-- **Associativity of kernel composition** at `(x, q)` under finite joint intermediate support. -/
theorem kernelComp_assoc {S₂ : Type*} {m : S → S₁ → R} {m' : S₁ → S₂ → R}
    {m'' : S₂ → S₀ → R} {x : S} {q : S₀}
    (hf : {r : S₁ × S₂ | m x r.1 ≠ 0 ∧ m' r.1 r.2 ≠ 0 ∧ m'' r.2 q ≠ 0}.Finite) :
    kernelComp (kernelComp m m') m'' x q = kernelComp m (kernelComp m' m'') x q := by
  have h₁₂₃ : HasFiniteSupport (uncurry fun p₁ p₂ => m x p₁ * m' p₁ p₂ * m'' p₂ q) :=
    hf.subset fun r hr => ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hr),
      right_ne_zero_of_mul (left_ne_zero_of_mul hr), right_ne_zero_of_mul hr⟩
  calc kernelComp (kernelComp m m') m'' x q
      = ∑ᶠ p₂, ∑ᶠ p₁, m x p₁ * m' p₁ p₂ * m'' p₂ q := by
        rw [kernelComp_apply]
        refine finsum_congr fun p₂ => ?_
        by_cases hp₂ : m'' p₂ q = 0
        · simp [hp₂]
        · rw [kernelComp_apply, finsum_mul' _ _
            ((hf.preimage (fun a _ b _ h => congrArg Prod.fst h : Set.InjOn (·, p₂) _)).subset
              fun p₁ hp₁ => ⟨left_ne_zero_of_mul hp₁, right_ne_zero_of_mul hp₁, hp₂⟩)]
    _ = ∑ᶠ p₁, ∑ᶠ p₂, m x p₁ * m' p₁ p₂ * m'' p₂ q := (finsum_comm h₁₂₃).symm
    _ = kernelComp m (kernelComp m' m'') x q := by
        rw [kernelComp_apply]
        refine finsum_congr fun p₁ => ?_
        by_cases hp₁ : m x p₁ = 0
        · simp [hp₁]
        · rw [kernelComp_apply, mul_finsum' _ _
            ((hf.preimage (Prod.mk_right_injective p₁).injOn).subset
              fun p₂ hp₂ => ⟨hp₁, left_ne_zero_of_mul hp₂, right_ne_zero_of_mul hp₂⟩)]
          exact finsum_congr fun p₂ => mul_assoc _ _ _

private theorem finite_support_kernelComp_left {S₂ : Type*} {m : S → S₁ → R}
    {m' : S₁ → S₂ → R} {m'' : S₂ → S₀ → R} {x : S} {q : S₀}
    (hf : {r : S₁ × S₂ | m x r.1 ≠ 0 ∧ m' r.1 r.2 ≠ 0 ∧ m'' r.2 q ≠ 0}.Finite) :
    (support fun p₂ => kernelComp m m' x p₂ * m'' p₂ q).Finite :=
  (hf.image Prod.snd).subset fun p₂ hp₂ => by
    obtain ⟨p₁, hp₁⟩ := not_forall.mp (mt finsum_eq_zero_of_forall_eq_zero
      (kernelComp_apply m m' x p₂ ▸ left_ne_zero_of_mul hp₂))
    exact ⟨(p₁, p₂), ⟨left_ne_zero_of_mul hp₁, right_ne_zero_of_mul hp₁,
      right_ne_zero_of_mul hp₂⟩, rfl⟩

private theorem finite_support_kernelComp_right {S₂ : Type*} {m : S → S₁ → R}
    {m' : S₁ → S₂ → R} {m'' : S₂ → S₀ → R} {x : S} {q : S₀}
    (hf : {r : S₁ × S₂ | m x r.1 ≠ 0 ∧ m' r.1 r.2 ≠ 0 ∧ m'' r.2 q ≠ 0}.Finite) :
    (support fun p₁ => m x p₁ * kernelComp m' m'' p₁ q).Finite :=
  (hf.image Prod.fst).subset fun p₁ hp₁ => by
    obtain ⟨p₂, hp₂⟩ := not_forall.mp (mt finsum_eq_zero_of_forall_eq_zero
      (kernelComp_apply m' m'' p₁ q ▸ right_ne_zero_of_mul hp₁))
    exact ⟨(p₁, p₂), ⟨left_ne_zero_of_mul hp₁, left_ne_zero_of_mul hp₂,
      right_ne_zero_of_mul hp₂⟩, rfl⟩

private theorem kernelReadout_functionalBoundary_of_deg {d : S → ℤ} {d₁ : S₁ → ℤ}
    {δ : S → S → R} {δ₁ : S₁ → S₁ → R} {φ : S → S₁ → R} {j : ℤ}
    (ht_deg : ∀ y p, kernelReadout d₁ φ y p ≠ 0 → d₁ p = d y + j) (x : S) (p : S₁) :
    kernelReadout d₁ (functionalBoundary d d₁ δ δ₁ φ) x p =
      kernelComp δ (kernelReadout d₁ φ) x p -
        negOnePowCast R j * kernelComp (kernelReadout d₁ φ) δ₁ x p := by
  have hb := functionalBoundary_kernelReadout (δ := δ) (δ₀ := δ₁) ht_deg x p
  rw [kernelReadout_kernelReadout d₁ φ] at hb
  rw [kernelReadout_apply, hb, kernelReadout_apply, negOnePowCast_add, negOnePowCast_one]
  linear_combination
    (-(negOnePowCast R j * kernelComp (kernelReadout d₁ φ) δ₁ x p) +
        negOnePowCast R j * negOnePowCast R j * kernelComp δ (kernelReadout d₁ φ) x p) *
      negOnePowCast_mul_self (R := R) (d₁ p) +
    kernelComp δ (kernelReadout d₁ φ) x p * negOnePowCast_mul_self (R := R) j

/-- **The Leibniz rule for coevaluation sewing.** When `φ` has operator degree `j` and only
finitely many broken configurations occur at the input, sewn neck, and output of `(x, q)`, the
boundary of `φ # ψ` equals `(∂φ) # ψ + (-1)^j φ # (∂ψ)` as neck-breaking sums cancel. -/
theorem functionalBoundary_functionalSew {d : S → ℤ} {d₁ : S₁ → ℤ} {d₀ : S₀ → ℤ}
    {δ : S → S → R} {δ₁ : S₁ → S₁ → R} {δ₀ : S₀ → S₀ → R}
    {φ : S → S₁ → R} {ψ : S₁ → S₀ → R} {j : ℤ}
    (hφ : ∀ x p, φ x p ≠ 0 → d₁ p = d x + j) {x : S} {q : S₀}
    (h_in : {r : S × S₁ | δ x r.1 ≠ 0 ∧ φ r.1 r.2 ≠ 0 ∧ ψ r.2 q ≠ 0}.Finite)
    (h_neck : {r : S₁ × S₁ | φ x r.1 ≠ 0 ∧ δ₁ r.1 r.2 ≠ 0 ∧ ψ r.2 q ≠ 0}.Finite)
    (h_out : {r : S₁ × S₀ | φ x r.1 ≠ 0 ∧ ψ r.1 r.2 ≠ 0 ∧ δ₀ r.2 q ≠ 0}.Finite) :
    functionalBoundary d d₀ δ δ₀ (functionalSew d₁ φ ψ) x q =
      functionalSew d₁ (functionalBoundary d d₁ δ δ₁ φ) ψ x q +
        negOnePowCast R j * functionalSew d₁ φ (functionalBoundary d₁ d₀ δ₁ δ₀ ψ) x q := by
  set t : S → S₁ → R := kernelReadout d₁ φ with ht
  have ht_ne : ∀ y p, t y p ≠ 0 → φ y p ≠ 0 := fun y p h hp =>
    h (by simp [t, kernelReadout_apply, hp])
  have ht_deg : ∀ y p, t y p ≠ 0 → d₁ p = d y + j := fun y p h => hφ y p (ht_ne y p h)
  have h_in' : {r : S × S₁ | δ x r.1 ≠ 0 ∧ t r.1 r.2 ≠ 0 ∧ ψ r.2 q ≠ 0}.Finite :=
    h_in.subset fun r ⟨h₁, h₂, h₃⟩ => ⟨h₁, ht_ne r.1 r.2 h₂, h₃⟩
  have h_neck' : {r : S₁ × S₁ | t x r.1 ≠ 0 ∧ δ₁ r.1 r.2 ≠ 0 ∧ ψ r.2 q ≠ 0}.Finite :=
    h_neck.subset fun r ⟨h₁, h₂, h₃⟩ => ⟨ht_ne x r.1 h₁, h₂, h₃⟩
  have h_out' : {r : S₁ × S₀ | t x r.1 ≠ 0 ∧ ψ r.1 r.2 ≠ 0 ∧ δ₀ r.2 q ≠ 0}.Finite :=
    h_out.subset fun r ⟨h₁, h₂, h₃⟩ => ⟨ht_ne x r.1 h₁, h₂, h₃⟩
  have hs₁ : functionalSew d₁ (functionalBoundary d d₁ δ δ₁ φ) ψ x q =
      kernelComp (kernelComp δ t) ψ x q -
        negOnePowCast R j * kernelComp (kernelComp t δ₁) ψ x q := by
    rw [functionalSew_eq_kernelComp_kernelReadout, kernelComp_apply, kernelComp_apply,
      kernelComp_apply, negOnePowCast_mul_finsum, ← finsum_sub_distrib
        (finite_support_kernelComp_left h_in') ((finite_support_kernelComp_left h_neck').subset
          fun p => mt fun h => by dsimp only at h ⊢; rw [h, mul_zero])]
    exact finsum_congr fun p => by rw [kernelReadout_functionalBoundary_of_deg ht_deg x p]; ring
  have hs₂ : negOnePowCast R j * functionalSew d₁ φ (functionalBoundary d₁ d₀ δ₁ δ₀ ψ) x q =
      negOnePowCast R j * kernelComp t (kernelComp δ₁ ψ) x q -
        negOnePowCast R (d x + d₀ q) * kernelComp t (kernelComp ψ δ₀) x q := by
    rw [functionalSew_eq_kernelComp_kernelReadout, ← ht, kernelComp_apply, kernelComp_apply,
      kernelComp_apply, negOnePowCast_mul_finsum, negOnePowCast_mul_finsum,
      negOnePowCast_mul_finsum, ← finsum_sub_distrib
        ((finite_support_kernelComp_right h_neck').subset
          fun p => mt fun h => by dsimp only at h ⊢; rw [h, mul_zero])
        ((finite_support_kernelComp_right h_out').subset
          fun p => mt fun h => by dsimp only at h ⊢; rw [h, mul_zero])]
    refine finsum_congr fun p => ?_
    by_cases hp : t x p = 0
    · simp [hp]
    · rw [functionalBoundary_apply, ht_deg x p hp]; simp only [negOnePowCast_add]
      linear_combination
        (-(negOnePowCast R (d x) * negOnePowCast R (d₀ q) * t x p * kernelComp ψ δ₀ p q)) *
          negOnePowCast_mul_self (R := R) j
  rw [functionalSew_eq_kernelComp_kernelReadout, ← ht, functionalBoundary_apply,
    ← kernelComp_assoc h_in', kernelComp_assoc h_out', hs₁, hs₂, kernelComp_assoc h_neck']
  abel

end Sewing

section Combination

variable {R S₁ S₂ S₀ : Type*} [CommRing R]

/-- **Combination readout of a no-input cap functional.** Multiplying `ε : S₀ → R` at `q` by
`(-1)^(d₀ q)` identifies cap functionals on `C₀^∨` with combinations in `C₀`. -/
def combinationReadout (d₀ : S₀ → ℤ) (ε : S₀ → R) (q : S₀) : R :=
  negOnePowCast R (d₀ q) * ε q

/-- A coefficient of the combination readout of a cap functional. -/
theorem combinationReadout_apply (d₀ : S₀ → ℤ) (ε : S₀ → R) (q : S₀) :
    combinationReadout d₀ ε q = negOnePowCast R (d₀ q) * ε q := (rfl)

/-- Combination readout is an involution. -/
@[simp]
theorem combinationReadout_combinationReadout (d₀ : S₀ → ℤ) (ε : S₀ → R) :
    combinationReadout d₀ (combinationReadout d₀ ε) = ε := by
  funext q; simp [combinationReadout_apply, ← mul_assoc]

@[simp]
theorem combinationReadout_zero (d₀ : S₀ → ℤ) :
    combinationReadout (R := R) d₀ 0 = 0 := by funext q; simp [combinationReadout_apply]

@[simp]
theorem combinationReadout_add (d₀ : S₀ → ℤ) (ε ε' : S₀ → R) :
    combinationReadout d₀ (ε + ε') = combinationReadout d₀ ε + combinationReadout d₀ ε' := by
  funext q; simp [combinationReadout_apply, mul_add]

@[simp]
theorem combinationReadout_neg (d₀ : S₀ → ℤ) (ε : S₀ → R) :
    combinationReadout d₀ (-ε) = -combinationReadout d₀ ε := by
  funext q; simp [combinationReadout_apply]

@[simp]
theorem combinationReadout_sub (d₀ : S₀ → ℤ) (ε ε' : S₀ → R) :
    combinationReadout d₀ (ε - ε') = combinationReadout d₀ ε - combinationReadout d₀ ε' := by
  funext q; simp [combinationReadout_apply, mul_sub]

@[simp]
theorem combinationReadout_smul (d₀ : S₀ → ℤ) (c : R) (ε : S₀ → R) :
    combinationReadout d₀ (c • ε) = c • combinationReadout d₀ ε := by
  funext q; simp only [combinationReadout_apply, Pi.smul_apply, smul_eq_mul]; ring

@[simp]
theorem combinationReadout_inj {d₀ : S₀ → ℤ} {ε ε' : S₀ → R} :
    combinationReadout d₀ ε = combinationReadout d₀ ε' ↔ ε = ε' :=
  ⟨fun h => by simpa using congrArg (combinationReadout d₀) h, fun h => h ▸ rfl⟩

/-- **Closed cap functionals give cocycles** for combinations of constant degree parity `j`. -/
theorem functionalBoundary_combinationReadout_eq_zero_iff {d₀ : S₀ → ℤ} {δ₀ : S₀ → S₀ → R}
    {e : S₀ → R} {j : ℤ} (he : ∀ p, e p ≠ 0 → Even (d₀ p - j)) (q : S₀) :
    functionalBoundary (fun _ : Unit => 0) d₀ 0 δ₀ (fun _ => combinationReadout d₀ e) () q = 0 ↔
      ∑ᶠ p, e p * δ₀ p q = 0 := by
  have hcomp : kernelComp (fun _ : Unit => combinationReadout d₀ e) δ₀ () q =
      negOnePowCast R j * ∑ᶠ p, e p * δ₀ p q := by
    rw [kernelComp_apply, negOnePowCast_mul_finsum]
    refine finsum_congr fun p => ?_
    by_cases hp : e p = 0
    · simp [combinationReadout_apply, hp]
    · have hd : d₀ p = (d₀ p - j) + j := by ring
      rw [combinationReadout_apply, hd, negOnePowCast_add, negOnePowCast_even (he p hp), one_mul,
        mul_assoc]
  rw [functionalBoundary_apply, kernelComp_apply]
  simp only [Pi.zero_apply, zero_mul, finsum_zero, zero_add, zero_sub, hcomp, neg_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [h, mul_zero, mul_zero]⟩
  simpa only [← mul_assoc, negOnePowCast_mul_self, one_mul, mul_zero] using
    congrArg (fun x => negOnePowCast R j * (negOnePowCast R (d₀ q) * x)) h

/-- **Left cap sewing into a product functional**, contracting adjacent factors `C₁^∨ ⊗ C₁`. -/
def functionalSewCapLeft (d₁ : S₁ → ℤ) (ε : S₁ → R) (φ : S₁ × S₂ → S₀ → R) (p₂ : S₂) (p₀ : S₀) :
    R :=
  ∑ᶠ t, negOnePowCast R (d₁ t) * ε t * φ (t, p₂) p₀

/-- A value of left cap sewing into a product functional. -/
theorem functionalSewCapLeft_apply (d₁ : S₁ → ℤ) (ε : S₁ → R) (φ : S₁ × S₂ → S₀ → R) (p₂ : S₂)
    (p₀ : S₀) :
    functionalSewCapLeft d₁ ε φ p₂ p₀ = ∑ᶠ t, negOnePowCast R (d₁ t) * ε t * φ (t, p₂) p₀ := (rfl)

/-- Operator readout turns left cap sewing into left multiplication by `combinationReadout d₁ ε`. -/
@[simp]
theorem kernelReadout_functionalSewCapLeft (d₁ : S₁ → ℤ) (d₀ : S₀ → ℤ) (ε : S₁ → R)
    (φ : S₁ × S₂ → S₀ → R) (p₂ : S₂) (p₀ : S₀) :
    kernelReadout d₀ (functionalSewCapLeft d₁ ε φ) p₂ p₀ =
      ∑ᶠ t, combinationReadout d₁ ε t * kernelReadout d₀ φ (t, p₂) p₀ := by
  simpa only [functionalSew_apply, functionalSewCapLeft_apply, kernelComp_apply,
    kernelReadout_apply, combinationReadout_apply] using
    congrFun₂ (kernelReadout_functionalSew d₁ d₀ (fun _ : Unit => ε) (fun t => φ (t, p₂))) () p₀

/-- Left cap sewing of readouts of `e` and `n` is the readout of `p₂ ↦ ∑ₜ e(t) n(t, p₂, ·)`. -/
theorem functionalSewCapLeft_combinationReadout_kernelReadout (d₁ : S₁ → ℤ) (d₀ : S₀ → ℤ)
    (e : S₁ → R) (n : S₁ → S₂ → S₀ → R) :
    functionalSewCapLeft d₁ (combinationReadout d₁ e) (kernelReadout d₀ fun q => n q.1 q.2) =
      kernelReadout d₀ fun p₂ p₀ => ∑ᶠ t, e t * n t p₂ p₀ := by
  apply kernelReadout_injective d₀; funext p₂ p₀; simp [kernelReadout_functionalSewCapLeft]

/-- **Right cap sewing into a product functional**, braiding `C₂^∨` past `p₁ ∈ C₁` with Koszul sign
`(-1)^(d₁ p₁ d₂ t)` alongside the coevaluation sign `(-1)^(d₂ t)`. -/
def functionalSewCapRight (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (ε : S₂ → R) (φ : S₁ × S₂ → S₀ → R)
    (p₁ : S₁) (p₀ : S₀) : R :=
  ∑ᶠ t, negOnePowCast R (d₁ p₁ * d₂ t + d₂ t) * ε t * φ (p₁, t) p₀

/-- A value of right cap sewing into a product functional. -/
theorem functionalSewCapRight_apply (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (ε : S₂ → R)
    (φ : S₁ × S₂ → S₀ → R) (p₁ : S₁) (p₀ : S₀) :
    functionalSewCapRight d₁ d₂ ε φ p₁ p₀ =
      ∑ᶠ t, negOnePowCast R (d₁ p₁ * d₂ t + d₂ t) * ε t * φ (p₁, t) p₀ := (rfl)

/-- Operator readout turns right cap sewing into Koszul-twisted right multiplication by
`combinationReadout d₂ ε`. -/
@[simp]
theorem kernelReadout_functionalSewCapRight (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (d₀ : S₀ → ℤ)
    (ε : S₂ → R) (φ : S₁ × S₂ → S₀ → R) (p₁ : S₁) (p₀ : S₀) :
    kernelReadout d₀ (functionalSewCapRight d₁ d₂ ε φ) p₁ p₀ =
      ∑ᶠ t, negOnePowCast R (d₁ p₁ * d₂ t) * combinationReadout d₂ ε t *
        kernelReadout d₀ φ (p₁, t) p₀ := by
  rw [kernelReadout_apply, functionalSewCapRight_apply, negOnePowCast_mul_finsum]
  exact finsum_congr fun t => by
    rw [combinationReadout_apply, kernelReadout_apply, negOnePowCast_add]; ring

/-- For `e` supported in degree parity `j`, right cap sewing multiplies the readout of
`p₁ ↦ ∑ₜ e(t) n(p₁, t, ·)` by `(-1)^(j d₁ p₁)`. -/
theorem functionalSewCapRight_combinationReadout_kernelReadout_of_even_sub {d₁ : S₁ → ℤ}
    {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e : S₂ → R} {j : ℤ}
    (he : ∀ t, e t ≠ 0 → Even (d₂ t - j)) (n : S₁ → S₂ → S₀ → R) (p₁ : S₁) (p₀ : S₀) :
    functionalSewCapRight d₁ d₂ (combinationReadout d₂ e)
        (kernelReadout d₀ fun q => n q.1 q.2) p₁ p₀ =
      negOnePowCast R (j * d₁ p₁) *
        kernelReadout d₀ (fun p₁ p₀ => ∑ᶠ t, e t * n p₁ t p₀) p₁ p₀ := by
  refine eq_negOnePowCast_mul_kernelReadout ?_
  rw [kernelReadout_functionalSewCapRight, negOnePowCast_mul_finsum]
  refine finsum_congr fun t => ?_
  simp only [combinationReadout_combinationReadout, kernelReadout_kernelReadout]
  by_cases ht : e t = 0
  · simp [ht]
  · have hd : d₁ p₁ * d₂ t = d₁ p₁ * (d₂ t - j) + j * d₁ p₁ := by ring
    rw [hd, negOnePowCast_add, negOnePowCast_even ((he t ht).mul_left (d₁ p₁)), one_mul, mul_assoc]

/-- For `e` supported in even degrees (such as the degree-`0` Floer unit), right cap sewing produces
the readout of `p₁ ↦ ∑ₜ e(t) n(p₁, t, ·)` with no extra sign. -/
theorem functionalSewCapRight_combinationReadout_kernelReadout_of_even {d₁ : S₁ → ℤ}
    {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e : S₂ → R} (he : ∀ t, e t ≠ 0 → Even (d₂ t))
    (n : S₁ → S₂ → S₀ → R) :
    functionalSewCapRight d₁ d₂ (combinationReadout d₂ e)
        (kernelReadout d₀ fun q => n q.1 q.2) =
      kernelReadout d₀ fun p₁ p₀ => ∑ᶠ t, e t * n p₁ t p₀ := by
  funext p₁ p₀
  simpa using functionalSewCapRight_combinationReadout_kernelReadout_of_even_sub
    (j := 0) (fun t ht => by simpa using he t ht) n p₁ p₀

section UnitHomotopy

variable {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {C Cφ Ck Cδ C₀ : ℝ}
  {n : S₁ → S₂ → S₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  {δ₀ : S₀ → S₀ → R} (hδ₀ : ∀ p q, δ₀ p q ≠ 0 → F₀ q ≤ F₀ p + C₀)
  (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)

/-- **Left unit homotopy** `e ⋆ b - φ b = δ₀ (K b) + K (δ₂ b)` from a left cap-gluing boundary. -/
theorem kernelProduct_sub_kernelMap_right_of_functionalBoundary
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ}
    {φ k : S₂ → S₀ → R} (hφ : ∀ p₂ p₀, φ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + Cφ)
    (hφfin : ∀ p₂, φ p₂ ∈ NovikovModule R F₀)
    (hk : ∀ p₂ p₀, k p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₂ p₂ + Ck) (hkfin : ∀ p₂, k p₂ ∈ NovikovModule R F₀)
    {δ₂ : S₂ → S₂ → R} (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + Cδ)
    (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hkd : ∀ p₂ p₀, k p₂ p₀ ≠ 0 → d₀ p₀ = d₂ p₂ - 1) (e : NovikovModule R F₁)
    (hB : ∀ p₂ p₀, functionalBoundary d₂ d₀ δ₂ δ₀ (kernelReadout d₀ k) p₂ p₀ =
      functionalSewCapLeft d₁ (combinationReadout d₁ e.val)
          (kernelReadout d₀ fun q => n q.1 q.2) p₂ p₀ -
        kernelReadout d₀ φ p₂ p₀)
    (b : NovikovModule R F₂) :
    kernelProduct hn hfin e b - kernelMap hφ hφfin b =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin b) +
        kernelMap hk hkfin (kernelMap hδ₂ hδ₂fin b) := by
  refine kernelProduct_sub_kernelMap_right hn hfin hδ₀ hδ₀fin hφ hφfin hk hkfin hδ₂ hδ₂fin e
    (fun p₂ p₀ => ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
      (s := (fun p₂ p₀ => ∑ᶠ t, e.val t * n t p₂ p₀) - φ) hkd p₂ p₀).mp ?_).symm) b
  rw [hB p₂ p₀, functionalSewCapLeft_combinationReadout_kernelReadout, kernelReadout_sub]; rfl

/-- **Right unit homotopy** `a ⋆ e - φ a = δ₀ (K a) + K (δ₁ a)` from a right cap-gluing boundary
when `e` is supported in even degrees. -/
theorem kernelProduct_sub_kernelMap_left_of_functionalBoundary
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ}
    {φ k : S₁ → S₀ → R} (hφ : ∀ p₁ p₀, φ p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + Cφ)
    (hφfin : ∀ p₁, φ p₁ ∈ NovikovModule R F₀)
    (hk : ∀ p₁ p₀, k p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + Ck) (hkfin : ∀ p₁, k p₁ ∈ NovikovModule R F₀)
    {δ₁ : S₁ → S₁ → R} (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + Cδ)
    (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hkd : ∀ p₁ p₀, k p₁ p₀ ≠ 0 → d₀ p₀ = d₁ p₁ - 1) (e : NovikovModule R F₂)
    (he : ∀ t, e.val t ≠ 0 → Even (d₂ t))
    (hB : ∀ p₁ p₀, functionalBoundary d₁ d₀ δ₁ δ₀ (kernelReadout d₀ k) p₁ p₀ =
      functionalSewCapRight d₁ d₂ (combinationReadout d₂ e.val)
          (kernelReadout d₀ fun q => n q.1 q.2) p₁ p₀ -
        kernelReadout d₀ φ p₁ p₀)
    (a : NovikovModule R F₁) :
    kernelProduct hn hfin a e - kernelMap hφ hφfin a =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin a) +
        kernelMap hk hkfin (kernelMap hδ₁ hδ₁fin a) := by
  refine kernelProduct_sub_kernelMap_left hn hfin hδ₀ hδ₀fin hφ hφfin hk hkfin hδ₁ hδ₁fin e
    (fun p₁ p₀ => ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
      (s := (fun p₁ p₀ => ∑ᶠ t, e.val t * n p₁ t p₀) - φ) hkd p₁ p₀).mp ?_).symm) a
  rw [hB p₁ p₀, functionalSewCapRight_combinationReadout_kernelReadout_of_even he,
    kernelReadout_sub]; rfl

end UnitHomotopy

end Combination

section Associativity

variable {R S₁ S₂ S₃ S₀ S₁₂ S₂₃ : Type*} [CommRing R]

/-- **Left product sewing of two pair-of-pants functionals**, contracting adjacent `C₁₂^∨ ⊗ C₁₂`. -/
def functionalSewProdLeft (d₁₂ : S₁₂ → ℤ) (φ : S₁ × S₂ → S₁₂ → R) (φ' : S₁₂ × S₃ → S₀ → R)
    (q : (S₁ × S₂) × S₃) (p₀ : S₀) : R :=
  ∑ᶠ t, negOnePowCast R (d₁₂ t) * φ q.1 t * φ' (t, q.2) p₀

/-- A value of left product sewing. -/
theorem functionalSewProdLeft_apply (d₁₂ : S₁₂ → ℤ) (φ : S₁ × S₂ → S₁₂ → R)
    (φ' : S₁₂ × S₃ → S₀ → R) (q : (S₁ × S₂) × S₃) (p₀ : S₀) :
    functionalSewProdLeft d₁₂ φ φ' q p₀ =
      ∑ᶠ t, negOnePowCast R (d₁₂ t) * φ q.1 t * φ' (t, q.2) p₀ := (rfl)

/-- Operator readout turns left product sewing into the nested left product kernel. -/
@[simp]
theorem kernelReadout_functionalSewProdLeft (d₁₂ : S₁₂ → ℤ) (d₀ : S₀ → ℤ)
    (φ : S₁ × S₂ → S₁₂ → R) (φ' : S₁₂ × S₃ → S₀ → R) (q : (S₁ × S₂) × S₃) (p₀ : S₀) :
    kernelReadout d₀ (functionalSewProdLeft d₁₂ φ φ') q p₀ =
      ∑ᶠ t, kernelReadout d₁₂ φ q.1 t * kernelReadout d₀ φ' (t, q.2) p₀ := by
  simpa only [functionalSew_apply, functionalSewProdLeft_apply, kernelComp_apply,
    kernelReadout_apply] using
    congrFun₂ (kernelReadout_functionalSew d₁₂ d₀ φ (fun t => φ' (t, q.2))) q.1 p₀

/-- Left product sewing of the readouts of `n` and `n'` is the readout of the nested product
kernel `∑ₜ n(p₁, p₂, t) n'(t, p₃, ·)`. -/
theorem functionalSewProdLeft_kernelReadout (d₁₂ : S₁₂ → ℤ) (d₀ : S₀ → ℤ)
    (n : S₁ → S₂ → S₁₂ → R) (n' : S₁₂ → S₃ → S₀ → R) :
    functionalSewProdLeft d₁₂ (kernelReadout d₁₂ fun q => n q.1 q.2)
        (kernelReadout d₀ fun q => n' q.1 q.2) =
      kernelReadout d₀ fun (q : (S₁ × S₂) × S₃) p₀ => ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ := by
  apply kernelReadout_injective d₀; funext q p₀; simp [kernelReadout_functionalSewProdLeft]

/-- **Right product sewing of two pair-of-pants functionals**, braiding `p₁ ∈ C₁` past
`C₂ ⊗ C₃ ⊗ C₂₃^∨` with `(-1)^(d₁ p₁ (d₂ p₂ + d₃ p₃ - d₂₃ u))` alongside `(-1)^(d₂₃ u)`. -/
def functionalSewProdRight (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (d₃ : S₃ → ℤ) (d₂₃ : S₂₃ → ℤ)
    (ψ : S₂ × S₃ → S₂₃ → R) (ψ' : S₁ × S₂₃ → S₀ → R) (q : (S₁ × S₂) × S₃) (p₀ : S₀) : R :=
  ∑ᶠ u, negOnePowCast R (d₁ q.1.1 * (d₂ q.1.2 + d₃ q.2 - d₂₃ u) + d₂₃ u) *
    ψ (q.1.2, q.2) u * ψ' (q.1.1, u) p₀

/-- A value of right product sewing. -/
theorem functionalSewProdRight_apply (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (d₃ : S₃ → ℤ) (d₂₃ : S₂₃ → ℤ)
    (ψ : S₂ × S₃ → S₂₃ → R) (ψ' : S₁ × S₂₃ → S₀ → R) (q : (S₁ × S₂) × S₃) (p₀ : S₀) :
    functionalSewProdRight d₁ d₂ d₃ d₂₃ ψ ψ' q p₀ =
      ∑ᶠ u, negOnePowCast R (d₁ q.1.1 * (d₂ q.1.2 + d₃ q.2 - d₂₃ u) + d₂₃ u) *
        ψ (q.1.2, q.2) u * ψ' (q.1.1, u) p₀ := (rfl)

/-- Operator readout turns right product sewing into the Koszul-twisted nested right product. -/
@[simp]
theorem kernelReadout_functionalSewProdRight (d₁ : S₁ → ℤ) (d₂ : S₂ → ℤ) (d₃ : S₃ → ℤ)
    (d₂₃ : S₂₃ → ℤ) (d₀ : S₀ → ℤ) (ψ : S₂ × S₃ → S₂₃ → R) (ψ' : S₁ × S₂₃ → S₀ → R)
    (q : (S₁ × S₂) × S₃) (p₀ : S₀) :
    kernelReadout d₀ (functionalSewProdRight d₁ d₂ d₃ d₂₃ ψ ψ') q p₀ =
      ∑ᶠ u, negOnePowCast R (d₁ q.1.1 * (d₂ q.1.2 + d₃ q.2 - d₂₃ u)) *
        kernelReadout d₂₃ ψ (q.1.2, q.2) u * kernelReadout d₀ ψ' (q.1.1, u) p₀ := by
  rw [kernelReadout_apply, functionalSewProdRight_apply, negOnePowCast_mul_finsum]
  exact finsum_congr fun u => by
    rw [kernelReadout_apply, kernelReadout_apply, negOnePowCast_add]; ring

/-- For an inner product kernel `m` of degree parity `j`, right product sewing multiplies the
readout of `∑ᵤ m(p₂, p₃, u) m'(p₁, u, ·)` by `(-1)^(j d₁ p₁)`. -/
theorem functionalSewProdRight_kernelReadout_of_even_sub {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ}
    {d₃ : S₃ → ℤ} {d₂₃ : S₂₃ → ℤ} {d₀ : S₀ → ℤ} {m : S₂ → S₃ → S₂₃ → R} {j : ℤ}
    (hm : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → Even (d₂₃ u - (d₂ p₂ + d₃ p₃) - j))
    (m' : S₁ → S₂₃ → S₀ → R) (q : (S₁ × S₂) × S₃) (p₀ : S₀) :
    functionalSewProdRight d₁ d₂ d₃ d₂₃ (kernelReadout d₂₃ fun r => m r.1 r.2)
        (kernelReadout d₀ fun r => m' r.1 r.2) q p₀ =
      negOnePowCast R (j * d₁ q.1.1) *
        kernelReadout d₀ (fun (q : (S₁ × S₂) × S₃) p₀ => ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀)
          q p₀ := by
  refine eq_negOnePowCast_mul_kernelReadout ?_
  rw [kernelReadout_functionalSewProdRight, negOnePowCast_mul_finsum]
  refine finsum_congr fun u => ?_
  simp only [kernelReadout_kernelReadout]
  by_cases hu : m q.1.2 q.2 u = 0
  · simp [hu]
  · have hd : -(d₁ q.1.1 * (d₂ q.1.2 + d₃ q.2 - d₂₃ u)) =
        d₁ q.1.1 * (d₂₃ u - (d₂ q.1.2 + d₃ q.2) - j) + j * d₁ q.1.1 := by ring
    rw [← negOnePowCast_neg, hd, negOnePowCast_add,
      negOnePowCast_even ((hm q.1.2 q.2 u hu).mul_left (d₁ q.1.1)), one_mul, mul_assoc]

/-- When `m` preserves degree parity, right product sewing gives the readout of
`∑ᵤ m(p₂, p₃, u) m'(p₁, u, ·)` with no extra sign. -/
theorem functionalSewProdRight_kernelReadout_of_even {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₃ : S₃ → ℤ}
    {d₂₃ : S₂₃ → ℤ} {d₀ : S₀ → ℤ} {m : S₂ → S₃ → S₂₃ → R}
    (hm : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → Even (d₂ p₂ + d₃ p₃ - d₂₃ u))
    (m' : S₁ → S₂₃ → S₀ → R) :
    functionalSewProdRight d₁ d₂ d₃ d₂₃ (kernelReadout d₂₃ fun r => m r.1 r.2)
        (kernelReadout d₀ fun r => m' r.1 r.2) =
      kernelReadout d₀ fun (q : (S₁ × S₂) × S₃) p₀ => ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ := by
  funext q p₀
  simpa using functionalSewProdRight_kernelReadout_of_even_sub (j := 0)
    (fun p₂ p₃ u hu => by convert (hm p₂ p₃ u hu).neg using 1; ring) m' q p₀

/-- **Composing the Koszul differential of `(C₁ ⊗ C₂) ⊗ C₃` with a kernel** expands to the three
signed single-input breaking sums when each slice has finite support. -/
theorem kernelComp_tripleTensorDifferential [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃]
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R}
    (k : (S₁ × S₂) × S₃ → S₀ → R) (p₁ : S₁) (p₂ : S₂) (p₃ : S₃) (p₀ : S₀)
    (h₁ : (support fun q₁ => δ₁ p₁ q₁ * k ((q₁, p₂), p₃) p₀).Finite)
    (h₂ : (support fun q₂ => δ₂ p₂ q₂ * k ((p₁, q₂), p₃) p₀).Finite)
    (h₃ : (support fun q₃ => δ₃ p₃ q₃ * k ((p₁, p₂), q₃) p₀).Finite) :
    kernelComp (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
        (tensorDifferential d₁ δ₁ δ₂) δ₃) k ((p₁, p₂), p₃) p₀ =
      kernelComp δ₁ (fun q₁ => k ((q₁, p₂), p₃)) p₁ p₀ +
        negOnePowCast R (d₁ p₁) * kernelComp δ₂ (fun q₂ => k ((p₁, q₂), p₃)) p₂ p₀ +
        negOnePowCast R (d₁ p₁ + d₂ p₂) * kernelComp δ₃ (fun q₃ => k ((p₁, p₂), q₃)) p₃ p₀ := by
  have h₁₂ : (support fun q₁₂ : S₁ × S₂ =>
      tensorDifferential d₁ δ₁ δ₂ (p₁, p₂) q₁₂ * k (q₁₂, p₃) p₀).Finite := by
    refine ((h₁.image fun q₁ => (q₁, p₂)).union (h₂.image fun q₂ => (p₁, q₂))).subset
      fun ⟨q₁, q₂⟩ hq => ?_
    rw [mem_support, tensorDifferential_apply, add_mul] at hq
    by_cases he : δ₁ p₁ q₁ * (if p₂ = q₂ then 1 else 0) * k ((q₁, q₂), p₃) p₀ = 0
    · rw [he, zero_add] at hq
      obtain rfl : p₁ = q₁ := by by_contra hne; simp [hne] at hq
      exact Set.mem_union_right _ ⟨q₂, by simpa [mul_assoc] using hq, rfl⟩
    · obtain rfl : p₂ = q₂ := by by_contra hne; simp [hne] at he
      exact Set.mem_union_left _ ⟨q₁, by simpa using he, rfl⟩
  rw [kernelComp_tensorDifferential k (p₁, p₂) p₃ p₀ h₁₂ h₃,
    kernelComp_tensorDifferential (fun q₁₂ => k (q₁₂, p₃)) p₁ p₂ p₀ h₁ h₂,
    negOnePowCast_eq_intCast, negOnePowCast_eq_intCast]

/-- **The associativity kernel homotopy** from a four-punctured-sphere count-functional boundary. -/
theorem sub_eq_kernelComp_add_kernelComp_of_functionalBoundary_assoc
    [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃]
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₃ : S₃ → ℤ} {d₀ : S₀ → ℤ} {d₁₂ : S₁₂ → ℤ} {d₂₃ : S₂₃ → ℤ}
    {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R} {δ₀ : S₀ → S₀ → R}
    {n : S₁ → S₂ → S₁₂ → R} {n' : S₁₂ → S₃ → S₀ → R}
    {m : S₂ → S₃ → S₂₃ → R} {m' : S₁ → S₂₃ → S₀ → R} {k : (S₁ × S₂) × S₃ → S₀ → R}
    (hmdeg : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → Even (d₂ p₂ + d₃ p₃ - d₂₃ u))
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1.1 + d₂ q.1.2 + d₃ q.2 - 1)
    {q : (S₁ × S₂) × S₃} {p₀ : S₀}
    (hB : functionalBoundary (fun q : (S₁ × S₂) × S₃ => d₁ q.1.1 + d₂ q.1.2 + d₃ q.2) d₀
        (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) (tensorDifferential d₁ δ₁ δ₂) δ₃)
        δ₀ (kernelReadout d₀ k) q p₀ =
      functionalSewProdLeft d₁₂ (kernelReadout d₁₂ fun r => n r.1 r.2)
          (kernelReadout d₀ fun r => n' r.1 r.2) q p₀ -
        functionalSewProdRight d₁ d₂ d₃ d₂₃ (kernelReadout d₂₃ fun r => m r.1 r.2)
          (kernelReadout d₀ fun r => m' r.1 r.2) q p₀) :
    ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀ - ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀ =
      kernelComp k δ₀ q p₀ +
        kernelComp (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2)
          (tensorDifferential d₁ δ₁ δ₂) δ₃) k q p₀ := by
  refine ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
    (s := (fun (q : (S₁ × S₂) × S₃) p₀ => ∑ᶠ t, n q.1.1 q.1.2 t * n' t q.2 p₀) -
      fun (q : (S₁ × S₂) × S₃) p₀ => ∑ᶠ u, m q.1.2 q.2 u * m' q.1.1 u p₀) hkd q p₀).mp ?_).symm
  rw [hB, functionalSewProdLeft_kernelReadout,
    functionalSewProdRight_kernelReadout_of_even hmdeg, kernelReadout_sub]; rfl

/-- **Associativity homotopy on completed modules** from a four-punctured-sphere functional. -/
theorem kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_functionalBoundary
    [DecidableEq S₁] [DecidableEq S₂] [DecidableEq S₃]
    {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₃ : S₃ → ℝ} {F₀ : S₀ → ℝ} {F₁₂ : S₁₂ → ℝ} {F₂₃ : S₂₃ → ℝ}
    {C₁ C₂ C₃ C₄ Ck C₀ E₁ E₂ E₃ : ℝ}
    {n : S₁ → S₂ → S₁₂ → R} {n' : S₁₂ → S₃ → S₀ → R}
    {m : S₂ → S₃ → S₂₃ → R} {m' : S₁ → S₂₃ → S₀ → R} {k : (S₁ × S₂) × S₃ → S₀ → R}
    {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {δ₃ : S₃ → S₃ → R} {δ₀ : S₀ → S₀ → R}
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₃ : S₃ → ℤ} {d₀ : S₀ → ℤ} {d₁₂ : S₁₂ → ℤ} {d₂₃ : S₂₃ → ℤ}
    (hn : ∀ p₁ p₂ t, n p₁ p₂ t ≠ 0 → F₁₂ t ≤ F₁ p₁ + F₂ p₂ + C₁)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₁₂)
    (hn' : ∀ t p₃ p₀, n' t p₃ p₀ ≠ 0 → F₀ p₀ ≤ F₁₂ t + F₃ p₃ + C₂)
    (hfin' : ∀ t p₃, n' t p₃ ∈ NovikovModule R F₀)
    (hm : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → F₂₃ u ≤ F₂ p₂ + F₃ p₃ + C₃)
    (hmfin : ∀ p₂ p₃, m p₂ p₃ ∈ NovikovModule R F₂₃)
    (hm' : ∀ p₁ u p₀, m' p₁ u p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂₃ u + C₄)
    (hmfin' : ∀ p₁ u, m' p₁ u ∈ NovikovModule R F₀)
    (hk : ∀ (q : (S₁ × S₂) × S₃) p₀, k q p₀ ≠ 0 → F₀ p₀ ≤ F₁ q.1.1 + F₂ q.1.2 + F₃ q.2 + Ck)
    (hkfin : ∀ q, k q ∈ NovikovModule R F₀)
    (hδ₀ : ∀ p p₀, δ₀ p p₀ ≠ 0 → F₀ p₀ ≤ F₀ p + C₀) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hδ₃ : ∀ p q, δ₃ p q ≠ 0 → F₃ q ≤ F₃ p + E₃) (hδ₃fin : ∀ p, δ₃ p ∈ NovikovModule R F₃)
    (hmdeg : ∀ p₂ p₃ u, m p₂ p₃ u ≠ 0 → Even (d₂ p₂ + d₃ p₃ - d₂₃ u))
    (hkd : ∀ q p₀, k q p₀ ≠ 0 → d₀ p₀ = d₁ q.1.1 + d₂ q.1.2 + d₃ q.2 - 1)
    (hB : ∀ q p₀, functionalBoundary (fun q : (S₁ × S₂) × S₃ => d₁ q.1.1 + d₂ q.1.2 + d₃ q.2) d₀
        (tensorDifferential (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) (tensorDifferential d₁ δ₁ δ₂) δ₃)
        δ₀ (kernelReadout d₀ k) q p₀ =
      functionalSewProdLeft d₁₂ (kernelReadout d₁₂ fun r => n r.1 r.2)
          (kernelReadout d₀ fun r => n' r.1 r.2) q p₀ -
        functionalSewProdRight d₁ d₂ d₃ d₂₃ (kernelReadout d₂₃ fun r => m r.1 r.2)
          (kernelReadout d₀ fun r => m' r.1 r.2) q p₀)
    {i j : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i)
    {b : NovikovModule R F₂} (hb : b ∈ gradeBy R F₂ d₂ j) (c : NovikovModule R F₃) :
    kernelProduct hn' hfin' (kernelProduct hn hfin a b) c -
        kernelProduct hm' hmfin' a (kernelProduct hm hmfin b c) =
      kernelMap hδ₀ hδ₀fin (kernelMap hk hkfin (tensor (tensor a b) c)) +
        kernelMap hk hkfin (tensor (tensor (kernelMap hδ₁ hδ₁fin a) b) c) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor (tensor a (kernelMap hδ₂ hδ₂fin b)) c) +
        ((i + j).negOnePow : R) •
          kernelMap hk hkfin (tensor (tensor a b) (kernelMap hδ₃ hδ₃fin c)) :=
  kernelProduct_kernelProduct_sub_kernelProduct_kernelProduct_of_mem_gradeBy hn hfin hn' hfin' hm
    hmfin hm' hmfin' hk hkfin hδ₀ hδ₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin hδ₃ hδ₃fin
    (fun q p₀ => sub_eq_kernelComp_add_kernelComp_of_functionalBoundary_assoc hmdeg hkd (hB q p₀))
    ha hb c

end Associativity

section PairSewing

variable {R S₁ S₂ S₀ T₁ T₂ T₀ : Type*} [CommRing R]

/-- **Sewing two one-input functionals into a product functional**, braiding `t₁ ∈ T₁` past
`C₂ ⊗ T₂^∨` with `(-1)^(e₁ t₁ (d₂ p₂ - e₂ t₂))` alongside `(-1)^(e₁ t₁ + e₂ t₂)`. -/
def functionalSewPair (d₂ : S₂ → ℤ) (e₁ : T₁ → ℤ) (e₂ : T₂ → ℤ)
    (ψ₁ : S₁ → T₁ → R) (ψ₂ : S₂ → T₂ → R) (θ : T₁ × T₂ → T₀ → R)
    (q : S₁ × S₂) (t₀ : T₀) : R :=
  ∑ᶠ t : T₁ × T₂,
    negOnePowCast R (e₁ t.1 * (d₂ q.2 - e₂ t.2) + e₁ t.1 + e₂ t.2) *
      ψ₁ q.1 t.1 * ψ₂ q.2 t.2 * θ t t₀

/-- A value of input-pair sewing. -/
theorem functionalSewPair_apply (d₂ : S₂ → ℤ) (e₁ : T₁ → ℤ) (e₂ : T₂ → ℤ)
    (ψ₁ : S₁ → T₁ → R) (ψ₂ : S₂ → T₂ → R) (θ : T₁ × T₂ → T₀ → R) (q : S₁ × S₂) (t₀ : T₀) :
    functionalSewPair d₂ e₁ e₂ ψ₁ ψ₂ θ q t₀ = ∑ᶠ t : T₁ × T₂,
      negOnePowCast R (e₁ t.1 * (d₂ q.2 - e₂ t.2) + e₁ t.1 + e₂ t.2) *
        ψ₁ q.1 t.1 * ψ₂ q.2 t.2 * θ t t₀ := (rfl)

/-- Operator readout turns input-pair sewing into the Koszul-twisted tensor-product composite. -/
@[simp]
theorem kernelReadout_functionalSewPair (d₂ : S₂ → ℤ) (e₁ : T₁ → ℤ) (e₂ : T₂ → ℤ) (e₀ : T₀ → ℤ)
    (ψ₁ : S₁ → T₁ → R) (ψ₂ : S₂ → T₂ → R) (θ : T₁ × T₂ → T₀ → R) (q : S₁ × S₂) (t₀ : T₀) :
    kernelReadout e₀ (functionalSewPair d₂ e₁ e₂ ψ₁ ψ₂ θ) q t₀ =
      ∑ᶠ t : T₁ × T₂, negOnePowCast R (e₁ t.1 * (d₂ q.2 - e₂ t.2)) *
        kernelReadout e₁ ψ₁ q.1 t.1 * kernelReadout e₂ ψ₂ q.2 t.2 * kernelReadout e₀ θ t t₀ := by
  rw [kernelReadout_apply, functionalSewPair_apply, negOnePowCast_mul_finsum]
  exact finsum_congr fun t => by simp only [kernelReadout_apply, negOnePowCast_add]; ring

/-- For input operator kernels `φ₁`, `φ₂` of degree parities `j₁`, `j₂`, input-pair sewing
multiplies the readout of `(φ₁ ⊗ φ₂) ∘ n'` by `(-1)^(j₂ d₁ p₁ + j₁ j₂)`. -/
theorem functionalSewPair_kernelReadout_of_even_sub {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ}
    {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ} {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R} {j₁ j₂ : ℤ}
    (hφ₁ : ∀ p₁ t₁, φ₁ p₁ t₁ ≠ 0 → Even (e₁ t₁ - d₁ p₁ - j₁))
    (hφ₂ : ∀ p₂ t₂, φ₂ p₂ t₂ ≠ 0 → Even (e₂ t₂ - d₂ p₂ - j₂))
    (n' : T₁ → T₂ → T₀ → R) (q : S₁ × S₂) (t₀ : T₀) :
    functionalSewPair d₂ e₁ e₂ (kernelReadout e₁ φ₁) (kernelReadout e₂ φ₂)
        (kernelReadout e₀ fun t => n' t.1 t.2) q t₀ =
      negOnePowCast R (j₂ * d₁ q.1 + j₁ * j₂) *
        kernelReadout e₀ (kernelComp (kernelTensor φ₁ φ₂) fun t => n' t.1 t.2) q t₀ := by
  refine eq_negOnePowCast_mul_kernelReadout ?_
  rw [kernelReadout_functionalSewPair, kernelComp_apply, negOnePowCast_mul_finsum]
  refine finsum_congr fun t => ?_
  simp only [kernelReadout_kernelReadout, kernelTensor_apply]
  by_cases h₁ : φ₁ q.1 t.1 = 0
  · simp [h₁]
  · by_cases h₂ : φ₂ q.2 t.2 = 0
    · simp [h₂]
    · have hd : -(e₁ t.1 * (d₂ q.2 - e₂ t.2)) =
          e₁ t.1 * (e₂ t.2 - d₂ q.2 - j₂) + j₂ * (e₁ t.1 - d₁ q.1 - j₁) +
            (j₂ * d₁ q.1 + j₁ * j₂) := by ring
      rw [← negOnePowCast_neg, hd, negOnePowCast_add, negOnePowCast_add,
        negOnePowCast_even ((hφ₂ q.2 t.2 h₂).mul_left (e₁ t.1)),
        negOnePowCast_even ((hφ₁ q.1 t.1 h₁).mul_left j₂), one_mul, one_mul]
      ring

/-- When `φ₂` preserves degree parity, input-pair sewing gives the readout of `(φ₁ ⊗ φ₂) ∘ n'`
with no extra sign and no degree condition on `φ₁` or `n'`. -/
theorem functionalSewPair_kernelReadout_of_even {d₂ : S₂ → ℤ} {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ}
    {e₀ : T₀ → ℤ} {φ₂ : S₂ → T₂ → R} (hφ₂ : ∀ p₂ t₂, φ₂ p₂ t₂ ≠ 0 → Even (d₂ p₂ - e₂ t₂))
    (φ₁ : S₁ → T₁ → R) (n' : T₁ → T₂ → T₀ → R) :
    functionalSewPair d₂ e₁ e₂ (kernelReadout e₁ φ₁) (kernelReadout e₂ φ₂)
        (kernelReadout e₀ fun t => n' t.1 t.2) =
      kernelReadout e₀ (kernelComp (kernelTensor φ₁ φ₂) fun t => n' t.1 t.2) := by
  apply kernelReadout_injective e₀; funext q t₀
  simp only [kernelReadout_functionalSewPair, kernelReadout_kernelReadout, kernelComp_apply,
    kernelTensor_apply]
  refine finsum_congr fun t => ?_
  by_cases h₂ : φ₂ q.2 t.2 = 0
  · simp [h₂]
  · rw [negOnePowCast_even ((hφ₂ q.2 t.2 h₂).mul_left (e₁ t.1)), one_mul, mul_assoc]

/-- **Continuation compatibility** `φ₀ (a ⋆ b) - φ₁ a ⋆' φ₂ b = η₀ (K (a ⊗ b)) + K (D (a ⊗ b))`
from a continuation-family count-functional boundary. -/
theorem kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_functionalBoundary
    [DecidableEq S₁] [DecidableEq S₂]
    {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₀ : T₀ → ℝ}
    {C C' C₁ C₂ C₀ Ck Cη E₁ E₂ : ℝ}
    {n : S₁ → S₂ → S₀ → R} {n' : T₁ → T₂ → T₀ → R}
    {φ₁ : S₁ → T₁ → R} {φ₂ : S₂ → T₂ → R} {φ₀ : S₀ → T₀ → R}
    {k : S₁ × S₂ → T₀ → R} {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {η₀ : T₀ → T₀ → R}
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (hn' : ∀ t₁ t₂ t₀, n' t₁ t₂ t₀ ≠ 0 → G₀ t₀ ≤ G₁ t₁ + G₂ t₂ + C')
    (hfin' : ∀ t₁ t₂, n' t₁ t₂ ∈ NovikovModule R G₀)
    (hφ₁ : ∀ p t, φ₁ p t ≠ 0 → G₁ t ≤ F₁ p + C₁) (hφ₁fin : ∀ p, φ₁ p ∈ NovikovModule R G₁)
    (hφ₂ : ∀ p t, φ₂ p t ≠ 0 → G₂ t ≤ F₂ p + C₂) (hφ₂fin : ∀ p, φ₂ p ∈ NovikovModule R G₂)
    (hφ₀ : ∀ p t, φ₀ p t ≠ 0 → G₀ t ≤ F₀ p + C₀) (hφ₀fin : ∀ p, φ₀ p ∈ NovikovModule R G₀)
    (hk : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → G₀ t₀ ≤ F₁ q.1 + F₂ q.2 + Ck)
    (hkfin : ∀ q, k q ∈ NovikovModule R G₀)
    (hη₀ : ∀ t t', η₀ t t' ≠ 0 → G₀ t' ≤ G₀ t + Cη) (hη₀fin : ∀ t, η₀ t ∈ NovikovModule R G₀)
    (hδ₁ : ∀ p q, δ₁ p q ≠ 0 → F₁ q ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
    (hδ₂ : ∀ p q, δ₂ p q ≠ 0 → F₂ q ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
    (hφ₂deg : ∀ p₂ t₂, φ₂ p₂ t₂ ≠ 0 → Even (d₂ p₂ - e₂ t₂))
    (hkd : ∀ (q : S₁ × S₂) t₀, k q t₀ ≠ 0 → e₀ t₀ = d₁ q.1 + d₂ q.2 - 1)
    (hB : ∀ q t₀, functionalBoundary (fun q : S₁ × S₂ => d₁ q.1 + d₂ q.2) e₀
        (tensorDifferential d₁ δ₁ δ₂) η₀ (kernelReadout e₀ k) q t₀ =
      functionalSew d₀ (kernelReadout d₀ fun r => n r.1 r.2) (kernelReadout e₀ φ₀) q t₀ -
        functionalSewPair d₂ e₁ e₂ (kernelReadout e₁ φ₁) (kernelReadout e₂ φ₂)
          (kernelReadout e₀ fun t => n' t.1 t.2) q t₀)
    {i : ℤ} {a : NovikovModule R F₁} (ha : a ∈ gradeBy R F₁ d₁ i) (b : NovikovModule R F₂) :
    kernelMap hφ₀ hφ₀fin (kernelProduct hn hfin a b) -
        kernelProduct hn' hfin' (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) =
      kernelMap hη₀ hη₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (tensor (kernelMap hδ₁ hδ₁fin a) b) +
        (i.negOnePow : R) • kernelMap hk hkfin (tensor a (kernelMap hδ₂ hδ₂fin b)) := by
  refine kernelMap_kernelProduct_sub_kernelProduct_kernelMap_of_mem_gradeBy hn hfin hn' hfin'
    hφ₁ hφ₁fin hφ₂ hφ₂fin hφ₀ hφ₀fin hk hkfin hη₀ hη₀fin hδ₁ hδ₁fin hδ₂ hδ₂fin
    (fun q t₀ => ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
      (s := kernelComp (fun r : S₁ × S₂ => n r.1 r.2) φ₀ -
        kernelComp (kernelTensor φ₁ φ₂) fun t => n' t.1 t.2) hkd q t₀).mp ?_).symm) ha b
  rw [hB q t₀, functionalSew_kernelReadout, functionalSewPair_kernelReadout_of_even hφ₂deg,
    kernelReadout_sub]; rfl

/-- **Homotopy inverse** `ψ₀ φ₀ - 1 = h₀ δ₀ + δ₀ h₀` from a boundary against `evalFunctional`. -/
theorem kernelComp_sub_diagonal_eq_add_of_functionalBoundary_evalFunctional [DecidableEq S₀]
    {d₀ : S₀ → ℤ} {e₀ : T₀ → ℤ} {δ₀ h₀ : S₀ → S₀ → R} {ψ₀ : S₀ → T₀ → R} {φ₀ : T₀ → S₀ → R}
    (hh₀d : ∀ p p', h₀ p p' ≠ 0 → d₀ p' = d₀ p - 1) {p p' : S₀}
    (hB : functionalBoundary d₀ d₀ δ₀ δ₀ (kernelReadout d₀ h₀) p p' =
      functionalSew e₀ (kernelReadout e₀ ψ₀) (kernelReadout d₀ φ₀) p p' -
        evalFunctional d₀ p p') :
    kernelComp ψ₀ φ₀ p p' - (if p = p' then 1 else 0) =
      kernelComp h₀ δ₀ p p' + kernelComp δ₀ h₀ p p' := by
  refine ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
    (s := kernelComp ψ₀ φ₀ - fun p p' => if p = p' then 1 else 0) hh₀d p p').mp ?_).symm
  rw [hB, functionalSew_kernelReadout, kernelReadout_sub]; simp only [Pi.sub_apply]
  rw [← kernelReadout_evalFunctional (R := R) d₀, kernelReadout_kernelReadout]

/-- **Multiplicative PSS comparison homotopy** between `φ₁ a ⋆ φ₂ b` and `φ₀ (a ⋆_q b)` from
three-end comparison and inverse-homotopy count-functional boundaries. -/
theorem kernelProduct_kernelMap_sub_kernelMap_kernelProduct_of_functionalBoundary
    [DecidableEq S₀]
    {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₀ : T₀ → ℝ}
    {C Cq C₁ C₂ C₀ Cψ Ck Ch Cδ Cη CD : ℝ}
    {n : S₁ → S₂ → S₀ → R} {q : T₁ → T₂ → T₀ → R}
    {φ₁ : T₁ → S₁ → R} {φ₂ : T₂ → S₂ → R} {φ₀ : T₀ → S₀ → R} {ψ₀ : S₀ → T₀ → R}
    {k : T₁ × T₂ → T₀ → R} {h₀ : S₀ → S₀ → R} {δ₀ : S₀ → S₀ → R} {η₀ : T₀ → T₀ → R}
    {D : T₁ × T₂ → T₁ × T₂ → R}
    {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (hq : ∀ t₁ t₂ t₀, q t₁ t₂ t₀ ≠ 0 → G₀ t₀ ≤ G₁ t₁ + G₂ t₂ + Cq)
    (hqfin : ∀ t₁ t₂, q t₁ t₂ ∈ NovikovModule R G₀)
    (hφ₁ : ∀ t p, φ₁ t p ≠ 0 → F₁ p ≤ G₁ t + C₁) (hφ₁fin : ∀ t, φ₁ t ∈ NovikovModule R F₁)
    (hφ₂ : ∀ t p, φ₂ t p ≠ 0 → F₂ p ≤ G₂ t + C₂) (hφ₂fin : ∀ t, φ₂ t ∈ NovikovModule R F₂)
    (hφ₀ : ∀ t p, φ₀ t p ≠ 0 → F₀ p ≤ G₀ t + C₀) (hφ₀fin : ∀ t, φ₀ t ∈ NovikovModule R F₀)
    (hψ₀ : ∀ p t, ψ₀ p t ≠ 0 → G₀ t ≤ F₀ p + Cψ) (hψ₀fin : ∀ p, ψ₀ p ∈ NovikovModule R G₀)
    (hk : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + Ck)
    (hkfin : ∀ t, k t ∈ NovikovModule R G₀)
    (hh₀ : ∀ p p', h₀ p p' ≠ 0 → F₀ p' ≤ F₀ p + Ch) (hh₀fin : ∀ p, h₀ p ∈ NovikovModule R F₀)
    (hδ₀ : ∀ p p', δ₀ p p' ≠ 0 → F₀ p' ≤ F₀ p + Cδ) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
    (hη₀ : ∀ t t', η₀ t t' ≠ 0 → G₀ t' ≤ G₀ t + Cη) (hη₀fin : ∀ t, η₀ t ∈ NovikovModule R G₀)
    (hD : ∀ t t', D t t' ≠ 0 → G₁ t'.1 + G₂ t'.2 ≤ G₁ t.1 + G₂ t.2 + CD)
    (hDfin : ∀ t, D t ∈ NovikovModule R fun t' : T₁ × T₂ => G₁ t'.1 + G₂ t'.2)
    (hφ₂deg : ∀ t₂ p₂, φ₂ t₂ p₂ ≠ 0 → Even (e₂ t₂ - d₂ p₂))
    (hkd : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → e₀ t₀ = e₁ t.1 + e₂ t.2 - 1)
    (hh₀d : ∀ p p', h₀ p p' ≠ 0 → d₀ p' = d₀ p - 1)
    (hφ₀D : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ e₀ i →
      kernelMap hδ₀ hδ₀fin (kernelMap hφ₀ hφ₀fin a) =
        kernelMap hφ₀ hφ₀fin (kernelMap hη₀ hη₀fin a))
    (hBk : ∀ t t₀, functionalBoundary (fun t : T₁ × T₂ => e₁ t.1 + e₂ t.2) e₀ D η₀
        (kernelReadout e₀ k) t t₀ =
      functionalSew d₀
          (functionalSewPair e₂ d₁ d₂ (kernelReadout d₁ φ₁) (kernelReadout d₂ φ₂)
            (kernelReadout d₀ fun p => n p.1 p.2))
          (kernelReadout e₀ ψ₀) t t₀ -
        kernelReadout e₀ (fun t => q t.1 t.2) t t₀)
    (hBh₀ : ∀ p p', functionalBoundary d₀ d₀ δ₀ δ₀ (kernelReadout d₀ h₀) p p' =
      functionalSew e₀ (kernelReadout e₀ ψ₀) (kernelReadout d₀ φ₀) p p' - evalFunctional d₀ p p')
    {i j : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ e₁ i)
    {b : NovikovModule R G₂} (hb : b ∈ gradeBy R G₂ e₂ j) :
    kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) -
        kernelMap hφ₀ hφ₀fin (kernelProduct hq hqfin a b) =
      kernelMap hδ₀ hδ₀fin (kernelMap hφ₀ hφ₀fin (kernelMap hk hkfin (tensor a b)) -
          kernelMap hh₀ hh₀fin
            (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b))) +
        (kernelMap hφ₀ hφ₀fin (kernelMap hk hkfin (kernelMap hD hDfin (tensor a b))) -
          kernelMap hh₀ hh₀fin (kernelMap hδ₀ hδ₀fin
            (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b)))) := by
  refine kernelProduct_kernelMap_sub_kernelMap_kernelProduct hn hfin hq hqfin hφ₁ hφ₁fin hφ₂
    hφ₂fin hφ₀ hφ₀fin hψ₀ hψ₀fin hk hkfin hh₀ hh₀fin hδ₀ hδ₀fin hη₀ hη₀fin (ε := 0) hD hDfin
    (fun t t₀ h => by rw [zero_sub, ← sub_eq_add_neg]; exact hkd t t₀ h) hφ₀D
    (fun t t₀ => ((functionalBoundary_kernelReadout_eq_kernelReadout_iff
      (s := kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p => n p.1 p.2) ψ₀ -
        fun t => q t.1 t.2) hkd t t₀).mp ?_).symm)
    (fun p p' => kernelComp_sub_diagonal_eq_add_of_functionalBoundary_evalFunctional hh₀d
      (hBh₀ p p')) ha hb
  rw [hBk t t₀, functionalSewPair_kernelReadout_of_even hφ₂deg, functionalSew_kernelReadout,
    kernelReadout_sub]; rfl

end PairSewing

end NovikovModule

end TauCeti
