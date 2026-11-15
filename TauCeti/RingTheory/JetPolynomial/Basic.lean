/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import TauCeti.Algebra.MvPolynomial.Derivation
public import TauCeti.RingTheory.Derivation.Coordinates

/-!
# Polynomial jets and total derivatives

Fix a finite type `ι` of base coordinates `x^μ` and a type `α` of field components `u^a`. The
*jet variables* `u^a_I` are indexed by a component `a` and a symmetric multi-index `I : ι → ℕ`,
the coordinate standing for the derivative `∂^I u^a`; the order of `u^a_I` is `|I| = ∑ μ, I μ`.
Position-dependent coefficients come from a commutative `R`-algebra `A` with derivations
`∂_μ`, for instance smooth functions of `x` with their partial derivatives, or polynomials in
`x` with `MvPolynomial.pderiv`.

`TauCeti.JetPolynomial ι α A` is the polynomial algebra over `A` in all jet variables. The
*total derivative* `TauCeti.totalDeriv ∂ μ` is the `R`-derivation of this algebra acting on
coefficients by `∂_μ` and on jet variables by `D_μ u^a_I = u^a_{I + e_μ}`:

`D_μ = ∂_μ + ∑_{a, I} u^a_{I + e_μ} ∂/∂u^a_I`.

The jet variables of order at most `r` generate the stage-`r` subalgebra
`TauCeti.jetStage ι α A r`. Total derivatives raise the stage by at most one, and no fixed
stage is closed under them, which is why the algebra uses all jet variables at once. Total
derivatives pairwise commute when the `∂_μ` do. Finally, evaluating jet variables on the derivatives
`∂^I f^a` of a field `f` in a differential algebra `B` intertwines total derivatives with the
derivations of `B` (`TauCeti.apply_jetEval`); this is the sense in which `D_μ` is the
derivative of a polynomial expression along a field.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A, for jet coordinates and total
  derivatives.
* Peter J. Olver, *Applications of Lie Groups to Differential Equations*, 2nd ed., §2.3, for
  total derivatives of differential functions.
-/

public section

noncomputable section

open MvPolynomial

namespace TauCeti

variable (ι α A : Type*)

/-- The polynomial jet algebra: polynomials with coefficients in `A` in the jet variables
`u^a_I = X (a, I)`, for a field component `a : α` and a symmetric multi-index `I : ι → ℕ`. -/
abbrev JetPolynomial [CommSemiring A] := MvPolynomial (α × (ι → ℕ)) A

/-- The stage-`r` subalgebra of the polynomial jet algebra: the polynomials in the jet variables
`u^a_I` of order `|I| ≤ r`. -/
def jetStage [CommSemiring A] [Fintype ι] (r : ℕ) : Subalgebra A (JetPolynomial ι α A) :=
  supported A {v | ∑ μ, v.2 μ ≤ r}

variable {ι α A}

/-! ### Stages -/

section Stage

variable [CommSemiring A] [Fintype ι]

/-- The defining formula of the stage-`r` subalgebra. -/
theorem jetStage_def (r : ℕ) : jetStage ι α A r = supported A {v | ∑ μ, v.2 μ ≤ r} := (rfl)

/-- A polynomial lies in stage `r` if and only if all its jet variables have order at most
`r`. -/
@[grind =]
theorem mem_jetStage_iff {r : ℕ} {p : JetPolynomial ι α A} :
    p ∈ jetStage ι α A r ↔ ∀ v ∈ p.vars, ∑ μ, v.2 μ ≤ r := by
  simp [jetStage_def, mem_supported, Set.subset_def]

/-- Constants lie in every stage. -/
@[simp]
theorem C_mem_jetStage {r : ℕ} (a : A) : (C a : JetPolynomial ι α A) ∈ jetStage ι α A r :=
  (jetStage ι α A r).algebraMap_mem a

/-- The jet variable `u^a_I` lies in every stage `r ≥ |I|`. -/
theorem X_mem_jetStage {r : ℕ} {a : α} {I : ι → ℕ} (h : ∑ μ, I μ ≤ r) :
    (X (a, I) : JetPolynomial ι α A) ∈ jetStage ι α A r := by
  rw [jetStage_def, supported_eq_adjoin_X]
  exact Algebra.subset_adjoin ⟨(a, I), h, rfl⟩

/-- The jet variable `u^a_I` lies in stage `r` if and only if its order is at most `r`. -/
@[simp, grind =]
theorem X_mem_jetStage_iff [Nontrivial A] {r : ℕ} {a : α} {I : ι → ℕ} :
    (X (a, I) : JetPolynomial ι α A) ∈ jetStage ι α A r ↔ ∑ μ, I μ ≤ r := by
  simp [jetStage_def, X_mem_supported]

/-- The stages increase with `r`. -/
theorem jetStage_mono {r s : ℕ} (h : r ≤ s) : jetStage ι α A r ≤ jetStage ι α A s :=
  supported_mono fun _ hv => le_trans hv h

/-- Every polynomial jet lies in some stage: the stages exhaust the polynomial jet algebra. -/
@[simp]
theorem iSup_jetStage : ⨆ r, jetStage ι α A r = ⊤ := by
  refine eq_top_iff.2 fun p _ => Algebra.mem_iSup_of_mem (p.vars.sup fun v => ∑ μ, v.2 μ) ?_
  exact mem_jetStage_iff.2 fun v hv => Finset.le_sup (f := fun v => ∑ μ, v.2 μ) hv

end Stage

/-! ### Total derivatives -/

section TotalDeriv

variable {R : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (d : ι → Derivation R A A)

/-- The total derivative `D_μ` on the polynomial jet algebra, for coefficient derivations
`d μ = ∂_μ` of `A`: it differentiates coefficients by `∂_μ` and sends the jet variable `u^a_I`
to `u^a_{I + e_μ}`. -/
def totalDeriv (μ : ι) : Derivation R (JetPolynomial ι α A) (JetPolynomial ι α A) :=
  letI := Classical.decEq ι
  (d μ).mvMapCoeffs +
    (mkDerivation A fun v : α × (ι → ℕ) => (X (v.1, v.2 + Pi.single μ 1) :
      JetPolynomial ι α A)).restrictScalars R

/-- The defining formula of the total derivative: the coefficientwise derivation plus the
`A`-linear derivation raising the multi-index of each jet variable. -/
theorem totalDeriv_def [DecidableEq ι] (μ : ι) :
    totalDeriv (α := α) d μ = (d μ).mvMapCoeffs +
      (mkDerivation A fun v : α × (ι → ℕ) => (X (v.1, v.2 + Pi.single μ 1) :
        JetPolynomial ι α A)).restrictScalars R := by
  unfold totalDeriv; congr!

/-- Total derivatives act on coefficients by the coefficient derivations. -/
@[simp, grind =]
theorem totalDeriv_C (μ : ι) (a : A) :
    totalDeriv d μ (C a : JetPolynomial ι α A) = C (d μ a) := by
  simp [totalDeriv, derivation_C]

/-- Total derivatives raise the multi-index of a jet variable: `D_μ u^a_I = u^a_{I + e_μ}`. -/
@[simp, grind =]
theorem totalDeriv_X [DecidableEq ι] (μ : ι) (a : α) (I : ι → ℕ) :
    totalDeriv d μ (X (a, I) : JetPolynomial ι α A) = X (a, I + Pi.single μ 1) := by
  simp [totalDeriv_def]

/-- The total derivative `D_μ` is the only `R`-derivation of the polynomial jet algebra acting
on coefficients by `∂_μ` and sending `u^a_I` to `u^a_{I + e_μ}`. -/
theorem eq_totalDeriv [DecidableEq ι] {μ : ι}
    {D : Derivation R (JetPolynomial ι α A) (JetPolynomial ι α A)}
    (hC : ∀ a, D (C a) = C (d μ a))
    (hX : ∀ (a : α) (I : ι → ℕ), D (X (a, I)) = X (a, I + Pi.single μ 1)) :
    D = totalDeriv d μ :=
  derivation_ext' (fun a => by rw [hC, totalDeriv_C]) fun v => by rw [hX, totalDeriv_X]

/-- Total derivatives in two directions commute when the coefficient derivations do. -/
theorem totalDeriv_comm {μ ν : ι} (hd : Commute (d μ : Module.End R A) (d ν))
    (p : JetPolynomial ι α A) :
    totalDeriv d μ (totalDeriv d ν p) = totalDeriv d ν (totalDeriv d μ p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    have := LinearMap.congr_fun hd.eq a
    simp only [mul_apply_eq_comp, Derivation.coeFn_coe] at this
    simp [this]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p v hp =>
    obtain ⟨a, I⟩ := v
    simp only [Derivation.leibniz, smul_eq_mul, map_add, totalDeriv_X, hp, add_right_comm I]
    ring

/-- Total derivatives commute when the coefficient derivations do. -/
theorem commute_totalDeriv {μ ν : ι} (hd : Commute (d μ : Module.End R A) (d ν)) :
    Commute (totalDeriv (α := α) d μ : Module.End R (JetPolynomial ι α A))
      (totalDeriv (α := α) d ν) :=
  LinearMap.ext fun p => totalDeriv_comm (α := α) d hd p

variable [Fintype ι]

/-- Total derivatives raise the stage by at most one. -/
theorem totalDeriv_mem_jetStage {r : ℕ} {p : JetPolynomial ι α A} (hp : p ∈ jetStage ι α A r)
    (μ : ι) : totalDeriv d μ p ∈ jetStage ι α A (r + 1) := by
  classical
  rw [jetStage_def, supported_eq_adjoin_X] at hp
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨a, I⟩, hI, rfl⟩ := hx
    rw [totalDeriv_X, jetStage_def, supported_eq_adjoin_X]
    refine Algebra.subset_adjoin ⟨_, ?_, rfl⟩
    simpa [Finset.sum_add_distrib] using hI
  | algebraMap a =>
    rw [algebraMap_eq, totalDeriv_C]
    exact (jetStage ι α A (r + 1)).algebraMap_mem _
  | add p q _ _ hp hq => exact map_add (totalDeriv d μ) p q ▸ add_mem hp hq
  | mul p q hp' hq' hp hq =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hmono := jetStage_mono (ι := ι) (α := α) (A := A) (Nat.le_succ r)
    exact add_mem (mul_mem (hmono hp') hq) (mul_mem (hmono hq') hp)

/-- No stage is closed under total derivatives: the total derivative of a jet variable of order
`|I|` does not lie in stage `|I|`. -/
theorem totalDeriv_X_notMem_jetStage [Nontrivial A] (μ : ι) (a : α) (I : ι → ℕ) :
    totalDeriv d μ (X (a, I) : JetPolynomial ι α A) ∉ jetStage ι α A (∑ ν, I ν) := by
  classical
  simp [Finset.sum_add_distrib]

end TotalDeriv

/-! ### Evaluation along a field -/

section Eval

variable [CommSemiring A] [Fintype ι] {R B : Type*} [CommSemiring R] [CommSemiring B]
  [Algebra R B] [Algebra A B]
  (δ : ι → Derivation R B B) (hδ : ∀ i j, Commute (δ i : Module.End R B) (δ j)) (f : α → B)

/-- Evaluation of polynomial jets along a field `f : α → B` in an `A`-algebra `B` with commuting
derivations `δ_μ`: the jet variable `u^a_I` is sent to the derivative `∂^I f^a`. -/
def jetEval : JetPolynomial ι α A →ₐ[A] B :=
  aeval fun v => multiIndexDeriv δ hδ v.2 (f v.1)

/-- The defining formula of evaluation along a field. -/
theorem jetEval_def :
    jetEval (A := A) δ hδ f = aeval fun v => multiIndexDeriv δ hδ v.2 (f v.1) := (rfl)

/-- Evaluation along a field sends `u^a_I` to `∂^I f^a`. -/
@[simp, grind =]
theorem jetEval_X (a : α) (I : ι → ℕ) :
    jetEval δ hδ f (X (a, I) : JetPolynomial ι α A) = multiIndexDeriv δ hδ I (f a) :=
  aeval_X _ _

/-- **Total derivatives are derivatives along fields.** If the derivations `δ_μ` of `B` restrict
to the coefficient derivations `∂_μ` on `A`, then differentiating the evaluation of a polynomial
jet `p` along a field is evaluating its total derivative: `δ_μ (p(j f)) = (D_μ p)(j f)`. -/
theorem apply_jetEval [Algebra R A] (d : ι → Derivation R A A)
    (μ : ι) (hdδ : ∀ a, δ μ (algebraMap A B a) = algebraMap A B (d μ a))
    (p : JetPolynomial ι α A) :
    δ μ (jetEval δ hδ f p) = jetEval δ hδ f (totalDeriv d μ p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => rw [algHom_C, totalDeriv_C, algHom_C, hdδ]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, map_add]
  | mul_X p v hp =>
    obtain ⟨a, I⟩ := v
    have hI : δ μ (multiIndexDeriv δ hδ I (f a)) =
        multiIndexDeriv δ hδ (I + Pi.single μ 1) (f a) := by
      rw [add_comm I, multiIndexDeriv_single_add, mul_apply_eq_comp, Derivation.coeFn_coe]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, jetEval_X, totalDeriv_X, hI, hp]

end Eval

end TauCeti
