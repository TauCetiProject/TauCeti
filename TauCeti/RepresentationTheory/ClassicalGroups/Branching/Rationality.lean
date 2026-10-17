/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Basic
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rationality

/-!
# Rational representations under the block inclusion

The block inclusion `TauCeti.glBlockSucc : GL (Fin n) ℂ →* GL (Fin (n + 1)) ℂ` replaces a
matrix `g` by `diag(g, 1)`.  Substitution of this block matrix into a polynomial in the entries of
an `(n + 1)`-square matrix again gives a polynomial in the entries of `g`.  Moreover the block
inclusion preserves determinants.  Consequently polynomial and rational functions pull back along
the inclusion, and polynomial and rational representations remain so after restriction.

Applying this to the rational Weyl representations gives the coordinate-regularity statement needed
by the `GL (n + 1) ↓ GL n` branching problem.  This file does not construct the multiplicity-free
decomposition of that restriction; the decomposition additionally needs the highest-weight
classification and complete reducibility.

## Main results

* `TauCeti.Matrix.GeneralLinearGroup.mem_polynomialFunctions_comp_glBlockSucc` and
  `TauCeti.Matrix.GeneralLinearGroup.mem_rationalFunctions_comp_glBlockSucc`: polynomial and
  rational functions pull back along the block inclusion.
* `TauCeti.IsPolynomialRep.comp_glBlockSucc` and `TauCeti.IsRationalRep.comp_glBlockSucc`:
  polynomiality and rationality are preserved by restriction.
* `TauCeti.isRationalRep_rationalWeylRep_comp_glBlockSucc`: the restricted rational Weyl
  representation is rational.
-/

public section

open Matrix MvPolynomial

universe u v

namespace TauCeti

section BlockSuccPolynomial

variable {k : Type u} [CommSemiring k] {n : ℕ}

/-- Substitute the generic block matrix `diag(X, 1)` into a polynomial in the entries of an
`(n + 1)`-square matrix. -/
private noncomputable def blockSuccPolynomial
    (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) k) :
    MvPolynomial (Fin n × Fin n) k :=
  MvPolynomial.aeval (fun p =>
    Matrix.blockSucc (Matrix.mvPolynomialX (Fin n) (Fin n) k) p.1 p.2) P

/-- Evaluating after substitution by the generic block matrix is evaluation at the corresponding
concrete block matrix. -/
private theorem eval_blockSuccPolynomial
    (P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) k)
    (M : Matrix (Fin n) (Fin n) k) :
    MvPolynomial.eval (fun p => M p.1 p.2) (blockSuccPolynomial P) =
      MvPolynomial.eval (fun p => Matrix.blockSucc M p.1 p.2) P := by
  unfold blockSuccPolynomial
  change MvPolynomial.aeval (fun p => M p.1 p.2)
      (MvPolynomial.aeval (fun p =>
        Matrix.blockSucc (Matrix.mvPolynomialX (Fin n) (Fin n) k) p.1 p.2) P) = _
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => MvPolynomial.aeval f P)
  funext p
  induction p.1 using Fin.lastCases with
  | last =>
      induction p.2 using Fin.lastCases with
      | last => simp
      | cast j => simp
  | cast i =>
      induction p.2 using Fin.lastCases with
      | last => simp
      | cast j => simp

end BlockSuccPolynomial

namespace Matrix.GeneralLinearGroup

section CommSemiring

variable {k : Type u} [CommSemiring k] {n : ℕ}

/-- **A polynomial function pulls back to a polynomial function along the block inclusion.** -/
theorem mem_polynomialFunctions_comp_glBlockSucc
    {f : GL (Fin (n + 1)) k → k} (hf : f ∈ polynomialFunctions k (n + 1)) :
    (fun g => f (glBlockSucc k n g)) ∈ polynomialFunctions k n := by
  obtain ⟨P, hP⟩ := mem_polynomialFunctions.mp hf
  refine mem_polynomialFunctions.mpr ⟨blockSuccPolynomial P, fun g => ?_⟩
  rw [hP, eval_blockSuccPolynomial, coe_glBlockSucc]

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

/-- **A rational function pulls back to a rational function along the block inclusion.**  The
denominator remains the same power because `diag(g, 1)` has determinant `det g`. -/
theorem mem_rationalFunctions_comp_glBlockSucc
    {f : GL (Fin (n + 1)) k → k} (hf : f ∈ rationalFunctions k (n + 1)) :
    (fun g => f (glBlockSucc k n g)) ∈ rationalFunctions k n := by
  obtain ⟨P, m, hP⟩ := mem_rationalFunctions.mp hf
  refine mem_rationalFunctions.mpr ⟨blockSuccPolynomial P, m, fun g => ?_⟩
  simpa only [coe_glBlockSucc, det_blockSucc, eval_blockSuccPolynomial] using
    hP (glBlockSucc k n g)

end CommRing

end Matrix.GeneralLinearGroup

/-! ## Restriction of representations -/

section Representations

open _root_.TauCeti.Matrix.GeneralLinearGroup

variable {n : ℕ} {W : Type v} [AddCommMonoid W] [Module ℂ W]
variable {ρ : Representation ℂ (GL (Fin (n + 1)) ℂ) W}

/-- **A polynomial representation remains polynomial after restriction along the block
inclusion.** -/
theorem IsPolynomialRep.comp_glBlockSucc (h : IsPolynomialRep ρ) :
    IsPolynomialRep (ρ.comp (glBlockSucc ℂ n)) := by
  obtain ⟨b, P, hP⟩ := (isPolynomialRep_iff ρ).mp h
  refine (isPolynomialRep_iff _).mpr
    ⟨b, fun i j => blockSuccPolynomial (P i j), fun g i j => ?_⟩
  change LinearMap.toMatrix b b (ρ (glBlockSucc ℂ n g)) i j = _
  rw [hP, eval_blockSuccPolynomial, coe_glBlockSucc]

/-- **A rational representation remains rational after restriction along the block inclusion.** -/
theorem IsRationalRep.comp_glBlockSucc (h : IsRationalRep ρ) :
    IsRationalRep (ρ.comp (glBlockSucc ℂ n)) := by
  obtain ⟨b, P, m, hP⟩ := (isRationalRep_iff ρ).mp h
  refine (isRationalRep_iff _).mpr
    ⟨b, fun i j => blockSuccPolynomial (P i j), m, fun g i j => ?_⟩
  change LinearMap.toMatrix b b (ρ (glBlockSucc ℂ n g)) i j = _
  simpa only [coe_glBlockSucc, det_blockSucc, eval_blockSuccPolynomial] using
    hP (glBlockSucc ℂ n g) i j

end Representations

/-! ## Restricted rational Weyl representations -/

/-- **The restriction of a rational Weyl representation from `GL (n + 1)` to `GL n` is
rational.**  This is the rationality input for its multiplicity-free branching decomposition. -/
@[simp]
theorem isRationalRep_rationalWeylRep_comp_glBlockSucc (n : ℕ)
    (l : DominantWeight (n + 1)) :
    IsRationalRep ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)) :=
  (isRationalRep_rationalWeylRep (n + 1) l).comp_glBlockSucc

end TauCeti
