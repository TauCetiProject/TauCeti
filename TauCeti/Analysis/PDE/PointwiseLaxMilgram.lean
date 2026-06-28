/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Pointwise Lax--Milgram solutions for PDE energy integrands

Lane D of the PDE roadmap ultimately applies Lax--Milgram to an integrated weak energy form.
The existing pointwise files already provide boundedness and coercivity estimates for the jet
integrand `energyIntegrand A b c` on `ℝ × EuclideanSpace ℝ n`. This file moves that integrand
to the Hilbert product `WithLp 2 (ℝ × EuclideanSpace ℝ n)` and records the corresponding
pointwise existence-and-uniqueness API.

These are finite-dimensional statements about a single jet, not weak Sobolev-space theorems.
They are the consumer forms that the later integrated energy-form layer will mirror after the
weak Sobolev space and integral construction are available.

## Main declarations

* `TauCeti.PDE.HilbertJet`: the L2 product Hilbert space of a value and a gradient.
* `TauCeti.PDE.energyIntegrandHilbert`: the pointwise energy integrand transported to
  `HilbertJet n`.
* `TauCeti.PDE.isCoercive_energyIntegrandHilbert_of_bounds`: coercivity from an ellipticity
  floor, drift bound, and dominating mass lower bound.
* `TauCeti.PDE.energyIntegrandHilbertSolutionOfInner` and
  `TauCeti.PDE.existsUnique_energyIntegrandHilbert_forall_eq_inner`: the pointwise
  Lax--Milgram solution and its existence-and-uniqueness theorem.
* `TauCeti.PDE.UniformlyEllipticOn.existsUnique_energyIntegrandHilbert` and `_on`: wrappers
  for the roadmap's bundled principal-coefficient hypothesis.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]
variable {lam Lam beta mu : ℝ}

/-- The Hilbert pointwise jet space: a function value and its gradient with the L2 product
norm and inner product. -/
abbrev HilbertJet (n : Type*) : Type _ :=
  WithLp 2 (ℝ × EuclideanSpace ℝ n)

/-- The continuous linear equivalence from the Hilbert jet space to the ordinary product
used by the pointwise coefficient API. -/
abbrev hilbertJetEquiv (n : Type*) [Fintype n] :
    HilbertJet n ≃L[ℝ] ℝ × EuclideanSpace ℝ n :=
  WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (EuclideanSpace ℝ n)

/-- The pointwise weak-form integrand transported to the L2 Hilbert product of value and
gradient jets. -/
def energyIntegrandHilbert (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    HilbertJet n →L[ℝ] HilbertJet n →L[ℝ] ℝ :=
  (energyIntegrand A b c).bilinearComp
    (hilbertJetEquiv n : HilbertJet n →L[ℝ] ℝ × EuclideanSpace ℝ n)
    (hilbertJetEquiv n : HilbertJet n →L[ℝ] ℝ × EuclideanSpace ℝ n)

/-- The Hilbert-jet form evaluates by forgetting the `WithLp 2` wrapper. -/
@[simp]
lemma energyIntegrandHilbert_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ)
    (U V : HilbertJet n) :
    energyIntegrandHilbert A b c U V =
      energyIntegrand A b c (WithLp.ofLp U) (WithLp.ofLp V) :=
  ContinuousLinearMap.bilinearComp_apply
    (energyIntegrand A b c)
    (hilbertJetEquiv n : HilbertJet n →L[ℝ] ℝ × EuclideanSpace ℝ n)
    (hilbertJetEquiv n : HilbertJet n →L[ℝ] ℝ × EuclideanSpace ℝ n) U V

omit [DecidableEq n] in
/-- The L2 product norm lower-bound bridge for coercivity estimates on Hilbert jets. -/
lemma min_mul_hilbertJet_norm_sq_le_add {a d : ℝ} (_ha : 0 ≤ a) (_hd : 0 ≤ d)
    (U : HilbertJet n) :
    min a d * ‖U‖ ^ 2 ≤ a * ‖U.snd‖ ^ 2 + d * U.fst ^ 2 := by
  have hmin_a : min a d ≤ a := min_le_left _ _
  have hmin_d : min a d ≤ d := min_le_right _ _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [Real.norm_eq_abs, sq_abs]
  have hfst : 0 ≤ U.fst ^ 2 := sq_nonneg _
  have hsnd : 0 ≤ ‖U.snd‖ ^ 2 := sq_nonneg _
  calc
    min a d * (U.fst ^ 2 + ‖U.snd‖ ^ 2)
        = min a d * U.fst ^ 2 + min a d * ‖U.snd‖ ^ 2 := by ring
    _ ≤ d * U.fst ^ 2 + a * ‖U.snd‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hmin_d hfst)
          (mul_le_mul_of_nonneg_right hmin_a hsnd)
    _ = a * ‖U.snd‖ ^ 2 + d * U.fst ^ 2 := by ring

/-- Coercivity of the Hilbert-jet energy integrand from raw coercive coefficient bounds.

The hypotheses are the finite-dimensional version of the coercive elliptic energy method:
the principal coefficient has lower quadratic bound `λ`, the drift is bounded by `β`, and
the mass lower bound `μ` dominates the drift defect `β² / (2λ)`. -/
lemma isCoercive_energyIntegrandHilbert_of_bounds {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b‖ ≤ beta) (hc : mu ≤ c) (hmu : beta ^ 2 / (2 * lam) < mu) :
    IsCoercive (energyIntegrandHilbert A b c) := by
  refine ⟨min (lam / 2) (mu - beta ^ 2 / (2 * lam)),
    min_coercivityConstant_pos hlam hmu, fun U => ?_⟩
  have hdelta : 0 ≤ mu - beta ^ 2 / (2 * lam) := (sub_pos.mpr hmu).le
  have hnorm := min_mul_hilbertJet_norm_sq_le_add (half_pos hlam).le hdelta U
  have henergy :=
    garding_energyIntegrand_self_of_mass_lower_bound_of_bounds
      (lam := lam) (beta := beta) (mu := mu) hlam hA hb hc (WithLp.ofLp U)
  simpa [energyIntegrandHilbert, pow_two, mul_assoc] using hnorm.trans henergy

/-- Coercivity of the Hilbert-jet zero-drift integrand from a positive mass coefficient. -/
lemma isCoercive_energyIntegrandHilbert_zero_drift {A : Matrix n n ℝ} {c : ℝ}
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 < c) :
    IsCoercive (energyIntegrandHilbert A 0 c) :=
  isCoercive_energyIntegrandHilbert_of_bounds (beta := 0) (mu := c) hlam hA (by simp)
    le_rfl (by simpa using hc)

/-- Coercivity of the shifted Laplacian Hilbert-jet integrand when the mass is positive. -/
lemma isCoercive_energyIntegrandHilbert_one_zero_mass {c : ℝ} (hc : 0 < c) :
    IsCoercive (energyIntegrandHilbert (1 : Matrix n n ℝ) 0 c) :=
  isCoercive_energyIntegrandHilbert_zero_drift zero_lt_one (by intro ξ; simp) hc

/-- The Lax--Milgram solution Hilbert jet for a coercive pointwise energy integrand.

For a coercive form `energyIntegrandHilbert A b c` and represented forcing jet `F`,
`energyIntegrandHilbertSolutionOfInner hB F` is the unique jet `U` satisfying
`energyIntegrandHilbert A b c U V = ⟪F, V⟫` for every test jet `V`. -/
def energyIntegrandHilbertSolutionOfInner {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ}
    (hB : IsCoercive (energyIntegrandHilbert A b c)) (F : HilbertJet n) :
    HilbertJet n :=
  TauCeti.IsCoercive.solutionOfInner hB F

/-- The pointwise Lax--Milgram solution satisfies the represented variational equation. -/
@[simp]
theorem apply_energyIntegrandHilbertSolutionOfInner_eq_inner {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ}
    (hB : IsCoercive (energyIntegrandHilbert A b c)) (F V : HilbertJet n) :
    energyIntegrandHilbert A b c (energyIntegrandHilbertSolutionOfInner hB F) V =
      ⟪F, V⟫_ℝ := by
  simp [energyIntegrandHilbertSolutionOfInner,
    TauCeti.IsCoercive.apply_solutionOfInner_eq_inner hB F V]

/-- A Hilbert jet satisfying the represented variational equation is the pointwise
Lax--Milgram solution. -/
theorem eq_energyIntegrandHilbertSolutionOfInner {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ}
    (hB : IsCoercive (energyIntegrandHilbert A b c)) {F U : HilbertJet n}
    (hU : ∀ V : HilbertJet n, energyIntegrandHilbert A b c U V = ⟪F, V⟫_ℝ) :
    U = energyIntegrandHilbertSolutionOfInner hB F := by
  simpa [energyIntegrandHilbertSolutionOfInner] using
    TauCeti.IsCoercive.eq_solutionOfInner hB hU

/-- Pointwise Lax--Milgram existence and uniqueness for any coercive Hilbert-jet energy
integrand. -/
theorem existsUnique_energyIntegrandHilbert_forall_eq_inner {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ}
    (hB : IsCoercive (energyIntegrandHilbert A b c)) (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert A b c U V = ⟪F, V⟫_ℝ :=
  TauCeti.IsCoercive.existsUnique_forall_eq_inner hB F

/-- Pointwise Lax--Milgram existence and uniqueness from raw coercive coefficient bounds. -/
theorem existsUnique_energyIntegrandHilbert_of_bounds {A : Matrix n n ℝ}
    {b : EuclideanSpace ℝ n} {c : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b‖ ≤ beta) (hc : mu ≤ c) (hmu : beta ^ 2 / (2 * lam) < mu)
    (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert A b c U V = ⟪F, V⟫_ℝ :=
  existsUnique_energyIntegrandHilbert_forall_eq_inner
    (isCoercive_energyIntegrandHilbert_of_bounds hlam hA hb hc hmu) F

/-- Pointwise Lax--Milgram existence and uniqueness for the zero-drift Hilbert-jet energy
integrand with positive mass. -/
theorem existsUnique_energyIntegrandHilbert_zero_drift {A : Matrix n n ℝ} {c : ℝ}
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 < c) (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert A 0 c U V = ⟪F, V⟫_ℝ :=
  existsUnique_energyIntegrandHilbert_forall_eq_inner
    (isCoercive_energyIntegrandHilbert_zero_drift hlam hA hc) F

/-- Pointwise Lax--Milgram existence and uniqueness for the shifted Laplacian model
`-Δ + c` with positive mass. -/
theorem existsUnique_energyIntegrandHilbert_one_zero_mass {c : ℝ} (hc : 0 < c)
    (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert (1 : Matrix n n ℝ) 0 c U V = ⟪F, V⟫_ℝ :=
  existsUnique_energyIntegrandHilbert_forall_eq_inner
    (isCoercive_energyIntegrandHilbert_one_zero_mass hc) F

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}

/-- Coercivity of the Hilbert-jet energy integrand from uniform ellipticity, a drift bound,
and a mass lower bound that dominates the drift defect. -/
lemma isCoercive_energyIntegrandHilbert (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b : EuclideanSpace ℝ n} {c : ℝ}
    (hb : ‖b‖ ≤ beta) (hc : mu ≤ c) (hmu : beta ^ 2 / (2 * lam) < mu) :
    IsCoercive (energyIntegrandHilbert (a x) b c) :=
  PDE.isCoercive_energyIntegrandHilbert_of_bounds h.pos (h.lower_bound hx) hb hc hmu

/-- Coefficient-field form of
`UniformlyEllipticOn.isCoercive_energyIntegrandHilbert`. -/
lemma isCoercive_energyIntegrandHilbert_on (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) < mu) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrandHilbert (a x) (b x) (c x)) :=
  h.isCoercive_energyIntegrandHilbert hx (hb hx) (hc hx) hmu

/-- Pointwise Lax--Milgram existence and uniqueness from uniform ellipticity, a drift bound,
and a mass lower bound that dominates the drift defect. -/
theorem existsUnique_energyIntegrandHilbert (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b : EuclideanSpace ℝ n} {c : ℝ}
    (hb : ‖b‖ ≤ beta) (hc : mu ≤ c) (hmu : beta ^ 2 / (2 * lam) < mu)
    (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert (a x) b c U V = ⟪F, V⟫_ℝ :=
  PDE.existsUnique_energyIntegrandHilbert_forall_eq_inner
    (h.isCoercive_energyIntegrandHilbert hx hb hc hmu) F

/-- Coefficient-field form of
`UniformlyEllipticOn.existsUnique_energyIntegrandHilbert`. -/
theorem existsUnique_energyIntegrandHilbert_on (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) < mu) {x : X} (hx : x ∈ Ω)
    (F : HilbertJet n) :
    ∃! U : HilbertJet n, ∀ V : HilbertJet n,
      energyIntegrandHilbert (a x) (b x) (c x) U V = ⟪F, V⟫_ℝ :=
  h.existsUnique_energyIntegrandHilbert hx (hb hx) (hc hx) hmu F

end UniformlyEllipticOn

end PDE

end TauCeti
