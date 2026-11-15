/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Resolution
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.GradedDimension

/-!
# Degreewise Euler cancellation for linear resolutions

A linear graded projective resolution need not terminate. Over a nonnegatively graded algebra,
however, its term in homological degree `i` vanishes in every internal degree below `i`.
Consequently the Euler calculation is finite in each fixed internal degree, even when there is
no cohomological vanishing bound.

For a degree-zero idempotent `e`, the formula proved here is

`dim_k(e M_p) = ∑ i ≤ n, (-1)^i dim_k(e (P_i)_p)` whenever `p ≤ n`.

Restriction to `e` retains the coordinates needed for Hilbert and Cartan matrix identities.
The result before imposing linearity also applies whenever just the next term's degree-`p`
piece vanishes. Finite-dimensionality is required only for the pieces occurring in the sum.
No infinite Euler sum, convergence convention, or Euler-admissibility assumption is used.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 2.11, for the Hilbert-series calculation from linear resolutions.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
-/

public section

namespace TauCeti

open CategoryTheory Module
open scoped Pointwise

universe uk uA v

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)
  {e : A} (he : IsIdempotentElem e) (he₀ : e ∈ 𝒜 0)

include he he₀ in
/-- An exact graded resolution computes the dimension of each idempotent coordinate by a finite
alternating sum as soon as the next term vanishes in that internal degree. Finite-dimensionality
is needed only in the summation range. -/
theorem sum_range_neg_one_pow_finrank_smul_piece_eq_of_piece_eq_bot (p : ℤ) (n : ℕ)
    (hfinite : ∀ i ≤ n, Module.Finite k ↥(e • (r.grading i).piece p))
    (hzero : (r.grading (n + 1)).piece p = ⊥) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * finrank k ↥(e • (r.grading i).piece p) =
      finrank k ↥(e • M.grading.piece p) := by
  have h := sum_range_neg_one_pow_finrank_eq_add_of_exact
    (fun i ↦ GradedModuleCat.smulPieceMap e (r.differential i) p)
    (GradedModuleCat.smulPieceMap e r.augmentation p)
    (GradedModuleCat.smulPieceMap_surjective r.surjective_π p)
    (GradedModuleCat.exact_smulPieceMap he he₀ r.exact_d_π p)
    (fun i ↦ GradedModuleCat.exact_smulPieceMap he he₀ (r.exact_d_d i) p) n hfinite
  have : Subsingleton ↥(e • (r.grading (n + 1)).piece p) := by
    rw [hzero, Submodule.smul_bot']
    infer_instance
  have hmap : GradedModuleCat.smulPieceMap e (r.differential n) p = 0 :=
    Subsingleton.elim _ _
  rw [hmap, LinearMap.range_zero, finrank_bot, Nat.cast_zero, mul_zero, add_zero] at h
  exact h

variable {r} [GradedAlgebra 𝒜]

/-- In a fixed internal degree, the idempotent-coordinate dimensions of a linear resolution
have finite support, even if the resolution has nonzero terms in every homological degree. -/
theorem IsLinear.finite_finrankSupport_smul_piece (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (e : A) (p : ℤ) :
    (Function.support fun i ↦ finrank k ↥(e • (r.grading i).piece p)).Finite := by
  apply (Finset.range (p.toNat + 1)).finite_toSet.subset
  intro i hi
  by_contra hmem
  have hi' : p.toNat + 1 ≤ i := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using hmem
  have hpi : p < (i : ℤ) := by omega
  have hpiece : (r.grading i).piece p = ⊥ := hr.piece_eq_bot_of_lt hneg hpi
  have hdim : finrank k ↥(e • (r.grading i).piece p) = 0 := by
    rw [hpiece, Submodule.smul_bot', finrank_bot]
  exact hi hdim

include he he₀ in
/-- **Degreewise Euler cancellation for a possibly infinite linear resolution.** Any cutoff
at least the internal degree gives the same finite alternating dimension sum. This includes
negative internal degrees, where all the summands and the resolved piece vanish. -/
theorem IsLinear.sum_range_neg_one_pow_finrank_smul_piece_eq (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (p : ℤ) (n : ℕ) (hn : p ≤ (n : ℤ))
    (hfinite : ∀ i ≤ n, Module.Finite k ↥(e • (r.grading i).piece p)) :
    ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * finrank k ↥(e • (r.grading i).piece p) =
      finrank k ↥(e • M.grading.piece p) :=
  r.sum_range_neg_one_pow_finrank_smul_piece_eq_of_piece_eq_bot he he₀ p n hfinite
    (hr.piece_eq_bot_of_lt hneg (by omega))

include he he₀ in
/-- The degree-`p` dimension of the resolved module is computed through homological degree
`p.toNat`. Thus the cutoff is explicit and needs no cohomological vanishing witness. -/
theorem IsLinear.finrank_smul_piece_eq_sum (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) (p : ℤ)
    (hfinite : ∀ i ≤ p.toNat, Module.Finite k ↥(e • (r.grading i).piece p)) :
    (finrank k ↥(e • M.grading.piece p) : ℤ) =
      ∑ i ∈ Finset.range (p.toNat + 1),
        (-1 : ℤ) ^ i * finrank k ↥(e • (r.grading i).piece p) :=
  (hr.sum_range_neg_one_pow_finrank_smul_piece_eq he he₀ hneg p p.toNat
    (Int.self_le_toNat p) hfinite).symm

include he he₀ in
/-- Coefficientwise form of the Euler identity for graded dimensions. Although every term has a
Laurent-polynomial graded dimension, the alternating sum over the resolution is used only after
fixing a coefficient, where linearity makes it finite. -/
theorem IsLinear.coeff_smulGradedDimension_eq_sum (hr : r.IsLinear)
    (hneg : ∀ p < 0, 𝒜 p = ⊥) [Module.Finite k M] [∀ i, Module.Finite k (r.X i)]
    (p : ℤ) :
    (M.smulGradedDimension e).coeff p =
      ∑ i ∈ Finset.range (p.toNat + 1),
        (-1 : ℤ) ^ i * ((r.termObj i).smulGradedDimension e).coeff p := by
  simp only [GradedModuleCat.coeff_smulGradedDimension]
  exact hr.finrank_smul_piece_eq_sum he he₀ hneg p (fun _ _ ↦ inferInstance)

end GradedProjectiveResolution

end TauCeti
