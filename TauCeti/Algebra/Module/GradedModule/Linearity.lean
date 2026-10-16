/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Nakayama
public import TauCeti.Algebra.Module.GradedModule.Resolution

/-!
# Detecting linear graded resolutions

A graded projective resolution is linear when its term in homological degree `n` is generated in
internal degree `n`. For a nonnegatively graded algebra, graded Nakayama detects this condition on
the quotient of each term by the positive-degree action `A₊`: the resolution is linear exactly when
the quotient of its `n`th term is concentrated in internal degree `n`.

This criterion is stated both with explicit termwise lower bounds and for terms finite over the
grading's scalar ring. It is the generation-theoretic bridge from computations of a minimal
resolution modulo `A₊` to linearity of that resolution.

## Main results

* `TauCeti.GradedProjectiveResolution.isLinear_iff_piece_le_positive_smul_top`: the bounded-below
  criterion.
* `TauCeti.GradedProjectiveResolution.isLinear_iff_piece_le_positive_smul_top_of_finite`: the
  finite-term criterion.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  Section 1.2, for detecting linear resolutions from their generating degrees.
* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded Nakayama.
-/

public section

namespace TauCeti.GradedProjectiveResolution

universe uk uA uM w

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
variable {M : Type uM} [AddCommGroup M] [Module k M] [Module A M]
  {G : InternalGrading k M} {r : GradedProjectiveResolution.{uk, uA, uM, w} 𝒜 G}

/-- **A resolution is linear exactly when every term modulo `A₊` is concentrated in its
homological degree**, provided each term is bounded below. The explicit lower bounds may depend on
the homological degree. -/
theorem isLinear_iff_piece_le_positive_smul_top (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (b : ℕ → ℤ) (hbelow : ∀ n p, p < b n → (r.grading n).piece p = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), p ≠ n →
      (r.grading n).piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) := by
  rw [isLinear_iff]
  constructor
  · intro h n
    exact (InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top
      𝒜 h𝒜 (b n) (hbelow n) n).mp (h n)
  · intro h n
    exact (InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top
      𝒜 h𝒜 (b n) (hbelow n) n).mpr (h n)

/-- For a resolution whose terms are finite over the grading's scalar ring, linearity is
equivalent to concentration of each term modulo `A₊` in its homological degree. Finiteness supplies
the lower bounds required by graded Nakayama. -/
theorem isLinear_iff_piece_le_positive_smul_top_of_finite
    [∀ n, Module.Finite k (r.X n)] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥) :
    r.IsLinear ↔ ∀ (n : ℕ) (p : ℤ), p ≠ n →
      (r.grading n).piece p ≤
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (r.X n)) := by
  rw [isLinear_iff]
  constructor
  · intro h n
    exact (InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite
      𝒜 h𝒜 n).mp (h n)
  · intro h n
    exact (InternalGrading.isGeneratedInDegree_iff_piece_le_positive_smul_top_of_finite
      𝒜 h𝒜 n).mpr (h n)

end TauCeti.GradedProjectiveResolution
