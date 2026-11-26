/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Characters as eigenvectors of group matrices

For a finite group `G` and a function `g : G → R`, the *group matrix*
`(g(t / s))_{s,t}` has every homomorphism `χ : G →* R` as an eigenvector, with eigenvalue
`∑ᵤ χ(u) g(u)`. By the adjugate, each such eigenvalue divides the group determinant.

## Main results

* `TauCeti.Matrix.of_div_mulVec_monoidHom`: the characters of `G` are eigenvectors of the group
  matrix.
* `TauCeti.Matrix.sum_mul_dvd_det_of_div`: each eigenvalue divides the group determinant.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Lemma 5.26 (the group
  determinant).

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Cyclotomic/Voronoi.lean`, declaration
`New.OddPart.mulVec_mulChar_eq_sum_smul`. Here the eigenvector statement is made for any finite
group.
-/

public section

open Finset Matrix

namespace TauCeti.Matrix

variable {G R : Type*} [Group G] [Fintype G] [CommRing R]

/-- **Characters are eigenvectors of group matrices.** For a finite group `G`, a
function `g : G → R` and a homomorphism `χ : G →* R`, the matrix `(g(t / s))_{s,t}` maps `χ` to
`(∑ᵤ χ(u) g(u)) χ`. -/
theorem of_div_mulVec_monoidHom (g : G → R) (χ : G →* R) :
    (of fun s t : G ↦ g (t / s)) *ᵥ (fun t ↦ χ t) = (∑ u, χ u * g u) • fun t ↦ χ t := by
  ext s
  simp only [mulVec, dotProduct, of_apply, Pi.smul_apply, smul_eq_mul, sum_mul]
  rw [← Equiv.sum_comp (Equiv.mulRight s)]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [Equiv.coe_mulRight, mul_div_cancel_right, map_mul]
  ring

/-- **Eigenvalues divide group determinants.** For a finite group `G`, a function
`g : G → R` and a homomorphism `χ : G →* R`, the eigenvalue `∑ᵤ χ(u) g(u)` divides the
determinant of `(g(t / s))_{s,t}`. -/
theorem sum_mul_dvd_det_of_div [DecidableEq G] (g : G → R) (χ : G →* R) :
    ∑ u, χ u * g u ∣ (of fun s t : G ↦ g (t / s)).det := by
  have h := congrArg (fun v ↦ (adjugate (of fun s t : G ↦ g (t / s)) *ᵥ v) 1)
    (of_div_mulVec_monoidHom g χ)
  simp only [mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec, mulVec_smul, Pi.smul_apply,
    smul_eq_mul, map_one, mul_one] at h
  exact ⟨_, h⟩

end TauCeti.Matrix
