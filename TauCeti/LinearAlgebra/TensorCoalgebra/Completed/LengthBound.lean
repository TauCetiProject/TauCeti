/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed.Map
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension

/-!
# Length bounds for finite-arity Taylor expansions

A Taylor map supported in arities at most `c + 1` replaces at most `c + 1` letters
by one letter. Its signed coderivation therefore shortens tensor length by at most `c`.
The extension by zero on the empty word has `CompletedTensorWords.HasLengthBound c`,
so it extends uniquely to the tensor-length completion. No homogeneity hypothesis is
needed: the Koszul twists change coefficients but preserve tensor length.

This supplies the length estimate used to complete finite-arity bar differentials.
Unbounded-arity Taylor maps require additional convergence data and are not covered.

The Taylor expansion follows Getzler--Jones, *A-infinity algebras and the cyclic bar
complex*, Sections 1--2; the length completion follows Loday--Vallette,
*Algebraic Operads*, Chapters 9--10.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

namespace ReducedTensorWords

/-- An arity-bounded graded Taylor expansion cannot contribute to a length more than `c`
below its input length. -/
theorem component_gradedCoderiv_of_eq_zero (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (c : ℕ)
    (hF : ∀ n : {n : ℕ // 0 < n}, c + 1 < n.1 → F ∘ₗ of R M n = 0)
    (k n : {n : ℕ // 0 < n}) (hn : k.1 + 1 + c ≤ n.1)
    (z : TensorPower R n.1 M) :
    component R M k (gradedCoderiv G F q (of R M n z)) = 0 := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      simp only [map_smul]
      suffices h : component R M k
          (gradedCoderiv G F q (of R M n (PiTensorProduct.tprod R x))) = 0 by
        rw [h, smul_zero]
      rw [gradedCoderiv_of_tprod, map_sum]
      apply Finset.sum_eq_zero
      intro p hp
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hfit : 0 < d ∧ p + d ≤ n.1
      · by_cases hdc : c + 1 < d
        · have hzero : F (subword R x p d) = 0 := by
            rw [subword_eq_of_tprod R x hfit.1 hfit.2]
            exact LinearMap.congr_fun (hF ⟨d, hfit.1⟩ hdc) _
          rw [hzero, splice_zero, map_zero]
        · rw [splice_eq_of_tprod R _ _ hfit.1 hfit.2 (by omega)]
          apply component_of_of_ne
          intro heq
          have := congrArg Subtype.val heq
          dsimp only at this
          omega
      · rw [splice_eq_zero_of_not_fits R _ _ hfit, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end ReducedTensorWords

namespace TensorWords

/-- Extending an arity-bounded graded Taylor expansion by zero on the empty word has
the corresponding uniform length bound. -/
theorem hasLengthBound_extendReduced_gradedCoderiv (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (c : ℕ)
    (hF : ∀ n : {n : ℕ // 0 < n}, c + 1 < n.1 →
      F ∘ₗ ReducedTensorWords.of R M n = 0) :
    CompletedTensorWords.HasLengthBound c
      (extendReduced (ReducedTensorWords.gradedCoderiv G F q)) := by
  rw [CompletedTensorWords.hasLengthBound_iff_component_of_eq_zero]
  intro k n hn z
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · simp
  · rw [extendReduced_of _ hnpos, component_reducedInclusion]
    split_ifs with hk
    · exact ReducedTensorWords.component_gradedCoderiv_of_eq_zero G F q c hF
        ⟨k, hk⟩ ⟨n, hnpos⟩ hn z
    · rfl

end TensorWords
end TauCeti
