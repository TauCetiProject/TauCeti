/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorCoalgebra.Completed.TensorProduct
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation

/-!
# Signed co-Leibniz identities after tensor-length completion

A signed coderivation on finite tensor words extends to the length completion when
it has a uniform length bound. Its extension satisfies the same signed co-Leibniz
identity, now in the product of tensor-power bidegrees. The two tensor-factor actions
are finite sums, and the Koszul twist acts on the left half of each cut.

No restriction on the ground characteristic or on the total letter degree is needed.
The length bound is essential: an arbitrary infinite-arity Taylor expansion need
not act on the product completion. This result provides the coalgebra compatibility
of bounded bar differentials, separately from their square-zero law.

The signs follow Getzler--Jones, *A-infinity algebras and the cyclic bar complex*,
Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*, Section 3.6.
-/

public section

namespace TauCeti.CompletedTensorWords

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {G : InternalGrading R M} {q : ℤ}
  {b : TensorWords R M →ₗ[R] TensorWords R M}

/-- Completing a bounded signed coderivation preserves its signed co-Leibniz
identity in every coproduct bidegree. -/
theorem deconcatenation_extend_of_isGradedCoderivation (c : ℕ)
    (hc : HasLengthBound c b) (hb : TensorWords.IsGradedCoderivation G q b)
    (x : CompletedTensorWords R M) (p r : ℕ) :
    deconcatenation R M (extend c b x) p r =
      tensorMap c 0 b LinearMap.id (deconcatenation R M x) p r +
        tensorMap 0 c (TensorWords.map (G.koszulTwist q)) b
          (deconcatenation R M x) p r := by
  let n := p + r + 1 + c
  let w := truncate R M n x
  have hleft : deconcatenation R M (extend c b x) p r =
      deconcatenation R M (b w) p r := by
    simp only [deconcatenation_apply]
    rw [extend_apply_eq_of_le c b hc x (p + r) n (by dsimp [n]; omega)]
  have hfinite := congrArg (fun z ↦ tensorInclusion z p r) (hb.deconcatenation_apply w)
  have htensor : LinearMap.lTensor (TensorWords R M) b ∘ₗ
      LinearMap.rTensor (TensorWords R M) (TensorWords.map (G.koszulTwist q)) =
      TensorProduct.map (TensorWords.map (G.koszulTwist q)) b := by
    simp only [LinearMap.lTensor_def, LinearMap.rTensor_def, ← TensorProduct.map_comp,
      LinearMap.id_comp, LinearMap.comp_id]
  have htensor_apply := LinearMap.congr_fun htensor (TensorWords.deconcatenation R M w)
  simp only [LinearMap.comp_apply] at htensor_apply
  rw [hleft]
  rw [map_add, LinearMap.rTensor_def, htensor_apply] at hfinite
  simp only [Pi.add_apply] at hfinite
  rw [← tensorMap_tensorInclusion c 0 b LinearMap.id hc (hasLengthBound_id 0),
    ← tensorMap_tensorInclusion 0 c (TensorWords.map (G.koszulTwist q)) b
      (hasLengthBound_map _) hc] at hfinite
  simp only [tensorInclusion_deconcatenation] at hfinite
  rw [tensorMap_deconcatenation_truncate c 0 b LinearMap.id x p r n (by dsimp [n]; omega),
    tensorMap_deconcatenation_truncate 0 c (TensorWords.map (G.koszulTwist q)) b
      x p r n (by dsimp [n]; omega)] at hfinite
  exact hfinite

/-- The counit of the finite-prefix extension of a signed coderivation vanishes,
even when the chosen cutoff is not a length bound. -/
theorem counit_extend_of_isGradedCoderivation (c : ℕ)
    (hb : TensorWords.IsGradedCoderivation G q b) (x : CompletedTensorWords R M) :
    counit R M (extend c b x) = 0 := by
  rw [counit_apply, extend_apply]
  simpa only [TensorWords.counit_apply, TensorWords.component_apply] using
    hb.counit_apply (truncate R M (0 + 1 + c) x)

end TauCeti.CompletedTensorWords
