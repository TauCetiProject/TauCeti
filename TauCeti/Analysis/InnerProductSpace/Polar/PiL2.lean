/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded

/-!
# Polar factors of coordinate blocks of Euclidean operators

Let `ι : 𝕜ᵏ → 𝕜ⁿ` be the zero extension onto the first `k` coordinates. For an operator `A` of
`𝕜ⁿ`, the block `ι† A ι` is the first diagonal block of `A` in the splitting
`𝕜ⁿ ≃ 𝕜ᵏ × 𝕜ⁿ⁻ᵏ` along `j < k` (`EuclideanSpace.sumComplEquivProd`), read on `𝕜ᵏ` through
`EuclideanSpace.finCastLEEquiv`. By naturality of polar factors under linear isometric
equivalences (`ContinuousLinearMap.polarFactor_conj`), the same holds for its polar factor.

## Main declarations

* `EuclideanSpace.polarFactor_adjoint_comp_comp_piLpExtendByZero`: the polar factor of `ι† A ι`
  is that of the first diagonal block of `A` in the splitting along `j < k`.
-/

public section

open LinearIsometry (piLpExtendByZero)

namespace EuclideanSpace

variable {𝕜 : Type*} [RCLike 𝕜] {n k : ℕ}

/-- The block `ι† A ι` of an operator `A` of `𝕜ⁿ`, for the zero extension `ι : 𝕜ᵏ → 𝕜ⁿ`, is the
first diagonal block of `A` in the splitting of `𝕜ⁿ` along `j < k`, read on `𝕜ᵏ`; so is its
polar factor. -/
theorem polarFactor_adjoint_comp_comp_piLpExtendByZero (hk : k ≤ n)
    (A : EuclideanSpace 𝕜 (Fin n) →L[𝕜] EuclideanSpace 𝕜 (Fin n)) :
    (ContinuousLinearMap.adjoint
        (piLpExtendByZero 2 𝕜 𝕜 (Fin.castLEEmb hk)).toContinuousLinearMap ∘L A ∘L
          (piLpExtendByZero 2 𝕜 𝕜 (Fin.castLEEmb hk)).toContinuousLinearMap).polarFactor =
      ((finCastLEEquiv 𝕜 hk).symm :
          EuclideanSpace 𝕜 {j : Fin n // j.val < k} →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘L
        (ContinuousLinearMap.fst 𝕜 _ _ ∘L
          ((sumComplEquivProd 𝕜 (fun j : Fin n ↦ j.val < k)).toContinuousLinearMap ∘L
            A ∘L (sumComplEquivProd 𝕜 (fun j : Fin n ↦ j.val < k)).symm.toContinuousLinearMap) ∘L
          ContinuousLinearMap.inl 𝕜 _ _).polarFactor ∘L
        ((finCastLEEquiv 𝕜 hk).symm.symm :
          EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 {j : Fin n // j.val < k}) := by
  rw [← ContinuousLinearMap.polarFactor_conj]
  congr 1
  ext1 w
  simp [← finCastLEEquiv_symm_fst_sumComplEquivProd]

end EuclideanSpace
