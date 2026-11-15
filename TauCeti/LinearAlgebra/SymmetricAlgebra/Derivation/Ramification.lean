/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Jacobian
public import TauCeti.LinearAlgebra.SymmetricAlgebra.DividedDifference
public import TauCeti.RingTheory.Invariant.SemiInvariant
import TauCeti.LinearAlgebra.Determinant.RankOne

/-!
# Hyperplane factors in Jacobians of invariant polynomials

Let `σ` be the identity modulo a line `K ∙ ℓ`, with determinant a primitive `e`-th root
of unity. The Jacobian of polynomials fixed by `σ` is divisible by `ℓ ^ (e - 1)`.

Indeed `σ` acts on `ℓ` by its determinant, is the identity modulo `(ℓ)` on the entire
symmetric algebra, and acts on the Jacobian by the inverse determinant character.
The vanishing-order argument for semi-invariants then gives the full power, including
when `e > 2`. Neither a choice of complementary coordinates nor a polynomial
presentation of the invariant algebra is required.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), Chapter 3.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

namespace SymmetricAlgebra

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- If `σ` is the identity modulo `K ∙ ℓ` and its determinant is a primitive `e`-th
root of unity, then `ℓ ^ (e - 1)` divides the Jacobian of any family fixed by `σ`. -/
theorem ι_pow_sub_one_dvd_jacobian (b : Module.Basis n K M) {σ : M →ₗ[K] M}
    {ℓ : M} (hℓ : ℓ ≠ 0) (hσ : ∀ m, m - σ m ∈ K ∙ ℓ)
    {e : ℕ} (he : 0 < e) (hζ : IsPrimitiveRoot (LinearMap.det σ) e)
    {f : n → SymmetricAlgebra K M} (hf : ∀ i, map K σ (f i) = f i) :
    ι K M ℓ ^ (e - 1) ∣ jacobian b f := by
  apply (map K σ).pow_sub_one_dvd_of_smul_apply_eq
    (isLeftRegular_ι hℓ) he hζ (ι_dvd_sub_map hσ)
  · rw [map_apply_ι, σ.apply_eq_det_smul_of_sub_mem_span hℓ hσ, map_smul]
  · simpa only [Algebra.smul_def] using algebraMap_det_mul_map_jacobian b hf

end SymmetricAlgebra
