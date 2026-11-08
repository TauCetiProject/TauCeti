/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Center
public import TauCeti.Algebra.Lie.Current.NormalOrder
public import TauCeti.Algebra.Lie.Killing.DualBasis

/-!
# Segal--Sugawara modes in the completed enveloping algebra

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ_L` is
nondegenerate, let `Φ` be an invariant symmetric form on `L`, and let `Û = lim_N U / I_N` be the
completed enveloping algebra of the residue central extension of `Φ` at the central value `a`
(`TauCeti.CurrentAlgebra.CompletedEnveloping`). For a basis `xᵢ` of `L` and the basis `yᵢ` dual to
it under `κ_L`, the **Segal--Sugawara modes** are

`Sₙ = ∑ᵢ :xᵢ yᵢ:_n ∈ Û`,

the modes of the normally ordered Casimir field `∑ᵢ :J^{xᵢ}(z) J^{yᵢ}(z):`
(`TauCeti.CurrentAlgebra.sugawaraMode`). They do not depend on the basis
(`TauCeti.CurrentAlgebra.sugawaraMode_eq_sum`).

The main result is the commutator of a current with these modes
(`TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul`): for the current
generator `z_k` of the mode `z ⊗ tᵏ`,

`[z_k, Sₙ] = k (z - 2 a w)_{n+k}`, where `κ_L(w, y) = Φ(z, y)` for all `y`.

It follows from the commutator of a current with a normally ordered mode
(`TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_normalOrderedMode_sub_mul`): the Leibniz terms
cancel because `∑ᵢ xᵢ ⊗ yᵢ` is invariant, the reordering terms give the adjoint Casimir operator
`∑ᵢ ⁅⁅z, xᵢ⁆, yᵢ⁆ = z` (`TauCeti.sum_lie_lie_killingDualBasis`), the central contractions give
`2 a w`, and the central constant vanishes because `∑ᵢ ⁅xᵢ, yᵢ⁆ = 0`. If `Φ = c κ_L` then `w = c z`
and `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`.

**The critical level.** When `2 a Φ = κ_L`, every `Sₙ` commutes with all currents, so it lies in the
center of `Û` (`TauCeti.CurrentAlgebra.sugawaraMode_mem_center`). For the affine level form
`κ = -Φ` at `a = 1` this is `κ = -½ κ_L`, the critical level `κ_c`.

No characteristic or algebraic-closure hypothesis is needed. In the normalisation of Frenkel, with
the invariant form `κ₀ = κ_L / (2 h^∨)` and `S(z) = ½ ∑ :J^a J_a:` for `κ₀`-dual bases, the
Segal--Sugawara modes are `h^∨ Sₙ`, and at the level `κ = k κ₀` the formula above becomes
`[z_m, h^∨ Sₙ] = (k + h^∨) m z_{n+m}`.

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraMode`: the Segal--Sugawara modes `Sₙ = ∑ᵢ :xᵢ yᵢ:_n`.

## Main results

* `TauCeti.CurrentAlgebra.sugawaraMode_eq_sum`: `Sₙ` may be computed in any basis.
* `TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul`: the commutator
  `[z_k, Sₙ] = k (z - 2 a w)_{n+k}`.
* `TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm`:
  for `Φ = c κ_L`, the commutator `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`.
* `TauCeti.CurrentAlgebra.sugawaraMode_mem_center`: at the critical level `2 a Φ = κ_L`, the
  Segal--Sugawara modes are central.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §3.1, for the Segal--Sugawara vector and
  its commutation relations with the currents, and Corollary 3.2.2, for the centrality of its
  Fourier coefficients at the critical level.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.5.10.
-/

public section

noncomputable section

open scoped TensorProduct
open LieAlgebra.ofTwoCocycle (envelopingι)

namespace TauCeti.CurrentAlgebra

section Sugawara

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

local notation "ιK[" x ", " m "]" =>
  toCompletedEnveloping Φ hΦ hΦs a
    (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x))

/-- The image of a mode is additive and homogeneous in the coefficient vector. -/
private theorem sum_smul_toCompletedEnveloping {ι : Type*} (s : Finset ι) (r : ι → K) (v : ι → L)
    (m : ℤ) : ∑ i ∈ s, r i • ιK[v i, m] = ιK[∑ i ∈ s, r i • v i, m] := by
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul]

variable [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- **The Segal--Sugawara modes** `Sₙ = ∑ᵢ :xᵢ yᵢ:_n` in `Û`, for a basis `xᵢ` of `L` and the basis
`yᵢ` dual to it under the Killing form: the modes of the normally ordered Casimir field
`∑ᵢ :J^{xᵢ}(z) J^{yᵢ}(z):`, without any normalising factor. The definition names a particular
basis, but the modes do not depend on it (`TauCeti.CurrentAlgebra.sugawaraMode_eq_sum`). -/
def sugawaraMode (n : ℤ) : CompletedEnveloping Φ hΦ hΦs a :=
  ∑ i, normalOrderedMode Φ hΦ hΦs a n (Module.finBasis K L i)
    (killingDualBasis (Module.finBasis K L) i)

variable {Φ hΦ hΦs a}

/-- **The Segal--Sugawara modes may be computed in any basis**: `Sₙ = ∑ᵢ :xᵢ yᵢ:_n` for every basis
`xᵢ` of `L` and its Killing-dual basis `yᵢ`. -/
theorem sugawaraMode_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L)
    (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n = ∑ i, normalOrderedMode Φ hΦ hΦs a n (b i) (killingDualBasis b i) :=
  (normalOrderedMode Φ hΦ hΦs a n).sum_apply_dualBasis_eq _ (Module.finBasis K L) b

/-- **The commutator of a current with the Segal--Sugawara modes.** For the current generator `z_k`
of the mode `z ⊗ tᵏ` and the vector `w` dual to `Φ(z, ·)` under the Killing form,
`[z_k, Sₙ] = k (z - 2 a w)_{n+k}`. -/
theorem toCompletedEnveloping_mul_sugawaraMode_sub_mul {z w : L}
    (hw : ∀ y, killingForm K L w y = Φ z y) (k n : ℤ) :
    ιK[z, k] * sugawaraMode Φ hΦ hΦs a n - sugawaraMode Φ hΦ hΦs a n * ιK[z, k] =
      (k : K) • ιK[z - (2 * a) • w, n + k] := by
  classical
  set b := Module.finBasis K L
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  rw [sugawaraMode, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [toCompletedEnveloping_mul_normalOrderedMode_sub_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_apply_lie_killingDualBasis_add_eq_zero, zero_add]
  -- The double brackets sum to `z`: the adjoint Casimir operator is the identity.
  have h₁ : ∑ i, (k : K) • ιK[⁅⁅z, b i⁆, killingDualBasis b i⁆, n + k] =
      (k : K) • ιK[z, n + k] := by
    rw [sum_smul_toCompletedEnveloping, ← Finset.smul_sum, sum_lie_lie_killingDualBasis,
      TensorProduct.tmul_smul, map_smul, map_smul]
  -- The contractions with `Φ z` are both the Killing-dual vector `w`.
  have h₂ : ∑ i, (k * a * Φ z (b i)) • ιK[killingDualBasis b i, n + k] =
      (k * a) • ιK[w, n + k] := by
    simp only [sum_smul_toCompletedEnveloping, ← hw, mul_smul, ← Finset.smul_sum]
    rw [LinearMap.BilinForm.sum_apply_smul_dualBasis hnd b w]
  have h₃ : ∑ i, (k * a * Φ z (killingDualBasis b i)) • ιK[b i, n + k] =
      (k * a) • ιK[w, n + k] := by
    simp only [sum_smul_toCompletedEnveloping, ← hw, mul_smul, ← Finset.smul_sum,
      LieModule.traceForm_comm K L L w]
    rw [LinearMap.BilinForm.sum_apply_dualBasis_smul hnd b w]
  -- The central terms vanish, since `∑ᵢ Φ(⁅z, xᵢ⁆, yᵢ) = Φ(z, ∑ᵢ ⁅xᵢ, yᵢ⁆) = 0`.
  have hc : ∑ i, Φ ⁅z, b i⁆ (killingDualBasis b i) = 0 := by
    have hi (i) : Φ ⁅z, b i⁆ (killingDualBasis b i) = Φ z ⁅b i, killingDualBasis b i⁆ := by
      rw [← lie_skew, map_neg, LinearMap.neg_apply, hΦ, neg_neg]
    simp only [hi]
    rw [← map_sum, sum_lie_killingDualBasis_eq_zero, map_zero]
  have h₄ : ∑ i, algebraMap K (CompletedEnveloping Φ hΦ hΦs a) (if n + k = 0 then
      ((k * (k - 1) / 2 : ℤ) : K) * a * Φ ⁅z, b i⁆ (killingDualBasis b i) else 0) = 0 := by
    rw [← map_sum]
    split_ifs
    · rw [← Finset.mul_sum, hc, mul_zero, map_zero]
    · simp
  rw [h₁, h₂, h₃, h₄, TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_sub, map_smul,
    map_sub, map_smul]
  module

/-- **The commutator of a current with the Segal--Sugawara modes, for a multiple of the Killing
form.** If `Φ = c κ_L`, then `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`. -/
theorem toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (z : L) (k n : ℤ) :
    ιK[z, k] * sugawaraMode Φ hΦ hΦs a n - sugawaraMode Φ hΦ hΦs a n * ιK[z, k] =
      ((k : K) * (1 - 2 * a * c)) • ιK[z, n + k] := by
  rw [toCompletedEnveloping_mul_sugawaraMode_sub_mul (w := c • z) (fun y ↦ by simp [h]),
    show z - (2 * a) • c • z = (1 - 2 * a * c) • z by module, TensorProduct.tmul_smul, map_smul,
    map_smul, smul_smul]

/-- **The Segal--Sugawara modes are central at the critical level.** If `2 a Φ = κ_L`, which for
the affine level form `κ = -Φ` at central value `1` is the critical level `κ = -½ κ_L`, then every
`Sₙ` lies in the center of `Û`. -/
theorem sugawaraMode_mem_center (h : (2 * a) • Φ = killingForm K L) (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n ∈ Subalgebra.center K (CompletedEnveloping Φ hΦ hΦs a) := by
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  refine mem_center_iff_forall_commute_single.2 fun k z ↦ ?_
  set w := ((killingForm K L).toDual hnd).symm (Φ z)
  have hw (y : L) : killingForm K L w y = Φ z y := LinearMap.BilinForm.apply_toDual_symm_apply ..
  have hz : (2 * a) • w = z := by
    refine sub_eq_zero.1 (hnd.1 _ fun y ↦ ?_)
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hw, ← h,
      LinearMap.smul_apply, LinearMap.smul_apply, sub_self]
  rw [Commute, SemiconjBy, ← sub_eq_zero, toCompletedEnveloping_mul_sugawaraMode_sub_mul hw, hz,
    sub_self, TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]

end Sugawara

end TauCeti.CurrentAlgebra
