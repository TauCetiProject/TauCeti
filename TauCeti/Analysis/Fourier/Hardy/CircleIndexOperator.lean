/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Hardy.Index

/-!
# The Atiyah–Singer circle Fourier operator

On the unit additive circle with normalized Haar measure, let `P` be orthogonal projection onto
the nonnegative Fourier modes and let `M_z` be multiplication by the first character
`z(t) = exp(2π i t)`. The operator `circleFourierIndexOperator` is `M_z ∘ P + (I - P)` on the
whole complex `L²` space. It acts by the forward shift on Hardy space and by the identity on its
orthogonal complement. Its kernel is zero and its range consists of the functions with vanishing
zeroth Fourier coefficient. This coefficient identifies the quotient by the range with `ℂ`, so the
operator has Fredholm index `-1`.

Atiyah and Singer define the operator and give its Fourier-mode action on p. 525 of §8, and
compute its index on p. 526. Here the coordinate change is `x = 2πt`.
[The Index of Elliptic Operators: I](https://doi.org/10.2307/1970715)

The Fourier coefficient and index arguments are adapted from `CircleFourierOperator.lean` and
`CircleFourierIndex.lean` in the Lean-Atiyah-Singer formalization by Alpha Squared Labs and Codex.
[Lean-Atiyah-Singer](https://github.com/alpha-squared-labs/Lean-Atiyah-Singer)
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TauCeti

local notation "L²" => Lp ℂ 2 (AddCircle.haarAddCircle (T := 1))

/-- The circle Fourier operator shifts the nonnegative modes and fixes the negative modes. -/
def circleFourierIndexOperator : L² →L[ℂ] L² :=
  (Lp.multiplicationOperator (E := ℂ) (fourierLp (T := 1) ∞ 1) ∘L
    hardySubmodule.starProjection) +
  (ContinuousLinearMap.id ℂ _ - hardySubmodule.starProjection)

/-- Apply the circle Fourier operator by multiplying the Hardy projection by the first character
and adding the orthogonal component. -/
theorem circleFourierIndexOperator_apply (f : L²) :
    circleFourierIndexOperator f =
      fourierLp (T := 1) ∞ 1 • hardySubmodule.starProjection f +
        (f - hardySubmodule.starProjection f) := by
  simp only [circleFourierIndexOperator, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, Lp.multiplicationOperator_apply]

/-- On Hardy space, the circle Fourier operator is the forward Toeplitz shift. -/
theorem circleFourierIndexOperator_apply_hardy (f : HardySpace) :
    circleFourierIndexOperator (f : L²) =
      (toeplitz (fourierLp (T := 1) ∞ 1) f : L²) := by
  rw [circleFourierIndexOperator_apply, Submodule.starProjection_eq_self_iff.mpr f.property,
    sub_self, add_zero, coe_toeplitz_fourierLp_one_apply]

/-- The circle Fourier operator fixes the orthogonal complement of Hardy space. -/
theorem circleFourierIndexOperator_apply_of_mem_orthogonal {f : L²}
    (hf : f ∈ hardySubmoduleᗮ) : circleFourierIndexOperator f = f := by
  rw [circleFourierIndexOperator_apply, hardySubmodule.starProjection_apply_eq_zero_iff.mpr hf,
    ← Lp.multiplicationOperator_apply, map_zero, sub_zero, zero_add]

/-- On each Fourier mode, the circle Fourier operator shifts its frequency up by one if it is
nonnegative and leaves it fixed if it is negative. -/
theorem circleFourierIndexOperator_fourierLp (n : ℤ) :
    circleFourierIndexOperator (fourierLp (T := 1) 2 n) =
      if 0 ≤ n then fourierLp (T := 1) 2 (n + 1) else fourierLp (T := 1) 2 n := by
  split_ifs with hn
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [← coe_fourierBasis, ← coe_hardyBasis, circleFourierIndexOperator_apply_hardy,
      toeplitz_fourierLp_one_hardyBasis, coe_hardyBasis, coe_fourierBasis, Nat.cast_add,
      Nat.cast_one]
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -n - 1)
    have hfreq : n = -(k : ℤ) - 1 := by omega
    rw [← coe_fourierBasis, hfreq]
    exact circleFourierIndexOperator_apply_of_mem_orthogonal
      (fourierBasis_mem_hardySubmodule_orthogonal k)

/-- On arbitrary `L²` inputs, the operator retains negative Fourier coefficients and shifts
nonnegative coefficients up by one, leaving the zeroth output coefficient zero. -/
@[simp]
theorem fourierCoeff_circleFourierIndexOperator (f : L²) (n : ℤ) :
    fourierCoeff (circleFourierIndexOperator f) n =
      if n < 0 then fourierCoeff f n else if n = 0 then 0 else fourierCoeff f (n - 1) := by
  rw [circleFourierIndexOperator_apply, ← fourierBasis_repr]
  simp only [map_add, map_sub, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply,
    fourierBasis_repr, fourierCoeff_fourierLp_smul, fourierCoeff_hardySubmodule_starProjection]
  split_ifs <;> first | omega | simp

/-- The circle Fourier operator is injective, since every input coefficient can be recovered from
an output coefficient. -/
theorem ker_circleFourierIndexOperator : circleFourierIndexOperator.ker = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro f g hfg
  simp only [ContinuousLinearMap.coe_coe] at hfg
  apply (fourierBasis (T := 1)).repr.injective
  apply lp.ext
  funext n
  simp only [fourierBasis_repr]
  have hcoeff (k : ℤ) := congrArg (fun u : L² ↦ fourierCoeff u k) hfg
  by_cases hn : n < 0
  · simpa [hn] using hcoeff n
  · have hpos : 0 < n + 1 := by omega
    simpa [not_lt.mpr hpos.le, hpos.ne'] using hcoeff (n + 1)

/-- A function belongs to the range of the circle Fourier operator exactly when its zeroth
Fourier coefficient vanishes. -/
theorem mem_range_circleFourierIndexOperator {g : L²} :
    g ∈ circleFourierIndexOperator.range ↔ fourierCoeff g 0 = 0 := by
  rw [LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe]
  constructor
  · rintro ⟨f, rfl⟩
    simp
  · intro hg
    have hproj : hardySubmodule.orthogonalProjectionOnto g ∈
        LinearMap.range (toeplitz (fourierLp (T := 1) ∞ 1) : HardySpace →ₗ[ℂ] HardySpace) := by
      rw [range_toeplitz_fourierLp_one, Submodule.mem_orthogonal_singleton_iff_inner_right,
        ← HilbertBasis.repr_apply_apply, hardyBasis_repr_orthogonalProjectionOnto, Nat.cast_zero]
      exact hg
    obtain ⟨h, hh⟩ := LinearMap.mem_range.mp hproj
    simp only [ContinuousLinearMap.coe_coe] at hh
    refine ⟨(h : L²) + (g - hardySubmodule.starProjection g), ?_⟩
    rw [map_add, circleFourierIndexOperator_apply_hardy,
      circleFourierIndexOperator_apply_of_mem_orthogonal
        (hardySubmodule.sub_starProjection_mem_orthogonal g), hh,
      Submodule.coe_orthogonalProjectionOnto_apply]
    abel

/-- The range of the circle Fourier operator is the kernel of the zeroth Fourier coefficient
functional, the inner product with the constant mode. -/
theorem range_circleFourierIndexOperator :
    circleFourierIndexOperator.range = (innerSL ℂ (fourierBasis (T := 1) (0 : ℤ))).ker := by
  ext g
  rw [mem_range_circleFourierIndexOperator, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    innerSL_fourierBasis_apply]

/-- The cokernel of the circle Fourier operator is linearly equivalent to `ℂ` via the zeroth
Fourier coefficient. -/
def circleFourierIndexOperatorCokernelEquiv : (L² ⧸ circleFourierIndexOperator.range) ≃ₗ[ℂ] ℂ :=
  (Submodule.quotEquivOfEq _ _ range_circleFourierIndexOperator).trans
    ((innerSL ℂ (fourierBasis (T := 1) (0 : ℤ))).toLinearMap.quotKerEquivOfSurjective fun c ↦
      ⟨c • fourierBasis (T := 1) (0 : ℤ), by
        rw [ContinuousLinearMap.coe_coe, map_smul, innerSL_apply_apply,
          inner_self_eq_one_of_norm_eq_one ((fourierBasis (T := 1)).orthonormal.norm_eq_one 0)]
        simp [smul_eq_mul]⟩)

/-- The circle Fourier operator's cokernel equivalence sends a class to its representative's
zeroth Fourier coefficient. -/
@[simp]
theorem circleFourierIndexOperatorCokernelEquiv_mk (f : L²) :
    circleFourierIndexOperatorCokernelEquiv (Submodule.Quotient.mk f) = fourierCoeff f 0 := by
  rw [circleFourierIndexOperatorCokernelEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    ← innerSL_fourierBasis_apply]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ f

/-- The class of the constant Fourier mode corresponds to `1` in the cokernel equivalence. -/
@[simp high]
theorem circleFourierIndexOperatorCokernelEquiv_mk_fourierLp_zero :
    circleFourierIndexOperatorCokernelEquiv
      (Submodule.Quotient.mk (fourierLp (T := 1) 2 0)) = 1 := by
  rw [circleFourierIndexOperatorCokernelEquiv_mk, fourierCoeff_fourierLp]
  simp

/-- The inverse cokernel equivalence represents `c` by the constant function with value `c`. -/
@[simp]
theorem circleFourierIndexOperatorCokernelEquiv_symm_apply (c : ℂ) :
    circleFourierIndexOperatorCokernelEquiv.symm c =
      Submodule.Quotient.mk (c • fourierLp (T := 1) 2 (0 : ℤ)) := by
  apply circleFourierIndexOperatorCokernelEquiv.injective
  rw [LinearEquiv.apply_symm_apply, Submodule.Quotient.mk_smul, map_smul,
    circleFourierIndexOperatorCokernelEquiv_mk_fourierLp_zero]
  simp [smul_eq_mul]

/-- The circle Fourier operator is Fredholm on the whole circle `L²` space. -/
theorem isFredholm_circleFourierIndexOperator : circleFourierIndexOperator.IsFredholm := by
  apply (isFredholm_iff_finite_ker_coker circleFourierIndexOperator).mpr
  refine ⟨?_, circleFourierIndexOperatorCokernelEquiv.symm.finiteDimensional⟩
  rw [ker_circleFourierIndexOperator]
  infer_instance

/-- The circle Fourier operator has Fredholm index `-1`, with zero kernel and one-dimensional
cokernel. -/
theorem index_circleFourierIndexOperator : circleFourierIndexOperator.index = -1 := by
  rw [ContinuousLinearMap.index_of_injective _ (LinearMap.ker_eq_bot.mp
    ker_circleFourierIndexOperator), circleFourierIndexOperatorCokernelEquiv.finrank_eq]
  simp

end TauCeti
