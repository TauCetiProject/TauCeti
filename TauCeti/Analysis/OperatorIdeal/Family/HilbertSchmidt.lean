/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.Schatten
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.HilbertSchmidt

import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The Hilbert–Schmidt operator-ideal family

The Hilbert–Schmidt family assigns to a bounded operator `T` between real or complex Hilbert spaces
the square root `E_b(T)^(1/2)` of its Hilbert–Schmidt energy `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²`, computed in
any Hilbert basis `(bᵢ)` of the source. The four operator-ideal laws come directly from the geometry
of the energy, without approximation numbers: subadditivity is Minkowski's inequality for
unconditional sums in `ℝ≥0∞`, homogeneity is the scaling of the energy, domination of the operator
norm and the two-sided ideal inequality are the energy bounds `‖T‖ₑ² ≤ E_b(T)` and
`E(A T B) ≤ ‖A‖ₑ² E(T) ‖B‖ₑ²`. Adjoint invariance of the energy makes the diagonal family symmetric.

An operator lies in the ideal exactly when its energy is finite, and there the ideal norm is the
Hilbert–Schmidt norm `ContinuousLinearMap.hilbertSchmidtNorm`. The energy is the sum of the squared
approximation numbers, so the Hilbert–Schmidt family is the `p = 2` member of the Schatten scale;
in particular its normed carriers are complete.

## Main declarations

* `TauCeti.OperatorIdealFamily.hilbertSchmidt`: the Hilbert–Schmidt operator-ideal family.
* `TauCeti.OperatorIdealFamily.gauge_hilbertSchmidt`: its gauge is `E_b(T)^(1/2)` for every
  Hilbert basis `b` of the source.
* `TauCeti.OperatorIdealFamily.mem_finiteSubmodule_hilbertSchmidt_iff`: membership in the ideal is
  finiteness of the energy.
* `TauCeti.OperatorIdealFamily.toReal_gauge_hilbertSchmidt`: the ideal norm is the Hilbert–Schmidt
  norm.
* `TauCeti.OperatorIdealFamily.schatten_two`: the Schatten family at `p = 2` is the
  Hilbert–Schmidt family.
* `TauCeti.OperatorIdealFamily.hilbertSchmidt_isComplete`: its normed carriers are complete.
* `TauCeti.SymmetricOperatorIdealFamily.hilbertSchmidt`: the adjoint-invariant diagonal family.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open scoped ENNReal

universe u v w

namespace TauCeti

namespace OperatorIdealFamily

variable (𝕜 : Type u) [RCLike 𝕜]

/-- The **Hilbert–Schmidt operator-ideal family**. Its gauge is the square root
`E_b(T)^(1/2)` of the Hilbert–Schmidt energy, computed in a Hilbert basis `b` of the source chosen
once and for all; by `gauge_hilbertSchmidt` every Hilbert basis gives the same value. -/
noncomputable def hilbertSchmidt : OperatorIdealFamily.{u, v, w} 𝕜 where
  gauge T := T.hilbertSchmidtEnergy (exists_hilbertBasis 𝕜 _).choose_spec.choose ^ (1 / 2 : ℝ)
  gauge_add_le S T := S.rpow_hilbertSchmidtEnergy_add_le T _
  gauge_smul c T := by
    rw [ContinuousLinearMap.hilbertSchmidtEnergy_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.sq_rpow_one_half]
  enorm_le_gauge T := by
    rw [← ENNReal.sq_rpow_one_half ‖T‖ₑ]
    gcongr
    exact T.enorm_sq_le_hilbertSchmidtEnergy _
  gauge_comp_le L A R := by
    grw [ContinuousLinearMap.hilbertSchmidtEnergy_comp_comp_le L A R _
      (exists_hilbertBasis 𝕜 _).choose_spec.choose]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.sq_rpow_one_half, ENNReal.sq_rpow_one_half]

variable {𝕜}
variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The Hilbert–Schmidt gauge is the square root of the Hilbert–Schmidt energy, computed in any
Hilbert basis of the source. -/
theorem gauge_hilbertSchmidt {ι : Type*} (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (hilbertSchmidt.{u, v, w} 𝕜).gauge T = T.hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) :=
  congrArg (· ^ (1 / 2 : ℝ)) (T.hilbertSchmidtEnergy_indep _ b)

/-- An operator belongs to the Hilbert–Schmidt ideal exactly when its Hilbert–Schmidt energy is
finite, in any Hilbert basis of the source. -/
theorem mem_finiteSubmodule_hilbertSchmidt_iff {ι : Type*} (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) :
    T ∈ ((hilbertSchmidt.{u, v, w} 𝕜).operatorGauge E F).finiteSubmodule ↔
      T.hilbertSchmidtEnergy b ≠ ∞ := by
  rw [OperatorGauge.mem_finiteSubmodule, operatorGauge_apply, gauge_hilbertSchmidt T b,
    lt_top_iff_ne_top, ne_eq, ENNReal.rpow_eq_top_iff_of_pos (by norm_num)]

/-- The real value of the Hilbert–Schmidt gauge is the Hilbert–Schmidt norm. On the ideal this is
the norm of the carrier. -/
@[simp]
theorem toReal_gauge_hilbertSchmidt (T : E →L[𝕜] F) :
    ((hilbertSchmidt.{u, v, w} 𝕜).gauge T).toReal = T.hilbertSchmidtNorm := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [gauge_hilbertSchmidt T b, T.hilbertSchmidtNorm_eq_toReal_rpow b]

/-- **The Hilbert–Schmidt endpoint of the Schatten scale.** The Schatten family at `p = 2` is the
Hilbert–Schmidt family: the sum of the squared approximation numbers is the Hilbert–Schmidt
energy. -/
theorem schatten_two : schatten.{u, v, w} 𝕜 2 one_le_two = hilbertSchmidt 𝕜 := by
  ext E F _ _ _ _ _ _ T
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  simp_rw [gauge_schatten, gauge_hilbertSchmidt T b, ENNReal.rpow_two,
    T.tsum_singularValue_sq_eq_hilbertSchmidtEnergy b]

/-- The Hilbert–Schmidt operator-ideal family has complete normed carriers. -/
instance hilbertSchmidt_isComplete : (hilbertSchmidt.{u, v, w} 𝕜).IsComplete := by
  rw [← schatten_two]
  infer_instance

end OperatorIdealFamily

namespace SymmetricOperatorIdealFamily

/-- The adjoint-invariant diagonal-universe Hilbert–Schmidt family. -/
noncomputable def hilbertSchmidt (𝕜 : Type u) [RCLike 𝕜] :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  toOperatorIdealFamily := OperatorIdealFamily.hilbertSchmidt.{u, v, v} 𝕜
  gauge_adjoint {E F} _ _ _ _ _ _ T := by
    obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
    obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
    rw [OperatorIdealFamily.gauge_hilbertSchmidt _ c, OperatorIdealFamily.gauge_hilbertSchmidt T b,
      T.hilbertSchmidtEnergy_adjoint b c]

/-- The underlying rectangular family of the symmetric Hilbert–Schmidt family. -/
@[simp]
theorem hilbertSchmidt_toOperatorIdealFamily (𝕜 : Type u) [RCLike 𝕜] :
    (hilbertSchmidt.{u, v} 𝕜).toOperatorIdealFamily =
      OperatorIdealFamily.hilbertSchmidt.{u, v, v} 𝕜 :=
  (rfl)

/-- The symmetric Schatten family at `p = 2` is the symmetric Hilbert–Schmidt family. -/
theorem schatten_two (𝕜 : Type u) [RCLike 𝕜] :
    schatten.{u, v} 𝕜 2 one_le_two = hilbertSchmidt 𝕜 := by
  ext E F _ _ _ _ _ _ T
  have h := congrArg (fun Φ : OperatorIdealFamily.{u, v, v} 𝕜 ↦ Φ.gauge T)
    (OperatorIdealFamily.schatten_two (𝕜 := 𝕜))
  rwa [← schatten_toOperatorIdealFamily, ← hilbertSchmidt_toOperatorIdealFamily] at h

end SymmetricOperatorIdealFamily

end TauCeti
