/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Comass
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis

/-!
# Mass of the Kähler bivector

For an orthogonal almost complex structure on a finite-dimensional real inner product space,
the Kähler bivector has mass `dim V / 2`, whereas its Hilbert norm is `√(dim V / 2)`.
Here mass is the norm in the native dual of continuous alternating forms, through
`exteriorPower.formDualEquiv`; no new norm is installed on the exterior power.

The associated alternating form has comass at most one: it evaluates on `(u, v)` as
`⟪J u, v⟫`. It certifies the lower mass bound, and the orthonormal-basis expansion of the
Kähler bivector gives the matching upper bound. In an orthonormal four-frame this proves that
`e₀ ∧ e₁ + e₂ ∧ e₃` has mass `2` and Hilbert norm `√2`. Thus the dual-comass mass used for
vector-valued representations of currents cannot be replaced by the Hilbert norm.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1 (comass and its dual mass norm).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, §2.1
  (orthogonal complex structures and their associated forms).

The constructions are `AlmostComplexStructure.kahlerForm`, `TauCeti.alternatingFormEquiv`
and `exteriorPower.formDualEquiv` from the imported modules.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

variable {J : AlmostComplexStructure V} (hJ : ∀ u v, ⟪J u, J v⟫ = ⟪u, v⟫)
include hJ

/-- The alternating form associated to an orthogonal complex structure has comass at most one.
This also covers the zero-dimensional space, where the form vanishes. -/
theorem norm_alternatingFormEquiv_kahlerForm_le :
    ‖alternatingFormEquiv V 2 J.kahlerForm‖ ≤ 1 := by
  refine (alternatingFormEquiv V 2 J.kahlerForm).opNorm_le_bound zero_le_one fun v ↦ ?_
  have heval : alternatingFormEquiv V 2 J.kahlerForm v = ⟪J (v 0), v 1⟫ := by
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv, alternatingFormEquiv_apply, inner_kahlerForm_ιMulti hJ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [heval, Real.norm_eq_abs, Fin.prod_univ_two, one_mul]
  simpa only [norm_apply hJ] using abs_real_inner_le_norm (J (v 0)) (v 1)

/-- The dual-comass mass of the Kähler bivector is half the real dimension, including in
dimension zero. Its Hilbert norm, in contrast, is the square root of this number. -/
@[simp]
theorem norm_formDualEquiv_kahlerForm :
    ‖formDualEquiv ℝ V 2 J.kahlerForm‖ = finrank ℝ V / 2 := by
  apply le_antisymm
  · refine (formDualEquiv ℝ V 2 J.kahlerForm).opNorm_le_bound (by positivity) fun ω ↦ ?_
    have hterm (i : Fin (finrank ℝ V)) :
        ‖ω ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)]‖ ≤ ‖ω‖ := by
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        norm_apply hJ, OrthonormalBasis.norm_eq_one, mul_one] using
        ω.le_opNorm ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)]
    rw [kahlerForm_def, map_smul, map_sum]
    simp only [smul_apply, sum_apply,
      formDualEquiv_ιMulti_apply, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2⁻¹ : ℝ))]
    calc (2⁻¹ : ℝ) * ‖∑ i, ω ![stdOrthonormalBasis ℝ V i, J (stdOrthonormalBasis ℝ V i)]‖
        ≤ (2⁻¹ : ℝ) * ∑ i : Fin (finrank ℝ V), ‖ω‖ := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hterm i)
      _ = (finrank ℝ V : ℝ) / 2 * ‖ω‖ := by simp [div_eq_inv_mul, mul_assoc]
  · calc (finrank ℝ V : ℝ) / 2 = ⟪J.kahlerForm, J.kahlerForm⟫ :=
          (inner_kahlerForm_self hJ).symm
        _ ≤ ‖formDualEquiv ℝ V 2 J.kahlerForm‖ *
            ‖alternatingFormEquiv V 2 J.kahlerForm‖ :=
          inner_le_norm_formDualEquiv_mul _ _
        _ ≤ ‖formDualEquiv ℝ V 2 J.kahlerForm‖ :=
          mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg _)
            (norm_alternatingFormEquiv_kahlerForm_le hJ)

end TauCeti.AlmostComplexStructure

namespace OrthonormalBasis

/-- The sum of the oriented unit bivectors of two orthogonal planes has dual-comass mass `2`.
In particular this computes the mass of `e₀ ∧ e₁ + e₂ ∧ e₃` in Euclidean four-space. -/
theorem norm_formDualEquiv_ιMulti_add_ιMulti_finFour (e : OrthonormalBasis (Fin 4) ℝ V) :
    ‖formDualEquiv ℝ V 2 (ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3])‖ = 2 := by
  obtain ⟨J, h₀, h₂⟩ := exists_almostComplexStructure_finFour e
  rw [← J.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂,
    J.norm_formDualEquiv_kahlerForm (J.inner_apply_apply_of_orthonormalBasis h₀ h₂)]
  norm_num [Module.finrank_eq_card_basis e.toBasis]

/-- The same sum of orthogonal unit bivectors has Hilbert norm `√2`, not its mass `2`. -/
theorem norm_ιMulti_add_ιMulti_finFour (e : OrthonormalBasis (Fin 4) ℝ V) :
    ‖ιMulti ℝ 2 ![e 0, e 1] + ιMulti ℝ 2 ![e 2, e 3]‖ = √2 := by
  obtain ⟨J, h₀, h₂⟩ := exists_almostComplexStructure_finFour e
  rw [← J.kahlerForm_eq_ιMulti_add_ιMulti h₀ h₂, norm_eq_sqrt_real_inner,
    J.inner_kahlerForm_self (J.inner_apply_apply_of_orthonormalBasis h₀ h₂)]
  norm_num [Module.finrank_eq_card_basis e.toBasis]

end OrthonormalBasis
