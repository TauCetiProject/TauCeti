/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Comass
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear
import TauCeti.Geometry.Symplectic.MixedWedge

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

The same evaluation `ω(u, v) = ⟪J u, v⟫` shows that a linear map preserving `ω` does not change
the Kähler component `G(e₀, e₁) + G(e₂, e₃)` of a two-form `G` in a unitary four-frame when `G`
is pulled back along it
(`TauCeti.AlmostComplexStructure.compContinuousLinearMap_apply_add_apply_eq`).

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

/-- The alternating form associated to an orthogonal complex structure is the Kähler form
`ω(u, w) = ⟪J u, w⟫`. -/
theorem alternatingFormEquiv_kahlerForm_apply (v : Fin 2 → V) :
    alternatingFormEquiv V 2 J.kahlerForm v = ⟪J (v 0), v 1⟫ := by
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, alternatingFormEquiv_apply, inner_kahlerForm_ιMulti hJ]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The alternating form associated to an orthogonal complex structure has comass at most one.
This also covers the zero-dimensional space, where the form vanishes. -/
theorem norm_alternatingFormEquiv_kahlerForm_le :
    ‖alternatingFormEquiv V 2 J.kahlerForm‖ ≤ 1 := by
  refine (alternatingFormEquiv V 2 J.kahlerForm).opNorm_le_bound zero_le_one fun v ↦ ?_
  rw [alternatingFormEquiv_kahlerForm_apply hJ, Real.norm_eq_abs, Fin.prod_univ_two, one_mul]
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
        ≤ (2⁻¹ : ℝ) * ∑ _ : Fin (finrank ℝ V), ‖ω‖ := by
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

omit hJ in
/-- **The Kähler component in a symplectic frame.** If `S` preserves the Kähler form
`ω(u, v) = ⟪J u, v⟫` of the structure `J` of a unitary frame `e` of a four-dimensional space
(`J e₀ = e₁`, `J e₂ = e₃`), then a two-form `G` and its pullback `G ∘ S` have the same Kähler
component `G(e₀, e₁) + G(e₂, e₃)`
(`ContinuousAlternatingMap.apply_add_apply_eq_of_cross_eq_zero`). -/
theorem compContinuousLinearMap_apply_add_apply_eq (hV : finrank ℝ V = 4)
    {e : OrthonormalBasis (Fin 4) ℝ V} (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3)
    {S : V →L[ℝ] V} (hS : ∀ u v, ⟪J (S u), S v⟫ = ⟪J u, v⟫) (G : V [⋀^Fin 2]→L[ℝ] ℝ) :
    G.compContinuousLinearMap S ![e 0, e 1] + G.compContinuousLinearMap S ![e 2, e 3] =
      G ![e 0, e 1] + G ![e 2, e 3] := by
  have hω (u w : V) : alternatingFormEquiv V 2 J.kahlerForm ![u, w] = ⟪J u, w⟫ :=
    alternatingFormEquiv_kahlerForm_apply (inner_apply_apply_of_orthonormalBasis h₀ h₂₃) _
  have he (i j : Fin 4) : ⟪e i, e j⟫ = if i = j then 1 else 0 :=
    orthonormal_iff_ite.1 e.orthonormal i j
  have h₁ : J (e 1) = -e 0 := by rw [← h₀, J.apply_apply]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply_vecCons_two]
  refine ContinuousAlternatingMap.apply_add_apply_eq_of_cross_eq_zero
    (ω₀ := alternatingFormEquiv V 2 J.kahlerForm) hV ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ G <;>
    simp only [hω, hS, h₀, h₁, h₂₃, inner_neg_left, he] <;> norm_num

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
