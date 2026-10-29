/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Bound
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction

/-!
# Local Tamagawa numbers

The minimal-equation index is defined for every Weierstrass equation. For an elliptic curve,
it is the local Tamagawa number: it is independent of the chosen minimal equation, and hence
of the Weierstrass presentation of the curve. Over a Henselian discrete valuation ring with
perfect residue field it is positive. Over a nonarchimedean local field it agrees with the local
index computed by Tate's algorithm.

The definition uses `WeierstrassCurve.minimal` and
`WeierstrassCurve.Affine.nonsingularReduction`; `tamagawaNumber_eq_index_of_isMinimal_smul`
is the interface for computations on any minimal equation. As with `AddSubgroup.index`, the value
is zero if the index is infinite; `tamagawaNumber_pos` excludes that case under the Henselian and
perfect-residue-field hypotheses. These numbers are the finite-place factors in the arithmetic
Birch–Swinnerton-Dyer quotient. The algorithmic comparison reuses
`WeierstrassCurve.Affine.index_nonsingularReduction_eq_tateLocalIndex`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.1.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, IV.9.
-/

public section

namespace WeierstrassCurve

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
  (E : WeierstrassCurve F) (v : Valuation F Γ₀)
  [IsDiscreteValuationRing v.valuationSubring]

open scoped Classical in
/-- The index of nonsingular reduction on a chosen minimal equation. For elliptic curves this
is the local Tamagawa number. -/
noncomputable def tamagawaNumber (E : WeierstrassCurve F)
    (v : Valuation F Γ₀) [IsDiscreteValuationRing v.valuationSubring] : ℕ :=
  ((E.minimal v.valuationSubring).toAffine.nonsingularReduction v).index

open scoped Classical in
/-- The chosen minimal equation computes the local Tamagawa number. -/
theorem tamagawaNumber_def : E.tamagawaNumber v =
    ((E.minimal v.valuationSubring).toAffine.nonsingularReduction v).index := by
  classical
  rfl

variable [E.IsElliptic]

/-- Every isomorphic minimal equation computes the same local Tamagawa number.

The equality decision is a parameter because `nonsingularReduction` on the right must retain the
caller's chosen point-group operations. The index agrees with the canonical decision used in the
definition, by uniqueness of equality decisions. -/
theorem tamagawaNumber_eq_index_of_isMinimal_smul [d : DecidableEq F] {W : WeierstrassCurve F}
    [IsMinimal v.valuationSubring W] (C : VariableChange F) (hC : C • E = W) :
    E.tamagawaNumber v = (W.toAffine.nonsingularReduction v).index := by
  classical
  cases Subsingleton.elim d (Classical.decEq F)
  obtain ⟨D, hD⟩ := exists_smul_minimal_eq_of_smul_eq v.valuationSubring C hC
  have : (E.minimal v.valuationSubring).IsElliptic := by
    obtain ⟨B, hB⟩ := exists_smul_eq_minimal v.valuationSubring E
    rw [← hB]
    infer_instance
  obtain ⟨D₀, rfl, -⟩ :=
    VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul
      v.valuationSubring D hD
  clear hC C
  subst W
  rw [tamagawaNumber_def]
  exact (Affine.index_nonsingularReduction_baseChange_smul v
    (W := E.minimal v.valuationSubring) D₀).symm

/-- On a minimal equation the Tamagawa number is the index of nonsingular reduction. -/
theorem tamagawaNumber_eq_index [DecidableEq F] [IsMinimal v.valuationSubring E] :
    E.tamagawaNumber v = (E.toAffine.nonsingularReduction v).index :=
  tamagawaNumber_eq_index_of_isMinimal_smul E v 1 (one_smul _ _)

/-- The local Tamagawa number is invariant under a change of Weierstrass variables. -/
@[simp]
theorem tamagawaNumber_smul (C : VariableChange F) :
    (C • E).tamagawaNumber v = E.tamagawaNumber v := by
  classical
  obtain ⟨D, hD⟩ := exists_smul_eq_minimal v.valuationSubring (C • E)
  exact (tamagawaNumber_def (C • E) v).trans
    (tamagawaNumber_eq_index_of_isMinimal_smul E v (D * C) (by rw [mul_smul, hD])).symm

omit [E.IsElliptic] in
/-- Good reduction contributes a factor of one. -/
@[simp]
theorem tamagawaNumber_eq_one_of_hasGoodReduction [E.HasGoodReduction v.valuationSubring] :
    E.tamagawaNumber v = 1 := by
  classical
  have : E.IsElliptic := HasGoodReduction.isElliptic v.valuationSubring inferInstance
  rw [tamagawaNumber_eq_index]
  have hΔ := (hasGoodReduction_iff_isUnit_integralModel_Δ v.valuationSubring E).1
    (inferInstance : E.HasGoodReduction v.valuationSubring)
  rw [Affine.nonsingularReduction_eq_top_of_Δ_notMem v fun h ↦
    (IsLocalRing.notMem_maximalIdeal.mpr hΔ)
      (Ideal.pow_le_self (by norm_num : 2 ≠ 0) h), AddSubgroup.index_top]

/-- Over a Henselian DVR with perfect residue field the Tamagawa number is positive. -/
theorem tamagawaNumber_pos [HenselianLocalRing v.valuationSubring]
    [PerfectField (IsLocalRing.ResidueField v.valuationSubring)] : 0 < E.tamagawaNumber v := by
  classical
  rw [tamagawaNumber_def]
  have : (E.minimal v.valuationSubring).IsElliptic := by
    obtain ⟨B, hB⟩ := exists_smul_eq_minimal v.valuationSubring E
    rw [← hB]
    infer_instance
  exact AddSubgroup.index_pos

/-- Tate's algorithm on any minimal equation computes the local Tamagawa number. -/
theorem tamagawaNumber_eq_tateLocalIndex [HenselianLocalRing v.valuationSubring]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [IsMinimal v.valuationSubring E]
    {ϖ : v.valuationSubring}
    (hϖ : IsLocalRing.maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    {s : TauCeti.ReductionSymbol}
    (h : (integralModel v.valuationSubring E).IsTateTerminal ϖ s) :
    E.tamagawaNumber v = (integralModel v.valuationSubring E).tateLocalIndex ϖ s := by
  classical
  rw [tamagawaNumber_eq_index]
  exact Affine.index_nonsingularReduction_eq_tateLocalIndex v hϖ h

end WeierstrassCurve

end
