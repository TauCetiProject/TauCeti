/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Cohomology
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Basic

/-!
# The Tate module from local cohomology

For a finite Galois extension of `p`-adic fields, local reciprocity gives a degree-two class of
the completed multiplicative group whose restrictions generate cohomology on every subgroup.
Together with the vanishing of degree-one cohomology and the orders on `p`-subgroups, this class
produces the Tate module used in the integral decomposition of the completed multiplicative
group.

## References

* J. Neukirch, A. Schmidt, and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  III (3.1.5), (3.6.4), and V (5.6.5).
-/

public section

namespace TauCeti

open ContCohomology

variable (p : ℕ) [Fact p.Prime] (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [CharZero K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]
  [Algebra ℚ_[p] K] [Algebra ℚ_[p] L] [IsScalarTower ℚ_[p] K L]
  [Module.Finite ℚ_[p] L] [ValuativeExtension ℚ_[p] L]

/-- **Existence of the Tate module of a finite Galois layer.** The compatible degree-two class of
`A(L)` from local reciprocity satisfies Tate's cohomological criterion: its restrictions generate
`H²` on every subgroup, `H¹` vanishes there, and on `p`-subgroups the order of `H²` is the order of
the subgroup. The resulting splitting module is the extension of the augmentation ideal by
`A(L)` used in the integral decomposition. -/
theorem nonempty_layerTateModule : Nonempty (LayerTateModule p L K) := by
  obtain ⟨u, hu⟩ :=
    exists_zmultiples_eq_top_restriction_groupCohomology_two_padicCompletionUnits p K L
  exact LayerTateModule.nonempty_of_tateHypotheses u
    (fun S _ ↦ isZero_groupCohomology_one_res_padicCompletionUnits p K L S)
    (fun S _ x ↦ by
      have hx := (hu S).ge (AddSubgroup.mem_top x)
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      exact ⟨(n : ℤ_[p]), by simpa only [Int.cast_smul_eq_zsmul] using hn⟩)
    (fun S hS ↦ natCard_groupCohomology_two_res_padicCompletionUnits p K L S hS)

end TauCeti
