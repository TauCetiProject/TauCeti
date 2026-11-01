/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.RealModel
public import TauCeti.NumberTheory.IntegralLattice.EvenUnimodularGenus
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Eisenstein

/-!
# The theta series does not determine the lattice

The lattices `E₈ ⊕ E₈` (`TauCeti.IntegralLattice.e8PowLattice 2`) and `D₁₆⁺`
(`TauCeti.IntegralLattice.checkerboardPlusLattice 16`) are positive definite, even and unimodular
of rank `16`. Every even unimodular lattice of rank `16` has theta series `E₄²`
(`ZLattice.IsEven.thetaSeries_eq_E₄_sq`), so the real models of these two lattices have the same
theta series.

They are nevertheless not isometric: the roots of `E₈ ⊕ E₈` span it, while those of `D₁₆⁺` lie in
the checkerboard lattice `D₁₆` of index two
(`TauCeti.IntegralLattice.isEmpty_isometry_e8PowLattice_checkerboardPlusLattice`). A real linear
isometry carrying one real model onto the other would induce an isometry of the rational lattices
(`TauCeti.IntegralLattice.Isometry.ofRealModel`), so no such isometry exists. Together these say
that the theta series of a positive definite lattice does not determine its isometry class, even
among the even unimodular lattices of a given rank.

## Main results

* `TauCeti.IntegralLattice.thetaSeries_realModel_e8PowLattice_two`: `Θ_{E₈ ⊕ E₈} = E₄²`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardPlusLattice_sixteen`:
  `Θ_{D₁₆⁺} = E₄²`.
* `TauCeti.IntegralLattice.map_realModel_e8PowLattice_ne_realModel_checkerboardPlusLattice`: for
  `k ≥ 2`, no real linear isometry carries the real model of `E₈^k` onto that of `D_{8k}⁺`.
* `TauCeti.IntegralLattice.not_forall_exists_map_eq_of_thetaSeries_eq`: there are even unimodular
  full lattices with equal theta series that are not carried onto each other by any linear
  isometry of the ambient spaces.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter VII, §6.6.
* J. Milnor, *Eigenvalues of the Laplace operator on certain manifolds*, Proc. Nat. Acad. Sci.
  U.S.A. 51 (1964), 542.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 16, §1.
-/

public section

open ModularForm

namespace TauCeti.IntegralLattice

/-! ### The real models are even unimodular -/

private theorem isEven_realModel_e8PowLattice_two :
    ZLattice.IsEven ((e8PowLattice 2).realModel (isPosDef_e8PowLattice 2)) :=
  ((e8PowLattice 2).isEven_realModel_iff _).mpr (isEven_e8PowLattice 2)

private theorem isUnimodular_realModel_e8PowLattice_two :
    ZLattice.IsUnimodular ((e8PowLattice 2).realModel (isPosDef_e8PowLattice 2)) :=
  ((e8PowLattice 2).isUnimodular_realModel_iff _).mpr (isUnimodular_e8PowLattice 2)

private theorem isEven_realModel_checkerboardPlusLattice_sixteen :
    ZLattice.IsEven ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).realModel
      (isPosDef_checkerboardPlusLattice _ _)) :=
  ((checkerboardPlusLattice _ _).isEven_realModel_iff _).mpr (isEven_checkerboardPlusLattice _ _)

private theorem isUnimodular_realModel_checkerboardPlusLattice_sixteen :
    ZLattice.IsUnimodular ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).realModel
      (isPosDef_checkerboardPlusLattice _ _)) :=
  ((checkerboardPlusLattice _ _).isUnimodular_realModel_iff _).mpr
    (isUnimodular_checkerboardPlusLattice _ _)

/-! ### The theta series -/

/-- **The theta series of `E₈ ⊕ E₈` is `E₄²`.** -/
theorem thetaSeries_realModel_e8PowLattice_two :
    ZLattice.thetaSeries ((e8PowLattice 2).realModel (isPosDef_e8PowLattice 2)) = E₄ ^ 2 :=
  isEven_realModel_e8PowLattice_two.thetaSeries_eq_E₄_sq isUnimodular_realModel_e8PowLattice_two
    (by simp [RealModelSpace.finrank_eq, finrank_carrier])

/-- **The theta series of `D₁₆⁺` is `E₄²`.** -/
theorem thetaSeries_realModel_checkerboardPlusLattice_sixteen :
    ZLattice.thetaSeries ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).realModel
      (isPosDef_checkerboardPlusLattice _ _)) = E₄ ^ 2 :=
  isEven_realModel_checkerboardPlusLattice_sixteen.thetaSeries_eq_E₄_sq
    isUnimodular_realModel_checkerboardPlusLattice_sixteen
    (by simp [RealModelSpace.finrank_eq, finrank_carrier])

/-! ### Non-isometry -/

/-- **The real models of `E₈^k` and `D_{8k}⁺` are not isometric for `k ≥ 2`**: no real linear
isometry of the ambient spaces carries the real model of `E₈^k` onto that of `D_{8k}⁺`. -/
theorem map_realModel_e8PowLattice_ne_realModel_checkerboardPlusLattice {k : ℕ} (hk : 2 ≤ k)
    (f : (e8PowLattice k).RealModelSpace (isPosDef_e8PowLattice k) ≃ₗᵢ[ℝ]
      (checkerboardPlusLattice (8 * k) (dvd_mul_right 8 k)).RealModelSpace
        (isPosDef_checkerboardPlusLattice _ _)) :
    ((e8PowLattice k).realModel _).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap ≠
      (checkerboardPlusLattice (8 * k) (dvd_mul_right 8 k)).realModel _ :=
  fun hf ↦ (isEmpty_isometry_e8PowLattice_checkerboardPlusLattice hk).false
    (Isometry.ofRealModel f hf)

/-- **The theta series does not determine the lattice.** There are even unimodular full lattices
`L ⊆ E` and `M ⊆ F` with `Θ_L = Θ_M` such that no linear isometry `E ≃ F` carries `L` onto `M`:
the real models of `E₈ ⊕ E₈` and `D₁₆⁺`, whose theta series are both `E₄²`. -/
theorem not_forall_exists_map_eq_of_thetaSeries_eq :
    ¬ ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
      (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]
      [DiscreteTopology M] [IsZLattice ℝ M], ZLattice.IsEven L → ZLattice.IsUnimodular L →
      ZLattice.IsEven M → ZLattice.IsUnimodular M →
      ZLattice.thetaSeries L = ZLattice.thetaSeries M →
      ∃ f : E ≃ₗᵢ[ℝ] F, L.map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap = M := fun h ↦
  have ⟨f, hf⟩ := h _ _ _ _ isEven_realModel_e8PowLattice_two
    isUnimodular_realModel_e8PowLattice_two isEven_realModel_checkerboardPlusLattice_sixteen
    isUnimodular_realModel_checkerboardPlusLattice_sixteen
    (thetaSeries_realModel_e8PowLattice_two.trans
      thetaSeries_realModel_checkerboardPlusLattice_sixteen.symm)
  map_realModel_e8PowLattice_ne_realModel_checkerboardPlusLattice le_rfl f hf

end TauCeti.IntegralLattice
