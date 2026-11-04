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

Every even unimodular lattice of rank `16` has theta series `E₄²`
(`ZLattice.IsEven.thetaSeries_eq_E₄_sq`). Transferred to the real model of a positive definite
rational lattice, this applies to `E₈ ⊕ E₈` (`TauCeti.IntegralLattice.e8PowLattice 2`) and `D₁₆⁺`
(`TauCeti.IntegralLattice.checkerboardPlusLattice (8 * 2) _`), which are even and unimodular of rank
`16`, so their real models have the same theta series. The index of `D₁₆⁺` is written `8 * 2`
rather than `16` on purpose: this is the form in which
`TauCeti.IntegralLattice.isEmpty_isometry_e8PowLattice_checkerboardPlusLattice` states the
non-isometry at `k = 2`, so the two halves below are about the same term.

The two lattices are nevertheless not isometric: the roots of `E₈ ⊕ E₈` span it, while those of
`D₁₆⁺` lie in the checkerboard lattice `D₁₆` of index two. A real linear isometry carrying one real
model onto the other would induce an isometry of the rational lattices
(`TauCeti.IntegralLattice.Isometry.ofRealModel`), so no such isometry exists. Together these say
that the theta series of a positive definite lattice does not determine its isometry class, even
among the even unimodular lattices of a given rank.

## Main results

* `TauCeti.IntegralLattice.thetaSeries_realModel_eq_E₄_sq`: the real model of an even unimodular
  positive definite rational lattice of rank `16` has theta series `E₄²`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_e8PowLattice_two`: `Θ_{E₈ ⊕ E₈} = E₄²`.
* `TauCeti.IntegralLattice.thetaSeries_realModel_checkerboardPlusLattice_sixteen`:
  `Θ_{D₁₆⁺} = E₄²`.
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

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-! ### The theta series -/

/-- **The theta series of an even unimodular lattice of rank `16` is `E₄²`**, for the real model of
a positive definite rational lattice. -/
theorem thetaSeries_realModel_eq_E₄_sq {M : IntegralLattice V} (hM : M.IsPosDef)
    (heM : M.IsEven) (huM : M.IsUnimodular) (hV : Module.finrank ℚ V = 16) :
    ZLattice.thetaSeries (M.realModel hM) = E₄ ^ 2 :=
  ((M.isEven_realModel_iff hM).mpr heM).thetaSeries_eq_E₄_sq
    ((M.isUnimodular_realModel_iff hM).mpr huM)
    (by rw [RealModelSpace.finrank_eq, finrank_carrier, hV])

/-- **The theta series of `E₈ ⊕ E₈` is `E₄²`.** -/
theorem thetaSeries_realModel_e8PowLattice_two :
    ZLattice.thetaSeries ((e8PowLattice 2).realModel (isPosDef_e8PowLattice 2)) = E₄ ^ 2 :=
  thetaSeries_realModel_eq_E₄_sq _ (isEven_e8PowLattice 2) (isUnimodular_e8PowLattice 2) (by simp)

/-- **The theta series of `D₁₆⁺` is `E₄²`.** -/
theorem thetaSeries_realModel_checkerboardPlusLattice_sixteen :
    ZLattice.thetaSeries ((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).realModel
      (isPosDef_checkerboardPlusLattice _ _)) = E₄ ^ 2 :=
  thetaSeries_realModel_eq_E₄_sq _ (isEven_checkerboardPlusLattice _ _)
    (isUnimodular_checkerboardPlusLattice _ _) (by simp)

/-! ### Non-isometry -/

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
  have ⟨f, hf⟩ := h _ _ _ _
    (((e8PowLattice 2).isEven_realModel_iff _).mpr (isEven_e8PowLattice 2))
    (((e8PowLattice 2).isUnimodular_realModel_iff _).mpr (isUnimodular_e8PowLattice 2))
    (((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).isEven_realModel_iff
      (isPosDef_checkerboardPlusLattice _ _)).mpr (isEven_checkerboardPlusLattice _ _))
    (((checkerboardPlusLattice (8 * 2) (dvd_mul_right 8 2)).isUnimodular_realModel_iff
      (isPosDef_checkerboardPlusLattice _ _)).mpr (isUnimodular_checkerboardPlusLattice _ _))
    (thetaSeries_realModel_e8PowLattice_two.trans
      thetaSeries_realModel_checkerboardPlusLattice_sixteen.symm)
  map_realModel_ne_realModel (isEmpty_isometry_e8PowLattice_checkerboardPlusLattice le_rfl) f hf

end TauCeti.IntegralLattice
