/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Prod
public import TauCeti.Geometry.Symplectic.Manifold.Energy.Surface
public import TauCeti.Geometry.Symplectic.Manifold.Prod
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The energy of a map into a product

Let `P` and `M` carry two-forms `σ` and `τ` and almost complex structures `J` and `L`, and give
`P × M` the product form `pr₁^* σ + pr₂^* τ` (`TauCeti.SmoothTwoForm.prod`) and the product
structure `J × L` (`TauCeti.SmoothAlmostComplexStructure.prod`). A map `u : C → P × M` from a
surface `(C, j)` has the two components `pr₁ ∘ u` and `pr₂ ∘ u`, and this file shows that the
energy of `u` is the sum of the energies of its components. At every point where `u` is
differentiable, the energy form of `u` is the sum of the energy forms of its components
(`TauCeti.SmoothTwoForm.energyForm_prod_apply`), so for a `C¹` map from a compact oriented surface

`E(u) = E(pr₁ ∘ u) + E(pr₂ ∘ u)`

(`TauCeti.SmoothTwoForm.energy_prod`). No relation between the forms and the almost complex
structures is needed, and `u` need not be pseudoholomorphic. This is the energy counterpart of the
splitting `∫_C u^* (pr₁^* σ + pr₂^* τ) = ∫_C (pr₁ ∘ u)^* σ + ∫_C (pr₂ ∘ u)^* τ` of the symplectic
area (`TauCeti.integralTopForm_mpullback_prod`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (the energy of a map from a Riemann surface).
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H P F H' M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H'] {I' : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]
  {E'' H'' C : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace C] [ChartedSpace H'' C]
  [IsManifold I'' ∞ C] {σ : SmoothTwoForm I P} {τ : SmoothTwoForm I' M}
  {J : SmoothAlmostComplexStructure I P} {L : SmoothAlmostComplexStructure I' M}
  {j : SmoothAlmostComplexStructure I'' C} {u : C → P × M} {c : C}

/-- **The energy form of a map into a product.** At a point where `u : C → P × M` is
differentiable, the energy form of `u` for the product form and the product almost complex
structure is the sum of the energy forms of its components. -/
theorem energyForm_prod_apply [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hu : MDifferentiableAt I'' (I.prod I') u c) :
    (σ.prod τ).energyForm (SmoothAlmostComplexStructure.prod J L) j u c =
      σ.energyForm J j (Prod.fst ∘ u) c + τ.energyForm L j (Prod.snd ∘ u) c := by
  ext v
  rw [show v = ![v 0, v 1] from (FinVec.etaExpand_eq v).symm, ContinuousAlternatingMap.add_apply,
    energyForm_apply, energyForm_apply, energyForm_apply, eval₂_prod, eval₂_prod]
  simp only [SmoothAlmostComplexStructure.prod_apply, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_apply, Function.comp_def, ← hu.mfderiv_fst_apply,
    ← hu.mfderiv_snd_apply]
  ring

variable [FiniteDimensional ℝ E''] [CompactSpace C] {o : Manifold.Orientation I'' C (Fin 2)}

/-- **The energy of a map into a product.** For a `C¹` map `u : C → P × M` from a compact oriented
surface, the energy of `u` for the product form and the product almost complex structure is the
sum of the energies of its components. -/
theorem energy_prod [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (hu : ContMDiff I'' (I.prod I') 1 u) :
    (σ.prod τ).energy (SmoothAlmostComplexStructure.prod J L) j o u =
      σ.energy J j o (Prod.fst ∘ u) + τ.energy L j o (Prod.snd ∘ u) := by
  rw [energy_def, energy_def, energy_def, ← integralTopForm_add_of_compactSpace o
    (isSmoothForm_energyForm (contMDiff_fst.comp hu) le_rfl)
    (isSmoothForm_energyForm (contMDiff_snd.comp hu) le_rfl)]
  exact congrArg _ (funext fun c ↦ energyForm_prod_apply ((hu c).mdifferentiableAt one_ne_zero))

end TauCeti.SmoothTwoForm
