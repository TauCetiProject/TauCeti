/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.SmoothSingular.Period
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic

/-!
# Periods of the suspension forms on the cross summand

Let `φ` be a diffeomorphism of a Hausdorff `σ`-compact smooth manifold `M`, modelled on a
finite-dimensional space, preserving a closed two-form `σ`. Let `Y_φ` be its smooth mapping torus
and let `X_φ = (ℝ / ℤ)_s × Y_φ` carry `Ω = ds ∧ dt + ω_v`, where `ω_v` is the fiber form `σ_v`
pulled back along the projection `X_φ → Y_φ` (`TauCeti.SmoothMappingTorus.suspensionForm`).

The second integral singular homology of `X_φ` contains the cross summand `[S¹_s] × H₁(Y_φ; ℤ)`,
the cross products of the class of the circle with the first homology classes of the mapping
torus. Classes of this summand include the classes of the orbit tori `(ℝ / ℤ) × γ` over closed
orbits `γ` of the suspension flow (`TauCeti.SmoothMappingTorus.orbitTorusHomologyClass`).

When `σ` is closed, `Ω`, `ds ∧ dt` and `ω_v` are bundled as closed forms
(`TauCeti.SmoothMappingTorus.suspensionClosedForm`, `TauCeti.SmoothMappingTorus.wedgeTimeForm` and
`TauCeti.SmoothMappingTorus.verticalForm`), and `Ω = ds ∧ dt + ω_v` holds among closed forms
(`TauCeti.SmoothMappingTorus.suspensionClosedForm_eq_add`).

This file proves that `ω_v` has zero period on the cross summand: for every class `α` of positive
degree of the circle and every class `a` of `Y_φ` of complementary degree, the period of the closed
form `ω_v` on `α × a` vanishes
(`SmoothMappingTorus.closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero`).
Since `ω_v` is pulled back from `Y_φ`, its period on `α × a` is the period of `σ_v` on the image of
`α × a` under the projection `X_φ → Y_φ`, which is zero because `α` has positive degree
(`TauCeti.closedFormHomologyPeriod_mpullback_snd_singularHomologyCrossBilinear_eq_zero`).
Consequently, on the cross summand the period of `Ω` is the period of `ds ∧ dt`
(`SmoothMappingTorus.closedFormHomologyPeriod_suspensionClosedForm_singularHomologyCrossBilinear`).

These are the homological input for compact pseudoholomorphic curves in `X_φ` whose class lies in
the cross summand: once the vertical area `∫_C u^* ω_v` of such a curve `u : C → X_φ` is identified
with the period of `ω_v` on its class, it vanishes, and the classification of curves of zero
vertical area as orbit tori applies
(`TauCeti.SmoothMappingTorus.range_eq_range_orbitTorus_of_integralTopForm_eq_zero`).

No compactness of `M` and no nondegeneracy of `σ` is needed.

## Main definitions

* `TauCeti.SmoothMappingTorus.wedgeTimeForm φ`: the closed form `ds ∧ dt` on `X_φ`.
* `TauCeti.SmoothMappingTorus.verticalForm hσc`: the closed form `ω_v` on `X_φ`.
* `TauCeti.SmoothMappingTorus.suspensionClosedForm hσc`: the closed form `Ω` on `X_φ`.

## Main results

* `TauCeti.SmoothMappingTorus.suspensionClosedForm_eq_add`: `Ω = ds ∧ dt + ω_v` as closed forms.
* `SmoothMappingTorus.closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero`:
  `ω_v` has zero period on every cross product with a positive-degree class of the circle.
* `SmoothMappingTorus.closedFormHomologyPeriod_suspensionClosedForm_singularHomologyCrossBilinear`:
  on such cross products the periods of `Ω` and of `ds ∧ dt` agree.

## References

* Michael Hutchings and Michael Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2.
* Eleny-Nicoleta Ionel and Thomas H. Parker, *Gromov invariants and symplectic maps*,
  Mathematische Annalen 314 (1999), 127–158.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] [SigmaCompactSpace M]
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

variable (φ) in
/-- The form `ds ∧ dt` on `(ℝ / ℤ) × Y_φ`, the wedge of the time forms of the circle and of the
mapping torus pulled back to the product, as a closed form. -/
def wedgeTimeForm :
    closedForms (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) 2 :=
  ⟨SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ)),
    SmoothForm.wedge_mem_closedForms
      ((mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1
        ((AddCircle.isClosed_timeForm 1).mpullback _ _)))
      ((mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1
        ((isClosed_timeForm φ).mpullback _ _)))⟩

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
/-- The closed form `ds ∧ dt` is the wedge of the pulled back time forms. -/
@[simp]
theorem coe_wedgeTimeForm :
    (wedgeTimeForm φ).val = SmoothForm.wedge
      (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ)) :=
  (rfl)

variable (hσ) in
/-- The vertical form `ω_v` on `(ℝ / ℤ) × Y_φ` of a closed `φ`-invariant two-form `σ`: the fiber
form `σ_v` pulled back along the projection to the mapping torus, as a closed form. -/
def verticalForm (hσc : σ.IsClosed) :
    closedForms (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) 2 :=
  closedForms.mpullback Prod.snd contMDiff_snd 2
    ⟨fiberForm φ σ hσ,
      (mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1 (isClosed_fiberForm_iff.2 hσc))⟩

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
/-- The vertical form is the fiber form pulled back along the projection to the mapping torus. -/
@[simp]
theorem coe_verticalForm (hσc : σ.IsClosed) :
    (verticalForm hσ hσc).val = SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ) :=
  closedForms.coe_mpullback _ _ _ _

variable (hσ) in
/-- The suspension form `Ω = ds ∧ dt + ω_v` on `(ℝ / ℤ) × Y_φ` of a closed `φ`-invariant two-form
`σ`, as a closed form. -/
def suspensionClosedForm (hσc : σ.IsClosed) :
    closedForms (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) 2 :=
  ⟨suspensionForm φ σ hσ,
    (mem_closedForms _ _).2 ((SmoothForm.isClosed_def _).1 (isClosed_suspensionForm_iff.2 hσc))⟩

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
/-- The closed form `Ω` is the suspension form. -/
@[simp]
theorem coe_suspensionClosedForm (hσc : σ.IsClosed) :
    (suspensionClosedForm hσ hσc).val = suspensionForm φ σ hσ :=
  (rfl)

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] in
/-- The closed form `Ω` splits as `ds ∧ dt + ω_v`. -/
theorem suspensionClosedForm_eq_add (hσc : σ.IsClosed) :
    suspensionClosedForm hσ hσc = wedgeTimeForm φ + verticalForm hσ hσc :=
  Subtype.ext (by rw [Submodule.coe_add, coe_verticalForm, coe_suspensionClosedForm,
    coe_wedgeTimeForm, suspensionForm_def])

/-- **The vertical form has zero period on the cross summand.** For a class `α` of positive degree
of the circle `ℝ / ℤ`, such as its fundamental class, and any class `a` of the mapping torus of
complementary degree, the period of `ω_v` on the cross product `α × a` vanishes. -/
@[simp]
theorem closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero
    (hσc : σ.IsClosed)
    {p q : ℕ} (h : p + q = 2) (hp : p ≠ 0)
    (α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology p)
    (a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology q) :
    closedFormHomologyPeriod (verticalForm hσ hσc)
      (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) = 0 :=
  closedFormHomologyPeriod_mpullback_snd_singularHomologyCrossBilinear_eq_zero h hp _ α a

/-- **On the cross summand, the periods of `Ω` are those of `ds ∧ dt`.** For a class `α` of
positive degree of the circle and a class `a` of the mapping torus of complementary degree, the
periods of `Ω = ds ∧ dt + ω_v` and of `ds ∧ dt` on the cross product `α × a` agree. -/
theorem closedFormHomologyPeriod_suspensionClosedForm_singularHomologyCrossBilinear
    (hσc : σ.IsClosed) {p q : ℕ} (h : p + q = 2) (hp : p ≠ 0)
    (α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology p)
    (a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology q) :
    closedFormHomologyPeriod (suspensionClosedForm hσ hσc)
        (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
          (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) =
      closedFormHomologyPeriod (wedgeTimeForm φ)
        (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
          (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) := by
  rw [suspensionClosedForm_eq_add, closedFormHomologyPeriod_add, AddMonoidHom.add_apply,
    closedFormHomologyPeriod_verticalForm_singularHomologyCrossBilinear_eq_zero hσc h hp, add_zero]

end TauCeti.SmoothMappingTorus
