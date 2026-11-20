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

This file proves that `ω_v` has zero period on the cross summand: for every class `α` of positive
degree of the circle and every class `a` of `Y_φ` of complementary degree, the period of the closed
form `ω_v` on `α × a` vanishes
(`TauCeti.SmoothMappingTorus.homologyIntegral_verticalForm_singularHomologyCrossBilinear`).
Since `ω_v` is pulled back from `Y_φ`, its period on `α × a` is the period of `σ_v` on the image of
`α × a` under the projection `X_φ → Y_φ`, which is zero because `α` has positive degree
(`TauCeti.homologyIntegral_mpullback_snd_singularHomologyCrossBilinear`). Consequently, on the
cross summand the period of `Ω` is the period of `ds ∧ dt`
(`TauCeti.SmoothMappingTorus.homologyIntegral_suspensionForm_singularHomologyCrossBilinear`).

These are the homological input for compact pseudoholomorphic curves in `X_φ` whose class lies in
the cross summand: once the vertical area `∫_C u^* ω_v` of such a curve `u : C → X_φ` is identified
with the period of `ω_v` on its class, it vanishes, and the classification of curves of zero
vertical area as orbit tori applies
(`TauCeti.SmoothMappingTorus.range_eq_range_orbitTorus_of_integralTopForm_eq_zero`).

No compactness of `M` and no nondegeneracy of `σ` is needed.

## Main definitions

* `TauCeti.SmoothMappingTorus.verticalForm hσc`: the closed form `ω_v` on `X_φ`.

## Main results

* `TauCeti.SmoothMappingTorus.homologyIntegral_verticalForm_singularHomologyCrossBilinear`: `ω_v`
  has zero period on every cross product with a positive-degree class of the circle.
* `TauCeti.SmoothMappingTorus.homologyIntegral_suspensionForm_singularHomologyCrossBilinear`: on
  such cross products the periods of `Ω` and of `ds ∧ dt` agree.

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
    (verticalForm hσ hσc).1 = SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ) :=
  closedForms.coe_mpullback _ _ _ _

/-- **The vertical form has zero period on the cross summand.** For a class `α` of positive degree
of the circle `ℝ / ℤ`, such as its fundamental class, and any class `a` of the mapping torus of
complementary degree, the period of `ω_v` on the cross product `α × a` vanishes. -/
@[simp]
theorem homologyIntegral_verticalForm_singularHomologyCrossBilinear (hσc : σ.IsClosed)
    {p q : ℕ} (h : p + q = 2) (hp : p ≠ 0)
    (α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology p)
    (a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology q) :
    homologyIntegral (verticalForm hσ hσc)
      (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) = 0 :=
  homologyIntegral_mpullback_snd_singularHomologyCrossBilinear h hp _ α a

/-- **On the cross summand, the periods of `Ω` are those of `ds ∧ dt`.** Let `Ω'` and `β` be the
closed forms underlying `Ω = ds ∧ dt + ω_v` and `ds ∧ dt`. For a class `α` of positive degree of
the circle and a class `a` of the mapping torus of complementary degree, their periods on the cross
product `α × a` agree. -/
theorem homologyIntegral_suspensionForm_singularHomologyCrossBilinear
    {Ω' β : closedForms (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (UnitAddCircle × SmoothMappingTorus φ) 2}
    (hΩ : Ω'.1 = suspensionForm φ σ hσ)
    (hβ : β.1 = SmoothForm.wedge
      (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
      (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm φ)))
    {p q : ℕ} (h : p + q = 2) (hp : p ≠ 0)
    (α : ((singularChains ℤ).obj (TopCat.of UnitAddCircle)).homology p)
    (a : ((singularChains ℤ).obj (TopCat.of (SmoothMappingTorus φ))).homology q) :
    homologyIntegral Ω' (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) =
      homologyIntegral β (TopCat.singularHomologyCrossBilinear ℤ (TopCat.of UnitAddCircle)
        (TopCat.of (SmoothMappingTorus φ)) p q 2 h α a) := by
  have hσc : σ.IsClosed := isClosed_suspensionForm_iff.1
    ((SmoothForm.isClosed_def _).2 (hΩ ▸ (mem_closedForms _ _).1 Ω'.2))
  have hsplit : Ω' = β + verticalForm hσ hσc :=
    Subtype.ext (by rw [Submodule.coe_add, coe_verticalForm, hΩ, hβ, suspensionForm_def])
  rw [hsplit, homologyIntegral_add, AddMonoidHom.add_apply,
    homologyIntegral_verticalForm_singularHomologyCrossBilinear hσc h hp, add_zero]

end TauCeti.SmoothMappingTorus
