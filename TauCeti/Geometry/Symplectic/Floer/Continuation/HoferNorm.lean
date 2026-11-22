/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.Manifold
public import TauCeti.Geometry.Symplectic.Hamiltonian.HoferNorm

/-!
# The action shift of continuation cylinders and the Hofer norm

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M` and `H₀`, `H₁` two `C¹`
time-dependent Hamiltonians. Along a solution `u` of the Floer equation for the continuation
homotopy from `H₀` to `H₁` (`TauCeti.Floer.continuationHomotopy`), with almost complex structures
tamed by `ω`, the capped action at the `H₁` end exceeds the capped action at the `H₀` end, with
the cap carried along the cylinder, by at most `∫₀¹ h` for any bound `H₀ - H₁ ≤ h`
(`SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_of_continuationHomotopy`).
This file reads off the two consequences for the action filtration.

* **Monotone homotopies preserve the action.** If `H₀ ≤ H₁` on `[0, 1] × M`, the action does not
  increase from the `H₀` end to the `H₁` end
  (`SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_of_continuationHomotopy_of_le`),
  so a continuation map along a monotone homotopy preserves the action filtration.
* **General homotopies shift the action by at most the Hofer norm.** On a compact manifold the
  best bound is `h(t) = max_x (H₀ - H₁)(t, x)`, so the action increases by at most the positive
  part `E⁺(H₀ - H₁) = ∫₀¹ max_x (H₀ - H₁)(t, x) dt` of the Hofer norm
  (`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus`), and
  so by at most the Hofer norm `‖H₀ - H₁‖` whenever `H₀ - H₁` is nonpositive somewhere at each
  time, as for two Hamiltonians normalized to have the same mean, or agreeing at some point
  (`TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferNorm`).

Since no weak exactness or closedness of `ω` is used, these apply to the capped Floer theory of
closed monotone targets as well as to closed symplectically aspherical ones. The existence,
compactness and counting of continuation cylinders are not treated here.

## Main results

* `SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_of_continuationHomotopy_of_le`:
  monotone homotopies do not increase the capped action.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus`: the
  action increases by at most `E⁺(H₀ - H₁)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferNorm`: the
  action increases by at most `‖H₀ - H₁‖`.

## References

* D. McDuff, D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, §12.3, on the energy of continuation solutions.
* M. Schwarz, *On the action spectrum for closed symplectically aspherical manifolds*, Pacific J.
  Math. 193 (2000), 419–461, on the Hofer-norm estimate for the action filtration.
-/

public section

open Function MeasureTheory Set
open scoped Manifold

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {H₀ H₁ : ℝ → M → ℝ}
  {u v : ℝ × ℝ → M} {a b : ℝ}

/-- **Monotone homotopies do not increase the capped action.** Let `ω` be a nondegenerate two-form
on a finite-dimensional manifold and `H₀ ≤ H₁` on `[0, 1] × M` two `C¹` time-dependent
Hamiltonians. If `u` solves the Floer equation `∂_s u + J_z (∂_t u - X_{H_z}(u)) = 0` for the
continuation homotopy from `H₀` to `H₁` on `[a, b] × [0, 1]`, with `a ≤ 0 ≤ 1 ≤ b` and almost
complex structures `J z` tamed by `ω`, and `v` is a `C¹` map with `v(0, ·) = u(b, ·)`, then
`A_{H₁}(γ_b, v) ≤ A_{H₀}(γ_a, w # v)` for the capped action `TauCeti.cylinderAction`, where
`w # v` glues `u`, rescaled from `[a, b]` to `[0, 1]`, to `v`. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_of_continuationHomotopy_of_le
    (hω : ω.IsNondegenerate)
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (ha : a ≤ 0) (hb : 1 ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    (hle : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, H₀ t x ≤ H₁ t x) :
    cylinderAction ω.val H₁ v ≤
      cylinderAction ω.val H₀ (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) := by
  simpa using hω.cylinderAction_le_cylinderAction_add_of_continuationHomotopy hH₀ hH₁ hu ha hb
    hv hv₀ J hJ hfloer (h := fun _ ↦ 0) (fun t ht x ↦ sub_nonpos.2 (hle t ht x))
    integrableOn_zero

variable [CompactSpace M]

/-- **The action shift of a continuation cylinder is at most `E⁺(H₀ - H₁)`.** Let `ω` be a
nondegenerate two-form on a compact finite-dimensional manifold and `H₀`, `H₁` two `C¹`
time-dependent Hamiltonians. If `u` solves the Floer equation for the continuation homotopy from
`H₀` to `H₁` on `[a, b] × [0, 1]`, with `a ≤ 0 ≤ 1 ≤ b` and almost complex structures tamed by
`ω`, and `v` is a `C¹` map with `v(0, ·) = u(b, ·)`, then
`A_{H₁}(γ_b, v) ≤ A_{H₀}(γ_a, w # v) + E⁺(H₀ - H₁)`, where
`E⁺(H₀ - H₁) = ∫₀¹ max_x (H₀ - H₁)(t, x) dt` (`TauCeti.hoferPlus`). -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus (hω : ω.IsNondegenerate)
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (ha : a ≤ 0) (hb : 1 ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0) :
    cylinderAction ω.val H₁ v ≤
      cylinderAction ω.val H₀ (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        hoferPlus (H₀ - H₁) := by
  have hc : Continuous (uncurry (H₀ - H₁)) := hH₀.continuous.sub hH₁.continuous
  rw [hoferPlus_def]
  exact hω.cylinderAction_le_cylinderAction_add_of_continuationHomotopy hH₀ hH₁ hu ha hb hv hv₀ J
    hJ hfloer (fun t _ x ↦ (hc.uncurry_left t).le_ciSup_of_compactSpace x)
    hc.iSup_apply_of_compactSpace.integrableOn_Icc

/-- **The action shift of a continuation cylinder is at most the Hofer norm.** Under the hypotheses
of `TauCeti.SmoothTwoForm.IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferPlus`, if
moreover at every time `t ∈ [0, 1]` there is a point `x` with `H₀(t, x) ≤ H₁(t, x)`, for instance
because `H₀` and `H₁` are normalized to have the same mean or agree at some point, then
`A_{H₁}(γ_b, v) ≤ A_{H₀}(γ_a, w # v) + ‖H₀ - H₁‖` for the Hofer norm `TauCeti.hoferNorm`. -/
theorem IsNondegenerate.cylinderAction_le_cylinderAction_add_hoferNorm (hω : ω.IsNondegenerate)
    (hH₀ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₀))
    (hH₁ : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry H₁)) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (ha : a ≤ 0) (hb : 1 ≤ b) (hv : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 v)
    (hv₀ : ∀ t, v (0, t) = u (b, t)) (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hJ : ∀ z ∈ Icc a b ×ˢ Icc 0 1, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Icc a b ×ˢ Icc 0 1, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J z (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (continuationHomotopy H₀ H₁ z) (u z)) = 0)
    (hsign : ∀ t ∈ Icc (0 : ℝ) 1, ∃ x, H₀ t x ≤ H₁ t x) :
    cylinderAction ω.val H₁ v ≤
      cylinderAction ω.val H₀ (rectangleTrans (u ∘ Prod.map (fun s ↦ a + (b - a) * s) id) v) +
        hoferNorm (H₀ - H₁) := by
  have hle := hoferPlus_le_hoferNorm (H := H₀ - H₁) fun t ht ↦
    (hsign t ht).imp fun _ hx ↦ sub_nonpos.2 hx
  linarith [hω.cylinderAction_le_cylinderAction_add_hoferPlus hH₀ hH₁ hu ha hb hv hv₀ J hJ hfloer]

end SmoothTwoForm

end TauCeti
