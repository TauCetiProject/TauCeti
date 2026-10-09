/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Submersion
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.NormalForm

/-!
# Transverse local equations for the toric boundary

Near each point of a regular toric fan realization, the boundary components through that point
have simultaneous holomorphic defining equations with jointly surjective complex differential.
Thus their conormal directions are independent: the boundary components meet transversely.
The differential is surjective throughout the neighbourhood, not just at its centre.

The equations are the coordinates assigned to the components by the holomorphic
coordinate-hyperplane normal form. Components not through the centre miss the neighbourhood.
The statement includes points in the dense torus, where the family of equations is empty.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§2.1 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and §4.1.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- The boundary components through any point have simultaneous holomorphic local defining
equations whose complex differential is surjective at every point of the neighbourhood.
This is the transversality of the ray-indexed boundary, including intersections of any number
of components. Components not through the chosen point do not meet this neighbourhood. -/
theorem exists_contMDiffOn_analyticBoundaryComponent_eq_zero_mvfderiv_surjective
    (x : Φ.analyticRealization hΦ) :
    letI := Φ.analyticChartedSpace hΦ
    letI := Fintype.ofFinite {ρ : Φ.Ray // x ∈ Φ.analyticBoundaryComponent hΦ ρ}
    ∃ (U : Set (Φ.analyticRealization hΦ))
      (F : Φ.analyticRealization hΦ →
        ({ρ : Φ.Ray // x ∈ Φ.analyticBoundaryComponent hΦ ρ} → ℂ)),
      IsOpen U ∧ x ∈ U ∧
        ContMDiffOn 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ)
          𝓘(ℂ, {ρ : Φ.Ray // x ∈ Φ.analyticBoundaryComponent hΦ ρ} → ℂ) ∞ F U ∧
        (∀ y ∈ U, Function.Surjective
          (mvfderiv 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) F y)) ∧
        ∀ y ∈ U, ∀ ρ : Φ.Ray,
          y ∈ Φ.analyticBoundaryComponent hΦ ρ ↔
            ∃ hρ : x ∈ Φ.analyticBoundaryComponent hΦ ρ, F y ⟨ρ, hρ⟩ = 0 := by
  classical
  let := Φ.analyticChartedSpace hΦ
  let := Fintype.ofFinite {ρ : Φ.Ray // x ∈ Φ.analyticBoundaryComponent hΦ ρ}
  obtain ⟨s, j, e, hx, hs, he⟩ :=
    Φ.exists_partialDiffeomorph_analyticBoundaryComponent_normalForm hΦ x ∞
  let j' := (Equiv.subtypeEquivRight hs).toEmbedding.trans j
  let L : (Fin (Module.finrank ℤ N) → ℂ) →L[ℂ]
      ({ρ : Φ.Ray // x ∈ Φ.analyticBoundaryComponent hΦ ρ} → ℂ) :=
    ContinuousLinearMap.pi fun ρ ↦ ContinuousLinearMap.proj (j' ρ)
  have hL : Function.Surjective L := by
    simpa only [L, ContinuousLinearMap.coe_pi', ContinuousLinearMap.proj_apply,
      Function.comp_def] using j'.injective.surjective_comp_right (γ := ℂ)
  refine ⟨e.source, L ∘ e, e.open_source, hx,
    L.contMDiff.comp_contMDiffOn e.contMDiffOn, ?_, ?_⟩
  · intro y hy
    exact mvfderiv_comp_surjective_of_isLocalDiffeomorphAt
      (_root_.PartialDiffeomorph.isLocalDiffeomorphAt _ _ ∞ e hy) (by simp) L hL
  · intro y hy ρ
    rw [he y hy ρ]
    constructor
    · rintro ⟨hρ, hzero⟩
      refine ⟨(hs ρ).mpr hρ, ?_⟩
      simpa [L, j', Equiv.subtypeEquivRight_apply] using hzero
    · rintro ⟨hρ, hzero⟩
      refine ⟨(hs ρ).mp hρ, ?_⟩
      simpa [L, j', Equiv.subtypeEquivRight_apply] using hzero

end TauCeti.Toric.Fan
