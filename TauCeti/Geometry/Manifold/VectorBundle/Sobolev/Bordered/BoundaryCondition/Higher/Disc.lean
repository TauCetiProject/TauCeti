/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition.Disc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition.Higher

/-!
# Higher-order boundary conditions on the closed unit disc

On the closed unit disc `Complex.UnitClosedDisc`, for the trivial bundle with fibre `ℂⁿ`, any finite
bundle atlas, `2 < p ≤ ∞` and the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`, a constant section
`v` lies in `W^{1+k,p}_{ℝⁿ}` of `TauCeti.BorderedSobolevSection.higherWithBoundaryIn` exactly when
all coordinates of `v` are real, at every order
(`TauCeti.BorderedSobolevSection.exists_mem_higherWithBoundaryIn_real_toSection_eq_const_iff`). So
the constant section `e₁` lies in `W^{1+k,p}_{ℝⁿ}` for every `k`, and `i e₁` does not.

## Main results

* `TauCeti.BorderedSobolevSection.exists_mem_higherWithBoundaryIn_real_toSection_eq_const_iff`:
  the constant sections in `W^{1+k,p}_{ℝⁿ}` are those with real coordinates.
* `TauCeti.BorderedSobolevSection.exists_mem_higherWithBoundaryIn_real_toSection_eq_single_one`,
  `TauCeti.BorderedSobolevSection.not_exists_mem_higherWithBoundaryIn_real_toSection_eq_single_I`:
  `e₁` lies in `W^{1+k,p}_{ℝⁿ}` for every `k`, and `i e₁` does not.
-/

public section

noncomputable section

open Bundle Complex MeasureTheory
open scoped Manifold ENNReal ContDiff Complex.UnitDisc

namespace TauCeti

namespace BorderedSobolevSection

variable {n : ℕ}
  {A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 (Fin n → ℂ) (Bundle.Trivial 𝕔𝔻 (Fin n → ℂ))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The constant section `v` of the trivial bundle with fibre `ℂⁿ`, of class `Cᵐ`. -/
private def constSection (m : ℕ) (v : Fin n → ℂ) :
    Cₛ^m⟮closedUpperHalfPlaneModel; Fin n → ℂ, Bundle.Trivial 𝕔𝔻 (Fin n → ℂ)⟯ :=
  ⟨fun _ ↦ v, fun x ↦ (contMDiffAt_section_iff x).2 (by simpa using contMDiffAt_const)⟩

private theorem constSection_apply (m : ℕ) (v : Fin n → ℂ) (z : 𝕔𝔻) :
    constSection m v z = v :=
  rfl

/-- **Constant sections on the closed disc.** For `2 < p ≤ ∞` and every `k`, the constant section
`v` of the trivial bundle with fibre `ℂⁿ` is the continuous representative of an element of
`W^{1+k,p}_{ℝⁿ}`, for the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`, exactly when all coordinates
of `v` are real. -/
theorem exists_mem_higherWithBoundaryIn_real_toSection_eq_const_iff (hp : 2 < p) (k : ℕ)
    (v : Fin n → ℂ) :
    (∃ w ∈ higherWithBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))) k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) = fun _ ↦ v) ↔
      ∀ j, (v j).im = 0 := by
  -- The point `1` lies on the boundary circle.
  have h1 : UnitClosedDisc.mk 1 (by simp) ∉ borderedInterior 𝕔𝔻 := by
    rw [← SetLike.mem_coe, ← Set.mem_compl_iff, UnitClosedDisc.compl_borderedInterior]
    simp
  refine ⟨fun ⟨w, hw, hwv⟩ ↦ ?_, fun h ↦ ⟨ofContMDiffSection A p (1 + k) (constSection (1 + k) v),
    ofContMDiffSection_mem_higherWithBoundaryIn_iff.2 fun _ _ ↦ ?_,
    toSection_lowerOrdersL_ofContMDiffSection hp _⟩⟩
  · have := mem_higherWithBoundaryIn_iff.1 hw _ h1
    rw [hwv] at this
    simpa [funext_iff] using this
  · simpa [funext_iff, constSection_apply] using h

/-- The constant section `e₁` is the continuous representative of an element of
`W^{1+k,p}_{ℝⁿ}`, for every `k`. -/
theorem exists_mem_higherWithBoundaryIn_real_toSection_eq_single_one [NeZero n] (hp : 2 < p)
    (k : ℕ) :
    ∃ w ∈ higherWithBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))) k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) =
        fun _ ↦ Pi.single 0 1 :=
  (exists_mem_higherWithBoundaryIn_real_toSection_eq_const_iff hp k _).2 fun j ↦ by
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]

/-- The constant section `i e₁` is the continuous representative of no element of
`W^{1+k,p}_{ℝⁿ}`. -/
theorem not_exists_mem_higherWithBoundaryIn_real_toSection_eq_single_I [NeZero n] (hp : 2 < p)
    (k : ℕ) :
    ¬∃ w ∈ higherWithBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))) k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) =
        fun _ ↦ Pi.single 0 I := fun h ↦ by
  simpa using (exists_mem_higherWithBoundaryIn_real_toSection_eq_const_iff hp k _).1 h 0

end BorderedSobolevSection

end TauCeti
