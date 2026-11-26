/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition.Higher
import TauCeti.Geometry.Manifold.VectorBundle.Section.Trivial

/-!
# Higher-order boundary conditions on the closed unit disc

This file works out the spaces `W^{1+k,p}_L` of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition.Higher` on the closed
unit disc `Complex.UnitClosedDisc`, for the trivial bundle with fibre `ℂⁿ`, any finite bundle atlas
and `2 < p ≤ ∞`, as `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition.Disc`
does at order one. A `C^{1+k}` map `f` from the closed disc to `ℂⁿ` is the continuous representative
of an element of `W^{1+k,p}_L` exactly when `f ζ ∈ L ζ` for every `ζ` on the unit circle
(`BorderedSobolevSection.exists_mem_higherWithBoundaryIn_toSection_eq_iff_of_unitClosedDisc`).
For the totally real subspace `L = ℝⁿ`, the constant section `e₁` lies in `W^{1+k,p}_{ℝⁿ}` for every
`k`, and the constant section `i e₁` does not.

## Main results

* `BorderedSobolevSection.exists_mem_higherWithBoundaryIn_toSection_eq_iff_of_unitClosedDisc`:
  a `C^{1+k}` map lies in `W^{1+k,p}_L` exactly when its values on the unit circle lie in `L`.
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

/-- **Higher-order boundary conditions on the closed disc.** For `2 < p ≤ ∞` and every `k`, a
`C^{1+k}` map `f` from the closed unit disc to `ℂⁿ` is the continuous representative of an
element of `W^{1+k,p}_L` of the trivial bundle exactly when its value at every point `ζ` of the
unit circle lies in `L ζ`. -/
theorem exists_mem_higherWithBoundaryIn_toSection_eq_iff_of_unitClosedDisc (hp : 2 < p)
    (L : 𝕔𝔻 → Submodule ℝ (Fin n → ℂ)) (k : ℕ) {f : 𝕔𝔻 → Fin n → ℂ}
    (hf : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, Fin n → ℂ) (1 + k : ℕ) f) :
    (∃ w ∈ higherWithBoundaryIn A hp L k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) = f) ↔
      ∀ ζ : 𝕔𝔻, ‖(ζ : ℂ)‖ = 1 → f ζ ∈ L ζ := by
  -- `f` as a `C^{1+k}` section of the trivial bundle.
  have h := exists_mem_higherWithBoundaryIn_toSection_eq_iff (A := A) (hp := hp) (L := L)
    (s := ContMDiffSection.trivialEquiv.symm ⟨f, hf⟩)
  have hs : ⇑(ContMDiffSection.trivialEquiv.symm
      (⟨f, hf⟩ : C^(1 + k : ℕ)⟮closedUpperHalfPlaneModel, 𝕔𝔻; 𝓘(ℝ, Fin n → ℂ), Fin n → ℂ⟯) :
        Cₛ^(1 + k : ℕ)⟮closedUpperHalfPlaneModel; Fin n → ℂ, Bundle.Trivial 𝕔𝔻 (Fin n → ℂ)⟯) =
      f :=
    -- The coercion of `⟨f, hf⟩` is `f`.
    ContMDiffSection.coe_trivialEquiv_symm _
  rw [hs] at h
  exact h.trans (forall_congr' fun ζ ↦ imp_congr_left UnitClosedDisc.notMem_borderedInterior_iff)

/-- The constant section `e₁` is the continuous representative of an element of
`W^{1+k,p}_{ℝⁿ}`, for every `k`. -/
theorem exists_mem_higherWithBoundaryIn_real_toSection_eq_single_one [NeZero n] (hp : 2 < p)
    (k : ℕ) :
    ∃ w ∈ higherWithBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))) k,
      toSection hp (A.halfSectionChartData.lowerOrdersL volume p 1 k w) =
        fun _ ↦ Pi.single 0 1 :=
  (exists_mem_higherWithBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _ k
    contMDiff_const).2 fun _ _ ↦ by
    simp only [LinearMap.mem_ker, funext_iff]
    intro j
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
        fun _ ↦ Pi.single 0 I := by
  rw [exists_mem_higherWithBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _ k contMDiff_const]
  intro h
  have := congrFun (LinearMap.mem_ker.1 (h (UnitClosedDisc.mk 1 (by simp)) (by simp))) 0
  simp at this

end BorderedSobolevSection

end TauCeti
