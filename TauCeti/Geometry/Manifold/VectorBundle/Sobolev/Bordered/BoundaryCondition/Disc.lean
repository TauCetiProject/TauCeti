/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedDisc
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition

/-!
# Boundary conditions on the closed unit disc

This file works out the space `W^{1,p}_L` of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.BoundaryCondition` on the closed unit
disc `Complex.UnitClosedDisc`, a Riemann surface with boundary whose boundary is the unit circle,
for the trivial bundle with fibre `ℂⁿ` and any finite bundle atlas, with `2 < p ≤ ∞`.

A `C¹` map `f` from the closed disc to `ℂⁿ` is the continuous representative of an element of
`W^{1,p}_L` exactly when `f ζ ∈ L ζ` for every `ζ` on the unit circle
(`TauCeti.BorderedSobolevSection.exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc`).
For the totally real subspace `L = ℝⁿ` of real vectors, with `e₁` the first standard basis vector,
this gives:

* the constant section `e₁` lies in `W^{1,p}_{ℝⁿ}`;
* the constant section `i e₁` does not;
* the section `z e₁` does not, since its value `i e₁` at `z = i` is not real;
* the section `(z + conj z) e₁ = 2 (re z) e₁` does.

## Main results

* `TauCeti.BorderedSobolevSection.exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc`:
  a `C¹` map lies in `W^{1,p}_L` exactly when its values on the unit circle lie in `L`.
* `TauCeti.BorderedSobolevSection.exists_mem_withBoundaryIn_real_toSection_eq_single_one`,
  `TauCeti.BorderedSobolevSection.not_exists_mem_withBoundaryIn_real_toSection_eq_single_I`,
  `TauCeti.BorderedSobolevSection.not_exists_mem_withBoundaryIn_real_toSection_eq_smul_single_one`,
  `TauCeti.BorderedSobolevSection.exists_mem_withBoundaryIn_real_toSection_eq_add_conj_smul`:
  the four examples above.
-/

public section

noncomputable section

open Bundle Complex
open scoped Manifold ENNReal ComplexConjugate Complex.UnitDisc

namespace TauCeti

namespace BorderedSobolevSection

variable {n : ℕ}
  {A : FiniteBundleAtlas ClosedUpperHalfPlane 𝕔𝔻 (Fin n → ℂ) (Bundle.Trivial 𝕔𝔻 (Fin n → ℂ))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A `C¹` map from the closed disc to `ℂⁿ`, as a `C¹` section of the trivial bundle. -/
private def trivialSection {f : 𝕔𝔻 → Fin n → ℂ}
    (hf : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, Fin n → ℂ) 1 f) :
    Cₛ^(1 : ℕ)⟮closedUpperHalfPlaneModel; Fin n → ℂ, Bundle.Trivial 𝕔𝔻 (Fin n → ℂ)⟯ :=
  ⟨f, fun x ↦ (contMDiffAt_section_iff x).2 (by simpa using hf x)⟩

/-- **Boundary conditions on the closed disc.** For `2 < p ≤ ∞`, a `C¹` map `f` from the closed
unit disc to `ℂⁿ` is the continuous representative of an element of `W^{1,p}_L` of the trivial
bundle exactly when its value at every point `ζ` of the unit circle lies in `L ζ`. -/
theorem exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc (hp : 2 < p)
    (L : 𝕔𝔻 → Submodule ℝ (Fin n → ℂ)) {f : 𝕔𝔻 → Fin n → ℂ}
    (hf : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, Fin n → ℂ) 1 f) :
    (∃ w ∈ withBoundaryIn A hp L, toSection hp w = f) ↔
      ∀ ζ : 𝕔𝔻, ‖(ζ : ℂ)‖ = 1 → f ζ ∈ L ζ := by
  have h := exists_mem_withBoundaryIn_toSection_eq_iff (A := A) (hp := hp) (L := L)
    (s := trivialSection hf)
  refine h.trans (forall_congr' fun ζ ↦ ?_)
  rw [← SetLike.mem_coe, ← Set.mem_compl_iff, UnitClosedDisc.compl_borderedInterior]
  rfl

/-- The real subspace `ℝⁿ` of `ℂⁿ`: the vectors all of whose coordinates are real. -/
private theorem mem_ker_im_iff {v : Fin n → ℂ} :
    v ∈ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j)) ↔
      ∀ j, (v j).im = 0 := by
  simp [funext_iff]

/-- The constant section `e₁` of the trivial bundle with fibre `ℂⁿ` over the closed disc lies in
`W^{1,p}_{ℝⁿ}`, for the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`. -/
theorem exists_mem_withBoundaryIn_real_toSection_eq_single_one [NeZero n] (hp : 2 < p) :
    ∃ w ∈ withBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))),
      toSection hp w = fun _ ↦ Pi.single 0 1 := by
  refine (exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _
    contMDiff_const).2 fun _ _ ↦ mem_ker_im_iff.2 fun j ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · simp [hj]

/-- The constant section `i e₁` of the trivial bundle with fibre `ℂⁿ` over the closed disc does not
lie in `W^{1,p}_{ℝⁿ}`, for the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`. -/
theorem not_exists_mem_withBoundaryIn_real_toSection_eq_single_I [NeZero n] (hp : 2 < p) :
    ¬∃ w ∈ withBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))),
      toSection hp w = fun _ ↦ Pi.single 0 I := by
  rw [exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _ contMDiff_const]
  intro h
  have := mem_ker_im_iff.1 (h (UnitClosedDisc.mk 1 (by simp)) (by simp)) 0
  simp at this

/-- The section `z e₁` of the trivial bundle with fibre `ℂⁿ` over the closed disc does not lie in
`W^{1,p}_{ℝⁿ}`, for the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`: its value at the boundary point
`z = i` is `i e₁`, which is not real. -/
theorem not_exists_mem_withBoundaryIn_real_toSection_eq_smul_single_one [NeZero n] (hp : 2 < p) :
    ¬∃ w ∈ withBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))),
      toSection hp w = fun z : 𝕔𝔻 ↦ (z : ℂ) • (Pi.single 0 1 : Fin n → ℂ) := by
  have hf : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, Fin n → ℂ) 1
      fun z : 𝕔𝔻 ↦ (z : ℂ) • (Pi.single 0 1 : Fin n → ℂ) :=
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (Pi.single 0 1 : Fin n → ℂ)).restrictScalars ℝ).contMDiff.comp UnitClosedDisc.contMDiff_coe
  rw [exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _ hf]
  intro h
  have := mem_ker_im_iff.1 (h (UnitClosedDisc.mk I (by simp)) (by simp)) 0
  simp at this

/-- The section `(z + conj z) e₁ = 2 (re z) e₁` of the trivial bundle with fibre `ℂⁿ` over the
closed disc lies in `W^{1,p}_{ℝⁿ}`, for the totally real boundary condition `ℝⁿ ⊆ ℂⁿ`. -/
theorem exists_mem_withBoundaryIn_real_toSection_eq_add_conj_smul [NeZero n] (hp : 2 < p) :
    ∃ w ∈ withBoundaryIn A hp
      (fun _ ↦ LinearMap.ker (LinearMap.pi fun j : Fin n ↦ imLm.comp (LinearMap.proj j))),
      toSection hp w = fun z : 𝕔𝔻 ↦ ((z : ℂ) + conj (z : ℂ)) • (Pi.single 0 1 : Fin n → ℂ) := by
  have hf : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, Fin n → ℂ) 1
      fun z : 𝕔𝔻 ↦ ((z : ℂ) + conj (z : ℂ)) • (Pi.single 0 1 : Fin n → ℂ) :=
    (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (Pi.single 0 1 : Fin n → ℂ)).restrictScalars ℝ).comp
        (ContinuousLinearMap.id ℝ ℂ + conjCLE.toContinuousLinearMap)).contMDiff.comp
          UnitClosedDisc.contMDiff_coe
  refine (exists_mem_withBoundaryIn_toSection_eq_iff_of_unitClosedDisc hp _ hf).2
    fun _ _ ↦ mem_ker_im_iff.2 fun j ↦ ?_
  rcases eq_or_ne j 0 with rfl | hj
  · simp [add_conj]
  · simp [hj]

end BorderedSobolevSection

end TauCeti
