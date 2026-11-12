/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Diffeomorphisms isotopic to the identity through form-preserving diffeomorphisms

Let `σ` be a smooth differential form on a manifold `M`. Its stabilizer
`TauCeti.SmoothForm.diffeomorphStabilizer σ` is the group of smooth diffeomorphisms `φ` with
`φ^* σ = σ`; for a symplectic form `ω` it is `Symp(M, ω)`. This file defines the subgroup

`TauCeti.SmoothForm.isotopyStabilizer σ ≤ diffeomorphStabilizer σ`

of the final diffeomorphisms `φ₁` of the smooth diffeotopies `φ_t`, `t ∈ [0, 1]`, starting at the
identity, all of whose time slices preserve `σ`. For a symplectic form these are the
symplectomorphisms joined to the identity by a smooth symplectic isotopy. The diffeotopies are
those of `TauCeti.Diffeotopy`; they are not required to be constant near the ends of the time
interval.

It is a subgroup because the constant diffeotopy, pointwise composites `ψ_t ∘ φ_t` and pointwise
inverses `φ_t⁻¹` of `σ`-preserving diffeotopies preserve `σ`. Conjugating a `σ`-preserving
diffeotopy by an element `f` of the stabilizer gives the `σ`-preserving diffeotopy
`f ∘ φ_t ∘ f⁻¹` (`TauCeti.Diffeotopy.transDiffeomorph`), so the subgroup is normal in the
stabilizer (`TauCeti.SmoothForm.normal_isotopyStabilizer_subgroupOf`).

## Main definitions

* `TauCeti.SmoothForm.isotopyStabilizer σ`: the final diffeomorphisms of the diffeotopies
  preserving `σ` at every time.

## Main results

* `TauCeti.SmoothForm.isotopyStabilizer_le_diffeomorphStabilizer`: these preserve `σ`.
* `TauCeti.SmoothForm.mul_mul_inv_mem_isotopyStabilizer`: conjugation by an element of the
  stabilizer preserves the subgroup.
* `TauCeti.SmoothForm.normal_isotopyStabilizer_subgroupOf`: the subgroup is normal in the
  stabilizer of `σ`.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {σ : SmoothForm J M F k}

/-- The **isotopy stabilizer** of a smooth form `σ`: the final diffeomorphisms `φ₁` of the smooth
diffeotopies `φ_t` all of whose time slices preserve `σ`. For a symplectic form these are the
symplectomorphisms joined to the identity by a smooth symplectic isotopy. -/
def isotopyStabilizer (σ : SmoothForm J M F k) : Subgroup (M ≃ₘ⟮J, J⟯ M) where
  carrier := {φ | ∃ Φ : Diffeotopy J ∞ M,
    (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ Φ.final = φ}
  one_mem' := ⟨Diffeotopy.refl J ∞ M, fun t ↦ by
    rw [Diffeotopy.timeSlice_refl]
    exact (diffeomorphStabilizer σ).one_mem, Diffeotopy.final_refl⟩
  mul_mem' := by
    rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
    exact ⟨Ψ.trans Φ, fun t ↦ by
      rw [Diffeotopy.timeSlice_trans, ← Diffeomorph.mul_def]
      exact (diffeomorphStabilizer σ).mul_mem (hΦ t) (hΨ t), by
      rw [Diffeotopy.final_trans, Diffeomorph.mul_def]⟩
  inv_mem' := by
    rintro _ ⟨Φ, hΦ, rfl⟩
    exact ⟨Φ.symm, fun t ↦ by
      rw [Diffeotopy.timeSlice_symm, ← Diffeomorph.inv_def]
      exact (diffeomorphStabilizer σ).inv_mem (hΦ t), by
      rw [Diffeotopy.final_symm, Diffeomorph.inv_def]⟩

/-- A diffeomorphism lies in the isotopy stabilizer of `σ` exactly when it is the final
diffeomorphism of a diffeotopy all of whose time slices preserve `σ`. -/
theorem mem_isotopyStabilizer {φ : M ≃ₘ⟮J, J⟯ M} :
    φ ∈ isotopyStabilizer σ ↔
      ∃ Φ : Diffeotopy J ∞ M, (∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) ∧ Φ.final = φ :=
  Iff.rfl

/-- The final diffeomorphism of a diffeotopy preserving `σ` at every time lies in the isotopy
stabilizer of `σ`. -/
theorem final_mem_isotopyStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) : Φ.final ∈ isotopyStabilizer σ :=
  ⟨Φ, hΦ, rfl⟩

/-- The final diffeomorphism of a diffeotopy preserving `σ` at every time preserves `σ`. -/
theorem final_mem_diffeomorphStabilizer {Φ : Diffeotopy J ∞ M}
    (hΦ : ∀ t, Φ.timeSlice t ∈ diffeomorphStabilizer σ) : Φ.final ∈ diffeomorphStabilizer σ := by
  rw [Diffeotopy.final_def]
  exact hΦ 1

/-- Diffeomorphisms isotopic to the identity through `σ`-preserving diffeomorphisms preserve
`σ`. -/
theorem isotopyStabilizer_le_diffeomorphStabilizer :
    isotopyStabilizer σ ≤ diffeomorphStabilizer σ := by
  rintro _ ⟨Φ, hΦ, rfl⟩
  exact final_mem_diffeomorphStabilizer hΦ

/-- Conjugating an element of the isotopy stabilizer of `σ` by an element `f` of the stabilizer
of `σ` gives an element of the isotopy stabilizer: if `φ_t` preserves `σ` at every time, so does
`f ∘ φ_t ∘ f⁻¹`. -/
theorem mul_mul_inv_mem_isotopyStabilizer {f φ : M ≃ₘ⟮J, J⟯ M}
    (hf : f ∈ diffeomorphStabilizer σ) (hφ : φ ∈ isotopyStabilizer σ) :
    f * φ * f⁻¹ ∈ isotopyStabilizer σ := by
  obtain ⟨Φ, hΦ, rfl⟩ := hφ
  refine ⟨Φ.transDiffeomorph f, fun t ↦ ?_, ?_⟩
  · rw [Diffeotopy.timeSlice_transDiffeomorph, ← Diffeomorph.diffCongr_apply,
      Diffeomorph.diffCongr_apply_eq_mul_mul_inv]
    exact (diffeomorphStabilizer σ).mul_mem ((diffeomorphStabilizer σ).mul_mem hf (hΦ t))
      ((diffeomorphStabilizer σ).inv_mem hf)
  · rw [Diffeotopy.final_transDiffeomorph, ← Diffeomorph.diffCongr_apply,
      Diffeomorph.diffCongr_apply_eq_mul_mul_inv]

/-- The isotopy stabilizer of `σ` is a normal subgroup of the stabilizer of `σ`. For a
symplectic form, the symplectomorphisms joined to the identity by a smooth symplectic isotopy form
a normal subgroup of `Symp(M, ω)`. -/
theorem normal_isotopyStabilizer_subgroupOf :
    ((isotopyStabilizer σ).subgroupOf (diffeomorphStabilizer σ)).Normal :=
  (Subgroup.normal_subgroupOf_iff isotopyStabilizer_le_diffeomorphStabilizer).2
    fun _ _ hφ hf ↦ mul_mul_inv_mem_isotopyStabilizer hf hφ

end SmoothForm

end TauCeti
