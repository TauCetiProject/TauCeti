/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Torus
public import TauCeti.Geometry.Manifold.VectorField.Torus
public import TauCeti.Geometry.Symplectic.Flux.Flow

/-!
# The flux of translation loops of a two-torus

Let `T² = AddCircle (p 0) × AddCircle (p 1)`, written as `∀ i : Fin 2, AddCircle (p i)`, carry
the area form `ω = A dt₀ ∧ dt₁` for a real constant `A`, where `dt₀, dt₁` are the coordinate time
forms (`TauCeti.torusTimeForm`) and `dt₀ ∧ dt₁` is the volume form of the torus
(`TauCeti.torusVolumeForm`). Running the constant vector field `c = c₀ ∂₀ + c₁ ∂₁`
(`TauCeti.torusConstVectorField`) for unit time gives the translation isotopy
`(t, x) ↦ x + [t c]`. Contracting the area form with `c` gives the closed one-form

`ι_c ω = A (c₀ dt₁ - c₁ dt₀)`

(`TauCeti.interiorₗ_torusConstVectorField_smul_torusVolumeForm`), so `c` is a symplectic vector
field and every map of the translation isotopy preserves `ω`. Its flux is therefore the class

`Flux = A (c₀ [dt₁] - c₁ [dt₀]) ∈ H¹_dR(T²)`

(`TauCeti.Diffeotopy.flux_globalFlowDiffeotopy_torusConstVectorField`). For the coordinate
directions this reads `Flux(∂₀-loop) = A [dt₁]` and `Flux(∂₁-loop) = -A [dt₀]`, which fixes the
sign conventions.

When `c` lies in the period lattice `p₀ ℤ × p₁ ℤ`, the translation isotopy is a loop of
symplectomorphisms based at the identity. Choosing `c = (n p₀, -m p₁)` shows that for all integers
`m` and `n` the class

`A (m p₁ [dt₀] + n p₀ [dt₁]) = A p₀ p₁ (m [dt₀ / p₀] + n [dt₁ / p₁])`

is the flux of a symplectic loop (`TauCeti.Diffeotopy.exists_flux_eq_torusVolume`). The classes
`[dt_i / p_i]` integrate to `1` around the `i`-th coordinate circle and to `0` around the other,
so they are the integral basis dual to the coordinate circles, and `A p₀ p₁` is the total
`ω`-area of the torus. Thus the flux group of `(T², ω)`, the image of the flux on loops of
symplectomorphisms, contains the total area times the integral lattice spanned by these classes.
On the unit torus `(ℝ / ℤ)²` this is the lattice `A ℤ [dt₀] + A ℤ [dt₁]`.

## Main results

* `TauCeti.interiorₗ_torusConstVectorField_smul_torusVolumeForm`: `ι_c (A dt₀ ∧ dt₁)` is
  `A (c₀ dt₁ - c₁ dt₀)`.
* `TauCeti.torusConstVectorField_mem_symplecticVectorFields`: constant vector fields are
  symplectic for every constant area form.
* `TauCeti.Diffeotopy.flux_globalFlowDiffeotopy_torusConstVectorField`: the flux of the
  translation isotopy with velocity `c` is `A (c₀ [dt₁] - c₁ [dt₀])`.
* `TauCeti.Diffeotopy.exists_flux_eq_torusVolume`: every class `A (m p₁ [dt₀] + n p₀ [dt₁])` with
  `m n : ℤ` is the flux of a loop of symplectomorphisms based at the identity.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism and the flux group).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)]

/-- **Contraction of a constant area form with a constant vector field.** On the two-torus, the
contraction of the area form `A dt₀ ∧ dt₁` with the constant vector field `c` is the closed
one-form `A (c₀ dt₁ - c₁ dt₀)`. -/
theorem interiorₗ_torusConstVectorField_smul_torusVolumeForm (A : ℝ) (c : Fin 2 → ℝ) :
    SmoothTwoForm.interiorₗ (A • torusVolumeForm p) (torusConstVectorField p c) =
      A • (c 0 • torusTimeForm p 1 - c 1 • torusTimeForm p 0) := by
  ext x v
  simp only [SmoothTwoForm.coe_interiorₗ, RoughForm.interior_apply, Submodule.coe_smul,
    Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.sub_apply, torusVolumeForm_apply, torusTimeForm_apply,
    Matrix.det_fin_two, torusConstVectorField_apply]
  -- The tangent vectors live in `TangentSpace`, a synonym of `Fin 2 → ℝ`, which blocks `simp`
  -- from evaluating `Matrix.vecCons` directly.
  have h0 : Matrix.vecCons (α := TangentSpace (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x) c v 0 =
      c := Matrix.cons_val_zero c v
  have h1 : Matrix.vecCons (α := TangentSpace (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) x) c v 1 =
      v 0 := Matrix.cons_val_one c v
  simp only [Matrix.of_apply, smul_eq_mul, h0, h1]
  ring

/-- **Constant vector fields are symplectic.** On the two-torus, every constant vector field has
closed contraction with every constant area form `A dt₀ ∧ dt₁`. -/
theorem torusConstVectorField_mem_symplecticVectorFields (A : ℝ) (c : Fin 2 → ℝ) :
    torusConstVectorField p c ∈ SmoothTwoForm.symplecticVectorFields (A • torusVolumeForm p) := by
  rw [SmoothTwoForm.mem_symplecticVectorFields_iff, ← SmoothTwoForm.coe_interiorₗ,
    interiorₗ_torusConstVectorField_smul_torusVolumeForm, ← mem_closedForms]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.smul_mem _ _ (by simpa using (torusTimeClosedForm p 1).2))
    (Submodule.smul_mem _ _ (by simpa using (torusTimeClosedForm p 0).2)))

namespace Diffeotopy

/-- **The flux of a translation isotopy of the two-torus.** For the area form `A dt₀ ∧ dt₁`, the
isotopy `(t, x) ↦ x + [t c]` which runs the constant vector field `c` for unit time has flux
`A (c₀ [dt₁] - c₁ [dt₀])`. -/
theorem flux_globalFlowDiffeotopy_torusConstVectorField (A : ℝ) (c : Fin 2 → ℝ)
    (hΦ : (globalFlowDiffeotopy le_top (torusConstVectorField p c).contMDiff
        (isCompleteVectorField_torusConstVectorField p c) 1).final ∈
      SmoothForm.diffeomorphStabilizer (A • torusVolumeClosedForm p).1) :
    (globalFlowDiffeotopy le_top (torusConstVectorField p c).contMDiff
        (isCompleteVectorField_torusConstVectorField p c) 1).flux
        (A • torusVolumeClosedForm p) hΦ =
      A • (c 0 • deRhamCohomology.mk _ 1 (torusTimeClosedForm p 1) -
        c 1 • deRhamCohomology.mk _ 1 (torusTimeClosedForm p 0)) := by
  have hσ : (A • torusVolumeClosedForm p).1 = A • torusVolumeForm p := by simp
  have hX : torusConstVectorField p c ∈
      SmoothTwoForm.symplecticVectorFields (A • torusVolumeClosedForm p).1 := by
    rw [hσ]
    exact torusConstVectorField_mem_symplecticVectorFields p A c
  rw [flux_globalFlowDiffeotopy _ hX, one_smul, SmoothTwoForm.interiorClass_apply, ← map_smul,
    ← map_smul, ← map_sub, ← map_smul]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_sub, coe_torusTimeClosedForm, hσ]
  exact interiorₗ_torusConstVectorField_smul_torusVolumeForm p A c

/-- **Integral translation loops realize the area lattice as fluxes.** On the two-torus with area
form `ω = A dt₀ ∧ dt₁`, for all integers `m` and `n` there is a loop of symplectomorphisms based
at the identity, the translation isotopy with velocity `(n p₀, -m p₁)`, whose flux is
`A (m p₁ [dt₀] + n p₀ [dt₁])`. These are the total area `A p₀ p₁` times the integer combinations
of the classes `[dt_i / p_i]` dual to the coordinate circles. -/
theorem exists_flux_eq_torusVolume (A : ℝ) (m n : ℤ) :
    ∃ (Φ : Diffeotopy (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞ (∀ i, AddCircle (p i)))
      (hΦ : Φ.final ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeClosedForm p).1),
      (∀ t, Φ.timeSlice t ∈ SmoothForm.diffeomorphStabilizer (A • torusVolumeClosedForm p).1) ∧
      Φ.final = Diffeomorph.refl _ _ _ ∧
      Φ.flux (A • torusVolumeClosedForm p) hΦ =
        A • ((m * p 1) • deRhamCohomology.mk _ 1 (torusTimeClosedForm p 0) +
          (n * p 0) • deRhamCohomology.mk _ 1 (torusTimeClosedForm p 1)) := by
  let c : Fin 2 → ℝ := ![n * p 0, -(m * p 1)]
  have hX : torusConstVectorField p c ∈
      SmoothTwoForm.symplecticVectorFields (A • torusVolumeClosedForm p).1 := by
    have hσ : (A • torusVolumeClosedForm p).1 = A • torusVolumeForm p := by simp
    rw [hσ]
    exact torusConstVectorField_mem_symplecticVectorFields p A c
  have hslice := timeSlice_globalFlowDiffeotopy_mem_diffeomorphStabilizer
    ((SmoothForm.isClosed_def _).2 ((mem_closedForms _ _).1 (A • torusVolumeClosedForm p).2)) hX
    (isCompleteVectorField_torusConstVectorField p c) 1
  have hloop : ∀ i, c i ∈ AddSubgroup.zmultiples (p i) := by
    intro i
    fin_cases i
    · exact ⟨n, by simp [c]⟩
    · exact ⟨-m, by simp [c]⟩
  refine ⟨_, by rw [final_def]; exact hslice 1, hslice,
    (final_globalFlowDiffeotopy_torusConstVectorField_eq_refl_iff p c).2 hloop, ?_⟩
  rw [flux_globalFlowDiffeotopy_torusConstVectorField]
  simp only [c, Matrix.cons_val_zero, Matrix.cons_val_one, neg_smul, sub_neg_eq_add]
  rw [add_comm]

end Diffeotopy

end TauCeti
