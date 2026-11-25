/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.BaseChange
public import TauCeti.Geometry.Hodge.WeightOne.RiemannForm
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# The Hodge datum of a complex torus

Let `E` be a finite-dimensional complex vector space and `Λ ⊆ E` a full lattice, so that `E / Λ`
is a complex torus. Since `Λ` spans `E` over `ℝ`, the realification `ℝ ⊗[ℤ] Λ` of `Λ` is
identified with `E` (`ZLattice.isBaseChange_subtype`), and multiplication by `i` on `E` becomes an
almost complex structure `J` on `ℝ ⊗[ℤ] Λ`
(`TauCeti.ComplexTorus.almostComplexStructure`). This is the datum `(Λ, J)` to which Riemann
forms (`TauCeti.AlmostComplexStructure.IsRiemannForm`) and the weight-one Hodge structure
`TauCeti.AlmostComplexStructure.latticeHodgeStructure` apply for the complex torus `E / Λ`.

## Main declarations

* `TauCeti.ComplexTorus.realificationEquiv`: the identification `ℝ ⊗[ℤ] Λ ≃ E`.
* `TauCeti.ComplexTorus.almostComplexStructure`: multiplication by `i`, transported to
  `ℝ ⊗[ℤ] Λ`.
* `TauCeti.ComplexTorus.realForm`: the real extension of an integral form on `Λ`, as a real
  bilinear form on `E`.

## Main results

* `TauCeti.ComplexTorus.isRiemannForm_iff`: an integral form on `Λ` is a Riemann form for the
  complex torus exactly when it is alternating and its real extension `E_ℝ` on `E` satisfies
  `E_ℝ(i v, i w) = E_ℝ(v, w)` and `E_ℝ(i v, v) > 0` for `v ≠ 0`.
* `TauCeti.ComplexTorus.hodgeNumber_latticeHodgeStructure`: the Hodge numbers of the associated
  weight-one Hodge structure are `h^{1,0} = h^{0,1} = dim_ℂ E`.
* `TauCeti.ComplexTorus.isComplexLinearMap_baseChange`: a complex-linear map `f : E → E'` with
  `f(Λ) ⊆ Λ'` is complex linear for the two structures `J` on the realifications.

## References

* C. Birkenhake, H. Lange, *Complex Abelian Varieties*, §§1.1, 4.1, for complex tori, their
  lattices and Riemann forms.
-/

public section

open Module TensorProduct

namespace TauCeti.ComplexTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- The realification `ℝ ⊗[ℤ] Λ` of a full lattice `Λ ⊆ E` is identified with `E`, by
`r ⊗ x ↦ r • x`. -/
noncomputable def realificationEquiv : Hodge.Realification Λ ≃ₗ[ℝ] E :=
  (ZLattice.isBaseChange_subtype ℝ Λ).equiv

@[simp]
theorem realificationEquiv_tmul (r : ℝ) (x : Λ) :
    realificationEquiv Λ (r ⊗ₜ x) = r • (x : E) :=
  (ZLattice.isBaseChange_subtype ℝ Λ).equiv_tmul r x

/-- The **complex structure of a complex torus** `E / Λ` on the realification of its lattice:
multiplication by `i` on `E`, transported along `realificationEquiv Λ`. -/
noncomputable def almostComplexStructure : AlmostComplexStructure (Hodge.Realification Λ) :=
  (AlmostComplexStructure.ofComplexModule E).transport (realificationEquiv Λ).symm

/-- Under `realificationEquiv Λ`, the complex structure of the torus is multiplication by `i`. -/
@[simp]
theorem realificationEquiv_almostComplexStructure (x : Hodge.Realification Λ) :
    realificationEquiv Λ (almostComplexStructure Λ x) = Complex.I • realificationEquiv Λ x := by
  simp [almostComplexStructure, AlmostComplexStructure.ofComplexModule_apply]

/-- The real extension `E_ℝ` of an integral bilinear form on `Λ`, as a real bilinear form on
`E = ℝ ⊗[ℤ] Λ`. -/
noncomputable def realForm (B : LinearMap.BilinForm ℤ Λ) : LinearMap.BilinForm ℝ E :=
  (B.baseChange ℝ).compl₁₂ (realificationEquiv Λ).symm.toLinearMap
    (realificationEquiv Λ).symm.toLinearMap

/-- On lattice vectors, the real extension is the integral form. -/
@[simp]
theorem realForm_coe (B : LinearMap.BilinForm ℤ Λ) (x y : Λ) :
    realForm Λ B x y = B x y := by
  have hx : (realificationEquiv Λ).symm x = 1 ⊗ₜ x := by
    rw [LinearEquiv.symm_apply_eq, realificationEquiv_tmul, one_smul]
  have hy : (realificationEquiv Λ).symm y = 1 ⊗ₜ y := by
    rw [LinearEquiv.symm_apply_eq, realificationEquiv_tmul, one_smul]
  simp [realForm, hx, hy, LinearMap.BilinForm.baseChange_tmul]

/-- **Riemann forms of a complex torus**: an integral form `B` on `Λ` is a Riemann form for the
complex torus `E / Λ` exactly when it is alternating and its real extension `E_ℝ` on `E` is
invariant under multiplication by `i` and satisfies `E_ℝ(i v, v) > 0` for `v ≠ 0`. -/
theorem isRiemannForm_iff (B : LinearMap.BilinForm ℤ Λ) :
    (almostComplexStructure Λ).IsRiemannForm B ↔
      B.IsAlt ∧ (∀ v w : E, realForm Λ B (Complex.I • v) (Complex.I • w) = realForm Λ B v w) ∧
        ∀ v : E, v ≠ 0 → 0 < realForm Λ B (Complex.I • v) v := by
  have hJ (v : E) : (realificationEquiv Λ).symm (Complex.I • v) =
      almostComplexStructure Λ ((realificationEquiv Λ).symm v) := by
    rw [LinearEquiv.symm_apply_eq, realificationEquiv_almostComplexStructure,
      LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨halt, hinv, hpos⟩
    refine ⟨halt, fun v w ↦ ?_, fun v hv ↦ ?_⟩
    · simp only [realForm, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hJ, hinv]
    · simp only [realForm, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hJ]
      exact hpos _ ((LinearEquiv.map_ne_zero_iff _).mpr hv)
  · rintro ⟨halt, hinv, hpos⟩
    refine ⟨halt, fun x y ↦ ?_, fun x hx ↦ ?_⟩
    · have := hinv (realificationEquiv Λ x) (realificationEquiv Λ y)
      simpa only [realForm, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hJ,
        LinearEquiv.symm_apply_apply] using this
    · have := hpos (realificationEquiv Λ x) ((LinearEquiv.map_ne_zero_iff _).mpr hx)
      simpa only [realForm, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, hJ,
        LinearEquiv.symm_apply_apply] using this

/-- The rank of a full lattice in `E` is twice the complex dimension of `E`. -/
theorem finrank_lattice :
    finrank ℤ Λ = 2 * finrank ℂ E := by
  rw [ZLattice.rank ℝ Λ, ← Module.finrank_mul_finrank ℝ ℂ E, Complex.finrank_real_complex]

/-- **The Hodge numbers of a complex torus**: the weight-one Hodge structure on `Λ` associated
with the complex structure of `E / Λ` has `h^{1,0} = h^{0,1} = dim_ℂ E`, and all other Hodge
numbers vanish. -/
theorem hodgeNumber_latticeHodgeStructure {Λℂ : Type*} [AddCommGroup Λℂ] [Module ℂ Λℂ]
    {ιℂ : Λ →ₗ[ℤ] Λℂ} (hℂ : IsBaseChange ℂ ιℂ) (p : ℤ) :
    ((almostComplexStructure Λ).latticeHodgeStructure hℂ).hodgeNumber p =
      if p = 0 ∨ p = 1 then finrank ℂ E else 0 := by
  have := ZLattice.module_free ℝ Λ
  have h := (almostComplexStructure Λ).two_mul_latticeHodgeStructure_hodgeNumber hℂ p
  rw [finrank_lattice] at h
  split_ifs at h ⊢ <;> omega

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] [IsZLattice ℝ Λ']

/-- **Complex-linear maps of tori give complex-linear maps of realifications**: if a complex-linear
map `f : E → E'` carries `Λ` into `Λ'`, the real extension of its restriction `Λ → Λ'` is complex
linear for the complex structures of the two tori. -/
theorem isComplexLinearMap_baseChange (f : E →ₗ[ℂ] E') (hf : ∀ x ∈ Λ, f x ∈ Λ') :
    IsComplexLinearMap (almostComplexStructure Λ) (almostComplexStructure Λ')
      (LinearMap.baseChange ℝ ((f.restrictScalars ℤ).restrict hf)) := by
  have hcomm (x : Hodge.Realification Λ) : realificationEquiv Λ'
      (LinearMap.baseChange ℝ ((f.restrictScalars ℤ).restrict hf) x) =
        f (realificationEquiv Λ x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x => simp; rfl
    | add x y hx hy => simp [hx, hy]
  rw [isComplexLinearMap_iff_apply]
  intro x
  apply (realificationEquiv Λ').injective
  rw [hcomm, realificationEquiv_almostComplexStructure, realificationEquiv_almostComplexStructure,
    hcomm, map_smul]

end TauCeti.ComplexTorus
