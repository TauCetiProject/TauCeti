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
import TauCeti.Algebra.Module.ZLattice.Rank

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
* `TauCeti.ComplexTorus.realificationEquiv_baseChange_restrict`: the identification
  `ℝ ⊗[ℤ] Λ ≃ E` is natural in complex-linear maps `f : E → E'` with `f(Λ) ⊆ Λ'`.
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

/-- A lattice vector `x` corresponds to `1 ⊗ x` in the realification. -/
@[simp]
theorem realificationEquiv_symm_coe (x : Λ) :
    (realificationEquiv Λ).symm x = 1 ⊗ₜ x :=
  (ZLattice.isBaseChange_subtype ℝ Λ).equiv_symm_apply x

/-- The **complex structure of a complex torus** `E / Λ` on the realification of its lattice:
multiplication by `i` on `E`, transported along `realificationEquiv Λ`. -/
noncomputable def almostComplexStructure : AlmostComplexStructure (Hodge.Realification Λ) :=
  (AlmostComplexStructure.ofComplexModule E).transport (realificationEquiv Λ).symm

/-- Under `realificationEquiv Λ`, the complex structure of the torus is multiplication by `i`. -/
@[simp]
theorem realificationEquiv_almostComplexStructure (x : Hodge.Realification Λ) :
    realificationEquiv Λ (almostComplexStructure Λ x) = Complex.I • realificationEquiv Λ x := by
  simp [almostComplexStructure, AlmostComplexStructure.ofComplexModule_apply]

/-- Multiplication by `i` on `E` corresponds to the complex structure of the torus on the
realification. -/
theorem realificationEquiv_symm_smul_I (v : E) :
    (realificationEquiv Λ).symm (Complex.I • v) =
      almostComplexStructure Λ ((realificationEquiv Λ).symm v) := by
  rw [LinearEquiv.symm_apply_eq, realificationEquiv_almostComplexStructure,
    LinearEquiv.apply_symm_apply]

/-- The real extension `E_ℝ` of an integral bilinear form on `Λ`, as a real bilinear form on
`E = ℝ ⊗[ℤ] Λ`. -/
noncomputable def realForm (B : LinearMap.BilinForm ℤ Λ) : LinearMap.BilinForm ℝ E :=
  LinearMap.BilinForm.congr (realificationEquiv Λ) (B.baseChange ℝ)

/-- The real extension evaluates the base-changed form on the preimages in `ℝ ⊗[ℤ] Λ`. -/
theorem realForm_apply (B : LinearMap.BilinForm ℤ Λ) (v w : E) :
    realForm Λ B v w =
      B.baseChange ℝ ((realificationEquiv Λ).symm v) ((realificationEquiv Λ).symm w) :=
  LinearMap.BilinForm.congr_apply _ _ v w

/-- On lattice vectors, the real extension is the integral form. -/
@[simp]
theorem realForm_coe (B : LinearMap.BilinForm ℤ Λ) (x y : Λ) :
    realForm Λ B x y = B x y := by
  simp [realForm_apply, LinearMap.BilinForm.baseChange_tmul]

/-- **Riemann forms of a complex torus**: an integral form `B` on `Λ` is a Riemann form for the
complex torus `E / Λ` exactly when it is alternating and its real extension `E_ℝ` on `E` is
invariant under multiplication by `i` and satisfies `E_ℝ(i v, v) > 0` for `v ≠ 0`. -/
theorem isRiemannForm_iff (B : LinearMap.BilinForm ℤ Λ) :
    (almostComplexStructure Λ).IsRiemannForm B ↔
      B.IsAlt ∧ (∀ v w : E, realForm Λ B (Complex.I • v) (Complex.I • w) = realForm Λ B v w) ∧
        ∀ v : E, v ≠ 0 → 0 < realForm Λ B (Complex.I • v) v := by
  simp only [realForm_apply, realificationEquiv_symm_smul_I]
  constructor
  · rintro ⟨halt, hinv, hpos⟩
    exact ⟨halt, fun v w ↦ hinv _ _, fun v hv ↦ hpos _ ((LinearEquiv.map_ne_zero_iff _).mpr hv)⟩
  · rintro ⟨halt, hinv, hpos⟩
    refine ⟨halt, fun x y ↦ ?_, fun x hx ↦ ?_⟩
    · simpa only [LinearEquiv.symm_apply_apply] using
        hinv (realificationEquiv Λ x) (realificationEquiv Λ y)
    · simpa only [LinearEquiv.symm_apply_apply] using
        hpos (realificationEquiv Λ x) ((LinearEquiv.map_ne_zero_iff _).mpr hx)

/-- **The Hodge numbers of a complex torus**: the weight-one Hodge structure on `Λ` associated
with the complex structure of `E / Λ` has `h^{1,0} = h^{0,1} = dim_ℂ E`, and all other Hodge
numbers vanish. -/
theorem hodgeNumber_latticeHodgeStructure {Λℂ : Type*} [AddCommGroup Λℂ] [Module ℂ Λℂ]
    {ιℂ : Λ →ₗ[ℤ] Λℂ} (hℂ : IsBaseChange ℂ ιℂ) (p : ℤ) :
    ((almostComplexStructure Λ).latticeHodgeStructure hℂ).hodgeNumber p =
      if p = 0 ∨ p = 1 then finrank ℂ E else 0 := by
  have := ZLattice.module_free ℝ Λ
  have h := (almostComplexStructure Λ).two_mul_latticeHodgeStructure_hodgeNumber hℂ p
  rw [ZLattice.finrank_eq_two_mul_finrank_complex] at h
  split_ifs at h ⊢ <;> omega

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] [IsZLattice ℝ Λ']

/-- **Naturality of `realificationEquiv`**: for a complex-linear map `f : E → E'` carrying `Λ`
into `Λ'`, the real extension of its restriction `Λ → Λ'` corresponds to `f` under the
identifications `ℝ ⊗[ℤ] Λ ≃ E` and `ℝ ⊗[ℤ] Λ' ≃ E'`. -/
@[simp]
theorem realificationEquiv_baseChange_restrict (f : E →ₗ[ℂ] E')
    (hf : ∀ x ∈ Λ, f.restrictScalars ℤ x ∈ Λ') (x : Hodge.Realification Λ) :
    realificationEquiv Λ' (LinearMap.baseChange ℝ ((f.restrictScalars ℤ).restrict hf) x) =
      f (realificationEquiv Λ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x => simp
  | add x y hx hy => simp [hx, hy]

/-- **Complex-linear maps of tori give complex-linear maps of realifications**: if a complex-linear
map `f : E → E'` carries `Λ` into `Λ'`, the real extension of its restriction `Λ → Λ'` is complex
linear for the complex structures of the two tori. -/
theorem isComplexLinearMap_baseChange (f : E →ₗ[ℂ] E')
    (hf : ∀ x ∈ Λ, f.restrictScalars ℤ x ∈ Λ') :
    IsComplexLinearMap (almostComplexStructure Λ) (almostComplexStructure Λ')
      (LinearMap.baseChange ℝ ((f.restrictScalars ℤ).restrict hf)) := by
  rw [isComplexLinearMap_iff_apply]
  intro x
  apply (realificationEquiv Λ').injective
  simp

end TauCeti.ComplexTorus
