/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.RestrictScalars
public import TauCeti.LinearAlgebra.Determinant.Complex.Orientation
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Complex orientations of determinant lines of complex-linear maps

The determinant line `det (ker f) ⊗ (det (coker f))^*` (`LinearMap.detLine`) of a complex-linear
map `f` is formed from the kernel and cokernel of the underlying real-linear map. These are the
complex kernel and cokernel with their real structures (`LinearMap.kerRestrictScalarsEquiv`,
`LinearMap.cokerRestrictScalarsEquiv`), and `LinearMap.detLineRestrictScalarsEquiv` identifies the
two forms. An element of the determinant line is complex positive
(`LinearMap.IsComplexPositiveDetLine`) if it corresponds to a complex positive element
(`TauCeti.IsComplexPositiveTMulDual`); this is an orientation of the determinant line.

Under this identification, transport along a commuting square of real isomorphisms
(`LinearMap.detLineCongr`) is the transport along the induced isomorphisms of complex kernels and
cokernels (`LinearMap.detLineRestrictScalarsEquiv_detLineCongr`). It therefore preserves complex
positivity when the isomorphisms commute with `I`
(`LinearMap.IsComplexPositiveDetLine.detLineCongr`), and multiplies it by `(-1) ^ (k + c)` when
they anticommute with `I`, where `k` and `c` are the complex dimensions of the kernel and the
cokernel
(`LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`, from
`TauCeti.IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr`). The sign is `(-1)` to
the complex index `k - c`.

In Seiberg–Witten theory this is the complex factor of the determinant sign of charge
conjugation: the quaternionic structure of the spinors is a conjugate-linear intertwiner of the
Dirac operators of a `Spinᶜ` structure and of its conjugate, so it contributes `(-1)` to the
complex index of the Dirac operator. Charge conjugation negates both the domain and the target of
the real deformation operator on imaginary forms; that contributes `(-1)` to the sum of the
dimensions of its kernel and cokernel (`LinearMap.detLineCongr_neg_apply`).

## Main definitions

* `LinearMap.detLineRestrictScalarsEquiv`: the real determinant line of a complex-linear map is
  formed from its complex kernel and cokernel.
* `LinearMap.IsComplexPositiveDetLine`: the complex orientation of the determinant line of a
  complex-linear map.

## Main results

* `LinearMap.detLineRestrictScalarsEquiv_detLineCongr`: transport along a commuting square is
  transport along the induced isomorphisms of complex kernels and cokernels.
* `LinearMap.IsComplexPositiveDetLine.exists_pos_smul_eq`,
  `LinearMap.IsComplexPositiveDetLine.not_neg`,
  `LinearMap.isComplexPositiveDetLine_or_isComplexPositiveDetLine_neg`: complex positivity is an
  orientation of the determinant line.
* `LinearMap.IsComplexPositiveDetLine.detLineCongr`: complex-linear transport preserves the
  complex orientation of the determinant line of a complex-linear map.
* `LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`: conjugate-linear transport
  multiplies it by `(-1) ^ (k + c)`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Module TensorProduct Complex

namespace LinearMap

open TauCeti

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (f : M →ₗ[ℂ] N)

/-! ### The complex orientation of the determinant line of a complex-linear map -/

/-- The real determinant line `det (ker f) ⊗ (det (coker f))^*` of a complex-linear map, formed
from the kernel and cokernel of the underlying real-linear map (`LinearMap.detLine`), is the one
formed from the complex kernel and cokernel with their real structures. -/
def detLineRestrictScalarsEquiv :
    (f.restrictScalars ℝ).detLine ≃ₗ[ℝ]
      TauCeti.detLine ℝ (ker f) ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ (N ⧸ range f)) :=
  TensorProduct.congr (LinearEquiv.detLineCongr (f.kerRestrictScalarsEquiv ℝ).symm)
    (LinearEquiv.detLineCongr (f.cokerRestrictScalarsEquiv ℝ).symm).dualMap

@[simp]
theorem detLineRestrictScalarsEquiv_tmul (x : TauCeti.detLine ℝ (ker (f.restrictScalars ℝ)))
    (φ : Dual ℝ (TauCeti.detLine ℝ (N ⧸ range (f.restrictScalars ℝ)))) :
    f.detLineRestrictScalarsEquiv (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr (f.kerRestrictScalarsEquiv ℝ).symm x ⊗ₜ
        (φ ∘ₗ (LinearEquiv.detLineCongr (f.cokerRestrictScalarsEquiv ℝ).symm).toLinearMap) :=
  (rfl)

@[simp]
theorem detLineRestrictScalarsEquiv_symm_tmul (x : TauCeti.detLine ℝ (ker f))
    (φ : Dual ℝ (TauCeti.detLine ℝ (N ⧸ range f))) :
    f.detLineRestrictScalarsEquiv.symm (x ⊗ₜ φ) =
      LinearEquiv.detLineCongr (f.kerRestrictScalarsEquiv ℝ) x ⊗ₜ
        (φ ∘ₗ (LinearEquiv.detLineCongr (f.cokerRestrictScalarsEquiv ℝ)).toLinearMap) := by
  rw [LinearEquiv.symm_apply_eq, detLineRestrictScalarsEquiv_tmul,
    ← LinearEquiv.detLineCongr_symm, LinearEquiv.symm_apply_apply]
  simp [comp_assoc, ← LinearEquiv.detLineCongr_symm]

/-- An element of the real determinant line of a complex-linear map `f` is **complex positive** if
it corresponds to a complex positive element of `det (ker f) ⊗ (det (coker f))^*`, that is, to
`(b₀ ∧ I • b₀ ∧ ⋯) ⊗ φ` for a complex basis `b` of the kernel and a functional `φ` positive on
`c₀ ∧ I • c₀ ∧ ⋯` for complex bases `c` of the cokernel
(`LinearMap.isComplexPositiveDetLine_iff`). These are the complex orientations of the determinant
lines of complex-linear Fredholm operators, such as complex Dirac and Cauchy–Riemann operators. -/
def IsComplexPositiveDetLine (z : (f.restrictScalars ℝ).detLine) : Prop :=
  IsComplexPositiveTMulDual (f.detLineRestrictScalarsEquiv z)

variable {f} {z w : (f.restrictScalars ℝ).detLine}

/-- Complex positivity of the determinant line of a complex-linear map is complex positivity of
`det (ker f) ⊗ (det (coker f))^*` under `LinearMap.detLineRestrictScalarsEquiv`. -/
theorem isComplexPositiveDetLine_iff :
    f.IsComplexPositiveDetLine z ↔ IsComplexPositiveTMulDual (f.detLineRestrictScalarsEquiv z) :=
  Iff.rfl

variable (f) in
/-- The determinant line of a complex-linear map with finite-dimensional kernel and cokernel has
a complex positive element. -/
theorem exists_isComplexPositiveDetLine [FiniteDimensional ℂ (ker f)]
    [FiniteDimensional ℂ (N ⧸ range f)] :
    ∃ z : (f.restrictScalars ℝ).detLine, f.IsComplexPositiveDetLine z := by
  obtain ⟨t, ht⟩ := exists_isComplexPositiveTMulDual (E := ker f) (F := N ⧸ range f)
  exact ⟨f.detLineRestrictScalarsEquiv.symm t, by
    rwa [isComplexPositiveDetLine_iff, LinearEquiv.apply_symm_apply]⟩

/-- A positive multiple of a complex positive element of the determinant line of a complex-linear
map is complex positive. -/
theorem IsComplexPositiveDetLine.smul (hz : f.IsComplexPositiveDetLine z) {c : ℝ} (hc : 0 < c) :
    f.IsComplexPositiveDetLine (c • z) := by
  rw [isComplexPositiveDetLine_iff, map_smul]
  exact IsComplexPositiveTMulDual.smul hz hc

/-- A complex positive element of the determinant line of a complex-linear map is nonzero. -/
theorem IsComplexPositiveDetLine.ne_zero [FiniteDimensional ℂ (N ⧸ range f)]
    (hz : f.IsComplexPositiveDetLine z) : z ≠ 0 := by
  rintro rfl
  exact IsComplexPositiveTMulDual.ne_zero hz f.detLineRestrictScalarsEquiv.map_zero

/-- Two complex positive elements of the determinant line of a complex-linear map differ by a
positive factor. -/
theorem IsComplexPositiveDetLine.exists_pos_smul_eq [FiniteDimensional ℂ (N ⧸ range f)]
    (hz : f.IsComplexPositiveDetLine z) (hw : f.IsComplexPositiveDetLine w) :
    ∃ c : ℝ, 0 < c ∧ w = c • z := by
  obtain ⟨c, hc, hcw⟩ := IsComplexPositiveTMulDual.exists_pos_smul_eq hz hw
  exact ⟨c, hc, f.detLineRestrictScalarsEquiv.injective (by rw [hcw, map_smul])⟩

/-- The negative of a complex positive element of the determinant line of a complex-linear map is
not complex positive. -/
theorem IsComplexPositiveDetLine.not_neg [FiniteDimensional ℂ (N ⧸ range f)]
    (hz : f.IsComplexPositiveDetLine z) : ¬ f.IsComplexPositiveDetLine (-z) := by
  rw [isComplexPositiveDetLine_iff, map_neg f.detLineRestrictScalarsEquiv z]
  exact IsComplexPositiveTMulDual.not_neg hz

/-- Exactly one of `z` and `-z` is complex positive for each nonzero element `z` of the
determinant line of a complex-linear map with finite-dimensional kernel and cokernel; that at most
one is follows from `LinearMap.IsComplexPositiveDetLine.not_neg`. -/
theorem isComplexPositiveDetLine_or_isComplexPositiveDetLine_neg [FiniteDimensional ℂ (ker f)]
    [FiniteDimensional ℂ (N ⧸ range f)] (hz : z ≠ 0) :
    f.IsComplexPositiveDetLine z ∨ f.IsComplexPositiveDetLine (-z) := by
  rw [isComplexPositiveDetLine_iff, isComplexPositiveDetLine_iff,
    map_neg f.detLineRestrictScalarsEquiv z]
  exact isComplexPositiveTMulDual_or_isComplexPositiveTMulDual_neg
    (f.detLineRestrictScalarsEquiv.map_ne_zero_iff.2 hz)

/-! ### Transport along commuting squares -/

section Transport

variable {M' N' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N'] {f' : M' →ₗ[ℂ] N'}
  (e₁ : M ≃ₗ[ℝ] M') (e₂ : N ≃ₗ[ℝ] N')
  (h : f'.restrictScalars ℝ ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f.restrictScalars ℝ)

variable (f) in
/-- Under `LinearMap.detLineRestrictScalarsEquiv`, transport along a commuting square of real
isomorphisms is the isomorphism of determinant lines induced by the isomorphisms of complex
kernels and cokernels (`LinearMap.kerCongrOfComp`, `LinearMap.cokerCongrOfComp`). -/
theorem detLineRestrictScalarsEquiv_detLineCongr (z : (f.restrictScalars ℝ).detLine) :
    f'.detLineRestrictScalarsEquiv ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) =
      TensorProduct.congr (LinearEquiv.detLineCongr (kerCongrOfComp f e₁ e₂ h))
        (LinearEquiv.detLineCongr (cokerCongrOfComp f e₁ e₂ h)).symm.dualMap
        (f.detLineRestrictScalarsEquiv z) := by
  -- The kernel and cokernel isomorphisms induced by the square, read on either side.
  have hk : (e₁.ofSubmodules _ _ ((f.restrictScalars ℝ).map_ker_eq_ker_of_comp_eq e₁.surjective
      e₂.injective h)).trans (f'.kerRestrictScalarsEquiv ℝ).symm =
      (f.kerRestrictScalarsEquiv ℝ).symm.trans (kerCongrOfComp f e₁ e₂ h) :=
    LinearEquiv.ext fun x ↦ Subtype.ext (by simp only [LinearEquiv.trans_apply,
      coe_kerRestrictScalarsEquiv_symm_apply, coe_kerCongrOfComp_apply,
      LinearEquiv.ofSubmodules_apply])
  have hc : (f'.cokerRestrictScalarsEquiv ℝ).symm.trans (Submodule.Quotient.equiv _ _ e₂
      ((f.restrictScalars ℝ).map_range_eq_range_of_comp_eq e₁.surjective h)).symm =
      (cokerCongrOfComp f e₁ e₂ h).symm.trans (f.cokerRestrictScalarsEquiv ℝ).symm := by
    refine LinearEquiv.ext fun y ↦ ?_
    induction y using Submodule.Quotient.induction_on with
    | H y => simp [Submodule.Quotient.equiv_symm]
  -- The same identities between the induced isomorphisms of determinant lines.
  have hk' (x) := by
    simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply] using
      LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hk) x
  have hc' (w) := by
    simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply] using
      LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hc) w
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul x φ =>
    rw [detLineCongr_tmul, detLineRestrictScalarsEquiv_tmul, detLineRestrictScalarsEquiv_tmul,
      TensorProduct.congr_tmul, hk']
    congr 1
    exact LinearMap.ext fun w ↦ by
      simp only [LinearEquiv.dualMap_apply, comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.detLineCongr_symm, hc']

/-- Transport along a commuting square of real isomorphisms commuting with `I`, that is, of
complex-linear isomorphisms, preserves the complex orientation of the determinant line of a
complex-linear map. -/
theorem IsComplexPositiveDetLine.detLineCongr {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z) (he₁ : ∀ x, e₁ (I • x) = I • e₁ x)
    (he₂ : ∀ y, e₂ (I • y) = I • e₂ y) :
    f'.IsComplexPositiveDetLine ((f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) := by
  set g₁ := kerCongrOfComp f e₁ e₂ h
  set g₂ := cokerCongrOfComp f e₁ e₂ h
  let G₁ : ker f ≃ₗ[ℂ] ker f' := .ofBijective
    (g₁.toLinearMap.complexOfMapISmul (kerCongrOfComp_smul f e₁ e₂ h he₁))
    (by simpa using g₁.bijective)
  let G₂ : (N ⧸ range f) ≃ₗ[ℂ] N' ⧸ range f' := .ofBijective
    (g₂.toLinearMap.complexOfMapISmul (cokerCongrOfComp_smul f e₁ e₂ h he₂))
    (by simpa using g₂.bijective)
  have hG₁ : G₁.restrictScalars ℝ = g₁ := LinearEquiv.ext fun _ ↦ by simp [G₁]
  have hG₂ : G₂.restrictScalars ℝ = g₂ := LinearEquiv.ext fun _ ↦ by simp [G₂]
  have := IsComplexPositiveTMulDual.congr_detLineCongr hz G₁ G₂
  rw [hG₁, hG₂] at this
  rw [isComplexPositiveDetLine_iff, detLineRestrictScalarsEquiv_detLineCongr]
  exact this

/-- **The determinant sign of a conjugate-linear transport.** Transport along a commuting square
of real isomorphisms anticommuting with `I`, that is, of conjugate-linear isomorphisms, maps a
complex positive element of the determinant line of `f` to `(-1) ^ (k + c)` times a complex
positive element of the determinant line of `f'`, where `k` and `c` are the complex dimensions of
the kernel and the cokernel of `f`. The sign is `(-1)` to the complex index `k - c`. -/
theorem IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr [FiniteDimensional ℂ (ker f)]
    [FiniteDimensional ℂ (N ⧸ range f)] {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z) (he₁ : ∀ x, e₁ (I • x) = -(I • e₁ x))
    (he₂ : ∀ y, e₂ (I • y) = -(I • e₂ y)) :
    f'.IsComplexPositiveDetLine ((-1 : ℝ) ^ (finrank ℂ (ker f) + finrank ℂ (N ⧸ range f)) •
      (f.restrictScalars ℝ).detLineCongr e₁ e₂ h z) := by
  have he₁' (x : M) : e₁ (I • x) = (-I) • e₁ x := by rw [he₁, neg_smul]
  have he₂' (y : N) : e₂ (I • y) = (-I) • e₂ y := by rw [he₂, neg_smul]
  rw [isComplexPositiveDetLine_iff, map_smul, detLineRestrictScalarsEquiv_detLineCongr]
  exact IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr hz _ _
    (fun x ↦ by rw [kerCongrOfComp_smul f e₁ e₂ h he₁' x, neg_smul])
    (fun y ↦ by rw [cokerCongrOfComp_smul f e₁ e₂ h he₂' y, neg_smul])

end Transport

end LinearMap
