/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.LinearMap.RestrictScalars
public import TauCeti.LinearAlgebra.Determinant.Complex.Orientation
public import TauCeti.LinearAlgebra.Determinant.Endomorphism
import TauCeti.LinearAlgebra.Complex.Finrank
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
the complex index `k - c`. The same holds for isomorphisms of kernels and cokernels that do not come
from a commuting square, such as identifications of the kernel and cokernel of a Fredholm operator
with those of a finite-dimensional reduction (`LinearMap.detLineCongrKerCoker`): if they commute
with `I`, they preserve complex positivity
(`LinearMap.IsComplexPositiveDetLine.detLineCongrKerCoker`).

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

* `LinearMap.detLineRestrictScalarsEquiv_eq_congr`,
  `LinearMap.detLineRestrictScalarsEquiv_symm_eq_congr`: the identification is the transport along
  the identifications of the real and complex kernels and cokernels.
* `LinearMap.detLineRestrictScalarsEquiv_detLineCongr`: transport along a commuting square is
  transport along the induced isomorphisms of complex kernels and cokernels.
* `LinearMap.IsComplexPositiveDetLine.exists_pos_smul_eq`,
  `LinearMap.IsComplexPositiveDetLine.not_neg`,
  `LinearMap.isComplexPositiveDetLine_or_isComplexPositiveDetLine_neg`: complex positivity is an
  orientation of the determinant line.
* `LinearMap.isComplexPositiveDetLine_detLineEquivOfBijective_symm_one`: for a bijective map the
  complex orientation is the orientation given by bijectivity.
* `LinearMap.IsComplexPositiveDetLine.detLineCongr`: complex-linear transport preserves the
  complex orientation of the determinant line of a complex-linear map.
* `LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`: conjugate-linear transport
  multiplies it by `(-1) ^ (k + c)`.
* `LinearMap.detLineRestrictScalarsEquiv_detLineCongrKerCoker`,
  `LinearMap.IsComplexPositiveDetLine.detLineCongrKerCoker`: the same for isomorphisms of kernels
  and cokernels commuting with `I`.
* `LinearMap.isComplexPositiveDetLine_detLineEndGenerator`: the normalized generator of the
  determinant line of a complex-linear endomorphism (`LinearMap.detLineEndGenerator`) is complex
  positive.

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

theorem detLineRestrictScalarsEquiv_def :
    f.detLineRestrictScalarsEquiv =
      TensorProduct.congr (LinearEquiv.detLineCongr (f.kerRestrictScalarsEquiv ℝ).symm)
        (LinearEquiv.detLineCongr (f.cokerRestrictScalarsEquiv ℝ).symm).dualMap :=
  (rfl)

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

/-- `LinearMap.detLineRestrictScalarsEquiv` is the transport along the identifications of the
real kernel and cokernel with the complex ones. -/
theorem detLineRestrictScalarsEquiv_eq_congr :
    f.detLineRestrictScalarsEquiv = TensorProduct.congr
      (f.kerRestrictScalarsEquiv ℝ).symm.detLineCongr
      (f.cokerRestrictScalarsEquiv ℝ).symm.detLineCongr.dualMap :=
  (rfl)

/-- The inverse of `LinearMap.detLineRestrictScalarsEquiv` is the transport along the
identifications of the complex kernel and cokernel with the real ones. -/
theorem detLineRestrictScalarsEquiv_symm_eq_congr :
    f.detLineRestrictScalarsEquiv.symm = TensorProduct.congr
      (f.kerRestrictScalarsEquiv ℝ).detLineCongr
      (f.cokerRestrictScalarsEquiv ℝ).symm.detLineCongr.symm.dualMap := by
  rw [detLineRestrictScalarsEquiv_eq_congr, TensorProduct.congr_symm,
    LinearEquiv.detLineCongr_symm, LinearEquiv.symm_symm, LinearEquiv.dualMap_symm]

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

/-- **The complex orientation of a bijective complex-linear map** is the orientation given by
bijectivity: kernel and cokernel vanish, and the element `1` of the determinant line under
`LinearMap.detLineEquivOfBijective` is complex positive. -/
theorem isComplexPositiveDetLine_detLineEquivOfBijective_symm_one
    (hf : Function.Bijective (f.restrictScalars ℝ)) :
    f.IsComplexPositiveDetLine ((detLineEquivOfBijective hf).symm 1) := by
  have hf' : Function.Bijective f := by simpa using hf
  have : Subsingleton (ker f) := Submodule.subsingleton_iff_eq_bot.2 (ker_eq_bot.2 hf'.1)
  have : Subsingleton (N ⧸ range f) :=
    Submodule.Quotient.subsingleton_iff.2 (range_eq_top.2 hf'.2)
  rw [detLineEquivOfBijective_symm_one_eq_ιMulti_tmul, isComplexPositiveDetLine_iff,
    detLineRestrictScalarsEquiv_tmul, LinearEquiv.detLineCongr_ιMulti]
  refine (isComplexPositive_ιMulti_of_subsingleton _).isComplexPositiveTMulDual_tmul
    ((isComplexPositive_ιMulti_of_subsingleton 0).isComplexPositiveDual_of_apply_eq_one ?_)
  simp

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

section TransportKerCoker

variable {M' N' : Type*} [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N'] {f' : M' →ₗ[ℂ] N'}

variable (f) in
/-- Under `LinearMap.detLineRestrictScalarsEquiv`, the isomorphism of determinant lines induced by
real isomorphisms `e₁` of kernels and `e₂` of cokernels (`LinearMap.detLineCongrKerCoker`) is the
one induced by the same isomorphisms read on the complex kernels and cokernels. -/
theorem detLineRestrictScalarsEquiv_detLineCongrKerCoker
    (e₁ : ker (f.restrictScalars ℝ) ≃ₗ[ℝ] ker (f'.restrictScalars ℝ))
    (e₂ : (N ⧸ range (f.restrictScalars ℝ)) ≃ₗ[ℝ] N' ⧸ range (f'.restrictScalars ℝ))
    (z : (f.restrictScalars ℝ).detLine) :
    f'.detLineRestrictScalarsEquiv (detLineCongrKerCoker e₁ e₂ z) =
      TensorProduct.congr (LinearEquiv.detLineCongr
          (((f.kerRestrictScalarsEquiv ℝ).trans e₁).trans (f'.kerRestrictScalarsEquiv ℝ).symm))
        (LinearEquiv.detLineCongr (((f.cokerRestrictScalarsEquiv ℝ).symm.trans e₂).trans
          (f'.cokerRestrictScalarsEquiv ℝ))).symm.dualMap
        (f.detLineRestrictScalarsEquiv z) := by
  set g₁ := ((f.kerRestrictScalarsEquiv ℝ).trans e₁).trans (f'.kerRestrictScalarsEquiv ℝ).symm
  set g₂ := ((f.cokerRestrictScalarsEquiv ℝ).symm.trans e₂).trans (f'.cokerRestrictScalarsEquiv ℝ)
  -- The kernel and cokernel identifications, composed with the transport, on each side.
  have hk : (f.kerRestrictScalarsEquiv ℝ).symm.trans g₁ =
      e₁.trans (f'.kerRestrictScalarsEquiv ℝ).symm :=
    LinearEquiv.ext fun x ↦ by simp only [g₁, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hc : g₂.symm.trans (f.cokerRestrictScalarsEquiv ℝ).symm =
      (f'.cokerRestrictScalarsEquiv ℝ).symm.trans e₂.symm :=
    LinearEquiv.ext fun y ↦ by
      simp only [g₂, LinearEquiv.trans_apply, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.symm_apply_apply]
  have hk' (x) := by
    simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply] using
      LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hk) x
  have hc' (w) := by
    simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply] using
      LinearEquiv.congr_fun (congrArg LinearEquiv.detLineCongr hc) w
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [LinearEquiv.map_add, LinearEquiv.map_add, ha, hb, LinearEquiv.map_add,
      LinearEquiv.map_add]
  | tmul x φ =>
    rw [detLineCongrKerCoker_tmul, detLineRestrictScalarsEquiv_tmul,
      detLineRestrictScalarsEquiv_tmul, TensorProduct.congr_tmul, ← hk']
    congr 1
    exact LinearMap.ext fun w ↦ by
      simp only [LinearEquiv.dualMap_apply, comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.detLineCongr_symm, hc']

/-- **Transport along isomorphisms of kernels and cokernels commuting with `I`** preserves the
complex orientation. Let `e₁` and `e₂` be real isomorphisms of the kernels and of the cokernels
of the real maps underlying complex-linear maps `f` and `f'`, which need not come from a
commuting square of the ambient spaces (`LinearMap.detLineCongrKerCoker`). If they commute with
multiplication by `I`, read on representatives in the ambient spaces, the induced isomorphism of
determinant lines maps complex positive elements to complex positive elements. -/
theorem IsComplexPositiveDetLine.detLineCongrKerCoker {z : (f.restrictScalars ℝ).detLine}
    (hz : f.IsComplexPositiveDetLine z)
    (e₁ : ker (f.restrictScalars ℝ) ≃ₗ[ℝ] ker (f'.restrictScalars ℝ))
    (e₂ : (N ⧸ range (f.restrictScalars ℝ)) ≃ₗ[ℝ] N' ⧸ range (f'.restrictScalars ℝ))
    (he₁ : ∀ x y : ker (f.restrictScalars ℝ), (x : M) = I • (y : M) →
      (e₁ x : M') = I • (e₁ y : M'))
    (he₂ : ∀ (x : N) (y : N'), e₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      e₂ (Submodule.Quotient.mk (I • x)) = Submodule.Quotient.mk (I • y)) :
    f'.IsComplexPositiveDetLine (detLineCongrKerCoker e₁ e₂ z) := by
  -- The isomorphisms read on the complex kernels and cokernels commute with `I`.
  set g₁ := ((f.kerRestrictScalarsEquiv ℝ).trans e₁).trans (f'.kerRestrictScalarsEquiv ℝ).symm
  set g₂ := ((f.cokerRestrictScalarsEquiv ℝ).symm.trans e₂).trans (f'.cokerRestrictScalarsEquiv ℝ)
  have hg₁ (x : ker f) : g₁ (I • x) = I • g₁ x := by
    have := he₁ (f.kerRestrictScalarsEquiv ℝ (I • x)) (f.kerRestrictScalarsEquiv ℝ x)
      (by simp only [coe_kerRestrictScalarsEquiv_apply, Submodule.coe_smul])
    refine Subtype.ext ?_
    simp only [g₁, LinearEquiv.trans_apply, coe_kerRestrictScalarsEquiv_symm_apply,
      Submodule.coe_smul]
    exact this
  have hg₂ (y : N ⧸ range f) : g₂ (I • y) = I • g₂ y := by
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e₂ (Submodule.Quotient.mk x))
      have hIy := he₂ x y hy.symm
      simp only [g₂, LinearEquiv.trans_apply, ← Submodule.Quotient.mk_smul,
        cokerRestrictScalarsEquiv_symm_mk, hIy, ← hy, cokerRestrictScalarsEquiv_mk]
  -- So they are complex-linear isomorphisms, which preserve complex positivity.
  let G₁ : ker f ≃ₗ[ℂ] ker f' :=
    .ofBijective (g₁.toLinearMap.complexOfMapISmul hg₁) (by simpa using g₁.bijective)
  let G₂ : (N ⧸ range f) ≃ₗ[ℂ] N' ⧸ range f' :=
    .ofBijective (g₂.toLinearMap.complexOfMapISmul hg₂) (by simpa using g₂.bijective)
  have hG₁ : G₁.restrictScalars ℝ = g₁ := LinearEquiv.ext fun _ ↦ by simp [G₁]
  have hG₂ : G₂.restrictScalars ℝ = g₂ := LinearEquiv.ext fun _ ↦ by simp [G₂]
  have := IsComplexPositiveTMulDual.congr_detLineCongr hz G₁ G₂
  rw [hG₁, hG₂] at this
  rw [isComplexPositiveDetLine_iff,
    _root_.LinearMap.detLineRestrictScalarsEquiv_detLineCongrKerCoker]
  exact this

end TransportKerCoker

section Endomorphism

/-! ### The normalized generator of a complex-linear endomorphism -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [FiniteDimensional ℝ V]

/-- **The normalized generator of a complex-linear endomorphism is complex positive.** For a
complex-linear endomorphism `f` of a finite-dimensional complex vector space, the normalized
generator `LinearMap.detLineEndGenerator` of the determinant line of the underlying real
endomorphism lies in its complex orientation. The sign normalizing the generator is `1` here,
because the kernel has even real dimension. -/
theorem isComplexPositiveDetLine_detLineEndGenerator (f : V →ₗ[ℂ] V) :
    f.IsComplexPositiveDetLine (f.restrictScalars ℝ).detLineEndGenerator := by
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  have : FiniteDimensional ℝ (ker f) := Module.Finite.equiv (f.kerRestrictScalarsEquiv ℝ).symm
  -- The kernel has even real dimension, so the normalized generator is the canonical element.
  have hk : Even (finrank ℝ (ker (f.restrictScalars ℝ)) * (finrank ℝ V + 1)) := by
    rw [← (f.kerRestrictScalarsEquiv ℝ).finrank_eq,
      TauCeti.finrank_real_eq_two_mul_finrank_complex (V := ker f)]
    exact (even_two_mul _).mul_right _
  -- The canonical element comes from `β ⊗ φ` with `β` complex positive and `φ β = 1`, and the
  -- four-term exact sequence of `f` respects complex orientations.
  obtain ⟨β, hβ⟩ := TauCeti.exists_isComplexPositive (E := V)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℝ hβ.ne_zero
  have hgen : (f.restrictScalars ℝ).detLineEndGenerator =
      TauCeti.detLineFourTermEquiv (ker (f.restrictScalars ℝ)).injective_subtype
        (f.restrictScalars ℝ).exact_subtype_ker_map (f.restrictScalars ℝ).exact_map_mkQ_range
        (range (f.restrictScalars ℝ)).mkQ_surjective (β ⊗ₜ φ) := by
    rw [detLineEndGenerator_def, hk.neg_one_pow, one_smul, LinearEquiv.symm_apply_eq,
      detLineEndEquiv_detLineFourTermEquiv, hφ]
  -- The real four-term sequence of `f` is the complex one with real scalars.
  have key := TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr
    (f := (ker f).subtype) (g := f) (h := (range f).mkQ)
    (ker f).injective_subtype f.exact_subtype_ker_map f.exact_map_mkQ_range
    (range f).mkQ_surjective (ker (f.restrictScalars ℝ)).injective_subtype
    (f.restrictScalars ℝ).exact_subtype_ker_map (f.restrictScalars ℝ).exact_map_mkQ_range
    (range (f.restrictScalars ℝ)).mkQ_surjective (f.kerRestrictScalarsEquiv ℝ)
    (LinearEquiv.refl ℝ V) (f.cokerRestrictScalarsEquiv ℝ).symm
    (LinearMap.ext fun x ↦ f.coe_kerRestrictScalarsEquiv_apply ℝ x) rfl
    (LinearMap.ext fun y ↦ (f.cokerRestrictScalarsEquiv_symm_mk ℝ y).symm)
    (hβ.isComplexPositiveTMulDual_tmul (hβ.isComplexPositiveDual_of_apply_eq_one hφ))
  simp only [LinearEquiv.detLineCongr_refl, LinearEquiv.rTensor_tmul, LinearEquiv.refl_apply]
    at key
  rwa [isComplexPositiveDetLine_iff, detLineRestrictScalarsEquiv_def, hgen]

end Endomorphism

end LinearMap
