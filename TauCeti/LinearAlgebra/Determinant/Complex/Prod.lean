/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
public import TauCeti.LinearAlgebra.Determinant.DirectSum

/-!
# Complex orientations and determinant lines of direct sums

For linear maps `f : M → N` and `g : M' → N'` with finite-dimensional kernels and cokernels, the
direct sum isomorphism `det (f ⊕ g) ≃ det f ⊗ det g` (`LinearMap.detLineProdMapEquiv`) splits the
determinant line of the direct sum. This file shows how it interacts with complex orientations
(`LinearMap.IsComplexPositiveDetLine`), first for complex summands, then for conjugations of a
complex summand beside a real one.

**Complex summands.** When `f` and `g` are complex linear, so is `f ⊕ g`, and the three
determinant lines carry their complex orientations. The direct sum isomorphism respects them: it
identifies the tensor product of complex positive elements of `det f` and `det g` with a complex
positive element of `det (f ⊕ g)`
(`LinearMap.IsComplexPositiveDetLine.detLineCongrOfEq_detLineProdMapEquiv_symm_tmul`), and
conversely every complex positive element of `det (f ⊕ g)` is such a tensor product
(`LinearMap.IsComplexPositiveDetLine.exists_detLineProdMapEquiv_detLineCongrOfEq_eq_tmul`). The
direct sum is given as a complex-linear map `h` together with an equation saying that its
underlying real map is the direct sum of those of `f` and `g`. Such an `h` is necessarily
`f.prodMap g`; stating it through the equation lets the results apply to other forms of
`f.prodMap g`, such as the realification of a continuous `prodMap`, and the elements of `det h` are
read through `LinearMap.detLineCongrOfEq`. An operator commuting with a splitting of its domain and
target is not of this form: transport its determinant line along the splitting isomorphisms
first, which preserves complex orientations when they are complex linear
(`LinearMap.IsComplexPositiveDetLine.detLineCongr`). No sign enters: the Koszul sign
`(-1) ^ (dim (coker f) * dim (ker g))` of the direct sum isomorphism is `1`, because complex
vector spaces have even real dimension. The isomorphism is assembled from the identifications
`det U ⊗ det W ≃ det (U × W)` (`TauCeti.detLineProdEquiv`), its dual
(`TauCeti.detLineDualProdEquiv`) and their combination `TauCeti.detLineTensorDualProdEquiv`,
which respect complex orientations for complex vector spaces
(`TauCeti.isComplexPositive_detLineProdEquiv_tmul`,
`TauCeti.isComplexPositiveDual_detLineDualProdEquiv_tmul`,
`TauCeti.isComplexPositiveTMulDual_detLineTensorDualProdEquiv_tmul`).

So the complex orientation of a complex-linear operator that splits as a direct sum is the
product of the complex orientations of its summands. This is how complex orientations are compared
along the splittings of determinant lines of Fredholm operators into direct sums, for instance
along the eigenspaces of an involution commuting with a complex-linear operator, or along finitely
many Fourier modes, where determinant signs are fixed relative to complex-linear references.

**Conjugation beside a real summand.** Let `T : M → N` be a real-linear map and `D : P → Q` a
complex-linear map, both with finite-dimensional kernel and cokernel, and consider the direct sum
`T ⊕ D`, a real-linear map `M × P → N × Q`. Its determinant line is `det T ⊗ det D`
(`LinearMap.detLineProdMapEquiv`). Let `D' : P' → Q'` be a second complex-linear map and
`j₁ : P → P'`, `j₂ : Q → Q'` real isomorphisms which anticommute with `I` and intertwine `D` with
`D'`. Transporting `det (T ⊕ D)` to
`det (T ⊕ D')` along the commuting square `(-1 × j₁, -1 × j₂)` splits, by the naturality of the
direct sum isomorphism (`LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`), into the
transport of `det T` along `(-1, -1)`, which is multiplication by
`(-1) ^ (dim ker T + dim coker T)` (`LinearMap.detLineCongr_neg_apply`), and the transport of
`det D` along `(j₁, j₂)`, which carries a complex positive element to `(-1) ^ (k + c)` times a
complex positive element, `k` and `c` being the complex dimensions of the kernel and cokernel of
`D` (`LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`). So an element
`x ⊗ z` with `z` complex positive is carried to

`(-1) ^ (dim ker T + dim coker T + k + c) • x ⊗ z'`

with `z'` complex positive for `D'`
(`LinearMap.IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr`).

This is the linear algebra of the determinant sign of charge conjugation in Seiberg–Witten
theory. After a homotopy through operators of order zero, the gauge-fixed linearization of the
Seiberg–Witten equations at a reducible configuration is the direct sum of the real deformation
operator `T = (-2 d*, d⁺)` on imaginary one-forms and the complex Dirac operator `D`. Charge
conjugation negates imaginary forms and acts on spinors by the quaternionic structure, a
conjugate-linear isomorphism intertwining the Dirac operators of a `Spinᶜ` structure and of its
conjugate. With `dim ker T = b₁` and `dim coker T = 1 + b⁺`, the sign is
`ε_det = (-1) ^ (1 + b₁ + b⁺ + ind_ℂ D)`.

The kernel and cokernel of the underlying real-linear map of `D` are finite-dimensional over `ℝ`
as soon as those of `D` are over `ℂ` (`LinearMap.finite_ker_restrictScalars`,
`LinearMap.finite_quotient_range_restrictScalars`).

## Main results

* `TauCeti.isComplexPositive_detLineProdEquiv_tmul`,
  `TauCeti.isComplexPositiveDual_detLineDualProdEquiv_tmul`,
  `TauCeti.isComplexPositiveTMulDual_detLineTensorDualProdEquiv_tmul`: the determinant lines of
  products of complex vector spaces carry the products of the complex orientations.
* `LinearMap.IsComplexPositiveDetLine.detLineCongrOfEq_detLineProdMapEquiv_symm_tmul`,
  `LinearMap.IsComplexPositiveDetLine.exists_detLineProdMapEquiv_detLineCongrOfEq_eq_tmul`: the
  direct sum isomorphism of determinant lines respects complex orientations.
* `LinearMap.IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr`: the transport of
  `det (T ⊕ D)` along `(-1 × j₁, -1 × j₂)` multiplies `x ⊗ z`, for `z` complex positive, by
  `(-1) ^ (dim ker T + dim coker T + k + c)`, up to replacing `z` by a complex positive element of
  `det D'`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines, and the canonical
  orientation of the determinant line of a complex-linear Fredholm operator).
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Module TensorProduct Complex

namespace TauCeti

/-! ### Products of complex vector spaces -/

section Prod

variable {U W : Type*} [AddCommGroup U] [Module ℂ U] [Module ℝ U] [IsScalarTower ℝ ℂ U]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
  -- Real finite-dimensionality follows from the complex one through the scalar tower, but
  -- `TauCeti.detLineProdEquiv` takes it as an instance argument.
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ W]

/-- **The determinant line of a product respects complex orientations.** For complex vector
spaces `U` and `W`, the identification `det U ⊗ det W ≃ det (U × W)` of real determinant lines
(`TauCeti.detLineProdEquiv`) sends `x ⊗ y`, for complex positive `x` and `y`, to a complex positive
element. -/
theorem isComplexPositive_detLineProdEquiv_tmul {x : detLine ℝ U} {y : detLine ℝ W}
    (hx : IsComplexPositive x) (hy : IsComplexPositive y) :
    IsComplexPositive (detLineProdEquiv ℝ U W (x ⊗ₜ y)) := by
  rw [detLineProdEquiv_def]
  exact isComplexPositive_detLineShortExactEquiv_tmul (f := LinearMap.inl ℂ U W)
    (g := LinearMap.snd ℂ U W) LinearMap.inl_injective Function.Exact.inl_snd
    LinearMap.snd_surjective hx hy

/-- **The dual line of a product respects complex orientations.** For complex vector spaces `U`
and `W`, the product `(det U)^* ⊗ (det W)^* ≃ (det (U × W))^*` of functionals
(`TauCeti.detLineDualProdEquiv`) sends `φ₁ ⊗ φ₂`, for complex positive functionals `φ₁` and `φ₂`,
to a complex positive functional. -/
theorem isComplexPositiveDual_detLineDualProdEquiv_tmul {φ₁ : Dual ℝ (detLine ℝ U)}
    {φ₂ : Dual ℝ (detLine ℝ W)} (h₁ : IsComplexPositiveDual φ₁) (h₂ : IsComplexPositiveDual φ₂) :
    IsComplexPositiveDual (detLineDualProdEquiv ℝ U W (φ₁ ⊗ₜ φ₂)) := by
  have : FiniteDimensional ℂ U := Module.Finite.of_restrictScalars_finite ℝ ℂ U
  have : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  -- It suffices to test at the image of `x ⊗ y` for complex positive `x` and `y`.
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := U)
  obtain ⟨y, hy⟩ := exists_isComplexPositive (E := W)
  rw [(isComplexPositive_detLineProdEquiv_tmul hx hy).isComplexPositiveDual_iff,
    detLineDualProdEquiv_tmul_apply]
  exact mul_pos (hx.isComplexPositiveDual_iff.1 h₁) (hy.isComplexPositiveDual_iff.1 h₂)

end Prod

section TensorDual

variable {U₁ V₁ U₂ V₂ : Type*} [AddCommGroup U₁] [Module ℂ U₁] [Module ℝ U₁]
  [IsScalarTower ℝ ℂ U₁] [AddCommGroup V₁] [Module ℂ V₁] [Module ℝ V₁] [IsScalarTower ℝ ℂ V₁]
  [AddCommGroup U₂] [Module ℂ U₂] [Module ℝ U₂] [IsScalarTower ℝ ℂ U₂]
  [AddCommGroup V₂] [Module ℂ V₂] [Module ℝ V₂] [IsScalarTower ℝ ℂ V₂]
  [FiniteDimensional ℝ U₁] [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ U₂]
  [FiniteDimensional ℝ V₂]

/-- **Gathering tensors of determinant lines and dual lines respects complex orientations.** For
complex vector spaces, the isomorphism
`(det U₁ ⊗ (det V₁)^*) ⊗ (det U₂ ⊗ (det V₂)^*) ≃ det (U₁ × U₂) ⊗ (det (V₁ × V₂))^*`
(`TauCeti.detLineTensorDualProdEquiv`) sends `t₁ ⊗ t₂`, for complex positive `t₁` and `t₂`, to a
complex positive element. -/
theorem isComplexPositiveTMulDual_detLineTensorDualProdEquiv_tmul
    {t₁ : detLine ℝ U₁ ⊗[ℝ] Dual ℝ (detLine ℝ V₁)} {t₂ : detLine ℝ U₂ ⊗[ℝ] Dual ℝ (detLine ℝ V₂)}
    (h₁ : IsComplexPositiveTMulDual t₁) (h₂ : IsComplexPositiveTMulDual t₂) :
    IsComplexPositiveTMulDual (detLineTensorDualProdEquiv ℝ U₁ V₁ U₂ V₂ (t₁ ⊗ₜ t₂)) := by
  obtain ⟨x₁, φ₁, hx₁, hφ₁, rfl⟩ := isComplexPositiveTMulDual_iff.1 h₁
  obtain ⟨x₂, φ₂, hx₂, hφ₂, rfl⟩ := isComplexPositiveTMulDual_iff.1 h₂
  rw [detLineTensorDualProdEquiv_tmul]
  exact (isComplexPositive_detLineProdEquiv_tmul hx₁ hx₂).isComplexPositiveTMulDual_tmul
    (isComplexPositiveDual_detLineDualProdEquiv_tmul hφ₁ hφ₂)

end TensorDual

end TauCeti

namespace LinearMap

open TauCeti

/-! ### Direct sums of complex-linear maps -/

section ComplexSummands

variable {M N M' N' : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N']
  {f : M →ₗ[ℂ] N} {g : M' →ₗ[ℂ] N'}

/-- Read through the identifications of the complex kernels of `f`, `g` and `f ⊕ g` with the real
ones, the splitting of the kernel of the real direct sum is the complex splitting. -/
private theorem kerRestrictScalarsEquiv_prodCongr_trans_kerProdMapEquiv_symm
    (hk : (ker ((f.restrictScalars ℝ).prodMap (g.restrictScalars ℝ))).map
      (LinearEquiv.refl ℝ (M × M') : M × M' →ₗ[ℝ] M × M') =
        ker ((f.prodMap g).restrictScalars ℝ)) :
    (kerRestrictScalarsEquiv ℝ f).prodCongr (kerRestrictScalarsEquiv ℝ g) ≪≫ₗ
      (((f.restrictScalars ℝ).kerProdMapEquiv (g.restrictScalars ℝ)).symm ≪≫ₗ
        ((LinearEquiv.refl ℝ (M × M')).ofSubmodules _ _ hk ≪≫ₗ
          (kerRestrictScalarsEquiv ℝ (f.prodMap g)).symm)) =
      (kerProdMapEquiv f g).symm.restrictScalars ℝ :=
  LinearEquiv.ext fun _ ↦ Subtype.ext (by
    simp only [LinearEquiv.trans_apply, coe_kerRestrictScalarsEquiv_symm_apply,
      LinearEquiv.ofSubmodules_apply, coe_kerProdMapEquiv_symm_apply, LinearEquiv.prodCongr_apply,
      coe_kerRestrictScalarsEquiv_apply, LinearEquiv.refl_apply, LinearEquiv.restrictScalars_apply])

/-- Read through the identifications of the complex cokernels of `f`, `g` and `f ⊕ g` with the
real ones, the splitting of the cokernel of the real direct sum is the complex splitting. -/
private theorem cokerRestrictScalarsEquiv_symm_trans_cokerProdMapEquiv
    (hc : (range ((f.restrictScalars ℝ).prodMap (g.restrictScalars ℝ))).map
      (LinearEquiv.refl ℝ (N × N') : N × N' →ₗ[ℝ] N × N') =
        range ((f.prodMap g).restrictScalars ℝ)) :
    (cokerRestrictScalarsEquiv ℝ (f.prodMap g)).symm ≪≫ₗ
      ((Submodule.Quotient.equiv _ _ (LinearEquiv.refl ℝ (N × N')) hc).symm ≪≫ₗ
        ((f.restrictScalars ℝ).cokerProdMapEquiv (g.restrictScalars ℝ) ≪≫ₗ
          (cokerRestrictScalarsEquiv ℝ f).prodCongr (cokerRestrictScalarsEquiv ℝ g))) =
      (cokerProdMapEquiv f g).restrictScalars ℝ := by
  refine LinearEquiv.ext fun q ↦ ?_
  induction q using Submodule.Quotient.induction_on
  simp only [LinearEquiv.trans_apply, cokerRestrictScalarsEquiv_symm_mk,
    Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply,
    LinearEquiv.refl_symm, LinearEquiv.coe_coe, LinearEquiv.refl_apply, cokerProdMapEquiv_mk,
    LinearEquiv.prodCongr_apply, cokerRestrictScalarsEquiv_mk, LinearEquiv.restrictScalars_apply]

variable [FiniteDimensional ℂ (ker f)] [FiniteDimensional ℂ (N ⧸ range f)]
  [FiniteDimensional ℂ (ker g)] [FiniteDimensional ℂ (N' ⧸ range g)] {h : M × M' →ₗ[ℂ] N × N'}
  {x : (f.restrictScalars ℝ).detLine} {y : (g.restrictScalars ℝ).detLine}

/-- **The direct sum of complex orientations is the complex orientation of the direct sum.** Let
`f` and `g` be complex-linear maps with finite-dimensional kernels and cokernels, and `h` a
complex-linear map whose underlying real map is the direct sum of those of `f` and `g` (by
`hh`), so that `h` is `f.prodMap g`, stated through `hh` to fit other forms of it such as the
realification of a continuous `prodMap`. For complex positive elements `x` of `det f` and `y` of
`det g`, the element of `det h` corresponding to `x ⊗ y` under the direct sum isomorphism
`LinearMap.detLineProdMapEquiv`, read through `LinearMap.detLineCongrOfEq`, is complex positive. -/
theorem IsComplexPositiveDetLine.detLineCongrOfEq_detLineProdMapEquiv_symm_tmul
    (hh : (f.restrictScalars ℝ).prodMap (g.restrictScalars ℝ) = h.restrictScalars ℝ)
    (hx : f.IsComplexPositiveDetLine x) (hy : g.IsComplexPositiveDetLine y) :
    h.IsComplexPositiveDetLine (detLineCongrOfEq hh
      ((detLineProdMapEquiv (f.restrictScalars ℝ) (g.restrictScalars ℝ)).symm (x ⊗ₜ y))) := by
  obtain rfl : f.prodMap g = h := restrictScalars_injective ℝ hh
  have : FiniteDimensional ℝ (ker f) := Module.Finite.trans ℂ (ker f)
  have : FiniteDimensional ℝ (ker g) := Module.Finite.trans ℂ (ker g)
  have : FiniteDimensional ℝ (N ⧸ range f) := Module.Finite.trans ℂ (N ⧸ range f)
  have : FiniteDimensional ℝ (N' ⧸ range g) := Module.Finite.trans ℂ (N' ⧸ range g)
  -- The Koszul sign `(-1) ^ (dim (coker f) * dim (ker g))` is `1`: complex cokernels are
  -- even-dimensional over `ℝ`.
  have hf := f.even_finrank_quotient_range_restrictScalars
  obtain ⟨a₁, φ₁, ha₁, hφ₁, h₁⟩ :=
    isComplexPositiveTMulDual_iff.1 (isComplexPositiveDetLine_iff.1 hx)
  obtain ⟨a₂, φ₂, ha₂, hφ₂, h₂⟩ :=
    isComplexPositiveTMulDual_iff.1 (isComplexPositiveDetLine_iff.1 hy)
  -- Write `x` and `y` as tensors of complex positive elements of the complex kernels and
  -- cokernels of `f` and `g`.
  rw [← f.detLineRestrictScalarsEquiv.symm_apply_apply x, h₁,
    ← g.detLineRestrictScalarsEquiv.symm_apply_apply y, h₂]
  -- Split through the componentwise splittings of the kernel and the cokernel of the real direct
  -- sum; the Koszul sign is `1`.
  rw [LinearMap.detLineProdMapEquiv_symm_tmul _ _ (kerProdMapEquiv _ _).symm
      (coe_kerProdMapEquiv_symm_apply _ _)
      (cokerProdMapEquiv _ _).symm (fun _ _ ↦ cokerProdMapEquiv_symm_mk _ _ _ _),
    (hf.mul_right _).neg_one_pow, one_smul]
  -- Evaluate the tensor isomorphisms on the factors.
  simp only [detLineRestrictScalarsEquiv_symm_tmul, detLineTensorDualProdEquiv_tmul,
    TensorProduct.congr_tmul, detLineCongrOfEq_eq_detLineCongr, detLineCongr_tmul,
    isComplexPositiveDetLine_iff, detLineRestrictScalarsEquiv_tmul]
  refine isComplexPositiveTMulDual_iff.2 ⟨_, _, ?_, ?_, rfl⟩
  · -- The kernel factor is the image of `a₁ ⊗ a₂` under the complex splitting of the kernel.
    have :=
      (isComplexPositive_detLineProdEquiv_tmul ha₁ ha₂).detLineCongr (kerProdMapEquiv f g).symm
    rw [← kerRestrictScalarsEquiv_prodCongr_trans_kerProdMapEquiv_symm] at this
    simpa only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply,
      detLineCongr_prodCongr_detLineProdEquiv, TensorProduct.congr_tmul] using this
  · -- The cokernel factor is the product of `φ₁` and `φ₂` pulled back along the complex splitting
    -- of the cokernel.
    convert (isComplexPositiveDual_comp_detLineCongr_iff (cokerProdMapEquiv f g)).2
      (isComplexPositiveDual_detLineDualProdEquiv_tmul hφ₁ hφ₂) using 1
    rw [← cokerRestrictScalarsEquiv_symm_trans_cokerProdMapEquiv
      (by rw [LinearEquiv.refl_toLinearMap, Submodule.map_id, hh])]
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.dualMap_apply, LinearEquiv.detLineCongr_symm,
      LinearEquiv.symm_symm, ← detLineDualProdEquiv_tmul_comp_detLineCongr_prodCongr]

/-- **The complex orientation of a direct sum splits.** Let `f` and `g` be complex-linear maps
with finite-dimensional kernels and cokernels, and `h` a complex-linear map whose underlying real
map is the direct sum of those of `f` and `g` (by `hh`), so that `h` is `f.prodMap g`, stated
through `hh` to fit other forms of it such as the realification of a continuous `prodMap`. The
direct sum isomorphism `LinearMap.detLineProdMapEquiv` sends a complex positive element of
`det h`, read through `LinearMap.detLineCongrOfEq`, to `x ⊗ y` for complex positive elements `x`
of `det f` and `y` of `det g`. -/
theorem IsComplexPositiveDetLine.exists_detLineProdMapEquiv_detLineCongrOfEq_eq_tmul
    (hh : (f.restrictScalars ℝ).prodMap (g.restrictScalars ℝ) = h.restrictScalars ℝ)
    {z : (h.restrictScalars ℝ).detLine} (hz : h.IsComplexPositiveDetLine z) :
    ∃ x y, f.IsComplexPositiveDetLine x ∧ g.IsComplexPositiveDetLine y ∧
      detLineProdMapEquiv (f.restrictScalars ℝ) (g.restrictScalars ℝ)
        (detLineCongrOfEq hh.symm z) = x ⊗ₜ y := by
  obtain rfl : f.prodMap g = h := restrictScalars_injective ℝ hh
  -- `z` is a positive multiple of the direct sum of complex positive elements.
  obtain ⟨x, hx⟩ := f.exists_isComplexPositiveDetLine
  obtain ⟨y, hy⟩ := g.exists_isComplexPositiveDetLine
  obtain ⟨c, hc, rfl⟩ :=
    (hx.detLineCongrOfEq_detLineProdMapEquiv_symm_tmul hh hy).exists_pos_smul_eq hz
  refine ⟨c • x, y, hx.smul hc, hy, ?_⟩
  rw [map_smul, map_smul, ← detLineCongrOfEq_symm hh, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply, smul_tmul']

end ComplexSummands

/-! ### Conjugation of a complex summand beside a real summand -/

section Conjugation

variable {M N P Q P' Q' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [AddCommGroup P] [Module ℂ P] [Module ℝ P] [IsScalarTower ℝ ℂ P]
  [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
  [AddCommGroup P'] [Module ℂ P'] [Module ℝ P'] [IsScalarTower ℝ ℂ P']
  [AddCommGroup Q'] [Module ℂ Q'] [Module ℝ Q'] [IsScalarTower ℝ ℂ Q']
  (T : M →ₗ[ℝ] N) [FiniteDimensional ℝ (ker T)] [FiniteDimensional ℝ (N ⧸ range T)]
  {D : P →ₗ[ℂ] Q} [FiniteDimensional ℂ (ker D)] [FiniteDimensional ℂ (Q ⧸ range D)]
  {D' : P' →ₗ[ℂ] Q'} [FiniteDimensional ℂ (ker D')] [FiniteDimensional ℂ (Q' ⧸ range D')]
  (j₁ : P ≃ₗ[ℝ] P') (j₂ : Q ≃ₗ[ℝ] Q')
  (hj : D'.restrictScalars ℝ ∘ₗ j₁.toLinearMap = j₂.toLinearMap ∘ₗ D.restrictScalars ℝ)

/-- **The determinant sign of a conjugation on a real plus complex operator.** Let `j₁` and `j₂`
be real isomorphisms anticommuting with `I` and intertwining the complex-linear maps `D` and
`D'`. The transport of `det (T ⊕ D)` to `det (T ⊕ D')` along `(-1 × j₁, -1 × j₂)` carries the
element `x ⊗ z` of `det T ⊗ det D`, for `z` complex positive, to
`(-1) ^ (dim ker T + dim coker T + k + c)` times `x ⊗ z'` for a complex positive `z'`, where `k`
and `c` are the complex dimensions of the kernel and cokernel of `D`. Both elements are read
through `LinearMap.detLineProdMapEquiv`. -/
theorem IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr
    (hj₁ : ∀ x, j₁ (I • x) = -(I • j₁ x)) (hj₂ : ∀ y, j₂ (I • y) = -(I • j₂ y))
    (x : T.detLine) {z : (D.restrictScalars ℝ).detLine} (hz : D.IsComplexPositiveDetLine z) :
    ∃ z', D'.IsComplexPositiveDetLine z' ∧
      (T.prodMap (D.restrictScalars ℝ)).detLineCongr ((LinearEquiv.neg ℝ).prodCongr j₁)
          ((LinearEquiv.neg ℝ).prodCongr j₂)
          (prodMap_comp_prodCongr_eq_of_comp_eq (comp_neg_eq_neg_comp T) hj)
          ((detLineProdMapEquiv T (D.restrictScalars ℝ)).symm (x ⊗ₜ z)) =
        (-1 : ℝ) ^ (finrank ℝ (ker T) + finrank ℝ (N ⧸ range T) +
            (finrank ℂ (ker D) + finrank ℂ (Q ⧸ range D))) •
          (detLineProdMapEquiv T (D'.restrictScalars ℝ)).symm (x ⊗ₜ z') := by
  set c := finrank ℂ (ker D) + finrank ℂ (Q ⧸ range D)
  refine ⟨(-1 : ℝ) ^ c • (D.restrictScalars ℝ).detLineCongr j₁ j₂ hj z,
    hz.neg_one_pow_smul_detLineCongr j₁ j₂ hj hj₁ hj₂, ?_⟩
  apply (detLineProdMapEquiv T (D'.restrictScalars ℝ)).injective
  have h := detLineProdMapEquiv_detLineCongr_prodCongr T (D.restrictScalars ℝ)
    (LinearEquiv.neg ℝ) (LinearEquiv.neg ℝ) j₁ j₂ (comp_neg_eq_neg_comp T) hj
    ((detLineProdMapEquiv T (D.restrictScalars ℝ)).symm (x ⊗ₜ z))
  refine h.trans ?_
  simp only [LinearEquiv.apply_symm_apply, map_smul, map_tmul, LinearEquiv.coe_coe,
    detLineCongr_neg_apply, tmul_smul, smul_tmul', smul_smul, ← pow_add]
  -- The exponents differ by the even number `c + c`.
  rw [add_assoc _ c c, pow_add _ _ (c + c), Even.neg_one_pow ⟨c, rfl⟩, mul_one]

end Conjugation

end LinearMap
