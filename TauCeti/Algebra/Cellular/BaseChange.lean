/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Algebra.Cellular.CellModule
import Mathlib.LinearAlgebra.TensorProduct.Opposite

/-!
# Base change of cellular bases

Cellular bases commute with extension of scalars. Given a cellular basis `c` of an `R`-algebra `A`
and any commutative `R`-algebra `S`, `c.baseChange S` is a cellular basis of `S ⊗[R] A` with basis
vectors `1 ⊗ₜ c.basis i`, anti-involution `s ⊗ₜ a ↦ s ⊗ₜ a*`, cell representations obtained by
applying `algebraMap R S` to `c.cellRep μ`, Gram matrices `(c.gramMatrix μ).map (algebraMap R S)`,
and cell modules `S`-linearly equivalent to `S ⊗[R] c.CellModule μ` intertwining the base-changed
bilinear form `(c.cellForm μ).baseChange S`.

Composing `(c.baseChange S).map e` (`TauCeti.CellularBasis.map`) transports a universal cellular
basis constructed over a generic coefficient ring `R` across a concrete base-change equivalence
`e : S ⊗[R] A ≃ₐ[S] B`, carrying Gram determinants along `algebraMap R S`.

## Main definitions

* `TauCeti.CellularBasis.baseChange`: extend scalars of a cellular basis to `S ⊗[R] A`.
* `TauCeti.CellularBasis.baseChangeCellModuleEquiv`: the `S`-linear equivalence
  `S ⊗[R] c.CellModule μ ≃ₗ[S] (c.baseChange S).CellModule μ`.

## Main results

* `TauCeti.CellularBasis.cellRep_baseChange_tmul`, `TauCeti.CellularBasis.gramMatrix_baseChange`,
  `TauCeti.CellularBasis.det_gramMatrix_baseChange`: `baseChange` maps `cellRep`, `gramMatrix`, and
  Gram determinants along `algebraMap R S`.
* `TauCeti.CellularBasis.cellForm_baseChangeCellModuleEquiv`: `baseChangeCellModuleEquiv` identifies
  the cell form of `c.baseChange S` with `(c.cellForm μ).baseChange S`.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Definition 1.1 and Section 1.8.
-/

public section

open Module Submodule
open scoped Matrix TensorProduct

namespace TauCeti.CellularBasis

section BaseChange

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] (c : CellularBasis R A M)
  (S : Type*) [CommRing S] [Algebra R S]

private theorem span_basis_baseChange_image_lt (μ : Λ) :
    span S (c.basis.baseChange S '' {i | i.1 < μ}) = (c.lowerSpan μ).baseChange S := by
  rw [lowerSpan_def, Submodule.baseChange_span, ← Set.image_comp]
  exact congrArg (span S) (congrArg (· '' _)
    (funext fun i ↦ c.basis.baseChange_apply S i))

/-- Extension of scalars of a cellular basis `c` of `A` over `R` to a cellular basis of `S ⊗[R] A`
over `S`. -/
noncomputable def baseChange : CellularBasis S (S ⊗[R] A) M where
  basis := c.basis.baseChange S
  antiInvolution := (Algebra.TensorProduct.congr (AlgEquiv.toOpposite S S) c.antiInvolution).trans
    (Algebra.TensorProduct.opAlgEquiv R S S A)
  unop_antiInvolution_basis μ s t := by simp
  exists_mul_basis z μ s := by
    refine TensorProduct.inductionOn z (fun s' a ↦ ?_) (fun x y hx hy ↦ ?_)
    · obtain ⟨r, hr⟩ := c.exists_mul_basis a μ s
      refine ⟨fun u ↦ r u • s', fun t ↦ ?_⟩
      rw [c.span_basis_baseChange_image_lt S μ]
      have hsmul (u : M μ) :
          (r u • s') • c.basis.baseChange S ⟨μ, u, t⟩ =
            s' ⊗ₜ[R] (r u • c.basis ⟨μ, u, t⟩) := by
        rw [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
          TensorProduct.smul_tmul]
      have hterm : (s' ⊗ₜ[R] a) * c.basis.baseChange S ⟨μ, s, t⟩ -
          ∑ u, (r u • s') • c.basis.baseChange S ⟨μ, u, t⟩ =
          s' ⊗ₜ[R] (a * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩) := by
        rw [Finset.sum_congr rfl fun u _ ↦ hsmul u, ← TensorProduct.tmul_sum,
          Basis.baseChange_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          ← TensorProduct.tmul_sub]
      rw [hterm]
      have hmem : a * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩ ∈ c.lowerSpan μ := by
        rw [lowerSpan_def]
        exact hr t
      exact Submodule.tmul_mem_baseChange_of_mem s' hmem
    · obtain ⟨rx, hrx⟩ := hx
      obtain ⟨ry, hry⟩ := hy
      refine ⟨rx + ry, fun t ↦ ?_⟩
      have hadd : (x + y) * c.basis.baseChange S ⟨μ, s, t⟩ -
          ∑ u, (rx + ry) u • c.basis.baseChange S ⟨μ, u, t⟩ =
          (x * c.basis.baseChange S ⟨μ, s, t⟩ - ∑ u, rx u • c.basis.baseChange S ⟨μ, u, t⟩) +
            (y * c.basis.baseChange S ⟨μ, s, t⟩ - ∑ u, ry u • c.basis.baseChange S ⟨μ, u, t⟩) := by
        simp only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]
        abel
      rw [hadd]
      exact add_mem (hrx t) (hry t)

/-- The base-changed cellular basis vectors are `1 ⊗ₜ c.basis i`. -/
@[simp]
theorem baseChange_basis (i : Σ μ, M μ × M μ) :
    (c.baseChange S).basis i = 1 ⊗ₜ[R] c.basis i :=
  c.basis.baseChange_apply S i

/-- Coordinates of a pure tensor in the base-changed cellular basis. -/
@[simp]
theorem baseChange_basis_repr_tmul (s : S) (a : A) (i : Σ μ, M μ × M μ) :
    (c.baseChange S).basis.repr (s ⊗ₜ[R] a) i = c.basis.repr a i • s :=
  c.basis.baseChange_repr_tmul S s a i

/-- The base-changed anti-involution acts on pure tensors by `s ⊗ₜ a ↦ s ⊗ₜ a*`. -/
@[simp]
theorem unop_antiInvolution_baseChange_tmul (s : S) (a : A) :
    ((c.baseChange S).antiInvolution (s ⊗ₜ[R] a)).unop = s ⊗ₜ[R] (c.antiInvolution a).unop := by
  simp [baseChange]

/-- Lower cell spans commute with submodule base change. -/
@[simp]
theorem lowerSpan_baseChange (μ : Λ) :
    (c.baseChange S).lowerSpan μ = (c.lowerSpan μ).baseChange S := by
  rw [lowerSpan_def, baseChange, c.span_basis_baseChange_image_lt]

/-- Pure tensors with right factor in `c.lowerSpan μ` lie in `(c.baseChange S).lowerSpan μ`. -/
theorem tmul_mem_lowerSpan_baseChange {μ : Λ} (s : S) {a : A} (ha : a ∈ c.lowerSpan μ) :
    s ⊗ₜ[R] a ∈ (c.baseChange S).lowerSpan μ := by
  rw [lowerSpan_baseChange]
  exact Submodule.tmul_mem_baseChange_of_mem s ha

/-- The canonical `S`-linear equivalence identifying the base-changed cell module
`S ⊗[R] c.CellModule μ` with `(c.baseChange S).CellModule μ`, matching standard basis vectors. -/
noncomputable def baseChangeCellModuleEquiv (μ : Λ) :
    S ⊗[R] c.CellModule μ ≃ₗ[S] (c.baseChange S).CellModule μ :=
  ((c.cellBasis μ).baseChange S).equiv ((c.baseChange S).cellBasis μ) (Equiv.refl (M μ))

/-- `baseChangeCellModuleEquiv` sends `s ⊗ₜ c.cellBasis μ t` to
`s • (c.baseChange S).cellBasis μ t`. -/
@[simp]
theorem baseChangeCellModuleEquiv_tmul_cellBasis (μ : Λ) (s : S) (t : M μ) :
    c.baseChangeCellModuleEquiv S μ (s ⊗ₜ[R] c.cellBasis μ t) =
      s • (c.baseChange S).cellBasis μ t := by
  have hs : s ⊗ₜ[R] c.cellBasis μ t = s • (c.cellBasis μ).baseChange S t := by
    rw [Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hs, map_smul, baseChangeCellModuleEquiv, Basis.equiv_apply, Equiv.refl_apply]

/-- The inverse of `baseChangeCellModuleEquiv` sends `(c.baseChange S).cellBasis μ t` to
`1 ⊗ₜ c.cellBasis μ t`. -/
@[simp]
theorem baseChangeCellModuleEquiv_symm_cellBasis (μ : Λ) (t : M μ) :
    (c.baseChangeCellModuleEquiv S μ).symm ((c.baseChange S).cellBasis μ t) =
      1 ⊗ₜ[R] c.cellBasis μ t := by
  simp [baseChangeCellModuleEquiv]

/-- Coordinates of `baseChangeCellModuleEquiv (s ⊗ₜ x)` in the standard basis. -/
@[simp]
theorem cellModuleEquiv_baseChangeCellModuleEquiv_tmul (μ : Λ) (s : S) (x : c.CellModule μ)
    (u : M μ) :
    (c.baseChange S).cellModuleEquiv μ (c.baseChangeCellModuleEquiv S μ (s ⊗ₜ[R] x)) u =
      c.cellModuleEquiv μ x u • s := by
  classical
  conv_lhs => rw [← (c.cellBasis μ).sum_repr x]
  simp [TensorProduct.tmul_sum, TensorProduct.smul_tmul', Pi.single_apply]

section Decidable

variable [∀ μ, DecidableEq (M μ)]

/-- The cell representation of `c.baseChange S` on pure tensors maps `c.cellRep` along
`algebraMap R S`. -/
@[simp]
theorem cellRep_baseChange_tmul (μ : Λ) (s : S) (a : A) :
    (c.baseChange S).cellRep μ (s ⊗ₜ[R] a) = s • (c.cellRep μ a).map (algebraMap R S) := by
  ext u v
  rw [cellRep_apply, baseChange_basis, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    baseChange_basis_repr_tmul, Matrix.smul_apply, Matrix.map_apply, cellRep_apply,
    Algebra.smul_def, smul_eq_mul, mul_comm]

/-- The Gram matrix of `c.baseChange S` at `μ` is `(c.gramMatrix μ).map (algebraMap R S)`. -/
@[simp]
theorem gramMatrix_baseChange (μ : Λ) :
    (c.baseChange S).gramMatrix μ = (c.gramMatrix μ).map (algebraMap R S) := by
  ext t u
  have h₁ := (c.baseChange S).cellRep_basis μ t t u t
  have h₂ := c.cellRep_basis μ t t u t
  simp only [↓reduceIte, baseChange_basis, cellRep_baseChange_tmul, one_smul,
    Matrix.map_apply] at h₁ h₂
  exact h₁.symm.trans (congrArg (algebraMap R S) h₂)

/-- Base change carries Gram determinants along `algebraMap R S`. -/
theorem det_gramMatrix_baseChange (μ : Λ) :
    ((c.baseChange S).gramMatrix μ).det = algebraMap R S (c.gramMatrix μ).det := by
  rw [gramMatrix_baseChange, ← RingHom.mapMatrix_apply, RingHom.map_det]

/-- `baseChangeCellModuleEquiv` intertwines the `(S ⊗[R] A)`-action on pure tensors with the
base-changed action `(s₁ ⊗ₜ a) • (s₂ ⊗ₜ x) = (s₁ * s₂) ⊗ₜ (a • x)`. -/
@[simp]
theorem tmul_smul_baseChangeCellModuleEquiv_tmul (μ : Λ) (s₁ s₂ : S) (a : A) (x : c.CellModule μ) :
    (s₁ ⊗ₜ[R] a) • c.baseChangeCellModuleEquiv S μ (s₂ ⊗ₜ[R] x) =
      c.baseChangeCellModuleEquiv S μ ((s₁ * s₂) ⊗ₜ[R] (a • x)) := by
  apply ((c.baseChange S).cellModuleEquiv μ).injective
  ext u
  rw [cellModuleEquiv_smul, cellRep_baseChange_tmul, Matrix.smul_mulVec, Pi.smul_apply,
    cellModuleEquiv_baseChangeCellModuleEquiv_tmul, cellModuleEquiv_smul]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    cellModuleEquiv_baseChangeCellModuleEquiv_tmul, smul_eq_mul, Algebra.smul_def, map_sum,
    map_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  ring

/-- `baseChangeCellModuleEquiv` identifies the cell form of `c.baseChange S` with Mathlib's
`(c.cellForm μ).baseChange S`. -/
@[simp]
theorem cellForm_baseChangeCellModuleEquiv (μ : Λ) (x y : S ⊗[R] c.CellModule μ) :
    (c.baseChange S).cellForm μ (c.baseChangeCellModuleEquiv S μ x)
        (c.baseChangeCellModuleEquiv S μ y) =
      (c.cellForm μ).baseChange S x y := by
  let f : LinearMap.BilinForm S (S ⊗[R] c.CellModule μ) :=
    ((c.baseChange S).cellForm μ).comp (c.baseChangeCellModuleEquiv S μ).toLinearMap
      (c.baseChangeCellModuleEquiv S μ).toLinearMap
  have hf : f = (c.cellForm μ).baseChange S :=
    ((c.cellBasis μ).baseChange S).ext fun s ↦ ((c.cellBasis μ).baseChange S).ext fun t ↦ by
      simp [f, LinearMap.BilinForm.comp_apply, Algebra.algebraMap_eq_smul_one]
  simpa [f] using LinearMap.congr_fun (LinearMap.congr_fun hf x) y

end Decidable

end BaseChange

end TauCeti.CellularBasis
