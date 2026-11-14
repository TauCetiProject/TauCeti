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

/-!
# Transport and base change of cellular bases

Cellular bases are functorial under algebra isomorphisms and commute with extension of scalars.
Given a cellular basis `c` of an `R`-algebra `A`:

* for any `R`-algebra equivalence `e : A ≃ₐ[R] B`, `c.map e` is a cellular basis of `B` whose Gram
  matrices coincide with those of `c` and whose cell modules are `R`-linearly equivalent to those of
  `c` compatibly with the algebra actions and cell forms;
* for any commutative `R`-algebra `S`, `c.baseChange S` is a cellular basis of `S ⊗[R] A` with basis
  vectors `1 ⊗ₜ c.basis i`, anti-involution `s ⊗ₜ a ↦ s ⊗ₜ a*`, cell representations obtained by
  applying `algebraMap R S` to `c.cellRep μ`, Gram matrices `(c.gramMatrix μ).map (algebraMap R S)`,
  and cell modules `S`-linearly equivalent to `S ⊗[R] c.CellModule μ` intertwining the base-changed
  bilinear form `(c.cellForm μ).baseChange S`.

Composing `(c.baseChange S).map e` transports a universal cellular basis constructed over a generic
coefficient ring `R` across a concrete base-change equivalence `e : S ⊗[R] A ≃ₐ[S] B`, carrying Gram
determinants along `algebraMap R S`.

## Main definitions

* `TauCeti.CellularBasis.map`: transport a cellular basis along an `R`-algebra isomorphism.
* `TauCeti.CellularBasis.mapCellModuleEquiv`: the `R`-linear equivalence between cell modules
  induced by `CellularBasis.map`.
* `TauCeti.CellularBasis.baseChange`: extend scalars of a cellular basis to `S ⊗[R] A`.
* `TauCeti.CellularBasis.baseChangeCellModuleEquiv`: the `S`-linear equivalence
  `S ⊗[R] c.CellModule μ ≃ₗ[S] (c.baseChange S).CellModule μ`.

## Main results

* `TauCeti.CellularBasis.cellRep_map`, `TauCeti.CellularBasis.gramMatrix_map`: `map` intertwines
  `cellRep` and preserves `gramMatrix`.
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

section Map

variable {R A B C Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  [Ring C] [Algebra R C] [Preorder Λ] {M : Λ → Type*} [∀ μ, Fintype (M μ)]
  (c : CellularBasis R A M)

private theorem span_basis_map_image_lt (e : A ≃ₐ[R] B) (μ : Λ) :
    span R (c.basis.map e.toLinearEquiv '' {i | i.1 < μ}) =
      (c.lowerSpan μ).map e.toLinearMap := by
  rw [lowerSpan_def, Submodule.map_span, ← Set.image_comp]
  exact congrArg (span R) (congrArg (· '' _)
    (funext fun i ↦ c.basis.map_apply e.toLinearEquiv i))

/-- Transport a cellular basis along an `R`-algebra equivalence `e : A ≃ₐ[R] B`. -/
noncomputable def map (e : A ≃ₐ[R] B) : CellularBasis R B M where
  basis := c.basis.map e.toLinearEquiv
  antiInvolution := e.symm.trans (c.antiInvolution.trans (AlgEquiv.op e))
  unop_antiInvolution_basis μ s t := by simp
  exists_mul_basis b μ s := by
    obtain ⟨r, hr⟩ := c.exists_mul_basis (e.symm b) μ s
    refine ⟨r, fun t ↦ ?_⟩
    rw [c.span_basis_map_image_lt e μ]
    have hmem : e.symm b * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩ ∈ c.lowerSpan μ := by
      rw [lowerSpan_def]
      exact hr t
    refine ⟨e.symm b * c.basis ⟨μ, s, t⟩ - ∑ u, r u • c.basis ⟨μ, u, t⟩, hmem, ?_⟩
    simp [map_sub, map_mul, map_sum, map_smul]

/-- The cellular basis transported along `e` applies `e` to each basis vector. -/
@[simp]
theorem map_basis (e : A ≃ₐ[R] B) (i : Σ μ, M μ × M μ) :
    (c.map e).basis i = e (c.basis i) :=
  c.basis.map_apply e.toLinearEquiv i

/-- Coordinates in the transported cellular basis pull back along `e.symm`. -/
@[simp]
theorem map_basis_repr (e : A ≃ₐ[R] B) (b : B) :
    (c.map e).basis.repr b = c.basis.repr (e.symm b) := by
  simp [map]

/-- Transporting along the identity algebra equivalence does nothing. -/
@[simp]
theorem map_refl : c.map (AlgEquiv.refl : A ≃ₐ[R] A) = c := by
  ext i
  simp

/-- Transporting along `e` and then `e'` is transporting along `e.trans e'`. -/
@[simp]
theorem map_trans (e : A ≃ₐ[R] B) (e' : B ≃ₐ[R] C) :
    (c.map e).map e' = c.map (e.trans e') := by
  ext i
  simp

/-- The anti-involution of `c.map e` conjugates `c.antiInvolution` by `e`. -/
@[simp]
theorem unop_antiInvolution_map (e : A ≃ₐ[R] B) (b : B) :
    ((c.map e).antiInvolution b).unop = e (c.antiInvolution (e.symm b)).unop :=
  (rfl)

/-- Lower cell spans push forward under `e`. -/
theorem lowerSpan_map (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).lowerSpan μ = (c.lowerSpan μ).map e.toLinearMap := by
  rw [lowerSpan_def, map, c.span_basis_map_image_lt]

/-- Membership in `(c.map e).lowerSpan μ` pulls back via `e.symm`. -/
@[simp]
theorem mem_lowerSpan_map_iff (e : A ≃ₐ[R] B) {μ : Λ} {b : B} :
    b ∈ (c.map e).lowerSpan μ ↔ e.symm b ∈ c.lowerSpan μ := by
  rw [mem_lowerSpan_iff, mem_lowerSpan_iff]
  simp

/-- The canonical `R`-linear equivalence between the cell modules of `c` and `c.map e`, preserving
coordinates in the standard cell basis. -/
noncomputable def mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) :
    c.CellModule μ ≃ₗ[R] (c.map e).CellModule μ :=
  (c.cellModuleEquiv μ).trans ((c.map e).cellModuleEquiv μ).symm

/-- `mapCellModuleEquiv` preserves standard coordinates. -/
@[simp]
theorem cellModuleEquiv_mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) (x : c.CellModule μ) :
    (c.map e).cellModuleEquiv μ (c.mapCellModuleEquiv e μ x) = c.cellModuleEquiv μ x := by
  simp [mapCellModuleEquiv]

/-- The inverse of `mapCellModuleEquiv` preserves standard coordinates. -/
@[simp]
theorem cellModuleEquiv_mapCellModuleEquiv_symm (e : A ≃ₐ[R] B) (μ : Λ)
    (x : (c.map e).CellModule μ) :
    c.cellModuleEquiv μ ((c.mapCellModuleEquiv e μ).symm x) = (c.map e).cellModuleEquiv μ x := by
  simp [mapCellModuleEquiv]

/-- `mapCellModuleEquiv` carries each standard cell basis vector to the corresponding one. -/
@[simp]
theorem mapCellModuleEquiv_cellBasis (e : A ≃ₐ[R] B) (μ : Λ) (s : M μ) :
    c.mapCellModuleEquiv e μ (c.cellBasis μ s) = (c.map e).cellBasis μ s := by
  classical
  apply ((c.map e).cellModuleEquiv μ).injective
  simp

/-- The inverse of `mapCellModuleEquiv` carries each standard cell basis vector back to `c`. -/
@[simp]
theorem mapCellModuleEquiv_symm_cellBasis (e : A ≃ₐ[R] B) (μ : Λ) (s : M μ) :
    (c.mapCellModuleEquiv e μ).symm ((c.map e).cellBasis μ s) = c.cellBasis μ s :=
  (c.mapCellModuleEquiv e μ).symm_apply_eq.mpr (c.mapCellModuleEquiv_cellBasis e μ s).symm

section Decidable

variable [∀ μ, DecidableEq (M μ)]

/-- The cell representation of `c.map e` pulls back `c.cellRep` along `e.symm`. -/
@[simp]
theorem cellRep_map (e : A ≃ₐ[R] B) (μ : Λ) (b : B) :
    (c.map e).cellRep μ b = c.cellRep μ (e.symm b) := by
  ext u s
  rw [cellRep_apply, cellRep_apply, map_basis_repr, map_basis, map_mul, e.symm_apply_apply]

/-- Transporting a cellular basis along an algebra isomorphism preserves every Gram matrix. -/
@[simp]
theorem gramMatrix_map (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).gramMatrix μ = c.gramMatrix μ := by
  ext t u
  have h₁ := (c.map e).cellRep_basis μ t t u t
  have h₂ := c.cellRep_basis μ t t u t
  simp only [↓reduceIte, cellRep_map, map_basis, AlgEquiv.symm_apply_apply] at h₁ h₂
  exact h₁.symm.trans h₂

/-- `mapCellModuleEquiv` intertwines the action of `a : A` with the action of `e a : B`. -/
@[simp]
theorem mapCellModuleEquiv_smul (e : A ≃ₐ[R] B) (μ : Λ) (a : A) (x : c.CellModule μ) :
    c.mapCellModuleEquiv e μ (a • x) = e a • c.mapCellModuleEquiv e μ x := by
  apply ((c.map e).cellModuleEquiv μ).injective
  simp

/-- `mapCellModuleEquiv` is an isometry for the cell bilinear forms. -/
@[simp]
theorem cellForm_mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) (x y : c.CellModule μ) :
    (c.map e).cellForm μ (c.mapCellModuleEquiv e μ x) (c.mapCellModuleEquiv e μ y) =
      c.cellForm μ x y := by
  simp [cellForm_apply]

/-- `mapCellModuleEquiv` identifies the cell radicals of `c` and `c.map e`. -/
theorem mem_cellRadical_mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) (x : c.CellModule μ) :
    c.mapCellModuleEquiv e μ x ∈ (c.map e).cellRadical μ ↔ x ∈ c.cellRadical μ := by
  simp only [mem_cellRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · simpa using hx (c.mapCellModuleEquiv e μ y)
  · obtain ⟨y, rfl⟩ := (c.mapCellModuleEquiv e μ).surjective y
    simpa using hx y

/-- Vanishing of the cell form is invariant under `CellularBasis.map`. -/
@[simp]
theorem cellForm_map_eq_zero_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).cellForm μ = 0 ↔ c.cellForm μ = 0 := by
  refine ⟨fun h ↦ LinearMap.BilinForm.ext fun x y ↦ ?_,
    fun h ↦ LinearMap.BilinForm.ext fun x y ↦ ?_⟩
  · rw [← c.cellForm_mapCellModuleEquiv e μ x y]
    simp [h]
  · obtain ⟨x, rfl⟩ := (c.mapCellModuleEquiv e μ).surjective x
    obtain ⟨y, rfl⟩ := (c.mapCellModuleEquiv e μ).surjective y
    simp [h]

/-- Nondegeneracy of the cell form is invariant under `CellularBasis.map`. -/
@[simp]
theorem nondegenerate_cellForm_map_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    ((c.map e).cellForm μ).Nondegenerate ↔ (c.cellForm μ).Nondegenerate := by
  have hcongr : LinearMap.BilinForm.congr (c.mapCellModuleEquiv e μ).symm ((c.map e).cellForm μ) =
      c.cellForm μ := by
    ext x y
    exact c.cellForm_mapCellModuleEquiv e μ x y
  rw [← hcongr, LinearMap.BilinForm.nondegenerate_congr_iff]

/-- Triviality of the cell radical is invariant under `CellularBasis.map`. -/
@[simp]
theorem cellRadical_map_eq_bot_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).cellRadical μ = ⊥ ↔ c.cellRadical μ = ⊥ := by
  simp only [Submodule.eq_bot_iff]
  refine ⟨fun h x hx ↦ (c.mapCellModuleEquiv e μ).injective ?_,
    fun h y hy ↦ ?_⟩
  · simpa using h (c.mapCellModuleEquiv e μ x) ((c.mem_cellRadical_mapCellModuleEquiv e μ x).2 hx)
  · obtain ⟨x, rfl⟩ := (c.mapCellModuleEquiv e μ).surjective y
    rw [h x ((c.mem_cellRadical_mapCellModuleEquiv e μ x).1 hy), map_zero]

end Decidable

end Map

section BaseChange

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] (c : CellularBasis R A M)
  (S : Type*) [CommRing S] [Algebra R S]

/-- Auxiliary `S`-algebra homomorphism `S ⊗[R] A →ₐ[S] (S ⊗[R] A)ᵐᵒᵖ` sending `s ⊗ₜ a` to
`op (s ⊗ₜ a*)`. -/
private noncomputable def baseChangeAntiHom : S ⊗[R] A →ₐ[S] (S ⊗[R] A)ᵐᵒᵖ :=
  Algebra.TensorProduct.lift (Algebra.ofId S _)
    ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).op.comp
      c.antiInvolution.toAlgHom)
    fun s _ ↦ by
      rw [Algebra.ofId_apply]
      exact Algebra.commute_algebraMap_left s _

private theorem unop_baseChangeAntiHom_tmul (s : S) (a : A) :
    (c.baseChangeAntiHom S (s ⊗ₜ[R] a)).unop = s ⊗ₜ[R] (c.antiInvolution a).unop := by
  simp [baseChangeAntiHom, Algebra.ofId_apply, Algebra.TensorProduct.algebraMap_apply]

private theorem opComm_comp_baseChangeAntiHom :
    (AlgHom.opComm (c.baseChangeAntiHom S)).comp (c.baseChangeAntiHom S) =
      AlgHom.id S (S ⊗[R] A) :=
  Algebra.TensorProduct.ext' fun s a ↦ by
    rw [AlgHom.comp_apply, AlgHom.id_apply,
      ← MulOpposite.op_unop (c.baseChangeAntiHom S (s ⊗ₜ[R] a))]
    simp [unop_baseChangeAntiHom_tmul]

/-- Base change of the anti-involution of `c` to `S ⊗[R] A`. -/
private noncomputable def baseChangeAntiInvolution : S ⊗[R] A ≃ₐ[S] (S ⊗[R] A)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (c.baseChangeAntiHom S) (AlgHom.opComm (c.baseChangeAntiHom S))
    (AlgHom.ext fun y ↦ by
      obtain ⟨x, rfl⟩ := MulOpposite.op_surjective y
      apply MulOpposite.unop_injective
      simp only [AlgHom.comp_apply, AlgHom.id_apply, AlgHom.opComm_apply_apply]
      exact DFunLike.congr_fun (c.opComm_comp_baseChangeAntiHom S) x)
    (c.opComm_comp_baseChangeAntiHom S)

private theorem span_basis_baseChange_image_lt (μ : Λ) :
    span S (c.basis.baseChange S '' {i | i.1 < μ}) = (c.lowerSpan μ).baseChange S := by
  rw [lowerSpan_def, Submodule.baseChange_span, ← Set.image_comp]
  exact congrArg (span S) (congrArg (· '' _)
    (funext fun i ↦ c.basis.baseChange_apply S i))

/-- Extension of scalars of a cellular basis `c` of `A` over `R` to a cellular basis of `S ⊗[R] A`
over `S`. -/
noncomputable def baseChange : CellularBasis S (S ⊗[R] A) M where
  basis := c.basis.baseChange S
  antiInvolution := c.baseChangeAntiInvolution S
  unop_antiInvolution_basis μ s t := by
    simp [baseChangeAntiInvolution, unop_baseChangeAntiHom_tmul]
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
    ((c.baseChange S).antiInvolution (s ⊗ₜ[R] a)).unop = s ⊗ₜ[R] (c.antiInvolution a).unop :=
  c.unop_baseChangeAntiHom_tmul S s a

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
theorem smul_baseChangeCellModuleEquiv_tmul (μ : Λ) (s₁ s₂ : S) (a : A) (x : c.CellModule μ) :
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
