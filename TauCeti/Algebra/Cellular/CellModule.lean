/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cellular.Basic
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Cell modules and their radicals

A cellular basis gives a left module for each cell, with its canonical symmetric bilinear
form. Cellular basis vectors from cells distinct from and not strictly above a cell act by
zero on its cell module. The radical of the form is an algebra submodule; because the form is
symmetric, its nondegeneracy is equivalent to triviality of the cell radical (and, over an
integral domain, to nonvanishing of the Gram determinant). Over a field every proper submodule
is contained in this radical, so a cell with nonzero form has a simple quotient. These are
the modules from which the simple modules of a cellular algebra are classified.

The module uses the existing matrix representation `CellularBasis.cellRep`; its underlying
scalar module is identified with the functions on the cell's index set by `cellModuleEquiv`.
No finiteness of the set of cells is required.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Definition 2.1 and Proposition 2.4. The cell modules and simple radical quotients constructed
  here lead to the classification in Theorem 3.4; this file does not prove completeness or
  pairwise non-isomorphism.
-/

public section

open Module
open scoped Matrix

namespace TauCeti.CellularBasis

section Preorder

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [Preorder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (c : CellularBasis R A M)

/-- The left cell module of a cellular basis at `μ`. Its vectors have coordinates indexed by
`M μ`, and the algebra acts through `cellRep`. The type synonym is exposed because the
transported additive and module instances require its underlying function type during
compilation; coordinates and the algebra action are provided by `cellModuleEquiv` and
`cellModuleEquiv_smul`. -/
@[expose]
def CellModule (_c : CellularBasis R A M) (μ : Λ) : Type _ := M μ → R

instance (μ : Λ) : AddCommGroup (c.CellModule μ) :=
  inferInstanceAs (AddCommGroup (M μ → R))

-- Prefer this action to the generic integer action, so finite/free instances also work over ℤ.
instance (priority := 1100) (μ : Λ) : Module R (c.CellModule μ) :=
  inferInstanceAs (Module R (M μ → R))

noncomputable instance (μ : Λ) : Module A (c.CellModule μ) :=
  Module.compHom (M μ → R) (c.cellRep μ).toRingHom

/-- Coordinates of a vector in the cell module. -/
def cellModuleEquiv (μ : Λ) : c.CellModule μ ≃ₗ[R] (M μ → R) :=
  LinearEquiv.refl R (M μ → R)

/-- The defining algebra action on the cell module is matrix multiplication by `cellRep`. -/
@[simp]
theorem cellModuleEquiv_smul (μ : Λ) (a : A) (x : c.CellModule μ) :
    c.cellModuleEquiv μ (a • x) = c.cellRep μ a *ᵥ c.cellModuleEquiv μ x :=
  Matrix.smul_eq_mulVec _ _

instance (μ : Λ) : IsScalarTower R A (c.CellModule μ) where
  smul_assoc r a x := by
    apply (c.cellModuleEquiv μ).injective
    simp only [map_smul, cellModuleEquiv_smul, Matrix.smul_mulVec]

instance (μ : Λ) : Module.Free R (c.CellModule μ) :=
  Module.Free.of_equiv (c.cellModuleEquiv μ).symm

instance (μ : Λ) : Module.Finite R (c.CellModule μ) :=
  Module.Finite.equiv (c.cellModuleEquiv μ).symm

/-- The standard basis of the cell module, indexed by the cell's index set. -/
noncomputable def cellBasis (μ : Λ) : Basis (M μ) R (c.CellModule μ) :=
  (Pi.basisFun R (M μ)).map (c.cellModuleEquiv μ).symm

@[simp]
theorem cellModuleEquiv_cellBasis (μ : Λ) (s : M μ) :
    c.cellModuleEquiv μ (c.cellBasis μ s) = Pi.single s 1 := by
  simp [cellBasis, Pi.basisFun_apply]

omit [∀ μ, DecidableEq (M μ)] in
/-- Coordinates in the standard cell basis are the cell-module coordinates. -/
@[simp]
theorem cellBasis_repr_apply (μ : Λ) (x : c.CellModule μ) (s : M μ) :
    (c.cellBasis μ).repr x s = c.cellModuleEquiv μ x s := by
  simp [cellBasis]

/-- The canonical bilinear form of the cell module, whose matrix is `gramMatrix`. -/
noncomputable def cellForm (μ : Λ) : LinearMap.BilinForm R (c.CellModule μ) :=
  (c.gramMatrix μ).toBilin'.comp (c.cellModuleEquiv μ).toLinearMap
    (c.cellModuleEquiv μ).toLinearMap

/-- The cell form in coordinates. -/
theorem cellForm_apply (μ : Λ) (x y : c.CellModule μ) :
    c.cellForm μ x y = c.cellModuleEquiv μ x ⬝ᵥ
      (c.gramMatrix μ *ᵥ c.cellModuleEquiv μ y) := by
  exact Matrix.toBilin'_apply' _ _ _

@[simp]
theorem cellForm_cellBasis (μ : Λ) (s t : M μ) :
    c.cellForm μ (c.cellBasis μ s) (c.cellBasis μ t) = c.gramMatrix μ s t := by
  simp [cellForm, Matrix.toBilin'_single]

/-- The matrix of `c.cellForm μ` in the standard cell basis `c.cellBasis μ` is `c.gramMatrix μ`. -/
@[simp]
theorem toMatrix_cellBasis_cellForm (μ : Λ) :
    LinearMap.BilinForm.toMatrix (c.cellBasis μ) (c.cellForm μ) = c.gramMatrix μ := by
  ext s t
  simp

/-- The cell bilinear form vanishes if and only if its Gram matrix vanishes. -/
theorem cellForm_eq_zero_iff (μ : Λ) : c.cellForm μ = 0 ↔ c.gramMatrix μ = 0 := by
  rw [← (LinearMap.BilinForm.toMatrix (c.cellBasis μ)).map_eq_zero_iff,
    toMatrix_cellBasis_cellForm]

/-- A cell with nonzero bilinear form has a nonzero entry in its Gram matrix. -/
theorem exists_gramMatrix_ne_zero {μ : Λ} (h : c.cellForm μ ≠ 0) :
    ∃ s t : M μ, c.gramMatrix μ s t ≠ 0 := by
  have hg : c.gramMatrix μ ≠ 0 := mt (c.cellForm_eq_zero_iff μ).mpr h
  by_contra! h0
  exact hg (Matrix.ext fun s t ↦ h0 s t)

/-- The cell form is symmetric. -/
theorem isSymm_cellForm (μ : Λ) : (c.cellForm μ).IsSymm :=
  ⟨fun x y => ((Matrix.isSymm_toBilin'_iff_isSymm).mpr
    (c.isSymm_gramMatrix μ)).eq (c.cellModuleEquiv μ x) (c.cellModuleEquiv μ y)⟩

/-- Invariance of the cell form under the algebra action and its anti-involution. -/
theorem cellForm_smul (μ : Λ) (a : A) (x y : c.CellModule μ) :
    c.cellForm μ (a • x) y = c.cellForm μ x ((c.antiInvolution a).unop • y) := by
  have h : (c.cellRep μ a)ᵀ * c.gramMatrix μ =
      c.gramMatrix μ * c.cellRep μ (c.antiInvolution a).unop := by
    simpa using c.cellRep_transpose_mul_gramMatrix (c.antiInvolution a).unop μ
  -- In coordinates, invariance is the identity xᵀ aᵀ G y = xᵀ G a* y.
  simp only [cellForm_apply, cellModuleEquiv_smul, Matrix.dotProduct_mulVec,
    Matrix.vecMul_mulVec, h, Matrix.vecMul_vecMul]

/-- A cellular basis vector acts as a rank-one operator given by the cell form. -/
theorem basis_smul (μ : Λ) (s t : M μ) (x : c.CellModule μ) :
    c.basis ⟨μ, s, t⟩ • x = c.cellForm μ (c.cellBasis μ t) x • c.cellBasis μ s := by
  apply (c.cellModuleEquiv μ).injective
  ext u
  simp [cellForm_apply, Matrix.mulVec, dotProduct, c.cellRep_basis, Pi.single_apply,
    Finset.sum_ite_irrel, ite_mul]

/-- A cellular basis vector from a cell `ν ≠ μ` not strictly above `μ` acts by zero in the cell
representation at `μ`. -/
theorem cellRep_basis_of_ne {μ ν : Λ} (hne : ν ≠ μ) (hnlt : ¬ μ < ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 := by
  have hsum (r : M ν → R) (u s : M μ) :
      c.basis.repr (∑ v, r v • c.basis ⟨ν, x, v⟩) ⟨μ, u, s⟩ = 0 := by
    simp [hne]
  ext u s
  rw [Matrix.zero_apply, cellRep_apply]
  have hsub := c.basis_mul_sub_sum_mem (c.basis ⟨μ, s, s⟩) ν x y
  have hzero := c.mem_lowerSpan_iff.1 hsub ⟨μ, u, s⟩ hnlt
  rw [map_sub, Finsupp.sub_apply, sub_eq_zero] at hzero
  exact hzero.trans (hsum _ u s)

/-- A cellular basis vector from a cell `ν ≠ μ` not strictly above `μ` annihilates
`c.CellModule μ`. -/
theorem basis_smul_eq_zero_of_ne {μ ν : Λ} (hne : ν ≠ μ) (hnlt : ¬ μ < ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 := by
  apply (c.cellModuleEquiv μ).injective
  rw [cellModuleEquiv_smul, c.cellRep_basis_of_ne hne hnlt, Matrix.zero_mulVec, map_zero]

/-- The radical of the cell form, as an algebra submodule rather than just a scalar subspace. -/
noncomputable def cellRadical (μ : Λ) : Submodule A (c.CellModule μ) where
  carrier := {x | ∀ y, c.cellForm μ x y = 0}
  zero_mem' := by simp
  add_mem' hx hy := by intro y; simp [hx y, hy y]
  smul_mem' a x hx := by intro y; rw [c.cellForm_smul]; exact hx _

/-- A vector lies in the radical exactly when it pairs to zero with every vector. -/
@[simp]
theorem mem_cellRadical (μ : Λ) (x : c.CellModule μ) :
    x ∈ c.cellRadical μ ↔ ∀ y, c.cellForm μ x y = 0 := Iff.rfl

/-- It suffices to test membership of the radical against the standard cell basis. -/
theorem mem_cellRadical_iff_cellBasis (μ : Λ) (x : c.CellModule μ) :
    x ∈ c.cellRadical μ ↔ ∀ t, c.cellForm μ (c.cellBasis μ t) x = 0 := by
  constructor
  · intro hx t
    rw [c.isSymm_cellForm μ |>.eq]
    exact (c.mem_cellRadical μ x).mp hx _
  · intro hx
    have hz : (c.cellForm μ).flip x = 0 := (c.cellBasis μ).ext fun t => hx t
    intro y
    rw [(c.isSymm_cellForm μ).eq]
    exact LinearMap.congr_fun hz y

/-- The scalar restriction of the cell radical is the kernel of the cell form. -/
theorem restrictScalars_cellRadical (μ : Λ) :
    (c.cellRadical μ).restrictScalars R = LinearMap.ker (c.cellForm μ) := by
  ext x
  simp [LinearMap.ext_iff]

/-- The cell radical is the whole module exactly when the cell form is zero. -/
@[simp]
theorem cellRadical_eq_top_iff (μ : Λ) : c.cellRadical μ = ⊤ ↔ c.cellForm μ = 0 := by
  simp [Submodule.eq_top_iff', LinearMap.ext_iff]

/-- Because `c.cellForm μ` is symmetric, it is nondegenerate (`SeparatingLeft ∧ SeparatingRight`)
if and only if `c.cellRadical μ = ⊥`. -/
theorem nondegenerate_cellForm_iff_cellRadical_eq_bot (μ : Λ) :
    (c.cellForm μ).Nondegenerate ↔ c.cellRadical μ = ⊥ := by
  simp only [(c.isSymm_cellForm μ).isRefl.nondegenerate_iff_separatingLeft,
    LinearMap.SeparatingLeft, Submodule.eq_bot_iff, mem_cellRadical]

/-- The Gram matrix `c.gramMatrix μ` is nondegenerate if and only if `c.cellRadical μ = ⊥`. -/
theorem nondegenerate_gramMatrix_iff_cellRadical_eq_bot (μ : Λ) :
    (c.gramMatrix μ).Nondegenerate ↔ c.cellRadical μ = ⊥ := by
  rw [← c.toMatrix_cellBasis_cellForm μ, LinearMap.BilinForm.nondegenerate_toMatrix_iff,
    c.nondegenerate_cellForm_iff_cellRadical_eq_bot]

section IsDomain

variable [IsDomain R]

/-- Over an integral domain `R`, the cell bilinear form `c.cellForm μ` is nondegenerate if and only
if its Gram determinant `(c.gramMatrix μ).det` is nonzero. -/
theorem nondegenerate_cellForm_iff_det_gramMatrix_ne_zero (μ : Λ) :
    (c.cellForm μ).Nondegenerate ↔ (c.gramMatrix μ).det ≠ 0 := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (c.cellBasis μ),
    toMatrix_cellBasis_cellForm]

/-- Over an integral domain `R`, `c.cellRadical μ = ⊥` if and only if `(c.gramMatrix μ).det ≠ 0`. -/
theorem cellRadical_eq_bot_iff_det_gramMatrix_ne_zero (μ : Λ) :
    c.cellRadical μ = ⊥ ↔ (c.gramMatrix μ).det ≠ 0 := by
  rw [← c.nondegenerate_cellForm_iff_cellRadical_eq_bot,
    c.nondegenerate_cellForm_iff_det_gramMatrix_ne_zero]

end IsDomain

section Field

variable {K B : Type*} [Field K] [Ring B] [Algebra K B]
  (d : CellularBasis K B M) (μ : Λ)

/-- Over a field, a submodule containing a vector outside the cell radical is the whole cell
module. Equivalently every proper submodule lies in the radical. -/
theorem eq_top_of_not_le_cellRadical (N : Submodule B (d.CellModule μ))
    (hN : ¬ N ≤ d.cellRadical μ) : N = ⊤ := by
  obtain ⟨x, hx, hxrad⟩ := IsConcreteLE.not_le_iff_exists.mp hN
  obtain ⟨t, ht⟩ := not_forall.mp (mt (d.mem_cellRadical_iff_cellBasis μ x).mpr hxrad)
  have hb (s : M μ) : d.cellBasis μ s ∈ N := by
    have hs := N.smul_mem (d.basis ⟨μ, s, t⟩) hx
    rw [d.basis_smul] at hs
    simpa [smul_smul, ht] using
      (N.restrictScalars K).smul_mem (d.cellForm μ (d.cellBasis μ t) x)⁻¹ hs
  have htop : N.restrictScalars K = ⊤ := by
    apply top_unique
    rw [← (d.cellBasis μ).span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨s, rfl⟩; exact hb s)
  exact (Submodule.restrictScalars_eq_top_iff K B (d.CellModule μ)).mp htop

/-- Every proper submodule of a cell module over a field lies in the cell radical. -/
theorem le_cellRadical_of_ne_top (N : Submodule B (d.CellModule μ)) (hN : N ≠ ⊤) :
    N ≤ d.cellRadical μ := by
  by_contra h
  exact hN (d.eq_top_of_not_le_cellRadical μ N h)

/-- Over a field, a cell with nonzero form has a maximal submodule given by its radical.
By `le_cellRadical_of_ne_top`, it is the unique maximal submodule. -/
theorem isCoatom_cellRadical (h : d.cellForm μ ≠ 0) : IsCoatom (d.cellRadical μ) := by
  refine ⟨by simpa using h, fun N hN => ?_⟩
  by_contra htop
  exact (not_le_of_gt hN) (d.le_cellRadical_of_ne_top μ N htop)

/-- The quotient of a cell module by its radical is simple exactly when the cell form is
nonzero. -/
theorem isSimpleModule_cellModule_quotient_iff :
    IsSimpleModule B (d.CellModule μ ⧸ d.cellRadical μ) ↔ d.cellForm μ ≠ 0 := by
  rw [isSimpleModule_iff_isCoatom]
  exact ⟨fun h => by simpa using h.ne_top, d.isCoatom_cellRadical μ⟩

end Field

end Preorder

section PartialOrder

variable {R A Λ : Type*} [CommRing R] [Ring A] [Algebra R A] [PartialOrder Λ]
  {M : Λ → Type*} [∀ μ, Fintype (M μ)] [∀ μ, DecidableEq (M μ)]
  (c : CellularBasis R A M)

/-- Over a partial order of cells, `c.basis ⟨ν, x, y⟩` acts as zero at `μ` whenever `¬ μ ≤ ν`. -/
theorem cellRep_basis_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν) :
    c.cellRep μ (c.basis ⟨ν, x, y⟩) = 0 :=
  c.cellRep_basis_of_ne (fun hEq ↦ h hEq.ge) (fun hlt ↦ h hlt.le) x y

/-- Over a partial order of cells, `c.basis ⟨ν, x, y⟩` annihilates `c.CellModule μ` whenever
`¬ μ ≤ ν`. -/
theorem basis_smul_eq_zero_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 :=
  c.basis_smul_eq_zero_of_ne (fun hEq ↦ h hEq.ge) (fun hlt ↦ h hlt.le) x y w

end PartialOrder

end TauCeti.CellularBasis
