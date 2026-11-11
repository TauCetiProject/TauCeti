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
form. The radical of the form is an algebra submodule. Over a field every proper submodule
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

end TauCeti.CellularBasis
