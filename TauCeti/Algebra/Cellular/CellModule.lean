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
form. Cellular basis vectors from cells distinct from and not strictly above a cell (and more
generally the inclusive cell ideal `leSpan ν` whenever `¬ μ ≤ ν`) act by zero on `CellModule μ`,
and any vector annihilated by lower cells in a left `A`-module `S` induces an `A`-linear
evaluation map `cellModuleHom` out of the cell module. Whenever a cell has nonzero form over a
ring without zero divisors, any nonzero `A`-linear map `CellModule ν →ₗ[A] CellModule μ` forces
`μ = ν ∨ μ < ν`; when an entry of the Gram matrix is a unit (in particular, whenever the form is
nonzero over a field), the cell module is cyclically generated over `leSpan ν` by a single
standard basis vector. Transporting a cellular basis along an `R`-algebra equivalence
(`CellularBasis.map`) induces an `R`-linear equivalence `mapCellModuleEquiv` of cell modules
intertwining the algebra actions, cell forms, and cell radicals.

The radical of the form is an algebra submodule; because the form is symmetric, its
nondegeneracy is equivalent to triviality of the cell radical, which holds whenever the Gram
determinant is a non-zero-divisor (and is equivalent to nonvanishing of the Gram determinant over
an integral domain). Over a field every proper submodule is contained in this radical, so a cell
with nonzero form has a simple quotient and is itself simple precisely when its radical vanishes,
and any nonempty cell with trivial radical is simple. These are the modules from which the simple
modules of a cellular algebra are classified.

The module uses the existing matrix representation `CellularBasis.cellRep`; its underlying
scalar module is identified with the functions on the cell's index set by `cellModuleEquiv`.
No finiteness of the set of cells is required.

## References

* J. J. Graham and G. I. Lehrer, *Cellular algebras*, Invent. Math. 123 (1996), 1–34,
  Definition 2.1, Proposition 2.4, and Lemma 2.5. The cell modules and simple radical quotients
  constructed here lead to the classification in Theorem 3.4; this file does not prove
  completeness or pairwise non-isomorphism.
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

/-- A cellular basis vector from a cell `ν` with `μ ≠ ν` and `¬ μ < ν` annihilates
`c.CellModule μ`. -/
theorem basis_smul_eq_zero_of_ne_of_not_lt {μ ν : Λ} (hne : μ ≠ ν) (hnlt : ¬ μ < ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 := by
  apply (c.cellModuleEquiv μ).injective
  rw [cellModuleEquiv_smul, c.cellRep_basis_of_ne_of_not_lt hne hnlt, Matrix.zero_mulVec, map_zero]

/-- A cellular basis vector from a cell `ν` with `¬ μ ≤ ν` annihilates `c.CellModule μ`. -/
theorem basis_smul_eq_zero_of_not_le {μ ν : Λ} (h : ¬ μ ≤ ν) (x y : M ν)
    (w : c.CellModule μ) : c.basis ⟨ν, x, y⟩ • w = 0 :=
  c.basis_smul_eq_zero_of_ne_of_not_lt (fun hEq ↦ h hEq.le) (fun hlt ↦ h hlt.le) x y w

/-- `A(≤ν)` acts as zero on `c.CellModule μ` whenever `¬ μ ≤ ν`. -/
theorem smul_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    (m : c.CellModule μ) : x • m = 0 := by
  apply (c.cellModuleEquiv μ).injective
  simp [c.cellRep_eq_zero_of_mem_leSpan h hx]

/-- `A(≤ν)` acts as zero on any quotient of `c.CellModule μ` whenever `¬ μ ≤ ν`. -/
theorem smul_quotient_eq_zero_of_mem_leSpan {ν μ : Λ} (h : ¬ μ ≤ ν) {x : A} (hx : x ∈ c.leSpan ν)
    {N : Submodule A (c.CellModule μ)} (m : c.CellModule μ ⧸ N) : x • m = 0 := by
  induction m using Submodule.Quotient.induction_on with
  | _ y =>
    rw [← Submodule.Quotient.mk_smul, c.smul_eq_zero_of_mem_leSpan h hx, Submodule.Quotient.mk_zero]

/-- If `c.gramMatrix ν t s` is a unit, then every element of `c.CellModule ν` lies in the
`c.leSpan ν`-orbit of `c.cellBasis ν s`. -/
theorem exists_mem_leSpan_smul_cellBasis_eq {ν : Λ} {t s : M ν}
    (hts : IsUnit (c.gramMatrix ν t s)) (x : c.CellModule ν) :
    ∃ a ∈ c.leSpan ν, a • c.cellBasis ν s = x := by
  obtain ⟨u, hu⟩ := hts
  refine ⟨∑ w, ((c.cellBasis ν).repr x w * u.inv) • c.basis ⟨ν, w, t⟩,
    sum_mem fun w _ ↦ Submodule.smul_mem _ _ (c.basis_self_mem_leSpan ν w t), ?_⟩
  have hstep (w : M ν) :
      (((c.cellBasis ν).repr x w * u.inv) • c.basis ⟨ν, w, t⟩) • c.cellBasis ν s =
        (c.cellBasis ν).repr x w • c.cellBasis ν w := by
    rw [smul_assoc, c.basis_smul, c.cellForm_cellBasis, ← hu, smul_smul, mul_assoc,
      u.inv_val, mul_one]
  rw [Finset.sum_smul]
  simp_rw [hstep]
  exact (c.cellBasis ν).sum_repr x

/-- Over a commutative ring without zero divisors, a nonzero `A`-linear map from a cell module with
nonzero form into another cell module forces `μ = ν ∨ μ < ν`. -/
theorem eq_or_lt_of_linearMap_cellModule_ne_zero [NoZeroDivisors R] {ν μ : Λ}
    (hν : c.cellForm ν ≠ 0) {f : c.CellModule ν →ₗ[A] c.CellModule μ} (hf : f ≠ 0) :
    μ = ν ∨ μ < ν := by
  by_contra! h
  obtain ⟨t, s, hts⟩ := c.exists_gramMatrix_ne_zero hν
  apply hf
  have h0 (u : M ν) : f (c.cellBasis ν u) = 0 := by
    have hsmul : c.gramMatrix ν t s • f (c.cellBasis ν u) = 0 := by
      rw [← LinearMap.map_smul_of_tower, ← c.cellForm_cellBasis ν t s,
        ← c.basis_smul ν u t (c.cellBasis ν s), map_smul,
        c.basis_smul_eq_zero_of_ne_of_not_lt h.1 h.2]
    apply (c.cellModuleEquiv μ).injective
    ext i
    have hi := congrFun (congrArg (c.cellModuleEquiv μ) hsmul) i
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_zero, Pi.zero_apply, mul_eq_zero] at hi
    exact hi.resolve_left hts
  have hres : f.restrictScalars R = 0 := (c.cellBasis ν).ext h0
  ext x
  exact LinearMap.congr_fun hres x

/-- Order form of `eq_or_lt_of_linearMap_cellModule_ne_zero`: over a commutative ring without zero
divisors, a nonzero `A`-linear map `c.CellModule ν →ₗ[A] c.CellModule μ` from a cell with nonzero
form implies `μ ≤ ν`. -/
theorem le_of_linearMap_cellModule_ne_zero [NoZeroDivisors R] {ν μ : Λ}
    (hν : c.cellForm ν ≠ 0) {f : c.CellModule ν →ₗ[A] c.CellModule μ} (hf : f ≠ 0) : μ ≤ ν :=
  le_of_eq_or_lt (c.eq_or_lt_of_linearMap_cellModule_ne_zero hν hf)

/-- Given a left `A`-module `S`, an index `t₀ : M μ`, and a vector `x₀ : S` annihilated by
`c.lowerSpan μ`, standard coordinates induce an `A`-linear homomorphism `c.CellModule μ →ₗ[A] S`
sending `c.cellBasis μ u` to `c.basis ⟨μ, u, t₀⟩ • x₀`. -/
noncomputable def cellModuleHom {S : Type*} [AddCommGroup S] [Module A S] {μ : Λ} (t₀ : M μ)
    (x₀ : S) (hlow : ∀ z ∈ c.lowerSpan μ, z • x₀ = 0) : c.CellModule μ →ₗ[A] S where
  toFun w := ∑ u, algebraMap R A (c.cellModuleEquiv μ w u) • (c.basis ⟨μ, u, t₀⟩ • x₀)
  map_add' w₁ w₂ := by
    simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a w := by
    have hstep (u : M μ) : (a * c.basis ⟨μ, u, t₀⟩) • x₀ =
        ∑ q, algebraMap R A (c.cellRep μ a q u) • (c.basis ⟨μ, q, t₀⟩ • x₀) := by
      have hmem := hlow _ (c.mul_basis_sub_sum_mem a μ u t₀)
      rw [sub_smul, sub_eq_zero] at hmem
      rw [hmem, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      rw [Algebra.smul_def, mul_smul]
    rw [RingHom.id_apply, Finset.smul_sum]
    have lhs_eq : ∑ u, a • (algebraMap R A (c.cellModuleEquiv μ w u) •
        (c.basis ⟨μ, u, t₀⟩ • x₀)) =
        ∑ u, ∑ q, (algebraMap R A (c.cellModuleEquiv μ w u) *
          algebraMap R A (c.cellRep μ a q u)) • (c.basis ⟨μ, q, t₀⟩ • x₀) := by
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      calc a • (algebraMap R A (c.cellModuleEquiv μ w u) • (c.basis ⟨μ, u, t₀⟩ • x₀))
          = (algebraMap R A (c.cellModuleEquiv μ w u) * a) • (c.basis ⟨μ, u, t₀⟩ • x₀) := by
              rw [← mul_smul, Algebra.commutes]
        _ = algebraMap R A (c.cellModuleEquiv μ w u) • ((a * c.basis ⟨μ, u, t₀⟩) • x₀) := by
              rw [mul_smul, mul_smul]
        _ = _ := by
              rw [hstep u, Finset.smul_sum]
              exact Finset.sum_congr rfl fun q _ ↦ (mul_smul _ _ _).symm
    rw [lhs_eq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [cellModuleEquiv_smul, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun u _ ↦
      congrArg (· • (c.basis ⟨μ, q, t₀⟩ • x₀))
        ((congrArg (algebraMap R A) (mul_comm _ _)).trans (map_mul _ _ _))

/-- Evaluating `cellModuleHom` on a vector expands it in the standard cell coordinates. -/
theorem cellModuleHom_apply {S : Type*} [AddCommGroup S] [Module A S] {μ : Λ} (t₀ : M μ)
    (x₀ : S) (hlow : ∀ z ∈ c.lowerSpan μ, z • x₀ = 0) (w : c.CellModule μ) :
    c.cellModuleHom t₀ x₀ hlow w =
      ∑ u, algebraMap R A (c.cellModuleEquiv μ w u) • (c.basis ⟨μ, u, t₀⟩ • x₀) :=
  (rfl)

/-- `cellModuleHom` sends the standard basis vector `c.cellBasis μ s` to
`c.basis ⟨μ, s, t₀⟩ • x₀`. -/
@[simp]
theorem cellModuleHom_cellBasis {S : Type*} [AddCommGroup S] [Module A S] {μ : Λ} (t₀ : M μ)
    (x₀ : S) (hlow : ∀ z ∈ c.lowerSpan μ, z • x₀ = 0) (s : M μ) :
    c.cellModuleHom t₀ x₀ hlow (c.cellBasis μ s) = c.basis ⟨μ, s, t₀⟩ • x₀ := by
  simp [cellModuleHom, Pi.single_apply]

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

/-- Over any commutative ring, if `(c.gramMatrix μ).det` is a non-zero-divisor, then
`c.cellRadical μ = ⊥`. -/
theorem cellRadical_eq_bot_of_det_gramMatrix_mem_nonZeroDivisors {μ : Λ}
    (h : (c.gramMatrix μ).det ∈ nonZeroDivisors R) : c.cellRadical μ = ⊥ :=
  (c.nondegenerate_gramMatrix_iff_cellRadical_eq_bot μ).mp (.of_det_mem_nonZeroDivisors h)

section Map

variable {B : Type*} [Ring B] [Algebra R B]

omit [∀ μ, DecidableEq (M μ)] in
/-- The canonical `R`-linear equivalence between the cell modules of `c` and `c.map e`, preserving
coordinates in the standard cell basis. -/
noncomputable def mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) :
    c.CellModule μ ≃ₗ[R] (c.map e).CellModule μ :=
  (c.cellModuleEquiv μ).trans ((c.map e).cellModuleEquiv μ).symm

omit [∀ μ, DecidableEq (M μ)] in
/-- `mapCellModuleEquiv` preserves standard coordinates. -/
@[simp]
theorem cellModuleEquiv_mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) (x : c.CellModule μ) :
    (c.map e).cellModuleEquiv μ (c.mapCellModuleEquiv e μ x) = c.cellModuleEquiv μ x := by
  simp [mapCellModuleEquiv]

omit [∀ μ, DecidableEq (M μ)] in
/-- The inverse of `mapCellModuleEquiv` preserves standard coordinates. -/
@[simp]
theorem cellModuleEquiv_mapCellModuleEquiv_symm (e : A ≃ₐ[R] B) (μ : Λ)
    (x : (c.map e).CellModule μ) :
    c.cellModuleEquiv μ ((c.mapCellModuleEquiv e μ).symm x) = (c.map e).cellModuleEquiv μ x := by
  simp [mapCellModuleEquiv]

omit [∀ μ, DecidableEq (M μ)] in
/-- `mapCellModuleEquiv` carries each standard cell basis vector to the corresponding one. -/
@[simp]
theorem mapCellModuleEquiv_cellBasis (e : A ≃ₐ[R] B) (μ : Λ) (s : M μ) :
    c.mapCellModuleEquiv e μ (c.cellBasis μ s) = (c.map e).cellBasis μ s := by
  classical
  apply ((c.map e).cellModuleEquiv μ).injective
  simp

omit [∀ μ, DecidableEq (M μ)] in
/-- The inverse of `mapCellModuleEquiv` carries each standard cell basis vector back to `c`. -/
@[simp]
theorem mapCellModuleEquiv_symm_cellBasis (e : A ≃ₐ[R] B) (μ : Λ) (s : M μ) :
    (c.mapCellModuleEquiv e μ).symm ((c.map e).cellBasis μ s) = c.cellBasis μ s :=
  (c.mapCellModuleEquiv e μ).symm_apply_eq.mpr (c.mapCellModuleEquiv_cellBasis e μ s).symm

/-- `mapCellModuleEquiv` intertwines the action of `a : A` with the action of `e a : B`. -/
@[simp]
theorem mapCellModuleEquiv_smul (e : A ≃ₐ[R] B) (μ : Λ) (a : A) (x : c.CellModule μ) :
    c.mapCellModuleEquiv e μ (a • x) = e a • c.mapCellModuleEquiv e μ x := by
  apply ((c.map e).cellModuleEquiv μ).injective
  simp

/-- The inverse of `mapCellModuleEquiv` intertwines the action of `b : B` with `e.symm b : A`. -/
@[simp]
theorem mapCellModuleEquiv_symm_smul (e : A ≃ₐ[R] B) (μ : Λ) (b : B)
    (x : (c.map e).CellModule μ) :
    (c.mapCellModuleEquiv e μ).symm (b • x) =
      e.symm b • (c.mapCellModuleEquiv e μ).symm x := by
  apply (c.cellModuleEquiv μ).injective
  simp

/-- `mapCellModuleEquiv` is an isometry for the cell bilinear forms. -/
@[simp]
theorem cellForm_mapCellModuleEquiv (e : A ≃ₐ[R] B) (μ : Λ) (x y : c.CellModule μ) :
    (c.map e).cellForm μ (c.mapCellModuleEquiv e μ x) (c.mapCellModuleEquiv e μ y) =
      c.cellForm μ x y := by
  simp [cellForm_apply]

/-- The inverse of `mapCellModuleEquiv` is an isometry for the cell bilinear forms. -/
@[simp]
theorem cellForm_mapCellModuleEquiv_symm (e : A ≃ₐ[R] B) (μ : Λ)
    (x y : (c.map e).CellModule μ) :
    c.cellForm μ ((c.mapCellModuleEquiv e μ).symm x) ((c.mapCellModuleEquiv e μ).symm y) =
      (c.map e).cellForm μ x y := by
  simp [cellForm_apply]

/-- `mapCellModuleEquiv` identifies the cell radicals of `c` and `c.map e`. -/
theorem mapCellModuleEquiv_mem_cellRadical_map_iff (e : A ≃ₐ[R] B) (μ : Λ) (x : c.CellModule μ) :
    c.mapCellModuleEquiv e μ x ∈ (c.map e).cellRadical μ ↔ x ∈ c.cellRadical μ := by
  simp only [mem_cellRadical]
  refine ⟨fun hx y ↦ ?_, fun hx y ↦ ?_⟩
  · simpa using hx (c.mapCellModuleEquiv e μ y)
  · obtain ⟨y, rfl⟩ := (c.mapCellModuleEquiv e μ).surjective y
    simpa using hx y

/-- The inverse of `mapCellModuleEquiv` identifies the cell radicals of `c.map e` and `c`. -/
theorem mapCellModuleEquiv_symm_mem_cellRadical_iff (e : A ≃ₐ[R] B) (μ : Λ)
    (x : (c.map e).CellModule μ) :
    (c.mapCellModuleEquiv e μ).symm x ∈ c.cellRadical μ ↔ x ∈ (c.map e).cellRadical μ := by
  rw [← c.mapCellModuleEquiv_mem_cellRadical_map_iff e μ, LinearEquiv.apply_symm_apply]

/-- Vanishing of the cell form is invariant under `CellularBasis.map`. -/
@[simp]
theorem cellForm_map_eq_zero_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).cellForm μ = 0 ↔ c.cellForm μ = 0 := by
  simp only [cellForm_eq_zero_iff, gramMatrix_map]

/-- Triviality of the cell radical is invariant under `CellularBasis.map`. -/
@[simp]
theorem cellRadical_map_eq_bot_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    (c.map e).cellRadical μ = ⊥ ↔ c.cellRadical μ = ⊥ := by
  simp only [← nondegenerate_gramMatrix_iff_cellRadical_eq_bot, gramMatrix_map]

/-- Nondegeneracy of the cell form is invariant under `CellularBasis.map`. -/
@[simp]
theorem nondegenerate_cellForm_map_iff (e : A ≃ₐ[R] B) (μ : Λ) :
    ((c.map e).cellForm μ).Nondegenerate ↔ (c.cellForm μ).Nondegenerate := by
  simp only [nondegenerate_cellForm_iff_cellRadical_eq_bot, cellRadical_map_eq_bot_iff]

end Map

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

variable {μ} in
/-- Over a field, a cell module whose form is nonzero is itself simple precisely when its radical is
trivial. -/
theorem isSimpleModule_cellModule_iff_of_cellForm_ne_zero (h : d.cellForm μ ≠ 0) :
    IsSimpleModule B (d.CellModule μ) ↔ d.cellRadical μ = ⊥ :=
  ⟨fun _ ↦ (eq_bot_or_eq_top (d.cellRadical μ)).resolve_right
      (mt (d.cellRadical_eq_top_iff μ).mp h),
    fun hbot ↦ ((d.cellRadical μ).quotEquivOfEqBot hbot).symm.isSimpleModule_iff.mpr
      ((d.isSimpleModule_cellModule_quotient_iff μ).mpr h)⟩

variable {μ} in
/-- Over a field, a nonempty cell module with trivial cell radical is simple. -/
theorem isSimpleModule_cellModule_of_cellRadical_eq_bot [Nonempty (M μ)]
    (h : d.cellRadical μ = ⊥) : IsSimpleModule B (d.CellModule μ) := by
  have : Nontrivial (d.CellModule μ) := inferInstanceAs (Nontrivial (M μ → K))
  exact (d.isSimpleModule_cellModule_iff_of_cellForm_ne_zero
    (mt (d.cellRadical_eq_top_iff μ).mpr (h ▸ bot_ne_top))).mpr h

variable {μ} in
/-- Over a field, when `d.cellForm μ ≠ 0`, there is a standard basis vector of `d.CellModule μ`
whose `d.leSpan μ`-orbit is the entire cell module (Graham–Lehrer, Lemma 2.5). -/
theorem exists_cellBasis_forall_exists_mem_leSpan_smul_eq (hμ : d.cellForm μ ≠ 0) :
    ∃ s : M μ, ∀ x : d.CellModule μ, ∃ a ∈ d.leSpan μ, a • d.cellBasis μ s = x := by
  obtain ⟨_, s, hts⟩ := d.exists_gramMatrix_ne_zero hμ
  exact ⟨s, fun x ↦ d.exists_mem_leSpan_smul_cellBasis_eq (isUnit_iff_ne_zero.mpr hts) x⟩

end Field

end Preorder

end TauCeti.CellularBasis
