/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Naturality
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Topology.Algebra.SymplecticGroup

import TauCeti.Analysis.Matrix.SymplecticGroup.ConleyZehnder.Zero
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Eigenspace.Matrix

/-!
# The Conley–Zehnder index of a path of linear symplectic maps

The Conley–Zehnder index `TauCeti.GLSymplectic.conleyZehnderIndex` is defined for paths of
symplectic *matrices*. A Hamiltonian orbit, however, comes with a path of linear symplectic maps
of an abstract symplectic vector space: the linearized flow `dφ_t(x(0))` on a symplectic vector
space, or, on a manifold, the linearized flow read in a symplectic frame `Φ` of the tangent bundle
along the orbit, `Φ(x(t))⁻¹ ∘ dφ_t(x(0)) ∘ Φ(x(0))`, a path of linear symplectic maps of the model
fibre. This file attaches a Conley–Zehnder index to such paths without choosing coordinates.

Let `(V, ω)` be a finite-dimensional symplectic vector space. A *symplectic basis* `b` of `V`,
indexed by `ι ⊕ ι`, is one in which `ω` has the matrix `Matrix.J ι ℝ`. In such a basis the matrix
of a linear map preserving `ω` is symplectic (`TauCeti.SymplecticForm.toMatrix_mem_symplecticGroup`,
`TauCeti.SymplecticForm.toGLSymplectic`), and a path `Ψ` of linear maps preserving `ω` becomes a
path of symplectic matrices (`TauCeti.SymplecticForm.matrixPath`), continuous by
`TauCeti.SymplecticForm.continuous_toGLSymplectic`. Taking matrices is multiplicative: it sends the
identity to `1`, compositions to products and inverses to inverses
(`TauCeti.SymplecticForm.toGLSymplectic_id`, `TauCeti.SymplecticForm.toGLSymplectic_comp`,
`TauCeti.SymplecticForm.toGLSymplectic_symm`).

* **Independence of the basis.** Two symplectic bases `b` and `b'` indexed by the same type differ
  by the change of basis matrix `b'.toMatrix b`, which is itself symplectic
  (`LinearMap.BilinForm.basis_toMatrix_mem_symplecticGroup_of_toMatrix_eq_J`), and the matrices of
  each `Ψ t` in the two bases are conjugate by it. By the naturality of the Conley–Zehnder index of
  matrices (`TauCeti.GLSymplectic.conleyZehnderIndex_map_conj`), the two paths of matrices have the
  same index (`TauCeti.SymplecticForm.conleyZehnderIndex_matrixPath_eq`).
* **The index.** `TauCeti.SymplecticForm.conleyZehnderIndex ω Ψ hΨ` is the index of the matrices of
  `Ψ` in a symplectic basis indexed by `Fin m ⊕ Fin m`, which exists by
  `LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`. It equals the index of the matrices of
  `Ψ` in *every* such basis (`TauCeti.SymplecticForm.conleyZehnderIndex_eq`), since `2 m` is the
  dimension of `V`.
* **Naturality.** A linear symplectomorphism `e : (V, ω) ≃ (W, ω')` carries a path `Ψ` to the path
  `e ∘ Ψ ∘ e⁻¹` of the same index (`TauCeti.SymplecticForm.conleyZehnderIndex_map_conj`): it
  carries symplectic bases to symplectic bases without changing matrices. This is the invariance
  under a change of symplectic frame by a constant symplectomorphism. A frame change along a loop
  multiplies the matrix path by a loop of symplectic matrices
  (`TauCeti.SymplecticForm.toGLSymplectic_comp`), to which the loop axiom
  `TauCeti.GLSymplectic.conleyZehnderIndex_mul` of the matrix index applies.
* **The axioms of the matrix index carry over:** the index only depends on the path as a function
  of time (`TauCeti.SymplecticForm.conleyZehnderIndex_congr`), the constant path has index zero
  (`TauCeti.SymplecticForm.conleyZehnderIndex_refl`), the index is additive under concatenation
  (`TauCeti.SymplecticForm.conleyZehnderIndex_trans`) and changes sign under reversal
  (`TauCeti.SymplecticForm.conleyZehnderIndex_symm`), it is invariant under homotopies relative
  to the endpoints through linear symplectic maps
  (`TauCeti.SymplecticForm.conleyZehnderIndex_eq_of_homotopy`), and a path along which the
  eigenvalue `1` keeps its geometric multiplicity has index zero
  (`TauCeti.SymplecticForm.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq`), for instance a
  path through linear maps none of which has the eigenvalue `1`.

## References

* J. Robbin and D. Salamon, *The Maslov index for paths*, Topology **32** (1993), 827–844,
  Section 4 (the Conley–Zehnder index and its naturality).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index of a periodic orbit through a
  symplectic trivialization).
-/

public section

noncomputable section

open Matrix Module
open scoped unitInterval

namespace TauCeti.SymplecticForm

/-! ### Matrices in symplectic bases -/

section Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : SymplecticForm V)
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Matrices of symplectic maps are symplectic.** In a symplectic basis `b` of `(V, ω)`, one in
which `ω` has the matrix `J`, the matrix of a linear map preserving `ω` is a symplectic matrix. -/
theorem toMatrix_mem_symplecticGroup {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {A : V →ₗ[ℝ] V}
    (hA : ∀ u v, ω (A u) (A v) = ω u v) :
    LinearMap.toMatrix b b A ∈ symplecticGroup ι ℝ := by
  rw [SymplecticGroup.mem_iff', ← hb]
  exact (TauCeti.BilinForm.isIsometry_iff_toMatrix b).1 (TauCeti.BilinForm.isIsometry_iff.2 hA)

/-- The matrix of a linear map `A` preserving `ω` in a symplectic basis `b`, as an element of the
symplectic group `TauCeti.GLSymplectic`. -/
def toGLSymplectic {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) (A : V →ₗ[ℝ] V)
    (hA : ∀ u v, ω (A u) (A v) = ω u v) : GLSymplectic ι ℝ :=
  GLSymplectic.symplecticGroupContinuousMulEquiv ι ℝ
    ⟨LinearMap.toMatrix b b A, ω.toMatrix_mem_symplecticGroup hb hA⟩

/-- The underlying matrix of `TauCeti.SymplecticForm.toGLSymplectic` is the matrix of the map. -/
@[simp]
theorem coe_toGLSymplectic {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) (A : V →ₗ[ℝ] V)
    (hA : ∀ u v, ω (A u) (A v) = ω u v) :
    ((ω.toGLSymplectic hb A hA : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      LinearMap.toMatrix b b A := by
  simp [toGLSymplectic, GLSymplectic.coe_ofSymplecticGroup]

/-- The symplectic matrix of a linear map only depends on the map. -/
theorem toGLSymplectic_congr {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {A A' : V →ₗ[ℝ] V} (h : A = A')
    (hA : ∀ u v, ω (A u) (A v) = ω u v) (hA' : ∀ u v, ω (A' u) (A' v) = ω u v) :
    ω.toGLSymplectic hb A hA = ω.toGLSymplectic hb A' hA' := by
  subst h
  rfl

/-- The symplectic matrix of the identity is the identity. -/
@[simp]
theorem toGLSymplectic_id {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (h : ∀ u v, ω (LinearMap.id u) (LinearMap.id v) = ω u v) :
    ω.toGLSymplectic hb LinearMap.id h = 1 :=
  Subtype.ext (Units.ext (by simp))

/-- **Matrices of compositions.** The symplectic matrix of a composition of linear maps preserving
`ω` is the product of their symplectic matrices. -/
@[simp]
theorem toGLSymplectic_comp {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {A B : V →ₗ[ℝ] V}
    (hA : ∀ u v, ω (A u) (A v) = ω u v) (hB : ∀ u v, ω (B u) (B v) = ω u v)
    (h : ∀ u v, ω ((A ∘ₗ B) u) ((A ∘ₗ B) v) = ω u v) :
    ω.toGLSymplectic hb (A ∘ₗ B) h = ω.toGLSymplectic hb A hA * ω.toGLSymplectic hb B hB :=
  Subtype.ext (Units.ext (by simp [LinearMap.toMatrix_comp b b b]))

/-- The symplectic matrix of the inverse of a linear equivalence preserving `ω` is the inverse of
its symplectic matrix. -/
theorem toGLSymplectic_symm {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) (e : V ≃ₗ[ℝ] V)
    (he : ∀ u v, ω (e u) (e v) = ω u v) (h : ∀ u v, ω (e.symm u) (e.symm v) = ω u v) :
    ω.toGLSymplectic hb e.symm h = (ω.toGLSymplectic hb e he)⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right ?_).symm
  rw [← ω.toGLSymplectic_comp hb he h fun u v ↦ by simp,
    ω.toGLSymplectic_congr hb (A' := LinearMap.id) (by ext; simp) _ fun u v ↦ rfl,
    toGLSymplectic_id]

/-- The change of basis matrix `b'.toMatrix b` between two symplectic bases of `(V, ω)` indexed by
the same type, as a symplectic matrix. It conjugates the matrices of linear symplectic maps in `b`
to their matrices in `b'` (`TauCeti.SymplecticForm.toGLSymplectic_eq_basisChange_mul`). -/
def basisChange {b b' : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (hb' : LinearMap.BilinForm.toMatrix b' ω.toBilinForm = J ι ℝ) : GLSymplectic ι ℝ :=
  GLSymplectic.symplecticGroupContinuousMulEquiv ι ℝ
    ⟨_, LinearMap.BilinForm.basis_toMatrix_mem_symplecticGroup_of_toMatrix_eq_J hb' hb⟩

/-- **Change of symplectic basis.** The matrix of a linear symplectic map in a symplectic basis `b'`
is the conjugate `P M P⁻¹` of its matrix `M` in another symplectic basis `b`, by the change of
basis matrix `P = b'.toMatrix b`. -/
theorem toGLSymplectic_eq_basisChange_mul {b b' : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (hb' : LinearMap.BilinForm.toMatrix b' ω.toBilinForm = J ι ℝ) (A : V →ₗ[ℝ] V)
    (hA : ∀ u v, ω (A u) (A v) = ω u v) :
    ω.toGLSymplectic hb' A hA =
      ω.basisChange hb hb' * ω.toGLSymplectic hb A hA * (ω.basisChange hb hb')⁻¹ := by
  have hP : ((ω.basisChange hb hb' : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      b'.toMatrix b := by
    simp [basisChange, GLSymplectic.coe_ofSymplecticGroup]
  have hP_inv : (((ω.basisChange hb hb')⁻¹ : GLSymplectic ι ℝ) : GL (ι ⊕ ι) ℝ) =
      (b.toMatrix b' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
    rw [Subgroup.coe_inv, Matrix.coe_units_inv, hP]
    exact Matrix.inv_eq_right_inv (Basis.toMatrix_mul_toMatrix_flip b' b)
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, hP, hP_inv, coe_toGLSymplectic]
  exact (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' b b' b _).symm

end Matrix

/-! ### Paths of symplectic matrices -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The symplectic matrices, in a symplectic basis `b`, of a continuous family of linear maps
preserving `ω` depend continuously on the parameter. -/
theorem continuous_toGLSymplectic {X : Type*} [TopologicalSpace X] {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {f : X → V →L[ℝ] V}
    (hf : Continuous f) (hf' : ∀ p u v, ω (f p u) (f p v) = ω u v) :
    Continuous fun p ↦ ω.toGLSymplectic hb (f p) (hf' p) :=
  (GLSymplectic.symplecticGroupContinuousMulEquiv ι ℝ).continuous.comp
    (Continuous.subtype_mk ((LinearMap.continuous_of_finiteDimensional
      ((LinearMap.toMatrix b b).toLinearMap ∘ₗ ContinuousLinearMap.coeLM ℝ)).comp hf) _)

/-- The matrices, in a symplectic basis `b`, of a path `Ψ` of linear maps preserving `ω`, as a
path of symplectic matrices. -/
def matrixPath {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {A B : V →L[ℝ] V}
    (Ψ : Path A B) (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    Path (ω.toGLSymplectic hb A (by simpa using hΨ 0))
      (ω.toGLSymplectic hb B (by simpa using hΨ 1)) where
  toFun t := ω.toGLSymplectic hb (Ψ t) (hΨ t)
  continuous_toFun := ω.continuous_toGLSymplectic hb Ψ.continuous hΨ
  source' := ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap Ψ.source) _ _
  target' := ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap Ψ.target) _ _

/-- At each time, `TauCeti.SymplecticForm.matrixPath` is the symplectic matrix of the map. -/
@[simp]
theorem matrixPath_apply {b : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ) {A B : V →L[ℝ] V}
    (Ψ : Path A B) (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (t : I) :
    ω.matrixPath hb Ψ hΨ t = ω.toGLSymplectic hb (Ψ t) (hΨ t) :=
  (rfl)

/-- **The Conley–Zehnder index does not depend on the symplectic basis.** The matrices of a path
`Ψ` of linear maps preserving `ω` in two symplectic bases indexed by the same type have the same
Conley–Zehnder index: they are conjugate by the change of basis matrix, which is symplectic. -/
theorem conleyZehnderIndex_matrixPath_eq {b b' : Basis (ι ⊕ ι) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J ι ℝ)
    (hb' : LinearMap.BilinForm.toMatrix b' ω.toBilinForm = J ι ℝ) {A B : V →L[ℝ] V}
    (Ψ : Path A B) (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    GLSymplectic.conleyZehnderIndex (ω.matrixPath hb' Ψ hΨ) =
      GLSymplectic.conleyZehnderIndex (ω.matrixPath hb Ψ hΨ) := by
  -- In the basis `b'` the matrices are the conjugates `P M P⁻¹` of those in `b`.
  rw [← GLSymplectic.conleyZehnderIndex_map_conj (ω.basisChange hb hb') (ω.matrixPath hb Ψ hΨ)]
  exact GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦
    ω.toGLSymplectic_eq_basisChange_mul hb hb' _ (hΨ t)

/-! ### Operations on paths of linear symplectic maps -/

omit [FiniteDimensional ℝ V] in
/-- The concatenation of two paths of linear maps preserving `ω` runs through maps preserving
`ω`. -/
theorem apply_path_trans_apply {A B C : V →L[ℝ] V} {Ψ₁ : Path A B} {Ψ₂ : Path B C}
    (h₁ : ∀ t u v, ω (Ψ₁ t u) (Ψ₁ t v) = ω u v) (h₂ : ∀ t u v, ω (Ψ₂ t u) (Ψ₂ t v) = ω u v)
    (t : I) (u v : V) : ω ((Ψ₁.trans Ψ₂) t u) ((Ψ₁.trans Ψ₂) t v) = ω u v := by
  rw [Path.trans_apply]
  split_ifs
  exacts [h₁ _ u v, h₂ _ u v]

omit [FiniteDimensional ℝ V] in
/-- The reverse of a path of linear maps preserving `ω` runs through maps preserving `ω`. -/
theorem apply_path_symm_apply {A B : V →L[ℝ] V} {Ψ : Path A B}
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (t : I) (u v : V) :
    ω (Ψ.symm t u) (Ψ.symm t v) = ω u v := by
  rw [Path.symm_apply]
  exact hΨ _ u v

/-! ### The Conley–Zehnder index -/

/-- **The Conley–Zehnder index of a path of linear symplectic maps.** For a path `Ψ` of linear
maps of a finite-dimensional symplectic vector space `(V, ω)` preserving `ω`, this is the
Conley–Zehnder index of the path of its matrices in a symplectic basis indexed by `Fin m ⊕ Fin m`.
By `TauCeti.SymplecticForm.conleyZehnderIndex_eq` it does not depend on the basis. -/
def conleyZehnderIndex {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) : ℝ :=
  GLSymplectic.conleyZehnderIndex
    (ω.matrixPath (ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate).choose_spec.choose_spec
      Ψ hΨ)

/-- **The index in any symplectic basis.** The Conley–Zehnder index of a path of linear symplectic
maps is the Conley–Zehnder index of its matrices in any symplectic basis indexed by
`Fin m ⊕ Fin m`. -/
theorem conleyZehnderIndex_eq {m : ℕ} {b : Basis (Fin m ⊕ Fin m) ℝ V}
    (hb : LinearMap.BilinForm.toMatrix b ω.toBilinForm = J (Fin m) ℝ) {A B : V →L[ℝ] V}
    (Ψ : Path A B) (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    ω.conleyZehnderIndex Ψ hΨ = GLSymplectic.conleyZehnderIndex (ω.matrixPath hb Ψ hΨ) := by
  -- A symplectic basis indexed by `Fin k ⊕ Fin k` has `k = m`, since `V` has dimension `2 k`.
  have key (k : ℕ) (c : Basis (Fin k ⊕ Fin k) ℝ V)
      (hc : LinearMap.BilinForm.toMatrix c ω.toBilinForm = J (Fin k) ℝ) :
      GLSymplectic.conleyZehnderIndex (ω.matrixPath hc Ψ hΨ) =
        GLSymplectic.conleyZehnderIndex (ω.matrixPath hb Ψ hΨ) := by
    have h₁ := finrank_eq_card_basis c
    have h₂ := finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at h₁ h₂
    obtain rfl : k = m := by omega
    exact ω.conleyZehnderIndex_matrixPath_eq hb hc Ψ hΨ
  exact key _ _ _

/-- The Conley–Zehnder index of a path of linear symplectic maps only depends on the path as a
function of time, not on the way its endpoints are written. -/
theorem conleyZehnderIndex_congr {A B A' B' : V →L[ℝ] V} (Ψ : Path A B) (Ψ' : Path A' B')
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (h : ∀ t, Ψ t = Ψ' t) :
    ω.conleyZehnderIndex Ψ hΨ = ω.conleyZehnderIndex Ψ' fun t ↦ h t ▸ hΨ t := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb]
  exact GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦
    ω.toGLSymplectic_congr hb (congrArg ContinuousLinearMap.toLinearMap (h t)) (hΨ t) (h t ▸ hΨ t)

/-- The constant path has Conley–Zehnder index zero. -/
@[simp]
theorem conleyZehnderIndex_refl (A : V →L[ℝ] V)
    (hA : ∀ t u v, ω (Path.refl A t u) (Path.refl A t v) = ω u v) :
    ω.conleyZehnderIndex (Path.refl A) hA = 0 := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ← GLSymplectic.conleyZehnderIndex_refl
    (ω.toGLSymplectic hb A (by simpa using hA 0))]
  exact GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦ by simp

/-- **Catenation.** The Conley–Zehnder index of linear symplectic maps is additive under
concatenation of paths. -/
theorem conleyZehnderIndex_trans {A B C : V →L[ℝ] V} (Ψ₁ : Path A B) (Ψ₂ : Path B C)
    (h₁ : ∀ t u v, ω (Ψ₁ t u) (Ψ₁ t v) = ω u v) (h₂ : ∀ t u v, ω (Ψ₂ t u) (Ψ₂ t v) = ω u v) :
    ω.conleyZehnderIndex (Ψ₁.trans Ψ₂) (ω.apply_path_trans_apply h₁ h₂) =
      ω.conleyZehnderIndex Ψ₁ h₁ + ω.conleyZehnderIndex Ψ₂ h₂ := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb,
    ← GLSymplectic.conleyZehnderIndex_trans]
  refine GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦ ?_
  rw [matrixPath_apply]
  -- Both paths run through the first path on `[0, 1/2]` and through the second on `[1/2, 1]`.
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · conv_rhs => rw [Path.trans_apply, dite_eq_left ht, matrixPath_apply]
    exact ω.toGLSymplectic_congr hb (by rw [Path.trans_apply, dite_eq_left ht]) _ _
  · conv_rhs => rw [Path.trans_apply, dite_eq_right ht, matrixPath_apply]
    exact ω.toGLSymplectic_congr hb (by rw [Path.trans_apply, dite_eq_right ht]) _ _

/-- Reversing a path of linear symplectic maps negates its Conley–Zehnder index. -/
theorem conleyZehnderIndex_symm {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    ω.conleyZehnderIndex Ψ.symm (ω.apply_path_symm_apply hΨ) = -ω.conleyZehnderIndex Ψ hΨ := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb,
    ← GLSymplectic.conleyZehnderIndex_symm]
  exact GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦ by simp [Path.symm_apply]

/-- **The zero axiom.** A path of linear symplectic maps along which the eigenvalue `1` keeps the
same geometric multiplicity has Conley–Zehnder index zero. In particular a path through linear
maps none of which has the eigenvalue `1` has index zero. -/
theorem conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) {k : ℕ}
    (h : ∀ t, finrank ℝ (End.eigenspace (Ψ t : V →ₗ[ℝ] V) 1) = k) :
    ω.conleyZehnderIndex Ψ hΨ = 0 := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb]
  refine GLSymplectic.conleyZehnderIndex_eq_zero_of_finrank_eigenspace_eq _ (k := k) fun t ↦ ?_
  rw [matrixPath_apply, coe_toGLSymplectic, LinearMap.finrank_eigenspace_toLin'_toMatrix, h t]

/-- **Homotopy invariance.** Paths of linear symplectic maps which are homotopic relative to their
endpoints through linear symplectic maps have the same Conley–Zehnder index. -/
theorem conleyZehnderIndex_eq_of_homotopy {A B : V →L[ℝ] V} {Ψ₀ Ψ₁ : Path A B}
    (F : Path.Homotopy Ψ₀ Ψ₁) (hF : ∀ p u v, ω (F p u) (F p v) = ω u v) :
    ω.conleyZehnderIndex Ψ₀ (fun t ↦ F.apply_zero t ▸ hF (0, t)) =
      ω.conleyZehnderIndex Ψ₁ (fun t ↦ F.apply_one t ▸ hF (1, t)) := by
  set h₀ : ∀ t u v, ω (Ψ₀ t u) (Ψ₀ t v) = ω u v := fun t ↦ F.apply_zero t ▸ hF (0, t)
  set h₁ : ∀ t u v, ω (Ψ₁ t u) (Ψ₁ t v) = ω u v := fun t ↦ F.apply_one t ▸ hF (1, t)
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  rw [ω.conleyZehnderIndex_eq hb, ω.conleyZehnderIndex_eq hb]
  -- The matrices of `F` form a homotopy of paths of symplectic matrices.
  let G : Path.Homotopy (ω.matrixPath hb Ψ₀ h₀) (ω.matrixPath hb Ψ₁ h₁) :=
    { toFun := fun p ↦ ω.toGLSymplectic hb (F p) (hF p)
      continuous_toFun := ω.continuous_toGLSymplectic hb F.continuous hF
      map_zero_left := fun t ↦ ω.toGLSymplectic_congr hb
        (congrArg ContinuousLinearMap.toLinearMap (F.apply_zero t)) (hF (0, t)) (h₀ t)
      map_one_left := fun t ↦ ω.toGLSymplectic_congr hb
        (congrArg ContinuousLinearMap.toLinearMap (F.apply_one t)) (hF (1, t)) (h₁ t)
      prop' := fun s t ht ↦ ω.toGLSymplectic_congr hb
        (congrArg ContinuousLinearMap.toLinearMap (F.prop' s t ht)) (hF (s, t)) (h₀ t) }
  exact GLSymplectic.conleyZehnderIndex_eq_of_homotopic ⟨G⟩

/-! ### Naturality -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {ω' : SymplecticForm W}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- A linear symplectomorphism `e : (V, ω) ≃ (W, ω')` carries a path `Ψ` of linear maps of `V`
preserving `ω` to the path `e ∘ Ψ ∘ e⁻¹` of linear maps of `W` preserving `ω'`. -/
theorem apply_path_map_conj_apply (e : V ≃L[ℝ] W) (he : IsSymplectomorphism ω ω' e.toLinearEquiv)
    {A B : V →L[ℝ] V} {Ψ : Path A B} (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) (t : I)
    (u v : W) :
    ω' ((Ψ.map (f := fun C : V →L[ℝ] V ↦ (e : V →L[ℝ] W) ∘L C ∘L (e.symm : W →L[ℝ] V))
      (by fun_prop)) t u)
      ((Ψ.map (f := fun C : V →L[ℝ] V ↦ (e : V →L[ℝ] W) ∘L C ∘L (e.symm : W →L[ℝ] V))
        (by fun_prop)) t v) = ω' u v := by
  have he' (x y : V) : ω' (e x) (e y) = ω x y := he.apply x y
  have key := he' (Ψ t (e.symm u)) (Ψ t (e.symm v))
  rw [hΨ, ← he', e.apply_symm_apply, e.apply_symm_apply] at key
  simpa using key

/-- **Naturality of the Conley–Zehnder index.** A linear symplectomorphism `e : (V, ω) ≃ (W, ω')`
carries a path `Ψ` of linear symplectic maps of `V` to the path `e ∘ Ψ ∘ e⁻¹` of linear symplectic
maps of `W` with the same Conley–Zehnder index. In particular the index of the linearized flow
along an orbit, read in a symplectic frame, does not change when the frame is composed with a
constant linear symplectomorphism. -/
theorem conleyZehnderIndex_map_conj (e : V ≃L[ℝ] W)
    (he : IsSymplectomorphism ω ω' e.toLinearEquiv) {A B : V →L[ℝ] V} (Ψ : Path A B)
    (hΨ : ∀ t u v, ω (Ψ t u) (Ψ t v) = ω u v) :
    ω'.conleyZehnderIndex (Ψ.map (f := fun C : V →L[ℝ] V ↦ (e : V →L[ℝ] W) ∘L C ∘L
      (e.symm : W →L[ℝ] V)) (by fun_prop)) (apply_path_map_conj_apply ω e he hΨ) =
      ω.conleyZehnderIndex Ψ hΨ := by
  obtain ⟨m, b, hb⟩ := ω.isAlt.exists_basis_toMatrix_eq_J ω.nondegenerate
  -- The image of a symplectic basis under `e` is a symplectic basis with the same matrices.
  have hb' : LinearMap.BilinForm.toMatrix (b.map e.toLinearEquiv) ω'.toBilinForm = J (Fin m) ℝ := by
    rw [← hb]
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply]
    exact he.apply (b i) (b j)
  rw [ω'.conleyZehnderIndex_eq hb', ω.conleyZehnderIndex_eq hb]
  refine GLSymplectic.conleyZehnderIndex_congr _ _ fun t ↦ Subtype.ext (Units.ext ?_)
  rw [matrixPath_apply, matrixPath_apply, coe_toGLSymplectic, coe_toGLSymplectic]
  ext i j
  simp [LinearMap.toMatrix_apply, Basis.map_apply, Basis.map_repr]

end TauCeti.SymplecticForm
