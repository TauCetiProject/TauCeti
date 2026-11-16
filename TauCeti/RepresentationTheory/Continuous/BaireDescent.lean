/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.Descent

import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import TauCeti.LinearAlgebra.LinearMap.BaseChange
import TauCeti.NumberTheory.Padics.CoefficientField
import TauCeti.RepresentationTheory.Continuous.StableLattice

/-!
# Coefficient-field and integral descent for continuous representations

Let `Γ` be a compact Hausdorff topological group and `ℓ` a prime. Every continuous matrix
representation `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` has its image contained in `GL ι E` for a single
finite extension `E / ℚ_[ℓ]` inside `PadicAlgCl ℓ`, which may be chosen to contain any prescribed
finite intermediate field `K`.

The proof is a Baire-category argument: the finite subextensions `E` of `PadicAlgCl ℓ / ℚ_[ℓ]`
are countably many (`PadicAlgCl.countable_finiteDimensional`) and closed
(`PadicAlgCl.isClosed_of_finiteDimensional`), so the closed subgroups `H_E = ρ⁻¹(GL ι E)` form a
countable closed cover of the compact Hausdorff (hence Baire) group `Γ`. One `H_{E₀}` therefore
has nonempty interior, hence is open of finite index in `Γ`; adjoining the finitely many matrix
entries of coset representatives to `E₀ ⊔ K` yields a finite extension `E` containing `ρ(Γ)`.

From this we deduce:
* **Matrix–representation bridges** (`TauCeti.ContinuousRep.ofGL`, `TauCeti.ContinuousRep.toGL`,
  `TauCeti.ContinuousRep.ofGLToGLIso`, `TauCeti.ContinuousRep.liftGL`,
  `TauCeti.ContinuousRep.baseChangeOfGLIso`) linking `Γ →ₜ* GL ι A` with `ContinuousRep Γ A M`.
* **Abstract Baire descent** (`TauCeti.ContinuousRep.baire_descent_of_countable`) for any compact
  Baire group and algebraic extension with countably many closed finite subextensions, specialized
  to `PadicAlgCl ℓ` in `TauCeti.ContinuousRep.baire_descent`.
* **Simultaneous descent of finite diagrams** (`TauCeti.ContinuousRep.exists_descent_family`) and
  of a single representation (`TauCeti.ContinuousRep.exists_descent`) over `PadicAlgCl ℓ`, showing
  together with `TauCeti.RepresentationTheory.Descent` that the category of continuous
  representations over `PadicAlgCl ℓ` is the filtered 2-colimit of those over finite extensions
  of `ℚ_[ℓ]`.
* **Integral descent** (`TauCeti.ContinuousRep.exists_conj_mem_integerRing_GL`,
  `TauCeti.ContinuousRep.exists_integral_conj_GL`): combining `baire_descent` with
  `TauCeti.ContinuousRep.exists_stable_lattice` over the resulting nonarchimedean local field `E`
  shows every continuous `ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` is conjugate into `GL ι 𝒪[E]`, i.e., to
  matrices with entries in `E` of norm at most `1`.

## Main definitions

* `TauCeti.ContinuousRep.ofGL`: the continuous representation on `ι → A` attached to a continuous
  homomorphism `Γ →ₜ* GL ι A`.
* `TauCeti.ContinuousRep.toGL`: the continuous matrix homomorphism `Γ →ₜ* GL ι A` attached to a
  continuous representation and a finite basis.
* `TauCeti.ContinuousRep.ofGLToGLIso`: the canonical isomorphism `(ofGL (toGL ρ b)).Iso ρ`.
* `TauCeti.ContinuousRep.liftGL`: lifting a matrix homomorphism `Γ →ₜ* GL ι L` whose entries lie
  in an intermediate field `E` to `Γ →ₜ* GL ι E`.
* `TauCeti.ContinuousRep.baseChangeOfGLIso`: extension of scalars of `ofGL φ` corresponds to
  applying `algebraMap A B` entrywise.

## Main results

* `TauCeti.ContinuousRep.baire_descent_of_countable`
* `TauCeti.ContinuousRep.baire_descent`
* `TauCeti.ContinuousRep.exists_descent_family`
* `TauCeti.ContinuousRep.exists_descent`
* `TauCeti.ContinuousRep.exists_conj_mem_integerRing_GL`
* `TauCeti.ContinuousRep.exists_integral_conj_GL`

## References

* G. Böckle, M. Harris, C. Khare and J. A. Thorne, *$\hat{G}$-local systems on smooth projective
  curves are potentially automorphic*, Acta Math. 223 (2019), Theorem 4.8.
* F. Calegari and D. Geraghty, *Modularity lifting beyond the Taylor–Wiles method*, Invent. Math.
  211 (2018), Proposition 6.8.
* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open Matrix IntermediateField ValuativeRel
open scoped TensorProduct Topology

namespace TauCeti.ContinuousRep

section MatrixBridge

section OfGL

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [Fintype ι] [DecidableEq ι]

/-- **Continuous representation attached to a continuous matrix homomorphism.** An element `g : Γ`
acts on `ι → A` by left multiplication by the matrix `φ g`. -/
def ofGL (φ : Γ →ₜ* GL ι A) : ContinuousRep Γ A (ι → A) where
  toRepresentation :=
    { toFun g := Matrix.mulVecLin (φ g : Matrix ι ι A)
      map_one' := by
        ext v i
        simp
      map_mul' g h := by
        ext v i
        simp }
  continuous_action :=
    (Units.continuous_val.comp (φ.continuous.comp continuous_fst)).matrix_mulVec continuous_snd

@[simp]
theorem ofGL_apply (φ : Γ →ₜ* GL ι A) (g : Γ) (v : ι → A) :
    ofGL φ g v = (φ g : Matrix ι ι A).mulVec v :=
  (rfl)

end OfGL

section ToGL

variable {Γ A V ι : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [AddCommGroup V] [Module A V] [TopologicalSpace V] [IsModuleTopology A V]
  [Fintype ι] [DecidableEq ι]

/-- **Continuous matrix homomorphism attached to a continuous representation and a finite basis.**
The matrix of `g : Γ` is `LinearMap.toMatrixAlgEquiv b (ρ g)`. -/
noncomputable def toGL (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) : Γ →ₜ* GL ι A where
  toMonoidHom :=
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp ρ.toRepresentation.toHomUnits
  continuous_toFun := by
    refine Continuous.of_coeHom_comp ?_
    have hequiv : Continuous b.equivFun :=
      IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
    refine continuous_matrix fun i j ↦ ?_
    exact ((_root_.continuous_apply i).comp (hequiv.comp (ρ.continuous_orbit (b j)))).congr
      fun g ↦ (LinearMap.toMatrixAlgEquiv_apply b (ρ g) i j).symm

@[simp]
theorem coe_toGL (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (g : Γ) :
    (toGL ρ b g : Matrix ι ι A) = LinearMap.toMatrixAlgEquiv b (ρ g) :=
  (rfl)

@[simp]
theorem coe_toGL_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (g : Γ) (i j : ι) :
    (toGL ρ b g : Matrix ι ι A) i j = b.repr (ρ g (b j)) i :=
  LinearMap.toMatrixAlgEquiv_apply b (ρ g) i j

/-- **Matrix realization isomorphism.** Choosing a finite basis `b` identifies `ofGL (toGL ρ b)`
equivariantly and homeomorphically with `ρ`. -/
noncomputable def ofGLToGLIso (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) :
    Iso (ofGL (toGL ρ b)) ρ :=
  .ofEquiv (.mk b.equivFun.symm fun g ↦ by
    apply LinearMap.ext
    intro v
    apply b.equivFun.injective
    ext i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coe_toRepresentation,
      LinearEquiv.apply_symm_apply, ofGL_apply, Matrix.mulVec, dotProduct, coe_toGL_apply]
    rw [Module.Basis.equivFun_symm_apply, map_sum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _)

@[simp]
theorem ofGLToGLIso_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (v : ι → A) :
    ofGLToGLIso ρ b v = b.equivFun.symm v :=
  Iso.ofEquiv_apply _ v

@[simp]
theorem ofGLToGLIso_symm_apply (ρ : ContinuousRep Γ A V) (b : Module.Basis ι A V) (x : V) :
    (ofGLToGLIso ρ b).symm x = b.equivFun x :=
  EquivLike.injective (ofGLToGLIso ρ b) (by simp)

/-- Recovering a continuous matrix homomorphism from `ofGL` via the standard basis `Pi.basisFun`. -/
@[simp]
theorem toGL_ofGL (φ : Γ →ₜ* GL ι A) : toGL (ofGL φ) (Pi.basisFun A ι) = φ := by
  ext g i j
  simp [coe_toGL_apply, ofGL_apply, Matrix.mulVec_single, Matrix.col_apply]

end ToGL

section LiftGL

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

/-- An invertible matrix over `L` whose entries lie in an intermediate field `E` lifts uniquely
to an element of `GL ι E`. -/
private noncomputable def liftGLMatrix (E : IntermediateField K L) (A : GL ι L)
    (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) : GL ι E :=
  let M : Matrix ι ι E := Matrix.of fun i j ↦ ⟨(A : Matrix ι ι L) i j, hA i j⟩
  have hM : E.val.toRingHom.mapMatrix M = (A : Matrix ι ι L) := by
    ext i j
    rfl
  have hdet : M.det ≠ 0 := by
    intro h0
    have hdetA : (A : Matrix ι ι L).det = 0 := by
      rw [← hM, ← RingHom.map_det E.val.toRingHom M, h0, map_zero]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero hdetA
  ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)).unit

private theorem map_liftGLMatrix (E : IntermediateField K L) (A : GL ι L)
    (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) :
    Matrix.GeneralLinearGroup.map E.val.toRingHom (liftGLMatrix E A hA) = A := by
  ext i j
  rfl

private theorem mem_intermediateField_inv (E : IntermediateField K L) (A : GL ι L)
    (hA : ∀ i j, (A : Matrix ι ι L) i j ∈ E) (i j : ι) :
    ((A⁻¹ : GL ι L) : Matrix ι ι L) i j ∈ E := by
  have hinv := congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j)
    (congrArg Inv.inv (map_liftGLMatrix E A hA))
  rw [← map_inv] at hinv
  rw [← hinv]
  exact SetLike.coe_mem _

private theorem continuous_gl_entry {Γ R : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [CommRing R] [TopologicalSpace R] (ρ : Γ →ₜ* GL ι R) (i j : ι) :
    Continuous fun g : Γ ↦ (ρ g : Matrix ι ι R) i j :=
  (_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
    ((Units.continuous_val (M := Matrix ι ι R)).comp ρ.continuous))

private theorem continuous_gl_inv_entry {Γ R : Type*} [Monoid Γ] [TopologicalSpace Γ]
    [CommRing R] [TopologicalSpace R] (ρ : Γ →ₜ* GL ι R) (i j : ι) :
    Continuous fun g : Γ ↦ (((ρ g)⁻¹ : GL ι R) : Matrix ι ι R) i j :=
  (_root_.continuous_apply j).comp ((_root_.continuous_apply i).comp
    ((Units.continuous_coe_inv (M := Matrix ι ι R)).comp ρ.continuous))

/-- **Lifting a continuous matrix homomorphism to an intermediate field.** If every matrix entry
of `ρ : Γ →ₜ* GL ι L` lies in `E : IntermediateField K L`, then `ρ` lifts continuously to
`Γ →ₜ* GL ι E`. -/
noncomputable def liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : IntermediateField K L)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) : Γ →ₜ* GL ι E where
  toFun g := liftGLMatrix E (ρ g) (hE g)
  map_one' := by
    ext i j
    have h := congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j)
      ((map_liftGLMatrix E (ρ 1) (hE 1)).trans
        (by rw [map_one, ← map_one (Matrix.GeneralLinearGroup.map E.val.toRingHom)]))
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      IntermediateField.coe_val] using h
  map_mul' g h := by
    ext i j
    have h' := congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j)
      ((map_liftGLMatrix E (ρ (g * h)) (hE (g * h))).trans
        (by rw [map_mul, ← map_liftGLMatrix E (ρ g) (hE g),
          ← map_liftGLMatrix E (ρ h) (hE h), ← map_mul]))
    simpa only [Matrix.GeneralLinearGroup.map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      IntermediateField.coe_val] using h'
  continuous_toFun := by
    refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j ↦ ?_,
      continuous_matrix fun i j ↦ ?_⟩
    · exact (continuous_gl_entry ρ i j).subtype_mk _
    · have hinv (g : Γ) : ((((liftGLMatrix E (ρ g) (hE g))⁻¹ : GL ι E) : Matrix ι ι E) i j : L) =
          (((ρ g)⁻¹ : GL ι L) : Matrix ι ι L) i j := by
        have heq : Matrix.GeneralLinearGroup.map E.val.toRingHom (liftGLMatrix E (ρ g) (hE g))⁻¹ =
            (ρ g)⁻¹ := by
          rw [map_inv, map_liftGLMatrix]
        exact congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j) heq
      exact ((continuous_gl_inv_entry ρ i j).congr fun g ↦ (hinv g).symm).subtype_mk _

@[simp]
theorem map_liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : IntermediateField K L)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) :
    Matrix.GeneralLinearGroup.map (E.val : E →+* L) (liftGL ρ E hE g) = ρ g :=
  map_liftGLMatrix E (ρ g) (hE g)

@[simp]
theorem coe_liftGL {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : IntermediateField K L)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E) (g : Γ) (i j : ι) :
    ((liftGL ρ E hE g : Matrix ι ι E) i j : L) = (ρ g : Matrix ι ι L) i j :=
  (rfl)

/-- **Uniqueness of `liftGL`.** A continuous homomorphism `Γ →ₜ* GL ι E` pushing forward to `ρ`
equals `liftGL ρ E hE`. -/
theorem liftGL_unique {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] [TopologicalSpace L]
    (ρ : Γ →ₜ* GL ι L) (E : IntermediateField K L)
    (hE : ∀ g i j, (ρ g : Matrix ι ι L) i j ∈ E)
    {φ : Γ →ₜ* GL ι E}
    (hφ : ∀ g, Matrix.GeneralLinearGroup.map (E.val : E →+* L) (φ g) = ρ g) :
    φ = liftGL ρ E hE := by
  ext g i j
  simpa only [Matrix.GeneralLinearGroup.map_apply, RingHom.coe_coe,
    IntermediateField.coe_val, coe_liftGL] using
    congrArg (fun u : GL ι L ↦ (u : Matrix ι ι L) i j) (hφ g)

end LiftGL

section BaseChangeOfGL

variable {Γ A ι : Type*} [Monoid Γ] [TopologicalSpace Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
  [Fintype ι] [DecidableEq ι]

variable (B : Type*) [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B]
  [Algebra A B] [ContinuousSMul A B]
  [TopologicalSpace (B ⊗[A] (ι → A))] [IsModuleTopology B (B ⊗[A] (ι → A))]

/-- **Extension of scalars of a matrix representation** identifies `B ⊗[A] (ι → A)` with `ι → B`
on which `Γ` acts by the image matrices under `algebraMap A B`, through
`TensorProduct.piScalarRight`. -/
def baseChangeOfGLIso (φ : Γ →ₜ* GL ι A) :
    Iso ((ofGL φ).baseChange B)
      (ofGL (ContinuousMonoidHom.comp
        ⟨Matrix.GeneralLinearGroup.map (algebraMap A B),
          Continuous.units_map _ (continuous_matrix fun i j ↦
            (continuous_algebraMap A B).comp
              ((_root_.continuous_apply j).comp (_root_.continuous_apply i)))⟩
        φ)) :=
  .ofEquiv (.mk (TensorProduct.piScalarRight A B B ι) fun g ↦ by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b v =>
      ext i
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coe_toRepresentation,
        toRepresentation_baseChange, Representation.baseChange_apply, LinearMap.baseChange_tmul,
        ofGL_apply, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
        Matrix.mulVec, dotProduct, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ ↦ mul_assoc _ _ _)

@[simp]
theorem baseChangeOfGLIso_tmul (φ : Γ →ₜ* GL ι A) (b : B) (v : ι → A) :
    baseChangeOfGLIso B φ (b ⊗ₜ v) = fun i ↦ v i • b :=
  (Iso.ofEquiv_apply _ _).trans (TensorProduct.piScalarRightHom_tmul A B B ι b v)

@[simp]
theorem baseChangeOfGLIso_symm_apply (φ : Γ →ₜ* GL ι A) (w : ι → B) :
    (baseChangeOfGLIso B φ).symm w = (TensorProduct.piScalarRight A B B ι).symm w :=
  EquivLike.injective (baseChangeOfGLIso B φ) (by
    rw [Iso.apply_symm_apply, baseChangeOfGLIso, Iso.ofEquiv_apply, Representation.Equiv.mk_apply]
    exact ((TensorProduct.piScalarRight A B B ι).apply_symm_apply w).symm)

end BaseChangeOfGL

end MatrixBridge

section BaireDescent

/-- The subgroup of elements whose image matrices have all entries in an intermediate field `E`. -/
private def entriesSubgroup {Γ K L ι : Type*} [Group Γ] [Field K] [Field L] [Algebra K L]
    [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι L) (E : IntermediateField K L) : Subgroup Γ where
  carrier := {g | ∀ i j, (ρ g : Matrix ι ι L) i j ∈ E}
  one_mem' i j := by
    rw [map_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact E.one_mem
    · exact E.zero_mem
  mul_mem' {g h} hg hh i j := by
    rw [map_mul, Units.val_mul, Matrix.mul_apply]
    exact E.sum_mem fun k _ ↦ E.mul_mem (hg i k) (hh k j)
  inv_mem' {g} hg i j := by
    rw [map_inv]
    exact mem_intermediateField_inv E (ρ g) hg i j

private theorem isClosed_entriesSubgroup {Γ K L ι : Type*} [Group Γ] [TopologicalSpace Γ]
    [Field K] [Field L] [Algebra K L] [TopologicalSpace L] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι L) {E : IntermediateField K L} (hE : IsClosed (E : Set L)) :
    IsClosed (entriesSubgroup (ρ : Γ →* GL ι L) E : Set Γ) := by
  have heq : (entriesSubgroup (ρ : Γ →* GL ι L) E : Set Γ) =
      ⋂ i, ⋂ j, (fun g : Γ ↦ (ρ g : Matrix ι ι L) i j) ⁻¹' (E : Set L) := by
    ext g
    simp [entriesSubgroup]
  rw [heq]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ hE.preimage (continuous_gl_entry ρ i j)

/-- **Abstract Baire-category descent for continuous matrix representations.** If `Γ` is a
compact Baire group and `L / K` is an algebraic field extension whose finite intermediate fields
are countably many and closed in `L`, then every continuous `ρ : Γ →ₜ* GL ι L` has entries in a
single finite intermediate field containing any prescribed finite `K₀`. -/
theorem baire_descent_of_countable
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [BaireSpace Γ]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    [TopologicalSpace L]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcount : {E : IntermediateField K L | FiniteDimensional K E}.Countable)
    (hclosed : ∀ E : IntermediateField K L, FiniteDimensional K E → IsClosed (E : Set L))
    (ρ : Γ →ₜ* GL ι L)
    (K₀ : IntermediateField K L) [FiniteDimensional K K₀] :
    ∃ E : IntermediateField K L, K₀ ≤ E ∧ FiniteDimensional K E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι L) i j ∈ E := by
  let S := {E : IntermediateField K L | FiniteDimensional K E}
  have : Countable S := hcount.to_subtype
  let H (E : S) : Subgroup Γ := entriesSubgroup (ρ : Γ →* GL ι L) E.1
  have hHclosed (E : S) : IsClosed (H E : Set Γ) :=
    isClosed_entriesSubgroup ρ (hclosed E.1 E.2)
  have hcover : (⋃ E : S, (H E : Set Γ)) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun g ↦ ?_
    let s : Set L := Set.range fun p : ι × ι ↦ (ρ g : Matrix ι ι L) p.1 p.2
    have : Finite s := Set.finite_range _
    exact Set.mem_iUnion.mpr ⟨⟨IntermediateField.adjoin K s,
      IntermediateField.finiteDimensional_adjoin fun x _ ↦
        (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩,
      fun i j ↦ IntermediateField.subset_adjoin K s ⟨(i, j), rfl⟩⟩
  -- By Baire category, some `H E₀` has nonempty interior, hence is open of finite index.
  obtain ⟨E₀, ⟨x, hx⟩⟩ := nonempty_interior_of_iUnion_of_closed hHclosed hcover
  have hopen : IsOpen (H E₀ : Set Γ) :=
    (H E₀).isOpen_of_mem_nhds (g := x) (mem_interior_iff_mem_nhds.mp hx)
  have : Finite (Γ ⧸ H E₀) := (H E₀).quotient_finite_of_isOpen hopen
  let T : Set L := Set.range fun p : (Γ ⧸ H E₀) × ι × ι ↦
    (ρ (Quotient.out p.1) : Matrix ι ι L) p.2.1 p.2.2
  have : Finite T := Set.finite_range _
  have : FiniteDimensional K E₀.1 := E₀.2
  have : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun y _ ↦
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  let E : IntermediateField K L := K₀ ⊔ E₀.1 ⊔ IntermediateField.adjoin K T
  refine ⟨E, le_sup_of_le_left le_sup_left, inferInstance, fun g i j ↦ ?_⟩
  let q : Γ ⧸ H E₀ := QuotientGroup.mk g
  let r : Γ := Quotient.out q
  have hrg : r⁻¹ * g ∈ H E₀ := by
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq q
  rw [← mul_inv_cancel_left r g, map_mul, Units.val_mul, Matrix.mul_apply]
  refine E.sum_mem fun k _ ↦ E.mul_mem ?_ ?_
  · exact (le_sup_right : IntermediateField.adjoin K T ≤ E)
      (IntermediateField.subset_adjoin K T ⟨(q, i, k), rfl⟩)
  · exact (le_sup_of_le_left le_sup_right : E₀.1 ≤ E) (hrg k j)

/-- **Coefficient-field descent from `PadicAlgCl ℓ`.** Every continuous matrix representation
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group has entries in a single finite
extension `E / ℚ_[ℓ]` containing any prescribed finite intermediate field `K`. -/
theorem baire_descent {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [SeparatelyContinuousMul Γ]
    [CompactSpace Γ] [T2Space Γ] (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ))
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ), K ≤ E ∧ FiniteDimensional ℚ_[ℓ] E ∧
      ∀ (g : Γ) (i j : ι), (ρ g : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E :=
  baire_descent_of_countable (PadicAlgCl.countable_finiteDimensional ℓ)
    (fun E _ ↦ PadicAlgCl.isClosed_of_finiteDimensional ℓ E) ρ K

end BaireDescent

section DiagramDescent

/-- Algebraic identification of `L ⊗[E] (ι → E)` with `V` attached to a basis `b`. -/
private noncomputable def descentLinearEquiv {E L V ι : Type*} [Field E] [Field L] [Algebra E L]
    [AddCommGroup V] [Module L V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι L V) :
    L ⊗[E] (ι → E) ≃ₗ[L] V :=
  (TensorProduct.piScalarRight E L L ι).trans b.equivFun.symm

private theorem descentLinearEquiv_intertwining {E L V W ιV ιW : Type*} [Field E] [Field L]
    [Algebra E L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    [Fintype ιV] [DecidableEq ιV] [Fintype ιW] [DecidableEq ιW]
    (bV : Module.Basis ιV L V) (bW : Module.Basis ιW L W)
    (f : V →ₗ[L] W) (M : Matrix ιW ιV E)
    (hM : ∀ i j, algebraMap E L (M i j) = LinearMap.toMatrix bV bW f i j)
    (x : L ⊗[E] (ιV → E)) :
    descentLinearEquiv bW ((Matrix.mulVecLin M).baseChange L x) =
      f (descentLinearEquiv bV x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c v =>
    apply bW.equivFun.injective
    ext i
    simp only [descentLinearEquiv, LinearEquiv.trans_apply, LinearMap.baseChange_tmul,
      Matrix.mulVecLin_apply, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_symm_apply, map_sum, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, Module.Basis.equivFun_apply,
      smul_eq_mul, Matrix.mulVec, dotProduct]
    simp only [Algebra.smul_def, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hM i j, LinearMap.toMatrix_apply]
    ring

private theorem descentLinearEquiv_equivariant {Γ K L V ι : Type*} [Group Γ] [TopologicalSpace Γ]
    [ContinuousInv Γ] [Field K] [Field L] [Algebra K L] [TopologicalSpace L]
    [IsTopologicalSemiring L] [AddCommGroup V] [Module L V] [TopologicalSpace V]
    [IsModuleTopology L V] [Fintype ι] [DecidableEq ι]
    (ρ : ContinuousRep Γ L V) (b : Module.Basis ι L V)
    (E : IntermediateField K L) [IsTopologicalSemiring E]
    (hE : ∀ g i j, (toGL ρ b g : Matrix ι ι L) i j ∈ E)
    (g : Γ) (x : L ⊗[E] (ι → E)) :
    descentLinearEquiv b (((ofGL (liftGL (toGL ρ b) E hE)).toRepresentation.baseChange L) g x) =
      ρ g (descentLinearEquiv b x) := by
  rw [Representation.baseChange_apply]
  exact descentLinearEquiv_intertwining b b (ρ g) (liftGL (toGL ρ b) E hE g : Matrix ι ι E)
    (fun i j ↦ ((coe_liftGL (toGL ρ b) E hE g i j).trans (coe_toGL_apply ρ b g i j)).trans
      (LinearMap.toMatrix_apply b b (ρ g) i j).symm) x

/-- **Simultaneous descent of a finite diagram of continuous representations over `PadicAlgCl ℓ`.**
Any finite family of finite-dimensional continuous representations of a compact Hausdorff group
`Γ` over `PadicAlgCl ℓ` together with finitely many intertwining maps between them descends to a
single finite extension `E / ℚ_[ℓ]` containing any prescribed finite intermediate field `K`. -/
theorem exists_descent_family {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [T2Space Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {α β : Type*} [Finite α] [Finite β]
    {V : α → Type*} [∀ a, AddCommGroup (V a)] [∀ a, Module (PadicAlgCl ℓ) (V a)]
    [∀ a, FiniteDimensional (PadicAlgCl ℓ) (V a)]
    [∀ a, TopologicalSpace (V a)] [∀ a, IsModuleTopology (PadicAlgCl ℓ) (V a)]
    (ρ : ∀ a : α, ContinuousRep Γ (PadicAlgCl ℓ) (V a))
    {src dst : β → α}
    (f : ∀ j : β, Representation.IntertwiningMap
      (ρ (src j)).toRepresentation (ρ (dst j)).toRepresentation)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ∀ a : α, ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))
      (fE : ∀ j : β, Representation.IntertwiningMap
        (ρE (src j)).toRepresentation (ρE (dst j)).toRepresentation),
      K ≤ E ∧
        ∀ [∀ a, TopologicalSpace ((PadicAlgCl ℓ) ⊗[E]
            (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))]
          [∀ a, IsModuleTopology (PadicAlgCl ℓ) ((PadicAlgCl ℓ) ⊗[E]
            (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E))],
          ∃ e : ∀ a : α, ((ρE a).baseChange (PadicAlgCl ℓ)).Iso (ρ a),
            ∀ (j : β) (x),
              e (dst j) ((fE j).baseChange (PadicAlgCl ℓ) x) = f j (e (src j) x) := by
  let b (a : α) := Module.finBasis (PadicAlgCl ℓ) (V a)
  choose Eobj _ hfinObj hmemObj using fun a ↦ baire_descent ℓ (toGL (ρ a) (b a)) K
  let M (j : β) := LinearMap.toMatrix (b (src j)) (b (dst j)) (f j).toLinearMap
  let Emor (j : β) : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
    IntermediateField.adjoin ℚ_[ℓ] (Set.range fun p : _ × _ ↦ M j p.1 p.2)
  have hfinMor (j : β) : FiniteDimensional ℚ_[ℓ] (Emor j) := by
    have : Finite (Set.range fun p : _ × _ ↦ M j p.1 p.2) := Set.finite_range _
    exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := K ⊔ (⨆ a, Eobj a) ⊔ (⨆ j, Emor j)
  have hmemE (a : α) (g : Γ) (r c : Fin (Module.finrank (PadicAlgCl ℓ) (V a))) :
      (toGL (ρ a) (b a) g : Matrix _ _ (PadicAlgCl ℓ)) r c ∈ E :=
    le_sup_of_le_left (le_sup_of_le_right (le_iSup Eobj a)) (hmemObj a g r c)
  let ρE (a : α) : ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) (V a)) → E) :=
    ofGL (liftGL (toGL (ρ a) (b a)) E (hmemE a))
  have hmorE (j : β) : Emor j ≤ E := le_trans (le_iSup Emor j) le_sup_right
  let ME (j : β) : Matrix _ _ E := Matrix.of fun r c ↦
    ⟨M j r c, hmorE j (IntermediateField.subset_adjoin ℚ_[ℓ] _ ⟨(r, c), rfl⟩)⟩
  have hcompat (j : β) (x) :
      descentLinearEquiv (b (dst j)) ((Matrix.mulVecLin (ME j)).baseChange (PadicAlgCl ℓ) x) =
        f j (descentLinearEquiv (b (src j)) x) :=
    descentLinearEquiv_intertwining (b (src j)) (b (dst j)) (f j).toLinearMap (ME j)
      (fun _ _ ↦ rfl) x
  let fE (j : β) : Representation.IntertwiningMap
      (ρE (src j)).toRepresentation (ρE (dst j)).toRepresentation :=
    { toLinearMap := Matrix.mulVecLin (ME j)
      isIntertwining' g := by
        apply LinearMap.baseChange_injective (R := E) (A := PadicAlgCl ℓ)
        refine LinearMap.ext fun x ↦ (descentLinearEquiv (b (dst j))).injective ?_
        simp only [LinearMap.baseChange_comp, LinearMap.comp_apply,
          ← Representation.baseChange_apply, hcompat, ρE, descentLinearEquiv_equivariant]
        simpa only [LinearMap.comp_apply, Representation.IntertwiningMap.coe_toLinearMap,
          coe_toRepresentation] using
          LinearMap.congr_fun ((f j).isIntertwining' g) (descentLinearEquiv (b (src j)) x) }
  refine ⟨E, inferInstance, ρE, fE, le_sup_of_le_left le_sup_left, ?_⟩
  intro _ _
  let e (a : α) : ((ρE a).baseChange (PadicAlgCl ℓ)).Iso (ρ a) :=
    .ofEquiv (.mk (descentLinearEquiv (b a)) fun g ↦ LinearMap.ext fun x ↦ by
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, toRepresentation_baseChange,
        coe_toRepresentation] using descentLinearEquiv_equivariant (ρ a) (b a) E (hmemE a) g x)
  exact ⟨e, fun j x ↦ by
    simpa only [e, fE, Iso.ofEquiv_apply, Representation.Equiv.mk_apply,
      ← Representation.IntertwiningMap.coe_toLinearMap,
      Representation.IntertwiningMap.toLinearMap_baseChange] using hcompat j x⟩

/-- **Object descent for a continuous representation over `PadicAlgCl ℓ`.** Every
finite-dimensional continuous representation of a compact Hausdorff group over `PadicAlgCl ℓ`
descends to a finite extension `E / ℚ_[ℓ]` containing any prescribed finite `K`. -/
theorem exists_descent {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [ContinuousInv Γ] [CompactSpace Γ] [T2Space Γ]
    (ℓ : ℕ) [Fact ℓ.Prime] {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    [FiniteDimensional (PadicAlgCl ℓ) V] [TopologicalSpace V] [IsModuleTopology (PadicAlgCl ℓ) V]
    (ρ : ContinuousRep Γ (PadicAlgCl ℓ) V)
    (K : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] K] :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
      (ρE : ContinuousRep Γ E (Fin (Module.finrank (PadicAlgCl ℓ) V) → E)),
      K ≤ E ∧
        ∀ [TopologicalSpace ((PadicAlgCl ℓ) ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))]
          [IsModuleTopology (PadicAlgCl ℓ)
            ((PadicAlgCl ℓ) ⊗[E] (Fin (Module.finrank (PadicAlgCl ℓ) V) → E))],
          Nonempty (((ρE.baseChange (PadicAlgCl ℓ)).Iso ρ)) := by
  obtain ⟨E, hfinE, ρE, _, hKE, he⟩ := exists_descent_family ℓ (α := Unit) (β := Empty)
    (V := fun _ ↦ V) (fun _ ↦ ρ) (src := Empty.elim) (dst := Empty.elim)
    (fun j ↦ j.elim) K
  refine ⟨E, hfinE, ρE (), hKE, ?_⟩
  intro hT hM
  obtain ⟨e, _⟩ := @he (fun _ ↦ hT) (fun _ ↦ hM)
  exact ⟨e ()⟩

end DiagramDescent

section IntegralDescent

/-- **Integral model over a nonarchimedean local field.** Every continuous matrix representation
`ρ : Γ →ₜ* GL ι E` of a compact group over a nonarchimedean local field `E` is conjugate in
`GL ι E` to one whose entries lie in the valuation ring `𝒪[E]`. -/
theorem exists_conj_mem_integerRing_GL {Γ E ι : Type*} [Group Γ] [TopologicalSpace Γ]
    [CompactSpace Γ] [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι E) :
    ∃ P : GL ι E, ∀ (g : Γ) (i j : ι), (P * ρ g * P⁻¹ : Matrix ι ι E) i j ∈ 𝒪[E] := by
  let σ : ContinuousRep Γ E (ι → E) := ofGL ρ
  obtain ⟨Λ, hΛ, hstab⟩ := σ.exists_stable_lattice
  have : Module.IsTorsionFree 𝒪[E] E :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (IsFractionRing.injective 𝒪[E] E)
  let b₀ := Module.Free.chooseBasis 𝒪[E] Λ
  let bΛ : Module.Basis ι 𝒪[E] Λ :=
    b₀.reindex ((b₀.extendOfIsLattice E).indexEquiv (Pi.basisFun E ι))
  let b : Module.Basis ι E (ι → E) := bΛ.extendOfIsLattice E
  -- Conjugating by the coordinate map `b.equivFun` expresses `σ g` in the lattice basis `b`.
  let P : GL ι E :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun)
  refine ⟨P, fun g i j ↦ ?_⟩
  have htoLin : Matrix.GeneralLinearGroup.toLin (P * ρ g * P⁻¹) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun *
        Matrix.GeneralLinearGroup.toLin (ρ g) *
        (LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun)⁻¹ := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hsingle : b.equivFun⁻¹ (Pi.single j (1 : E)) = b j := by
    apply b.equivFun.injective
    ext k
    simp [Pi.single_apply]
  have hentry : (P * ρ g * P⁻¹ : Matrix ι ι E) i j = b.repr (σ g (b j)) i := by
    have hlin := congrArg (fun f : LinearMap.GeneralLinearGroup E (ι → E) ↦
        (f : (ι → E) →ₗ[E] (ι → E)) (Pi.single j (1 : E)) i) htoLin
    rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_single, Pi.smul_apply, op_smul_eq_mul, mul_one, Matrix.col_apply] at hlin
    rw [← LinearMap.GeneralLinearGroup.ofLinearEquiv_inv] at hlin
    simpa only [Units.val_mul, mul_apply_eq_comp, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv,
      Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply, hsingle, σ, ofGL_apply,
      Module.Basis.equivFun_apply] using hlin
  rw [hentry]
  have hσbj : σ g (b j) ∈ Submodule.span 𝒪[E] (Set.range b) := by
    rw [bΛ.span_range_extendOfIsLattice]
    exact hstab g _ (bΛ.extendOfIsLattice_apply E j ▸ (bΛ j).2)
  obtain ⟨a, ha⟩ := (b.mem_span_iff_repr_mem 𝒪[E] (σ g (b j))).mp hσbj i
  exact ha ▸ a.2

/-- **Integral descent over `PadicAlgCl ℓ`.** Every continuous matrix representation
`ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)` of a compact Hausdorff group is conjugate into `GL ι 𝒪[E]` for
a finite extension `E / ℚ_[ℓ]`: its conjugates have all entries in `E` of norm at most `1`. -/
theorem exists_integral_conj_GL {Γ : Type*} [Group Γ] [TopologicalSpace Γ]
    [SeparatelyContinuousMul Γ] [CompactSpace Γ] [T2Space Γ] (ℓ : ℕ) [Fact ℓ.Prime]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : Γ →ₜ* GL ι (PadicAlgCl ℓ)) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (P : GL ι (PadicAlgCl ℓ)),
      FiniteDimensional ℚ_[ℓ] E ∧ ∀ (g : Γ) (i j : ι),
        (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j ∈ E ∧
        ‖(P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j‖ ≤ 1 := by
  obtain ⟨E, -, hfin, hE⟩ := baire_descent ℓ ρ ⊥
  let ρE : Γ →ₜ* GL ι E := liftGL ρ E hE
  -- Equip `E` with its spectral-norm local-field structure, whose topology is the subspace one.
  let : ValuativeRel E := TauCeti.algebraicExtensionValuativeRel ℚ_[ℓ] E
  have : IsNonarchimedeanLocalField E :=
    PadicAlgCl.finiteIntermediateField_isNonarchimedeanLocalField ℓ E
  obtain ⟨PE, hPE⟩ := exists_conj_mem_integerRing_GL ρE
  let P : GL ι (PadicAlgCl ℓ) := Matrix.GeneralLinearGroup.map (E.val : E →+* PadicAlgCl ℓ) PE
  refine ⟨E, P, hfin, fun g i j ↦ ?_⟩
  have hconj : P * ρ g * P⁻¹ =
      Matrix.GeneralLinearGroup.map (E.val : E →+* PadicAlgCl ℓ) (PE * ρE g * PE⁻¹) := by
    simp only [P, map_mul, map_inv, map_liftGL, ρE]
  have hval : (P * ρ g * P⁻¹ : Matrix ι ι (PadicAlgCl ℓ)) i j =
      (((PE * ρE g * PE⁻¹ : GL ι E) : Matrix ι ι E) i j : PadicAlgCl ℓ) := by
    rw [← Units.val_mul, ← Units.val_mul, hconj]
    rfl
  rw [hval]
  exact ⟨SetLike.coe_mem _,
    (PadicAlgCl.mem_integerRing_algebraicExtension_iff ℓ E _).mp
      (by simpa only [Units.val_mul] using hPE g i j)⟩

end IntegralDescent

end TauCeti.ContinuousRep
