/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Submodule
public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Representation.Fixed
public import TauCeti.Algebra.AlgebraicGroup.Representation.LieStable
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.FromMatrix
import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
import TauCeti.RingTheory.FiniteType.Tensor.PointSeparation

/-!
# The differential of a rational representation of `GL n ℂ`

A rational representation `ρ` of `GL n ℂ` (`TauCeti.IsRationalRep`), whose matrix entries are
polynomials in the entries of `g` divided by powers of `det g`, is the same thing as a
representation of the algebraic group `GLₙ`: a comodule over its coordinate Hopf algebra `O(GLₙ)`.
This file constructs that comodule, `TauCeti.IsRationalRep.comodule`, characterizes it as the
unique comodule on which each invertible matrix `g` acts by `ρ g`, and differentiates it at the
identity. Since the tangent Lie algebra of `GLₙ` is the matrix Lie algebra
(`TauCeti.GeneralLinear.tangentLieEquivMatrix`), this gives the differential

`dρ : 𝔤𝔩ₙ(ℂ) →ₗ⁅ℂ⁆ End W`,

`TauCeti.IsRationalRep.differential`, a representation of the Lie algebra of `n × n` complex
matrices. The construction is algebraic: it differentiates the matrix coefficients of `ρ`, viewed
as elements of `O(GLₙ)`, at the identity, and needs no topology on `W`. On the standard
representation `ℂⁿ` it is matrix multiplication (`TauCeti.IsRationalRep.differential_stdRep`).

Because `GLₙ` is connected and `ℂ` is algebraically closed of characteristic zero, the differential
loses nothing that the subspace and morphism structure of `ρ` sees: a subspace is
`ρ`-invariant exactly when it is `dρ`-stable, a vector is `ρ`-fixed exactly when `dρ` kills it, and
a linear map intertwines two rational representations exactly when it intertwines their
differentials. These statements let the representation theory of the Lie algebra `𝔤𝔩ₙ` be applied
to rational representations of the group, and conversely.

## Main definitions

* `TauCeti.IsRationalRep.comodule`: the `O(GLₙ)`-comodule of a rational representation.
* `TauCeti.IsRationalRep.differential`: the differential of a rational representation, a Lie
  algebra representation of `𝔤𝔩ₙ(ℂ)`.

## Main results

* `TauCeti.IsRationalRep.basePointsRepresentation_comodule`: each invertible matrix `g` acts on
  the comodule by `ρ g`; `TauCeti.IsRationalRep.eq_comodule`: no other comodule structure does.
* `TauCeti.IsRationalRep.differential_stdRep`: the standard representation differentiates to
  matrix multiplication.
* `TauCeti.IsRationalRep.mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential`: the
  invariant subspaces of `ρ` are the subspaces stable under `dρ`.
* `TauCeti.IsRationalRep.isIrreducible_differential`: an irreducible rational representation is
  irreducible for `𝔤𝔩ₙ`.
* `TauCeti.IsRationalRep.mem_invariants_iff_forall_differential_apply_eq_zero`: the invariants of
  `ρ` are the vectors killed by `dρ`.
* `TauCeti.IsRationalRep.isIntertwiningMap_iff_forall_map_differential`: the intertwiners of two
  rational representations are the intertwiners of their differentials.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, Chapters 2 and 7.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 4 and 10.
* J. E. Humphreys, *Linear Algebraic Groups*, §13.
-/

public section

open WithConv TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

namespace IsRationalRep

open GeneralLinear

variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W}

section Coefficients

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι ℂ W}
  {Y : Matrix ι ι (coordinateHopfAlgebra ℂ n)}

/-- In every finite basis, the matrix entries of a rational representation are coordinate
functions on `GLₙ`. -/
private theorem exists_coefficients (hρ : IsRationalRep ρ) (b : Module.Basis ι ℂ W) :
    ∃ Y : Matrix ι ι (coordinateHopfAlgebra ℂ n), ∀ g i j,
      (generalLinearToPoint n g).ofConv (Y i j) = LinearMap.toMatrix b b (ρ g) i j := by
  choose Y hY using fun i j ↦ mem_rationalFunctions_iff_exists_generalLinearToPoint_apply_eq.mp
    ((isRationalRep_iff_forall_mem_rationalFunctions b).mp hρ i j)
  exact ⟨Y, fun g i j ↦ hY i j g⟩

/-- The coordinate functions of a representation are multiplicative under comultiplication. -/
private theorem comul_coefficients
    (hY : ∀ g i j, (generalLinearToPoint n g).ofConv (Y i j) =
      LinearMap.toMatrix b b (ρ g) i j) (i j : ι) :
    Coalgebra.comul (R := ℂ) (Y i j) = ∑ l, Y i l ⊗ₜ[ℂ] Y l j := by
  refine tensor_eq_of_forall_lift_generalLinearToPoint_eq fun g g' ↦ ?_
  have hmul : generalLinearToPoint (R := ℂ) (A := ℂ) n g * generalLinearToPoint n g' =
      generalLinearToPoint n (g * g') := by
    simpa using ((pointsMulEquiv (R := ℂ) (A := ℂ) n).symm.map_mul g g').symm
  rw [← AlgHom.convMul_apply, hmul, hY, map_sum, map_mul, LinearMap.toMatrix_mul,
    Matrix.mul_apply]
  simp [hY]

/-- The coordinate functions of a representation take the identity-matrix values under the
counit. -/
private theorem counit_coefficients
    (hY : ∀ g i j, (generalLinearToPoint n g).ofConv (Y i j) =
      LinearMap.toMatrix b b (ρ g) i j) (i j : ι) :
    Coalgebra.counit (R := ℂ) (Y i j) = (Pi.basisFun ℂ ι).repr ((Pi.basisFun ℂ ι) j) i := by
  have hone : generalLinearToPoint (R := ℂ) (A := ℂ) n 1 = 1 := by
    simpa using (pointsMulEquiv (R := ℂ) (A := ℂ) n).symm.map_one
  have h := hY 1 i j
  rw [hone, map_one, LinearMap.toMatrix_one] at h
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using h

end Coefficients

/-- **The comodule of a rational representation.** A rational representation `ρ` of `GL n ℂ` is
a right comodule over the coordinate Hopf algebra `O(GLₙ)`: for a basis `b` of `W`, a vector `w`
coacts by `∑ᵢ bᵢ ⊗ cᵢ(w)`, where `cᵢ(w) ∈ O(GLₙ)` is the coordinate function
`g ↦ bᵢ*(ρ g w)`. This is the representation of the algebraic group `GLₙ` on which each invertible
matrix `g` acts by `ρ g` (`TauCeti.IsRationalRep.basePointsRepresentation_comodule`), and it does
not depend on the basis (`TauCeti.IsRationalRep.eq_comodule`). -/
@[instance_reducible]
noncomputable def comodule (hρ : IsRationalRep ρ) : Comodule ℂ (coordinateHopfAlgebra ℂ n) W :=
  have := hρ.finite
  let hY := (hρ.exists_coefficients (Module.finBasis ℂ W)).choose_spec
  letI := Comodule.matrixComodule ℂ _
    ((Comodule.map_comul_iff ℂ _).mpr (comul_coefficients hY)) (counit_coefficients hY)
  Comodule.Transport (Module.finBasis ℂ W).equivFun.symm

/-- In the basis used to build it, the coefficient matrix of `TauCeti.IsRationalRep.comodule`
evaluates at each point to the matrix of the representation. -/
private theorem apply_coefficientMatrix_comodule [Module.Finite ℂ W] (hρ : IsRationalRep ρ)
    (g : GL (Fin n) ℂ) (i j : Fin (Module.finrank ℂ W)) :
    letI := hρ.comodule
    (generalLinearToPoint n g).ofConv
        (Comodule.coefficientMatrix (C := coordinateHopfAlgebra ℂ n) (Module.finBasis ℂ W) i j) =
      LinearMap.toMatrix (Module.finBasis ℂ W) (Module.finBasis ℂ W) (ρ g) i j := by
  have hY := (hρ.exists_coefficients (Module.finBasis ℂ W)).choose_spec
  let _ := Comodule.matrixComodule ℂ _
    ((Comodule.map_comul_iff ℂ _).mpr (comul_coefficients hY)) (counit_coefficients hY)
  let _ := hρ.comodule
  have hb : (Module.finBasis ℂ W).equivFun (Module.finBasis ℂ W j) = Pi.basisFun ℂ _ j := by
    ext l
    simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [← hY g i j, Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def, comodule,
    Comodule.transport_coact_apply, LinearEquiv.symm_symm, hb, Comodule.matrixComodule_coact,
    Comodule.matrixCoact_apply_basisFun]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

/-- **The comodule of a rational representation integrates it**: the complex point of `GLₙ`
attached to `g` acts on `TauCeti.IsRationalRep.comodule` by `ρ g`. -/
@[simp]
theorem basePointsRepresentation_comodule (hρ : IsRationalRep ρ) (g : GL (Fin n) ℂ) :
    letI := hρ.comodule
    Comodule.basePointsRepresentation (H := coordinateHopfAlgebra ℂ n) W
      (generalLinearToPoint n g) = ρ g := by
  have := hρ.finite
  let _ := hρ.comodule
  let b := Module.finBasis ℂ W
  refine (LinearMap.toMatrix b b).injective (Matrix.ext fun i j ↦ ?_)
  rw [LinearMap.toMatrix_apply, ← apply_coefficientMatrix_comodule hρ g i j,
    Comodule.coefficientMatrix_apply, Comodule.apply_matrixCoefficient,
    Module.Basis.coord_apply]

/-- Every complex point `p` of `GLₙ` acts on `TauCeti.IsRationalRep.comodule` by `ρ` of the
invertible matrix `p` names. -/
theorem basePointsRepresentation_comodule_eq_pointsMulEquiv (hρ : IsRationalRep ρ)
    (p : WithConv (coordinateHopfAlgebra ℂ n →ₐ[ℂ] ℂ)) :
    letI := hρ.comodule
    Comodule.basePointsRepresentation (H := coordinateHopfAlgebra ℂ n) W p =
      ρ (pointsMulEquiv n p) := by
  have h := basePointsRepresentation_comodule hρ (pointsMulEquiv n p)
  rwa [← pointsMulEquiv_symm_apply, MulEquiv.symm_apply_apply] at h

/-- The coefficient matrix of a comodule integrating a representation is evaluated, point by
point, by the matrices of the representation. -/
private theorem apply_coefficientMatrix_of_basePointsRepresentation_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ W) (c : Comodule ℂ (coordinateHopfAlgebra ℂ n) W)
    (hc : ∀ g : GL (Fin n) ℂ, letI := c
      Comodule.basePointsRepresentation (H := coordinateHopfAlgebra ℂ n) W
        (generalLinearToPoint n g) = ρ g) (g : GL (Fin n) ℂ) (i j : ι) :
    letI := c
    (generalLinearToPoint n g).ofConv
        (Comodule.coefficientMatrix (C := coordinateHopfAlgebra ℂ n) b i j) =
      LinearMap.toMatrix b b (ρ g) i j := by
  let _ := c
  rw [Comodule.coefficientMatrix_apply, Comodule.apply_matrixCoefficient, hc,
    Module.Basis.coord_apply, LinearMap.toMatrix_apply]

/-- **`TauCeti.IsRationalRep.comodule` is the only comodule integrating `ρ`**: every comodule
structure on `W` on which each complex point `g` of `GLₙ` acts by `ρ g` is
`TauCeti.IsRationalRep.comodule`. -/
theorem eq_comodule (hρ : IsRationalRep ρ) (c : Comodule ℂ (coordinateHopfAlgebra ℂ n) W)
    (hc : ∀ g : GL (Fin n) ℂ, letI := c
      Comodule.basePointsRepresentation (H := coordinateHopfAlgebra ℂ n) W
        (generalLinearToPoint n g) = ρ g) :
    c = hρ.comodule := by
  have := hρ.finite
  let b := Module.finBasis ℂ W
  have hcoeff (i j : Fin (Module.finrank ℂ W)) :
      (letI := c; Comodule.coefficientMatrix (C := coordinateHopfAlgebra ℂ n) b i j) =
        (letI := hρ.comodule;
          Comodule.coefficientMatrix (C := coordinateHopfAlgebra ℂ n) b i j) :=
    eq_of_forall_generalLinearToPoint_apply_eq fun g ↦
      (apply_coefficientMatrix_of_basePointsRepresentation_eq b c hc g i j).trans
        (apply_coefficientMatrix_of_basePointsRepresentation_eq b hρ.comodule
          (basePointsRepresentation_comodule hρ) g i j).symm
  refine Comodule.ext (b.ext fun j ↦ ?_)
  have hc' := (letI := c; Comodule.coact_basis_eq_sum_coefficientMatrix
    (C := coordinateHopfAlgebra ℂ n) b j)
  have hρ' := (letI := hρ.comodule; Comodule.coact_basis_eq_sum_coefficientMatrix
    (C := coordinateHopfAlgebra ℂ n) b j)
  simp only [hcoeff] at hc'
  exact hc'.trans hρ'.symm

/-- **The differential of a rational representation**: the representation `dρ` of the matrix Lie
algebra `𝔤𝔩ₙ(ℂ)` on `W` obtained by differentiating `TauCeti.IsRationalRep.comodule` at the
identity, through the identification `TauCeti.GeneralLinear.tangentLieEquivMatrix` of the tangent
Lie algebra of `GLₙ` with `n × n` matrices. In a basis, the matrix entries of `dρ X` are the
derivatives along `X` at the identity of the matrix coefficients of `ρ`. -/
noncomputable def differential (hρ : IsRationalRep ρ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ W :=
  letI := hρ.comodule
  (Comodule.differential (R := ℂ) (H := coordinateHopfAlgebra ℂ n) (M := W)).comp
    (tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm.toLieHom

/-- A matrix acts through the differential as the tangent vector it names acts on the comodule
of the representation. -/
theorem differential_apply (hρ : IsRationalRep ρ) (X : Matrix (Fin n) (Fin n) ℂ) :
    letI := hρ.comodule
    hρ.differential X = Comodule.differential (R := ℂ) (H := coordinateHopfAlgebra ℂ n) (M := W)
      ((tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm X) :=
  (rfl)

/-- **The standard representation differentiates to matrix multiplication**: a matrix `X` acts
on `ℂⁿ` through the differential of `TauCeti.stdRep` by `v ↦ X *ᵥ v`. -/
@[simp]
theorem differential_stdRep (h : IsRationalRep (stdRep ℂ n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    h.differential X = Matrix.mulVecLin X := by
  have hc : h.comodule = standardComodule ℂ n := by
    refine (h.eq_comodule _ fun g ↦ LinearMap.ext fun v ↦ ?_).symm
    let _ := standardComodule ℂ n
    rw [basePointsRepresentation_eq_mulVec, pointToGeneralLinear_generalLinearToPoint,
      stdRep_apply_apply]
  refine (Pi.basisFun ℂ (Fin n)).ext fun j ↦ funext fun i ↦ ?_
  let _ := standardComodule ℂ n
  have key := Derivation.apply_matrixCoefficient (M := Fin n → ℂ)
    ((tangentLieEquivMatrix (R := ℂ) (B := ℂ) n).symm X) ((Pi.basisFun ℂ (Fin n)).coord i)
    (Pi.basisFun ℂ (Fin n) j)
  rw [Module.Basis.coord_apply, Pi.basisFun_repr] at key
  rw [differential_apply, hc, ← key, ← Comodule.coefficientMatrix_apply,
    coefficientMatrix_basisFun, genericMatrix_apply, ← tangentMatrix_apply,
    ← tangentLieEquivMatrix_apply, LieEquiv.apply_symm_apply]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **The invariant subspaces of a rational representation are the `𝔤𝔩ₙ`-stable subspaces**:
a subspace is preserved by every `ρ g` exactly when it is preserved by every `dρ X`. -/
theorem mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential (hρ : IsRationalRep ρ)
    (U : Submodule ℂ W) :
    U ∈ Representation.invtSubmodule ρ ↔
      ∀ X, U ∈ Module.End.invtSubmodule (hρ.differential X) := by
  let H := FiniteTypeCommHopfAlgCat.of ℂ (coordinateHopfAlgebra ℂ n)
  let _ : Comodule ℂ H W := hρ.comodule
  have hU : U ∈ Representation.invtSubmodule ρ ↔
      ∃ N : Subcomodule ℂ H W, N.toSubmodule = U := by
    rw [Representation.mem_invtSubmodule]
    constructor
    · intro h
      refine ⟨Subcomodule.ofEndOfPointStable (K := ℂ) U fun f m hm ↦ ?_,
        Subcomodule.ofEndOfPointStable_toSubmodule _ _⟩
      rw [Comodule.endOfPoint_tmul, one_smul,
        Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation (g := toConv f),
        hρ.basePointsRepresentation_comodule_eq_pointsMulEquiv]
      exact Submodule.tmul_mem_baseChange_of_mem 1 (h _ hm)
    · rintro ⟨N, rfl⟩ g w hw
      have hN := Comodule.basePointsRepresentation_mem N (generalLinearToPoint n g) hw
      rwa [basePointsRepresentation_comodule] at hN
  rw [hU, Submodule.exists_subcomodule_iff_forall_differential_mem (H := H) U]
  refine ⟨fun h X w hw ↦ h _ w hw, fun h d w hw ↦ ?_⟩
  have hd := h (tangentLieEquivMatrix n d) hw
  rwa [differential_apply, LieEquiv.symm_apply_apply] at hd

/-- **An irreducible rational representation is irreducible for `𝔤𝔩ₙ`**: through its
differential, an irreducible rational representation is an irreducible module over the matrix Lie
algebra `𝔤𝔩ₙ(ℂ)`. -/
theorem isIrreducible_differential (hρ : IsRationalRep ρ) [ρ.IsIrreducible] :
    letI := LieRingModule.compLieHom W hρ.differential
    LieModule.IsIrreducible ℂ (Matrix (Fin n) (Fin n) ℂ) W := by
  let _ := LieRingModule.compLieHom W hρ.differential
  have := Representation.IsIrreducible.nontrivial (ρ := ρ) inferInstance
  refine LieModule.IsIrreducible.mk fun N hN ↦ ?_
  have hN' : N.toSubmodule ∈ ρ.invtSubmodule :=
    (hρ.mem_invtSubmodule_iff_forall_mem_invtSubmodule_differential _).mpr
      fun X _ hw ↦ N.lie_mem (x := X) hw
  let S : Subrepresentation ρ :=
    ⟨N.toSubmodule, fun g _ hw ↦ (Representation.mem_invtSubmodule ρ).mp hN' g hw⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · exact absurd ((LieSubmodule.toSubmodule_eq_bot N).mp
      (congrArg Subrepresentation.toSubmodule h)) hN
  · exact (LieSubmodule.toSubmodule_eq_top N).mp (congrArg Subrepresentation.toSubmodule h)

/-- **The invariants of a rational representation are the vectors killed by `𝔤𝔩ₙ`**: a vector
is fixed by every `ρ g` exactly when every `dρ X` sends it to zero. -/
theorem mem_invariants_iff_forall_differential_apply_eq_zero (hρ : IsRationalRep ρ) (w : W) :
    w ∈ ρ.invariants ↔ ∀ X, hρ.differential X w = 0 := by
  let H := FiniteTypeCommHopfAlgCat.of ℂ (coordinateHopfAlgebra ℂ n)
  let _ : Comodule ℂ H W := hρ.comodule
  rw [Representation.mem_invariants]
  trans Comodule.coact (R := ℂ) (C := H) w = w ⊗ₜ 1
  · rw [Comodule.coact_eq_tmul_one_iff_forall_basePointsRepresentation_eq]
    refine ⟨fun h g ↦ ?_, fun h g ↦ ?_⟩
    · rw [hρ.basePointsRepresentation_comodule_eq_pointsMulEquiv]
      exact h _
    · rw [← basePointsRepresentation_comodule hρ g]
      exact h _
  · rw [Comodule.coact_eq_tmul_one_iff_forall_differential_eq_zero]
    refine ⟨fun h X ↦ h _, fun h d ↦ ?_⟩
    have hd := h (tangentLieEquivMatrix n d)
    rwa [differential_apply, LieEquiv.symm_apply_apply] at hd

section Intertwining

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ (GL (Fin n) ℂ) V}

/-- Evaluating the image of a coaction under a linear map at a point of `GLₙ` gives the image of
that point's action. -/
private theorem comm_lTensor_map_coact (hρ : IsRationalRep ρ)
    (p : coordinateHopfAlgebra ℂ n →ₐ[ℂ] ℂ) (f : W →ₗ[ℂ] V) (w : W) :
    letI := hρ.comodule
    TensorProduct.comm ℂ V ℂ (LinearMap.lTensor V p.toLinearMap
        (TensorProduct.map f LinearMap.id
          (Comodule.coact (R := ℂ) (C := coordinateHopfAlgebra ℂ n) w))) =
      1 ⊗ₜ f (ρ (pointToGeneralLinear n (toConv p)) w) := by
  let _ := hρ.comodule
  have hp := basePointsRepresentation_comodule hρ (pointToGeneralLinear n (toConv p))
  rw [generalLinearToPoint_pointToGeneralLinear] at hp
  have h1 := Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation (toConv p) w
  rw [ofConv_toConv] at h1
  have hcomm (t : W ⊗[ℂ] coordinateHopfAlgebra ℂ n) :
      TensorProduct.comm ℂ V ℂ
          (LinearMap.lTensor V p.toLinearMap (TensorProduct.map f LinearMap.id t)) =
        TensorProduct.map LinearMap.id f
          (TensorProduct.comm ℂ W ℂ (LinearMap.lTensor W p.toLinearMap t)) := by
    simp only [LinearMap.lTensor_def, TensorProduct.map_comm, TensorProduct.map_map,
      LinearMap.id_comp, LinearMap.comp_id]
  rw [hcomm, h1, ← hp, map_tmul, LinearMap.id_apply]

/-- **Intertwiners of rational representations are the `𝔤𝔩ₙ`-intertwiners.** A linear map
between rational representations of `GL n ℂ` commutes with the group actions exactly when it
commutes with their differentials. -/
theorem isIntertwiningMap_iff_forall_map_differential (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (f : W →ₗ[ℂ] V) :
    Representation.IsIntertwiningMap ρ σ f ↔
      ∀ X w, f (hρ.differential X w) = hσ.differential X (f w) := by
  let H := FiniteTypeCommHopfAlgCat.of ℂ (coordinateHopfAlgebra ℂ n)
  let _ : Comodule ℂ H W := hρ.comodule
  let _ : Comodule ℂ H V := hσ.comodule
  have hV (p : H →ₐ[ℂ] ℂ) (v : V) := comm_lTensor_map_coact hσ p LinearMap.id v
  simp only [map_id, LinearMap.id_apply] at hV
  have hW := comm_lTensor_map_coact hρ (f := f)
  have hcolin : Representation.IsIntertwiningMap ρ σ f ↔
      TensorProduct.map f LinearMap.id ∘ₗ Comodule.coact (R := ℂ) (C := H) =
        Comodule.coact (R := ℂ) (C := H) ∘ₗ f := by
    rw [Representation.isIntertwiningMap_iff]
    constructor
    · intro h
      refine LinearMap.ext fun w ↦ (TensorProduct.comm ℂ V H).injective ?_
      refine tensor_eq_of_forall_map_algHom_eq (K := ℂ) fun p ↦ ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, map_comm, map_comm,
        ← LinearMap.lTensor_def, hW, h, ← hV]
    · intro h g w
      have hg := congr(TensorProduct.lid ℂ V (TensorProduct.comm ℂ V ℂ (LinearMap.lTensor V
        (generalLinearToPoint (R := ℂ) n g).ofConv.toLinearMap $(LinearMap.congr_fun h w))))
      rwa [LinearMap.comp_apply, LinearMap.comp_apply, hW, hV, toConv_ofConv,
        pointToGeneralLinear_generalLinearToPoint, TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, one_smul, one_smul] at hg
  rw [hcolin, LinearMap.map_coact_iff_map_differential]
  refine ⟨fun h X w ↦ h _ w, fun h d w ↦ ?_⟩
  have hd := h (tangentLieEquivMatrix n d) w
  rwa [differential_apply, differential_apply, LieEquiv.symm_apply_apply] at hd

end Intertwining

end IsRationalRep

end TauCeti
