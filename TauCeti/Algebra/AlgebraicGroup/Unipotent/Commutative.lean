/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Embedding
public import TauCeti.Algebra.Bialgebra.SymmetricAlgebra.Lift
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.FunctorOfPoints
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Logarithm
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Basic

/-!
# Commutative unipotent groups in characteristic zero are vector groups

Let `H` be the coordinate Hopf algebra of a commutative affine group of finite type over a field
`k` of characteristic zero, so that `H` is commutative and cocommutative. If the group is
unipotent, in the comodule sense that every nonzero finite-dimensional representation has a
nonzero fixed vector, then `H` is the symmetric algebra on its primitive elements: the bialgebra
map `SymmetricAlgebra k P → H` extending the inclusion of the primitive elements `P` is an
isomorphism. Geometrically, the group is the vector group of the dual of `P`, and the primitive
elements are its additive characters, the homomorphisms to `𝔾ₐ`.

The proof uses the finite logarithm of a unipotent coefficient matrix. A faithful representation
of the unipotent group has, in a suitable basis, an upper-unitriangular coefficient matrix `X`
whose entries generate `H`. Comultiplication acts on `X` as the product `(X ⊗ 1) (1 ⊗ X)`, and
cocommutativity says that the two factors commute. The logarithm of a product of commuting
unipotent matrices is the sum of their logarithms, so every entry of `log X` is primitive
(`TauCeti.Comodule.isPrimitiveElem_log_coefficientMatrix`, in
TauCeti/Algebra/Coalgebra/Comodule/MatrixCoefficient/Logarithm.lean). Since `X = exp (log X)`, the
primitive elements generate `H`, which gives surjectivity. Injectivity is the algebraic
independence of linearly independent primitive elements in characteristic zero,
`SymmetricAlgebra.liftBialgHom_injective`.

Over an algebraically closed field, unipotence in the comodule sense follows from unipotence of
the rational points, since a Hopf algebra in characteristic zero is reduced (Cartier).

## Main declarations

* `TauCeti.HopfAlgebra.liftBialgHom_primitive_bijective`: for a commutative unipotent group over
  a field of characteristic zero, the symmetric algebra on the primitive elements maps
  bijectively onto the coordinate Hopf algebra.
* `TauCeti.HopfAlgebra.symmetricAlgebraPrimitiveBialgEquiv`: the corresponding isomorphism of
  bialgebras.
* `TauCeti.HopfAlgebra.liftBialgHom_primitive_bijective_of_forall_isUnipotentPoint`: the same
  over an algebraically closed field when every rational point is unipotent.

## References

* J. S. Milne, *Algebraic Groups* (2017), §14.c.
-/

public section

open Module

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} {H : Type v} [Field k] [CharZero k] [CommRing H] [_root_.HopfAlgebra k H]
  [Coalgebra.IsCocomm k H]

/-- The entries of a cocommutative unipotent coefficient matrix are polynomials in primitive
elements: they are the entries of `exp (log X)`, and the entries of `log X` are primitive. -/
private theorem coefficientMatrix_mem_adjoin_primitive {M : Type v} [AddCommGroup M]
    [Module k M] [Comodule k H M] {n : ℕ} (b : Basis (Fin n) k M)
    (hb : IsNilpotent (Comodule.coefficientMatrix (C := H) b - 1)) (i j : Fin n) :
    Comodule.coefficientMatrix (C := H) b i j ∈
      Algebra.adjoin k (Coalgebra.skewPrimitive k (1 : H) 1 : Set H) := by
  let _ : Algebra ℚ H := ((algebraMap k H).comp (algebraMap ℚ k)).toAlgebra
  set X := Comodule.coefficientMatrix (C := H) b
  set S := Algebra.adjoin k (Coalgebra.skewPrimitive k (1 : H) 1 : Set H)
  -- The entries of `log X` are primitive, so `log X` is a matrix over `S`.
  let N : Matrix (Fin n) (Fin n) S := Matrix.of fun i j ↦ ⟨IsNilpotent.log X i j,
    Algebra.subset_adjoin (Comodule.isPrimitiveElem_log_coefficientMatrix b i j)⟩
  have hN : S.val.mapMatrix N = IsNilpotent.log X := by
    ext i j
    simp [N]
  -- Hence so is `X = exp (log X)`, a sum of rational multiples of powers of `log X`.
  obtain ⟨m, hm⟩ := IsNilpotent.isNilpotent_log hb
  rw [← IsNilpotent.exp_log hb, IsNilpotent.exp_eq_sum hm, ← hN, Matrix.sum_apply]
  refine Subalgebra.sum_mem _ fun l _ ↦ ?_
  rw [Matrix.smul_apply, ← map_pow]
  -- A rational multiple is a multiple by the image of that rational number in `k`.
  have hq (q : ℚ) (z : H) : q • z = algebraMap ℚ k q • z := by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  rw [hq]
  exact Subalgebra.smul_mem S (Subtype.prop _) _

/-- The primitive elements of `H` generate it as an algebra, when `H` is cocommutative and has a
representation with surjective coordinate map and upper-unitriangular coefficient matrix. -/
private theorem adjoin_primitive_eq_top_of_isUpperUnitriangular {M : Type v} [AddCommGroup M]
    [Module k M] [Comodule k H M] {n : ℕ} (b : Basis (Fin n) k M)
    (hb : (Comodule.coefficientMatrix (C := H) b).IsUpperUnitriangular)
    (hsurj : Function.Surjective (Comodule.coordinateBialgHom (H := H) b)) :
    Algebra.adjoin k (Coalgebra.skewPrimitive k (1 : H) 1 : Set H) = ⊤ := by
  set X := Comodule.coefficientMatrix (C := H) b
  set S := Algebra.adjoin k (Coalgebra.skewPrimitive k (1 : H) 1 : Set H)
  have hXS := coefficientMatrix_mem_adjoin_primitive b hb.isNilpotent_sub_one
  -- The coefficient matrix over `S` is invertible, so the coordinate map factors through `S`.
  let Y : Matrix (Fin n) (Fin n) S := Matrix.of fun i j ↦ ⟨X i j, hXS i j⟩
  have hY : Y.IsUpperUnitriangular := by
    obtain ⟨htri, hdiag⟩ := (Matrix.isUpperUnitriangular_def X).mp hb
    exact (Matrix.isUpperUnitriangular_def Y).mpr
      ⟨fun i j hij ↦ Subtype.ext (htri hij), fun i ↦ Subtype.ext (hdiag i)⟩
  let g : GeneralLinear.coordinateHopfAlgebra k n →ₐ[k] S :=
    (GeneralLinear.generalLinearToPoint (R := k) n hY.toGL).ofConv
  have hfac : (Comodule.coordinateBialgHom (H := H) b : _ →ₐ[k] H) = S.val.comp g := by
    apply GeneralLinear.coordinateHopfAlgebra_algHom_ext k n
    intro i j
    rw [AlgHom.comp_apply, GeneralLinear.generalLinearToPoint_apply,
      Matrix.IsUpperUnitriangular.coe_toGL]
    exact Comodule.coordinateBialgHom_X b i j
  rw [eq_top_iff]
  intro h _
  obtain ⟨y, rfl⟩ := hsurj h
  have hy := congrArg (fun φ : _ →ₐ[k] H ↦ φ y) hfac
  simp only [BialgHom.coe_toAlgHom, AlgHom.comp_apply] at hy
  rw [hy]
  exact (g y).property

/-- **A commutative unipotent group over a field of characteristic zero is a vector group.** If
`H` is commutative, cocommutative and of finite type over a field of characteristic zero, and every
nonzero finite-dimensional comodule has a nonzero fixed vector, then the symmetric algebra on the
primitive elements of `H` maps bijectively onto `H`. -/
theorem liftBialgHom_primitive_bijective [Algebra.FiniteType k H]
    (hfixed : ∀ (V : Type v) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], Comodule.HasNonzeroFixedVector k H V) :
    Function.Bijective (SymmetricAlgebra.liftBialgHom (Coalgebra.skewPrimitive k (1 : H) 1).subtype
      fun p ↦ p.property) := by
  refine ⟨SymmetricAlgebra.liftBialgHom_injective _ Subtype.val_injective, ?_⟩
  -- A faithful representation has an upper-unitriangular coefficient matrix.
  obtain ⟨M, m, c, hc⟩ := Comodule.exists_coordinateBialgHom_surjective (k := k) (H := H)
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k M := Module.Finite.of_basis c
  obtain ⟨n, b, hb⟩ :=
    Comodule.exists_basis_coefficientMatrix_isUpperUnitriangular_of_fixed_vectors (M := M) hfixed
  have hsurj := (Comodule.coordinateBialgHom_surjective_iff_of_bases c b).mp hc
  -- Its primitive logarithm generates `H`, and the range of the lift contains the primitives.
  suffices h : (SymmetricAlgebra.liftBialgHom (Coalgebra.skewPrimitive k (1 : H) 1).subtype
      fun p ↦ p.property).toAlgHom.range = ⊤ from
    (AlgHom.range_eq_top _).mp h
  rw [eq_top_iff, ← adjoin_primitive_eq_top_of_isUpperUnitriangular b hb hsurj,
    Algebra.adjoin_le_iff]
  intro p hp
  exact ⟨SymmetricAlgebra.ι k _ ⟨p, hp⟩, SymmetricAlgebra.liftBialgHom_ι _ _ _⟩

/-- **The coordinate Hopf algebra of a commutative unipotent group over a field of characteristic
zero is the symmetric algebra on its primitive elements.** Here unipotence means that every
nonzero finite-dimensional comodule has a nonzero fixed vector; the isomorphism extends the
inclusion of the primitive elements. -/
noncomputable def symmetricAlgebraPrimitiveBialgEquiv [Algebra.FiniteType k H]
    (hfixed : ∀ (V : Type v) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], Comodule.HasNonzeroFixedVector k H V) :
    SymmetricAlgebra k (Coalgebra.skewPrimitive k (1 : H) 1) ≃ₐc[k] H :=
  BialgEquiv.ofBijective _ (liftBialgHom_primitive_bijective hfixed)

/-- The isomorphism `symmetricAlgebraPrimitiveBialgEquiv` sends each generator to the primitive
element it names. -/
@[simp]
theorem symmetricAlgebraPrimitiveBialgEquiv_ι [Algebra.FiniteType k H]
    (hfixed : ∀ (V : Type v) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], Comodule.HasNonzeroFixedVector k H V)
    (p : Coalgebra.skewPrimitive k (1 : H) 1) :
    symmetricAlgebraPrimitiveBialgEquiv hfixed (SymmetricAlgebra.ι k _ p) = p :=
  SymmetricAlgebra.liftBialgHom_ι _ _ p

/-- The inverse of `symmetricAlgebraPrimitiveBialgEquiv` sends a primitive element to the
corresponding generator. -/
@[simp]
theorem symmetricAlgebraPrimitiveBialgEquiv_symm_apply_coe [Algebra.FiniteType k H]
    (hfixed : ∀ (V : Type v) [AddCommGroup V] [Module k V] [Comodule k H V]
      [FiniteDimensional k V] [Nontrivial V], Comodule.HasNonzeroFixedVector k H V)
    (p : Coalgebra.skewPrimitive k (1 : H) 1) :
    (symmetricAlgebraPrimitiveBialgEquiv hfixed).symm p = SymmetricAlgebra.ι k _ p := by
  rw [← symmetricAlgebraPrimitiveBialgEquiv_ι hfixed p, BialgEquiv.symm_apply_apply]

/-- **Over an algebraically closed field of characteristic zero, a commutative affine group of
finite type whose rational points are unipotent is a vector group:** the symmetric algebra on the
primitive elements of its coordinate Hopf algebra maps bijectively onto it. -/
theorem liftBialgHom_primitive_bijective_of_forall_isUnipotentPoint [IsAlgClosed k]
    [Algebra.FiniteType k H] (hH : ∀ g : WithConv (H →ₐ[k] k), IsUnipotentPoint g) :
    Function.Bijective (SymmetricAlgebra.liftBialgHom (Coalgebra.skewPrimitive k (1 : H) 1).subtype
      fun p ↦ p.property) :=
  have := isReduced_of_charZero k H
  liftBialgHom_primitive_bijective fun _ _ _ _ _ _ ↦
    Comodule.hasNonzeroFixedVector_of_forall_isUnipotentPoint hH

end TauCeti.HopfAlgebra
