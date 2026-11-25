/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Comodule
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.CoadjointNilpotentCone
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.Algebra.Polynomial.Degree.Map

/-!
# The coadjoint nilpotent cone of the general linear group

Let `𝔤 = 𝔤𝔩ₙ` be the Lie algebra of `GLₙ` over a field `k`, identified with the `n × n` matrices
by `TauCeti.GeneralLinear.cotangentDualMatrixEquiv`. Through the trace pairing, a matrix `Y` with
entries in a `k`-algebra `A` is read as the `A`-valued covector `X ↦ tr (Y X)` on `𝔤`
(`TauCeti.GeneralLinear.traceCovector`), and every covector arises this way. The coadjoint action
of a point `G ∈ GLₙ(A)` is then conjugation, `Y ↦ G⁻¹ Y G`.

The coefficients of the characteristic polynomial of the generic matrix
`TauCeti.GeneralLinear.coadjointGenericMatrix` are invariant polynomial functions on `𝔤*`, and all
but the leading one vanish at the origin. So every point of the coadjoint nilpotent cone, with
values in any commutative `k`-algebra, has characteristic polynomial `Xⁿ`. Conversely, a covector
scaled by a cocharacter lies on the cone, and so does a first-order covector vanishing on the
centre of `𝔤`.

For `GL₂` this gives the following checks: `E₁₂` lies on the cone; `diag(1, -1)` does not, although
its trace, the invariant of degree one, vanishes, so that the trace alone gives the wrong zero
fibre; the identity matrix does not; and over the dual numbers `diag(ε, -ε)`, whose trace and
determinant vanish, does.

## Main declarations

* `TauCeti.GeneralLinear.traceCovector`: the covector `X ↦ tr (Y X)` of a matrix `Y`.
* `TauCeti.GeneralLinear.liftBaseChange_traceCovector_endOfPoint`: the coadjoint action of a point
  `G` is conjugation `Y ↦ G⁻¹ Y G`.
* `TauCeti.GeneralLinear.charpoly_coeff_coadjointGenericMatrix_mem_coadjointInvariantPolynomials`:
  the characteristic coefficients of the generic matrix are invariant.
* `TauCeti.GeneralLinear.charpoly_eq_X_pow_of_coadjointNilpotentConeIdeal_le_ker` and
  `TauCeti.GeneralLinear.pow_eq_zero_of_coadjointNilpotentConeIdeal_le_ker`: points of the cone
  have characteristic polynomial `Xⁿ`, so they are nilpotent matrices.
* `TauCeti.GeneralLinear.coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_single_zero_one`,
  `TauCeti.GeneralLinear.not_coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_diagonal`,
  `TauCeti.GeneralLinear.not_coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_one`, and
  `TauCeti.GeneralLinear.coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_diagonal_eps`: the
  checks for `GL₂`.

## References

* L. Fargues and P. Scholze, *Geometrization of the local Langlands correspondence*, proof of
  Proposition VIII.2.11.
-/

public section

open scoped TensorProduct LaurentPolynomial DualNumber

namespace TauCeti.GeneralLinear

universe u

attribute [local instance] Derivation.adjointComodule

variable {k : Type u} [Field k] {n : ℕ}

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k (coordinateHopfAlgebra k n))

section TraceCovector

variable {A : Type*} [CommSemiring A] [Algebra k A]

variable (k) in
/-- The covector `X ↦ tr (Y X)` on the Lie algebra `𝔤𝔩ₙ` with values in `A` attached to a matrix
`Y` with entries in `A` by the trace pairing. -/
noncomputable def traceCovector (Y : Matrix (Fin n) (Fin n) A) : 𝔤 →ₗ[k] A where
  toFun x := (Y * (cotangentDualMatrixEquiv x).map (algebraMap k A)).trace
  map_add' x y := by
    rw [map_add, Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.trace_add]
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, Matrix.map_smul' _ _ _ fun _ _ ↦ map_mul _ _ _,
      Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Algebra.smul_def]

/-- The trace covector of `Y` pairs `Y` with the matrix of a vector of `𝔤𝔩ₙ`. -/
@[simp]
theorem traceCovector_apply (Y : Matrix (Fin n) (Fin n) A) (x : 𝔤) :
    traceCovector k Y x = (Y * (cotangentDualMatrixEquiv x).map (algebraMap k A)).trace :=
  (rfl)

/-- The trace pairing is linear in the matrix. -/
theorem traceCovector_smul (a : A) (Y : Matrix (Fin n) (Fin n) A) :
    traceCovector k (a • Y) = a • traceCovector k Y := by
  ext x
  simp [Matrix.trace_smul]

/-- The trace covector of a matrix with entries in `k`, viewed over `A`, is the trace covector over
`k` followed by the structure map. -/
theorem traceCovector_map_algebraMap (Y : Matrix (Fin n) (Fin n) k) :
    traceCovector k (Y.map (algebraMap k A)) = Algebra.linearMap k A ∘ₗ traceCovector k Y := by
  ext x
  simp only [traceCovector_apply, LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
    Matrix.trace, Matrix.diag, map_sum, Matrix.mul_apply, map_mul, Matrix.map_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

variable (k n) in
/-- The generic covector on `𝔤𝔩ₙ` as a matrix in the trace pairing: the matrix with entries in the
polynomial functions `Sym 𝔤` on `𝔤*` whose entry `(i, j)` is the matrix unit `E_ji ∈ 𝔤`, a linear
function on `𝔤*`. Evaluating it at a covector gives the matrix of that covector. -/
noncomputable def coadjointGenericMatrix : Matrix (Fin n) (Fin n) (SymmetricAlgebra k 𝔤) :=
  Matrix.of fun i j ↦ SymmetricAlgebra.ι k 𝔤 (cotangentDualMatrixEquiv.symm (Matrix.single j i 1))

/-- The entries of the generic matrix are the matrix units, as linear functions on `𝔤*`. -/
theorem coadjointGenericMatrix_apply (i j : Fin n) :
    coadjointGenericMatrix k n i j =
      SymmetricAlgebra.ι k 𝔤 (cotangentDualMatrixEquiv.symm (Matrix.single j i 1)) :=
  (rfl)

/-- **The trace pairing is nondegenerate.** Evaluating the generic matrix at the trace covector of
`Y` gives back `Y`. -/
@[simp]
theorem map_lift_traceCovector_coadjointGenericMatrix (Y : Matrix (Fin n) (Fin n) A) :
    (coadjointGenericMatrix k n).map (SymmetricAlgebra.lift (traceCovector k Y)) = Y := by
  ext i j
  simp [coadjointGenericMatrix_apply, Matrix.trace_mul_single]

/-- **Every covector comes from a matrix.** A covector on `𝔤𝔩ₙ` with values in `A` is the trace
covector of its matrix, the evaluation of the generic matrix at it. -/
theorem traceCovector_map_lift_coadjointGenericMatrix (ψ : 𝔤 →ₗ[k] A) :
    traceCovector k ((coadjointGenericMatrix k n).map (SymmetricAlgebra.lift ψ)) = ψ := by
  ext x
  conv_rhs => rw [← cotangentDualMatrixEquiv.symm_apply_apply x,
    Matrix.matrix_eq_sum_single (cotangentDualMatrixEquiv x)]
  simp only [map_sum, traceCovector_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.map_apply, coadjointGenericMatrix_apply, SymmetricAlgebra.lift_ι_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : Matrix.single j i (cotangentDualMatrixEquiv x j i) =
      cotangentDualMatrixEquiv x j i • Matrix.single j i (1 : k) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, Algebra.smul_def, mul_comm]

end TraceCovector

section Invariants

variable {A : Type*} [CommRing A] [Algebra k A]

/-- The scalar extension of the trace covector of `Y` evaluates the trace of `Y` against the matrix
of an `A`-valued tangent vector. -/
private theorem liftBaseChange_traceCovector (Y : Matrix (Fin n) (Fin n) A) (w : A ⊗[k] 𝔤) :
    LinearMap.liftBaseChange A (traceCovector k Y) w =
      (Y * tangentMatrix n (Derivation.tangentScalarExtensionEquiv (R := k)
        (A := coordinateHopfAlgebra k n) (B := A) w)).trace := by
  induction w using TensorProduct.inductionOn with
  | tmul a x =>
    rw [LinearMap.liftBaseChange_tmul, tangentMatrix_tangentScalarExtensionEquiv_tmul,
      traceCovector_apply, Matrix.mul_smul, Matrix.trace_smul]
  | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', Matrix.mul_add, Matrix.trace_add]

/-- **The coadjoint action of `GLₙ` is conjugation.** In the trace pairing, the point `G ∈ GLₙ(A)`
translates the covector of `Y` to the covector of `G⁻¹ Y G`. -/
theorem liftBaseChange_traceCovector_endOfPoint
    (g : HopfAlgebra.points (H := coordinateHopfAlgebra k n) (CommAlgCat.of k A))
    (Y : Matrix (Fin n) (Fin n) A) (x : 𝔤) :
    LinearMap.liftBaseChange A (traceCovector k Y)
        (Comodule.endOfPoint 𝔤 g.ofConv (1 ⊗ₜ[k] x)) =
      traceCovector k ((((pointsMulEquiv n g)⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) * Y * (pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)) x := by
  rw [liftBaseChange_traceCovector, tangentMatrix_adjointComodule_endOfPoint,
    tangentMatrix_tangentScalarExtensionEquiv_one_tmul, traceCovector_apply,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc]

/-- The value of the characteristic coefficients of the generic matrix at the trace covector of `Y`
are the characteristic coefficients of `Y`. -/
theorem lift_traceCovector_charpoly_coeff_coadjointGenericMatrix (Y : Matrix (Fin n) (Fin n) A)
    (i : ℕ) :
    SymmetricAlgebra.lift (traceCovector k Y) ((coadjointGenericMatrix k n).charpoly.coeff i) =
      Y.charpoly.coeff i := by
  conv_rhs => rw [← map_lift_traceCovector_coadjointGenericMatrix (k := k) Y]
  rw [← AlgHom.coe_toRingHom, Matrix.charpoly_map, Polynomial.coeff_map]

/-- The translate of the trace covector of `Y` by the coadjoint action of `G ∈ GLₙ(A)` is the trace
covector of `G⁻¹ Y G`. -/
private theorem translate_traceCovector (G : Matrix.GeneralLinearGroup (Fin n) A)
    (Y : Matrix (Fin n) (Fin n) A) :
    (LinearMap.liftBaseChange A (traceCovector k Y)).restrictScalars k ∘ₗ
        (Comodule.endOfPoint 𝔤 ((pointsMulEquiv n).symm G).ofConv).restrictScalars k ∘ₗ
          TensorProduct.mk k A 𝔤 1 =
      traceCovector k (((G⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) * Y * (G : Matrix (Fin n) (Fin n) A)) := by
  ext x
  simpa using liftBaseChange_traceCovector_endOfPoint ((pointsMulEquiv n).symm G) Y x

/-- **Invariant functions are conjugation invariant.** An invariant polynomial function on `𝔤𝔩ₙ*`
takes the same value at the trace covectors of `Y` and of `G⁻¹ Y G`, for every `G ∈ GLₙ(A)`. -/
theorem lift_traceCovector_conj_of_mem_coadjointInvariantPolynomials {p : SymmetricAlgebra k 𝔤}
    (hp : p ∈ coadjointInvariantPolynomials k (coordinateHopfAlgebra k n))
    (G : Matrix.GeneralLinearGroup (Fin n) A) (Y : Matrix (Fin n) (Fin n) A) :
    SymmetricAlgebra.lift (traceCovector k (((G⁻¹ : Matrix.GeneralLinearGroup (Fin n) A) :
        Matrix (Fin n) (Fin n) A) * Y * (G : Matrix (Fin n) (Fin n) A))) p =
      SymmetricAlgebra.lift (traceCovector k Y) p := by
  rw [← translate_traceCovector]
  exact lift_liftBaseChange_endOfPoint_of_mem_coadjointInvariantPolynomials hp _ _

/-- **The characteristic coefficients are invariant.** The coefficients of the characteristic
polynomial of the generic matrix are invariant polynomial functions on `𝔤𝔩ₙ*`. -/
theorem charpoly_coeff_coadjointGenericMatrix_mem_coadjointInvariantPolynomials (i : ℕ) :
    (coadjointGenericMatrix k n).charpoly.coeff i ∈
      coadjointInvariantPolynomials k (coordinateHopfAlgebra k n) := by
  rw [mem_coadjointInvariantPolynomials_iff_lift_liftBaseChange_endOfPoint]
  intro A _ _ g ψ
  obtain ⟨G, rfl⟩ : ∃ G, ((pointsMulEquiv n).symm G).ofConv = g :=
    ⟨pointsMulEquiv n (WithConv.toConv g), by simp⟩
  rw [← traceCovector_map_lift_coadjointGenericMatrix ψ, translate_traceCovector,
    lift_traceCovector_charpoly_coeff_coadjointGenericMatrix,
    lift_traceCovector_charpoly_coeff_coadjointGenericMatrix, Matrix.charpoly_mul_comm,
    ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

/-- The characteristic coefficients of the generic matrix below the leading one vanish at the
origin. -/
theorem algebraMapInv_charpoly_coeff_coadjointGenericMatrix {i : ℕ} (hi : i < n) :
    SymmetricAlgebra.algebraMapInv ((coadjointGenericMatrix k n).charpoly.coeff i) = 0 := by
  have h0 : (SymmetricAlgebra.algebraMapInv : SymmetricAlgebra k 𝔤 →ₐ[k] k) =
      SymmetricAlgebra.lift (traceCovector k (0 : Matrix (Fin n) (Fin n) k)) :=
    SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ by simp [SymmetricAlgebra.algebraMapInv_ι])
  rw [h0, lift_traceCovector_charpoly_coeff_coadjointGenericMatrix, Matrix.charpoly_zero,
    Fintype.card_fin, Polynomial.coeff_X_pow]
  simp [hi.ne]

/-- **Points of the coadjoint nilpotent cone of `GLₙ` have characteristic polynomial `Xⁿ`.** If
the trace covector of a matrix `Y` with entries in a commutative `k`-algebra `A` lies on the
coadjoint nilpotent cone, then the characteristic polynomial of `Y` is `Xⁿ`, since its other
coefficients are invariant polynomial functions vanishing at the origin. -/
theorem charpoly_eq_X_pow_of_coadjointNilpotentConeIdeal_le_ker {Y : Matrix (Fin n) (Fin n) A}
    (h : coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k n) ≤
      RingHom.ker (SymmetricAlgebra.lift (traceCovector k Y))) :
    Y.charpoly = Polynomial.X ^ n := by
  conv_lhs => rw [← map_lift_traceCovector_coadjointGenericMatrix (k := k) Y]
  rw [← AlgHom.coe_toRingHom, Matrix.charpoly_map]
  have hn : (coadjointGenericMatrix k n).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have key := (Matrix.charpoly_monic (coadjointGenericMatrix k n)).map_eq_X_pow_of_map_coeff_eq_zero
    (φ := (SymmetricAlgebra.lift (traceCovector k Y)).toRingHom) fun i hi ↦ h <|
      mem_coadjointNilpotentConeIdeal_of_mem_coadjointInvariantPolynomials
        (charpoly_coeff_coadjointGenericMatrix_mem_coadjointInvariantPolynomials i)
        (algebraMapInv_charpoly_coeff_coadjointGenericMatrix (hn ▸ hi))
  rwa [hn] at key

/-- **Points of the coadjoint nilpotent cone of `GLₙ` are nilpotent.** If the trace covector of a
matrix `Y` with entries in a commutative `k`-algebra lies on the coadjoint nilpotent cone, then
`Yⁿ = 0`, by the Cayley–Hamilton theorem. -/
theorem pow_eq_zero_of_coadjointNilpotentConeIdeal_le_ker {Y : Matrix (Fin n) (Fin n) A}
    (h : coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k n) ≤
      RingHom.ker (SymmetricAlgebra.lift (traceCovector k Y))) :
    Y ^ n = 0 := by
  simpa [charpoly_eq_X_pow_of_coadjointNilpotentConeIdeal_le_ker h] using
    Matrix.aeval_self_charpoly Y

/-- Points of the coadjoint nilpotent cone of `GLₙ`, for `n ≠ 0`, have determinant zero. -/
theorem det_eq_zero_of_coadjointNilpotentConeIdeal_le_ker (hn : n ≠ 0)
    {Y : Matrix (Fin n) (Fin n) A}
    (h : coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k n) ≤
      RingHom.ker (SymmetricAlgebra.lift (traceCovector k Y))) :
    Y.det = 0 := by
  rw [Matrix.det_eq_sign_charpoly_coeff, charpoly_eq_X_pow_of_coadjointNilpotentConeIdeal_le_ker h,
    Polynomial.coeff_X_pow]
  simp [Ne.symm hn]

end Invariants

section GL₂

/-! ### The checks for `GL₂` -/

open LaurentPolynomial in
/-- **`E₁₂` lies on the coadjoint nilpotent cone of `GL₂`.** The cocharacter `t ↦ diag(1, t)`
scales the covector `X ↦ tr (E₁₂ X)` by `t`. -/
theorem coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_single_zero_one :
    coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k 2) ≤ RingHom.ker
      (SymmetricAlgebra.lift
        (traceCovector k (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k)))) := by
  set E : Matrix (Fin 2) (Fin 2) k[T;T⁻¹] := Matrix.single 0 1 1 with hE
  have hu : IsUnit (Matrix.diagonal ![1, T 1] : Matrix (Fin 2) (Fin 2) k[T;T⁻¹]) :=
    Matrix.isUnit_diagonal.mpr <| Pi.isUnit_iff.mpr fun i ↦ by
      fin_cases i <;> simp [isUnit_T]
  have hmap : Algebra.linearMap k k[T;T⁻¹] ∘ₗ
      traceCovector k (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k)) = traceCovector k E := by
    rw [← traceCovector_map_algebraMap]
    congr 1
    refine Matrix.ext fun i j ↦ ?_
    simp [hE, Matrix.single_apply]
  -- Conjugation by `diag(1, t)` scales `E₁₂` by `t`.
  have hconj : ((hu.unit⁻¹ : (Matrix (Fin 2) (Fin 2) k[T;T⁻¹])ˣ) : Matrix (Fin 2) (Fin 2) _) * E *
      (hu.unit : Matrix (Fin 2) (Fin 2) _) = (T 1 : k[T;T⁻¹]) • E := by
    have hcomm : E * (hu.unit : Matrix (Fin 2) (Fin 2) k[T;T⁻¹]) =
        (hu.unit : Matrix (Fin 2) (Fin 2) k[T;T⁻¹]) * ((T 1 : k[T;T⁻¹]) • E) := by
      rw [IsUnit.unit_spec, hE]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  refine coadjointNilpotentConeIdeal_le_ker_lift_of_endOfPoint
    ((pointsMulEquiv 2).symm hu.unit).ofConv one_ne_zero fun x ↦ ?_
  rw [hmap, liftBaseChange_traceCovector_endOfPoint, MulEquiv.apply_symm_apply, hconj,
    traceCovector_smul, LinearMap.smul_apply, smul_eq_mul, ← hmap, LinearMap.comp_apply,
    Algebra.linearMap_apply]

/-- **`diag(1, -1)` does not lie on the coadjoint nilpotent cone of `GL₂`**, although its trace,
the value of the invariant of degree one, vanishes: its determinant is `-1`. So the trace alone
cuts out the wrong zero fibre. -/
theorem not_coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_diagonal :
    ¬ coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k 2) ≤
      RingHom.ker (SymmetricAlgebra.lift (traceCovector k (Matrix.diagonal ![(1 : k), -1]))) :=
  fun h ↦ by simpa using det_eq_zero_of_coadjointNilpotentConeIdeal_le_ker two_ne_zero h

/-- **The identity matrix does not lie on the coadjoint nilpotent cone of `GL₂`**: its
determinant is `1`. -/
theorem not_coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_one :
    ¬ coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k 2) ≤
      RingHom.ker (SymmetricAlgebra.lift (traceCovector k (1 : Matrix (Fin 2) (Fin 2) k))) :=
  fun h ↦ by simpa using det_eq_zero_of_coadjointNilpotentConeIdeal_le_ker two_ne_zero h

/-- **`diag(ε, -ε)` lies on the coadjoint nilpotent cone of `GL₂` over the dual numbers.** It is
the first-order covector `ε • ψ` for the covector `ψ` of `diag(1, -1) = ⁅E₁₂, E₂₁⁆`, which vanishes
on the centre of `𝔤𝔩₂` since the trace form is invariant. -/
theorem coadjointNilpotentConeIdeal_le_ker_lift_traceCovector_diagonal_eps :
    coadjointNilpotentConeIdeal k (coordinateHopfAlgebra k 2) ≤
      RingHom.ker (SymmetricAlgebra.lift
        (traceCovector k (Matrix.diagonal ![(ε : k[ε]), -ε]))) := by
  have hdiag : Matrix.diagonal ![(ε : k[ε]), -ε] =
      (ε : k[ε]) • (Matrix.diagonal ![(1 : k), -1]).map (algebraMap k k[ε]) := by
    refine Matrix.ext fun i j ↦ ?_
    fin_cases i <;> fin_cases j <;> simp
  have hpt : traceCovector k (Matrix.diagonal ![(ε : k[ε]), -ε]) =
      (traceCovector k (Matrix.diagonal ![(1 : k), -1])).smulRight ε := by
    refine LinearMap.ext fun x ↦ ?_
    rw [hdiag, traceCovector_smul, traceCovector_map_algebraMap, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.smulRight_apply, Algebra.linearMap_apply, smul_eq_mul,
      mul_comm, ← Algebra.smul_def]
  rw [hpt]
  refine coadjointNilpotentConeIdeal_le_ker_lift_smulRight DualNumber.eps_mul_eps fun z hz ↦ ?_
  set x₁ := cotangentDualMatrixEquiv.symm (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : k)) with hx₁
  set x₂ := cotangentDualMatrixEquiv.symm (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : k)) with hx₂
  have hY : (Matrix.diagonal ![(1 : k), -1]) =
      cotangentDualMatrixEquiv x₁ * cotangentDualMatrixEquiv x₂ -
        cotangentDualMatrixEquiv x₂ * cotangentDualMatrixEquiv x₁ := by
    simp only [hx₁, hx₂, LinearEquiv.apply_symm_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hz₂ : cotangentDualMatrixEquiv x₂ * cotangentDualMatrixEquiv z -
      cotangentDualMatrixEquiv z * cotangentDualMatrixEquiv x₂ = 0 := by
    rw [← cotangentDualMatrixEquiv_lie, hz x₂, map_zero]
  have hid : (cotangentDualMatrixEquiv z).map (algebraMap k k) = cotangentDualMatrixEquiv z := by
    ext
    simp
  -- The trace form is invariant: `tr (⁅A, B⁆ C) = tr (A ⁅B, C⁆)`.
  rw [traceCovector_apply, hid, hY, Matrix.sub_mul, Matrix.trace_sub, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.trace_mul_comm (cotangentDualMatrixEquiv x₂), Matrix.mul_assoc,
    ← Matrix.trace_sub, ← Matrix.mul_sub, hz₂, Matrix.mul_zero, Matrix.trace_zero]

end GL₂

end TauCeti.GeneralLinear
