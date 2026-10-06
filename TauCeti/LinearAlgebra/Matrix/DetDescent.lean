/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.Rat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Localization.Integer

/-!
# Descending a nonsingular intertwining matrix to a smaller ring

Let `K` be an algebra over an infinite integral domain `F`, free as an `F`-module. A nonsingular
matrix `X` over `K` need not have a nonsingular entrywise image under a given `F`-linear functional
`K → F`, but it has one under *some* functional: writing the entries of `X` in a basis of `K` over
`F`, the determinant of the generic image is a nonzero polynomial over `F` in the coordinates of
the functional, and a nonzero polynomial over an infinite domain does not vanish everywhere
(`MvPolynomial.funext`). This is `Matrix.exists_linearMap_det_map_ne_zero`.

An `F`-linear functional respects every linear relation with coefficients in `F` between the
entries. So if a nonsingular matrix over `K` intertwines two families of matrices over `F`,
`B s * X = X * A s`, then so does a nonsingular matrix over `F`
(`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap`). This is the matrix form of the
Noether–Deuring theorem for an infinite base field: representations over `F` which become
isomorphic over `K` are already isomorphic over `F`.

For integer matrices and a `ℚ`-algebra `K`, clearing the denominators of the rational intertwiner
gives a nonsingular *integer* intertwiner
(`Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_intCast`). Read in bases of two free `ℤ`-modules
of the same rank, an integer matrix with nonzero determinant is an injective map
(`Matrix.injective_toLin_of_det_ne_zero`, over any integral domain) whose cokernel is finite
(`Matrix.finite_quotient_range_toLin_of_det_ne_zero`): composing with the adjugate matrix on
either side is multiplication by the determinant. So two integral representations of a group which
become isomorphic over a `ℚ`-algebra, for instance over `ℝ`, admit an injective intertwining map
with finite cokernel between them; this is the algebraic content of Tate's lemma on lattices in a
real representation.

## Main results

* `Matrix.exists_linearMap_det_map_ne_zero`: a nonsingular matrix over `K` has a nonsingular image
  under some `F`-linear functional `K → F`.
* `Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap`: a nonsingular matrix over `K`
  intertwining two families of matrices over `F` can be replaced by one over `F`.
* `Matrix.exists_det_ne_zero_forall_mul_eq_mul_of_intCast`: a nonsingular matrix over a
  `ℚ`-algebra intertwining two families of integer matrices can be replaced by an integer matrix.
* `Matrix.injective_toLin_of_det_ne_zero`, `Matrix.finite_quotient_range_toLin_of_det_ne_zero`:
  an integer matrix with nonzero determinant is a finite-index embedding of lattices.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, the Herbrand quotient of the unit group.
* C. W. Curtis and I. Reiner, *Representation Theory of Finite Groups and Associative Algebras*,
  §29 (the Noether–Deuring theorem).
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n]

/-- **A nonsingular matrix descends along some linear functional.** If `K` is an algebra over an
infinite integral domain `F` which is free as an `F`-module, then every matrix over `K` with
nonzero determinant has, under some `F`-linear functional `f : K → F` applied entrywise, an image
with nonzero determinant. -/
theorem exists_linearMap_det_map_ne_zero [DecidableEq n] {F K : Type*} [CommRing F] [IsDomain F]
    [Infinite F] [CommRing K] [Algebra F K] [Module.Free F K] {X : Matrix n n K} (hX : X.det ≠ 0) :
    ∃ f : K →ₗ[F] F, (X.map f).det ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis F K
  -- the generic functional, sending a basis vector to the corresponding variable
  let ℓ : K →ₗ[F] MvPolynomial (Module.Free.ChooseBasisIndex F K) F := b.constr F MvPolynomial.X
  have hℓ : (MvPolynomial.aeval fun k ↦ b k).toLinearMap ∘ₗ ℓ = LinearMap.id :=
    b.ext fun k ↦ by simp [ℓ]
  have hP : (X.map ℓ).det ≠ 0 := by
    intro h
    apply hX
    have := congrArg (MvPolynomial.aeval fun k ↦ b k) h
    rwa [AlgHom.map_det, map_zero, AlgHom.mapMatrix_apply, map_map,
      ← AlgHom.coe_toLinearMap, ← LinearMap.coe_comp, hℓ, LinearMap.id_coe, map_id] at this
  obtain ⟨q, hq⟩ : ∃ q, MvPolynomial.eval q (X.map ℓ).det ≠ 0 := by
    by_contra! h
    exact hP (MvPolynomial.funext fun q ↦ by simpa using h q)
  refine ⟨(MvPolynomial.aeval q).toLinearMap ∘ₗ ℓ, ?_⟩
  rw [LinearMap.coe_comp, ← map_map, AlgHom.coe_toLinearMap, ← AlgHom.mapMatrix_apply,
    ← AlgHom.map_det]
  simpa [MvPolynomial.coe_aeval_eq_eval] using hq

/-- An `F`-linear functional applied entrywise commutes with left multiplication by a matrix over
`F`. -/
private theorem map_algebraMap_mul {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    (f : K →ₗ[F] F) (C : Matrix n n F) (X : Matrix n n K) :
    (C.map (algebraMap F K) * X).map f = C * X.map f := by
  ext i j
  simp [mul_apply, ← Algebra.smul_def]

/-- An `F`-linear functional applied entrywise commutes with right multiplication by a matrix over
`F`. -/
private theorem map_mul_algebraMap {F K : Type*} [CommRing F] [CommRing K] [Algebra F K]
    (f : K →ₗ[F] F) (C : Matrix n n F) (X : Matrix n n K) :
    (X * C.map (algebraMap F K)).map f = X.map f * C := by
  ext i j
  simp only [map_apply, mul_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/-- **A nonsingular intertwiner descends to an infinite base ring.** Let `K` be an algebra over an
infinite integral domain `F`, free as an `F`-module, and let `A s` and `B s` be two families of
matrices over `F`. If a matrix `X` over `K` with nonzero determinant satisfies `B s * X = X * A s`
for every `s`, after mapping `A s` and `B s` to `K`, then so does a matrix over `F` with nonzero
determinant. This is the matrix form of the Noether–Deuring theorem for an infinite field. -/
theorem exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap [DecidableEq n] {ι F K : Type*}
    [CommRing F] [IsDomain F] [Infinite F] [CommRing K] [Algebra F K] [Module.Free F K]
    (A B : ι → Matrix n n F) {X : Matrix n n K} (hX : X.det ≠ 0)
    (hAB : ∀ s, (B s).map (algebraMap F K) * X = X * (A s).map (algebraMap F K)) :
    ∃ Y : Matrix n n F, Y.det ≠ 0 ∧ ∀ s, B s * Y = Y * A s := by
  obtain ⟨f, hf⟩ := exists_linearMap_det_map_ne_zero (F := F) hX
  exact ⟨X.map f, hf, fun s ↦ by
    simpa only [map_algebraMap_mul, map_mul_algebraMap] using congrArg (Matrix.map · f) (hAB s)⟩

/-- **A nonsingular intertwiner over a `ℚ`-algebra descends to the integers.** Let `A s` and
`B s` be two families of integer matrices. If a matrix `X` with nonzero determinant over a
`ℚ`-algebra `K` satisfies `B s * X = X * A s` for every `s`, after casting `A s` and `B s` to `K`,
then so does an integer matrix with nonzero determinant. -/
theorem exists_det_ne_zero_forall_mul_eq_mul_of_intCast [DecidableEq n] {ι K : Type*}
    [CommRing K] [Algebra ℚ K] (A B : ι → Matrix n n ℤ) {X : Matrix n n K} (hX : X.det ≠ 0)
    (hAB : ∀ s, (B s).map (Int.cast : ℤ → K) * X = X * (A s).map (Int.cast : ℤ → K)) :
    ∃ Z : Matrix n n ℤ, Z.det ≠ 0 ∧ ∀ s, B s * Z = Z * A s := by
  -- first descend to a rational intertwiner `Y`
  obtain ⟨Y, hY, hYAB⟩ := exists_det_ne_zero_forall_mul_eq_mul_of_algebraMap (K := K)
    (fun s ↦ (A s).map (Int.cast : ℤ → ℚ)) (fun s ↦ (B s).map (Int.cast : ℤ → ℚ)) hX
    fun s ↦ by simpa only [map_map, Function.comp_def, map_intCast] using hAB s
  -- then clear the denominators of `Y`
  obtain ⟨⟨d, hd⟩, hdY⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) fun p : n × n ↦ Y p.1 p.2
  choose Z hZ using hdY
  let Z' : Matrix n n ℤ := Matrix.of fun i j ↦ Z (i, j)
  have hZ' : Z'.map (Int.castRingHom ℚ) = (d : ℚ) • Y := by
    ext i j
    simpa [Z', zsmul_eq_mul] using hZ (i, j)
  have hd0 : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero hd)
  refine ⟨Z', fun h ↦ ?_, fun s ↦ map_injective (Int.castRingHom ℚ).injective_int ?_⟩
  · have := congrArg (Int.castRingHom ℚ) h
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hZ', det_smul, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hd0) hY this
  · dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, hZ', Matrix.mul_smul, Matrix.smul_mul, Int.coe_castRingHom,
      hYAB s]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A square matrix with nonzero determinant over an integral domain, read as a linear map in a
basis of the source and one of the target, is injective. -/
theorem injective_toLin_of_det_ne_zero {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (bM : Module.Basis ι R M)
    (bN : Module.Basis ι R N) {Z : Matrix ι ι R} (hZ : Z.det ≠ 0) :
    Function.Injective (toLin bM bN Z) := by
  have := Module.Free.of_basis bM
  intro x y h
  -- composing with the adjugate matrix is multiplication by the determinant
  have h' := congrArg (toLin bN bM Z.adjugate) h
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← toLin_mul, adjugate_mul,
    LinearEquiv.map_smul, toLin_one] at h'
  exact smul_right_injective M hZ h'

/-- A square integer matrix with nonzero determinant, read as a linear map in a basis of the
source and one of the target, has finite cokernel: the cokernel is finitely generated and killed by
the determinant. -/
theorem finite_quotient_range_toLin_of_det_ne_zero {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (bM : Module.Basis ι ℤ M) (bN : Module.Basis ι ℤ N)
    {Z : Matrix ι ι ℤ} (hZ : Z.det ≠ 0) : Finite (N ⧸ LinearMap.range (toLin bM bN Z)) := by
  -- `Module.finite_of_fg_torsion` is stated for the canonical `ℤ`-module structure
  obtain rfl := Subsingleton.elim ‹Module ℤ N› (AddCommGroup.toIntModule N)
  have := Module.Finite.of_basis bN
  refine Module.finite_of_fg_torsion _ fun y ↦ ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  refine ⟨⟨Z.det, mem_nonZeroDivisors_of_ne_zero hZ⟩, ?_⟩
  rw [Submonoid.mk_smul, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- `det Z • y` is the image of `adjugate Z • y`
  refine ⟨toLin bN bM Z.adjugate y, ?_⟩
  rw [← LinearMap.comp_apply, ← toLin_mul, mul_adjugate, LinearEquiv.map_smul, toLin_one]
  rfl

end Matrix
