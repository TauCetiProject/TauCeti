/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Nonsingular quadratic forms in characteristic two and symplectic planes

In characteristic two, the polarization `QuadraticMap.polar Q` of a quadratic map satisfies
`polar Q x x = 2 • Q x = 0`, so `Q.polarBilin` is alternating rather than recovering `Q`. In
particular, nondegeneracy of the polar bilinear form (`Q.polarBilin.Nondegenerate`, called
*nonsingularity* or *ordinary nondegeneracy* by Elman--Karpenko--Merkurjev) is strictly stronger
than `QuadraticMap.Nondegenerate`, which permits a rank-one polar kernel: `Q.polarBilin` is a
symplectic form on the ambient space, forcing even dimension and symplectic coordinates.

The characteristic-free polar-kernel descent, product, and totally isotropic dimension lemmas live
in `TauCeti.LinearAlgebra.QuadraticForm.Radical`, `TauCeti.LinearAlgebra.QuadraticForm.Prod`,
`TauCeti.LinearAlgebra.QuadraticForm.Isometry`, and
`TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic`. This file builds the symplectic-plane
models and characteristic-two structure that underpin the Arf invariant:

1. **Binary symplectic planes.** The plane `TauCeti.symplecticPlane R a b` on `Fin 2 → R` given by
   `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` carries a unimodular polar pairing whenever `2 = 0` (or
   `a = b = 0`). Over any commutative ring, `symplecticPlane R a 0` and `symplecticPlane R 0 b` are
   explicitly isometric to the hyperbolic plane `symplecticPlane R 0 0`. In characteristic two, the
   diagonal submodule of `Q.prod Q` is always `Q`-totally-isotropic, and the orthogonal sum of two
   copies of `symplecticPlane R 1 1` is explicitly isometric to the orthogonal sum of two copies of
   `symplecticPlane R 0 0`.
2. **Symplectic-basis decomposition.** Whenever `b : Module.Basis (ι ⊕ ι) R M` puts `Q.polarBilin`
   in standard symplectic form `Matrix.J ι R`, `Q` decomposes isometrically as the orthogonal sum of
   the planes `symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))`.
3. **Characteristic-two quadratic Lagrangians.** Over any field of characteristic two, a
   finite-dimensional quadratic space with nondegenerate polar form has even dimension, admits a
   symplectic basis, and splits into hyperbolic planes `symplecticPlane K 0 0` if and only if it
   contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement
   (equivalently, of half the ambient dimension).

## Main definitions

* `TauCeti.symplecticPlane`: the binary quadratic form `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` on
  `Fin 2 → R`.
* `TauCeti.isometryEquivSymplecticPlaneLeft`, `TauCeti.isometryEquivSymplecticPlaneRight`: explicit
  shear isometries from `symplecticPlane R a 0` and `symplecticPlane R 0 b` to
  `symplecticPlane R 0 0`.
* `TauCeti.isometryEquivSymplecticPlaneOneProd`: explicit characteristic-two isometry from
  `(symplecticPlane R 1 1).prod (symplecticPlane R 1 1)` to
  `(symplecticPlane R 0 0).prod (symplecticPlane R 0 0)`.
* `QuadraticMap.isometryEquivPiSymplecticPlane`: decomposition of `Q` along any symplectic basis of
  `Q.polarBilin` into an orthogonal sum of binary symplectic planes.

## Main results

* `QuadraticMap.nondegenerate_polarBilin_of_toMatrix_eq_J`: any finite basis putting `Q.polarBilin`
  in standard symplectic form `Matrix.J` witnesses `Q.polarBilin.Nondegenerate`.
* `QuadraticMap.isTotallyIsotropic_diag_prod`: in characteristic two, the diagonal submodule of
  `Q.prod Q` is totally isotropic.
* `QuadraticMap.isAlt_polarBilin`: in characteristic two, `Q.polarBilin` is alternating.
* `QuadraticMap.even_finrank_of_nondegenerate_polarBilin`,
  `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`: over a field of characteristic two, a
  finite-dimensional space with nondegenerate polar form has even dimension and a symplectic
  basis.
* `QuadraticMap.equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_orthogonal_eq`:
  over a field of characteristic two, splitting into hyperbolic planes is equivalent to the
  existence of a `Q`-totally-isotropic subspace equal to its polar orthogonal complement.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §§7--8.
-/

public section

universe u

/-! ### Symplectic polar matrices and characteristic-two diagonals -/

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- If a finite basis puts `Q.polarBilin` in standard symplectic form `Matrix.J`, then
`Q.polarBilin` is nondegenerate. -/
theorem nondegenerate_polarBilin_of_toMatrix_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm R M} {b : Module.Basis (ι ⊕ ι) R M}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    Q.polarBilin.Nondegenerate := by
  refine (LinearMap.BilinForm.nondegenerate_toMatrix_iff b).mp ?_
  rw [hb]
  exact Matrix.Nondegenerate.of_det_mem_nonZeroDivisors
    (Matrix.isUnit_det_J ι R).mem_nonZeroDivisors

/-- In characteristic two, the diagonal submodule `{(x, x) | x : M}` is totally isotropic for
`Q.prod Q`. -/
theorem isTotallyIsotropic_diag_prod [CharP R 2] (Q : QuadraticMap R M P) :
    (Q.prod Q).IsTotallyIsotropic
      (LinearMap.range (LinearMap.inl R M M + LinearMap.inr R M M)) := by
  rw [isTotallyIsotropic_iff]
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, QuadraticMap.prod_apply, ← two_nsmul, ← Nat.cast_smul_eq_nsmul R,
    CharP.cast_eq_zero, zero_smul]

/-- In characteristic two, the polar bilinear map of any quadratic map is alternating. -/
theorem isAlt_polarBilin [CharP R 2] (Q : QuadraticMap R M P) : Q.polarBilin.IsAlt := fun x ↦ by
  rw [polarBilin_apply_apply, polar_self, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero,
    zero_smul]

end QuadraticMap

/-! ### Binary symplectic planes -/

namespace TauCeti

open QuadraticMap

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- The binary quadratic form `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` on `Fin 2 → R`.

In characteristic two its polarization is the standard alternating pairing
`x 0 * y 1 + x 1 * y 0` independently of `a` and `b`; `symplecticPlane R 0 0` is the `xy`-hyperbolic
plane, and over `ZMod 2` the form `symplecticPlane (ZMod 2) 1 1` is the unique anisotropic
nonsingular plane. -/
def symplecticPlane (R : Type u) [CommSemiring R] (a b : R) : QuadraticForm R (Fin 2 → R) :=
  weightedSumSquares R ![a, b] + proj 0 1

/-- Evaluation of `TauCeti.symplecticPlane` in coordinates. -/
@[simp]
theorem symplecticPlane_apply (a b : R) (x : Fin 2 → R) :
    symplecticPlane R a b x = a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2 := by
  simp only [symplecticPlane, add_apply, weightedSumSquares_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, proj_apply, smul_eq_mul, pow_two]
  ring

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- Polarization of `TauCeti.symplecticPlane` over a commutative ring. -/
theorem polar_symplecticPlane (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane R a b) x y =
      2 * (a * (x 0 * y 0) + b * (x 1 * y 1)) + (x 0 * y 1 + x 1 * y 0) := by
  simp only [polar, symplecticPlane_apply, Pi.add_apply]
  ring

/-- Polarization of the hyperbolic plane `symplecticPlane R 0 0` in coordinates. -/
@[simp]
theorem polar_symplecticPlane_zero (x y : Fin 2 → R) :
    polar (symplecticPlane R 0 0) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_symplecticPlane]
  ring

/-- In characteristic two, the polarization of `symplecticPlane R a b` is `x 0 * y 1 + x 1 * y 0`,
independent of `a` and `b`. -/
@[simp]
theorem polar_symplecticPlane_of_charTwo [CharP R 2] (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane R a b) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_symplecticPlane, CharTwo.two_eq_zero, zero_mul, zero_add]

/-- The polar bilinear form of `symplecticPlane R 0 0` is nondegenerate over every commutative
ring. -/
theorem nondegenerate_polarBilin_symplecticPlane_zero :
    (symplecticPlane R 0 0).polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (symplecticPlane R 0 0).isSymm_polarBilin.isRefl]
  intro x hx
  have h0 : x 0 = 0 := by simpa [polarBilin_apply_apply] using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa [polarBilin_apply_apply] using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- In characteristic two, `symplecticPlane R a b` has nondegenerate polar bilinear form for all
`a, b : R`. -/
theorem nondegenerate_polarBilin_symplecticPlane [CharP R 2] (a b : R) :
    (symplecticPlane R a b).polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (symplecticPlane R a b).isSymm_polarBilin.isRefl]
  intro x hx
  have h0 : x 0 = 0 := by simpa [polarBilin_apply_apply] using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa [polarBilin_apply_apply] using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- The first coordinate axis `{x | x 1 = 0}` is totally isotropic for `symplecticPlane R 0 b`. -/
theorem isTotallyIsotropic_ker_proj_one_symplecticPlane (b : R) :
    (symplecticPlane R 0 b).IsTotallyIsotropic
      (LinearMap.ker (LinearMap.proj (R := R) (φ := fun _ : Fin 2 ↦ R) 1)) := by
  rw [isTotallyIsotropic_iff]
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.proj_apply] at hx
  simp [hx]

/-- Over a nontrivial commutative ring, the hyperbolic plane `symplecticPlane R 0 0` is not
anisotropic, since `![1, 0]` is a nonzero isotropic vector. -/
theorem not_anisotropic_symplecticPlane_zero [Nontrivial R] :
    ¬(symplecticPlane R 0 0).Anisotropic := by
  intro h
  have h10 := h ![1, 0] (by simp)
  exact one_ne_zero (α := R) (by simpa using congrFun h10 0)

/-- Explicit shear isometry `(x 0, x 1) ↦ (x 0, a * x 0 + x 1)` from `symplecticPlane R a 0` to
`symplecticPlane R 0 0`, valid over every commutative ring. -/
def isometryEquivSymplecticPlaneLeft (a : R) :
    (symplecticPlane R a 0).IsometryEquiv (symplecticPlane R 0 0) where
  toFun x := ![x 0, a * x 0 + x 1]
  invFun u := ![u 0, u 1 - a * u 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_left_comm]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    simp only [symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Coordinates of `TauCeti.isometryEquivSymplecticPlaneLeft`. -/
@[simp]
theorem isometryEquivSymplecticPlaneLeft_apply (a : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneLeft a x = ![x 0, a * x 0 + x 1] :=
  (rfl)

/-- Explicit shear isometry `(x 0, x 1) ↦ (x 0 + b * x 1, x 1)` from `symplecticPlane R 0 b` to
`symplecticPlane R 0 0`, valid over every commutative ring. -/
def isometryEquivSymplecticPlaneRight (b : R) :
    (symplecticPlane R 0 b).IsometryEquiv (symplecticPlane R 0 0) where
  toFun x := ![x 0 + b * x 1, x 1]
  invFun u := ![u 0 - b * u 1, u 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mul_add, add_assoc, add_left_comm]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mul_add, mul_left_comm]
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv u := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    simp only [symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Coordinates of `TauCeti.isometryEquivSymplecticPlaneRight`. -/
@[simp]
theorem isometryEquivSymplecticPlaneRight_apply (b : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneRight b x = ![x 0 + b * x 1, x 1] :=
  (rfl)

/-- In characteristic two, the orthogonal sum of two copies of `symplecticPlane R 1 1` is
explicitly isometric to the orthogonal sum of two hyperbolic planes `symplecticPlane R 0 0`. -/
def isometryEquivSymplecticPlaneOneProd [CharP R 2] :
    ((symplecticPlane R 1 1).prod (symplecticPlane R 1 1)).IsometryEquiv
      ((symplecticPlane R 0 0).prod (symplecticPlane R 0 0)) where
  toFun p := (![p.1 0 + p.2 1, p.1 1 + p.2 1],
    ![p.2 0 + p.1 0 + p.1 1, p.2 1 + p.2 0 + p.1 0 + p.1 1])
  invFun q := (![q.1 0 + q.2 0 + q.2 1, q.1 1 + q.2 0 + q.2 1],
    ![q.1 0 + q.1 1 + q.2 0, q.2 0 + q.2 1])
  map_add' p q := by
    ext i <;> fin_cases i <;> simp <;> ring
  map_smul' c p := by
    ext i <;> fin_cases i <;> simp [mul_add]
  left_inv p := by
    ext i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination (p.1 0 + p.1 1 + p.2 0 + p.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (p.1 0 + p.1 1 + p.2 0 + p.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (p.1 0 + p.1 1 + p.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (p.1 0 + p.1 1 + p.2 0) * CharTwo.two_eq_zero (R := R)
  right_inv q := by
    ext i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination (q.2 0 + q.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (q.2 0 + q.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (q.1 0 + q.1 1 + q.2 0 + q.2 1) * CharTwo.two_eq_zero (R := R)
    · linear_combination (q.1 0 + q.1 1 + 2 * q.2 0 + q.2 1) * CharTwo.two_eq_zero (R := R)
  map_app' p := by
    simp only [QuadraticMap.prod_apply, symplecticPlane_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination
      (p.1 0 * p.1 1 + p.1 0 * p.2 0 + p.1 0 * p.2 1 + p.1 1 * p.2 0 + p.1 1 * p.2 1) *
        CharTwo.two_eq_zero (R := R)

end CommRing

section Field

/-- Over a field, `symplecticPlane K 1 c` is anisotropic if and only if the Artin--Schreier
polynomial `t ^ 2 + t + c` has no root in `K`. -/
theorem anisotropic_symplecticPlane_one_iff {K : Type u} [Field K] (c : K) :
    (symplecticPlane K 1 c).Anisotropic ↔ ∀ t : K, t ^ 2 + t + c ≠ 0 := by
  refine ⟨fun h t ht ↦ ?_, fun h x hx ↦ ?_⟩
  · have h0 := h ![t, 1] (by simpa [symplecticPlane_apply] using ht)
    exact one_ne_zero (α := K) (by simpa using congrFun h0 1)
  · by_cases hx1 : x 1 = 0
    · have hx0 : x 0 = 0 := by simpa [symplecticPlane_apply, hx1] using hx
      ext i
      fin_cases i <;> simp [hx0, hx1]
    · refine False.elim (h (x 0 / x 1) ?_)
      have hdiv : (x 0 / x 1) ^ 2 + x 0 / x 1 + c =
          (x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2) / x 1 ^ 2 := by
        field_simp
      rw [hdiv]
      have hx' : x 0 ^ 2 + x 0 * x 1 + c * x 1 ^ 2 = 0 := by
        simpa [symplecticPlane_apply] using hx
      rw [hx', zero_div]

/-- Over `ZMod 2`, `symplecticPlane (ZMod 2) 1 1` (`x 0 ^ 2 + x 0 * x 1 + x 1 ^ 2`) is
anisotropic. -/
theorem anisotropic_symplecticPlane_one : (symplecticPlane (ZMod 2) 1 1).Anisotropic := by
  rw [anisotropic_symplecticPlane_one_iff]
  intro t
  fin_cases t <;> decide

end Field

end TauCeti

/-! ### Symplectic-basis decomposition and characteristic-two quadratic Lagrangians -/

namespace QuadraticMap

open TauCeti

section SymplecticDecomposition

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In a basis `b : Module.Basis (ι ⊕ ι) R M` in which `Q.polarBilin` has matrix `Matrix.J ι R`,
`Q v` expands as the sum over `i : ι` of the binary symplectic planes on the `i`-th coordinates. -/
theorem apply_eq_sum_of_toMatrix_polarBilin_eq_J (Q : QuadraticForm R M)
    {b : Module.Basis (ι ⊕ ι) R M}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (v : M) :
    Q v = ∑ i : ι, (Q (b (Sum.inl i)) * b.repr v (Sum.inl i) ^ 2 +
      b.repr v (Sum.inl i) * b.repr v (Sum.inr i) +
      Q (b (Sum.inr i)) * b.repr v (Sum.inr i) ^ 2) := by
  have hentry (x y : ι ⊕ ι) : polar Q (b x) (b y) = Matrix.J ι R x y := by
    simpa [polarBilin_apply_apply] using congrFun (congrFun hb x) y
  have hinl (i j : ι) : polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0 := by
    simpa [Matrix.J, Matrix.fromBlocks] using hentry (Sum.inl i) (Sum.inl j)
  have hinr (i j : ι) : polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0 := by
    simpa [Matrix.J, Matrix.fromBlocks] using hentry (Sum.inr i) (Sum.inr j)
  have hpair' (i j : ι) : polar Q (b (Sum.inr i)) (b (Sum.inl j)) = if i = j then 1 else 0 := by
    simpa [Matrix.J, Matrix.fromBlocks, Matrix.one_apply] using hentry (Sum.inr i) (Sum.inl j)
  have hpair (i j : ι) : polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if j = i then 1 else 0 := by
    rw [polar_comm, hpair']
  let u (i : ι) : M := b.repr v (Sum.inl i) • b (Sum.inl i) + b.repr v (Sum.inr i) • b (Sum.inr i)
  have hv : v = ∑ i : ι, u i := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  have hortho : Set.Pairwise (↑(Finset.univ : Finset ι)) fun i j ↦ Q.IsOrtho (u i) (u j) := by
    intro i _ j _ hij
    rw [← isOrtho_polarBilin, polarBilin_apply_apply]
    simp only [u, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hinl, hinr, hpair, hpair', hij, hij.symm, ↓reduceIte, smul_zero, add_zero]
  conv_lhs => rw [hv]
  rw [Q.map_sum_of_pairwise_isOrtho Finset.univ u hortho]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [u, QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
    hpair, ↓reduceIte, smul_eq_mul]
  ring

/-- A basis `b : Module.Basis (ι ⊕ ι) R M` putting `Q.polarBilin` in standard symplectic form
`Matrix.J ι R` decomposes `Q` isometrically into the orthogonal sum of the binary planes
`symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))`. -/
noncomputable def isometryEquivPiSymplecticPlane (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    Q.IsometryEquiv
      (QuadraticMap.pi fun i : ι ↦ symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))) where
  toFun v i := ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)]
  invFun c := b.equivFun.symm (Sum.elim (fun i ↦ c i 0) (fun i ↦ c i 1))
  map_add' x y := by
    ext i k
    fin_cases k <;> simp
  map_smul' r x := by
    ext i k
    fin_cases k <;> simp
  left_inv v := by
    apply b.equivFun.injective
    rw [b.equivFun.apply_symm_apply]
    ext (i | i) <;> simp [Module.Basis.equivFun_apply]
  right_inv c := by
    have h := b.equivFun.apply_symm_apply (Sum.elim (fun i ↦ c i 0) (fun i ↦ c i 1))
    ext i k
    fin_cases k
    · simpa [Module.Basis.equivFun_apply] using congrFun h (Sum.inl i)
    · simpa [Module.Basis.equivFun_apply] using congrFun h (Sum.inr i)
  map_app' v := by
    rw [pi_apply, Q.apply_eq_sum_of_toMatrix_polarBilin_eq_J hb v]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [symplecticPlane_apply]

/-- Coordinates of `QuadraticMap.isometryEquivPiSymplecticPlane`. -/
@[simp]
theorem isometryEquivPiSymplecticPlane_apply (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (v : M) (i : ι) :
    Q.isometryEquivPiSymplecticPlane b hb v i = ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] :=
  (rfl)

end SymplecticDecomposition

section CharTwoField

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over a field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form admits a symplectic basis `b : Module.Basis (Fin m ⊕ Fin m) K V`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) K V),
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K :=
  LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J Q.isAlt_polarBilin hQ

/-- Over a field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form has even dimension. -/
theorem even_finrank_of_nondegenerate_polarBilin {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) : Even (Module.finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank Q.isAlt_polarBilin hQ

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to the orthogonal sum of `m` hyperbolic
planes `symplecticPlane K 0 0` if and only if `V` contains a `Q`-totally-isotropic subspace of
dimension `m`. -/
theorem equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_finrank_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane K 0 0) ↔
      ∃ U : Submodule K V, Q.IsTotallyIsotropic U ∧ Module.finrank K U = m := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨U, hU, hUm⟩ ↦ ?_⟩
  · let f : (Fin m → K) →ₗ[K] (Fin m → Fin 2 → K) :=
      { toFun := fun c i ↦ ![c i, 0]
        map_add' := fun x y ↦ by ext i k; fin_cases k <;> simp
        map_smul' := fun r x ↦ by ext i k; fin_cases k <;> simp }
    have hf : Function.Injective f := fun x y hxy ↦ funext fun i ↦ by
      simpa [f] using congrFun (congrFun hxy i) 0
    refine ⟨(LinearMap.range f).map e.symm.toLinearMap, ?_, ?_⟩
    · rw [isTotallyIsotropic_iff]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      simp [f]
    · rw [e.symm.toLinearEquiv.finrank_map_eq, ← (LinearEquiv.ofInjective f hf).finrank_eq,
        Module.finrank_fin_fun]
  · have hU_orth : U = LinearMap.BilinForm.orthogonal Q.polarBilin U :=
      ((hU.orthogonal_polarBilin_eq_self_iff hQ).mpr (by omega)).symm
    let eU : Module.Basis (Fin m) K U := Module.finBasisOfFinrankEq K U hUm
    obtain ⟨b, hb, hbinl⟩ :=
      LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq Q.isAlt_polarBilin hQ eU hU_orth
    have hQinl (i : Fin m) : Q (b (Sum.inl i)) = 0 := by
      rw [hbinl i]
      exact hU.apply_eq_zero (eU i).2
    refine ⟨(Q.isometryEquivPiSymplecticPlane b hb).trans
      (IsometryEquiv.pi fun i ↦ ?_)⟩
    rw [hQinl i]
    exact isometryEquivSymplecticPlaneRight (Q (b (Sum.inr i)))

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to `m` hyperbolic planes if and only if
`V` contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement. -/
theorem equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_orthogonal_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane K 0 0) ↔
      ∃ U : Submodule K V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  rw [equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]
  refine ⟨fun ⟨U, hU, hUm⟩ ↦ ⟨U, hU, (hU.orthogonal_polarBilin_eq_self_iff hQ).mpr (by omega)⟩,
    fun ⟨U, hU, hUorth⟩ ↦ ⟨U, hU, ?_⟩⟩
  have := (hU.orthogonal_polarBilin_eq_self_iff hQ).mp hUorth
  omega

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to `m` hyperbolic planes if and only if
`V` contains a `Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ symplecticPlane K 0 0) ↔
      ∃ U : Submodule K V, Q.IsTotallyIsotropic U ∧
        2 * Module.finrank K U = Module.finrank K V := by
  rw [equivalent_pi_symplecticPlane_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]
  exact ⟨fun ⟨U, hU, hUm⟩ ↦ ⟨U, hU, by omega⟩, fun ⟨U, hU, hU2⟩ ↦ ⟨U, hU, by omega⟩⟩

end CharTwoField

end QuadraticMap
