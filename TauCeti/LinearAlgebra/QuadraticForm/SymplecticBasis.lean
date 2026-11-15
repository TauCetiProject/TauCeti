/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent

/-!
# Symplectic bases and binary symplectic planes for quadratic forms

In characteristic two, the polar bilinear form `Q.polarBilin` of a scalar-valued quadratic form
`Q` is alternating (`Q.polarBilin x x = 2 * Q x = 0`). When `Q.polarBilin` is nondegenerate on a
finite-dimensional vector space over a field of characteristic two, `V` therefore has even
dimension and admits a symplectic basis `b : Basis (Fin m ⊕ Fin m) K V` in which the Gram matrix
of `Q.polarBilin` is `Matrix.J (Fin m) K`.

Evaluating `Q` in any basis `b : Basis (ι ⊕ ι) R M` whose halves are polar-isotropic and paired
by the Kronecker delta splits `Q` into mutually orthogonal binary planes
`TauCeti.symplecticPlane R a b` (`(x₀, x₁) ↦ a x₀² + x₀ x₁ + b x₁²`). Two structural isometries
of these planes hold without field or finiteness hypotheses:

* Over any commutative ring `R`, `symplecticPlane R a b` is isometric to the split hyperbolic
  plane `TauCeti.splitHyperbolicPlane R` (`(x₀, x₁) ↦ x₀ x₁`) whenever `a * b = 0`, because
  `(x₀ + b x₁)(a x₀ + x₁) = a x₀² + x₀ x₁ + b x₁²`.
* Over any commutative ring `R` of characteristic two, the orthogonal sum of two copies of
  `symplecticPlane R 1 1` is isometric to the orthogonal sum of two split hyperbolic planes.

We also record the characteristic-free dimension bound for totally isotropic subspaces of a
polar-nondegenerate quadratic space over a field: every totally isotropic subspace `W` satisfies
`W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W`, hence `2 * finrank K W ≤ finrank K V`, with
equality if and only if `W` is Lagrangian for `Q.polarBilin`.

## Main definitions

* `TauCeti.splitHyperbolicPlane`: the split hyperbolic plane `(x₀, x₁) ↦ x₀ x₁` on `Fin 2 → R`.
* `TauCeti.symplecticPlane`: the binary quadratic form `(x₀, x₁) ↦ a x₀² + x₀ x₁ + b x₁²` on
  `Fin 2 → R`.
* `QuadraticMap.isometryEquivPiSymplecticPlane`: the isometry from `Q` to an orthogonal sum of
  binary symplectic planes determined by a symplectically paired basis.
* `TauCeti.isometryEquivSymplecticPlaneZeroRight`,
  `TauCeti.isometryEquivSymplecticPlaneZeroLeft`,
  `TauCeti.isometryEquivSymplecticPlaneOfMulEqZero`: isometries from `symplecticPlane R a b`
  (when `b = 0`, `a = 0`, or `a * b = 0`) to `splitHyperbolicPlane R`.
* `TauCeti.isometryEquivSymplecticPlaneOneOneProd`: in characteristic two, the explicit isometry
  from `symplecticPlane R 1 1 ⊥ symplecticPlane R 1 1` to the orthogonal sum of two split
  hyperbolic planes.

## Main results

* `QuadraticMap.IsTotallyIsotropic.eq_orthogonal_polarBilin_iff_two_mul_finrank_eq`: a totally
  isotropic subspace of a polar-nondegenerate space is polar-Lagrangian iff it is half-dimensional.
* `QuadraticMap.isAlt_polarBilin`: in characteristic two, `Q.polarBilin` is alternating.
* `QuadraticMap.apply_of_toMatrix_polarBilin_eq_J`: coordinate expansion of `Q` in a symplectic
  basis.
* `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`: over a field of characteristic two, a
  polar-nondegenerate finite-dimensional quadratic space admits a symplectic basis.
* `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J_inl_eq_and_apply_eq_zero`: over a field of
  characteristic two, a basis of a `Q`-totally-isotropic polar-Lagrangian subspace extends to a
  symplectic basis of `Q`-isotropic vectors.
* `QuadraticMap.equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_eq_orthogonal`:
  over a field of characteristic two, a polar-nondegenerate space is equivalent to an orthogonal
  sum of split hyperbolic planes iff it admits a `Q`-totally-isotropic polar-Lagrangian subspace.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*
  (2008), Chapter II, §§7–8.
-/

public section

open Module Submodule QuadraticMap

namespace TauCeti

universe u

section CommRing

variable {R : Type u} [CommRing R]

/-- The split hyperbolic plane `(x₀, x₁) ↦ x₀ x₁` on `Fin 2 → R`.

Unlike `TauCeti.hyperbolicPlane`, which is the diagonal form `x₀² - x₁²` when `2` is invertible,
`splitHyperbolicPlane` has nondegenerate polar form over every commutative ring, including rings
of characteristic two. -/
def splitHyperbolicPlane (R : Type u) [CommRing R] : QuadraticForm R (Fin 2 → R) :=
  QuadraticMap.proj 0 1

/-- Evaluation of `TauCeti.splitHyperbolicPlane`. -/
@[simp]
theorem splitHyperbolicPlane_apply (x : Fin 2 → R) :
    splitHyperbolicPlane R x = x 0 * x 1 :=
  (rfl)

/-- Polarization of `TauCeti.splitHyperbolicPlane`. -/
@[simp]
theorem polar_splitHyperbolicPlane (x y : Fin 2 → R) :
    polar (splitHyperbolicPlane R) x y = x 0 * y 1 + x 1 * y 0 := by
  simp only [polar, splitHyperbolicPlane_apply, Pi.add_apply]
  ring

/-- The polar bilinear form of `TauCeti.splitHyperbolicPlane` is nondegenerate over every
commutative ring. -/
theorem nondegenerate_polarBilin_splitHyperbolicPlane :
    (splitHyperbolicPlane R).polarBilin.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (splitHyperbolicPlane R).isSymm_polarBilin.isRefl).mpr fun x hx ↦ ?_
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- The split hyperbolic plane is nondegenerate over every commutative ring. -/
theorem nondegenerate_splitHyperbolicPlane : (splitHyperbolicPlane R).Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp nondegenerate_polarBilin_splitHyperbolicPlane.1)

/-- The binary symplectic plane `(x₀, x₁) ↦ a x₀² + x₀ x₁ + b x₁²` on `Fin 2 → R`.

On the standard basis `e₀ = ![1, 0]`, `e₁ = ![0, 1]`, it takes values `Q e₀ = a` and `Q e₁ = b`
with `polar Q e₀ e₁ = 1`. -/
def symplecticPlane (R : Type u) [CommRing R] (a b : R) : QuadraticForm R (Fin 2 → R) :=
  a • QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 + b • QuadraticMap.proj 1 1

/-- Evaluation of `TauCeti.symplecticPlane`. -/
@[simp]
theorem symplecticPlane_apply (a b : R) (x : Fin 2 → R) :
    symplecticPlane R a b x = a * (x 0 * x 0) + x 0 * x 1 + b * (x 1 * x 1) := by
  simp [symplecticPlane, smul_eq_mul]

/-- With zero diagonal weights, `TauCeti.symplecticPlane` is `TauCeti.splitHyperbolicPlane`. -/
@[simp]
theorem symplecticPlane_zero_zero :
    symplecticPlane R 0 0 = splitHyperbolicPlane R := by
  ext x
  simp

/-- Polarization of `TauCeti.symplecticPlane`. -/
theorem polar_symplecticPlane (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane R a b) x y =
      2 * a * (x 0 * y 0) + (x 0 * y 1 + x 1 * y 0) + 2 * b * (x 1 * y 1) := by
  simp only [polar, symplecticPlane_apply, Pi.add_apply]
  ring

/-- Swapping coordinates gives an isometry between `symplecticPlane R a b` and
`symplecticPlane R b a`. -/
def isometryEquivSymplecticPlaneSwap (a b : R) :
    (symplecticPlane R a b).IsometryEquiv (symplecticPlane R b a) where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl
  left_inv _ := by ext i; fin_cases i <;> rfl
  right_inv _ := by ext i; fin_cases i <;> rfl
  map_app' x := by
    simp only [symplecticPlane_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Forward map of `TauCeti.isometryEquivSymplecticPlaneSwap`. -/
@[simp]
theorem isometryEquivSymplecticPlaneSwap_apply (a b : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneSwap a b x = ![x 1, x 0] :=
  (rfl)

/-- The shear `(x₀, x₁) ↦ (x₀, a x₀ + x₁)` is an isometry from `symplecticPlane R a 0` to
`splitHyperbolicPlane R`, over any commutative ring. -/
def isometryEquivSymplecticPlaneZeroRight (a : R) :
    (symplecticPlane R a 0).IsometryEquiv (splitHyperbolicPlane R) where
  toFun x := ![x 0, a * x 0 + x 1]
  invFun y := ![y 0, y 1 - a * y 0]
  map_add' _ _ := by
    ext i
    fin_cases i
    · simp
    · simp; ring
  map_smul' _ _ := by
    ext i
    fin_cases i
    · simp
    · simp; ring
  left_inv _ := by
    ext i
    fin_cases i <;> simp
  right_inv _ := by
    ext i
    fin_cases i <;> simp
  map_app' x := by
    simp only [splitHyperbolicPlane_apply, symplecticPlane_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Forward map of `TauCeti.isometryEquivSymplecticPlaneZeroRight`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroRight_apply (a : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneZeroRight a x = ![x 0, a * x 0 + x 1] :=
  (rfl)

/-- Over any commutative ring, `symplecticPlane R 0 b` is isometric to `splitHyperbolicPlane R`. -/
def isometryEquivSymplecticPlaneZeroLeft (b : R) :
    (symplecticPlane R 0 b).IsometryEquiv (splitHyperbolicPlane R) :=
  (isometryEquivSymplecticPlaneSwap 0 b).trans (isometryEquivSymplecticPlaneZeroRight b)

/-- Forward map of `TauCeti.isometryEquivSymplecticPlaneZeroLeft`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroLeft_apply (b : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneZeroLeft b x = ![x 1, b * x 1 + x 0] :=
  (rfl)

/-- Over any commutative ring, `TauCeti.splitHyperbolicPlane` is isometric to
`QuadraticForm.dualProd R R`. -/
def isometryEquivSplitHyperbolicPlaneDualProd :
    (splitHyperbolicPlane R).IsometryEquiv (QuadraticForm.dualProd R R) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    (((LinearMap.ringLmapEquivSelf R R R).symm).prodCongr (LinearEquiv.refl R R))
  map_app' x := by
    -- Expose the underlying linear equivalence application in `IsometryEquiv.map_app'`.
    change QuadraticForm.dualProd R R ((LinearMap.ringLmapEquivSelf R R R).symm (x 0), x 1) =
      splitHyperbolicPlane R x
    simp [mul_comm]

/-- Forward map of `TauCeti.isometryEquivSplitHyperbolicPlaneDualProd`. -/
@[simp]
theorem isometryEquivSplitHyperbolicPlaneDualProd_apply (x : Fin 2 → R) :
    isometryEquivSplitHyperbolicPlaneDualProd x =
      ((LinearMap.ringLmapEquivSelf R R R).symm (x 0), x 1) :=
  (rfl)

/-- Over any nontrivial commutative ring, `TauCeti.splitHyperbolicPlane` is isotropic. -/
theorem not_anisotropic_splitHyperbolicPlane [Nontrivial R] :
    ¬ (splitHyperbolicPlane R).Anisotropic := by
  rw [QuadraticMap.not_anisotropic_iff_exists]
  refine ⟨![1, 0], fun h ↦ (one_ne_zero : (1 : R) ≠ 0) (by simpa using congrFun h 0), by simp⟩

/-- Over any commutative ring, when `a * b = 0`, the invertible transformation
`(x₀, x₁) ↦ (x₀ + b x₁, a x₀ + x₁)` (with inverse `(y₀, y₁) ↦ (y₀ - b y₁, y₁ - a y₀)`) is an
isometry from `symplecticPlane R a b` to `splitHyperbolicPlane R`. -/
def isometryEquivSymplecticPlaneOfMulEqZero {a b : R} (hab : a * b = 0) :
    (symplecticPlane R a b).IsometryEquiv (splitHyperbolicPlane R) where
  toFun x := ![x 0 + b * x 1, a * x 0 + x 1]
  invFun y := ![y 0 - b * y 1, y 1 - a * y 0]
  map_add' _ _ := by
    ext i
    fin_cases i <;> (simp; ring)
  map_smul' _ _ := by
    ext i
    fin_cases i <;> (simp; ring)
  left_inv x := by
    have h0 : x 0 + b * x 1 - b * (a * x 0 + x 1) = x 0 - (a * b) * x 0 := by ring
    have h1 : a * x 0 + x 1 - a * (x 0 + b * x 1) = x 1 - (a * b) * x 1 := by ring
    ext i
    fin_cases i <;> simp [h0, h1, hab]
  right_inv y := by
    have h0 : y 0 - b * y 1 + b * (y 1 - a * y 0) = y 0 - (a * b) * y 0 := by ring
    have h1 : a * (y 0 - b * y 1) + (y 1 - a * y 0) = y 1 - (a * b) * y 1 := by ring
    ext i
    fin_cases i <;> simp [h0, h1, hab]
  map_app' x := by
    have hq : (x 0 + b * x 1) * (a * x 0 + x 1) =
        a * (x 0 * x 0) + x 0 * x 1 + b * (x 1 * x 1) + (a * b) * (x 0 * x 1) := by ring
    simp only [splitHyperbolicPlane_apply, symplecticPlane_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, hq, hab, zero_mul, add_zero]

/-- Forward map of `TauCeti.isometryEquivSymplecticPlaneOfMulEqZero`. -/
@[simp]
theorem isometryEquivSymplecticPlaneOfMulEqZero_apply {a b : R} (hab : a * b = 0)
    (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneOfMulEqZero hab x = ![x 0 + b * x 1, a * x 0 + x 1] :=
  (rfl)

/-- Over any commutative ring, `symplecticPlane R a b` is equivalent to `splitHyperbolicPlane R`
whenever `a * b = 0`. -/
theorem equivalent_splitHyperbolicPlane_of_mul_eq_zero {a b : R} (hab : a * b = 0) :
    (symplecticPlane R a b).Equivalent (splitHyperbolicPlane R) :=
  ⟨isometryEquivSymplecticPlaneOfMulEqZero hab⟩

end CommRing

section CharTwo

open scoped CharTwo

variable {R : Type u} [CommRing R] [CharP R 2]

/-- In characteristic two, the polar form of `TauCeti.symplecticPlane` is independent of its
diagonal weights. -/
@[simp]
theorem polar_symplecticPlane_of_charTwo (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane R a b) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_symplecticPlane, CharTwo.two_eq_zero]
  ring

/-- In characteristic two, `TauCeti.symplecticPlane` has nondegenerate polar form for all weights
`a, b`. -/
theorem nondegenerate_polarBilin_symplecticPlane (a b : R) :
    (symplecticPlane R a b).polarBilin.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (symplecticPlane R a b).isSymm_polarBilin.isRefl).mpr fun x hx ↦ ?_
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- In characteristic two, `TauCeti.symplecticPlane` is nondegenerate for all weights `a, b`. -/
theorem nondegenerate_symplecticPlane (a b : R) :
    (symplecticPlane R a b).Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp (nondegenerate_polarBilin_symplecticPlane a b).1)

/-- **Two `[1, 1]` planes are isometric to two split hyperbolic planes in characteristic two.**

In the standard basis `(a₁, b₁)` and `(a₂, b₂)` of the two `[1, 1]` planes, the vectors
`e₁ = (a₁, a₂)`, `f₁ = (b₁, a₂)`, `e₂ = (a₁ + b₁, b₂)`, `f₂ = (a₁ + b₁, a₂ + b₂)` are isotropic
and form two orthogonal hyperbolic pairs. -/
def isometryEquivSymplecticPlaneOneOneProd :
    ((symplecticPlane R 1 1).prod (symplecticPlane R 1 1)).IsometryEquiv
      ((splitHyperbolicPlane R).prod (splitHyperbolicPlane R)) where
  toFun p :=
    (![p.1 0 + p.2 1, p.1 1 + p.2 1],
      ![p.1 0 + p.1 1 + p.2 0 + p.2 1, p.1 0 + p.1 1 + p.2 0])
  invFun q :=
    (![q.1 0 + q.2 0 + q.2 1, q.1 1 + q.2 0 + q.2 1],
      ![q.1 0 + q.1 1 + q.2 1, q.2 0 + q.2 1])
  map_add' _ _ := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> (simp; ring)
  map_smul' _ _ := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;> (simp; ring)
  left_inv p := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring_nf; simp)
  right_inv q := by
    refine Prod.ext (funext fun i ↦ ?_) (funext fun i ↦ ?_) <;> fin_cases i <;>
      (simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; ring_nf; simp)
  map_app' p := by
    simp only [QuadraticMap.prod_apply, splitHyperbolicPlane_apply, symplecticPlane_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
    ring_nf
    simp

/-- Forward map of `TauCeti.isometryEquivSymplecticPlaneOneOneProd`. -/
@[simp]
theorem isometryEquivSymplecticPlaneOneOneProd_apply
    (p : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivSymplecticPlaneOneOneProd p =
      (![p.1 0 + p.2 1, p.1 1 + p.2 1],
        ![p.1 0 + p.1 1 + p.2 0 + p.2 1, p.1 0 + p.1 1 + p.2 0]) :=
  (rfl)

/-- In characteristic two, `symplecticPlane R 1 1 ⊥ symplecticPlane R 1 1` is equivalent to the
orthogonal sum of two split hyperbolic planes. -/
theorem equivalent_symplecticPlane_one_one_prod :
    ((symplecticPlane R 1 1).prod (symplecticPlane R 1 1)).Equivalent
      ((splitHyperbolicPlane R).prod (splitHyperbolicPlane R)) :=
  ⟨isometryEquivSymplecticPlaneOneOneProd⟩

end CharTwo

end TauCeti

namespace QuadraticMap

section CommRing

variable {R M M₁ M₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- An isometric equivalence of scalar quadratic forms preserves nondegeneracy of the polar
bilinear form. -/
theorem IsometryEquiv.nondegenerate_polarBilin_iff
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (e : Q₁.IsometryEquiv Q₂) :
    Q₁.polarBilin.Nondegenerate ↔ Q₂.polarBilin.Nondegenerate := by
  have hL : Q₁.polarBilin.SeparatingLeft ↔ Q₂.polarBilin.SeparatingLeft := by
    refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
    · rw [← e.apply_symm_apply y, map_eq_zero_iff e e.injective]
      refine h (e.symm y) fun x ↦ ?_
      rw [polarBilin_apply_apply, ← e.polar_apply, e.apply_symm_apply]
      simpa [polarBilin_apply_apply] using hy (e x)
    · rw [← map_eq_zero_iff e e.injective]
      refine h (e x) fun y ↦ ?_
      simpa [polarBilin_apply_apply, ← e.polar_apply] using hx (e.symm y)
  simpa only [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    Q₁.isSymm_polarBilin.isRefl, LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    Q₂.isSymm_polarBilin.isRefl] using hL

/-- Every totally isotropic submodule is contained in its polar orthogonal complement. -/
theorem IsTotallyIsotropic.le_orthogonal_polarBilin {Q : QuadraticForm R M}
    {W : Submodule R M} (hW : Q.IsTotallyIsotropic W) :
    W ≤ LinearMap.BilinForm.orthogonal Q.polarBilin W :=
  fun _ hx _ hy ↦ hW.polar_eq_zero hy hx

/-- The polar bilinear form of an orthogonal product is the block-diagonal product of the polar
bilinear forms. -/
theorem polarBilin_prod_eq_prod (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.prod Q₂).polarBilin = LinearMap.BilinForm.prod Q₁.polarBilin Q₂.polarBilin :=
  LinearMap.ext₂ fun x y ↦ by simp

/-- The polar bilinear form of an orthogonal product is nondegenerate if and only if both factors
have nondegenerate polar bilinear forms. -/
theorem nondegenerate_polarBilin_prod_iff {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} :
    (Q₁.prod Q₂).polarBilin.Nondegenerate ↔
      Q₁.polarBilin.Nondegenerate ∧ Q₂.polarBilin.Nondegenerate := by
  rw [polarBilin_prod_eq_prod]
  exact LinearMap.BilinForm.nondegenerate_prod_iff

/-- The polar bilinear form of `QuadraticForm.dualProd R M` is `LinearMap.dualProd R M`. -/
@[simp]
theorem _root_.QuadraticForm.polarBilin_dualProd :
    (QuadraticForm.dualProd R M).polarBilin = LinearMap.dualProd R M := by
  refine LinearMap.ext fun p ↦ LinearMap.ext fun q ↦ ?_
  simp only [polarBilin_apply_apply, polar, Prod.fst_add, Prod.snd_add,
    QuadraticForm.dualProd_apply, LinearMap.add_apply, map_add, LinearMap.dualProd_apply_apply]
  ring

/-- Over any commutative ring, the polar bilinear form of `QuadraticForm.dualProd R M` on a
projective module `M` is nondegenerate. -/
theorem _root_.QuadraticForm.nondegenerate_polarBilin_dualProd [Module.Projective R M] :
    (QuadraticForm.dualProd R M).polarBilin.Nondegenerate := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (QuadraticForm.dualProd R M).isSymm_polarBilin.isRefl,
    QuadraticForm.polarBilin_dualProd, LinearMap.separatingLeft_dualProd]
  exact Module.eval_apply_injective R

/-- The polar bilinear form of a finite orthogonal sum is nondegenerate if and only if each
summand has nondegenerate polar bilinear form. -/
theorem nondegenerate_polarBilin_pi_iff {ι : Type*} [Fintype ι] {Mᵢ : ι → Type*}
    [∀ i, AddCommGroup (Mᵢ i)] [∀ i, Module R (Mᵢ i)]
    {Q : ∀ i, QuadraticForm R (Mᵢ i)} :
    (QuadraticMap.pi Q).polarBilin.Nondegenerate ↔
      ∀ i, (Q i).polarBilin.Nondegenerate := by
  classical
  have hpi : (QuadraticMap.pi Q).polarBilin.Nondegenerate ↔
      (QuadraticMap.pi Q).polarBilin.SeparatingLeft :=
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft (QuadraticMap.pi Q).isSymm_polarBilin.isRefl
  have hi (i : ι) : (Q i).polarBilin.Nondegenerate ↔ (Q i).polarBilin.SeparatingLeft :=
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft (Q i).isSymm_polarBilin.isRefl
  simp_rw [hpi, hi]
  refine ⟨fun h i x hx ↦ ?_, fun h x hx ↦ funext fun i ↦ h i (x i) fun y ↦ ?_⟩
  · have hsingle : Pi.single i x = 0 := h (Pi.single i x) fun y ↦ by
      rw [polarBilin_apply_apply, QuadraticMap.Ring.polar_pi,
        Fintype.sum_eq_single i fun j hj ↦ ?_, Pi.single_eq_same]
      · exact hx (y i)
      · rw [Pi.single_eq_of_ne hj, polar_zero_left]
    simpa using congrFun hsingle i
  · have hy := hx (Pi.single i y)
    rw [polarBilin_apply_apply, QuadraticMap.Ring.polar_pi,
      Fintype.sum_eq_single i fun j hj ↦ ?_, Pi.single_eq_same] at hy
    · exact hy
    · rw [Pi.single_eq_of_ne hj, polar_zero_right]

/-- A scalar quadratic form with nondegenerate polar bilinear form is nondegenerate. -/
theorem nondegenerate_of_nondegenerate_polarBilin {Q : QuadraticForm R M}
    (hQ : Q.polarBilin.Nondegenerate) : Q.Nondegenerate :=
  nondegenerate_of_ker_polarBilin_eq_bot (LinearMap.separatingLeft_iff_ker_eq_bot.mp hQ.1)

/-- Polarization of `Q.lift N hN` on quotient representatives equals polarization of `Q`. -/
@[simp]
theorem polar_lift_mk {P : Type*} [AddCommGroup P] [Module R P] (Q : QuadraticMap R M P)
    {N : Submodule R M} (hN : N ≤ Q.radical) (x y : M) :
    polar (Q.lift N hN) (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = polar Q x y := by
  simp only [polar, ← Submodule.Quotient.mk_add, lift_mk]

/-- The form induced by `Q` on `M ⧸ Q.radical` has nondegenerate polar bilinear form if and only
if `Q.radical = Q.polarBilin.ker` (that is, `Q` vanishes on the kernel of its polar form). -/
theorem nondegenerate_polarBilin_lift_radical_iff {Q : QuadraticForm R M} :
    (Q.lift Q.radical le_rfl).polarBilin.Nondegenerate ↔ Q.radical = Q.polarBilin.ker := by
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (Q.lift Q.radical le_rfl).isSymm_polarBilin.isRefl]
  refine ⟨fun h ↦ le_antisymm Q.radical_le_ker_polarBilin fun x hx ↦ ?_, fun h q hq ↦ ?_⟩
  · rw [← Submodule.Quotient.mk_eq_zero]
    refine h (Submodule.Quotient.mk x) fun q ↦ ?_
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      rw [polarBilin_apply_apply, polar_lift_mk]
      simpa [polarBilin_apply_apply] using LinearMap.congr_fun hx y
  · induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero, h, LinearMap.mem_ker]
      ext y
      simpa [polarBilin_apply_apply] using hq (Submodule.Quotient.mk y)

/-- The form induced by `Q` on `M ⧸ Q.radical` has nondegenerate polar bilinear form if and only
if `Q` vanishes on every vector in `Q.polarBilin.ker`. -/
theorem nondegenerate_polarBilin_lift_radical_iff_forall_ker {Q : QuadraticForm R M} :
    (Q.lift Q.radical le_rfl).polarBilin.Nondegenerate ↔
      ∀ x ∈ Q.polarBilin.ker, Q x = 0 := by
  rw [nondegenerate_polarBilin_lift_radical_iff]
  refine ⟨fun h x hx ↦ (h.symm ▸ hx).1,
    fun h ↦ le_antisymm Q.radical_le_ker_polarBilin fun x hx ↦ ⟨h x hx, hx⟩⟩

/-- **Coordinate formula for a quadratic form in a symplectically paired basis.**

If `b : Basis (ι ⊕ ι) R M` has polar-isotropic halves paired by the Kronecker delta, then `Q`
decomposes on `v` as the sum over `i : ι` of the binary symplectic planes
`xᵢ² Q(eᵢ) + yᵢ² Q(fᵢ) + xᵢ yᵢ`. -/
theorem apply_of_polar_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm R M)
    (b : Basis (ι ⊕ ι) R M)
    (hll : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0)
    (v : M) :
    Q v = ∑ i : ι, ((b.repr v (Sum.inl i)) ^ 2 * Q (b (Sum.inl i)) +
      (b.repr v (Sum.inr i)) ^ 2 * Q (b (Sum.inr i)) +
      b.repr v (Sum.inl i) * b.repr v (Sum.inr i)) := by
  let u : ι → M := fun i ↦
    b.repr v (Sum.inl i) • b (Sum.inl i) + b.repr v (Sum.inr i) • b (Sum.inr i)
  have hsum : ∑ i : ι, u i = v := by
    calc ∑ i : ι, u i
        = (∑ i : ι, b.repr v (Sum.inl i) • b (Sum.inl i)) +
          ∑ i : ι, b.repr v (Sum.inr i) • b (Sum.inr i) := Finset.sum_add_distrib
      _ = ∑ x : ι ⊕ ι, b.repr v x • b x :=
        (Fintype.sum_sum_type fun x ↦ b.repr v x • b x).symm
      _ = v := b.sum_repr v
  have horth {i j : ι} (hij : i ≠ j) : polar Q (u i) (u j) = 0 := by
    have hji : j ≠ i := hij.symm
    simp only [u, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hll, hrr, hlr, polar_comm Q (b (Sum.inr i)) (b (Sum.inl j)), hij, hji, ite_false,
      smul_zero, add_zero]
  conv_lhs => rw [← hsum]
  rw [QuadraticMap.map_sum]
  have hsym2 : (∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ ij.IsDiag,
      polarSym2 Q (ij.map u)) = 0 := by
    refine Finset.sum_eq_zero fun ij hij ↦ ?_
    rw [Finset.mem_filter] at hij
    induction ij using Sym2.ind with
    | _ i j =>
      rw [Sym2.mk_isDiag_iff] at hij
      simpa using horth hij.2
  rw [hsym2, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [u, QuadraticMap.map_add, QuadraticMap.map_smul, polar_smul_left, polar_smul_right,
    hlr, ite_true, smul_eq_mul, pow_two]
  ring

/-- A symplectically paired basis `b : Basis (ι ⊕ ι) R M` gives an isometric equivalence between
`Q` and the orthogonal sum of the binary symplectic planes `symplecticPlane R (Q eᵢ) (Q fᵢ)`. -/
noncomputable def isometryEquivPiSymplecticPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hll : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) :
    Q.IsometryEquiv (QuadraticMap.pi fun i : ι ↦
      TauCeti.symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))) where
  toLinearEquiv := b.equivFun.trans
    { toFun := fun c i ↦ ![c (Sum.inl i), c (Sum.inr i)]
      invFun := fun d ↦ Sum.elim (fun i ↦ d i 0) (fun i ↦ d i 1)
      map_add' := fun _ _ ↦ by ext i k; fin_cases k <;> rfl
      map_smul' := fun _ _ ↦ by ext i k; fin_cases k <;> rfl
      left_inv := fun c ↦ by ext (i | i) <;> rfl
      right_inv := fun d ↦ by ext i k; fin_cases k <;> rfl }
  map_app' v := by
    -- Expose the underlying linear equivalence application in `IsometryEquiv.map_app'`.
    change (QuadraticMap.pi fun i : ι ↦
      TauCeti.symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i))))
      (fun i ↦ ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)]) = Q v
    rw [QuadraticMap.pi_apply, Q.apply_of_polar_eq b hll hrr hlr v]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TauCeti.symplecticPlane_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- Coordinate formula for `QuadraticMap.isometryEquivPiSymplecticPlane`. -/
@[simp]
theorem isometryEquivPiSymplecticPlane_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hll : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0)
    (v : M) (i : ι) :
    Q.isometryEquivPiSymplecticPlane b hll hrr hlr v i =
      ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] :=
  (rfl)

end CommRing

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {W : Submodule K V}

/-- In a finite-dimensional quadratic space with nondegenerate polar form, a totally isotropic
subspace has at most half the ambient dimension. -/
theorem IsTotallyIsotropic.two_mul_finrank_le_of_nondegenerate_polarBilin
    (hW : Q.IsTotallyIsotropic W) (hQ : Q.polarBilin.Nondegenerate) :
    2 * Module.finrank K W ≤ Module.finrank K V := by
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal Q.isSymm_polarBilin.isRefl W
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_bot_eq, finrank_bot,
    add_zero] at hdim
  have hle := Submodule.finrank_mono hW.le_orthogonal_polarBilin
  omega

/-- In a finite-dimensional quadratic space with nondegenerate polar form, a totally isotropic
subspace equals its polar orthogonal complement if and only if it has half the ambient
dimension. -/
theorem IsTotallyIsotropic.eq_orthogonal_polarBilin_iff_two_mul_finrank_eq
    (hW : Q.IsTotallyIsotropic W) (hQ : Q.polarBilin.Nondegenerate) :
    W = LinearMap.BilinForm.orthogonal Q.polarBilin W ↔
      2 * Module.finrank K W = Module.finrank K V := by
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal Q.isSymm_polarBilin.isRefl W
  rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ, inf_bot_eq, finrank_bot,
    add_zero] at hdim
  refine ⟨fun h ↦ ?_, fun h ↦ Submodule.eq_of_le_of_finrank_eq hW.le_orthogonal_polarBilin ?_⟩
  · rw [← h] at hdim
    omega
  · omega

omit [FiniteDimensional K V] in
/-- Over any field, a quadratic space that is isometric to an orthogonal sum of `m` split
hyperbolic planes admits a `Q`-totally-isotropic polar-Lagrangian subspace of dimension `m`. -/
theorem exists_isTotallyIsotropic_and_eq_orthogonal_of_isometryEquiv_pi_splitHyperbolicPlane
    {m : ℕ}
    (e : Q.IsometryEquiv (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane K)) :
    ∃ U : Submodule K V, Q.IsTotallyIsotropic U ∧
      U = LinearMap.BilinForm.orthogonal Q.polarBilin U ∧ Module.finrank K U = m := by
  have : FiniteDimensional K V := Module.Finite.equiv e.symm.toLinearEquiv
  have hQ : Q.polarBilin.Nondegenerate :=
    e.nondegenerate_polarBilin_iff.mpr (nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
      TauCeti.nondegenerate_polarBilin_splitHyperbolicPlane)
  let g : (Fin m → K) →ₗ[K] (Fin m → Fin 2 → K) :=
    LinearMap.pi fun i ↦ (LinearMap.single K (fun _ : Fin 2 ↦ K) 0).comp (LinearMap.proj i)
  let h : (Fin m → K) →ₗ[K] V := e.symm.toLinearEquiv.toLinearMap ∘ₗ g
  have hh_inj : Function.Injective h := e.symm.injective.comp fun c₁ c₂ hc ↦
    funext fun i ↦ by simpa [g] using congrFun (congrFun hc i) 0
  let U : Submodule K V := LinearMap.range h
  have hU : Q.IsTotallyIsotropic U := isTotallyIsotropic_iff.mpr fun _ ⟨c, hc⟩ ↦ by
    rw [← hc]
    simp [h, g]
  have hdimV : Module.finrank K V = 2 * m := by
    have hpi : Module.finrank K (Fin m → Fin 2 → K) = 2 * m := by
      rw [Module.finrank_pi_fintype]
      simp [mul_comm]
    exact e.toLinearEquiv.finrank_eq.trans hpi
  have hdimU : Module.finrank K U = m := by
    simpa [Module.finrank_pi] using LinearMap.finrank_range_of_inj hh_inj
  exact ⟨U, hU, (hU.eq_orthogonal_polarBilin_iff_two_mul_finrank_eq hQ).mpr (by omega), hdimU⟩

end Field

section CharTwoRing

variable {R M : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]

/-- In characteristic two, the polar bilinear form of a scalar quadratic form is alternating. -/
theorem isAlt_polarBilin (Q : QuadraticForm R M) :
    LinearMap.BilinForm.IsAlt Q.polarBilin := by
  intro x
  rw [polarBilin_apply_apply, polar_self, two_nsmul, CharTwo.add_self_eq_zero]

/-- Over a commutative ring of characteristic two, `b : Basis (ι ⊕ ι) R M` has polar Gram matrix
`Matrix.J ι R` if and only if each half is polar-isotropic and the two halves are paired by the
Kronecker delta. -/
theorem toMatrix_polarBilin_eq_J_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 := by
  rw [← Matrix.ext_iff]
  refine ⟨fun h ↦ ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩, fun ⟨hll, hrr, hlr⟩ x y ↦ ?_⟩
  · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using h (Sum.inl i) (Sum.inl j)
  · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using h (Sum.inr i) (Sum.inr j)
  · have hij := h (Sum.inl i) (Sum.inr j)
    simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J, Matrix.one_apply, CharTwo.neg_eq] using hij
  · rcases x with i | i <;> rcases y with j | j
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hll i j
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J, Matrix.one_apply, CharTwo.neg_eq]
        using hlr i j
    · have hji := hlr j i
      rw [polar_comm] at hji
      simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J, Matrix.one_apply, eq_comm] using hji
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hrr i j

/-- Coordinate expansion of a characteristic-two quadratic form in a symplectic basis. -/
theorem apply_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (v : M) :
    Q v = ∑ i : ι, ((b.repr v (Sum.inl i)) ^ 2 * Q (b (Sum.inl i)) +
      (b.repr v (Sum.inr i)) ^ 2 * Q (b (Sum.inr i)) +
      b.repr v (Sum.inl i) * b.repr v (Sum.inr i)) := by
  obtain ⟨hll, hrr, hlr⟩ := (Q.toMatrix_polarBilin_eq_J_iff b).mp hb
  exact Q.apply_of_polar_eq b hll hrr hlr v

/-- Coordinate expansion of `Q (b.equivFun.symm c)` in a symplectic basis over a ring of
characteristic two. -/
theorem apply_equivFun_symm_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (c : ι ⊕ ι → R) :
    Q (b.equivFun.symm c) = ∑ i : ι, (c (Sum.inl i) ^ 2 * Q (b (Sum.inl i)) +
      c (Sum.inr i) ^ 2 * Q (b (Sum.inr i)) + c (Sum.inl i) * c (Sum.inr i)) := by
  have hc (x : ι ⊕ ι) : b.repr (b.equivFun.symm c) x = c x :=
    congrFun (b.equivFun.apply_symm_apply c) x
  rw [Q.apply_of_toMatrix_polarBilin_eq_J b hb]
  simp_rw [hc]

/-- In characteristic two, any symplectic basis `b : Basis (ι ⊕ ι) R M` gives an isometry from `Q`
to the orthogonal sum of the binary symplectic planes `symplecticPlane R (Q eᵢ) (Q fᵢ)`. -/
noncomputable def isometryEquivPiSymplecticPlaneOfToMatrixEqJ {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    Q.IsometryEquiv (QuadraticMap.pi fun i : ι ↦
      TauCeti.symplecticPlane R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))) :=
  Q.isometryEquivPiSymplecticPlane b
    ((Q.toMatrix_polarBilin_eq_J_iff b).mp hb).1
    ((Q.toMatrix_polarBilin_eq_J_iff b).mp hb).2.1
    ((Q.toMatrix_polarBilin_eq_J_iff b).mp hb).2.2

/-- Coordinate formula for `QuadraticMap.isometryEquivPiSymplecticPlaneOfToMatrixEqJ`. -/
@[simp]
theorem isometryEquivPiSymplecticPlaneOfToMatrixEqJ_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (Q : QuadraticForm R M) (b : Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (v : M) (i : ι) :
    Q.isometryEquivPiSymplecticPlaneOfToMatrixEqJ b hb v i =
      ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] :=
  (rfl)

end CharTwoRing

section CharTwoField

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
/-- Over a field of characteristic two, a quadratic space with nondegenerate polar form has even
`finrank` (automatically `0` when infinite-dimensional). -/
theorem even_finrank_of_nondegenerate_polarBilin (hQ : Q.polarBilin.Nondegenerate) :
    Even (Module.finrank K V) := by
  by_cases hfin : FiniteDimensional K V
  · exact Q.isAlt_polarBilin.even_finrank hQ
  · rw [Module.finrank_of_not_finite hfin]
    exact Even.zero

/-- Over a field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form admits a symplectic basis. -/
theorem exists_basis_toMatrix_polarBilin_eq_J (hQ : Q.polarBilin.Nondegenerate) :
    ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K :=
  Q.isAlt_polarBilin.exists_basis_toMatrix_eq_J hQ

/-- Over a field of characteristic two, a quadratic space of dimension `2 * m` with nondegenerate
polar form admits a symplectic basis indexed by `Fin m ⊕ Fin m`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq_two_mul {m : ℕ}
    (hQ : Q.polarBilin.Nondegenerate) (hm : Module.finrank K V = 2 * m) :
    ∃ b : Basis (Fin m ⊕ Fin m) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K := by
  obtain ⟨m', b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hdim : 2 * m' = 2 * m := by
    have hcard := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  obtain rfl : m' = m := by omega
  exact ⟨b, hb⟩

omit [CharP K 2] [FiniteDimensional K V] in
private theorem finiteDimensional_of_basis_eq_orthogonal {ι : Type*} [Finite ι]
    {B : LinearMap.BilinForm K V} {U : Submodule K V} (e : Basis ι K U)
    (horth : U = B.orthogonal U) :
    FiniteDimensional K V := by
  let φ : V →ₗ[K] Module.Dual K U := (B.domRestrict U).flip
  have hker : LinearMap.ker φ = U := le_antisymm
    (fun v hv ↦ horth.symm ▸ LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu ↦
      LinearMap.congr_fun hv ⟨u, hu⟩)
    (fun v hv ↦ LinearMap.ext fun ⟨u, hu⟩ ↦
      (LinearMap.BilinForm.mem_orthogonal_iff.mp (horth ▸ hv)) u hu)
  have : FiniteDimensional K U := Module.Finite.of_basis e
  have : FiniteDimensional K (LinearMap.ker φ) := hker.symm ▸ ‹FiniteDimensional K U›
  have : FiniteDimensional K (V ⧸ LinearMap.ker φ) :=
    Module.Finite.equiv φ.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker φ)

omit [FiniteDimensional K V] in
/-- Over a field of characteristic two, every finite basis of a `Q`-totally-isotropic
polar-Lagrangian subspace `U = LinearMap.BilinForm.orthogonal Q.polarBilin U` extends to a
symplectic basis all of whose basis vectors are `Q`-isotropic, with the prescribed vectors in the
`Sum.inl` positions. -/
theorem exists_basis_toMatrix_polarBilin_eq_J_inl_eq_and_apply_eq_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V} (e : Basis ι K U)
    (hU : Q.IsTotallyIsotropic U) (horth : U = LinearMap.BilinForm.orthogonal Q.polarBilin U) :
    ∃ b : Basis (ι ⊕ ι) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι K ∧
        (∀ i, b (Sum.inl i) = (e i : V)) ∧ ∀ x, Q (b x) = 0 := by
  have : FiniteDimensional K V := finiteDimensional_of_basis_eq_orthogonal e horth
  obtain ⟨b₀, hb₀, hinl⟩ := Q.isAlt_polarBilin.exists_basis_toMatrix_eq_J_inl_eq hQ e horth
  obtain ⟨hll, hrr, hlr⟩ := (Q.toMatrix_polarBilin_eq_J_iff b₀).mp hb₀
  have hQe (i : ι) : Q (b₀ (Sum.inl i)) = 0 := hinl i ▸ hU.apply_eq_zero (e i).2
  let f : ι → V := fun i ↦ b₀ (Sum.inr i) + Q (b₀ (Sum.inr i)) • b₀ (Sum.inl i)
  have hQf (i : ι) : Q (f i) = 0 := by
    simp [f, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQe, polar_comm Q (b₀ (Sum.inr i)),
      hlr, CharTwo.add_self_eq_zero]
  have hef (i j : ι) : polar Q (b₀ (Sum.inl i)) (f j) = if i = j then 1 else 0 := by
    simp [f, polar_add_right, polar_smul_right, hll, hlr]
  have hff (i j : ι) : polar Q (f i) (f j) = 0 := by
    simp only [f, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hll, hrr, hlr, polar_comm Q (b₀ (Sum.inr i)) (b₀ (Sum.inl j)), smul_eq_mul, zero_add]
    by_cases hij : i = j
    · subst hij; simp [CharTwo.add_self_eq_zero]
    · simp [hij, Ne.symm hij]
  let d : ι ⊕ ι → V := Sum.elim (fun i ↦ b₀ (Sum.inl i)) f
  have hd_apply (x y : ι ⊕ ι) : Q.polarBilin (d x) (d y) = Matrix.J ι K x y := by
    rcases x with i | i <;> rcases y with j | j
    · simpa [d, Matrix.J] using hll i j
    · simpa [d, Matrix.J, Matrix.one_apply, CharTwo.neg_eq] using hef i j
    · have hji := hef j i
      rw [polar_comm] at hji
      simpa [d, Matrix.J, Matrix.one_apply, eq_comm] using hji
    · simpa [d, Matrix.J] using hff i j
  have hd : (Matrix.of fun x y ↦ Q.polarBilin (d x) (d y)) = Matrix.J ι K := Matrix.ext hd_apply
  have hli : LinearIndependent K d :=
    LinearMap.BilinForm.linearIndependent_of_det_ne_zero Q.polarBilin
      (hd ▸ (Matrix.isUnit_det_J ι K).ne_zero)
  have hcard : Fintype.card (ι ⊕ ι) = Module.finrank K V := (Module.finrank_eq_card_basis b₀).symm
  let b := basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  have hb : ⇑b = d := coe_basisOfLinearIndependentOfCardEqFinrank' d hli hcard
  refine ⟨b, Matrix.ext fun x y ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · rw [LinearMap.BilinForm.toMatrix_apply, hb, hd_apply]
  · rw [hb]; exact hinl i
  · rw [hb]; exact x.casesOn hQe hQf

omit [FiniteDimensional K V] in
/-- Over any field of characteristic two, a quadratic space is equivalent to a finite orthogonal
sum of split hyperbolic planes if and only if it admits a finite symplectic basis of `Q`-isotropic
vectors. -/
theorem equivalent_pi_splitHyperbolicPlane_iff_exists_basis_apply_eq_zero :
    (∃ m : ℕ, Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane K)) ↔
      ∃ (m : ℕ) (b : Basis (Fin m ⊕ Fin m) K V),
        LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K ∧ ∀ x, Q (b x) = 0 := by
  refine ⟨fun ⟨m, ⟨e⟩⟩ ↦ ?_, fun ⟨m, b, hb, hbQ⟩ ↦ ⟨m, ?_⟩⟩
  · have : FiniteDimensional K V := Module.Finite.equiv e.symm.toLinearEquiv
    have hQ : Q.polarBilin.Nondegenerate :=
      e.nondegenerate_polarBilin_iff.mpr (nondegenerate_polarBilin_pi_iff.mpr fun _ ↦
        TauCeti.nondegenerate_polarBilin_splitHyperbolicPlane)
    obtain ⟨U, hU, horth, hdimU⟩ :=
      Q.exists_isTotallyIsotropic_and_eq_orthogonal_of_isometryEquiv_pi_splitHyperbolicPlane e
    obtain ⟨b, hb, -, hbQ⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J_inl_eq_and_apply_eq_zero hQ
      ((Module.finBasis K U).reindex (finCongr hdimU)) hU horth
    exact ⟨m, b, hb, hbQ⟩
  · refine ⟨(Q.isometryEquivPiSymplecticPlaneOfToMatrixEqJ b hb).trans
      (IsometryEquiv.pi fun i ↦ ?_)⟩
    rw [hbQ (Sum.inl i), hbQ (Sum.inr i), TauCeti.symplecticPlane_zero_zero]
    exact IsometryEquiv.refl _

/-- Over any field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form is equivalent to an orthogonal sum of split hyperbolic planes if and only if it admits a
`Q`-totally-isotropic polar-Lagrangian subspace. -/
theorem equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_eq_orthogonal
    (hQ : Q.polarBilin.Nondegenerate) :
    (∃ m : ℕ, Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane K)) ↔
      ∃ U : Submodule K V,
        Q.IsTotallyIsotropic U ∧ U = LinearMap.BilinForm.orthogonal Q.polarBilin U := by
  refine ⟨fun ⟨_, ⟨e⟩⟩ ↦ ?_, fun ⟨U, hU, horth⟩ ↦ ?_⟩
  · obtain ⟨U, hU, horth, -⟩ :=
      Q.exists_isTotallyIsotropic_and_eq_orthogonal_of_isometryEquiv_pi_splitHyperbolicPlane e
    exact ⟨U, hU, horth⟩
  · obtain ⟨b, hb, -, hbQ⟩ :=
      Q.exists_basis_toMatrix_polarBilin_eq_J_inl_eq_and_apply_eq_zero hQ (Module.finBasis K U)
        hU horth
    exact Q.equivalent_pi_splitHyperbolicPlane_iff_exists_basis_apply_eq_zero.mpr
      ⟨_, b, hb, hbQ⟩

/-- Over any field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form is equivalent to an orthogonal sum of split hyperbolic planes if and only if it admits a
`Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_two_mul_finrank_eq
    (hQ : Q.polarBilin.Nondegenerate) :
    (∃ m : ℕ, Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ TauCeti.splitHyperbolicPlane K)) ↔
      ∃ U : Submodule K V,
        Q.IsTotallyIsotropic U ∧ 2 * Module.finrank K U = Module.finrank K V := by
  rw [Q.equivalent_pi_splitHyperbolicPlane_iff_exists_isTotallyIsotropic_and_eq_orthogonal hQ]
  exact exists_congr fun U ↦ and_congr_right fun hU ↦
    hU.eq_orthogonal_polarBilin_iff_two_mul_finrank_eq hQ

end CharTwoField

end QuadraticMap
