/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.CharP.Two
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Quadratic forms in characteristic two and binary symplectic planes

Over a commutative ring of characteristic two, `2 • Q x = 0`, so the polar bilinear form of every
quadratic map is alternating (`QuadraticMap.isAlt_polarBilin`). When `Q` is a quadratic form on a
finite-dimensional vector space over a field of characteristic two whose polar form is
nondegenerate, `Q.polarBilin` is therefore a symplectic form: the underlying space has even
dimension and admits a symplectic basis in which the matrix of `Q.polarBilin` is `Matrix.J`, where
`-1 = 1` makes both off-diagonal blocks the identity.

In characteristic two, the diagonal submodule `{(m, m) | m ∈ M}` of `M × M` is totally isotropic
for `Q.prod Q`, and equals its own polar orthogonal complement whenever `Q.polarBilin` is
left-separating.

To decompose a quadratic space along a symplectic basis, this file introduces the binary quadratic
form `TauCeti.symplecticPlane a b` on `Fin 2 → R` given by `a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2`
(classically written `[a, b]`). Over any commutative ring, `[0, 0]` is isometric to
`QuadraticForm.dualProd R R`, and both `[a, 0]` and `[0, b]` are isometric to `[0, 0]`. In
characteristic two, the polar form of `[a, b]` is `x 0 * y 1 + x 1 * y 0` independently of `a` and
`b` and is always nondegenerate, two copies of `[1, 1]` are isometric to two copies of `[0, 0]`,
any basis in which `Q.polarBilin` has matrix `Matrix.J` decomposes `Q` as the orthogonal sum of
the planes `[Q (b (inl i)), Q (b (inr i))]`, and any pair `e, f` with `polar Q e f = 1` splits `Q`
as `[Q e, Q f]` orthogonal-summed with the restriction to `span {e, f} ^ ⊥`.

## Main definitions

* `TauCeti.symplecticPlane`: the binary quadratic form `x ↦ a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2`
  on `Fin 2 → R`.
* `TauCeti.isometryEquivSymplecticPlaneZeroZeroDualProd`: the isometry between
  `symplecticPlane 0 0` and `QuadraticForm.dualProd R R`.
* `TauCeti.isometryEquivSymplecticPlaneZeroRight` and
  `TauCeti.isometryEquivSymplecticPlaneZeroLeft`: the isometries from `symplecticPlane a 0` and
  `symplecticPlane 0 b` to `symplecticPlane 0 0` over any commutative ring.
* `TauCeti.isometryEquivSymplecticPlaneOneOneProd`: the characteristic-two isometry between
  `(symplecticPlane 0 0).prod (symplecticPlane 0 0)` and
  `(symplecticPlane 1 1).prod (symplecticPlane 1 1)`.
* `QuadraticMap.isometryEquivPiSymplecticPlane`: the orthogonal decomposition of a
  characteristic-two quadratic form along a symplectic basis of its polar form.
* `QuadraticMap.isometryEquivSymplecticPlaneRestrictSpanPair` and
  `QuadraticMap.isometryEquivSymplecticPlaneProdRestrictOrthogonal`: over a characteristic-two
  commutative ring, a pair `e, f` with `polar Q e f = 1` spans a copy of
  `symplecticPlane (Q e) (Q f)` and splits off orthogonally.

## Main results

* `QuadraticMap.isAlt_polarBilin`: in characteristic two, `Q.polarBilin` is alternating.
* `QuadraticMap.toMatrix_polarBilin_eq_J_iff`: in characteristic two, a basis gives `Q.polarBilin`
  the matrix `Matrix.J` exactly when each half is polar-isotropic and opposite halves pair by the
  Kronecker delta.
* `QuadraticMap.even_finrank_of_nondegenerate_polarBilin` and
  `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`: over a field of characteristic two, a
  finite-dimensional quadratic space with nondegenerate polar form has even dimension and a
  symplectic basis.
* `QuadraticMap.isTotallyIsotropic_range_id_prod_id_prod_self` and
  `QuadraticMap.orthogonal_range_id_prod_id_prod_self`: in characteristic two, the diagonal of
  `M × M` is totally isotropic for `Q.prod Q` and self-orthogonal when `Q.polarBilin` is
  left-separating.
* `TauCeti.nondegenerate_polarBilin_symplecticPlane` and `TauCeti.nondegenerate_symplecticPlane`:
  in characteristic two, `symplecticPlane a b` has nondegenerate polar form and is nondegenerate.
* `TauCeti.orthogonal_polarBilin_symplecticPlane_span_one_zero` and
  `TauCeti.orthogonal_polarBilin_symplecticPlane_span_zero_one`: in characteristic two, each
  coordinate axis of `Fin 2 → R` equals its own `(symplecticPlane a b).polarBilin`-orthogonal
  complement.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. 183 (1941), 148–167.
* R. Elman, N. Karpenko, A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*
  (2008), Chapter II, §7.
-/

public section

open QuadraticMap

namespace QuadraticMap

section CharTwoSemiring

variable {R M P : Type*} [CommSemiring R] [CharP R 2] [AddCommMonoid M] [Module R M]
  [AddCommMonoid P] [Module R P]

/-- In characteristic two, the diagonal submodule `{(m, m) | m ∈ M}` is totally isotropic for
`Q.prod Q`. -/
theorem isTotallyIsotropic_range_id_prod_id_prod_self (Q : QuadraticMap R M P) :
    (Q.prod Q).IsTotallyIsotropic (LinearMap.range (LinearMap.id.prod LinearMap.id)) := by
  rw [isTotallyIsotropic_iff]
  rintro _ ⟨m, rfl⟩
  simp only [LinearMap.prod_apply, Function.prod, LinearMap.id_apply, QuadraticMap.prod_apply]
  exact TauCeti.add_self_eq_zero_of_charTwo R (Q m)

end CharTwoSemiring

section CharTwoMap

variable {R M P : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- In characteristic two, the polar form of any quadratic map vanishes on the diagonal. -/
@[simp high]
theorem polar_self_of_charTwo (Q : QuadraticMap R M P) (x : M) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, TauCeti.add_self_eq_zero_of_charTwo R]

/-- In characteristic two, the polar bilinear map of any quadratic map is alternating. -/
theorem isAlt_polarBilin (Q : QuadraticMap R M P) : Q.polarBilin.IsAlt := fun x => by
  rw [polarBilin_apply_apply, polar_self_of_charTwo]

end CharTwoMap

section CharTwoRing

variable {R M : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]

/-- In characteristic two, the matrix of `Q.polarBilin` in a basis `b` indexed by `ι ⊕ ι` is
`Matrix.J ι R` if and only if each half is polar-isotropic and `b (inl i)` pairs with `b (inr j)`
by the Kronecker delta. Because `-1 = 1` in `R`, both off-diagonal blocks of `Matrix.J` are the
identity matrix. -/
theorem toMatrix_polarBilin_eq_J_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Module.Basis (ι ⊕ ι) R M) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0) ∧
      (∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0) ∧
      (∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) := by
  constructor
  · intro hb
    have hentry (x y : ι ⊕ ι) : polar Q (b x) (b y) = Matrix.J ι R x y := by
      simpa [LinearMap.BilinForm.toMatrix_apply] using congrFun₂ hb x y
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.J, Matrix.fromBlocks] using hentry (.inl i) (.inl j)
    · simpa [Matrix.J, Matrix.fromBlocks] using hentry (.inr i) (.inr j)
    · rw [polar_comm, hentry (.inr j) (.inl i)]
      simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, eq_comm]
  · rintro ⟨hll, hrr, hlr⟩
    ext x y
    rw [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply]
    rcases x with i | i <;> rcases y with j | j
    · simp [Matrix.J, Matrix.fromBlocks, hll i j]
    · simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, hlr i j, CharTwo.neg_eq]
    · rw [polar_comm, hlr j i]
      simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, eq_comm]
    · simp [Matrix.J, Matrix.fromBlocks, hrr i j]

/-- In characteristic two, when `Q.polarBilin` is left-separating, the diagonal submodule
`{(m, m) | m ∈ M}` is equal to its own `(Q.prod Q).polarBilin`-orthogonal complement. -/
theorem orthogonal_range_id_prod_id_prod_self {Q : QuadraticForm R M}
    (hQ : Q.polarBilin.SeparatingLeft) :
    LinearMap.BilinForm.orthogonal (Q.prod Q).polarBilin
      (LinearMap.range (LinearMap.id.prod LinearMap.id)) =
      LinearMap.range (LinearMap.id.prod LinearMap.id) := by
  ext ⟨x, y⟩
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_range, LinearMap.prod_apply,
    Function.prod, LinearMap.id_apply, Prod.mk.injEq, forall_exists_index,
    polarBilin_prod, LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, polarBilin_apply_apply]
  constructor
  · intro h
    have hsum : x + y = 0 := hQ (x + y) fun m => by
      have hm := h (m, m) m rfl
      rwa [polarBilin_apply_apply, polar_add_left, polar_comm Q x m, polar_comm Q y m]
    exact ⟨y, ((TauCeti.add_eq_zero_iff_eq_of_charTwo R).mp hsum).symm, rfl⟩
  · rintro ⟨m, rfl, rfl⟩ _ n rfl
    exact CharTwo.add_self_eq_zero _

end CharTwoRing

section CharTwoField

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Over a field of characteristic two, a finite-dimensional quadratic space whose polar bilinear
form is nondegenerate has even dimension. -/
theorem even_finrank_of_nondegenerate_polarBilin (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : Even (Module.finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank Q.isAlt_polarBilin hQ

/-- Over a field of characteristic two, a finite-dimensional quadratic space whose polar bilinear
form is nondegenerate admits a symplectic basis in which `Q.polarBilin` has matrix `Matrix.J`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    ∃ m : ℕ, 2 * m = Module.finrank K V ∧
      ∃ b : Module.Basis (Fin m ⊕ Fin m) K V,
        LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K := by
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J Q.isAlt_polarBilin hQ
  refine ⟨m, ?_, b, hb⟩
  simpa [two_mul] using (Module.finrank_eq_card_basis b).symm

end CharTwoField

end QuadraticMap

namespace TauCeti

universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- The binary quadratic form `x ↦ a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2` on `Fin 2 → R`,
classically denoted `[a, b]`. It is the coordinate expression of a quadratic form on a plane
spanned by two vectors of norms `a` and `b` with polar pairing `1`. -/
def symplecticPlane (a b : R) : QuadraticForm R (Fin 2 → R) :=
  a • QuadraticMap.proj 0 0 + QuadraticMap.proj 0 1 + b • QuadraticMap.proj 1 1

/-- Evaluation of `TauCeti.symplecticPlane` in coordinates. -/
@[simp]
theorem symplecticPlane_apply (a b : R) (x : Fin 2 → R) :
    symplecticPlane a b x = a * x 0 ^ 2 + x 0 * x 1 + b * x 1 ^ 2 := by
  simp [symplecticPlane, pow_two]

/-- The split binary plane `symplecticPlane 0 0` (`x ↦ x 0 * x 1`) is isometric to
`QuadraticForm.dualProd R R`. -/
def isometryEquivSymplecticPlaneZeroZeroDualProd :
    (symplecticPlane (0 : R) 0).IsometryEquiv (QuadraticForm.dualProd R R) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    ((LinearMap.ringLmapEquivSelf R R R).symm.prodCongr (.refl R R))
  map_app' x := by simp [mul_comm]

/-- The forward map of `TauCeti.isometryEquivSymplecticPlaneZeroZeroDualProd`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroZeroDualProd_apply (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneZeroZeroDualProd x = (x 0 • LinearMap.id, x 1) := by
  rw [← IsometryEquiv.coe_toLinearEquiv]
  refine Prod.ext (LinearMap.ext fun r ↦ ?_) rfl
  simp [isometryEquivSymplecticPlaneZeroZeroDualProd, mul_comm]

/-- The inverse map of `TauCeti.isometryEquivSymplecticPlaneZeroZeroDualProd`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroZeroDualProd_symm_apply (p : Module.Dual R R × R) :
    isometryEquivSymplecticPlaneZeroZeroDualProd.symm p = ![p.1 1, p.2] := by
  rw [IsometryEquiv.symm_apply_eq]
  refine Prod.ext (LinearMap.ext fun r ↦ ?_) (by simp)
  simpa [mul_comm] using p.1.map_smul r 1

/-- The first coordinate axis `R ∙ ![1, 0]` is totally isotropic for `symplecticPlane 0 b`. -/
theorem isTotallyIsotropic_span_symplecticPlane_zero_left (b : R) :
    (symplecticPlane (0 : R) b).IsTotallyIsotropic (R ∙ ![(1 : R), 0]) := by
  rw [isTotallyIsotropic_span_singleton_iff]
  simp

/-- The second coordinate axis `R ∙ ![0, 1]` is totally isotropic for `symplecticPlane a 0`. -/
theorem isTotallyIsotropic_span_symplecticPlane_zero_right (a : R) :
    (symplecticPlane a (0 : R)).IsTotallyIsotropic (R ∙ ![(0 : R), 1]) := by
  rw [isTotallyIsotropic_span_singleton_iff]
  simp

/-- In a finite product of planes `symplecticPlane 0 (b i)`, the product of the first coordinate
axes `R ∙ ![1, 0]` is totally isotropic. -/
theorem isTotallyIsotropic_pi_symplecticPlane_zero_left {ι : Type*} [Fintype ι] (b : ι → R) :
    (QuadraticMap.pi fun i ↦ symplecticPlane (0 : R) (b i)).IsTotallyIsotropic
      (Submodule.pi Set.univ fun _ : ι ↦ R ∙ ![(1 : R), 0]) := by
  rw [isTotallyIsotropic_iff]
  intro x hx
  rw [QuadraticMap.pi_apply]
  exact Finset.sum_eq_zero fun i _ ↦
    isTotallyIsotropic_iff.mp (isTotallyIsotropic_span_symplecticPlane_zero_left (b i))
      (x i) (hx i trivial)

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- Polarization of `TauCeti.symplecticPlane` over a commutative ring. -/
theorem polar_symplecticPlane (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane a b) x y =
      2 * a * (x 0 * y 0) + (x 0 * y 1 + x 1 * y 0) + 2 * b * (x 1 * y 1) := by
  simp only [polar, symplecticPlane_apply, Pi.add_apply]
  ring

/-- Over any commutative ring, the plane `symplecticPlane a 0` (`a * x 0 ^ 2 + x 0 * x 1`) is
isometric to `symplecticPlane 0 0` (`x 0 * x 1`) via `(x 0, x 1) ↦ (x 0, a * x 0 + x 1)`. -/
def isometryEquivSymplecticPlaneZeroRight (a : R) :
    (symplecticPlane a 0).IsometryEquiv (symplecticPlane 0 0) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    (((LinearEquiv.refl R R).skewProd (.refl R R) (a • LinearMap.id)).trans
      (LinearEquiv.finTwoArrow R R).symm)
  map_app' x := by
    simp
    ring

/-- Evaluation of `TauCeti.isometryEquivSymplecticPlaneZeroRight`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroRight_apply (a : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneZeroRight a x = ![x 0, a * x 0 + x 1] := by
  rw [← IsometryEquiv.coe_toLinearEquiv]
  ext i
  fin_cases i <;> simp [isometryEquivSymplecticPlaneZeroRight, add_comm]

/-- Evaluation of the inverse of `TauCeti.isometryEquivSymplecticPlaneZeroRight`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroRight_symm_apply (a : R) (y : Fin 2 → R) :
    (isometryEquivSymplecticPlaneZeroRight a).symm y = ![y 0, y 1 - a * y 0] := by
  rw [IsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i <;> simp

/-- Over any commutative ring, the plane `symplecticPlane 0 b` (`x 0 * x 1 + b * x 1 ^ 2`) is
isometric to `symplecticPlane 0 0` (`x 0 * x 1`) via `(x 0, x 1) ↦ (x 0 + b * x 1, x 1)`. -/
def isometryEquivSymplecticPlaneZeroLeft (b : R) :
    (symplecticPlane 0 b).IsometryEquiv (symplecticPlane 0 0) where
  toLinearEquiv := (LinearEquiv.finTwoArrow R R).trans
    ((LinearEquiv.prodComm R R R).trans
      (((LinearEquiv.refl R R).skewProd (.refl R R) (b • LinearMap.id)).trans
        ((LinearEquiv.prodComm R R R).trans (LinearEquiv.finTwoArrow R R).symm)))
  map_app' x := by
    simp
    ring

/-- Evaluation of `TauCeti.isometryEquivSymplecticPlaneZeroLeft`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroLeft_apply (b : R) (x : Fin 2 → R) :
    isometryEquivSymplecticPlaneZeroLeft b x = ![x 0 + b * x 1, x 1] := by
  rw [← IsometryEquiv.coe_toLinearEquiv]
  ext i
  fin_cases i <;> simp [isometryEquivSymplecticPlaneZeroLeft]

/-- Evaluation of the inverse of `TauCeti.isometryEquivSymplecticPlaneZeroLeft`. -/
@[simp]
theorem isometryEquivSymplecticPlaneZeroLeft_symm_apply (b : R) (y : Fin 2 → R) :
    (isometryEquivSymplecticPlaneZeroLeft b).symm y = ![y 0 - b * y 1, y 1] := by
  rw [IsometryEquiv.symm_apply_eq]
  ext i
  fin_cases i <;> simp

end CommRing

section CharTwo

variable {R : Type u} [CommRing R] [CharP R 2]

/-- In characteristic two, the polar form of `symplecticPlane a b` is `x 0 * y 1 + x 1 * y 0`,
independently of `a` and `b`. -/
@[simp]
theorem polar_symplecticPlane_of_charTwo (a b : R) (x y : Fin 2 → R) :
    polar (symplecticPlane a b) x y = x 0 * y 1 + x 1 * y 0 := by
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  rw [polar_symplecticPlane]
  linear_combination (a * (x 0 * y 0) + b * (x 1 * y 1)) * h2

/-- In characteristic two, the polar bilinear form of `symplecticPlane a b` is nondegenerate. -/
@[simp]
theorem nondegenerate_polarBilin_symplecticPlane (a b : R) :
    (symplecticPlane a b).polarBilin.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (symplecticPlane a b).isSymm_polarBilin.isRefl).mpr fun x hx => ?_
  have h0 : x 0 = 0 := by simpa using hx ![0, 1]
  have h1 : x 1 = 0 := by simpa using hx ![1, 0]
  ext i
  fin_cases i <;> simp [h0, h1]

/-- In characteristic two, `symplecticPlane a b` is nondegenerate as a quadratic form. -/
@[simp]
theorem nondegenerate_symplecticPlane (a b : R) : (symplecticPlane a b).Nondegenerate :=
  QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
    (LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (nondegenerate_polarBilin_symplecticPlane a b).1)

/-- In characteristic two, the first coordinate axis `R ∙ ![1, 0]` is equal to its own
`(symplecticPlane a b).polarBilin`-orthogonal complement. -/
theorem orthogonal_polarBilin_symplecticPlane_span_one_zero (a b : R) :
    LinearMap.BilinForm.orthogonal (symplecticPlane a b).polarBilin (R ∙ ![(1 : R), 0]) =
      R ∙ ![(1 : R), 0] := by
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_span_singleton,
    forall_exists_index, forall_apply_eq_imp_iff, polarBilin_apply_apply,
    polar_symplecticPlane_of_charTwo]
  constructor
  · intro hx
    refine ⟨x 0, ?_⟩
    have h1 : x 1 = 0 := by simpa using hx 1
    ext i
    fin_cases i <;> simp [h1]
  · rintro ⟨c, rfl⟩ d
    simp

/-- In characteristic two, the second coordinate axis `R ∙ ![0, 1]` is equal to its own
`(symplecticPlane a b).polarBilin`-orthogonal complement. -/
theorem orthogonal_polarBilin_symplecticPlane_span_zero_one (a b : R) :
    LinearMap.BilinForm.orthogonal (symplecticPlane a b).polarBilin (R ∙ ![(0 : R), 1]) =
      R ∙ ![(0 : R), 1] := by
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_span_singleton,
    forall_exists_index, forall_apply_eq_imp_iff, polarBilin_apply_apply,
    polar_symplecticPlane_of_charTwo]
  constructor
  · intro hx
    refine ⟨x 1, ?_⟩
    have h0 : x 0 = 0 := by simpa using hx 1
    ext i
    fin_cases i <;> simp [h0]
  · rintro ⟨c, rfl⟩ d
    simp

/-- In characteristic two, the product of the first coordinate axes `R ∙ ![1, 0]` is equal to its
own polar-orthogonal complement in a finite product of planes `symplecticPlane (a i) (b i)`. -/
theorem orthogonal_polarBilin_pi_symplecticPlane_span_one_zero {ι : Type*} [Fintype ι]
    (a b : ι → R) :
    LinearMap.BilinForm.orthogonal
      (QuadraticMap.pi fun i ↦ symplecticPlane (a i) (b i)).polarBilin
      (Submodule.pi Set.univ fun _ : ι ↦ R ∙ ![(1 : R), 0]) =
      Submodule.pi Set.univ fun _ : ι ↦ R ∙ ![(1 : R), 0] := by
  classical
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_pi, Set.mem_univ,
    forall_true_left, polarBilin_apply_apply, QuadraticMap.Ring.polar_pi]
  constructor
  · intro hx i
    rw [← orthogonal_polarBilin_symplecticPlane_span_one_zero (a i) (b i),
      LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have hsingle (j : ι) : (Pi.single i v : ι → Fin 2 → R) j ∈ R ∙ ![(1 : R), 0] := by
      rcases eq_or_ne j i with rfl | hne
      · simpa using hv
      · simp [hne]
    have hsum := hx (Pi.single i v) hsingle
    rw [Finset.sum_eq_single i] at hsum
    · simpa [polarBilin_apply_apply] using hsum
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  · intro hx y hy
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have hxi := hx i
    rw [← orthogonal_polarBilin_symplecticPlane_span_one_zero (a i) (b i),
      LinearMap.BilinForm.mem_orthogonal_iff] at hxi
    simpa [polarBilin_apply_apply] using hxi (y i) (hy i)

/-- In characteristic two, the orthogonal sum of two split planes `symplecticPlane 0 0` is
isometric to the orthogonal sum of two `[1, 1]` planes `symplecticPlane 1 1`. -/
def isometryEquivSymplecticPlaneOneOneProd :
    ((symplecticPlane (0 : R) 0).prod (symplecticPlane 0 0)).IsometryEquiv
      ((symplecticPlane 1 1).prod (symplecticPlane 1 1)) where
  toFun p := (![p.1 0 + p.2 0 + p.2 1, p.1 1 + p.2 0 + p.2 1],
    ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1])
  invFun q := (![q.1 0 + q.2 1, q.1 1 + q.2 1],
    ![q.1 0 + q.1 1 + q.2 0 + q.2 1, q.1 0 + q.1 1 + q.2 0])
  map_add' p q := by
    refine Prod.ext ?_ ?_ <;> · ext i; fin_cases i <;> · simp; ring
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> · ext i; fin_cases i <;> · simp; ring
  left_inv p := by
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination (p.2 0 + p.2 1) * h2
    · linear_combination (p.2 0 + p.2 1) * h2
    · linear_combination (p.1 0 + p.1 1 + p.2 0 + 2 * p.2 1) * h2
    · linear_combination (p.1 0 + p.1 1 + p.2 0 + p.2 1) * h2
  right_inv q := by
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
    refine Prod.ext ?_ ?_ <;> ext i <;> fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one]
    · linear_combination (q.1 0 + q.1 1 + q.2 0 + q.2 1) * h2
    · linear_combination (q.1 0 + q.1 1 + q.2 0 + q.2 1) * h2
    · linear_combination (q.1 0 + q.1 1 + q.2 1) * h2
    · linear_combination (q.1 0 + q.1 1 + q.2 0) * h2
  map_app' p := by
    have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
    simp only [QuadraticMap.prod_apply, symplecticPlane_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination
      (p.1 0 ^ 2 + p.1 1 ^ 2 + 2 * p.2 0 ^ 2 + 3 * p.2 1 ^ 2 + p.1 0 * p.1 1 +
        2 * p.1 0 * p.2 0 + 3 * p.1 0 * p.2 1 + 2 * p.1 1 * p.2 0 +
        3 * p.1 1 * p.2 1 + 4 * p.2 0 * p.2 1) * h2

/-- Evaluation of `TauCeti.isometryEquivSymplecticPlaneOneOneProd`. -/
@[simp]
theorem isometryEquivSymplecticPlaneOneOneProd_apply (p : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivSymplecticPlaneOneOneProd p =
      (![p.1 0 + p.2 0 + p.2 1, p.1 1 + p.2 0 + p.2 1],
       ![p.1 0 + p.1 1 + p.2 1, p.2 0 + p.2 1]) :=
  (rfl)

/-- Evaluation of the inverse of `TauCeti.isometryEquivSymplecticPlaneOneOneProd`. -/
@[simp]
theorem isometryEquivSymplecticPlaneOneOneProd_symm_apply (q : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivSymplecticPlaneOneOneProd.symm q =
      (![q.1 0 + q.2 1, q.1 1 + q.2 1],
       ![q.1 0 + q.1 1 + q.2 0 + q.2 1, q.1 0 + q.1 1 + q.2 0]) :=
  (rfl)

end CharTwo

end TauCeti

namespace QuadraticMap

section SymplecticDecomposition

open TauCeti

universe u v

variable {R : Type u} [CommRing R] [CharP R 2] {M : Type v} [AddCommGroup M] [Module R M]

omit [CharP R 2] in
private theorem equivFun_symm_piFinTwoEquivSumArrow {ι : Type*} [Fintype ι]
    (b : Module.Basis (ι ⊕ ι) R M) (x : ι → Fin 2 → R) :
    b.equivFun.symm (LinearEquiv.piFinTwoEquivSumArrow R ι R x) =
      ∑ i : ι, (x i 0 • b (.inl i) + x i 1 • b (.inr i)) := by
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib,
    LinearEquiv.piFinTwoEquivSumArrow_apply]
  rfl

/-- In characteristic two, any basis `b : Basis (ι ⊕ ι) R M` in which `Q.polarBilin` has matrix
`Matrix.J ι R` gives an isometry from the orthogonal sum of the binary planes
`symplecticPlane (Q (b (inl i))) (Q (b (inr i)))` to `Q`. -/
noncomputable def isometryEquivPiSymplecticPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    (QuadraticMap.pi fun i : ι =>
      symplecticPlane (Q (b (.inl i))) (Q (b (.inr i)))).IsometryEquiv Q where
  toLinearEquiv := (LinearEquiv.piFinTwoEquivSumArrow R ι R).trans b.equivFun.symm
  map_app' x := by
    obtain ⟨hll, hrr, hlr⟩ := (Q.toMatrix_polarBilin_eq_J_iff b).mp hb
    simp only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply]
    rw [equivFun_symm_piFinTwoEquivSumArrow, Q.map_sum]
    have horth : ∑ ij ∈ (Finset.univ : Finset ι).sym2 with ¬ij.IsDiag,
        polarSym2 Q (ij.map fun i => x i 0 • b (.inl i) + x i 1 • b (.inr i)) = 0 := by
      refine Finset.sum_eq_zero fun ij hij => ?_
      rcases ij with ⟨i, j⟩
      have hij_ne : i ≠ j := by
        simpa [Finset.mem_filter, Sym2.mk_isDiag_iff] using hij
      simp [polarSym2, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
        hll, hrr, hlr, polar_comm Q (b (.inr i)) (b (.inl j)), hij_ne, hij_ne.symm]
    rw [horth, add_zero, pi_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QuadraticMap.map_add Q, Q.map_smul, Q.map_smul, polar_smul_left, polar_smul_right,
      hlr i i]
    simp only [↓reduceIte, symplecticPlane_apply, smul_eq_mul, pow_two]
    ring

/-- The linear equivalence underlying `QuadraticMap.isometryEquivPiSymplecticPlane`. -/
@[simp]
theorem toLinearEquiv_isometryEquivPiSymplecticPlane {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    (Q.isometryEquivPiSymplecticPlane b hb).toLinearEquiv =
      (LinearEquiv.piFinTwoEquivSumArrow R ι R).trans b.equivFun.symm :=
  (rfl)

/-- Evaluation of `QuadraticMap.isometryEquivPiSymplecticPlane` on a family of binary vectors. -/
@[simp]
theorem isometryEquivPiSymplecticPlane_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (x : ι → Fin 2 → R) :
    Q.isometryEquivPiSymplecticPlane b hb x =
      ∑ i : ι, (x i 0 • b (.inl i) + x i 1 • b (.inr i)) := by
  rw [← IsometryEquiv.coe_toLinearEquiv, toLinearEquiv_isometryEquivPiSymplecticPlane,
    LinearEquiv.trans_apply, equivFun_symm_piFinTwoEquivSumArrow]

/-- Coordinate evaluation of the inverse of `QuadraticMap.isometryEquivPiSymplecticPlane`. -/
@[simp]
theorem isometryEquivPiSymplecticPlane_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R M) (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (m : M) (i : ι) :
    (Q.isometryEquivPiSymplecticPlane b hb).symm m i = ![b.repr m (.inl i), b.repr m (.inr i)] := by
  rw [← IsometryEquiv.coe_toLinearEquiv (f := (Q.isometryEquivPiSymplecticPlane b hb).symm),
    ← IsometryEquiv.coe_symm_toLinearEquiv, toLinearEquiv_isometryEquivPiSymplecticPlane]
  simp

/-- Subtracting the symplectic-pair projection from `v` lands in the polar-orthogonal complement of
`span R {e, f}`. -/
theorem sub_polar_smul_mem_orthogonal_span_pair (Q : QuadraticForm R M) {e f : M}
    (hef : polar Q e f = 1) (v : M) :
    v - polar Q v f • e - polar Q e v • f ∈
      LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span R {e, f}) := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rcases Submodule.mem_span_pair.mp hw with ⟨a, b, rfl⟩
  have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
  have hfv : polar Q f v = polar Q v f := polar_comm Q f v
  simp only [map_add, map_smul, map_sub, LinearMap.add_apply, LinearMap.smul_apply,
    polarBilin_apply_apply, polar_self_of_charTwo, hef, hfe, hfv, smul_eq_mul, mul_zero, add_zero,
    zero_add]
  ring

/-- Over a commutative ring of characteristic two, two vectors `e, f` with `polar Q e f = 1` span a
plane on which `Q` restricts isometrically to `symplecticPlane (Q e) (Q f)`. -/
noncomputable def isometryEquivSymplecticPlaneRestrictSpanPair (Q : QuadraticForm R M) {e f : M}
    (hef : polar Q e f = 1) :
    (symplecticPlane (Q e) (Q f)).IsometryEquiv (Q.restrict (Submodule.span R {e, f})) := by
  have hfe : Q.polarBilin f e = 1 := by
    rw [polarBilin_apply_apply, polar_comm, hef]
  have hli : LinearIndependent R ![e, f] :=
    LinearMap.BilinForm.IsAlt.linearIndependent_pair_of_apply_eq_one Q.isAlt_polarBilin hfe
  have hrange : Set.range ![e, f] = {e, f} := by
    ext v
    simp [eq_comm, or_comm]
  let b : Module.Basis (Fin 2) R (Submodule.span R {e, f}) :=
    (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (congrArg (Submodule.span R) hrange))
  refine
    { toLinearEquiv := b.equivFun.symm
      map_app' := fun x => ?_ }
  have hb0 : (b 0 : M) = e := by simp [b]
  have hb1 : (b 1 : M) = f := by simp [b]
  simp only [QuadraticMap.restrict_apply, LinearMap.toFun_eq_coe, LinearEquiv.coe_coe]
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_smul, hb0, hb1, QuadraticMap.map_add Q, Q.map_smul, Q.map_smul, polar_smul_left,
    polar_smul_right, hef]
  simp only [symplecticPlane_apply, smul_eq_mul, pow_two]
  ring

/-- Evaluation of `QuadraticMap.isometryEquivSymplecticPlaneRestrictSpanPair` in the ambient
module. -/
@[simp]
theorem coe_isometryEquivSymplecticPlaneRestrictSpanPair_apply (Q : QuadraticForm R M) {e f : M}
    (hef : polar Q e f = 1) (x : Fin 2 → R) :
    (Q.isometryEquivSymplecticPlaneRestrictSpanPair hef x : M) = x 0 • e + x 1 • f := by
  rw [← IsometryEquiv.coe_toLinearEquiv]
  simp [isometryEquivSymplecticPlaneRestrictSpanPair, Module.Basis.equivFun_symm_apply,
    Fin.sum_univ_two]

/-- Evaluation of the inverse of `QuadraticMap.isometryEquivSymplecticPlaneRestrictSpanPair`. -/
@[simp]
theorem isometryEquivSymplecticPlaneRestrictSpanPair_symm_apply (Q : QuadraticForm R M) {e f : M}
    (hef : polar Q e f = 1) (w : Submodule.span R {e, f}) :
    (Q.isometryEquivSymplecticPlaneRestrictSpanPair hef).symm w =
      ![polar Q w f, polar Q e w] := by
  rw [IsometryEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [coe_isometryEquivSymplecticPlaneRestrictSpanPair_apply]
  have hfe : Q.polarBilin f e = 1 := by rw [polarBilin_apply_apply, polar_comm, hef]
  have hcompl := LinearMap.BilinForm.IsAlt.isCompl_span_pair_orthogonal Q.isAlt_polarBilin hfe
  have hmem_span : (w : M) - polar Q w f • e - polar Q e w • f ∈ Submodule.span R {e, f} :=
    sub_mem (sub_mem w.2 (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hzero : (w : M) - polar Q w f • e - polar Q e w • f = 0 := by
    rw [← Submodule.mem_bot R, ← hcompl.inf_eq_bot]
    exact ⟨hmem_span, Q.sub_polar_smul_mem_orthogonal_span_pair hef w⟩
  rw [sub_sub] at hzero
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact sub_eq_zero.mp hzero

/-- Over a commutative ring of characteristic two, two vectors `e, f` with `polar Q e f = 1` split
`Q` as the orthogonal sum of `symplecticPlane (Q e) (Q f)` and the restriction of `Q` to the polar
orthogonal complement of `span R {e, f}`. -/
noncomputable def isometryEquivSymplecticPlaneProdRestrictOrthogonal (Q : QuadraticForm R M)
    {e f : M} (hef : polar Q e f = 1) :
    ((symplecticPlane (Q e) (Q f)).prod
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin
        (Submodule.span R {e, f})))).IsometryEquiv Q := by
  have hfe : Q.polarBilin f e = 1 := by
    rw [polarBilin_apply_apply, polar_comm, hef]
  exact ((Q.isometryEquivSymplecticPlaneRestrictSpanPair hef).prod (IsometryEquiv.refl _)).trans
    (IsometryEquiv.prodRestrictOrthogonal Q (Submodule.span R {e, f})
      (LinearMap.BilinForm.IsAlt.isCompl_span_pair_orthogonal Q.isAlt_polarBilin hfe))

/-- Evaluation of `QuadraticMap.isometryEquivSymplecticPlaneProdRestrictOrthogonal`. -/
@[simp]
theorem isometryEquivSymplecticPlaneProdRestrictOrthogonal_apply (Q : QuadraticForm R M)
    {e f : M} (hef : polar Q e f = 1)
    (p : (Fin 2 → R) × LinearMap.BilinForm.orthogonal Q.polarBilin (Submodule.span R {e, f})) :
    Q.isometryEquivSymplecticPlaneProdRestrictOrthogonal hef p =
      p.1 0 • e + p.1 1 • f + p.2 := by
  simp [isometryEquivSymplecticPlaneProdRestrictOrthogonal]

/-- Evaluation of the inverse of
`QuadraticMap.isometryEquivSymplecticPlaneProdRestrictOrthogonal`. -/
@[simp]
theorem isometryEquivSymplecticPlaneProdRestrictOrthogonal_symm_apply (Q : QuadraticForm R M)
    {e f : M} (hef : polar Q e f = 1) (v : M) :
    (Q.isometryEquivSymplecticPlaneProdRestrictOrthogonal hef).symm v =
      (![polar Q v f, polar Q e v],
       ⟨v - polar Q v f • e - polar Q e v • f,
        Q.sub_polar_smul_mem_orthogonal_span_pair hef v⟩) := by
  rw [IsometryEquiv.symm_apply_eq, isometryEquivSymplecticPlaneProdRestrictOrthogonal_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  abel

end SymplecticDecomposition

end QuadraticMap
