/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.QuadraticForm.Dual
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# The Arf invariant, Gauss sum, and zero counts of quadratic forms over `𝔽₂`

In characteristic two, a quadratic form `Q` is strictly finer than its polar bilinear form
`Q.polarBilin`: `QuadraticMap.polar_self` forces `polar Q x x = 2 • Q x = 0`, so `Q.polarBilin` is
alternating (`QuadraticMap.isAlt_polarBilin`) and cannot recover the diagonal values `Q x`. When
`Q.polarBilin` is nondegenerate on a finite-dimensional vector space `V` over a field `K` of
characteristic two, `V` has even dimension `2 * m` and admits a symplectic basis `b` indexed by
`Fin m ⊕ Fin m` in which the Gram matrix of `Q.polarBilin` is `Matrix.J (Fin m) K` (since `-1 = 1`
in characteristic two, each pair `(b (inl i), b (inr i))` has polar value `1` while all other pairs
are orthogonal).

Over `𝔽₂` (`ZMod 2`), Cahit Arf (1941) showed that the scalar
$$\operatorname{Arf}(Q) = \sum_{i = 1}^m Q(a_i)\, Q(b_i) \in \mathbb{F}_2$$
is independent of the choice of symplectic basis `(a_i, b_i)`. Following Pyronneau (§2.1) and
Browder (§III.1), basis independence and the zero-counting formulas flow simultaneously from the
integer Gauss sum
$$\sum_{v \in V} (-1)^{(Q\, v).\mathrm{val}} = (-1)^{(\operatorname{Arf} Q).\mathrm{val}} 2^m.$$
Expanding a vector along a symplectic basis factors the left-hand side into `m` planar four-term
sums, each equal to `(-1) ^ (Q a_i * Q b_i).val * 2`. Since `2 ^ m ≠ 0` in `ℤ` and
`c ↦ (-1) ^ c.val` is injective on `ZMod 2`, the sum `∑ i, Q (a_i) * Q (b_i)` depends only on `Q`
and not on the symplectic basis. Combining the Gauss sum with `#V = 2 ^ (2 * m)` yields the exact
count of isotropic vectors (`Q v = 0`): `2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)` when
`m ≥ 1`, and `1` when `m = 0`.

Model planes, plane decomposition, Arf's classification theorem, and the totally isotropic
Lagrangian criteria for `Q.arf = 0` are proved in
`TauCeti.LinearAlgebra.QuadraticForm.Arf.Classification`.

## Main definitions

* `QuadraticMap.arf`: the Arf invariant in `ZMod 2` of a quadratic form over `ZMod 2`, defined via
  a symplectic basis when one exists and `0` otherwise.

## Main results

* `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J` and
  `QuadraticMap.even_finrank_of_nondegenerate_polarBilin`: symplectic basis existence and even
  dimension in characteristic two.
* `QuadraticMap.exists_hyperbolic_basis_of_isTotallyIsotropic`: over any field of characteristic
  two, any basis of a `Q`-totally isotropic Lagrangian extends to a hyperbolic basis (`Q = 0` on
  all basis vectors and Gram matrix `Matrix.J`).
* `QuadraticMap.sum_mul_eq_of_toMatrix_polarBilin_eq_J` and
  `QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`: independence of `∑ i, Q (a_i) * Q (b_i)`
  from the symplectic basis.
* `QuadraticMap.IsometryEquiv.arf_eq`, `QuadraticMap.Equivalent.arf_eq`, `QuadraticMap.arf_prod`,
  `QuadraticMap.arf_pi`, and `QuadraticMap.arf_dualProd`: isometry invariance and additivity under
  orthogonal sums.
* `QuadraticMap.sum_neg_one_pow_val_apply` and
  `QuadraticMap.card_apply_eq_zero_of_finrank_eq_two_mul`: the integer Gauss sum and `Q`-zero
  count.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*,
  J. Reine Angew. Math. **183** (1941), 148–167.
* W. Browder, *Surgery on Simply-Connected Manifolds*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete **65**, Springer-Verlag (1972), §III.1.
* L. Pyronneau, *Arf invariant*, §2.1 (Lemmas 2.11–2.13, Corollary 2.14).
-/

public section

namespace QuadraticMap

/-! ### Characteristic-two symplectic and hyperbolic bases -/

section CharTwoRing

variable {R M ι : Type*} [CommRing R] [CharP R 2] [AddCommGroup M] [Module R M]

/-- Over a commutative ring of characteristic two, a basis indexed by `ι ⊕ ι` has polar Gram matrix
`Matrix.J ι R` if and only if each half is pairwise polar-orthogonal and opposite basis vectors pair
by Kronecker delta. -/
theorem toMatrix_polarBilin_eq_J_iff [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm R M} {b : Module.Basis (ι ⊕ ι) R M} :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0) ∧
      (∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0) ∧
      ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0 := by
  constructor
  · intro h
    have hentry (x y : ι ⊕ ι) : polar Q (b x) (b y) = Matrix.J ι R x y := by
      simpa [LinearMap.BilinForm.toMatrix_apply] using congrFun (congrFun h x) y
    refine ⟨fun i j ↦ by simpa [Matrix.J] using hentry (.inl i) (.inl j),
      fun i j ↦ by simpa [Matrix.J] using hentry (.inr i) (.inr j), fun i j ↦ ?_⟩
    rw [polar_comm, hentry (.inr j) (.inl i)]
    simp [Matrix.J, Matrix.one_apply, eq_comm]
  · rintro ⟨hll, hrr, hlr⟩
    ext (i | i) (j | j)
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hll i j
    · rw [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, hlr i j]
      by_cases hij : i = j <;> simp [Matrix.J, hij, CharTwo.neg_eq]
    · rw [LinearMap.BilinForm.toMatrix_apply, polarBilin_apply_apply, polar_comm, hlr j i]
      by_cases hij : i = j <;> simp [Matrix.J, hij, eq_comm]
    · simpa [LinearMap.BilinForm.toMatrix_apply, Matrix.J] using hrr i j

omit [CharP R 2] in
/-- Coordinate expansion of a quadratic form along a symplectic pair family: distinct planes are
polar-orthogonal, and on the `i`-th plane
`Q (x_i • a_i + y_i • b_i) = x_i ^ 2 * Q a_i + x_i * y_i + y_i ^ 2 * Q b_i`. -/
theorem apply_sum_symplectic [DecidableEq ι] (Q : QuadraticForm R M) (s : Finset ι) (a b : ι → M)
    (haa : ∀ i ∈ s, ∀ j ∈ s, polar Q (a i) (a j) = 0)
    (hbb : ∀ i ∈ s, ∀ j ∈ s, polar Q (b i) (b j) = 0)
    (hab : ∀ i ∈ s, ∀ j ∈ s, polar Q (a i) (b j) = if i = j then 1 else 0) (x y : ι → R) :
    Q (∑ i ∈ s, (x i • a i + y i • b i)) =
      ∑ i ∈ s, (x i ^ 2 * Q (a i) + x i * y i + y i ^ 2 * Q (b i)) := by
  rw [Q.map_sum_of_polar_eq_zero s _ fun i hi j hj hij ↦ by
    simp [haa i hi j hj, hbb i hi j hj, hab i hi j hj, polar_comm Q (b i) (a j),
      hab j hj i hi, hij, hij.symm]]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, hab i hi i hi]
  simp only [↓reduceIte, smul_eq_mul]
  ring

/-- Coordinate expansion of `Q (b.equivFun.symm c)` on a symplectic basis `b` in characteristic
two. -/
theorem apply_equivFun_symm_of_toMatrix_polarBilin_eq_J [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm R M} {b : Module.Basis (ι ⊕ ι) R M}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (c : ι ⊕ ι → R) :
    Q (b.equivFun.symm c) =
      ∑ i : ι, (c (Sum.inl i) ^ 2 * Q (b (Sum.inl i)) + c (Sum.inl i) * c (Sum.inr i) +
        c (Sum.inr i) ^ 2 * Q (b (Sum.inr i))) := by
  obtain ⟨hll, hrr, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb
  have hrepr : b.equivFun.symm c =
      ∑ i : ι, (c (Sum.inl i) • b (Sum.inl i) + c (Sum.inr i) • b (Sum.inr i)) := by
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rw [hrepr]
  exact Q.apply_sum_symplectic Finset.univ (fun i ↦ b (Sum.inl i)) (fun i ↦ b (Sum.inr i))
    (fun i _ j _ ↦ hll i j) (fun i _ j _ ↦ hrr i j) (fun i _ j _ ↦ hlr i j)
    (fun i ↦ c (Sum.inl i)) (fun i ↦ c (Sum.inr i))

end CharTwoRing

section CharTwoField

variable {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

/-- A finite-dimensional quadratic space over a field of characteristic two with nondegenerate polar
form has even dimension. -/
theorem even_finrank_of_nondegenerate_polarBilin [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) : Even (Module.finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank (B := Q.polarBilin) Q.isAlt_polarBilin hQ

/-- In a finite-dimensional polar-nondegenerate quadratic space in characteristic two, twice half
the dimension equals the dimension. -/
theorem two_mul_finrank_div_two_of_nondegenerate_polarBilin [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) :
    2 * (Module.finrank K V / 2) = Module.finrank K V := by
  obtain ⟨m, hm⟩ := even_finrank_of_nondegenerate_polarBilin hQ
  omega

/-- Every finite-dimensional quadratic space over a field of characteristic two with nondegenerate
polar form admits a symplectic basis indexed by `Fin (finrank K V / 2) ⊕ Fin (finrank K V / 2)`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) :
    ∃ b : Module.Basis (Fin (Module.finrank K V / 2) ⊕ Fin (Module.finrank K V / 2)) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin (Module.finrank K V / 2)) K := by
  obtain ⟨m, b, hb⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
    (B := Q.polarBilin) Q.isAlt_polarBilin hQ
  have hm : m = Module.finrank K V / 2 := by
    have hcard := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at hcard
    omega
  subst hm
  exact ⟨b, hb⟩

/-- Over any field of characteristic two, every basis of a `Q`-totally isotropic Lagrangian subspace
`U` (`U = U^⊥` for `Q.polarBilin`) extends to a hyperbolic basis: a symplectic basis whose `Sum.inl`
half is the given basis of `U` and on whose basis vectors `Q` vanishes identically. -/
theorem exists_hyperbolic_basis_of_isTotallyIsotropic [FiniteDimensional K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V} (e : Module.Basis ι K U)
    (hU : Q.IsTotallyIsotropic U) (horth : LinearMap.BilinForm.orthogonal Q.polarBilin U = U) :
    ∃ b : Module.Basis (ι ⊕ ι) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι K ∧
      (∀ i, b (Sum.inl i) = (e i : V)) ∧
      (∀ i, Q (b (Sum.inl i)) = 0) ∧
      ∀ i, Q (b (Sum.inr i)) = 0 := by
  obtain ⟨b₀, hb₀, hinl⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq
    (B := Q.polarBilin) Q.isAlt_polarBilin hQ e horth.symm
  obtain ⟨hll, hrr, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb₀
  have hQinl (i : ι) : Q (b₀ (Sum.inl i)) = 0 := by
    rw [hinl i]
    exact hU.apply_eq_zero (e i).2
  -- Correct each dual partner by `Q (b₀ (inr i)) • b₀ (inl i)` to kill `Q` in characteristic two.
  let d : ι ⊕ ι → V := Sum.elim (fun i ↦ b₀ (Sum.inl i))
    (fun i ↦ b₀ (Sum.inr i) + Q (b₀ (Sum.inr i)) • b₀ (Sum.inl i))
  have hd_polar : (∀ i j, polar Q (d (.inl i)) (d (.inl j)) = 0) ∧
      (∀ i j, polar Q (d (.inr i)) (d (.inr j)) = 0) ∧
      ∀ i j, polar Q (d (.inl i)) (d (.inr j)) = if i = j then 1 else 0 := by
    refine ⟨hll, fun i j ↦ ?_, fun i j ↦ by simp [d, hll, hlr]⟩
    simp only [d, Sum.elim_inr, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hrr, hll, hlr, polar_comm Q (b₀ (.inr i)) (b₀ (.inl j)), smul_eq_mul, mul_zero, zero_add,
      add_zero]
    rcases eq_or_ne i j with rfl | hij
    · simp [CharTwo.add_self_eq_zero]
    · simp [hij, hij.symm]
  have hdJ (x y : ι ⊕ ι) : Q.polarBilin (d x) (d y) = Matrix.J ι K x y := by
    rcases x with i | i <;> rcases y with j | j
    · simpa [Matrix.J] using hd_polar.1 i j
    · rw [polarBilin_apply_apply, hd_polar.2.2 i j]
      by_cases hij : i = j <;> simp [Matrix.J, hij, CharTwo.neg_eq]
    · rw [polarBilin_apply_apply, polar_comm, hd_polar.2.2 j i]
      by_cases hij : i = j <;> simp [Matrix.J, hij, eq_comm]
    · simpa [Matrix.J] using hd_polar.2.1 i j
  have hli : LinearIndependent K d := by
    apply LinearMap.BilinForm.linearIndependent_of_det_ne_zero (B := Q.polarBilin)
    have hmat : (Matrix.of fun x y ↦ Q.polarBilin (d x) (d y)) = Matrix.J ι K := Matrix.ext hdJ
    rw [hmat]
    exact (Matrix.isUnit_det_J ι K).ne_zero
  let b := basisOfLinearIndependentOfCardEqFinrank' d hli (Module.finrank_eq_card_basis b₀).symm
  have hb : ⇑b = d :=
    coe_basisOfLinearIndependentOfCardEqFinrank' d hli (Module.finrank_eq_card_basis b₀).symm
  refine ⟨b, (toMatrix_polarBilin_eq_J_iff (Q := Q)).mpr ?_,
    fun i ↦ by simp [hb, d, hinl], fun i ↦ by simp [hb, d, hQinl], fun i ↦ ?_⟩
  · simpa [hb] using hd_polar
  · simp [hb, d, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQinl,
      polar_comm Q (b₀ (.inr i)), hlr, CharTwo.add_self_eq_zero]

end CharTwoField

/-! ### The Arf invariant, Gauss sum, and zero counts over `ZMod 2` -/

section ZModTwoHelpers

private theorem neg_one_pow_val_add (x y : ZMod 2) :
    (-1 : ℤ) ^ (x + y).val = (-1 : ℤ) ^ x.val * (-1 : ℤ) ^ y.val := by
  fin_cases x <;> fin_cases y <;> decide

private theorem neg_one_pow_val_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    (-1 : ℤ) ^ (∑ i ∈ s, f i).val = ∏ i ∈ s, (-1 : ℤ) ^ (f i).val := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.prod_cons, neg_one_pow_val_add, ih]

private theorem neg_one_pow_val_inj {x y : ZMod 2}
    (h : (-1 : ℤ) ^ x.val = (-1 : ℤ) ^ y.val) : x = y := by
  have key : ∀ a b : ZMod 2, (-1 : ℤ) ^ a.val = (-1 : ℤ) ^ b.val → a = b := by decide
  exact key x y h

private theorem sum_neg_one_pow_plane (a b : ZMod 2) :
    ∑ p : ZMod 2 × ZMod 2, (-1 : ℤ) ^ (p.1 ^ 2 * a + p.1 * p.2 + p.2 ^ 2 * b).val =
      (-1 : ℤ) ^ (a * b).val * 2 := by
  fin_cases a <;> fin_cases b <;> decide

private theorem one_add_neg_one_pow_val (x : ZMod 2) :
    (1 : ℤ) + (-1 : ℤ) ^ x.val = if x = 0 then 2 else 0 := by
  fin_cases x <;> decide

end ZModTwoHelpers

section ArfBasic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The **Arf invariant** of a quadratic form `Q` over `ZMod 2`: when `V` admits a finite
symplectic basis `b` indexed by `Fin m ⊕ Fin m` for `Q.polarBilin`, `Q.arf` is
`∑ i, Q (b (inl i)) * Q (b (inr i))`; otherwise `Q.arf = 0`. By
`QuadraticMap.arf_eq_sum_of_toMatrix_polarBilin_eq_J`, the sum is independent of the chosen
symplectic basis. -/
noncomputable def arf (Q : QuadraticForm (ZMod 2) V) : ZMod 2 :=
  open scoped Classical in
  if h : ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V),
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) (ZMod 2) then
    ∑ i : Fin h.choose, Q (h.choose_spec.choose (Sum.inl i)) * Q (h.choose_spec.choose (Sum.inr i))
  else 0

/-- **Planar factorization of the integer Gauss sum.** On any finite `ZMod 2`-space `V` equipped
with a symplectic basis `b` indexed by `ι ⊕ ι` for `Q.polarBilin`, the Gauss sum of `Q` equals
`(-1) ^ (∑ i, Q (b (inl i)) * Q (b (inr i))).val * 2 ^ card ι`. -/
theorem sum_neg_one_pow_val_apply_of_toMatrix_polarBilin_eq_J [Fintype V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm (ZMod 2) V}
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      (-1 : ℤ) ^ (∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i))).val * 2 ^ Fintype.card ι := by
  let e : (ι → ZMod 2 × ZMod 2) ≃ V :=
    { toFun g := b.equivFun.symm (Sum.elim (fun i ↦ (g i).1) (fun i ↦ (g i).2))
      invFun v i := (b.equivFun v (Sum.inl i), b.equivFun v (Sum.inr i))
      left_inv g := by
        ext i
        · simpa using congrFun (b.equivFun.apply_symm_apply
            (Sum.elim (fun j ↦ (g j).1) (fun j ↦ (g j).2))) (Sum.inl i)
        · simpa using congrFun (b.equivFun.apply_symm_apply
            (Sum.elim (fun j ↦ (g j).1) (fun j ↦ (g j).2))) (Sum.inr i)
      right_inv v := by
        have hfun : Sum.elim (fun i ↦ b.equivFun v (Sum.inl i))
            (fun i ↦ b.equivFun v (Sum.inr i)) = b.equivFun v := by
          ext (i | i) <;> rfl
        dsimp only
        rw [hfun, b.equivFun.symm_apply_apply] }
  have he (g : ι → ZMod 2 × ZMod 2) :
      Q (e g) = ∑ i : ι, ((g i).1 ^ 2 * Q (b (Sum.inl i)) + (g i).1 * (g i).2 +
        (g i).2 ^ 2 * Q (b (Sum.inr i))) := by
    simpa [e] using apply_equivFun_symm_of_toMatrix_polarBilin_eq_J hb
      (Sum.elim (fun i ↦ (g i).1) (fun i ↦ (g i).2))
  rw [← e.sum_comp]
  simp_rw [he, neg_one_pow_val_sum]
  rw [← Fintype.prod_sum (f := fun i (p : ZMod 2 × ZMod 2) ↦
    (-1 : ℤ) ^ (p.1 ^ 2 * Q (b (Sum.inl i)) + p.1 * p.2 + p.2 ^ 2 * Q (b (Sum.inr i))).val)]
  simp_rw [sum_neg_one_pow_plane]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← neg_one_pow_val_sum]

/-- **Symplectic-basis independence of the Arf sum.** Any two finite symplectic bases of the same
quadratic form over `ZMod 2` yield the same sum of products `∑ i, Q (a_i) * Q (b_i)`. -/
theorem sum_mul_eq_of_toMatrix_polarBilin_eq_J {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {Q : QuadraticForm (ZMod 2) V}
    {b : Module.Basis (ι ⊕ ι) (ZMod 2) V} {c : Module.Basis (κ ⊕ κ) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2))
    (hc : LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J κ (ZMod 2)) :
    ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) =
      ∑ j : κ, Q (c (Sum.inl j)) * Q (c (Sum.inr j)) := by
  let _ : Fintype V := Fintype.ofEquiv (ι ⊕ ι → ZMod 2) b.equivFun.symm.toEquiv
  have hcard : Fintype.card ι = Fintype.card κ := by
    have hdim : Fintype.card (ι ⊕ ι) = Fintype.card (κ ⊕ κ) := by
      rw [← Module.finrank_eq_card_basis b, ← Module.finrank_eq_card_basis c]
    simp only [Fintype.card_sum] at hdim
    omega
  have hgauss := (sum_neg_one_pow_val_apply_of_toMatrix_polarBilin_eq_J hb).symm.trans
    (sum_neg_one_pow_val_apply_of_toMatrix_polarBilin_eq_J hc)
  rw [← hcard] at hgauss
  have hpow : (2 : ℤ) ^ Fintype.card ι ≠ 0 := by positivity
  exact neg_one_pow_val_inj (mul_right_cancel₀ hpow hgauss)

/-- On any finite symplectic basis `b` for `Q.polarBilin`, `Q.arf` equals
`∑ i, Q (b (Sum.inl i)) * Q (b (Sum.inr i))`. -/
theorem arf_eq_sum_of_toMatrix_polarBilin_eq_J {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) V} {b : Module.Basis (ι ⊕ ι) (ZMod 2) V}
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι (ZMod 2)) :
    Q.arf = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) := by
  let σ := Fintype.equivFin ι
  let b' : Module.Basis (Fin (Fintype.card ι) ⊕ Fin (Fintype.card ι)) (ZMod 2) V :=
    b.reindex (σ.sumCongr σ)
  have hb' : LinearMap.BilinForm.toMatrix b' Q.polarBilin =
      Matrix.J (Fin (Fintype.card ι)) (ZMod 2) := by
    obtain ⟨hll, hrr, hlr⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q)).mp hb
    refine (toMatrix_polarBilin_eq_J_iff (Q := Q)).mpr ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simpa [b'] using hll (σ.symm i) (σ.symm j)
    · simpa [b'] using hrr (σ.symm i) (σ.symm j)
    · simpa [b', σ.symm.injective.eq_iff] using hlr (σ.symm i) (σ.symm j)
  have hex : ∃ (m : ℕ) (c : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V),
      LinearMap.BilinForm.toMatrix c Q.polarBilin = Matrix.J (Fin m) (ZMod 2) :=
    ⟨Fintype.card ι, b', hb'⟩
  rw [arf, dite_eq_left hex]
  exact sum_mul_eq_of_toMatrix_polarBilin_eq_J hex.choose_spec.choose_spec hb

/-- Unbundled symplectic-basis formula for `Q.arf`: if `b` is a basis of `V` indexed by `ι ⊕ ι`
with pairwise orthogonal halves and `polar Q (b (inl i)) (b (inr j)) = δᵢⱼ`, then
`Q.arf = ∑ i, Q (b (inl i)) * Q (b (inr i))`. -/
theorem arf_eq_sum_of_polar_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm (ZMod 2) V} (b : Module.Basis (ι ⊕ ι) (ZMod 2) V)
    (hll : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inl j)) = 0)
    (hrr : ∀ i j, polar Q (b (Sum.inr i)) (b (Sum.inr j)) = 0)
    (hlr : ∀ i j, polar Q (b (Sum.inl i)) (b (Sum.inr j)) = if i = j then 1 else 0) :
    Q.arf = ∑ i : ι, Q (b (Sum.inl i)) * Q (b (Sum.inr i)) :=
  arf_eq_sum_of_toMatrix_polarBilin_eq_J
    ((toMatrix_polarBilin_eq_J_iff (Q := Q)).mpr ⟨hll, hrr, hlr⟩)

/-- The Arf invariant of a form on a trivial `ZMod 2`-module is `0`. -/
@[simp]
theorem arf_of_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) : Q.arf = 0 := by
  have hb : LinearMap.BilinForm.toMatrix (Module.Basis.empty V :
      Module.Basis (Fin 0 ⊕ Fin 0) (ZMod 2) V) Q.polarBilin = Matrix.J (Fin 0) (ZMod 2) := by
    ext x
    exact Fin.elim0 (Sum.rec id id x)
  simpa using arf_eq_sum_of_toMatrix_polarBilin_eq_J hb

/-- The Arf invariant of the zero quadratic form is `0`. -/
@[simp]
theorem arf_zero : (0 : QuadraticForm (ZMod 2) V).arf = 0 := by
  classical
  rw [arf]
  split_ifs <;> simp

/-- If `Q.polarBilin` is degenerate, `Q` admits no symplectic basis and `Q.arf = 0`. -/
theorem arf_eq_zero_of_not_nondegenerate_polarBilin {Q : QuadraticForm (ZMod 2) V}
    (hQ : ¬ Q.polarBilin.Nondegenerate) : Q.arf = 0 := by
  refine dite_eq_right fun ⟨m, b, hb⟩ ↦ hQ ?_
  refine (LinearMap.BilinForm.nondegenerate_toMatrix_iff (B := Q.polarBilin) b).mp ?_
  rw [hb]
  exact Matrix.nondegenerate_of_det_ne_zero (Matrix.isUnit_det_J (Fin m) (ZMod 2)).ne_zero

/-- If `V` is infinite-dimensional over `ZMod 2`, `Q.arf = 0`. -/
theorem arf_eq_zero_of_not_finite {Q : QuadraticForm (ZMod 2) V}
    (hV : ¬ FiniteDimensional (ZMod 2) V) : Q.arf = 0 :=
  dite_eq_right fun ⟨_, b, _⟩ ↦ hV (Module.Finite.of_basis b)

end ArfBasic

/-! ### Isometry invariance and additivity under orthogonal sums -/

private theorem IsometryEquiv.toMatrix_map_polarBilin_eq_J {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]
    {Q₁ : QuadraticForm (ZMod 2) V₁} {Q₂ : QuadraticForm (ZMod 2) V₂}
    (e : Q₁.IsometryEquiv Q₂) {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V₁)
    (hb : LinearMap.BilinForm.toMatrix b Q₁.polarBilin = Matrix.J (Fin m) (ZMod 2)) :
    LinearMap.BilinForm.toMatrix (b.map e.toLinearEquiv) Q₂.polarBilin =
      Matrix.J (Fin m) (ZMod 2) := by
  ext x y
  simpa [LinearMap.BilinForm.toMatrix_apply, e.polar_apply] using congrFun (congrFun hb x) y

/-- Isometric quadratic forms over `ZMod 2` have equal Arf invariants. -/
theorem IsometryEquiv.arf_eq {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] {Q₁ : QuadraticForm (ZMod 2) V₁}
    {Q₂ : QuadraticForm (ZMod 2) V₂} (e : Q₁.IsometryEquiv Q₂) : Q₁.arf = Q₂.arf := by
  by_cases h₁ : ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V₁),
      LinearMap.BilinForm.toMatrix b Q₁.polarBilin = Matrix.J (Fin m) (ZMod 2)
  · obtain ⟨m, b, hb⟩ := h₁
    have hb₂ := e.toMatrix_map_polarBilin_eq_J b hb
    rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J (Q := Q₁) hb,
      arf_eq_sum_of_toMatrix_polarBilin_eq_J (Q := Q₂) hb₂]
    simp
  · have h₂ : ¬ ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) V₂),
        LinearMap.BilinForm.toMatrix b Q₂.polarBilin = Matrix.J (Fin m) (ZMod 2) :=
      fun ⟨m, b, hb⟩ ↦ h₁ ⟨m, b.map e.symm.toLinearEquiv, e.symm.toMatrix_map_polarBilin_eq_J b hb⟩
    have ha₁ : Q₁.arf = 0 := dite_eq_right h₁
    have ha₂ : Q₂.arf = 0 := dite_eq_right h₂
    rw [ha₁, ha₂]

/-- Equivalent quadratic forms over `ZMod 2` have equal Arf invariants. -/
theorem Equivalent.arf_eq {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] {Q₁ : QuadraticForm (ZMod 2) V₁}
    {Q₂ : QuadraticForm (ZMod 2) V₂} (h : Q₁.Equivalent Q₂) : Q₁.arf = Q₂.arf := by
  obtain ⟨e⟩ := h
  exact e.arf_eq

/-- Pulling back a quadratic form over `ZMod 2` along a linear equivalence preserves `arf`. -/
@[simp]
theorem arf_comp_linearEquiv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂] (Q : QuadraticForm (ZMod 2) V₂)
    (e : V₁ ≃ₗ[ZMod 2] V₂) : (Q.comp e.toLinearMap).arf = Q.arf :=
  ({ toLinearEquiv := e, map_app' := fun _ ↦ rfl } : (Q.comp e.toLinearMap).IsometryEquiv Q).arf_eq

/-- **Additivity of the Arf invariant on binary orthogonal sums.** For finite-dimensional
polar-nondegenerate quadratic spaces `(V₁, Q₁)` and `(V₂, Q₂)` over `ZMod 2`,
`(Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf`. -/
theorem arf_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [FiniteDimensional (ZMod 2) V₁] [AddCommGroup V₂] [Module (ZMod 2) V₂]
    [FiniteDimensional (ZMod 2) V₂] {Q₁ : QuadraticForm (ZMod 2) V₁}
    {Q₂ : QuadraticForm (ZMod 2) V₂} (h₁ : Q₁.polarBilin.Nondegenerate)
    (h₂ : Q₂.polarBilin.Nondegenerate) :
    (Q₁.prod Q₂).arf = Q₁.arf + Q₂.arf := by
  obtain ⟨b₁, hb₁⟩ := exists_basis_toMatrix_polarBilin_eq_J h₁
  obtain ⟨b₂, hb₂⟩ := exists_basis_toMatrix_polarBilin_eq_J h₂
  obtain ⟨hll₁, hrr₁, hlr₁⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q₁)).mp hb₁
  obtain ⟨hll₂, hrr₂, hlr₂⟩ := (toMatrix_polarBilin_eq_J_iff (Q := Q₂)).mp hb₂
  let b := (b₁.prod b₂).reindex (Equiv.sumSumSumComm _ _ _ _)
  have hb : LinearMap.BilinForm.toMatrix b (Q₁.prod Q₂).polarBilin =
      Matrix.J (Fin (Module.finrank (ZMod 2) V₁ / 2) ⊕
        Fin (Module.finrank (ZMod 2) V₂ / 2)) (ZMod 2) := by
    refine (toMatrix_polarBilin_eq_J_iff (Q := Q₁.prod Q₂)).mpr ⟨?_, ?_, ?_⟩
    · rintro (i | i) (j | j) <;> simp [b, hll₁, hll₂]
    · rintro (i | i) (j | j) <;> simp [b, hrr₁, hrr₂]
    · rintro (i | i) (j | j) <;> simp [b, hlr₁, hlr₂]
  rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, Fintype.sum_sum_type,
    arf_eq_sum_of_toMatrix_polarBilin_eq_J hb₁, arf_eq_sum_of_toMatrix_polarBilin_eq_J hb₂]
  simp [b]

private theorem arf_pi_fin : ∀ (n : ℕ) (W : Fin n → Type*) [∀ i, AddCommGroup (W i)]
    [∀ i, Module (ZMod 2) (W i)] [∀ i, FiniteDimensional (ZMod 2) (W i)]
    (P : ∀ i, QuadraticForm (ZMod 2) (W i)),
    (∀ i, (P i).polarBilin.Nondegenerate) → (QuadraticMap.pi P).arf = ∑ i, (P i).arf
  | 0, W, _, _, _, P, _ => by simp [arf_of_subsingleton]
  | n + 1, W, _, _, _, P, hP => by
    rw [← (QuadraticMap.IsometryEquiv.consPi P).arf_eq,
      arf_prod (hP 0) (nondegenerate_polarBilin_pi_iff.mpr fun i ↦ hP i.succ),
      arf_pi_fin n (fun i ↦ W i.succ) (fun i ↦ P i.succ) (fun i ↦ hP i.succ),
      Fin.sum_univ_succ]

/-- **Additivity of the Arf invariant on finite orthogonal sums.** -/
theorem arf_pi {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module (ZMod 2) (V i)] [∀ i, FiniteDimensional (ZMod 2) (V i)]
    {Q : ∀ i, QuadraticForm (ZMod 2) (V i)} (hQ : ∀ i, (Q i).polarBilin.Nondegenerate) :
    (QuadraticMap.pi Q).arf = ∑ i, (Q i).arf := by
  let σ := (Fintype.equivFin ι).symm
  rw [← (QuadraticMap.IsometryEquiv.piCongrLeft Q σ).arf_eq,
    arf_pi_fin (Fintype.card ι) (fun j ↦ V (σ j)) (fun j ↦ Q (σ j)) (fun j ↦ hQ (σ j))]
  exact σ.sum_comp (fun i ↦ (Q i).arf)

/-- The canonical hyperbolic form `QuadraticForm.dualProd (ZMod 2) V` has Arf invariant `0`. -/
@[simp]
theorem arf_dualProd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    (QuadraticForm.dualProd (ZMod 2) V).arf = 0 := by
  by_cases hV : FiniteDimensional (ZMod 2) V
  · let e := Module.finBasis (ZMod 2) V
    let b := e.dualBasis.prod e
    have hb : LinearMap.BilinForm.toMatrix b (QuadraticForm.dualProd (ZMod 2) V).polarBilin =
        Matrix.J (Fin (Module.finrank (ZMod 2) V)) (ZMod 2) := by
      refine (toMatrix_polarBilin_eq_J_iff (Q := QuadraticForm.dualProd (ZMod 2) V)).mpr
        ⟨fun i j ↦ by simp [b, TauCeti.polar_dualProd],
          fun i j ↦ by simp [b, TauCeti.polar_dualProd], fun i j ↦ ?_⟩
      by_cases hij : i = j <;> simp [b, TauCeti.polar_dualProd, hij]
    rw [arf_eq_sum_of_toMatrix_polarBilin_eq_J hb]
    simp [b]
  · refine arf_eq_zero_of_not_finite fun hprod ↦ hV ?_
    exact Module.Finite.of_surjective (LinearMap.snd (ZMod 2) (Module.Dual (ZMod 2) V) V)
      LinearMap.snd_surjective

/-! ### Gauss sum and zero-counting theorems -/

section GaussAndZeros

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- **Gauss sum for quadratic forms over `𝔽₂`.** On any finite `ZMod 2`-vector space `V` carrying a
quadratic form `Q` with nondegenerate polar form,
`∑ v : V, (-1 : ℤ) ^ (Q v).val = (-1 : ℤ) ^ Q.arf.val * 2 ^ (finrank (ZMod 2) V / 2)`. -/
theorem sum_neg_one_pow_val_apply [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val =
      (-1 : ℤ) ^ Q.arf.val * 2 ^ (Module.finrank (ZMod 2) V / 2) := by
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  rw [sum_neg_one_pow_val_apply_of_toMatrix_polarBilin_eq_J hb,
    ← arf_eq_sum_of_toMatrix_polarBilin_eq_J hb, Fintype.card_fin]

/-- **Gauss sum in terms of the half-dimension `m`.** When `finrank (ZMod 2) V = 2 * m`,
`∑ v : V, (-1 : ℤ) ^ (Q v).val = (-1 : ℤ) ^ Q.arf.val * 2 ^ m`. -/
theorem sum_neg_one_pow_val_apply_of_finrank_eq_two_mul [Fintype V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hm : Module.finrank (ZMod 2) V = 2 * m) :
    ∑ v : V, (-1 : ℤ) ^ (Q v).val = (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  rw [sum_neg_one_pow_val_apply hQ, hm, Nat.mul_div_right m two_pos]

/-- Twice the number of isotropic vectors (`Q v = 0`) is `2 ^ (2 * m) + (-1) ^ Q.arf.val * 2 ^ m`
for every `m ≥ 0` with `finrank (ZMod 2) V = 2 * m`. -/
theorem two_mul_card_apply_eq_zero [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m) :
    2 * (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m) + (-1 : ℤ) ^ Q.arf.val * 2 ^ m := by
  obtain ⟨b, _⟩ := exists_basis_toMatrix_polarBilin_eq_J hQ
  have hcardV : Fintype.card V = 2 ^ (2 * m) := by
    have hm' : Module.finrank (ZMod 2) V / 2 = m := by omega
    rw [Fintype.card_congr b.equivFun.toEquiv]
    simp [hm', two_mul, pow_add]
  have hfilter : (2 : ℤ) * Fintype.card {v : V // Q v = 0} =
      ∑ v : V, ((1 : ℤ) + (-1 : ℤ) ^ (Q v).val) := by
    simp_rw [one_add_neg_one_pow_val, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_comm _ (2 : ℤ), Fintype.card_subtype]
  rw [hfilter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_one, hcardV,
    Nat.cast_pow, Nat.cast_ofNat, sum_neg_one_pow_val_apply_of_finrank_eq_two_mul hQ hm]

/-- **Isotropic-vector count for `m ≥ 1`.** If `finrank (ZMod 2) V = 2 * m` with `1 ≤ m` and
`Q.polarBilin` is nondegenerate, the number of `v : V` with `Q v = 0` satisfies
`(Fintype.card {v : V // Q v = 0} : ℤ) = 2 ^ (2 * m - 1) + (-1) ^ Q.arf.val * 2 ^ (m - 1)`. -/
theorem card_apply_eq_zero_of_finrank_eq_two_mul [Fintype V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hm : Module.finrank (ZMod 2) V = 2 * m)
    (hm1 : 1 ≤ m) :
    (Fintype.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  have h2 := two_mul_card_apply_eq_zero hQ hm
  have hpow1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    conv_lhs => rw [show 2 * m = (2 * m - 1) + 1 by omega, pow_succ']
  have hpow2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ']
  rw [hpow1, hpow2] at h2
  linarith

/-- On a zero-dimensional (`m = 0`) `ZMod 2`-space, `0` is the unique isotropic vector, so the zero
count is `1`. -/
@[simp]
theorem card_apply_eq_zero_of_subsingleton [Fintype V] [Subsingleton V]
    (Q : QuadraticForm (ZMod 2) V) : Fintype.card {v : V // Q v = 0} = 1 := by
  have : Unique {v : V // Q v = 0} :=
    { default := ⟨0, map_zero Q⟩
      uniq := fun ⟨v, _⟩ ↦ Subtype.ext (Subsingleton.elim v 0) }
  exact Fintype.card_unique

/-- `Nat.card` version of `card_apply_eq_zero_of_finrank_eq_two_mul`, requiring only
`[FiniteDimensional (ZMod 2) V]` rather than a `Fintype V` instance. -/
theorem natCard_apply_eq_zero_of_finrank_eq_two_mul [FiniteDimensional (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hm : Module.finrank (ZMod 2) V = 2 * m) (hm1 : 1 ≤ m) :
    (Nat.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m - 1) + (-1 : ℤ) ^ Q.arf.val * 2 ^ (m - 1) := by
  let e := Module.finBasis (ZMod 2) V
  let _ : Fintype V := Fintype.ofEquiv _ e.equivFun.symm.toEquiv
  rw [Nat.card_eq_fintype_card]
  exact card_apply_eq_zero_of_finrank_eq_two_mul hQ hm hm1

/-- `Nat.card` zero-count on a trivial `ZMod 2`-space (`m = 0`). -/
@[simp]
theorem natCard_apply_eq_zero_of_subsingleton [Subsingleton V] (Q : QuadraticForm (ZMod 2) V) :
    Nat.card {v : V // Q v = 0} = 1 := by
  let _ : Unique V := ⟨⟨0⟩, fun v ↦ Subsingleton.elim v 0⟩
  rw [Nat.card_eq_fintype_card]
  exact card_apply_eq_zero_of_subsingleton Q

end GaussAndZeros

end QuadraticMap
