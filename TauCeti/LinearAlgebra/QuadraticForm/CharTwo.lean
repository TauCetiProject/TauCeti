/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Binary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.LagrangianBasis
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import TauCeti.LinearAlgebra.Dimension.Basis
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Nonsingular quadratic forms in characteristic two

In characteristic two, the polarization `QuadraticMap.polar Q` of a quadratic map satisfies
`polar Q x x = 2 • Q x = 0` (`QuadraticMap.polar_self_of_charTwo`), so `Q.polarBilin` is
alternating (`QuadraticMap.isAlt_polarBilin`) rather than recovering `Q`. In particular,
nondegeneracy of the polar bilinear form (`Q.polarBilin.Nondegenerate`, called *nonsingularity* or
*ordinary nondegeneracy* by Elman--Karpenko--Merkurjev) is strictly stronger than
`QuadraticMap.Nondegenerate` in odd dimension, where the latter permits a rank-one polar kernel:
`Q.polarBilin` is a symplectic form on the ambient space, forcing even dimension and symplectic
coordinates. In even dimension the two notions agree over every field
(`QuadraticMap.nondegenerate_polar_iff_of_even_finrank`).

The characteristic-free polar-kernel descent, product, totally isotropic dimension, and binary
quadratic form `[a, b]` APIs live in `TauCeti.LinearAlgebra.QuadraticForm.Radical`,
`TauCeti.LinearAlgebra.QuadraticForm.Prod`, `TauCeti.LinearAlgebra.QuadraticForm.Isometry`,
`TauCeti.LinearAlgebra.QuadraticForm.TotallyIsotropic`, and
`TauCeti.LinearAlgebra.QuadraticForm.Binary`. This file builds the characteristic-two structure
that underpins the Arf invariant:

1. **Characteristic-two diagonals and binary forms `[a, b]`.** In characteristic two, the diagonal
   submodule of `M × M` is `(Q.prod Q)`-totally-isotropic and equals its own polar orthogonal
   complement whenever `Q.polarBilin` is left-separating, `Q.polarBilin` is alternating, every
   binary form `TauCeti.binaryQuadraticForm R a b` has nondegenerate polar pairing
   `x 0 * y 1 + x 1 * y 0` with polar-self-orthogonal first coordinate axis, and the orthogonal sum
   of two copies of `binaryQuadraticForm R 1 1` is explicitly isometric to the orthogonal sum of two
   hyperbolic planes `binaryQuadraticForm R 0 0`.
2. **Symplectic-basis decomposition.** Whenever `b : Module.Basis (ι ⊕ ι) R M` puts `Q.polarBilin`
   in standard symplectic form `Matrix.J ι R`, `Q` decomposes isometrically as the orthogonal sum of
   the binary forms `binaryQuadraticForm R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))`.
3. **Characteristic-two quadratic Lagrangians.** Over any field of characteristic two, a
   finite-dimensional quadratic space with nondegenerate polar form has even dimension, admits a
   symplectic basis, and splits into hyperbolic planes `binaryQuadraticForm K 0 0` if and only if it
   contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement
   (equivalently, of half the ambient dimension).
4. **Binary planes and the even-dimensional comparison.** In characteristic two, `[1, a]` is
   isotropic exactly when `a` lies in the Artin--Schreier image `℘(K) = {x ^ 2 + x}`. Over any
   field, nonsingularity agrees with `QuadraticMap.Nondegenerate` in even dimension, because a
   nondegenerate alternating form on a complement of the polar kernel forces that kernel to have
   even dimension. The characteristic-free normal form `[a, b]` of a nonsingular plane representing
   `a ≠ 0` is `QuadraticMap.exists_equivalent_binaryQuadraticForm_of_represents` in
   `TauCeti.LinearAlgebra.QuadraticForm.Binary`.

## Main definitions

* `TauCeti.isometryEquivBinaryQuadraticFormOneProd`: explicit characteristic-two isometry from
  `(binaryQuadraticForm R 1 1).prod (binaryQuadraticForm R 1 1)` to
  `(binaryQuadraticForm R 0 0).prod (binaryQuadraticForm R 0 0)`.
* `QuadraticMap.isometryEquivPiBinaryQuadraticForm`: decomposition of `Q` along any symplectic basis
  of `Q.polarBilin` into an orthogonal sum of binary quadratic forms `[a, b]`.

## Main results

* `QuadraticMap.isTotallyIsotropic_range_inl_add_inr_prod_self` and
  `QuadraticMap.orthogonal_range_inl_add_inr_prod_self`: in characteristic two, the diagonal
  submodule of `M × M` is `(Q.prod Q)`-totally-isotropic, and equals its own polar orthogonal
  complement when `Q.polarBilin` is left-separating.
* `QuadraticMap.polar_self_of_charTwo` and `QuadraticMap.isAlt_polarBilin`: in characteristic two,
  `polar Q x x = 0` and `Q.polarBilin` is alternating.
* `QuadraticMap.toMatrix_polarBilin_eq_J_iff`: in characteristic two, `toMatrix b Q.polarBilin = J`
  if and only if each half is polar-isotropic and opposite halves pair by the Kronecker delta.
* `TauCeti.nondegenerate_polarBilin_binaryQuadraticForm`: in characteristic two, every binary form
  `binaryQuadraticForm R a b` has nondegenerate polar bilinear form.
* `TauCeti.orthogonal_polarBilin_binaryQuadraticForm_span_one_zero`: in characteristic two, the
  first coordinate axis `R ∙ ![1, 0]` equals its own polar orthogonal complement.
* `QuadraticMap.even_finrank_of_nondegenerate_polarBilin`,
  `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J`,
  `QuadraticMap.exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq`: over a field of characteristic
  two, a finite-dimensional space with nondegenerate polar form has even dimension and a symplectic
  basis.
* `QuadraticMap.equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_orthogonal_eq`:
  over a field of characteristic two, splitting into hyperbolic planes is equivalent to the
  existence of a `Q`-totally-isotropic subspace equal to its polar orthogonal complement.
* `TauCeti.not_anisotropic_binaryQuadraticForm_one_iff`: in characteristic two, `[1, a]` is
  isotropic if and only if `a = x ^ 2 + x` for some `x`.
* `QuadraticMap.nondegenerate_polar_iff_of_even_finrank`: on an even-dimensional space over any
  field, nonsingularity (nondegenerate polar form) agrees with `QuadraticMap.Nondegenerate`.

## References

* C. Arf, *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2 (Teil I)*, J.
  Reine Angew. Math. **183** (1941), 148--167.
* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §§7--8.
* A. Pyronneau, *The Arf and Rohklin's invariant* (January 2024), §2.1, Lemma 2.13 and
  Theorem 2.15, pp. 4--5.
-/

public section

universe u

/-! ### Characteristic-two diagonals and alternating polarization -/

namespace QuadraticMap

section CharTwoSemiring

variable {R M P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid P] [Module R P]

/-- In characteristic two, the diagonal submodule `{(x, x) | x : M}` is totally isotropic for
`Q.prod Q`. -/
theorem isTotallyIsotropic_range_inl_add_inr_prod_self [CharP R 2] (Q : QuadraticMap R M P) :
    (Q.prod Q).IsTotallyIsotropic
      (LinearMap.range (LinearMap.inl R M M + LinearMap.inr R M M)) := by
  rw [isTotallyIsotropic_iff]
  rintro _ ⟨x, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk,
    add_zero, zero_add, QuadraticMap.prod_apply, ← two_nsmul, ← Nat.cast_smul_eq_nsmul R,
    CharP.cast_eq_zero, zero_smul]

end CharTwoSemiring

section CharTwoRing

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]

/-- In characteristic two, the polar form of any quadratic map vanishes on the diagonal. -/
@[simp high]
theorem polar_self_of_charTwo [CharP R 2] (Q : QuadraticMap R M P) (x : M) : polar Q x x = 0 := by
  rw [polar_self, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero, zero_smul]

/-- In characteristic two, the polar bilinear map of any quadratic map is alternating. -/
theorem isAlt_polarBilin [CharP R 2] (Q : QuadraticMap R M P) : Q.polarBilin.IsAlt := fun x ↦ by
  rw [polarBilin_apply_apply, polar_self_of_charTwo]

/-- In characteristic two, when `Q.polarBilin` is left-separating, the diagonal submodule
`{(x, x) | x : M}` equals its own `(Q.prod Q).polarBilin`-orthogonal complement. -/
theorem orthogonal_range_inl_add_inr_prod_self [CharP R 2] {Q : QuadraticForm R M}
    (hQ : Q.polarBilin.SeparatingLeft) :
    LinearMap.BilinForm.orthogonal (Q.prod Q).polarBilin
      (LinearMap.range (LinearMap.inl R M M + LinearMap.inr R M M)) =
      LinearMap.range (LinearMap.inl R M M + LinearMap.inr R M M) := by
  ext ⟨x, y⟩
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_range, LinearMap.add_apply,
    LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq,
    forall_exists_index, polarBilin_prod, LinearMap.compl₁₂_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, polarBilin_apply_apply]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hsum : x + y = 0 := hQ (x + y) fun m ↦ by
      have hm := h (m, m) m rfl
      rwa [polarBilin_apply_apply, polar_add_left, polar_comm Q x m, polar_comm Q y m]
    have hyy : y + y = 0 := by rw [← two_smul R y, CharTwo.two_eq_zero, zero_smul]
    exact ⟨y, (add_right_cancel (hsum.trans hyy.symm)).symm, rfl⟩
  · rintro ⟨m, rfl, rfl⟩ _ n rfl
    exact CharTwo.add_self_eq_zero _

end CharTwoRing

end QuadraticMap

/-! ### Characteristic-two binary quadratic forms `[a, b]` -/

namespace TauCeti

section CommRing

variable {R : Type u} [CommRing R]

/-- In characteristic two, the polarization of `binaryQuadraticForm R a b` is
`x 0 * y 1 + x 1 * y 0`, independent of `a` and `b`. -/
@[simp]
theorem polar_binaryQuadraticForm_of_charTwo [CharP R 2] (a b : R) (x y : Fin 2 → R) :
    QuadraticMap.polar (binaryQuadraticForm R a b) x y = x 0 * y 1 + x 1 * y 0 := by
  rw [polar_binaryQuadraticForm, CharTwo.two_eq_zero, zero_mul, zero_add]

/-- In characteristic two, the polar bilinear form of `binaryQuadraticForm R a b` coincides with
that of the hyperbolic plane `binaryQuadraticForm R 0 0`. -/
theorem polarBilin_binaryQuadraticForm_of_charTwo [CharP R 2] (a b : R) :
    (binaryQuadraticForm R a b).polarBilin = (binaryQuadraticForm R 0 0).polarBilin :=
  polarBilin_binaryQuadraticForm_of_two_mul_eq_zero
    (by rw [CharTwo.two_eq_zero, zero_mul]) (by rw [CharTwo.two_eq_zero, zero_mul])

/-- In characteristic two, `binaryQuadraticForm R a b` has nondegenerate polar bilinear form for all
`a, b : R`. -/
@[simp]
theorem nondegenerate_polarBilin_binaryQuadraticForm [CharP R 2] (a b : R) :
    (binaryQuadraticForm R a b).polarBilin.Nondegenerate :=
  nondegenerate_polarBilin_binaryQuadraticForm_of_two_mul_eq_zero
    (by rw [CharTwo.two_eq_zero, zero_mul]) (by rw [CharTwo.two_eq_zero, zero_mul])

/-- In characteristic two, the first coordinate axis `R ∙ ![1, 0]` equals its own
`(binaryQuadraticForm R a b).polarBilin`-orthogonal complement. -/
theorem orthogonal_polarBilin_binaryQuadraticForm_span_one_zero [CharP R 2] (a b : R) :
    LinearMap.BilinForm.orthogonal (binaryQuadraticForm R a b).polarBilin (R ∙ ![(1 : R), 0]) =
      R ∙ ![(1 : R), 0] := by
  ext x
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_span_singleton,
    forall_exists_index, forall_apply_eq_imp_iff, QuadraticMap.polarBilin_apply_apply,
    polar_binaryQuadraticForm_of_charTwo]
  refine ⟨fun hx ↦ ⟨x 0, ?_⟩, ?_⟩
  · have h1 : x 1 = 0 := by simpa using hx 1
    ext i
    fin_cases i <;> simp [h1]
  · rintro ⟨c, rfl⟩ d
    simp

/-- In characteristic two, the orthogonal sum of two copies of `binaryQuadraticForm R 1 1` is
explicitly isometric to the orthogonal sum of two hyperbolic planes
`binaryQuadraticForm R 0 0`. -/
def isometryEquivBinaryQuadraticFormOneProd [CharP R 2] :
    ((binaryQuadraticForm R 1 1).prod (binaryQuadraticForm R 1 1)).IsometryEquiv
      ((binaryQuadraticForm R 0 0).prod (binaryQuadraticForm R 0 0)) where
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
    simp only [QuadraticMap.prod_apply, binaryQuadraticForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination
      (p.1 0 * p.1 1 + p.1 0 * p.2 0 + p.1 0 * p.2 1 + p.1 1 * p.2 0 + p.1 1 * p.2 1) *
        CharTwo.two_eq_zero (R := R)

/-- Coordinates of `TauCeti.isometryEquivBinaryQuadraticFormOneProd`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormOneProd_apply [CharP R 2]
    (p : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivBinaryQuadraticFormOneProd p = (![p.1 0 + p.2 1, p.1 1 + p.2 1],
      ![p.2 0 + p.1 0 + p.1 1, p.2 1 + p.2 0 + p.1 0 + p.1 1]) :=
  (rfl)

/-- Coordinates of the inverse of `TauCeti.isometryEquivBinaryQuadraticFormOneProd`. -/
@[simp]
theorem isometryEquivBinaryQuadraticFormOneProd_symm_apply [CharP R 2]
    (q : (Fin 2 → R) × (Fin 2 → R)) :
    isometryEquivBinaryQuadraticFormOneProd.symm q =
      (![q.1 0 + q.2 0 + q.2 1, q.1 1 + q.2 0 + q.2 1],
        ![q.1 0 + q.1 1 + q.2 0, q.2 0 + q.2 1]) :=
  (rfl)

end CommRing

/-- Over a field of characteristic two, `binaryQuadraticForm K 1 a` is isotropic if and only if
`a` lies in the image `℘ K = {x ^ 2 + x}` of the Artin--Schreier map. -/
theorem not_anisotropic_binaryQuadraticForm_one_iff {K : Type u} [Field K] [CharP K 2] (a : K) :
    ¬(binaryQuadraticForm K 1 a).Anisotropic ↔ ∃ x, x ^ 2 + x = a := by
  simp [anisotropic_binaryQuadraticForm_one_iff, ← CharTwo.sub_eq_add, sub_eq_zero]

end TauCeti

/-! ### Symplectic-basis decomposition and characteristic-two quadratic Lagrangians -/

namespace QuadraticMap

open TauCeti

section SymplecticDecomposition

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In characteristic two, the matrix of `Q.polarBilin` in a basis `b` indexed by `ι ⊕ ι` is
`Matrix.J ι R` if and only if each half is polar-isotropic and `b (Sum.inl i)` pairs with
`b (Sum.inr j)` by the Kronecker delta. Because `-1 = 1` in `R`, both off-diagonal blocks of
`Matrix.J` are the identity matrix. -/
theorem toMatrix_polarBilin_eq_J_iff [CharP R 2] (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R ↔
      (∀ i j, polar Q (b (.inl i)) (b (.inl j)) = 0) ∧
      (∀ i j, polar Q (b (.inr i)) (b (.inr j)) = 0) ∧
      (∀ i j, polar Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0) := by
  refine ⟨fun hb ↦ ?_, ?_⟩
  · have hentry (x y : ι ⊕ ι) : polar Q (b x) (b y) = Matrix.J ι R x y := by
      simpa [LinearMap.BilinForm.toMatrix_apply] using congrFun₂ hb x y
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
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

/-- In a basis `b : Module.Basis (ι ⊕ ι) R M` in which `Q.polarBilin` has matrix `Matrix.J ι R`,
`Q v` expands as the sum over `i : ι` of the binary quadratic forms
`[Q (b (inl i)), Q (b (inr i))]` on the `i`-th coordinates. -/
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
`Matrix.J ι R` decomposes `Q` isometrically into the orthogonal sum of the binary quadratic forms
`binaryQuadraticForm R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))`. -/
noncomputable def isometryEquivPiBinaryQuadraticForm (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) :
    Q.IsometryEquiv
      (QuadraticMap.pi fun i : ι ↦
        binaryQuadraticForm R (Q (b (Sum.inl i))) (Q (b (Sum.inr i)))) where
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
    simp [binaryQuadraticForm_apply]

/-- Coordinates of `QuadraticMap.isometryEquivPiBinaryQuadraticForm`. -/
@[simp]
theorem isometryEquivPiBinaryQuadraticForm_apply (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (v : M) (i : ι) :
    Q.isometryEquivPiBinaryQuadraticForm b hb v i =
      ![b.repr v (Sum.inl i), b.repr v (Sum.inr i)] :=
  (rfl)

/-- Inverse of `QuadraticMap.isometryEquivPiBinaryQuadraticForm`. -/
@[simp]
theorem isometryEquivPiBinaryQuadraticForm_symm_apply (Q : QuadraticForm R M)
    (b : Module.Basis (ι ⊕ ι) R M)
    (hb : LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J ι R) (c : ι → Fin 2 → R) :
    (Q.isometryEquivPiBinaryQuadraticForm b hb).symm c =
      b.equivFun.symm (Sum.elim (fun i ↦ c i 0) (fun i ↦ c i 1)) :=
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

/-- Over a field of characteristic two, a finite-dimensional quadratic space of dimension `2 * m`
with nondegenerate polar form admits a symplectic basis `b : Module.Basis (Fin m ⊕ Fin m) K V`. -/
theorem exists_basis_toMatrix_polarBilin_eq_J_of_finrank_eq {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {m : ℕ} (hdim : Module.finrank K V = 2 * m) :
    ∃ b : Module.Basis (Fin m ⊕ Fin m) K V,
      LinearMap.BilinForm.toMatrix b Q.polarBilin = Matrix.J (Fin m) K := by
  obtain ⟨k, b, hb⟩ := Q.exists_basis_toMatrix_polarBilin_eq_J hQ
  have hkm : k = m := by
    have hcard := Module.finrank_eq_two_mul_card_of_basis_sum b
    rw [Fintype.card_fin] at hcard
    omega
  exact hkm ▸ ⟨b, hb⟩

/-- Over a field of characteristic two, a finite-dimensional quadratic space with nondegenerate
polar form has even dimension. -/
theorem even_finrank_of_nondegenerate_polarBilin {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) : Even (Module.finrank K V) :=
  LinearMap.BilinForm.IsAlt.even_finrank Q.isAlt_polarBilin hQ

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to the orthogonal sum of `m` hyperbolic
planes `binaryQuadraticForm K 0 0` if and only if `V` contains a `Q`-totally-isotropic subspace of
dimension `m`. -/
theorem equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_finrank_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0) ↔
      ∃ U : Submodule K V, Q.IsTotallyIsotropic U ∧ Module.finrank K U = m := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨U, hU, hUm⟩ ↦ ?_⟩
  · let f : (Fin m → K) →ₗ[K] (Fin m → Fin 2 → K) :=
      { toFun := fun c i ↦ ![c i, 0]
        map_add' := fun x y ↦ by ext i k; fin_cases k <;> simp
        map_smul' := fun r x ↦ by ext i k; fin_cases k <;> simp }
    have hf : Function.Injective f := fun x y hxy ↦ funext fun i ↦ by
      simpa [f] using congrFun (congrFun hxy i) 0
    refine ⟨(LinearMap.range f).map e.symm.toLinearMap,
      e.symm.isTotallyIsotropic_map_iff.mpr ?_, ?_⟩
    · rw [isTotallyIsotropic_iff]
      rintro _ ⟨c, rfl⟩
      simp [f]
    · rw [e.symm.toLinearEquiv.finrank_map_eq, ← (LinearEquiv.ofInjective f hf).finrank_eq,
        Module.finrank_fin_fun]
  · have hrad : Q.radical = ⊥ :=
      eq_bot_mono Q.radical_le_ker_polarBilin (LinearMap.BilinForm.Nondegenerate.ker_eq_bot hQ)
    have hU_orth : U = LinearMap.BilinForm.orthogonal Q.polarBilin U :=
      ((hU.orthogonal_polarBilin_eq_self_iff hrad).mpr (by omega)).symm
    let eU : Module.Basis (Fin m) K U := Module.finBasisOfFinrankEq K U hUm
    obtain ⟨b, hb, hbinl⟩ :=
      LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J_inl_eq Q.isAlt_polarBilin hQ eU hU_orth
    have hQinl (i : Fin m) : Q (b (Sum.inl i)) = 0 := by
      rw [hbinl i]
      exact hU.apply_eq_zero (eU i).property
    refine ⟨(Q.isometryEquivPiBinaryQuadraticForm b hb).trans
      (IsometryEquiv.pi fun i ↦ ?_)⟩
    rw [hQinl i]
    exact isometryEquivBinaryQuadraticFormRight (Q (b (Sum.inr i)))

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to `m` hyperbolic planes if and only if
`V` contains a `Q`-totally-isotropic subspace equal to its own polar orthogonal complement. -/
theorem equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_orthogonal_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0) ↔
      ∃ U : Submodule K V,
        Q.IsTotallyIsotropic U ∧ LinearMap.BilinForm.orthogonal Q.polarBilin U = U := by
  rw [equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]
  have hrad : Q.radical = ⊥ :=
    eq_bot_mono Q.radical_le_ker_polarBilin (LinearMap.BilinForm.Nondegenerate.ker_eq_bot hQ)
  refine ⟨fun ⟨U, hU, hUm⟩ ↦ ⟨U, hU, (hU.orthogonal_polarBilin_eq_self_iff hrad).mpr (by omega)⟩,
    fun ⟨U, hU, hUorth⟩ ↦ ⟨U, hU, ?_⟩⟩
  have := (hU.orthogonal_polarBilin_eq_self_iff hrad).mp hUorth
  omega

/-- Over a field of characteristic two, a finite-dimensional quadratic form `Q` with nondegenerate
polar form and `Module.finrank K V = 2 * m` is isometric to `m` hyperbolic planes if and only if
`V` contains a `Q`-totally-isotropic subspace of half the ambient dimension. -/
theorem equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_two_mul_finrank_eq
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {m : ℕ}
    (hdim : Module.finrank K V = 2 * m) :
    Q.Equivalent (QuadraticMap.pi fun _ : Fin m ↦ binaryQuadraticForm K 0 0) ↔
      ∃ U : Submodule K V, Q.IsTotallyIsotropic U ∧
        2 * Module.finrank K U = Module.finrank K V := by
  rw [equivalent_pi_binaryQuadraticForm_zero_iff_exists_isTotallyIsotropic_finrank_eq hQ hdim]
  exact ⟨fun ⟨U, hU, hUm⟩ ↦ ⟨U, hU, by omega⟩, fun ⟨U, hU, hU2⟩ ↦ ⟨U, hU, by omega⟩⟩

end CharTwoField

section EvenFinrank

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- On an even-dimensional space over a field, a quadratic form is nonsingular, that is its polar
bilinear form is nondegenerate, if and only if it is nondegenerate in the sense of
`QuadraticMap.Nondegenerate`. In characteristic two the even dimension is needed: the polar form is
alternating, so its kernel has the parity of the dimension and cannot be a line. -/
theorem nondegenerate_polar_iff_of_even_finrank {Q : QuadraticForm K V}
    (hV : Even (Module.finrank K V)) : Q.polarBilin.Nondegenerate ↔ Q.Nondegenerate := by
  refine ⟨nondegenerate_of_nondegenerate_polarBilin, fun hQ ↦ ?_⟩
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    -- A complement `W` of the polar kernel carries a nondegenerate alternating form, so it is
    -- even-dimensional, and the kernel of dimension at most one is then zero.
    obtain ⟨W, hW⟩ := (LinearMap.ker Q.polarBilin).exists_isCompl
    have hWnd : (Q.restrict W).polarBilin.Nondegenerate := by
      rw [polarBilin_restrict]
      exact Q.isSymm_polarBilin.isRefl.nondegenerate_restrict_of_isCompl_ker hW.symm
    obtain ⟨k, hk⟩ := even_finrank_of_nondegenerate_polarBilin hWnd
    obtain ⟨n, hn⟩ := hV
    have hsum := Submodule.finrank_add_eq_of_isCompl hW
    have hker : Module.finrank K (LinearMap.ker Q.polarBilin) ≤ 1 :=
      Module.finrank_le_of_rank_le (by simpa using hQ.rank_rad_polar_le)
    rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft Q.isRefl_polarBilin,
      LinearMap.separatingLeft_iff_ker_eq_bot, ← Submodule.finrank_eq_zero]
    omega
  · have := invertibleOfNonzero h2
    exact nondegenerate_polar_iff.mpr hQ

end EvenFinrank

end QuadraticMap
