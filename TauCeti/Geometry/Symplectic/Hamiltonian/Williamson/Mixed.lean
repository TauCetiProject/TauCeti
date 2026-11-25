/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.EllipticHyperbolic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.FocusFocus
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.FinCases
import TauCeti.Data.Fin.Basic
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting
import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.Geometry.Symplectic.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Commute
import TauCeti.LinearAlgebra.Eigenspace.Aeval
import TauCeti.LinearAlgebra.Eigenspace.Restrict
import TauCeti.LinearAlgebra.QuadraticForm.Basic

/-!
# Williamson's classification of nondegenerate families: mixed types

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `Q` a nondegenerate family
of quadratic forms on `V` (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`): the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra of `sp(V, ω)`. Williamson's
classification puts such a family, up to its span, into a normal form made of `k_e` elliptic,
`k_h` hyperbolic and `k_f` focus-focus blocks on the coordinate planes of one Darboux basis, with
`k_e + k_h + 2 k_f = dim V / 2`. The pure types are
`IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_eq_finrank_iff` (elliptic and
hyperbolic blocks) and `IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_four_eq_finrank_iff`
(focus-focus blocks). This file treats all three types together.

For a basis `b` of `V` indexed as a Darboux basis with `m + 2k` planes and a set `t` of the first
`m` planes, the **Williamson blocks** `TauCeti.SymplecticForm.williamsonBlocks b t` are the
elliptic block `Iᵢ = (xᵢ² + yᵢ²) / 2` on the plane `i < m` for `i ∈ t`, the hyperbolic block
`Hᵢ = xᵢ yᵢ` on the plane `i < m` for `i ∉ t`, and, for `j < k`, the focus-focus pair

`Q₁ⱼ = q p + q' p'`,  `Q₂ⱼ = q p' - q' p`

on the planes `(q, p) = (q_{m+2j}, p_{m+2j})` and `(q', p') = (q_{m+2j+1}, p_{m+2j+1})`. They
pairwise Poisson-commute in a Darboux basis
(`TauCeti.SymplecticForm.IsDarbouxBasis.quadraticPoissonBracket_williamsonBlocks`).

## Main results

* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks`:
  **Williamson's classification, mixed types.** Suppose the span of a nondegenerate family `Q`
  contains a form `P` whose Hamiltonian endomorphism `A = A_P` has `dim V / 2` eigenvalue pairs
  `±λ` counted as follows: a set `s` of distinct nonzero real eigenvalues `μ = λ²` of `A²`, each
  counting once, and a set `c` of distinct eigenvalues `a + bi` of `A` with `a, b > 0`, each
  counting twice (with `-a - bi`, `±a ∓ bi` it fills a focus-focus quadruple), so that
  `2 |s| + 4 |c| = dim V`. Then `Q` spans the Williamson blocks of some Darboux basis, with
  `|s|` elliptic or hyperbolic planes and `|c|` focus-focus pairs.
* `IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank_iff`:
  this characterizes the nondegenerate families spanning the Williamson blocks of a Darboux basis:
  conversely, the form `∑ᵢ (i + 1) Bᵢ + ∑ⱼ ((j + 1) Q₁ⱼ + Q₂ⱼ)`, `Bᵢ` the elliptic or hyperbolic
  block of the plane `i`, has such eigenvalues.

The classification of every Cartan subalgebra of `sp(V, ω)` further needs such an element in the
span of every nondegenerate family, and the invariance of the numbers of blocks of each type;
neither is proved here.

The proof splits `V` into the vectors `L` killed by a power of `p(A)`, `p = ∏_{μ ∈ s} (X² - μ)`,
and its symplectic complement `L^ω`. Since `p` is even, `L` is a symplectic subspace preserved by
the family. Each `μ ∈ s` contributes a symplectic subspace of `L` of dimension at least two, and
each `a + bi ∈ c` a symplectic subspace of `L^ω` of dimension at least four
(`TauCeti.SymplecticForm.four_le_finrank_maxGenEigenspace_aeval_focusFocusPolynomial`): the roots
`±a ± bi` of the focus-focus polynomial are neither real nor imaginary, so it is coprime to `p`.
These subspaces are pairwise `ω`-orthogonal, so counting dimensions gives
`dim L = 2 |s|` and `dim L^ω = 4 |c|`. The restrictions of the family to `L` and to `L^ω` are
nondegenerate (`IsNondegenerateQuadraticFamily.restrict_maxGenEigenspace_aeval`,
`IsNondegenerateQuadraticFamily.restrict_orthogonal`), and the elliptic–hyperbolic and
focus-focus classifications apply to them. Their Darboux bases assemble to one of `V`
(`TauCeti.SymplecticForm.IsSymplectic.exists_isDarbouxBasis_castAdd_natAdd`), in which
every `Q i` is a combination of the Williamson blocks; as these Poisson-commute, the
maximality of a nondegenerate family
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_eq_of_span_le`) gives equality of the
spans.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m k : ℕ}

/-! ### The Williamson blocks of a Darboux basis -/

/-- The **Williamson blocks** of a basis `b` of `V` indexed as a Darboux basis with `m + 2k` planes,
`qᵢ = b (i, 0)` and `pᵢ = b (i, 1)`, for a set `t` of the first `m` planes. On the plane `i < m`,
indexed by `Sum.inl i`, it is the elliptic block `Iᵢ = (xᵢ² + yᵢ²) / 2` if `i ∈ t` and the
hyperbolic block `Hᵢ = xᵢ yᵢ` if `i ∉ t`. For `j < k`, indexed by `Sum.inr (j, 0)` and
`Sum.inr (j, 1)`, it is the focus-focus pair `Q₁ⱼ = q p + q' p'` and `Q₂ⱼ = q p' - q' p` of the
planes `(q, p) = (q_{m+2j}, p_{m+2j})` and `(q', p') = (q_{m+2j+1}, p_{m+2j+1})`. -/
def williamsonBlocks (b : Basis (Fin (m + k * 2) × Fin 2) ℝ V) (t : Finset (Fin m)) :
    Fin m ⊕ Fin k × Fin 2 → QuadraticForm ℝ V :=
  Sum.elim
    (fun i ↦ if i ∈ t then elliptic b (Fin.castAdd _ i) else hyperbolic b (Fin.castAdd _ i))
    fun l ↦
      ![QuadraticMap.linMulLin (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 0)), 0))
            (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 0)), 1)) +
          QuadraticMap.linMulLin (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 1)), 0))
            (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 1)), 1)),
        QuadraticMap.linMulLin (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 0)), 0))
            (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 1)), 1)) -
          QuadraticMap.linMulLin (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 1)), 0))
            (b.coord (Fin.natAdd m (finProdFinEquiv (l.1, 0)), 1))] l.2

variable {b : Basis (Fin (m + k * 2) × Fin 2) ℝ V} {t : Finset (Fin m)}

@[simp]
theorem williamsonBlocks_inl_of_mem {i : Fin m} (hi : i ∈ t) :
    williamsonBlocks b t (Sum.inl i) = elliptic b (Fin.castAdd _ i) := by
  simp [williamsonBlocks, hi]

@[simp]
theorem williamsonBlocks_inl_of_notMem {i : Fin m} (hi : i ∉ t) :
    williamsonBlocks b t (Sum.inl i) = hyperbolic b (Fin.castAdd _ i) := by
  simp [williamsonBlocks, hi]

@[simp]
theorem williamsonBlocks_inr_zero_apply (j : Fin k) (x : V) :
    williamsonBlocks b t (Sum.inr (j, 0)) x =
      b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) x *
          b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 1) x +
        b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 0) x *
          b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 1) x := by
  simp [williamsonBlocks]

@[simp]
theorem williamsonBlocks_inr_one_apply (j : Fin k) (x : V) :
    williamsonBlocks b t (Sum.inr (j, 1)) x =
      b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) x *
          b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 1) x -
        b.coord (Fin.natAdd m (finProdFinEquiv (j, 1)), 0) x *
          b.coord (Fin.natAdd m (finProdFinEquiv (j, 0)), 1) x := by
  simp [williamsonBlocks]

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V}

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic or hyperbolic block on the
plane `i < m` sends `qᵢ` to `-pᵢ` if the block is elliptic and to `qᵢ` if it is hyperbolic, and
the other `qⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inl_apply_fst (hb : ω.IsDarbouxBasis b)
    (i : Fin m) (j : Fin (m + k * 2)) :
    ω.hamiltonianEnd (williamsonBlocks b t (Sum.inl i)) (b (j, 0)) =
      if j = Fin.castAdd _ i then
        (if i ∈ t then -b (Fin.castAdd _ i, 1) else b (Fin.castAdd _ i, 0)) else 0 := by
  by_cases hi : i ∈ t
  · simp [hi, hb.hamiltonianEnd_elliptic_apply_fst]
  · simp [hi, hb.hamiltonianEnd_hyperbolic_apply_fst]

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic or hyperbolic block on the
plane `i < m` sends `pᵢ` to `qᵢ` if the block is elliptic and to `-pᵢ` if it is hyperbolic, and
the other `pⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inl_apply_snd (hb : ω.IsDarbouxBasis b)
    (i : Fin m) (j : Fin (m + k * 2)) :
    ω.hamiltonianEnd (williamsonBlocks b t (Sum.inl i)) (b (j, 1)) =
      if j = Fin.castAdd _ i then
        (if i ∈ t then b (Fin.castAdd _ i, 0) else -b (Fin.castAdd _ i, 1)) else 0 := by
  by_cases hi : i ∈ t
  · simp [hi, hb.hamiltonianEnd_elliptic_apply_snd]
  · simp [hi, hb.hamiltonianEnd_hyperbolic_apply_snd]

/-- In a Darboux basis, the Hamiltonian endomorphisms of the focus-focus blocks kill the first `m`
planes. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd
    (hb : ω.IsDarbouxBasis b) (l : Fin k × Fin 2) (i : Fin m) (c : Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (Sum.inr l)) (b (Fin.castAdd _ i, c)) = 0 := by
  obtain ⟨j, l⟩ := l
  have h (p : Fin (k * 2)) (c' : Fin 2) :
      b.coord (Fin.natAdd m p, c') (b (Fin.castAdd _ i, c)) = 0 := by
    simp
  fin_cases l <;>
    simp [williamsonBlocks, hb.hamiltonianEnd_linMulLin_coord_apply, h]

/-- In a Darboux basis, the Hamiltonian endomorphism of the first form `Q₁ⱼ` of the `j`-th
focus-focus block fixes the `q`'s of that block, negates its `p`'s and kills the other focus-focus
blocks. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inr_zero_apply_natAdd
    (hb : ω.IsDarbouxBasis b) (j j' : Fin k) (i c : Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (Sum.inr (j, 0)))
        (b (Fin.natAdd m (finProdFinEquiv (j', i)), c)) =
      if j' = j then (if c = 0 then b (Fin.natAdd m (finProdFinEquiv (j', i)), c)
        else -b (Fin.natAdd m (finProdFinEquiv (j', i)), c)) else 0 := by
  simp only [williamsonBlocks, Sum.elim_inr, Matrix.cons_val_zero, map_add,
    hb.hamiltonianEnd_linMulLin_coord_apply, LinearMap.add_apply]
  by_cases hj : j' = j
  · subst hj
    fin_cases i <;> fin_cases c <;> simp [Fin.natAdd_inj]
  · simp [hj, Ne.symm hj, Fin.natAdd_inj]

/-- In a Darboux basis, the Hamiltonian endomorphism of the second form `Q₂ⱼ` of the `j`-th
focus-focus block sends `q ↦ q' ↦ -q` and `p ↦ p' ↦ -p` on the planes `(q, p)` and `(q', p')` of
that block, and kills the other focus-focus blocks. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inr_one_apply_natAdd
    (hb : ω.IsDarbouxBasis b) (j j' : Fin k) (i c : Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (Sum.inr (j, 1)))
        (b (Fin.natAdd m (finProdFinEquiv (j', i)), c)) =
      if j' = j then (if i = 0 then b (Fin.natAdd m (finProdFinEquiv (j', 1)), c)
        else -b (Fin.natAdd m (finProdFinEquiv (j', 0)), c)) else 0 := by
  simp only [williamsonBlocks, Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero, map_sub,
    hb.hamiltonianEnd_linMulLin_coord_apply, LinearMap.sub_apply]
  by_cases hj : j' = j
  · subst hj
    fin_cases i <;> fin_cases c <;> simp [Fin.natAdd_inj]
  · simp [hj, Ne.symm hj, Fin.natAdd_inj]

/-- In a Darboux basis, the Williamson blocks pairwise Poisson-commute. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_williamsonBlocks (hb : ω.IsDarbouxBasis b)
    (x y : Fin m ⊕ Fin k × Fin 2) :
    ω.quadraticPoissonBracket (williamsonBlocks b t x) (williamsonBlocks b t y) = 0 := by
  rw [quadraticPoissonBracket_eq_zero_iff, Commute, SemiconjBy]
  refine b.ext fun ⟨n, c⟩ ↦ ?_
  simp only [mul_apply_eq_comp]
  induction n using Fin.addCases with
  | left i =>
    rcases x with i₁ | l₁ <;> rcases y with i₂ | l₂ <;> fin_cases c <;>
      simp only [Fin.zero_eta, Fin.mk_one, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
        hb.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd] <;>
      (try split_ifs) <;>
      simp_all [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
        hb.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd]
  | right p =>
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective p
    rcases x with i₁ | ⟨j₁, l₁⟩ <;> rcases y with i₂ | ⟨j₂, l₂⟩
    · fin_cases c <;>
        simp [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]
    all_goals
      fin_cases i <;> fin_cases c <;> (try fin_cases l₁) <;> (try fin_cases l₂) <;>
      simp only [Fin.zero_eta, Fin.mk_one, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
        hb.hamiltonianEnd_williamsonBlocks_inr_zero_apply_natAdd,
        hb.hamiltonianEnd_williamsonBlocks_inr_one_apply_natAdd, Fin.natAdd_ne_castAdd,
        ite_false] <;>
      split_ifs <;>
      simp_all [hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
        hb.hamiltonianEnd_williamsonBlocks_inr_zero_apply_natAdd,
        hb.hamiltonianEnd_williamsonBlocks_inr_one_apply_natAdd]

/-! ### Dimension counts -/

/-- If pairwise `ω`-orthogonal symplectic subspaces `G j` of `L` all have dimension at least `d`,
then `L` has dimension at least `d` times their number. -/
private theorem card_mul_le_finrank {κ : Type*} [Fintype κ] {G : κ → Submodule ℝ V}
    (hG : ∀ j, ω.IsSymplectic (G j)) (horth : Pairwise fun j j' ↦ ∀ v ∈ G j, ∀ w ∈ G j', ω v w = 0)
    {L : Submodule ℝ V} (hL : ∀ j, G j ≤ L) {d : ℕ} (hd : ∀ j, d ≤ finrank ℝ (G j)) :
    Fintype.card κ * d ≤ finrank ℝ L :=
  calc Fintype.card κ * d = ∑ _j : κ, d := by simp [mul_comm]
    _ ≤ ∑ j, finrank ℝ (G j) := Finset.sum_le_sum fun j _ ↦ hd j
    _ ≤ finrank ℝ L := sum_finrank_le_finrank_of_pairwise_apply_eq_zero hG horth hL

/-- `X² - μ` is coprime to the focus-focus polynomial of `a + bi` for `a, b ≠ 0`: the roots
`±a ± bi` of the latter have squares with nonzero imaginary part `±2ab`. -/
private theorem isCoprime_X_sq_sub_C_focusFocusPolynomial (μ : ℝ) {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) : IsCoprime (X ^ 2 - C μ) (focusFocusPolynomial a b) := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun w ↦ ?_
  by_contra! hw
  obtain ⟨h₁, h₂⟩ := abs_re_eq_and_abs_im_eq_of_aeval_focusFocusPolynomial_eq_zero hb hw.2
  have hw₁ : w ^ 2 = μ := by
    have := hw.1
    simp only [map_sub, map_pow, aeval_X, aeval_C, Complex.coe_algebraMap] at this
    exact sub_eq_zero.1 this
  have him := congrArg Complex.im hw₁
  simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at him
  have hre : w.re ≠ 0 := by
    rintro h0
    rw [h0, abs_zero] at h₁
    exact ha (abs_eq_zero.1 h₁.symm)
  have hre' : w.im ≠ 0 := by
    rintro h0
    rw [h0, abs_zero] at h₂
    exact hb (abs_eq_zero.1 h₂.symm)
  exact mul_ne_zero hre hre' (by linarith)

/-- The polynomial `∏_{μ ∈ s} (X² - μ)` is even. -/
private theorem prod_X_sq_sub_C_comp_neg_X (s : Finset ℝ) :
    (∏ μ ∈ s, (X ^ 2 - C μ)).comp (-X) = ∏ μ ∈ s, (X ^ 2 - C μ) := by
  simp only [prod_comp, comp_neg_X_sq_sub_C]

omit [FiniteDimensional ℝ V] in
/-- For `A ∈ sp(V, ω)` and `a, b ≠ 0`, the focus-focus block of `A` for `a + bi` is `ω`-orthogonal
to the vectors killed by a power of `∏_{μ ∈ s} (A² - μ)`. -/
private theorem maxGenEigenspace_aeval_focusFocusPolynomial_le_orthogonal {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (s : Finset ℝ) {a b : ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    (aeval A (focusFocusPolynomial a b)).maxGenEigenspace 0 ≤
      ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0) := fun _ hv ↦
  mem_orthogonal_iff.2 fun _ hy ↦
    ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval
      (by
        rw [focusFocusPolynomial_comp_neg_X]
        exact IsCoprime.prod_left fun μ _ ↦ isCoprime_X_sq_sub_C_focusFocusPolynomial μ ha hb)
      hy hv

/-- **The dimension count.** Let `A ∈ sp(V, ω)` have distinct nonzero real
eigenvalues `μ ∈ s` of `A²` and distinct eigenvalues `a + bi ∈ c` with `a, b > 0`, where
`2 |s| + 4 |c| = dim V`. Then the vectors killed by a power of `∏_{μ ∈ s} (A² - μ)` form a subspace
of dimension `2 |s|`, and its symplectic complement has dimension `4 |c|`. -/
private theorem finrank_maxGenEigenspace_aeval_prod_eq {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    {c : Finset ℂ} (hsc : s.card * 2 + c.card * 4 = finrank ℝ V)
    (hs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) (hc0 : ∀ z ∈ c, 0 < z.re ∧ 0 < z.im)
    (hc : ∀ z ∈ c, ∃ v w : V, v ≠ 0 ∧ A v = z.re • v - z.im • w ∧ A w = z.im • v + z.re • w) :
    finrank ℝ ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0) = s.card * 2 ∧
      finrank ℝ (ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0)) =
        c.card * 4 := by
  set L := (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0
  -- Each `μ ∈ s` contributes a symplectic subspace of `L` of dimension at least two.
  have hsL : s.card * 2 ≤ finrank ℝ L := by
    have h2 (μ : s) : 2 ≤ finrank ℝ ((aeval A (X ^ 2 - C (μ : ℝ))).maxGenEigenspace 0) := by
      obtain ⟨v, hv⟩ := (hs μ μ.property).exists_hasEigenvector
      exact (isSymplectic_maxGenEigenspace_sq_sub hA _).two_le_finrank
        (mem_maxGenEigenspace_sq_sub (by simpa [sq] using hv.apply_eq_smul)) hv.2
    have hle (μ : s) : (aeval A (X ^ 2 - C (μ : ℝ))).maxGenEigenspace 0 ≤ L :=
      Module.End.maxGenEigenspace_aeval_le_of_dvd A
        (Finset.dvd_prod_of_mem (fun ν : ℝ ↦ X ^ 2 - C ν) μ.property)
    have := card_mul_le_finrank (fun μ : s ↦ isSymplectic_maxGenEigenspace_sq_sub hA μ)
      (fun μ ν hμν _ hv _ hw ↦ apply_eq_zero_of_mem_maxGenEigenspace_sq_sub hA
        (fun h ↦ hμν (Subtype.ext h)) hv hw) hle h2
    rwa [Fintype.card_coe] at this
  -- Each `a + bi ∈ c` contributes a symplectic subspace of `L^ω` of dimension at least four.
  have hcL' : c.card * 4 ≤ finrank ℝ (ω.orthogonal L) := by
    have h4 (z : c) : 4 ≤ finrank ℝ
        ((aeval A (focusFocusPolynomial (z : ℂ).re (z : ℂ).im)).maxGenEigenspace 0) := by
      obtain ⟨v, w, hv, hAv, hAw⟩ := hc z z.property
      exact four_le_finrank_maxGenEigenspace_aeval_focusFocusPolynomial hA
        (hc0 z z.property).1.ne' (hc0 z z.property).2.ne' hv hAv hAw
    have horth : Pairwise fun z z' : c ↦
        ∀ v ∈ (aeval A (focusFocusPolynomial (z : ℂ).re (z : ℂ).im)).maxGenEigenspace 0,
          ∀ w ∈ (aeval A (focusFocusPolynomial (z' : ℂ).re (z' : ℂ).im)).maxGenEigenspace 0,
            ω v w = 0 := fun z z' hzz' _ hv _ hw ↦
      ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval
        (isCoprime_focusFocusPolynomial (hc0 z z.property).1 (hc0 z z.property).2
          (hc0 z' z'.property).1 (hc0 z' z'.property).2 (by
            by_contra! hh
            exact hzz' (Subtype.ext (Complex.ext hh.1 hh.2)))) hv hw
    have := card_mul_le_finrank
      (fun _ ↦ ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPolynomial_comp_neg_X _ _))
      horth (fun z ↦ maxGenEigenspace_aeval_focusFocusPolynomial_le_orthogonal hA s
        (hc0 z z.property).1.ne' (hc0 z z.property).2.ne') h4
    rwa [Fintype.card_coe] at this
  have := ω.finrank_add_finrank_orthogonal L
  exact ⟨by omega, by omega⟩

/-! ### Assembling the two summands -/

/-- **Combinations of the Williamson blocks.** Let `b` be the Darboux basis of `V` assembled from
Darboux bases `b₁` of a symplectic subspace `L` and `b₂` of `L^ω`. A quadratic form `R` whose
Hamiltonian endomorphism preserves `L`, whose restriction to `L` lies in the span of the
elliptic–hyperbolic blocks of `b₁` and whose restriction to `L^ω` lies in the span of the
focus-focus blocks of `b₂`, lies in the span of the Williamson blocks of `b`. -/
private theorem mem_span_williamsonBlocks {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    {b₁ : Basis (Fin m × Fin 2) ℝ L}
    (hb₁ : (ω.restrict L hL.nondegenerate_restrict).IsDarbouxBasis b₁)
    {b₂ : Basis (Fin (k * 2) × Fin 2) ℝ (ω.orthogonal L)}
    (hb₂ : (ω.restrict _ hL.orthogonal.nondegenerate_restrict).IsDarbouxBasis b₂)
    (hb : ω.IsDarbouxBasis b) (hb1 : ∀ i a, b (Fin.castAdd _ i, a) = b₁ (i, a))
    (hb2 : ∀ i a, b (Fin.natAdd m i, a) = b₂ (i, a)) {R : QuadraticForm ℝ V}
    (hRL : ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L)
    (hR₁ : R.comp L.subtype ∈ Submodule.span ℝ (Set.range (ellipticHyperbolic b₁ t)))
    (hR₂ : R.comp (ω.orthogonal L).subtype ∈
      Submodule.span ℝ (Set.range (focusFocusBlocks b₂))) :
    R ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hR₁
  obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hR₂
  -- Both sides have the same Hamiltonian endomorphism, as they agree on the basis `b`.
  have hR : R = ∑ j, d j • williamsonBlocks b t (Sum.inl j) +
      ∑ l, e l • williamsonBlocks b t (Sum.inr l) := by
    refine ω.hamiltonianEnd_injective (b.ext fun ⟨n, a⟩ ↦ ?_)
    induction n using Fin.addCases with
    | left j' =>
      have hL₁ : ω.hamiltonianEnd R (b (Fin.castAdd _ j', a)) =
          ((ω.restrict L hL.nondegenerate_restrict).hamiltonianEnd (R.comp L.subtype)
            (b₁ (j', a)) : V) := by
        rw [hamiltonianEnd_comp_subtype hL hRL, LinearMap.coe_restrict_apply, hb1]
      rw [hL₁, ← hd]
      fin_cases a <;>
        simp only [Fin.zero_eta, Fin.mk_one, map_add, map_sum, map_smul, LinearMap.add_apply,
          LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
          hb₁.hamiltonianEnd_ellipticHyperbolic_apply_fst,
          hb₁.hamiltonianEnd_ellipticHyperbolic_apply_snd,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
          hb.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd] <;>
        by_cases hj : j' ∈ t <;> simp [hb1, hj, apply_ite, (Fin.castAdd_injective _ _).eq_iff]
    | right p =>
      obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective p
      have hRL' : ∀ v ∈ ω.orthogonal L, ω.hamiltonianEnd R v ∈ ω.orthogonal L :=
        (Module.End.mem_invtSubmodule _).1
          (orthogonal_mem_invtSubmodule (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra R)
            ((Module.End.mem_invtSubmodule _).2 hRL))
      have hL₂ : ω.hamiltonianEnd R (b (Fin.natAdd m (finProdFinEquiv (j', i')), a)) =
          ((ω.restrict _ hL.orthogonal.nondegenerate_restrict).hamiltonianEnd
            (R.comp (ω.orthogonal L).subtype) (b₂ (finProdFinEquiv (j', i'), a)) : V) := by
        rw [hamiltonianEnd_comp_subtype hL.orthogonal hRL', LinearMap.coe_restrict_apply,
          hb2]
      rw [hL₂, ← he]
      fin_cases i' <;> fin_cases a <;>
        simp only [Fin.zero_eta, Fin.mk_one, map_add, map_sum, map_smul, LinearMap.add_apply,
          LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
          Submodule.coe_add, Fintype.sum_prod_type, Fin.sum_univ_two,
          hb₂.hamiltonianEnd_focusFocusBlocks_zero_apply,
          hb₂.hamiltonianEnd_focusFocusBlocks_one_apply,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
          hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
          hb.hamiltonianEnd_williamsonBlocks_inr_zero_apply_natAdd,
          hb.hamiltonianEnd_williamsonBlocks_inr_one_apply_natAdd, Fin.natAdd_ne_castAdd] <;>
        simp [hb2, apply_ite ((↑) : ω.orthogonal L → V), smul_ite, Finset.sum_add_distrib]
  rw [hR]
  exact add_mem (Submodule.sum_mem _ fun j _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩))
    (Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr l, rfl⟩))

/-! ### Williamson's classification -/

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's classification, mixed types.** Let `Q` be a nondegenerate family of quadratic
forms on `V`, and suppose that its span contains a form `P` whose Hamiltonian endomorphism `A_P`
has the following eigenvalues: the distinct nonzero real eigenvalues `μ ∈ s` of `A_P²`, and the
distinct eigenvalues `z = a + bi ∈ c` with `a, b > 0`, recorded as vectors `v ≠ 0` and `w` with
`A_P v = a v - b w` and `A_P w = b v + a w`, with `2 |s| + 4 |c| = dim V`. Then the span of `Q` is
the span of the Williamson blocks of some Darboux basis: elliptic or hyperbolic blocks on `m = |s|`
planes and focus-focus pairs on `k = |c|` pairs of planes. -/
theorem exists_isDarbouxBasis_span_eq_span_williamsonBlocks
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s : Finset ℝ} {c : Finset ℂ}
    (hsc : s.card * 2 + c.card * 4 = finrank ℝ V) (hs0 : (0 : ℝ) ∉ s)
    (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ)
    (hc0 : ∀ z ∈ c, 0 < z.re ∧ 0 < z.im)
    (hPc : ∀ z ∈ c, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
      ω.hamiltonianEnd P w = z.im • v + z.re • w) :
    ∃ (m k : ℕ) (b : Basis (Fin (m + k * 2) × Fin 2) ℝ V) (t : Finset (Fin m)),
      m = s.card ∧ k = c.card ∧ ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  set A := ω.hamiltonianEnd P
  have hA := ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  -- `L`: the vectors killed by a power of `∏_{μ ∈ s} (A² - μ)`; it has dimension `2 |s|`.
  set L := (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0
  have hL : ω.IsSymplectic L :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (prod_X_sq_sub_C_comp_neg_X s)
  have hRL {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
      ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L := fun _ hv ↦
    Module.End.mapsTo_genEigenspace_aeval_of_comm (ω.quadraticPoissonBracket_eq_zero_iff.1
      (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hP hR))
      _ 0 ⊤ hv
  obtain ⟨hLs, hL'c⟩ : finrank ℝ L = s.card * 2 ∧ finrank ℝ (ω.orthogonal L) = c.card * 4 :=
    finrank_maxGenEigenspace_aeval_prod_eq hA hsc hPs hc0 hPc
  -- The elliptic–hyperbolic classification on `L`.
  obtain ⟨m, b₁, t, hb₁, hspan₁⟩ : ∃ (m : ℕ) (b₁ : Basis (Fin m × Fin 2) ℝ L)
      (t : Finset (Fin m)), (ω.restrict L hL.nondegenerate_restrict).IsDarbouxBasis b₁ ∧
        Submodule.span ℝ (Set.range fun i ↦ (Q i).comp L.subtype) =
          Submodule.span ℝ (Set.range (ellipticHyperbolic b₁ t)) :=
    exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic
      (h.restrict_maxGenEigenspace_aeval hP (prod_X_sq_sub_C_comp_neg_X s))
      (QuadraticMap.comp_mem_span_range_comp hP L.subtype) hLs.symm hs0 fun μ hμ ↦ by
        obtain ⟨v, hv⟩ := (hPs μ hμ).exists_hasEigenvector
        rw [hamiltonianEnd_comp_subtype hL (hRL hP), Module.End.pow_restrict]
        exact Module.End.hasEigenvalue_restrict _ (Module.End.maxGenEigenspace_aeval_le_of_dvd A
          (Finset.dvd_prod_of_mem (fun ν : ℝ ↦ X ^ 2 - C ν) hμ)
          (mem_maxGenEigenspace_sq_sub (by simpa [sq] using hv.apply_eq_smul))) hv
  -- The focus-focus classification on `L^ω`.
  obtain ⟨k, b₂, hb₂, hspan₂⟩ : ∃ (k : ℕ) (b₂ : Basis (Fin (k * 2) × Fin 2) ℝ (ω.orthogonal L)),
      (ω.restrict _ hL.orthogonal.nondegenerate_restrict).IsDarbouxBasis b₂ ∧
        Submodule.span ℝ (Set.range fun i ↦ (Q i).comp (ω.orthogonal L).subtype) =
          Submodule.span ℝ (Set.range (focusFocusBlocks b₂)) :=
    (h.restrict_orthogonal hL fun i ↦ (Module.End.mem_invtSubmodule _).2 fun v hv ↦
      hRL (Submodule.subset_span ⟨i, rfl⟩) v hv).exists_isDarbouxBasis_span_eq_span_focusFocusBlocks
      (QuadraticMap.comp_mem_span_range_comp hP _) hL'c.symm hc0 fun z hz ↦ by
        obtain ⟨v, w, hv, hAv, hAw⟩ := hPc z hz
        rw [hamiltonianEnd_comp_subtype hL.orthogonal ((Module.End.mem_invtSubmodule _).1
          (orthogonal_mem_invtSubmodule (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra _)
            ((Module.End.mem_invtSubmodule _).2 (hRL hP))))]
        exact Module.End.exists_restrict_apply_eq _ (hc0 z hz).2.ne'
          (maxGenEigenspace_aeval_focusFocusPolynomial_le_orthogonal hA s (hc0 z hz).1.ne'
            (hc0 z hz).2.ne' ((Module.End.mem_maxGenEigenspace _ _ _).2
              ⟨1, by simpa using aeval_focusFocusPolynomial_apply_eq_zero hAv hAw⟩)) hv hAv hAw
  -- Every `Q i` is a combination of the assembled Williamson blocks, which Poisson-commute.
  obtain ⟨b, hb, hb1, hb2⟩ := hL.exists_isDarbouxBasis_castAdd_natAdd hb₁ hb₂
  obtain ⟨hm, hk⟩ := And.intro (finrank_eq_card_basis b₁) (finrank_eq_card_basis b₂)
  simp only [Fintype.card_prod, Fintype.card_fin] at hm hk
  refine ⟨m, k, b, t, by omega, by omega, hb, h.span_eq_of_span_le
    hb.quadraticPoissonBracket_williamsonBlocks (Submodule.span_le.2 (Set.range_subset_iff.2 fun i ↦
      mem_span_williamsonBlocks hL hb₁ hb₂ hb hb1 hb2 (hRL (Submodule.subset_span ⟨i, rfl⟩))
        (hspan₁ ▸ Submodule.subset_span ⟨i, rfl⟩) (hspan₂ ▸ Submodule.subset_span ⟨i, rfl⟩)))⟩

end IsNondegenerateQuadraticFamily

/-! ### The converse: a regular element -/

variable (b t) in
/-- The form `∑ᵢ (i + 1) Bᵢ + ∑ⱼ ((j + 1) Q₁ⱼ + Q₂ⱼ)` in the span of the Williamson blocks,
`Bᵢ` the elliptic or hyperbolic block of the plane `i < m`. -/
private def williamsonRegular : QuadraticForm ℝ V :=
  ∑ i : Fin m, (((i : ℕ) : ℝ) + 1) • williamsonBlocks b t (Sum.inl i) +
    ∑ j : Fin k, ((((j : ℕ) : ℝ) + 1) • williamsonBlocks b t (Sum.inr (j, 0)) +
      williamsonBlocks b t (Sum.inr (j, 1)))

omit [FiniteDimensional ℝ V] in
private theorem williamsonRegular_mem_span :
    williamsonRegular b t ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) :=
  add_mem (Submodule.sum_mem _ fun _ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun _ _ ↦ add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩))

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_castAdd_fst
    (hb : ω.IsDarbouxBasis b) (i : Fin m) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.castAdd _ i, 0)) =
      (((i : ℕ) : ℝ) + 1) •
        (if i ∈ t then -b (Fin.castAdd _ i, 1) else b (Fin.castAdd _ i, 0)) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
    hb.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd, smul_ite,
    (Fin.castAdd_injective _ _).eq_iff]

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_castAdd_snd
    (hb : ω.IsDarbouxBasis b) (i : Fin m) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.castAdd _ i, 1)) =
      (((i : ℕ) : ℝ) + 1) •
        (if i ∈ t then b (Fin.castAdd _ i, 0) else -b (Fin.castAdd _ i, 1)) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
    hb.hamiltonianEnd_williamsonBlocks_inr_apply_castAdd, smul_ite,
    (Fin.castAdd_injective _ _).eq_iff]

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_natAdd
    (hb : ω.IsDarbouxBasis b) (j : Fin k) (i : Fin 2) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.natAdd m (finProdFinEquiv (j, i)), 0)) =
      (((j : ℕ) : ℝ) + 1) • b (Fin.natAdd m (finProdFinEquiv (j, i)), 0) +
        if i = 0 then b (Fin.natAdd m (finProdFinEquiv (j, 1)), 0)
        else -b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
    hb.hamiltonianEnd_williamsonBlocks_inr_zero_apply_natAdd,
    hb.hamiltonianEnd_williamsonBlocks_inr_one_apply_natAdd, smul_ite, Finset.sum_add_distrib]

/-- In a Darboux basis, the square of the Hamiltonian endomorphism of the regular element has the
eigenvalue `-(i + 1)²` if the plane `i < m` is elliptic and `(i + 1)²` if it is hyperbolic. -/
private theorem IsDarbouxBasis.hasEigenvalue_hamiltonianEnd_williamsonRegular_sq
    (hb : ω.IsDarbouxBasis b) (i : Fin m) :
    (ω.hamiltonianEnd (williamsonRegular b t) ^ 2).HasEigenvalue
      (if i ∈ t then -((((i : ℕ) : ℝ) + 1) ^ 2) else (((i : ℕ) : ℝ) + 1) ^ 2) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := b (Fin.castAdd _ i, 0))
    ⟨Module.End.mem_eigenspace_iff.2 ?_, b.ne_zero _⟩
  rw [sq, mul_apply_eq_comp, hb.hamiltonianEnd_williamsonRegular_castAdd_fst]
  by_cases hit : i ∈ t <;>
    simp [hit, hb.hamiltonianEnd_williamsonRegular_castAdd_fst,
      hb.hamiltonianEnd_williamsonRegular_castAdd_snd, smul_smul, sq]

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Nondegenerate families of mixed type.** The span of a nondegenerate family `Q` contains a
form `P` whose Hamiltonian endomorphism has `|s|` distinct nonzero real eigenvalues `μ ∈ s` of
`A_P²` and `|c|` distinct eigenvalues `a + bi ∈ c` with `a, b > 0`, each with an eigenvector
`v + iw`, `v ≠ 0`, where `2 |s| + 4 |c| = dim V`, exactly when it is the span of the Williamson
blocks of some Darboux basis. -/
theorem exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank_iff
    (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ (s : Finset ℝ) (c : Finset ℂ),
        s.card * 2 + c.card * 4 = finrank ℝ V ∧ (0 : ℝ) ∉ s ∧
        (∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) ∧ (∀ z ∈ c, 0 < z.re ∧ 0 < z.im) ∧
        ∀ z ∈ c, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
          ω.hamiltonianEnd P w = z.im • v + z.re • w) ↔
      ∃ (m k : ℕ) (b : Basis (Fin (m + k * 2) × Fin 2) ℝ V) (t : Finset (Fin m)),
        ω.IsDarbouxBasis b ∧
          Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  refine ⟨fun ⟨P, hP, s, c, hsc, hs0, hPs, hc0, hPc⟩ ↦
    let ⟨m, k, b, t, _, _, hb, hspan⟩ :=
      h.exists_isDarbouxBasis_span_eq_span_williamsonBlocks hP hsc hs0 hPs hc0 hPc
    ⟨m, k, b, t, hb, hspan⟩,
    fun ⟨m, k, b, t, hb, hspan⟩ ↦ ?_⟩
  -- The regular element has the eigenvalues `∓(i + 1)²` of its square and `(j + 1) + i`.
  let z : Fin k → ℂ := fun j ↦ ((((j : ℕ) : ℝ) + 1 : ℝ) : ℂ) + Complex.I
  have hz : Function.Injective z := fun j j' hjj' ↦ by
    have := congrArg Complex.re hjj'
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, add_left_inj,
      Nat.cast_inj] at this
    exact Fin.ext this
  have hmono : StrictMono fun i : Fin m ↦ (((i : ℕ) : ℝ) + 1) ^ 2 := fun i l hil ↦ by
    dsimp only
    gcongr
    exact_mod_cast hil
  have hinj : Function.Injective fun i : Fin m ↦
      if i ∈ t then -((((i : ℕ) : ℝ) + 1) ^ 2) else (((i : ℕ) : ℝ) + 1) ^ 2 :=
    injective_ite_neg_sq t (fun _ _ hil _ ↦ hmono.injective.ne hil) fun _ ↦ by positivity
  refine ⟨williamsonRegular b t, hspan ▸ williamsonRegular_mem_span,
    Finset.univ.image fun i : Fin m ↦
      if i ∈ t then -((((i : ℕ) : ℝ) + 1) ^ 2) else (((i : ℕ) : ℝ) + 1) ^ 2,
    Finset.univ.image z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj,
      Finset.card_image_of_injective _ hz, finrank_eq_card_basis b]
    simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    ring
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have := sq_pos_of_pos (by positivity : (0 : ℝ) < ((i : ℕ) : ℝ) + 1)
    by_cases hit : i ∈ t <;> simp only [hit, ↓reduceIte] at hi <;> linarith
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ i rfl
    exact hb.hasEigenvalue_hamiltonianEnd_williamsonRegular_sq i
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ j rfl
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.add_im,
      Complex.ofReal_im, Complex.I_im, zero_add, zero_lt_one, and_true]
    positivity
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ j rfl
    refine ⟨b (Fin.natAdd m (finProdFinEquiv (j, 1)), 0),
      b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0), b.ne_zero _, ?_, ?_⟩ <;>
      simp [z, hb.hamiltonianEnd_williamsonRegular_natAdd, add_comm, sub_eq_add_neg]

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
