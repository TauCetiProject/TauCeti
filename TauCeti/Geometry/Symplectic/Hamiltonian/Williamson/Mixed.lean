/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.EllipticHyperbolic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.FocusFocus
import TauCeti.Algebra.Polynomial.EvenComp
import TauCeti.Geometry.Symplectic.Darboux.Basis
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting
import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.Geometry.Symplectic.Restrict
import TauCeti.Geometry.Symplectic.Spectrum
import TauCeti.LinearAlgebra.Dimension.DirectSum
import TauCeti.LinearAlgebra.Eigenspace.Aeval
import TauCeti.LinearAlgebra.Eigenspace.Commute
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Williamson's classification of nondegenerate families: the mixed type

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. Williamson's
classification puts such a family, up to its span, into a normal form made of elliptic,
hyperbolic and focus-focus blocks on disjoint symplectic planes of a Darboux basis. The
elliptic–hyperbolic and focus-focus types are treated in
`TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.EllipticHyperbolic` and
`TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.FocusFocus`. This file combines them into the
classification of families of **mixed type**, with all three kinds of blocks.

For a basis `(q₀, p₀, …, q₂ₖ₊ₙ₋₁, p₂ₖ₊ₙ₋₁)` of `V`, indexed as a Darboux basis by
`Fin (k * 2 + n) × Fin 2`, and a set `t` of planes, the **Williamson blocks**
(`TauCeti.SymplecticForm.williamsonBlocks`) are

* on the first `2k` planes, the focus-focus pairs `q₂ⱼ p₂ⱼ + q₂ⱼ₊₁ p₂ⱼ₊₁` and
  `q₂ⱼ p₂ⱼ₊₁ - q₂ⱼ₊₁ p₂ⱼ` of the planes `2j` and `2j + 1`, for `j < k`;
* on the last `n` planes `2k + j`, the elliptic block `(x² + y²) / 2` for `j ∈ t` and the
  hyperbolic block `x y` for `j ∉ t`.

So there are `|t|` elliptic, `n - |t|` hyperbolic and `k` focus-focus blocks, with
`|t| + (n - |t|) + 2k = dim V / 2`.

The classification
(`IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks` in the
namespace `TauCeti.SymplecticForm`) starts from a regular element: a form `P` in the span
of `Q` whose Hamiltonian endomorphism `A = A_P` has `dim V` distinct eigenvalues of the three
kinds. These are recorded by a set `s'` of eigenvalues `a + bi` with `a, b > 0`, each giving the
four eigenvalues `±a ± bi`, and a set `s` of nonzero real eigenvalues `μ` of `A²`, each giving the
two eigenvalues `±√μ`, with `4 |s'| + 2 |s| = dim V`.

The proof splits `V` into its focus-focus and elliptic–hyperbolic parts and applies the two
classifications there.

* **The focus-focus part.** For `f = ∏_{a + bi ∈ s'} (X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`,
  the vectors `L` killed by a power of `f(A)` form a symplectic subspace, since `f` is even. It is
  preserved by the family, whose Hamiltonian endomorphisms commute with `A`. Its symplectic
  complement `L^ω` is the elliptic–hyperbolic part.
* **Dimensions.** The generalized eigenspaces of `A` for the factors of `f` are pairwise
  `ω`-orthogonal subspaces of `L` of dimension at least four, so `dim L ≥ 4 |s'|`. The vectors
  killed by a power of `A² - μ`, `μ ∈ s`, form nonzero symplectic subspaces, pairwise orthogonal and
  orthogonal to `L`, since `X² - μ` is coprime to `f`. So `dim L ≤ dim V - 2 |s|`, and
  `dim L = 4 |s'|`, `dim L^ω = 2 |s|`. The eigenvectors of `A` for `a + bi ∈ s'` lie in `L`, and
  those of `A²` for `μ ∈ s` in `L^ω`.
* **Assembling.** The family restricts to nondegenerate families on `L` and `L^ω`, which the
  focus-focus and elliptic–hyperbolic classifications put into normal form in Darboux bases of
  `L` and `L^ω`. Along `L × L^ω ≃ V` every form of the family is the direct sum of its
  restrictions, and the concatenated Darboux basis carries the two normal forms to the Williamson
  blocks.

## Main definitions

* `TauCeti.SymplecticForm.williamsonBlocks b t`: the Williamson normal form with focus-focus
  blocks on the first planes and elliptic and hyperbolic blocks on the others.

## Main results

* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks`:
  **Williamson's classification, mixed type.** A nondegenerate family whose span contains a regular
  element spans the Williamson blocks of some Darboux basis.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Ann. Sci. École Norm. Sup. 37 (2004), 819–839, Section 2.
-/

public section

noncomputable section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-! ### The Williamson blocks -/

section Blocks

variable {k n : ℕ} (b : Basis (Fin (k * 2 + n) × Fin 2) ℝ V) (t : Finset (Fin n))

/-- The **Williamson blocks** of a basis `(q₀, p₀, …, q₂ₖ₊ₙ₋₁, p₂ₖ₊ₙ₋₁)` of `V`, indexed as a
Darboux basis, for a set `t ⊆ Fin n`. The indices `.inl (j, 0)` and `.inl (j, 1)`, for `j < k`,
give the focus-focus pair `x₂ⱼ y₂ⱼ + x₂ⱼ₊₁ y₂ⱼ₊₁`, `x₂ⱼ y₂ⱼ₊₁ - x₂ⱼ₊₁ y₂ⱼ` of the planes `2j` and
`2j + 1`; the index `.inr j`, for `j < n`, gives on the plane `2k + j` the elliptic block
`(x² + y²) / 2` when `j ∈ t` and the hyperbolic block `x y` when `j ∉ t`. Here `xᵢ` and `yᵢ` are
the coordinates along `qᵢ` and `pᵢ`. These are the normal forms of Williamson's classification of
nondegenerate families of quadratic forms. -/
def williamsonBlocks : Fin k × Fin 2 ⊕ Fin n → QuadraticForm ℝ V :=
  Sum.elim
    (fun l ↦ ![QuadraticMap.linMulLin (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 0)), 0))
          (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 0)), 1)) +
        QuadraticMap.linMulLin (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 1)), 0))
          (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 1)), 1)),
      QuadraticMap.linMulLin (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 0)), 0))
          (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 1)), 1)) -
        QuadraticMap.linMulLin (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 1)), 0))
          (b.coord (Fin.castAdd n (finProdFinEquiv (l.1, 0)), 1))] l.2)
    fun j ↦ if j ∈ t then elliptic b (Fin.natAdd (k * 2) j) else hyperbolic b (Fin.natAdd (k * 2) j)

/-- The first form of the `j`-th focus-focus block is `x₂ⱼ y₂ⱼ + x₂ⱼ₊₁ y₂ⱼ₊₁`. -/
@[simp]
theorem williamsonBlocks_inl_zero_apply (j : Fin k) (x : V) :
    williamsonBlocks b t (.inl (j, 0)) x =
      b.repr x (Fin.castAdd n (finProdFinEquiv (j, 0)), 0) *
          b.repr x (Fin.castAdd n (finProdFinEquiv (j, 0)), 1) +
        b.repr x (Fin.castAdd n (finProdFinEquiv (j, 1)), 0) *
          b.repr x (Fin.castAdd n (finProdFinEquiv (j, 1)), 1) := by
  simp [williamsonBlocks]

/-- The second form of the `j`-th focus-focus block is `x₂ⱼ y₂ⱼ₊₁ - x₂ⱼ₊₁ y₂ⱼ`. -/
@[simp]
theorem williamsonBlocks_inl_one_apply (j : Fin k) (x : V) :
    williamsonBlocks b t (.inl (j, 1)) x =
      b.repr x (Fin.castAdd n (finProdFinEquiv (j, 0)), 0) *
          b.repr x (Fin.castAdd n (finProdFinEquiv (j, 1)), 1) -
        b.repr x (Fin.castAdd n (finProdFinEquiv (j, 1)), 0) *
          b.repr x (Fin.castAdd n (finProdFinEquiv (j, 0)), 1) := by
  simp [williamsonBlocks]

variable {b t}

/-- For `j ∈ t`, the block on the plane `2k + j` is elliptic. -/
@[simp]
theorem williamsonBlocks_inr_of_mem {j : Fin n} (hj : j ∈ t) :
    williamsonBlocks b t (.inr j) = elliptic b (Fin.natAdd (k * 2) j) := by
  simp [williamsonBlocks, hj]

/-- For `j ∉ t`, the block on the plane `2k + j` is hyperbolic. -/
@[simp]
theorem williamsonBlocks_inr_of_notMem {j : Fin n} (hj : j ∉ t) :
    williamsonBlocks b t (.inr j) = hyperbolic b (Fin.natAdd (k * 2) j) := by
  simp [williamsonBlocks, hj]

end Blocks

/-! ### The classification -/

/-- On the concatenation of a basis `b₁` of `L` and a basis `b₂` of `M`, carried to `V` along an
isomorphism `e : L × M ≃ V`, the Williamson blocks are the focus-focus blocks of `b₁` and the
elliptic–hyperbolic blocks of `b₂`, extended by zero and read through `e`. -/
private theorem williamsonBlocks_prod {L M : Type*} [AddCommGroup L] [Module ℝ L]
    [AddCommGroup M] [Module ℝ M] {k n : ℕ} (b₁ : Basis (Fin (k * 2) × Fin 2) ℝ L)
    (b₂ : Basis (Fin n × Fin 2) ℝ M) (t : Finset (Fin n)) (e : (L × M) ≃ₗ[ℝ] V) :
    williamsonBlocks (((b₁.prod b₂).reindex ((Equiv.sumProdDistrib _ _ _).symm.trans
        (finSumFinEquiv.prodCongr (Equiv.refl _)))).map e) t =
      fun l ↦ (Sum.elim (fun l ↦ (focusFocusBlocks b₁ l).prod 0)
        (fun j ↦ (0 : QuadraticForm ℝ L).prod (ellipticHyperbolic b₂ t j)) l).comp
          (e.symm : V →ₗ[ℝ] L × M) := by
  set b := ((b₁.prod b₂).reindex ((Equiv.sumProdDistrib _ _ _).symm.trans
    (finSumFinEquiv.prodCongr (Equiv.refl _)))).map e
  -- The coordinates of `b` on the first `2k` planes are those of `b₁`, on the others those of `b₂`.
  have hrepr₁ (x : V) (i : Fin (k * 2)) (c : Fin 2) :
      b.repr x (Fin.castAdd n i, c) = b₁.repr (e.symm x).1 (i, c) := by
    simp [b]
  have hrepr₂ (x : V) (j : Fin n) (c : Fin 2) :
      b.repr x (Fin.natAdd (k * 2) j, c) = b₂.repr (e.symm x).2 (j, c) := by
    simp [b]
  funext l
  rcases l with ⟨j, c⟩ | j
  · ext x
    fin_cases c <;> simp [hrepr₁]
  · ext x
    by_cases hj : j ∈ t <;> simp [hj, hrepr₂]

variable [FiniteDimensional ℝ V]

/-! #### The focus-focus part of a regular element -/

section Parts

variable {A : Module.End ℝ V} {s' : Finset ℂ}

omit [FiniteDimensional ℝ V] in
/-- For `z = a + bi ∈ s'`, the vectors killed by a power of
`(A² - 2aA + a² + b²)(A² + 2aA + a² + b²)` are killed by a power of `f(A)` for
`f = ∏_{a + bi ∈ s'} (X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`, a multiple of it. -/
private theorem maxGenEigenspace_focusFocusPoly_le_prod {z : ℂ} (hz : z ∈ s') :
    (aeval A (focusFocusPoly z.re z.im)).maxGenEigenspace 0 ≤
      (aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0 :=
  Module.End.maxGenEigenspace_aeval_le_of_dvd A
    (Finset.dvd_prod_of_mem (fun z : ℂ ↦ focusFocusPoly z.re z.im) hz)

omit [FiniteDimensional ℝ V] in
/-- If `A` has the eigenvalue `z = a + bi`, `z ∈ s'`, with eigenvector `v + iw`, then `v` is killed
by a power of `f(A)` for `f = ∏_{a + bi ∈ s'} (X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`. -/
private theorem mem_maxGenEigenspace_prod_focusFocusPoly {z : ℂ} (hz : z ∈ s') {v w : V}
    (hAv : A v = z.re • v - z.im • w) (hAw : A w = z.im • v + z.re • w) :
    v ∈ (aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0 :=
  maxGenEigenspace_focusFocusPoly_le_prod hz <| (Module.End.mem_maxGenEigenspace _ _ _).2
    ⟨1, by simpa using aeval_focusFocusPoly_apply_eq_zero hAv hAw⟩

/-- For `A ∈ sp(V, ω)`, the vectors killed by a power of `f(A)`, for `f` as in
`mem_maxGenEigenspace_prod_focusFocusPoly`, form a symplectic subspace, since `f` is even. -/
private theorem isSymplectic_maxGenEigenspace_prod_focusFocusPoly
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) :
    ω.IsSymplectic ((aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0) :=
  ω.isSymplectic_maxGenEigenspace_aeval hA <| by
    simp only [prod_comp, focusFocusPoly_comp_neg_X]

omit [FiniteDimensional ℝ V] in
/-- The vectors killed by a power of `f(A)`, for `f` as in
`mem_maxGenEigenspace_prod_focusFocusPoly`, are `ω`-orthogonal to those killed by a power of
`A² - μ`, since `X² - μ` is coprime to `f`. -/
private theorem apply_eq_zero_of_mem_maxGenEigenspace_prod_focusFocusPoly
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (hs'0 : ∀ z ∈ s', 0 < z.re ∧ 0 < z.im)
    (μ : ℝ) {v w : V}
    (hv : v ∈ (aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0)
    (hw : w ∈ (aeval A (X ^ 2 - C μ)).maxGenEigenspace 0) : ω v w = 0 :=
  ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval (by
    rw [comp_neg_X_sq_sub_C]
    exact IsCoprime.prod_left fun z hz ↦
      isCoprime_focusFocusPoly_X_sq_sub_C (hs'0 z hz).1.ne' (hs'0 z hz).2.ne' μ) hv hw

/-- **Lower bound on the focus-focus part.** If `A ∈ sp(V, ω)` has the distinct
eigenvalues `z = a + bi ∈ s'` with `a, b > 0`, then the vectors killed by a power of `f(A)`, for `f`
as in `mem_maxGenEigenspace_prod_focusFocusPoly`, form a subspace of dimension at least
`4 |s'|`: it contains the pairwise orthogonal generalized eigenspaces of the factors of `f`, each of
dimension at least four. -/
private theorem card_mul_four_le_finrank_maxGenEigenspace_prod_focusFocusPoly
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (hs'0 : ∀ z ∈ s', 0 < z.re ∧ 0 < z.im)
    (hAs' : ∀ z ∈ s', ∃ v w : V, v ≠ 0 ∧ A v = z.re • v - z.im • w ∧ A w = z.im • v + z.re • w) :
    s'.card * 4 ≤
      finrank ℝ ((aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0) := by
  set H : s' → Submodule ℝ V := fun z ↦
    (aeval A (focusFocusPoly (z : ℂ).re (z : ℂ).im)).maxGenEigenspace 0
  have hHs (z : s') : ω.IsSymplectic (H z) :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPoly_comp_neg_X _ _)
  have horth : Pairwise fun z z' : s' ↦ ∀ v ∈ H z, ∀ w ∈ H z', ω v w = 0 :=
    fun z z' hzz' _ hv _ hw ↦ apply_eq_zero_of_mem_maxGenEigenspace_aeval_focusFocusPoly hA
      (hs'0 _ z.property) (hs'0 _ z'.property) (fun h ↦ hzz' (Subtype.ext h)) hv hw
  have hH4 (z : s') : 4 ≤ finrank ℝ (H z) := by
    obtain ⟨v, w, hv, hAv, hAw⟩ := hAs' z z.property
    exact four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly hA (hs'0 _ z.property).1.ne'
      (hs'0 _ z.property).2.ne' hv hAv hAw
  calc s'.card * 4 = ∑ _z : s', 4 := by simp
    _ ≤ ∑ z, finrank ℝ (H z) := Finset.sum_le_sum fun z _ ↦ hH4 z
    _ = finrank ℝ ↥(⨆ z, H z) :=
      (finrank_iSup_eq_sum_finrank_of_iSupIndep
        (iSupIndep_of_pairwise_apply_eq_zero hHs horth)).symm
    _ ≤ _ := Submodule.finrank_mono
      (iSup_le fun z ↦ maxGenEigenspace_focusFocusPoly_le_prod z.property)

/-- **Upper bound on the focus-focus part.** If `A ∈ sp(V, ω)` and `A²` has the distinct nonzero
eigenvalues `μ ∈ s`, then the vectors killed by a power of `f(A)`, for `f` as in
`mem_maxGenEigenspace_prod_focusFocusPoly`, form a subspace of dimension at most
`dim V - 2 |s|`: it is orthogonal to the generalized eigenspaces of `A²` for `μ ∈ s`, which are
pairwise orthogonal nonzero symplectic subspaces. -/
private theorem finrank_maxGenEigenspace_prod_focusFocusPoly_add_card_mul_two_le
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (hs'0 : ∀ z ∈ s', 0 < z.re ∧ 0 < z.im)
    {s : Finset ℝ} (hAs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) :
    finrank ℝ ((aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0) +
      s.card * 2 ≤ finrank ℝ V := by
  set L := (aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0
  set G : ℝ → Submodule ℝ V := fun μ ↦ (aeval A (X ^ 2 - C μ)).maxGenEigenspace 0
  have hL : ω.IsSymplectic L := isSymplectic_maxGenEigenspace_prod_focusFocusPoly hA
  -- Each `G μ` contains an eigenvector of `A²`, so it is a nonzero symplectic subspace.
  have hG2 (μ : s) : 2 ≤ finrank ℝ (G μ) := by
    obtain ⟨x, hx⟩ := (hAs μ μ.property).exists_hasEigenvector
    exact (isSymplectic_maxGenEigenspace_aeval_X_sq_sub_C hA μ).two_le_finrank_of_mem
      (Module.End.mem_maxGenEigenspace_aeval_X_sq_sub_C (by simpa [sq] using hx.apply_eq_smul))
      hx.2
  set K : Option s → Submodule ℝ V := fun o ↦ o.elim L fun μ ↦ G μ
  have hKs (o : Option s) : ω.IsSymplectic (K o) := by
    rcases o with _ | μ
    exacts [hL, isSymplectic_maxGenEigenspace_aeval_X_sq_sub_C hA μ]
  have horth : Pairwise fun o o' : Option s ↦ ∀ v ∈ K o, ∀ w ∈ K o', ω v w = 0 := by
    rintro (_ | μ) (_ | ν) hne v hv w hw
    · exact absurd rfl hne
    · exact apply_eq_zero_of_mem_maxGenEigenspace_prod_focusFocusPoly hA hs'0 ν hv hw
    · rw [← ω.neg_eq,
        apply_eq_zero_of_mem_maxGenEigenspace_prod_focusFocusPoly hA hs'0 μ hw hv, neg_zero]
    · exact apply_eq_zero_of_mem_maxGenEigenspace_aeval_X_sq_sub_C hA
        (fun h ↦ hne (congrArg some (Subtype.ext h))) hv hw
  have hsum : finrank ℝ L + ∑ μ : s, finrank ℝ (G μ) ≤ finrank ℝ V := by
    have := (finrank_iSup_eq_sum_finrank_of_iSupIndep
      (iSupIndep_of_pairwise_apply_eq_zero hKs horth)).symm.trans_le (Submodule.finrank_le _)
    rw [Fintype.sum_option] at this
    -- `K none` is `L` and `K (some μ)` is `G μ`, definitionally.
    exact this
  have : s.card * 2 ≤ ∑ μ : s, finrank ℝ (G μ) :=
    (by simp : s.card * 2 = ∑ _μ : s, 2).trans_le (Finset.sum_le_sum fun μ _ ↦ hG2 μ)
  omega

/-- **Dimension of the focus-focus part.** If `A ∈ sp(V, ω)` has the distinct
eigenvalues `a + bi ∈ s'` with `a, b > 0`, and `A²` the distinct nonzero real eigenvalues `μ ∈ s`,
with `4 |s'| + 2 |s| = dim V`, then the vectors killed by a power of `f(A)`, for `f` as in
`mem_maxGenEigenspace_prod_focusFocusPoly`, form a subspace of dimension `4 |s'|`. -/
private theorem finrank_maxGenEigenspace_prod_focusFocusPoly
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hs : s'.card * 4 + s.card * 2 = finrank ℝ V) (hs'0 : ∀ z ∈ s', 0 < z.re ∧ 0 < z.im)
    (hAs' : ∀ z ∈ s', ∃ v w : V, v ≠ 0 ∧ A v = z.re • v - z.im • w ∧ A w = z.im • v + z.re • w)
    (hAs2 : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) :
    finrank ℝ ((aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0) =
      s'.card * 4 := by
  have := card_mul_four_le_finrank_maxGenEigenspace_prod_focusFocusPoly hA hs'0 hAs'
  have := finrank_maxGenEigenspace_prod_focusFocusPoly_add_card_mul_two_le (ω := ω) hA hs'0 hAs2
  omega

end Parts

/-! #### Assembling the two parts -/

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- If `P` lies in the span of a nondegenerate family and its Hamiltonian endomorphism and those of
the family preserve a symplectic subspace `L`, the restriction of `P` to `L` lies in the span of
the restricted family: it Poisson-commutes with it, and the restricted family is nondegenerate. -/
private theorem IsNondegenerateQuadraticFamily.comp_subtype_mem_span
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    (hQL : ∀ i, ∀ v ∈ L, ω.hamiltonianEnd (Q i) v ∈ L) (hPL : ∀ v ∈ L, ω.hamiltonianEnd P v ∈ L) :
    P.comp L.subtype ∈ Submodule.span ℝ (Set.range fun i ↦ (Q i).comp L.subtype) :=
  IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero
    (h.restrict hL fun i ↦ (Module.End.mem_invtSubmodule _).2 (hQL i)) fun i ↦
      (quadraticPoissonBracket_eq_zero_iff _).2 <| by
        rw [hamiltonianEnd_comp_subtype hL hPL, hamiltonianEnd_comp_subtype hL (hQL i)]
        exact LinearMap.restrict_commute (ω.quadraticPoissonBracket_eq_zero_iff.1 <|
          ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hP
            (Submodule.subset_span ⟨i, rfl⟩)) _ _

/-- **Assembling Williamson blocks.** Let `L` be a symplectic subspace preserved by the
Hamiltonian endomorphisms of a nondegenerate family `Q`. If the restrictions of `Q` to `L` span the
focus-focus blocks of a Darboux basis `b₁` of `L`, and its restrictions to `L^ω` span the
elliptic–hyperbolic blocks of a Darboux basis `b₂` of `L^ω`, then `Q` spans the Williamson blocks of
the concatenation of `b₁` and `b₂`, carried to `V` along `L × L^ω ≃ V`. -/
private theorem IsNondegenerateQuadraticFamily.span_eq_span_williamsonBlocks
    (h : ω.IsNondegenerateQuadraticFamily Q) {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    (hQL : ∀ i, ∀ v ∈ L, ω.hamiltonianEnd (Q i) v ∈ L) {k n : ℕ}
    {b₁ : Basis (Fin (k * 2) × Fin 2) ℝ L} {b₂ : Basis (Fin n × Fin 2) ℝ (ω.orthogonal L)}
    {t : Finset (Fin n)}
    (hspan₁ : Submodule.span ℝ (Set.range fun i ↦ (Q i).comp L.subtype) =
      Submodule.span ℝ (Set.range (focusFocusBlocks b₁)))
    (hspan₂ : Submodule.span ℝ (Set.range fun i ↦ (Q i).comp (ω.orthogonal L).subtype) =
      Submodule.span ℝ (Set.range (ellipticHyperbolic b₂ t))) :
    Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks
      (((b₁.prod b₂).reindex ((Equiv.sumProdDistrib _ _ _).symm.trans
        (finSumFinEquiv.prodCongr (Equiv.refl _)))).map
          (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) (isSymplectic_iff_isCompl.1 hL)))
      t)) := by
  set e := Submodule.prodEquivOfIsCompl L (ω.orthogonal L) (isSymplectic_iff_isCompl.1 hL)
  have he := ω.isSymplectomorphism_prodEquivOfIsCompl (isSymplectic_iff_isCompl.1 hL)
  rw [williamsonBlocks_prod]
  -- Along `e`, the family is the direct sum of its restrictions, whose spans are known.
  set Q₁ := fun i ↦ (Q i).comp L.subtype
  set Q₂ := fun i ↦ (Q i).comp (ω.orthogonal L).subtype
  have hQe (i : ι) : (Q i).comp (e : L × ω.orthogonal L →ₗ[ℝ] V) = (Q₁ i).prod (Q₂ i) :=
    comp_prodEquivOfIsCompl_eq_prod hL (hQL i)
  have hnd : ((ω.restrict L hL.nondegenerate_restrict).prod (ω.restrict (ω.orthogonal L)
      hL.orthogonal.nondegenerate_restrict)).IsNondegenerateQuadraticFamily
        fun i ↦ (Q₁ i).prod (Q₂ i) := by
    convert (isNondegenerateQuadraticFamily_comp_iff he Q).2 h using 1
    exact (funext hQe).symm
  have hS : Submodule.span ℝ (Set.range fun i ↦ (Q i).comp (e : L × ω.orthogonal L →ₗ[ℝ] V)) =
      Submodule.span ℝ (Set.range (Sum.elim (fun l ↦ (focusFocusBlocks b₁ l).prod 0)
        fun j ↦ (0 : QuadraticForm ℝ L).prod (ellipticHyperbolic b₂ t j))) := by
    rw [show (fun i ↦ (Q i).comp (e : L × ω.orthogonal L →ₗ[ℝ] V)) = _ from funext hQe,
      hnd.span_range_prod_eq]
    ext R
    rw [QuadraticMap.mem_span_range_sumElim_prod_iff, QuadraticMap.mem_span_range_sumElim_prod_iff,
      hspan₁, hspan₂]
  -- Read back in `V` through `R ↦ R ∘ e⁻¹`.
  rw [← QuadraticMap.span_range_comp_eq_span_range_comp hS e.symm.toLinearMap]
  congr 2
  funext i
  ext x
  simp

/-! #### The classification -/

namespace IsNondegenerateQuadraticFamily

/-- **Williamson's classification, mixed type.** Let `Q` be a nondegenerate family of quadratic
forms on `V`, and suppose that its span contains a regular element: a form `P` whose Hamiltonian
endomorphism `A = A_P` has `dim V` distinct eigenvalues, listed as follows.

* `s'` is a set of eigenvalues `z = a + bi` with `a, b > 0`: for each of them there are `v ≠ 0`
  and `w` with `A v = a v - b w` and `A w = b v + a w`, so that `A (v + iw) = z (v + iw)`. Each
  accounts for the four eigenvalues `±a ± bi`.
* `s` is a set of nonzero real eigenvalues `μ` of `A²`. Each accounts for the two eigenvalues
  `±√μ` of `A`, real when `μ > 0` and imaginary when `μ < 0`.

with `4 |s'| + 2 |s| = dim V`. Then the span of `Q` is the span of the Williamson blocks of some
Darboux basis: focus-focus blocks, and elliptic and hyperbolic blocks on the remaining planes. -/
theorem exists_isDarbouxBasis_span_eq_span_williamsonBlocks
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s' : Finset ℂ} {s : Finset ℝ}
    (hs : s'.card * 4 + s.card * 2 = finrank ℝ V) (hs'0 : ∀ z ∈ s', 0 < z.re ∧ 0 < z.im)
    (hPs' : ∀ z ∈ s', ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
      ω.hamiltonianEnd P w = z.im • v + z.re • w)
    (hs0 : (0 : ℝ) ∉ s) (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) :
    ∃ (k n : ℕ) (b : Basis (Fin (k * 2 + n) × Fin 2) ℝ V) (t : Finset (Fin n)),
      ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  set A := ω.hamiltonianEnd P
  have hA := ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  -- The focus-focus part `L` has dimension `4 |s'|`, and its complement `2 |s|`.
  set L := (aeval A (∏ z ∈ s', focusFocusPoly z.re z.im)).maxGenEigenspace 0
  have hL : ω.IsSymplectic L := isSymplectic_maxGenEigenspace_prod_focusFocusPoly hA
  have hfinL : s'.card * 4 = finrank ℝ L :=
    (finrank_maxGenEigenspace_prod_focusFocusPoly hA hs hs'0 hPs' hPs).symm
  have hfinM : s.card * 2 = finrank ℝ (ω.orthogonal L) := by
    have := ω.finrank_add_finrank_orthogonal L; omega
  -- `A` and the family preserve `L` and `L^ω`.
  have hmapsL {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
      ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L := fun v hv ↦
    Module.End.mapsTo_genEigenspace_aeval_of_comm (ω.quadraticPoissonBracket_eq_zero_iff.1 <|
      ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hP hR) _ 0 ⊤
      hv
  have hmapsM {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
      ∀ v ∈ ω.orthogonal L, ω.hamiltonianEnd R v ∈ ω.orthogonal L := fun _ ↦
    ((LinearMap.mem_skewAdjointSubmodule _).1
      (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra R)).apply_mem_orthogonal (hmapsL hR)
  have hQ (i : ι) : Q i ∈ Submodule.span ℝ (Set.range Q) := Submodule.subset_span ⟨i, rfl⟩
  -- The focus-focus classification on `L`: the eigenvectors for `z ∈ s'` lie in `L`.
  obtain ⟨k, b₁, hb₁, hspan₁⟩ := (h.restrict hL fun i ↦ (Module.End.mem_invtSubmodule _).2
    (hmapsL (hQ i))).exists_isDarbouxBasis_span_eq_span_focusFocusBlocks
      (h.comp_subtype_mem_span hP hL (fun i ↦ hmapsL (hQ i)) (hmapsL hP)) hfinL hs'0 fun z hz ↦ by
    obtain ⟨v, w, hv, hAv, hAw⟩ := hPs' z hz
    have hvL := mem_maxGenEigenspace_prod_focusFocusPoly hz hAv hAw
    have hwL := mem_maxGenEigenspace_prod_focusFocusPoly (v := w) (w := -v) hz
      (by rw [hAw]; module) (by rw [map_neg, hAv]; module)
    refine ⟨⟨v, hvL⟩, ⟨w, hwL⟩, by simpa using hv, ?_, ?_⟩ <;>
      rw [hamiltonianEnd_comp_subtype hL (hmapsL hP)] <;> ext <;> simpa
  -- The elliptic–hyperbolic classification on `L^ω`: the eigenvectors of `A²` lie in `L^ω`.
  obtain ⟨n, b₂, t, hb₂, hspan₂⟩ :=
    exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic (h.restrict hL.orthogonal fun i ↦
      (Module.End.mem_invtSubmodule _).2 (hmapsM (hQ i)))
      (h.comp_subtype_mem_span hP hL.orthogonal (fun i ↦ hmapsM (hQ i)) (hmapsM hP)) hfinM hs0
      fun μ hμ ↦ by
    obtain ⟨x, hx⟩ := (hPs μ hμ).exists_hasEigenvector
    have hxM : x ∈ ω.orthogonal L := mem_orthogonal_iff.2 fun y hy ↦
      apply_eq_zero_of_mem_maxGenEigenspace_prod_focusFocusPoly hA hs'0 μ hy <|
        Module.End.mem_maxGenEigenspace_aeval_X_sq_sub_C (by simpa [sq] using hx.apply_eq_smul)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxM⟩) ⟨?_, by simpa using hx.2⟩
    rw [Module.End.mem_eigenspace_iff, hamiltonianEnd_comp_subtype hL.orthogonal (hmapsM hP)]
    ext
    simpa [sq] using hx.apply_eq_smul
  exact ⟨k, n, _, t, (hb₁.prod hb₂).map (ω.isSymplectomorphism_prodEquivOfIsCompl
    (isSymplectic_iff_isCompl.1 hL)), h.span_eq_span_williamsonBlocks hL (fun i ↦ hmapsL (hQ i))
      hspan₁ hspan₂⟩

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
