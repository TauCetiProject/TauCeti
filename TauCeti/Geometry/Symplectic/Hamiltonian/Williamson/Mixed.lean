/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.EllipticHyperbolic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.FocusFocus
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Order.Ring.Square
import TauCeti.Algebra.Polynomial.EvenComp
import TauCeti.Data.Fin.Basic
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting
import TauCeti.Geometry.Symplectic.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Aeval
import TauCeti.LinearAlgebra.Eigenspace.Commute
import TauCeti.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# Williamson's classification of nondegenerate families of mixed type

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra of `sp(V, ω)`. Williamson's
classification puts such a family, up to its span, into a normal form made of elliptic, hyperbolic
and focus-focus blocks on disjoint symplectic coordinate planes of a Darboux basis.

For a basis `b` indexed as a Darboux basis with `m + 2f` planes and a set `t` of planes among the
first `m`, the **Williamson blocks** `TauCeti.SymplecticForm.williamsonBlocks b t` are, in the dual
coordinates `(xₖ, yₖ)`:

* on each of the first `m` planes, the elliptic block `(xₖ² + yₖ²) / 2` for `k ∈ t` and the
  hyperbolic block `xₖ yₖ` for `k ∉ t`;
* on the planes `m + 2j` and `m + 2j + 1`, for `j < f`, with coordinates `(x, y)` and `(x', y')`,
  the focus-focus pair `x y + x' y'` and `x y' - x' y`.

So `|t|` elliptic, `m - |t|` hyperbolic and `f` focus-focus blocks, with `|t| + (m - |t|) + 2f`
equal to half the dimension. These blocks restrict on the coordinate summands to the
elliptic–hyperbolic blocks (`TauCeti.SymplecticForm.ellipticHyperbolic`) and to the focus-focus
blocks (`TauCeti.SymplecticForm.focusFocusBlocks`)
(`TauCeti.SymplecticForm.williamsonBlocks_prod`). In a Darboux basis they pairwise Poisson-commute
(`TauCeti.SymplecticForm.IsDarbouxBasis.quadraticPoissonBracket_williamsonBlocks`).

## Main results

All declarations are in the namespace `TauCeti.SymplecticForm`.

* `exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_isSymplectic`, in the namespace
  `IsNondegenerateQuadraticFamily`: **assembling normal forms along an invariant splitting.** If
  a symplectic subspace `L` preserved by a nondegenerate family carries a Darboux basis in whose
  elliptic–hyperbolic blocks the restricted family is in normal form, and `L^ω` one in whose
  focus-focus blocks it is, then
  the two bases concatenate to a Darboux basis of `V` in whose Williamson blocks the family is in
  normal form.
* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span`:
  **Williamson's classification of mixed type.** If the span of a nondegenerate family contains a
  form `P` such that `A_P²` has nonzero real eigenvalues `μ ∈ s` and `A_P` has eigenvalues
  `z = a + bi` with `a, b > 0`, `z ∈ t`, and `2 |s| + 4 |t| = dim V`, then the family spans the same
  space as the Williamson blocks of some Darboux basis with `|s|` elliptic or hyperbolic and `|t|`
  focus-focus blocks.
* `IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank_iff`:
  this characterizes the nondegenerate families spanning the Williamson blocks of a Darboux basis.
  Conversely, the form `∑ₖ (k + 1) Bₖ + ∑ⱼ ((j + 1) Q₁ⱼ + Q₂ⱼ)`, `Bₖ` the elliptic or hyperbolic
  block of the plane `k` and `(Q₁ⱼ, Q₂ⱼ)` the `j`-th focus-focus pair, has such eigenvalues.

The proof of the classification splits `V` along `P`. The vectors `L` killed by a power of
`∏_{μ ∈ s} (A_P² - μ)` form a symplectic subspace preserved by the family, since this polynomial is
even. Each eigenvector of `A_P²` for `μ ∈ s` lies in `L`; each pair `(v, w)` with
`A_P (v + iw) = z (v + iw)`, `z ∈ t`, lies in `L^ω`, because the polynomial
`(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` (`TauCeti.SymplecticForm.focusFocusPoly`), with roots
`±a ± bi`, has no common complex root with `X² - μ`. Counting dimensions as in the two pure cases,
`L` has dimension `2 |s|` and `L^ω` dimension `4 |t|`, so the elliptic–hyperbolic classification
applies on `L` and the focus-focus classification on `L^ω`. Along `L × L^ω ≃ V`, the span of the
family is the sum of the spans of its restrictions
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.mem_span_range_iff_exists_prod`), and the
two normal forms assemble.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
* E. Miranda and N. T. Zung, *Equivariant normal form for nondegenerate singular orbits of
  integrable Hamiltonian systems*, Annales scientifiques de l'École Normale Supérieure 37 (2004),
  819–839, Section 2.
-/

public section

noncomputable section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m f : ℕ}

/-! ### The Williamson blocks -/

variable (b : Basis (Fin (m + f * 2) × Fin 2) ℝ V) (t : Finset (Fin m))

/-- The **Williamson blocks** of a basis `b` of `V` indexed as a Darboux basis with `m + 2f`
planes, `qₖ = b (k, 0)` and `pₖ = b (k, 1)`, for a set `t` of planes among the first `m`: on the
plane `k < m`, indexed by `inl k`, the elliptic block `(xₖ² + yₖ²) / 2` if `k ∈ t` and the
hyperbolic block `xₖ yₖ` otherwise; on the planes `m + 2j` and `m + 2j + 1`, for `j < f`, the
focus-focus pair `x y + x' y'` and `x y' - x' y`, indexed by `inr (j, 0)` and `inr (j, 1)`: these
are the focus-focus blocks `TauCeti.SymplecticForm.focusFocusBlocksAt` on the planes
`m + 2j + i`. -/
def williamsonBlocks : Fin m ⊕ Fin f × Fin 2 → QuadraticForm ℝ V :=
  Sum.elim
    (fun k ↦ ellipticHyperbolic b (t.map (Fin.castAddEmb (f * 2))) (Fin.castAdd (f * 2) k))
    (focusFocusBlocksAt b fun l ↦ Fin.natAdd m (finProdFinEquiv l))

/-- The Williamson block on one of the first `m` planes is the elliptic–hyperbolic block of that
plane. -/
theorem williamsonBlocks_inl (k : Fin m) :
    williamsonBlocks b t (.inl k) =
      ellipticHyperbolic b (t.map (Fin.castAddEmb (f * 2))) (Fin.castAdd (f * 2) k) := by
  simp [williamsonBlocks]

@[simp]
theorem williamsonBlocks_inl_apply (k : Fin m) (x : V) :
    williamsonBlocks b t (.inl k) x =
      if k ∈ t then
        (b.repr x (Fin.castAdd (f * 2) k, 0) ^ 2 + b.repr x (Fin.castAdd (f * 2) k, 1) ^ 2) / 2
      else b.repr x (Fin.castAdd (f * 2) k, 0) * b.repr x (Fin.castAdd (f * 2) k, 1) := by
  by_cases hk : k ∈ t <;> simp [williamsonBlocks_inl, hk]

/-- The Williamson blocks on the last `2f` planes are the focus-focus blocks on the planes
`m + 2j + i`. -/
theorem williamsonBlocks_inr (l : Fin f × Fin 2) :
    williamsonBlocks b t (.inr l) =
      focusFocusBlocksAt b (fun l ↦ Fin.natAdd m (finProdFinEquiv l)) l := by
  simp [williamsonBlocks]

@[simp]
theorem williamsonBlocks_inr_zero_apply (j : Fin f) (x : V) :
    williamsonBlocks b t (.inr (j, 0)) x =
      b.repr x (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) *
          b.repr x (Fin.natAdd m (finProdFinEquiv (j, 0)), 1) +
        b.repr x (Fin.natAdd m (finProdFinEquiv (j, 1)), 0) *
          b.repr x (Fin.natAdd m (finProdFinEquiv (j, 1)), 1) := by
  simp [williamsonBlocks]

@[simp]
theorem williamsonBlocks_inr_one_apply (j : Fin f) (x : V) :
    williamsonBlocks b t (.inr (j, 1)) x =
      b.repr x (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) *
          b.repr x (Fin.natAdd m (finProdFinEquiv (j, 1)), 1) -
        b.repr x (Fin.natAdd m (finProdFinEquiv (j, 1)), 0) *
          b.repr x (Fin.natAdd m (finProdFinEquiv (j, 0)), 1) := by
  simp [williamsonBlocks]

/-- The Williamson blocks are natural in the basis: transporting the basis along a linear
equivalence `e` transports the blocks along `e`. -/
theorem williamsonBlocks_map {W : Type*} [AddCommGroup W] [Module ℝ W] (e : V ≃ₗ[ℝ] W)
    (k : Fin m ⊕ Fin f × Fin 2) :
    (williamsonBlocks (b.map e) t k).comp (e : V →ₗ[ℝ] W) = williamsonBlocks b t k := by
  ext x
  rcases k with k | ⟨j, i⟩
  · simp
  · fin_cases i <;> simp

/-- **The Williamson blocks of a direct sum.** For the concatenation of a basis `b₁` of `V₁` with
`m` planes and a basis `b₂` of `V₂` with `2f` planes, a basis of `V₁ × V₂`, the Williamson blocks
are the elliptic–hyperbolic blocks of `b₁` on the first summand and the focus-focus blocks of `b₂`
on the second. -/
theorem williamsonBlocks_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂]
    [Module ℝ V₂] (b₁ : Basis (Fin m × Fin 2) ℝ V₁) (b₂ : Basis (Fin (f * 2) × Fin 2) ℝ V₂) :
    williamsonBlocks ((b₁.prod b₂).reindex
        ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))) t =
      Sum.elim (fun k ↦ (ellipticHyperbolic b₁ t k).prod 0)
        fun j ↦ (0 : QuadraticForm ℝ V₁).prod (focusFocusBlocks b₂ j) := by
  funext k
  ext ⟨u, w⟩
  rcases k with k | ⟨j, i⟩
  · by_cases hk : k ∈ t <;> simp [hk]
  · fin_cases i <;> simp

/-! ### The Williamson blocks in a Darboux basis -/

section Darboux

variable {b t} [FiniteDimensional ℝ V] {ω : SymplecticForm V}

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic or hyperbolic block on the
plane `k < m` sends `qₖ` to `-pₖ` if the block is elliptic and to `qₖ` if it is hyperbolic, and
the other `qⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inl_apply_fst (hb : ω.IsDarbouxBasis b)
    (k : Fin m) (j : Fin (m + f * 2)) :
    ω.hamiltonianEnd (williamsonBlocks b t (.inl k)) (b (j, 0)) =
      if j = Fin.castAdd _ k then
        (if k ∈ t then -b (Fin.castAdd _ k, 1) else b (Fin.castAdd _ k, 0)) else 0 := by
  simp [williamsonBlocks_inl, hb.hamiltonianEnd_ellipticHyperbolic_apply_fst]

/-- In a Darboux basis, the Hamiltonian endomorphism of the elliptic or hyperbolic block on the
plane `k < m` sends `pₖ` to `qₖ` if the block is elliptic and to `-pₖ` if it is hyperbolic, and
the other `pⱼ` to `0`. -/
theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inl_apply_snd (hb : ω.IsDarbouxBasis b)
    (k : Fin m) (j : Fin (m + f * 2)) :
    ω.hamiltonianEnd (williamsonBlocks b t (.inl k)) (b (j, 1)) =
      if j = Fin.castAdd _ k then
        (if k ∈ t then b (Fin.castAdd _ k, 0) else -b (Fin.castAdd _ k, 1)) else 0 := by
  simp [williamsonBlocks_inl, hb.hamiltonianEnd_ellipticHyperbolic_apply_snd]

/-- In a Darboux basis, the Hamiltonian endomorphism of a focus-focus Williamson block followed by
that of an elliptic or hyperbolic one is zero: the focus-focus block kills the first `m` planes and
maps the last `2f` planes into themselves, which the elliptic or hyperbolic block kills. -/
private theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inl_mul_inr
    (hb : ω.IsDarbouxBasis b) (k : Fin m) (l : Fin f × Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (.inl k)) *
      ω.hamiltonianEnd (williamsonBlocks b t (.inr l)) = 0 := by
  refine b.ext fun ⟨n, c⟩ ↦ ?_
  induction n using Fin.addCases with
  | left i =>
    simp [mul_apply_eq_comp, williamsonBlocks_inr,
      hb.hamiltonianEnd_focusFocusBlocksAt_apply_of_forall_ne]
  | right p =>
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨j', l⟩ := l
    fin_cases l <;> fin_cases i <;> fin_cases c <;>
      simp [mul_apply_eq_comp, williamsonBlocks_inr,
        hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply Fin.natAdd_comp_finProdFinEquiv_injective,
        hb.hamiltonianEnd_focusFocusBlocksAt_one_apply Fin.natAdd_comp_finProdFinEquiv_injective,
        apply_ite, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]

/-- In a Darboux basis, the Hamiltonian endomorphism of an elliptic or hyperbolic Williamson block
followed by that of a focus-focus one is zero: the elliptic or hyperbolic block kills the last `2f`
planes and maps the first `m` planes into themselves, which the focus-focus block kills. -/
private theorem IsDarbouxBasis.hamiltonianEnd_williamsonBlocks_inr_mul_inl
    (hb : ω.IsDarbouxBasis b) (k : Fin m) (l : Fin f × Fin 2) :
    ω.hamiltonianEnd (williamsonBlocks b t (.inr l)) *
      ω.hamiltonianEnd (williamsonBlocks b t (.inl k)) = 0 := by
  refine b.ext fun ⟨n, c⟩ ↦ ?_
  induction n using Fin.addCases with
  | left i =>
    fin_cases c <;>
      simp [mul_apply_eq_comp, williamsonBlocks_inr, apply_ite,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
        hb.hamiltonianEnd_focusFocusBlocksAt_apply_of_forall_ne]
  | right p =>
    fin_cases c <;>
      simp [mul_apply_eq_comp, hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
        hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd]

/-- In a Darboux basis, the Williamson blocks pairwise Poisson-commute: the elliptic–hyperbolic
and the focus-focus blocks do among themselves, and the Hamiltonian endomorphisms of an elliptic
or hyperbolic block and a focus-focus block compose to zero in both orders. -/
theorem IsDarbouxBasis.quadraticPoissonBracket_williamsonBlocks (hb : ω.IsDarbouxBasis b)
    (x y : Fin m ⊕ Fin f × Fin 2) :
    ω.quadraticPoissonBracket (williamsonBlocks b t x) (williamsonBlocks b t y) = 0 := by
  rcases x with k₁ | l₁ <;> rcases y with k₂ | l₂
  · simpa only [williamsonBlocks_inl] using hb.quadraticPoissonBracket_ellipticHyperbolic _ _ _
  · exact (quadraticPoissonBracket_eq_zero_iff ω).2
      ((hb.hamiltonianEnd_williamsonBlocks_inl_mul_inr k₁ l₂).trans
        (hb.hamiltonianEnd_williamsonBlocks_inr_mul_inl k₁ l₂).symm)
  · exact (quadraticPoissonBracket_eq_zero_iff ω).2
      ((hb.hamiltonianEnd_williamsonBlocks_inr_mul_inl k₂ l₁).trans
        (hb.hamiltonianEnd_williamsonBlocks_inl_mul_inr k₂ l₁).symm)
  · exact hb.quadraticPoissonBracket_focusFocusBlocksAt
      Fin.natAdd_comp_finProdFinEquiv_injective _ _

end Darboux

/-! ### Assembling normal forms along an invariant splitting -/

namespace IsNondegenerateQuadraticFamily

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {ι : Type*} {Q : ι → QuadraticForm ℝ V}

variable {t} in
/-- **Assembling Williamson normal forms along an invariant symplectic splitting.** Let `L` be a
symplectic subspace preserved by every Hamiltonian endomorphism of a nondegenerate family `Q`.
Suppose the restrictions of `Q` to `L` span the elliptic–hyperbolic blocks of a Darboux basis `b₁`
of `L`, and its restrictions to `L^ω` the focus-focus blocks of a Darboux basis `b₂` of `L^ω`.
Then `b₁` followed by `b₂` is a Darboux basis of `V` whose Williamson blocks span the same space as
`Q`. -/
theorem exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_isSymplectic
    (h : ω.IsNondegenerateQuadraticFamily Q) {L : Submodule ℝ V} (hL : ω.IsSymplectic L)
    (hQL : ∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i)))
    {b₁ : Basis (Fin m × Fin 2) ℝ L}
    (hb₁ : (ω.restrict L hL.nondegenerate_restrict).IsDarbouxBasis b₁)
    (h₁ : Submodule.span ℝ (Set.range fun i ↦ (Q i).comp L.subtype) =
      Submodule.span ℝ (Set.range (ellipticHyperbolic b₁ t)))
    {b₂ : Basis (Fin (f * 2) × Fin 2) ℝ (ω.orthogonal L)}
    (hb₂ : (ω.restrict (ω.orthogonal L) hL.orthogonal.nondegenerate_restrict).IsDarbouxBasis b₂)
    (h₂ : Submodule.span ℝ (Set.range fun i ↦ (Q i).comp (ω.orthogonal L).subtype) =
      Submodule.span ℝ (Set.range (focusFocusBlocks b₂))) :
    ∃ b : Basis (Fin (m + f * 2) × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧
      (∀ k c, b (Fin.castAdd (f * 2) k, c) = b₁ (k, c)) ∧
      (∀ l c, b (Fin.natAdd m l, c) = b₂ (l, c)) ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b t)) := by
  set e := Submodule.prodEquivOfIsCompl L (ω.orthogonal L) hL.isCompl
  set b' := (b₁.prod b₂).reindex
    ((Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _)))
  refine ⟨b'.map e, (hb₁.prod hb₂).map (ω.isSymplectomorphism_prodEquivOfIsCompl hL.isCompl),
    fun k c ↦ by simp [b', e, Basis.reindex_apply], fun l c ↦ by simp [b', e, Basis.reindex_apply],
    ?_⟩
  -- Along `e : L × L^ω ≃ V`, both spans consist of the orthogonal sums of a form in the span on
  -- `L` and a form in the span on `L^ω`.
  ext R
  rw [h.mem_span_range_iff_exists_prod hL hQL, ← QuadraticMap.comp_mem_span_range_comp_iff e,
    funext (williamsonBlocks_map b' t e), williamsonBlocks_prod,
    QuadraticMap.mem_span_range_sumElim_prod_iff, h₁, h₂]

end IsNondegenerateQuadraticFamily

/-! ### Williamson's classification of mixed type -/

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {A : Module.End ℝ V}

/-- If `A ∈ sp(V, ω)` and `A²` has the distinct eigenvalues `μ ∈ s`, the vectors killed by a power
of `∏_{μ ∈ s} (A² - μ)` form a subspace of dimension at least `2 |s|`: it contains the pairwise
`ω`-orthogonal symplectic subspaces of vectors killed by a power of `A² - μ`, each nonzero. -/
private theorem card_mul_two_le_finrank_maxGenEigenspace
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hAs : ∀ μ ∈ s, (A ^ 2).HasEigenvalue μ) :
    s.card * 2 ≤ finrank ℝ ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0) := by
  -- Each generalized kernel of `A² - μ` contains an eigenvector of `A²`, so it is a nonzero
  -- symplectic subspace.
  have h2 (μ : s) : 2 ≤ finrank ℝ ((aeval A (X ^ 2 - C (μ : ℝ))).maxGenEigenspace 0) := by
    obtain ⟨x, hx⟩ := (hAs μ μ.property).exists_hasEigenvector
    exact (isSymplectic_maxGenEigenspace_aeval_X_sq_sub_C hA μ).two_le_finrank_of_mem
      (Module.End.mem_maxGenEigenspace_aeval_X_sq_sub_C (by simpa [sq] using hx.apply_eq_smul))
      hx.2
  have h := card_mul_le_finrank_of_pairwise_apply_eq_zero
    (fun μ : s ↦ isSymplectic_maxGenEigenspace_aeval_X_sq_sub_C hA μ)
    (fun μ ν hμν _ hv _ hw ↦
      apply_eq_zero_of_mem_maxGenEigenspace_aeval_X_sq_sub_C hA (Subtype.coe_injective.ne hμν)
        hv hw) h2
    fun μ ↦ Module.End.maxGenEigenspace_aeval_zero_le_of_dvd A
      (Finset.dvd_prod_of_mem (fun ν : ℝ ↦ X ^ 2 - C ν) μ.property)
  rwa [Fintype.card_coe] at h

omit [FiniteDimensional ℝ V] in
/-- For `A ∈ sp(V, ω)` and `a, b > 0`, the vectors killed by a power of
`(A² - 2aA + a² + b²)(A² + 2aA + a² + b²)` are `ω`-orthogonal to those killed by a power of
`∏_{μ ∈ s} (A² - μ)`. -/
private theorem mem_orthogonal_maxGenEigenspace_of_mem_maxGenEigenspace_focusFocusPoly
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (s : Finset ℝ) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) {x : V} (hx : x ∈ (aeval A (focusFocusPoly a b)).maxGenEigenspace 0) :
    x ∈ ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0) :=
  mem_orthogonal_iff.2 fun _ hy ↦
    ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval
      (by rw [focusFocusPoly_comp_neg_X]
          exact IsCoprime.prod_left fun μ _ ↦
            (isCoprime_focusFocusPoly_X_sq_sub_C ha.ne' hb.ne' μ).symm) hy hx

/-- If `A ∈ sp(V, ω)` has the distinct eigenvalues `z ∈ t` in the open first quadrant, each with an
eigenvector `v + iw`, the symplectic complement of the vectors killed by a power of
`∏_{μ ∈ s} (A² - μ)` has dimension at least `4 |t|`: it contains the pairwise `ω`-orthogonal
symplectic subspaces of vectors killed by a power of `focusFocusPoly z.re z.im` evaluated at `A`,
each of dimension at least four. -/
private theorem card_mul_four_le_finrank_orthogonal
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (s : Finset ℝ) {t : Finset ℂ}
    (ht0 : ∀ z ∈ t, 0 < z.re ∧ 0 < z.im)
    (hAt : ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ A v = z.re • v - z.im • w ∧ A w = z.im • v + z.re • w) :
    t.card * 4 ≤
      finrank ℝ (ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0)) := by
  have h4 (z : t) :
      4 ≤ finrank ℝ ((aeval A (focusFocusPoly (z : ℂ).re (z : ℂ).im)).maxGenEigenspace 0) := by
    obtain ⟨v, w, hv, hAv, hAw⟩ := hAt z z.property
    exact four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly hA (ht0 _ z.property).1.ne'
      (ht0 _ z.property).2.ne' hv hAv hAw
  have h := card_mul_le_finrank_of_pairwise_apply_eq_zero
    (fun z : t ↦ ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPoly_comp_neg_X _ _))
    (fun z z' hzz' _ hv _ hw ↦ apply_eq_zero_of_mem_maxGenEigenspace_aeval_focusFocusPoly hA
      (ht0 _ z.property) (ht0 _ z'.property) (Subtype.coe_injective.ne hzz') hv hw) h4
    fun z _ hx ↦ mem_orthogonal_maxGenEigenspace_of_mem_maxGenEigenspace_focusFocusPoly hA
      s (ht0 _ z.property).1 (ht0 _ z.property).2 hx
  rwa [Fintype.card_coe] at h

omit [FiniteDimensional ℝ V] in
/-- An eigenvalue `μ ∈ s` of `A²` is an eigenvalue of the square of the restriction of `A` to the
vectors killed by a power of `∏_{μ ∈ s} (A² - μ)`. -/
private theorem hasEigenvalue_restrict_sq {s : Finset ℝ}
    (hAL : ∀ x ∈ (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0,
      A x ∈ (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0) {μ : ℝ} (hμ : μ ∈ s)
    (hAμ : (A ^ 2).HasEigenvalue μ) : Module.End.HasEigenvalue (A.restrict hAL ^ 2) μ := by
  obtain ⟨x, hx⟩ := hAμ.exists_hasEigenvector
  have hxμ : A (A x) = μ • x := by simpa [sq] using hx.apply_eq_smul
  have hxL : x ∈ (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0 :=
    Module.End.maxGenEigenspace_aeval_zero_le_of_dvd A (Finset.dvd_prod_of_mem _ hμ)
      (Module.End.mem_maxGenEigenspace_aeval_X_sq_sub_C hxμ)
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨x, hxL⟩)
    ⟨Module.End.mem_eigenspace_iff.2 (Subtype.ext ?_), fun h0 ↦ hx.2 (congrArg Subtype.val h0)⟩
  simp only [pow_two, mul_apply_eq_comp, LinearMap.coe_restrict_apply, hxμ,
    Submodule.coe_smul]

omit [FiniteDimensional ℝ V] in
/-- An eigenvalue `z = a + bi`, `a, b > 0`, of `A ∈ sp(V, ω)`, with eigenvector `v + iw`, is one of
the restriction of `A` to the symplectic complement of the vectors killed by a power of
`∏_{μ ∈ s} (A² - μ)`: both `v` and `w` lie there. -/
private theorem exists_restrict_orthogonal_apply_eq
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {s : Finset ℝ}
    (hAL : ∀ x ∈ ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0),
      A x ∈ ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0)) {z : ℂ}
    (hz : 0 < z.re ∧ 0 < z.im) {v w : V} (hv : v ≠ 0) (hAv : A v = z.re • v - z.im • w)
    (hAw : A w = z.im • v + z.re • w) :
    ∃ v' w' : ω.orthogonal ((aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0), v' ≠ 0 ∧
      A.restrict hAL v' = z.re • v' - z.im • w' ∧ A.restrict hAL w' = z.im • v' + z.re • w' := by
  have hmem {x y : V} (hAx : A x = z.re • x - z.im • y) (hAy : A y = z.im • x + z.re • y) :=
    mem_orthogonal_maxGenEigenspace_of_mem_maxGenEigenspace_focusFocusPoly hA s hz.1 hz.2
      ((Module.End.mem_maxGenEigenspace _ _ _).2
        ⟨1, by simpa using aeval_focusFocusPoly_apply_eq_zero hAx hAy⟩)
  -- `w + i(-v) = -i (v + iw)` is an eigenvector for the same eigenvalue.
  have hwv : w ∈ _ := hmem (y := -v) (by rw [hAw]; module) (by rw [map_neg, hAv]; module)
  refine ⟨⟨v, hmem hAv hAw⟩, ⟨w, hwv⟩, fun h0 ↦ hv (congrArg Subtype.val h0), Subtype.ext ?_,
    Subtype.ext ?_⟩
  · rw [LinearMap.coe_restrict_apply, hAv]
    simp
  · rw [LinearMap.coe_restrict_apply, hAw]
    simp

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's classification of mixed type.** Let `Q` be a nondegenerate family of quadratic
forms, and suppose that its span contains a form `P` such that the square of its Hamiltonian
endomorphism has distinct nonzero real eigenvalues `μ ∈ s`, and the Hamiltonian endomorphism itself
has distinct eigenvalues `z = a + bi`, `a, b > 0`, `z ∈ t`, each with an eigenvector `v + iw`
(recorded as `v ≠ 0` and `w` with `A_P v = a v - b w`, `A_P w = b v + a w`), with
`2 |s| + 4 |t| = dim V`. Then there are a Darboux basis with `|s| + 2 |t|` planes and a set of
elliptic planes among the first `|s|` whose Williamson blocks span the same space as `Q`: `|s|`
elliptic or hyperbolic blocks and `|t|` focus-focus blocks. -/
theorem exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s : Finset ℝ} {t : Finset ℂ}
    (hst : s.card * 2 + t.card * 4 = finrank ℝ V) (hs0 : (0 : ℝ) ∉ s)
    (hPs : ∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ)
    (ht0 : ∀ z ∈ t, 0 < z.re ∧ 0 < z.im)
    (hPt : ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
      ω.hamiltonianEnd P w = z.im • v + z.re • w) :
    ∃ (b : Basis (Fin (s.card + t.card * 2) × Fin 2) ℝ V) (u : Finset (Fin s.card)),
      ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u)) := by
  set A := ω.hamiltonianEnd P
  have hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm :=
    ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  -- Split `V` along the subspace `L` of vectors killed by a power of `∏_{μ ∈ s} (A² - μ)`.
  set L := (aeval A (∏ μ ∈ s, (X ^ 2 - C μ))).maxGenEigenspace 0
  have hL : ω.IsSymplectic L :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (prod_X_sq_sub_C_comp_neg_X s id)
  have hmaps {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
      Set.MapsTo (ω.hamiltonianEnd R) L L :=
    Module.End.mapsTo_genEigenspace_aeval_of_comm (ω.quadraticPoissonBracket_eq_zero_iff.1
      (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hP hR)) _ 0 ⊤
  have hQL (i : ι) : L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i)) :=
    (Module.End.mem_invtSubmodule _).2 fun _ hx ↦ hmaps (Submodule.subset_span ⟨i, rfl⟩) hx
  have hAL : ∀ x ∈ L, A x ∈ L := fun _ hx ↦ hmaps hP hx
  -- `A` preserves `L^ω` too, since it is skew-adjoint.
  have hAL' : ∀ x ∈ ω.orthogonal L, A x ∈ ω.orthogonal L := fun x hx ↦
    mem_orthogonal_iff.2 fun y hy ↦ by
      rw [apply_hamiltonianEnd_right, ← apply_hamiltonianEnd, mem_orthogonal_iff.1 hx _ (hAL y hy),
        neg_zero]
  -- Counting dimensions: `dim L = 2 |s|` and `dim L^ω = 4 |t|`.
  have h₁ : s.card * 2 ≤ finrank ℝ L := card_mul_two_le_finrank_maxGenEigenspace hA hPs
  have h₂ : t.card * 4 ≤ finrank ℝ (ω.orthogonal L) :=
    card_mul_four_le_finrank_orthogonal hA s ht0 hPt
  have hsum := ω.finrank_add_finrank_orthogonal L
  -- The elliptic–hyperbolic classification on `L`, the focus-focus classification on `L^ω`.
  obtain ⟨m, b₁, u, hb₁, hspan₁⟩ :=
    (h.restrict hL hQL).exists_isDarbouxBasis_span_eq_span_ellipticHyperbolic
      (QuadraticMap.comp_mem_span_range_comp L.subtype hP) (by omega) hs0 fun μ hμ ↦ by
        rw [hamiltonianEnd_comp_subtype hL hAL]
        exact hasEigenvalue_restrict_sq hAL hμ (hPs μ hμ)
  obtain ⟨f, b₂, hb₂, hspan₂⟩ :=
    (h.restrict_orthogonal hL hQL).exists_isDarbouxBasis_span_eq_span_focusFocusBlocks
      (QuadraticMap.comp_mem_span_range_comp (ω.orthogonal L).subtype hP) (by omega) ht0
      fun z hz ↦ by
        rw [hamiltonianEnd_comp_subtype hL.orthogonal hAL']
        obtain ⟨v, w, hv, hAv, hAw⟩ := hPt z hz
        exact exists_restrict_orthogonal_apply_eq hA hAL' (ht0 z hz) hv hAv hAw
  -- The bases have `|s|` and `2 |t|` planes.
  have hm := finrank_eq_card_basis b₁
  have hf := finrank_eq_card_basis b₂
  simp only [Fintype.card_prod, Fintype.card_fin] at hm hf
  obtain rfl : m = s.card := by omega
  obtain rfl : f = t.card := by omega
  obtain ⟨b, hb, -, -, hspan⟩ :=
    h.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_isSymplectic hL hQL hb₁ hspan₁ hb₂
      hspan₂
  exact ⟨b, u, hb, hspan⟩

end IsNondegenerateQuadraticFamily

/-! ### The converse: a regular element -/

section Converse

variable {b t}

variable (b t) in
/-- The form `∑ₖ (k + 1) Bₖ + ∑ⱼ ((j + 1) Q₁ⱼ + Q₂ⱼ)` in the span of the Williamson blocks,
`Bₖ` the elliptic or hyperbolic block of the plane `k < m`. -/
private def williamsonRegular : QuadraticForm ℝ V :=
  ∑ k : Fin m, (((k : ℕ) : ℝ) + 1) • williamsonBlocks b t (.inl k) +
    ∑ j : Fin f, ((((j : ℕ) : ℝ) + 1) • williamsonBlocks b t (.inr (j, 0)) +
      williamsonBlocks b t (.inr (j, 1)))

omit [FiniteDimensional ℝ V] in
private theorem williamsonRegular_mem_span :
    williamsonRegular b t ∈ Submodule.span ℝ (Set.range (williamsonBlocks b t)) :=
  add_mem (Submodule.sum_mem _ fun _ _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.sum_mem _ fun _ _ ↦ add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩))

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_castAdd_fst
    (hb : ω.IsDarbouxBasis b) (k : Fin m) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.castAdd _ k, 0)) =
      (((k : ℕ) : ℝ) + 1) •
        (if k ∈ t then -b (Fin.castAdd _ k, 1) else b (Fin.castAdd _ k, 0)) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply, williamsonBlocks_inr,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
    hb.hamiltonianEnd_focusFocusBlocksAt_apply_of_forall_ne, smul_ite,
    (Fin.castAdd_injective _ _).eq_iff]

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_castAdd_snd
    (hb : ω.IsDarbouxBasis b) (k : Fin m) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.castAdd _ k, 1)) =
      (((k : ℕ) : ℝ) + 1) •
        (if k ∈ t then b (Fin.castAdd _ k, 0) else -b (Fin.castAdd _ k, 1)) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply, williamsonBlocks_inr,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_snd,
    hb.hamiltonianEnd_focusFocusBlocksAt_apply_of_forall_ne, smul_ite,
    (Fin.castAdd_injective _ _).eq_iff]

private theorem IsDarbouxBasis.hamiltonianEnd_williamsonRegular_natAdd
    (hb : ω.IsDarbouxBasis b) (j : Fin f) (i : Fin 2) :
    ω.hamiltonianEnd (williamsonRegular b t) (b (Fin.natAdd m (finProdFinEquiv (j, i)), 0)) =
      (((j : ℕ) : ℝ) + 1) • b (Fin.natAdd m (finProdFinEquiv (j, i)), 0) +
        if i = 0 then b (Fin.natAdd m (finProdFinEquiv (j, 1)), 0)
        else -b (Fin.natAdd m (finProdFinEquiv (j, 0)), 0) := by
  simp [williamsonRegular, map_sum, LinearMap.sum_apply, williamsonBlocks_inr,
    hb.hamiltonianEnd_williamsonBlocks_inl_apply_fst,
    hb.hamiltonianEnd_focusFocusBlocksAt_zero_apply Fin.natAdd_comp_finProdFinEquiv_injective,
    hb.hamiltonianEnd_focusFocusBlocksAt_one_apply Fin.natAdd_comp_finProdFinEquiv_injective,
    smul_ite, Finset.sum_add_distrib]

/-- In a Darboux basis, the square of the Hamiltonian endomorphism of the regular element has the
eigenvalue `-(k + 1)²` if the plane `k < m` is elliptic and `(k + 1)²` if it is hyperbolic. -/
private theorem IsDarbouxBasis.hasEigenvalue_hamiltonianEnd_williamsonRegular_sq
    (hb : ω.IsDarbouxBasis b) (k : Fin m) :
    (ω.hamiltonianEnd (williamsonRegular b t) ^ 2).HasEigenvalue
      (if k ∈ t then -((((k : ℕ) : ℝ) + 1) ^ 2) else (((k : ℕ) : ℝ) + 1) ^ 2) := by
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := b (Fin.castAdd _ k, 0))
    ⟨Module.End.mem_eigenspace_iff.2 ?_, b.ne_zero _⟩
  rw [sq, mul_apply_eq_comp, hb.hamiltonianEnd_williamsonRegular_castAdd_fst]
  by_cases hkt : k ∈ t <;>
    simp [hkt, hb.hamiltonianEnd_williamsonRegular_castAdd_fst,
      hb.hamiltonianEnd_williamsonRegular_castAdd_snd, smul_smul, sq]

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Nondegenerate families of mixed type.** The span of a nondegenerate family `Q` contains a
form `P` such that the square of its Hamiltonian endomorphism has distinct nonzero real
eigenvalues `μ ∈ s` and the Hamiltonian endomorphism itself has distinct eigenvalues
`z = a + bi ∈ t` with `a, b > 0`, each with an eigenvector `v + iw`, `v ≠ 0`, where
`2 |s| + 4 |t| = dim V`, exactly when it is the span of the Williamson blocks of some Darboux
basis. -/
theorem exists_mem_span_card_mul_two_add_card_mul_four_eq_finrank_iff
    (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ (s : Finset ℝ) (t : Finset ℂ),
        s.card * 2 + t.card * 4 = finrank ℝ V ∧ (0 : ℝ) ∉ s ∧
        (∀ μ ∈ s, (ω.hamiltonianEnd P ^ 2).HasEigenvalue μ) ∧ (∀ z ∈ t, 0 < z.re ∧ 0 < z.im) ∧
        ∀ z ∈ t, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
          ω.hamiltonianEnd P w = z.im • v + z.re • w) ↔
      ∃ (m f : ℕ) (b : Basis (Fin (m + f * 2) × Fin 2) ℝ V) (u : Finset (Fin m)),
        ω.IsDarbouxBasis b ∧
          Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (williamsonBlocks b u)) := by
  refine ⟨fun ⟨P, hP, s, t, hst, hs0, hPs, ht0, hPt⟩ ↦
    let ⟨b, u, hb, hspan⟩ :=
      h.exists_isDarbouxBasis_span_eq_span_williamsonBlocks_of_mem_span hP hst hs0 hPs ht0 hPt
    ⟨_, _, b, u, hb, hspan⟩,
    fun ⟨m, f, b, u, hb, hspan⟩ ↦ ?_⟩
  -- The regular element has the eigenvalues `∓(k + 1)²` of its square and `(j + 1) + i`.
  let z : Fin f → ℂ := fun j ↦ ((((j : ℕ) : ℝ) + 1 : ℝ) : ℂ) + Complex.I
  have hz : Function.Injective z := fun j j' hjj' ↦ by
    have := congrArg Complex.re hjj'
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, add_left_inj,
      Nat.cast_inj] at this
    exact Fin.ext this
  have hmono : StrictMono fun k : Fin m ↦ (((k : ℕ) : ℝ) + 1) ^ 2 := fun k l hkl ↦ by
    dsimp only
    gcongr
    exact_mod_cast hkl
  have hinj : Function.Injective fun k : Fin m ↦
      if k ∈ u then -((((k : ℕ) : ℝ) + 1) ^ 2) else (((k : ℕ) : ℝ) + 1) ^ 2 :=
    injective_ite_neg_sq u (fun _ _ hkl _ ↦ hmono.injective.ne hkl) fun _ ↦ by positivity
  refine ⟨williamsonRegular b u, hspan ▸ williamsonRegular_mem_span,
    Finset.univ.image fun k : Fin m ↦
      if k ∈ u then -((((k : ℕ) : ℝ) + 1) ^ 2) else (((k : ℕ) : ℝ) + 1) ^ 2,
    Finset.univ.image z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj,
      Finset.card_image_of_injective _ hz, finrank_eq_card_basis b]
    simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_prod]
    ring
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro k hk
    have := sq_pos_of_pos (by positivity : (0 : ℝ) < ((k : ℕ) : ℝ) + 1)
    by_cases hku : k ∈ u <;> simp only [hku, ↓reduceIte] at hk <;> linarith
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ k rfl
    exact hb.hasEigenvalue_hamiltonianEnd_williamsonRegular_sq k
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

end Converse

end TauCeti.SymplecticForm
