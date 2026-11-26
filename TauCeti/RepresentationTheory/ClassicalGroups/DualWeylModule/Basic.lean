/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.DeterminantalIdeal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The polynomial model of the dual Weyl modules of `GL_N`

Let `R` be a commutative semiring and `x = (x_{a,s})` an `N × n` matrix of variables, with `a` the
row and `s` the column. For a vector `d : Fin n → ℕ` of column degrees, the **dual Weyl module**
`TauCeti.dualWeylModule R N d` is the submodule of `R[x]` of the polynomials that are homogeneous of
degree `d s` in the column `s` for every `s`, and invariant under every column operation
`x ↦ x·(1 + T·e_{st})` with `s < t` (the column `t` replaced by itself plus `T` times the column
`s`), as an identity in `R[x][T]`. For the row lengths `d s = ν_s` of a partition `ν` with at most
`N` and at most `n` rows it is the polynomial model of the dual Weyl module `∇_R(ν)` of `GL_N` of
highest weight `ν`, the group acting on the rows. Over a field of characteristic zero `∇(ν)` is
the irreducible polynomial representation of highest weight `ν`; in positive characteristic it
need not be irreducible.

The operations are evaluated through `TauCeti.DualWeylModule.aeval_ite_mul_eq_pow_mul_aeval`
and `TauCeti.DualWeylModule.aeval_add_ite_mul_eq_aeval`: in every commutative `R`-algebra `S` and
at every matrix over `S`, scaling a column by `c` multiplies a member by `c` to the power of the
degree of that column, and adding `c` times an earlier column to a later one does not change its
value.

The minor of `x` on any `k` rows and the first `k` columns lies in the module of the column degrees
`(1, …, 1, 0, …, 0)` (`k` ones), and the modules form a graded monoid. So the **bideterminant**
`TauCeti.DualWeylModule.bideterminant` of a filling `T` of a Young diagram `μ` by rows of `x`, the
product over the columns `j` of `μ` of the minor on the rows listed in the column `j` of `T` and
the first `μ.colLen j` columns of `x`, lies in the module of the column degrees given by the row
lengths of `μ` (`TauCeti.DualWeylModule.bideterminant_mem_dualWeylModule`).

## Main definitions

* `TauCeti.DualWeylModule.columnOperation`: the column operation `x ↦ x·(1 + T·e_{st})`.
* `TauCeti.dualWeylModule`: the dual Weyl module of column degrees `d`.
* `TauCeti.DualWeylModule.columnMinor` and `TauCeti.DualWeylModule.bideterminant`: the minor of a
  filling of a Young diagram at one of its columns, and the bideterminant, their product.

## Main results

* `TauCeti.mem_dualWeylModule`: the defining conditions, as two statements about the monomials
  and about the column operations.
* `TauCeti.DualWeylModule.aeval_ite_mul_eq_pow_mul_aeval` and
  `TauCeti.DualWeylModule.aeval_add_ite_mul_eq_aeval`: the conditions specialised to any matrix
  over any commutative algebra.
* `TauCeti.DualWeylModule.map_mem_dualWeylModule_iff`: saturation, `∇_R(d) = ∇_S(d) ∩ R[x]` for
  an injective change of coefficients `R → S`.
* `TauCeti.DualWeylModule.mvPolynomialMinor_mem_dualWeylModule`: minors on initial columns are
  members.
* `TauCeti.DualWeylModule.bideterminant_mem_dualWeylModule`: bideterminants are members.

## References

For an `N × N` matrix and the column degrees of a normalised dominant weight this is the dual Weyl
lattice `TauCeti.dualWeylLattice` of the weight. The membership of minors and bideterminants is
adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC),
`src/Lib/GLn/SchurModule/Basic.lean` (`New.minor_mem_nabla`, `New.tableauPoly`), where the module
is defined as the semi-invariants of a Borel subgroup instead. The conventions follow
* C. De Concini, D. Eisenbud, C. Procesi, *Young diagrams and determinantal varieties*,
  Invent. Math. **56** (1980), 129-165.
-/

public section

namespace TauCeti

open MvPolynomial Finset

namespace DualWeylModule

variable (R : Type*) [CommSemiring R] {N n : ℕ}

/-- The **column operation** `x ↦ x·(1 + T·e_{st})` on the polynomials in an `N × n` matrix of
variables: the column `t` is replaced by itself plus `T` times the column `s`, as an algebra map
from `R[x]` to `R[x][T]`. -/
noncomputable def columnOperation (s t : Fin n) :
    MvPolynomial (Fin N × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin N × Fin n) R) :=
  aeval fun p => Polynomial.C (X p) + if p.2 = t then Polynomial.X * Polynomial.C (X (p.1, s))
    else 0

theorem columnOperation_def (s t : Fin n) :
    columnOperation (N := N) R s t = aeval fun p => Polynomial.C (X p) +
      if p.2 = t then Polynomial.X * Polynomial.C (X (p.1, s)) else 0 :=
  (rfl)

@[simp]
theorem columnOperation_X (s t : Fin n) (p : Fin N × Fin n) :
    columnOperation R s t (X p) =
      Polynomial.C (X p) + if p.2 = t then Polynomial.X * Polynomial.C (X (p.1, s)) else 0 :=
  aeval_X _ _

/-- At `T = 0` the column operation is the identity: the constant coefficient of
`columnOperation R s t g` is `g`. -/
@[simp]
theorem coeff_zero_columnOperation (s t : Fin n) (g : MvPolynomial (Fin N × Fin n) R) :
    (columnOperation R s t g).coeff 0 = g := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have h : (Polynomial.evalRingHom 0).comp (columnOperation (N := N) R s t).toRingHom =
      RingHom.id _ :=
    MvPolynomial.ringHom_ext (fun r => by simp [Polynomial.algebraMap_apply])
      fun p => by by_cases hp : p.2 = t <;> simp [hp]
  exact congr($h g)

end DualWeylModule

open DualWeylModule

variable (R : Type*) [CommSemiring R] {N n : ℕ}

/-- The **dual Weyl module** `∇_R(d)` of column degrees `d : Fin n → ℕ`: the polynomials over `R`
in the `N × n` matrix of variables `x_{a,s}` that are homogeneous of degree `d s` in the column `s`
for every `s`, and invariant under every column operation `x ↦ x·(1 + T·e_{st})` with `s < t`, as
an identity in `R[x][T]`. -/
noncomputable def dualWeylModule (N : ℕ) (d : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin N × Fin n) R) :=
  restrictSupport R {m | ∀ s, ∑ a, m (a, s) = d s} ⊓
    ⨅ (s : Fin n) (t : Fin n) (_ : s < t),
      LinearMap.eqLocus (columnOperation R s t).toLinearMap
        (Polynomial.CAlgHom (R := R) (A := MvPolynomial (Fin N × Fin n) R)).toLinearMap

variable {R} {d e : Fin n → ℕ} {f g : MvPolynomial (Fin N × Fin n) R}

/-- Membership in the dual Weyl module: every monomial has the column degrees `d`, and every
column operation `x ↦ x·(1 + T·e_{st})` with `s < t` fixes the polynomial. -/
theorem mem_dualWeylModule :
    f ∈ dualWeylModule R N d ↔
      (∀ m ∈ f.support, ∀ s, ∑ a, m (a, s) = d s) ∧
        ∀ s t : Fin n, s < t → columnOperation R s t f = Polynomial.C f := by
  simp [dualWeylModule, mem_restrictSupport_iff, Set.subset_def]

namespace DualWeylModule

/-- The monomials of a member of the dual Weyl module have the column degrees `d`. -/
theorem sum_apply_eq_of_mem_support (hf : f ∈ dualWeylModule R N d) {m : Fin N × Fin n →₀ ℕ}
    (hm : m ∈ f.support) (s : Fin n) : ∑ a, m (a, s) = d s :=
  (mem_dualWeylModule.mp hf).1 m hm s

/-- A member of the dual Weyl module is fixed by the column operations `x ↦ x·(1 + T·e_{st})`
with `s < t`. -/
theorem columnOperation_eq_C (hf : f ∈ dualWeylModule R N d) {s t : Fin n} (hst : s < t) :
    columnOperation R s t f = Polynomial.C f :=
  (mem_dualWeylModule.mp hf).2 s t hst

variable {S : Type*} [CommSemiring S] [Algebra R S]

/-- **Scaling a column.** If every monomial of `f` has degree `d t` in the column `t`, then
multiplying the column `t` of a matrix `M` over a commutative `R`-algebra by `c` multiplies the
value of `f` at `M` by `c ^ d t`. -/
theorem aeval_ite_mul_eq_pow_mul_aeval {t : Fin n}
    (hf : ∀ m ∈ f.support, ∑ a, m (a, t) = d t) (M : Fin N × Fin n → S) (c : S) :
    aeval (fun p => (if p.2 = t then c else 1) * M p) f = c ^ d t * aeval M f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  -- The factor contributed by the column `t` is `c` to the power of the degree of `m` there.
  have h_col : (m.prod fun p e => (if p.2 = t then c else 1) ^ e) = c ^ d t := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, ← hf m hm,
      ← Finset.prod_pow_eq_pow_sum, Finset.prod_comm]
    simp
  rw [← h_col]
  simp only [mul_pow, Finsupp.prod_mul]
  ring

/-- **Adding a multiple of a column.** If the column operation `x ↦ x·(1 + T·e_{st})` fixes `f`,
then adding `c` times the column `s` of a matrix `M` over a commutative `R`-algebra to its column
`t` does not change the value of `f` at `M`. -/
theorem aeval_add_ite_mul_eq_aeval {s t : Fin n} (hf : columnOperation R s t f = Polynomial.C f)
    (M : Fin N × Fin n → S) (c : S) :
    aeval (fun p => M p + if p.2 = t then c * M (p.1, s) else 0) f = aeval M f := by
  -- Evaluate the identity `hf` in `R[x][T]` at `x = M` and `T = c`.
  let ev : Polynomial (MvPolynomial (Fin N × Fin n) R) →ₐ[R] S :=
    Polynomial.eval₂AlgHom (aeval M) c fun _ => Commute.all _ _
  have h_comp : ev.comp (columnOperation R s t) =
      aeval fun p => M p + if p.2 = t then c * M (p.1, s) else 0 := by
    refine algHom_ext fun p => ?_
    by_cases hp : p.2 = t <;> simp [ev, hp]
    ring
  rw [← h_comp, AlgHom.comp_apply, hf]
  simp [ev]

end DualWeylModule

/-- The dual Weyl modules form a graded monoid: the product of members of column degrees `d` and
`e` is a member of column degrees `d + e`, and `1` is a member of column degrees `0`. -/
instance : SetLike.GradedMonoid (dualWeylModule R N : (Fin n → ℕ) → _) where
  one_mem := by
    rw [mem_dualWeylModule]
    refine ⟨fun m hm s => ?_, fun s t _ => by simp⟩
    rw [← C_1, mem_support_iff, coeff_C] at hm
    obtain rfl : m = 0 := by by_contra h; exact hm (ite_eq_right_iff.mpr fun h' => absurd h'.symm h)
    simp
  mul_mem := by
    classical
    intro d e f g hf hg
    rw [mem_dualWeylModule] at hf hg ⊢
    refine ⟨fun m hm s => ?_, fun s t hst => by simp [hf.2 s t hst, hg.2 s t hst]⟩
    obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
    simp [Finset.sum_add_distrib, hf.1 m₁ hm₁ s, hg.1 m₂ hm₂ s]

namespace DualWeylModule

section Map

variable {S : Type*} [CommSemiring S] (φ : R →+* S)

/-- The column operations commute with a change of coefficients. -/
theorem columnOperation_map (s t : Fin n) (f : MvPolynomial (Fin N × Fin n) R) :
    columnOperation S s t (map φ f) = Polynomial.map (map φ) (columnOperation R s t f) := by
  have h : (columnOperation S s t).toRingHom.comp (map φ) =
      (Polynomial.mapRingHom (map φ)).comp (columnOperation (N := N) R s t).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp [Polynomial.algebraMap_apply])
      fun p => by by_cases hp : p.2 = t <;> simp [hp]
  exact congr($h f)

/-- A change of coefficients maps the dual Weyl module over `R` into the one over `S`. -/
theorem map_mem_dualWeylModule (hf : f ∈ dualWeylModule R N d) :
    map φ f ∈ dualWeylModule S N d := by
  rw [mem_dualWeylModule] at hf ⊢
  refine ⟨fun m hm => hf.1 m (support_map_subset φ f hm), fun s t hst => ?_⟩
  rw [columnOperation_map, hf.2 s t hst, Polynomial.map_C]

/-- **Saturation.** For an injective change of coefficients `φ : R → S`, a polynomial over `R`
lies in the dual Weyl module over `R` as soon as its image lies in the one over `S`. For
`ℤ → ℚ` this is `∇_ℤ(d) = ∇_ℚ(d) ∩ ℤ[x]`. -/
theorem map_mem_dualWeylModule_iff {φ : R →+* S} (hφ : Function.Injective φ) :
    map φ f ∈ dualWeylModule S N d ↔ f ∈ dualWeylModule R N d := by
  refine ⟨fun hf => ?_, map_mem_dualWeylModule φ⟩
  rw [mem_dualWeylModule] at hf ⊢
  refine ⟨fun m hm => hf.1 m (by rwa [support_map_of_injective f hφ]), fun s t hst => ?_⟩
  have h := hf.2 s t hst
  rw [columnOperation_map, ← Polynomial.map_C] at h
  exact Polynomial.map_injective _ (map_injective φ hφ) h

end Map

end DualWeylModule

namespace DualWeylModule

section Minor

variable (R : Type*) [CommRing R] {N n : ℕ}

/-- The column degrees `(1, …, 1, 0, …, 0)`, with `k` ones, of a minor on the first `k`
columns. -/
def initialColumns (n k : ℕ) (s : Fin n) : ℕ := if (s : ℕ) < k then 1 else 0

@[simp]
theorem initialColumns_apply (n k : ℕ) (s : Fin n) :
    initialColumns n k s = if (s : ℕ) < k then 1 else 0 :=
  (rfl)

/-- Every monomial of a minor on the first `k` columns uses each of these columns once. -/
theorem mvPolynomialMinor_mem_restrictSupport {k : ℕ} (hk : k ≤ n) (r : Fin k → Fin N) :
    Matrix.mvPolynomialMinor R r (Fin.castLE hk) ∈
      restrictSupport R {m | ∀ s, ∑ a, m (a, s) = initialColumns n k s} := by
  classical
  rw [Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_of_tower_mem _ _ ?_
  have h_prod : ∏ i, (Matrix.mvPolynomialX (Fin N) (Fin n) R).submatrix r (Fin.castLE hk)
      (σ i) i = monomial (∑ i, Finsupp.single (r (σ i), Fin.castLE hk i) 1) (1 : R) := by
    simp [monomial_sum_one, X]
  rw [h_prod, monomial_mem_restrictSupport]
  refine Or.inl fun s => ?_
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Prod.mk.injEq]
  rw [Finset.sum_comm]
  have h_inner (i : Fin k) : (∑ a, if r (σ i) = a ∧ Fin.castLE hk i = s then 1 else 0) =
      if Fin.castLE hk i = s then 1 else 0 := by
    by_cases h : Fin.castLE hk i = s <;> simp [h]
  simp only [h_inner, Finset.sum_boole, initialColumns]
  split_ifs with hs
  · rw [Nat.cast_eq_one, Finset.card_eq_one]
    exact ⟨⟨s, hs⟩, by ext i; simp [Fin.ext_iff]⟩
  · simp only [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ h => hs (h ▸ i.isLt)

/-- A column operation fixes a minor on the first `k` columns: on these columns it adds `T` times
the column `s` to the column `t`, or it changes nothing. -/
private theorem columnOperation_mvPolynomialMinor {k : ℕ} (hk : k ≤ n) (r : Fin k → Fin N)
    {s t : Fin n} (hst : s < t) :
    columnOperation R s t (Matrix.mvPolynomialMinor R r (Fin.castLE hk)) =
      Polynomial.C (Matrix.mvPolynomialMinor R r (Fin.castLE hk)) := by
  let A : Matrix (Fin N) (Fin n) (Polynomial (MvPolynomial (Fin N × Fin n) R)) :=
    Matrix.of fun a b => Polynomial.C (X (a, b)) +
      if b = t then Polynomial.X * Polynomial.C (X (a, s)) else 0
  let B := ((Matrix.mvPolynomialX (Fin N) (Fin n) R).submatrix r (Fin.castLE hk)).map
    (Polynomial.C (R := MvPolynomial (Fin N × Fin n) R))
  have h_eval : columnOperation R s t = aeval fun p : Fin N × Fin n => A p.1 p.2 :=
    columnOperation_def R s t
  have h_C : Polynomial.C (Matrix.mvPolynomialMinor R r (Fin.castLE hk)) = B.det := by
    rw [Matrix.mvPolynomialMinor_eq_det_submatrix, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h_eval, Matrix.aeval_mvPolynomialMinor, h_C]
  by_cases htk : (t : ℕ) < k
  · have hsk : (s : ℕ) < k := lt_trans hst htk
    have h_upd : A.submatrix r (Fin.castLE hk) = B.updateCol ⟨t, htk⟩
        fun a => B a ⟨t, htk⟩ + (Polynomial.X : Polynomial (MvPolynomial (Fin N × Fin n) R)) •
          B a ⟨s, hsk⟩ := by
      ext a b
      by_cases hb : b = ⟨t, htk⟩
      · subst hb
        simp [A, B, Matrix.updateCol_self]
      · have hb' : Fin.castLE hk b ≠ t := fun h => hb (Fin.ext (by simpa [Fin.ext_iff] using h))
        simp [A, B, hb, hb']
    rw [h_upd, Matrix.det_updateCol_add_smul_self _ (fun h => hst.ne' (by
      simpa [Fin.ext_iff] using h))]
  · congr 1
    ext a b
    have hb : Fin.castLE hk b ≠ t := fun h => htk (h ▸ b.isLt)
    simp [A, B, hb]

/-- **Minors on initial columns are dual Weyl vectors.** The minor of `x` on any `k` rows `r` and
the first `k` columns lies in the dual Weyl module of the column degrees `(1, …, 1, 0, …, 0)`, with
`k` ones: a column operation either adds a multiple of one of these columns to another, which does
not change the determinant, or does not touch them. -/
theorem mvPolynomialMinor_mem_dualWeylModule {k : ℕ} (hk : k ≤ n) (r : Fin k → Fin N) :
    Matrix.mvPolynomialMinor R r (Fin.castLE hk) ∈ dualWeylModule R N (initialColumns n k) :=
  mem_dualWeylModule.mpr ⟨fun _ hm s => mvPolynomialMinor_mem_restrictSupport R hk r hm s,
    fun _ _ hst => columnOperation_mvPolynomialMinor R hk r hst⟩

/-- The weight `w_a` counting the variables of the row `a`: a monomial is weighted homogeneous of
degree `k` for it when it has degree `k` in the row `a`. -/
def rowWeight (a : Fin N) (p : Fin N × Fin n) : ℕ := if p.1 = a then 1 else 0

@[simp]
theorem rowWeight_apply (a : Fin N) (p : Fin N × Fin n) :
    rowWeight a p = if p.1 = a then 1 else 0 :=
  (rfl)

/-- **Minors are weight vectors.** A minor of `x` on the rows `r` has degree `#{i | r i = a}` in
the row `a`, the number of times `r` lists `a`. -/
theorem isWeightedHomogeneous_mvPolynomialMinor {k : Type*} [Fintype k] [DecidableEq k]
    (a : Fin N) (r : k → Fin N) (c : k → Fin n) :
    IsWeightedHomogeneous (rowWeight a) (Matrix.mvPolynomialMinor R r c)
      (Finset.univ.filter fun i => r i = a).card := by
  classical
  rw [Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply,
    ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun σ _ => Submodule.smul_of_tower_mem _ _ ?_
  rw [mem_weightedHomogeneousSubmodule]
  have h := IsWeightedHomogeneous.prod Finset.univ (fun i =>
    (X (r (σ i), c i) : MvPolynomial (Fin N × Fin n) R)) (fun i => rowWeight a (r (σ i), c i))
    (w := rowWeight a) fun i _ => isWeightedHomogeneous_X R _ _
  have h_deg : ∑ i, rowWeight a (r (σ i), c i) = (Finset.univ.filter fun i => r i = a).card := by
    simp only [rowWeight, Finset.sum_boole, Nat.cast_id]
    exact Finset.card_bij (fun i _ => σ i) (by simp) (fun _ _ _ _ h => σ.injective h)
      fun i hi => ⟨σ.symm i, by simpa using hi, by simp⟩
  rwa [h_deg] at h

/-- Summed over the columns `j` of a Young diagram `μ` (or over any longer range), the column
degrees of the minors on the first `μ.colLen j` columns are the row lengths of `μ`. -/
theorem sum_initialColumns_colLen (μ : YoungDiagram) {K : ℕ} (hK : μ.rowLen 0 ≤ K) :
    ∑ j ∈ range K, initialColumns n (μ.colLen j) = fun s : Fin n => μ.rowLen s := by
  classical
  ext s
  -- `s < μ.colLen j` says that `(s, j)` is a cell, that is `j < μ.rowLen s`.
  have h_filter : (range K).filter (fun j => (s : ℕ) < μ.colLen j) = range (μ.rowLen s) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, ← YoungDiagram.mem_iff_lt_colLen,
      YoungDiagram.mem_iff_lt_rowLen]
    exact ⟨And.right, fun h => ⟨h.trans_le ((μ.rowLen_anti 0 s (Nat.zero_le _)).trans hK), h⟩⟩
  simp [initialColumns, Finset.sum_boole, h_filter]

/-- The minor of a filling `T` of the Young diagram `μ` at its column `j`: the minor of the
`N × n` matrix of variables `x` on the rows `T (0, j), …, T (μ.colLen j - 1, j)` listed in the
column `j` of `T` and the first `μ.colLen j` columns of `x`. -/
noncomputable def columnMinor (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) (j : ℕ) : MvPolynomial (Fin N × Fin n) R :=
  Matrix.mvPolynomialMinor R
    (fun a : Fin (μ.colLen j) => T a j (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt))
    (Fin.castLE ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ))

theorem columnMinor_def (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) (j : ℕ) :
    columnMinor R μ hμ T j = Matrix.mvPolynomialMinor R
      (fun a : Fin (μ.colLen j) => T a j (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt))
      (Fin.castLE ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ)) :=
  (rfl)

/-- The minor of a filling at a column outside the Young diagram is the empty minor `1`. -/
theorem columnMinor_eq_one_of_rowLen_le (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) {j : ℕ} (hj : μ.rowLen 0 ≤ j) :
    columnMinor R μ hμ T j = 1 := by
  have h0 : μ.colLen j = 0 := by
    by_contra h
    have := YoungDiagram.mem_iff_lt_rowLen.mp
      (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h))
    exact absurd hj (not_le.mpr this)
  have : IsEmpty (Fin (μ.colLen j)) := by rw [h0]; infer_instance
  exact Matrix.mvPolynomialMinor_zero _ _

/-- The **bideterminant** `B_T` of a filling `T` of the Young diagram `μ` by rows of the `N × n`
matrix of variables `x`: the product over the columns `j` of `μ` of the minor of `x` on the rows
`T (0, j), …, T (μ.colLen j - 1, j)` listed in the column `j` of `T` and the first `μ.colLen j`
columns of `x` (`TauCeti.DualWeylModule.columnMinor`). The row `s` of `μ` corresponds to the
column `s` of `x`, so `μ` has at most `n` rows. -/
noncomputable def bideterminant (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) : MvPolynomial (Fin N × Fin n) R :=
  ∏ j ∈ range (μ.rowLen 0), columnMinor R μ hμ T j

/-- The bideterminant is the product of the column minors over any range of columns containing
those of `μ`: the further columns are empty and contribute the empty minor `1`. -/
theorem bideterminant_eq_prod_range (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) {K : ℕ} (hK : μ.rowLen 0 ≤ K) :
    bideterminant R μ hμ T = ∏ j ∈ range K, columnMinor R μ hμ T j := by
  rw [bideterminant, ← Finset.prod_range_mul_prod_Ico _ hK,
    Finset.prod_eq_one (s := Ico _ _) (fun j hj => columnMinor_eq_one_of_rowLen_le R μ hμ T
      (Finset.mem_Ico.mp hj).1), mul_one]

/-- **Bideterminants are dual Weyl vectors.** The bideterminant of a filling of a Young diagram
`μ` lies in the dual Weyl module whose column degrees are the row lengths of `μ`. -/
theorem bideterminant_mem_dualWeylModule (μ : YoungDiagram) (hμ : μ.colLen 0 ≤ n)
    (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) :
    bideterminant R μ hμ T ∈ dualWeylModule R N fun s : Fin n => μ.rowLen s := by
  rw [← sum_initialColumns_colLen μ le_rfl, bideterminant]
  exact SetLike.prod_mem_graded _ _ _ fun j _ => mvPolynomialMinor_mem_dualWeylModule R _ _

/-- Bideterminants commute with a change of coefficients. -/
@[simp]
theorem map_bideterminant {S : Type*} [CommRing S] (φ : R →+* S) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) (T : ∀ i j : ℕ, (i, j) ∈ μ → Fin N) :
    map φ (bideterminant R μ hμ T) = bideterminant S μ hμ T := by
  simp only [bideterminant_eq_prod_range _ μ hμ T le_rfl, map_prod, columnMinor_def,
    Matrix.map_mvPolynomialMinor]

end Minor

end DualWeylModule

end TauCeti
