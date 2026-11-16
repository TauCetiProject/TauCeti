/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.Algebra.Module.GradedModule.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.GradedAlgebra.FiniteType
import TauCeti.RingTheory.MvPolynomial.Finrank
import TauCeti.RingTheory.Polynomial.HilbertPoly
import TauCeti.RingTheory.PowerSeries.Expand

/-!
# The Hilbert–Serre theorem and finiteness of graded pieces

Let `B = ⨁_{i : ℕ} ℬ i` be a nonnegatively graded `A`-algebra and `M = ⨁_{d : ℤ} ℳ d` a finitely
generated `ℤ`-graded `B`-module (where the grading allows generators of negative degree).

## Finiteness of graded pieces

1. If `B` is an `ℕ`-graded commutative `A`-algebra of finite type over `ℬ 0` and `ℬ 0` is a finite
   `A`-module, then every graded piece `ℬ n` is a finite `A`-module
   (`moduleFinite_gradedPiece_of_finiteType`). No Noetherian hypothesis on `A` and no degree-one
   generation hypothesis on `B` are needed: `ℬ n` is spanned over `ℬ 0` by the finitely many
   monomials of weighted degree `n` in finitely many positive-degree homogeneous generators.
2. For any `ℕ`-graded semiring `B` and finitely generated `ℤ`-graded `B`-module `M`, the graded
   pieces `ℳ d` vanish for all `d` below the minimum degree of the homogeneous components of a
   finite `B`-generating set (`exists_forall_lt_piece_eq_bot`).
3. If in addition every `ℬ i` is a finite `A`-module, then every `ℳ d` is a finite `A`-module
   (`moduleFinite_piece`), again without assuming `A` is Noetherian: `ℳ d` is equal to the finite
   sum of the images of `ℬ (d - deg g)` under right-multiplication by finitely many homogeneous
   generators `g`. Over an Artinian ring `A`, every piece `ℳ d` therefore has finite `A`-length
   (`length_piece_ne_top`). For a polynomial algebra `MvPolynomial σ A`, the monomial basis,
   multichoose rank, and coefficient base-change compatibility of the homogeneous pieces are
   already provided in `TauCeti.RingTheory.MvPolynomial.Finrank`.

## The Hilbert–Serre theorem

Over a commutative Artinian ring `A`, let `M` be a finitely generated `ℤ`-graded module over the
standard polynomial ring `MvPolynomial σ A` on `e = Fintype.card σ` variables. Choose `d₀ : ℤ` so
that `ℳ d = ⊥` for all `d < d₀`. Inducting on `e` via multiplication by the last variable
`X (Fin.last e)` — whose kernel and cokernel are finitely generated `ℤ`-graded modules over `e - 1`
variables, by the Hilbert basis theorem since `A` is Artinian hence Noetherian — yields a polynomial
`h : ℤ[X]` such that
`(∑ n, (Module.length A (ℳ (d₀ + n))).toNat • Xⁿ) * (1 - X)^e = h` in `ℤ⟦X⟧`. In fact, because
any finite-length piece in sufficiently high degree generates the tail of `M` and has Artinian
annihilator quotient, the rational series identity holds over any commutative ring `A` and from any
starting degree `d₀ : ℤ` (`exists_hilbertSeries_mul_one_sub_X_pow`).

Translating Mathlib's `Polynomial.hilbertPoly` by `d₀` then supplies the eventual Hilbert
polynomial `P : ℚ[X]` of degree `< e`, taking integer values at every integer, and agreeing with
`Module.length A (ℳ d)` for all sufficiently large `d : ℤ` (`hilbertSerre`). Restricting scalars
along evaluation at finitely many algebra generators that shift grading by `1` transfers the
theorem to any standard finitely generated `A`-algebra (`hilbertSerre_of_adjoin_eq_top`), and over
a field `k` lengths coincide with `Module.finrank` (`hilbertSerre_field`). Finally, homogeneous
short exact sequences add lengths piece by piece (`length_piece_eq_add_of_exact`) and hence add
eventual Hilbert polynomials (`hilbertPoly_add_of_exact`), while shifting degrees by `a`
substitutes `X + C a` (`hilbertPoly_shift`).

## Main results

* `TauCeti.GradedAlgebra.moduleFinite_gradedPiece_of_finiteType`: every graded piece of a
  finite-type `ℕ`-graded algebra with finite degree-zero part is finite over the base.
* `TauCeti.GradedAlgebra.exists_forall_lt_piece_eq_bot`: a finitely generated `ℤ`-graded module
  over an `ℕ`-graded semiring vanishes below some degree `d₀`.
* `TauCeti.GradedAlgebra.moduleFinite_piece`: every graded piece of a finitely generated `ℤ`-graded
  module over an `ℕ`-graded semiring with finite pieces is finite over the base.
* `TauCeti.GradedAlgebra.length_piece_ne_top`: over an Artinian ring, every graded piece has finite
  length.
* `TauCeti.GradedAlgebra.length_piece_eq_add_of_exact`: additivity of piece lengths in a
  homogeneous short exact sequence over any cancellative grading monoid.
* `TauCeti.GradedAlgebra.exists_hilbertSeries_mul_one_sub_X_pow`: rational form `h / (1 - X)^e` of
  the shifted Hilbert series in `ℤ⟦X⟧` over any commutative ring and from any starting degree.
* `TauCeti.GradedAlgebra.hilbertSerre`: the Hilbert–Serre theorem for finitely generated `ℤ`-graded
  modules over `MvPolynomial σ A` for an Artinian ring `A`.
* `TauCeti.GradedAlgebra.hilbertSerre_of_adjoin_eq_top`: the Hilbert–Serre theorem for algebras
  generated by finitely many elements that shift the module grading by `1`.
* `TauCeti.GradedAlgebra.hilbertSerre_field`: the dimension-polynomial specialization over a field.
* `TauCeti.GradedAlgebra.hilbertPoly_add_of_exact` and `TauCeti.GradedAlgebra.hilbertPoly_shift`:
  additivity in degree-zero short exact sequences and behavior under degree shifts.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison–Wesley (1969),
  Chapter 11, Theorem 11.1.
* The Stacks Project, Algebra, Lemmas 10.58.5–10.58.7 (tags 00K7, 00K8, 00K9),
  <https://stacks.math.columbia.edu/tag/00K9>.
-/

public section

open DirectSum

namespace TauCeti.GradedAlgebra

universe u v w

/-! ### Finiteness of graded pieces -/

section GradedPiecesFinite

/-- For an `ℕ`-graded commutative algebra generated over `ℬ 0` by a finite set `s` of
positive-degree homogeneous elements with degrees `m : s → ℕ+`, the `n`-th graded piece `ℬ n`
equals the `ℬ 0`-span of the monomials of weighted degree `n` in `s`. -/
private theorem span_weightedAntidiag_eq_gradedPiece {A B : Type*} [CommSemiring A] [CommSemiring B]
    [DecidableEq B] [Algebra A B] (ℬ : ℕ → Submodule A B) [GradedAlgebra ℬ] {s : Finset B}
    (hs : Algebra.adjoin (ℬ 0) (s : Set B) = ⊤) (m : s → ℕ+) (hm : ∀ y : s, (y : B) ∈ ℬ (m y))
    (n : ℕ) :
    (Submodule.span (ℬ 0)
      ((((Finset.univ : Finset s).weightedFinsuppAntidiag m n).image
        fun l ↦ l.prod fun y e ↦ (y : B) ^ e) : Set B)).restrictScalars A = ℬ n := by
  let T : Finset B := ((Finset.univ : Finset s).weightedFinsuppAntidiag m n).image
    fun l ↦ l.prod fun y e ↦ (y : B) ^ e
  have hprod_mem (l : s →₀ ℕ) :
      (l.prod fun y e ↦ (y : B) ^ e) ∈ ℬ (∑ y : s, (m y : ℕ) * l y) := by
    have hw : (∑ y : s, (m y : ℕ) * l y) = l.sum fun y e ↦ e • (m y : ℕ) := by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
      exact Finset.sum_congr rfl fun y _ ↦ by simp [mul_comm]
    rw [hw]
    exact SetLike.prod_pow_mem_graded ℬ (fun y : s ↦ (m y : ℕ)) (fun y : s ↦ (y : B)) l
      fun y _ ↦ hm y
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases Finset.mem_image.mp hy with ⟨l, hl, rfl⟩
      rw [← (Finset.mem_weightedFinsuppAntidiag.mp hl).2]
      exact hprod_mem l
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul c y _ hy =>
      rw [Algebra.smul_def]
      simpa using SetLike.GradedMul.mul_mem c.2 hy
  · have hrange : (MvPolynomial.aeval (R := ℬ 0) (Subtype.val : s → B)).range = ⊤ := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      simpa [Subtype.range_coe_subtype] using hs
    have hx_range : x ∈ (MvPolynomial.aeval (R := ℬ 0) (Subtype.val : s → B)).range :=
      hrange ▸ (Algebra.mem_top : x ∈ (⊤ : Subalgebra (ℬ 0) B))
    obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).mp hx_range
    rw [← decompose_of_mem_same ℬ hx]
    clear hx hx_range
    induction p using MvPolynomial.induction_on' with
    | monomial d c =>
      rw [MvPolynomial.aeval_monomial, SetLike.GradeZero.algebraMap_apply]
      have hmem : (c : B) * (d.prod fun y e ↦ (y : B) ^ e) ∈ ℬ (∑ y : s, (m y : ℕ) * d y) := by
        simpa using SetLike.GradedMul.mul_mem c.2 (hprod_mem d)
      by_cases hwt : ∑ y : s, (m y : ℕ) * d y = n
      · rw [decompose_of_mem_same ℬ (hwt ▸ hmem)]
        have hdT : (d.prod fun y e ↦ (y : B) ^ e) ∈ T :=
          Finset.mem_image.mpr ⟨d, Finset.mem_weightedFinsuppAntidiag.mpr
            ⟨Finset.subset_univ _, hwt⟩, rfl⟩
        simpa only [Submodule.restrictScalars_mem, Algebra.smul_def,
          SetLike.GradeZero.algebraMap_apply] using
          Submodule.smul_mem (Submodule.span (ℬ 0) (T : Set B)) c (Submodule.subset_span hdT)
      · rw [decompose_of_mem_ne ℬ hmem hwt]
        exact zero_mem _
    | add p q hp hq =>
      rw [map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem hp hq

/-- Every graded piece of an `ℕ`-graded commutative algebra of finite type over its degree-zero
part, whose degree-zero part is finite over the base semiring, is a finite module over the base
semiring. -/
theorem moduleFinite_gradedPiece_of_finiteType {A B : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] (ℬ : ℕ → Submodule A B) [GradedAlgebra ℬ] [Algebra.FiniteType (ℬ 0) B]
    [Module.Finite A (ℬ 0)] (n : ℕ) : Module.Finite A (ℬ n) := by
  classical
  obtain ⟨s, hs, hdeg⟩ := exists_finset_adjoin_eq_top_and_mem_grade_ne_zero ℬ
  choose deg hdeg_ne hdeg_mem using fun y : s ↦ hdeg y.1 y.2
  let m : s → ℕ+ := fun y ↦ ⟨deg y, Nat.pos_of_ne_zero (hdeg_ne y)⟩
  let T : Finset B := ((Finset.univ : Finset s).weightedFinsuppAntidiag m n).image
    fun l ↦ l.prod fun y e ↦ (y : B) ^ e
  have hspan : (Submodule.span (ℬ 0) (T : Set B)).restrictScalars A = ℬ n :=
    span_weightedAntidiag_eq_gradedPiece ℬ hs m hdeg_mem n
  rw [Module.Finite.iff_fg, ← hspan]
  exact (Submodule.fg_span T.finite_toSet).restrictScalars

/-- A finitely generated module with an internal `ℤ`-grading is spanned over the acting semiring
by finitely many homogeneous elements. -/
private theorem exists_finset_homogeneous_span {A B M : Type*} [Semiring A] [Semiring B]
    [AddCommMonoid M] [Module A M] [Module B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ] :
    ∃ G : Finset (ℤ × M), (∀ p ∈ G, p.2 ∈ ℳ p.1) ∧
      Submodule.span B (Set.range fun p : G ↦ p.1.2) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := B) (M := M)
  let G : Finset (ℤ × M) :=
    S.biUnion fun s ↦ (decompose ℳ s).support.image fun j ↦ (j, (decompose ℳ s j : M))
  refine ⟨G, ?_, ?_⟩
  · intro p hp
    simp only [G, Finset.mem_biUnion, Finset.mem_image] at hp
    rcases hp with ⟨s, -, j, -, rfl⟩
    exact (decompose ℳ s j).2
  · rw [← top_le_iff, ← hS, Submodule.span_le]
    intro s hs
    rw [← sum_support_decompose ℳ s]
    refine Submodule.sum_mem _ fun j hj ↦ Submodule.subset_span ?_
    have hmem : (j, (decompose ℳ s j : M)) ∈ G :=
      Finset.mem_biUnion.mpr ⟨s, hs, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
    exact ⟨⟨(j, (decompose ℳ s j : M)), hmem⟩, rfl⟩

/-- The degree-`d` component of `b • m`, for `m ∈ ℳ j`, vanishes whenever `d < j`. -/
private theorem decompose_smul_eq_zero_of_lt {A B M : Type*} [Semiring A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i))
    {j d : ℤ} (hdj : d < j) (b : B) {m : M} (hm : m ∈ ℳ j) :
    (decompose ℳ (b • m) d : M) = 0 := by
  classical
  conv_lhs => rw [← sum_support_decompose ℬ b]
  rw [Finset.sum_smul, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  exact decompose_of_mem_ne ℳ (hgraded i j _ (decompose ℬ b i).2 m hm) (by omega)

/-- The degree-`d` component of `b • m`, for `m ∈ ℳ j` with `j ≤ d`, equals the degree-`(d - j)`
component of `b` acting on `m`. -/
private theorem decompose_smul_of_le {A B M : Type*} [Semiring A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i))
    {j d : ℤ} (hjd : j ≤ d) (b : B) {m : M} (hm : m ∈ ℳ j) :
    (decompose ℳ (b • m) d : M) = (decompose ℬ b (d - j).toNat : B) • m := by
  classical
  conv_lhs => rw [← sum_support_decompose ℬ b]
  rw [Finset.sum_smul, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single (d - j).toNat]
  · have hmem : (decompose ℬ b (d - j).toNat : B) • m ∈ ℳ d := by
      have h := hgraded (d - j).toNat j _ (decompose ℬ b (d - j).toNat).2 m hm
      rwa [show j + ((d - j).toNat : ℤ) = d by omega] at h
    exact decompose_of_mem_same ℳ hmem
  · intro i _ hi
    exact decompose_of_mem_ne ℳ (hgraded i j _ (decompose ℬ b i).2 m hm) (by omega)
  · intro hnot
    rw [DFinsupp.notMem_support_iff.mp hnot, ZeroMemClass.coe_zero, zero_smul]
    simp

/-- **Vanishing in sufficiently negative degrees.** A finitely generated `ℤ`-graded module over an
`ℕ`-graded semiring vanishes in all degrees below some integer `d₀`. -/
theorem exists_forall_lt_piece_eq_bot {A B M : Type*} [Semiring A] [Semiring B] [Module A B]
    (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    [AddCommMonoid M] [Module A M] [Module B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) :
    ∃ d₀ : ℤ, ∀ d < d₀, ℳ d = ⊥ := by
  classical
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := B) ℳ
  let d₀ : ℤ := if h : G.Nonempty then (G.image Prod.fst).min' (h.image _) else 0
  refine ⟨d₀, fun d hd ↦ (Submodule.eq_bot_iff _).mpr fun m hm ↦ ?_⟩
  have hm_span : m ∈ Submodule.span B (Set.range fun p : G ↦ p.1.2) := hGspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hm_span
  rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Finset.sum_eq_zero fun p _ ↦ ?_
  have hne : G.Nonempty := ⟨p.1, p.2⟩
  have hd_lt : d < p.1.1 := by
    have hle : d₀ ≤ p.1.1 := by
      simp only [d₀, hne, ↓reduceDIte]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩)
    exact hd.trans_le hle
  exact decompose_smul_eq_zero_of_lt ℬ ℳ hgraded hd_lt (c p) (hGmem p.1 p.2)

/-- **Finiteness of graded pieces.** Every graded piece of a finitely generated `ℤ`-graded module
over an `ℕ`-graded semiring whose graded pieces are finite `A`-modules is itself a finite
`A`-module. No Noetherian hypothesis on `A` is needed. -/
theorem moduleFinite_piece {A B M : Type*} [Semiring A] [Semiring B] [Module A B]
    (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ] (hℬ : ∀ i, Module.Finite A (ℬ i))
    [AddCommMonoid M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.Finite A (ℳ d) := by
  classical
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := B) ℳ
  -- For each generator `p ∈ G` with `p.1 ≤ d`, map `ℬ (d - p.1)` into `M` by `b ↦ b • p.2`.
  let φ : ∀ p : G, ℬ (d - p.1.1).toNat →ₗ[A] M := fun p ↦
    { toFun := fun b ↦ (b : B) • p.1.2
      map_add' := fun b₁ b₂ ↦ add_smul _ _ _
      map_smul' := fun a b ↦ by simp [smul_assoc] }
  let U : Submodule A M :=
    (Finset.univ.filter fun p : G ↦ p.1.1 ≤ d).sup fun p ↦ LinearMap.range (φ p)
  have hU_fg : U.FG := Submodule.fg_finset_sup _ _ fun p _ ↦ by
    have : Module.Finite A (ℬ (d - p.1.1).toNat) := hℬ _
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top (R := A)).map (φ p)
  have hU_eq : U = ℳ d := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup_le fun p hp ↦ ?_
      have hle : p.1.1 ≤ d := (Finset.mem_filter.mp hp).2
      rintro _ ⟨b, rfl⟩
      have h := hgraded (d - p.1.1).toNat p.1.1 b b.2 p.1.2 (hGmem p.1 p.2)
      rwa [show p.1.1 + ((d - p.1.1).toNat : ℤ) = d by omega] at h
    · intro m hm
      have hm_span : m ∈ Submodule.span B (Set.range fun p : G ↦ p.1.2) :=
        hGspan ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hm_span
      rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
      refine Submodule.sum_mem U fun p _ ↦ ?_
      by_cases hle : p.1.1 ≤ d
      · rw [decompose_smul_of_le ℬ ℳ hgraded hle (c p) (hGmem p.1 p.2)]
        have hpU : LinearMap.range (φ p) ≤ U :=
          Finset.le_sup (f := fun q : G ↦ LinearMap.range (φ q))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ p, hle⟩)
        exact hpU ⟨decompose ℬ (c p) (d - p.1.1).toNat, rfl⟩
      · rw [decompose_smul_eq_zero_of_lt ℬ ℳ hgraded (by omega) (c p) (hGmem p.1 p.2)]
        exact U.zero_mem
  exact Module.Finite.of_fg (hU_eq ▸ hU_fg)

/-- Every graded piece of a finitely generated `ℤ`-graded module over `MvPolynomial σ A` (with
finitely many variables `σ`) is a finite `A`-module. -/
theorem moduleFinite_piece_mvPolynomial {A σ M : Type*} [CommSemiring A] [Finite σ]
    [AddCommMonoid M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.Finite A (ℳ d) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  exact moduleFinite_piece (MvPolynomial.homogeneousSubmodule σ A)
    (fun i ↦ TauCeti.homogeneousSubmodule_moduleFinite i) ℳ hgraded d

/-- Over an Artinian ring `A`, every graded piece of a finitely generated `ℤ`-graded module over an
`ℕ`-graded semiring with finite pieces has finite `A`-length. -/
theorem length_piece_ne_top {A B M : Type*} [Ring A] [IsArtinianRing A] [Semiring B]
    [Module A B] (ℬ : ℕ → Submodule A B) [DirectSum.Decomposition ℬ]
    (hℬ : ∀ i, Module.Finite A (ℬ i)) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] [Module.Finite B M] (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (b : B), b ∈ ℬ i → ∀ m ∈ ℳ j, b • m ∈ ℳ (j + i)) (d : ℤ) :
    Module.length A (ℳ d) ≠ ⊤ := by
  have : Module.Finite A (ℳ d) := moduleFinite_piece ℬ hℬ ℳ hgraded d
  exact Module.length_ne_top_iff.mpr (TauCeti.isFiniteLength_of_finite A (ℳ d))

end GradedPiecesFinite

/-! ### Exact sequences of homogeneous pieces -/

section ExactLength

/-- In a short exact sequence of internally `ι`-graded `S`-modules where `f` has degree `r₁` and
`g` has degree `r₂` (over any cancellative additive monoid `ι`), the `A`-lengths of the pieces
satisfy `ℓ((ℳ₂)_{d + r₁}) = ℓ((ℳ₁)_d) + ℓ((ℳ₃)_{d + r₁ + r₂})`. -/
theorem length_piece_eq_add_of_exact {A S ι M₁ M₂ M₃ : Type*} [Ring A] [Semiring S] [SMul A S]
    [DecidableEq ι] [AddRightCancelMonoid ι]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    [IsScalarTower A S M₁] [IsScalarTower A S M₂] [IsScalarTower A S M₃]
    (ℳ₁ : ι → Submodule A M₁) [DirectSum.Decomposition ℳ₁]
    (ℳ₂ : ι → Submodule A M₂) [DirectSum.Decomposition ℳ₂]
    (ℳ₃ : ι → Submodule A M₃) [DirectSum.Decomposition ℳ₃]
    {f : M₁ →ₗ[S] M₂} {g : M₂ →ₗ[S] M₃} {r₁ r₂ : ι}
    (hf_hom : TauCeti.LinearMap.IsHomogeneous f ℳ₁ ℳ₂ r₁)
    (hg_hom : TauCeti.LinearMap.IsHomogeneous g ℳ₂ ℳ₃ r₂)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) (d : ι) :
    Module.length A (ℳ₂ (d + r₁)) =
      Module.length A (ℳ₁ d) + Module.length A (ℳ₃ (d + r₁ + r₂)) := by
  let fd : ℳ₁ d →ₗ[A] ℳ₂ (d + r₁) :=
    ((f.restrictScalars A).domRestrict (ℳ₁ d)).codRestrict (ℳ₂ (d + r₁)) fun x ↦ hf_hom.map_mem x.2
  let gd : ℳ₂ (d + r₁) →ₗ[A] ℳ₃ (d + r₁ + r₂) :=
    ((g.restrictScalars A).domRestrict (ℳ₂ (d + r₁))).codRestrict (ℳ₃ (d + r₁ + r₂)) fun y ↦
      hg_hom.map_mem y.2
  refine Module.length_eq_add_of_exact fd gd
    (fun x y h ↦ Subtype.ext (hf (congrArg Subtype.val h))) (fun z ↦ ?_) (fun y ↦ ?_)
  · obtain ⟨y, hy⟩ := hg z
    refine ⟨decompose ℳ₂ y (d + r₁), Subtype.ext ?_⟩
    have hdec := hg_hom.map_decompose (d + r₁) y
    rw [hy, decompose_of_mem_same ℳ₃ z.2] at hdec
    exact hdec
  · constructor
    · intro hy
      obtain ⟨x, hx⟩ := (hex y).mp (congrArg Subtype.val hy)
      refine ⟨decompose ℳ₁ x d, Subtype.ext ?_⟩
      have hdec := hf_hom.map_decompose d x
      rw [hx, decompose_of_mem_same ℳ₂ y.2] at hdec
      exact hdec
    · rintro ⟨x, rfl⟩
      exact Subtype.ext ((hex (f x)).mpr ⟨x, rfl⟩)

/-- For any homogeneous `S`-linear endomorphism `μ` of degree `r` on an internally `ι`-graded
`A`-module `G` (where `S` acts compatibly with `A`), the `A`-lengths of the pieces of `G`, `ker μ`,
and `coker μ = M ⧸ range μ` satisfy
`ℓ(G_j) + ℓ((coker μ)_{j + r}) = ℓ(G_{j + r}) + ℓ((ker μ)_j)`. -/
theorem length_piece_add_quotient_eq_add_ker {A S ι M : Type*} [Ring A] [Ring S] [SMul A S]
    [DecidableEq ι] [AddRightCancelMonoid ι]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (G : InternalGrading A M ι) {μ : M →ₗ[S] M} {r : ι}
    (hμ : TauCeti.LinearMap.IsHomogeneous μ G.piece G.piece r) (j : ι) :
    Module.length A (G.piece j) +
        Module.length A ((G.quotient (LinearMap.range μ) hμ.isHomogeneous_range).piece (j + r)) =
      Module.length A (G.piece (j + r)) + Module.length A ((G.ker hμ).piece j) := by
  let I := G.submodule (LinearMap.range μ) hμ.isHomogeneous_range
  let K := G.ker hμ
  let Q := G.quotient (LinearMap.range μ) hμ.isHomogeneous_range
  have hK_hom : TauCeti.LinearMap.IsHomogeneous (LinearMap.ker μ).subtype K.piece G.piece 0 :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by simpa using (G.mem_ker_piece hμ).mp hx
  have h1 := length_piece_eq_add_of_exact K.piece G.piece I.piece
    hK_hom (G.isHomogeneous_rangeRestrict hμ)
    (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict μ)
    (fun x ↦ ⟨fun hx ↦ ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩,
      fun ⟨⟨_, hy⟩, h⟩ ↦ Subtype.ext (h ▸ hy)⟩) j
  rw [add_zero] at h1
  have h2 := length_piece_eq_add_of_exact I.piece G.piece Q.piece
    (G.isHomogeneous_subtype (LinearMap.range μ) hμ.isHomogeneous_range)
    (G.isHomogeneous_mkQ (LinearMap.range μ) hμ.isHomogeneous_range)
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (fun x ↦ by simp [Submodule.Quotient.mk_eq_zero]) (j + r)
  rw [add_zero, add_zero] at h2
  rw [h1, h2]
  abel

end ExactLength

/-! ### Rational Hilbert–Serre series -/

section RationalSeries

/-- Scalar restriction along an `A`-algebra homomorphism preserves the scalar tower with `A`. -/
private theorem isScalarTower_compHom {A R S M : Type*} [CommSemiring A] [Semiring R] [Semiring S]
    [Algebra A R] [Algebra A S] [AddCommMonoid M] [Module A M] [Module S M] [IsScalarTower A S M]
    (f : R →ₐ[A] S) :
    let : Module R M := Module.compHom M f.toRingHom
    IsScalarTower A R M := by
  intro _
  exact ⟨fun a r m ↦ by
    -- Unfold the `Module.compHom` scalar action `r • m = f r • m`.
    change f (a • r) • m = a • (f r • m)
    rw [map_smul, smul_assoc]⟩

/-- If every `S`-scalar action on `M` can be realized through `f : R →+* S`, then finiteness over
`S` implies finiteness over `R` via `Module.compHom`. -/
private theorem moduleFinite_compHom_of_forall_smul {R S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module S M] [Module.Finite S M] (f : R →+* S)
    (h : ∀ (s : S) (m : M), ∃ r : R, s • m = f r • m) :
    let : Module R M := Module.compHom M f
    Module.Finite R M := by
  intro _
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := S) (M := M)
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨(T : Set M), T.finite_toSet, eq_top_iff.mpr fun m _ ↦ ?_⟩
  have hm : m ∈ Submodule.span S (T : Set M) := hT ▸ Submodule.mem_top
  clear ‹m ∈ ⊤›
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul s x _ hx =>
    obtain ⟨r, hr⟩ := h s x
    rw [hr]
    exact Submodule.smul_mem _ r hx

/-- A finitely generated module over `MvPolynomial (Fin (e + 1)) A` annihilated by the last
variable `X (Fin.last e)` is finitely generated over `MvPolynomial (Fin e) A` via `Fin.castSucc`. -/
private theorem moduleFinite_compHom_rename_castSucc {A : Type u} [CommRing A] {e : ℕ}
    {N : Type w} [AddCommGroup N] [Module (MvPolynomial (Fin (e + 1)) A) N]
    [Module.Finite (MvPolynomial (Fin (e + 1)) A) N]
    (hkill : ∀ z : N, (MvPolynomial.X (Fin.last e) : MvPolynomial (Fin (e + 1)) A) • z = 0) :
    let : Module (MvPolynomial (Fin e) A) N :=
      Module.compHom N (MvPolynomial.rename (R := A) Fin.castSucc).toRingHom
    Module.Finite (MvPolynomial (Fin e) A) N := by
  let ι : MvPolynomial (Fin e) A →ₐ[A] MvPolynomial (Fin (e + 1)) A :=
    MvPolynomial.rename Fin.castSucc
  let π : MvPolynomial (Fin (e + 1)) A →ₐ[A] MvPolynomial (Fin e) A :=
    MvPolynomial.aeval (Fin.lastCases 0 MvPolynomial.X)
  refine moduleFinite_compHom_of_forall_smul ι.toRingHom fun p z ↦ ⟨π p, ?_⟩
  induction p using MvPolynomial.induction_on generalizing z with
  | C a => simp [ι, π]
  | add p q hp hq => simp [add_smul, hp, hq]
  | mul_X p i hp =>
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · rw [mul_smul, hkill z, smul_zero, map_mul, map_mul]
      simp [π]
    · rw [mul_smul, hp, map_mul, map_mul, mul_smul]
      simp [ι, π]

/-- Coefficientwise length identity `(1 - X) * H_M = H_Q - X * H_K` for a degree-1 endomorphism
`μ` on an internally `ℤ`-graded module vanishing below `d₀`. -/
private theorem hilbertSeries_mul_one_sub_X {A S M : Type*} [Ring A] [Ring S] [SMul A S]
    [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower A S M]
    (G : InternalGrading A M ℤ) {μ : M →ₗ[S] M}
    (hμ : TauCeti.LinearMap.IsHomogeneous μ G.piece G.piece 1)
    {d₀ : ℤ} (hd₀ : ∀ d < d₀, G.piece d = ⊥)
    (hfinM : ∀ d, Module.length A (G.piece d) ≠ ⊤) :
    let GK := G.ker hμ
    let GQ := G.quotient (LinearMap.range μ) hμ.isHomogeneous_range
    (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (G.piece (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) =
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (GQ.piece (d₀ + n))).toNat : ℤ)) -
        PowerSeries.X *
          (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (GK.piece (d₀ + n))).toNat : ℤ)) := by
  intro GK GQ
  have hfinK (d : ℤ) : Module.length A (GK.piece d) ≠ ⊤ := by
    let fK : GK.piece d →ₗ[A] G.piece d :=
      { toFun := fun x ↦ ⟨x.1.1, (G.mem_ker_piece hμ).mp x.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hle : Module.length A (GK.piece d) ≤ Module.length A (G.piece d) :=
      Module.length_le_of_injective fK fun x y h ↦
        Subtype.ext (Subtype.ext (congrArg (Subtype.val : G.piece d → M) h))
    exact ne_top_of_le_ne_top (hfinM d) hle
  have hfinQ (d : ℤ) : Module.length A (GQ.piece d) ≠ ⊤ := by
    let I := G.submodule (LinearMap.range μ) hμ.isHomogeneous_range
    have h2 := length_piece_eq_add_of_exact I.piece G.piece GQ.piece
      (G.isHomogeneous_subtype (LinearMap.range μ) hμ.isHomogeneous_range)
      (G.isHomogeneous_mkQ (LinearMap.range μ) hμ.isHomogeneous_range)
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (fun x ↦ by simp [Submodule.Quotient.mk_eq_zero]) d
    rw [add_zero, add_zero] at h2
    exact ne_top_of_le_ne_top (hfinM d) (h2 ▸ le_add_self)
  have hstep (j : ℤ) :
      ((Module.length A (G.piece (j + 1))).toNat : ℤ) -
          ((Module.length A (G.piece j)).toNat : ℤ) =
        ((Module.length A (GQ.piece (j + 1))).toNat : ℤ) -
          ((Module.length A (GK.piece j)).toNat : ℤ) := by
    have h := congrArg ENat.toNat (length_piece_add_quotient_eq_add_ker G hμ j)
    rw [ENat.toNat_add (hfinM j) (hfinQ (j + 1)),
      ENat.toNat_add (hfinM (j + 1)) (hfinK j)] at h
    omega
  ext n
  rw [mul_sub, mul_one, map_sub, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  cases n with
  | zero =>
    simp only [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_mul_X, sub_zero]
    rw [Nat.cast_zero, add_zero]
    have hbotM : G.piece (d₀ - 1) = ⊥ := hd₀ (d₀ - 1) (by omega)
    have hbotK : GK.piece (d₀ - 1) = ⊥ := (Submodule.eq_bot_iff _).mpr fun x hx ↦
      Subtype.ext ((Submodule.eq_bot_iff _).mp hbotM x.1 ((G.mem_ker_piece hμ).mp hx))
    have h0 := hstep (d₀ - 1)
    rw [sub_add_cancel, hbotM, hbotK, Module.length_bot] at h0
    simpa using h0
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk]
    have heq : d₀ + ((n + 1 : ℕ) : ℤ) = (d₀ + (n : ℤ)) + 1 := by push_cast; ring
    rw [heq]
    exact hstep (d₀ + n)

/-- Base case (`e = 0` variables) of the rational Hilbert–Serre series: `M` is finite over `A`,
hence has only finitely many nonzero graded pieces, so its shifted Hilbert series is already a
polynomial. -/
private theorem exists_hilbertSeries_zero_vars {A : Type u} [CommRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module (MvPolynomial (Fin 0) A) M]
    [IsScalarTower A (MvPolynomial (Fin 0) A) M] [Module.Finite (MvPolynomial (Fin 0) A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ] (d₀ : ℤ) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ 0 = h.toPowerSeries := by
  classical
  have : Module.Finite A (MvPolynomial (Fin 0) A) :=
    Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).toLinearEquiv.symm
  have : Module.Finite A M := Module.Finite.trans (MvPolynomial (Fin 0) A) M
  let G := InternalGrading.ofDecomposition ℳ
  have hfin : {d : ℤ | ℳ d ≠ ⊥}.Finite := by
    simpa [G] using G.finite_piece_ne_bot
  let S : Finset ℕ := (hfin.toFinset.image fun d ↦ (d - d₀).toNat)
  let B : ℕ := if h : S.Nonempty then S.max' h + 1 else 0
  refine ⟨∑ k ∈ Finset.range B,
    Polynomial.monomial k ((Module.length A (ℳ (d₀ + k))).toNat : ℤ), ?_⟩
  rw [pow_zero, mul_one]
  ext n
  rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hn
  · rfl
  · have hbot : ℳ (d₀ + n) = ⊥ := by
      by_contra hne
      have hmemS : n ∈ S := by
        refine Finset.mem_image.mpr ⟨d₀ + n, hfin.mem_toFinset.mpr hne, ?_⟩
        omega
      have hle : n ≤ S.max' ⟨n, hmemS⟩ := Finset.le_max' S n hmemS
      have hB : B = S.max' ⟨n, hmemS⟩ + 1 := dite_eq_left ⟨n, hmemS⟩
      omega
    rw [hbot, Module.length_bot]
    simp

/-- Any finitely generated `ℤ`-graded `MvPolynomial (Fin (e + 1)) A`-module annihilated by
`X (Fin.last e)` restricts to a finitely generated `ℤ`-graded `MvPolynomial (Fin e) A`-module via
`Fin.castSucc`, allowing the induction hypothesis on `e` variables to apply. -/
private theorem exists_hilbertSeries_of_smul_last_eq_zero {A : Type u} [CommRing A] {e : ℕ}
    (ih : ∀ {N : Type w} [AddCommGroup N] [Module A N]
      [Module (MvPolynomial (Fin e) A) N] [IsScalarTower A (MvPolynomial (Fin e) A) N]
      [Module.Finite (MvPolynomial (Fin e) A) N]
      (𝒩 : ℤ → Submodule A N) [DirectSum.Decomposition 𝒩],
      (∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin e) A),
        p ∈ MvPolynomial.homogeneousSubmodule (Fin e) A i → ∀ n ∈ 𝒩 j, p • n ∈ 𝒩 (j + i)) →
      ∀ (d₀ : ℤ), (∀ d < d₀, 𝒩 d = ⊥) →
      ∃ h : Polynomial ℤ,
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (𝒩 (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ e = h.toPowerSeries)
    {N : Type w} [AddCommGroup N] [Module A N]
    [Module (MvPolynomial (Fin (e + 1)) A) N] [IsScalarTower A (MvPolynomial (Fin (e + 1)) A) N]
    [Module.Finite (MvPolynomial (Fin (e + 1)) A) N]
    (𝒩 : ℤ → Submodule A N) [DirectSum.Decomposition 𝒩]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin (e + 1)) A),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin (e + 1)) A i → ∀ n ∈ 𝒩 j, p • n ∈ 𝒩 (j + i))
    (hkill : ∀ z : N, (MvPolynomial.X (Fin.last e) : MvPolynomial (Fin (e + 1)) A) • z = 0)
    {d₀ : ℤ} (hd₀ : ∀ d < d₀, 𝒩 d = ⊥) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (𝒩 (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ e = h.toPowerSeries := by
  let ι : MvPolynomial (Fin e) A →ₐ[A] MvPolynomial (Fin (e + 1)) A :=
    MvPolynomial.rename Fin.castSucc
  let : Module (MvPolynomial (Fin e) A) N := Module.compHom N ι.toRingHom
  have : IsScalarTower A (MvPolynomial (Fin e) A) N := isScalarTower_compHom ι
  have : Module.Finite (MvPolynomial (Fin e) A) N := moduleFinite_compHom_rename_castSucc hkill
  exact ih 𝒩 (fun i j p hp n hn ↦ hgraded i j (ι p) hp.rename_isHomogeneous n hn) d₀ hd₀

/-- Induction step (`e → e + 1` variables) of the rational Hilbert–Serre series: multiplication by
`X (Fin.last e)` splits the problem into its kernel and cokernel, both finite over `e` variables. -/
private theorem exists_hilbertSeries_step {A : Type u} [CommRing A] [IsArtinianRing A] {e : ℕ}
    (ih : ∀ {N : Type w} [AddCommGroup N] [Module A N]
      [Module (MvPolynomial (Fin e) A) N] [IsScalarTower A (MvPolynomial (Fin e) A) N]
      [Module.Finite (MvPolynomial (Fin e) A) N]
      (𝒩 : ℤ → Submodule A N) [DirectSum.Decomposition 𝒩],
      (∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin e) A),
        p ∈ MvPolynomial.homogeneousSubmodule (Fin e) A i → ∀ n ∈ 𝒩 j, p • n ∈ 𝒩 (j + i)) →
      ∀ (d₀ : ℤ), (∀ d < d₀, 𝒩 d = ⊥) →
      ∃ h : Polynomial ℤ,
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (𝒩 (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ e = h.toPowerSeries)
    {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial (Fin (e + 1)) A) M] [IsScalarTower A (MvPolynomial (Fin (e + 1)) A) M]
    [Module.Finite (MvPolynomial (Fin (e + 1)) A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin (e + 1)) A),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin (e + 1)) A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    {d₀ : ℤ} (hd₀ : ∀ d < d₀, ℳ d = ⊥) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ (e + 1) = h.toPowerSeries := by
  let R := MvPolynomial (Fin (e + 1)) A
  let x : R := MvPolynomial.X (Fin.last e)
  let μ : M →ₗ[R] M := LinearMap.lsmul R M x
  let G := InternalGrading.ofDecomposition ℳ
  have hGp : G.piece = ℳ := InternalGrading.ofDecomposition_piece ℳ
  have hμ : TauCeti.LinearMap.IsHomogeneous μ G.piece G.piece (1 : ℤ) :=
    TauCeti.LinearMap.isHomogeneous_def.mpr fun j m hm ↦ by
      rw [hGp] at hm ⊢
      exact hgraded 1 j x (MvPolynomial.isHomogeneous_X A (Fin.last e)) m hm
  let K := LinearMap.ker μ
  let Q := M ⧸ LinearMap.range μ
  let GK := G.ker hμ
  let GQ := G.quotient (LinearMap.range μ) hμ.isHomogeneous_range
  let : IsNoetherianRing A := (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp ‹_›).1
  let : IsNoetherianRing R := MvPolynomial.isNoetherianRing
  have : Module.Finite R K := Module.Finite.of_fg (IsNoetherian.noetherian K)
  have : Module.Finite R Q :=
    Module.Finite.of_surjective (LinearMap.range μ).mkQ (Submodule.mkQ_surjective _)
  obtain ⟨hK, hhK⟩ := exists_hilbertSeries_of_smul_last_eq_zero ih GK.piece
    (fun i j p hp k hk ↦ by
      rw [G.mem_ker_piece, hGp] at hk ⊢
      exact hgraded i j p hp k.1 hk)
    (fun k ↦ Subtype.ext k.2)
    (fun d hd ↦ (Submodule.eq_bot_iff _).mpr fun k hk ↦
      Subtype.ext ((Submodule.eq_bot_iff _).mp (hd₀ d hd) k.1 (hGp ▸ (G.mem_ker_piece hμ).mp hk)))
  obtain ⟨hQ, hhQ⟩ := exists_hilbertSeries_of_smul_last_eq_zero ih GQ.piece
    (fun i j p hp q hq ↦ by
      obtain ⟨m, hm, rfl⟩ := (G.mem_quotient_piece_iff _ _).mp hq
      exact G.mk_mem_quotient_piece _ _ (hGp ▸ hgraded i j p hp m (hGp ▸ hm)))
    (fun q ↦ by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩)
    (fun d hd ↦ (Submodule.eq_bot_iff _).mpr fun q hq ↦ by
      obtain ⟨m, hm, rfl⟩ := (G.mem_quotient_piece_iff _ _).mp hq
      rw [(Submodule.eq_bot_iff _).mp (hd₀ d hd) m (hGp ▸ hm), Submodule.Quotient.mk_zero])
  let := MvPolynomial.gradedAlgebra (σ := Fin (e + 1)) (R := A)
  have hfinM : ∀ d, Module.length A (G.piece d) ≠ ⊤ := fun d ↦ by
    rw [hGp]
    exact length_piece_ne_top (MvPolynomial.homogeneousSubmodule (Fin (e + 1)) A)
      (fun i ↦ TauCeti.homogeneousSubmodule_moduleFinite i) ℳ hgraded d
  have hdiff := hilbertSeries_mul_one_sub_X G hμ (by simpa [hGp] using hd₀) hfinM
  rw [hGp] at hdiff
  refine ⟨hQ - Polynomial.X * hK, ?_⟩
  rw [pow_succ', ← mul_assoc, hdiff, sub_mul, mul_assoc, hhQ, hhK]
  simp

/-- Induction on the number `e` of polynomial variables for the rational Hilbert–Serre series. -/
private theorem exists_hilbertSeries_mul_one_sub_X_pow_fin {A : Type u} [CommRing A]
    [IsArtinianRing A] :
    ∀ (e : ℕ) {M : Type w} [AddCommGroup M] [Module A M]
      [Module (MvPolynomial (Fin e) A) M] [IsScalarTower A (MvPolynomial (Fin e) A) M]
      [Module.Finite (MvPolynomial (Fin e) A) M]
      (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ],
      (∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin e) A),
        p ∈ MvPolynomial.homogeneousSubmodule (Fin e) A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) →
      ∀ (d₀ : ℤ), (∀ d < d₀, ℳ d = ⊥) →
      ∃ h : Polynomial ℤ,
        (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
          (1 - PowerSeries.X) ^ e = h.toPowerSeries
  | 0, _, _, _, _, _, _, ℳ, _, _, d₀, _ =>
    exists_hilbertSeries_zero_vars ℳ d₀
  | e + 1, _, _, _, _, _, _, ℳ, _, hgraded, _, hd₀ =>
    exists_hilbertSeries_step (exists_hilbertSeries_mul_one_sub_X_pow_fin e) ℳ hgraded hd₀

/-- Rational Hilbert–Serre series over an Artinian base ring, from a vanishing bound `d₀`. -/
private theorem exists_hilbertSeries_mul_one_sub_X_pow_of_artinian {A : Type u} [CommRing A]
    [IsArtinianRing A] {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    {d₀ : ℤ} (hd₀ : ∀ d < d₀, ℳ d = ⊥) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries := by
  let e : Fin (Fintype.card σ) ≃ σ := (Fintype.equivFin σ).symm
  let φ : MvPolynomial (Fin (Fintype.card σ)) A ≃ₐ[A] MvPolynomial σ A :=
    MvPolynomial.renameEquiv A e
  let : Module (MvPolynomial (Fin (Fintype.card σ)) A) M := Module.compHom M φ.toRingHom
  have : IsScalarTower A (MvPolynomial (Fin (Fintype.card σ)) A) M :=
    isScalarTower_compHom φ.toAlgHom
  have : Module.Finite (MvPolynomial (Fin (Fintype.card σ)) A) M :=
    moduleFinite_compHom_of_forall_smul φ.toRingHom fun p m ↦
      ⟨φ.symm p, by rw [RingEquiv.toRingHom_eq_coe]; simp⟩
  have hgraded' : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial (Fin (Fintype.card σ)) A),
      p ∈ MvPolynomial.homogeneousSubmodule (Fin (Fintype.card σ)) A i →
        ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i) := fun i j p hp m hm ↦
    hgraded i j (φ p) hp.rename_isHomogeneous m hm
  exact exists_hilbertSeries_mul_one_sub_X_pow_fin (Fintype.card σ) ℳ hgraded' d₀ hd₀

/-- Shifting the starting degree of a formal power series preserves rationality with denominator
`(1 - X) ^ e`. -/
private theorem exists_mul_one_sub_X_pow_shift {f : ℤ → ℤ} {e : ℕ} {d₁ : ℤ} {h : Polynomial ℤ}
    (hh : (PowerSeries.mk fun n : ℕ ↦ f (d₁ + n)) * (1 - PowerSeries.X) ^ e = h.toPowerSeries)
    (d₀ : ℤ) :
    ∃ h' : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e = h'.toPowerSeries := by
  have hsplit (a b : ℤ) (hab : a ≤ b) :
      (PowerSeries.mk fun n : ℕ ↦ f (a + n)) =
        (∑ j ∈ Finset.range (b - a).toNat, Polynomial.monomial j (f (a + j))).toPowerSeries +
          PowerSeries.X ^ (b - a).toNat * (PowerSeries.mk fun n : ℕ ↦ f (b + n)) := by
    ext n
    rw [map_add, PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.finsetSum_coeff,
      PowerSeries.coeff_X_pow_mul']
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hlt hle
    · omega
    · rw [add_zero]
    · rw [zero_add, PowerSeries.coeff_mk]
      congr 1; omega
    · omega
  rcases le_total d₀ d₁ with hle | hle
  · let p₀ : Polynomial ℤ :=
      ∑ j ∈ Finset.range (d₁ - d₀).toNat, Polynomial.monomial j (f (d₀ + j))
    refine ⟨p₀ * (1 - Polynomial.X) ^ e + Polynomial.X ^ (d₁ - d₀).toNat * h, ?_⟩
    rw [hsplit d₀ d₁ hle, add_mul, mul_assoc, hh]
    simp [p₀]
  · let k : ℕ := (d₀ - d₁).toNat
    let p₀ : Polynomial ℤ := ∑ j ∈ Finset.range k, Polynomial.monomial j (f (d₁ + j))
    let q : Polynomial ℤ := h - p₀ * (1 - Polynomial.X) ^ e
    let S : PowerSeries ℤ := (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e
    have hXS : PowerSeries.X ^ k * S = q.toPowerSeries := by
      have h1 : p₀.toPowerSeries * (1 - PowerSeries.X) ^ e + PowerSeries.X ^ k * S =
          h.toPowerSeries := by
        rw [← hh, hsplit d₁ d₀ hle, add_mul, mul_assoc]
      have h2 := eq_sub_of_add_eq' h1
      simpa [q] using h2
    refine ⟨∑ n ∈ Finset.range (q.natDegree + 1), Polynomial.monomial n (q.coeff (n + k)), ?_⟩
    ext n
    have hcoeff : PowerSeries.coeff n S = q.coeff (n + k) := by
      have h1 := congrArg (PowerSeries.coeff (n + k)) hXS
      rw [PowerSeries.coeff_X_pow_mul, Polynomial.coeff_coe] at h1
      exact h1
    rw [hcoeff, Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with hn
    · rfl
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- The quotient of a commutative ring by the annihilator of a finite-length module is Artinian. -/
private theorem isArtinianRing_quotient_annihilator {A N : Type*} [CommRing A] [AddCommGroup N]
    [Module A N] (hfl : IsFiniteLength A N) :
    IsArtinianRing (A ⧸ Module.annihilator A N) := by
  have ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  have : Module.Finite A N := Module.finite_def.mpr (IsNoetherian.noetherian ⊤)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := N)
  let φ : A →ₗ[A] (T → N) :=
    { toFun := fun a t ↦ a • t.1
      map_add' := fun a b ↦ funext fun _ ↦ add_smul a b _
      map_smul' := fun r a ↦ funext fun _ ↦ mul_smul r a _ }
  have hker : LinearMap.ker φ = Module.annihilator A N := by
    ext a
    rw [LinearMap.mem_ker, Module.mem_annihilator]
    refine ⟨fun ha x ↦ ?_, fun ha ↦ funext fun t ↦ ha t.1⟩
    have hx : x ∈ Submodule.span A (T : Set N) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrFun ha ⟨y, hy⟩
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  have hinj : Function.Injective ((Module.annihilator A N).liftQ φ (le_of_eq hker.symm)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ_eq_bot']
    exact hker.symm
  have : IsArtinian A (A ⧸ Module.annihilator A N) := isArtinian_of_injective _ hinj
  exact isArtinian_of_tower A (M := A ⧸ Module.annihilator A N) this

/-- For a finitely generated `ℤ`-graded `MvPolynomial σ A`-module, all pieces from some degree `N₀`
onward are generated over `MvPolynomial σ A` by any single piece `ℳ N₁` with `N₁ ≥ N₀`. -/
private theorem exists_degree_ge_le_span_piece {A σ M : Type*} [CommSemiring A]
    [AddCommMonoid M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    ∃ N₀ : ℤ, ∀ N₁ ≥ N₀, ∀ d ≥ N₁,
      ℳ d ≤ (Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)).restrictScalars A := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  obtain ⟨G, hGmem, hGspan⟩ := exists_finset_homogeneous_span (B := MvPolynomial σ A) ℳ
  let N₀ : ℤ := if h : G.Nonempty then (G.image Prod.fst).max' (h.image _) else 0
  refine ⟨N₀, fun N₁ hN₁ d hd m hm ↦ ?_⟩
  have hm_span : m ∈ Submodule.span (MvPolynomial σ A) (Set.range fun p : G ↦ p.1.2) :=
    hGspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ A)).mp hm_span
  rw [← decompose_of_mem_same ℳ hm, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun p _ ↦ ?_
  have hp_le : p.1.1 ≤ N₁ := le_trans (by
    have hne : G.Nonempty := ⟨p.1, p.2⟩
    simp only [N₀, hne, ↓reduceDIte]
    exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p.1, p.2, rfl⟩)) hN₁
  rw [decompose_smul_of_le (MvPolynomial.homogeneousSubmodule σ A) ℳ hgraded (hp_le.trans hd)
    (c p) (hGmem p.1 p.2)]
  set q := decompose (MvPolynomial.homogeneousSubmodule σ A) (c p) (d - p.1.1).toNat
  have hdeg : (d - p.1.1).toNat = (d - N₁).toNat + (N₁ - p.1.1).toNat := by omega
  have hq : (q : MvPolynomial σ A) ∈
      MvPolynomial.homogeneousSubmodule σ A (d - N₁).toNat *
        MvPolynomial.homogeneousSubmodule σ A (N₁ - p.1.1).toNat := by
    have hpow1 : MvPolynomial.homogeneousSubmodule σ A (d - N₁).toNat =
        MvPolynomial.homogeneousSubmodule σ A 1 ^ (d - N₁).toNat :=
      (MvPolynomial.homogeneousSubmodule_one_pow A _).symm
    have hpow2 : MvPolynomial.homogeneousSubmodule σ A (N₁ - p.1.1).toNat =
        MvPolynomial.homogeneousSubmodule σ A 1 ^ (N₁ - p.1.1).toNat :=
      (MvPolynomial.homogeneousSubmodule_one_pow A _).symm
    rw [hpow1, hpow2, ← pow_add, MvPolynomial.homogeneousSubmodule_one_pow, ← hdeg]
    exact q.2
  refine Submodule.mul_induction_on hq (fun r₁ _ r₂ hr₂ ↦ ?_) (fun u v hu hv ↦ by
    rw [add_smul]; exact add_mem hu hv)
  rw [mul_smul]
  have hr₂m : r₂ • p.1.2 ∈ ℳ N₁ := by
    have h1 := hgraded (N₁ - p.1.1).toNat p.1.1 r₂ hr₂ p.1.2 (hGmem p.1 p.2)
    rwa [show p.1.1 + ((N₁ - p.1.1).toNat : ℤ) = N₁ by omega] at h1
  exact Submodule.smul_mem _ r₁ (Submodule.subset_span hr₂m)

/-- Every homogeneous polynomial over a quotient ring lifts to a homogeneous polynomial of the
same degree. -/
private theorem exists_isHomogeneous_map_eq {A B σ : Type*} [CommSemiring A] [CommSemiring B]
    {f : A →+* B} (hf : Function.Surjective f) {i : ℕ} {q : MvPolynomial σ B}
    (hq : q ∈ MvPolynomial.homogeneousSubmodule σ B i) :
    ∃ p ∈ MvPolynomial.homogeneousSubmodule σ A i, MvPolynomial.map f p = q := by
  classical
  let p : MvPolynomial σ A :=
    ∑ s ∈ q.support, MvPolynomial.monomial s (hf (q.coeff s)).choose
  refine ⟨p, Submodule.sum_mem _ fun s hs ↦
    MvPolynomial.isWeightedHomogeneous_monomial 1 s _ (hq (MvPolynomial.mem_support_iff.mp hs)),
    ?_⟩
  ext s
  rw [map_sum, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.map_monomial, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' q.support s]
  split_ifs with hs
  · exact (hf (q.coeff s)).choose_spec
  · exact (MvPolynomial.notMem_support_iff.mp hs).symm

/-- Lifting an `A`-module grading on a module annihilated by `I` to `A ⧸ I` preserves internal
direct sum decompositions. -/
private theorem isInternal_quotient_grade {A M : Type*} [CommRing A] (I : Ideal A) [AddCommGroup M]
    [Module A M] (hI : Module.IsTorsionBySet A M I) (ℳ : ℤ → Submodule A M)
    [DirectSum.Decomposition ℳ] :
    let : Module (A ⧸ I) M := hI.module
    DirectSum.IsInternal fun d : ℤ ↦
      ({ (ℳ d).toAddSubmonoid with
        smul_mem' := fun b x hx ↦ by
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
          exact (ℳ d).smul_mem a hx } : Submodule (A ⧸ I) M) := by
  let : Module (A ⧸ I) M := hI.module
  have : IsScalarTower A (A ⧸ I) M := hI.isScalarTower
  let ℳB : ℤ → Submodule (A ⧸ I) M := fun d ↦
    { (ℳ d).toAddSubmonoid with
      smul_mem' := fun b x hx ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (ℳ d).smul_mem a hx }
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    refine disjoint_iff.mpr ((Submodule.eq_bot_iff _).mpr fun x ⟨hx1, hx2⟩ ↦ ?_)
    have hle : (⨆ (j) (_ : j ≠ d), ℳB j).restrictScalars A ≤ ⨆ (j) (_ : j ≠ d), ℳ j := by
      refine (Submodule.restrictScalars_iSup _ _).le.trans (iSup_mono fun j ↦ ?_)
      exact (Submodule.restrictScalars_iSup _ _).le.trans (iSup_mono fun _ ↦ le_rfl)
    have hind := iSupIndep_def.mp (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep d
    have hmem : x ∈ ℳ d ⊓ ⨆ (j) (_ : j ≠ d), ℳ j := ⟨hx1, hle hx2⟩
    rw [disjoint_iff.mp hind] at hmem
    exact (Submodule.mem_bot _).mp hmem
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    have hge : ⨆ d, ℳ d ≤ (⨆ d, ℳB d).restrictScalars A :=
      iSup_le fun d ↦ (le_iSup (fun j ↦ (ℳB j).restrictScalars A) d).trans
        (Submodule.restrictScalars_iSup _ _).ge
    exact hge ((DirectSum.Decomposition.isInternal ℳ).submodule_iSup_eq_top ▸ Submodule.mem_top)

/-- If `M` is annihilated by `I ⊆ A`, then `M` is annihilated by the kernel of
`MvPolynomial.map (Ideal.Quotient.mk I)`. -/
private theorem isTorsionBySet_ker_mvPolynomial_map {A σ M : Type*} [CommRing A] (I : Ideal A)
    [AddCommGroup M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] (hI : Module.IsTorsionBySet A M I) :
    Module.IsTorsionBySet (MvPolynomial σ A) M
      (RingHom.ker (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk I))) := fun x ⟨p, hp⟩ ↦ by
  change p • x = 0
  rw [MvPolynomial.as_sum p, Finset.sum_smul]
  refine Finset.sum_eq_zero fun s _ ↦ ?_
  have hc : p.coeff s ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (by
    simpa [MvPolynomial.coeff_map] using congrArg (fun q ↦ q.coeff s) hp)
  rw [← mul_one (p.coeff s), ← MvPolynomial.C_mul_monomial, ← MvPolynomial.algebraMap_eq,
    ← Algebra.smul_def, smul_assoc]
  exact @hI (MvPolynomial.monomial s 1 • x) ⟨p.coeff s, hc⟩

/-- If an `R`-action on `M` factors through `π : R →+* S`, then finiteness over `R` implies
finiteness over `S`. -/
private theorem moduleFinite_of_ringHom_smul {R S M : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [Module S M] [Module.Finite R M] (π : R →+* S)
    (hπ : ∀ (r : R) (x : M), π r • x = r • x) : Module.Finite S M := by
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := M)
  refine Module.finite_def.mpr ⟨T, eq_top_iff.mpr fun x hx_top ↦ ?_⟩
  clear hx_top
  have hx : x ∈ Submodule.span R (T : Set M) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul r y _ hy => rw [← hπ]; exact Submodule.smul_mem _ (π r) hy

/-- Lifting an `A`-module grading on a module annihilated by `I` to `A ⧸ I` reduces the rational
Hilbert–Serre series to the Artinian ring `A ⧸ I`. -/
private theorem exists_hilbertSeries_of_isTorsionBySet {A : Type u} [CommRing A] (I : Ideal A)
    [IsArtinianRing (A ⧸ I)] {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M] (hI : Module.IsTorsionBySet A M I)
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    {d₀ : ℤ} (hd₀ : ∀ d < d₀, ℳ d = ⊥) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries := by
  let B := A ⧸ I
  let : Module B M := hI.module
  have : IsScalarTower A B M := hI.isScalarTower
  let π : MvPolynomial σ A →+* MvPolynomial σ B := MvPolynomial.map (Ideal.Quotient.mk I)
  have hπ_surj : Function.Surjective π := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker := isTorsionBySet_ker_mvPolynomial_map (σ := σ) I hI
  let eR : (MvPolynomial σ A ⧸ RingHom.ker π) ≃+* MvPolynomial σ B :=
    RingHom.quotientKerEquivOfSurjective hπ_surj
  let : Module (MvPolynomial σ A ⧸ RingHom.ker π) M := hker.module
  let : Module (MvPolynomial σ B) M := Module.compHom M eR.symm.toRingHom
  have hπ_smul (p : MvPolynomial σ A) (x : M) : π p • x = p • x := by
    change eR.symm (π p) • x = p • x
    have : eR (Ideal.Quotient.mk (RingHom.ker π) p) = π p := rfl
    rw [← this, RingEquiv.symm_apply_apply]
    exact hker.mk_smul p x
  have : IsScalarTower B (MvPolynomial σ B) M := ⟨fun b q x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p, rfl⟩ := hπ_surj q
    have hsm : Ideal.Quotient.mk I a • π p = π (a • p) := by
      simp [Algebra.smul_def, π, B]
    rw [hsm, hπ_smul, hπ_smul, smul_assoc, hI.mk_smul]⟩
  have : Module.Finite (MvPolynomial σ B) M := moduleFinite_of_ringHom_smul π hπ_smul
  let ℳB : ℤ → Submodule B M := fun d ↦
    { (ℳ d).toAddSubmonoid with
      smul_mem' := fun b x hx ↦ by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (ℳ d).smul_mem a hx }
  let : DirectSum.Decomposition ℳB := (isInternal_quotient_grade I hI ℳ).chooseDecomposition
  have hgradedB : ∀ (i : ℕ) (j : ℤ) (q : MvPolynomial σ B),
      q ∈ MvPolynomial.homogeneousSubmodule σ B i → ∀ m ∈ ℳB j, q • m ∈ ℳB (j + i) := by
    intro i j q hq m hm
    obtain ⟨p, hp, rfl⟩ := exists_isHomogeneous_map_eq Ideal.Quotient.mk_surjective hq
    rw [hπ_smul]
    exact hgraded i j p hp m hm
  have hlen (d : ℤ) : Module.length A (ℳ d) = Module.length B (ℳB d) :=
    (LinearEquiv.length_eq
      { toFun := fun x ↦ ⟨x.1, x.2⟩, invFun := fun x ↦ ⟨x.1, x.2⟩
        map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }).trans
      (Module.length_eq_of_surjective (S := A) (R := B) Ideal.Quotient.mk_surjective)
  simpa only [hlen] using exists_hilbertSeries_mul_one_sub_X_pow_of_artinian ℳB hgradedB
    (fun d hd ↦ Submodule.ext fun x ↦ by simp [ℳB, hd₀ d hd])

/-- The `MvPolynomial σ A`-submodule generated by a finite `A`-module piece `ℳ N₁` is finitely
generated over `MvPolynomial σ A`, has zero homogeneous components below `N₁`, and is annihilated
by `Module.annihilator A (ℳ N₁)`. -/
private theorem tail_span_properties {A : Type u} [CommRing A] {σ : Type v} {M : Type w}
    [AddCommGroup M] [Module A M] [Module (MvPolynomial σ A) M]
    [IsScalarTower A (MvPolynomial σ A) M] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    (N₁ : ℤ) [Module.Finite A (ℳ N₁)] :
    let M' : Submodule (MvPolynomial σ A) M := Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)
    Module.Finite (MvPolynomial σ A) M' ∧
      (∀ x ∈ M', ∀ d < N₁, (decompose ℳ x d : M) = 0) ∧
      Module.IsTorsionBySet A M' (Module.annihilator A (ℳ N₁)) := by
  classical
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  let R := MvPolynomial σ A
  intro M'
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := A) (M := ℳ N₁)
    refine Module.Finite.of_fg ⟨T.image Subtype.val, le_antisymm
      (Submodule.span_le.mpr fun x hx ↦ by
        rcases Finset.mem_image.mp hx with ⟨y, -, rfl⟩; exact Submodule.subset_span y.2)
      (Submodule.span_le.mpr fun x hx ↦ ?_)⟩
    suffices ∀ y : ℳ N₁, y.1 ∈ Submodule.span R ((T.image Subtype.val) : Set M) from this ⟨x, hx⟩
    intro y
    have hyA : y ∈ Submodule.span A (T : Set (ℳ N₁)) := hT ▸ Submodule.mem_top
    induction hyA using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span (Finset.mem_image_of_mem _ hz)
    | zero => exact zero_mem _
    | add z w _ _ hz hw => exact add_mem hz hw
    | smul a z _ hz =>
      rw [Submodule.coe_smul, ← algebraMap_smul R a z.1]
      exact Submodule.smul_mem _ _ hz
  · intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun d hd ↦ decompose_of_mem_ne ℳ hy (by omega)
    | zero => intro _ _; simp
    | add y z _ _ hy hz => intro d hd; simp [hy d hd, hz d hd]
    | smul p y _ hy =>
      intro d hd
      conv_lhs => rw [← sum_support_decompose ℳ y]
      rw [Finset.smul_sum, decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hjge : N₁ ≤ j := by
        by_contra hlt
        exact DFinsupp.mem_support_iff.mp hj (Subtype.ext (hy j (by omega)))
      exact decompose_smul_eq_zero_of_lt (MvPolynomial.homogeneousSubmodule σ A) ℳ hgraded
        (by omega) p (decompose ℳ y j).2
  · rintro ⟨x, hx⟩ ⟨a, ha⟩
    refine Subtype.ext ?_
    change a • x = 0
    induction hx using Submodule.span_induction with
    | mem y hy => exact congrArg Subtype.val (Module.mem_annihilator.mp ha ⟨y, hy⟩)
    | zero => exact smul_zero a
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul p y _ hy =>
      rw [← algebraMap_smul R a (p • y), smul_smul, mul_comm, ← smul_smul,
        algebraMap_smul, hy, smul_zero]

/-- A homogeneous submodule `M'` inherits an internal direct sum decomposition into pieces
`(ℳ d).comap M'.subtype`. -/
private theorem isInternal_comap_of_isHomogeneous {A M : Type*} [Ring A] [AddCommGroup M]
    [Module A M] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (M' : Submodule A M) (hM' : SetLike.IsHomogeneous ℳ M') :
    DirectSum.IsInternal fun d : ℤ ↦ (ℳ d).comap M'.subtype := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · rw [iSupIndep_def]
    intro d
    refine disjoint_iff.mpr ((Submodule.eq_bot_iff _).mpr fun x ⟨hx1, hx2⟩ ↦ Subtype.ext ?_)
    have hle : (⨆ (j) (_ : j ≠ d), (ℳ j).comap M'.subtype).map M'.subtype ≤
        ⨆ (j) (_ : j ≠ d), ℳ j := by
      rw [Submodule.map_iSup]
      exact iSup_le fun j ↦ by
        rw [Submodule.map_iSup]
        exact iSup_le fun hj ↦ (Submodule.map_comap_le M'.subtype (ℳ j)).trans
          (le_iSup₂ (f := fun j (_ : j ≠ d) ↦ ℳ j) j hj)
    have hind := iSupIndep_def.mp (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep d
    have hmem : x.1 ∈ ℳ d ⊓ ⨆ (j) (_ : j ≠ d), ℳ j := ⟨hx1, hle ⟨x, hx2, rfl⟩⟩
    rw [disjoint_iff.mp hind] at hmem
    exact (Submodule.mem_bot _).mp hmem
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    have hsum : x = ∑ d ∈ (decompose ℳ x.1).support,
        (⟨(decompose ℳ x.1 d : M), hM' d x.2⟩ : M') :=
      Subtype.ext (by rw [Submodule.coe_sum]; exact (sum_support_decompose ℳ x.1).symm)
    rw [hsum]
    refine Submodule.sum_mem _ fun d _ ↦
      le_iSup (fun j ↦ (ℳ j).comap M'.subtype) d (decompose ℳ x.1 d).2

/-- If a single sufficiently high piece `ℳ N₁` (generating the tail `d ≥ N₁` over
`MvPolynomial σ A`) has finite `A`-length, then the shifted Hilbert series from `N₁` is rational
with denominator `(1 - X) ^ Fintype.card σ`. -/
private theorem exists_hilbertSeries_of_tail_piece_length_ne_top {A : Type u} [CommRing A]
    {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    {N₁ : ℤ}
    (htail : ∀ d ≥ N₁, ℳ d ≤ (Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)).restrictScalars A)
    (hfin : Module.length A (ℳ N₁) ≠ ⊤) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (N₁ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries := by
  let M' : Submodule (MvPolynomial σ A) M := Submodule.span (MvPolynomial σ A) (ℳ N₁ : Set M)
  have hfl : IsFiniteLength A (ℳ N₁) := Module.length_ne_top_iff.mp hfin
  have : IsArtinianRing (A ⧸ Module.annihilator A (ℳ N₁)) :=
    isArtinianRing_quotient_annihilator hfl
  have : IsNoetherian A (ℳ N₁) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  have : Module.Finite A (ℳ N₁) := Module.finite_def.mpr (IsNoetherian.noetherian ⊤)
  obtain ⟨_, hlt_zero, hI_M'⟩ := tail_span_properties ℳ hgraded N₁
  have hM'_hom : SetLike.IsHomogeneous ℳ (M'.restrictScalars A) := fun d x hx ↦ by
    by_cases hd : d < N₁
    · rw [hlt_zero x hx d hd]; exact zero_mem _
    · exact htail d (by omega) (decompose ℳ x d).2
  let ℳ' : ℤ → Submodule A M' := fun d ↦ (ℳ d).comap (M'.restrictScalars A).subtype
  let : DirectSum.Decomposition ℳ' :=
    (isInternal_comap_of_isHomogeneous ℳ (M'.restrictScalars A) hM'_hom).chooseDecomposition
  obtain ⟨h, hh⟩ := exists_hilbertSeries_of_isTorsionBySet (d₀ := N₁) (Module.annihilator A (ℳ N₁))
    hI_M' ℳ' (fun i j p hp x hx ↦ hgraded i j p hp x.1 hx)
    (fun d hd ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ by
      have hxd : x.1 ∈ ℳ d := hx
      exact Subtype.ext (by rw [← decompose_of_mem_same ℳ hxd, hlt_zero x.1 x.2 d hd]; rfl))
  have hlen (n : ℕ) : Module.length A (ℳ' (N₁ + n)) = Module.length A (ℳ (N₁ + n)) :=
    LinearEquiv.length_eq
      { toFun := fun x ↦ ⟨x.1.1, x.2⟩
        invFun := fun y ↦ ⟨⟨y.1, htail (N₁ + n) (by omega) y.2⟩, y.2⟩
        map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl
        left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl }
  have hmk : (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ' (N₁ + n))).toNat : ℤ)) =
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (N₁ + n))).toNat : ℤ)) := by
    ext n; rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, hlen n]
  exact ⟨h, hmk ▸ hh⟩

/-- **Rational Hilbert–Serre series.** For any commutative ring `A` and any finitely generated
`ℤ`-graded module `M` over `MvPolynomial σ A` (with `σ` finite), the shifted Hilbert series from
any starting degree `d₀ : ℤ` multiplied by `(1 - X) ^ Fintype.card σ` is a polynomial in `ℤ[X]`. -/
theorem exists_hilbertSeries_mul_one_sub_X_pow {A : Type u} [CommRing A]
    {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    (d₀ : ℤ) :
    ∃ h : Polynomial ℤ,
      (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) *
        (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries := by
  obtain ⟨N₀, hN₀⟩ := exists_degree_ge_le_span_piece ℳ hgraded
  by_cases hex : ∃ N₁ ≥ N₀, Module.length A (ℳ N₁) ≠ ⊤
  · obtain ⟨N₁, hN₁, hfin⟩ := hex
    obtain ⟨h, hh⟩ := exists_hilbertSeries_of_tail_piece_length_ne_top ℳ hgraded (hN₀ N₁ hN₁) hfin
    exact exists_mul_one_sub_X_pow_shift
      (f := fun k ↦ ((Module.length A (ℳ k)).toNat : ℤ)) (d₁ := N₁) hh d₀
  · push Not at hex
    let B : ℕ := (N₀ - d₀).toNat
    let p : Polynomial ℤ := ∑ k ∈ Finset.range B,
      Polynomial.monomial k ((Module.length A (ℳ (d₀ + k))).toNat : ℤ)
    refine ⟨p * (1 - Polynomial.X) ^ Fintype.card σ, ?_⟩
    have hser : (PowerSeries.mk fun n : ℕ ↦ ((Module.length A (ℳ (d₀ + n))).toNat : ℤ)) =
        p.toPowerSeries := by
      ext n
      rw [PowerSeries.coeff_mk, Polynomial.coeff_coe, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range]
      split_ifs with hn
      · rfl
      · rw [hex (d₀ + n) (by omega), ENat.toNat_top, Nat.cast_zero]
    rw [hser]
    simp

end RationalSeries

/-! ### The Hilbert–Serre theorem and specializations -/

section HilbertSerre

/-- Mapping a rational Hilbert–Serre power-series identity from `ℤ⟦X⟧` to `ℚ⟦X⟧` and evaluating
the shifted rational Hilbert polynomial in sufficiently large degrees. -/
private theorem eval_hilbertPoly_map_rat_eq {f : ℤ → ℤ} {d₀ : ℤ} {h : Polynomial ℤ} {e : ℕ}
    (hh : (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) * (1 - PowerSeries.X) ^ e = h.toPowerSeries)
    {d : ℤ} (hd : d₀ + (h.natDegree : ℤ) + 1 ≤ d) :
    ((Polynomial.hilbertPoly (h.map (Int.castRingHom ℚ)) e).comp
      (Polynomial.X - Polynomial.C (d₀ : ℚ))).eval (d : ℚ) = (f d : ℚ) := by
  have hserQ : (PowerSeries.mk fun n : ℕ ↦ (f (d₀ + n) : ℚ)) * (1 - PowerSeries.X) ^ e =
      ((h.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
    have hmap := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hh
    rw [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X] at hmap
    have hmk : PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk fun n : ℕ ↦ f (d₀ + n)) =
        PowerSeries.mk fun n : ℕ ↦ (f (d₀ + n) : ℚ) := by
      ext n; simp
    have hcoe : PowerSeries.map (Int.castRingHom ℚ) (h : PowerSeries ℤ) =
        ((h.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ) := by
      ext n; simp
    rwa [hmk, hcoe] at hmap
  have hdeg : (h.map (Int.castRingHom ℚ)).natDegree ≤ h.natDegree := Polynomial.natDegree_map_le
  have hdQ : d₀ + ((h.map (Int.castRingHom ℚ)).natDegree : ℤ) + 1 ≤ d := by omega
  exact Polynomial.eval_hilbertPoly_comp_sub_eq_of_mul_one_sub_pow_eq
    (f := fun k ↦ (f k : ℚ)) (d₀ := d₀) (h := h.map (Int.castRingHom ℚ)) (e := e)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hserQ hdQ

/-- **The Hilbert–Serre theorem.** A finitely generated `ℤ`-graded module `M` over a standard
polynomial ring `MvPolynomial σ A` (with `A` Artinian and `σ` finite) has finite-length graded
pieces, vanishes below some integer `d₀`, has shifted Hilbert series `h(X) / (1 - X)^e` for some
`h : ℤ[X]` (where `e = Fintype.card σ`), and has an eventual rational Hilbert polynomial `P : ℚ[X]`
of degree strictly less than `e`. -/
theorem hilbertSerre (A : Type u) [CommRing A] [IsArtinianRing A]
    (σ : Type v) [Fintype σ] (M : Type w) [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i →
        ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite A (ℳ d) ∧ Module.length A (ℳ d) ≠ ⊤) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ =>
          ((Module.length A (ℳ (d₀ + n))).toNat : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = ((Module.length A (ℳ d)).toNat : ℚ) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := A)
  have hfin : ∀ d, Module.Finite A (ℳ d) ∧ Module.length A (ℳ d) ≠ ⊤ := fun d ↦
    ⟨moduleFinite_piece_mvPolynomial ℳ hgraded d,
      length_piece_ne_top (MvPolynomial.homogeneousSubmodule σ A)
        (fun i ↦ TauCeti.homogeneousSubmodule_moduleFinite i) ℳ hgraded d⟩
  obtain ⟨d₀, hd₀⟩ := exists_forall_lt_piece_eq_bot (MvPolynomial.homogeneousSubmodule σ A)
    ℳ hgraded
  obtain ⟨h, hh⟩ := exists_hilbertSeries_mul_one_sub_X_pow ℳ hgraded d₀
  let P : Polynomial ℚ :=
    (Polynomial.hilbertPoly (h.map (Int.castRingHom ℚ)) (Fintype.card σ)).comp
      (Polynomial.X - Polynomial.C (d₀ : ℚ))
  refine ⟨hfin, d₀, h, P, d₀ + (h.natDegree : ℤ) + 1, hd₀, hh,
    Polynomial.degree_hilbertPoly_comp_X_sub_C_lt _ _ _, fun d hd ↦ ?_⟩
  simpa only [Int.cast_natCast] using eval_hilbertPoly_map_rat_eq
    (f := fun k ↦ ((Module.length A (ℳ k)).toNat : ℤ)) hh hd

/-- Any eventual Hilbert polynomial `P : R[X]` (over a ring `R` with unique additive division) of a
finitely generated `ℤ`-graded `MvPolynomial σ A`-module takes integer values at every integer `z`,
and has degree strictly less than `Fintype.card σ`. -/
theorem exists_int_eval_of_eventually_eval_length {A : Type u} [CommRing A]
    {σ : Type v} [Fintype σ] {M : Type w} [AddCommGroup M] [Module A M]
    [Module (MvPolynomial σ A) M] [IsScalarTower A (MvPolynomial σ A) M]
    [Module.Finite (MvPolynomial σ A) M]
    (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i))
    {R : Type*} [Ring R] [HasUniqueDiv R] {P : Polynomial R} {N : ℤ}
    (hP : ∀ d : ℤ, N ≤ d → P.eval (d : R) = ((Module.length A (ℳ d)).toNat : R)) :
    P.degree < (Fintype.card σ : WithBot ℕ) ∧ ∀ z : ℤ, ∃ m : ℤ, P.eval (z : R) = (m : R) := by
  let e := Fintype.card σ
  obtain ⟨h, hh⟩ := exists_hilbertSeries_mul_one_sub_X_pow ℳ hgraded 0
  obtain ⟨Q, hQdeg, hQmap⟩ := Polynomial.exists_map_eq_factorial_nsmul_hilbertPoly h e
  have hmapQ (x : ℤ) : (Q.map (Int.castRingHom ℚ)).eval (x : ℚ) = ((Q.eval x : ℤ) : ℚ) := by
    have h1 := (Polynomial.hom_eval₂ Q (RingHom.id ℤ) (Int.castRingHom ℚ) x).symm
    rw [RingHom.comp_id, Int.coe_castRingHom] at h1
    rw [Polynomial.eval_map]; exact h1
  have hmapR (x : ℤ) : (Q.map (Int.castRingHom R)).eval (x : R) = ((Q.eval x : ℤ) : R) := by
    have h1 := (Polynomial.hom_eval₂ Q (RingHom.id ℤ) (Int.castRingHom R) x).symm
    rw [RingHom.comp_id, Int.coe_castRingHom] at h1
    rw [Polynomial.eval_map]; exact h1
  have hQ_eval (d : ℤ) (hd : (h.natDegree : ℤ) + 1 ≤ d) :
      Q.eval d = ((e - 1).factorial : ℤ) * ((Module.length A (ℳ d)).toNat : ℤ) := by
    apply Int.cast_injective (α := ℚ)
    have h1 := eval_hilbertPoly_map_rat_eq
      (f := fun k ↦ ((Module.length A (ℳ k)).toNat : ℤ)) hh (by simpa using hd)
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, ← hmapQ d, hQmap, Polynomial.eval_smul,
      nsmul_eq_mul]
    simpa [Polynomial.eval_comp] using congrArg (((e - 1).factorial : ℚ) * ·) h1
  have hPQ : (e - 1).factorial • P = Q.map (Int.castRingHom R) := by
    refine Polynomial.eq_of_forall_ge_intCast_eval_eq (N := max N ((h.natDegree : ℤ) + 1))
      fun d hd ↦ ?_
    rw [Polynomial.eval_smul, hP d (le_of_max_le_left hd), hmapR d,
      hQ_eval d (le_of_max_le_right hd), Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
      nsmul_eq_mul]
  refine ⟨?_, fun z ↦ ?_⟩
  · by_cases hP0 : P = 0
    · simp [hP0]
    · rw [Polynomial.degree_eq_natDegree hP0]
      norm_cast
      by_contra hge
      have hkQ : Q.coeff P.natDegree = 0 := Polynomial.coeff_eq_zero_of_degree_lt
        (hQdeg.trans_le (WithBot.coe_le_coe.mpr (Nat.le_of_not_lt hge)))
      have hc := congrArg (fun p : Polynomial R ↦ p.coeff P.natDegree) hPQ
      rw [AddMonoidAlgebra.coeff_smul_apply, Polynomial.coeff_map, hkQ, map_zero,
        ← nsmul_zero ((e - 1).factorial)] at hc
      exact Polynomial.leadingCoeff_ne_zero.mpr hP0
        (HasUniqueDiv.nsmul_right_injective (Nat.factorial_ne_zero _) hc)
  · obtain ⟨m, hm⟩ := Polynomial.exists_int_eval_hilbertPoly_map_intCast (F := ℚ) h e z
    have hQz : Q.eval z = ((e - 1).factorial : ℤ) * m := by
      apply Int.cast_injective (α := ℚ)
      rw [← hmapQ z, hQmap, Polynomial.eval_smul, nsmul_eq_mul, hm, Int.cast_mul, Int.cast_natCast]
    refine ⟨m, HasUniqueDiv.nsmul_right_injective (Nat.factorial_ne_zero (e - 1)) ?_⟩
    have h1 := congrArg (Polynomial.eval (z : R)) hPQ
    rw [Polynomial.eval_smul, hmapR z, hQz, Int.cast_mul, Int.cast_natCast, ← nsmul_eq_mul] at h1
    exact h1

/-- Evaluating a homogeneous polynomial at elements of `B` that shift the grading of `M` by `1`
shifts the grading of `M` by the polynomial's degree. -/
private theorem aeval_smul_mem_of_isHomogeneous {A B σ M : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [AddCommMonoid M] [Module A M] [Module B M] [IsScalarTower A B M]
    {f : σ → B} {ℳ : ℤ → Submodule A M}
    (hf : ∀ (s : σ) (j : ℤ) (m : M), m ∈ ℳ j → f s • m ∈ ℳ (j + 1))
    {i : ℕ} {j : ℤ} {p : MvPolynomial σ A} (hp : p ∈ MvPolynomial.homogeneousSubmodule σ A i)
    {m : M} (hm : m ∈ ℳ j) :
    (MvPolynomial.aeval f p) • m ∈ ℳ (j + i) := by
  have hpow (s : σ) (k : ℕ) (r : ℤ) (x : M) (hx : x ∈ ℳ r) :
      (f s ^ k) • x ∈ ℳ (r + k) := by
    induction k generalizing r x with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ', mul_smul]
      have h1 := hf s (r + k) _ (ih r x hx)
      rwa [show r + k + 1 = r + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h1
  have hprod (d : σ →₀ ℕ) (r : ℤ) (x : M) (hx : x ∈ ℳ r) :
      (d.prod fun s k ↦ f s ^ k) • x ∈ ℳ (r + ((Finsupp.weight (1 : σ → ℕ) d : ℕ) : ℤ)) := by
    induction d using Finsupp.induction generalizing r x with
    | zero => simpa using hx
    | single_add s k d _ _ ih =>
      rw [Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
        Finsupp.prod_single_index (h := fun s k ↦ f s ^ k) (pow_zero (f s)), mul_smul]
      have h1 := hpow s k _ _ (ih r x hx)
      have hwt : ((Finsupp.weight (1 : σ → ℕ) (Finsupp.single s k + d) : ℕ) : ℤ) =
          ((Finsupp.weight (1 : σ → ℕ) d : ℕ) : ℤ) + (k : ℤ) := by
        simp [map_add, Finsupp.weight_single, add_comm]
      rwa [add_assoc, ← hwt] at h1
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q _ _ hp hq =>
    rw [map_add, add_smul]
    exact (ℳ (j + i)).add_mem hp hq
  | monomial d a hd =>
    rw [MvPolynomial.aeval_monomial, mul_smul, algebraMap_smul]
    exact (ℳ (j + i)).smul_mem a (hd ▸ hprod d j m hm)

/-- **Hilbert–Serre for finitely generated algebras.** If `B` is a commutative `A`-algebra
generated over an Artinian ring `A` by finitely many elements `f : σ → B` each shifting a
`ℤ`-grading `ℳ` of a finitely generated `B`-module `M` by `1`, then `M` satisfies the
Hilbert–Serre theorem with denominator `(1 - X) ^ Fintype.card σ`. -/
theorem hilbertSerre_of_adjoin_eq_top {A : Type u} [CommRing A] [IsArtinianRing A]
    {B : Type*} [CommSemiring B] [Algebra A B] {σ : Type v} [Fintype σ] {f : σ → B}
    (hgen : Algebra.adjoin A (Set.range f) = ⊤)
    {M : Type w} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] (ℳ : ℤ → Submodule A M) [DirectSum.Decomposition ℳ]
    (hf : ∀ (i : σ) (j : ℤ) (m : M), m ∈ ℳ j → f i • m ∈ ℳ (j + 1)) :
    (∀ d, Module.Finite A (ℳ d) ∧ Module.length A (ℳ d) ≠ ⊤) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ =>
          ((Module.length A (ℳ (d₀ + n))).toNat : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = ((Module.length A (ℳ d)).toNat : ℚ) := by
  let φ : MvPolynomial σ A →ₐ[A] B := MvPolynomial.aeval f
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hgen
  let : Module (MvPolynomial σ A) M := Module.compHom M φ.toRingHom
  have : IsScalarTower A (MvPolynomial σ A) M := isScalarTower_compHom φ
  have : Module.Finite (MvPolynomial σ A) M :=
    moduleFinite_compHom_of_forall_smul φ.toRingHom fun b m ↦ by
      obtain ⟨p, rfl⟩ := hsurj b
      exact ⟨p, rfl⟩
  have hgraded' : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ A),
      p ∈ MvPolynomial.homogeneousSubmodule σ A i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i) :=
    fun _ _ _ hp _ hm ↦ aeval_smul_mem_of_isHomogeneous hf hp hm
  exact hilbertSerre A σ M ℳ hgraded'

/-- **Hilbert–Serre over a field.** For a finitely generated `ℤ`-graded module over a standard
polynomial ring `MvPolynomial σ k` over a field `k`, the Hilbert series and eventual Hilbert
polynomial compute `Module.finrank k (ℳ d)` and take integer values at all integers. -/
theorem hilbertSerre_field (k : Type u) [Field k]
    (σ : Type v) [Fintype σ] (M : Type w) [AddCommGroup M] [Module k M]
    [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
    [Module.Finite (MvPolynomial σ k) M]
    (ℳ : ℤ → Submodule k M) [DirectSum.Decomposition ℳ]
    (hgraded : ∀ (i : ℕ) (j : ℤ) (p : MvPolynomial σ k),
      p ∈ MvPolynomial.homogeneousSubmodule σ k i → ∀ m ∈ ℳ j, p • m ∈ ℳ (j + i)) :
    (∀ d, Module.Finite k (ℳ d)) ∧
      ∃ (d₀ : ℤ) (h : Polynomial ℤ) (P : Polynomial ℚ) (N : ℤ),
        (∀ d < d₀, ℳ d = ⊥) ∧
        (PowerSeries.mk (fun n : ℕ => (Module.finrank k (ℳ (d₀ + n)) : ℤ))) *
          (1 - PowerSeries.X) ^ Fintype.card σ = h.toPowerSeries ∧
        P.degree < (Fintype.card σ : WithBot ℕ) ∧
        (∀ z : ℤ, ∃ m : ℤ, P.eval (z : ℚ) = m) ∧
        ∀ d, N ≤ d → P.eval (d : ℚ) = (Module.finrank k (ℳ d) : ℚ) := by
  obtain ⟨hfin, d₀, h, P, N, hd₀, hh, hdeg, hP⟩ := hilbertSerre k σ M ℳ hgraded
  have hlen (d : ℤ) : (Module.length k (ℳ d)).toNat = Module.finrank k (ℳ d) := by
    have : Module.Finite k (ℳ d) := (hfin d).1
    rw [Module.length_eq_finrank, ENat.toNat_natCast]
  have hint := (exists_int_eval_of_eventually_eval_length ℳ hgraded hP).2
  refine ⟨fun d ↦ (hfin d).1, d₀, h, P, N, hd₀, ?_, hdeg, hint, fun d hd ↦ ?_⟩
  · simpa only [hlen] using hh
  · simpa only [hlen] using hP d hd

end HilbertSerre

/-! ### Additivity and shifts of eventual Hilbert polynomials -/

section AdditivityAndShift

/-- **Additivity of Hilbert polynomials.** In a degree-zero short exact sequence of internally
`ℤ`-graded `S`-modules (where `S` acts compatibly with `A`) whose middle pieces have finite
`A`-length for sufficiently large degrees, the eventual length polynomials over any ring with
unique additive division satisfy `P₂ = P₁ + P₃`. -/
theorem hilbertPoly_add_of_exact {A S M₁ M₂ M₃ R : Type*} [Ring A] [Semiring S] [SMul A S]
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module A M₁] [Module A M₂] [Module A M₃]
    [Module S M₁] [Module S M₂] [Module S M₃]
    [IsScalarTower A S M₁] [IsScalarTower A S M₂] [IsScalarTower A S M₃]
    (ℳ₁ : ℤ → Submodule A M₁) [DirectSum.Decomposition ℳ₁]
    (ℳ₂ : ℤ → Submodule A M₂) [DirectSum.Decomposition ℳ₂]
    (ℳ₃ : ℤ → Submodule A M₃) [DirectSum.Decomposition ℳ₃]
    {f : M₁ →ₗ[S] M₂} {g : M₂ →ₗ[S] M₃}
    (hf_hom : TauCeti.LinearMap.IsHomogeneous f ℳ₁ ℳ₂ 0)
    (hg_hom : TauCeti.LinearMap.IsHomogeneous g ℳ₂ ℳ₃ 0)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)
    [Ring R] [HasUniqueDiv R]
    {P₁ P₂ P₃ : Polynomial R} {N₀ N₁ N₂ N₃ : ℤ}
    (hfin : ∀ d : ℤ, N₀ ≤ d → Module.length A (ℳ₂ d) ≠ ⊤)
    (hP₁ : ∀ d : ℤ, N₁ ≤ d → P₁.eval (d : R) = ((Module.length A (ℳ₁ d)).toNat : R))
    (hP₂ : ∀ d : ℤ, N₂ ≤ d → P₂.eval (d : R) = ((Module.length A (ℳ₂ d)).toNat : R))
    (hP₃ : ∀ d : ℤ, N₃ ≤ d → P₃.eval (d : R) = ((Module.length A (ℳ₃ d)).toNat : R)) :
    P₂ = P₁ + P₃ := by
  refine Polynomial.eq_of_forall_ge_intCast_eval_eq (N := max (max N₀ N₂) (max N₁ N₃)) fun d hd ↦ ?_
  have hd0 : N₀ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_left hd)
  have hd2 : N₂ ≤ d := le_trans (le_max_right _ _) (le_of_max_le_left hd)
  have hd1 : N₁ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_right hd)
  have hd3 : N₃ ≤ d := le_trans (le_max_right _ _) (le_of_max_le_right hd)
  have hadd := length_piece_eq_add_of_exact ℳ₁ ℳ₂ ℳ₃ hf_hom hg_hom hf hg hex d
  rw [add_zero, add_zero] at hadd
  have hfin2 : Module.length A (ℳ₂ d) ≠ ⊤ := hfin d hd0
  have hfin1 : Module.length A (ℳ₁ d) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (hadd ▸ le_self_add)
  have hfin3 : Module.length A (ℳ₃ d) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin2 (hadd ▸ le_add_self)
  rw [Polynomial.eval_add, hP₁ d hd1, hP₂ d hd2, hP₃ d hd3, hadd,
    ENat.toNat_add hfin1 hfin3, Nat.cast_add]

/-- **Degree shifts of Hilbert polynomials.** If `ℳ' d` has the same `A`-length as `ℳ (d + a)` for
all sufficiently large degrees `d`, then their eventual length polynomials over any ring with
unique additive division are related by `P'(t) = P(t + a)`. -/
theorem hilbertPoly_shift {A M M' R : Type*} [Ring A] [AddCommGroup M] [AddCommGroup M']
    [Module A M] [Module A M']
    (ℳ : ℤ → Submodule A M) (ℳ' : ℤ → Submodule A M') (a : ℤ)
    [Ring R] [HasUniqueDiv R]
    {P P' : Polynomial R} {N₀ N N' : ℤ}
    (hshift : ∀ d : ℤ, N₀ ≤ d → Module.length A (ℳ' d) = Module.length A (ℳ (d + a)))
    (hP : ∀ d : ℤ, N ≤ d → P.eval (d : R) = ((Module.length A (ℳ d)).toNat : R))
    (hP' : ∀ d : ℤ, N' ≤ d → P'.eval (d : R) = ((Module.length A (ℳ' d)).toNat : R)) :
    P' = P.comp (Polynomial.X + Polynomial.C (a : R)) := by
  refine Polynomial.eq_of_forall_ge_intCast_eval_eq (N := max (max N₀ N') (N - a)) fun d hd ↦ ?_
  have hd0 : N₀ ≤ d := le_trans (le_max_left _ _) (le_of_max_le_left hd)
  have hd' : N' ≤ d := le_trans (le_max_right _ _) (le_of_max_le_left hd)
  have hda : N ≤ d + a := by have := le_of_max_le_right hd; omega
  have hcomp (Q : Polynomial R) : (Q.comp (Polynomial.X + Polynomial.C (a : R))).eval (d : R) =
      Q.eval ((d + a : ℤ) : R) := by
    have hmul (u v : Polynomial R) : (u * v).eval (d : R) = u.eval (d : R) * v.eval (d : R) :=
      Polynomial.eval₂_mul_noncomm (RingHom.id R) (d : R) fun _ ↦ (Int.cast_commute d _).symm
    have hpow (m : ℕ) : ((Polynomial.X + Polynomial.C (a : R)) ^ m).eval (d : R) =
        ((d + a : ℤ) : R) ^ m := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, hmul, ih, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          ← Int.cast_add, pow_succ]
    induction Q using Polynomial.induction_on' with
    | add p q hp hq => rw [Polynomial.add_comp, Polynomial.eval_add, Polynomial.eval_add, hp, hq]
    | monomial k r => rw [Polynomial.monomial_comp, Polynomial.eval_C_mul, hpow,
        Polynomial.eval_monomial]
  rw [hP' d hd', hshift d hd0, hcomp P, hP (d + a) hda]

end AdditivityAndShift

end TauCeti.GradedAlgebra
