/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import TauCeti.LinearAlgebra.LinearIndependent.Iterate
import TauCeti.LinearAlgebra.LinearMap.FixedPoints

/-!
# Fixed vectors of Frobenius-semilinear maps over algebraically closed fields

Let `k` be an algebraically closed field of characteristic `p > 0`, let `q = p ^ f` with `f > 0`,
and let `σ : k → k` be the `q`-power Frobenius `x ↦ x ^ q`. Let `V` be a finite-dimensional
`k`-vector space and `F : V → V` an injective `σ`-semilinear map. This file proves *Lang's lemma*:
`V` has a basis of `F`-fixed vectors. In matrix form, every invertible `A` over `k` can be
written as `B σ(B)⁻¹` for an invertible `B`, where `σ` acts entrywise; this is Lang's theorem for
the general linear group.

The fixed vectors are not a `k`-subspace, only an `𝔽_q`-subspace, so the result is genuinely
nonlinear. The proof has two steps.

* A nonzero `F`-fixed vector exists. Choose `v ≠ 0` and let `v, F v, …, Fⁿ v` be linearly
  independent with `Fⁿ⁺¹ v = ∑ aᵢ Fⁱ v`. The vector `∑ dⱼ Fʲ v` is fixed exactly when its
  coordinates `dⱼ` satisfy `d₀ = a₀ σ(dₙ)` and `dⱼ₊₁ = σ(dⱼ) + aⱼ₊₁ σ(dₙ)`. Writing `t = dₙ`, all
  coordinates are additive polynomials in `t`, and the remaining condition is one polynomial
  equation `∑ σⁿ⁻ⁱ(aᵢ) t ^ (qⁿ⁻ⁱ⁺¹) = t` in `t`, which has a nonzero root in `k`.
* The fixed vectors span. Otherwise `F` induces an injective semilinear map on the quotient by
  their span, which has a nonzero fixed vector by the first step. A lift `w` of it satisfies
  `F w = w + ∑ cᵢ vᵢ` with `vᵢ` fixed, and solving the Artin–Schreier equations
  `sᵢ ^ q - sᵢ = -cᵢ` makes `w + ∑ sᵢ vᵢ` fixed, a contradiction.

This is the residue-field step of the Dieudonné–Manin classification: over `k⟦π⟧` with the
coefficientwise Frobenius, an invertible matrix `A` is likewise `B σ(B)⁻¹`, by lifting the
solution modulo `π` through successive approximation, so that unit-root Frobenius modules are
trivial.

## Main results

* `LinearMap.exists_ne_zero_isFixedPt_of_injective_iterateFrobenius`: an injective
  Frobenius-semilinear map on a nonzero finite-dimensional space has a nonzero fixed vector.
* `LinearMap.span_fixedPoints_eq_top_of_injective_iterateFrobenius`: its fixed vectors span the
  space.
* `LinearMap.exists_basis_isFixedPt_of_injective_iterateFrobenius`: the space has a basis of fixed
  vectors.
* `Matrix.exists_isUnit_mul_map_iterateFrobenius_eq`: Lang's theorem for `GLₙ(k)`, every
  invertible `A` has an invertible `B` with `A σ(B) = B`.

## References

* S. Lang, *Algebraic groups over finite fields*, Amer. J. Math. 78 (1956), 555–563, for Lang's
  theorem for connected algebraic groups, of which the matrix form here is the case `GLₙ`.
* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer, 1973, §4.1, for fixed vectors of
  unit-root Frobenius modules.
-/

public section

open Function Polynomial Submodule Module Finset

namespace IsAlgClosed

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, for `q > 1` and coefficients `a₀, …, aₙ` not all zero, the
equation `∑ aᵢ ^ (q ^ (n - i)) t ^ (q ^ (n - i + 1)) = t` has a nonzero solution `t`. -/
private theorem exists_ne_zero_sum_pow_eq_self {q : ℕ} (hq : 1 < q) (a : ℕ → k) (n : ℕ)
    (ha : ∃ i ≤ n, a i ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ ∑ i ∈ range (n + 1), a i ^ q ^ (n - i) * t ^ q ^ (n - i + 1) = t := by
  set g : k[X] := ∑ i ∈ range (n + 1), C (a i ^ q ^ (n - i)) * X ^ q ^ (n - i + 1) with hg_def
  have hcoeff (d : ℕ) : g.coeff d =
      ∑ i ∈ range (n + 1), if d = q ^ (n - i + 1) then a i ^ q ^ (n - i) else 0 := by
    simp only [g, finsetSum_coeff, coeff_C_mul_X_pow]
  have hg : g ≠ 0 := by
    obtain ⟨i₀, hi₀, hai₀⟩ := ha
    intro h
    have h₀ := hcoeff (q ^ (n - i₀ + 1))
    rw [h, coeff_zero, Finset.sum_eq_single i₀] at h₀
    · simp only [↓reduceIte] at h₀
      exact hai₀ (pow_eq_zero_iff (by positivity) |>.1 h₀.symm)
    · intro i hi hne
      refine ite_eq_right_iff.2 fun heq ↦ ?_
      have := Nat.pow_right_injective hq heq
      simp only [mem_range] at hi
      omega
    · intro h
      simp only [mem_range] at h
      omega
  obtain ⟨h, hgh⟩ : X ^ 2 ∣ g := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [hcoeff]
    refine Finset.sum_eq_zero fun i _ ↦ ite_eq_right_iff.2 fun heq ↦ ?_
    have : q ≤ q ^ (n - i + 1) := Nat.le_self_pow (by omega) q
    omega
  have hh : h ≠ 0 := by
    rintro rfl
    exact hg (by rw [hgh, mul_zero])
  have hdeg : (X * h - 1).natDegree = h.natDegree + 1 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hh]
  obtain ⟨t, ht⟩ := exists_root (X * h - 1)
    (degree_ne_of_natDegree_ne (by rw [hdeg]; exact Nat.succ_ne_zero _))
  have ht' : t * h.eval t = 1 := by simpa [sub_eq_zero] using ht
  refine ⟨t, fun h0 ↦ by simp [h0] at ht', ?_⟩
  have := congrArg (Polynomial.eval t) hgh
  simp only [hg_def, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at this
  rw [this, sq, mul_assoc, ht', mul_one]

end IsAlgClosed

namespace LinearMap

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable {p f : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k]

/-- **A nonzero fixed vector.** Over an algebraically closed field `k` of characteristic `p`, an
injective `σ`-semilinear map `F` on a nonzero finite-dimensional space, for the Frobenius
`σ x = x ^ p ^ f` with `f ≠ 0`, has a nonzero fixed vector. -/
theorem exists_ne_zero_isFixedPt_of_injective_iterateFrobenius [FiniteDimensional k V]
    [Nontrivial V] (hf : f ≠ 0) {F : V →ₛₗ[_root_.iterateFrobenius k p f] V} (hF : Injective F) :
    ∃ x, x ≠ 0 ∧ IsFixedPt F x := by
  set q := p ^ f
  have hq : 1 < q := Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt
  have hσ (c : k) : _root_.iterateFrobenius k p f c = c ^ q := _root_.iterateFrobenius_def p f c
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨n, hli, hspan⟩ := exists_linearIndependent_iterate_mem_span (K := k) F hv
  obtain ⟨a', ha'⟩ := (mem_span_range_iff_exists_fun k).1 hspan
  -- the coefficients of the relation `Fⁿ⁺¹ v = ∑ aᵢ Fⁱ v`, indexed by `ℕ`
  set a : ℕ → k := fun i ↦ if h : i < n + 1 then a' ⟨i, h⟩ else 0
  have hrel : F^[n + 1] v = ∑ i ∈ Finset.range (n + 1), a i • F^[i] v := by
    rw [← ha', ← Fin.sum_univ_eq_sum_range (fun i ↦ a i • F^[i] v)]
    simp [a, Fin.is_le]
  have ha : ∃ i ≤ n, a i ≠ 0 := by
    by_contra! h
    refine hv (hF.iterate (n + 1) ?_)
    rw [iterate_map_zero, hrel]
    exact Finset.sum_eq_zero fun i hi ↦ by
      rw [h i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)), zero_smul]
  obtain ⟨t, ht0, ht⟩ := IsAlgClosed.exists_ne_zero_sum_pow_eq_self hq a n ha
  -- the coordinates of the fixed vector
  set d : ℕ → k := fun j ↦ ∑ i ∈ Finset.range (j + 1), a i ^ q ^ (j - i) * t ^ q ^ (j - i + 1)
    with hd_def
  have hd0 : d 0 = a 0 * t ^ q := by simp [d]
  have hdsucc (j : ℕ) : d (j + 1) = d j ^ q + a (j + 1) * t ^ q := by
    have hpow : d j ^ q =
        ∑ i ∈ Finset.range (j + 1), (a i ^ q ^ (j - i) * t ^ q ^ (j - i + 1)) ^ q :=
      sum_pow_char_pow p f _ _
    rw [hpow]
    simp only [hd_def]
    rw [Finset.sum_range_succ _ (j + 1)]
    congr 1
    · refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [show j + 1 - i = j - i + 1 by omega]
      ring
    · simp
  have hdn : d n = t := ht
  refine ⟨∑ j ∈ Finset.range (n + 1), d j • F^[j] v, fun hx ↦ ht0 ?_, ?_⟩
  · have := Fintype.linearIndependent_iff.1 hli (fun i ↦ d i)
      (by rwa [Fin.sum_univ_eq_sum_range (fun j ↦ d j • F^[j] v)]) (Fin.last n)
    rwa [Fin.val_last, hdn] at this
  · simp only [IsFixedPt, map_sum, map_smulₛₗ, hσ, ← iterate_succ_apply' F]
    rw [Finset.sum_range_succ, hdn, hrel, Finset.sum_range_succ', Finset.sum_range_succ' _ n,
      hd0]
    simp only [hdsucc, add_smul, mul_smul, smul_add, Finset.smul_sum, Finset.sum_add_distrib,
      iterate_zero, id_eq, smul_comm (t ^ q), Nat.succ_eq_add_one]
    abel

/-- **The fixed vectors span.** Over an algebraically closed field `k` of characteristic `p`, the
fixed vectors of an injective `σ`-semilinear map on a finite-dimensional space, for the Frobenius
`σ x = x ^ p ^ f` with `f ≠ 0`, span the space. -/
theorem span_fixedPoints_eq_top_of_injective_iterateFrobenius [FiniteDimensional k V]
    (hf : f ≠ 0) {F : V →ₛₗ[_root_.iterateFrobenius k p f] V} (hF : Injective F) :
    span k (fixedPoints F) = ⊤ := by
  set U := span k (fixedPoints F)
  have hq : 1 < p ^ f := Nat.one_lt_pow hf (Fact.out : p.Prime).one_lt
  have hσ (c : k) : _root_.iterateFrobenius k p f c = c ^ p ^ f := _root_.iterateFrobenius_def p f c
  by_contra hU
  have : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hU
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_isFixedPt_of_injective_iterateFrobenius hf
    (injective_mapQ_span_fixedPoints (iterateFrobeniusEquiv k p f).surjective hF)
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective U y
  have hw : F w - w ∈ U := by
    rwa [IsFixedPt, mapQ_apply, ← sub_eq_zero, ← Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨n, c, g, hcg⟩ := mem_span_set'.1 hw
  choose s hs using fun i ↦ IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' p (p ^ f) 1 (-1)
    (c i) (dvd_pow_self p hf) hq (by simp)
  -- correcting `w` by the Artin–Schreier solutions gives a fixed vector
  have hfix : IsFixedPt F (w + ∑ i, s i • (g i : V)) := by
    have hg (i : Fin n) : F (g i) = g i := (g i).property
    rw [IsFixedPt, map_add, map_sum]
    have hs' (i : Fin n) : s i ^ p ^ f = s i - c i := by linear_combination hs i
    have hFw : F w = w + ∑ i, c i • (g i : V) := by rw [hcg]; abel
    simp only [map_smulₛₗ, hσ, hg, hs', sub_smul, Finset.sum_sub_distrib, hFw]
    abel
  refine hy0 ((Submodule.Quotient.mk_eq_zero U).2 ?_)
  have hsum : ∑ i, s i • (g i : V) ∈ U :=
    sum_mem fun i _ ↦ smul_mem _ _ (subset_span (g i).property)
  simpa using sub_mem (subset_span hfix) hsum

/-- **Lang's lemma.** Over an algebraically closed field `k` of characteristic `p`, a
finite-dimensional space with an injective `σ`-semilinear map `F`, for the Frobenius
`σ x = x ^ p ^ f` with `f ≠ 0`, has a basis of `F`-fixed vectors. -/
theorem exists_basis_isFixedPt_of_injective_iterateFrobenius [FiniteDimensional k V]
    (hf : f ≠ 0) {F : V →ₛₗ[_root_.iterateFrobenius k p f] V} (hF : Injective F) :
    ∃ b : Basis (Fin (finrank k V)) k V, ∀ i, IsFixedPt F (b i) := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent k (fixedPoints F)
  rw [span_fixedPoints_eq_top_of_injective_iterateFrobenius hf hF] at hspan
  let b := Basis.mk hli (by rw [Subtype.range_coe, hspan])
  refine ⟨b.reindex (b.indexEquiv (finBasis k V)), fun i ↦ ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact hs (Subtype.mem _)

end LinearMap

namespace Matrix

variable {k n : Type*} [Field k] [Fintype n] [DecidableEq n] {p f : ℕ} [Fact p.Prime] [CharP k p]
  [IsAlgClosed k]

/-- **Lang's theorem for `GLₙ`.** Over an algebraically closed field `k` of characteristic `p`,
for the Frobenius `σ x = x ^ p ^ f` with `f ≠ 0` acting entrywise, every invertible matrix `A`
is `B σ(B)⁻¹` for an invertible matrix `B`: `A σ(B) = B`. -/
theorem exists_isUnit_mul_map_iterateFrobenius_eq (hf : f ≠ 0) {A : Matrix n n k}
    (hA : IsUnit A) : ∃ B : Matrix n n k, IsUnit B ∧ A * B.map (iterateFrobenius k p f) = B := by
  set σ := iterateFrobenius k p f
  let F : (n → k) →ₛₗ[σ] (n → k) :=
    { toFun x := A *ᵥ (σ ∘ x)
      map_add' x y := by
        rw [← mulVec_add]
        congr 1
        ext i
        simp
      map_smul' c x := by
        rw [← mulVec_smul]
        congr 1
        ext i
        simp }
  -- `F` applies as its `toFun` field; state this once and rewrite with it below.
  have hFapply (x : n → k) : F x = A *ᵥ (σ ∘ x) := rfl
  have hF : Injective F := by
    have : Injective fun x : n → k ↦ A *ᵥ (σ ∘ x) :=
      (mulVec_injective_iff_isUnit.2 hA).comp (Injective.comp_left σ.injective)
    intro x y hxy
    rw [hFapply, hFapply] at hxy
    exact this hxy
  obtain ⟨b, hb⟩ := LinearMap.exists_basis_isFixedPt_of_injective_iterateFrobenius hf hF
  let b' := b.reindex (b.indexEquiv (Pi.basisFun k n))
  have hb' (j : n) : A *ᵥ (σ ∘ b' j) = b' j := by
    rw [← hFapply, Basis.reindex_apply]
    exact (hb _).eq
  refine ⟨Matrix.of fun i j ↦ b' j i, ?_, ?_⟩
  · rw [← linearIndependent_col_iff_isUnit]
    exact b'.linearIndependent
  · refine Matrix.ext fun i j ↦ ?_
    rw [Matrix.mul_apply, of_apply, ← congrFun (hb' j) i]
    simp [mulVec, dotProduct]

end Matrix
