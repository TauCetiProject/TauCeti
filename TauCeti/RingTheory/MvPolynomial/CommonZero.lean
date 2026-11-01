/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.Algebra.MvPolynomial.Units
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Common zeros of few polynomials, and irreducibility of nonsingular hypersurfaces

Let `K` be an algebraically closed field and `σ` a finite type. Fewer than `#σ` polynomials that
vanish at the origin of `K^σ` have another common zero there
(`MvPolynomial.exists_ne_zero_forall_aeval_eq_zero`). This is the dimension theorem: their zero
set has dimension at least `#σ` minus their number, so it is not the single point `0`. In
projective language, with `#σ = n + 1`, at most `n` hypersurfaces of `ℙⁿ` have a common point.
The proof is Krull's height theorem together with the Nullstellensatz: if `0` were the only
common zero, the maximal ideal of the origin, of height `#σ`, would be a minimal prime over the
ideal the polynomials generate.

In particular two hypersurfaces of `ℙⁿ`, for `n ≥ 2`, always meet. At a common point of the
factors of a product `a * b`, the product and all its partial derivatives vanish. So a projective
hypersurface `G = 0` of dimension at least one whose points over `K` are all nonsingular is
irreducible (`TauCeti.irreducible_of_isHomogeneous`), since the factors of a homogeneous
polynomial are homogeneous. This is the form used by the scheme `Proj (k[X₀, …, Xₙ] ⧸ (G))`, which
is integral for irreducible `G`. Function fields use the affine form: the equation of `G = 0` in a
standard affine chart is irreducible over `K` (`TauCeti.irreducible_map_dehomogenize`), unless it
is a unit. A factorization in the chart lifts to a factorization of `G` up to a power of the
omitted coordinate, by homogenization. For a nonsingular plane curve `G = 0` with a point
`(x : y : 1)` in a function field, this makes `G(X₀, X₁, 1)` the irreducible relation between `x`
and `y`.

## Main results

* `MvPolynomial.exists_ne_zero_forall_aeval_eq_zero`: fewer than `#σ` polynomials vanishing at
  the origin of `K^σ` have a nonzero common zero.
* `MvPolynomial.exists_ne_zero_aeval_mul_eq_zero_and_aeval_pderiv_eq_zero`: in at least three
  variables, a product of two polynomials vanishing at the origin is singular at some point other
  than the origin.
* `TauCeti.irreducible_map_dehomogenize`: the affine equation of a nonsingular projective
  hypersurface of dimension at least one is irreducible over an algebraically closed field.
* `TauCeti.irreducible_of_isHomogeneous`: a nonsingular homogeneous polynomial of positive degree
  in at least three variables is irreducible.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Chapter I, Proposition 7.1 and
  Theorem 7.2 (the affine and projective dimension theorems).
* W. Fulton, *Algebraic Curves*, Section 5.3, for the irreducibility of a nonsingular projective
  plane curve.
-/

public section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K] [Finite σ]

/-- **The dimension theorem at the origin**: let `K` be an algebraically closed extension of `k`.
Fewer than `#σ` polynomials in `k[X_σ]` vanishing at the origin have a common zero in `K^σ` other
than the origin. -/
theorem exists_ne_zero_forall_aeval_eq_zero {s : Finset (MvPolynomial σ k)}
    (hs : s.card < Nat.card σ) (h0 : ∀ p ∈ s, constantCoeff p = 0) :
    ∃ x : σ → K, x ≠ 0 ∧ ∀ p ∈ s, aeval x p = 0 := by
  by_contra! H
  set I := Ideal.span (s : Set (MvPolynomial σ k))
  -- The polynomials vanishing at the origin form a maximal ideal `m` containing `I`.
  set m := RingHom.ker (constantCoeff (σ := σ) (R := k))
  have hm : m.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, constantCoeff_C σ c⟩
  have hIm : I ≤ m := Ideal.span_le.mpr fun p hp ↦ h0 p hp
  -- The origin is the only zero of `I`, so the Nullstellensatz gives `m ≤ √I`.
  have hmI : m ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro p hp x hx
    have hx0 : x = 0 := by
      by_contra hx0
      obtain ⟨q, hq, hqx⟩ := H x hx0
      exact hqx (hx q (Ideal.subset_span hq))
    rw [hx0, aeval_zero, RingHom.mem_ker.mp hp, map_zero]
  -- Hence `m` is a minimal prime over `I`, of height at most `#s` by Krull's height theorem.
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (hIm.trans_lt hm.ne_top.lt_top).ne
  have hpm : m = p :=
    hm.eq_of_le hp.1.1.ne_top (hmI.trans ((hp.1.1.radical_le_iff).mpr hp.1.2))
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hp
  rw [← hpm, height_eq_natCard_of_isMaximal] at h1
  exact hs.not_ge (by exact_mod_cast h1)

/-- **A reducible cone is singular away from its vertex**: let `K` be an algebraically closed
extension of `k` and `σ` have at least three elements. If `a, b ∈ k[X_σ]` vanish at the origin,
then at some point of `K^σ` other than the origin, `a * b` and all its partial derivatives
vanish. -/
theorem exists_ne_zero_aeval_mul_eq_zero_and_aeval_pderiv_eq_zero (hσ : 2 < Nat.card σ)
    {a b : MvPolynomial σ k} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    ∃ x : σ → K, x ≠ 0 ∧ aeval x (a * b) = 0 ∧ ∀ i, aeval x (pderiv i (a * b)) = 0 := by
  classical
  obtain ⟨x, hx, hab⟩ := exists_ne_zero_forall_aeval_eq_zero (K := K) (s := {a, b})
    (Finset.card_le_two.trans_lt hσ) (by simp [ha, hb])
  have hxa := hab a (by simp)
  have hxb := hab b (by simp)
  exact ⟨x, hx, by simp [hxa], fun i ↦ by simp [hxa, hxb]⟩

end MvPolynomial

namespace TauCeti

open MvPolynomial

variable {n d : ℕ} {k K : Type*} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]

/-- **A nonsingular projective hypersurface is irreducible in its affine charts**: let
`G ∈ k[X₀, …, Xₙ]` be homogeneous with `n ≥ 2`, and suppose that at every point of `G = 0` over an
algebraically closed extension `K` of `k` some partial derivative of `G` is nonzero. Then the
equation of `G = 0` in the `i`-th standard affine chart is irreducible over `K`, unless it is a
unit.

Both hypotheses on the dimension and on units are needed: `X₀ X₁ (X₀ - X₁)` is nonsingular in
`ℙ¹`, while its equation `X₀ (X₀ - 1)` in the chart `X₁ ≠ 0` is reducible; and the line `X₂ = 0`
has the unit `1` as its equation in the chart `X₂ ≠ 0`. -/
theorem irreducible_map_dehomogenize (hn : 2 ≤ n) {G : MvPolynomial (Fin (n + 1)) k}
    (hG : G.IsHomogeneous d)
    (hsm : ∀ b : Fin (n + 1) → K, b ≠ 0 → aeval b G = 0 → ∃ l, aeval b (pderiv l G) ≠ 0)
    (i : Fin (n + 1)) (hu : ¬IsUnit (dehomogenize i G)) :
    Irreducible ((dehomogenize i G).map (algebraMap k K)) := by
  set G' := G.map (algebraMap k K) with hG'_def
  have hG' : G'.IsHomogeneous d := hG.map _
  -- Nonsingularity, read over the coefficients `K`.
  have hsm' (b : Fin (n + 1) → K) (hb : b ≠ 0) (hbG : eval b G' = 0) :
      ∃ l, eval b (pderiv l G') ≠ 0 := by
    obtain ⟨l, hl⟩ := hsm b hb (by rwa [hG'_def, eval_map, ← aeval_def] at hbG)
    exact ⟨l, by rwa [hG'_def, pderiv_map, eval_map, ← aeval_def]⟩
  rw [map_dehomogenize]
  refine ⟨fun h ↦ hu (isUnit_of_map_unit (map (algebraMap k K)) _ (by rwa [map_dehomogenize])),
    fun f g hfg ↦ ?_⟩
  by_contra! hfg'
  obtain ⟨hf, hg⟩ := hfg'
  -- The affine equation is nonzero, since `G' = 0` would be singular everywhere.
  have hG'0 : dehomogenize i G' ≠ 0 := fun h0 ↦ by
    have : G' = 0 := dehomogenize_injOn i d hG' (isHomogeneous_zero _ _ _) (by rw [h0, map_zero])
    obtain ⟨l, hl⟩ := hsm' 1 one_ne_zero (by simp [this])
    simp [this] at hl
  have hfg0 : f * g ≠ 0 := hfg ▸ hG'0
  have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg0
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg0
  -- Homogenize `f` and `g`; then `G' = X_i^e F G₁` with `F` and `G₁` vanishing at the origin.
  obtain ⟨F, hF, rfl⟩ := exists_isHomogeneous_dehomogenize_eq i le_rfl (p := f)
  obtain ⟨G₁, hG₁, rfl⟩ := exists_isHomogeneous_dehomogenize_eq i le_rfl (p := g)
  have hle : (dehomogenize i F).totalDegree + (dehomogenize i G₁).totalDegree ≤ d := by
    rw [← totalDegree_mul_of_isDomain hf0 hg0, ← hfg]
    exact (totalDegree_dehomogenize_le i G').trans hG'.totalDegree_le
  set e := d - ((dehomogenize i F).totalDegree + (dehomogenize i G₁).totalDegree)
  have hP : (X i ^ e * F * G₁).IsHomogeneous d := by
    have := ((isHomogeneous_X_pow (R := K) i e).mul hF).mul hG₁
    rwa [add_assoc, Nat.sub_add_cancel hle] at this
  have hGP : G' = X i ^ e * F * G₁ :=
    dehomogenize_injOn i d hG' hP (by
      rw [map_mul, map_mul, map_pow, dehomogenize_X, Fin.insertNth_apply_same, one_pow, one_mul,
        hG'_def, hfg])
  -- The two factors meet at a point of `ℙⁿ`, where `G'` is singular.
  obtain ⟨x, hx, hx0, hxd⟩ := exists_ne_zero_aeval_mul_eq_zero_and_aeval_pderiv_eq_zero (K := K)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) (a := X i ^ e * F) (b := G₁)
    (by rw [map_mul, hF.constantCoeff_eq_zero (mt (isUnit_iff_totalDegree_eq_zero hf0).mpr hf),
      mul_zero])
    (hG₁.constantCoeff_eq_zero (mt (isUnit_iff_totalDegree_eq_zero hg0).mpr hg))
  obtain ⟨l, hl⟩ := hsm' x hx (by rw [hGP]; exact hx0)
  exact hl (by rw [hGP]; exact hxd l)

/-- **A nonsingular projective hypersurface is irreducible**: let `G ∈ k[X₀, …, Xₙ]` be homogeneous
of positive degree with `n ≥ 2`, and suppose that at every point of `G = 0` over an algebraically
closed extension `K` of `k` some partial derivative of `G` is nonzero. Then `G` is irreducible.

Taking `k = K` and the polynomial `G` with coefficients mapped to `K`, a nonsingular `G` is
absolutely irreducible. Both hypotheses on the dimension and on the degree are needed: the
binary form `X₀ X₁` is nonsingular in `ℙ¹`, and a nonzero constant is a unit. -/
theorem irreducible_of_isHomogeneous (hn : 2 ≤ n) {G : MvPolynomial (Fin (n + 1)) k}
    (hG : G.IsHomogeneous d) (hd : d ≠ 0)
    (hsm : ∀ b : Fin (n + 1) → K, b ≠ 0 → aeval b G = 0 → ∃ l, aeval b (pderiv l G) ≠ 0) :
    Irreducible G := by
  -- `G` is nonzero, since `G = 0` would be singular everywhere.
  have hG0 : G ≠ 0 := by
    rintro rfl
    obtain ⟨l, hl⟩ := hsm 1 one_ne_zero (map_zero _)
    simp at hl
  refine ⟨fun hu ↦ hd ?_, fun a b hab ↦ ?_⟩
  · rw [← hG.totalDegree hG0]
    exact (isUnit_iff_totalDegree_eq_zero hG0).mp hu
  by_contra! hab'
  obtain ⟨ha, hb⟩ := hab'
  have hab0 : a * b ≠ 0 := hab ▸ hG0
  rw [hab] at hG
  -- The factors are homogeneous of positive degree, so they vanish at the origin; they meet at a
  -- point of `ℙⁿ`, where `G` is singular.
  have ha0 := (hG.of_mul_left hab0).constantCoeff_eq_zero
    (mt (isUnit_iff_totalDegree_eq_zero (left_ne_zero_of_mul hab0)).mpr ha)
  have hb0 := (hG.of_mul_right hab0).constantCoeff_eq_zero
    (mt (isUnit_iff_totalDegree_eq_zero (right_ne_zero_of_mul hab0)).mpr hb)
  obtain ⟨x, hx, hx0, hxd⟩ := exists_ne_zero_aeval_mul_eq_zero_and_aeval_pderiv_eq_zero (K := K)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) ha0 hb0
  obtain ⟨l, hl⟩ := hsm x hx (hab ▸ hx0)
  exact hl (hab ▸ hxd l)

end TauCeti
