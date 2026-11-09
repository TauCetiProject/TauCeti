/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Restricted.GoodZero
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.RingTheory.PowerSeries.RootBound

/-!
# Strassmann's theorem

Let `K` be a complete ultrametric normed field and `f = ∑ aₙ Xⁿ` a nonzero power series over `K`
restricted at a radius `c > 0`, so that `‖aₙ‖ cⁿ → 0`. Let `s` be the largest index at which the
weighted coefficient norm `‖aₙ‖ cⁿ` attains its maximum, so that `f` is distinguished of degree `s`
at `c` (`TauCeti.PowerSeries.IsDistinguished`). **Strassmann's theorem** says that `f` has at most
`s` distinct zeros in the closed disc of radius `c`, and this holds in every complete normed field
`L` containing `K` isometrically.

Weierstrass preparation writes `f = e * ω` with `ω` a monic polynomial of degree `s` and `e` a unit
of the ring of series restricted at `c`. Evaluation at a point `x` with `‖x‖ ≤ c` is a ring
homomorphism on that ring, so it sends `e` to a unit, and the zeros of `f` in the disc are roots of
`ω`. The field `L` is automatically ultrametric, since `K` is and `L` is a normed `K`-algebra.

At points of `K`, counting zeros with their multiplicities, the orders of the good zeros of `f` in
the closed disc add up to at most `s`, since they are root multiplicities of `ω`. Every root of a
polynomial `P` with `f = u * P`, `u` a unit of the ring of series restricted at `c` and `P` of
degree at most `s`, lies in the closed disc, so over an algebraically closed `K` the bound is an
equality: the zeros of `f` in the closed disc, counted with multiplicity, number exactly `s`.

As a consequence, a series restricted at `c` that vanishes on an infinite subset of the closed disc
of radius `c` is zero. The bound is sharp: `X ^ p - X` over `ℚ_p` is distinguished of degree `p` at
the unit radius and vanishes at the `p` Teichmüller representatives in `ℤ_p`.

The identity principle extends to series with coefficients in a normed space `E` over `K` that
carries a jointly injective family of continuous linear maps `φⱼ : E → Lⱼ` into complete normed
field extensions of `K`: each `φⱼ` turns such a series into a restricted series over `Lⱼ`.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le`: Strassmann's theorem.
* `TauCeti.PowerSeries.IsDistinguished.sum_le_of_isGoodZero`: Strassmann's theorem with
  multiplicities.
* `TauCeti.PowerSeries.IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul`: the prepared
  polynomial has its roots in the closed disc.
* `TauCeti.PowerSeries.IsDistinguished.exists_card_eq_isGoodZero`: over an algebraically closed
  field, a series distinguished of degree `s` at `c > 0` has exactly `s` zeros in the closed disc,
  counted with multiplicity.
* `PowerSeries.IsRestricted.eq_zero_of_infinite_of_evalAt_eq_zero`: the identity principle for
  restricted series.
* `TauCeti.PowerSeries.eq_zero_of_hasSum_pow_smul`: the identity principle for series with
  coefficients in a normed space with a jointly injective family of functionals into complete
  field extensions.

## References

* R. Strassmann, *Über den Wertevorrat von Potenzreihen im Gebiet der p-adischen Zahlen*,
  J. Reine Angew. Math. 159 (1928), 13–28.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.2, Theorem 1 (Weierstrass
  preparation), from which the bound is deduced.
-/

public section

namespace TauCeti.PowerSeries

section RootBound

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {c : ℝ} {s : ℕ} {f : PowerSeries K}

/-- **The prepared polynomial has its roots in the closed disc.** If `f` is distinguished of degree
`s` at `c > 0` and `f = u * P` with `u` a unit of the ring of series restricted at `c` and `P` a
polynomial of degree at most `s`, then every root of `P` has norm at most `c`. -/
theorem IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul (hf : IsDistinguished c s f)
    (hc : 0 < c) {u : _root_.PowerSeries.IsRestricted.subring (R := K) c} (hu : IsUnit u)
    {P : Polynomial K} (hPdeg : P.natDegree ≤ s)
    (hmul : (u : PowerSeries K) * (P : PowerSeries K) = f) {α : K}
    (hα : α ∈ P.roots) : ‖α‖ ≤ c := by
  have ha : P.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.2 (Polynomial.ne_zero_of_mem_roots hα)
  -- normalise `P` to the monic `Q = P.leadingCoeff⁻¹ • P`, which is still distinguished
  set Q := Polynomial.C P.leadingCoeff⁻¹ * P
  have hQm : Q.IsMonicOfDegree s :=
    ⟨by rw [Polynomial.natDegree_C_mul (inv_ne_zero ha),
        natDegree_eq_of_isUnit_mul hc hf hu hPdeg hmul],
      by rw [Polynomial.Monic, Polynomial.leadingCoeff_C_mul_of_isUnit (inv_ne_zero ha).isUnit,
        inv_mul_cancel₀ ha]⟩
  have hPQ : Polynomial.C P.leadingCoeff * Q = P := by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ ha, Polynomial.C_1, one_mul]
  have hQd : IsDistinguished c s (Q : PowerSeries K) := by
    refine IsDistinguished.of_isUnit_mul (u := algebraMap K _ P.leadingCoeff) ?_ hc
      (ha.isUnit.map _)
    have hP := IsDistinguished.of_isUnit_mul (hmul ▸ hf) hc hu
    rw [← hPQ, Polynomial.coe_mul, Polynomial.coe_C] at hP
    simpa using hP
  refine hQd.norm_le_of_eval_eq_zero hc hQm ?_
  rw [Polynomial.eval_mul, (Polynomial.isRoot_of_mem_roots hα).eq_zero, mul_zero]

end RootBound

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [NormedAlgebra K L] [CompleteSpace L] {c : ℝ} {s : ℕ} {f : PowerSeries K}

/-- **Strassmann's theorem.** Let `f` be a power series over a complete ultrametric normed field
`K`, restricted at a radius `c > 0` and distinguished of degree `s` there, that is, `s` is the
largest index at which the weighted coefficient norm `‖aₙ‖ cⁿ` attains the Gauss norm. Then `f` has
at most `s` zeros of norm at most `c` in any complete normed field extension `L` of `K`. -/
theorem IsDistinguished.encard_setOf_evalAt_eq_zero_le (hf : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) :
    {x : L | ‖x‖ ≤ c ∧ f.evalAt x = 0}.encard ≤ s := by
  classical
  have : IsUltrametricDist L := .of_normedAlgebra K
  obtain ⟨e, ω, he, hω, rfl⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hf.coeff_ne_zero) hc hfr
  have hω0 : ω.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hω.ne_zero
  -- A zero of `f = e * ω` in the closed disc is a root of `ω`, since `e(x)` is a unit.
  have hsub : {x : L | ‖x‖ ≤ c ∧ ((e : PowerSeries K) * ω).evalAt x = 0} ⊆
      (ω.map (algebraMap K L)).roots.toFinset := by
    rintro x ⟨hx, h0⟩
    have hu : IsUnit ((e : PowerSeries K).evalAt x) := by
      simpa using he.map (_root_.PowerSeries.IsRestricted.evalAtHom K hx)
    rw [_root_.PowerSeries.IsRestricted.evalAt_mul e.2 (isRestricted_polynomial ω) hx,
      _root_.PowerSeries.evalAt_coe, hu.mul_right_eq_zero] at h0
    simpa [Polynomial.mem_roots hω0] using h0
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  calc _ ≤ Multiset.card (ω.map (algebraMap K L)).roots := Multiset.toFinset_card_le _
    _ ≤ (ω.map (algebraMap K L)).natDegree := Polynomial.card_roots' _
    _ ≤ ω.natDegree := Polynomial.natDegree_map_le
    _ = s := hω.natDegree_eq

/-- **Strassmann's theorem with multiplicities.** Let `f` be restricted at `c > 0` and
distinguished of degree `s` there. If `f` has a good zero of order `h a` at each point `a` of a
finite set `S` in the closed disc of radius `c`, then `∑_{a ∈ S} h a ≤ s`. -/
theorem IsDistinguished.sum_le_of_isGoodZero (hfd : IsDistinguished c s f) (hc : 0 < c)
    (hfr : f.IsRestricted c) {S : Finset K} {h : K → ℕ}
    (hS : ∀ a ∈ S, ‖a‖ ≤ c ∧ f.IsGoodZero a (h a)) :
    ∑ a ∈ S, h a ≤ s := by
  classical
  obtain ⟨u, P, hu, hP, hmul⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc hfr
  have hroot : ∀ a ∈ S, h a = P.roots.count a := fun a ha ↦ (hS a ha).2.unique
    (_root_.PowerSeries.isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero (hS a ha).1)
  rw [Finset.sum_congr rfl hroot, ← hP.natDegree_eq]
  calc ∑ a ∈ S, P.roots.count a ≤ ∑ a ∈ S ∪ P.roots.toFinset, P.roots.count a :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = Multiset.card P.roots :=
        Multiset.sum_count_eq_card fun a ha ↦ Finset.mem_union_right _ (Multiset.mem_toFinset.2 ha)
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- **Zeros in a closed disc, with multiplicity.** Over an algebraically closed field, the zeros
of a series `f` restricted at `c > 0` and distinguished of degree `s` there, in the closed disc of
radius `c` and counted with multiplicity, form a multiset `Z` with exactly `s` elements: `f` has a
good zero of order `Z.count a` at every `a` of norm at most `c`. -/
theorem IsDistinguished.exists_card_eq_isGoodZero [IsAlgClosed K] [DecidableEq K]
    (hfd : IsDistinguished c s f) (hc : 0 < c) (hfr : f.IsRestricted c) :
    ∃ Z : Multiset K, Multiset.card Z = s ∧ (∀ a ∈ Z, ‖a‖ ≤ c) ∧
      ∀ a, ‖a‖ ≤ c → f.IsGoodZero a (Z.count a) := by
  obtain ⟨u, P, hu, hP, hmul⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc hfr
  refine ⟨P.roots, ?_, fun a ha ↦ (IsDistinguished.of_isUnit_mul (hmul ▸ hfd) hc hu
      ).norm_le_of_eval_eq_zero hc hP (Polynomial.isRoot_of_mem_roots ha), fun a ha ↦ ?_⟩
  · rw [← hP.natDegree_eq]
    exact Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits P)
  · exact _root_.PowerSeries.isGoodZero_count_roots_of_isUnit_mul hu hmul hfd.ne_zero ha

end TauCeti.PowerSeries

namespace PowerSeries

open TauCeti.PowerSeries

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [NormedAlgebra K L] [CompleteSpace L] {c : ℝ} {f : PowerSeries K}

/-- **Identity principle for restricted series.** A power series over a complete ultrametric
normed field, restricted at a radius `c > 0`, that vanishes on an infinite set of points of norm at
most `c` in a complete normed field extension is zero. -/
theorem IsRestricted.eq_zero_of_infinite_of_evalAt_eq_zero (hfr : f.IsRestricted c) (hc : 0 < c)
    {S : Set L} (hS : S.Infinite) (hSc : ∀ x ∈ S, ‖x‖ ≤ c) (hfS : ∀ x ∈ S, f.evalAt x = 0) :
    f = 0 := by
  by_contra hf0
  obtain ⟨s, hs⟩ := exists_isDistinguished hc hfr hf0
  have h := (Set.encard_le_encard (t := {x : L | ‖x‖ ≤ c ∧ f.evalAt x = 0})
    fun x hx ↦ ⟨hSc x hx, hfS x hx⟩).trans (hs.encard_setOf_evalAt_eq_zero_le hc hfr)
  rw [hS.encard_eq] at h
  exact ENat.natCast_ne_top s (top_le_iff.mp h)

end PowerSeries

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

variable {K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NormedAddCommGroup E]
  [NormedSpace K E] {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)]
  [∀ j, NormedAlgebra K (L j)] [∀ j, CompleteSpace (L j)]

/-- **Identity principle for module-valued series.** Let `E` be a normed space over an ultrametric
nontrivially normed field `K`, with a jointly injective family of continuous linear maps
`φⱼ : E → Lⱼ` into complete normed field extensions of `K`. A sequence `β` in `E` with
`‖β k‖ rᵏ → 0`, whose series `∑ₖ xᵏ • β k` sums to zero at every point of an infinite subset of
the disc of radius `r`, is zero. -/
theorem eq_zero_of_hasSum_pow_smul (φ : ∀ j, E →L[K] L j)
    (hφ : ∀ e, (∀ j, φ j e = 0) → e = 0) {r : ℝ} {β : ℕ → E}
    (hβ : Tendsto (fun k ↦ ‖β k‖ * r ^ k) atTop (𝓝 0)) {S : Set K} (hS : S.Infinite)
    (hSr : ∀ x ∈ S, ‖x‖ ≤ r) (h : ∀ x ∈ S, HasSum (fun k ↦ x ^ k • β k) 0) : β = 0 := by
  -- Each `φⱼ` turns `β` into the coefficients of a restricted series over `Lⱼ`, which is zero
  -- by Strassmann's theorem.
  have hr := hS.nontrivial.pos_of_forall_norm_le hSr
  funext k
  refine hφ _ fun j ↦ ?_
  have : IsUltrametricDist (L j) := .of_normedAlgebra K
  set f : _root_.PowerSeries (L j) := .mk fun k ↦ φ j (β k) with hf_def
  have hf : f.IsRestricted r := by
    rw [_root_.PowerSeries.isRestricted_iff']
    refine squeeze_zero (fun k ↦ by positivity) (fun k ↦ ?_)
      (by simpa using hβ.const_mul ‖φ j‖)
    rw [hf_def, _root_.PowerSeries.coeff_mk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((φ j).le_opNorm _) (by positivity)
  have hzero : f = 0 := by
    refine hf.eq_zero_of_infinite_of_evalAt_eq_zero hr
      (hS.image (algebraMap K (L j)).injective.injOn) ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [norm_algebraMap']
      exact hSr x hx
    · rintro _ ⟨x, hx, rfl⟩
      have hterm (n : ℕ) :
          _root_.PowerSeries.coeff n f • algebraMap K (L j) x ^ n = φ j (x ^ n • β n) := by
        rw [hf_def, _root_.PowerSeries.coeff_mk, map_smul, smul_eq_mul, Algebra.smul_def, map_pow,
          mul_comm]
      rw [_root_.PowerSeries.evalAt_def, tsum_congr hterm]
      simpa only [Function.comp_def, map_zero] using
        ((h x hx).map (φ j) (φ j).continuous).tsum_eq
  simpa [hf_def] using congrArg (_root_.PowerSeries.coeff k) hzero

end TauCeti.PowerSeries
