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
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.RingTheory.PowerSeries.RootBound

/-!
# Strassmann's theorem

Let `K` be an ultrametric normed field and `f = ∑ aₙ Xⁿ` a nonzero power series over `K`
restricted at a radius `c > 0`, so that `‖aₙ‖ cⁿ → 0`. Let `s` be the largest index at which the
weighted coefficient norm `‖aₙ‖ cⁿ` attains its maximum, so that `f` is distinguished of degree `s`
at `c` (`TauCeti.PowerSeries.IsDistinguished`). **Strassmann's theorem** says that `f` has at most
`s` distinct zeros in the closed disc of radius `c`, and this holds in every complete normed field
`L` containing `K` isometrically.

Weierstrass preparation, applied over `L`, writes `f = e * ω` with `ω` a monic polynomial of
degree `s` and `e` a unit of the ring of series restricted at `c`. Evaluation at a point `x` with
`‖x‖ ≤ c` is a ring homomorphism on that ring, so it sends `e` to a unit, and the zeros of `f` in
the disc are roots of `ω`. The field `L` is automatically ultrametric, since `K` is and `L` is a
normed `K`-algebra.

When `K` is complete, at points of `K` and counting zeros with their multiplicities, the orders of
the good zeros of `f` in the closed disc add up to at most `s`, since they are root multiplicities
of `ω`. Every root of a polynomial `P` with `f = u * P`, `u` a unit of the ring of series
restricted at `c` and `P` of degree at most `s`, lies in the closed disc, so over an algebraically
closed `K` the bound is an equality: the zeros of `f` in the closed disc, counted with
multiplicity, number exactly `s`.

As a consequence, a nonzero series restricted at `c` has only finitely many zeros in the closed disc
of radius `c`, so a series restricted at `c` that vanishes on an infinite subset of that disc is
zero. The bound is sharp: `X ^ p - X` over `ℚ_p` is distinguished of degree `p` at
the unit radius and vanishes at the `p` Teichmüller representatives in `ℤ_p`.

The identity principle extends to series with coefficients in a normed space `E` over `K` that
carries a jointly injective family of continuous linear maps `φⱼ : E → Lⱼ` into normed field
extensions of `K`: each `φⱼ` turns such a series into a restricted series over the completion of
`Lⱼ`.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le`: Strassmann's theorem.
* `TauCeti.PowerSeries.IsDistinguished.sum_le_of_isGoodZero`: Strassmann's theorem with
  multiplicities.
* `TauCeti.PowerSeries.IsDistinguished.norm_le_of_mem_roots_of_isUnit_mul`: the prepared
  polynomial has its roots in the closed disc.
* `TauCeti.PowerSeries.IsDistinguished.exists_card_eq_isGoodZero`: over an algebraically closed
  field, a series distinguished of degree `s` at `c > 0` has exactly `s` zeros in the closed disc,
  counted with multiplicity.
* `PowerSeries.IsRestricted.finite_setOf_norm_le_and_evalAt_eq_zero`: a nonzero restricted
  series has finitely many zeros in the closed disc.
* `PowerSeries.IsRestricted.eq_zero_of_infinite_of_evalAt_eq_zero`: the identity principle for
  restricted series.
* `TauCeti.PowerSeries.eq_zero_of_hasSum_pow_smul`: the identity principle for series with
  coefficients in a normed space with a jointly injective family of functionals into field
  extensions.

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

/-- **Strassmann's theorem over a complete field**: the case of zeros in the coefficient field
itself, from which the general case is deduced by extension of scalars. -/
private theorem IsDistinguished.encard_setOf_evalAt_eq_zero_le_of_completeSpace
    {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {c : ℝ} {s : ℕ}
    {f : PowerSeries K} (hf : IsDistinguished c s f) (hc : 0 < c) (hfr : f.IsRestricted c) :
    {x : K | ‖x‖ ≤ c ∧ f.evalAt x = 0}.encard ≤ s := by
  classical
  obtain ⟨e, ω, he, hω, rfl⟩ :=
    hf.exists_isUnit_isMonicOfDegree_mul_eq (isUnit_iff_ne_zero.mpr hf.coeff_ne_zero) hc hfr
  -- A zero of `f = e * ω` in the closed disc is a root of `ω`, since `e(x)` is a unit.
  have hsub : {x : K | ‖x‖ ≤ c ∧ ((e : PowerSeries K) * ω).evalAt x = 0} ⊆ ω.roots.toFinset := by
    rintro x ⟨hx, h0⟩
    have hu : IsUnit ((e : PowerSeries K).evalAt x) := by
      simpa using he.map (_root_.PowerSeries.IsRestricted.evalAtHom K hx)
    rw [_root_.PowerSeries.IsRestricted.evalAt_mul e.2 (isRestricted_polynomial ω) hx,
      _root_.PowerSeries.evalAt_coe, hu.mul_right_eq_zero] at h0
    simpa [Polynomial.mem_roots hω.ne_zero] using h0
  refine (Set.encard_le_encard hsub).trans ?_
  rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le]
  calc _ ≤ Multiset.card ω.roots := Multiset.toFinset_card_le _
    _ ≤ ω.natDegree := Polynomial.card_roots' _
    _ = s := hω.natDegree_eq

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [CompleteSpace L] {c : ℝ} {s : ℕ} {f : PowerSeries K}

omit [IsUltrametricDist K] [CompleteSpace L] in
/-- At a radius `c ≤ 0` a distinguished series has no zero of norm at most `c`: such a point is
`0` and the radius is `0`, where the distinguished degree is `0`, so the constant coefficient is
nonzero. -/
private theorem IsDistinguished.evalAt_ne_zero_of_nonpos (hf : IsDistinguished c s f)
    (hc : c ≤ 0) {x : L} (hx : ‖x‖ ≤ c) : f.evalAt x ≠ 0 := by
  have hx0 : x = 0 := norm_le_zero_iff.mp (hx.trans hc)
  have hc0 : c = 0 := le_antisymm hc ((norm_nonneg x).trans hx)
  have hs : s = 0 := by
    by_contra hs
    have := hf.gaussNorm_pos
    rw [← hf.norm_coeff_mul_pow_eq, hc0, zero_pow hs, mul_zero] at this
    exact lt_irrefl _ this
  rw [hx0, _root_.PowerSeries.evalAt_at_zero, map_ne_zero_iff _ (algebraMap K L).injective,
    ← _root_.PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hs]
  exact hf.coeff_ne_zero

/-- **Strassmann's theorem.** Let `f` be a power series over an ultrametric normed field
`K`, restricted at a radius `c` and distinguished of degree `s` there, that is, `s` is the
largest index at which the weighted coefficient norm `‖aₙ‖ cⁿ` attains the Gauss norm. Then `f` has
at most `s` zeros of norm at most `c` in any complete normed field extension `L` of `K`. For
`c ≤ 0` there are none. -/
theorem IsDistinguished.encard_setOf_evalAt_eq_zero_le (hf : IsDistinguished c s f)
    (hfr : f.IsRestricted c) :
    {x : L | ‖x‖ ≤ c ∧ f.evalAt x = 0}.encard ≤ s := by
  rcases le_or_gt c 0 with hc | hc
  · have h : {x : L | ‖x‖ ≤ c ∧ f.evalAt x = 0} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx ↦ hf.evalAt_ne_zero_of_nonpos hc hx.1 hx.2
    simp [h]
  have : IsUltrametricDist L := .of_normedAlgebra K
  simpa using (hf.map (algebraMap K L) (norm_algebraMap' L)
    ).encard_setOf_evalAt_eq_zero_le_of_completeSpace hc
    (MvPowerSeries.isRestricted_map _ (algebraMap K L) (C := 1)
      (fun a ↦ by rw [norm_algebraMap', one_mul]) hfr)

variable [CompleteSpace K]

/-- **Strassmann's theorem with multiplicities.** Let `f` be restricted at `c` and
distinguished of degree `s` there. If `f` has a good zero of order `h a` at each point `a` of a
finite set `S` in the closed disc of radius `c`, then `∑_{a ∈ S} h a ≤ s`. -/
theorem IsDistinguished.sum_le_of_isGoodZero (hfd : IsDistinguished c s f)
    (hfr : f.IsRestricted c) {S : Finset K} {h : K → ℕ}
    (hS : ∀ a ∈ S, ‖a‖ ≤ c ∧ f.IsGoodZero a (h a)) :
    ∑ a ∈ S, h a ≤ s := by
  classical
  rcases le_or_gt c 0 with hc | hc
  · -- `f` has no zero in the closed disc of radius `c ≤ 0`, so every order vanishes
    refine (Finset.sum_eq_zero fun a ha ↦ ?_).trans_le (Nat.zero_le _)
    by_contra hne
    exact hfd.evalAt_ne_zero_of_nonpos hc (hS a ha).1
      ((hS a ha).2.evalAt_eq_zero (Nat.pos_of_ne_zero hne))
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

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L] [CompleteSpace L] {c : ℝ} {f : PowerSeries K}

/-- A nonzero power series over an ultrametric normed field, restricted at a radius `c`, has only
finitely many zeros of norm at most `c` in any complete normed field extension. For `c ≤ 0` the
closed disc is at most `{0}`. -/
theorem IsRestricted.finite_setOf_norm_le_and_evalAt_eq_zero (hfr : f.IsRestricted c)
    (hf0 : f ≠ 0) : {x : L | ‖x‖ ≤ c ∧ f.evalAt x = 0}.Finite := by
  rcases le_or_gt c 0 with hc | hc
  · exact (Set.finite_singleton 0).subset fun x hx ↦ norm_le_zero_iff.mp (hx.1.trans hc)
  obtain ⟨s, hs⟩ := exists_isDistinguished hc hfr hf0
  exact Set.finite_of_encard_le_coe (hs.encard_setOf_evalAt_eq_zero_le hfr)

/-- **Identity principle for restricted series.** A power series over an ultrametric
normed field, restricted at a radius `c`, that vanishes on an infinite set of points of norm at
most `c` in a complete normed field extension is zero. -/
theorem IsRestricted.eq_zero_of_infinite_of_evalAt_eq_zero (hfr : f.IsRestricted c)
    {S : Set L} (hS : S.Infinite) (hSc : ∀ x ∈ S, ‖x‖ ≤ c) (hfS : ∀ x ∈ S, f.evalAt x = 0) :
    f = 0 := by
  by_contra hf0
  exact hS ((hfr.finite_setOf_norm_le_and_evalAt_eq_zero hf0).subset
    fun x hx ↦ ⟨hSc x hx, hfS x hx⟩)

end PowerSeries

namespace TauCeti.PowerSeries

open Filter
open scoped Topology

variable {K E : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [NormedAddCommGroup E]
  [NormedSpace K E] {ι : Type*} {L : ι → Type*} [∀ j, NormedField (L j)]
  [∀ j, NormedAlgebra K (L j)]

/-- **Identity principle for module-valued series** over complete extensions: the case in which
the fields `Lⱼ` are complete, from which the general case is deduced by completing them. -/
private theorem eq_zero_of_hasSum_pow_smul_of_completeSpace [∀ j, CompleteSpace (L j)]
    (φ : ∀ j, E →L[K] L j)
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
    refine hf.eq_zero_of_infinite_of_evalAt_eq_zero
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

/-- **Identity principle for module-valued series.** Let `E` be a normed space over an ultrametric
nontrivially normed field `K`, with a jointly injective family of continuous linear maps
`φⱼ : E → Lⱼ` into normed field extensions of `K`. A sequence `β` in `E` with
`‖β k‖ rᵏ → 0`, whose series `∑ₖ xᵏ • β k` sums to zero at every point of an infinite subset of
the disc of radius `r`, is zero. -/
theorem eq_zero_of_hasSum_pow_smul (φ : ∀ j, E →L[K] L j)
    (hφ : ∀ e, (∀ j, φ j e = 0) → e = 0) {r : ℝ} {β : ℕ → E}
    (hβ : Tendsto (fun k ↦ ‖β k‖ * r ^ k) atTop (𝓝 0)) {S : Set K} (hS : S.Infinite)
    (hSr : ∀ x ∈ S, ‖x‖ ≤ r) (h : ∀ x ∈ S, HasSum (fun k ↦ x ^ k • β k) 0) : β = 0 :=
  eq_zero_of_hasSum_pow_smul_of_completeSpace (L := fun j ↦ UniformSpace.Completion (L j))
    (fun j ↦ (UniformSpace.Completion.toComplL : L j →L[K] _).comp (φ j))
    (fun e he ↦ hφ e fun j ↦ UniformSpace.Completion.coe_injective _ (by simpa using he j))
    hβ hS hSr h

end TauCeti.PowerSeries
