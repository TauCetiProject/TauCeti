/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Preparation
import TauCeti.Analysis.Normed.Group.Basic

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

As a consequence, a series restricted at `c` that vanishes on an infinite subset of the closed disc
of radius `c` is zero. The bound is sharp: `X ^ p - X` over `ℚ_p` is distinguished of degree `p` at
the unit radius and vanishes at the `p` Teichmüller representatives in `ℤ_p`.

The identity principle extends to series with coefficients in a normed space `E` over `K` that
carries a jointly injective family of continuous linear maps `φⱼ : E → Lⱼ` into complete normed
field extensions of `K`: each `φⱼ` turns such a series into a restricted series over `Lⱼ`.

## Main results

* `TauCeti.PowerSeries.IsDistinguished.encard_setOf_evalAt_eq_zero_le`: Strassmann's theorem.
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
