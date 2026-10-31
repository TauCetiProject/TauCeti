/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RootsOfUnity.Descent

/-!
# Descent of equivariant functions through `u ↦ u ^ m`

Let `0 ≤ r < m`. A function `f` on a rotation-invariant open set `s ⊆ ℂ` which transforms under
the rotations by the `m`-th roots of unity by the character `ζ ↦ ζ ^ r`,
`f (ζ • u) = ζ ^ r • f u`, is not invariant, so it does not descend through the quotient map
`u ↦ u ^ m` itself. Its power series at `0` only has terms of degree congruent to `r` modulo `m`,
and the correct statement is the factorization

`f u = u ^ r • g (u ^ m)`

with `g` holomorphic on the open set `(· ^ m) '' s` of quotient-coordinate values
(`TauCeti.pow_smul_descendPowTwist_pow`). Consequently the order of `f` at `0` is
`r + m * ord₀ g` (`TauCeti.analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul`), and it
is congruent to `r` modulo `m`.

This is the local model for the sections of a line bundle on a quotient by a finite cyclic group
which acts on the fibre over the fixed point by a nontrivial character: the integer `r` is the
correction by which the order of a section upstairs exceeds `m` times the order of the descended
section. For automorphic forms of weight `k` at an elliptic point it produces the corrections
`⌊k / 4⌋` and `⌊k / 3⌋` of the dimension formulas, and at an irregular cusp of odd weight
(`m = 2`, `r = 1`) the half-integral orders.

The function `g` is `TauCeti.descendPowTwist m r f`, the difference quotient at `0` of the
descent (`TauCeti.descendPow`) of the invariant function `u ↦ u ^ (m - r) • f u`. It is the
unique continuous function with this factorization (`TauCeti.eqOn_descendPowTwist`).

## Main declarations

* `TauCeti.descendPowTwist`: the descent of a function transforming by `ζ ↦ ζ ^ r`.
* `TauCeti.differentiableOn_descendPowTwist` and `TauCeti.analyticOnNhd_descendPowTwist`: it is
  holomorphic, hence analytic, on `(· ^ m) '' s`.
* `TauCeti.pow_smul_descendPowTwist_pow`: the factorization `f u = u ^ r • g (u ^ m)` on `s`.
* `TauCeti.eqOn_descendPowTwist`: uniqueness of the factorization.
* `TauCeti.analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul`: `ord₀ f = r + ord₀ g * m`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §§2.3 and 3.1.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §3.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m r : ℕ} [NeZero m]

/-- The descent through `u ↦ u ^ m` of a function `f` transforming under the `m`-th roots of
unity by the character `ζ ↦ ζ ^ r`, for `r < m`: the function `g` with `f u = u ^ r • g (u ^ m)`
(`TauCeti.pow_smul_descendPowTwist_pow`). It is the difference quotient at `0` of the descent of
the invariant function `u ↦ u ^ (m - r) • f u`, which vanishes at `0`. -/
noncomputable def descendPowTwist (m r : ℕ) [NeZero m] (f : ℂ → E) : ℂ → E :=
  dslope (descendPow m fun u ↦ u ^ (m - r) • f u) 0

omit [NeZero m] in
/-- Multiplying a function transforming by `ζ ↦ ζ ^ r` by `u ^ (m - r)` makes it invariant. -/
private theorem pow_sub_smul_invariant {f : ℂ → E} {u : ℂ} (hr : r ≤ m)
    (hf : ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) (ζ : rootsOfUnity m ℂ) :
    (ζ • u) ^ (m - r) • f (ζ • u) = u ^ (m - r) • f u := by
  have hζ : ((ζ : ℂˣ) : ℂ) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m (ζ : ℂˣ)).mp ζ.2, Units.val_one]
  rw [hf, rootsOfUnity.smul_eq_mul, smul_smul, mul_pow, mul_assoc, mul_comm (u ^ (m - r)),
    ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr, hζ, one_mul]

/-- The invariant function `u ↦ u ^ (m - r) • f u` vanishes at `0` and so does its descent. -/
private theorem descendPow_pow_sub_smul_zero (hr : r < m) (f : ℂ → E) :
    descendPow m (fun u ↦ u ^ (m - r) • f u) 0 = 0 := by
  rw [descendPow_apply, Complex.zero_cpow (by simp [NeZero.ne m]),
    zero_pow (Nat.sub_ne_zero_of_lt hr), zero_smul]

/-- **The factorization away from `0`.** If `f` transforms by `ζ ↦ ζ ^ r` at a nonzero point `u`,
then `f u = u ^ r • descendPowTwist m r f (u ^ m)`. -/
theorem pow_smul_descendPowTwist_pow_of_ne_zero (hr : r < m) {f : ℂ → E} {u : ℂ} (hu : u ≠ 0)
    (hf : ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) :
    u ^ r • descendPowTwist m r f (u ^ m) = f u := by
  have hum : u ^ m ≠ 0 := pow_ne_zero m hu
  rw [descendPowTwist, dslope_of_ne _ hum, slope_def_module, descendPow_pow_sub_smul_zero hr,
    sub_zero, sub_zero, descendPow_pow (pow_sub_smul_invariant hr.le hf), smul_smul, smul_smul]
  convert one_smul ℂ (f u) using 2
  rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' hr.le, mul_inv_cancel₀ hum]

/-- **The descent of a holomorphic equivariant function is holomorphic.** If `f` is holomorphic
on an open set `s` and transforms by `ζ ↦ ζ ^ r` at every point of `s`, then
`descendPowTwist m r f` is holomorphic on the open set `(· ^ m) '' s`. -/
theorem differentiableOn_descendPowTwist [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}
    (hs : IsOpen s) (hr : r ≤ m) (hfd : DifferentiableOn ℂ f s)
    (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) :
    DifferentiableOn ℂ (descendPowTwist m r f) ((· ^ m) '' s) := by
  have hd := differentiableOn_descendPow hs ((differentiableOn_id.pow _).smul hfd)
    fun u hu ↦ pow_sub_smul_invariant hr (hf u hu)
  by_cases h0 : (0 : ℂ) ∈ (· ^ m) '' s
  · exact (Complex.differentiableOn_dslope
      (((Complex.isOpenQuotientMap_pow m).isOpenMap _ hs).mem_nhds h0)).mpr hd
  · exact (differentiableOn_dslope_of_notMem h0).mpr hd

/-- **The descent of a holomorphic equivariant function is analytic** at every point of the open
set `(· ^ m) '' s` of quotient-coordinate values, in particular at `0` when `0 ∈ s`. -/
theorem analyticOnNhd_descendPowTwist [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}
    (hs : IsOpen s) (hr : r ≤ m) (hfd : DifferentiableOn ℂ f s)
    (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) :
    AnalyticOnNhd ℂ (descendPowTwist m r f) ((· ^ m) '' s) :=
  (differentiableOn_descendPowTwist hs hr hfd hf).analyticOnNhd
    ((Complex.isOpenQuotientMap_pow m).isOpenMap _ hs)

/-- **The factorization of an equivariant function.** If `f` is holomorphic on an open set `s`
and transforms by `ζ ↦ ζ ^ r` at every point of `s`, with `r < m`, then
`f u = u ^ r • descendPowTwist m r f (u ^ m)` for every `u ∈ s`, including `u = 0`. -/
theorem pow_smul_descendPowTwist_pow [CompleteSpace E] {s : Set ℂ} {f : ℂ → E} (hs : IsOpen s)
    (hr : r < m) (hfd : DifferentiableOn ℂ f s)
    (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) {u : ℂ}
    (hu : u ∈ s) : u ^ r • descendPowTwist m r f (u ^ m) = f u := by
  rcases ne_or_eq u 0 with hu0 | rfl
  · exact pow_smul_descendPowTwist_pow_of_ne_zero hr hu0 (hf u hu)
  -- At `0` both sides are continuous and agree on a punctured neighbourhood.
  have hG : ContinuousAt (descendPowTwist m r f) 0 :=
    (analyticOnNhd_descendPowTwist hs hr.le hfd hf 0 ⟨0, hu, zero_pow (NeZero.ne m)⟩).continuousAt
  have hlhs : ContinuousAt (fun u : ℂ ↦ u ^ r • descendPowTwist m r f (u ^ m)) 0 :=
    (continuousAt_id.pow r).smul
      (hG.comp_of_eq (continuous_pow m).continuousAt (zero_pow (NeZero.ne m)))
  have heq : (fun u : ℂ ↦ u ^ r • descendPowTwist m r f (u ^ m)) =ᶠ[𝓝[≠] 0] f :=
    (eventually_nhdsWithin_of_eventually_nhds (hs.mem_nhds hu)).mp <|
      eventually_nhdsWithin_of_forall fun v hv hvs ↦
        pow_smul_descendPowTwist_pow_of_ne_zero hr hv (hf v hvs)
  exact ((hlhs.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hfd.differentiableAt (hs.mem_nhds hu)).continuousAt).mp heq).eq_of_nhds

/-- **Uniqueness of the factorization.** If `f` is holomorphic and transforms by `ζ ↦ ζ ^ r` on
an open set `s`, with `r < m`, then any function `g` continuous on `(· ^ m) '' s` with
`f u = u ^ r • g (u ^ m)` on `s` is `descendPowTwist m r f` there. -/
theorem eqOn_descendPowTwist [CompleteSpace E] {s : Set ℂ} {f g : ℂ → E} (hs : IsOpen s)
    (hr : r < m) (hfd : DifferentiableOn ℂ f s)
    (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u)
    (hg : ContinuousOn g ((· ^ m) '' s)) (hfg : ∀ u ∈ s, f u = u ^ r • g (u ^ m)) :
    EqOn g (descendPowTwist m r f) ((· ^ m) '' s) := by
  have hopen : IsOpen ((· ^ m) '' s) := (Complex.isOpenQuotientMap_pow m).isOpenMap _ hs
  -- Away from `0` the factor `u ^ r` cancels.
  have hne : ∀ w ∈ (· ^ m) '' s, w ≠ 0 → g w = descendPowTwist m r f w := by
    rintro _ ⟨u, hu, rfl⟩ hw
    have hu0 : u ≠ 0 := by rintro rfl; exact hw (zero_pow (NeZero.ne m))
    refine smul_right_injective E (pow_ne_zero r hu0) ?_
    simp only
    rw [← hfg u hu, pow_smul_descendPowTwist_pow hs hr hfd hf hu]
  intro w hw
  rcases ne_or_eq w 0 with hw0 | rfl
  · exact hne w hw hw0
  -- At `0` both functions are continuous and agree on a punctured neighbourhood.
  have hG : ContinuousAt (descendPowTwist m r f) 0 :=
    (analyticOnNhd_descendPowTwist hs hr.le hfd hf 0 hw).continuousAt
  have heq : g =ᶠ[𝓝[≠] 0] descendPowTwist m r f :=
    (eventually_nhdsWithin_of_eventually_nhds (hopen.mem_nhds hw)).mp <|
      eventually_nhdsWithin_of_forall fun v hv hvs ↦ hne v hvs hv
  exact (((hg.continuousAt (hopen.mem_nhds hw)).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    hG).mp heq).eq_of_nhds

/-- **The order of an equivariant function.** If `f` is holomorphic and transforms by
`ζ ↦ ζ ^ r` on an open set `s` containing `0`, with `r < m`, then its order at `0` is `r` plus
`m` times the order of its descent: `ord₀ f = r + ord₀ (descendPowTwist m r f) * m`. -/
theorem analyticOrderAt_eq_add_analyticOrderAt_descendPowTwist_mul [CompleteSpace E] {s : Set ℂ}
    {f : ℂ → E} (hs : IsOpen s) (h0 : 0 ∈ s) (hr : r < m) (hfd : DifferentiableOn ℂ f s)
    (hf : ∀ u ∈ s, ∀ ζ : rootsOfUnity m ℂ, f (ζ • u) = ((ζ : ℂˣ) : ℂ) ^ r • f u) :
    analyticOrderAt f 0 = r + analyticOrderAt (descendPowTwist m r f) 0 * m := by
  have hGa : AnalyticAt ℂ (descendPowTwist m r f) 0 :=
    analyticOnNhd_descendPowTwist hs hr.le hfd hf 0 ⟨0, h0, zero_pow (NeZero.ne m)⟩
  have heq : (fun u : ℂ ↦ u ^ r) • (fun u : ℂ ↦ descendPowTwist m r f (u ^ m)) =ᶠ[𝓝 0] f :=
    Filter.mem_of_superset (hs.mem_nhds h0) fun u hu ↦ pow_smul_descendPowTwist_pow hs hr hfd hf hu
  have hcomp : AnalyticAt ℂ (fun u : ℂ ↦ descendPowTwist m r f (u ^ m)) 0 :=
    hGa.comp_of_eq (by fun_prop) (zero_pow (NeZero.ne m))
  have hpow : (fun u : ℂ ↦ u ^ r) = (· - 0) ^ r := funext fun u ↦ by simp
  rw [← analyticOrderAt_congr heq, analyticOrderAt_smul (by fun_prop) hcomp, hpow,
    analyticOrderAt_centeredMonomial,
    analyticOrderAt_comp_pow_zero hGa (Nat.pos_of_neZero m)]

end TauCeti
