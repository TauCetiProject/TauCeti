/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Cerf
-- Private: used only inside proofs.
import TauCeti.Analysis.Calculus.ContDiff.Prod
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.Analysis.Normed.Operator.Splitting.Bordered
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Birth–death points of a one-parameter family are isolated degeneracies

Let `f t : E → ℝ` be a one-parameter family of functions on a finite-dimensional real normed space
`E`, jointly `C³`. Its critical points are the zeros of the parametrized differential
`G (t, x) = d(f t)_x`, and the family is *transverse* at `(t, x)` when the derivative of `G` there
is onto (`TauCeti.surjective_fderiv_fderiv_iff`). At a transverse critical point the Hessian has
corank at most one (`TauCeti.finrank_ker_fderiv_fderiv_le_one`), so a degenerate critical point has
a kernel line spanned by some `v ≠ 0`. It is a *birth–death point*, or an `A₂` singularity, when
moreover the third derivative along the kernel does not vanish:

`D³(f t)_x (v, v, v) ≠ 0`.

This is the condition of Cerf's theorem that a generic family satisfies at each of its degenerate
critical points, besides transversality. The main result of this file is that a birth–death point
is an **isolated degeneracy** of the family: near it, every other critical point of every nearby
`f s` is nondegenerate (`TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`). The
hypotheses are stated so that they also cover a nondegenerate critical point, near which there is
nothing to prove. Consequently, if the family is transverse and satisfies the cubic condition at
every critical point of a compact set `K ⊆ ℝ × E`, it has only finitely many degenerate critical
points in `K` (`TauCeti.finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint`), and in
particular only finitely many parameters `t` at which `f t` has a degenerate critical point in `K`.

The proof uses two auxiliary linear maps at the birth–death point `(t₀, x₀)`, with `H(t, x)` the
Hessian of `f t` at `x`, `v` a kernel vector of `H(t₀, x₀)` and `ℓ` a functional with `ℓ v = 1`.

* The **bordered Hessian** `(w, μ) ↦ (H(t, x) w + μ ℓ, ℓ w)` is invertible at `(t₀, x₀)`, by the
  symmetry of the Hessian, and so near it. Near `(t₀, x₀)`, whenever `H(t, x)` is degenerate, its
  kernel is spanned by the vector `w(t, x)` read off the kernel section of the bordered Hessian
  (`ContinuousLinearMap.kerSection`), which tends to `v`
  (`ContinuousLinearMap.exists_tendsto_eventually_apply_eq_zero`).
* The map `Ψ ((t, x), w) = (d(f t)_x, H(t, x) w, ℓ w)` has an injective derivative at
  `((t₀, x₀), v)`: its first component cuts the critical locus transversally along the line of
  `(0, v)`, and along that line the cubic condition moves `H(t, x) v` off the range of the
  Hessian. So near `((t₀, x₀), v)` the map `Ψ` takes the value `Ψ ((t₀, x₀), v)` only there,
  whereas a degenerate critical point `(t, x) ≠ (t₀, x₀)` near `(t₀, x₀)` would give
  `Ψ ((t, x), w(t, x)) = Ψ ((t₀, x₀), v)`.

The cubic condition cannot be dropped. The family `f t x = t x` on `ℝ` is transverse at `(0, 0)`
(`TauCeti.surjective_fderiv_fderiv_mul_zero_zero`), but its Hessians all vanish, and every point
`(0, x)` is a degenerate critical point
(`TauCeti.not_eventually_isNondegenerateCriticalPoint_mul_zero_zero`). The birth–death family
`x³ / 3 - s x` of `TauCeti.Analysis.Calculus.Morse.BirthDeath` is the model case: it is transverse
at its degenerate critical point `(0, 0)` (`TauCeti.surjective_fderiv_fderiv_birthDeathPotential`),
and its third derivative is `2` (`TauCeti.iteratedDeriv_three_birthDeathPotential`).

## Main results

* `TauCeti.eq_zero_of_fderiv_fderiv_fderiv_apply_eq_zero`: at a transverse point, one kernel
  vector `v` of the Hessian with `D³(f t)_x (v, v, v) ≠ 0` gives the cubic condition for the whole
  kernel.
* `TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`: near a transverse critical
  point at which the third derivative does not vanish along the kernel of the Hessian, every other
  critical point of the family is nondegenerate.
* `TauCeti.finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint`: such a family has
  finitely many degenerate critical points in a compact set.

## References

* J. Cerf, *La stratification naturelle des espaces de fonctions différentiables réelles et le
  théorème de la pseudo-isotopie*, Publ. Math. IHÉS **39** (1970), 5–173, Chapter III.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4 (generic one-parameter families and bifurcations).
-/

public section

open Function Module Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E → ℝ} {t : ℝ} {x : E}

/-! ### The derivative at a birth–death point -/

/-- **The derivative of the augmented critical-point map is injective at a birth–death point.**
Here `H₀` stands for the Hessian, symmetric with kernel the line spanned by `v`, `a` for the
parameter derivative `∂ₜ (d(f t)_x)` of the differential, `D` for the derivative of the Hessian
in the parameter and the point, and `ℓ v = 1`. The three equations are the vanishing of the
derivative of `((t, x), w) ↦ (d(f t)_x, H(t, x) w, ℓ w)` at `((t₀, x₀), v)` in the direction
`(q, η)`. -/
private theorem eq_zero_of_birthDeath {H₀ : E →L[ℝ] StrongDual ℝ E}
    (hsymm : ∀ u w, H₀ u w = H₀ w u) {v : E} (hv : H₀ v = 0)
    (hker : ∀ u, H₀ u = 0 → ∃ c : ℝ, u = c • v) {a : StrongDual ℝ E} (ha : a v ≠ 0)
    {D : ℝ × E →L[ℝ] E →L[ℝ] StrongDual ℝ E} (hD : D (0, v) v v ≠ 0) {ℓ : StrongDual ℝ E}
    (hℓ : ℓ v = 1) {q : ℝ × E} {η : E} (h₁ : q.1 • a + H₀ q.2 = 0) (h₂ : H₀ η + D q v = 0)
    (h₃ : ℓ η = 0) : q = 0 ∧ η = 0 := by
  obtain ⟨τ, ξ⟩ := q
  -- Pairing the first equation with `v` gives `τ = 0`, so `ξ` lies on the kernel line.
  have hτ : τ = 0 := by
    simpa [hsymm ξ v, hv, ha] using congrArg (· v) h₁
  subst hτ
  obtain ⟨c, rfl⟩ := hker ξ (by simpa using h₁)
  -- Pairing the second equation with `v` gives `c D(0, v)(v, v) = 0`, so `c = 0`.
  have hc : c = 0 := by
    have hq : ((0 : ℝ), c • v) = c • ((0 : ℝ), v) := by simp
    rw [hq, map_smul] at h₂
    simpa [hsymm η v, hv, hD] using congrArg (· v) h₂
  subst hc
  have hD₀ : D ((0 : ℝ), (0 : E)) = 0 := map_zero D
  obtain ⟨d, rfl⟩ := hker η (by simpa [hD₀] using h₂)
  simp_all

/-! ### Isolation of birth–death points -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **The augmented critical-point map is locally injective at a birth–death point.** Let `G` be
the parametrized differential and `H` the Hessian of a family, differentiable at `p`, with
`dG_p (τ, ξ) = τ a + H p ξ`, and let `v`, `ℓ` and the hypotheses be as in
`eq_zero_of_birthDeath`. Then the map `(q, w) ↦ (G q, H q w, ℓ w)` takes its value at `(p, v)` at
no other point near `(p, v)`, since its derivative there is injective. -/
private theorem eventually_ne_of_birthDeath {G : ℝ × E → StrongDual ℝ E}
    {H : ℝ × E → E →L[ℝ] StrongDual ℝ E} {p : ℝ × E} (hG : DifferentiableAt ℝ G p)
    (hH : DifferentiableAt ℝ H p) {a : StrongDual ℝ E}
    (hGa : ∀ q, fderiv ℝ G p q = q.1 • a + H p q.2) (hsymm : ∀ u w, H p u w = H p w u) {v : E}
    (hv : H p v = 0) (hker : ∀ u, H p u = 0 → ∃ c : ℝ, u = c • v) (ha : a v ≠ 0)
    (hD : fderiv ℝ H p (0, v) v v ≠ 0) {ℓ : StrongDual ℝ E} (hℓ : ℓ v = 1) :
    ∀ᶠ z in 𝓝[≠] (p, v), ((G z.1, H z.1 z.2), ℓ z.2) ≠ ((G p, H p v), ℓ v) := by
  obtain ⟨D, hΨ, hD'⟩ : ∃ D, HasFDerivAt (fun z : (ℝ × E) × E ↦ ((G z.1, H z.1 z.2), ℓ z.2)) D
      (p, v) ∧ ∀ q η, D (q, η) = ((q.1 • a + H p q.2, H p η + fderiv ℝ H p q v), ℓ η) := by
    have h₁ : HasFDerivAt (fun z : (ℝ × E) × E ↦ G z.1)
        ((fderiv ℝ G p).comp (ContinuousLinearMap.fst ℝ (ℝ × E) E)) (p, v) :=
      hG.hasFDerivAt.comp (f := Prod.fst) (p, v) hasFDerivAt_fst
    have h₂ : HasFDerivAt (fun z : (ℝ × E) × E ↦ H z.1)
        ((fderiv ℝ H p).comp (ContinuousLinearMap.fst ℝ (ℝ × E) E)) (p, v) :=
      hH.hasFDerivAt.comp (f := Prod.fst) (p, v) hasFDerivAt_fst
    exact ⟨_, (h₁.prodMk (h₂.clm_apply hasFDerivAt_snd)).prodMk
      (ℓ.hasFDerivAt.comp (p, v) hasFDerivAt_snd), fun q η ↦ by simp [hGa]⟩
  have hinj : Injective D := (injective_iff_map_eq_zero _).2 fun ⟨q, η⟩ h ↦ by
    rw [hD'] at h
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := Prod.mk_eq_zero.1 h |>.imp_left Prod.mk_eq_zero.1
    obtain ⟨rfl, rfl⟩ := eq_zero_of_birthDeath hsymm hv hker ha hD hℓ h₁ h₂ h₃
    rfl
  obtain ⟨K, -, hK⟩ := (D.toLinearMap.injective_iff_antilipschitz).1 hinj
  exact hΨ.eventually_ne ⟨K, hK⟩

/-- The case of `TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero` at a degenerate
critical point, with a nonzero kernel vector `v` of the Hessian: nearby, the Hessians at the other
critical points are injective. -/
private theorem eventually_injective_of_birthDeath (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (h3 : ∀ v, fderiv ℝ (fderiv ℝ (f t)) x v = 0 →
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v = 0 → v = 0)
    {v : E} (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0) (hv0 : v ≠ 0) (hc : fderiv ℝ (f t) x = 0) :
    ∀ᶠ z in 𝓝[≠] (t, x), fderiv ℝ (f z.1) z.2 = 0 →
      Injective (fderiv ℝ (fderiv ℝ (f z.1)) z.2) := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  set H : ℝ × E → E →L[ℝ] StrongDual ℝ E := fun w ↦ fderiv ℝ (fderiv ℝ (f w.1)) w.2
  have hf2 : ContDiffAt ℝ 2 (uncurry f) (t, x) := hf.of_le (by norm_num)
  have hG : ContDiffAt ℝ 2 G (t, x) := hf.fderiv_slice (m := 2) le_rfl
  have hH : ContDiffAt ℝ 1 H (t, x) := hG.fderiv_slice (m := 1) le_rfl
  have hsymm : ∀ u w, H (t, x) u w = H (t, x) w u := fderiv_fderiv_apply_comm_of_uncurry hf2
  have hker : ∀ u, H (t, x) u = 0 → ∃ c : ℝ, u = c • v :=
    fun u hu ↦ exists_eq_smul_of_fderiv_fderiv_apply_eq_zero hf2 hs hv0 hv hu
  have ha : deriv (fun s ↦ fderiv ℝ (f s) x) t v ≠ 0 :=
    fun h ↦ hv0 ((surjective_fderiv_fderiv_iff hf2).1 hs v hv h)
  -- The derivative of the Hessian in the direction `(0, v)` is the third derivative along `v`.
  have hD : fderiv ℝ H (t, x) (0, v) v v ≠ 0 := by
    rw [fderiv_apply_eq_fderiv_slice_left_add_fderiv_slice_right
      (hH.differentiableAt one_ne_zero)]
    simpa [H] using fun h ↦ hv0 (h3 v hv h)
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_eq_one (R := ℝ) hv0
  obtain ⟨W, hWt, hWev⟩ :=
    ContinuousLinearMap.exists_tendsto_eventually_apply_eq_zero hH.continuousAt hv
      (fun w ↦ (hsymm w v).trans (by simp [H, hv])) hℓ hker
  have hne := eventually_ne_of_birthDeath (hG.differentiableAt two_ne_zero)
    (hH.differentiableAt one_ne_zero) (fderiv_fderiv_apply hf2) hsymm hv hker ha hD hℓ
  -- The curve `z ↦ (z, W z)` approaches `((t, x), v)` from outside it.
  have htend : Tendsto (fun z ↦ (z, W z)) (𝓝[≠] (t, x)) (𝓝[≠] ((t, x), v)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((tendsto_id.prodMk_nhds hWt).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun z hz h ↦ hz (congrArg Prod.fst h))
  filter_upwards [htend.eventually hne, nhdsWithin_le_nhds hWev] with z hzΨ hzW hz₀
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ by_contra fun hu0 ↦ hzΨ ?_
  obtain ⟨h₁, h₂⟩ := hzW u hu hu0
  simp only [Prod.mk.injEq]
  exact ⟨⟨hz₀.trans hc.symm, h₁.trans hv.symm⟩, h₂.trans hℓ.symm⟩

/-- **The cubic condition along the kernel line.** At a transverse point, if the Hessian of
`f t` at `x` has a kernel vector `v` with `D³(f t)_x (v, v, v) ≠ 0`, then no nonzero kernel vector
`u` has `D³(f t)_x (u, u, u) = 0`, since `u` is a multiple of `v`. So a single such `v` supplies the
cubic hypothesis of `TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`. -/
theorem eq_zero_of_fderiv_fderiv_fderiv_apply_eq_zero
    (hf : ContDiffAt ℝ 2 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x))) {v : E}
    (hv : fderiv ℝ (fderiv ℝ (f t)) x v = 0)
    (hκ : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v ≠ 0) {u : E}
    (hu : fderiv ℝ (fderiv ℝ (f t)) x u = 0)
    (hu3 : fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x u u u = 0) : u = 0 := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hκ
  obtain ⟨k, rfl⟩ := exists_eq_smul_of_fderiv_fderiv_apply_eq_zero hf hs hv0 hv hu
  have hk : k ^ 3 * fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v = 0 := by
    simpa [pow_succ, mul_assoc] using hu3
  simp [pow_eq_zero_iff, hκ] at hk
  simp [hk]

/-- **Birth–death points are isolated degeneracies.** Let `f t` be a family of functions on a
finite-dimensional real normed space, jointly `C³` at `(t, x)` and transverse there: the derivative
of the parametrized differential `(t, x) ↦ d(f t)_x` is onto. Suppose that no nonzero vector `v` of
the kernel of the Hessian of `f t` at `x` has `D³(f t)_x (v, v, v) = 0`. Then near `(t, x)`, every
critical point `y` of `f s`, with `(s, y) ≠ (t, x)`, is nondegenerate.

At a critical point the hypotheses say that `(t, x)` is either a nondegenerate critical point or a
birth–death point. -/
theorem eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero
    (hf : ContDiffAt ℝ 3 (uncurry f) (t, x))
    (hs : Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) (t, x)))
    (h3 : ∀ v, fderiv ℝ (fderiv ℝ (f t)) x v = 0 →
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f t))) x v v v = 0 → v = 0) :
    ∀ᶠ z in 𝓝[≠] (t, x), fderiv ℝ (f z.1) z.2 = 0 → IsNondegenerateCriticalPoint (f z.1) z.2 := by
  set G : ℝ × E → StrongDual ℝ E := fun w ↦ fderiv ℝ (f w.1) w.2
  set H : ℝ × E → E →L[ℝ] StrongDual ℝ E := fun w ↦ fderiv ℝ (fderiv ℝ (f w.1)) w.2
  have hG : ContDiffAt ℝ 2 G (t, x) := hf.fderiv_slice (m := 2) le_rfl
  have hH : ContDiffAt ℝ 1 H (t, x) := hG.fderiv_slice (m := 1) le_rfl
  have hdim : finrank ℝ E = finrank ℝ (StrongDual ℝ E) := by
    simp [ContinuousLinearMap.dual_finrank_eq]
  -- It suffices to show that the nearby Hessians at critical points are injective.
  suffices hinj : ∀ᶠ z in 𝓝[≠] (t, x), G z = 0 → Injective (H z) by
    filter_upwards [nhdsWithin_le_nhds (hf.eventually (by simp)), hinj] with z hz hz₁ hz₀
    exact ⟨(hz.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num), hz₀,
      (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim).2 (hz₁ hz₀)⟩
  by_cases hk : ∀ v, H (t, x) v = 0 → v = 0
  · -- A nondegenerate Hessian stays nondegenerate nearby.
    have hH₀ : (H (t, x)).IsInvertible :=
      (ContinuousLinearMap.isInvertible_iff_injective_of_finrank_eq hdim).2
        ((injective_iff_map_eq_zero _).2 hk)
    filter_upwards [nhdsWithin_le_nhds (hH.continuousAt.eventually hH₀.eventually_nhds)]
      with z hz _ using hz.injective
  obtain ⟨v, hv, hv0⟩ : ∃ v, H (t, x) v = 0 ∧ v ≠ 0 := by simpa using hk
  rcases eq_or_ne (G (t, x)) 0 with hG₀ | hG₀
  · exact eventually_injective_of_birthDeath hf hs h3 hv hv0 hG₀
  -- Away from the critical locus there is nothing to prove.
  filter_upwards [nhdsWithin_le_nhds (hG.continuousAt.eventually_ne hG₀)] with z hz hz₀
  exact absurd hz₀ hz

/-- **A family with only birth–death degeneracies has finitely many of them in a compact set.** Let
`K ⊆ ℝ × E` be compact and the family jointly `C³` at every point of `K`. Suppose that at every
critical point in `K` the family is transverse, and no nonzero vector `v` of the kernel of the
Hessian has `D³(f t)_x (v, v, v) = 0`. Then only finitely many points `(t, x) ∈ K` are degenerate
critical points of `f t`, so only finitely many parameters `t` have one in `K`. -/
theorem finite_setOf_fderiv_eq_zero_and_not_isNondegenerateCriticalPoint {K : Set (ℝ × E)}
    (hK : IsCompact K) (hf : ∀ z ∈ K, ContDiffAt ℝ 3 (uncurry f) z)
    (hs : ∀ z ∈ K, fderiv ℝ (f z.1) z.2 = 0 →
      Surjective (fderiv ℝ (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) z))
    (h3 : ∀ z ∈ K, fderiv ℝ (f z.1) z.2 = 0 → ∀ v, fderiv ℝ (fderiv ℝ (f z.1)) z.2 v = 0 →
      fderiv ℝ (fderiv ℝ (fderiv ℝ (f z.1))) z.2 v v v = 0 → v = 0) :
    {z ∈ K | fderiv ℝ (f z.1) z.2 = 0 ∧ ¬ IsNondegenerateCriticalPoint (f z.1) z.2}.Finite := by
  set S := {z ∈ K | fderiv ℝ (f z.1) z.2 = 0 ∧ ¬ IsNondegenerateCriticalPoint (f z.1) z.2}
  have hGc : ContinuousOn (fun w : ℝ × E ↦ fderiv ℝ (f w.1) w.2) K := fun z hz ↦
    ((hf z hz).fderiv_slice (m := 2) le_rfl).continuousAt.continuousWithinAt
  have hHc : ContinuousOn (fun w : ℝ × E ↦ fderiv ℝ (fderiv ℝ (f w.1)) w.2) K := fun z hz ↦
    (((hf z hz).fderiv_slice (m := 2) le_rfl).fderiv_slice (m := 1) le_rfl).continuousAt
      |>.continuousWithinAt
  -- On `K`, a degenerate critical point is a zero of the differential with a singular Hessian, so
  -- the degenerate critical points form a closed set.
  have hclosed : IsClosed S := by
    convert (hGc.preimage_isClosed_of_isClosed hK.isClosed (isClosed_singleton (x := 0))).inter
      (hHc.preimage_isClosed_of_isClosed hK.isClosed
        ContinuousLinearMap.isOpen_setOfPred_isInvertible.isClosed_compl) using 1
    ext z
    refine ⟨fun ⟨hzK, hz₀, hzn⟩ ↦ ⟨⟨hzK, hz₀⟩, hzK, fun hinv ↦ hzn ⟨?_, hz₀, hinv⟩⟩,
      fun ⟨⟨hzK, hz₀⟩, _, hzn⟩ ↦ ⟨hzK, hz₀, fun h ↦ hzn h.isInvertible⟩⟩
    exact ((hf z hzK).comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  -- Each of them is isolated among the critical points.
  have hdisc : IsDiscrete S := by
    rw [isDiscrete_iff_nhdsNE]
    rintro z ⟨hzK, hz₀, -⟩
    rw [inf_principal_eq_bot]
    filter_upwards [eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero (t := z.1)
      (x := z.2) (hf z hzK) (hs z hzK hz₀) (h3 z hzK hz₀)] with y hy
    rintro ⟨-, hy₀, hyn⟩
    exact hyn (hy hy₀)
  exact (hK.of_isClosed_subset hclosed fun _ hz ↦ hz.1).finite hdisc

end FiniteDimensional

/-! ### The cubic condition cannot be dropped -/

/-- The differential of `y ↦ s y` is multiplication by `s`. -/
private theorem fderiv_mul_left (s y : ℝ) :
    fderiv ℝ (fun y ↦ s * y) y = s • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp

/-- **The family `f t x = t x` is transverse at `(0, 0)`.** The parameter derivative of its
differential is the identity, which is injective on the kernel of every Hessian. -/
theorem surjective_fderiv_fderiv_mul_zero_zero :
    Surjective (fderiv ℝ (fun w : ℝ × ℝ ↦ fderiv ℝ (fun y ↦ w.1 * y) w.2) (0, 0)) := by
  refine (surjective_fderiv_fderiv_iff (f := fun s y ↦ s * y) (by fun_prop)).2 fun v _ hv ↦ ?_
  have hd : HasDerivAt (fun s : ℝ ↦ s • ContinuousLinearMap.id ℝ ℝ)
      ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ) 0 :=
    (hasDerivAt_id' (0 : ℝ)).smul_const (ContinuousLinearMap.id ℝ ℝ)
  simp_rw [fderiv_mul_left, hd.deriv] at hv
  simpa using hv

/-- **Without the cubic condition degeneracies need not be isolated.** The family `f t x = t x` is
transverse at `(0, 0)` (`TauCeti.surjective_fderiv_fderiv_mul_zero_zero`), but its Hessians all
vanish, and every point `(0, x)` is a degenerate critical point. Its third derivative vanishes, so
it does not satisfy the cubic condition of
`TauCeti.eventually_isNondegenerateCriticalPoint_of_fderiv_eq_zero`. -/
theorem not_eventually_isNondegenerateCriticalPoint_mul_zero_zero :
    ¬ ∀ᶠ z in 𝓝[≠] ((0 : ℝ), (0 : ℝ)), fderiv ℝ (fun y ↦ z.1 * y) z.2 = 0 →
      IsNondegenerateCriticalPoint (fun y ↦ z.1 * y) z.2 := by
  intro h
  have htend : Tendsto (fun y : ℝ ↦ ((0 : ℝ), y)) (𝓝[≠] 0) (𝓝[≠] ((0 : ℝ), (0 : ℝ))) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (((continuous_const.prodMk continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun y hy h ↦ hy (congrArg Prod.snd h))
  obtain ⟨y, hy⟩ := (htend.eventually h).exists
  have hinv := (hy (by simp)).isInvertible
  exact one_ne_zero (hinv.injective (a₁ := (1 : ℝ)) (a₂ := 0) (by simp))

end TauCeti
