/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.UniqueFactorization
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Approximation
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Rueckert
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback

/-!
# The Nullstellensatz for holomorphic hypersurface germs

Let `x` be a point of a finite-dimensional complex manifold `X` without boundary, and let `s` and
`t` be holomorphic germs at `x`, represented near `x` by functions `F` and `G`. The germ `t`
vanishes on the zero germ of `s` when `G` vanishes at every zero of `F` near `x`. This file
proves that this happens exactly when some power of `t` is divisible by `s`, that is, when `t`
lies in the radical of the principal ideal `(s)`; for irreducible `s`, exactly when `s` divides
`t`. This is Rückert's Nullstellensatz for principal ideals of the ring of holomorphic germs,
and it identifies the germs vanishing on a hypersurface germ.

## Main results

* `TauCeti.holomorphicStructureSheaf.dvd_iff_of_irreducible`: an irreducible germ `s` divides `t`
  if and only if `t` vanishes on the zero germ of `s`.
* `TauCeti.holomorphicStructureSheaf.mem_radical_span_singleton_iff`: `t` lies in the radical of
  `(s)` if and only if `t` vanishes on the zero germ of `s`.

## Implementation notes

The irreducible case is proved in a chart. After an affine change of coordinates
(`TauCeti.holomorphicStructureSheaf.exists_ringEquiv_mul_eq_evalVertical`), `s` is a unit times
a distinguished polynomial `P` in the last coordinate `w`, and `P` is prime because the stalk is a
unique factorisation domain. Weierstrass division reduces `t` to a polynomial remainder `R`.
If `P` did not divide `R`, then, by Gauss's lemma, `P` and `R` would be coprime over the fraction
field of the base stalk, so their resultant `δ` would be a nonzero germ of the remaining
variables with `δ = P * a + R * b`. But every fibre of `P` over a point near the base point has a
root close to the base point (continuity of roots), at which both `P` and `R` vanish; so `δ`
vanishes near the base point, a contradiction. The radical case follows from the irreducible
one by unique factorisation.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II, §B.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §4.
-/

public noncomputable section

open Filter Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Model

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- If a distinguished polynomial `P` of positive degree and a polynomial `R` satisfy
`P * a + R * b = C δ`, and `evalVertical R` vanishes on the zero germ of `evalVertical P`, then
`δ = 0`. -/
private theorem eq_zero_of_mul_add_mul_eq_C {x₀ : E} {w₀ : ℂ}
    {P R a b : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    {δ : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hd : P.natDegree ≠ 0) (h : P * a + R * b = C δ) {F G : E × ℂ → ℂ}
    (hF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
      (evalVertical x₀ w₀ P) = F)
    (hG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
      (evalVertical x₀ w₀ R) = G)
    (hFG : ∀ᶠ p in 𝓝 (x₀, w₀), F p = 0 → G p = 0) : δ = 0 := by
  set d := P.natDegree
  -- Analytic representatives of the lower coefficients of `P`, vanishing at `x₀`.
  choose C hCan hC using fun i : Fin d ↦ exists_analyticAt_toFilterGerm_eq x₀ (P.coeff i)
  have hPc : TauCeti.Polynomial.monicOfCoeff (fun i : Fin d ↦ P.coeff i) = P :=
    TauCeti.Polynomial.monicOfCoeff_coeff hP.monic rfl
  have hC0 (i : Fin d) : C i x₀ = 0 := by
    rw [← eval_eq_of_toFilterGerm_eq (hC i _ le_rfl)]
    exact (isDistinguishedAt_monicOfCoeff_iff _).1 (hPc ▸ hP) i
  set Pf : E → ℂ[X] := fun x ↦ TauCeti.Polynomial.monicOfCoeff fun i ↦ C i x
  have hFeq : F =ᶠ[𝓝 (x₀, w₀)] fun p ↦ (Pf p.1).eval (p.2 - w₀) := by
    have := toFilterGerm_evalVertical_monicOfCoeff (w₀ := w₀) fun i ↦ hC i _ le_rfl
    rw [hPc, hF] at this
    exact Germ.coe_eq.1 this
  -- The Bézout identity, read on representatives.
  obtain ⟨A, -, hA⟩ := exists_toFilterGerm_eq (x₀, w₀) (evalVertical x₀ w₀ a)
  obtain ⟨B, -, hB⟩ := exists_toFilterGerm_eq (x₀, w₀) (evalVertical x₀ w₀ b)
  obtain ⟨D, -, hD⟩ := exists_toFilterGerm_eq x₀ δ
  have hid : (fun p ↦ F p * A p + G p * B p) =ᶠ[𝓝 (x₀, w₀)] fun p ↦ D p.1 := by
    have := congrArg (toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl)
      (congrArg (evalVertical x₀ w₀) h)
    rw [map_add, map_mul, map_mul, map_add, map_mul, map_mul, evalVertical_C, hF, hG,
      hA _ le_rfl, hB _ le_rfl, toFilterGerm_stalkPrecomp, hD _ le_rfl, Germ.coe_compTendsto,
      ← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add] at this
    exact Germ.coe_eq.1 this
  -- Near `(x₀, w₀)`, a zero of a fibre of `P` forces `D` to vanish at the base of the fibre.
  have hzero : ∀ᶠ p in 𝓝 (x₀, w₀), (Pf p.1).eval (p.2 - w₀) = 0 → D p.1 = 0 := by
    filter_upwards [hFeq, hFG, hid] with p hpF hpFG hpid hp
    rw [← hpid, hpFG (hpF.trans hp), hpF, hp]
    ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hzero
  -- Every fibre of `P` near `x₀` has a root of norm less than `ε`.
  have hroot : ∀ᶠ x in 𝓝 x₀, ∃ w : ℂ, (Pf x).IsRoot w ∧ ‖0 - w‖ < ε := by
    refine eventually_exists_isRoot_norm_sub_lt (fun i hi ↦ ?_)
      (Eventually.of_forall fun x ↦ (TauCeti.Polynomial.natDegree_monicOfCoeff _).le)
      (TauCeti.Polynomial.monic_monicOfCoeff _).ne_zero ?_ hε
    · rcases hi.lt_or_eq with hi | rfl
      · have hcoeff : (fun x ↦ (Pf x).coeff i) = C ⟨i, hi⟩ :=
          funext fun x ↦ TauCeti.Polynomial.coeff_monicOfCoeff _ ⟨i, hi⟩
        exact hcoeff ▸ (hCan ⟨i, hi⟩).continuousAt
      · simp only [TauCeti.Polynomial.coeff_monicOfCoeff_self]
        exact continuousAt_const
    · simp [IsRoot, TauCeti.Polynomial.eval_monicOfCoeff, hC0, hd]
  refine (eq_zero_iff_of_toFilterGerm_eq (hD _ le_rfl)).2 ?_
  filter_upwards [hroot, Metric.ball_mem_nhds x₀ hε] with x ⟨w, hw, hwε⟩ hx
  refine hball (y := (x, w₀ + w)) ?_ (by simpa using hw.eq_zero)
  rw [Prod.dist_eq, max_lt_iff, dist_self_add_left]
  exact ⟨hx, by simpa using hwε⟩

/-- An irreducible distinguished polynomial `P` divides every germ vanishing on the zero germ of
`evalVertical P`, after evaluation. -/
private theorem evalVertical_dvd_of_irreducible {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hirr : Irreducible P)
    {t : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {F G : E × ℂ → ℂ}
    (hF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl
      (evalVertical x₀ w₀ P) = F)
    (hG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl t = G)
    (hFG : ∀ᶠ p in 𝓝 (x₀, w₀), F p = 0 → G p = 0) : evalVertical x₀ w₀ P ∣ t := by
  obtain ⟨⟨q, R⟩, ⟨-, hdiv⟩, -⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hP t
  suffices hPR : P ∣ R by
    rw [hdiv]
    exact dvd_add (dvd_mul_right _ _) ((evalVertical_dvd_iff_of_isDistinguishedAt hP).1 hPR)
  by_contra hPR
  have hd : P.natDegree ≠ 0 := fun h0 ↦
    hirr.not_isUnit (by rw [eq_one_of_monic_natDegree_zero hP.monic h0]; exact isUnit_one)
  -- Over the fraction field `P` is irreducible and does not divide `R`, so the resultant of `P`
  -- and `R` is a nonzero combination of them.
  let K := FractionRing ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)
  have hinj := IsFractionRing.injective ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀) K
  have hcop : IsCoprime (P.map (algebraMap _ K)) (R.map (algebraMap _ K)) :=
    ((hP.monic.irreducible_iff_irreducible_map_fraction_map.1 hirr).coprime_iff_not_dvd).2
      fun h ↦ hPR ((map_dvd_map _ hinj hP.monic).1 h)
  have hres : resultant P R ≠ 0 := fun h0 ↦ by
    refine (resultant_eq_zero_iff.1 ?_).2 hcop
    rw [hP.monic.natDegree_map, natDegree_map_eq_of_injective hinj, resultant_map_map, h0,
      map_zero]
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant P R le_rfl le_rfl (Or.inl hd)
  obtain ⟨Q, -, hQ⟩ := exists_toFilterGerm_eq (x₀, w₀) q
  refine hres (eq_zero_of_mul_add_mul_eq_C hP hd hab hF (G := fun p ↦ G p - F p * Q p) ?_ ?_)
  · rw [show evalVertical x₀ w₀ R = t - evalVertical x₀ w₀ P * q by rw [hdiv]; ring, map_sub,
      map_mul, hF, hG, hQ _ le_rfl, ← Germ.coe_mul, ← Germ.coe_sub]
    rfl
  · filter_upwards [hFG] with p hp h0
    simp [h0, hp h0]

/-- In a model space `E × ℂ`, an irreducible holomorphic germ divides every germ vanishing on its
zero germ. -/
private theorem dvd_of_irreducible_prod {x₀ : E} {w₀ : ℂ}
    {s t : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hs : Irreducible s) {F G : E × ℂ → ℂ}
    (hF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl s = F)
    (hG : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl t = G)
    (hFG : ∀ᶠ p in 𝓝 (x₀, w₀), F p = 0 → G p = 0) : s ∣ t := by
  obtain ⟨φ, hφ, α, u, P, hα, hP, hu⟩ := exists_ringEquiv_mul_eq_evalVertical x₀ w₀ hs.ne_zero
  -- `evalVertical P` is associated to the irreducible germ `α s`, hence prime, and so is `P`.
  have hprime : Prime (evalVertical x₀ w₀ P) := hu ▸
    (associated_unit_mul_left (α s) _ u.isUnit).symm.prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.1 ((MulEquiv.irreducible_iff α).2 hs))
  have hPprime : Prime P := by
    refine ⟨hP.monic.ne_zero, fun h ↦ hprime.not_isUnit (h.map _), fun A B hAB ↦ ?_⟩
    rcases hprime.dvd_or_dvd (by simpa using map_dvd (evalVertical x₀ w₀) hAB) with h | h
    · exact .inl ((evalVertical_dvd_iff_of_isDistinguishedAt hP).2 h)
    · exact .inr ((evalVertical_dvd_iff_of_isDistinguishedAt hP).2 h)
  -- Read the vanishing hypothesis in the new coordinates.
  obtain ⟨U, hUc, hU⟩ := exists_toFilterGerm_eq (x₀, w₀)
    (u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀))
  have hU0 : U (x₀, w₀) ≠ 0 := by
    rw [← eval_eq_of_toFilterGerm_eq (hU _ le_rfl)]
    exact (isUnit_stalk_iff _ _ _).1 u.isUnit
  have hPt := evalVertical_dvd_of_irreducible hP hPprime.irreducible
    (F := fun p ↦ U p * F (φ p)) (G := fun p ↦ G (φ p))
    (by rw [← hu, map_mul, hα, hU _ le_rfl, hF, Germ.coe_compTendsto, ← Germ.coe_mul]; rfl)
    (by rw [hα, hG, Germ.coe_compTendsto]; rfl)
    (by
      filter_upwards [hUc.self_of_nhds.continuousAt.eventually_ne hU0, hφ.eventually hFG]
        with p hp hpFG h0
      exact hpFG ((mul_eq_zero.1 h0).resolve_left hp))
  exact (map_dvd_iff α).1 ((hu ▸ dvd_mul_left (α s) _).trans hPt)

end Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- An irreducible holomorphic germ divides every germ vanishing on its zero germ. -/
private theorem dvd_of_irreducible {x : X}
    {s t : (holomorphicStructureSheaf I X).presheaf.stalk x} (hs : Irreducible s) {F G : X → ℂ}
    (hF : toFilterGerm I X x (𝓝 x) le_rfl s = F) (hG : toFilterGerm I X x (𝓝 x) le_rfl t = G)
    (hFG : ∀ᶠ y in 𝓝 x, F y = 0 → G y = 0) : s ∣ t := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℂ E = n := ⟨_, rfl⟩
  cases n with
  | zero =>
    -- In dimension zero the stalk is a copy of the field `ℂ`, which has no irreducible elements.
    let e : E ≃L[ℂ] (Fin 0 → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
    have hs' := (MulEquiv.irreducible_iff ((stalkEquivModelSpace x e).trans
      (evalEquivOfNhdsEqPure 𝓘(ℂ, Fin 0 → ℂ) (congrFun (nhds_discrete _) _)))).2 hs
    exact absurd (isUnit_iff_ne_zero.2 hs'.ne_zero) hs'.not_isUnit
  | succ k =>
    -- Otherwise transport to the model `(Fin k → ℂ) × ℂ` through the chart at `x`.
    let e : E ≃L[ℂ] (Fin k → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hn])
    have htend : Tendsto ((extChartAt I x).symm ∘ e.symm) (𝓝 (e (extChartAt I x x))) (𝓝 x) := by
      have he := e.symm.continuous.tendsto (e (extChartAt I x x))
      rw [e.symm_apply_apply] at he
      simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm x).tendsto.comp he
    refine (map_dvd_iff (stalkEquivModelSpace x e)).1 (dvd_of_irreducible_prod
      ((MulEquiv.irreducible_iff _).2 hs) (F := F ∘ (extChartAt I x).symm ∘ e.symm)
      (G := G ∘ (extChartAt I x).symm ∘ e.symm) ?_ ?_ (htend.eventually hFG))
    · exact (toFilterGerm_stalkEquivModelSpace x e s).trans (by rw [hF]; rfl)
    · exact (toFilterGerm_stalkEquivModelSpace x e t).trans (by rw [hG]; rfl)

/-- **Rückert's Nullstellensatz for hypersurface germs.** Let `F` and `G` represent holomorphic
germs `s` and `t` at `x`. Then `t` lies in the radical of `(s)` if and only if `G` vanishes at
every zero of `F` near `x`. -/
theorem mem_radical_span_singleton_iff {x : X}
    {s t : (holomorphicStructureSheaf I X).presheaf.stalk x} {F G : X → ℂ}
    (hF : toFilterGerm I X x (𝓝 x) le_rfl s = F) (hG : toFilterGerm I X x (𝓝 x) le_rfl t = G) :
    t ∈ (Ideal.span {s}).radical ↔ ∀ᶠ y in 𝓝 x, F y = 0 → G y = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hk
    obtain ⟨Q, -, hQ⟩ := exists_toFilterGerm_eq x q
    have := congrArg (toFilterGerm I X x (𝓝 x) le_rfl) hq
    rw [map_mul, map_pow, hQ _ le_rfl, hF, hG, ← Germ.coe_mul, ← Germ.coe_pow] at this
    filter_upwards [Germ.coe_eq.1 this] with y hy h0
    exact (pow_eq_zero_iff'.1 (by rw [← Pi.pow_apply, ← hy, Pi.mul_apply, h0, mul_zero])).1
  · intro hFG
    by_cases hs0 : s = 0
    · have hG0 : G =ᶠ[𝓝 x] 0 := by
        filter_upwards [hFG, (eq_zero_iff_of_toFilterGerm_eq hF).1 hs0] with y hy hy0
        exact hy hy0
      rw [(eq_zero_iff_of_toFilterGerm_eq hG).2 hG0]
      exact Ideal.le_radical (Ideal.zero_mem _)
    classical
    -- Each irreducible factor of `s` divides `t`, so `s` divides a power of `t`.
    have hdvd (p) (hp : p ∈ UniqueFactorizationMonoid.factors s) : p ∣ t := by
      obtain ⟨r, hr⟩ := UniqueFactorizationMonoid.dvd_of_mem_factors hp
      obtain ⟨P, -, hP⟩ := exists_toFilterGerm_eq x p
      obtain ⟨R, -, hR⟩ := exists_toFilterGerm_eq x r
      have := congrArg (toFilterGerm I X x (𝓝 x) le_rfl) hr
      rw [map_mul, hF, hP _ le_rfl, hR _ le_rfl, ← Germ.coe_mul] at this
      refine dvd_of_irreducible (UniqueFactorizationMonoid.irreducible_of_factor p hp)
        (hP _ le_rfl) hG ?_
      filter_upwards [Germ.coe_eq.1 this, hFG] with y hy hyG h0
      exact hyG (by rw [hy, Pi.mul_apply, h0, zero_mul])
    refine ⟨(UniqueFactorizationMonoid.factors s).card, Ideal.mem_span_singleton.2 ?_⟩
    refine (UniqueFactorizationMonoid.factors_prod hs0).symm.dvd.trans ?_
    simpa using Multiset.prod_dvd_prod_of_dvd id (fun _ ↦ t) hdvd

/-- **The hypersurface Nullstellensatz.** Let `F` and `G` represent holomorphic germs `s` and `t`
at `x`, with `s` irreducible. Then `s` divides `t` if and only if `G` vanishes at every zero of
`F` near `x`. -/
theorem dvd_iff_of_irreducible {x : X}
    {s t : (holomorphicStructureSheaf I X).presheaf.stalk x} (hs : Irreducible s) {F G : X → ℂ}
    (hF : toFilterGerm I X x (𝓝 x) le_rfl s = F) (hG : toFilterGerm I X x (𝓝 x) le_rfl t = G) :
    s ∣ t ↔ ∀ᶠ y in 𝓝 x, F y = 0 → G y = 0 :=
  ⟨fun h ↦ (mem_radical_span_singleton_iff hF hG).1
    (Ideal.le_radical (Ideal.mem_span_singleton.2 h)), dvd_of_irreducible hs hF hG⟩

end TauCeti.holomorphicStructureSheaf
