/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Multiplicity
public import TauCeti.Analysis.Analytic.FiniteFamily
public import TauCeti.Analysis.Polynomial.Conjugation

/-!
# Ordered real roots of finite nonmonic Laurent limits

The finite limits of a nonmonic Puiseux splitting give strictly ordered real analytic root
sections of a nonzero divided central-fiber family, with constant positive multiplicities.
Branches with negative Laurent exponent contribute no finite root. Repeated finite limits
are allowed and are removed by one fixed selection of labels on a common open neighborhood.

The complex root multiset of the real divided family is an input along the real parameter
space: for Lazard evaluations it is supplied by
`MvPolynomial.roots_lazardEval_eq_map_of_laurent`. This family need not be the ordinary
central fiber, which can be nullified. Nonzeroness of the divided family is required
separately, including when there are no finite branches. Reality of the selected labels,
their strict ordering, and constancy of their multiplicities are conclusions.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, §5.2, proof of Theorem 5.1.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Finite Laurent limits of a prepared nonmonic splitting descend to a complete, strictly
ordered analytic list of real roots of a nonzero divided central-fiber family. Every section
has constant positive multiplicity on one open neighborhood. The real label set and distinct
root count are derived, and an empty finite-label set or an empty real-root set is allowed.

For Lazard evaluation, `MvPolynomial.roots_lazardEval_eq_map_of_laurent` supplies the root
multiset identity; this statement concerns the real divided family `F`, not a possibly zero
ordinary central fiber of `P`. Analyticity is required only for the amplitudes of the finite
branches. -/
theorem exists_analyticOnNhd_ordered_real_roots_of_finite_laurent_limits
    {d a c : ℕ} {P : E × ℂ → ℂ[X]} {r s : Fin d → E × ℂ → ℂ}
    {φ : B → E} {b₀ : B} {F : B → ℝ[X]}
    {u v : E × ℂ → ℂ} {e : Fin d → ℤ} {w : Fin d → E × ℂ → ℂ}
    (hs : ∀ i, AnalyticAt ℂ (s i) (φ b₀, 0))
    (hu : AnalyticAt ℂ u (φ b₀, 0)) (hu0 : u (φ b₀, 0) ≠ 0)
    (hv : AnalyticAt ℂ v (φ b₀, 0)) (hv0 : v (φ b₀, 0) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).coeff d = p.2 ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).discr = p.2 ^ a * u p)
    (hscale : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, 0 ≤ e i → (P p).coeff d * r i p = s i p)
    (hw : ∀ i, 0 ≤ e i → AnalyticAt ℂ (w i) (φ b₀, 0))
    (hLaurent : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, 0 ≤ e i → r i p = p.2 ^ e i * w i p)
    (hroots : ∀ᶠ b in 𝓝 b₀, ((F b).map (algebraMap ℝ ℂ)).roots =
      (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
        (fun i ↦ if e i = 0 then w i (φ b, 0) else 0))
    (hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0)
    (hφ : AnalyticAt ℝ φ b₀) :
    ∃ k : ℕ, ∃ t : Fin k → B → ℝ, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      (∀ b ∈ U, F b ≠ 0) ∧
      (∀ i, AnalyticOnNhd ℝ (t i) U) ∧
      (∀ b ∈ U, StrictMono (fun i ↦ t i b)) ∧
      (∀ b ∈ U, ∀ z, (F b).IsRoot z ↔ ∃ i, t i b = z) ∧
      (∀ i, 0 < (F b₀).rootMultiplicity (t i b₀)) ∧
      ∀ b ∈ U, ∀ i,
        (F b).rootMultiplicity (t i b) = (F b₀).rootMultiplicity (t i b₀) := by
  classical
  let I := {i : Fin d // 0 ≤ e i}
  let f : I → E × ℂ → ℂ := fun i p ↦ p.2 ^ (e i.val).toNat * w i.val p
  have hf (i : I) : AnalyticAt ℂ (f i) (φ b₀, 0) :=
    (analyticAt_snd.fun_pow _).mul (hw i.val i.property)
  have hvalue (i : I) (x : E) :
      f i (x, 0) = if e i.val = 0 then w i.val (x, 0) else 0 := by
    by_cases he : e i.val = 0
    · simp [f, he]
    · have hpos : (e i.val).toNat ≠ 0 := by have := i.property; omega
      simp [f, he, zero_pow hpos]
  have hscaled : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i : I, (P p).coeff d * f i p = s i.val p := by
    filter_upwards [hscale, hLaurent] with p hp hl hp0 i
    rw [← hp hp0 i.val i.property, hl hp0 i.val i.property,
      ← Int.toNat_of_nonneg i.property, zpow_natCast]
  -- Finite extensions inherit collision persistence from the normalized splitting.
  have hcollision : ∀ᶠ b in 𝓝 b₀, ∀ i j : I,
      f i (φ b, 0) = f j (φ b, 0) ↔ f i (φ b₀, 0) = f j (φ b₀, 0) :=
    eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
      hφ.continuousAt.tendsto.eventually
        (eventually_finite_root_eq_iff_on_hyperplane
          (r := fun i p ↦ p.2 ^ (e i).toNat * w i p) hs hu hu0 hv hv0
          hnorm (by simpa only [sub_zero] using hlead)
          (by simpa only [sub_zero] using hdiscr) i.val j.val (hf i) (hf j)
          (hscaled.mono fun p hp hp0 ↦ ⟨hp hp0 i, hp hp0 j⟩))
  have hroot : ∀ᶠ b in 𝓝 b₀, ∀ z,
      ((F b).map (algebraMap ℝ ℂ)).IsRoot z ↔ ∃ i : I, f i (φ b, 0) = z := by
    filter_upwards [hroots, hF] with b hb hFb z
    rw [← mem_roots ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 hFb), hb]
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hiz⟩
      exact ⟨⟨i, hi⟩, (hvalue ⟨i, hi⟩ (φ b)).trans hiz⟩
    · rintro ⟨i, hiz⟩
      exact ⟨i.val, i.property, (hvalue i (φ b)).symm.trans hiz⟩
  have hcont (i : I) : ContinuousAt (fun b ↦ f i (φ b, 0)) b₀ :=
    (hf i).continuousAt.comp_of_eq (hφ.continuousAt.prodMk continuousAt_const) rfl
  -- Conjugate roots belong to the same persistent central collision class.
  have hlabels := eventually_root_im_eq_zero_iff_of_persistent_collisions hcont hroot
    (fun i j hji ↦ hcollision.mono fun b hb ↦ (hb j i).2 hji)
  let J := {i : I // (f i (φ b₀, 0)).im = 0}
  let g : J → B → ℝ := fun i b ↦ (f i.val (φ b, 0)).re
  have hg (i : J) : AnalyticAt ℝ (g i) b₀ :=
    Complex.reCLM.analyticAt _ |>.comp
      (((hf i.val).restrictScalars (𝕜 := ℝ)).comp_of_eq
        (hφ.prod (analyticAt_const (v := (0 : ℂ)))) rfl)
  have hgr : ∀ᶠ b in 𝓝 b₀, ∀ i : J, (g i b : ℂ) = f i.val (φ b, 0) := by
    filter_upwards [hlabels] with b hb i
    exact Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ((hb i.val).2 i.property))
  have hcover : ∀ᶠ b in 𝓝 b₀, ∀ z, (F b).IsRoot z ↔ ∃ i : J, g i b = z := by
    filter_upwards [hlabels, hroot, hgr] with b hb hrb hgb z
    rw [← isRoot_map_iff (algebraMap ℝ ℂ).injective, hrb]
    constructor
    · rintro ⟨i, hi⟩
      have him : (f i (φ b₀, 0)).im = 0 := (hb i).1 (by simp [hi])
      exact ⟨⟨i, him⟩, Complex.ofReal_injective ((hgb ⟨i, him⟩).trans hi)⟩
    · rintro ⟨i, hi⟩
      exact ⟨i.val, (hgb i).symm.trans (congrArg (fun z : ℝ ↦ (z : ℂ)) hi)⟩
  have heq (i j : J) (hij : g i b₀ = g j b₀) : g i =ᶠ[𝓝 b₀] g j := by
    have hc : f i.val (φ b₀, 0) = f j.val (φ b₀, 0) := by
      rw [← hgr.self_of_nhds i, ← hgr.self_of_nhds j, hij]
    filter_upwards [hgr, hcollision] with b hb hbc
    apply Complex.ofReal_injective
    rw [hb i, hb j]
    exact (hbc i.val j.val).2 hc
  obtain ⟨k, l, V, hV, hbV, ht, horder⟩ :=
    exists_analyticOnNhd_strictMono_range_eq hg heq
  -- The same collision classes count the multiplicities of the real family's complex roots.
  have hlimits : ∀ᶠ b in 𝓝 b₀, ∀ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ e i),
      ∀ j ∈ Finset.univ.filter (fun i ↦ 0 ≤ e i),
      (if e i = 0 then w i (φ b, 0) else 0) =
        (if e j = 0 then w j (φ b, 0) else 0) ↔
      (if e i = 0 then w i (φ b₀, 0) else 0) =
        (if e j = 0 then w j (φ b₀, 0) else 0) := by
    filter_upwards [hcollision] with b hb i hi j hj
    let i' : I := ⟨i, (Finset.mem_filter.mp hi).2⟩
    let j' : I := ⟨j, (Finset.mem_filter.mp hj).2⟩
    simpa only [hvalue i' (φ b), hvalue j' (φ b),
      hvalue i' (φ b₀), hvalue j' (φ b₀)] using hb i' j'
  have hmult := eventually_rootMultiplicity_eq_of_roots_eq_map
    hroots.self_of_nhds hroots hlimits
  have hm : ∀ᶠ b in 𝓝 b₀, ∀ i : J,
      (F b).rootMultiplicity (g i b) = (F b₀).rootMultiplicity (g i b₀) := by
    filter_upwards [hgr, hmult] with b hb hmb i
    rw [eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective,
      eq_rootMultiplicity_map (algebraMap ℝ ℂ).injective (g i b₀),
      Complex.coe_algebraMap,
      hb i, hgr.self_of_nhds i, hvalue i.val (φ b), hvalue i.val (φ b₀)]
    exact hmb i.val.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.val.property⟩)
  obtain ⟨U, hU, hopen, hbU⟩ := eventually_nhds_iff.1
    (Filter.Eventually.and (hV.mem_nhds hbV) (hF.and (hcover.and hm)))
  refine ⟨k, fun i ↦ g (l i), U, hopen, hbU,
    fun b hb ↦ (hU b hb).2.1,
    fun i ↦ (ht i).mono fun b hb ↦ (hU b hb).1,
    fun b hb ↦ (horder b (hU b hb).1).1, ?_, ?_,
    fun b hb i ↦ (hU b hb).2.2.2 (l i)⟩
  · intro b hb z
    rw [(hU b hb).2.2.1 z]
    exact (congrArg (z ∈ ·) (horder b (hU b hb).1).2).symm.to_iff
  · intro i
    apply (rootMultiplicity_pos hF.self_of_nhds).2
    exact hcover.self_of_nhds _ |>.2 ⟨l i, rfl⟩

end TauCeti
