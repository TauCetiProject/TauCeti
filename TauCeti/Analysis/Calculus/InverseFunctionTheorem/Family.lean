/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
public import TauCeti.Analysis.Calculus.ContDiff.TaylorInverse
public import TauCeti.Analysis.Calculus.ContDiff.TendstoAt
public import TauCeti.Analysis.Calculus.FDeriv.Equiv
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The inverse function theorem for converging families

Let `Φ i → Φ₀` in `C^n` near `x₀`, with `1 ≤ n` and `D Φ₀ (x₀)` invertible. The inverse
function theorem applies to every `Φ i` with `i` close enough to the limit with *uniform*
constants: on a fixed ball `B` around `x₀` each `Φ i` approximates the linear map `D Φ₀ (x₀)`
with the same constant, so all these maps restrict to partial homeomorphisms with the common
source `B`, whose targets all contain a fixed neighbourhood `T` of `Φ₀ (x₀)`. On `T` the local
inverses converge to the inverse of `Φ₀` in `C^n`
(`TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`).

The order-zero convergence comes from the uniform antilipschitz bound of the approximation
(`TauCeti.tendsto_symm_of_approximatesLinearOn`).
Higher derivatives of the inverses are then recovered from the Faà di Bruno formula for
`(Φ i)⁻¹ ∘ Φ i = id`, whose singleton-partition term is the only one that involves the top
derivative of the inverse (`TauCeti.TendstoContDiffAt.symm`); this is the argument by which
inversion is continuous in `C^n` topologies.

## Main declarations

* `TauCeti.TendstoContDiffAt.symm`: if partial homeomorphisms converge in `C^n` and their
  inverses converge continuously, the inverses converge in `C^n`.
* `TauCeti.tendsto_symm_of_approximatesLinearOn`: partial homeomorphisms approximating one linear
  equivalence with one constant have continuously converging inverses when they converge
  continuously.
* `TauCeti.exists_openPartialHomeomorph_tendstoContDiffAt_symm`: the inverse function theorem
  with a common domain and `C^n` convergence of the local inverses.
-/

public section

open Set Filter Topology Metric
open scoped NNReal ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {n : ℕ}

/-- **`C^n` convergence of inverses.** Let `e i` be partial homeomorphisms converging in `C^n`
to `e₀` at `e₀⁻¹ (y₀)`, with `e i` and its inverse `C^n` near the relevant points. If the
inverses converge continuously at `y₀`, then they converge in `C^n` at `y₀`. -/
theorem TendstoContDiffAt.symm [CompleteSpace E] {e : ι → OpenPartialHomeomorph E F}
    {e₀ : OpenPartialHomeomorph E F} {y₀ : F} (hy₀ : y₀ ∈ e₀.target)
    (he : TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i)) e₀ l (e₀.symm y₀))
    (hsymm : Tendsto (fun p : ι × F ↦ (e p.1).symm p.2) (l ×ˢ 𝓝 y₀) (𝓝 (e₀.symm y₀)))
    (hd : ∀ᶠ p in l ×ˢ 𝓝 y₀, p.2 ∈ (e p.1).target ∧
      ContDiffAt 𝕜 n (e p.1) ((e p.1).symm p.2) ∧ ContDiffAt 𝕜 n (e p.1).symm p.2)
    (hd₀ : ContDiffAt 𝕜 n e₀ (e₀.symm y₀)) (hds₀ : ContDiffAt 𝕜 n e₀.symm y₀) :
    TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i).symm) e₀.symm l y₀ := by
  have hlim : Tendsto (fun p : ι × F ↦ (p.1, (e p.1).symm p.2)) (l ×ˢ 𝓝 y₀)
      (l ×ˢ 𝓝 (e₀.symm y₀)) :=
    tendsto_fst.prodMk hsymm
  -- The composite `(e i)⁻¹ ∘ e i` is the identity near the moving point `(e i)⁻¹ y`.
  have hcomp (k : ℕ) (hk : k ≤ n) : Tendsto (fun p : ι × F ↦
      (ftaylorSeries 𝕜 (e p.1).symm p.2).taylorComp
        (ftaylorSeries 𝕜 (e p.1) ((e p.1).symm p.2)) k) (l ×ˢ 𝓝 y₀)
      (𝓝 ((ftaylorSeries 𝕜 e₀.symm y₀).taylorComp (ftaylorSeries 𝕜 e₀ (e₀.symm y₀)) k)) := by
    have hk' : ((k : ℕ) : WithTop ℕ∞) ≤ n := by exact_mod_cast hk
    rw [e₀.taylorComp_ftaylorSeries_symm hy₀ (hd₀.of_le hk') (hds₀.of_le hk')]
    refine ((((contDiff_id (𝕜 := 𝕜) (E := E) (n := k)).continuous_iteratedFDeriv
      le_rfl).tendsto _).comp hsymm).congr' ?_
    filter_upwards [hd] with p hp
    exact ((e p.1).taylorComp_ftaylorSeries_symm hp.1 (hp.2.1.of_le hk') (hp.2.2.of_le hk')).symm
  -- The derivatives of the inverses are the inverses of the derivatives.
  have hA (hn : 1 ≤ n) : Tendsto (fun p : ι × F ↦ fderiv 𝕜 (e p.1).symm p.2) (l ×ˢ 𝓝 y₀)
      (𝓝 (fderiv 𝕜 e₀.symm y₀)) := by
    have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h₁ := e₀.fderiv_comp_fderiv_symm hy₀ (hd₀.differentiableAt hn')
      (hds₀.differentiableAt hn')
    have h₂ := e₀.fderiv_symm_comp_fderiv hy₀ (hd₀.differentiableAt hn')
      (hds₀.differentiableAt hn')
    have hcont : ContinuousAt ContinuousLinearMap.inverse (fderiv 𝕜 e₀ (e₀.symm y₀)) := by
      simpa using (contDiffAt_map_inverse (n := 0)
        (ContinuousLinearEquiv.equivOfInverse' _ _ h₁ h₂)).continuousAt
    rw [← ContinuousLinearMap.inverse_eq h₁ h₂]
    refine (hcont.tendsto.comp ((he.tendsto_fderiv hn).comp hlim)).congr' ?_
    filter_upwards [hd] with p hp
    exact ContinuousLinearMap.inverse_eq
      ((e p.1).fderiv_comp_fderiv_symm hp.1 (hp.2.1.differentiableAt hn')
        (hp.2.2.differentiableAt hn'))
      ((e p.1).fderiv_symm_comp_fderiv hp.1 (hp.2.1.differentiableAt hn')
        (hp.2.2.differentiableAt hn'))
  refine tendstoContDiffAt_iff.2 fun k hk ↦ ?_
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact (tendstoContDiffAt_zero_iff (f := fun i ↦ ⇑(e i).symm) (f₀ := e₀.symm).2
        hsymm).tendsto_iteratedFDeriv le_rfl
    have hn : 1 ≤ n := hk0.trans_le hk
    have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    -- Recover the `k`-th inverse coefficient from the lower ones and the identity composite.
    refine Filter.Tendsto.of_taylorComp (q := fun p : ι × F ↦ ftaylorSeries 𝕜 (e p.1).symm p.2)
      (p := fun p : ι × F ↦ ftaylorSeries 𝕜 (e p.1) ((e p.1).symm p.2))
      (q₀ := ftaylorSeries 𝕜 e₀.symm y₀) (p₀ := ftaylorSeries 𝕜 e₀ (e₀.symm y₀))
      (A := fun p : ι × F ↦ fderiv 𝕜 (e p.1).symm p.2) (A₀ := fderiv 𝕜 e₀.symm y₀) hk0
      (fun j _ hj ↦ ih j hj (hj.le.trans hk))
      (fun j _ hj ↦ (he.tendsto_iteratedFDeriv (hj.trans hk)).comp hlim)
      (hcomp k hk) (hA hn) ?_ ?_
    · filter_upwards [hd] with p hp
      simpa only [ftaylorSeries, continuousMultilinearCurryFin1_iteratedFDeriv_one] using
        (e p.1).fderiv_comp_fderiv_symm hp.1 (hp.2.1.differentiableAt hn')
          (hp.2.2.differentiableAt hn')
    · simpa only [ftaylorSeries, continuousMultilinearCurryFin1_iteratedFDeriv_one] using
        e₀.fderiv_comp_fderiv_symm hy₀ (hd₀.differentiableAt hn') (hds₀.differentiableAt hn')

/-- **Continuous convergence of inverses.** Let the partial homeomorphisms `e i` eventually
approximate one continuous linear equivalence `L`, with one constant `c` below `‖L⁻¹‖⁻¹`, on a set
`s` containing their sources, and let `e₀.source ⊆ s`. If the maps `e i` converge continuously to
`y₀ ∈ e₀.target` at `e₀⁻¹ (y₀)`, and the points near `y₀` eventually lie in the targets of the
`e i`, then the inverses `(e i)⁻¹` converge continuously to `e₀⁻¹` at `y₀`. -/
theorem tendsto_symm_of_approximatesLinearOn {e : ι → OpenPartialHomeomorph E F}
    {e₀ : OpenPartialHomeomorph E F} {L : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0} {y₀ : F}
    (hc : Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹)
    (he : ∀ᶠ i in l, ApproximatesLinearOn (e i) (L : E →L[𝕜] F) s c ∧ (e i).source ⊆ s)
    (he₀ : e₀.source ⊆ s) (hy₀ : y₀ ∈ e₀.target)
    (ht : ∀ᶠ p in l ×ˢ 𝓝 y₀, p.2 ∈ (e p.1).target)
    (hconv : Tendsto (fun p : ι × E ↦ e p.1 p.2) (l ×ˢ 𝓝 (e₀.symm y₀)) (𝓝 y₀)) :
    Tendsto (fun p : ι × F ↦ (e p.1).symm p.2) (l ×ˢ 𝓝 y₀) (𝓝 (e₀.symm y₀)) := by
  set K : ℝ≥0 := (‖(L.symm : F →L[𝕜] E)‖₊⁻¹ - c)⁻¹
  have hb : Tendsto (fun p : ι × F ↦ e₀.symm p.2) (l ×ˢ 𝓝 y₀) (𝓝 (e₀.symm y₀)) :=
    (e₀.continuousAt_symm hy₀).tendsto.comp tendsto_snd
  have h₁ : Tendsto (fun p : ι × F ↦ e p.1 (e₀.symm p.2)) (l ×ˢ 𝓝 y₀) (𝓝 y₀) :=
    hconv.comp (tendsto_fst.prodMk hb)
  have hd : Tendsto (fun p : ι × F ↦
      K * dist p.2 (e p.1 (e₀.symm p.2)) + dist (e₀.symm p.2) (e₀.symm y₀)) (l ×ˢ 𝓝 y₀)
      (𝓝 0) := by
    simpa using (((tendsto_snd (f := l) (g := 𝓝 y₀)).dist h₁).const_mul (K : ℝ)).add
      (hb.dist (tendsto_const_nhds (x := e₀.symm y₀)))
  refine tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ ↦
    dist_nonneg) ?_ hd)
  -- The uniform antilipschitz bound compares `(e i)⁻¹ y` with `e₀⁻¹ y`.
  filter_upwards [tendsto_fst.eventually he, ht,
    tendsto_snd.eventually (e₀.open_target.mem_nhds hy₀)] with p hp hpt hp₀
  have hanti := (hp.1.antilipschitzWith hc).le_mul_dist ⟨_, hp.2 ((e p.1).map_target hpt)⟩
    ⟨_, he₀ (e₀.map_target hp₀)⟩
  simp only [Subtype.dist_eq, Set.domRestrict_apply, (e p.1).right_inv hpt] at hanti
  calc dist ((e p.1).symm p.2) (e₀.symm y₀)
      ≤ dist ((e p.1).symm p.2) (e₀.symm p.2) + dist (e₀.symm p.2) (e₀.symm y₀) :=
        dist_triangle _ _ _
    _ ≤ _ := by gcongr

section Existence

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} {l : Filter ι} {n : ℕ}

omit [CompleteSpace E] in
/-- If `Φ i → Φ₀` in `C^n` at `x₀ ∈ s`, with `1 ≤ n`, the maps `C^n` on the open set `s`, and
`D Φ₀ (x₀) = L` invertible, then there are one constant `c` below `‖L⁻¹‖⁻¹` and one ball around
`x₀` inside `s` on which `Φ₀` and, eventually along `l`, every `Φ i` approximate `L` with
constant `c`. -/
private theorem exists_ball_approximatesLinearOn {Φ : ι → E → F} {Φ₀ : E → F} {s : Set E}
    {x₀ : E} (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hn : 1 ≤ n)
    (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 n (Φ i) s) (hΦ₀ : ContDiffOn 𝕜 n Φ₀ s)
    (hconv : TendstoContDiffAt 𝕜 n Φ Φ₀ l x₀) {L : E ≃L[𝕜] F}
    (hL : (L : E →L[𝕜] F) = fderiv 𝕜 Φ₀ x₀) :
    ∃ c : ℝ≥0, (Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) ∧ ∃ r > 0, ball x₀ r ⊆ s ∧
      ApproximatesLinearOn Φ₀ (L : E →L[𝕜] F) (ball x₀ r) c ∧
      ∀ᶠ i in l, ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c := by
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set c : ℝ≥0 := ‖(L.symm : F →L[𝕜] E)‖₊⁻¹ / 2
  -- The constant `c` is admissible, and every map near `L` is within `c` of it.
  obtain ⟨hc, hnear⟩ : (Subsingleton E ∨ c < ‖(L.symm : F →L[𝕜] E)‖₊⁻¹) ∧
      ∀ᶠ q in 𝓝 (L : E →L[𝕜] F), ‖q - (L : E →L[𝕜] F)‖₊ ≤ c := by
    rcases L.subsingleton_or_nnNorm_symm_pos with hE | hpos
    · refine ⟨Or.inl hE, Eventually.of_forall fun q ↦ ?_⟩
      have : q - L = 0 := ContinuousLinearMap.ext fun v ↦ by simp [Subsingleton.elim v 0]
      simp [this]
    · refine ⟨Or.inr (NNReal.half_lt_self (inv_ne_zero hpos.ne')), ?_⟩
      filter_upwards [closedBall_mem_nhds (L : E →L[𝕜] F)
        (show (0 : ℝ) < c by positivity)] with q hq
      rw [← NNReal.coe_le_coe, coe_nnNorm, ← dist_eq_norm]
      exact hq
  -- The derivatives of the family and of the limit stay within `c` of `L` near `x₀`.
  have hev : ∀ᶠ p in l ×ˢ 𝓝 x₀, ‖fderiv 𝕜 (Φ p.1) p.2 - (L : E →L[𝕜] F)‖₊ ≤ c := by
    have h := hconv.tendsto_fderiv hn
    rw [← hL] at h
    exact h.eventually hnear
  have hev₀ : ∀ᶠ x in 𝓝 x₀, ‖fderiv 𝕜 Φ₀ x - (L : E →L[𝕜] F)‖₊ ≤ c := by
    have h := ((hΦ₀.contDiffAt (hs.mem_nhds hx₀)).continuousAt_fderiv hn').tendsto
    rw [← hL] at h
    exact h.eventually hnear
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := eventually_prod_iff.mp hev
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hpb.and hev₀).and (hs.mem_nhds hx₀))
  have hrs : ball x₀ r ⊆ s := fun x hx ↦ (hrb x hx).2
  -- By the mean value inequality, a map `C^n` on `s` with derivative near `L` approximates `L`.
  have happrox (g : E → F) (hg : ContDiffOn 𝕜 n g s)
      (hgb : ∀ x ∈ ball x₀ r, ‖fderiv 𝕜 g x - (L : E →L[𝕜] F)‖₊ ≤ c) :
      ApproximatesLinearOn g (L : E →L[𝕜] F) (ball x₀ r) c := by
    let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    exact (convex_ball x₀ r).approximatesLinearOn_of_nnnorm_fderiv_sub_le
      (fun x hx ↦ (hg.contDiffAt (hs.mem_nhds (hrs hx))).differentiableAt hn') hgb
  refine ⟨c, hc, r, hr, hrs, happrox Φ₀ hΦ₀ fun x hx ↦ (hrb x hx).1.2, ?_⟩
  filter_upwards [hΦ, hpa] with i h1 h2
  exact happrox (Φ i) h1 fun x hx ↦ hpab h2 (hrb x hx).1.1

/-- **The inverse function theorem for a converging family.** Let `Φ i → Φ₀` in `C^n` at every
point of an open set `s`, with `1 ≤ n`, the maps `Φ i` eventually `C^n` on `s`, and `D Φ₀`
invertible at `x₀ ∈ s`. Then `Φ₀` and, eventually along `l`, all the `Φ i` restrict to partial
homeomorphisms with one common source inside `s`, whose targets contain a common open
neighbourhood `T` of `Φ₀ (x₀)` and whose inverses are `C^n` on their targets. On `T` the inverses
converge to the inverse of `Φ₀` in `C^n`. -/
theorem exists_openPartialHomeomorph_tendstoContDiffAt_symm {Φ : ι → E → F} {Φ₀ : E → F}
    {s : Set E} {x₀ : E} (hs : IsOpen s) (hx₀ : x₀ ∈ s) (hn : 1 ≤ n)
    (hΦ : ∀ᶠ i in l, ContDiffOn 𝕜 n (Φ i) s) (hΦ₀ : ContDiffOn 𝕜 n Φ₀ s)
    (hconv : ∀ x ∈ s, TendstoContDiffAt 𝕜 n Φ Φ₀ l x)
    (hinv : (fderiv 𝕜 Φ₀ x₀).IsInvertible) :
    ∃ (e₀ : OpenPartialHomeomorph E F) (e : ι → OpenPartialHomeomorph E F) (T : Set F),
      IsOpen T ∧ Φ₀ x₀ ∈ T ∧ ⇑e₀ = Φ₀ ∧ x₀ ∈ e₀.source ∧ e₀.source ⊆ s ∧ T ⊆ e₀.target ∧
      ContDiffOn 𝕜 n e₀.symm e₀.target ∧
      (∀ᶠ i in l, ⇑(e i) = Φ i ∧ (e i).source = e₀.source ∧ T ⊆ (e i).target ∧
        ContDiffOn 𝕜 n (e i).symm (e i).target) ∧
      ∀ y ∈ T, TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i).symm) e₀.symm l y := by
  classical
  obtain ⟨L, hL⟩ := hinv
  obtain ⟨c, hc, r, hr, hrs, h₀a, hΦa⟩ :=
    exists_ball_approximatesLinearOn hs hx₀ hn hΦ hΦ₀ (hconv x₀ hx₀) hL
  set e₀ := h₀a.toOpenPartialHomeomorph Φ₀ (ball x₀ r) hc isOpen_ball with he₀_def
  have h₀c : ContDiffOn 𝕜 n e₀.symm e₀.target :=
    h₀a.contDiffOn_toOpenPartialHomeomorph_symm hc isOpen_ball (hΦ₀.mono hrs)
  have he₀c : ⇑e₀ = Φ₀ := by rw [he₀_def, ApproximatesLinearOn.toOpenPartialHomeomorph_coe]
  have he₀s : e₀.source = ball x₀ r := by
    rw [he₀_def, ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  have hrs₀ : e₀.source ⊆ s := he₀s ▸ hrs
  let e : ι → OpenPartialHomeomorph E F := fun i ↦
    if h : ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c then
      h.toOpenPartialHomeomorph (Φ i) (ball x₀ r) hc isOpen_ball else e₀
  -- A common radius `ρ` of target balls around `Φ₀ x₀`.
  obtain ⟨ρ, hρ, hρT⟩ := exists_ball_subset_toOpenPartialHomeomorph_target hr hc (Φ₀ x₀)
  have hΦx₀ : Tendsto (fun i ↦ Φ i x₀) l (𝓝 (Φ₀ x₀)) :=
    (hconv x₀ hx₀).tendsto.comp (tendsto_id.prodMk tendsto_const_nhds)
  have hgood : ∀ᶠ i in l, ContDiffOn 𝕜 n (Φ i) s ∧
      ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c ∧ dist (Φ i x₀) (Φ₀ x₀) < ρ := by
    filter_upwards [hΦ, hΦa, hΦx₀.eventually (ball_mem_nhds _ hρ)] with i h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Properties of the good members of the family.
  have hgood' : ∀ i, ContDiffOn 𝕜 n (Φ i) s ∧
      ApproximatesLinearOn (Φ i) (L : E →L[𝕜] F) (ball x₀ r) c ∧ dist (Φ i x₀) (Φ₀ x₀) < ρ →
      ApproximatesLinearOn (e i) (L : E →L[𝕜] F) (ball x₀ r) c ∧ ⇑(e i) = Φ i ∧
        (e i).source = ball x₀ r ∧ ContDiffOn 𝕜 n (e i).symm (e i).target ∧
        ball (Φ₀ x₀) ρ ⊆ (e i).target := by
    rintro i ⟨h1, hia, h3⟩
    have hei : e i = hia.toOpenPartialHomeomorph (Φ i) (ball x₀ r) hc isOpen_ball := by
      simp [e, hia]
    have hec : ⇑(e i) = Φ i := by rw [hei, ApproximatesLinearOn.toOpenPartialHomeomorph_coe]
    refine ⟨hec ▸ hia, hec, ?_,
      hei ▸ hia.contDiffOn_toOpenPartialHomeomorph_symm hc isOpen_ball (h1.mono hrs),
      hei ▸ hρT (Φ i) hia h3⟩
    rw [hei, ApproximatesLinearOn.toOpenPartialHomeomorph_source]
  have hT₀ : ball (Φ₀ x₀) ρ ⊆ e₀.target := hρT Φ₀ h₀a (by simpa using hρ)
  refine ⟨e₀, e, ball (Φ₀ x₀) ρ, isOpen_ball, mem_ball_self hρ, he₀c, he₀s ▸ mem_ball_self hr,
    hrs₀, hT₀, h₀c, ?_, fun y hy ↦ ?_⟩
  · filter_upwards [hgood] with i hi
    obtain ⟨-, hec, hes, hic, hiT⟩ := hgood' i hi
    exact ⟨hec, hes.trans he₀s.symm, hiT, hic⟩
  have hyt := hT₀ hy
  have hconv' : TendstoContDiffAt 𝕜 n (fun i ↦ ⇑(e i)) e₀ l (e₀.symm y) := by
    rw [he₀c]
    refine (hconv _ (hrs₀ (e₀.map_target hyt))).congr ?_
    filter_upwards [hgood] with i hi
    exact (hgood' i hi).2.1.symm
  -- Order zero: the inverses converge continuously, by the uniform antilipschitz bound.
  have hsymm : Tendsto (fun p : ι × F ↦ (e p.1).symm p.2) (l ×ˢ 𝓝 y) (𝓝 (e₀.symm y)) := by
    refine tendsto_symm_of_approximatesLinearOn hc ?_ he₀s.subset hyt ?_ ?_
    · filter_upwards [hgood] with i hi
      obtain ⟨hia, -, hes, -⟩ := hgood' i hi
      exact ⟨hia, hes.subset⟩
    · filter_upwards [tendsto_fst.eventually hgood,
        tendsto_snd.eventually (isOpen_ball.mem_nhds hy)] with p hp hpT
      exact (hgood' p.1 hp).2.2.2.2 hpT
    · simpa only [e₀.right_inv hyt] using hconv'.tendsto
  refine hconv'.symm hyt hsymm ?_ ?_ ?_
  · filter_upwards [tendsto_fst.eventually hgood,
      tendsto_snd.eventually (isOpen_ball.mem_nhds hy)] with p hp hpT
    obtain ⟨-, hec, hes, hic, hiT⟩ := hgood' p.1 hp
    have hpt := hiT hpT
    refine ⟨hpt, ?_, hic.contDiffAt ((e p.1).open_target.mem_nhds hpt)⟩
    rw [hec]
    exact hp.1.contDiffAt (hs.mem_nhds (hrs (hes ▸ (e p.1).map_target hpt)))
  · rw [he₀c]
    exact hΦ₀.contDiffAt (hs.mem_nhds (hrs₀ (e₀.map_target hyt)))
  · exact h₀c.contDiffAt (e₀.open_target.mem_nhds hyt)

end Existence

end TauCeti
