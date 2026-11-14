/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Flat.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Flat distance between pushforwards along nearby maps

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, with `E` finite-dimensional, and
let `T` be a normal current on `Ω` whose support is a compact subset of `Ω`. Maps `f` and `g`
smooth on `Ω` push `T` forward to `f_# T = T ∘ (χ f^*)` and `g_# T = T ∘ (χ g^*)`, for a test
function `χ` equal to one near the support of `T` (`TestFunction.cutoffPullbackCLM`). The
straight-line homotopy `H (x, t) = f x + t • (g x - f x)` and the homotopy formula for currents
with compact support give the decomposition

`g_# T - f_# T = H_# ([[0, 1]] × ∂ T) + ∂ H_# ([[0, 1]] × T)`

into normal currents (`Distribution.IsNormal.comp_cutoffHomotopyPullbackCLM`). If `‖g - f‖ ≤ A`
and `‖Df‖, ‖Dg‖ ≤ L` on the support of `χ`, the mass estimate for homotopy currents bounds both
pieces, so that for a `(k + 1)`-current

`F(g_# T - f_# T) ≤ A (L ^ (k + 1) M(T) + L ^ k M(∂ T))`,

where `F` is the real normal flat mass `ContinuousLinearMap.normalFlatMass`; for a `0`-current the
bound is `A M(T)`. Consequently, if smooth maps `fᵢ` converge to `f` uniformly on the support of `χ`
with uniformly bounded derivatives there, then `fᵢ# T → f# T` in flat mass, and hence on every
test form.

The estimate uses no geometry of the target: test forms on `Ω'` are smooth on all of `E'`, so the
segments from `f x` to `g x` need not stay in `Ω'`. Here the target is a normed space; on a
Riemannian manifold the segments would have to be replaced by short geodesics.

## Main declarations

* `ContinuousLinearMap.normalFlatMass_comp_cutoffPullbackCLM_sub_le`: the flat estimate
  `F(g_# T - f_# T) ≤ A (L ^ (k + 1) M(T) + L ^ k M(∂ T))`, and
  `ContinuousLinearMap.normalFlatMass_comp_cutoffPullbackCLM_sub_finZero_le` in degree zero.
* `ContinuousLinearMap.tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub`: flat convergence of the
  pushforwards along uniformly convergent maps with bounded derivatives.
* `ContinuousLinearMap.tendsto_comp_cutoffPullbackCLM_apply`: the corresponding convergence on each
  test form.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.9 (the homotopy formula and the affine homotopy)
  and §4.1.14 (the flat estimate for pushforwards along nearby maps).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction Distribution TauCeti
open scoped Distributions Topology NNReal ENNReal

namespace ContinuousLinearMap

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'} {k : ℕ}
  {χ : 𝓓(Ω, ℝ)} {f g : E → E'} {hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω}
  {hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω}

/-- The straight-line homotopy `(x, t) ↦ f x + t • (g x - f x)` from `f` to `g`, that is
`AffineMap.lineMap (f x) (g x) t`, written as a sum so that the sum and product rules compute its
derivative. -/
private def lineHomotopy (f g : E → E') (p : E × ℝ) : E' :=
  f p.1 + p.2 • (g p.1 - f p.1)

omit [FiniteDimensional ℝ E] in
private theorem contDiffAt_lineHomotopy (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) :
    ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) (lineHomotopy f g) p := fun p hp ↦ by
  have hf' := (hf.contDiffAt (Ω.isOpen.mem_nhds hp.1)).comp p contDiffAt_fst
  have hg' := (hg.contDiffAt (Ω.isOpen.mem_nhds hp.1)).comp p contDiffAt_fst
  exact hf'.add (contDiffAt_snd.smul (hg'.sub hf'))

omit [FiniteDimensional ℝ E] in
private theorem fderiv_lineHomotopy_apply {x : E} (hfx : DifferentiableAt ℝ f x)
    (hgx : DifferentiableAt ℝ g x) (t : ℝ) (v : E) (s : ℝ) :
    fderiv ℝ (lineHomotopy f g) (x, t) (v, s) =
      fderiv ℝ f x v + t • (fderiv ℝ g x v - fderiv ℝ f x v) + s • (g x - f x) := by
  have hfst : HasFDerivAt (Prod.fst : E × ℝ → E) (ContinuousLinearMap.fst ℝ E ℝ) (x, t) :=
    hasFDerivAt_fst
  have hf' := hfx.hasFDerivAt.comp (x, t) hfst
  have hg' := hgx.hasFDerivAt.comp (x, t) hfst
  have h : HasFDerivAt (lineHomotopy f g) _ (x, t) := hf'.add (hasFDerivAt_snd.smul (hg'.sub hf'))
  rw [h.fderiv]
  simp [add_assoc]

omit [FiniteDimensional ℝ E] in
/-- The time derivative of the straight-line homotopy is `g x - f x`, and its spatial derivative is
bounded by any common bound for `Df` and `Dg`. -/
private theorem norm_fderiv_lineHomotopy_le (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {K : Set E} (hKΩ : K ⊆ Ω) {A L : ℝ≥0}
    (hA : ∀ x ∈ K, ‖g x - f x‖ ≤ A) (hfL : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ L) :
    (∀ p ∈ K ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ (lineHomotopy f g) p (0, 1)‖ ≤ A) ∧
      ∀ p ∈ K ×ˢ Icc (0 : ℝ) 1, ‖(fderiv ℝ (lineHomotopy f g) p).comp (.inl ℝ E ℝ)‖ ≤ L := by
  have hd {x : E} (hx : x ∈ K) :
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x :=
    ⟨(hf.contDiffAt (Ω.isOpen.mem_nhds (hKΩ hx))).differentiableAt (by simp),
      (hg.contDiffAt (Ω.isOpen.mem_nhds (hKΩ hx))).differentiableAt (by simp)⟩
  refine ⟨fun ⟨x, t⟩ ⟨hx, _⟩ ↦ ?_, fun ⟨x, t⟩ ⟨hx, ht⟩ ↦ ?_⟩
  · rw [fderiv_lineHomotopy_apply (hd hx).1 (hd hx).2]
    simpa using hA x hx
  · -- The spatial derivative is a convex combination of `Df` and `Dg`.
    have h : (fderiv ℝ (lineHomotopy f g) (x, t)).comp (.inl ℝ E ℝ) =
        fderiv ℝ f x + t • (fderiv ℝ g x - fderiv ℝ f x) := by
      ext v
      simp [fderiv_lineHomotopy_apply (hd hx).1 (hd hx).2]
    rw [h, ← mem_closedBall_zero_iff]
    exact (convex_closedBall (0 : E →L[ℝ] E') L).add_smul_sub_mem
      (mem_closedBall_zero_iff.2 (hfL x hx)) (mem_closedBall_zero_iff.2 (hgL x hx)) ht

omit [FiniteDimensional ℝ E] in
/-- The derivative of a map smooth on `Ω` is bounded on the compact support of `χ`. -/
private theorem exists_norm_fderiv_le_of_contDiffOn (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    ∃ M : ℝ≥0, ∀ x ∈ tsupport χ, ‖fderiv ℝ f x‖ ≤ M :=
  χ.hasCompactSupport.isCompact.exists_norm_fderiv_le (by simp) fun x hx ↦
    hf.contDiffAt (Ω.isOpen.mem_nhds (χ.tsupport_subset hx))

omit [FiniteDimensional ℝ E] in
private theorem cutoffPullbackCLM_lineHomotopy_one {m : ℕ}
    {h : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy f g (x, 1)) Ω} :
    (cutoffPullbackCLM χ (fun x ↦ lineHomotopy f g (x, 1)) h :
        𝓓(Ω', E' [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] _) = cutoffPullbackCLM χ g hg := by
  have hfun : (fun x ↦ lineHomotopy f g (x, 1)) = g := funext fun x ↦ by simp [lineHomotopy]
  ext ω x : 2
  simp only [cutoffPullbackCLM_apply, hfun]

omit [FiniteDimensional ℝ E] in
private theorem cutoffPullbackCLM_lineHomotopy_zero {m : ℕ}
    {h : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ lineHomotopy f g (x, 0)) Ω} :
    (cutoffPullbackCLM χ (fun x ↦ lineHomotopy f g (x, 0)) h :
        𝓓(Ω', E' [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] _) = cutoffPullbackCLM χ f hf := by
  have hfun : (fun x ↦ lineHomotopy f g (x, 0)) = f := funext fun x ↦ by simp [lineHomotopy]
  ext ω x : 2
  simp only [cutoffPullbackCLM_apply, hfun]

/-- The flat estimate for a cutoff with values in `[-1, 1]`. -/
private theorem normalFlatMass_comp_cutoffPullbackCLM_sub_le_of_abs_le_one
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ1 : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ : ∀ x, |χ x| ≤ 1) {A L : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) (hfL : ∀ x ∈ tsupport χ, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ tsupport χ, ‖fderiv ℝ g x‖ ≤ L) :
    (T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf).normalFlatMass ≤
      A * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by
  have hH := contDiffAt_lineHomotopy hf hg
  obtain ⟨hA', hL'⟩ := norm_fderiv_lineHomotopy_le hf hg χ.tsupport_subset hA hfL hgL
  have hχ1' : ∀ᶠ x in 𝓝ˢ (dsupport (T ∘L extDerivCLM)), χ x = 1 :=
    hχ1.filter_mono (nhdsSet_mono (dsupport_comp_extDerivCLM_subset T))
  -- The straight-line homotopy decomposes `g_# T - f_# T` into a residual and a boundary.
  have heq : T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf =
      (T ∘L extDerivCLM) ∘L cutoffHomotopyPullbackCLM χ hH +
        (T ∘L cutoffHomotopyPullbackCLM χ hH) ∘L extDerivCLM := by
    rw [comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM T hχ1,
      cutoffPullbackCLM_lineHomotopy_one (hg := hg),
      cutoffPullbackCLM_lineHomotopy_zero (hf := hf)]
    abel
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM _
    (hT.comp_extDerivCLM.comp_cutoffHomotopyPullbackCLM hχ1')
    (hT.comp_cutoffHomotopyPullbackCLM hχ1) heq).trans ?_
  calc _ ≤ A * L ^ k * mass (T ∘L extDerivCLM) + A * L ^ (k + 1) * mass T :=
        add_le_add (mass_comp_cutoffHomotopyPullbackCLM_le _ hχ hA' hL')
          (mass_comp_cutoffHomotopyPullbackCLM_le _ hχ hA' hL')
    _ = A * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by ring

/-- The degree-zero flat estimate for a cutoff with values in `[-1, 1]`. -/
private theorem normalFlatMass_comp_cutoffPullbackCLM_sub_finZero_le_of_abs_le_one
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ1 : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ : ∀ x, |χ x| ≤ 1) {A : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) :
    (T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf).normalFlatMass ≤ A * mass T := by
  have hH := contDiffAt_lineHomotopy hf hg
  -- Only the time derivative enters the mass bound in degree zero; the spatial one is bounded on
  -- the compact support of `χ`.
  obtain ⟨Mf, hMf⟩ := exists_norm_fderiv_le_of_contDiffOn (χ := χ) hf
  obtain ⟨Mg, hMg⟩ := exists_norm_fderiv_le_of_contDiffOn (χ := χ) hg
  obtain ⟨hA', hL'⟩ := norm_fderiv_lineHomotopy_le (L := max Mf Mg) hf hg χ.tsupport_subset hA
    (fun x hx ↦ (hMf x hx).trans (mod_cast le_max_left _ _))
    fun x hx ↦ (hMg x hx).trans (mod_cast le_max_right _ _)
  have heq : T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf =
      0 + (T ∘L cutoffHomotopyPullbackCLM χ hH) ∘L extDerivCLM := by
    rw [comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero T hχ1,
      cutoffPullbackCLM_lineHomotopy_one (hg := hg),
      cutoffPullbackCLM_lineHomotopy_zero (hf := hf), zero_add]
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero
    (hT.comp_cutoffHomotopyPullbackCLM hχ1) heq).trans ?_
  have hS := mass_comp_cutoffHomotopyPullbackCLM_le (Ω' := Ω') (hH := hH) T hχ hA' hL'
  rw [← ContinuousLinearMap.coe_comp] at hS
  simpa using hS

/-- **The flat estimate for pushforwards along nearby maps**: let `T` be a normal
`(k + 1)`-current whose support lies in the interior of `{χ = 1}`. If `‖g - f‖ ≤ A` and
`‖Df‖, ‖Dg‖ ≤ L` on the support of `χ`, then
`F(g_# T - f_# T) ≤ A (L ^ (k + 1) M(T) + L ^ k M(∂ T))`, where `F` is the real normal flat mass
and `f_# T = T ∘ (χ f^*)`. -/
theorem normalFlatMass_comp_cutoffPullbackCLM_sub_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {A L : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) (hfL : ∀ x ∈ tsupport χ, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ tsupport χ, ‖fderiv ℝ g x‖ ≤ L) :
    (T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf).normalFlatMass ≤
      A * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by
  obtain ⟨ψ, hψ1, hψ, hψχ, hχψ⟩ := exists_cutoff_abs_le_one hχ
  rw [comp_cutoffPullbackCLM_congr T hχψ, comp_cutoffPullbackCLM_congr T hχψ]
  exact normalFlatMass_comp_cutoffPullbackCLM_sub_le_of_abs_le_one T hT hψ1 hψ
    (fun x hx ↦ hA x (hψχ hx)) (fun x hx ↦ hfL x (hψχ hx)) fun x hx ↦ hgL x (hψχ hx)

/-- **The flat estimate for pushforwards of `0`-currents along nearby maps**: let `T` be a normal
`0`-current whose support lies in the interior of `{χ = 1}`. If `‖g - f‖ ≤ A` on the support of
`χ`, then `F(g_# T - f_# T) ≤ A M(T)`, where `F` is the real normal flat mass and
`f_# T = T ∘ (χ f^*)`. -/
theorem normalFlatMass_comp_cutoffPullbackCLM_sub_finZero_le
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {A : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) :
    (T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] _) -
        T ∘L cutoffPullbackCLM χ f hf).normalFlatMass ≤ A * mass T := by
  obtain ⟨ψ, hψ1, hψ, hψχ, hχψ⟩ := exists_cutoff_abs_le_one hχ
  rw [comp_cutoffPullbackCLM_congr T hχψ, comp_cutoffPullbackCLM_congr T hχψ]
  exact normalFlatMass_comp_cutoffPullbackCLM_sub_finZero_le_of_abs_le_one T hT hψ1 hψ
    fun x hx ↦ hA x (hψχ hx)

/-- **Flat convergence of pushforwards along uniformly convergent maps**: let `T` be a normal
current whose support lies in the interior of `{χ = 1}`. If smooth maps `fᵢ` converge to `f`
uniformly on the support of `χ`, and eventually `‖Dfᵢ‖ ≤ L` there, then
`F(fᵢ# T - f_# T) → 0`, where `F` is the real normal flat mass and `f_# T = T ∘ (χ f^*)`. -/
theorem tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub {ι : Type*} {l : Filter ι}
    {fs : ι → E → E'} {hfs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fs i) Ω}
    (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {L : ℝ≥0}
    (hfsL : ∀ᶠ i in l, ∀ x ∈ tsupport χ, ‖fderiv ℝ (fs i) x‖ ≤ L)
    (hconv : TendstoUniformlyOn fs f l (tsupport χ)) :
    Tendsto (fun i ↦ (T ∘L (cutoffPullbackCLM χ (fs i) (hfs i) :
        𝓓(Ω', E' [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) - T ∘L cutoffPullbackCLM χ f hf).normalFlatMass)
      l (𝓝 0) := by
  -- Eventually, the flat distance is at most a fixed finite constant times the uniform distance
  -- of the maps.
  obtain ⟨C, hC, hbound⟩ : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ i in l, ∀ A : ℝ≥0,
      (∀ x ∈ tsupport χ, ‖fs i x - f x‖ ≤ A) →
        (T ∘L (cutoffPullbackCLM χ (fs i) (hfs i) : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] _) -
          T ∘L cutoffPullbackCLM χ f hf).normalFlatMass ≤ A * C := by
    cases k with
    | zero =>
      exact ⟨mass T, hT.mass_ne_top, .of_forall fun i A hA ↦
        normalFlatMass_comp_cutoffPullbackCLM_sub_finZero_le T hT hχ hA⟩
    | succ k =>
      obtain ⟨M, hM⟩ := exists_norm_fderiv_le_of_contDiffOn (χ := χ) hf
      have h1 := hT.mass_ne_top
      have h2 := (isNormal_succ_iff.1 hT).2
      refine ⟨max L M ^ (k + 1) * mass T + max L M ^ k * mass (T ∘L extDerivCLM), by finiteness,
        hfsL.mono fun i hi A hA ↦ normalFlatMass_comp_cutoffPullbackCLM_sub_le T hT hχ hA
          (fun x hx ↦ (hM x hx).trans (mod_cast le_max_right _ _))
          fun x hx ↦ (hi x hx).trans (mod_cast le_max_left _ _)⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hε.ne'
  filter_upwards [hbound, Metric.tendstoUniformlyOn_iff.1 hconv δ (NNReal.coe_pos.2 hδ)]
    with i hb hi
  refine (hb δ fun x hx ↦ ?_).trans hδε.le
  rw [← dist_eq_norm, dist_comm]
  exact (hi x hx).le

/-- **Weak convergence of pushforwards along uniformly convergent maps**: under the hypotheses of
`ContinuousLinearMap.tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub`, `fᵢ# T (ω) → f_# T (ω)` for
every test form `ω`. -/
theorem tendsto_comp_cutoffPullbackCLM_apply {ι : Type*} {l : Filter ι}
    {fs : ι → E → E'} {hfs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fs i) Ω}
    (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {L : ℝ≥0}
    (hfsL : ∀ᶠ i in l, ∀ x ∈ tsupport χ, ‖fderiv ℝ (fs i) x‖ ≤ L)
    (hconv : TendstoUniformlyOn fs f l (tsupport χ)) (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] ℝ)) :
    Tendsto (fun i ↦ T (cutoffPullbackCLM χ (fs i) (hfs i) ω)) l
      (𝓝 (T (cutoffPullbackCLM χ f hf ω))) :=
  tendsto_apply_of_normalFlatMass_sub_tendsto_zero _
    (tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub (hf := hf) T hT hχ hfsL hconv) ω

end ContinuousLinearMap
