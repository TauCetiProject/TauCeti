/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Flat.Basic
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Flat distance between pushforwards along nearby maps

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, with `E` finite-dimensional, and
let `T` be a normal current on `Ω` whose support is a compact subset of `Ω`. Maps `f` and `g`
smooth on `Ω` push `T` forward to `f_# T = T ∘ (χ f^*)` and `g_# T = T ∘ (χ g^*)`, for a test
function `χ` equal to one near the support of `T` (`TestFunction.cutoffPullbackCLM`). The
straight-line homotopy `H (x, t) = AffineMap.lineMap (f x) (g x) t = f x + t • (g x - f x)` and the
homotopy formula for currents with compact support give the decomposition

`g_# T - f_# T = H_# ([[0, 1]] × ∂ T) + ∂ H_# ([[0, 1]] × T)`

into normal currents supported in the union of the segments from `f x` to `g x` over the support
of `T`. If `‖g - f‖ ≤ A` and `‖Df‖, ‖Dg‖ ≤ L` on the support of `χ`, the mass estimate for homotopy
currents bounds both pieces, so that for a `(k + 1)`-current

`F(g_# T - f_# T) ≤ A (L ^ (k + 1) M(T) + L ^ k M(∂ T))`,

where `F` is the real normal flat mass `ContinuousLinearMap.normalFlatMass`; for a `0`-current the
bound is `A M(T)`. Consequently, if smooth maps `fᵢ` converge to `f` uniformly on the support of `χ`
with uniformly bounded derivatives there, then `fᵢ# T → f# T` in flat mass, and hence on every
test form.

The estimate uses no geometry of the target: test forms on `Ω'` are smooth on all of `E'`, so the
segments from `f x` to `g x` need not stay in `Ω'`. Here the target is a normed space; on a
Riemannian manifold the segments would have to be replaced by short geodesics.

## Main declarations

* `ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM`: the
  decomposition `g_# T - f_# T = R + ∂ S` into normal currents with compact supports near the
  segments from `f` to `g`, `M(R) ≤ A L ^ k M(∂ T)` and `M(S) ≤ A L ^ (k + 1) M(T)`, and
  `ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_finZero_eq_comp_extDerivCLM` in degree
  zero.
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

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens E} {Ω' : Opens E'}
  {k : ℕ} {χ : 𝓓(Ω, ℝ)} {f g : E → E'} {hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω}
  {hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω}

omit [FiniteDimensional ℝ E] in
/-- The straight-line homotopy `(x, t) ↦ AffineMap.lineMap (f x) (g x) t` from `f` to `g` is
smooth near `Ω × [0, 1]`. -/
private theorem contDiffAt_lineMap (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) :
    ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2) p :=
  fun p hp ↦ ContDiffAt.lineMap ((hf.contDiffAt (Ω.isOpen.mem_nhds hp.1)).comp p contDiffAt_fst)
    ((hg.contDiffAt (Ω.isOpen.mem_nhds hp.1)).comp p contDiffAt_fst) contDiffAt_snd

omit [FiniteDimensional ℝ E] in
/-- On `K × [0, 1]`, the time derivative of the straight-line homotopy is bounded by any bound for
`‖g - f‖` on `K`, and its spatial derivative by any common bound for `Df` and `Dg` on `K`. -/
private theorem norm_fderiv_lineMap_le (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {K : Set E} (hKΩ : K ⊆ Ω) {A L : ℝ≥0}
    (hA : ∀ x ∈ K, ‖g x - f x‖ ≤ A) (hfL : ∀ x ∈ K, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ L) :
    (∀ p ∈ K ×ˢ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2) p (0, 1)‖ ≤ A) ∧
      ∀ p ∈ K ×ˢ Icc (0 : ℝ) 1,
        ‖(fderiv ℝ (fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2) p).comp
          (.inl ℝ E ℝ)‖ ≤ L := by
  have hd {x : E} (hx : x ∈ K) :
      DifferentiableAt ℝ f x ∧ DifferentiableAt ℝ g x :=
    ⟨(hf.contDiffAt (Ω.isOpen.mem_nhds (hKΩ hx))).differentiableAt (by simp),
      (hg.contDiffAt (Ω.isOpen.mem_nhds (hKΩ hx))).differentiableAt (by simp)⟩
  refine ⟨fun ⟨x, t⟩ ⟨hx, _⟩ ↦ ?_, fun ⟨x, t⟩ ⟨hx, ht⟩ ↦ ?_⟩
  · rw [fderiv_lineMap_apply_zero_one (hd hx).1 (hd hx).2]
    exact hA x hx
  · exact norm_fderiv_lineMap_comp_inl_le (hd hx).1 (hd hx).2 ht (hfL x hx) (hgL x hx)

omit [FiniteDimensional ℝ E] in
/-- The derivative of a map smooth on `Ω` is bounded on the compact support of `χ`. -/
private theorem exists_norm_fderiv_le_of_contDiffOn (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    ∃ M : ℝ≥0, ∀ x ∈ tsupport χ, ‖fderiv ℝ f x‖ ≤ M :=
  χ.hasCompactSupport.isCompact.exists_norm_fderiv_le (by simp) fun x hx ↦
    hf.contDiffAt (Ω.isOpen.mem_nhds (χ.tsupport_subset hx))

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- A slice `x ↦ H (x, t)` of a homotopy that agrees with a map `Φ` has the same pullback with
cutoff. -/
private theorem cutoffPullbackCLM_slice_eq {m : ℕ} {H : E × ℝ → E'} {t : ℝ} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (h : ∀ x, H (x, t) = Φ x)
    {hH : ContDiffOn ℝ (⊤ : ℕ∞) (fun x ↦ H (x, t)) Ω} :
    (cutoffPullbackCLM χ (fun x ↦ H (x, t)) hH : 𝓓(Ω', E' [⋀^Fin m]→L[ℝ] F) →L[ℝ] _) =
      cutoffPullbackCLM χ Φ hΦ := by
  obtain rfl : (fun x ↦ H (x, t)) = Φ := funext h
  rfl

omit [FiniteDimensional ℝ E] in
/-- The support of a homotopy current `S ∘ K_ψ` of the straight-line homotopy is compact and lies in
the union of the segments from `f x` to `g x` over any set `U` containing the support of `S`. -/
private theorem isCompact_dsupport_comp_cutoffHomotopyPullbackCLM_lineMap {j : ℕ}
    (ψ : 𝓓(Ω, ℝ)) (S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] V) {U : Set E} (hSU : dsupport S ⊆ U) :
    IsCompact (dsupport (S ∘L (cutoffHomotopyPullbackCLM ψ (contDiffAt_lineMap hf hg) :
      𝓓(Ω', E' [⋀^Fin (j + 1)]→L[ℝ] F) →L[ℝ] _))) ∧
      dsupport (S ∘L (cutoffHomotopyPullbackCLM ψ (contDiffAt_lineMap hf hg) :
        𝓓(Ω', E' [⋀^Fin (j + 1)]→L[ℝ] F) →L[ℝ] _)) ⊆ ⋃ x ∈ U, segment ℝ (f x) (g x) := by
  have hsub := dsupport_comp_cutoffHomotopyPullbackCLM_subset (Ω' := Ω') (χ := ψ)
    (hH := contDiffAt_lineMap hf hg) S
  have hc : IsCompact ((fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2) ''
      ((tsupport ψ ∩ dsupport S) ×ˢ Icc (0 : ℝ) 1)) :=
    ((ψ.hasCompactSupport.isCompact.inter_right isClosed_dsupport).prod
      isCompact_Icc).image_of_continuousOn fun p hp ↦
        (contDiffAt_lineMap hf hg p
          ⟨ψ.tsupport_subset hp.1.1, hp.2⟩).continuousAt.continuousWithinAt
  refine ⟨hc.of_isClosed_subset isClosed_dsupport hsub, hsub.trans ?_⟩
  rintro _ ⟨⟨x, t⟩, ⟨⟨-, hx⟩, ht⟩, rfl⟩
  exact mem_biUnion (hSU hx) (segment_eq_image_lineMap ℝ (f x) (g x) ▸ mem_image_of_mem _ ht)

/-- **The homotopy decomposition of pushforwards along nearby maps**: let `T` be a normal
`(k + 1)`-current whose support lies in the interior of `{χ = 1}`. If `‖g - f‖ ≤ A` and
`‖Df‖, ‖Dg‖ ≤ L` on the support of `χ`, then `g_# T - f_# T = R + ∂ S` for normal currents `R` and
`S` with compact supports in the union of the segments from `f x` to `g x` over `x ∈ spt T`,
`M(R) ≤ A L ^ k M(∂ T)` and `M(S) ≤ A L ^ (k + 1) M(T)`. Here `f_# T = T ∘ (χ f^*)`. -/
theorem exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {A L : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) (hfL : ∀ x ∈ tsupport χ, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ tsupport χ, ‖fderiv ℝ g x‖ ≤ L) :
    ∃ (R : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω', E' [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] V),
      IsNormal R ∧ IsNormal S ∧ IsCompact (dsupport R) ∧ IsCompact (dsupport S) ∧
        dsupport R ⊆ ⋃ x ∈ dsupport T, segment ℝ (f x) (g x) ∧
        dsupport S ⊆ ⋃ x ∈ dsupport T, segment ℝ (f x) (g x) ∧
        T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) -
          T ∘L cutoffPullbackCLM χ f hf = R + S ∘L extDerivCLM ∧
        mass R ≤ A * L ^ k * mass (T ∘L extDerivCLM) ∧ mass S ≤ A * L ^ (k + 1) * mass T := by
  -- Replace `χ` by a cutoff `ψ` with `|ψ| ≤ 1`; this does not change the pushforwards.
  obtain ⟨ψ, hψ1, hψ, hψχ, hχψ⟩ := exists_cutoff_abs_le_one hχ
  obtain ⟨hA', hL'⟩ := norm_fderiv_lineMap_le hf hg ψ.tsupport_subset
    (fun x hx ↦ hA x (hψχ hx)) (fun x hx ↦ hfL x (hψχ hx)) fun x hx ↦ hgL x (hψχ hx)
  obtain ⟨hRc, hRs⟩ := isCompact_dsupport_comp_cutoffHomotopyPullbackCLM_lineMap (Ω' := Ω')
    (hf := hf) (hg := hg) ψ (T ∘L extDerivCLM) (dsupport_comp_extDerivCLM_subset T)
  obtain ⟨hSc, hSs⟩ := isCompact_dsupport_comp_cutoffHomotopyPullbackCLM_lineMap (Ω' := Ω')
    (hf := hf) (hg := hg) ψ T subset_rfl
  refine ⟨(T ∘L extDerivCLM) ∘L cutoffHomotopyPullbackCLM ψ (contDiffAt_lineMap hf hg),
    T ∘L cutoffHomotopyPullbackCLM ψ (contDiffAt_lineMap hf hg),
    hT.comp_extDerivCLM.comp_cutoffHomotopyPullbackCLM, hT.comp_cutoffHomotopyPullbackCLM, hRc,
    hSc, hRs, hSs, ?_, by rw [coe_comp]; exact mass_comp_cutoffHomotopyPullbackCLM_le _ hψ hA' hL',
    by rw [coe_comp]; exact mass_comp_cutoffHomotopyPullbackCLM_le _ hψ hA' hL'⟩
  -- The homotopy formula for the straight-line homotopy from `f` to `g`.
  rw [comp_cutoffPullbackCLM_congr T hχψ, comp_cutoffPullbackCLM_congr T hχψ,
    comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM T hψ1,
    cutoffPullbackCLM_slice_eq (H := fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2)
      (t := 1) (hΦ := hg) fun x ↦ AffineMap.lineMap_apply_one _ _,
    cutoffPullbackCLM_slice_eq (H := fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2)
      (t := 0) (hΦ := hf) fun x ↦ AffineMap.lineMap_apply_zero _ _]
  abel

/-- **The homotopy decomposition of pushforwards of `0`-currents along nearby maps**: let `T` be a
normal `0`-current whose support lies in the interior of `{χ = 1}`. If `‖g - f‖ ≤ A` on the support
of `χ`, then `g_# T - f_# T = ∂ S` for a normal current `S` with compact support in the union of
the segments from `f x` to `g x` over `x ∈ spt T` and `M(S) ≤ A M(T)`. Here
`f_# T = T ∘ (χ f^*)`. -/
theorem exists_comp_cutoffPullbackCLM_sub_finZero_eq_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {A : ℝ≥0}
    (hA : ∀ x ∈ tsupport χ, ‖g x - f x‖ ≤ A) :
    ∃ S : 𝓓(Ω', E' [⋀^Fin 1]→L[ℝ] F) →L[ℝ] V,
      IsNormal S ∧ IsCompact (dsupport S) ∧
        dsupport S ⊆ ⋃ x ∈ dsupport T, segment ℝ (f x) (g x) ∧
        T ∘L (cutoffPullbackCLM χ g hg : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) -
          T ∘L cutoffPullbackCLM χ f hf = S ∘L extDerivCLM ∧
        mass S ≤ A * mass T := by
  obtain ⟨ψ, hψ1, hψ, hψχ, hχψ⟩ := exists_cutoff_abs_le_one hχ
  -- Only the time derivative enters the mass bound in degree zero; the spatial one is bounded on
  -- the compact support of `ψ`.
  obtain ⟨Mf, hMf⟩ := exists_norm_fderiv_le_of_contDiffOn (χ := ψ) hf
  obtain ⟨Mg, hMg⟩ := exists_norm_fderiv_le_of_contDiffOn (χ := ψ) hg
  obtain ⟨hA', hL'⟩ := norm_fderiv_lineMap_le (L := max Mf Mg) hf hg ψ.tsupport_subset
    (fun x hx ↦ hA x (hψχ hx)) (fun x hx ↦ (hMf x hx).trans (mod_cast le_max_left _ _))
    fun x hx ↦ (hMg x hx).trans (mod_cast le_max_right _ _)
  obtain ⟨hSc, hSs⟩ := isCompact_dsupport_comp_cutoffHomotopyPullbackCLM_lineMap (Ω' := Ω')
    (hf := hf) (hg := hg) ψ T subset_rfl
  refine ⟨T ∘L cutoffHomotopyPullbackCLM ψ (contDiffAt_lineMap hf hg),
    hT.comp_cutoffHomotopyPullbackCLM, hSc, hSs, ?_, ?_⟩
  · rw [comp_cutoffPullbackCLM_congr T hχψ, comp_cutoffPullbackCLM_congr T hχψ,
      comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero T hψ1,
      cutoffPullbackCLM_slice_eq (H := fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2)
      (t := 1) (hΦ := hg) fun x ↦ AffineMap.lineMap_apply_one _ _,
      cutoffPullbackCLM_slice_eq (H := fun p : E × ℝ ↦ AffineMap.lineMap (f p.1) (g p.1) p.2)
      (t := 0) (hΦ := hf) fun x ↦ AffineMap.lineMap_apply_zero _ _]
  · have hS := mass_comp_cutoffHomotopyPullbackCLM_le (Ω' := Ω')
      (hH := contDiffAt_lineMap hf hg) T hψ hA' hL'
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
  obtain ⟨R, S, hR, hS, -, -, -, -, heq, hRm, hSm⟩ :=
    exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM (Ω' := Ω') (hf := hf) (hg := hg)
      T hT hχ hA hfL hgL
  calc _ ≤ mass R + mass S := normalFlatMass_le_of_eq_add_comp_extDerivCLM _ hR hS heq
    _ ≤ A * L ^ k * mass (T ∘L extDerivCLM) + A * L ^ (k + 1) * mass T := add_le_add hRm hSm
    _ = A * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by ring

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
  obtain ⟨S, hS, -, -, heq, hSm⟩ :=
    exists_comp_cutoffPullbackCLM_sub_finZero_eq_comp_extDerivCLM (Ω' := Ω') (hf := hf)
      (hg := hg) T hT hχ hA
  refine (normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hS
    (by rw [heq, zero_add])).trans ?_
  simpa using hSm

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
