/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule

/-!
# Local bounds for composition at every order

Let `p > 2`, let `Ω` be an open planar domain, and let `F` and `G` be finite-dimensional real
normed spaces. Let `g : F → G` be `C^{k+1}` on an open set `W` and let `L ⊆ W` be compact. On a
set `U` whose closure is compact and contained in `Ω` there is a constant `C`, depending on `g`,
`L`, `U`, `Ω`, `p` and `k`, such that

`‖g ∘ u‖_{W^{k+1,p}(U)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}`

for every `u` continuous on `Ω` with `u(Ω) ⊆ L` (`TauCeti.exists_eLpNormWkp_succ_comp_le`). This is
the local bound that accompanies the membership statement
`TauCeti.MemWkpLoc.contDiffOn_comp_succ`.

The constant depends on `g` only through a bound `B` for the norms of its derivatives of orders
`0` through `k + 1` on `u(Ω)` (`TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le`), so the bound
is uniform along a sequence of maps with uniformly bounded derivatives, as in the uniform
estimates for sequences of nonlinear elliptic equations with converging data.

## Proof

By induction on `k`, from the order-one bound `TauCeti.eLpNormWkp_one_comp_le`. The weak
derivative of `g ∘ u` is `Dg(u) ∘ Du`. On an open set `V` between `U` and `Ω`, the induction
hypothesis for the `C^{k+1}` map `Dg`, whose derivatives are those of `g` of one order higher,
bounds `‖Dg ∘ u‖_{W^{k+1,p}(V)}` by
`C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}`, while `‖Du‖_{W^{k+1,p}(V)} ≤ ‖u‖_{W^{k+2,p}(Ω)}`. The local
product bound `TauCeti.exists_eLpNormWkp_succ_compL_le` for `(A, T) ↦ A ∘L T` bounds
`‖Dg(u) ∘ Du‖_{W^{k+1,p}(U)}` by the product of these norms on `V`, which raises the power by one.

## Main declarations

* `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le`: the local bound for `g ∘ u` in
  `W^{k+1,p}`, uniform over maps `g` with derivatives bounded by `B` on `u(Ω)`.
* `TauCeti.exists_eLpNormWkp_succ_comp_le`: the local bound for a fixed `g` and `u(Ω)` in a fixed
  compact set.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe uF uG

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Ω : Opens ℂ} {p : ℝ≥0}

omit [FiniteDimensional ℝ F] in
/-- The order-one case of `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le`, in the form used
by the induction: `‖g ∘ u‖_{W^{1,p}(U)} ≤ C (1 + ‖u‖_{W^{1,p}(Ω)})` for every `g` with
`‖g‖ ≤ B` and `‖Dg‖ ≤ B` on `u(Ω)`, read as bounds for the derivatives of orders `0` and `1`. It
holds for every exponent. -/
private theorem exists_eLpNormWkp_one_comp_le_one_add {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (B : ℝ≥0) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (g : F → G) (W : Set F) (u : ℂ → F), IsOpen W → ContDiffOn ℝ 1 g W →
      ContinuousOn u Ω → MapsTo u Ω W → (∀ z ∈ Ω, ∀ i ≤ 1, ‖iteratedFDeriv ℝ i g (u z)‖ ≤ B) →
      eLpNormWkp p U 1 (fun z => g (u z)) ≤ C * (1 + eLpNormWkp p Ω 1 u) := by
  set A : ℝ≥0∞ := volume (closure U) ^ (p : ℝ≥0∞).toReal⁻¹
  have hA : A ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hU.measure_lt_top.ne
  refine ⟨B * A.toNNReal + (B + 1), fun g W u hW hg huc huW hB => ?_⟩
  set X := eLpNormWkp p Ω 1 u
  have hY : eLpNormWkp p (closure U) 1 u ≤ X := eLpNormWkp_mono_set hUΩ
  calc
    _ ≤ eLpNormWkp p (closure U) 1 (fun z => g (u z)) := eLpNormWkp_mono_set subset_closure
    _ ≤ B * A + ↑(B + 1) * eLpNormWkp p (closure U) 1 u :=
      eLpNormWkp_one_comp_le isClosed_closure.measurableSet (fun h => absurd h (by positivity))
        (huc.mono hUΩ) hW hg (huW.mono_left hUΩ) (fun z hz => ?_) fun z hz => ?_
    _ ≤ B * A * (1 + X) + ↑(B + 1) * (1 + X) :=
      add_le_add (le_mul_of_one_le_right' le_self_add)
        (mul_le_mul' le_rfl (hY.trans le_add_self))
    _ = ↑(B * A.toNNReal + (B + 1)) * (1 + X) := by
      push_cast
      rw [ENNReal.coe_toNNReal hA]
      ring
  · rw [← NNReal.coe_le_coe, coe_nnNorm, ← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact hB z (hUΩ hz) 0 zero_le_one
  · rw [← NNReal.coe_le_coe, coe_nnNorm, ← norm_iteratedFDeriv_one, NNReal.coe_add]
    exact (hB z (hUΩ hz) 1 le_rfl).trans (by simp)

/-- `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le` for values in a universe at least that of
`F`, which makes the statement closed under the passage from `g` to `fderiv ℝ g`. -/
private theorem exists_eLpNormWkp_succ_comp_le_of_norm_le_aux (hp : 2 < p) (k : ℕ) (B : ℝ≥0)
    {G : Type (max uF uG)} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (g : F → G) (W : Set F) (u : ℂ → F), IsOpen W → ContDiffOn ℝ (k + 1) g W →
      ContinuousOn u Ω → MapsTo u Ω W →
      (∀ z ∈ Ω, ∀ i ≤ k + 1, ‖iteratedFDeriv ℝ i g (u z)‖ ≤ B) →
      eLpNormWkp p U (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p Ω (k + 1) u) ^ (k + 1) := by
  induction k generalizing G U with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_comp_le_one_add (F := F) (G := G) (p := p) B hU hUΩ
    refine ⟨C, fun g W u hW hg huc huW hB => ?_⟩
    simpa using hC g W u hW (by simpa using hg) huc huW hB
  | succ k ih =>
    obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
    -- The bound for `g` itself controls the `Lᵖ` part, the bound for `Dg` on `V` and the product
    -- bound for `(A, T) ↦ A ∘L T` control the weak derivative `Dg(u) ∘ Du`.
    obtain ⟨C₀, hC₀⟩ := ih (G := G) hU hUΩ
    obtain ⟨C₁, hC₁⟩ := ih (G := F →L[ℝ] G) hVc hVΩ
    obtain ⟨Cc, hCc⟩ := exists_eLpNormWkp_succ_compL_le (F := ℂ) (G := F) (H := G) (Ω := V) hp
      (one_lt_two.trans hp) le_rfl k hU hUV
    refine ⟨C₀ + Cc * C₁ + 1, fun g W u hW hg huc huW hB => ?_⟩
    set X := eLpNormWkp p Ω (k + 1 + 1) u
    by_cases hX : X = ∞
    · rw [hX, add_top, ENNReal.top_pow (by omega), ENNReal.mul_top (by simp)]
      exact le_top
    obtain ⟨Du, hDu, -, hXeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hX
    have hD := hDu.contDiffOn_comp huc hW (hg.of_le (by norm_cast; omega)) huW
    have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
    have hu1 : eLpNormWkp p Ω (k + 1) u ≤ X := eLpNormWkp_mono_order (by omega)
    have hg0 := hC₀ g W u hW (hg.of_le (by norm_cast; omega)) huc huW
      fun z hz i hi => hB z hz i (by omega)
    have hg1 := hC₁ (fderiv ℝ g) W u hW (hg.fderiv_of_isOpen hW (by push_cast; rfl)) huc huW
      fun z hz i hi => by rw [norm_iteratedFDeriv_fderiv]; exact hB z hz (i + 1) (by omega)
    have hDuX : eLpNormWkp p V (k + 1) Du ≤ X :=
      (eLpNormWkp_mono_set (subset_closure.trans hVΩ)).trans (le_add_self.trans_eq hXeq.symm)
    have h1 : (1 + X) ^ (k + 1) ≤ (1 + X) ^ (k + 1 + 1) :=
      pow_le_pow_right₀ le_self_add (by omega)
    have h2 : (1 + X) ^ (k + 1) * X ≤ (1 + X) ^ (k + 1 + 1) := by
      rw [pow_succ _ (k + 1)]
      exact mul_le_mul' le_rfl (le_add_self : X ≤ 1 + X)
    calc
      _ ≤ eLpNorm (fun z => g (u z)) p (volume.restrict U) +
          eLpNormWkp p U (k + 1) (fun z => (fderiv ℝ g (u z)).comp (Du z)) :=
        eLpNormWkp_succ_le (hD.mono fun z hz => hUΩ' (interior_subset hz))
      _ ≤ C₀ * (1 + X) ^ (k + 1) + Cc * (C₁ * (1 + X) ^ (k + 1)) * X := by
        gcongr
        · exact eLpNorm_le_eLpNormWkp.trans (hg0.trans (by gcongr))
        · exact (hCc _ _).trans (by gcongr; exact hg1.trans (by gcongr))
      _ = C₀ * (1 + X) ^ (k + 1) + Cc * C₁ * ((1 + X) ^ (k + 1) * X) := by ring
      _ ≤ C₀ * (1 + X) ^ (k + 1 + 1) + Cc * C₁ * (1 + X) ^ (k + 1 + 1) := by gcongr
      _ = ↑(C₀ + Cc * C₁) * (1 + X) ^ (k + 1 + 1) := by push_cast; ring
      _ ≤ _ := by gcongr ?_ * _; exact_mod_cast le_self_add

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Local bound for composition, uniform in the map.** Let `p > 2`, let `U` have compact closure
contained in `Ω` and let `B ≥ 0`. There is a constant `C` such that
`‖g ∘ u‖_{W^{k+1,p}(U)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}` for every map `g : F → G` that is
`C^{k+1}` on an open set `W` and every `u` continuous on `Ω` with `u(Ω) ⊆ W`, provided the
derivatives of `g` of orders `0` through `k + 1` have norm at most `B` on `u(Ω)`. The constant
depends on `g` only through `B`, which makes the bound uniform along a sequence of maps with
uniformly bounded derivatives. -/
theorem exists_eLpNormWkp_succ_comp_le_of_norm_le (hp : 2 < p) (k : ℕ) (B : ℝ≥0) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (g : F → G) (W : Set F) (u : ℂ → F), IsOpen W → ContDiffOn ℝ (k + 1) g W →
      ContinuousOn u Ω → MapsTo u Ω W →
      (∀ z ∈ Ω, ∀ i ≤ k + 1, ‖iteratedFDeriv ℝ i g (u z)‖ ≤ B) →
      eLpNormWkp p U (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p Ω (k + 1) u) ^ (k + 1) := by
  -- Move the values to `ULift G`, which lies in a universe at least that of `F`.
  let e : G ≃ₗᵢ[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_comp_le_of_norm_le_aux.{uF, uG} (F := F)
    (G := ULift.{uF} G) hp k B hU hUΩ
  refine ⟨C, fun g W u hW hg huc huW hB => ?_⟩
  rw [← eLpNormWkp_linearIsometryEquiv_comp e]
  refine hC (fun x => e (g x)) W u hW (e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hg) huc
    huW fun z hz i hi => ?_
  rw [← Function.comp_def e g, e.norm_iteratedFDeriv_comp_left]
  exact hB z hz i hi

/-- **Local bound for composition with a `C^{k+1}` map.** Let `p > 2`, let `g : F → G` be
`C^{k+1}` on an open set `W`, let `L ⊆ W` be compact and let `U` have compact closure contained in
`Ω`. There is a constant `C` such that
`‖g ∘ u‖_{W^{k+1,p}(U)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}` for every `u` continuous on `Ω`
with `u(Ω) ⊆ L`. This is the bound that accompanies `TauCeti.MemWkpLoc.contDiffOn_comp_succ`; it
is `TauCeti.exists_eLpNormWkp_succ_comp_le_of_norm_le` with a bound for the derivatives of `g` on
`L`. -/
theorem exists_eLpNormWkp_succ_comp_le (hp : 2 < p) (k : ℕ) {g : F → G} {W L : Set F}
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p Ω (k + 1) u) ^ (k + 1) := by
  have hcont : ContinuousOn (fun x => ∑ i ∈ Finset.range (k + 2), ‖iteratedFDeriv ℝ i g x‖) W :=
    continuousOn_finsetSum _ fun i hi => ((hg.continuousOn_iteratedFDerivWithin
      (by norm_cast; simp only [Finset.mem_range] at hi; omega) hW.uniqueDiffOn).congr
        fun x hx => (iteratedFDerivWithin_of_isOpen i hW hx).symm).norm
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (hcont.mono hLW)
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_comp_le_of_norm_le (F := F) (G := G) hp k B.toNNReal hU
    hUΩ
  refine ⟨C, fun u huc huL => hC g W u hW hg huc (huL.mono_right hLW) fun z hz i hi => ?_⟩
  have hBz := hB _ (huL hz)
  rw [Real.norm_of_nonneg (by positivity)] at hBz
  exact (Finset.single_le_sum (fun j _ => norm_nonneg (iteratedFDeriv ℝ j g (u z)))
    (Finset.mem_range.2 (by omega))).trans (hBz.trans (Real.le_coe_toNNReal B))

end TauCeti
