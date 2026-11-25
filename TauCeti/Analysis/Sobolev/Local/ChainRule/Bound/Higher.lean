/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.ChainRule.Continuity
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Analysis.Sobolev.Local.Norm.LinearIsometryEquiv
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

## Proof

By induction on `k`, from the order-one bound `TauCeti.exists_eLpNormWkp_one_comp_le`. The weak
derivative of `g ∘ u` is `Dg(u) ∘ Du`. On an open set `V` between `U` and `Ω`, the induction
hypothesis for the `C^{k+1}` map `Dg` bounds `‖Dg ∘ u‖_{W^{k+1,p}(V)}` by
`C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}`, while `‖Du‖_{W^{k+1,p}(V)} ≤ ‖u‖_{W^{k+2,p}(Ω)}`. The local
product bound `TauCeti.exists_eLpNormWkp_succ_compL_le` for `(A, T) ↦ A ∘L T` bounds
`‖Dg(u) ∘ Du‖_{W^{k+1,p}(U)}` by the product of these norms on `V`, which raises the power by one.

## Main declarations

* `TauCeti.exists_eLpNormWkp_succ_comp_le`: the local bound for `g ∘ u` in `W^{k+1,p}`.

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
/-- The order-one case of `TauCeti.exists_eLpNormWkp_succ_comp_le`, in the form used by the
induction: `‖g ∘ u‖_{W^{1,p}(U)} ≤ C (1 + ‖u‖_{W^{1,p}(Ω)})`. It holds for every exponent. -/
private theorem exists_eLpNormWkp_one_comp_le_one_add {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] {g : F → G} {W L : Set F} (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U 1 (fun z => g (u z)) ≤ C * (1 + eLpNormWkp p Ω 1 u) := by
  obtain ⟨C₀, C₁, hC⟩ := exists_eLpNormWkp_one_comp_le hW hg hL hLW
  set A : ℝ≥0∞ := volume (closure U) ^ (p : ℝ≥0∞).toReal⁻¹
  have hA : A ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) hU.measure_lt_top.ne
  refine ⟨C₀ * A.toNNReal + C₁, fun u huc huL => ?_⟩
  set X := eLpNormWkp p Ω 1 u
  have hY : eLpNormWkp p (closure U) 1 u ≤ X := eLpNormWkp_mono_set hUΩ
  calc
    _ ≤ eLpNormWkp p (closure U) 1 (fun z => g (u z)) := eLpNormWkp_mono_set subset_closure
    _ ≤ C₀ * A + C₁ * eLpNormWkp p (closure U) 1 u :=
      hC p (closure U) u isClosed_closure.measurableSet (huc.mono hUΩ) (huL.mono_left hUΩ)
    _ ≤ C₀ * A * (1 + X) + C₁ * (1 + X) :=
      add_le_add (le_mul_of_one_le_right' le_self_add)
        (mul_le_mul' le_rfl (hY.trans le_add_self))
    _ = ↑(C₀ * A.toNNReal + C₁) * (1 + X) := by
      push_cast
      rw [ENNReal.coe_toNNReal hA]
      ring

/-- `TauCeti.exists_eLpNormWkp_succ_comp_le` for values in a universe at least that of `F`, which
makes the statement closed under the passage from `g` to `fderiv ℝ g`. -/
private theorem exists_eLpNormWkp_succ_comp_le_aux (hp : 2 < p) (k : ℕ) {G : Type (max uF uG)}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {g : F → G} {W L : Set F}
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p Ω (k + 1) u) ^ (k + 1) := by
  induction k generalizing G g U with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_comp_le_one_add (p := p) hW (by simpa using hg) hL
      hLW hU hUΩ
    exact ⟨C, fun u huc huL => by simpa using hC u huc huL⟩
  | succ k ih =>
    obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
    -- The bound for `g` itself controls the `Lᵖ` part, the bound for `Dg` on `V` and the product
    -- bound for `(A, T) ↦ A ∘L T` control the weak derivative `Dg(u) ∘ Du`.
    obtain ⟨C₀, hC₀⟩ := ih (hg.of_le (by norm_cast; omega)) hU hUΩ
    obtain ⟨C₁, hC₁⟩ := ih (G := F →L[ℝ] G) (g := fderiv ℝ g)
      (hg.fderiv_of_isOpen hW (by push_cast; rfl)) hVc hVΩ
    obtain ⟨Cc, hCc⟩ := exists_eLpNormWkp_succ_compL_le (F := ℂ) (G := F) (H := G) (Ω := V) hp
      (one_lt_two.trans hp) le_rfl k hU hUV
    refine ⟨C₀ + Cc * C₁ + 1, fun u huc huL => ?_⟩
    set X := eLpNormWkp p Ω (k + 1 + 1) u
    by_cases hX : X = ∞
    · rw [hX, add_top, ENNReal.top_pow (by omega), ENNReal.mul_top (by simp)]
      exact le_top
    obtain ⟨Du, hDu, -, hXeq⟩ := exists_hasWeakFDerivOn_eLpNormWkp_succ_eq_of_ne_top hX
    have hD := hDu.contDiffOn_comp huc hW (hg.of_le (by norm_cast; omega)) (huL.mono_right hLW)
    have hUΩ' : U ⊆ Ω := subset_closure.trans hUΩ
    have hu1 : eLpNormWkp p Ω (k + 1) u ≤ X := eLpNormWkp_mono_order (by omega)
    have hDuX : eLpNormWkp p V (k + 1) Du ≤ X := by
      refine (eLpNormWkp_mono_set (subset_closure.trans hVΩ)).trans ?_
      simp only [X, hXeq]
      exact le_add_self
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
        · exact eLpNorm_le_eLpNormWkp.trans ((hC₀ u huc huL).trans (by gcongr))
        · exact (hCc _ _).trans (by
            gcongr
            exact (hC₁ u huc huL).trans (by gcongr))
      _ = C₀ * (1 + X) ^ (k + 1) + Cc * C₁ * ((1 + X) ^ (k + 1) * X) := by ring
      _ ≤ C₀ * (1 + X) ^ (k + 1 + 1) + Cc * C₁ * (1 + X) ^ (k + 1 + 1) := by gcongr
      _ = ↑(C₀ + Cc * C₁) * (1 + X) ^ (k + 1 + 1) := by push_cast; ring
      _ ≤ _ := by gcongr ?_ * _; exact_mod_cast le_self_add

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Local bound for composition with a `C^{k+1}` map.** Let `p > 2`, let `g : F → G` be
`C^{k+1}` on an open set `W`, let `L ⊆ W` be compact and let `U` have compact closure contained in
`Ω`. There is a constant `C` such that
`‖g ∘ u‖_{W^{k+1,p}(U)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω)})^{k+1}` for every `u` continuous on `Ω`
with `u(Ω) ⊆ L`. This is the bound that accompanies `TauCeti.MemWkpLoc.contDiffOn_comp_succ`; at
`k = 0` it follows from `TauCeti.exists_eLpNormWkp_one_comp_le`. -/
theorem exists_eLpNormWkp_succ_comp_le (hp : 2 < p) (k : ℕ) {g : F → G} {W L : Set F}
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u Ω → MapsTo u Ω L →
      eLpNormWkp p U (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p Ω (k + 1) u) ^ (k + 1) := by
  -- Move the values to `ULift G`, which lies in a universe at least that of `F`.
  let e : G ≃ₗᵢ[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_comp_le_aux hp k (g := fun x => e (g x)) hW
    (e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hg) hL hLW hU hUΩ
  refine ⟨C, fun u huc huL => ?_⟩
  rw [← eLpNormWkp_linearIsometryEquiv_comp e]
  exact hC u huc huL

end TauCeti
