/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.ChainRule.Bound.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Bound
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Local bounds for composition on half-discs at every order

Let `p > 2`, let `Ω` be an open planar domain and write `Ω⁺ = Ω ∩ {0 ≤ im}` for the relatively
open set of the closed upper half-plane. Let `F` and `G` be finite-dimensional real normed
spaces, let `g : F → G` be `C^{k+1}` on an open set `W` and let `L ⊆ W` be compact. For a set `U`
whose closure is compact and contained in `Ω`, write `U⁺ = U ∩ {0 ≤ im}`; `U` may meet the real
axis. There is a constant `C`, depending on `g`, `L`, `U`, `Ω`, `p` and `k`, such that

`‖g ∘ u‖_{W^{k+1,p}(U⁺)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω⁺)})^{k+1}`

for every `u` continuous on `Ω⁺` with `u(Ω⁺) ⊆ L`
(`TauCeti.exists_eLpNormWkp_succ_comp_le_halfPlane`). This is the local bound that accompanies the
membership statement `TauCeti.MemWkpLoc.contDiffOn_comp_succ_halfPlane`, and the half-disc form of
`TauCeti.exists_eLpNormWkp_succ_comp_le`.

## Proof

Composition does not commute with the higher reflections across the real axis, so instead of
reflecting, the induction on `k` behind `TauCeti.exists_eLpNormWkp_succ_comp_le` is run directly
on half-discs. The set `Ω⁺` agrees almost everywhere with its interior, the open upper half of
`Ω`, so its norms are realized by weak derivatives there
(`TauCeti.exists_hasWeakFDerivOn_interior_eLpNormWkp_succ_eq_of_ne_top`). The base case is
`TauCeti.exists_eLpNormWkp_one_comp_le_one_add` and the inductive step is
`TauCeti.eLpNormWkp_succ_succ_comp_le_of_le`, with the half-disc product bound
`TauCeti.exists_eLpNormWkp_succ_compL_le_halfPlane` in place of the interior one.

## Main declarations

* `TauCeti.exists_eLpNormWkp_succ_comp_le_halfPlane`: the local bound for `g ∘ u` in
  `W^{k+1,p}` on half-discs.

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

/-- `TauCeti.exists_eLpNormWkp_succ_comp_le_halfPlane` for values in a universe at least that of
`F`, which makes the statement closed under the passage from `g` to `fderiv ℝ g`. -/
private theorem exists_eLpNormWkp_succ_comp_le_halfPlane_aux (hp : 2 < p) (k : ℕ)
    {G : Type (max uF uG)} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {g : F → G} {W L : Set F} (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hL : IsCompact L)
    (hLW : L ⊆ W) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L →
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) ^ (k + 1) := by
  induction k generalizing G g U with
  | zero =>
    have hUc : IsCompact (closure (U ∩ {z | 0 ≤ z.im})) :=
      hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
    obtain ⟨C, hC⟩ := exists_eLpNormWkp_one_comp_le_one_add (p := p) hW (by simpa using hg) hL
      hLW hUc (closure_inter_setOf_im_nonneg_subset hUΩ)
    exact ⟨C, fun u huc huL => by simpa using hC u huc huL⟩
  | succ k ih =>
    obtain ⟨V, hUV, hVΩ, hVc⟩ := Opens.exists_between_and_isCompact_closure hU hUΩ
    -- The bound for `g` itself controls the `Lᵖ` part, the bound for `Dg` on `V ∩ {0 ≤ im}` and
    -- the half-disc product bound for `(A, T) ↦ A ∘L T` control the weak derivative `Dg(u) ∘ Du`.
    obtain ⟨C₀, hC₀⟩ := ih (hg.of_le (by norm_cast; omega)) hU hUΩ
    obtain ⟨C₁, hC₁⟩ := ih (G := F →L[ℝ] G) (g := fderiv ℝ g)
      (hg.fderiv_of_isOpen hW (by push_cast; rfl)) hVc hVΩ
    obtain ⟨Cc, hCc⟩ := exists_eLpNormWkp_succ_compL_le_halfPlane (F := ℂ) (G := F) (H := G)
      (Ω := V) hp (one_lt_two.trans hp) le_rfl k hU hUV
    exact ⟨_, fun u huc huL => eLpNormWkp_succ_succ_comp_le_of_le hW hg hLW
      (inter_setOf_im_nonneg_ae_eq_interior Ω)
      (inter_subset_inter_left _ (subset_closure.trans hUΩ))
      (inter_subset_inter_left _ (subset_closure.trans hVΩ)) huc huL
      (hC₀ u huc huL) (hC₁ u huc huL) hCc⟩

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Local bound for composition with a `C^{k+1}` map on half-discs.** Let `p > 2`, let
`g : F → G` be `C^{k+1}` on an open set `W`, let `L ⊆ W` be compact and let `U` have compact
closure contained in `Ω`. There is a constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and
`Ω⁺ = Ω ∩ {0 ≤ im}`, `‖g ∘ u‖_{W^{k+1,p}(U⁺)} ≤ C (1 + ‖u‖_{W^{k+1,p}(Ω⁺)})^{k+1}` for every `u`
continuous on `Ω⁺` with `u(Ω⁺) ⊆ L`. This is the bound that accompanies
`TauCeti.MemWkpLoc.contDiffOn_comp_succ_halfPlane`; the set `U` may meet the real axis. -/
theorem exists_eLpNormWkp_succ_comp_le_halfPlane (hp : 2 < p) (k : ℕ) {g : F → G} {W L : Set F}
    (hW : IsOpen W) (hg : ContDiffOn ℝ (k + 1) g W) (hL : IsCompact L) (hLW : L ⊆ W) {U : Set ℂ}
    (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ u : ℂ → F, ContinuousOn u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) →
      MapsTo u ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) L →
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => g (u z)) ≤
        C * (1 + eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) ^ (k + 1) := by
  -- Move the values to `ULift G`, which lies in a universe at least that of `F`.
  let e : G ≃ₗᵢ[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_comp_le_halfPlane_aux hp k (g := fun x => e (g x)) hW
    (e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hg) hL hLW hU hUΩ
  refine ⟨C, fun u huc huL => ?_⟩
  rw [← eLpNormWkp_linearIsometryEquiv_comp e]
  exact hC u huc huL

end TauCeti
