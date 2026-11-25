/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.Multiplication
import TauCeti.Analysis.Sobolev.Local.Multiplication.Supercritical
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.ChainRule
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Composition of local Sobolev maps for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open, let `1 < p` and `k p > 2`, and let `F` and `G` be finite-dimensional. If
`u ∈ W^{k,p}_loc(Ω, F)` is continuous on `Ω` and `g : F → G` is `Cᵏ` on an open set `W`
containing `u '' Ω`, then `g ∘ u ∈ W^{k,p}_loc(Ω, G)`. The range `p > 2` is
`TauCeti.MemWkpLoc.contDiffOn_comp_succ`, which is derived from this theorem; the new range is
`p ≤ 2`, for instance `k = 2` and `p = 4/3`. By Morrey's embedding for `kp > 2`
(`TauCeti.MemWkpLoc.exists_continuousOn_ae_eq_of_two_lt_mul`) every member of `W^{k,p}_loc` has a
continuous representative. For globally `Cᵏ` maps `g`
(`TauCeti.MemWkpLoc.contDiff_comp_of_two_lt_mul`) continuity is therefore no restriction; in
general the continuous representative must also map `Ω` into `W`.

Without continuity, `kp > 2` cannot be dropped at `k = 1`: for `p = 4/3` the function
`u = |z|^{-2/5}` is in `W^{1,4/3}` near `0` while `u²` is not. For continuous `u` at `k = 1`,
`TauCeti.MemWkpLoc.contDiffOn_comp` covers every `p`.

## Proof

The weak derivative of `g ∘ u` is `Dg(u) ∘ Du`. For `p ≤ 2` the factor `Du` lies only in
`W^{k-1,p}_loc` with `(k - 1) p` possibly at most `2`, so the products of
`TauCeti.Analysis.Sobolev.Local.Multiplication.Supercritical` do not apply to `Dg(u) ∘ Du`
directly: they do not see that `Dg(u)` is bounded. Instead the proof establishes, by induction on
`m ≤ k`, the more general statement that `B(g ∘ u, v) ∈ W^{m,p}_loc` for every continuous
bilinear map `B`, every `g` that is `Cᵐ` on `W` and every `v ∈ W^{b,p}_loc` with `m ≤ b` and
`(b + k - m) p > 2`. The weak Leibniz rule gives

`D B(g ∘ u, v) = B(Dg(u) ∘ Du, v) + B(g ∘ u, Dv)`.

The second term is the statement at order `m - 1` for `Dv ∈ W^{b-1,p}_loc`. The first is
`Φ(Du, v)` evaluated at `Dg(u)`, for a fixed continuous bilinear map `Φ`; the product
`Φ(Du, v)` lies in `W^{m-1,p}_loc` by `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul`, since
`(k - 1 + b - (m - 1)) p > 2`, and the statement at order `m - 1` for the `C^{m-1}` map `Dg`
applies to it. The Leibniz rule itself uses that `g ∘ u` is continuous and lies in
`W^{1,r}_loc` for some `r > 2` (`TauCeti.MemWkpLoc.exists_two_lt_memWkpLoc_one_of_two_lt_mul`).
The case `B(x, c) = c x` and `v = 1` gives the theorem.

## Main declarations

* `TauCeti.MemWkpLoc.contDiffOn_comp_of_two_lt_mul`: composition with maps that are `Cᵏ` on an
  open neighbourhood of the image, for `kp > 2`.
* `TauCeti.MemWkpLoc.contDiff_comp_of_two_lt_mul`: composition with globally `Cᵏ` maps.
* `TauCeti.MemWkpLoc.contDiffOn_comp_graph_of_two_lt_mul`: the domain-dependent composition
  `z ↦ g(z, u z)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (composition in local Sobolev spaces).
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, second edition, Theorem 4.39.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

universe uF uG uH

variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Ω : Opens ℂ}

omit [FiniteDimensional ℝ F] in
/-- The continuous bilinear map `(D, v) ↦ (A ↦ B(A ∘ D, v))`, which writes `B(A ∘ D, v)` as a
product of `A` with `Φ(D, v)`. It is stated as an existence statement so that `Φ` stays opaque in
the proof below, where unfolding it makes unification of its iterated operator spaces slow. -/
private theorem exists_bilin_comp_precompL {G V H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup H]
    [NormedSpace ℝ H] (B : G →L[ℝ] V →L[ℝ] H) :
    ∃ Φ : (ℂ →L[ℝ] F) →L[ℝ] V →L[ℝ] (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H,
      ∀ D v A, Φ D v A = B.precompL ℂ (A.comp D) v :=
  ⟨(((ContinuousLinearMap.compL ℝ (F →L[ℝ] G) (ℂ →L[ℝ] G) (ℂ →L[ℝ] H)).comp
    (B.precompL ℂ).flip).flip).comp (ContinuousLinearMap.compL ℝ ℂ F G).flip,
    fun _ _ _ => rfl⟩

/-- The general statement behind `TauCeti.MemWkpLoc.contDiffOn_comp_of_two_lt_mul`: for
`u ∈ W^{k,p}_loc` continuous with `1 < p` and `kp > 2`, a map `g` that is `Cᵐ` on `W ⊇ u '' Ω`
with `m ≤ k`, and `v ∈ W^{b,p}_loc` with `m ≤ b` and `(b + k - m) p > 2`, the product
`B(g ∘ u, v)` is in `W^{m,p}_loc`. The values of `g`, `v` and `B` lie in a universe at least that
of `F`, so that the statement is closed under the passage from `g` to `fderiv ℝ g`. -/
private theorem MemWkpLoc.bilin_comp_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {u : ℂ → F} {W : Set F} (hu : MemWkpLoc p Ω k u)
    (huc : ContinuousOn u Ω) (hW : IsOpen W) (huW : MapsTo u Ω W) (m : ℕ) (hmk : m ≤ k)
    {G V H : Type (max uF uH)} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (B : G →L[ℝ] V →L[ℝ] H) {g : F → G} {v : ℂ → V} {b : ℕ} (hg : ContDiffOn ℝ m g W)
    (hv : MemWkpLoc p Ω b v) (hmb : m ≤ b) (hbkm : 2 < ((b + k - m : ℕ) : ℝ≥0) * p) :
    MemWkpLoc p Ω m (fun z => B (g (u z)) (v z)) := by
  induction m generalizing G V H g v b with
  | zero =>
    simpa using memWkpLoc_zero_iff.2
      ((hv.memLpLoc.clm_comp B.flip).clm_apply_continuousOn (hg.continuousOn.comp huc huW))
  | succ m ih =>
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
    -- `u` lies in `W^{1,r}_loc` for some `r > 2` with `p ≤ r`.
    obtain ⟨r, hr, hpr, hur⟩ : ∃ r : ℝ≥0, 2 < r ∧ p ≤ r ∧ MemWkpLoc r Ω 1 u := by
      by_cases hp2 : 2 < p
      · exact ⟨p, hp2, le_rfl, hu.of_le (by omega)⟩
      obtain ⟨r, hr, hur⟩ := hu.exists_two_lt_memWkpLoc_one_of_two_lt_mul hp1
        (by exact_mod_cast hkp)
      exact ⟨r, hr, (not_lt.1 hp2).trans hr.le, hur⟩
    obtain ⟨Du, hDu, hDur⟩ := hur.exists_weakFDeriv_of_isOpen
    obtain ⟨Dv, hDv, hDvb⟩ := hv.exists_weakFDeriv_of_isOpen
    have hDuk : MemWkpLoc p Ω k Du := hu.memWkpLoc_of_hasWeakFDerivOn hDu
    have hgc : ContinuousOn (fun z => g (u z)) Ω := hg.continuousOn.comp huc huW
    have hDgc : ContinuousOn (fun z => fderiv ℝ g (u z)) Ω :=
      (hg.continuousOn_fderiv_of_isOpen hW (by simp)).comp huc huW
    -- The weak Leibniz rule for `B(g ∘ u, v)`, with `g ∘ u` bounded and in `W^{1,r}_loc`.
    have hD := hDu.contDiffOn_comp huc hW (hg.of_le (by simp)) huW
    have hDf : MemLpLoc r Ω (fun z => (fderiv ℝ g (u z)).comp (Du z)) :=
      hDur.memLpLoc.continuousOn_clm_comp hDgc
    have hLeib := hD.bilin_of_memLpLoc B hr hp hpr hgc.memLpLoc hDf hDv hv.memLpLoc
      hDvb.memLpLoc
    -- The first term is `Φ(Du, v)` evaluated at `Dg(u)`.
    have h₁ : MemWkpLoc p Ω m (fun z => B.precompL ℂ ((fderiv ℝ g (u z)).comp (Du z)) (v z)) := by
      obtain ⟨Φ, hΦdef⟩ := exists_bilin_comp_precompL (F := F) B
      have hΦ : MemWkpLoc p Ω m (fun z => Φ (Du z) (v z)) :=
        MemWkpLoc.bilin_of_two_lt_add_sub_mul (H := (F →L[ℝ] G) →L[ℝ] ℂ →L[ℝ] H) (B := Φ) hp hDuk
          hv (c := m) (by omega) (by omega)
          (by rwa [show k + (b + 1) - m = b + 1 + (k + 1) - (m + 1) by omega])
      have hDg : ContDiffOn ℝ m (fderiv ℝ g) W := hg.fderiv_of_isOpen hW (by push_cast; rfl)
      refine (ih (by omega) (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] H)) hDg hΦ le_rfl
        (by rwa [Nat.add_sub_cancel_left])).congr fun z _ => ?_
      simp only [ContinuousLinearMap.apply_apply, hΦdef]
    have h₂ : MemWkpLoc p Ω m (fun z => B.precompR ℂ (g (u z)) (Dv z)) :=
      ih (by omega) (B.precompR ℂ) (hg.of_le (by simp)) hDvb (by omega)
        (by rwa [show b + (k + 1) - m = b + 1 + (k + 1) - (m + 1) by omega])
    exact memWkpLoc_succ_iff_of_isOpen.2
      ⟨by simpa using (hv.memLpLoc.clm_comp B.flip).clm_apply_continuousOn hgc, _, hLeib,
        h₁.add h₂⟩

variable {G : Type uG} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Composition of continuous local Sobolev maps for `kp > 2`.** Let `1 < p` and `k p > 2`. If
`u` is continuous on `Ω` and belongs to `W^{k,p}_loc(Ω)`, and `g` is `Cᵏ` on an open set `W`
containing `u '' Ω`, then `g ∘ u` belongs to `W^{k,p}_loc(Ω)`. This includes `p ≤ 2` for
`k ≥ 2`. -/
theorem MemWkpLoc.contDiffOn_comp_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {u : ℂ → F} {g : F → G} {W : Set F} (hu : MemWkpLoc p Ω k u)
    (huc : ContinuousOn u Ω) (hW : IsOpen W) (hg : ContDiffOn ℝ k g W) (huW : MapsTo u Ω W) :
    MemWkpLoc p Ω k (fun z => g (u z)) := by
  -- Move the values to `ULift G`, in a universe at least that of `F`, and multiply by the
  -- constant `c⁻¹ 1` of `ULift ℝ`.
  let e : G ≃L[ℝ] ULift.{uF} G := (LinearIsometryEquiv.ulift ℝ G).symm.toContinuousLinearEquiv
  let c : ULift.{max uF uG} ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.ulift
  let B : ULift.{uF} G →L[ℝ] ULift.{max uF uG} ℝ →L[ℝ] ULift.{uF} G :=
    ((ContinuousLinearMap.compL ℝ _ ℝ _).flip (c : ULift.{max uF uG} ℝ →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hone : MemWkpLoc p Ω k (fun _ : ℂ => c.symm 1) := contDiff_const.memWkpLoc
  have h := MemWkpLoc.bilin_comp_of_two_lt_mul hp hkp hu huc hW huW k le_rfl B
    (e.contDiff.comp_contDiffOn hg) hone le_rfl (by rwa [Nat.add_sub_cancel])
  refine e.comp_memWkpLoc_iff.1 (h.congr fun z _ => ?_)
  simp [B]

/-- **Composition of continuous local Sobolev maps with globally `Cᵏ` maps for `kp > 2`.** Let
`1 < p` and `k p > 2`. If `u` is continuous on `Ω` and belongs to `W^{k,p}_loc(Ω)`, and `g` is
`Cᵏ`, then `g ∘ u` belongs to `W^{k,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiff_comp_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {u : ℂ → F} {g : F → G} (hu : MemWkpLoc p Ω k u)
    (huc : ContinuousOn u Ω) (hg : ContDiff ℝ k g) : MemWkpLoc p Ω k (fun z => g (u z)) :=
  hu.contDiffOn_comp_of_two_lt_mul hp hkp huc isOpen_univ hg.contDiffOn (mapsTo_univ _ _)

/-- **Composition with domain dependence for `kp > 2`.** Let `1 < p` and `k p > 2`. If `u` is
continuous on `Ω` and belongs to `W^{k,p}_loc(Ω)`, and `g : ℂ × F → G` is `Cᵏ` on an open set
containing the graph of `u` over `Ω`, then `z ↦ g (z, u z)` belongs to `W^{k,p}_loc(Ω)`. -/
theorem MemWkpLoc.contDiffOn_comp_graph_of_two_lt_mul {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {u : ℂ → F} {g : ℂ × F → G} {W : Set (ℂ × F)}
    (hu : MemWkpLoc p Ω k u) (huc : ContinuousOn u Ω) (hW : IsOpen W) (hg : ContDiffOn ℝ k g W)
    (huW : ∀ z ∈ Ω, (z, u z) ∈ W) : MemWkpLoc p Ω k (fun z => g (z, u z)) := by
  have hid : MemWkpLoc p Ω k (fun z : ℂ => z) := contDiff_id.memWkpLoc
  exact (hid.prodMk hu).contDiffOn_comp_of_two_lt_mul hp hkp (continuousOn_id.prodMk huc) hW hg
    huW

/-- The check at `p = 4/3` and `k = 2`: here `kp = 8/3 > 2` while `p < 2`, outside the range
`p > 2` of `TauCeti.MemWkpLoc.contDiffOn_comp_succ`, and the square of a continuous member of
`W^{2,4/3}_loc` is in `W^{2,4/3}_loc`. -/
example {u : ℂ → ℝ} (hu : MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 u) (huc : ContinuousOn u Ω) :
    MemWkpLoc (4 / 3 : ℝ≥0) Ω 2 (fun z => u z ^ 2) :=
  hu.contDiff_comp_of_two_lt_mul (g := fun x : ℝ => x ^ 2) (by norm_num) (by norm_num) huc
    (contDiff_id.pow 2)

end TauCeti
