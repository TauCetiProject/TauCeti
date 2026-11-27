/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.Family
import TauCeti.Analysis.Calculus.Deriv.LevelCrossing
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Smooth graphs of transverse scalar levels

Quantitative crossing along each real fibre gives a unique height on a manifold of
parameters. The local inverse of the map preserving the parameter and sending height
to the scalar function then shows that the height is smooth.

## References

* B. Kleiner and J. Lott, *Notes on Perelman's papers*, Theorem 46.1.
* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace P] [ChartedSpace H P] {n : ℕ∞ω} [IsManifold I n P]
  [BoundarylessManifold I P]

/-- Local inverse branches of the map `(q,t) ↦ (q, F(q,t))` identify the unique fibre root
with a smooth function on the parameter manifold. -/
private theorem contMDiff_of_unique_axial_level {φ : P × ℝ → ℝ} {s : Set (P × ℝ)}
    {W c : ℝ} {h : P → ℝ} (hs : IsOpen s) (hf : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) n φ s)
    (hn : 1 ≤ n) (hslab : (univ ×ˢ Ioo (-W) W) ⊆ s)
    (hroot : ∀ q, h q ∈ Ioo (-W) W ∧ φ (q, h q) = c)
    (hderiv : ∀ q, deriv (fun t ↦ φ (q, t)) (h q) ≠ 0)
    (hunique : ∀ q t, t ∈ Ioo (-W) W → φ (q, t) = c → t = h q) :
    ContMDiff I 𝓘(ℝ) n h := by
  intro q
  let F : P × ℝ → P × ℝ := fun p ↦ (p.1, φ p)
  have hq : F (q, h q) = (q, c) := Prod.ext rfl (hroot q).2
  have hL : IsLocalDiffeomorphAt (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) n F (q, h q) :=
    isLocalDiffeomorphAt_fst_prodMk hf hs (hslab ⟨mem_univ _, (hroot q).1⟩) hn
      ((differentiableAt_of_deriv_ne_zero (hderiv q)).hasDerivAt.isInvertible_mfderiv (hderiv q))
  have hleft : hL.localInverse (q, c) = (q, h q) := by
    rw [← hq]
    exact hL.localInverse_left_inv hL.localInverse_mem_target
  have hsource : (q, c) ∈ hL.localInverse.source := hq ▸ hL.localInverse_mem_source
  have hcur : ContMDiffAt I (I.prod 𝓘(ℝ)) n (fun p : P ↦ (p, c)) q :=
    contMDiffAt_id.prodMk contMDiffAt_const
  have hbranch : ContMDiffAt I (I.prod 𝓘(ℝ)) n
      (fun p : P ↦ hL.localInverse (p, c)) q :=
    (hq ▸ hL.contMDiffAt_localInverse).comp q hcur
  refine (contMDiffAt_snd.comp q hbranch).congr_of_eventuallyEq ?_
  have hmem : hL.localInverse (q, c) ∈ univ ×ˢ Ioo (-W) W :=
    hleft.symm ▸ ⟨mem_univ _, (hroot q).1⟩
  filter_upwards [hcur.continuousAt.eventually_mem
    (hL.localInverse_open_source.mem_nhds hsource),
    hbranch.continuousAt.eventually_mem
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hmem)] with p hp hps
  have hsnd := hL.localInverse_right_inv hp
  let z := hL.localInverse (p, c)
  have hfst : z.1 = p := congrArg Prod.fst hsnd
  have hc : φ (z.1, z.2) = c := congrArg Prod.snd hsnd
  exact (hunique p z.2 hps.2 ((congrArg (fun x ↦ φ (x, z.2)) hfst).symm.trans hc)).symm

/-- A uniform lower bound on the axial derivative and a smaller central oscillation produce
a smooth graph that is exactly the indicated level in the open slab. The scalar function is
assumed smooth on an open neighbourhood of the closed slab. For each parameter the central
bound forces a positive half-width. If the parameter space is empty, the graph is the empty
function and all pointwise conditions are vacuous. -/
theorem exists_contMDiff_levelGraph {φ : P × ℝ → ℝ} {s : Set (P × ℝ)} {W m c : ℝ}
    (hs : IsOpen s) (hf : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) n φ s)
    (hn : 1 ≤ n) (hm : 0 < m)
    (hslab : (univ ×ˢ Icc (-W) W) ⊆ s)
    (hderiv : ∀ q t, t ∈ Ioo (-W) W → m ≤ |deriv (fun z ↦ φ (q, z)) t|)
    (hcenter : ∀ q, |φ (q, 0) - c| < m * W) :
    ∃ h : P → ℝ, ContMDiff I 𝓘(ℝ) n h ∧ (∀ q, h q ∈ Ioo (-W) W) ∧
      ∀ q t, t ∈ Ioo (-W) W → (φ (q, t) = c ↔ t = h q) := by
  have hslice (q : P) (t : ℝ) (ht : t ∈ Icc (-W) W) :
      ContinuousAt (fun z ↦ φ (q, z)) t :=
    ((hf.contMDiffAt (hs.mem_nhds (hslab ⟨mem_univ _, ht⟩))).comp t
      (contMDiffAt_const.prodMk contMDiffAt_id)).continuousAt
  have roots (q : P) : ∃! t, t ∈ Ioo (-W) W ∧ φ (q, t) = c :=
    existsUnique_level_of_le_abs_deriv hm
      (fun t ht ↦ (hslice q t ht).continuousWithinAt) (hderiv q) (hcenter q)
  choose h hroot hunique using roots
  have hnonzero (q : P) : deriv (fun z ↦ φ (q, z)) (h q) ≠ 0 :=
    abs_pos.mp (hm.trans_le (hderiv q _ (hroot q).1))
  have hu (q : P) (t : ℝ) (ht : t ∈ Ioo (-W) W) (heq : φ (q, t) = c) : t = h q :=
    hunique q t ⟨ht, heq⟩
  refine ⟨h, contMDiff_of_unique_axial_level hs hf hn
    (fun x hx ↦ hslab ⟨hx.1, Ioo_subset_Icc_self hx.2⟩) hroot hnonzero hu,
    fun q ↦ (hroot q).1, fun q t ht ↦ ⟨hu q t ht, ?_⟩⟩
  rintro rfl
  exact (hroot q).2

end TauCeti
