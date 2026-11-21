/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Analysis.Complex.Wirtinger.OpenSet
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The additive Cousin problem on open subsets of `ℂ`

Given an arbitrary family of open subsets `U : ι → Set ℂ` and holomorphic functions `c i j` on
each overlap `U i ∩ U j` with values in a complex Banach space `W` satisfying the additive
cocycle condition `c i j + c j k + c k i = 0` on triple overlaps `U i ∩ U j ∩ U k`, there exist
holomorphic functions `b i` on `U i` solving `b i - b j = c i j` on `U i ∩ U j`
(`TauCeti.exists_differentiableOn_sub_eq`). Neither connectedness of `⋃ i, U i` nor local
finiteness or countability of the cover is required.

The proof resolves the cocycle smoothly using a smooth partition of unity `ρ` subordinate to the
cover on the open submanifold `Ω = ⋃ i, U i` (`SmoothPartitionOfUnity.exists_isSubordinate`):
the locally finite sums `g i = ∑ᶠ k, ρ k • c i k` are smooth on `U i` and satisfy
`g i - g j = c i j` on `U i ∩ U j`. Because `c i j` is holomorphic, the conjugate Wirtinger
derivatives `\bar∂ (g i)` agree on overlaps and glue to a global smooth function `f` on `Ω`. Solving
`\bar∂ u = f` globally on `Ω` (`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq`) and
setting `b i = g i - u` yields holomorphic functions with the same differences.

Any two solutions `b₁` and `b₂` of the same additive Cousin problem differ by a single global
holomorphic function on `⋃ i, U i` (`TauCeti.exists_differentiableOn_iUnion_sub_eq`).

## Main results

* `TauCeti.exists_differentiableOn_sub_eq`: every holomorphic additive cocycle on an arbitrary
  open cover of an open subset of `ℂ` is a coboundary (Cousin I).
* `TauCeti.exists_differentiableOn_iUnion_sub_eq`: two holomorphic coboundaries with the same
  overlap differences differ by a global holomorphic function on the union of the cover.

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 12.3 and Theorem 12.4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.5.
-/

public section

open Filter Set TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti

private theorem exists_eqOn_iUnion {ι α β : Type*} [Zero β] {U : ι → Set α} {φ : ι → α → β}
    (hagree : ∀ i j, ∀ z ∈ U i ∩ U j, φ i z = φ j z) :
    ∃ ψ : α → β, ∀ i, EqOn (φ i) ψ (U i) := by
  classical
  refine ⟨fun z ↦ if hz : z ∈ ⋃ i, U i then φ (mem_iUnion.1 hz).choose z else 0, fun i z hz ↦ ?_⟩
  have hzU : z ∈ ⋃ k, U k := mem_iUnion.2 ⟨i, hz⟩
  simp only [hzU, ↓reduceDIte]
  exact hagree i _ z ⟨hz, (mem_iUnion.1 hzU).choose_spec⟩

variable {ι W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

private theorem cocycle_sub {U : ι → Set ℂ} {c : ι → ι → ℂ → W}
    (hcycle : ∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z + c k i z = 0)
    {i j k : ι} {z : ℂ} (hz : z ∈ U i ∩ U j ∩ U k) :
    c i k z - c j k z = c i j z := by
  have hdiag : c i i z = 0 := by
    have h3 : (3 : ℝ) • c i i z = 0 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
      exact hcycle i i i z ⟨⟨hz.1.1, hz.1.1⟩, hz.1.1⟩
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  have hskew : c k i z = -c i k z := by
    have h := hcycle i k i z ⟨⟨hz.1.1, hz.2⟩, hz.1.1⟩
    rw [hdiag, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  have h := hcycle i j k z hz
  rw [hskew] at h
  have hrew : c i k z - c j k z - c i j z = -(c i j z + c j k z + -c i k z) := by abel
  exact eq_of_sub_eq_zero (by rw [hrew, h, neg_zero])

/-- **Additive Cousin problem (Cousin I).** For an arbitrary family of open subsets
`U : ι → Set ℂ` and a Banach-valued holomorphic cocycle `c i j` on `U i ∩ U j` satisfying
`c i j z + c j k z + c k i z = 0` on triple overlaps, there exist holomorphic functions `b i` on
`U i` with `b i z - b j z = c i j z` on `U i ∩ U j`. Neither local finiteness of the cover nor
connectedness of `⋃ i, U i` is assumed. -/
theorem exists_differentiableOn_sub_eq [CompleteSpace W] {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) {c : ι → ι → ℂ → W}
    (hc : ∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j))
    (hcycle : ∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z + c k i z = 0) :
    ∃ b : ι → ℂ → W, (∀ i, DifferentiableOn ℂ (b i) (U i)) ∧
      ∀ i j, ∀ z ∈ U i ∩ U j, b i z - b j z = c i j z := by
  -- Work on the open submanifold `Ω = ⋃ i, U i`, which is Hausdorff and σ-compact.
  let Ω : Opens ℂ := ⟨⋃ i, U i, isOpen_iUnion hU⟩
  have : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  let V : ι → Set Ω := fun i ↦ Subtype.val ⁻¹' U i
  have hVopen : ∀ i, IsOpen (V i) := fun i ↦ (hU i).preimage continuous_subtypeVal
  have hVcover : (univ : Set Ω) ⊆ ⋃ i, V i := fun x _ ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 x.property
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ V hVopen hVcover
  -- Smooth splitting `g i = ∑ᶠ k, ρ k • c i k` on `U i`.
  let gΩ : ι → Ω → W := fun i x ↦ ∑ᶠ k, ρ k x • c i k x
  let g : ι → ℂ → W := fun i ↦ Subtype.val.extend (gΩ i) 0
  have hg_sub {i j : ι} {z : ℂ} (hz : z ∈ U i ∩ U j) : g i z - g j z = c i j z := by
    set x : Ω := ⟨z, mem_iUnion.2 ⟨i, hz.1⟩⟩
    have hgi : g i z = gΩ i x := Subtype.val_injective.extend_apply (gΩ i) 0 x
    have hgj : g j z = gΩ j x := Subtype.val_injective.extend_apply (gΩ j) 0 x
    rw [hgi, hgj]
    dsimp only [gΩ]
    rw [← ρ.sum_finsupport_smul_eq_finsum x (fun k (y : Ω) ↦ c i k y),
      ← ρ.sum_finsupport_smul_eq_finsum x (fun k (y : Ω) ↦ c j k y),
      ← Finset.sum_sub_distrib]
    have hcongr : ∑ k ∈ ρ.finsupport x, (ρ k x • c i k z - ρ k x • c j k z) =
        ∑ k ∈ ρ.finsupport x, ρ k x • c i j z := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hzk : z ∈ U k := hρ k (subset_tsupport _ ((ρ.mem_finsupport x).1 hk))
      rw [← smul_sub, cocycle_sub hcycle ⟨hz, hzk⟩]
    rw [hcongr, ← Finset.sum_smul, ρ.sum_finsupport x (mem_univ x), one_smul]
  have hg_smooth (i : ι) : ContDiffOn ℝ ∞ (g i) (U i) := fun z₀ hz₀ ↦ by
    set x₀ : Ω := ⟨z₀, mem_iUnion.2 ⟨i, hz₀⟩⟩
    have hΩ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) ∞ (gΩ i) x₀ := by
      refine ρ.contMDiffAt_finsum (g := fun k (x : Ω) ↦ c i k x) fun k hk ↦ ?_
      have hzk : z₀ ∈ U k := hρ k hk
      have hck : ContDiffAt ℝ ∞ (c i k) z₀ :=
        (((hc i k).contDiffOn ((hU i).inter (hU k))).of_le le_top).restrict_scalars ℝ
          |>.contDiffAt (((hU i).inter (hU k)).mem_nhds ⟨hz₀, hzk⟩)
      exact contMDiffAt_subtype_iff.2 (contMDiffAt_iff_contDiffAt.2 hck)
    exact (contMDiffAt_iff_contDiffAt.1 (hΩ.extend_subtypeVal 0)).contDiffWithinAt
  -- Glue `\bar∂ (g i)` across the cover to a global smooth datum `f` on `Ω`.
  obtain ⟨f, hf_eq⟩ := exists_eqOn_iUnion (U := U)
    (φ := fun i z ↦ conjWirtingerDeriv (g i) z 1) fun i j z ⟨hzi, hzj⟩ ↦ by
      have heq : g i =ᶠ[𝓝 z] g j + c i j := by
        filter_upwards [((hU i).inter (hU j)).mem_nhds ⟨hzi, hzj⟩] with w hw
        simp only [Pi.add_apply, ← hg_sub hw]
        abel
      have hgj : DifferentiableAt ℝ (g j) z :=
        ((hg_smooth j).contDiffAt ((hU j).mem_nhds hzj)).differentiableAt (by simp)
      have hcij : DifferentiableAt ℂ (c i j) z :=
        (hc i j).differentiableAt (((hU i).inter (hU j)).mem_nhds ⟨hzi, hzj⟩)
      rw [heq.conjWirtingerDeriv_eq, conjWirtingerDeriv_add hgj (hcij.restrictScalars ℝ),
        add_apply, hcij.conjWirtingerDeriv_eq_zero, zero_apply, add_zero]
  have hf_smooth : ContDiffOn ℝ ∞ f (Ω : Set ℂ) := fun z hz ↦ by
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    have heq : f =ᶠ[𝓝 z] fun w ↦ conjWirtingerDeriv (g i) w 1 := by
      filter_upwards [(hU i).mem_nhds hzi] with w hw
      exact (hf_eq i hw).symm
    have hcd : ContDiffAt ℝ ∞ (fun w ↦ conjWirtingerDeriv (g i) w 1) z :=
      ((hg_smooth i).contDiffAt ((hU i).mem_nhds hzi)).conjWirtingerDeriv_apply (by simp) 1
    exact (hcd.congr_of_eventuallyEq heq).contDiffWithinAt
  -- Solve `\bar∂ u = f` globally on `Ω` and set `b i = g i - u`.
  obtain ⟨u, hu_smooth, hu_eq⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq (n := ⊤) le_top Ω.isOpen hf_smooth
  refine ⟨fun i ↦ g i - u, fun i ↦ ?_, fun i j z hz ↦ ?_⟩
  · exact (contDiffOn_and_conjWirtingerDeriv_apply_one_eq_iff (n := ∞) (by simp) (hU i)
      (hu_smooth.mono (subset_iUnion U i)) (fun z hz ↦ hu_eq z (mem_iUnion.2 ⟨i, hz⟩))).1
      ⟨hg_smooth i, fun z hz ↦ hf_eq i hz⟩
  · simp only [Pi.sub_apply, sub_sub_sub_cancel_right]
    exact hg_sub hz

/-- **Uniqueness of Cousin I solutions modulo global holomorphic functions.** If two families of
holomorphic functions on an open cover `U : ι → Set ℂ` have the same overlap differences, their
termwise difference glues to a single holomorphic function on `⋃ i, U i`. -/
theorem exists_differentiableOn_iUnion_sub_eq {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {b₁ b₂ : ι → ℂ → W} (hb₁ : ∀ i, DifferentiableOn ℂ (b₁ i) (U i))
    (hb₂ : ∀ i, DifferentiableOn ℂ (b₂ i) (U i))
    (hdiff : ∀ i j, ∀ z ∈ U i ∩ U j, b₁ i z - b₁ j z = b₂ i z - b₂ j z) :
    ∃ h : ℂ → W, DifferentiableOn ℂ h (⋃ i, U i) ∧
      ∀ i, ∀ z ∈ U i, b₁ i z - b₂ i z = h z := by
  obtain ⟨h, heq⟩ := exists_eqOn_iUnion (U := U)
    (φ := fun i z ↦ b₁ i z - b₂ i z) fun i j z hz ↦ by
      have hsub := hdiff i j z hz
      have hrew :
          b₁ i z - b₂ i z - (b₁ j z - b₂ j z) = (b₁ i z - b₁ j z) - (b₂ i z - b₂ j z) := by
        abel
      exact eq_of_sub_eq_zero (by rw [hrew, hsub, sub_self])
  refine ⟨h, fun z hz ↦ ?_, fun i z hz ↦ heq i hz⟩
  obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
  have hloc : h =ᶠ[𝓝 z] fun w ↦ b₁ i w - b₂ i w := by
    filter_upwards [(hU i).mem_nhds hzi] with w hw
    exact (heq i hw).symm
  have hd : DifferentiableAt ℂ (fun w ↦ b₁ i w - b₂ i w) z :=
    ((hb₁ i).differentiableAt ((hU i).mem_nhds hzi)).sub
      ((hb₂ i).differentiableAt ((hU i).mem_nhds hzi))
  exact (hd.congr_of_eventuallyEq hloc).differentiableWithinAt

end TauCeti
