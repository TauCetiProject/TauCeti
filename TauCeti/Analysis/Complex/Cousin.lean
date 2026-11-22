/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.PartitionOfUnity.CechSplitting
import TauCeti.Logic.Function.Extend

/-!
# The additive Cousin problem on open subsets of `ℂ`

Given an arbitrary family of open subsets `U : ι → Set ℂ` and holomorphic functions `c i j` on
each overlap `U i ∩ U j` with values in a complex Banach space `W` satisfying the additive
cocycle condition `c i j + c j k + c k i = 0` on triple overlaps `U i ∩ U j ∩ U k`, there exist
holomorphic functions `b i` on `U i` solving `b i - b j = c i j` on `U i ∩ U j`
(`TauCeti.exists_differentiableOn_sub_eq`). Neither connectedness of `⋃ i, U i` nor local
finiteness or countability of the cover is required.

The proof resolves the cocycle smoothly on the open submanifold `Ω = ⋃ i, U i` using
`TauCeti.exists_contMDiffOn_eq_smul_sub_of_cocycle`: this produces smooth functions `g i` on
`U i` satisfying `g i - g j = c i j` on `U i ∩ U j`. Because `c i j` is holomorphic, the
differences `g i - g j` are holomorphic on overlaps, so global Dolbeault gluing on open sets
(`IsOpen.exists_contDiffOn_differentiableOn_sub`) gives one smooth `f` on `Ω` with every
`f - g i` holomorphic on `U i`; setting `b i = g i - f` yields holomorphic functions with the
same differences.

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

variable {ι W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

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
  have hVo : ∀ i, IsOpen (V i) := fun i ↦ (hU i).preimage continuous_subtypeVal
  have hV : ⋃ i, V i = univ := eq_univ_iff_forall.2 fun x ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 x.property
    exact mem_iUnion.2 ⟨i, hi⟩
  -- Antisymmetry and cocycle identity `c i j + c j k = c i k` on triple overlaps.
  have hcoc : ∀ i j k, ∀ x ∈ V i ∩ V j ∩ V k,
      c i j (x : ℂ) + (1 : ℝ) • c j k (x : ℂ) = c i k (x : ℂ) := fun i j k x hx ↦ by
    have hii : (3 : ℂ) • c i i (x : ℂ) = 0 := by
      have h3 : (3 : ℂ) • c i i (x : ℂ) = c i i (x : ℂ) + c i i (x : ℂ) + c i i (x : ℂ) := by
        module
      rw [h3, hcycle i i i x ⟨⟨hx.1.1, hx.1.1⟩, hx.1.1⟩]
    have hci : c i i (x : ℂ) = 0 := (smul_eq_zero.1 hii).resolve_left (by norm_num)
    have hki : c i k (x : ℂ) + c k i (x : ℂ) = 0 := by
      simpa [hci] using hcycle i k i x ⟨⟨hx.1.1, hx.2⟩, hx.1.1⟩
    have hijk := hcycle i j k x hx
    rw [one_smul]
    exact eq_of_sub_eq_zero (by
      calc c i j (x : ℂ) + c j k (x : ℂ) - c i k (x : ℂ)
          = (c i j (x : ℂ) + c j k (x : ℂ) + c k i (x : ℂ)) -
              (c i k (x : ℂ) + c k i (x : ℂ)) := by abel
        _ = 0 := by rw [hijk, hki, sub_self])
  -- Smoothness of the cocycle on `V i ∩ V j` and smooth Čech splitting on `Ω`.
  have hξ (i j : ι) :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, W) (⊤ : ℕ∞) (fun x : Ω ↦ c i j (x : ℂ)) (V i ∩ V j) :=
    (contMDiffOn_iff_contDiffOn.2
      ((((hc i j).contDiffOn ((hU i).inter (hU j))).of_le le_top).restrict_scalars ℝ)).comp
      contMDiff_subtypeVal.contMDiffOn fun _ hx ↦ hx
  obtain ⟨gΩ, hgΩ, hgΩ_eq, -⟩ :=
    exists_contMDiffOn_eq_smul_sub_of_cocycle (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
      (ψ := fun _ _ _ ↦ (1 : ℝ)) hVo hV hξ hcoc
  let g : ι → ℂ → W := fun i ↦ Subtype.val.extend (-gΩ i) 0
  have hg_sub {i j : ι} {z : ℂ} (hz : z ∈ U i ∩ U j) : g i z - g j z = c i j z := by
    set x : Ω := ⟨z, mem_iUnion.2 ⟨i, hz.1⟩⟩
    have hgi : g i z = -gΩ i x := Subtype.val_injective.extend_apply (-gΩ i) 0 x
    have hgj : g j z = -gΩ j x := Subtype.val_injective.extend_apply (-gΩ j) 0 x
    rw [hgi, hgj, neg_sub_neg, hgΩ_eq i j x hz, one_smul]
  have hg_smooth (i : ι) : ContDiffOn ℝ ∞ (g i) (U i) := fun z₀ hz₀ ↦ by
    set x₀ : Ω := ⟨z₀, mem_iUnion.2 ⟨i, hz₀⟩⟩
    have hAt : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) (⊤ : ℕ∞) (-gΩ i) x₀ :=
      ((hgΩ i).neg.contMDiffAt ((hVo i).mem_nhds hz₀))
    exact (contMDiffAt_iff_contDiffAt.1 (hAt.extend_subtypeVal 0)).contDiffWithinAt
  -- Holomorphic pairwise differences allow global Dolbeault gluing on `Ω = ⋃ i, U i`.
  have hg_diff (k l : ι) : DifferentiableOn ℂ (g k - g l) (U k ∩ U l) :=
    (hc k l).congr fun _ hz ↦ hg_sub hz
  obtain ⟨f, -, hfg⟩ :=
    (isOpen_iUnion hU).exists_contDiffOn_differentiableOn_sub hU hg_smooth hg_diff Subset.rfl
  refine ⟨fun i ↦ g i - f, fun i ↦ ?_, fun i j z hz ↦ ?_⟩
  · simpa only [inter_eq_self_of_subset_right (subset_iUnion U i), neg_sub] using (hfg i).neg
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
  have hagree (i j : ι) (z : ℂ) (hzi : z ∈ U i) (hzj : z ∈ U j) :
      b₁ i z - b₂ i z = b₁ j z - b₂ j z :=
    sub_eq_sub_iff_sub_eq_sub.mp (hdiff i j z ⟨hzi, hzj⟩)
  obtain ⟨h, heq, -⟩ :=
    Function.exists_eqOn_of_agree (U := U) (f := fun i z ↦ b₁ i z - b₂ i z) hagree 0
  refine ⟨h, (differentiableOn_iUnion_iff_of_isOpen hU).2 fun i ↦ ?_, fun i z hz ↦ (heq i hz).symm⟩
  exact ((hb₁ i).sub (hb₂ i)).congr fun z hz ↦ heq i hz

end TauCeti
