/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.PartitionOfUnity.CechSplitting

/-!
# The additive Cousin problem on open subsets of the plane

Let `U i` be open subsets of `ℂ`, indexed by an arbitrary type, and let `c i j` be holomorphic on
`U i ∩ U j` with values in a complex Banach space, satisfying the additive cocycle relation
`c i j + c j k + c k i = 0` on `U i ∩ U j ∩ U k`. Then there are functions `b i`, holomorphic on
`U i`, with `b i - b j = c i j` on `U i ∩ U j`
(`TauCeti.exists_differentiableOn_sub_eq_of_cocycle`). Any two such families differ by one
function holomorphic on the union of the `U i`
(`TauCeti.exists_differentiableOn_eqOn_sub_of_sub_eq`). Neither local finiteness nor
countability of the cover is assumed, and the union may be empty or disconnected.

In the language of sheaf cohomology, the first Čech cohomology of the sheaf of holomorphic
functions vanishes for every open cover of every open subset of the plane.

The proof has two steps. First the cocycle splits smoothly: on the open subset `Ω = ⋃ i, U i`,
viewed as a smooth manifold, a smooth partition of unity `ρ` subordinate to the cover gives
smooth `g i` on `U i` with `c i j = g j - g i`
(`TauCeti.exists_contMDiffOn_eq_smul_sub_of_cocycle`). The differences `g i - g j` are
holomorphic, so the `\bar∂ (g i)` agree on overlaps, and the Dolbeault lemma on `Ω` produces one
smooth `f` with every `f - g i` holomorphic on `U i`
(`IsOpen.exists_contDiffOn_differentiableOn_sub`). Then `b i = f - g i` solves the problem.

## Main results

* `TauCeti.exists_differentiableOn_sub_eq_of_cocycle`: the additive Cousin problem is solvable for
  every open cover of an open subset of `ℂ`.
* `TauCeti.exists_differentiableOn_eqOn_sub_of_sub_eq`: two solutions differ by a function
  holomorphic on the union of the cover.

## References

* A. Rainer, *Advanced Complex Analysis*, Proposition 12.3 and Theorem 12.4.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.5.
-/

public section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {ι : Type*} {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] {U : ι → Set ℂ}

/-- **Uniqueness in the additive Cousin problem.** Let `b i` and `b' i` be holomorphic on open
sets `U i ⊆ ℂ` with `b i - b j = b' i - b' j` on every `U i ∩ U j`. Then there is one function
`h`, holomorphic on `⋃ i, U i`, with `b i - b' i = h` on each `U i`. -/
theorem exists_differentiableOn_eqOn_sub_of_sub_eq (hU : ∀ i, IsOpen (U i)) {b b' : ι → ℂ → W}
    (hb : ∀ i, DifferentiableOn ℂ (b i) (U i)) (hb' : ∀ i, DifferentiableOn ℂ (b' i) (U i))
    (hbb' : ∀ i j, ∀ z ∈ U i ∩ U j, b i z - b j z = b' i z - b' j z) :
    ∃ h : ℂ → W, DifferentiableOn ℂ h (⋃ i, U i) ∧ ∀ i, EqOn (b i - b' i) h (U i) := by
  classical
  let h : ℂ → W := fun z ↦ if hz : ∃ i, z ∈ U i then (b hz.choose - b' hz.choose) z else 0
  have hh (i : ι) : EqOn (b i - b' i) h (U i) := fun z hz ↦ by
    have hz' : ∃ i, z ∈ U i := ⟨i, hz⟩
    simp only [h, hz', ↓reduceDIte, Pi.sub_apply]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hbb' _ _ z ⟨hz, hz'.choose_spec⟩
  exact ⟨h, DifferentiableOn.iUnion_of_isOpen
    (fun i ↦ ((hb i).sub (hb' i)).congr fun z hz ↦ (hh i hz).symm) hU, hh⟩

variable [CompleteSpace W]

/-- **The additive Cousin problem on an open subset of the plane.** Let `U i` be open subsets of
`ℂ`, indexed by an arbitrary type, and let `c i j` be holomorphic on `U i ∩ U j`, with
`c i j + c j k + c k i = 0` on `U i ∩ U j ∩ U k`. Then there are functions `b i`, holomorphic on
`U i`, with `b i - b j = c i j` on `U i ∩ U j`. The cover need not be locally finite or
countable. -/
theorem exists_differentiableOn_sub_eq_of_cocycle (hU : ∀ i, IsOpen (U i)) {c : ι → ι → ℂ → W}
    (hc : ∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j))
    (hcocycle : ∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z + c k i z = 0) :
    ∃ b : ι → ℂ → W, (∀ i, DifferentiableOn ℂ (b i) (U i)) ∧
      ∀ i j, ∀ z ∈ U i ∩ U j, b i z - b j z = c i j z := by
  classical
  -- The union `Ω` of the cover, as an open submanifold of `ℂ`.
  have hΩ : IsOpen (⋃ i, U i) := isOpen_iUnion hU
  let Ω : Opens ℂ := ⟨⋃ i, U i, hΩ⟩
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have hmem {i : ι} {z : ℂ} (hz : z ∈ U i) : z ∈ Ω := mem_iUnion.2 ⟨i, hz⟩
  -- The cocycle relation in the form `c i j + c j k = c i k`.
  have hcii (i : ι) {z : ℂ} (hz : z ∈ U i) : c i i z = 0 := by
    have h3 := hcocycle i i i z ⟨⟨hz, hz⟩, hz⟩
    have : (3 : ℂ) • c i i z = 0 := by rw [← h3]; module
    simpa using this
  have hadd (i j k : ι) {z : ℂ} (hz : z ∈ U i ∩ U j ∩ U k) : c i j z + c j k z = c i k z := by
    have hik := hcocycle i k i z ⟨⟨hz.1.1, hz.2⟩, hz.1.1⟩
    rw [hcii i hz.1.1, add_zero] at hik
    rw [eq_neg_of_add_eq_zero_left (hcocycle i j k z hz), eq_neg_of_add_eq_zero_right hik, neg_neg]
  -- Split the cocycle smoothly on `Ω`: `c i j = g j - g i` with `g i` smooth on `U i`.
  let V : ι → Set Ω := fun i ↦ Subtype.val ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) := (hU i).preimage continuous_subtypeVal
  have hVcov : ⋃ i, V i = univ := eq_univ_of_forall fun z ↦ by
    obtain ⟨i, hi⟩ := mem_iUnion.1 ((Opens.mem_mk (h := hΩ)).1 z.property)
    exact mem_iUnion.2 ⟨i, hi⟩
  have hξ (i j : ι) :
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, W) ∞ (fun z : Ω ↦ c i j z) (V i ∩ V j) := fun z hz ↦ by
    have hcd : ContDiffAt ℝ ∞ (c i j) z :=
      (((hc i j).contDiffOn ((hU i).inter (hU j))).contDiffAt
        (((hU i).inter (hU j)).mem_nhds hz)).restrict_scalars ℝ
    exact (contMDiffAt_subtype_iff.2 hcd.contMDiffAt).contMDiffWithinAt
  obtain ⟨g, hg, hgξ, -⟩ := exists_contMDiffOn_eq_smul_sub_of_cocycle (ψ := fun _ _ _ ↦ (1 : ℝ))
    hV hVcov hξ fun i j k z hz ↦ by rw [one_smul]; exact hadd i j k hz
  -- Extend each `g i` by zero to a function on `ℂ`, smooth on `U i`.
  let G : ι → ℂ → W := fun i ↦ Subtype.val.extend (g i) 0
  have hG (i : ι) {z : ℂ} (hz : z ∈ Ω) : G i z = g i ⟨z, hz⟩ :=
    Subtype.val_injective.extend_apply (g i) 0 ⟨z, hz⟩
  have hGs (i : ι) : ContDiffOn ℝ (⊤ : ℕ∞) (G i) (U i) := fun z hz ↦ by
    have hgz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, W) ∞ (g i) ⟨z, hmem hz⟩ :=
      (hg i).contMDiffAt ((hV i).mem_nhds hz)
    exact (contMDiffAt_iff_contDiffAt.1 (hgz.extend_subtypeVal 0)).contDiffWithinAt
  have hGc (i j : ι) : EqOn (G i - G j) (-c i j) (U i ∩ U j) := fun z hz ↦ by
    simp only [Pi.sub_apply, Pi.neg_apply, hG i (hmem hz.1), hG j (hmem hz.1),
      hgξ i j ⟨z, hmem hz.1⟩ hz, one_smul, neg_sub]
  -- The Dolbeault lemma corrects the `G i` to holomorphic functions.
  obtain ⟨f, -, hf⟩ := hΩ.exists_contDiffOn_differentiableOn_sub hU hGs
    (fun i j ↦ (hc i j).neg.congr (hGc i j)) fun z hz ↦ hz
  refine ⟨fun i ↦ f - G i, fun i ↦ (hf i).mono fun z hz ↦ ⟨hmem hz, hz⟩, fun i j z hz ↦ ?_⟩
  have := hGc i j hz
  simp only [Pi.sub_apply, Pi.neg_apply] at this ⊢
  rw [sub_sub_sub_cancel_left, ← neg_sub, this, neg_neg]

end TauCeti
