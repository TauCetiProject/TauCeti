/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication
public import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.Local.Locality

/-!
# Mixed-exponent products of local Sobolev maps on half-discs

Let `p > 2`, `1 < q ≤ p` and let `B : F × G → H` be continuous bilinear with `G`
finite-dimensional. This file carries the order-zero and order-one mixed-exponent product
theorems of `TauCeti.Analysis.Sobolev.Local.Multiplication` from an open planar domain `Ω` to the
relatively open set `Ω ∩ {0 ≤ im}` of the closed upper half-plane, with `Lᵖ` bounds up to the
real axis.

Near a point of the real axis, both factors on a disc centred on the axis are extended across the
axis by the even reflection, `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`, the
interior theorem is applied on the disc, and the result is restricted back to the half-disc,
where the reflection agrees with the original map. Near a point off the axis the interior
theorem applies directly. Local membership is a local property, `TauCeti.memWkpLoc_iff_locally`,
which glues the two cases.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple_halfPlane`: the local gain of integrability
  `W^{1,q} ⊂ Lʳ` with `1/p + 1/r = 1/q`.
* `TauCeti.MemLpLoc.bilin_of_memWkpLoc_halfPlane`: order zero, `Lᵖ · W^{1,q} ⊂ L^q`.
* `TauCeti.MemWkpLoc.bilin_of_memLpLoc_top_halfPlane` and `TauCeti.MemWkpLoc.bilin_halfPlane`:
  order one, `W^{1,p} · W^{1,q} ⊂ W^{1,q}`. At `q = p` this is the algebra property of
  `W^{1,p}_loc` on half-discs.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace Filter Metric
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- A local property on `Ω ∩ {0 ≤ im}` follows from the property on the open subsets of
`Ω ∩ {0 < im}` and on the half-discs `ball x r ∩ {0 ≤ im}` centred on the real axis inside `Ω`. -/
private theorem halfPlane_of_open_of_ball (P : Set ℂ → Prop)
    (hP : ∀ {U : Set ℂ}, P U ↔ ∀ z ∈ U, ∃ V ∈ 𝓝[U] z, P V)
    (hint : ∀ V : Opens ℂ, (V : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} → P V)
    (hbd : ∀ x r : ℝ, ball (x : ℂ) r ⊆ Ω → P (ball (x : ℂ) r ∩ {z | 0 ≤ z.im})) :
    P ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  refine hP.2 fun z hz => ?_
  rcases (show (0 : ℝ) ≤ z.im from hz.2).lt_or_eq with hz0 | hz0
  · let V : Opens ℂ := Ω ⊓ ⟨{z | 0 < z.im}, isOpen_lt continuous_const Complex.continuous_im⟩
    refine ⟨V, mem_nhdsWithin_of_mem_nhds (V.isOpen.mem_nhds ⟨hz.1, hz0⟩),
      hint V fun w hw => ⟨hw.1, (show 0 < w.im from hw.2).le⟩⟩
  · have hzx : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen _ (hzx.symm ▸ hz.1)
    refine ⟨ball (z.re : ℂ) r ∩ {z | 0 ≤ z.im}, mem_nhdsWithin.2 ⟨ball (z.re : ℂ) r, isOpen_ball,
      hzx ▸ mem_ball_self hr, fun w hw => ⟨hw.1, hw.2.2⟩⟩, hbd z.re r hrΩ⟩

/-- A local Sobolev map on a disc centred on the real axis restricts to the half-disc as any map
agreeing with it on the closed upper half-plane. -/
private theorem MemWkpLoc.ball_inter_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ≥0∞} {x r : ℝ} {k : ℕ} {u v : ℂ → E} (hu : MemWkpLoc s (ball (x : ℂ) r) k u)
    (huv : ∀ z : ℂ, 0 ≤ z.im → u z = v z) :
    MemWkpLoc s (ball (x : ℂ) r ∩ {z | 0 ≤ z.im}) k v :=
  (hu.mono inter_subset_left).congr_ae <| by
    filter_upwards [ae_restrict_mem (measurableSet_ball.inter
      (measurableSet_le measurable_const Complex.measurable_im))] with z hz using huv z hz.2

/-- The even reflection of a half-disc Sobolev map of order one. -/
private theorem MemWkpLoc.reflect_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ≥0∞} (hs : 1 ≤ s) {x r : ℝ} {u : ℂ → E} (hΩ : ball (x : ℂ) r ⊆ Ω)
    (hu : MemWkpLoc s ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    MemWkpLoc s (ball (x : ℂ) r) 1 (TauCeti.planarReflection (higherReflectionCoeff 1) u) :=
  MemWkpLoc.planarReflection_higherReflectionCoeff_ball hs x r
    (hu.mono (inter_subset_inter_left _ hΩ))

/-- The reflection of a half-disc locally `Lˢ` map. -/
private theorem MemLpLoc.reflect {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℝ≥0∞} {x r : ℝ} {u : ℂ → E} (hΩ : ball (x : ℂ) r ⊆ Ω)
    (hu : MemLpLoc s ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) u) :
    MemLpLoc s (ball (x : ℂ) r) (TauCeti.planarReflection (higherReflectionCoeff 1) u) :=
  MemLpLoc.planarReflection (fun _ hz _ j => imDilation_higherReflectionNode_mem_ball x r j hz)
    (hu.mono_set (inter_subset_inter_left _ hΩ)) _

/-- **Local gain of integrability on half-discs.** For `p > 2` and `1 ≤ q ≤ p`, a map in
`W^{1,q}_loc(Ω ∩ {0 ≤ im})` with finite-dimensional values is in `Lʳ_loc(Ω ∩ {0 ≤ im})` for
`1/p + 1/r = 1/q`, with bounds up to the real axis. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple_halfPlane (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G}
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g := by
  refine halfPlane_of_open_of_ball (MemLpLoc r · g) memLpLoc_iff_locally
    (fun V hV => (hg.mono hV).memLpLoc_of_holderTriple hp hqp) fun x r hΩ => ?_
  exact memWkpLoc_zero_iff.1 <| MemWkpLoc.ball_inter_of_eq (k := 0)
    (memWkpLoc_zero_iff.2 <| MemWkpLoc.memLpLoc_of_holderTriple (Ω := ⟨_, isOpen_ball⟩) hp hqp
      (hg.reflect_one Fact.out hΩ)) fun z hz => planarReflection_of_nonneg _ _ hz

/-- **Order-zero mixed products on half-discs.** For `p > 2` and `1 ≤ q ≤ p`, the product of a
locally `Lᵖ` map with a `W^{1,q}_loc` map with finite-dimensional values on `Ω ∩ {0 ≤ im}` is
locally `L^q` there, with bounds up to the real axis. -/
theorem MemLpLoc.bilin_of_memWkpLoc_halfPlane (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G}
    (hf : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) f)
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (fun z => B (f z) (g z)) := by
  refine halfPlane_of_open_of_ball (MemLpLoc q · fun z => B (f z) (g z)) memLpLoc_iff_locally
    (fun V hV => (hf.mono_set hV).bilin_of_memWkpLoc B hp hqp (hg.mono hV)) fun x r hΩ => ?_
  exact memWkpLoc_zero_iff.1 <| MemWkpLoc.ball_inter_of_eq (k := 0)
    (memWkpLoc_zero_iff.2 <| MemLpLoc.bilin_of_memWkpLoc (Ω := ⟨_, isOpen_ball⟩) B hp hqp
      (hf.reflect hΩ) (hg.reflect_one Fact.out hΩ))
    fun z hz => by simp [planarReflection_of_nonneg _ _ hz]

/-- **Order-one mixed products on half-discs.** For `p > 2` and `1 < q ≤ p`, the product of a
locally bounded `W^{1,p}_loc` map with a `W^{1,q}_loc` map with finite-dimensional values on
`Ω ∩ {0 ≤ im}` is in `W^{1,q}_loc` there, with bounds up to the real axis. At `q = p` this is the
algebra property of `W^{1,p}_loc` on half-discs under continuous bilinear maps. -/
theorem MemWkpLoc.bilin_of_memLpLoc_top_halfPlane [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 f)
    (hfi : MemLpLoc ∞ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) f)
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 (fun z => B (f z) (g z)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have hp1 : (1 : ℝ≥0∞) ≤ p := hq1.trans (by exact_mod_cast hqp)
  refine halfPlane_of_open_of_ball (MemWkpLoc q · 1 fun z => B (f z) (g z)) memWkpLoc_iff_locally
    (fun V hV => (hf.mono hV).bilin_of_memLpLoc_top B hp hq hqp (hfi.mono_set hV) (hg.mono hV))
    fun x r hΩ => ?_
  exact MemWkpLoc.ball_inter_of_eq
    (MemWkpLoc.bilin_of_memLpLoc_top (Ω := ⟨_, isOpen_ball⟩) B hp hq hqp
      (hf.reflect_one hp1 hΩ) (hfi.reflect hΩ) (hg.reflect_one hq1 hΩ))
    fun z hz => by simp [planarReflection_of_nonneg _ _ hz]

/-- **Order-one mixed products on half-discs with finite-dimensional factors.** For `p > 2` and
`1 < q ≤ p`, the product of a `W^{1,p}_loc` map with a `W^{1,q}_loc` map on `Ω ∩ {0 ≤ im}`, both
with finite-dimensional values, is in `W^{1,q}_loc` there, with bounds up to the real axis. -/
theorem MemWkpLoc.bilin_halfPlane [FiniteDimensional ℝ F] [CompleteSpace H]
    (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 f)
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 (fun z => B (f z) (g z)) := by
  let _ : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le.trans hqp⟩
  exact hf.bilin_of_memLpLoc_top_halfPlane B hp hq hqp
    (hf.memLpLoc_of_holderTriple_halfPlane hp le_rfl) hg

end TauCeti
