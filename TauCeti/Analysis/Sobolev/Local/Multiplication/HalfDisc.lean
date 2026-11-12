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

Near a boundary point of a pseudoholomorphic curve with boundary, the curve is modelled on a
half-disc, and elliptic bootstrapping must control nonlinear terms that are bilinear in the map
and its derivatives, in local Sobolev classes whose bounds reach the real axis. These theorems
supply that control: a product of an `Lᵖ_loc` factor with a `W^{1,q}_loc` factor stays in
`L^q_loc`, and a product of `W^{1,p}_loc` and `W^{1,q}_loc` factors stays in `W^{1,q}_loc`, all up
to the boundary. For finite-dimensional factors and `q = p`, `W^{1,p}_loc` on half-discs is closed
under continuous bilinear maps, such as multiplication of matrix-valued maps.

## Main declarations

* `TauCeti.MemWkpLoc.memLpLoc_of_holderTriple_halfPlane`: the local gain of integrability
  `W^{1,q} ⊂ Lʳ` with `1/p + 1/r = 1/q`.
* `TauCeti.MemLpLoc.bilin_of_memWkpLoc_halfPlane`: order zero, `Lᵖ · W^{1,q} ⊂ L^q`.
* `TauCeti.MemWkpLoc.bilin_of_memLpLoc_top_halfPlane` and `TauCeti.MemWkpLoc.bilin_halfPlane`:
  order one, `W^{1,p} · W^{1,q} ⊂ W^{1,q}`. At `q = p` this is the algebra property of
  `W^{1,p}_loc` on half-discs.

## Implementation notes

Near a point of the real axis, both factors on a disc centred on the axis are extended across the
axis by the even reflection, `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`, the
interior theorem is applied on the disc, and the result is restricted back to the half-disc by
`TauCeti.MemWkpLoc.congr_mono`, since the reflection agrees with the original map there. Near a
point off the axis the interior theorem applies directly. `TauCeti.inter_setOf_im_nonneg_induction`
glues the two cases.

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

/-- **Local gain of integrability on half-discs.** For `p > 2` and `1 ≤ q ≤ p`, a map in
`W^{1,q}_loc(Ω ∩ {0 ≤ im})` with finite-dimensional values is in `Lʳ_loc(Ω ∩ {0 ≤ im})` for
`1/p + 1/r = 1/q`, with bounds up to the real axis. -/
theorem MemWkpLoc.memLpLoc_of_holderTriple_halfPlane (hp : 2 < p) (hqp : q ≤ p)
    [Fact (1 ≤ (q : ℝ≥0∞))] {r : ℝ≥0∞} [ENNReal.HolderTriple p r q] {g : ℂ → G}
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemLpLoc r ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) g := by
  refine inter_setOf_im_nonneg_induction (MemLpLoc r · g) memLpLoc_iff_locally.2
    (fun V hV => (hg.mono hV).memLpLoc_of_holderTriple hp hqp) fun x r hΩ => ?_
  exact memWkpLoc_zero_iff.1 <| MemWkpLoc.congr_mono (k := 0)
    (memWkpLoc_zero_iff.2 <| MemWkpLoc.memLpLoc_of_holderTriple (Ω := ⟨_, isOpen_ball⟩) hp hqp
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball Fact.out x r
        (hg.mono (inter_subset_inter_left _ hΩ))))
    (fun z hz => (planarReflection_of_nonneg _ _ hz.2).symm) inter_subset_left

/-- **Order-zero mixed products on half-discs.** For `p > 2` and `1 ≤ q ≤ p`, the product of a
locally `Lᵖ` map with a `W^{1,q}_loc` map with finite-dimensional values on `Ω ∩ {0 ≤ im}` is
locally `L^q` there, with bounds up to the real axis. -/
theorem MemLpLoc.bilin_of_memWkpLoc_halfPlane (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hqp : q ≤ p) [Fact (1 ≤ (q : ℝ≥0∞))] {f : ℂ → F} {g : ℂ → G}
    (hf : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) f)
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) :
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (fun z => B (f z) (g z)) := by
  refine inter_setOf_im_nonneg_induction (MemLpLoc q · fun z => B (f z) (g z))
    memLpLoc_iff_locally.2
    (fun V hV => (hf.mono_set hV).bilin_of_memWkpLoc B hp hqp (hg.mono hV)) fun x r hΩ => ?_
  exact memWkpLoc_zero_iff.1 <| MemWkpLoc.congr_mono (k := 0)
    (memWkpLoc_zero_iff.2 <| MemLpLoc.bilin_of_memWkpLoc (Ω := ⟨_, isOpen_ball⟩) B hp hqp
      ((hf.mono_set (inter_subset_inter_left _ hΩ)).planarReflection_ball x r
        (higherReflectionCoeff 1))
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball Fact.out x r
        (hg.mono (inter_subset_inter_left _ hΩ))))
    (fun z hz => by simp [planarReflection_of_nonneg _ _ hz.2]) inter_subset_left

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
  refine inter_setOf_im_nonneg_induction (MemWkpLoc q · 1 fun z => B (f z) (g z))
    memWkpLoc_iff_locally.2
    (fun V hV => (hf.mono hV).bilin_of_memLpLoc_top B hp hq hqp (hfi.mono_set hV) (hg.mono hV))
    fun x r hΩ => ?_
  exact MemWkpLoc.congr_mono
    (MemWkpLoc.bilin_of_memLpLoc_top (Ω := ⟨_, isOpen_ball⟩) B hp hq hqp
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
        (hf.mono (inter_subset_inter_left _ hΩ)))
      ((hfi.mono_set (inter_subset_inter_left _ hΩ)).planarReflection_ball x r
        (higherReflectionCoeff 1))
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hq1 x r
        (hg.mono (inter_subset_inter_left _ hΩ))))
    (fun z hz => by simp [planarReflection_of_nonneg _ _ hz.2]) inter_subset_left

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
