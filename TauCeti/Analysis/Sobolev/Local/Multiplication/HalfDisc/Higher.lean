/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Reflection

/-!
# Mixed-exponent products of local Sobolev maps on half-discs at every order

Let `p > 2`, `1 < q ≤ p` and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. For every `i ≥ 1`, if `f ∈ W^{i,p}_loc` and `g ∈ W^{i,q}_loc` on the
relatively open set `Ω ∩ {0 ≤ im}` of the closed upper half-plane, then
`B(f, g) ∈ W^{i,q}_loc(Ω ∩ {0 ≤ im})`, with bounds up to the real axis. At `q = p` this is the
algebra property of `W^{i,p}_loc` on half-discs under continuous bilinear maps. This carries
`TauCeti.MemWkpLoc.bilin_succ` from open planar domains to half-discs; the order-one case is
`TauCeti.MemWkpLoc.bilin_halfPlane`.

Near a boundary point of a pseudoholomorphic curve with boundary, the curve is modelled on a
half-disc, and the boundary bootstrap multiplies the map and its derivatives by coefficient
fields in the same local Sobolev classes, up to the real axis.

## Main declarations

* `TauCeti.MemWkpLoc.bilin_succ_halfPlane`: mixed-exponent products at every positive order.
* `TauCeti.MemWkpLoc.clm_apply_succ_halfPlane`: the field form `z ↦ A z (u z)`.
* `TauCeti.MemWkpLoc.compL_succ_halfPlane`: the composition form `z ↦ A z ∘L C z`.

## Implementation notes

Near a point of the real axis, both factors on a disc centred on the axis are extended across the
axis by the higher-order reflection of the same order,
`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`, the interior theorem is applied on
the disc, and the result is restricted back to the half-disc by `TauCeti.MemWkpLoc.congr_mono`,
since the reflection agrees with the original map there. Near a point off the axis the interior
theorem applies directly. `TauCeti.inter_setOf_im_nonneg_induction` glues the two cases.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
-/

public noncomputable section

open Set TopologicalSpace Metric
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

/-- **Mixed-exponent products on half-discs at every positive order.** For `p > 2` and
`1 < q ≤ p`, the product of a `W^{k+1,p}_loc` map with a `W^{k+1,q}_loc` map on `Ω ∩ {0 ≤ im}`,
both with finite-dimensional values, is in `W^{k+1,q}_loc` there, with bounds up to the real
axis. At `q = p` this is the algebra property of `W^{k+1,p}_loc` on half-discs under continuous
bilinear maps. -/
theorem MemWkpLoc.bilin_succ_halfPlane [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) {k : ℕ} {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) f)
    (hg : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) g) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => B (f z) (g z)) := by
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  have hp1 : (1 : ℝ≥0∞) ≤ p := hq1.trans (by exact_mod_cast hqp)
  refine inter_setOf_im_nonneg_induction (MemWkpLoc q · (k + 1) fun z => B (f z) (g z))
    memWkpLoc_iff_locally.2
    ((hf.mono Ω.coe_upperHalf_subset).bilin_succ B hp hq hqp (hg.mono Ω.coe_upperHalf_subset))
    fun x r _ hΩ => ?_
  exact MemWkpLoc.congr_mono
    (MemWkpLoc.bilin_succ (Ω := ⟨_, isOpen_ball⟩) B hp hq hqp
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
        (hf.mono (inter_subset_inter_left _ hΩ)))
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hq1 x r
        (hg.mono (inter_subset_inter_left _ hΩ))))
    (fun z hz => by simp [planarReflection_of_nonneg _ _ hz.2]) inter_subset_left

/-- **Coefficient fields acting on local Sobolev maps on half-discs.** For `p > 2` and
`1 < q ≤ p`, a coefficient field `A ∈ W^{k+1,p}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] G)` applied to a map
`u ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ im}; F)` gives `z ↦ A z (u z) ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ im}; G)`. -/
theorem MemWkpLoc.clm_apply_succ_halfPlane (hp : 2 < p) (hq : 1 < q) (hqp : q ≤ p) {k : ℕ}
    {A : ℂ → F →L[ℝ] G} {u : ℂ → F}
    (hA : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A)
    (hu : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => A z (u z)) :=
  hA.bilin_succ_halfPlane (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) hp hq hqp hu

/-- **Composition of local Sobolev fields of linear maps on half-discs.** For `p > 2` and
`1 < q ≤ p`, if `A ∈ W^{k+1,p}_loc(Ω ∩ {0 ≤ im}; G →L[ℝ] H)` and
`C ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] G)`, then
`z ↦ A z ∘L C z ∈ W^{k+1,q}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] H)`. -/
theorem MemWkpLoc.compL_succ_halfPlane [FiniteDimensional ℝ H] (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) {k : ℕ} {A : ℂ → G →L[ℝ] H} {C : ℂ → F →L[ℝ] G}
    (hA : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A)
    (hC : MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) C) :
    MemWkpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => (A z).comp (C z)) :=
  hA.bilin_succ_halfPlane (ContinuousLinearMap.compL ℝ F G H) hp hq hqp hC

end TauCeti
