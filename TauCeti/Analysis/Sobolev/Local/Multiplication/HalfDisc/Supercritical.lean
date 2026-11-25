/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Multiplication.Supercritical
import TauCeti.Analysis.Sobolev.Local.Reflection

/-!
# Products of local Sobolev maps on half-discs for `kp > 2`, including `p ≤ 2`

Let `1 < p` and `k p > 2`, and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. If `f` and `g` are in `W^{k,p}_loc` on the relatively open set
`Ω ∩ {0 ≤ im}` of the closed upper half-plane, then so is `B(f, g)`. This carries
`TauCeti.MemWkpLoc.bilin_of_two_lt_mul` from open planar domains to half-discs; for `p > 2` it is
`TauCeti.MemWkpLoc.bilin_succ_halfPlane` at `q = p`.

This is the diagonal case of a statement with three orders, as in the interior. Near a point of
the real axis both factors are extended across the axis by the higher reflections of their own
orders `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`, the interior theorem
is applied on a disc centred on the axis, and the result is restricted back, since the reflection
agrees with the map on `{0 ≤ im}`. Near a point off the axis the interior theorem applies
directly. `TauCeti.inter_setOf_im_nonneg_induction` glues the two cases.

## Main declarations

* `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul_halfPlane`: `B(f, g) ∈ W^{c,p}_loc` on half-discs
  for `f ∈ W^{a,p}_loc`, `g ∈ W^{b,p}_loc` and `(a + b - c) p > 2`.
* `TauCeti.MemWkpLoc.bilin_of_two_lt_mul_halfPlane`: the algebra property of `W^{k,p}_loc` on
  half-discs for `kp > 2`.
* `TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul_halfPlane` and
  `TauCeti.MemWkpLoc.compL_of_two_lt_mul_halfPlane`: the field and composition forms.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
-/

public noncomputable section

open Set TopologicalSpace Metric
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ}

/-- **Products on half-discs with three orders.** Let `1 < p`, let
`f ∈ W^{a,p}_loc(Ω ∩ {0 ≤ im}, F)` and `g ∈ W^{b,p}_loc(Ω ∩ {0 ≤ im}, G)`, and let `c ≤ a`,
`c ≤ b` with `(a + b - c) p > 2`. Then `B(f, g)` is in `W^{c,p}_loc(Ω ∩ {0 ≤ im}, H)`, with bounds
up to the real axis. Near the axis `f` and `g` are reflected with their own orders `a` and `b`. -/
theorem MemWkpLoc.bilin_of_two_lt_add_sub_mul_halfPlane [CompleteSpace H]
    (B : F →L[ℝ] G →L[ℝ] H) {p : ℝ≥0} (hp : 1 < p) {a b c : ℕ} {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) a f)
    (hg : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) b g) (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) c (fun z => B (f z) (g z)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  refine inter_setOf_im_nonneg_induction (MemWkpLoc p · c fun z => B (f z) (g z))
    memWkpLoc_iff_locally.2
    ((hf.mono Ω.coe_upperHalf_subset).bilin_of_two_lt_add_sub_mul B hp
      (hg.mono Ω.coe_upperHalf_subset) hca hcb habc)
    fun x r _ hΩ => ?_
  exact MemWkpLoc.congr_mono
    (MemWkpLoc.bilin_of_two_lt_add_sub_mul (Ω := ⟨_, isOpen_ball⟩) B hp
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
        (hf.mono (inter_subset_inter_left _ hΩ)))
      (MemWkpLoc.planarReflection_higherReflectionCoeff_ball hp1 x r
        (hg.mono (inter_subset_inter_left _ hΩ))) hca hcb habc)
    (fun z hz => by simp [planarReflection_of_nonneg _ _ hz.2]) inter_subset_left

/-- **The algebra property on half-discs for `kp > 2`.** Let `1 < p` and `k p > 2`. For
`f ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}, F)` and `g ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}, G)`, the product `B(f, g)`
is in `W^{k,p}_loc(Ω ∩ {0 ≤ im}, H)`, with bounds up to the real axis. This includes `p ≤ 2` for
`k ≥ 2`. -/
theorem MemWkpLoc.bilin_of_two_lt_mul_halfPlane [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H)
    {p : ℝ≥0} (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k f)
    (hg : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k g) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => B (f z) (g z)) :=
  hf.bilin_of_two_lt_add_sub_mul_halfPlane B hp hg le_rfl le_rfl (by rwa [Nat.add_sub_cancel])

/-- **Coefficient fields on half-discs for `kp > 2`.** Let `1 < p` and `k p > 2`. A coefficient
field `A ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] G)` applied to `u ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; F)`
gives `z ↦ A z (u z) ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; G)`. -/
theorem MemWkpLoc.clm_apply_of_two_lt_mul_halfPlane {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {A : ℂ → F →L[ℝ] G} {u : ℂ → F}
    (hA : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k A)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => A z (u z)) :=
  hA.bilin_of_two_lt_mul_halfPlane (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) hp hkp hu

/-- **Composition of fields of linear maps on half-discs for `kp > 2`.** Let `1 < p` and
`k p > 2`. If `A ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; G →L[ℝ] H)` and
`C ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] G)`, then
`z ↦ A z ∘L C z ∈ W^{k,p}_loc(Ω ∩ {0 ≤ im}; F →L[ℝ] H)`. -/
theorem MemWkpLoc.compL_of_two_lt_mul_halfPlane [FiniteDimensional ℝ H] {p : ℝ≥0} (hp : 1 < p)
    {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {A : ℂ → G →L[ℝ] H} {C : ℂ → F →L[ℝ] G}
    (hA : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k A)
    (hC : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k C) :
    MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k (fun z => (A z).comp (C z)) :=
  hA.bilin_of_two_lt_mul_halfPlane (ContinuousLinearMap.compL ℝ F G H) hp hkp hC

/-- The check at `p = 4/3` and `k = 2` on half-discs: `kp = 8/3 > 2` while `p < 2`, outside the
range of `TauCeti.MemWkpLoc.bilin_succ_halfPlane`. -/
example [CompleteSpace H] (B : F →L[ℝ] G →L[ℝ] H) {f : ℂ → F} {g : ℂ → G}
    (hf : MemWkpLoc (4 / 3 : ℝ≥0) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 2 f)
    (hg : MemWkpLoc (4 / 3 : ℝ≥0) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 2 g) :
    MemWkpLoc (4 / 3 : ℝ≥0) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 2 (fun z => B (f z) (g z)) :=
  hf.bilin_of_two_lt_mul_halfPlane B (by norm_num) (by norm_num) hg

end TauCeti
