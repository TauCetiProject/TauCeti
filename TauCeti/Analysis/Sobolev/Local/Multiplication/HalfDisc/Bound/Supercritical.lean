/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Supercritical
import TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Bound

/-!
# Local bounds for products on half-discs for `kp > 2`, including `p ≤ 2`

Let `Ω ⊆ ℂ` be open, let `1 < p` and let `B : F × G → H` be continuous bilinear with `F` and `G`
finite-dimensional. This file proves the local bounds that accompany the half-disc membership
theorems of `TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc.Supercritical`, with norms on
the relatively open set `Ω⁺ = Ω ∩ {0 ≤ im}` of the closed upper half-plane. For a set `U` whose
closure is compact and contained in `Ω`, write `U⁺ = U ∩ {0 ≤ im}`. There is a constant `C`,
uniform in `B`, `f` and `g`, such that

`‖B(f, g)‖_{W^{c,p}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω⁺)} ‖g‖_{W^{b,p}(Ω⁺)}`

for `c ≤ a`, `c ≤ b` and `(a + b - c) p > 2`. The bounds reach the real axis: `U` may meet it.
For `p > 2` the equal-order case is also covered by
`TauCeti.exists_eLpNormWkp_succ_bilin_le_halfPlane`; the point here is the range `p ≤ 2`.

## Proof

The closure of `U⁺` is a compact subset of the reflection core `Ω.reflectionCore`, an open set
containing `Ω⁺` (`TopologicalSpace.Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore`), so
the interior bounds `TauCeti.exists_eLpNorm_bilin_le_of_two_lt_add_mul` and
`TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul` apply on the reflection core.
`TauCeti.exists_bilin_le_halfPlane_of_reflectionCore` turns them into bounds on half-discs, by
extending each factor with the higher reflection of its own order: `f` with order `a` and `g` with
order `b`.

## Main declarations

* `TauCeti.exists_eLpNorm_bilin_le_of_two_lt_add_mul_halfPlane` and
  `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul_halfPlane`: the local bounds on
  half-discs for products with `(a + b) p > 2` and `(a + b - c) p > 2`.
* `TauCeti.exists_eLpNormWkp_bilin_le_of_two_lt_mul_halfPlane`,
  `TauCeti.exists_eLpNormWkp_clm_apply_le_of_two_lt_mul_halfPlane` and
  `TauCeti.exists_eLpNormWkp_compL_le_of_two_lt_mul_halfPlane`: the local bounds for the algebra
  property of `W^{k,p}_loc(Ω⁺)` for `kp > 2`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, second edition, Theorem 4.39.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ}

/-- **Local bound for products in `Lᵖ` on half-discs.** Let `1 ≤ p` and `(a + b) p > 2`, and let
`U` have compact closure contained in `Ω`. There is a constant `C` such that, with
`U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{Lᵖ(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω⁺)} ‖g‖_{W^{b,p}(Ω⁺)}` for every continuous bilinear
map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. -/
theorem exists_eLpNorm_bilin_le_of_two_lt_add_mul_halfPlane {p : ℝ≥0} (hp : 1 ≤ p) {a b : ℕ}
    (hab : 2 < ((a + b : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) p (volume.restrict (U ∩ {z | 0 ≤ z.im})) ≤
        C * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) a f *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) b g := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le_of_two_lt_add_mul (F := F) (G := G) (H := H)
    (Ω := Ω.reflectionCore) hp hab
    (hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore hUΩ)
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp
  obtain ⟨C', hC'⟩ := exists_bilin_le_halfPlane_of_reflectionCore (c := 0) hp1 hp1
    fun B f g => by simpa only [eLpNormWkp_zero] using hC B f g
  exact ⟨C', fun B f g => by simpa only [eLpNormWkp_zero] using hC' B f g⟩

/-- **Local bound for products on half-discs with three orders.** Let `1 < p`, let `c ≤ a`,
`c ≤ b` with `(a + b - c) p > 2`, and let `U` have compact closure contained in `Ω`. There is a
constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{W^{c,p}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω⁺)} ‖g‖_{W^{b,p}(Ω⁺)}` for every continuous
bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the bound that
accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_add_sub_mul_halfPlane`. -/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul_halfPlane [CompleteSpace H] {p : ℝ≥0}
    (hp : 1 < p) {a b c : ℕ} (hca : c ≤ a) (hcb : c ≤ b)
    (habc : 2 < ((a + b - c : ℕ) : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) c (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) a f *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) b g := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul (F := F) (G := G) (H := H)
    (Ω := Ω.reflectionCore) hp hca hcb habc
    (hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore hUΩ)
  have hp1 : (1 : ℝ≥0∞) ≤ p := by exact_mod_cast hp.le
  exact exists_bilin_le_halfPlane_of_reflectionCore hp1 hp1 hC

/-- **Local bound for the algebra property on half-discs for `kp > 2`.** Let `1 < p` and
`k p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C` such that,
with `U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{W^{k,p}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{k,p}(Ω⁺)} ‖g‖_{W^{k,p}(Ω⁺)}` for every continuous
bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This includes `p ≤ 2`
for `k ≥ 2`, and is the bound that accompanies `TauCeti.MemWkpLoc.bilin_of_two_lt_mul_halfPlane`.
-/
theorem exists_eLpNormWkp_bilin_le_of_two_lt_mul_halfPlane [CompleteSpace H] {p : ℝ≥0}
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) k (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k f *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_add_sub_mul_halfPlane hp le_rfl le_rfl
    (by rwa [Nat.add_sub_cancel]) hU hUΩ

/-- **Local bound for coefficient fields on half-discs for `kp > 2`.** Let `1 < p` and `k p > 2`,
and let `U` have compact closure contained in `Ω`. There is a constant `C` such that, with
`U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖z ↦ A z (u z)‖_{W^{k,p}(U⁺)} ≤ C ‖A‖_{W^{k,p}(Ω⁺)} ‖u‖_{W^{k,p}(Ω⁺)}` for every coefficient
field `A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the bound that accompanies
`TauCeti.MemWkpLoc.clm_apply_of_two_lt_mul_halfPlane`. -/
theorem exists_eLpNormWkp_clm_apply_le_of_two_lt_mul_halfPlane {p : ℝ≥0} (hp : 1 < p) {k : ℕ}
    (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) k (fun z => A z (u z)) ≤
        C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k A *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul_halfPlane (F := F →L[ℝ] G) (G := F)
    (H := G) hp hkp hU hUΩ
  exact ⟨C, fun A u => le_mul_mul_of_le_mul_eNorm_mul_mul ContinuousLinearMap.norm_id_le
    (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u)⟩

/-- **Local bound for compositions of fields of linear maps on half-discs for `kp > 2`.** Let
`1 < p` and `k p > 2`, and let `U` have compact closure contained in `Ω`. There is a constant `C`
such that, with `U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖z ↦ A z ∘L T z‖_{W^{k,p}(U⁺)} ≤ C ‖A‖_{W^{k,p}(Ω⁺)} ‖T‖_{W^{k,p}(Ω⁺)}` for all fields
`A : ℂ → G →L[ℝ] H` and `T : ℂ → F →L[ℝ] G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.compL_of_two_lt_mul_halfPlane`. -/
theorem exists_eLpNormWkp_compL_le_of_two_lt_mul_halfPlane [FiniteDimensional ℝ H] {p : ℝ≥0}
    (hp : 1 < p) {k : ℕ} (hkp : 2 < (k : ℝ≥0) * p) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → G →L[ℝ] H) (T : ℂ → F →L[ℝ] G),
      eLpNormWkp p (U ∩ {z | 0 ≤ z.im}) k (fun z => (A z).comp (T z)) ≤
        C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k A *
          eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k T := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_of_two_lt_mul_halfPlane (F := G →L[ℝ] H)
    (G := F →L[ℝ] G) (H := F →L[ℝ] H) hp hkp hU hUΩ
  exact ⟨C, fun A T => le_mul_mul_of_le_mul_eNorm_mul_mul
    (ContinuousLinearMap.norm_compL_le ℝ F G H) (hC (ContinuousLinearMap.compL ℝ F G H) A T)⟩

/-- The bound at `p = 4/3` and `k = 2`, where `kp = 8/3 > 2` while `p < 2`: on the upper half of
the disc of radius `1/2`, up to the real axis, the `W^{2,4/3}` norm of a product is controlled by
the norms of the factors on the upper half of the unit disc. -/
example [CompleteSpace H] :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) (1 / 2) ∩ {z | 0 ≤ z.im}) 2
          (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 2 f *
          eLpNormWkp (4 / 3 : ℝ≥0) (Metric.ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 2 g :=
  exists_eLpNormWkp_bilin_le_of_two_lt_mul_halfPlane
    (Ω := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩) (by norm_num) (by norm_num)
    ((isCompact_closedBall 0 (1 / 2)).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall)
    (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num)))

end TauCeti
