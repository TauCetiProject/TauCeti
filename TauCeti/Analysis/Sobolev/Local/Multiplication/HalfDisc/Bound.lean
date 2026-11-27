/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ImDilation
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.Higher
import TauCeti.Analysis.Sobolev.Local.Reflection.Bound

/-!
# Local bounds for mixed-exponent products on half-discs

Let `p > 2`, `1 < q ≤ p` and let `Ω ⊆ ℂ` be open. Fix real normed spaces `F`, `G` and `H` with
`G` finite-dimensional. This file proves the local bounds that accompany the half-disc product
theorems of `TauCeti.Analysis.Sobolev.Local.Multiplication.HalfDisc` and its `Higher` companion,
with norms on the relatively open set `Ω⁺ = Ω ∩ {0 ≤ im}` of the closed upper half-plane. For a set
`U` whose closure is compact and contained in `Ω`, write `U⁺ = U ∩ {0 ≤ im}`. There is a constant
`C`, uniform in the continuous bilinear map `B : F × G → H` and in `f` and `g`, such that

* order zero, for `1 ≤ q ≤ p`:
  `‖B(f, g)‖_{L^q(U⁺)} ≤ C ‖B‖ ‖f‖_{Lᵖ(U⁺)} ‖g‖_{W^{1,q}(Ω⁺)}`;
* every positive order, for finite-dimensional `F` and complete `H`:
  `‖B(f, g)‖_{W^{k+1,q}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{k+1,p}(Ω⁺)} ‖g‖_{W^{k+1,q}(Ω⁺)}`,

together with the coefficient-field form `z ↦ A z (u z)` and the composition form
`z ↦ A z ∘L T z`. The bounds reach the real axis: `U` may meet it.

## Proof

The order-`k` higher reflection `TauCeti.planarReflection (higherReflectionCoeff k)` extends a map
on `Ω⁺` to the reflection core `Ω.reflectionCore`, an open set containing `Ω⁺`, with
`‖R u‖_{W^{k,p}(Ω.reflectionCore)} ≤ higherReflectionBound k p ‖u‖_{W^{k,p}(Ω⁺)}`
(`TauCeti.eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le`). The reflection
agrees with the map almost everywhere on `U⁺`
(`TauCeti.planarReflection_ae_eq_inter_setOf_im_nonneg`), so there `B(f, g)` agrees with
`B(R f, R g)`. The closure of `U⁺` is a compact subset of `Ω⁺`, hence of the reflection core
(`TopologicalSpace.Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore`), so the interior
bounds `TauCeti.exists_eLpNorm_bilin_le_eLpNormWkp_one` and
`TauCeti.exists_eLpNormWkp_succ_bilin_le` on the reflection core apply to `B(R f, R g)`, and the
reflection bound returns to `Ω⁺`.

## Main declarations

* `TauCeti.exists_bilin_le_halfPlane_of_reflectionCore`: product bounds on the reflection core
  give product bounds on half-discs.
* `TauCeti.exists_eLpNorm_bilin_le_eLpNormWkp_one_halfPlane`: the order-zero bound.
* `TauCeti.exists_eLpNormWkp_succ_bilin_le_halfPlane`: the bound at every positive order. At
  `q = p` it is the local bound for the algebra property of `W^{k+1,p}_loc(Ω⁺)`.
* `TauCeti.exists_eLpNormWkp_bilin_le_mul_eLpNormWkp_succ_halfPlane` and
  `TauCeti.exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ_halfPlane`: the bound of order `k`
  with a `W^{k+1,q}` factor, which loses no derivative of the `W^{k,p}` factor.
* `TauCeti.exists_eLpNormWkp_succ_clm_apply_le_halfPlane` and
  `TauCeti.exists_eLpNormWkp_succ_compL_le_halfPlane`: the coefficient-field and composition
  forms.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Proposition B.1.19.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, second edition, Theorem 5.19.
-/

public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Ω : Opens ℂ} {p q : ℝ≥0}

omit [FiniteDimensional ℝ G] in
/-- **Transfer of product bounds from the reflection core to half-discs.** Let `1 ≤ p`, `1 ≤ q`,
let `r` be an exponent and `a`, `b`, `c` orders, and let `U ⊆ ℂ`. Suppose that
`‖B(f, g)‖_{W^{c,r}(U ∩ {0 ≤ im})} ≤ C ‖B‖ ‖f‖_{W^{a,p}(Ω.reflectionCore)}
‖g‖_{W^{b,q}(Ω.reflectionCore)}` for every continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all
`f` and `g`. Then there is a constant `C'` with, for `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{W^{c,r}(U ∩ {0 ≤ im})} ≤ C' ‖B‖ ‖f‖_{W^{a,p}(Ω⁺)} ‖g‖_{W^{b,q}(Ω⁺)}`.
The proof applies the hypothesis to the higher reflections of `f` of order `a` and of `g` of order
`b`, which agree with `f` and `g` almost everywhere on `U ∩ {0 ≤ im}`
(`TauCeti.planarReflection_ae_eq_inter_setOf_im_nonneg`) and are controlled by
`TauCeti.eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le`. This turns the
interior product bounds, applied on the reflection core, into bounds on half-discs. -/
theorem exists_bilin_le_halfPlane_of_reflectionCore {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {a b c : ℕ} {U : Set ℂ} {C : ℝ≥0}
    (hC : ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) c (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p Ω.reflectionCore a f * eLpNormWkp q Ω.reflectionCore b g) :
    ∃ C' : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) c (fun z => B (f z) (g z)) ≤
        C' * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) a f *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) b g := by
  set Ma := higherReflectionBound a p
  set Mb := higherReflectionBound b q
  refine ⟨C * Ma.toNNReal * Mb.toNNReal, fun B f g => ?_⟩
  calc
    _ = eLpNormWkp r (U ∩ {z | 0 ≤ z.im}) c
          (fun z => B (planarReflection (higherReflectionCoeff a) f z)
            (planarReflection (higherReflectionCoeff b) g z)) :=
      eLpNormWkp_congr_ae ((planarReflection_ae_eq_inter_setOf_im_nonneg
        (higherReflectionCoeff a) f U).mp ((planarReflection_ae_eq_inter_setOf_im_nonneg
          (higherReflectionCoeff b) g U).mono fun z hg hf => by simp only [hf, hg]))
    _ ≤ C * ‖B‖ₑ *
          eLpNormWkp p Ω.reflectionCore a (planarReflection (higherReflectionCoeff a) f) *
          eLpNormWkp q Ω.reflectionCore b (planarReflection (higherReflectionCoeff b) g) :=
      hC B _ _
    _ ≤ C * ‖B‖ₑ * (Ma * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) a f) *
          (Mb * eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) b g) := by
      gcongr
      exacts [eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le hp f,
        eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le hq g]
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_toNNReal (higherReflectionBound_ne_top a p),
        ENNReal.coe_toNNReal (higherReflectionBound_ne_top b q)]
      ring

/-- **Local bound for order-zero mixed products on half-discs.** Fix real normed spaces `F`, `G`
and `H` with `G` finite-dimensional. For `p > 2`, `1 ≤ q ≤ p` and a set `U` whose closure is
compact and contained in `Ω`, there is a constant `C` such that
`‖B(f, g)‖_{L^q(U ∩ {0 ≤ im})} ≤ C ‖B‖ ‖f‖_{Lᵖ(U ∩ {0 ≤ im})} ‖g‖_{W^{1,q}(Ω ∩ {0 ≤ im})}` for every
continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. -/
theorem exists_eLpNorm_bilin_le_eLpNormWkp_one_halfPlane (hp : 2 < p) (hq : 1 ≤ q) (hqp : q ≤ p)
    {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNorm (fun z => B (f z) (g z)) q (volume.restrict (U ∩ {z | 0 ≤ z.im})) ≤
        C * ‖B‖ₑ * eLpNorm f p (volume.restrict (U ∩ {z | 0 ≤ z.im})) *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g := by
  have hUc : IsCompact (closure (U ∩ {z | 0 ≤ z.im})) :=
    hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  have hUcore := Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore hUΩ
  obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le_eLpNormWkp_one (F := F) (G := G) (H := H)
    (Ω := Ω.reflectionCore) hp hq hqp hUc hUcore
  set M := higherReflectionBound 1 q
  refine ⟨C * M.toNNReal, fun B f g => ?_⟩
  -- Reflect `g` across the real axis; on `U ∩ {0 ≤ im}` nothing changes.
  have hg := planarReflection_ae_eq_inter_setOf_im_nonneg (higherReflectionCoeff 1) g U
  calc
    _ = eLpNorm (fun z => B (f z) (planarReflection (higherReflectionCoeff 1) g z)) q
          (volume.restrict (U ∩ {z | 0 ≤ z.im})) :=
      eLpNorm_congr_ae (hg.mono fun z hz => by simp only [hz])
    _ ≤ C * ‖B‖ₑ * eLpNorm f p (volume.restrict (U ∩ {z | 0 ≤ z.im})) *
          eLpNormWkp q Ω.reflectionCore 1 (planarReflection (higherReflectionCoeff 1) g) :=
      hC B _ _
    _ ≤ C * ‖B‖ₑ * eLpNorm f p (volume.restrict (U ∩ {z | 0 ≤ z.im})) *
          (M * eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g) := by
      gcongr
      exact eLpNormWkp_planarReflection_higherReflectionCoeff_reflectionCore_le
        (by exact_mod_cast hq) g
    _ = ↑(C * M.toNNReal) * ‖B‖ₑ * eLpNorm f p (volume.restrict (U ∩ {z | 0 ≤ z.im})) *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 g := by
      rw [ENNReal.coe_mul, ENNReal.coe_toNNReal (higherReflectionBound_ne_top 1 q)]
      ring

variable [FiniteDimensional ℝ F]

/-- **Local bound for mixed-exponent products on half-discs at every positive order.** Fix real
normed spaces `F`, `G` and `H` with `F` and `G` finite-dimensional and `H` complete. For `p > 2`,
`1 < q ≤ p`, every `k` and a set `U` whose closure is compact and contained in `Ω`, there is a
constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{W^{k+1,q}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{k+1,p}(Ω⁺)} ‖g‖_{W^{k+1,q}(Ω⁺)}` for every
continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. This is the
bound that accompanies `TauCeti.MemWkpLoc.bilin_succ_halfPlane`; at `q = p` it is the local bound
for the algebra property of `W^{k+1,p}_loc(Ω ∩ {0 ≤ im})`. -/
theorem exists_eLpNormWkp_succ_bilin_le_halfPlane [CompleteSpace H] (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) f *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) g := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_bilin_le (F := F) (G := G) (H := H)
    (Ω := Ω.reflectionCore) hp hq hqp k
    (hU.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left))
    (Opens.closure_inter_setOf_im_nonneg_subset_reflectionCore hUΩ)
  have hq1 : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq.le
  exact exists_bilin_le_halfPlane_of_reflectionCore (hq1.trans (by exact_mod_cast hqp)) hq1 hC

/-- **Local bound for mixed-exponent products on half-discs with one derivative to spare.** Fix
real normed spaces `F`, `G` and `H` with `F` and `G` finite-dimensional and `H` complete. For
`p > 2`, `1 < q ≤ p`, every `k` and a set `U` whose closure is compact and contained in `Ω`, there
is a constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖B(f, g)‖_{W^{k,q}(U⁺)} ≤ C ‖B‖ ‖f‖_{W^{k,p}(Ω⁺)} ‖g‖_{W^{k+1,q}(Ω⁺)}` for every continuous
bilinear map `B : F →L[ℝ] G →L[ℝ] H` and all `f : ℂ → F` and `g : ℂ → G`. At `k = 0` the extra
derivative of `g` makes it integrable to the exponent conjugate to `p` relative to `q`. -/
theorem exists_eLpNormWkp_bilin_le_mul_eLpNormWkp_succ_halfPlane [CompleteSpace H] (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (f : ℂ → F) (g : ℂ → G),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) k (fun z => B (f z) (g z)) ≤
        C * ‖B‖ₑ * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k f *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) g := by
  cases k with
  | zero =>
    obtain ⟨C, hC⟩ := exists_eLpNorm_bilin_le_eLpNormWkp_one_halfPlane (F := F) (G := G) (H := H)
      hp hq.le hqp hU hUΩ
    refine ⟨C, fun B f g => ?_⟩
    rw [eLpNormWkp_zero, eLpNormWkp_zero]
    refine (hC B f g).trans ?_
    gcongr
    exact subset_closure.trans hUΩ
  | succ k =>
    obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_bilin_le_halfPlane (F := F) (G := G) (H := H) hp hq
      hqp k hU hUΩ
    exact ⟨C, fun B f g => (hC B f g).trans (by gcongr; exact eLpNormWkp_mono_order k.succ.le_succ)⟩

/-- **Local bound for coefficient fields on half-discs with one derivative to spare.** Fix
finite-dimensional real normed spaces `F` and `G`. For `p > 2`, `1 < q ≤ p`, every `k` and a set
`U` whose closure is compact and contained in `Ω`, there is a constant `C` such that, with
`U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖z ↦ A z (u z)‖_{W^{k,q}(U⁺)} ≤ C ‖A‖_{W^{k,p}(Ω⁺)} ‖u‖_{W^{k+1,q}(Ω⁺)}` for every coefficient
field `A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the half-disc form of
`TauCeti.exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ`. -/
theorem exists_eLpNormWkp_clm_apply_le_mul_eLpNormWkp_succ_halfPlane (hp : 2 < p) (hq : 1 < q)
    (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) k (fun z => A z (u z)) ≤
        C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k A *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_bilin_le_mul_eLpNormWkp_succ_halfPlane (F := F →L[ℝ] G)
    (G := F) (H := G) hp hq hqp k hU hUΩ
  exact ⟨C, fun A u => le_mul_mul_of_le_mul_eNorm_mul_mul ContinuousLinearMap.norm_id_le
    (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u)⟩

/-- **Local bound for coefficient fields on half-discs.** Fix finite-dimensional real normed spaces
`F` and `G`. For `p > 2`, `1 < q ≤ p`, every `k` and a set `U` whose closure is compact and
contained in `Ω`, there is a constant `C` such that, with `U⁺ = U ∩ {0 ≤ im}` and
`Ω⁺ = Ω ∩ {0 ≤ im}`, `‖z ↦ A z (u z)‖_{W^{k+1,q}(U⁺)} ≤ C ‖A‖_{W^{k+1,p}(Ω⁺)} ‖u‖_{W^{k+1,q}(Ω⁺)}`
for every coefficient field `A : ℂ → F →L[ℝ] G` and every `u : ℂ → F`. This is the bound that
accompanies `TauCeti.MemWkpLoc.clm_apply_succ_halfPlane`. -/
theorem exists_eLpNormWkp_succ_clm_apply_le_halfPlane (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → F →L[ℝ] G) (u : ℂ → F),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => A z (u z)) ≤
        C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_bilin_le_halfPlane (F := F →L[ℝ] G) (G := F) (H := G)
    hp hq hqp k hU hUΩ
  refine ⟨C, fun A u => (hC (ContinuousLinearMap.id ℝ (F →L[ℝ] G)) A u).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) u := by
      gcongr
      exact (ofReal_norm _).symm.trans_le (ENNReal.ofReal_le_one.2 ContinuousLinearMap.norm_id_le)
    _ = _ := by rw [mul_one]

/-- **Local bound for compositions of fields of linear maps on half-discs.** Fix finite-dimensional
real normed spaces `F`, `G` and `H`. For `p > 2`, `1 < q ≤ p`, every `k` and a set `U` whose
closure is compact and contained in `Ω`, there is a constant `C` such that, with
`U⁺ = U ∩ {0 ≤ im}` and `Ω⁺ = Ω ∩ {0 ≤ im}`,
`‖z ↦ A z ∘L T z‖_{W^{k+1,q}(U⁺)} ≤ C ‖A‖_{W^{k+1,p}(Ω⁺)} ‖T‖_{W^{k+1,q}(Ω⁺)}` for all fields
`A : ℂ → G →L[ℝ] H` and `T : ℂ → F →L[ℝ] G`. This is the bound that accompanies
`TauCeti.MemWkpLoc.compL_succ_halfPlane`. -/
theorem exists_eLpNormWkp_succ_compL_le_halfPlane [FiniteDimensional ℝ H] (hp : 2 < p)
    (hq : 1 < q) (hqp : q ≤ p) (k : ℕ) {U : Set ℂ} (hU : IsCompact (closure U))
    (hUΩ : closure U ⊆ Ω) :
    ∃ C : ℝ≥0, ∀ (A : ℂ → G →L[ℝ] H) (T : ℂ → F →L[ℝ] G),
      eLpNormWkp q (U ∩ {z | 0 ≤ z.im}) (k + 1) (fun z => (A z).comp (T z)) ≤
        C * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) T := by
  obtain ⟨C, hC⟩ := exists_eLpNormWkp_succ_bilin_le_halfPlane (F := G →L[ℝ] H)
    (G := F →L[ℝ] G) (H := F →L[ℝ] H) hp hq hqp k hU hUΩ
  refine ⟨C, fun A T => (hC (ContinuousLinearMap.compL ℝ F G H) A T).trans ?_⟩
  calc
    _ ≤ C * 1 * eLpNormWkp p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) A *
          eLpNormWkp q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (k + 1) T := by
      gcongr
      exact (ofReal_norm _).symm.trans_le
        (ENNReal.ofReal_le_one.2 (ContinuousLinearMap.norm_compL_le ℝ F G H))
    _ = _ := by rw [mul_one]

end TauCeti
