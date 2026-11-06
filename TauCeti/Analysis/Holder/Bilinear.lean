/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Normed
public import TauCeti.Analysis.Normed.Operator.Holder
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuous bilinear operations on Hölder spaces

A continuous bilinear map `B : E →L[ℝ] F →L[ℝ] G` acts pointwise on bounded Hölder functions.
The resulting bilinear map has norm at most `‖B‖`, and exactly `‖B‖` on a nonempty domain.
This supplies multiplication and scalar multiplication in Hölder spaces with the usual
supremum-plus-Hölder norm, without replacing the existing space or its norm. When the second
factor vanishes off a set on which the first is small, the first factor enters the norm of the
product only through that bound and its Hölder seminorm
(`ContinuousLinearMap.norm_compHolder₂_apply_le_of_eq_zero`).

If the second factor `f` vanishes off a set `s`, the first factor need only be a Hölder function
`g` on `s`: the function equal to `B (g x) (f x)` on `s` and to zero off `s` is Hölder on the whole
space and vanishes off `s`. This gives a bounded operator
`ContinuousLinearMap.compHolder₂ExtendByZero` from Hölder functions on `s` to the Hölder
functions supported in `s`, of norm at most `‖B‖ * ‖f‖`; it is how a coefficient supported in a
disc multiplies a function known only on that disc.

The construction generalizes the scalar-multiplication operator `boundedHolderSpaceSmu` in
[DifferentialGeometry, Holder/Bilinear.lean](https://github.com/qinz1yang/differential-geometry/blob/7a48598d35109aa99d1cc678e2724c213cdf4ff3/DifferentialGeometry/Analysis/Schauder/Holder/Bilinear.lean).
Keeping the supremum and Hölder terms separate improves its factor `3` to `1`.
-/

public section

noncomputable section

open scoped NNReal BoundedContinuousFunction
open TauCeti

namespace ContinuousLinearMap

variable {X E F G : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ≥0}

private def holderBilinear (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) : HolderSpace α X G :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup (fun x ↦ B (f x) (g x))
      ((B.continuous.comp f.continuous).clm_apply g.continuous)
      (‖B‖ * ‖f.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
      (fun x ↦ (B.le_opNorm₂ _ _).trans (by
        gcongr
        · simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x
        · simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x)))
    (by
      simpa using (B.holderWith_comp₂
        (Mf := ‖f.toBoundedContinuousFunction‖₊) (Mg := ‖g.toBoundedContinuousFunction‖₊)
        f.memHolder.holderWith g.memHolder.holderWith
        f.toBoundedContinuousFunction.norm_coe_le_norm
        g.toBoundedContinuousFunction.norm_coe_le_norm).memHolder)

private theorem holderBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) (x : X) :
    holderBilinear B f g x = B (f x) (g x) := by
  simp [holderBilinear]

private theorem norm_holderBilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) :
    ‖holderBilinear B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  have hsup : ‖(holderBilinear B f g).toBoundedContinuousFunction‖ ≤
      ‖B‖ * ‖f.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_apply, holderBilinear_apply]
    exact (B.le_opNorm₂ _ _).trans (by
      gcongr
      · simpa using f.toBoundedContinuousFunction.norm_coe_le_norm x
      · simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x)
  have hholder := B.holderWith_comp₂
    (Mf := ‖f.toBoundedContinuousFunction‖₊) (Mg := ‖g.toBoundedContinuousFunction‖₊)
    f.memHolder.holderWith g.memHolder.holderWith
    f.toBoundedContinuousFunction.norm_coe_le_norm
    g.toBoundedContinuousFunction.norm_coe_le_norm
  have hsemi : (nnHolderNorm α
      ((holderBilinear B f g).toBoundedContinuousFunction : X → G) : ℝ) ≤
      ‖B‖ * (‖f.toBoundedContinuousFunction‖ * nnHolderNorm α (g : X → F) +
        ‖g.toBoundedContinuousFunction‖ * nnHolderNorm α (f : X → E)) := by
    have heq : ((holderBilinear B f g).toBoundedContinuousFunction : X → G) =
        fun x ↦ B (f x) (g x) := by
      funext x
      rw [HolderSpace.toBoundedContinuousFunction_apply, holderBilinear_apply]
    rw [heq]
    exact_mod_cast (by simpa using hholder.nnholderNorm_le :
      nnHolderNorm α (fun x ↦ B (f x) (g x)) ≤
        ‖B‖₊ * (‖f.toBoundedContinuousFunction‖₊ * nnHolderNorm α (g : X → F) +
          ‖g.toBoundedContinuousFunction‖₊ * nnHolderNorm α (f : X → E)))
  have htotal := add_le_add hsup hsemi
  simp only [HolderSpace.coe_toBoundedContinuousFunction] at htotal
  simp only [HolderSpace.norm_def, HolderSpace.coe_toBoundedContinuousFunction]
  nlinarith [mul_nonneg (norm_nonneg B)
    (mul_nonneg (NNReal.coe_nonneg (nnHolderNorm α (f : X → E)))
      (NNReal.coe_nonneg (nnHolderNorm α (g : X → F))))]

private def holderBilinearLinear (B : E →L[ℝ] F →L[ℝ] G) :
    HolderSpace α X E →ₗ[ℝ] HolderSpace α X F →ₗ[ℝ] HolderSpace α X G :=
  LinearMap.mk₂ ℝ (holderBilinear B)
    (fun f₁ f₂ g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun c f g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun f g₁ g₂ ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])
    (fun c f g ↦ HolderSpace.ext fun x ↦ by
      simp [holderBilinear_apply])

/-- Pointwise application of a continuous bilinear map as a continuous bilinear map of
bounded Hölder spaces. -/
def compHolder₂ (B : E →L[ℝ] F →L[ℝ] G) :
    HolderSpace α X E →L[ℝ] HolderSpace α X F →L[ℝ] HolderSpace α X G :=
  (holderBilinearLinear B).mkContinuous₂ ‖B‖ (norm_holderBilinear_le B)

@[simp]
theorem compHolder₂_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : HolderSpace α X E) (g : HolderSpace α X F) (x : X) :
    B.compHolder₂ f g x = B (f x) (g x) := by
  simp [compHolder₂, holderBilinearLinear, holderBilinear_apply]

/-- Pointwise lifting to Hölder functions does not increase a bilinear map's operator norm. -/
theorem norm_compHolder₂_le (B : E →L[ℝ] F →L[ℝ] G) :
    ‖B.compHolder₂ (α := α) (X := X)‖ ≤ ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (norm_nonneg B) _

/-- The values of a lifted bilinear map are bounded by the norms of the map and its inputs. -/
theorem norm_compHolder₂_apply_le (B : E →L[ℝ] F →L[ℝ] G) (f : HolderSpace α X E)
    (g : HolderSpace α X F) : ‖B.compHolder₂ f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ :=
  (B.compHolder₂.le_opNorm₂ f g).trans (by gcongr; exact B.norm_compHolder₂_le)

/-- Pointwise application of a Hölder field of continuous linear maps to a Hölder function is
bounded by the product of their norms. -/
theorem norm_id_compHolder₂_apply_le (f : HolderSpace α X (F →L[ℝ] G)) (g : HolderSpace α X F) :
    ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] G)).compHolder₂ f g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_compHolder₂_apply_le _ f g).trans (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg f) ContinuousLinearMap.norm_id_le) (norm_nonneg g))

/-- If `g` vanishes off a set `s` on which `‖f‖ ≤ δ`, then `f` enters the norm of the product only
through `δ` and its Hölder seminorm: `‖B (f, g)‖ ≤ ‖B‖ (δ ‖g‖ + [f]_α ‖g‖_∞)`. This is the
estimate for freezing a coefficient field on the support of a localized function. -/
theorem norm_compHolder₂_apply_le_of_eq_zero (B : E →L[ℝ] F →L[ℝ] G) (f : HolderSpace α X E)
    (g : HolderSpace α X F) {s : Set X} {δ : ℝ≥0} (hf : ∀ x ∈ s, ‖f x‖ ≤ δ)
    (hg : ∀ x ∉ s, g x = 0) :
    ‖B.compHolder₂ f g‖ ≤
      ‖B‖ * (δ * ‖g‖ + nnHolderNorm α (f : X → E) * ‖g.toBoundedContinuousFunction‖) := by
  have hgM : ∀ x, ‖g x‖ ≤ ‖g.toBoundedContinuousFunction‖₊ := fun x ↦ by
    simpa using g.toBoundedContinuousFunction.norm_coe_le_norm x
  have hsup : ‖(B.compHolder₂ f g).toBoundedContinuousFunction‖ ≤
      ‖B‖ * δ * ‖g.toBoundedContinuousFunction‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x ↦ ?_
    rw [HolderSpace.toBoundedContinuousFunction_apply, compHolder₂_apply]
    by_cases hx : x ∈ s
    · exact (B.le_opNorm₂ _ _).trans (by gcongr; exacts [hf x hx, hgM x])
    · rw [hg x hx, map_zero, norm_zero]
      positivity
  have hsemi : (nnHolderNorm α ((B.compHolder₂ f g).toBoundedContinuousFunction : X → G) : ℝ) ≤
      ‖B‖ * (δ * nnHolderNorm α (g : X → F) +
        ‖g.toBoundedContinuousFunction‖ * nnHolderNorm α (f : X → E)) := by
    have heq : ((B.compHolder₂ f g).toBoundedContinuousFunction : X → G) =
        fun x ↦ B (f x) (g x) := by
      funext x
      rw [HolderSpace.toBoundedContinuousFunction_apply, compHolder₂_apply]
    rw [heq]
    have h := B.holderWith_comp₂_of_eq_zero (f.memHolder.holderWith.holderOnWith s)
      g.memHolder.holderWith (Mf := δ) (Mg := ‖g.toBoundedContinuousFunction‖₊)
      (fun x hx ↦ by simpa using hf x hx) (fun x _ ↦ by simpa using hgM x)
      (fun x hx ↦ by simpa using hg x hx)
    exact_mod_cast (by simpa using h.nnholderNorm_le :
      nnHolderNorm α (fun x ↦ B (f x) (g x)) ≤
        ‖B‖₊ * (δ * nnHolderNorm α (g : X → F) +
          ‖g.toBoundedContinuousFunction‖₊ * nnHolderNorm α (f : X → E)))
  rw [HolderSpace.norm_def, HolderSpace.norm_def g]
  simp only [HolderSpace.coe_toBoundedContinuousFunction] at hsemi ⊢
  linarith

/-- On a nonempty domain, pointwise lifting preserves the bilinear operator norm. -/
@[simp]
theorem norm_compHolder₂ [Nonempty X] (B : E →L[ℝ] F →L[ℝ] G) :
    ‖B.compHolder₂ (α := α) (X := X)‖ = ‖B‖ := by
  refine le_antisymm B.norm_compHolder₂_le
    (B.opNorm_le_bound₂ (norm_nonneg (B.compHolder₂ (α := α) (X := X))) ?_)
  intro e f
  obtain ⟨x⟩ := ‹Nonempty X›
  calc
    ‖B e f‖ = ‖B.compHolder₂ (HolderSpace.const (α := α) (X := X) e)
        (HolderSpace.const f) x‖ := by
      simp
    _ ≤ ‖B.compHolder₂ (HolderSpace.const (α := α) e) (HolderSpace.const f)‖ := by
      let h := B.compHolder₂ (HolderSpace.const (α := α) (X := X) e) (HolderSpace.const f)
      simpa only [HolderSpace.toBoundedContinuousFunction_apply] using
        (h.toBoundedContinuousFunction.norm_coe_le_norm x).trans
          h.norm_toBoundedContinuousFunction_le
    _ ≤ _ := by
      simpa only [HolderSpace.norm_const] using (B.compHolder₂ (α := α) (X := X)).le_opNorm₂
        (HolderSpace.const e) (HolderSpace.const f)

@[simp]
theorem compHolder₂_flip (B : E →L[ℝ] F →L[ℝ] G) :
    B.flip.compHolder₂ (α := α) (X := X) = B.compHolder₂.flip := by
  ext f g x
  simp

@[simp]
theorem compHolder₂_const (B : E →L[ℝ] F →L[ℝ] G) (e : E) (f : F) :
    B.compHolder₂ (HolderSpace.const (α := α) (X := X) e) (HolderSpace.const f) =
      HolderSpace.const (B e f) := by
  ext x
  simp

section ExtendByZero

variable {s : Set X}

open Classical in
/-- The extension by zero of a function on `s`; it is Hölder on `s` but not, in general, on `X`. -/
private def extendByZeroFun (g : HolderSpace α s E) : X → E :=
  fun x ↦ if hx : x ∈ s then g ⟨x, hx⟩ else 0

private theorem extendByZeroFun_of_mem (g : HolderSpace α s E) {x : X} (hx : x ∈ s) :
    extendByZeroFun g x = g ⟨x, hx⟩ := by
  simp [extendByZeroFun, hx]

private theorem norm_extendByZeroFun_le (g : HolderSpace α s E) (x : X) :
    ‖extendByZeroFun g x‖ ≤ ‖g.toBoundedContinuousFunction‖₊ := by
  by_cases hx : x ∈ s
  · rw [extendByZeroFun_of_mem g hx]
    simpa using g.toBoundedContinuousFunction.norm_coe_le_norm ⟨x, hx⟩
  · simp [extendByZeroFun, hx]

private theorem holderOnWith_extendByZeroFun (g : HolderSpace α s E) :
    HolderOnWith (nnHolderNorm α (g : s → E)) α (extendByZeroFun g) s := by
  intro x hx y hy
  rw [extendByZeroFun_of_mem g hx, extendByZeroFun_of_mem g hy]
  exact g.holderWith ⟨x, hx⟩ ⟨y, hy⟩

private theorem continuousOn_extendByZeroFun (g : HolderSpace α s E) :
    ContinuousOn (extendByZeroFun g) s := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert g.continuous using 1
  funext x
  exact extendByZeroFun_of_mem g x.2

/-- Applying `B` to the zero extension of a function on `s` and a function vanishing off `s`
gives a continuous function: near points where the second factor vanishes the product is small,
and elsewhere `s` is a neighbourhood. -/
private theorem continuous_comp₂_extendByZeroFun (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) :
    Continuous fun x ↦ B (extendByZeroFun g x) ((f : HolderSpace α X F) x) := by
  set f' : HolderSpace α X F := ↑f
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : f' x = 0
  · have hcont : Continuous fun y ↦ ‖B‖ * ‖g.toBoundedContinuousFunction‖ * ‖f' y‖ :=
      continuous_const.mul f'.continuous.norm
    rw [ContinuousAt, hx, map_zero]
    refine squeeze_zero_norm (fun y ↦ (B.le_opNorm₂ _ _).trans ?_)
      (by simpa [hx] using hcont.tendsto x)
    gcongr
    simpa using norm_extendByZeroFun_le g y
  · have hs : s ∈ nhds x := Filter.mem_of_superset
      ((isOpen_ne_fun f'.continuous continuous_const).mem_nhds hx) fun y hy ↦ by
        by_contra hys
        exact hy (mem_supportedHolderSubmodule_iff.mp f.2 y hys)
    exact ((B.continuous.comp_continuousOn (continuousOn_extendByZeroFun g)).clm_apply
      f'.continuous.continuousOn).continuousAt hs

private theorem holderWith_comp₂_extendByZeroFun (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) :
    HolderWith (‖B‖₊ * (‖g.toBoundedContinuousFunction‖₊ *
        nnHolderNorm α ((f : HolderSpace α X F) : X → F) +
      ‖(f : HolderSpace α X F).toBoundedContinuousFunction‖₊ * nnHolderNorm α (g : s → E))) α
      fun x ↦ B (extendByZeroFun g x) ((f : HolderSpace α X F) x) :=
  B.holderWith_comp₂_of_eq_zero (holderOnWith_extendByZeroFun g)
    (f : HolderSpace α X F).holderWith (fun x _ ↦ norm_extendByZeroFun_le g x)
    (fun x _ ↦ by
      simpa using (f : HolderSpace α X F).toBoundedContinuousFunction.norm_coe_le_norm x)
    (fun x hx ↦ mem_supportedHolderSubmodule_iff.mp f.2 x hx)

private def compHolder₂ExtendByZeroFun (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) : HolderSpace α X G :=
  HolderSpace.ofBoundedContinuousFunction
    (BoundedContinuousFunction.ofNormedAddCommGroup _ (continuous_comp₂_extendByZeroFun B f g)
      (‖B‖ * ‖g.toBoundedContinuousFunction‖ *
        ‖(f : HolderSpace α X F).toBoundedContinuousFunction‖)
      fun x ↦ (B.le_opNorm₂ _ _).trans (by
        gcongr
        · simpa using norm_extendByZeroFun_le g x
        · simpa using (f : HolderSpace α X F).toBoundedContinuousFunction.norm_coe_le_norm x))
    (by simpa using (holderWith_comp₂_extendByZeroFun B f g).memHolder)

private theorem compHolder₂ExtendByZeroFun_apply (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) (x : X) :
    compHolder₂ExtendByZeroFun B f g x = B (extendByZeroFun g x) ((f : HolderSpace α X F) x) := by
  simp [compHolder₂ExtendByZeroFun]

private theorem norm_compHolder₂ExtendByZeroFun_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) :
    ‖compHolder₂ExtendByZeroFun B f g‖ ≤ ‖B‖ * ‖f‖ * ‖g‖ := by
  set f' : HolderSpace α X F := ↑f
  have hsup : ‖(compHolder₂ExtendByZeroFun B f g).toBoundedContinuousFunction‖ ≤
      ‖B‖ * ‖g.toBoundedContinuousFunction‖ * ‖f'.toBoundedContinuousFunction‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro x
    rw [HolderSpace.toBoundedContinuousFunction_apply, compHolder₂ExtendByZeroFun_apply]
    exact (B.le_opNorm₂ _ _).trans (by
      gcongr
      · simpa using norm_extendByZeroFun_le g x
      · simpa using f'.toBoundedContinuousFunction.norm_coe_le_norm x)
  have hsemi : (nnHolderNorm α
      ((compHolder₂ExtendByZeroFun B f g).toBoundedContinuousFunction : X → G) : ℝ) ≤
      ‖B‖ * (‖g.toBoundedContinuousFunction‖ * nnHolderNorm α (f' : X → F) +
        ‖f'.toBoundedContinuousFunction‖ * nnHolderNorm α (g : s → E)) := by
    have heq : ((compHolder₂ExtendByZeroFun B f g).toBoundedContinuousFunction : X → G) =
        fun x ↦ B (extendByZeroFun g x) (f' x) := by
      funext x
      rw [HolderSpace.toBoundedContinuousFunction_apply, compHolder₂ExtendByZeroFun_apply]
    rw [heq]
    exact_mod_cast (holderWith_comp₂_extendByZeroFun B f g).nnholderNorm_le
  have htotal := add_le_add hsup hsemi
  rw [← Submodule.norm_coe]
  simp only [HolderSpace.norm_def, HolderSpace.coe_toBoundedContinuousFunction] at htotal ⊢
  nlinarith [mul_nonneg (norm_nonneg B)
    (mul_nonneg (NNReal.coe_nonneg (nnHolderNorm α (f' : X → F)))
      (NNReal.coe_nonneg (nnHolderNorm α (g : s → E))))]

/-- For `f` vanishing off `s`, pointwise application `x ↦ B (g x) (f x)` of a continuous bilinear
map to a bounded Hölder function `g` given only on `s`, extended by zero off `s`. The result is
Hölder on the whole space because `f` vanishes across the boundary of `s`, and it again vanishes
off `s`. Its operator norm is at most `‖B‖ * ‖f‖`
(`ContinuousLinearMap.norm_compHolder₂ExtendByZero_le`). -/
def compHolder₂ExtendByZero (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) :
    HolderSpace α s E →L[ℝ] supportedHolderSubmodule (Y := G) α s :=
  LinearMap.mkContinuous
    { toFun g := ⟨compHolder₂ExtendByZeroFun B f g,
        mem_supportedHolderSubmodule_iff.mpr fun x hx ↦ by
          rw [compHolder₂ExtendByZeroFun_apply, mem_supportedHolderSubmodule_iff.mp f.2 x hx,
            map_zero]⟩
      map_add' g₁ g₂ := Subtype.ext <| HolderSpace.ext fun x ↦ by
        by_cases hx : x ∈ s <;>
          simp [compHolder₂ExtendByZeroFun_apply, extendByZeroFun, hx]
      map_smul' c g := Subtype.ext <| HolderSpace.ext fun x ↦ by
        by_cases hx : x ∈ s <;>
          simp [compHolder₂ExtendByZeroFun_apply, extendByZeroFun, hx] }
    (‖B‖ * ‖f‖) fun g ↦ by
      rw [← Submodule.norm_coe]
      exact norm_compHolder₂ExtendByZeroFun_le B f g

/-- On `s`, the zero-extended product is pointwise application of the bilinear map. -/
@[simp]
theorem compHolder₂ExtendByZero_apply_of_mem (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) {x : X} (hx : x ∈ s) :
    (B.compHolder₂ExtendByZero f g : HolderSpace α X G) x =
      B (g ⟨x, hx⟩) ((f : HolderSpace α X F) x) := by
  simp [compHolder₂ExtendByZero, compHolder₂ExtendByZeroFun_apply, extendByZeroFun_of_mem g hx]

/-- Off `s`, the zero-extended product vanishes. -/
@[simp]
theorem compHolder₂ExtendByZero_apply_of_notMem (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) (g : HolderSpace α s E) {x : X} (hx : x ∉ s) :
    (B.compHolder₂ExtendByZero f g : HolderSpace α X G) x = 0 :=
  mem_supportedHolderSubmodule_iff.mp (B.compHolder₂ExtendByZero f g).2 x hx

/-- The zero-extended product has operator norm at most `‖B‖ * ‖f‖`. -/
theorem norm_compHolder₂ExtendByZero_le (B : E →L[ℝ] F →L[ℝ] G)
    (f : supportedHolderSubmodule (Y := F) α s) :
    ‖B.compHolder₂ExtendByZero (E := E) f‖ ≤ ‖B‖ * ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end ExtendByZero

end ContinuousLinearMap
