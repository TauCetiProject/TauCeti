/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `Lᵖ` functions with values in an `ℓ^q` product

For `1 ≤ p` and `1 ≤ q`, a function with values in the product `WithLp q (E × F)` lies in `Lᵖ`
exactly when its two components do. `MeasureTheory.Lp.withLpProdEquiv` packages this as a
continuous linear equivalence

`Lp (WithLp q (E × F)) p μ ≃L[𝕜] Lp E p μ × Lp F p μ`,

which sends `f` to its components `s ↦ (f s).fst` and `s ↦ (f s).snd`, and a pair `(g, h)` back to
`s ↦ (g s, h s)` (`MeasureTheory.Lp.coeFn_withLpProdEquiv_symm`). It is the binary counterpart of
the isometry `MeasureTheory.Lp.piLpEquiv` for finite `PiLp` products; here the exponents `p` and `q`
may differ, and the equivalence is only continuous. It splits operators on `L²` paths in a direct
sum `WithLp 2 (H₁ × H₂)` of Hilbert spaces into their two blocks.
-/

public section

noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal

variable {α 𝕜 E F : Type*} {m : MeasurableSpace α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  {μ : Measure α} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 q μ) in
/-- The map `(g, h) ↦ (s ↦ (g s, h s))` from `Lp E p μ × Lp F p μ` to `Lp (WithLp q (E × F)) p μ`,
the inverse of `MeasureTheory.Lp.withLpProdEquiv`. -/
private def withLpProdMk : Lp E p μ × Lp F p μ →L[𝕜] Lp (WithLp q (E × F)) p μ :=
  ((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm : E × F →L[𝕜] WithLp q (E × F)).comp
      (ContinuousLinearMap.inl 𝕜 E F)).compLpL p μ).coprod
    ((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm : E × F →L[𝕜] WithLp q (E × F)).comp
      (ContinuousLinearMap.inr 𝕜 E F)).compLpL p μ)

variable (𝕜 q) in
private theorem coeFn_withLpProdMk (g : Lp E p μ × Lp F p μ) :
    withLpProdMk 𝕜 q μ g =ᵐ[μ] fun s ↦ WithLp.toLp q (g.1 s, g.2 s) := by
  filter_upwards [Lp.coeFn_add (((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm :
        E × F →L[𝕜] WithLp q (E × F)).comp (ContinuousLinearMap.inl 𝕜 E F)).compLpL p μ) g.1)
      (((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm :
        E × F →L[𝕜] WithLp q (E × F)).comp (ContinuousLinearMap.inr 𝕜 E F)).compLpL p μ) g.2),
    ContinuousLinearMap.coeFn_compLpL ((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm :
        E × F →L[𝕜] WithLp q (E × F)).comp (ContinuousLinearMap.inl 𝕜 E F))) g.1,
    ContinuousLinearMap.coeFn_compLpL ((((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm :
        E × F →L[𝕜] WithLp q (E × F)).comp (ContinuousLinearMap.inr 𝕜 E F))) g.2]
    with s h h₁ h₂
  simp only [withLpProdMk, ContinuousLinearMap.coprod_apply, h, Pi.add_apply, h₁, h₂]
  simp [WithLp.ext_iff]

variable (𝕜 q μ) in
/-- **`Lᵖ` functions into an `ℓ^q` product are pairs of `Lᵖ` functions.** The continuous linear
equivalence sending `f` to its two components `s ↦ (f s).fst` and `s ↦ (f s).snd`. -/
def withLpProdEquiv : Lp (WithLp q (E × F)) p μ ≃L[𝕜] Lp E p μ × Lp F p μ :=
  .ofContinuousLinearMap
    (((WithLp.fstL q 𝕜 E F).compLpL p μ).prod ((WithLp.sndL q 𝕜 E F).compLpL p μ))
    (withLpProdMk 𝕜 q μ)
    (ContinuousLinearMap.ext fun g ↦ by
      refine Prod.ext (Lp.ext ?_) (Lp.ext ?_)
      · filter_upwards [coeFn_withLpProdMk 𝕜 q g,
          ContinuousLinearMap.coeFn_compLpL (WithLp.fstL q 𝕜 E F) (withLpProdMk 𝕜 q μ g)]
          with s h h₁
        simp [h₁, h]
      · filter_upwards [coeFn_withLpProdMk 𝕜 q g,
          ContinuousLinearMap.coeFn_compLpL (WithLp.sndL q 𝕜 E F) (withLpProdMk 𝕜 q μ g)]
          with s h h₁
        simp [h₁, h])
    (ContinuousLinearMap.ext fun f ↦ by
      refine Lp.ext ?_
      filter_upwards [coeFn_withLpProdMk 𝕜 q
          ((WithLp.fstL q 𝕜 E F).compLpL p μ f, (WithLp.sndL q 𝕜 E F).compLpL p μ f),
        ContinuousLinearMap.coeFn_compLpL (WithLp.fstL q 𝕜 E F) f,
        ContinuousLinearMap.coeFn_compLpL (WithLp.sndL q 𝕜 E F) f] with s h h₁ h₂
      -- `toLp q (x.fst, x.snd) = x` holds by structure eta.
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, h, h₁, h₂]
      rfl)

theorem withLpProdEquiv_apply (f : Lp (WithLp q (E × F)) p μ) :
    withLpProdEquiv 𝕜 q μ f =
      ((WithLp.fstL q 𝕜 E F).compLpL p μ f, (WithLp.sndL q 𝕜 E F).compLpL p μ f) :=
  (rfl)

theorem withLpProdEquiv_symm_apply (g : Lp E p μ × Lp F p μ) :
    (withLpProdEquiv 𝕜 q μ).symm g =
      (((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm : E × F →L[𝕜] WithLp q (E × F)).comp
          (ContinuousLinearMap.inl 𝕜 E F)).compLpL p μ g.1 +
        (((WithLp.prodContinuousLinearEquiv q 𝕜 E F).symm : E × F →L[𝕜] WithLp q (E × F)).comp
          (ContinuousLinearMap.inr 𝕜 E F)).compLpL p μ g.2 :=
  (rfl)

/-- The first component of `MeasureTheory.Lp.withLpProdEquiv f` is `f` followed by the first
projection. -/
@[simp]
theorem withLpProdEquiv_apply_fst (f : Lp (WithLp q (E × F)) p μ) :
    (withLpProdEquiv 𝕜 q μ f).1 = (WithLp.fstL q 𝕜 E F).compLpL p μ f :=
  (rfl)

/-- The second component of `MeasureTheory.Lp.withLpProdEquiv f` is `f` followed by the second
projection. -/
@[simp]
theorem withLpProdEquiv_apply_snd (f : Lp (WithLp q (E × F)) p μ) :
    (withLpProdEquiv 𝕜 q μ f).2 = (WithLp.sndL q 𝕜 E F).compLpL p μ f :=
  (rfl)

/-- The first component of `MeasureTheory.Lp.withLpProdEquiv` is `s ↦ (f s).fst`. -/
theorem coeFn_withLpProdEquiv_fst (f : Lp (WithLp q (E × F)) p μ) :
    (withLpProdEquiv 𝕜 q μ f).1 =ᵐ[μ] fun s ↦ (f s).fst :=
  ContinuousLinearMap.coeFn_compLpL (WithLp.fstL q 𝕜 E F) f

/-- The second component of `MeasureTheory.Lp.withLpProdEquiv` is `s ↦ (f s).snd`. -/
theorem coeFn_withLpProdEquiv_snd (f : Lp (WithLp q (E × F)) p μ) :
    (withLpProdEquiv 𝕜 q μ f).2 =ᵐ[μ] fun s ↦ (f s).snd :=
  ContinuousLinearMap.coeFn_compLpL (WithLp.sndL q 𝕜 E F) f

/-- The inverse of `MeasureTheory.Lp.withLpProdEquiv` pairs the two functions pointwise. -/
theorem coeFn_withLpProdEquiv_symm (g : Lp E p μ × Lp F p μ) :
    (withLpProdEquiv 𝕜 q μ).symm g =ᵐ[μ] fun s ↦ WithLp.toLp q (g.1 s, g.2 s) := by
  exact coeFn_withLpProdMk 𝕜 q g

end MeasureTheory.Lp
