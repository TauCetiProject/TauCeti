module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Pointwise products of `L²` functions on a product measure

For an `L²(μ)` function `f` and an `L²(ν)` function `g` on σ-finite measures, the pointwise
product `(x, y) ↦ f x * g y` belongs to `L²(μ ⊗ ν)`, and the assignment factors the inner product
as a tensor:
`⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫`.
Consequently the products of two orthonormal families are an orthonormal family of `L²(μ ⊗ ν)`.

This is the Fubini orthonormality half of Part B3 of the `OrthogonalL2Bases` roadmap (the product
`L²`-basis milestone): the elementary tensors are orthonormal, and their inner products separate.
It is a genuine gap in Mathlib, which provides only `MemLp.comp_fst`/`MemLp.comp_snd`
(single-factor membership, and only for finite measures) and the finite-dimensional
`OrthonormalBasis.tensorProduct`; there is no `L²(μ.prod ν)` product API. The completeness half —
that these tensors *span* `L²(μ ⊗ ν)`, hence form a Hilbert basis — is left to a separate
construction; this file supplies the orthonormality input it consumes.

The scalars are generic over `[RCLike 𝕜]`, so a single construction serves both the real and
complex `L²` spaces.

## Main definitions

* `TauCeti.L2prodMul` — the pointwise product `(x, y) ↦ f x * g y` of `F : L²(μ)` and `G : L²(ν)`
  as a vector of `L²(μ ⊗ ν)`.

## Main statements

* `TauCeti.memLp_mul_prod` — the pointwise product of `L²` functions is `L²` for the product
  measure.
* `TauCeti.inner_L2prodMul` — the inner product of two tensors factors as a product of inner
  products.
* `TauCeti.orthonormal_L2prodMul` — products of orthonormal families are orthonormal.
-/

public section

namespace TauCeti

open MeasureTheory

variable {𝕜 α β : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

/-- The pointwise product `(x, y) ↦ f x * g y` of an `L²(μ)` and an `L²(ν)` function is `L²` for the
product measure `μ ⊗ ν`. -/
theorem memLp_mul_prod [SFinite μ] [SFinite ν] {f : α → 𝕜} {g : β → 𝕜}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 * g p.2) 2 (μ.prod ν) := by
  have hfst : AEStronglyMeasurable (fun p : α × β => f p.1) (μ.prod ν) :=
    hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun p : α × β => g p.2) (μ.prod ν) :=
    hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hmeas : AEStronglyMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) := hfst.mul hsnd
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hf2 : Integrable (fun x => ‖f x‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hg2 : Integrable (fun y => ‖g y‖ ^ 2) ν := (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  refine (hf2.mul_prod hg2).congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [norm_mul, mul_pow]

/-- The pointwise product `(x, y) ↦ F x * G y` of `F : L²(μ)` and `G : L²(ν)`, as a vector of
`L²(μ ⊗ ν)`. -/
noncomputable def L2prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    Lp 𝕜 2 (μ.prod ν) :=
  (memLp_mul_prod (Lp.memLp F) (Lp.memLp G)).toLp _

/-- The `Lp` representative of `L2prodMul F G` is the pointwise product of the representatives. -/
theorem coeFn_L2prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ⇑(L2prodMul F G) =ᵐ[μ.prod ν] fun p : α × β => F p.1 * G p.2 :=
  MemLp.coeFn_toLp _

/-- **The tensor inner-product identity.** The inner product of two pointwise-product vectors in
`L²(μ ⊗ ν)` factors as the product of the inner products of the factors. -/
@[simp]
theorem inner_L2prodMul [SFinite μ] [SFinite ν] (F₁ F₂ : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    inner 𝕜 (L2prodMul F₁ G₁) (L2prodMul F₂ G₂) = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by
  rw [L2.inner_def]
  calc
    ∫ p, inner 𝕜 (L2prodMul F₁ G₁ p) (L2prodMul F₂ G₂ p) ∂(μ.prod ν)
        = ∫ p : α × β, inner 𝕜 (F₁ p.1 * G₁ p.2) (F₂ p.1 * G₂ p.2) ∂(μ.prod ν) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_L2prodMul F₁ G₁, coeFn_L2prodMul F₂ G₂] with p hp1 hp2
          rw [hp1, hp2]
    _ = ∫ p : α × β,
          inner 𝕜 (F₁ p.1) (F₂ p.1) * inner 𝕜 (G₁ p.2) (G₂ p.2) ∂(μ.prod ν) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          simp only [RCLike.inner_apply', map_mul]
          ring
    _ = (∫ x, inner 𝕜 (F₁ x) (F₂ x) ∂μ) * ∫ y, inner 𝕜 (G₁ y) (G₂ y) ∂ν :=
          integral_prod_mul (fun x => inner 𝕜 (F₁ x) (F₂ x))
            (fun y => inner 𝕜 (G₁ y) (G₂ y))
    _ = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by rw [← L2.inner_def, ← L2.inner_def]

/-- **Orthonormality of the tensor family.** If `b` and `c` are orthonormal families of `L²(μ)` and
`L²(ν)`, their pointwise products form an orthonormal family of `L²(μ ⊗ ν)`, indexed by the product
of index types. -/
theorem orthonormal_L2prodMul [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    {b : ι₁ → Lp 𝕜 2 μ} {c : ι₂ → Lp 𝕜 2 ν}
    (hb : Orthonormal 𝕜 b) (hc : Orthonormal 𝕜 c) :
    Orthonormal 𝕜 (fun ij : ι₁ × ι₂ => L2prodMul (b ij.1) (c ij.2)) := by
  classical
  rw [orthonormal_iff_ite] at hb hc ⊢
  intro ij kl
  rw [inner_L2prodMul, hb, hc]
  by_cases h1 : ij.1 = kl.1 <;> by_cases h2 : ij.2 = kl.2 <;>
    simp [h1, h2, Prod.ext_iff]

end TauCeti
