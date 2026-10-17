/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import TauCeti.MeasureTheory.Function.Lp.Product
public import TauCeti.MeasureTheory.Integral.Prod

/-!
# Pointwise products of `L²` functions on a product measure

For an `L²(μ)` function `f` and an `L²(ν)` function `g` on s-finite measures, the pointwise
product `(x, y) ↦ f x * g y` belongs to `L²(μ ⊗ ν)`, and the assignment factors the inner product
as a tensor:
`⟪f₁ ⊗ g₁, f₂ ⊗ g₂⟫ = ⟪f₁, f₂⟫ * ⟪g₁, g₂⟫`.
Consequently the products of two orthonormal families are an orthonormal family of `L²(μ ⊗ ν)`.

For σ-finite factors the products of two Hilbert bases form a Hilbert basis
`HilbertBasis.prod` of `L²(μ ⊗ ν)`. Its index type is the product of the factor index types,
and its basis vectors are the concrete pointwise products of the factor vectors.

The underlying normed-ring construction and its additive and scalar laws are provided by
`TauCeti.MeasureTheory.Function.Lp.Product`.

The tensor family has dense linear span in `L²(μ ⊗ ν)` for arbitrary factor index types. Thus
expansions in the product Hilbert basis are available without countability assumptions on either
basis. The vanishing-integral lemmas relate orthogonality to all elementary tensors to the
integrals of representatives over finite-measure rectangles and measurable sets.

The scalars are generic over `[RCLike 𝕜]`, so a single construction serves both the real and
complex `L²` spaces.

## Main definitions

* `MeasureTheory.Lp.prodMul` — the pointwise product `(x, y) ↦ f x * g y` of `F : L²(μ)` and
  `G : L²(ν)` as a vector of `L²(μ ⊗ ν)`.
* `HilbertBasis.prod` — the Hilbert basis of `L²(μ ⊗ ν)` built from Hilbert bases of the
  factors.

## Main statements

* `MeasureTheory.MemLp.mul_prod` — the pointwise product of `L²` functions is `L²` for the product
  measure.
* `MeasureTheory.Lp.inner_prodMul` — the inner product of two tensors factors as a product of inner
  products.
* `Orthonormal.prodMul` — products of orthonormal families are orthonormal.
* `HilbertBasis.orthogonal_span_range_prodMul_eq_bot` — the basis tensors have trivial orthogonal
  complement.
* `TauCeti.setIntegral_prod_eq_zero_of_forall_inner` — orthogonality to every elementary tensor
  implies vanishing integrals over finite-measure rectangles.
* `TauCeti.setIntegral_eq_zero_of_forall_inner` — orthogonality to every elementary tensor implies
  vanishing integrals over all measurable sets of finite measure.
* `HilbertBasis.prod_apply` — the `(i, j)` basis vector is the tensor `b₁ i ⊗ b₂ j`;
  `HilbertBasis.coeFn_prod` gives its a.e. representative.
-/

public section

open MeasureTheory MeasureTheory.Lp

variable {𝕜 α β : Type*} [RCLike 𝕜] {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {ν : Measure β}

namespace MeasureTheory.Lp

/-- **The tensor inner-product identity.** The inner product of two pointwise-product vectors in
`L²(μ ⊗ ν)` factors as the product of the inner products of the factors. -/
@[simp]
theorem inner_prodMul [SFinite μ] [SFinite ν] (F₁ F₂ : Lp 𝕜 2 μ) (G₁ G₂ : Lp 𝕜 2 ν) :
    inner 𝕜 (prodMul F₁ G₁) (prodMul F₂ G₂) = inner 𝕜 F₁ F₂ * inner 𝕜 G₁ G₂ := by
  rw [L2.inner_def]
  calc
    ∫ p, inner 𝕜 (prodMul F₁ G₁ p) (prodMul F₂ G₂ p) ∂(μ.prod ν)
        = ∫ p : α × β, inner 𝕜 (F₁ p.1 * G₁ p.2) (F₂ p.1 * G₂ p.2) ∂(μ.prod ν) := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_prodMul F₁ G₁, coeFn_prodMul F₂ G₂] with p hp1 hp2
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

end MeasureTheory.Lp

/-- **Orthonormality of the tensor family.** If `b` and `c` are orthonormal families of `L²(μ)` and
`L²(ν)`, their pointwise products form an orthonormal family of `L²(μ ⊗ ν)`, indexed by the product
of index types. -/
theorem Orthonormal.prodMul [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    {b : ι₁ → Lp 𝕜 2 μ} {c : ι₂ → Lp 𝕜 2 ν} (hb : Orthonormal 𝕜 b) (hc : Orthonormal 𝕜 c) :
    Orthonormal 𝕜 (fun ij : ι₁ × ι₂ => prodMul (b ij.1) (c ij.2)) := by
  classical
  rw [orthonormal_iff_ite] at hb hc ⊢
  intro ij kl
  rw [inner_prodMul, hb, hc]
  by_cases h1 : ij.1 = kl.1 <;> by_cases h2 : ij.2 = kl.2 <;>
    simp [h1, h2, Prod.ext_iff]

namespace MeasureTheory.Lp

/-- The tensor construction is norm-multiplicative. -/
@[simp]
theorem norm_prodMul [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    ‖prodMul F G‖ = ‖F‖ * ‖G‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), mul_pow]
  exact_mod_cast (by simpa only [inner_self_eq_norm_sq_to_K] using inner_prodMul F F G G :
    ((‖prodMul F G‖ : ℝ) : 𝕜) ^ 2 = ((‖F‖ : ℝ) : 𝕜) ^ 2 * ((‖G‖ : ℝ) : 𝕜) ^ 2)

/-- **The tensor as a bounded bilinear map.** `prodMulL F G = prodMul F G`, packaged so that
either operand can be fixed: `prodMulL F` fixes the left factor, `prodMulL.flip G` the right.
Its operator norm is at most `1`. -/
noncomputable def prodMulL [SFinite μ] [SFinite ν] :
    Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 (μ.prod ν) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 prodMul
      (fun F₁ F₂ G => prodMul_add_left F₁ F₂ G)
      (fun c F G => prodMul_smul_left c F G)
      (fun F G₁ G₂ => prodMul_add_right F G₁ G₂)
      (fun c F G => prodMul_smul_right c F G))
    1 fun F G => by simp [norm_prodMul]

@[simp]
theorem prodMulL_apply [SFinite μ] [SFinite ν] (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) :
    prodMulL F G = prodMul F G :=
  LinearMap.mkContinuous₂_apply _ _ _ _

end MeasureTheory.Lp

namespace HilbertBasis

/-- **Basis tensors detect all tensors.** A vector orthogonal to every tensor built from two Hilbert
bases is orthogonal to every elementary tensor. Thus the basis tensors suffice for testing
orthogonality to the family of elementary tensors. -/
theorem inner_prodMul_eq_zero_of_forall_basis [SFinite μ] [SFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν))
    {h : Lp 𝕜 2 (μ.prod ν)} (hz : ∀ i j, inner 𝕜 h (prodMul (b₁ i) (b₂ j)) = 0)
    (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν) : inner 𝕜 h (prodMul F G) = 0 := by
  -- With a left basis vector fixed, the induced functional vanishes on the dense span of b₂.
  have step (i : ι₁) : (innerSL 𝕜 h).comp (prodMulL (b₁ i)) = 0 := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b₂.dense_span)
    rintro _ ⟨j, rfl⟩
    simpa using hz i j
  -- For any right vector, the left functional then vanishes on the dense span of b₁.
  have hzero : (innerSL 𝕜 h).comp (prodMulL.flip G) = 0 := by
    apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 b₁.dense_span)
    rintro _ ⟨i, rfl⟩
    simpa using DFunLike.congr_fun (step i) G
  simpa using DFunLike.congr_fun hzero F

end HilbertBasis

namespace TauCeti

/-- A vector orthogonal to every elementary tensor has vanishing integral over every measurable
rectangle whose sides have finite measure. This determines its averages on such rectangles. -/
theorem setIntegral_prod_eq_zero_of_forall_inner [SFinite ν] {h : Lp 𝕜 2 (μ.prod ν)}
    (hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (prodMul F G) h = 0)
    {A : Set α} (hA : MeasurableSet A) (hμA : μ A ≠ ⊤)
    {B : Set β} (hB : MeasurableSet B) (hνB : ν B ≠ ⊤) :
    ∫ p in A ×ˢ B, h p ∂(μ.prod ν) = 0 := by
  -- The product of the two indicator vectors is the indicator of the rectangle.
  set F : Lp 𝕜 2 μ := indicatorConstLp 2 hA hμA (1 : 𝕜)
  set G : Lp 𝕜 2 ν := indicatorConstLp 2 hB hνB (1 : 𝕜)
  have hFc : ⇑F =ᵐ[μ] A.indicator fun _ => (1 : 𝕜) := indicatorConstLp_coeFn
  have hGc : ⇑G =ᵐ[ν] B.indicator fun _ => (1 : 𝕜) := indicatorConstLp_coeFn
  calc ∫ p in A ×ˢ B, h p ∂(μ.prod ν)
      = ∫ p, (A ×ˢ B).indicator (fun q => h q) p ∂(μ.prod ν) :=
        (integral_indicator (hA.prod hB)).symm
    _ = ∫ p, inner 𝕜 ((prodMul F G) p) (h p) ∂(μ.prod ν) := by
        refine integral_congr_ae ?_
        filter_upwards [coeFn_prodMul F G, ae_of_ae_fst (β := β) (ν := ν) hFc,
          ae_of_ae_snd (α := α) (μ := μ) hGc] with p hp hpF hpG
        rw [hp, hpF, hpG]
        by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ B <;>
          simp [Set.mem_prod, h1, h2]
    _ = inner 𝕜 (prodMul F G) h := (L2.inner_def _ _).symm
    _ = 0 := hz F G

/-- **Orthogonality kills the part of a measurable set inside a finite-measure box.** -/
private theorem setIntegral_inter_prod_eq_zero [SFinite ν] {h : Lp 𝕜 2 (μ.prod ν)}
    (hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (prodMul F G) h = 0)
    {u : Set (α × β)} (hu : MeasurableSet u)
    {A : Set α} (hA : MeasurableSet A) (hμA : μ A ≠ ⊤)
    {B : Set β} (hB : MeasurableSet B) (hνB : ν B ≠ ⊤) :
    ∫ p in u ∩ (A ×ˢ B), h p ∂(μ.prod ν) = 0 := by
  -- Inside a finite box the rectangles on which the integral is known to vanish generate the
  -- whole product σ-algebra.
  have hboxfin : (μ.prod ν) (A ×ˢ B) ≠ ⊤ := by
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top hμA.lt_top hνB.lt_top).ne
  have hrect : ∀ s, MeasurableSet s → ∀ t, MeasurableSet t →
      ∫ p in s ×ˢ t, h p ∂((μ.prod ν).restrict (A ×ˢ B)) = 0 := by
    intro s hs t ht
    rw [Measure.restrict_restrict (hs.prod ht), Set.prod_inter_prod]
    exact setIntegral_prod_eq_zero_of_forall_inner hz (hs.inter hA)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hμA.lt_top).ne
      (ht.inter hB)
      (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hνB.lt_top).ne
  -- Apply the Dynkin (π-λ) theorem for the finite-box restriction.
  have hdyn := setIntegral_eq_zero_of_forall_prod
    (integrableOn_Lp_of_measure_ne_top h one_le_two hboxfin) hrect u hu
  rwa [Measure.restrict_restrict hu] at hdyn

/-- A vector orthogonal to every elementary tensor has vanishing integral over every measurable
set of finite measure. -/
theorem setIntegral_eq_zero_of_forall_inner [SigmaFinite μ] [SigmaFinite ν] {h : Lp 𝕜 2 (μ.prod ν)}
    (hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (prodMul F G) h = 0)
    (u : Set (α × β)) (hu : MeasurableSet u) (hfin : (μ.prod ν) u < ⊤) :
    ∫ p in u, h p ∂(μ.prod ν) = 0 := by
  -- Exhaust the product space by finite-measure boxes and pass to the monotone limit.
  have hmono : Monotone fun n => u ∩ (spanningSets μ n ×ˢ spanningSets ν n) := fun m n hmn =>
    Set.inter_subset_inter_right _
      (Set.prod_mono (monotone_spanningSets μ hmn) (monotone_spanningSets ν hmn))
  have hcover : ⋃ n, u ∩ (spanningSets μ n ×ˢ spanningSets ν n) = u := by
    rw [← Set.inter_iUnion,
      Set.iUnion_prod_of_monotone (monotone_spanningSets μ) (monotone_spanningSets ν),
      iUnion_spanningSets, iUnion_spanningSets, Set.univ_prod_univ, Set.inter_univ]
  have htend := tendsto_setIntegral_of_monotone
    (fun n => hu.inter ((measurableSet_spanningSets μ n).prod (measurableSet_spanningSets ν n)))
    hmono
    (by rw [hcover]; exact integrableOn_Lp_of_measure_ne_top h one_le_two hfin.ne)
  rw [hcover] at htend
  simp only [fun n ↦ setIntegral_inter_prod_eq_zero hz hu (measurableSet_spanningSets μ n)
    (measure_spanningSets_lt_top μ n).ne (measurableSet_spanningSets ν n)
    (measure_spanningSets_lt_top ν n).ne] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

end TauCeti

namespace HilbertBasis

open TauCeti

/-- **Completeness of the tensor family.** The tensors built from two Hilbert bases have trivial
orthogonal complement in `L²(μ ⊗ ν)`. Together with orthonormality, this supplies the completeness
condition for the product Hilbert basis. -/
theorem orthogonal_span_range_prodMul_eq_bot [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) : (Submodule.span 𝕜
      (Set.range (fun ij : ι₁ × ι₂ => prodMul (b₁ ij.1) (b₂ ij.2))))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun h hh => ?_
  rw [Submodule.mem_orthogonal] at hh
  -- Upgrade orthogonality to basis tensors to orthogonality to all elementary tensors.
  have hz : ∀ (F : Lp 𝕜 2 μ) (G : Lp 𝕜 2 ν), inner 𝕜 (prodMul F G) h = 0 := by
    intro F G
    rw [inner_eq_zero_symm]
    refine inner_prodMul_eq_zero_of_forall_basis b₁ b₂ (fun i j => ?_) F G
    rw [inner_eq_zero_symm]
    exact hh _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  -- Vanishing integrals over finite-measure sets force the representative to vanish a.e.
  have hae := Lp.ae_eq_zero_of_forall_setIntegral_eq_zero h (by norm_num) (by norm_num)
    (fun s _ hs' => integrableOn_Lp_of_measure_ne_top h one_le_two hs'.ne)
    (fun s hs hs' => setIntegral_eq_zero_of_forall_inner hz s hs hs')
  rw [Lp.ext_iff]
  exact hae.trans (Lp.coeFn_zero 𝕜 2 (μ.prod ν)).symm

/-- **The product Hilbert basis.** Pointwise products of two Hilbert bases form a Hilbert basis of
`L²(μ ⊗ ν)`, indexed by the product of the index types. -/
noncomputable def prod [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) :
    HilbertBasis (ι₁ × ι₂) 𝕜 (Lp 𝕜 2 (μ.prod ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (b₁.orthonormal.prodMul b₂.orthonormal)
    (orthogonal_span_range_prodMul_eq_bot b₁ b₂)

/-- The vector of `HilbertBasis.prod` at `ij` is the tensor of the corresponding factor vectors. -/
@[simp]
theorem prod_apply [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) (ij : ι₁ × ι₂) :
    prod b₁ b₂ ij = prodMul (b₁ ij.1) (b₂ ij.2) := by
  rw [prod, HilbertBasis.coe_mkOfOrthogonalEqBot]

/-- The vector of `HilbertBasis.prod` at `ij` is a.e. the pointwise product of its factors. -/
theorem coeFn_prod [SigmaFinite μ] [SigmaFinite ν] {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ 𝕜 (Lp 𝕜 2 μ)) (b₂ : HilbertBasis ι₂ 𝕜 (Lp 𝕜 2 ν)) (ij : ι₁ × ι₂) :
    ⇑(prod b₁ b₂ ij) =ᵐ[μ.prod ν] fun q : α × β => b₁ ij.1 q.1 * b₂ ij.2 q.2 := by
  rw [prod_apply]
  exact coeFn_prodMul _ _

end HilbertBasis
