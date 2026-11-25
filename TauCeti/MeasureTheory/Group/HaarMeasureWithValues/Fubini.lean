/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Integral
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Prod
public import TauCeti.Topology.LocallyConstant.CompactSupport.Prod

/-!
# Fubini's theorem for Haar measures with values in a ring

Let `G` and `H` be Hausdorff topological groups, `A` a commutative semiring, `μ` and `ν`
`A`-valued Haar measures on `G` and `H`, and `M` an `A`-module. For a locally constant function
`f : G × H → M` with compact support, each slice `h ↦ f (g, h)` lies in `C_c^∞(H, M)`
(`LocallyConstant.compactlySupported.sliceRight`), and integrating it against `ν` gives a
function of `g` that again lies in `C_c^∞(G, M)` (`TauCeti.HaarMeasureWithValues.integralRight`):
for an indicator `1_K • m` it is `g ↦ ν(K_g) • m`
(`TauCeti.HaarMeasureWithValues.integralRight_compactOpenIndicator`), and the slices `K_g` of a
compact open set depend locally constantly on `g`. Integrating in the other variable gives
`TauCeti.HaarMeasureWithValues.integralLeft`.

**Fubini's theorem** (`TauCeti.HaarMeasureWithValues.integral_integralRight` and
`TauCeti.HaarMeasureWithValues.integral_integralLeft`) says that both iterated integrals are the
integral against the product measure `μ.prod ν`. Both sides are `A`-linear in `f`, so by the
uniqueness of the integral it suffices to treat an indicator `1_K • m`, where the first iterated
integral is the sum over the slices `T` of `K` of `μ{g | K_g = T} • ν(T) • m`, the product volume
of `K` times `m`. The second order follows from the first applied to `ν` and `μ`, since exchanging
the factors carries `ν.prod μ` to `μ.prod ν` when `A` is commutative
(`TauCeti.HaarMeasureWithValues.prod_apply_swap`).

## Main definitions

* `TauCeti.HaarMeasureWithValues.integralRight ν`: `C_c^∞(G × H, M) → C_c^∞(G, M)`,
  `f ↦ (g ↦ ∫ f (g, h) dν(h))`.
* `TauCeti.HaarMeasureWithValues.integralLeft μ`: `C_c^∞(G × H, M) → C_c^∞(H, M)`,
  `f ↦ (h ↦ ∫ f (g, h) dμ(g))`.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_integralRight`:
  `∫ (∫ f (g, h) dν(h)) dμ(g) = ∫ f d(μ.prod ν)`.
* `TauCeti.HaarMeasureWithValues.integral_integralLeft`:
  `∫ (∫ f (g, h) dμ(g)) dν(h) = ∫ f d(μ.prod ν)`.
* `TauCeti.HaarMeasureWithValues.prod_apply_swap`: `(ν.prod μ)(K.swap) = (μ.prod ν)(K)`.
* `TauCeti.HaarMeasureWithValues.integralRight_compactOpenIndicator`,
  `TauCeti.HaarMeasureWithValues.integralLeft_compactOpenIndicator`: the partial integrals of an
  indicator `1_K • m` are `g ↦ ν(K_g) • m` and `h ↦ μ(K^h) • m`.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.2, pp. 28–29.
-/

public section

open Set TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti.HaarMeasureWithValues

/-! ### Exchanging the factors -/

section Swap

variable {A G H : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H] [NonUnitalNonAssocCommSemiring A]

omit [T2Space G] [T2Space H] in
private theorem swap_smul (x : G × H) (K : CompactOpens (G × H)) :
    (x • K).swap = x.swap • K.swap :=
  CompactOpens.ext (Set.ext fun y ↦ by
    simp only [CompactOpens.coe_swap, CompactOpens.coe_smul, mem_preimage,
      Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, Prod.swap_mul, Prod.swap_inv,
      Prod.swap_swap])

/-- The volume `K ↦ (ν.prod μ)(K.swap)` on `G × H`, an `A`-valued Haar measure. -/
private noncomputable def swapProd (μ : HaarMeasureWithValues A G)
    (ν : HaarMeasureWithValues A H) : HaarMeasureWithValues A (G × H) where
  toFun K := ν.prod μ K.swap
  map_bot' := (congrArg (ν.prod μ) CompactOpens.swap_bot).trans (apply_bot _)
  map_sup' K L hKL := (congrArg (ν.prod μ) (CompactOpens.swap_sup K L)).trans <|
    apply_sup _ (by simpa only [CompactOpens.coe_swap] using hKL.preimage Prod.swap)
  map_smul' x K := (congrArg (ν.prod μ) (swap_smul x K)).trans (apply_smul _ _ _)

private theorem swapProd_apply (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) : swapProd μ ν K = ν.prod μ K.swap := by
  rw [swapProd, coe_mk]

/-- **Exchanging the factors of a product measure.** For a commutative `A`, the volume under
`ν.prod μ` of the image `K.swap` of `K ⊆ G × H` under `(g, h) ↦ (h, g)` is the volume of `K` under
`μ.prod ν`. -/
theorem prod_apply_swap (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) : ν.prod μ K.swap = μ.prod ν K := by
  -- `K ↦ (ν.prod μ)(K.swap)` is a Haar measure on `G × H` with the volumes of `μ.prod ν` on
  -- rectangles.
  rw [← swapProd_apply, eq_prod_of_apply_prod μ ν (swapProd μ ν) fun U V ↦ by
    rw [swapProd_apply, CompactOpens.swap_prod, prod_apply_prod, mul_comm]]

end Swap

/-! ### Integration in one variable -/

section Partial

variable {A G H M : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H]
  [CommSemiring A] [AddCommMonoid M] [Module A M]

omit [Group G] [ContinuousMul G] in
/-- The function `g ↦ ∫ f (g, h) dν(h)` is locally constant with compact support. -/
private theorem exists_integralRight (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    ∃ F : compactlySupported A G M,
      ∀ g, (F : LocallyConstant G M) g = ν.integral (compactlySupported.sliceRight A M g f) := by
  obtain ⟨s, K, hf⟩ := exists_eq_sum_compactOpenIndicator (mem_compactlySupported.1 f.property)
  have hfs : f = ∑ m ∈ s, ⟨compactOpenIndicator (K m) m,
      compactOpenIndicator_mem_compactlySupported (K m) m⟩ :=
    Subtype.ext (by rw [hf, Submodule.coe_sum])
  -- Each indicator contributes `g ↦ ν(K_g) • m`, locally constant with support in `fst '' K`.
  have hval (g : G) :
      ν.integral (compactlySupported.sliceRight A M g f) = ∑ m ∈ s, ν ((K m).slice g) • m := by
    rw [hfs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun m _ ↦ by
      rw [compactlySupported.sliceRight_compactOpenIndicator, integral_compactOpenIndicator]
  let F : LocallyConstant G M := ∑ m ∈ s,
    ⟨fun g ↦ ν ((K m).slice g) • m, (K m).isLocallyConstant_slice.comp fun T ↦ ν T • m⟩
  have hFg (g : G) : F g = ∑ m ∈ s, ν ((K m).slice g) • m := by
    rw [← coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    simp only [coeFnAddMonoidHom_apply, LocallyConstant.coe_mk]
  have hF : HasCompactSupport F := by
    refine HasCompactSupport.intro' (K := ⋃ m ∈ s, Prod.fst '' ((K m : Set (G × H))))
      (s.finite_toSet.isCompact_biUnion fun m _ ↦ (K m).isCompact.image continuous_fst)
      (s.finite_toSet.isClosed_biUnion fun m _ ↦
        ((K m).isCompact.image continuous_fst).isClosed) fun g hg ↦ ?_
    rw [hFg]
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    simp only [mem_iUnion, not_exists] at hg
    rw [CompactOpens.slice_eq_bot_of_notMem (hg m hm), apply_bot, zero_smul]
  exact ⟨⟨F, mem_compactlySupported.2 hF⟩, fun g ↦ (hFg g).trans (hval g).symm⟩

variable (M) in
/-- **Integration in the second variable**: `f ↦ (g ↦ ∫ f (g, h) dν(h))`, an `A`-linear map
`C_c^∞(G × H, M) → C_c^∞(G, M)`. -/
noncomputable def integralRight (ν : HaarMeasureWithValues A H) :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A G M where
  toFun f := (exists_integralRight ν f).choose
  map_add' f f' := compactlySupported.ext fun g ↦ by
    rw [(exists_integralRight ν (f + f')).choose_spec g, Submodule.coe_add,
      LocallyConstant.add_apply, (exists_integralRight ν f).choose_spec g,
      (exists_integralRight ν f').choose_spec g, map_add, map_add]
  map_smul' c f := compactlySupported.ext fun g ↦ by
    rw [(exists_integralRight ν (c • f)).choose_spec g, RingHom.id_apply, Submodule.coe_smul,
      LocallyConstant.smul_apply, (exists_integralRight ν f).choose_spec g, map_smul, map_smul]

omit [Group G] [ContinuousMul G] in
@[simp]
theorem integralRight_apply (ν : HaarMeasureWithValues A H) (f : compactlySupported A (G × H) M)
    (g : G) :
    (integralRight M ν f : LocallyConstant G M) g =
      ν.integral (compactlySupported.sliceRight A M g f) :=
  (exists_integralRight ν f).choose_spec g

omit [Group G] [ContinuousMul G] in
/-- Integrating an indicator `1_K • m` in the second variable gives `g ↦ ν(K_g) • m`. -/
theorem integralRight_compactOpenIndicator (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) (m : M) (g : G) :
    (integralRight M ν ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ :
      LocallyConstant G M) g = ν (K.slice g) • m := by
  rw [integralRight_apply, compactlySupported.sliceRight_compactOpenIndicator,
    integral_compactOpenIndicator]

/-- **Fubini's theorem**, integrating first in the second variable:
`∫ (∫ f (g, h) dν(h)) dμ(g) = ∫ f d(μ.prod ν)`. -/
theorem integral_integralRight (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    μ.integral (integralRight M ν f) = (μ.prod ν).integral f := by
  classical
  -- Both sides are linear in `f`; compare them on indicators `1_K • m`.
  refine LinearMap.congr_fun (eq_integral_of_apply_compactOpenIndicator (μ.prod ν)
    (μ.integral ∘ₗ integralRight M ν) fun K m ↦ ?_) f
  rw [LinearMap.comp_apply, prod_apply_eq_sum_slices, Finset.sum_smul]
  -- `g ↦ ν(K_g) • m` takes the value `ν(T) • m` on the fibre `{g | K_g = T}`.
  refine (integral_eq_sum μ _ (s := K.slices) (K := K.sliceFiber) (v := fun T ↦ ν T • m)
    K.pairwiseDisjoint_sliceFiber (fun T _ g hg ↦ ?_) fun g hg ↦ ?_).trans
      (Finset.sum_congr rfl fun T _ ↦ (mul_smul _ _ _).symm)
  · rw [integralRight_compactOpenIndicator, (CompactOpens.mem_sliceFiber.1 hg).1]
  · rw [integralRight_compactOpenIndicator] at hg
    have hK : K.slice g ≠ ⊥ := fun h ↦ hg (by rw [h, apply_bot, zero_smul])
    obtain ⟨h, hh⟩ := CompactOpens.coe_nonempty.2 hK
    exact ⟨K.slice g,
      CompactOpens.mem_slices.2 ⟨g, ⟨(g, h), CompactOpens.mem_slice.1 hh, rfl⟩, rfl⟩,
      CompactOpens.mem_sliceFiber.2 ⟨rfl, hK⟩⟩

/-- The integral against `ν.prod μ` of `(h, g) ↦ f (g, h)` is the integral of `f` against
`μ.prod ν`. -/
theorem integral_prod_swap (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    (ν.prod μ).integral (compactlySupported.swap A M f) = (μ.prod ν).integral f := by
  refine LinearMap.congr_fun (eq_integral_of_apply_compactOpenIndicator (μ.prod ν)
    ((ν.prod μ).integral ∘ₗ compactlySupported.swap A M) fun K m ↦ ?_) f
  rw [LinearMap.comp_apply, compactlySupported.swap_compactOpenIndicator,
    integral_compactOpenIndicator, prod_apply_swap]

variable (M) in
/-- **Integration in the first variable**: `f ↦ (h ↦ ∫ f (g, h) dμ(g))`, an `A`-linear map
`C_c^∞(G × H, M) → C_c^∞(H, M)`. -/
noncomputable def integralLeft (μ : HaarMeasureWithValues A G) :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A H M :=
  integralRight M μ ∘ₗ compactlySupported.swap A M

omit [Group H] [ContinuousMul H] in
@[simp]
theorem integralLeft_apply (μ : HaarMeasureWithValues A G) (f : compactlySupported A (G × H) M)
    (h : H) :
    (integralLeft M μ f : LocallyConstant H M) h =
      μ.integral (compactlySupported.sliceLeft A M h f) := by
  rw [integralLeft, LinearMap.comp_apply, integralRight_apply, compactlySupported.sliceRight_swap]

omit [Group H] [ContinuousMul H] in
/-- Integrating an indicator `1_K • m` in the first variable gives `h ↦ μ(K^h) • m`, where
`K^h = {g | (g, h) ∈ K}` is the slice `K.swap.slice h`. -/
theorem integralLeft_compactOpenIndicator (μ : HaarMeasureWithValues A G)
    (K : CompactOpens (G × H)) (m : M) (h : H) :
    (integralLeft M μ ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩ :
      LocallyConstant H M) h = μ (K.swap.slice h) • m := by
  rw [integralLeft, LinearMap.comp_apply, compactlySupported.swap_compactOpenIndicator,
    integralRight_compactOpenIndicator]

/-- **Fubini's theorem**, integrating first in the first variable:
`∫ (∫ f (g, h) dμ(g)) dν(h) = ∫ f d(μ.prod ν)`. -/
theorem integral_integralLeft (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    ν.integral (integralLeft M μ f) = (μ.prod ν).integral f := by
  rw [integralLeft, LinearMap.comp_apply, integral_integralRight, integral_prod_swap]

end Partial

end TauCeti.HaarMeasureWithValues
