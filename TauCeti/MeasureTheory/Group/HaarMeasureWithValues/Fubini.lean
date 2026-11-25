/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Integral
public import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Prod

/-!
# Fubini's theorem for Haar measures with values in a ring

Let `G` and `H` be Hausdorff topological groups, `A` a commutative semiring, `μ` and `ν`
`A`-valued Haar measures on `G` and `H`, and `M` an `A`-module. For a locally constant function
`f : G × H → M` with compact support, each slice `h ↦ f (g, h)` lies in `C_c^∞(H, M)`
(`TauCeti.HaarMeasureWithValues.sliceRight`), and integrating it against `ν` gives a function of
`g` that again lies in `C_c^∞(G, M)` (`TauCeti.HaarMeasureWithValues.integralRight`): for an
indicator `1_K • m` it is `g ↦ ν(K_g) • m`, and the slices `K_g` of a compact open set depend
locally constantly on `g`. Integrating in the other variable gives
`TauCeti.HaarMeasureWithValues.integralLeft`.

**Fubini's theorem** (`TauCeti.HaarMeasureWithValues.integral_integralRight` and
`TauCeti.HaarMeasureWithValues.integral_integralLeft`) says that both iterated integrals are the
integral against the product measure `μ.prod ν`. Both sides are `A`-linear in `f`, so by the
uniqueness of the integral it suffices to treat an indicator `1_K • m`, where the first iterated
integral is the sum over the slices `T` of `K` of `μ{g | K_g = T} • ν(T) • m`, the product volume
of `K` times `m`. The second order follows from the first applied to `ν` and `μ`, since exchanging
the factors carries `ν.prod μ` to `μ.prod ν` when `A` is commutative
(`TauCeti.HaarMeasureWithValues.prod_apply_map_swap`).

## Main definitions

* `TauCeti.HaarMeasureWithValues.sliceRight`, `TauCeti.HaarMeasureWithValues.sliceLeft`: the
  slices `h ↦ f (g, h)` and `g ↦ f (g, h)` of `f ∈ C_c^∞(G × H, M)`, as `A`-linear maps.
* `TauCeti.HaarMeasureWithValues.integralRight ν`: `C_c^∞(G × H, M) → C_c^∞(G, M)`,
  `f ↦ (g ↦ ∫ f (g, h) dν(h))`.
* `TauCeti.HaarMeasureWithValues.integralLeft μ`: `C_c^∞(G × H, M) → C_c^∞(H, M)`,
  `f ↦ (h ↦ ∫ f (g, h) dμ(g))`.

## Main results

* `TauCeti.HaarMeasureWithValues.integral_integralRight`:
  `∫ (∫ f (g, h) dν(h)) dμ(g) = ∫ f d(μ.prod ν)`.
* `TauCeti.HaarMeasureWithValues.integral_integralLeft`:
  `∫ (∫ f (g, h) dμ(g)) dν(h) = ∫ f d(μ.prod ν)`.
* `TauCeti.HaarMeasureWithValues.prod_apply_map_swap`: `(ν.prod μ)(swap K) = (μ.prod ν)(K)`.

## References

* C. J. Bushnell and G. Henniart, *The Local Langlands Conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, §3.2, pp. 28–29.
-/

public section

open Set TopologicalSpace LocallyConstant
open scoped Pointwise

namespace TauCeti.HaarMeasureWithValues

/-! ### Slices of compactly supported locally constant functions -/

section Slice

variable {A G H M : Type*} [TopologicalSpace G] [TopologicalSpace H] [Semiring A]
  [AddCommMonoid M] [Module A M]

omit [Semiring A] [Module A M] in
/-- A slice of a compactly supported function on `X × Y` at a point of `X` has compact support. -/
theorem _root_.TauCeti.hasCompactSupport_comp_prodMk {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X × Y → M} (hf : HasCompactSupport f) (x : X) :
    HasCompactSupport fun y ↦ f (x, y) := by
  have hc : Continuous (Prod.mk x : Y → X × Y) := continuous_const.prodMk continuous_id
  refine HasCompactSupport.intro' (K := Prod.mk x ⁻¹' tsupport f)
    ((hf.image continuous_snd).of_isClosed_subset ((isClosed_tsupport f).preimage hc)
      fun y hy ↦ ⟨(x, y), hy, rfl⟩) ((isClosed_tsupport f).preimage hc) fun y hy ↦ ?_
  exact image_eq_zero_of_notMem_tsupport hy

variable (A M) in
/-- The **slice** `h ↦ f (g, h)` of a locally constant function `f` on `G × H` with compact support,
an element of `C_c^∞(H, M)`, as an `A`-linear map in `f`. -/
@[expose] noncomputable def sliceRight (g : G) :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A H M where
  toFun f := ⟨(f : LocallyConstant (G × H) M).comap
      ⟨Prod.mk g, continuous_const.prodMk continuous_id⟩,
    mem_compactlySupported.2 (hasCompactSupport_comp_prodMk
      (mem_compactlySupported.1 f.property) g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sliceRight_apply (g : G) (f : compactlySupported A (G × H) M) (h : H) :
    (sliceRight A M g f : LocallyConstant H M) h = (f : LocallyConstant (G × H) M) (g, h) :=
  rfl

variable (A M) in
/-- The **slice** `g ↦ f (g, h)` of a locally constant function `f` on `G × H` with compact support,
an element of `C_c^∞(G, M)`, as an `A`-linear map in `f`. -/
@[expose] noncomputable def sliceLeft (h : H) :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A G M where
  toFun f := ⟨(f : LocallyConstant (G × H) M).comap
      ⟨fun g ↦ (g, h), continuous_id.prodMk continuous_const⟩,
    mem_compactlySupported.2 (hasCompactSupport_comp_prodMk
        ((mem_compactlySupported.1 f.property).comp_homeomorph (Homeomorph.prodComm H G)) h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sliceLeft_apply (h : H) (f : compactlySupported A (G × H) M) (g : G) :
    (sliceLeft A M h f : LocallyConstant G M) g = (f : LocallyConstant (G × H) M) (g, h) :=
  rfl

end Slice

/-! ### Integration in one variable -/

section Partial

variable {A G H M : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G]
  [Group H] [TopologicalSpace H] [ContinuousMul H] [T2Space H]
  [CommSemiring A] [AddCommMonoid M] [Module A M]

omit [Group G] [ContinuousMul G] in
/-- Integrating the slices of an indicator `1_K • m` gives `g ↦ ν(K_g) • m`. -/
private theorem integral_sliceRight_compactOpenIndicator (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) (m : M) (g : G) :
    ν.integral (sliceRight A M g
      ⟨compactOpenIndicator K m, compactOpenIndicator_mem_compactlySupported K m⟩) =
      ν (K.slice g) • m := by
  rw [← integral_compactOpenIndicator ν (K.slice g) m]
  congr 1
  ext h
  classical
  simp only [sliceRight_apply, coe_compactOpenIndicator, Set.indicator]
  exact if_congr (by rw [SetLike.mem_coe, SetLike.mem_coe, CompactOpens.mem_slice]) rfl rfl

omit [Group G] [ContinuousMul G] in
/-- The function `g ↦ ∫ f (g, h) dν(h)` is locally constant with compact support. -/
private theorem exists_integralRight (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    ∃ F : compactlySupported A G M,
      ∀ g, (F : LocallyConstant G M) g = ν.integral (sliceRight A M g f) := by
  obtain ⟨s, K, hf⟩ := exists_eq_sum_compactOpenIndicator (mem_compactlySupported.1 f.property)
  have hfs : f = ∑ m ∈ s, ⟨compactOpenIndicator (K m) m,
      compactOpenIndicator_mem_compactlySupported (K m) m⟩ :=
    Subtype.ext (by rw [hf, Submodule.coe_sum])
  -- Each indicator contributes `g ↦ ν(K_g) • m`, locally constant with support in `fst '' K`.
  have hval (g : G) : ν.integral (sliceRight A M g f) = ∑ m ∈ s, ν ((K m).slice g) • m := by
    rw [hfs, map_sum, map_sum]
    exact Finset.sum_congr rfl fun m _ ↦ integral_sliceRight_compactOpenIndicator ν (K m) m g
  let F : LocallyConstant G M := ∑ m ∈ s,
    ⟨fun g ↦ ν ((K m).slice g) • m, (K m).isLocallyConstant_slice.comp fun T ↦ ν T • m⟩
  have hFg (g : G) : F g = ∑ m ∈ s, ν ((K m).slice g) • m := by
    rw [← coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
    rfl
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
    (integralRight M ν f : LocallyConstant G M) g = ν.integral (sliceRight A M g f) :=
  (exists_integralRight ν f).choose_spec g

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
  · rw [integralRight_apply, integral_sliceRight_compactOpenIndicator,
      (CompactOpens.mem_sliceFiber.1 hg).1]
  · rw [integralRight_apply, integral_sliceRight_compactOpenIndicator] at hg
    have hK : K.slice g ≠ ⊥ := fun h ↦ hg (by rw [h, apply_bot, zero_smul])
    obtain ⟨h, hh⟩ := CompactOpens.coe_nonempty.2 hK
    exact ⟨K.slice g,
      CompactOpens.mem_slices.2 ⟨g, ⟨(g, h), CompactOpens.mem_slice.1 hh, rfl⟩, rfl⟩,
      CompactOpens.mem_sliceFiber.2 ⟨rfl, hK⟩⟩

/-! ### Exchanging the factors -/

omit [Group G] [ContinuousMul G] [T2Space G] [Group H] [ContinuousMul H] [T2Space H] in
/-- The compact open set `swap '' K ⊆ H × G` obtained from `K ⊆ G × H` by exchanging the
factors. -/
private def swapCompactOpens (K : CompactOpens (G × H)) : CompactOpens (H × G) :=
  K.map (Homeomorph.prodComm G H) (Homeomorph.prodComm G H).continuous
    (Homeomorph.prodComm G H).isOpenMap

omit [Group G] [ContinuousMul G] [T2Space G] [Group H] [ContinuousMul H] [T2Space H] in
private theorem coe_swapCompactOpens (K : CompactOpens (G × H)) :
    (swapCompactOpens K : Set (H × G)) = Prod.swap ⁻¹' K := by
  rw [swapCompactOpens, CompactOpens.coe_map, Homeomorph.coe_prodComm,
    Set.image_swap_eq_preimage_swap]

/-- **Exchanging the factors of a product measure.** For a commutative semiring `A`, the volume
under `ν.prod μ` of the image of `K ⊆ G × H` under `(g, h) ↦ (h, g)` is the volume of `K` under
`μ.prod ν`. -/
theorem prod_apply_map_swap (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (K : CompactOpens (G × H)) :
    ν.prod μ (K.map (Homeomorph.prodComm G H) (Homeomorph.prodComm G H).continuous
      (Homeomorph.prodComm G H).isOpenMap) = μ.prod ν K := by
  -- `K ↦ (ν.prod μ)(swap '' K)` is a Haar measure on `G × H` with the volumes of `μ.prod ν` on
  -- rectangles.
  let ρ : HaarMeasureWithValues A (G × H) :=
    { toFun K := ν.prod μ (swapCompactOpens K)
      map_bot' := by
        rw [← apply_bot (ν.prod μ)]
        exact congrArg _ (CompactOpens.ext (by
          rw [coe_swapCompactOpens, CompactOpens.coe_bot, CompactOpens.coe_bot, preimage_empty]))
      map_sup' K L hKL := by
        rw [← apply_sup _ (by
          rw [coe_swapCompactOpens, coe_swapCompactOpens]
          exact hKL.preimage _)]
        exact congrArg _ (CompactOpens.ext (by
          rw [coe_swapCompactOpens, CompactOpens.coe_sup, CompactOpens.coe_sup,
            coe_swapCompactOpens, coe_swapCompactOpens, preimage_union]))
      map_smul' x K := by
        change ν.prod μ (swapCompactOpens (x • K)) = ν.prod μ (swapCompactOpens K)
        rw [← apply_smul (ν.prod μ) x.swap (swapCompactOpens K)]
        exact congrArg _ (CompactOpens.ext (Set.ext fun y ↦ by
          simp only [coe_swapCompactOpens, CompactOpens.coe_smul, mem_preimage,
            Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, Prod.swap_mul, Prod.swap_inv,
            Prod.swap_swap])) }
  have hρ : ρ = μ.prod ν := eq_prod_of_apply_prod μ ν ρ fun U V ↦ by
    change ν.prod μ (swapCompactOpens (U ×ˢ V)) = _
    rw [show swapCompactOpens (U ×ˢ V) = V ×ˢ U from CompactOpens.ext <| by
        rw [coe_swapCompactOpens, CompactOpens.coe_prod, CompactOpens.coe_prod,
          Set.preimage_swap_prod],
      prod_apply_prod, mul_comm]
  exact congrArg (fun ρ : HaarMeasureWithValues A (G × H) ↦ ρ K) hρ

variable (A M) in
/-- Exchanging the variables of a function in `C_c^∞(G × H, M)`. -/
@[expose] noncomputable def swapCompactlySupported :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A (H × G) M where
  toFun f := ⟨(f : LocallyConstant (G × H) M).comap ⟨Prod.swap, continuous_swap⟩,
    mem_compactlySupported.2 ((mem_compactlySupported.1 f.property).comp_homeomorph
      (Homeomorph.prodComm H G))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Group G] [ContinuousMul G] [T2Space G] [Group H] [ContinuousMul H] [T2Space H] in
@[simp]
theorem swapCompactlySupported_apply (f : compactlySupported A (G × H) M) (x : H × G) :
    (swapCompactlySupported A M f : LocallyConstant (H × G) M) x =
      (f : LocallyConstant (G × H) M) x.swap :=
  rfl

/-- The integral against `ν.prod μ` of `(h, g) ↦ f (g, h)` is the integral of `f` against
`μ.prod ν`. -/
theorem integral_swapCompactlySupported (μ : HaarMeasureWithValues A G)
    (ν : HaarMeasureWithValues A H) (f : compactlySupported A (G × H) M) :
    (ν.prod μ).integral (swapCompactlySupported A M f) = (μ.prod ν).integral f := by
  refine LinearMap.congr_fun (eq_integral_of_apply_compactOpenIndicator (μ.prod ν)
    ((ν.prod μ).integral ∘ₗ swapCompactlySupported A M) fun K m ↦ ?_) f
  rw [LinearMap.comp_apply, ← prod_apply_map_swap, ← integral_compactOpenIndicator]
  congr 1
  ext ⟨h, g⟩
  classical
  simp only [swapCompactlySupported_apply, coe_compactOpenIndicator, Set.indicator,
    Prod.swap_prod_mk]
  exact if_congr (by rw [← swapCompactOpens, coe_swapCompactOpens, mem_preimage,
    Prod.swap_prod_mk]) rfl rfl

variable (M) in
/-- **Integration in the first variable**: `f ↦ (h ↦ ∫ f (g, h) dμ(g))`, an `A`-linear map
`C_c^∞(G × H, M) → C_c^∞(H, M)`. -/
noncomputable def integralLeft (μ : HaarMeasureWithValues A G) :
    compactlySupported A (G × H) M →ₗ[A] compactlySupported A H M :=
  integralRight M μ ∘ₗ swapCompactlySupported A M

omit [Group H] [ContinuousMul H] in
@[simp]
theorem integralLeft_apply (μ : HaarMeasureWithValues A G) (f : compactlySupported A (G × H) M)
    (h : H) :
    (integralLeft M μ f : LocallyConstant H M) h = μ.integral (sliceLeft A M h f) := by
  rw [integralLeft, LinearMap.comp_apply, integralRight_apply]
  rfl

/-- **Fubini's theorem**, integrating first in the first variable:
`∫ (∫ f (g, h) dμ(g)) dν(h) = ∫ f d(μ.prod ν)`. -/
theorem integral_integralLeft (μ : HaarMeasureWithValues A G) (ν : HaarMeasureWithValues A H)
    (f : compactlySupported A (G × H) M) :
    ν.integral (integralLeft M μ f) = (μ.prod ν).integral f := by
  rw [integralLeft, LinearMap.comp_apply, integral_integralRight,
    integral_swapCompactlySupported]

end Partial

end TauCeti.HaarMeasureWithValues
