/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Topological support of a translate

The topological support of a right translate of a function on a topological group, and of a
function transported along a homeomorphism, next to Mathlib's `mulTSupport_comp_eq_preimage`.

## Main results

* `TauCeti.mulTSupport_comp_div_right`: the topological multiplicative support of
  `fun y => f (y / x)` is the preimage of that of `f` under `(· / x)`, with additive version
  `TauCeti.tsupport_comp_sub_right`.
* `Homeomorph.tsupport_comp_symm`: transporting a function `F` along a homeomorphism `e` gives
  `F ∘ e⁻¹`, whose topological support is `e(tsupport F)`, with multiplicative version
  `Homeomorph.mulTSupport_comp_symm`.
* `Homeomorph.tsupport_comp_symm_subset_interior_image`: support in the interior of a set is
  transported to support in the interior of its image, with multiplicative version
  `Homeomorph.mulTSupport_comp_symm_subset_interior_image`.
* `Continuous.smul_of_continuousOn_of_tsupport_subset`: a continuous function supported
  in `U`, times a function continuous on `U`, is continuous.
* `TauCeti.tsupport_snd_smul_fst_subset`: the topological support of `(x, y) ↦ f y • g x` lies in
  `tsupport g ×ˢ tsupport f`.
* `TauCeti.tsupport_subset_of_forall_notMem_eq_zero`: a function vanishing off a closed set `s`
  has topological support in `s`, with multiplicative version
  `TauCeti.mulTSupport_subset_of_forall_notMem_eq_one`.
* `HasCompactSupport.comp_of_forall_mem_imp_mem`: a function of `Ψ y` that vanishes outside `T` is
  compactly supported when the preimage of `T` under `Ψ` lies in a compact set.
* `HasCompactSupport.mono_of_eq_zero`: a function vanishing wherever a compactly supported
  function vanishes is compactly supported, with multiplicative version
  `HasCompactMulSupport.mono_of_eq_one`.
* `HasCompactSupport.of_forall_mem_support_eq_one`: a function is compactly supported when a
  compactly supported function is equal to `1` on its support.
* `TauCeti.hasCompactSupport_pi_iff`: a function with values in a finite product is compactly
  supported exactly when every coordinate is, with multiplicative version
  `TauCeti.hasCompactMulSupport_pi_iff`.
* `TauCeti.sum_eventuallyEq_of_notMem_tsupport`: near a point outside the topological supports
  of all summands but one, a finite sum agrees with that summand, with multiplicative version
  `TauCeti.prod_eventuallyEq_of_notMem_mulTSupport`.
* `TauCeti.apply_sum_smul_eq_sum_sq_mul_of_notMem_tsupport`: a functional that depends only on
  the germ at `x` and is quadratic under scaling does not mix functions whose topological
  supports at `x` are disjoint.
-/

public section

namespace TauCeti

variable {X G : Type*} [TopologicalSpace X] [Group X] [SeparatelyContinuousMul X] [One G]

/-- The topological multiplicative support of a right translate is the preimage of the
topological multiplicative support under the opposite translation. -/
@[to_additive /-- The topological support of a translate is the translated topological
support. -/]
theorem mulTSupport_comp_div_right (f : X → G) (x : X) :
    (mulTSupport fun y => f (y / x)) = (· / x) ⁻¹' mulTSupport f := by
  simpa [div_eq_mul_inv, Function.comp_def] using
    mulTSupport_comp_eq_preimage f (Homeomorph.mulRight x⁻¹)

section Prod

variable {Y R M : Type*} [Zero R] [Zero M] [SMulWithZero R M]

omit [TopologicalSpace X] [Group X] [SeparatelyContinuousMul X] in
/-- The function `(x, y) ↦ f y • g x` is supported in `support g ×ˢ support f`. -/
theorem support_snd_smul_fst_subset (f : Y → R) (g : X → M) :
    Function.support (fun p : X × Y ↦ f p.2 • g p.1) ⊆ Function.support g ×ˢ Function.support f :=
  fun _ hp ↦ ⟨right_ne_zero_of_smul hp, left_ne_zero_of_smul hp⟩

omit [Group X] [SeparatelyContinuousMul X] in
/-- The function `(x, y) ↦ f y • g x` is supported in `tsupport g ×ˢ tsupport f`. -/
theorem tsupport_snd_smul_fst_subset [TopologicalSpace Y] (f : Y → R) (g : X → M) :
    tsupport (fun p : X × Y ↦ f p.2 • g p.1) ⊆ tsupport g ×ˢ tsupport f :=
  closure_minimal ((support_snd_smul_fst_subset f g).trans
    (Set.prod_mono (subset_tsupport _) (subset_tsupport _)))
    ((isClosed_tsupport _).prod (isClosed_tsupport _))

end Prod

/-- A function equal to `1` off a closed set `s` has topological multiplicative support in `s`. -/
@[to_additive /-- A function vanishing off a closed set `s` has topological support in `s`. -/]
theorem mulTSupport_subset_of_forall_notMem_eq_one {Y M : Type*} [TopologicalSpace Y] [One M]
    {f : Y → M} {s : Set Y} (hf : ∀ x ∉ s, f x = 1) (hs : IsClosed s) : mulTSupport f ⊆ s :=
  hs.closure_subset_iff.2 (Function.mulSupport_subset_iff'.2 hf)

end TauCeti

namespace Continuous

/-- A function `b` continuous with topological support in `U`, times a function `a` continuous
on `U`, is continuous. The function `a` need not be continuous off `U`, and `U` need not be
open. -/
theorem smul_of_continuousOn_of_tsupport_subset {Z 𝕜 F : Type*} [TopologicalSpace Z]
    [TopologicalSpace 𝕜] [Zero F] [TopologicalSpace F] [SMulZeroClass 𝕜 F]
    [ContinuousSMul 𝕜 F] {a : Z → 𝕜} {b : Z → F} {U : Set Z} (hb : Continuous b)
    (hbU : tsupport b ⊆ U) (ha : ContinuousOn a U) : Continuous fun x ↦ a x • b x := by
  have hzero : ∀ x ∈ Uᶜ, b x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hbU h)
  refine continuous_of_tsupport fun x hx ↦ ?_
  have hxU : x ∈ U := hbU (tsupport_smul_subset_right _ _ hx)
  rw [← continuousWithinAt_univ, ← Set.union_compl_self U, continuousWithinAt_union]
  refine ⟨(ha x hxU).smul hb.continuousAt.continuousWithinAt, ?_⟩
  exact (continuousWithinAt_const.smul hb.continuousAt.continuousWithinAt).congr
    (fun y hy ↦ by simp [hzero y hy]) rfl

end Continuous

namespace Homeomorph

variable {X Y α : Type*} [TopologicalSpace X] [TopologicalSpace Y] [One α]

/-- The topological multiplicative support of a function transported along a homeomorphism `e`
is the image under `e` of its topological multiplicative support. -/
@[to_additive /-- The topological support of a function transported along a homeomorphism `e` is
the image under `e` of its topological support. -/]
theorem mulTSupport_comp_symm (e : X ≃ₜ Y) (F : X → α) :
    mulTSupport (F ∘ e.symm) = e '' mulTSupport F := by
  rw [e.image_eq_preimage_symm, mulTSupport_comp_eq_preimage]

/-- A function whose topological multiplicative support lies in the interior of `s`, transported
along a homeomorphism `e`, has topological multiplicative support in the interior of `e(s)`. -/
@[to_additive /-- A function supported in the interior of `s`, transported along a homeomorphism
`e`, is supported in the interior of `e(s)`. -/]
theorem mulTSupport_comp_symm_subset_interior_image (e : X ≃ₜ Y) {F : X → α} {s : Set X}
    (h : mulTSupport F ⊆ interior s) : mulTSupport (F ∘ e.symm) ⊆ interior (e '' s) := by
  rw [e.mulTSupport_comp_symm, ← e.image_interior]
  exact Set.image_mono h

end Homeomorph

/-- A function of `Ψ y` that vanishes outside `T` is compactly supported when the preimage under
`Ψ` of `T` lies in a compact set. -/
theorem HasCompactSupport.comp_of_forall_mem_imp_mem {X Y Z : Type*} [TopologicalSpace X]
    [R1Space X] [Zero Z] {Ψ : X → Y} {T : Set Y} {K : Set X} (hK : IsCompact K)
    (hΨK : ∀ y, Ψ y ∈ T → y ∈ K) {k : Y → Z}
    (hkz : ∀ z ∉ T, k z = 0) : HasCompactSupport fun y ↦ k (Ψ y) :=
  HasCompactSupport.intro hK fun y hy ↦ hkz _ fun h ↦ hy (hΨK y h)

/-- A function equal to `1` wherever a function with compact multiplicative support is equal to
`1` has compact multiplicative support. -/
@[to_additive /-- A function vanishing wherever a compactly supported function vanishes is
compactly supported. -/]
theorem HasCompactMulSupport.mono_of_eq_one {X β γ : Type*} [TopologicalSpace X] [One β] [One γ]
    {f : X → β} {g : X → γ} (hf : HasCompactMulSupport f) (hg : ∀ x, f x = 1 → g x = 1) :
    HasCompactMulSupport g :=
  hf.mono <| Function.mulSupport_subset_iff'.2 fun x hx ↦ hg x (Function.notMem_mulSupport.1 hx)

/-- A function is compactly supported when a compactly supported function is equal to `1` on its
support. -/
theorem HasCompactSupport.of_forall_mem_support_eq_one {X β γ : Type*} [TopologicalSpace X]
    [Zero β] [One β] [NeZero (1 : β)] [Zero γ] {f : X → β} {g : X → γ} (hf : HasCompactSupport f)
    (hfg : ∀ x ∈ Function.support g, f x = 1) : HasCompactSupport g :=
  hf.mono fun x hx ↦ by
    rw [Function.mem_support, hfg x hx]
    exact one_ne_zero

namespace TauCeti

/-- A function with values in a finite product has compact multiplicative support exactly when
each coordinate has compact multiplicative support. -/
@[to_additive /-- A function with values in a finite product is compactly supported exactly when
each coordinate is compactly supported. -/]
theorem hasCompactMulSupport_pi_iff {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {M : ι → Type*} [∀ i, One (M i)] {f : X → ∀ i, M i} :
    HasCompactMulSupport f ↔ ∀ i, HasCompactMulSupport (f · i) := by
  simp [hasCompactMulSupport_iff_eventuallyEq, Filter.EventuallyEq, funext_iff]

open scoped Topology in
/-- Near a point outside the topological multiplicative supports of all `f j` with `j ∈ s` and
`j ≠ i`, the product `∏ j ∈ s, f j` agrees with `f i`. -/
@[to_additive /-- Near a point outside the topological supports of all `f j` with `j ∈ s` and
`j ≠ i`, the sum `∑ j ∈ s, f j` agrees with `f i`. -/]
theorem prod_eventuallyEq_of_notMem_mulTSupport {X M κ : Type*} [TopologicalSpace X]
    [CommMonoid M] {s : Finset κ} {f : κ → X → M} {x : X} {i : κ} (hi : i ∈ s)
    (h : ∀ j ∈ s, j ≠ i → x ∉ mulTSupport (f j)) : (∏ j ∈ s, f j) =ᶠ[𝓝 x] f i := by
  classical
  have h₁ : ∀ᶠ y in 𝓝 x, ∀ j ∈ s.erase i, f j y = 1 := (Filter.eventually_all_finset _).2
    fun j hj ↦ notMem_mulTSupport_iff_eventuallyEq.1 (h j (Finset.mem_of_mem_erase hj)
      (Finset.ne_of_mem_erase hj))
  filter_upwards [h₁] with y hy
  rw [Finset.prod_apply, ← Finset.mul_prod_erase s _ hi, Finset.prod_eq_one hy, mul_one]

open scoped Topology in
/-- Let `Q` be a functional of functions `X → M` that depends only on the germ at `x` and satisfies
`Q (a • φ) = a ^ 2 * Q φ`. If `x` lies in the topological support of at most one `v j`, then
`Q (∑ j, c j • v j) = ∑ j, c j ^ 2 * Q (v j)`. -/
theorem apply_sum_smul_eq_sum_sq_mul_of_notMem_tsupport {X R M κ : Type*} [TopologicalSpace X]
    [Semiring R] [AddCommMonoid M] [Module R M] [Fintype κ] {v : κ → X → M} {x : X}
    (Q : (X → M) → R) (hQ : ∀ (a : R) φ, Q (a • φ) = a ^ 2 * Q φ)
    (hQx : ∀ φ ψ, φ =ᶠ[𝓝 x] ψ → Q φ = Q ψ) (c : κ → R)
    (hv : ∀ i j, i ≠ j → x ∈ tsupport (v i) → x ∉ tsupport (v j)) :
    Q (∑ j, c j • v j) = ∑ j, c j ^ 2 * Q (v j) := by
  classical
  -- `Q` vanishes on functions vanishing near `x`, since such a function is `0 • φ` near `x`.
  have hzero : ∀ φ : X → M, φ =ᶠ[𝓝 x] 0 → Q φ = 0 := fun φ hφ ↦ by
    rw [hQx φ ((0 : R) • φ) (hφ.trans (.of_eq (by ext; simp))), hQ, zero_pow two_ne_zero,
      zero_mul]
  have hzero' : ∀ j, x ∉ tsupport (v j) → c j ^ 2 * Q (v j) = 0 := fun j hj ↦ by
    rw [hzero _ (notMem_tsupport_iff_eventuallyEq.1 hj), mul_zero]
  by_cases hx : ∃ i, x ∈ tsupport (v i)
  · obtain ⟨i, hi⟩ := hx
    have hi' : ∀ j ≠ i, x ∉ tsupport (v j) := fun j hj ↦ hv i j (Ne.symm hj) hi
    rw [hQx _ _ (sum_eventuallyEq_of_notMem_tsupport (f := fun j ↦ c j • v j) (Finset.mem_univ i)
        fun j _ hj hx ↦ hi' j hj (tsupport_smul_subset_right (fun _ ↦ c j) (v j) hx)), hQ,
      Finset.sum_eq_single i (fun j _ hj ↦ hzero' j (hi' j hj)) (by simp)]
  · push Not at hx
    rw [Finset.sum_eq_zero fun j _ ↦ hzero' j (hx j)]
    refine hzero _ ((Filter.eventually_all.2 fun j ↦
      notMem_tsupport_iff_eventuallyEq.1 (hx j)).mono fun y hy ↦ ?_)
    simp [Finset.sum_apply, hy]

end TauCeti
