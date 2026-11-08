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
* `TauCeti.continuous_smul_of_continuousOn_of_tsupport_subset`: a continuous function supported
  in `U`, times a function continuous on `U`, is continuous.
* `TauCeti.tsupport_snd_smul_fst_subset`: the topological support of `(x, y) ↦ f y • g x` lies in
  `tsupport g ×ˢ tsupport f`.
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

/-- A function `b` continuous with topological support in `U`, times a function `a` continuous
on `U`, is continuous. The function `a` need not be continuous off `U`, and `U` need not be
open. -/
theorem continuous_smul_of_continuousOn_of_tsupport_subset {Z 𝕜 F : Type*} [TopologicalSpace Z]
    [TopologicalSpace 𝕜] [Zero F] [TopologicalSpace F] [T2Space F] [SMulZeroClass 𝕜 F]
    [ContinuousSMul 𝕜 F] {a : Z → 𝕜} {b : Z → F} {U : Set Z} (hb : Continuous b)
    (hbU : tsupport b ⊆ U) (ha : ContinuousOn a U) : Continuous fun x ↦ a x • b x := by
  have hzero : ∀ x ∈ Uᶜ, b x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hbU h)
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hxU : x ∈ U
  · rw [← continuousWithinAt_univ, ← Set.union_compl_self U, continuousWithinAt_union]
    refine ⟨(ha x hxU).smul hb.continuousAt.continuousWithinAt, ?_⟩
    by_cases hx : x ∈ closure Uᶜ
    · have hbx : b x = 0 := Set.EqOn.closure hzero hb continuous_const hx
      exact (continuousWithinAt_const (b := (0 : F))).congr
        (fun y hy ↦ by simp [hzero y hy]) (by simp [hbx])
    · exact continuousWithinAt_of_notMem_closure hx
  · have hx : x ∉ tsupport b := fun h ↦ hxU (hbU h)
    have hev : b =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
    exact (continuousAt_const (y := (0 : F))).congr
      (hev.mono fun y (hy : b y = 0) ↦ by simp [hy])

end TauCeti

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
