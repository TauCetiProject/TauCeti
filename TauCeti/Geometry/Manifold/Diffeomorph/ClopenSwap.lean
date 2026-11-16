/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Swapping two disjoint clopen pieces of a manifold

Let `U` and `V` be disjoint open subsets of a manifold `M` that are also closed, for instance two
distinct connected components of a locally connected manifold. A diffeomorphism `φ : U ≃ₘ V`
between them, each carrying the charts Mathlib restricts to it, extends to a self-diffeomorphism
of `M`: it acts as `φ` on `U`, as `φ⁻¹` on `V`, and as the identity on the rest of `M`
(`Diffeomorph.clopenSwap`). The extension is an involution. Closedness of `U` and `V` is what makes
the extension smooth: near a point outside both sets it is the identity, because the complement of
`U ∪ V` is open.

This is how a diffeomorphism between two components of a disconnected manifold is realized by a
global diffeomorphism, so that the diffeomorphism group can move a point of one component to a
point of the other.

## Main declarations

* `Diffeomorph.clopenSwap`: the self-diffeomorphism of `M` exchanging `U` and `V` along `φ`.
* `Diffeomorph.clopenSwap_apply_coe_left`, `Diffeomorph.clopenSwap_apply_coe_right` and
  `Diffeomorph.clopenSwap_apply_of_notMem`: its values on `U`, on `V` and off `U ∪ V`.
* `Diffeomorph.clopenSwap_symm`: it is its own inverse.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {U V : Opens M}

open scoped Classical in
/-- The underlying map of `Diffeomorph.clopenSwap`: `φ` on `U`, `φ⁻¹` on `V` and the identity
elsewhere. -/
private def clopenSwapFun (φ : U ≃ₘ^n⟮I, I⟯ V) (x : M) : M :=
  if hU : x ∈ U then φ ⟨x, hU⟩ else if hV : x ∈ V then φ.symm ⟨x, hV⟩ else x

private theorem clopenSwapFun_of_mem_left (φ : U ≃ₘ^n⟮I, I⟯ V) (x : U) :
    clopenSwapFun φ x = φ x := by
  simp [clopenSwapFun]

private theorem clopenSwapFun_of_mem_right (φ : U ≃ₘ^n⟮I, I⟯ V) (hUV : Disjoint U V) (y : V) :
    clopenSwapFun φ y = φ.symm y := by
  have hyU : (y : M) ∉ U := (Opens.coe_disjoint.2 hUV).symm.notMem_of_mem_left y.2
  simp [clopenSwapFun, hyU]

private theorem clopenSwapFun_of_notMem {φ : U ≃ₘ^n⟮I, I⟯ V} {x : M} (hU : x ∉ U) (hV : x ∉ V) :
    clopenSwapFun φ x = x := by
  simp [clopenSwapFun, hU, hV]

private theorem involutive_clopenSwapFun (φ : U ≃ₘ^n⟮I, I⟯ V) (hUV : Disjoint U V) :
    Function.Involutive (clopenSwapFun φ) := fun x ↦ by
  by_cases hU : x ∈ U
  · rw [clopenSwapFun_of_mem_left φ ⟨x, hU⟩, clopenSwapFun_of_mem_right φ hUV, symm_apply_apply]
  by_cases hV : x ∈ V
  · rw [clopenSwapFun_of_mem_right φ hUV ⟨x, hV⟩, clopenSwapFun_of_mem_left, apply_symm_apply]
  · rw [clopenSwapFun_of_notMem hU hV, clopenSwapFun_of_notMem hU hV]

private theorem contMDiff_clopenSwapFun (φ : U ≃ₘ^n⟮I, I⟯ V) (hU : IsClosed (U : Set M))
    (hV : IsClosed (V : Set M)) (hUV : Disjoint U V) : ContMDiff I I n (clopenSwapFun φ) := by
  intro x
  by_cases hxU : x ∈ U
  · -- On the open set `U` the map is `φ`.
    rw [← contMDiffAt_subtype_iff (x := (⟨x, hxU⟩ : U))]
    have : (fun y : U ↦ clopenSwapFun φ y) = fun y ↦ (φ y : M) :=
      funext (clopenSwapFun_of_mem_left φ)
    rw [this]
    exact (contMDiff_subtype_val.comp φ.contMDiff).contMDiffAt
  by_cases hxV : x ∈ V
  · -- On the open set `V` the map is `φ⁻¹`.
    rw [← contMDiffAt_subtype_iff (x := (⟨x, hxV⟩ : V))]
    have : (fun y : V ↦ clopenSwapFun φ y) = fun y ↦ (φ.symm y : M) :=
      funext (clopenSwapFun_of_mem_right φ hUV)
    rw [this]
    exact (contMDiff_subtype_val.comp φ.symm.contMDiff).contMDiffAt
  · -- Off the closed set `U ∪ V` the map is the identity.
    refine contMDiffAt_id.congr_of_eventuallyEq ?_
    filter_upwards [(hU.union hV).isOpen_compl.mem_nhds (by simp [hxU, hxV])] with y hy
    simp only [mem_compl_iff, mem_union, not_or] at hy
    exact clopenSwapFun_of_notMem hy.1 hy.2

/-- **Swapping two disjoint clopen pieces.** Given disjoint open subsets `U` and `V` of `M` that
are also closed, and a diffeomorphism `φ : U ≃ₘ V`, the self-diffeomorphism of `M` that acts as `φ`
on `U`, as `φ⁻¹` on `V` and as the identity on the rest of `M`. -/
def clopenSwap (φ : U ≃ₘ^n⟮I, I⟯ V) (hU : IsClosed (U : Set M)) (hV : IsClosed (V : Set M))
    (hUV : Disjoint U V) : M ≃ₘ^n⟮I, I⟯ M where
  toEquiv := (involutive_clopenSwapFun φ hUV).toPerm _
  contMDiff_toFun := contMDiff_clopenSwapFun φ hU hV hUV
  contMDiff_invFun := contMDiff_clopenSwapFun φ hU hV hUV

variable (φ : U ≃ₘ^n⟮I, I⟯ V) (hU : IsClosed (U : Set M)) (hV : IsClosed (V : Set M))
  (hUV : Disjoint U V)

/-- On `U`, the swap `Diffeomorph.clopenSwap` acts as `φ`. -/
@[simp]
theorem clopenSwap_apply_coe_left (x : U) : clopenSwap φ hU hV hUV x = φ x :=
  clopenSwapFun_of_mem_left φ x

/-- On `V`, the swap `Diffeomorph.clopenSwap` acts as `φ⁻¹`. -/
@[simp]
theorem clopenSwap_apply_coe_right (y : V) : clopenSwap φ hU hV hUV y = φ.symm y :=
  clopenSwapFun_of_mem_right φ hUV y

/-- Off `U ∪ V`, the swap `Diffeomorph.clopenSwap` is the identity. -/
theorem clopenSwap_apply_of_notMem {x : M} (hxU : x ∉ U) (hxV : x ∉ V) :
    clopenSwap φ hU hV hUV x = x :=
  clopenSwapFun_of_notMem (φ := φ) hxU hxV

/-- The swap `Diffeomorph.clopenSwap` is its own inverse. -/
@[simp]
theorem clopenSwap_symm : (clopenSwap φ hU hV hUV).symm = clopenSwap φ hU hV hUV :=
  (rfl)

end Diffeomorph
