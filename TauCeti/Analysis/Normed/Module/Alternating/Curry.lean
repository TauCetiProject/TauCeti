/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Comparing normed and topological interior products

The normed `ContinuousAlternatingMap.curryLeft` agrees pointwise with the norm-free
`ContinuousAlternatingMap.curryLeftTopological`. This comparison lets normed applications use
the topological interior-product API without importing wedge constructions.

A continuous alternating map of one vector is read as a continuous linear functional by
`ContinuousAlternatingMap.toDual`. Currying a continuous alternating map of two vectors in its
first slot and reading the result as a linear map gives its **flat map** `f ↦ (v ↦ f(v, ·))`, a
continuous linear map `ContinuousAlternatingMap.flatL`, an alternating bilinear map
(`ContinuousAlternatingMap.isAlt_toLinearMap₁₂_flatL`) whose value at `v` has norm at most
`‖f‖ ‖v‖` (`ContinuousAlternatingMap.norm_flatL_apply_le`). Invertibility of flat maps is an open
condition with uniform bounds: a continuous family of such maps with invertible flat map at one
point has flat maps uniformly bounded below nearby
(`ContinuousAlternatingMap.exists_eventually_norm_le_mul_norm_flatL_apply`).
-/

public section

namespace ContinuousAlternatingMap

variable {E F₁ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]

/-- The normed and norm-free interior products agree on normed spaces. -/
theorem curryLeft_eq_curryLeftTopological {n : ℕ}
    (f : E [⋀^Fin (n + 1)]→L[ℝ] F₁) (x : E) :
    f.curryLeft x = f.curryLeftTopological x := by
  ext v
  simp only [ContinuousAlternatingMap.curryLeft_apply_apply,
    ContinuousAlternatingMap.curryLeftTopological_apply_apply]

section toDual

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A one-form at a point, read as a continuous linear functional. -/
noncomputable def toDual : (E [⋀^Fin 1]→L[𝕜] 𝕜) →L[𝕜] E →L[𝕜] 𝕜 :=
  (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := 𝕜) (ι := Fin 1)
    0).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The functional of a one-form evaluates the form on the one-vector family. -/
@[simp]
theorem toDual_apply (a : E [⋀^Fin 1]→L[𝕜] 𝕜) (v : E) : toDual a v = a ![v] := by
  simp only [toDual, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ofSubsingletonLIE_symm_apply, ofSubsingleton_symm_apply_apply]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

end toDual

section flatL

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The **flat map** of continuous alternating maps of two vectors, `f ↦ (v ↦ f(v, ·))`: currying
in the first slot, then reading the resulting alternating map of one vector as a linear map. -/
noncomputable def flatL : (E [⋀^Fin 2]→L[𝕜] F) →L[𝕜] E →L[𝕜] E →L[𝕜] F :=
  ContinuousLinearMap.compL 𝕜 E (E [⋀^Fin 1]→L[𝕜] F) (E →L[𝕜] F)
      (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F) (ι := Fin 1)
        0).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := 1)).toContinuousLinearMap

/-- The flat map of `f` at `v`, read back as an alternating map of one vector, is the curried
map `f(v, ·)`. -/
@[simp]
theorem ofSubsingleton_flatL_apply (f : E [⋀^Fin 2]→L[𝕜] F) (v : E) :
    ofSubsingleton 𝕜 E F (0 : Fin 1) (flatL 𝕜 E F f v) = f.curryLeft v :=
  (ofSubsingletonLIE (𝕜 := 𝕜) (E := E) (F := F) (ι := Fin 1) 0).apply_symm_apply _

/-- The flat map evaluates the alternating map on the pair. -/
@[simp]
theorem flatL_apply_apply (f : E [⋀^Fin 2]→L[𝕜] F) (v w : E) : flatL 𝕜 E F f v w = f ![v, w] :=
  DFunLike.congr_fun (ofSubsingleton_flatL_apply f v) ![w]

/-- The flat map of `f` at `v` has norm at most `‖f‖ ‖v‖`. -/
theorem norm_flatL_apply_le (f : E [⋀^Fin 2]→L[𝕜] F) (v : E) :
    ‖flatL 𝕜 E F f v‖ ≤ ‖f‖ * ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ by
    rw [flatL_apply_apply, mul_assoc]
    simpa [Fin.prod_univ_two] using f.le_opNorm ![v, w]

open Filter Topology in
/-- A family of continuous alternating maps of two vectors, continuous at `z₀` and with invertible
flat map at `z₀`, has flat maps uniformly bounded below near `z₀`. -/
theorem exists_eventually_norm_le_mul_norm_flatL_apply {X : Type*} [TopologicalSpace X]
    {ω : X → E [⋀^Fin 2]→L[𝕜] F} {z₀ : X} (hω : ContinuousAt ω z₀)
    (h : (flatL 𝕜 E F (ω z₀)).IsInvertible) :
    ∃ C, 0 < C ∧ ∀ᶠ z in 𝓝 z₀, ∀ v, ‖v‖ ≤ C * ‖flatL 𝕜 E F (ω z) v‖ := by
  set S : X → E →L[𝕜] E →L[𝕜] F := fun z ↦ flatL 𝕜 E F (ω z)
  obtain ⟨e, he⟩ : (S z₀).IsInvertible := h
  obtain ⟨C, hC, hCb⟩ := (e.symm : (E →L[𝕜] F) →L[𝕜] E).bound
  have h₀ (v : E) : ‖v‖ ≤ C * ‖S z₀ v‖ := by
    rw [← he]
    simpa using hCb (e v)
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [(tendsto_iff_norm_sub_tendsto_zero.1 hω.tendsto).eventually
    (gt_mem_nhds (inv_pos.2 (mul_pos two_pos hC)))] with z hz
  refine ContinuousLinearMap.norm_le_two_mul_mul_norm_apply_of_forall_norm_le h₀ ?_
  -- `S z - S z₀` is the flat map of `ω z - ω z₀`.
  have hd : ‖S z - S z₀‖ ≤ ‖ω z - ω z₀‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v ↦ by
      have h : (S z - S z₀) v = flatL 𝕜 E F (ω z - ω z₀) v := by
        simp only [S, map_sub, _root_.sub_apply]
      rw [h]
      exact norm_flatL_apply_le _ v
  calc C * ‖S z - S z₀‖ ≤ C * (2 * C)⁻¹ := by gcongr; exact hd.trans hz.le
    _ = 1 / 2 := by field_simp

/-- The flat map of a continuous alternating map of two vectors, read as a bilinear map, is
alternating. -/
theorem isAlt_toLinearMap₁₂_flatL (f : E [⋀^Fin 2]→L[𝕜] F) :
    (flatL 𝕜 E F f).toLinearMap₁₂.IsAlt := fun v ↦ by
  simp [f.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl Fin.zero_ne_one]

end flatL

end ContinuousAlternatingMap
