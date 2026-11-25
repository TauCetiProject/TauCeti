/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.Curry
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Comparing normed and topological interior products

The normed `ContinuousAlternatingMap.curryLeft` agrees pointwise with the norm-free
`ContinuousAlternatingMap.curryLeftTopological`. This comparison lets normed applications use
the topological interior-product API without importing wedge constructions. Currying commutes
with subtraction (`ContinuousAlternatingMap.curryLeft_sub`), and the difference of two curried maps
`f(u, ·)` and `g(v, ·)` is bounded by `‖f - g‖ ‖u‖ + ‖g‖ ‖u - v‖`
(`ContinuousAlternatingMap.norm_curryLeft_sub_curryLeft_le`). Iterating `curryLeft` inserts a
family `u` of `N` vectors in the first `N` slots (`ContinuousAlternatingMap.curryLeftVec`), which
evaluates as the map on `u` followed by the arguments
(`ContinuousAlternatingMap.curryLeftVec_apply`) and depends continuously on the map and on `u`
(`Continuous.curryLeftVec`).

A continuous alternating map of one vector is read as a continuous linear functional by
`ContinuousAlternatingMap.toDual`. Currying a continuous alternating map of two vectors in its
first slot and reading the result as a linear map gives its **flat map** `f ↦ (v ↦ f(v, ·))`, a
continuous linear map `ContinuousAlternatingMap.flatL`, an alternating bilinear map
(`ContinuousAlternatingMap.isAlt_toLinearMap₁₂_flatL`).

The interior product `f ↦ f.curryLeft x` with a fixed vector `x`, as a continuous linear map
depending linearly on `x`, is `ContinuousAlternatingMap.curryLeftFlipL`, of norm at most `‖x‖`.
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

/-- The interior product of a pullback `A^* α` with `v`, restricted along `B`, is bounded by
`‖α‖ ‖A v‖ ‖A ∘ B‖ ^ n`: only the contracted slot sees `A v`. -/
theorem norm_curryLeft_compContinuousLinearMap_compContinuousLinearMap_le {𝕜 X Y G F : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y]
    [NormedSpace 𝕜 Y] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {n : ℕ} (α : G [⋀^Fin (n + 1)]→L[𝕜] F) (A : X →L[𝕜] G) (v : X)
    (B : Y →L[𝕜] X) :
    ‖((α.compContinuousLinearMap A).curryLeft v).compContinuousLinearMap B‖ ≤
      ‖α‖ * ‖A v‖ * ‖A.comp B‖ ^ n := by
  rw [curryLeft_compContinuousLinearMap]
  -- Pulling back along `A` and then along `B` is pulling back along `A ∘ B`: on vectors `u`,
  -- both sides evaluate to `α.curryLeft (A v) (A ∘ B ∘ u)`.
  calc _ = ‖(α.curryLeft (A v)).compContinuousLinearMap (A.comp B)‖ := by congr 1
    _ ≤ ‖α.curryLeft (A v)‖ * ‖A.comp B‖ ^ n :=
        (norm_compContinuousLinearMap_le _ _).trans_eq (by simp)
    _ ≤ ‖α‖ * ‖A v‖ * ‖A.comp B‖ ^ n := by
        gcongr
        exact (α.curryLeft.le_opNorm _).trans_eq (by rw [norm_curryLeft])

section Lipschitz

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Currying commutes with subtraction. -/
@[simp]
theorem curryLeft_sub {n : ℕ} (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    (f - g).curryLeft = f.curryLeft - g.curryLeft := by
  simpa using (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := n)).map_sub f g

/-- The difference of the curried maps `f(u, ·)` and `g(v, ·)` is bounded by
`‖f - g‖ ‖u‖ + ‖g‖ ‖u - v‖`. -/
theorem norm_curryLeft_sub_curryLeft_le {n : ℕ} (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) (u v : E) :
    ‖f.curryLeft u - g.curryLeft v‖ ≤ ‖f - g‖ * ‖u‖ + ‖g‖ * ‖u - v‖ := by
  have hsplit : f.curryLeft u - g.curryLeft v = (f - g).curryLeft u + g.curryLeft (u - v) := by
    rw [curryLeft_sub, map_sub, _root_.sub_apply]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_curryLeft]

end Lipschitz

section curryLeftVec

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {m : ℕ}

/-- The iterated interior product of a continuous alternating map with the vectors
`u 0, …, u (N - 1)`, inserted in its first `N` slots by `N` successive applications of
`ContinuousAlternatingMap.curryLeft`. -/
noncomputable def curryLeftVec :
    {N : ℕ} → (E [⋀^Fin (m + N)]→L[𝕜] F) → (Fin N → E) → E [⋀^Fin m]→L[𝕜] F
  | 0, f, _ => f
  | N + 1, f, u => curryLeftVec (curryLeft (n := m + N) f (u 0)) (Fin.tail u)

/-- The iterated interior product evaluates the map on the vectors `u` followed by the
arguments. -/
@[simp]
theorem curryLeftVec_apply :
    ∀ {N : ℕ} (f : E [⋀^Fin (m + N)]→L[𝕜] F) (u : Fin N → E) (t : Fin m → E),
      curryLeftVec f u t = f (Matrix.vecAppend (Nat.add_comm m N) u t)
  | 0, f, u, t => by
    rw [curryLeftVec]
    congr 1
    funext i
    simp [Matrix.vecAppend_eq_ite]
  | N + 1, f, u, t => by
    rw [curryLeftVec, curryLeftVec_apply, curryLeft_apply_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · simp [Matrix.vecAppend_eq_ite]
    · simp only [Matrix.vecAppend_eq_ite, Matrix.cons_val_succ, Fin.val_succ, Fin.tail]
      split_ifs with h₁ h₂ h₂
      · rfl
      · omega
      · omega
      · congr 1
        ext
        simp

/-- The iterated interior product of a continuous family of continuous alternating maps with a
continuous family of vectors is continuous. -/
theorem _root_.Continuous.curryLeftVec {X : Type*} [TopologicalSpace X] :
    ∀ {N : ℕ} {f : X → E [⋀^Fin (m + N)]→L[𝕜] F} {u : X → Fin N → E}, Continuous f →
      Continuous u → Continuous fun x ↦ curryLeftVec (f x) (u x)
  | 0, _, _, hf, _ => hf
  | N + 1, f, u, hf, hu =>
    Continuous.curryLeftVec (f := fun x ↦ curryLeft (n := m + N) (f x) (u x 0))
      (u := fun x ↦ Fin.tail (u x))
      (((curryLeftLI (n := m + N)).continuous.comp hf).clm_apply ((continuous_apply 0).comp hu))
      (continuous_pi fun i ↦ (continuous_apply i.succ).comp hu)

end curryLeftVec

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

/-- The flat map of a continuous alternating map of two vectors, read as a bilinear map, is
alternating. -/
theorem isAlt_toLinearMap₁₂_flatL (f : E [⋀^Fin 2]→L[𝕜] F) :
    (flatL 𝕜 E F f).toLinearMap₁₂.IsAlt := fun v ↦ by
  simp [f.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl Fin.zero_ne_one]

end flatL

section curryLeftFlipL

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}

/-- The interior product `f ↦ f.curryLeft x` of continuous alternating maps of `n + 1` vectors with
a fixed vector `x`, as a continuous linear map depending linearly on `x`: the flip of
`ContinuousAlternatingMap.curryLeftLI`. -/
noncomputable def curryLeftFlipL :
    E →L[𝕜] (E [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  (curryLeftLI (𝕜 := 𝕜) (E := E) (F := F) (n := n)).toContinuousLinearMap.flip

@[simp]
theorem curryLeftFlipL_apply_apply (x : E) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeftFlipL x f = f.curryLeft x :=
  (rfl)

/-- The interior product with `x` has norm at most `‖x‖`. -/
theorem norm_curryLeftFlipL_apply_le (x : E) :
    ‖(curryLeftFlipL x : (E [⋀^Fin (n + 1)]→L[𝕜] F) →L[𝕜] E [⋀^Fin n]→L[𝕜] F)‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ by
    rw [curryLeftFlipL_apply_apply, mul_comm]
    exact (f.curryLeft.le_opNorm x).trans_eq (by rw [norm_curryLeft])

end curryLeftFlipL

end ContinuousAlternatingMap
