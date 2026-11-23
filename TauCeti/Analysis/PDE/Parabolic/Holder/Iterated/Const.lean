/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation

/-!
# Constant maps in the parabolic Hölder spaces of every order

A constant map `(x, t) ↦ c` on a slab `E × [a, b]` lies in the bounded parabolic Hölder space
`C_{par,b}^{k+α}` of every order `k` (`TauCeti.ParabolicCkHolderSpace.const`): its field
`D_t^0 D_x^0` is `c` and all its other mixed derivatives vanish. Its norm is at most `2 ‖c‖`
(`TauCeti.ParabolicCkHolderSpace.norm_const_le`): for `k ≤ 1` the norm counts the supremum of the
value once as a bounded field and once more in a Hölder norm, and for `k ≥ 2` it is `‖c‖`.

Constant maps are the coefficients of constant-coefficient operators. For instance the heat
operator `∂ₜ - Δ` is the parabolic operator whose second-order coefficient is the constant trace
functional on Hessians, as for the constant maps `TauCeti.HolderSpace.const` of order zero and
`TauCeti.ParabolicC2HolderSpace.const` of order two.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.const`: the constant map `c` as an element of `C_{par,b}^{k+α}`.
* `TauCeti.ParabolicCkHolderSpace.const_apply`,
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_zero_zero_const_apply`,
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_succ_const` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_const_succ`: its values and its fields.
* `TauCeti.ParabolicCkHolderSpace.timeDerivL_const` and
  `TauCeti.ParabolicCkHolderSpace.spatialFDerivL_const`: its derivatives vanish.
* `TauCeti.ParabolicCkHolderSpace.norm_const_le`: the bound `‖const c‖ ≤ 2 ‖c‖`.
-/

public section

noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

namespace ParabolicCkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The fields of a constant map `c`: the constant `c`, read as a `0`-multilinear map, at the pair
`(0, 0)`, and zero at every other pair. -/
private def constField (c : F) : ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => BoundedContinuousFunction.const _ ((continuousMultilinearCurryFin0 ℝ E F).symm c)
  | 0, _ + 1 => 0
  | _ + 1, _ => 0

private theorem constField_zero_zero_apply (c : F) (p : slab (E := E) a b) :
    constField c 0 0 p = (continuousMultilinearCurryFin0 ℝ E F).symm c := (rfl)

private theorem constField_succ_right (c : F) (r m : ℕ) :
    constField (E := E) (a := a) (b := b) c r (m + 1) = 0 := by
  cases r <;> rfl

private theorem constField_succ_left (c : F) (r m : ℕ) :
    constField (E := E) (a := a) (b := b) c (r + 1) m = 0 := (rfl)

private theorem constField_apply_eq (c : F) (r m : ℕ) (p q : slab (E := E) a b) :
    constField c r m p = constField c r m q := by
  rcases r with _ | r <;> rcases m with _ | m <;> rfl

private theorem norm_constField_eq_zero (c : F) {r m : ℕ} (h : (r, m) ≠ (0, 0)) :
    ‖constField (E := E) (a := a) (b := b) c r m‖ = 0 := by
  rcases r with _ | r
  · rcases m with _ | m
    · exact absurd rfl h
    · rw [constField_succ_right]
      exact norm_zero (E := slab (E := E) a b →ᵇ (E [×(m + 1)]→L[ℝ] F))
  · rw [constField_succ_left]
    exact norm_zero (E := slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F))

private theorem holderWith_zero_constField (c : F) (r m : ℕ) {X : Type*} [PseudoMetricSpace X]
    (β : ℝ≥0) (g : X → slab (E := E) a b) :
    HolderWith 0 β fun x ↦ constField c r m (g x) :=
  holderWith_zero_iff.2 fun _ _ ↦ constField_apply_eq c r m _ _

/-- **Constant maps** belong to the bounded parabolic Hölder space of every order: the map
`(x, t) ↦ c` has the field `D_t^0 D_x^0 = c` and all other fields zero. -/
def const (c : F) : ParabolicCkHolderSpace k α E F hab :=
  mk (constField c)
    (fun r m _ t x ↦ by
      rw [constField_succ_right, FunLike.coe_zero, Pi.zero_apply]
      have hc : (fun y ↦ constField c r m (slabMk y t)) =
          fun _ ↦ constField c r m (slabMk x t) :=
        funext fun y ↦ constField_apply_eq c r m _ _
      rw [hc]
      convert hasFDerivAt_const (constField c r m (slabMk x t)) x using 1
      ext
      simp)
    (fun r m _ x t ↦ by
      rw [constField_succ_left, FunLike.coe_zero, Pi.zero_apply]
      have hc : ParabolicC2HolderSpace.timeExtension hab.le (constField c r m) x =
          fun _ ↦ constField c r m (slabMk x t) := by
        rw [ParabolicC2HolderSpace.timeExtension_def]
        exact funext fun s ↦ constField_apply_eq c r m _ _
      rw [hc]
      exact hasDerivWithinAt_const _ _ _)
    (fun r m _ ↦ ⟨0, fun x ↦ holderWith_zero_constField c r m _ (slabMk x)⟩)
    fun r m _ ↦ (holderWith_zero_constField c r m α id).memHolder

/-- A constant map takes its value everywhere. -/
@[simp]
theorem const_apply (c : F) (p : slab (E := E) a b) :
    (const c : ParabolicCkHolderSpace k α E F hab) p = c := by
  rw [const, mk_apply, constField_zero_zero_apply]
  simp

/-- The field `D_t^0 D_x^0` of a constant map is the constant, read as a `0`-multilinear map. -/
@[simp]
theorem mixedDerivL_zero_zero_const_apply (c : F) (p : slab (E := E) a b) :
    mixedDerivL 0 0 (const c : ParabolicCkHolderSpace k α E F hab) p =
      (continuousMultilinearCurryFin0 ℝ E F).symm c := by
  rw [const, mixedDerivL_mk _ _ _ _ (Nat.zero_le k), constField_zero_zero_apply]

/-- The time derivatives of a constant map vanish. -/
@[simp]
theorem mixedDerivL_succ_const (c : F) (r m : ℕ) :
    mixedDerivL (r + 1) m (const c : ParabolicCkHolderSpace k α E F hab) = 0 := by
  by_cases h : 2 * (r + 1) + m ≤ k
  · rw [const, mixedDerivL_mk _ _ _ _ h, constField_succ_left]
  · rw [mixedDerivL_of_lt (by omega), _root_.zero_apply]

/-- The spatial derivatives of a constant map vanish. -/
@[simp]
theorem mixedDerivL_const_succ (c : F) (r m : ℕ) :
    mixedDerivL r (m + 1) (const c : ParabolicCkHolderSpace k α E F hab) = 0 := by
  by_cases h : 2 * r + (m + 1) ≤ k
  · rw [const, mixedDerivL_mk _ _ _ _ h, constField_succ_right]
  · rw [mixedDerivL_of_lt (by omega), _root_.zero_apply]

/-- The time derivative of a constant map vanishes. -/
@[simp]
theorem timeDerivL_const (c : F) :
    timeDerivL k α E F hab (const c) = 0 := by
  ext p
  simp [timeDerivL_apply, mixedDerivL_succ_const c 0 0]

/-- The spatial derivative of a constant map vanishes. -/
@[simp]
theorem spatialFDerivL_const (c : F) :
    spatialFDerivL k α E F hab (const c) = 0 := by
  ext p
  simp [spatialFDerivL_apply, mixedDerivL_const_succ c 0 0]

/-- A constant map has norm at most twice the norm of its value, uniformly in `k`. The factor `2`
is needed only for `k ≤ 1`, where the norm counts the supremum of the value once as a bounded field
and once more in a Hölder norm (of the field itself for `k = 0`, of its time slices for `k = 1`).
For `k ≥ 2` the value enters only as a bounded field, and the norm is `‖c‖`. -/
theorem norm_const_le (c : F) : ‖(const c : ParabolicCkHolderSpace k α E F hab)‖ ≤ 2 * ‖c‖ := by
  have hfield (p : ℕ × ℕ) (hp : p ∈ parabolicDerivPairs k) :
      mixedDerivL p.1 p.2 (const c : ParabolicCkHolderSpace k α E F hab) =
        constField c p.1 p.2 := by
    rw [const, mixedDerivL_mk _ _ _ _ (mem_parabolicDerivPairs.1 hp)]
  set u : ParabolicCkHolderSpace k α E F hab := const c
  have hpair (p : ℕ × ℕ) (hp : p ∈ parabolicDerivPairs k) :
      ‖mixedDerivL p.1 p.2 u‖ + (‖timeSliceL p.1 p.2 u‖ + ‖mixedDerivHolderL p.1 p.2 u‖) ≤
        2 * ‖constField (E := E) (a := a) (b := b) c p.1 p.2‖ := by
    have hc (q q' : slab (E := E) a b) : mixedDerivL p.1 p.2 u q = mixedDerivL p.1 p.2 u q' := by
      rw [hfield p hp]
      exact constField_apply_eq c p.1 p.2 q q'
    simpa using norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le (C := 0) u
      (congrArg norm (hfield p hp)).le
      (fun _ _ ↦ holderWith_zero_iff.2 fun _ _ ↦ hc _ _) (fun _ ↦ holderWith_zero_iff.2 hc)
  have h00 : (0, 0) ∈ parabolicDerivPairs k := mem_parabolicDerivPairs.2 (by omega)
  rw [norm_eq]
  refine (Finset.sum_le_sum hpair).trans ?_
  rw [Finset.sum_eq_single_of_mem (0, 0) h00 fun p _ hp ↦ ?_]
  · gcongr
    refine (BoundedContinuousFunction.norm_const_le _).trans_eq ?_
    exact LinearIsometryEquiv.norm_map _ c
  · rw [norm_constField_eq_zero c (r := p.1) (m := p.2) (by simpa using hp), mul_zero]

end ParabolicCkHolderSpace

end TauCeti
