/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Iterated
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Normed.Module.Multilinear.Basic

/-!
# Composition with linear maps in bounded Hölder spaces

Precomposition by a continuous linear map acts boundedly on `CkHolderSpace`. The derivative
of order `i` is pulled back in all `i` arguments, and the top Hölder seminorm acquires the
additional factor `‖e‖^α`. Invertible linear coordinate changes therefore give continuous
linear equivalences. These maps transport spatial initial data together with parabolic
changes of coordinates.

Postcomposition by a continuous linear map `g : F →L[ℝ] G` of the values also acts boundedly
(`TauCeti.CkHolderSpace.compLeftL`), with operator norm at most `‖g‖`: every derivative of `g ∘ f`
is `g` applied to the corresponding derivative of `f`. For instance, the real part of a
complex-valued bounded `C^{k,α}` map is a real-valued one.

The constructions use Mathlib's `ContinuousLinearMap.iteratedFDeriv_comp_right`,
`ContinuousMultilinearMap.compContinuousLinearMapL`,
`ContinuousLinearMap.iteratedFDeriv_comp_left` and
`ContinuousLinearMap.compContinuousMultilinearMapL`.
-/

public section
noncomputable section

namespace TauCeti.CkHolderSpace

open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E E' E'' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section compLinear

private theorem holderWith_iteratedFDeriv_comp (e : E →L[ℝ] E')
    (f : CkHolderSpace k α E' F) :
    HolderWith (‖e‖₊ ^ k * nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) * ‖e‖₊ ^ (α : ℝ)) α
      (_root_.iteratedFDeriv ℝ k (f ∘ e)) := by
  have hnorm : ‖ContinuousMultilinearMap.compContinuousLinearMapL
      (F := F) (fun _ : Fin k ↦ e)‖₊ ≤ ‖e‖₊ ^ k := by
    apply NNReal.coe_le_coe.mp
    simpa using ContinuousMultilinearMap.norm_compContinuousLinearMapL_le F
      (fun _ : Fin k ↦ e)
  have h := ((ContinuousMultilinearMap.compContinuousLinearMapL
    (F := F) (fun _ : Fin k ↦ e)).lipschitzWith.holderWith.comp
      (f.memHolder_iteratedFDeriv.holderWith.comp e.lipschitzWith.holderWith))
  simp only [mul_one, one_mul] at h
  have heq : _root_.iteratedFDeriv ℝ k (f ∘ e) = fun x ↦
      ContinuousMultilinearMap.compContinuousLinearMapL (F := F) (fun _ : Fin k ↦ e)
        (_root_.iteratedFDeriv ℝ k f (e x)) :=
    funext fun x ↦ e.iteratedFDeriv_comp_right f.contDiff x le_rfl
  rw [heq]
  convert h.mono (mul_le_mul_of_nonneg_right hnorm (by positivity)) using 1
  · simp [mul_assoc]
  · rfl

/-- Precomposition of a bounded `C^{k,α}` function by a continuous linear map. -/
private def compLinear (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) : CkHolderSpace k α E F :=
  ofContDiff (f ∘ e) (f.contDiff.comp e.contDiff)
    (fun i hi ↦ ⟨‖f.iteratedFDeriv ⟨i, by omega⟩‖ * ‖e‖ ^ i, fun x ↦ by
      refine (e.norm_iteratedFDeriv_comp_right_le f.contDiff x (by exact_mod_cast hi)).trans ?_
      gcongr
      rw [iteratedFDeriv_eq f ⟨i, by omega⟩]
      exact BoundedContinuousFunction.norm_coe_le_norm _ _⟩)
    (holderWith_iteratedFDeriv_comp e f).memHolder

@[simp]
private theorem compLinear_apply (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) (x : E) :
    compLinear e f x = f (e x) := by
  simp [compLinear]

@[simp]
private theorem coe_compLinear (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) :
    ⇑(compLinear e f) = f ∘ e :=
  funext (compLinear_apply e f)

private theorem iteratedFDeriv_compLinear (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F)
    (i : Fin (k + 1)) (x : E) :
    (compLinear e f).iteratedFDeriv i x =
      (f.iteratedFDeriv i (e x)).compContinuousLinearMap (fun _ ↦ e) := by
  rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq]
  rw [coe_compLinear]
  exact e.iteratedFDeriv_comp_right f.contDiff x (by exact_mod_cast Nat.le_of_lt_succ i.isLt)

/-- A linear change of coordinates multiplies the norm by at most
`max(1, ‖e‖)^k max(1, ‖e‖^α)`. -/
private theorem norm_compLinear_le (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) :
    ‖compLinear e f‖ ≤ (max 1 ‖e‖) ^ k * max 1 (‖e‖ ^ (α : ℝ)) * ‖f‖ := by
  let C := (max 1 ‖e‖) ^ k * max 1 (‖e‖ ^ (α : ℝ))
  have hpow (i : Fin (k + 1)) : ‖e‖ ^ (i : ℕ) ≤ C := by
    calc
      ‖e‖ ^ (i : ℕ) ≤ (max 1 ‖e‖) ^ (i : ℕ) := by gcongr; exact le_max_right _ _
      _ ≤ (max 1 ‖e‖) ^ k := pow_le_pow_right₀ (le_max_left _ _) (by omega)
      _ ≤ C := le_mul_of_one_le_right (by positivity) (le_max_left _ _)
  have hfield (i : Fin (k + 1)) :
      ‖(compLinear e f).iteratedFDeriv i‖ ≤ C * ‖f.iteratedFDeriv i‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [← iteratedFDeriv_eq, coe_compLinear]
    refine (e.norm_iteratedFDeriv_comp_right_le f.contDiff x
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt)).trans ?_
    rw [iteratedFDeriv_eq f i]
    calc
      _ ≤ ‖f.iteratedFDeriv i‖ * C := mul_le_mul
        (BoundedContinuousFunction.norm_coe_le_norm _ _) (hpow i) (by positivity) (by positivity)
      _ = _ := mul_comm _ _
  have htop : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k (compLinear e f)) : ℝ) ≤
      C * nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) := by
    rw [coe_compLinear]
    have h := (holderWith_iteratedFDeriv_comp e f).nnholderNorm_le
    have hk : ‖e‖ ^ k ≤ (max 1 ‖e‖) ^ k := by gcongr; exact le_max_right _ _
    have he' : ‖e‖ ^ k * ‖e‖ ^ (α : ℝ) ≤ C :=
      mul_le_mul hk (le_max_right _ _) (by positivity) (by positivity)
    have h' : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k (f ∘ e)) : ℝ) ≤
        ‖e‖ ^ k * nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) * ‖e‖ ^ (α : ℝ) := by
      exact_mod_cast h
    have hmul := mul_le_mul_of_nonneg_right he'
      (NNReal.coe_nonneg (nnHolderNorm α (_root_.iteratedFDeriv ℝ k f)))
    exact h'.trans (by nlinarith only [hmul])
  rw [norm_eq, norm_eq, mul_add, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) htop

/-- Precomposition by a continuous linear map as a bounded linear operator. -/
def compLinearL (e : E →L[ℝ] E') : CkHolderSpace k α E' F →L[ℝ] CkHolderSpace k α E F :=
  LinearMap.mkContinuous
    { toFun := compLinear e
      map_add' f g := ext fun x ↦ by simp [coe_add]
      map_smul' c f := ext fun x ↦ by simp [coe_smul] }
    _ (norm_compLinear_le e)

private theorem compLinearL_eq_compLinear (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) :
    compLinearL e f = compLinear e f :=
  (rfl)

@[simp]
theorem compLinearL_apply (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) (x : E) :
    compLinearL e f x = f (e x) := by
  rw [compLinearL_eq_compLinear, compLinear_apply]

@[simp]
theorem coe_compLinearL (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F) :
    ⇑(compLinearL e f) = f ∘ e :=
  funext (compLinearL_apply e f)

/-- The exact pullback formula for every recorded derivative field. -/
@[simp]
theorem iteratedFDeriv_compLinearL (e : E →L[ℝ] E') (f : CkHolderSpace k α E' F)
    (i : Fin (k + 1)) (x : E) :
    (compLinearL e f).iteratedFDeriv i x =
      (f.iteratedFDeriv i (e x)).compContinuousLinearMap (fun _ ↦ e) := by
  rw [compLinearL_eq_compLinear, iteratedFDeriv_compLinear]

/-- The operator norm bound for linear precomposition. -/
theorem norm_compLinearL_le (e : E →L[ℝ] E') :
    ‖compLinearL (k := k) (α := α) (F := F) e‖ ≤
      (max 1 ‖e‖) ^ k * max 1 (‖e‖ ^ (α : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_compLinear_le e)

@[simp]
theorem compLinearL_id (f : CkHolderSpace k α E F) : compLinearL (.id ℝ E) f = f :=
  ext fun _ ↦ by simp

@[simp]
theorem compLinearL_compLinearL (e : E →L[ℝ] E') (e' : E' →L[ℝ] E'')
    (f : CkHolderSpace k α E'' F) :
    compLinearL e (compLinearL e' f) = compLinearL (e'.comp e) f :=
  ext fun _ ↦ by simp

/-- Invertible linear coordinate changes on bounded `C^{k,α}` functions. -/
def compLinearCLE (e : E ≃L[ℝ] E') : CkHolderSpace k α E' F ≃L[ℝ] CkHolderSpace k α E F :=
  { compLinearL (k := k) (α := α) (F := F) (e : E →L[ℝ] E') with
    invFun := compLinearL (e.symm : E' →L[ℝ] E)
    left_inv f := ext fun x ↦ by simp
    right_inv f := ext fun x ↦ by simp
    continuous_toFun := (compLinearL (e : E →L[ℝ] E')).continuous
    continuous_invFun := (compLinearL (e.symm : E' →L[ℝ] E)).continuous }

@[simp]
theorem compLinearCLE_apply (e : E ≃L[ℝ] E') (f : CkHolderSpace k α E' F) :
    compLinearCLE e f = compLinearL (e : E →L[ℝ] E') f :=
  (rfl)

@[simp]
theorem compLinearCLE_symm_apply (e : E ≃L[ℝ] E') (f : CkHolderSpace k α E F) :
    (compLinearCLE e).symm f = compLinearL (e.symm : E' →L[ℝ] E) f :=
  (rfl)

end compLinear

section compLeft

variable {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup G'] [NormedSpace ℝ G']

private theorem iteratedFDeriv_comp_left (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) {i : ℕ}
    (hi : i ≤ k) (x : E) :
    _root_.iteratedFDeriv ℝ i (g ∘ f) x =
      g.compContinuousMultilinearMap (_root_.iteratedFDeriv ℝ i f x) :=
  g.iteratedFDeriv_comp_left f.contDiff.contDiffAt (by exact_mod_cast hi)

private theorem holderWith_iteratedFDeriv_comp_left (g : F →L[ℝ] G)
    (f : CkHolderSpace k α E F) :
    HolderWith (‖g‖₊ * nnHolderNorm α (_root_.iteratedFDeriv ℝ k f)) α
      (_root_.iteratedFDeriv ℝ k (g ∘ f)) := by
  -- The top derivative of `g ∘ f` is the top derivative of `f` followed by the continuous linear
  -- map `A ↦ g ∘ A` on multilinear maps, whose norm is at most `‖g‖`.
  set L := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k ↦ E) F G g
  have hL : ‖L‖₊ ≤ ‖g‖₊ := NNReal.coe_le_coe.mp g.norm_compContinuousMultilinearMapL_le
  have h := L.lipschitzWith.holderWith.comp f.memHolder_iteratedFDeriv.holderWith
  simp only [NNReal.coe_one, NNReal.rpow_one, one_mul] at h
  have heq : _root_.iteratedFDeriv ℝ k (g ∘ f) = L ∘ _root_.iteratedFDeriv ℝ k f :=
    funext fun x ↦ iteratedFDeriv_comp_left g f le_rfl x
  rw [heq]
  exact h.mono (mul_le_mul_of_nonneg_right hL (zero_le))

/-- Postcomposition of a bounded `C^{k,α}` map with a continuous linear map. -/
private def compLeft (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) : CkHolderSpace k α E G :=
  ofContDiff (g ∘ f) (g.contDiff.comp f.contDiff)
    (fun i hi ↦ ⟨‖g‖ * ‖f‖, fun x ↦ by
      rw [iteratedFDeriv_comp_left g f hi x]
      exact (g.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul_of_nonneg_left (f.norm_iteratedFDeriv_apply_le hi x) (norm_nonneg g))⟩)
    (holderWith_iteratedFDeriv_comp_left g f).memHolder

private theorem coe_compLeft (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) :
    ⇑(compLeft g f) = g ∘ f := by
  simp [compLeft]

/-- Postcomposition with `g` multiplies the norm by at most `‖g‖`. -/
private theorem norm_compLeft_le (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) :
    ‖compLeft g f‖ ≤ ‖g‖ * ‖f‖ := by
  have hfield (i : Fin (k + 1)) :
      ‖(compLeft g f).iteratedFDeriv i‖ ≤ ‖g‖ * ‖f.iteratedFDeriv i‖ := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [← iteratedFDeriv_eq, coe_compLeft, iteratedFDeriv_comp_left g f (Nat.lt_succ_iff.1 i.isLt),
      iteratedFDeriv_eq f i]
    exact (g.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm _ _) (norm_nonneg g))
  have htop : (nnHolderNorm α (_root_.iteratedFDeriv ℝ k (compLeft g f)) : ℝ) ≤
      ‖g‖ * nnHolderNorm α (_root_.iteratedFDeriv ℝ k f) := by
    rw [coe_compLeft]
    exact_mod_cast (holderWith_iteratedFDeriv_comp_left g f).nnholderNorm_le
  rw [norm_eq, norm_eq, mul_add, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ ↦ hfield i) htop

/-- Postcomposition with a continuous linear map `g` of the values, as a bounded linear operator
between spaces of bounded `C^{k,α}` maps. -/
def compLeftL (g : F →L[ℝ] G) : CkHolderSpace k α E F →L[ℝ] CkHolderSpace k α E G :=
  LinearMap.mkContinuous
    { toFun := compLeft g
      map_add' f₁ f₂ := ext fun x ↦ by simp [coe_compLeft, coe_add]
      map_smul' c f := ext fun x ↦ by simp [coe_compLeft, coe_smul] }
    ‖g‖ (norm_compLeft_le g)

private theorem compLeftL_eq_compLeft (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) :
    compLeftL g f = compLeft g f :=
  (rfl)

@[simp]
theorem compLeftL_apply (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) (x : E) :
    compLeftL g f x = g (f x) := by
  rw [compLeftL_eq_compLeft, coe_compLeft, Function.comp_apply]

theorem coe_compLeftL (g : F →L[ℝ] G) (f : CkHolderSpace k α E F) :
    ⇑(compLeftL g f) = g ∘ f :=
  funext (compLeftL_apply g f)

/-- The derivative fields of `g ∘ f` are those of `f` followed by `g`. -/
@[simp]
theorem iteratedFDeriv_compLeftL (g : F →L[ℝ] G) (f : CkHolderSpace k α E F)
    (i : Fin (k + 1)) (x : E) :
    (compLeftL g f).iteratedFDeriv i x = g.compContinuousMultilinearMap (f.iteratedFDeriv i x) := by
  rw [← iteratedFDeriv_eq, ← iteratedFDeriv_eq, coe_compLeftL]
  exact iteratedFDeriv_comp_left g f (Nat.lt_succ_iff.1 i.isLt) x

/-- The operator norm of postcomposition with `g` is at most `‖g‖`. -/
theorem norm_compLeftL_le (g : F →L[ℝ] G) :
    ‖compLeftL (k := k) (α := α) (E := E) g‖ ≤ ‖g‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg g) _

@[simp]
theorem compLeftL_id (f : CkHolderSpace k α E F) : compLeftL (.id ℝ F) f = f :=
  ext fun _ ↦ by simp

@[simp]
theorem compLeftL_compLeftL (g : F →L[ℝ] G) (g' : G →L[ℝ] G') (f : CkHolderSpace k α E F) :
    compLeftL g' (compLeftL g f) = compLeftL (g'.comp g) f :=
  ext fun _ ↦ by simp

end compLeft

end TauCeti.CkHolderSpace
