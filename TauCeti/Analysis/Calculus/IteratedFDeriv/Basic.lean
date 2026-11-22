/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Iterated derivatives of iterated derivatives

The `i`-th iterated derivative of the `m`-th iterated derivative of a function has the same norm
as its `(i + m)`-th iterated derivative. This extends Mathlib's `norm_iteratedFDeriv_fderiv`, the
case `m = 1`, and lets bounds on all iterated derivatives of a function transfer to its iterated
derivative fields. The first iterated derivative, uncurried, is the Fréchet derivative
(`TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one`, with the function-level form
`TauCeti.fderiv_eq_continuousMultilinearCurryFin1_comp`), the `(n + 1)`-st iterated derivative
is the `n`-th iterated derivative of the Fréchet derivative, curried on the right
(`TauCeti.iteratedFDeriv_succ_eq_comp_right'`), while evaluating the third iterated
derivative on three directions gives the three-times curried Fréchet derivative
(`TauCeti.iteratedFDeriv_three_apply`). The file also supplies the
two-variable currying isometry used to identify continuous multilinear second derivatives with
curried bilinear maps, with the left currying of the one- and two-variable inverse curryings
(`TauCeti.curryLeft_continuousMultilinearCurryFin1_symm`,
`TauCeti.curryLeft_continuousMultilinearCurryFin2_symm`), and the corresponding exact comparison
for differences of second derivatives, which transfers Hölder bounds between the two forms of the
second derivative (`TauCeti.holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two`). The same holds
for the second iterated derivative of the `k`-th iterated derivative and the `(k + 2)`-th iterated
derivative (`TauCeti.holderOnWith_iteratedFDeriv_two_iteratedFDeriv_iff`).
Where a function `ζ` equals one on a neighbourhood of a point, every iterated derivative of
`ζ * u` there is that of `u` (`Filter.EventuallyEq.iteratedFDeriv_mul_eq`), and at a point of
which `s` is a neighbourhood every iterated derivative of `s.indicator g` is that of `g`
(`TauCeti.iteratedFDeriv_indicator_of_mem_nhds`). Bounded derivatives up
to a finite order have a common bound
(`TauCeti.exists_forall_norm_iteratedFDeriv_le_of_forall_exists`, and for derivatives of positive
order `TauCeti.exists_forall_norm_iteratedFDeriv_le_of_forall_one_le`), and such a
common bound is nonnegative and bounds the function itself
(`TauCeti.nonneg_and_norm_le_of_norm_iteratedFDeriv_le`). Adding a constant to a function does not
change its iterated derivatives of positive order (`TauCeti.iteratedFDeriv_succ_add_const`). The
iterated derivatives of a constant `c` have norm at most `‖c‖`
(`TauCeti.norm_iteratedFDeriv_const_le`), and those of positive order of the identity have norm at
most one (`TauCeti.norm_iteratedFDeriv_id_le_one`), as have those of right translations
(`TauCeti.norm_iteratedFDeriv_addRight_le`). The iterated derivatives of positive order of
a continuous linear map `L` are constant (`ContinuousLinearMap.iteratedFDeriv_succ_eq`), so
adding `L` to a differentiable function adds them to its derivatives of positive order
(`ContinuousLinearMap.iteratedFDeriv_succ_add_apply`) and does not change their Hölder constants
(`ContinuousLinearMap.holderOnWith_iteratedFDeriv_succ_add_left_iff`). For `f` of class `C^n` and
`m < n`, the derivative of `D^m f` is `D^(m + 1) f`, curried on the left
(`ContDiff.hasFDerivAt_iteratedFDeriv`).
-/

public section

open scoped NNReal Topology

namespace TauCeti

section CurryFin2

variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The currying linear isometry from continuous multilinear maps on `Fin 2` to
continuous bilinear maps in curried form. -/
noncomputable def continuousMultilinearCurryFin2 :
    (E [×2]→L[𝕜] F) ≃ₗᵢ[𝕜] E →L[𝕜] E →L[𝕜] F :=
  (continuousMultilinearCurryRightEquiv' 𝕜 1 E F).trans
    (continuousMultilinearCurryFin1 𝕜 E (E →L[𝕜] F))

/-- The currying isometry evaluates a multilinear map on its two arguments in order. -/
@[simp]
theorem continuousMultilinearCurryFin2_apply (f : E [×2]→L[𝕜] F) (x y : E) :
    continuousMultilinearCurryFin2 𝕜 E F f x y = f ![x, y] := by
  simp [continuousMultilinearCurryFin2]

/-- The inverse currying isometry evaluates its arguments in their original order. -/
@[simp]
theorem continuousMultilinearCurryFin2_symm_apply
    (g : E →L[𝕜] E →L[𝕜] F) (m : Fin 2 → E) :
    (continuousMultilinearCurryFin2 𝕜 E F).symm g m = g (m 0) (m 1) := by
  simp [continuousMultilinearCurryFin2, Fin.init]

variable {𝕜 E F} in
/-- Left currying the `1`-multilinear map of a continuous linear map `L` gives back `L`, with its
values read as `0`-multilinear maps. -/
theorem curryLeft_continuousMultilinearCurryFin1_symm (L : E →L[𝕜] F) :
    ((continuousMultilinearCurryFin1 𝕜 E F).symm L).curryLeft =
      (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.toContinuousLinearMap.comp L :=
  ContinuousLinearMap.ext fun v ↦ ContinuousMultilinearMap.ext fun w ↦ by simp

variable {𝕜 E F} in
/-- Left currying the `2`-multilinear map of a curried bilinear map `B` gives back `B`, with its
values read as `1`-multilinear maps. -/
theorem curryLeft_continuousMultilinearCurryFin2_symm (B : E →L[𝕜] E →L[𝕜] F) :
    ((continuousMultilinearCurryFin2 𝕜 E F).symm B).curryLeft =
      (continuousMultilinearCurryFin1 𝕜 E F).symm.toLinearIsometry.toContinuousLinearMap.comp B :=
  ContinuousLinearMap.ext fun v ↦ ContinuousMultilinearMap.ext fun w ↦ by simp

end CurryFin2

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The first iterated derivative, uncurried, is the Fréchet derivative. -/
@[simp]
theorem continuousMultilinearCurryFin1_iteratedFDeriv_one (f : E → F) (x : E) :
    continuousMultilinearCurryFin1 𝕜 E F (iteratedFDeriv 𝕜 1 f x) = fderiv 𝕜 f x := by
  ext v
  simp [iteratedFDeriv_one_apply]

/-- The Fréchet derivative is the first iterated derivative, curried, including at points where
these derivatives are junk-valued. -/
theorem fderiv_eq_continuousMultilinearCurryFin1_comp (f : E → F) :
    fderiv 𝕜 f = continuousMultilinearCurryFin1 𝕜 E F ∘ iteratedFDeriv 𝕜 1 f :=
  funext fun x ↦ (continuousMultilinearCurryFin1_iteratedFDeriv_one f x).symm

/-- The `(n + 1)`-st iterated derivative of `f` is the `n`-th iterated derivative of `Df` with its
last variable joined to the others: the function-level form of Mathlib's pointwise
`iteratedFDeriv_succ_eq_comp_right`, including at points where these derivatives are
junk-valued. -/
theorem iteratedFDeriv_succ_eq_comp_right' (f : E → F) {n : ℕ} :
    iteratedFDeriv 𝕜 (n + 1) f = (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
      iteratedFDeriv 𝕜 n (fderiv 𝕜 f) :=
  funext fun _ ↦ iteratedFDeriv_succ_eq_comp_right

/-- Currying the second iterated derivative gives the Fréchet derivative of the first
Fréchet derivative, including at points where these derivatives are junk-valued. -/
theorem continuousMultilinearCurryFin2_iteratedFDeriv_two (f : E → F) (x : E) :
    continuousMultilinearCurryFin2 𝕜 E F (iteratedFDeriv 𝕜 2 f x) =
      fderiv 𝕜 (fderiv 𝕜 f) x := by
  ext v w
  simp only [continuousMultilinearCurryFin2_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- Evaluating the third iterated derivative on three directions gives the three-times curried
Fréchet derivative, including at points where these derivatives are junk-valued. -/
theorem iteratedFDeriv_three_apply (f : E → F) (x : E) (m : Fin 3 → E) :
    iteratedFDeriv 𝕜 3 f x m = fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 f)) x (m 0) (m 1) (m 2) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

/-- Differences of curried second derivatives and multilinear second derivatives have
exactly the same norm, without differentiability assumptions. -/
theorem norm_fderiv_fderiv_sub (f : E → F) (x y : E) :
    ‖fderiv 𝕜 (fderiv 𝕜 f) x - fderiv 𝕜 (fderiv 𝕜 f) y‖ =
      ‖iteratedFDeriv 𝕜 2 f x - iteratedFDeriv 𝕜 2 f y‖ := by
  rw [← continuousMultilinearCurryFin2_iteratedFDeriv_two f x,
    ← continuousMultilinearCurryFin2_iteratedFDeriv_two f y, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map]

/-- The curried second Fréchet derivative is `r`-Hölder with constant `C` on a set exactly when
the second iterated derivative is, without differentiability assumptions: the two differ by the
currying isometry. -/
theorem holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two {C r : ℝ≥0} {s : Set E} (f : E → F) :
    HolderOnWith C r (fderiv 𝕜 (fderiv 𝕜 f)) s ↔ HolderOnWith C r (iteratedFDeriv 𝕜 2 f) s := by
  simp only [HolderOnWith, ← continuousMultilinearCurryFin2_iteratedFDeriv_two,
    LinearIsometryEquiv.edist_map]

/-- Differences of the second iterated derivative of the `k`-th iterated derivative of `f` have
the same norm as differences of the `(k + 2)`-th iterated derivative of `f`, without
differentiability assumptions: the two differ by a pair of currying isometries. -/
theorem norm_iteratedFDeriv_two_iteratedFDeriv_sub (f : E → F) (k : ℕ) (x y : E) :
    ‖iteratedFDeriv 𝕜 2 (iteratedFDeriv 𝕜 k f) x - iteratedFDeriv 𝕜 2 (iteratedFDeriv 𝕜 k f) y‖ =
      ‖iteratedFDeriv 𝕜 (k + 2) f x - iteratedFDeriv 𝕜 (k + 2) f y‖ := by
  -- The spaces are given explicitly: unifying them against the instances carried by the currying
  -- isometries otherwise fails.
  set e₁ : (E [×k + 1]→L[𝕜] F) ≃ₗᵢ[𝕜] E →L[𝕜] E [×k]→L[𝕜] F :=
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 1) => E) F
  set e₂ : (E [×k + 2]→L[𝕜] F) ≃ₗᵢ[𝕜] E →L[𝕜] E [×k + 1]→L[𝕜] F :=
    continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (k + 2) => E) F
  have h₁ : fderiv 𝕜 (iteratedFDeriv 𝕜 k f) = e₁ ∘ iteratedFDeriv 𝕜 (k + 1) f := by
    funext z
    simp [iteratedFDeriv_succ_eq_comp_left, e₁]
  have h₂ (z : E) :
      fderiv 𝕜 (iteratedFDeriv 𝕜 (k + 1) f) z = e₂ (iteratedFDeriv 𝕜 (k + 2) f z) := by
    simp [iteratedFDeriv_succ_eq_comp_left (n := k + 1), e₂]
  have h₃ (z : E) : fderiv 𝕜 (e₁ ∘ iteratedFDeriv 𝕜 (k + 1) f) z =
      e₁.toLinearIsometry.toContinuousLinearMap.comp (fderiv 𝕜 (iteratedFDeriv 𝕜 (k + 1) f) z) :=
    LinearIsometryEquiv.comp_fderiv (𝕜 := 𝕜) (E := E [×k + 1]→L[𝕜] F)
      (F := E →L[𝕜] E [×k]→L[𝕜] F) (G := E) (iso := e₁) (f := iteratedFDeriv 𝕜 (k + 1) f) (x := z)
  rw [← norm_fderiv_fderiv_sub, h₁, h₃, h₃, h₂, h₂, ← ContinuousLinearMap.comp_sub,
    ← LinearIsometryEquiv.map_sub]
  refine (ContinuousLinearMap.opNorm_ext _
    (e₂ (iteratedFDeriv 𝕜 (k + 2) f x - iteratedFDeriv 𝕜 (k + 2) f y)) fun v =>
      e₁.norm_map _).trans ?_
  exact e₂.norm_map _

/-- The second iterated derivative of the `k`-th iterated derivative of `f` is `r`-Hölder with
constant `C` on a set exactly when the `(k + 2)`-th iterated derivative of `f` is. -/
theorem holderOnWith_iteratedFDeriv_two_iteratedFDeriv_iff {C r : ℝ≥0} {s : Set E} (f : E → F)
    (k : ℕ) :
    HolderOnWith C r (iteratedFDeriv 𝕜 2 (iteratedFDeriv 𝕜 k f)) s ↔
      HolderOnWith C r (iteratedFDeriv 𝕜 (k + 2) f) s := by
  simp only [HolderOnWith, edist_dist, dist_eq_norm, norm_iteratedFDeriv_two_iteratedFDeriv_sub]

/-- The `i`-th iterated derivative of the `m`-th iterated derivative of `f` has the same norm as
the `(i + m)`-th iterated derivative of `f`. -/
theorem norm_iteratedFDeriv_iteratedFDeriv (f : E → F) (i m : ℕ) (x : E) :
    ‖iteratedFDeriv 𝕜 i (iteratedFDeriv 𝕜 m f) x‖ = ‖iteratedFDeriv 𝕜 (i + m) f x‖ := by
  induction m generalizing i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.add_zero]
  | succ m ih =>
    -- Peel off the first derivative: `D^(m+1) f = e ∘ D (D^m f)` for a currying isometry `e`.
    have h : iteratedFDeriv 𝕜 (m + 1) f =
        (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F).symm ∘
          fderiv 𝕜 (iteratedFDeriv 𝕜 m f) :=
      iteratedFDeriv_succ_eq_comp_left
    -- The spaces are given explicitly: unifying them against the instances carried by `e`
    -- otherwise fails.
    have he := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := 𝕜) (E := E)
      (F := E →L[𝕜] E [×m]→L[𝕜] F) (G := E [×m + 1]→L[𝕜] F)
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) => E) F).symm
      (fderiv 𝕜 (iteratedFDeriv 𝕜 m f)) x i
    rw [← h] at he
    rw [he, norm_iteratedFDeriv_fderiv, ih, Nat.add_right_comm, Nat.add_assoc]

/-- Adding a constant to a function does not change its iterated derivatives of positive order. No
differentiability is needed, since the derivative of `f + c` is that of `f` everywhere. -/
theorem iteratedFDeriv_succ_add_const (f : E → F) (c : F) (n : ℕ) :
    iteratedFDeriv 𝕜 (n + 1) (fun x ↦ f x + c) = iteratedFDeriv 𝕜 (n + 1) f := by
  funext x
  simp only [iteratedFDeriv_succ_eq_comp_right, fderiv_add_const]

/-- The iterated derivatives of a constant function `c` have norm at most `‖c‖`. -/
theorem norm_iteratedFDeriv_const_le (n : ℕ) (c : F) (x : E) :
    ‖iteratedFDeriv 𝕜 n (fun _ : E ↦ c) x‖ ≤ ‖c‖ := by
  rcases n with _ | n
  · simp
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

/-- The iterated derivatives of positive order of the identity have norm at most one. -/
theorem norm_iteratedFDeriv_id_le_one {n : ℕ} (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv 𝕜 n (id : E → E) x‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hD : fderiv 𝕜 (id : E → E) = fun _ ↦ ContinuousLinearMap.id 𝕜 E := funext fun _ ↦ fderiv_id
  rw [← norm_iteratedFDeriv_fderiv, hD]
  rcases n with _ | n
  · simpa using ContinuousLinearMap.norm_id_le
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]

/-- Right translation `Equiv.addRight a` has iterated derivatives of every positive order of norm
at most one. -/
theorem norm_iteratedFDeriv_addRight_le (a : E) {n : ℕ} (hn : 1 ≤ n) (x : E) :
    ‖iteratedFDeriv 𝕜 n (Equiv.addRight a) x‖ ≤ 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hfn : (Equiv.addRight a : E → E) = fun y ↦ (id : E → E) y + a := rfl
  rw [hfn, iteratedFDeriv_succ_add_const]
  exact norm_iteratedFDeriv_id_le_one (by omega) x

/-- The iterated derivatives of positive order of a continuous linear map are constant. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_succ_eq (L : E →L[𝕜] F) (n : ℕ) (x y : E) :
    iteratedFDeriv 𝕜 (n + 1) L x = iteratedFDeriv 𝕜 (n + 1) L y := by
  have hL : fderiv 𝕜 L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply, hL]
  rcases n with _ | n
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  · rw [iteratedFDeriv_succ_const, Pi.zero_apply, Pi.zero_apply]

/-- Where `f` is differentiable near `x`, the iterated derivatives of positive order of
`y ↦ L y + f y`, for a continuous linear map `L`, are those of `L` plus those of `f`. No higher
differentiability of `f` is needed, since `D (L + f) = L + D f` near `x` and `L` is constant. -/
theorem _root_.ContinuousLinearMap.iteratedFDeriv_succ_add_apply (L : E →L[𝕜] F) {f : E → F}
    {x : E} (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) (n : ℕ) :
    iteratedFDeriv 𝕜 (n + 1) (fun y ↦ L y + f y) x =
      iteratedFDeriv 𝕜 (n + 1) L x + iteratedFDeriv 𝕜 (n + 1) f x := by
  have hD : fderiv 𝕜 (fun y ↦ L y + f y) =ᶠ[𝓝 x] fun y ↦ fderiv 𝕜 f y + L :=
    hf.mono fun y hy ↦ by rw [fderiv_fun_add L.differentiableAt hy, L.fderiv, add_comm]
  have hL : fderiv 𝕜 L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    (hD.iteratedFDeriv 𝕜 n).eq_of_nhds, hL]
  rcases n with _ | n
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, map_add, add_comm]
  · rw [iteratedFDeriv_succ_add_const, iteratedFDeriv_succ_const, Pi.zero_apply,
      LinearIsometryEquiv.map_zero, zero_add]

/-- Adding a continuous linear map `L` to a function `f` that is differentiable near every point
of `s` does not change the Hölder constants on `s` of its derivatives of positive order. -/
theorem _root_.ContinuousLinearMap.holderOnWith_iteratedFDeriv_succ_add_left_iff {n : ℕ}
    (L : E →L[𝕜] F) {f : E → F} {C r : ℝ≥0} {s : Set E}
    (hf : ∀ x ∈ s, ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y) :
    HolderOnWith C r (iteratedFDeriv 𝕜 (n + 1) (fun y ↦ L y + f y)) s ↔
      HolderOnWith C r (iteratedFDeriv 𝕜 (n + 1) f) s := by
  unfold HolderOnWith
  refine forall₂_congr fun x hx ↦ forall₂_congr fun y hy ↦ ?_
  rw [L.iteratedFDeriv_succ_add_apply (hf x hx), L.iteratedFDeriv_succ_add_apply (hf y hy),
    L.iteratedFDeriv_succ_eq n y x, edist_add_left]

/-- Bounded derivatives up to order `N` have a common bound. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_forall_exists {f : E → F} {N : ℕ}
    (hbd : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) :
    ∃ G, ∀ n ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ G := by
  choose C hC using fun n ↦ (em (n ≤ N)).elim (fun hn ↦ (hbd n hn).imp fun _ h _ ↦ h)
    fun hn ↦ ⟨0, fun h ↦ absurd h hn⟩
  exact ⟨∑ n ∈ Finset.range (N + 1), max (C n) 0, fun n hn x ↦ (hC n hn x).trans
    ((le_max_left _ _).trans (Finset.single_le_sum (f := fun n ↦ max (C n) 0)
      (fun _ _ ↦ le_max_right _ _) (Finset.mem_range.2 (by omega))))⟩

/-- Bounded derivatives of orders `1` to `N + 1` have a common bound. These are the derivatives of
order at most `N` of `Df`. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_forall_one_le {f : E → F} {N : ℕ}
    (hbd : ∀ n, 1 ≤ n → n ≤ N + 1 → ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) :
    ∃ L, ∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ L := by
  obtain ⟨L, hL⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists (𝕜 := 𝕜)
    (f := fderiv 𝕜 f) (N := N) fun n hn ↦ by
      simpa only [norm_iteratedFDeriv_fderiv] using hbd (n + 1) (by omega) (by omega)
  refine ⟨L, fun n h₁ h₂ x ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h₁
  simpa only [norm_iteratedFDeriv_fderiv] using hL n (by omega) x

/-- A bound `G` on the derivatives of `f` of order at most `N` is nonnegative and bounds `f`. -/
theorem nonneg_and_norm_le_of_norm_iteratedFDeriv_le {f : E → F} {N : ℕ} {G : ℝ}
    (hfG : ∀ n ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ G) :
    0 ≤ G ∧ ∀ x, ‖f x‖ ≤ G :=
  have hf (x : E) : ‖f x‖ ≤ G := by simpa using hfG 0 (Nat.zero_le _) x
  ⟨(norm_nonneg _).trans (hf 0), hf⟩

/-- Where a function `ζ` equals one on a neighbourhood of `x`, every iterated derivative of `ζ * u`
at `x` is that of `u`. -/
theorem _root_.Filter.EventuallyEq.iteratedFDeriv_mul_eq {𝕜 F A : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedRing A] [NormedSpace 𝕜 A] {k : ℕ}
    {ζ u : F → A} {x : F} (hζ : ζ =ᶠ[𝓝 x] 1) :
    iteratedFDeriv 𝕜 k (ζ * u) x = iteratedFDeriv 𝕜 k u x := by
  have hev : ζ * u =ᶠ[𝓝 x] u := by
    filter_upwards [hζ] with y hy
    simp only [Pi.mul_apply, hy, Pi.one_apply, one_mul]
  exact (hev.iteratedFDeriv 𝕜 k).eq_of_nhds

/-- For a function of class `C^n` and `m < n`, the derivative of `D^m f` at `x` is
`D^(m + 1) f x`, curried on the left. -/
theorem _root_.ContDiff.hasFDerivAt_iteratedFDeriv {n : WithTop ℕ∞} {f : E → F} {m : ℕ}
    (hm : m < n) (hf : ContDiff 𝕜 n f) (x : E) :
    HasFDerivAt (iteratedFDeriv 𝕜 m f) (iteratedFDeriv 𝕜 (m + 1) f x).curryLeft x :=
  hf.ftaylorSeries.fderiv m hm x

/-- At a point of which `s` is a neighbourhood, every iterated derivative of `s.indicator g` is
that of `g`. -/
theorem iteratedFDeriv_indicator_of_mem_nhds {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {s : Set E} {g : E → F} {x : E} (hs : s ∈ 𝓝 x) (k : ℕ) :
    iteratedFDeriv 𝕜 k (s.indicator g) x = iteratedFDeriv 𝕜 k g x :=
  (Filter.EventuallyEq.iteratedFDeriv 𝕜 (Filter.eventually_of_mem hs
    fun _ hy ↦ Set.indicator_of_mem hy g) k).eq_of_nhds

end TauCeti
