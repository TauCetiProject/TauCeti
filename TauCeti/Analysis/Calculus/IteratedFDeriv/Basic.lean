/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Iterated derivatives of iterated derivatives

The `i`-th iterated derivative of the `m`-th iterated derivative of a function has the same norm
as its `(i + m)`-th iterated derivative. This extends Mathlib's `norm_iteratedFDeriv_fderiv`, the
case `m = 1`, and lets bounds on all iterated derivatives of a function transfer to its iterated
derivative fields. The first iterated derivative, uncurried, is the Fréchet derivative
(`TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one`, with the function-level form
`TauCeti.fderiv_eq_continuousMultilinearCurryFin1_comp`). The file also supplies the
two-variable currying isometry used to identify continuous multilinear second derivatives with
curried bilinear maps, and the corresponding exact comparison for differences of second
derivatives, which transfers Hölder bounds between the two forms of the second derivative.
Where a function `ζ` equals one on a neighbourhood of a point, every iterated derivative of
`ζ * u` there is that of `u` (`Filter.EventuallyEq.iteratedFDeriv_mul_eq`). Bounded derivatives up
to a finite order have a common bound
(`TauCeti.exists_forall_norm_iteratedFDeriv_le_of_forall_exists`), and such a
common bound is nonnegative and bounds the function itself
(`TauCeti.nonneg_and_norm_le_of_norm_iteratedFDeriv_le`).
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

/-- Currying the second iterated derivative gives the Fréchet derivative of the first
Fréchet derivative, including at points where these derivatives are junk-valued. -/
theorem continuousMultilinearCurryFin2_iteratedFDeriv_two (f : E → F) (x : E) :
    continuousMultilinearCurryFin2 𝕜 E F (iteratedFDeriv 𝕜 2 f x) =
      fderiv 𝕜 (fderiv 𝕜 f) x := by
  ext v w
  simp only [continuousMultilinearCurryFin2_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

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

/-- Bounded derivatives up to order `N` have a common bound. -/
theorem exists_forall_norm_iteratedFDeriv_le_of_forall_exists {f : E → F} {N : ℕ}
    (hbd : ∀ n ≤ N, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) :
    ∃ G, ∀ n ≤ N, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ G := by
  choose C hC using fun n ↦ (em (n ≤ N)).elim (fun hn ↦ (hbd n hn).imp fun _ h _ ↦ h)
    fun hn ↦ ⟨0, fun h ↦ absurd h hn⟩
  exact ⟨∑ n ∈ Finset.range (N + 1), max (C n) 0, fun n hn x ↦ (hC n hn x).trans
    ((le_max_left _ _).trans (Finset.single_le_sum (f := fun n ↦ max (C n) 0)
      (fun _ _ ↦ le_max_right _ _) (Finset.mem_range.2 (by omega))))⟩

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

end TauCeti
