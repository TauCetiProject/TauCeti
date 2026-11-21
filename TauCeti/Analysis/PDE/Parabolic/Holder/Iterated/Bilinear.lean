/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Holder.Leibniz
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Inclusion
import TauCeti.Topology.MetricSpace.Holder

/-!
# Continuous bilinear operations on parabolic Hölder spaces of every order

A continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` acts pointwise on the bounded parabolic Hölder
spaces `C_{par,b}^{k+α}` on a slab `E × [a, b]` of every order `k`: for `α ≤ 1`,
`u ∈ C_{par,b}^{k+α}(F)` and `v ∈ C_{par,b}^{k+α}(G)`, the map `(x, t) ↦ B (u (x, t)) (v (x, t))`
belongs to `C_{par,b}^{k+α}(H)`, and the resulting bilinear map is continuous with operator norm at
most `25 · 2^k · N · ‖B‖`, where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`. The bound
depends neither on the spaces nor on the slab. With `B` the multiplication of `ℝ`, the scalar
multiplication, or the application of matrix-valued coefficients to Hessians, this is the product
estimate of the space: the coefficients of a parabolic operator of order `k` multiply the
derivatives of a solution within it.

The mixed derivatives of `w = B u v` are given by the Leibniz rule in time and in space: for
`2 r + m ≤ k`, the field `D_t^r D_x^m w` at `(x, t)` is the `m`-th spatial derivative at `x` of

`y ↦ ∑_{j ≤ r} (r choose j) B (D_t^j u (y, t)) (D_t^(r-j) v (y, t))`

(`ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`).

## Implementation notes

The fields of `B u v` are built term by term from the maps
`y ↦ B (D_t^i u (y, t)) (D_t^j v (y, t))`, which are `C^m` in space on each time slice, and are
checked against the conditions of `ParabolicCkHolderSpace.mk`.

* In space, each field is an iterated Fréchet derivative, so its spatial derivative is the next one.
* In time, the time derivative passes through the spatial derivatives of a product
  (`ContinuousLinearMap.hasDerivWithinAt_iteratedFDeriv_of_bilinear`), and Pascal's rule
  reassembles the result into the field of time order `r + 1`.
* The Hölder conditions of the top two orders follow in time from the Leibniz bound for
  differences (`ContinuousLinearMap.norm_iteratedFDeriv_sub_le_of_bilinear`), and in space from the
  Hölder bound for derivatives of products
  (`ContinuousLinearMap.holderWith_iteratedFDeriv_of_tsupport_subset_right`). They need every field
  of `u` and `v` to be `α`-Hölder in space and `α / 2`-Hölder in time, and every field below the
  top order to be `(1 + α) / 2`-Hölder in time. Below the top order these follow from the bounded
  next derivative, which is where `α ≤ 1` is used.

## Main declarations

* `ContinuousLinearMap.compParabolicCkHolder₂`: pointwise application of `B` as a continuous
  bilinear map of parabolic Hölder spaces of order `k`.
* `ContinuousLinearMap.compParabolicCkHolder₂_apply`: its value.
* `ContinuousLinearMap.mixedDerivL_compParabolicCkHolder₂`: the Leibniz rule for its fields.
* `ContinuousLinearMap.norm_compParabolicCkHolder₂_le`: the operator-norm bound.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

open Set TauCeti ParabolicSpaceTime
open scoped NNReal ENNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {a b : ℝ} {hab : a < b}

namespace TauCeti.ParabolicCkHolderSpace

/-! ### The spatial slices of the time derivatives -/

/-- The spatial slice `y ↦ D_t^r u (y, t)` at the time `t`. -/
private def timeDerivSlice (f : ParabolicCkHolderSpace k α E F hab) (r : ℕ) (t : Icc a b) :
    E → F :=
  fun y ↦ (mixedDerivL r 0 f (slabMk y t)).curry0

private theorem contDiff_timeDerivSlice (f : ParabolicCkHolderSpace k α E F hab) {r l : ℕ}
    (h : 2 * r + l ≤ k) (t : Icc a b) : ContDiff ℝ l (timeDerivSlice f r t) :=
  (f.hasFTaylorSeriesUpTo_mixedDerivL r t).contDiff.of_le (by exact_mod_cast (by omega))

private theorem iteratedFDeriv_timeDerivSlice (f : ParabolicCkHolderSpace k α E F hab)
    {r l : ℕ} (h : 2 * r + l ≤ k) (t : Icc a b) (y : E) :
    iteratedFDeriv ℝ l (timeDerivSlice f r t) y = mixedDerivL r l f (slabMk y t) :=
  f.iteratedFDeriv_mixedDerivL_zero h y t

end TauCeti.ParabolicCkHolderSpace

namespace ContinuousLinearMap

open ParabolicCkHolderSpace

variable (B : F →L[ℝ] G →L[ℝ] H) (u : ParabolicCkHolderSpace k α E F hab)
  (v : ParabolicCkHolderSpace k α E G hab)

/-! ### The products of the time derivatives and their spatial derivatives -/

/-- The field `(x, t) ↦ D_x^m (y ↦ B (D_t^i u (y, t)) (D_t^j v (y, t))) x`. -/
private def prodField (i j m : ℕ) (p : slab (E := E) a b) : E [×m]→L[ℝ] H :=
  iteratedFDeriv ℝ m (fun y ↦ B (timeDerivSlice u i (slabTime p) y)
    (timeDerivSlice v j (slabTime p) y)) (p : ParabolicSpaceTime E).space

private theorem prodField_slabMk (i j m : ℕ) (x : E) (t : Icc a b) :
    prodField B u v i j m (slabMk x t) = iteratedFDeriv ℝ m
      (fun y ↦ B (timeDerivSlice u i t y) (timeDerivSlice v j t y)) x := by
  simp only [prodField, slabTime_slabMk, space_slabMk]

variable {u v}

private theorem contDiff_prodSlice {i j n : ℕ} (hi : 2 * i + n ≤ k) (hj : 2 * j + n ≤ k)
    (t : Icc a b) :
    ContDiff ℝ n fun y ↦ B (timeDerivSlice u i t y) (timeDerivSlice v j t y) :=
  B.isBoundedBilinearMap.contDiff.comp
    ((contDiff_timeDerivSlice u hi t).prodMk (contDiff_timeDerivSlice v hj t))

private theorem norm_prodField_le {i j m : ℕ} (h : 2 * (i + j) + m ≤ k)
    (p : slab (E := E) a b) : ‖prodField B u v i j m p‖ ≤ ‖B‖ * 2 ^ m * ‖u‖ * ‖v‖ := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  rw [prodField_slabMk]
  exact B.norm_iteratedFDeriv_le_of_bilinear_of_forall_le isOpen_univ (mem_univ x)
    (contDiff_timeDerivSlice u (r := i) (l := m) (by omega) t).contDiffOn
    (contDiff_timeDerivSlice v (r := j) (l := m) (by omega) t).contDiffOn
    (fun l hl ↦ by
      rw [iteratedFDeriv_timeDerivSlice u (r := i) (l := l) (by omega)]
      exact norm_mixedDerivL_apply_le u _ _ _)
    (fun l hl ↦ by
      rw [iteratedFDeriv_timeDerivSlice v (r := j) (l := l) (by omega)]
      exact norm_mixedDerivL_apply_le v _ _ _)

/-- The Leibniz bound for the difference of the field at two times: it is controlled by the
differences of the fields of `u` and `v` of spatial order at most `m` at those times. -/
private theorem norm_prodField_sub_le {i j m : ℕ} (h : 2 * (i + j) + m ≤ k) (x : E)
    (t s : Icc a b) {δ₁ δ₂ : ℝ}
    (hu : ∀ l ≤ m, ‖mixedDerivL i l u (slabMk x t) - mixedDerivL i l u (slabMk x s)‖ ≤ δ₁)
    (hv : ∀ l ≤ m, ‖mixedDerivL j l v (slabMk x t) - mixedDerivL j l v (slabMk x s)‖ ≤ δ₂) :
    ‖prodField B u v i j m (slabMk x t) - prodField B u v i j m (slabMk x s)‖ ≤
      ‖B‖ * 2 ^ m * (δ₁ * ‖v‖ + ‖u‖ * δ₂) := by
  rw [prodField_slabMk, prodField_slabMk]
  have hu' (l : ℕ) (hl : l ≤ m) := iteratedFDeriv_timeDerivSlice u (r := i) (l := l) (by omega)
  have hv' (l : ℕ) (hl : l ≤ m) := iteratedFDeriv_timeDerivSlice v (r := j) (l := l) (by omega)
  exact B.norm_iteratedFDeriv_sub_le_of_bilinear
    (contDiff_timeDerivSlice u (r := i) (l := m) (by omega) t)
    (contDiff_timeDerivSlice u (r := i) (l := m) (by omega) s)
    (contDiff_timeDerivSlice v (r := j) (l := m) (by omega) t)
    (contDiff_timeDerivSlice v (r := j) (l := m) (by omega) s)
    (fun l hl ↦ by rw [hu' l hl, hu' l hl]; exact hu l hl)
    (fun l hl ↦ by rw [hv' l hl]; exact norm_mixedDerivL_apply_le v _ _ _)
    (fun l hl ↦ by rw [hu' l hl]; exact norm_mixedDerivL_apply_le u _ _ _)
    (fun l hl ↦ by rw [hv' l hl, hv' l hl]; exact hv l hl)

/-- If the time slices of the fields of `u` and `v` that enter are `γ`-Hölder with constants
`c ‖u‖` and `c ‖v‖`, then so are those of the field, with constant `2 c 2^m ‖B‖ ‖u‖ ‖v‖`. -/
private theorem dist_prodField_le_of_holderWith {i j m : ℕ} (h : 2 * (i + j) + m ≤ k) {c γ : ℝ≥0}
    (x : E)
    (hu : ∀ l ≤ m, HolderWith (c * ‖u‖₊) γ fun t : Icc a b ↦ mixedDerivL i l u (slabMk x t))
    (hv : ∀ l ≤ m, HolderWith (c * ‖v‖₊) γ fun t : Icc a b ↦ mixedDerivL j l v (slabMk x t))
    (t s : Icc a b) :
    ‖prodField B u v i j m (slabMk x t) - prodField B u v i j m (slabMk x s)‖ ≤
      2 * c * 2 ^ m * ‖B‖ * ‖u‖ * ‖v‖ * dist t s ^ (γ : ℝ) := by
  refine (norm_prodField_sub_le B h x t s (δ₁ := c * ‖u‖ * dist t s ^ (γ : ℝ))
    (δ₂ := c * ‖v‖ * dist t s ^ (γ : ℝ)) (fun l hl ↦ ?_) fun l hl ↦ ?_).trans (le_of_eq (by ring))
  · simpa [← dist_eq_norm] using (hu l hl).dist_le t s
  · simpa [← dist_eq_norm] using (hv l hl).dist_le t s

/-- The field is `α`-Hölder in space, with constant `6 · 2^m ‖B‖ ‖u‖ ‖v‖`. -/
private theorem holderWith_prodField_space (hα : α ≤ 1) {i j m : ℕ} (h : 2 * (i + j) + m ≤ k)
    (t : Icc a b) :
    HolderWith (6 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊) α fun x ↦ prodField B u v i j m (slabMk x t) := by
  have hDu (l : ℕ) (hl : l ≤ m) : iteratedFDeriv ℝ l (timeDerivSlice u i t) =
      fun y ↦ mixedDerivL i l u (slabMk y t) :=
    funext (iteratedFDeriv_timeDerivSlice u (r := i) (l := l) (by omega) t)
  have hDv (l : ℕ) (hl : l ≤ m) : iteratedFDeriv ℝ l (timeDerivSlice v j t) =
      fun y ↦ mixedDerivL j l v (slabMk y t) :=
    funext (iteratedFDeriv_timeDerivSlice v (r := j) (l := l) (by omega) t)
  have hH := B.holderWith_iteratedFDeriv_of_tsupport_subset_right (k := m) (s := univ)
    (contDiff_timeDerivSlice u (r := i) (l := m) (by omega) t).contDiffOn
    (contDiff_timeDerivSlice v (r := j) (l := m) (by omega) t)
    isOpen_univ (subset_univ _) (M := ‖u‖₊) (N := ‖v‖₊) (H := 3 * ‖u‖₊) (K := 3 * ‖v‖₊)
    (fun l hl y _ ↦ by rw [hDu l hl]; exact norm_mixedDerivL_apply_le u _ _ _)
    (fun l hl y ↦ by rw [hDv l hl]; exact norm_mixedDerivL_apply_le v _ _ _)
    (fun l hl ↦ by
      rw [hDu l hl]
      exact (holderWith_mixedDerivL_space u (r := i) (m := l) (by omega) hα t).holderOnWith univ)
    (fun l hl ↦ by
      rw [hDv l hl]
      exact holderWith_mixedDerivL_space v (r := j) (m := l) (by omega) hα t)
  simp only [prodField_slabMk]
  exact hH.mono (le_of_eq (by ring))

/-- **Spatial derivatives of the field.** -/
private theorem hasFDerivAt_prodField {i j m : ℕ} (h : 2 * (i + j) + m + 1 ≤ k) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ prodField B u v i j m (slabMk y t))
      (prodField B u v i j (m + 1) (slabMk x t)).curryLeft x := by
  have hc := contDiff_prodSlice B (u := u) (v := v) (n := m + 1) (i := i) (j := j) (by omega)
    (by omega) t
  simp only [prodField_slabMk]
  -- The derivative of `D_x^m` is `D_x^(m+1)`, curried on the left (`fderiv_iteratedFDeriv`).
  exact ((hc.differentiable_iteratedFDeriv (by exact_mod_cast lt_add_one m)) x).hasFDerivAt
    |>.congr_fderiv (by
      ext y v
      rw [fderiv_iteratedFDeriv, Function.comp_apply, continuousMultilinearCurryLeftEquiv_apply,
        ContinuousMultilinearMap.curryLeft_apply])

/-- **Time derivatives of the field**, by the product rule. -/
private theorem hasDerivWithinAt_prodField {i j m : ℕ} (h : 2 * (i + j) + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (prodField B u v i j m) x)
      (prodField B u v (i + 1) j m (slabMk x t) + prodField B u v i (j + 1) m (slabMk x t))
      (Icc a b) t := by
  have key := B.hasDerivWithinAt_iteratedFDeriv_of_bilinear (s := Icc a b) (t := (t : ℝ)) (x := x)
    (f := fun τ ↦ timeDerivSlice u i (projIcc a b hab.le τ))
    (g := fun τ ↦ timeDerivSlice v j (projIcc a b hab.le τ))
    (f' := timeDerivSlice u (i + 1) t) (g' := timeDerivSlice v (j + 1) t) (n := m)
    (fun τ ↦ contDiff_timeDerivSlice u (r := i) (l := m) (by omega) _)
    (fun τ ↦ contDiff_timeDerivSlice v (r := j) (l := m) (by omega) _)
    (contDiff_timeDerivSlice u (r := i + 1) (l := m) (by omega) t)
    (contDiff_timeDerivSlice v (r := j + 1) (l := m) (by omega) t)
    (fun l hl ↦ by
      simpa only [iteratedFDeriv_timeDerivSlice u (show 2 * i + l ≤ k by omega),
        iteratedFDeriv_timeDerivSlice u (show 2 * (i + 1) + l ≤ k by omega),
        ParabolicC2HolderSpace.timeExtension_def] using
        u.hasDerivWithinAt_mixedDerivL (r := i) (m := l) (by omega) x t)
    (fun l hl ↦ by
      simpa only [iteratedFDeriv_timeDerivSlice v (show 2 * j + l ≤ k by omega),
        iteratedFDeriv_timeDerivSlice v (show 2 * (j + 1) + l ≤ k by omega),
        ParabolicC2HolderSpace.timeExtension_def] using
        v.hasDerivWithinAt_mixedDerivL (r := j) (m := l) (by omega) x t)
  simpa only [ParabolicC2HolderSpace.timeExtension_def, prodField_slabMk, projIcc_val] using key

/-- The Leibniz bound for the difference of the field at two times, with the differences of the
fields of `u` and `v` summed over the spatial orders `l ≤ m`. -/
private theorem norm_prodField_sub_le_sum {i j m : ℕ} (h : 2 * (i + j) + m ≤ k) (x : E)
    (t s : Icc a b) :
    ‖prodField B u v i j m (slabMk x t) - prodField B u v i j m (slabMk x s)‖ ≤
      ‖B‖ * 2 ^ m *
        ((∑ l ∈ Finset.range (m + 1),
            ‖mixedDerivL i l u (slabMk x t) - mixedDerivL i l u (slabMk x s)‖) * ‖v‖ +
          ‖u‖ * ∑ l ∈ Finset.range (m + 1),
            ‖mixedDerivL j l v (slabMk x t) - mixedDerivL j l v (slabMk x s)‖) := by
  have hterm (w : ℕ → ℝ) (hw : ∀ l, 0 ≤ w l) {l : ℕ} (hl : l ≤ m) :
      w l ≤ ∑ l' ∈ Finset.range (m + 1), w l' :=
    Finset.single_le_sum (fun l' _ ↦ hw l') (Finset.mem_range.2 (Nat.lt_succ_of_le hl))
  exact norm_prodField_sub_le B h x t s
    (fun l hl ↦ hterm (fun l ↦ ‖mixedDerivL i l u (slabMk x t) -
      mixedDerivL i l u (slabMk x s)‖) (fun _ ↦ norm_nonneg _) hl)
    (fun l hl ↦ hterm (fun l ↦ ‖mixedDerivL j l v (slabMk x t) -
      mixedDerivL j l v (slabMk x s)‖) (fun _ ↦ norm_nonneg _) hl)

/-- The field is continuous: in space on each time slice it is a derivative of a `C^m` map, and
its change in time at a fixed point is controlled by that of the continuous fields of `u`
and `v`. -/
private theorem continuous_prodField {i j m : ℕ} (h : 2 * (i + j) + m ≤ k) :
    Continuous (prodField B u v i j m) := by
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  obtain ⟨x₀, t₀, rfl⟩ : ∃ x t, slabMk x t = p₀ := ⟨_, _, slabMk_space_slabTime p₀⟩
  -- Compare `p = (x, t)` with `q p = (x, t₀)` in time, then `q p` with `(x₀, t₀)` in space.
  set q : slab (E := E) a b → slab (E := E) a b :=
    fun p ↦ slabMk (p : ParabolicSpaceTime E).space t₀
  have hq : Continuous q := continuous_slabMk.comp
    ((continuous_space.comp continuous_subtypeVal).prodMk continuous_const)
  have hq₀ : q (slabMk x₀ t₀) = slabMk x₀ t₀ := by simp [q]
  have hbound (p : slab (E := E) a b) :
      ‖prodField B u v i j m p - prodField B u v i j m (slabMk x₀ t₀)‖ ≤
        ‖B‖ * 2 ^ m *
          ((∑ l ∈ Finset.range (m + 1), ‖mixedDerivL i l u p - mixedDerivL i l u (q p)‖) * ‖v‖ +
            ‖u‖ * ∑ l ∈ Finset.range (m + 1), ‖mixedDerivL j l v p - mixedDerivL j l v (q p)‖) +
          ‖prodField B u v i j m (q p) - prodField B u v i j m (slabMk x₀ t₀)‖ := by
    obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
    refine (norm_sub_le_norm_sub_add_norm_sub _ (prodField B u v i j m (q (slabMk x t))) _).trans
      (add_le_add ?_ le_rfl)
    simpa only [q, space_slabMk] using norm_prodField_sub_le_sum B h x t t₀
  -- The differences of the fields tend to zero, and so does the spatial change.
  have hδ {w : ℕ → slab (E := E) a b → ℝ} (hw : ∀ l, Continuous (w l))
      (hw₀ : ∀ l, w l (slabMk x₀ t₀) = 0) :
      Filter.Tendsto (fun p ↦ ∑ l ∈ Finset.range (m + 1), w l p)
        (nhds (slabMk x₀ t₀)) (nhds 0) := by
    simpa [hw₀] using tendsto_finsetSum (Finset.range (m + 1)) fun l _ ↦
      (hw l).tendsto (slabMk x₀ t₀)
  have hδu := hδ (w := fun l p ↦ ‖mixedDerivL i l u p - mixedDerivL i l u (q p)‖)
    (fun l ↦ ((mixedDerivL i l u).continuous.sub ((mixedDerivL i l u).continuous.comp hq)).norm)
    (fun l ↦ by simp [hq₀])
  have hδv := hδ (w := fun l p ↦ ‖mixedDerivL j l v p - mixedDerivL j l v (q p)‖)
    (fun l ↦ ((mixedDerivL j l v).continuous.sub ((mixedDerivL j l v).continuous.comp hq)).norm)
    (fun l ↦ by simp [hq₀])
  have hspace : Continuous fun p ↦ prodField B u v i j m (q p) := by
    simp only [q, prodField_slabMk]
    exact ((contDiff_prodSlice B (n := m) (by omega) (by omega) t₀).continuous_iteratedFDeriv'
      ).comp (continuous_space.comp continuous_subtypeVal)
  have hlim := ((((hδu.mul_const ‖v‖).add (hδv.const_mul ‖u‖)).const_mul (‖B‖ * 2 ^ m)).add
    (((hspace.tendsto (slabMk x₀ t₀)).sub_const
      (prodField B u v i j m (slabMk x₀ t₀))).norm))
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun p ↦ norm_nonneg _) hbound ?_
  simpa [hq₀] using hlim

/-! ### The fields of the product -/

variable (u v) in
/-- The Leibniz field `∑_{j ≤ r} (r choose j) D_x^m (y ↦ B (D_t^j u (y, t)) (D_t^(r-j) v (y, t)))`,
the field `D_t^r D_x^m` of the product. -/
private def leibnizField (r m : ℕ) (p : slab (E := E) a b) : E [×m]→L[ℝ] H :=
  ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) • prodField B u v j (r - j) m p

private theorem leibnizField_sub (r m : ℕ) (p q : slab (E := E) a b) :
    leibnizField B u v r m p - leibnizField B u v r m q = ∑ j ∈ Finset.range (r + 1),
      (r.choose j : ℝ) • (prodField B u v j (r - j) m p - prodField B u v j (r - j) m q) := by
  simp only [leibnizField, ← Finset.sum_sub_distrib, smul_sub]

private theorem norm_leibnizField_le {r m : ℕ} (h : 2 * r + m ≤ k) (p : slab (E := E) a b) :
    ‖leibnizField B u v r m p‖ ≤ 2 ^ r * (‖B‖ * 2 ^ m * ‖u‖ * ‖v‖) :=
  norm_sum_choose_smul_le fun j hj ↦ norm_prodField_le B (u := u) (v := v) (i := j) (j := r - j)
    (m := m) (by have := Finset.mem_range.1 hj; omega) p

private theorem continuous_leibnizField {r m : ℕ} (h : 2 * r + m ≤ k) :
    Continuous (leibnizField B u v r m) :=
  continuous_finsetSum _ fun j hj ↦ (continuous_prodField B (u := u) (v := v) (i := j)
    (j := r - j) (m := m) (by have := Finset.mem_range.1 hj; omega)).fun_const_smul _

/-- If the fields of `u` and `v` have `γ`-Hölder time slices with constants `c ‖u‖` and `c ‖v‖`,
then the time slices of the Leibniz field are `γ`-Hölder. -/
private theorem holderWith_leibnizField_time {r m : ℕ} (h : 2 * r + m ≤ k) {c γ : ℝ≥0} (x : E)
    (hu : ∀ i l, 2 * i + l ≤ 2 * r + m →
      HolderWith (c * ‖u‖₊) γ fun t : Icc a b ↦ mixedDerivL i l u (slabMk x t))
    (hv : ∀ j l, 2 * j + l ≤ 2 * r + m →
      HolderWith (c * ‖v‖₊) γ fun t : Icc a b ↦ mixedDerivL j l v (slabMk x t)) :
    HolderWith (2 ^ r * (2 * c * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊)) γ
      fun t : Icc a b ↦ leibnizField B u v r m (slabMk x t) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun t _ s _ ↦ ?_)
  rw [dist_eq_norm, leibnizField_sub]
  refine (norm_sum_choose_smul_le (c := 2 * c * 2 ^ m * ‖B‖ * ‖u‖ * ‖v‖ * dist t s ^ (γ : ℝ))
    fun j hj ↦ ?_).trans_eq (by push_cast; ring)
  have hj := Finset.mem_range.1 hj
  exact dist_prodField_le_of_holderWith B (u := u) (v := v) (i := j) (j := r - j) (m := m)
    (by omega) x
    (fun l hl ↦ hu j l (by omega)) (fun l hl ↦ hv (r - j) l (by omega)) t s

/-- The Leibniz field is `α`-Hölder in space. -/
private theorem holderWith_leibnizField_space (hα : α ≤ 1) {r m : ℕ} (h : 2 * r + m ≤ k)
    (t : Icc a b) :
    HolderWith (2 ^ r * (6 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊)) α
      fun x ↦ leibnizField B u v r m (slabMk x t) := by
  refine holderOnWith_univ.1 (HolderOnWith.of_dist_le fun x _ y _ ↦ ?_)
  rw [dist_eq_norm, leibnizField_sub]
  refine (norm_sum_choose_smul_le (c := 6 * 2 ^ m * ‖B‖ * ‖u‖ * ‖v‖ * dist x y ^ (α : ℝ))
    fun j hj ↦ ?_).trans_eq (by push_cast; ring)
  rw [← dist_eq_norm]
  have hH := holderWith_prodField_space B hα (u := u) (v := v) (i := j) (j := r - j) (m := m)
    (by have := Finset.mem_range.1 hj; omega) t
  simpa using hH.dist_le x y

/-- **Spatial derivatives of the Leibniz field.** -/
private theorem hasFDerivAt_leibnizField {r m : ℕ} (h : 2 * r + m + 1 ≤ k) (t : Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ leibnizField B u v r m (slabMk y t))
      (leibnizField B u v r (m + 1) (slabMk x t)).curryLeft x := by
  have hsum := HasFDerivAt.fun_sum (u := Finset.range (r + 1)) fun j hj ↦
    (hasFDerivAt_prodField B (u := u) (v := v) (i := j) (j := r - j) (m := m)
      (by have := Finset.mem_range.1 hj; omega) t x).const_smul (r.choose j : ℝ)
  refine hsum.congr_fderiv ?_
  ext w z
  simp [leibnizField]

/-- **Time derivatives of the Leibniz field**: the product rule and Pascal's rule. -/
private theorem hasDerivWithinAt_leibnizField {r m : ℕ} (h : 2 * r + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (leibnizField B u v r m) x)
      (leibnizField B u v (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.range (r + 1)) fun j hj ↦
    (hasDerivWithinAt_prodField B (hab := hab) (u := u) (v := v) (i := j) (j := r - j) (m := m)
      (by have := Finset.mem_range.1 hj; omega) x t).const_smul (r.choose j : ℝ)
  have e : ParabolicC2HolderSpace.timeExtension hab.le (leibnizField B u v r m) x =
      fun τ ↦ ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) •
        ParabolicC2HolderSpace.timeExtension hab.le (prodField B u v j (r - j) m) x τ := by
    funext τ
    simp only [ParabolicC2HolderSpace.timeExtension_def, leibnizField]
  rw [e]
  refine hsum.congr_deriv ?_
  -- Pascal's rule `(r + 1 choose j) = (r choose j) + (r choose (j - 1))`.
  have hpascal := Finset.sum_choose_succ_nsmul
    (fun i j ↦ prodField B u v i j m (slabMk x t)) r
  simp only [leibnizField, Nat.cast_smul_eq_nsmul ℝ, smul_add, Finset.sum_add_distrib]
  rw [hpascal, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [show r - j + 1 = r + 1 - j by have := Finset.mem_range.1 hj; omega]

/-- The time slices of a Leibniz field one order below the top are `(1 + α) / 2`-Hölder. -/
private theorem holderWith_leibnizField_slice (hα : α ≤ 1) {r m : ℕ} (h : 2 * r + m + 1 = k)
    (x : E) :
    HolderWith (2 ^ r * (2 * 3 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊)) ((1 + α) / 2)
      fun t : Icc a b ↦ leibnizField B u v r m (slabMk x t) :=
  holderWith_leibnizField_time B (by omega) x
    (fun i l hil ↦ holderWith_mixedDerivL_slabMk_of_add_one_le u (r := i) (m := l) (by omega) hα x)
    (fun j l hjl ↦ holderWith_mixedDerivL_slabMk_of_add_one_le v (r := j) (m := l) (by omega) hα x)

/-- A Leibniz field of the top order is parabolically `α`-Hölder. -/
private theorem holderWith_leibnizField (hα : α ≤ 1) {r m : ℕ} (h : 2 * r + m = k) :
    HolderWith (2 ^ r * (6 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊) +
      2 ^ r * (2 * 5 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊)) α (leibnizField B u v r m) :=
  holderWith_of_holderWith_slices (holderWith_leibnizField_space B hα h.le) fun x ↦
    holderWith_leibnizField_time B h.le x
      (fun i l hil ↦ holderWith_div_two_mixedDerivL_slabMk u (r := i) (m := l) (by omega) hα x)
      (fun j l hjl ↦ holderWith_div_two_mixedDerivL_slabMk v (r := j) (m := l) (by omega) hα x)

variable (u v) in
/-- The fields of the product as bounded continuous fields: the Leibniz fields up to the order `k`,
and zero above it. -/
private def productField (r m : ℕ) : slab (E := E) a b →ᵇ (E [×m]→L[ℝ] H) :=
  if h : 2 * r + m ≤ k then
    BoundedContinuousFunction.ofNormedAddCommGroup (leibnizField B u v r m)
      (continuous_leibnizField B h) _ (norm_leibnizField_le B h)
  else 0

private theorem coe_productField {r m : ℕ} (h : 2 * r + m ≤ k) :
    ⇑(productField B u v r m) = leibnizField B u v r m := by
  rw [productField, dite_eq_left h, BoundedContinuousFunction.coe_ofNormedAddCommGroup]

private theorem two_pow_mul_two_pow_le {r m : ℕ} (h : 2 * r + m ≤ k) :
    (2 : ℝ) ^ r * 2 ^ m ≤ 2 ^ k := by
  rw [← pow_add]
  exact pow_le_pow_right₀ one_le_two (by omega)

private theorem norm_productField_le {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖productField B u v r m‖ ≤ 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by
  have hK : 0 ≤ ‖B‖ * ‖u‖ * ‖v‖ := by positivity
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
  rw [coe_productField B h]
  refine (norm_leibnizField_le B h p).trans ?_
  calc (2 : ℝ) ^ r * (‖B‖ * 2 ^ m * ‖u‖ * ‖v‖) = 2 ^ r * 2 ^ m * (‖B‖ * ‖u‖ * ‖v‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (two_pow_mul_two_pow_le h) hK

variable (hα : α ≤ 1)

variable (u v) in
/-- The pointwise product `B u v` as a parabolic Hölder map of order `k`. -/
private def compParabolicCkHolderAux : ParabolicCkHolderSpace k α E H hab :=
  ParabolicCkHolderSpace.mk (productField B u v)
    (fun r m h t x ↦ by
      rw [coe_productField B (by omega), coe_productField B (by omega)]
      exact hasFDerivAt_leibnizField B h t x)
    (fun r m h x t ↦ by
      rw [coe_productField B (by omega), coe_productField B (by omega)]
      exact hasDerivWithinAt_leibnizField B h x t)
    (fun r m h ↦ ⟨_, fun x ↦ by
      rw [coe_productField B (by omega)]
      exact holderWith_leibnizField_slice B hα h x⟩)
    (fun r m h ↦ by
      rw [coe_productField B h.le]
      exact (holderWith_leibnizField B hα h).memHolder)

private theorem compParabolicCkHolderAux_apply (p : slab (E := E) a b) :
    compParabolicCkHolderAux B u v hα p = B (u p) (v p) := by
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  rw [compParabolicCkHolderAux, mk_apply, coe_productField B (by omega)]
  simp [leibnizField, prodField_slabMk, timeDerivSlice, ContinuousMultilinearMap.curry0_apply]

private theorem mixedDerivL_compParabolicCkHolderAux_eq {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (compParabolicCkHolderAux B u v hα) = productField B u v r m := by
  rw [compParabolicCkHolderAux, mixedDerivL_mk _ _ _ _ h]

private theorem mixedDerivL_compParabolicCkHolderAux {r m : ℕ} (h : 2 * r + m ≤ k) :
    ⇑(mixedDerivL r m (compParabolicCkHolderAux B u v hα)) = leibnizField B u v r m := by
  rw [mixedDerivL_compParabolicCkHolderAux_eq B hα h, coe_productField B h]

private theorem norm_mixedDerivL_compParabolicCkHolderAux_le {r m : ℕ} (h : 2 * r + m ≤ k) :
    ‖mixedDerivL r m (compParabolicCkHolderAux B u v hα)‖ ≤ 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by
  rw [mixedDerivL_compParabolicCkHolderAux_eq B hα h]
  exact norm_productField_le B h

/-- At the two top orders, the family of time slices and the Hölder field of the product have norm
at most `23 · 2^k ‖B‖ ‖u‖ ‖v‖`. -/
private theorem norm_timeSliceL_add_norm_mixedDerivHolderL_compAux_le (r m : ℕ) :
    ‖timeSliceL r m (compParabolicCkHolderAux B u v hα)‖ +
      ‖mixedDerivHolderL r m (compParabolicCkHolderAux B u v hα)‖ ≤
        23 * 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by
  set w := compParabolicCkHolderAux B u v hα
  have hK : 0 ≤ ‖B‖ * ‖u‖ * ‖v‖ := by positivity
  have hK' : 0 ≤ (2 : ℝ) ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by positivity
  by_cases hs : 2 * r + m + 1 = k
  · -- One order below the top, only the time slices enter.
    rw [mixedDerivHolderL_of_ne (by omega), zero_apply, norm_zero, add_zero]
    refine (norm_timeSliceL_le_of_holderWith w hs
      (C := 2 ^ r * (2 * 3 * 2 ^ m * ‖B‖₊ * ‖u‖₊ * ‖v‖₊)) fun x ↦ ?_).trans ?_
    · rw [mixedDerivL_compParabolicCkHolderAux B hα (by omega)]
      exact holderWith_leibnizField_slice B hα hs x
    · have h₁ : ‖mixedDerivL r m w‖ ≤ 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖) :=
        norm_mixedDerivL_compParabolicCkHolderAux_le B hα (by omega)
      have h₂ := mul_le_mul_of_nonneg_right (two_pow_mul_two_pow_le (k := k) (r := r) (m := m)
        (by omega)) hK
      push_cast
      linarith
  · rw [timeSliceL_of_ne hs, zero_apply, norm_zero, zero_add]
    by_cases hh : 2 * r + m = k
    · -- At the top, only the Hölder field enters.
      have hcoe : ⇑(mixedDerivHolderL r m w) = leibnizField B u v r m := by
        rw [← HolderSpace.coe_toBoundedContinuousFunction,
          toBoundedContinuousFunction_mixedDerivHolderL _ hh,
          mixedDerivL_compParabolicCkHolderAux B hα hh.le]
      refine (HolderSpace.norm_le_of_norm_le_of_holderWith
        (M := 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖)) (by positivity)
        (fun p ↦ ?_) (hcoe ▸ holderWith_leibnizField B hα hh)).trans ?_
      · rw [hcoe, ← mixedDerivL_compParabolicCkHolderAux B hα hh.le]
        exact ((mixedDerivL r m w).norm_coe_le_norm p).trans
          (norm_mixedDerivL_compParabolicCkHolderAux_le B hα hh.le)
      · have h₂ := mul_le_mul_of_nonneg_right (two_pow_mul_two_pow_le hh.le) hK
        push_cast
        linarith
    · rw [mixedDerivHolderL_of_ne hh, zero_apply, norm_zero]
      positivity

private theorem norm_compParabolicCkHolderAux_le :
    ‖compParabolicCkHolderAux B u v hα‖ ≤
      (parabolicDerivPairs k).card * 25 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [norm_eq]
  calc _ ≤ ∑ _p ∈ parabolicDerivPairs k, 25 * 2 ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have h1 := norm_timeSliceL_add_norm_mixedDerivHolderL_compAux_le B hα (u := u) (v := v)
          p.1 p.2
        have h2 := norm_mixedDerivL_compParabolicCkHolderAux_le B hα (u := u) (v := v)
          (mem_parabolicDerivPairs.1 hp)
        have h3 : 0 ≤ (2 : ℝ) ^ k * (‖B‖ * ‖u‖ * ‖v‖) := by positivity
        linarith
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### The bundled bilinear map -/

/-- For `α ≤ 1`, pointwise application `(u, v) ↦ B u v` of a continuous bilinear map, as a
continuous bilinear map of the bounded parabolic Hölder spaces of order `k` on a slab. -/
def compParabolicCkHolder₂ :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E G hab →L[ℝ]
      ParabolicCkHolderSpace k α E H hab :=
  (LinearMap.mk₂ ℝ (fun u v ↦ compParabolicCkHolderAux B u v hα)
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by
      simp [compParabolicCkHolderAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by
      simp [compParabolicCkHolderAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by
      simp [compParabolicCkHolderAux_apply])
    (fun _ _ _ ↦ ParabolicCkHolderSpace.ext fun _ ↦ by
      simp [compParabolicCkHolderAux_apply])).mkContinuous₂
    ((parabolicDerivPairs k).card * 25 * 2 ^ k * ‖B‖)
    (fun u v ↦ norm_compParabolicCkHolderAux_le B hα)

/- This is `LinearMap.mkContinuous₂_apply` followed by `LinearMap.mk₂_apply`, both proved by `rfl`
in Mathlib; as for `ContinuousLinearMap.compParabolicC2Holder₂`, they do not rewrite here because
the definition of `ParabolicCkHolderSpace` as a submodule is not exposed, so the equation is closed
by `rfl` directly. -/
private theorem compParabolicCkHolder₂_eq :
    B.compParabolicCkHolder₂ hα u v = compParabolicCkHolderAux B u v hα := (rfl)

@[simp]
theorem compParabolicCkHolder₂_apply (p : slab (E := E) a b) :
    B.compParabolicCkHolder₂ hα u v p = B (u p) (v p) := by
  rw [compParabolicCkHolder₂_eq, compParabolicCkHolderAux_apply]

/-- **The Leibniz rule.** For `2 r + m ≤ k`, the field `D_t^r D_x^m` of `B u v` at `(x, t)` is
`∑_{j ≤ r} (r choose j) D_x^m (y ↦ B (D_t^j u (y, t)) (D_t^(r-j) v (y, t))) x`, where the time
derivatives are taken within `[a, b]`. -/
theorem mixedDerivL_compParabolicCkHolder₂ {r m : ℕ} (h : 2 * r + m ≤ k) (x : E) (t : Icc a b) :
    mixedDerivL r m (B.compParabolicCkHolder₂ hα u v) (slabMk x t) =
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) • iteratedFDeriv ℝ m
        (fun y ↦ B (iteratedDerivWithin j (ParabolicC2HolderSpace.timeExtension hab.le u y)
            (Icc a b) t)
          (iteratedDerivWithin (r - j) (ParabolicC2HolderSpace.timeExtension hab.le v y)
            (Icc a b) t)) x := by
  rw [compParabolicCkHolder₂_eq, mixedDerivL_compParabolicCkHolderAux B hα h, leibnizField]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj := Finset.mem_range.1 hj
  rw [prodField_slabMk]
  congr 2
  funext y
  rw [timeDerivSlice, timeDerivSlice, curry0_mixedDerivL_slabMk u (by omega),
    curry0_mixedDerivL_slabMk v (by omega)]

/-- **The product estimate.** Pointwise application of `B` to parabolic Hölder maps of order `k`
has operator norm at most `25 · 2^k · N · ‖B‖`, where `N` is the number of pairs `(r, m)` with
`2 r + m ≤ k`, uniformly over the spaces and the slab. -/
theorem norm_compParabolicCkHolder₂_le :
    ‖B.compParabolicCkHolder₂ (k := k) (E := E) (hab := hab) hα‖ ≤
      (parabolicDerivPairs k).card * 25 * 2 ^ k * ‖B‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- The norm of `B u v` is at most `25 · 2^k · N · ‖B‖ ‖u‖ ‖v‖`. -/
theorem norm_compParabolicCkHolder₂_apply_le :
    ‖B.compParabolicCkHolder₂ hα u v‖ ≤
      (parabolicDerivPairs k).card * 25 * 2 ^ k * ‖B‖ * ‖u‖ * ‖v‖ := by
  rw [compParabolicCkHolder₂_eq]
  exact norm_compParabolicCkHolderAux_le B hα

end ContinuousLinearMap
