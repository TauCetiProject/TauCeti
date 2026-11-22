/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Topology.MetricSpace.Holder

/-!
# Postcomposition with a continuous linear map on parabolic Hölder spaces of every order

For a continuous linear map `L : F →L[ℝ] G`, postcomposition `u ↦ L ∘ u` maps the bounded
parabolic Hölder space `C_{par,b}^{k+α}(E × [a, b], F)` (`TauCeti.ParabolicCkHolderSpace`) to the
same space with values in `G`, as a continuous linear map
`TauCeti.ParabolicCkHolderSpace.compLeftL L` of operator norm at most `3 (k + 1)² ‖L‖`. Its fields
are those of `u` followed by `L`:

`D_t^r D_x^m (L ∘ u) = L ∘ D_t^r D_x^m u`

(`TauCeti.ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`). It reads off components of
vector-valued maps, such as the directional derivatives `∂ₑu = (D_x u) e` of a spatial gradient,
and assembles vector-valued maps from scalar ones, such as `D_x u = ∑ᵢ ∂ᵢu • dxᵢ` on `ℝⁿ`. It is
the parabolic counterpart of `TauCeti.CkHolderSpace.compLeftL`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.compLeftL`: postcomposition with `L` as a continuous linear map.
* `TauCeti.ParabolicCkHolderSpace.compLeftL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`: its values and its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_compLeftL_le`: the operator-norm bound.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
-/

public section
noncomputable section

namespace TauCeti.ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {a b : ℝ} {hab : a < b}

/-- Postcomposition of `m`-multilinear maps with `L`, as a continuous linear map. -/
private abbrev compMultilinearL (L : F →L[ℝ] G) (m : ℕ) : (E [×m]→L[ℝ] F) →L[ℝ] E [×m]→L[ℝ] G :=
  ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin m ↦ E) F G L

/-- Separating the first variable commutes with postcomposition. -/
private theorem curryLeft_compMultilinearL (L : F →L[ℝ] G) {m : ℕ} (M : E [×(m + 1)]→L[ℝ] F) :
    (compMultilinearL L (m + 1) M).curryLeft = (compMultilinearL L m).comp M.curryLeft := by
  ext h v
  simp

/-- The norm of postcomposition of multilinear maps with `L` is at most `‖L‖`. -/
private theorem norm_compMultilinearL_le (L : F →L[ℝ] G) (m : ℕ) :
    ‖compMultilinearL (E := E) L m‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) fun M ↦
    L.norm_compContinuousMultilinearMap_le M

/-- The fields `L ∘ D_t^r D_x^m u` of the postcomposition. -/
private def compLeftFields (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] G) :=
  (compMultilinearL L m).compLeftContinuousBounded _ (mixedDerivL r m u)

private theorem compLeftFields_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) (p : slab (E := E) a b) :
    compLeftFields L u r m p = L.compContinuousMultilinearMap (mixedDerivL r m u p) :=
  (rfl)

private theorem coe_compLeftFields (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (r m : ℕ) : ⇑(compLeftFields L u r m) = compMultilinearL L m ∘ mixedDerivL r m u :=
  funext fun _ ↦ ContinuousLinearMap.compLeftContinuousBounded_apply _ _ _

/-- Postcomposition with a continuous linear map preserves a Hölder bound, multiplying the
constant by `‖L‖`. -/
private theorem holderWith_comp {X : Type*} [PseudoEMetricSpace X] (L' : F →L[ℝ] G) {C r : ℝ≥0}
    {f : X → F} (hf : HolderWith C r f) : HolderWith (‖L'‖₊ * C) r (L' ∘ f) :=
  holderOnWith_univ.mp (L'.lipschitzWith.comp_holderOnWith (hf.holderOnWith univ))

private theorem hasFDerivAt_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (h : 2 * r + m + 1 ≤ k) (t : Icc a b)
    (x : E) :
    HasFDerivAt (fun y ↦ compLeftFields L u r m (slabMk y t))
      (compLeftFields L u r (m + 1) (slabMk x t)).curryLeft x := by
  have hd := (compMultilinearL L m).hasFDerivAt.comp x (hasFDerivAt_mixedDerivL u h t x)
  rw [← curryLeft_compMultilinearL] at hd
  exact hd

private theorem hasDerivWithinAt_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) (r m : ℕ) (h : 2 * r + m + 2 ≤ k) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (compLeftFields L u r m) x)
      (compLeftFields L u (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hd := HasFDerivAt.comp_hasDerivWithinAt (x := (t : ℝ))
    (compMultilinearL L m).hasFDerivAt (hasDerivWithinAt_mixedDerivL u h x t)
  rw [← ParabolicC2HolderSpace.timeExtension_comp] at hd
  exact hd

private theorem holderWith_compLeftFields_slabMk (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m + 1 = k) (x : E) :
    HolderWith (‖compMultilinearL (E := E) L m‖₊ * ‖timeSliceL r m u‖₊) ((1 + α) / 2)
      fun t : Icc a b ↦ compLeftFields L u r m (slabMk x t) := by
  have hc := holderWith_comp (compMultilinearL L m) (holderWith_mixedDerivL_slabMk u h x)
  rw [coe_compLeftFields]
  exact hc

private theorem holderWith_compLeftFields (L : F →L[ℝ] G)
    (u : ParabolicCkHolderSpace k α E F hab) {r m : ℕ} (h : 2 * r + m = k) :
    HolderWith (‖compMultilinearL (E := E) L m‖₊ * ‖mixedDerivHolderL r m u‖₊) α
      (compLeftFields L u r m : slab (E := E) a b → E [×m]→L[ℝ] G) := by
  have hm := holderWith_mixedDerivL u h
  have hc := holderWith_comp (compMultilinearL L m) hm
  rw [coe_compLeftFields]
  exact hc

/-- Postcomposition with `L`; `compLeftL` is its bundled form. -/
private def compLeft (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ParabolicCkHolderSpace k α E G hab :=
  mk (compLeftFields L u) (hasFDerivAt_compLeftFields L u) (hasDerivWithinAt_compLeftFields L u)
    (fun _ _ h ↦ ⟨_, holderWith_compLeftFields_slabMk L u h⟩)
    (fun _ _ h ↦ (holderWith_compLeftFields L u h).memHolder)

private theorem mixedDerivL_compLeft (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (compLeft L u) = compLeftFields L u r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem compLeft_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a b) : compLeft L u p = L (u p) := by
  rw [compLeft, mk_apply, compLeftFields_apply, ← mixedDerivL_zero_zero_apply u p 0]
  rfl

/-- Postcomposition with `L` multiplies the norm by at most `3 (k + 1)² ‖L‖`. -/
private theorem norm_compLeft_le (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ‖compLeft L u‖ ≤ 3 * (k + 1) ^ 2 * ‖L‖ * ‖u‖ := by
  have hpair (i : ℕ × ℕ) (hi : i ∈ parabolicDerivPairs k) :
      ‖mixedDerivL i.1 i.2 (compLeft L u)‖ +
          (‖timeSliceL i.1 i.2 (compLeft L u)‖ +
            ‖mixedDerivHolderL i.1 i.2 (compLeft L u)‖) ≤ 3 * (‖L‖ * ‖u‖) := by
    replace hi := mem_parabolicDerivPairs.1 hi
    have hfield := mixedDerivL_compLeft L u hi
    have hL : ‖compMultilinearL (E := E) L i.2‖₊ ≤ ‖L‖₊ := by
      exact_mod_cast norm_compMultilinearL_le (E := E) L i.2
    have hs' : ‖timeSliceL i.1 i.2 u‖₊ ≤ ‖u‖₊ := by
      exact_mod_cast norm_timeSliceL_le u _ _
    have hh' : ‖mixedDerivHolderL i.1 i.2 u‖₊ ≤ ‖u‖₊ := by
      exact_mod_cast norm_mixedDerivHolderL_le u _ _
    have h := norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le (compLeft L u)
      (B := ‖L‖ * ‖u‖) (C := ‖L‖₊ * ‖u‖₊)
      (by
        rw [hfield]
        refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun p ↦ ?_
        rw [compLeftFields_apply]
        exact (L.norm_compContinuousMultilinearMap_le _).trans
          (mul_le_mul_of_nonneg_left (((mixedDerivL _ _ u).norm_coe_le_norm p).trans
            (norm_mixedDerivL_le u _ _)) (norm_nonneg L)))
      (fun hs x ↦ by
        simp only [hfield]
        exact (holderWith_compLeftFields_slabMk L u hs x).mono (mul_le_mul' hL hs'))
      (fun hh ↦ by
        rw [hfield]
        exact (holderWith_compLeftFields L u hh).mono (mul_le_mul' hL hh'))
    push_cast at h
    linarith
  have hc : ((parabolicDerivPairs k).card : ℝ) ≤ (k + 1) ^ 2 := by
    exact_mod_cast card_parabolicDerivPairs_le k
  rw [norm_eq]
  refine (Finset.sum_le_sum hpair).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 3 * (‖L‖ * ‖u‖))
  linarith

/-- **Postcomposition** `u ↦ L ∘ u` with a continuous linear map `L : F →L[ℝ] G`, as a continuous
linear map from `C_{par,b}^{k+α}(E × [a, b], F)` to `C_{par,b}^{k+α}(E × [a, b], G)`. Its fields
are those of `u` followed by `L` (`ParabolicCkHolderSpace.mixedDerivL_compLeftL_apply`). -/
def compLeftL (L : F →L[ℝ] G) :
    ParabolicCkHolderSpace k α E F hab →L[ℝ] ParabolicCkHolderSpace k α E G hab :=
  LinearMap.mkContinuous
    { toFun := compLeft L
      map_add' u v := ext fun p ↦ by simp [compLeft_apply]
      map_smul' c u := ext fun p ↦ by simp [compLeft_apply] }
    (3 * (k + 1) ^ 2 * ‖L‖) (norm_compLeft_le L)

/-- The values of the postcomposition are those of `u` followed by `L`. -/
@[simp]
theorem compLeftL_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    (p : slab (E := E) a b) : compLeftL L u p = L (u p) :=
  compLeft_apply L u p

theorem coe_compLeftL (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab) :
    ⇑(compLeftL L u) = L ∘ u :=
  funext (compLeftL_apply L u)

/-- The fields of the postcomposition are those of `u` followed by `L`:
`D_t^r D_x^m (L ∘ u) = L ∘ D_t^r D_x^m u`. -/
@[simp]
theorem mixedDerivL_compLeftL_apply (L : F →L[ℝ] G) (u : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) (p : slab (E := E) a b) :
    mixedDerivL r m (compLeftL L u) p = L.compContinuousMultilinearMap (mixedDerivL r m u p) := by
  rw [← compLeftFields_apply]
  exact DFunLike.congr_fun (mixedDerivL_compLeft L u h) p

/-- The operator norm of postcomposition with `L` is at most `3 (k + 1)² ‖L‖`. -/
theorem norm_compLeftL_le (L : F →L[ℝ] G) :
    ‖compLeftL (k := k) (α := α) (E := E) (hab := hab) L‖ ≤ 3 * (k + 1) ^ 2 * ‖L‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]
theorem compLeftL_id (u : ParabolicCkHolderSpace k α E F hab) : compLeftL (.id ℝ F) u = u :=
  ext fun _ ↦ by simp

@[simp]
theorem compLeftL_compLeftL {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (L : F →L[ℝ] G) (L' : G →L[ℝ] G') (u : ParabolicCkHolderSpace k α E F hab) :
    compLeftL L' (compLeftL L u) = compLeftL (L'.comp L) u :=
  ext fun _ ↦ by simp

end TauCeti.ParabolicCkHolderSpace
