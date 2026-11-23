/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.Calculus.FDeriv.MixedPartial
import TauCeti.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Parabolic Hölder maps from their first derivatives

A bounded continuous map `u` on the slab `E × [a, b]` whose spatial derivative `D_x u` lies in the
parabolic Hölder space `C_{par,b}^{(k+1)+α}` and whose time derivative `∂ₜu` within `[a, b]` lies
in `C_{par,b}^{k+α}` lies in `C_{par,b}^{(k+2)+α}`
(`TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`), with

`‖u‖_{(k+2)+α} ≤ 4 (k + 3)² (‖u‖_∞ + ‖D_x u‖_{(k+1)+α} + ‖∂ₜu‖_{k+α})`

(`TauCeti.ParabolicCkHolderSpace.norm_ofSpatialFDerivTimeDeriv_le`). In the parabolic scaling a
spatial derivative lowers the order by one and a time derivative by two, so this is the converse of
differentiation. It is the step that raises the order in the higher regularity theory of parabolic
equations: for a solution of `∂ₜu = aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u + f`, regularity of `D_x u` one
order up makes the right-hand side, hence `∂ₜu`, regular two orders below the target, and the
construction here then places `u` itself at the target order.

## The argument

The fields `D_t^r D_x^m u` of the new map are read off its derivatives: `D_x^(m+1) u` from the
field `D_x^m` of `G = D_x u` with its last variable uncurried, and `D_t^(r+1) D_x^m u` from the
field `D_t^r D_x^m` of `H = ∂ₜu`. The spatial derivative identities required by
`TauCeti.ParabolicCkHolderSpace.mk` hold within each of the two families, and so do the time
derivative identities for the fields without spatial derivatives. The remaining time derivative
identities cross between the families: the time derivative of `D_x^(m+1) u`, read off `G`, must be
the field `D_x^(m+1) ∂ₜu` read off `H`. This is the theorem of Schwarz and Peano on mixed
space-time derivatives, with one-sided time derivatives at the ends of `[a, b]`, applied on the
lower set of parabolic orders `2 r + m ≤ k + 2`
(`TauCeti.hasDerivWithinAt_mixedDeriv_of_isLowerSet`); its continuity hypothesis holds because the
fields with a time derivative are those of `H`. The Hölder conditions at the top two orders are
those of `G` and `H`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`: the element of
  `C_{par,b}^{(k+2)+α}` with value `u`, spatial derivative `G` and time derivative `H`.
* `TauCeti.ParabolicCkHolderSpace.mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_succ_ofSpatialFDerivTimeDeriv`: its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_ofSpatialFDerivTimeDeriv_le`: its norm estimate.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime ParabolicC2HolderSpace
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

namespace ParabolicCkHolderSpace

variable {k : ℕ} {α : ℝ≥0} {hab : a < b}

/-! ### Currying the last variable -/

variable (E F) in
/-- Joining the last of `m + 1` variables (uncurrying on the right), as a continuous linear map: an
`m`-multilinear map with values in `E →L[ℝ] F` read as an `(m + 1)`-multilinear map. -/
private abbrev uncurryRightL (m : ℕ) : (E [×m]→L[ℝ] (E →L[ℝ] F)) →L[ℝ] E [×(m + 1)]→L[ℝ] F :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.toLinearIsometry.toContinuousLinearMap

private theorem uncurryRightL_apply {m : ℕ} (M : E [×m]→L[ℝ] (E →L[ℝ] F)) :
    uncurryRightL E F m M = (continuousMultilinearCurryRightEquiv' ℝ m E F).symm M :=
  (rfl)

/-- Separating the first variable commutes with `uncurryRightL`. -/
private theorem curryLeft_uncurryRightL_succ {m : ℕ} (M : E [×(m + 1)]→L[ℝ] (E →L[ℝ] F)) :
    (uncurryRightL E F (m + 1) M).curryLeft = (uncurryRightL E F m).comp M.curryLeft :=
  ContinuousLinearMap.ext M.curryLeft_continuousMultilinearCurryRightEquiv'_symm

/-! ### The fields -/

/-- The fields of the map with value `u`, spatial derivative `G` and time derivative `H`: the
spatial derivatives `D_x^(m+1) u` are read off `G`, and the fields with a time derivative off
`H`. -/
private def ofDerivFields (u : slab (E := E) a b →ᵇ F)
    (G : ParabolicCkHolderSpace (k + 1) α E (E →L[ℝ] F) hab)
    (H : ParabolicCkHolderSpace k α E F hab) :
    ℕ → ∀ m : ℕ, slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F)
  | 0, 0 => (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.compLeftContinuousBounded _ u
  | 0, m + 1 => (uncurryRightL E F m).compLeftContinuousBounded _ (mixedDerivL 0 m G)
  | r + 1, m => mixedDerivL r m H

variable {u : slab (E := E) a b →ᵇ F} {G : ParabolicCkHolderSpace (k + 1) α E (E →L[ℝ] F) hab}
  {H : ParabolicCkHolderSpace k α E F hab}

private theorem ofDerivFields_zero_zero_apply (p : slab (E := E) a b) :
    ofDerivFields u G H 0 0 p = (continuousMultilinearCurryFin0 ℝ E F).symm (u p) :=
  (rfl)

private theorem ofDerivFields_zero_succ_apply (m : ℕ) (p : slab (E := E) a b) :
    ofDerivFields u G H 0 (m + 1) p = uncurryRightL E F m (mixedDerivL 0 m G p) :=
  (rfl)

private theorem ofDerivFields_succ (r m : ℕ) :
    ofDerivFields u G H (r + 1) m = mixedDerivL r m H :=
  (rfl)

section Construction

variable (hG : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x)
  (hH : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
    (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t)
include hG hH

omit hH in
private theorem hasFDerivAt_ofDerivFields (r m : ℕ) (h : 2 * r + m + 1 ≤ k + 2) (t : Icc a b)
    (x : E) : HasFDerivAt (fun y ↦ ofDerivFields u G H r m (slabMk y t))
      (ofDerivFields u G H r (m + 1) (slabMk x t)).curryLeft x := by
  rcases r with _ | r
  · rcases m with _ | m
    · have hL (L : E →L[ℝ] F) : (uncurryRightL E F 0
          ((continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).symm L)).curryLeft =
          (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap.comp
            L :=
        ContinuousLinearMap.ext fun v ↦ ContinuousMultilinearMap.ext fun w ↦ by simp
      rw [ofDerivFields_zero_succ_apply, mixedDerivL_zero_zero_eq, hL]
      exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
        |>.hasFDerivAt.comp x (hG t x)
    · rw [ofDerivFields_zero_succ_apply, curryLeft_uncurryRightL_succ]
      exact (uncurryRightL E F m).hasFDerivAt.comp x
        (hasFDerivAt_mixedDerivL G (r := 0) (m := m) (by omega) t x)
  · exact hasFDerivAt_mixedDerivL H (r := r) (m := m) (by omega) t x

omit hG in
/-- The time derivatives of the fields without spatial derivatives: of `u` itself it is `H`, and
the others are fields of `H`. -/
private theorem hasDerivWithinAt_ofDerivFields_zero (r : ℕ) (h : 2 * r + 2 ≤ k + 2) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (ofDerivFields u G H r 0) x)
      (ofDerivFields u G H (r + 1) 0 (slabMk x t)) (Icc a b) t := by
  rcases r with _ | r
  · rw [show ⇑(ofDerivFields u G H 0 0) = (continuousMultilinearCurryFin0 ℝ E F).symm ∘ u from
        funext ofDerivFields_zero_zero_apply, ParabolicC2HolderSpace.timeExtension_comp,
      ofDerivFields_succ, mixedDerivL_zero_zero_eq]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hH x t)
  · exact hasDerivWithinAt_mixedDerivL H (r := r) (m := 0) (by omega) x t

/-- **The mixed derivatives commute.** The time derivatives of the fields read off `G` are the
fields read off `H`: by the theorem of Schwarz and Peano on the lower set of parabolic orders
`2 r + m ≤ k + 2` (`TauCeti.hasDerivWithinAt_mixedDeriv_of_isLowerSet`), it suffices that the
fields are related by spatial derivatives, that the fields without spatial derivatives are related
by time derivatives, and that the fields with a time derivative are continuous. -/
private theorem hasDerivWithinAt_ofDerivFields (r m : ℕ) (h : 2 * r + m + 2 ≤ k + 2) (x : E)
    (t : Icc a b) :
    HasDerivWithinAt (ParabolicC2HolderSpace.timeExtension hab.le (ofDerivFields u G H r m) x)
      (ofDerivFields u G H (r + 1) m (slabMk x t)) (Icc a b) t := by
  have hmem {r n : ℕ} : (r, n) ∈ (parabolicDerivPairs (k + 2) : Set (ℕ × ℕ)) ↔
      2 * r + n ≤ k + 2 := by
    simp
  have hI : IsLowerSet (parabolicDerivPairs (k + 2) : Set (ℕ × ℕ)) := fun p q hqp hp ↦ by
    rw [Finset.mem_coe, mem_parabolicDerivPairs] at hp ⊢
    have := Prod.le_def.1 hqp
    omega
  have hd := hasDerivWithinAt_mixedDeriv_of_isLowerSet
    (Q := fun r y τ n ↦ ParabolicC2HolderSpace.timeExtension hab.le (ofDerivFields u G H r n) y τ)
    hI (convex_Icc a b) (fun r n hrn τ hτ y ↦ ?_) (fun r hr y τ hτ ↦ ?_) (fun r n _ ↦ ?_)
    (r := r) (n := m) (hmem.2 (by omega)) x t.property
  · rwa [ParabolicC2HolderSpace.timeExtension_of_mem] at hd
  · simp only [ParabolicC2HolderSpace.timeExtension_of_mem hab.le _ _ ⟨τ, hτ⟩]
    exact hasFDerivAt_ofDerivFields hG r n (by have := hmem.1 hrn; omega) ⟨τ, hτ⟩ y
  · have hd₀ := hasDerivWithinAt_ofDerivFields_zero (G := G) hH r
      (by have := hmem.1 hr; omega) y ⟨τ, hτ⟩
    rwa [← ParabolicC2HolderSpace.timeExtension_of_mem hab.le (ofDerivFields u G H (r + 1) 0) y
      ⟨τ, hτ⟩] at hd₀
  · exact ((ParabolicC2HolderSpace.continuous_timeExtension hab.le
      (ofDerivFields u G H (r + 1) (n + 1)).continuous).comp continuous_swap).continuousOn

omit hG hH in
/-- The time Hölder bound of the spatial derivatives `D_x^(m+1) u` read off `G`. -/
private theorem holderWith_ofDerivFields_zero_succ_slabMk (m : ℕ) (h : m + 2 = k + 2) (x : E) :
    HolderWith ‖timeSliceL 0 m G‖₊ ((1 + α) / 2)
      fun t : Icc a b ↦ ofDerivFields u G H 0 (m + 1) (slabMk x t) :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
    (holderWith_mixedDerivL_slabMk G (r := 0) (m := m) (by omega) x)

omit hG hH in
/-- The spatial Hölder bound of the spatial derivatives `D_x^(m+1) u` read off `G`. -/
private theorem holderWith_ofDerivFields_zero_succ (m : ℕ) (h : m + 1 = k + 2) :
    HolderWith ‖mixedDerivHolderL 0 m G‖₊ α
      (ofDerivFields u G H 0 (m + 1) : slab (E := E) a b → E [×(m + 1)]→L[ℝ] F) :=
  (continuousMultilinearCurryRightEquiv' ℝ m E F).symm.isometry.comp_holderWith
    (holderWith_mixedDerivL G (r := 0) (m := m) (by omega))

omit hG hH in
private theorem holderWith_ofDerivFields_slabMk (r m : ℕ) (h : 2 * r + m + 1 = k + 2) :
    ∃ C, ∀ x : E, HolderWith C ((1 + α) / 2)
      fun t : Icc a b ↦ ofDerivFields u G H r m (slabMk x t) := by
  rcases r with _ | r
  · rcases m with _ | m
    · omega
    · exact ⟨_, holderWith_ofDerivFields_zero_succ_slabMk m (by omega)⟩
  · rw [ofDerivFields_succ]
    exact ⟨_, holderWith_mixedDerivL_slabMk H (r := r) (m := m) (by omega)⟩

omit hG hH in
private theorem memHolder_ofDerivFields (r m : ℕ) (h : 2 * r + m = k + 2) :
    MemHolder α (ofDerivFields u G H r m : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  rcases r with _ | r
  · rcases m with _ | m
    · omega
    · exact ⟨_, holderWith_ofDerivFields_zero_succ m (by omega)⟩
  · rw [ofDerivFields_succ]
    exact memHolder_mixedDerivL H (r := r) (m := m) (by omega)

omit hG hH in
variable (u G H) in
/-- **A parabolic Hölder map from its first derivatives.** A bounded continuous map `u` on the
slab `E × [a, b]` whose spatial derivative `G = D_x u` lies in `C_{par,b}^{(k+1)+α}` and whose time
derivative `H = ∂ₜu` within `[a, b]` lies in `C_{par,b}^{k+α}` lies in `C_{par,b}^{(k+2)+α}`.
Spatial differentiation lowers the parabolic order by one and time differentiation by two, so this
is the converse of differentiating. Its fields are read off `G` and `H`
(`ParabolicCkHolderSpace.mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv`,
`ParabolicCkHolderSpace.mixedDerivL_succ_ofSpatialFDerivTimeDeriv`). -/
def ofSpatialFDerivTimeDeriv
    (hG : ∀ (t : Icc a b) (x : E), HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x)
    (hH : ∀ (x : E) (t : Icc a b), HasDerivWithinAt
      (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t) :
    ParabolicCkHolderSpace (k + 2) α E F hab :=
  mk (ofDerivFields u G H) (hasFDerivAt_ofDerivFields hG)
    (hasDerivWithinAt_ofDerivFields hG hH) holderWith_ofDerivFields_slabMk memHolder_ofDerivFields

/-- The map built from its first derivatives is the map. -/
@[simp]
theorem ofSpatialFDerivTimeDeriv_apply (p : slab (E := E) a b) :
    ofSpatialFDerivTimeDeriv u G H hG hH p = u p := by
  rw [ofSpatialFDerivTimeDeriv, mk_apply, ofDerivFields_zero_zero_apply]
  exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply (u p)

/-- The fields of the map built from its first derivatives are `ofDerivFields`. -/
private theorem mixedDerivL_ofSpatialFDerivTimeDeriv {r m : ℕ} (h : 2 * r + m ≤ k + 2) :
    mixedDerivL r m (ofSpatialFDerivTimeDeriv u G H hG hH) = ofDerivFields u G H r m := by
  rw [ofSpatialFDerivTimeDeriv, mixedDerivL_mk _ _ _ _ h]

/-- The spatial derivatives `D_x^(m+1) u` of the map built from its first derivatives are the
fields `D_x^m G` of its spatial derivative `G`, with the last variable uncurried. -/
@[simp]
theorem mixedDerivL_zero_succ_ofSpatialFDerivTimeDeriv {m : ℕ} (hm : m ≤ k + 1)
    (p : slab (E := E) a b) :
    mixedDerivL 0 (m + 1) (ofSpatialFDerivTimeDeriv u G H hG hH) p =
      (continuousMultilinearCurryRightEquiv' ℝ m E F).symm (mixedDerivL 0 m G p) := by
  rw [mixedDerivL_ofSpatialFDerivTimeDeriv hG hH (by omega), ofDerivFields_zero_succ_apply,
    uncurryRightL_apply]

/-- The fields `D_t^(r+1) D_x^m u` of the map built from its first derivatives are the fields
`D_t^r D_x^m H` of its time derivative `H`. -/
@[simp]
theorem mixedDerivL_succ_ofSpatialFDerivTimeDeriv {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL (r + 1) m (ofSpatialFDerivTimeDeriv u G H hG hH) = mixedDerivL r m H := by
  rw [mixedDerivL_ofSpatialFDerivTimeDeriv hG hH (by omega), ofDerivFields_succ]

/-- The contribution of each pair `(r, m)` to the norm of the map built from its first
derivatives is at most `4 (‖u‖ + ‖G‖ + ‖H‖)`. -/
private theorem norm_add_norm_add_norm_ofSpatialFDerivTimeDeriv_le :
    ∀ p ∈ parabolicDerivPairs (k + 2),
      ‖mixedDerivL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖ +
        (‖timeSliceL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖ +
          ‖mixedDerivHolderL p.1 p.2 (ofSpatialFDerivTimeDeriv u G H hG hH)‖) ≤
        4 * (‖u‖ + ‖G‖ + ‖H‖) := by
  set f := ofSpatialFDerivTimeDeriv u G H hG hH
  rintro ⟨r, m⟩ hp
  have hp' := mem_parabolicDerivPairs.1 hp
  have hfield : mixedDerivL r m f = ofDerivFields u G H r m :=
    mixedDerivL_ofSpatialFDerivTimeDeriv hG hH hp'
  rcases r with _ | r
  · rcases m with _ | m
    · refine (norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le f (B := ‖u‖) (C := 0) ?_
        (fun h ↦ by omega) (fun h ↦ by omega)).trans
        (by rw [NNReal.coe_zero]; linarith [norm_nonneg u, norm_nonneg G, norm_nonneg H])
      rw [hfield]
      refine (BoundedContinuousFunction.norm_le (norm_nonneg u)).2 fun p ↦ ?_
      rw [ofDerivFields_zero_zero_apply, LinearIsometryEquiv.norm_map]
      exact u.norm_coe_le_norm p
    · have hC : ((‖timeSliceL 0 m G‖₊ + ‖mixedDerivHolderL 0 m G‖₊ : ℝ≥0) : ℝ) ≤ 2 * ‖G‖ := by
        push_cast
        linarith [norm_timeSliceL_le G 0 m, norm_mixedDerivHolderL_le G 0 m]
      refine (norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le f (B := ‖G‖)
        (C := ‖timeSliceL 0 m G‖₊ + ‖mixedDerivHolderL 0 m G‖₊) ?_ (fun h x ↦ ?_)
        (fun h ↦ ?_)).trans (by linarith [norm_nonneg u, norm_nonneg H])
      · rw [hfield]
        refine (BoundedContinuousFunction.norm_le (norm_nonneg G)).2 fun p ↦ ?_
        rw [ofDerivFields_zero_succ_apply, uncurryRightL_apply, LinearIsometryEquiv.norm_map]
        exact ((mixedDerivL 0 m G).norm_coe_le_norm p).trans (norm_mixedDerivL_le G 0 m)
      · rw [hfield]
        exact (holderWith_ofDerivFields_zero_succ_slabMk m (by omega) x).mono le_self_add
      · rw [hfield]
        exact (holderWith_ofDerivFields_zero_succ m (by omega)).mono le_add_self
  · have hC : ((‖timeSliceL r m H‖₊ + ‖mixedDerivHolderL r m H‖₊ : ℝ≥0) : ℝ) ≤ 2 * ‖H‖ := by
      push_cast
      linarith [norm_timeSliceL_le H r m, norm_mixedDerivHolderL_le H r m]
    refine (norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le f (B := ‖H‖)
      (C := ‖timeSliceL r m H‖₊ + ‖mixedDerivHolderL r m H‖₊) ?_ (fun h x ↦ ?_)
      (fun h ↦ ?_)).trans (by linarith [norm_nonneg u, norm_nonneg G])
    · rw [hfield, ofDerivFields_succ]
      exact norm_mixedDerivL_le H r m
    · rw [hfield, ofDerivFields_succ]
      exact (holderWith_mixedDerivL_slabMk H (by omega) x).mono le_self_add
    · rw [hfield, ofDerivFields_succ]
      exact (holderWith_mixedDerivL H (by omega)).mono le_add_self

/-- **The norm estimate.** The order-`(k + 2)` norm of the map built from its first derivatives is
controlled by the supremum of the map and the norms of its spatial and time derivatives in the
spaces of orders `k + 1` and `k`. -/
theorem norm_ofSpatialFDerivTimeDeriv_le :
    ‖ofSpatialFDerivTimeDeriv u G H hG hH‖ ≤ 4 * (k + 3) ^ 2 * (‖u‖ + ‖G‖ + ‖H‖) := by
  have hc : ((parabolicDerivPairs (k + 2)).card : ℝ) ≤ (k + 3) ^ 2 := by
    exact_mod_cast card_parabolicDerivPairs_le (k + 2)
  have h4 := mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 4 * (‖u‖ + ‖G‖ + ‖H‖))
  rw [norm_eq]
  refine (Finset.sum_le_sum (norm_add_norm_add_norm_ofSpatialFDerivTimeDeriv_le hG hH)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  linarith

end Construction

end ParabolicCkHolderSpace

end TauCeti
