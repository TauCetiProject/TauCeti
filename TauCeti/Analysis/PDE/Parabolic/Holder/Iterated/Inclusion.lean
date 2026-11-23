/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Basic
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.FieldHolder
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder

/-!
# Inclusions between parabolic Hölder spaces of consecutive orders

For `α ≤ 1` and a nondegenerate closed time slab `E × [a, b]`, every bounded parabolic Hölder map
of order `k + 1` is one of order `k`, and the inclusion

`C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`

is a bounded linear map (`TauCeti.ParabolicCkHolderSpace.inclusionL`). It keeps the map and its
mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k`. Its norm is at most `8 N`,
where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`
(`TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le`). The bound depends neither on `E` and `F`
nor on the slab.

Only the two top orders of the smaller space need an argument; below them the conditions of both
spaces are the same derivative identities. Both come from the Hölder bounds that a map of order
`k + 1` has on its fields of every order:

* A field `D_t^r D_x^m u` with `2 r + m = k - 1` must have uniformly `(1 + α) / 2`-Hölder time
  slices. In the larger space it lies below the order `(k + 1) - 1`, so it is bounded and
  Lipschitz in time, and its time slices are `(1 + α) / 2`-Hölder with constant `3 ‖u‖`
  (`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_slabMk_of_add_one_le`).
* A field `D_t^r D_x^m u` with `2 r + m = k` must be parabolically `α`-Hölder. In the larger space
  it lies below the top order, so it is bounded, Lipschitz in space and `(1 + α) / 2`-Hölder in
  time, and parabolically `α`-Hölder with constant `6 ‖u‖`
  (`TauCeti.ParabolicCkHolderSpace.holderWith_mixedDerivL_of_le`).

The hypothesis `α ≤ 1` is used for both: a bounded Lipschitz function is `α`-Hölder only for
`α ≤ 1`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.inclusionL`: the inclusion
  `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}`.
* `TauCeti.ParabolicCkHolderSpace.inclusionL_apply` and
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_inclusionL`: it keeps the map and its fields.
* `TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le` and
  `TauCeti.ParabolicCkHolderSpace.norm_inclusionL_le_mul_sq`: the bounds on its norm.
* `TauCeti.ParabolicCkHolderSpace.inclusionOfLEL`: the inclusion
  `C_{par,b}^{n+α} → C_{par,b}^{m+α}` for `m ≤ n`, the composite of the inclusions of consecutive
  orders (`TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_self`,
  `TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_succ`), which keeps the map and its fields
  (`TauCeti.ParabolicCkHolderSpace.inclusionOfLEL_apply`,
  `TauCeti.ParabolicCkHolderSpace.mixedDerivL_inclusionOfLEL`) and has norm at most
  `(8 n²) ^ (n - m)` (`TauCeti.ParabolicCkHolderSpace.norm_inclusionOfLEL_le`).
* `TauCeti.ParabolicCkHolderSpace.inclusionL_injective`: the inclusion of consecutive orders is
  injective.
* `TauCeti.ParabolicCkHolderSpace.memHolder_mixedDerivL_of_le`: every field of order at most `k`
  is parabolically `α`-Hölder.
* `TauCeti.ParabolicCkHolderSpace.exists_coe_eq_of_le` and
  `TauCeti.ParabolicCkHolderSpace.exists_holderSpace_coe_eq`: a map of order `k` is one of every
  order `j ≤ k`, and a bounded parabolically `α`-Hölder map.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

namespace ParabolicCkHolderSpace

open Set ParabolicSpaceTime
open scoped NNReal ENNReal

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The map of order `k + 1` read as a map of order `k`. -/
private def ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ParabolicCkHolderSpace k α E F hab :=
  mk (fun r m ↦ mixedDerivL r m f) (fun _ _ h t x ↦ f.hasFDerivAt_mixedDerivL (by omega) t x)
    (fun _ _ h x t ↦ f.hasDerivWithinAt_mixedDerivL (by omega) x t)
    (fun _ _ h ↦ ⟨_, holderWith_mixedDerivL_slabMk_of_add_one_le hα f (by omega)⟩)
    (fun _ _ h ↦ (holderWith_mixedDerivL_of_le hα f (by omega)).memHolder)

private theorem mixedDerivL_ofSucc (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) : mixedDerivL r m (ofSucc hα f) = mixedDerivL r m f :=
  mixedDerivL_mk _ _ _ _ h

private theorem ofSucc_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : ofSucc hα f p = f p := by
  rw [ofSucc, mk_apply, ContinuousMultilinearMap.curry0_apply, mixedDerivL_zero_zero_apply]

/-- The norm of a map of order `k + 1`, read as a map of order `k`, is at most `8 N` times its
norm, with `N` the number of pairs `(r, m)`, `2 r + m ≤ k`. -/
private theorem norm_ofSucc_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab) :
    ‖ofSucc hα f‖ ≤ (parabolicDerivPairs k).card * 8 * ‖f‖ := by
  rw [norm_eq, mul_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp := mem_parabolicDerivPairs.1 hp
  -- Each pair contributes at most `2 ‖u‖ + 6 ‖u‖`: the Hölder constants of the two top orders
  -- are at most `3 ‖u‖` and `6 ‖u‖`.
  refine (norm_add_norm_timeSliceL_add_norm_mixedDerivHolderL_le (ofSucc hα f) (B := ‖f‖)
    (C := 6 * ‖f‖₊) ?_ (fun h x ↦ ?_) (fun h ↦ ?_)).trans_eq (by push_cast; ring)
  · rw [mixedDerivL_ofSucc hα f hp]
    exact f.norm_mixedDerivL_le p.1 p.2
  · rw [mixedDerivL_ofSucc hα f hp]
    exact (holderWith_mixedDerivL_slabMk_of_add_one_le hα f (by omega) x).mono
      (by gcongr; norm_num)
  · rw [mixedDerivL_ofSucc hα f hp]
    exact holderWith_mixedDerivL_of_le hα f (by omega)

/-- **The inclusion of parabolic Hölder spaces of consecutive orders.** For `α ≤ 1`, a bounded
parabolic Hölder map of order `k + 1` on the slab `E × [a, b]` is one of order `k`, with the same
mixed derivatives `D_t^r D_x^m u` for `2 r + m ≤ k`, and the inclusion
`C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}` is a bounded linear map. -/
def inclusionL (hα : α ≤ 1) :
    ParabolicCkHolderSpace (k + 1) α E F hab →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := ofSucc hα
      map_add' f g := ext fun p ↦ by simp only [ofSucc_apply, coe_add, Pi.add_apply]
      map_smul' c f := ext fun p ↦ by
        simp only [ofSucc_apply, coe_smul, Pi.smul_apply, RingHom.id_apply] }
    ((parabolicDerivPairs k).card * 8) (norm_ofSucc_le hα)

/-- The inclusion keeps the map. -/
@[simp]
theorem inclusionL_apply (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    (p : slab (E := E) a b) : inclusionL hα f p = f p :=
  ofSucc_apply hα f p

/-- The inclusion keeps the mixed derivatives `D_t^r D_x^m u` of parabolic order `2 r + m ≤ k`. -/
@[simp]
theorem mixedDerivL_inclusionL (hα : α ≤ 1) (f : ParabolicCkHolderSpace (k + 1) α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) :
    mixedDerivL r m (inclusionL hα f) = mixedDerivL r m f :=
  mixedDerivL_ofSucc hα f h

/-- **The norm of the inclusion.** The inclusion `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}` has norm
at most `8 N`, where `N` is the number of pairs `(r, m)` with `2 r + m ≤ k`. -/
theorem norm_inclusionL_le (hα : α ≤ 1) :
    ‖inclusionL (k := k) (E := E) (F := F) (hab := hab) hα‖ ≤
      (parabolicDerivPairs k).card * 8 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- The inclusion `C_{par,b}^{(k+1)+α} → C_{par,b}^{k+α}` has norm at most `8 (k + 1)²`. -/
theorem norm_inclusionL_le_mul_sq (hα : α ≤ 1) :
    ‖inclusionL (k := k) (E := E) (F := F) (hab := hab) hα‖ ≤ 8 * (k + 1) ^ 2 := by
  refine (norm_inclusionL_le hα).trans ?_
  have := card_parabolicDerivPairs_le k
  rw [mul_comm]
  gcongr
  exact_mod_cast this

/-- The inclusion is injective. -/
theorem inclusionL_injective (hα : α ≤ 1) :
    Function.Injective (inclusionL (k := k) (E := E) (F := F) (hab := hab) hα) :=
  fun f g hfg ↦ ext fun p ↦ by rw [← inclusionL_apply hα f p, hfg, inclusionL_apply]

/-- **The inclusion of parabolic Hölder spaces of comparable orders.** For `α ≤ 1` and `m ≤ n`,
the composite `C_{par,b}^{n+α} → C_{par,b}^{m+α}` of the inclusions of consecutive orders. -/
def inclusionOfLEL (hα : α ≤ 1) {m n : ℕ} (h : m ≤ n) :
    ParabolicCkHolderSpace n α E F hab →L[ℝ] ParabolicCkHolderSpace m α E F hab :=
  Nat.leRec (motive := fun n _ ↦
      ParabolicCkHolderSpace n α E F hab →L[ℝ] ParabolicCkHolderSpace m α E F hab)
    (ContinuousLinearMap.id ℝ _) (fun _ _ L ↦ L.comp (inclusionL hα)) h

/-- The inclusion of an order into itself is the identity. -/
@[simp]
theorem inclusionOfLEL_self (hα : α ≤ 1) (n : ℕ) :
    inclusionOfLEL (E := E) (F := F) (hab := hab) hα (le_refl n) = ContinuousLinearMap.id ℝ _ :=
  Nat.leRec_self _ _

/-- The inclusion from order `n + 1` is the inclusion from order `n` after the inclusion of
consecutive orders. -/
theorem inclusionOfLEL_succ (hα : α ≤ 1) {m n : ℕ} (h : m ≤ n) :
    inclusionOfLEL (E := E) (F := F) (hab := hab) hα (h.trans (n.le_add_right 1)) =
      (inclusionOfLEL hα h).comp (inclusionL hα) :=
  Nat.leRec_succ _ _ h

/-- The inclusion of comparable orders keeps the map. -/
@[simp]
theorem inclusionOfLEL_apply (hα : α ≤ 1) {m n : ℕ} (h : m ≤ n)
    (f : ParabolicCkHolderSpace n α E F hab) (p : slab (E := E) a b) :
    inclusionOfLEL hα h f p = f p := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [inclusionOfLEL_succ hα h, ContinuousLinearMap.comp_apply, ih, inclusionL_apply]

/-- The inclusion of comparable orders keeps the mixed derivatives `D_t^r D_x^m u` of parabolic
order `2 r + m ≤ k`. -/
@[simp]
theorem mixedDerivL_inclusionOfLEL (hα : α ≤ 1) {n : ℕ} (h : k ≤ n)
    (f : ParabolicCkHolderSpace n α E F hab) {r m : ℕ} (hrm : 2 * r + m ≤ k) :
    mixedDerivL r m (inclusionOfLEL hα h f) = mixedDerivL r m f := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [inclusionOfLEL_succ hα h, ContinuousLinearMap.comp_apply, ih,
      mixedDerivL_inclusionL hα f (hrm.trans h)]

/-- **The norm of the inclusion of comparable orders.** For `m ≤ n`, the inclusion
`C_{par,b}^{n+α} → C_{par,b}^{m+α}` has norm at most `(8 n²) ^ (n - m)`. -/
theorem norm_inclusionOfLEL_le (hα : α ≤ 1) {m n : ℕ} (h : m ≤ n) :
    ‖inclusionOfLEL (E := E) (F := F) (hab := hab) hα h‖ ≤ (8 * n ^ 2 : ℝ) ^ (n - m) := by
  induction n, h using Nat.le_induction with
  | base => simpa using ContinuousLinearMap.norm_id_le
  | succ n h ih =>
    -- Each of the `n - m` earlier inclusions has norm at most `8 n² ≤ 8 (n + 1)²`, and the last
    -- one has norm at most `8 (n + 1)²`.
    rw [inclusionOfLEL_succ hα h, Nat.succ_sub h, pow_succ]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    push_cast
    gcongr
    · exact ih.trans (by gcongr; linarith)
    · exact norm_inclusionL_le_mul_sq hα

/-- **Every field is parabolically Hölder.** For `α ≤ 1`, every field `D_t^r D_x^m u` with
`2 r + m ≤ k` of a map of order `k` is parabolically `α`-Hölder, not only those of top order:
the map is also of every order `2 r + m ≤ k`, where the field has top order. -/
theorem memHolder_mixedDerivL_of_le (hα : α ≤ 1) (f : ParabolicCkHolderSpace k α E F hab)
    {r m : ℕ} (h : 2 * r + m ≤ k) :
    MemHolder α (mixedDerivL r m f : slab (E := E) a b → E [×m]→L[ℝ] F) := by
  induction k with
  | zero => exact f.memHolder_mixedDerivL (by omega)
  | succ k ih =>
    rcases h.eq_or_lt with h | h
    · exact f.memHolder_mixedDerivL h
    · rw [← mixedDerivL_inclusionL hα f (by omega)]
      exact ih _ (by omega)

/-- For `α ≤ 1`, a parabolic Hölder map of order `k` is one of every order `j ≤ k`. -/
theorem exists_coe_eq_of_le (hα : α ≤ 1) {j : ℕ} (h : j ≤ k)
    (f : ParabolicCkHolderSpace k α E F hab) :
    ∃ g : ParabolicCkHolderSpace j α E F hab, ⇑g = ⇑f := by
  induction k, h using Nat.le_induction with
  | base => exact ⟨f, rfl⟩
  | succ k _ ih =>
    obtain ⟨g, hg⟩ := ih (inclusionL hα f)
    exact ⟨g, hg.trans (funext (inclusionL_apply hα f))⟩

/-- For `α ≤ 1`, a parabolic Hölder map of every order `k` is a bounded parabolically `α`-Hölder
map on the slab. -/
theorem exists_holderSpace_coe_eq (hα : α ≤ 1) (f : ParabolicCkHolderSpace k α E F hab) :
    ∃ g : HolderSpace α (slab (E := E) a b) F, ⇑g = ⇑f := by
  obtain ⟨g, hg⟩ := exists_coe_eq_of_le hα k.zero_le f
  exact ⟨equivHolderSpace g, funext fun p ↦ (equivHolderSpace_apply g p).trans (congrFun hg p)⟩

end ParabolicCkHolderSpace

end TauCeti
