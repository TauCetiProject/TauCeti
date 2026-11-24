/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
public import TauCeti.Analysis.Holder.LowOrder
import TauCeti.Topology.MetricSpace.Holder

/-!
# Time-independent maps in the parabolic Hölder spaces of every order

A bounded `C^{k,α}` map `g` on space, viewed as the time-independent map `(x, t) ↦ g x` on a
nondegenerate closed time slab `E × [a, b]`, is a bounded parabolic Hölder map of order `k`, and
this lift

`C_b^{k,α}(E) → C_{par,b}^{k+α}(E × [a, b])`

is a bounded linear map of norm at most `2` (`TauCeti.CkHolderSpace.compSlabSpaceL`,
`TauCeti.CkHolderSpace.norm_compSlabSpaceL_le`), independent of the slab. Its mixed derivatives
are the spatial derivatives of `g`, `D_t^0 D_x^m (g ∘ π) = D^m g ∘ π` for `m ≤ k`, where `π` is
the spatial position, and every field with a time derivative vanishes. This is the order-`k`
form of `TauCeti.HolderSpace.compSlabSpaceL`, which treats the order zero: time-independent data
such as the initial value `u₀ ∈ C_b^{k+2,α}` of a Cauchy problem, coefficients that do not depend
on time, and the derivatives of the logarithm of a spatial weight, which enter the conjugated
coefficients of a weighted parabolic operator, are thereby elements of the data spaces of the
parabolic Schauder theory of order `k`.

## The argument

The fields `D r m` of `g ∘ π` are `D^m g ∘ π` for `r = 0` and zero for `r ≥ 1`, and they satisfy
the conditions of `TauCeti.ParabolicCkHolderSpace.mk`:

* the spatial derivative of `D^m g` is `D^(m+1) g`, curried on the left (Mathlib's
  `fderiv_iteratedFDeriv`), for `m < k`;
* every field is constant in time, so its time derivative is the zero field;
* the time slices of every field are constant, hence Hölder of every exponent with constant zero;
* the only nonzero field of top order is `D^k g ∘ π`, which is `α`-Hölder with the constant of
  `D^k g` because `π` is `1`-Lipschitz for the parabolic distance
  (`TauCeti.ParabolicSpaceTime.lipschitzWith_slabSpace`).

No hypothesis on `α` is needed. The norm is the sum, over `m ≤ k`, of the supremum norms of the
fields `D^m g ∘ π`, the norm of the constant time slices of `D^(k-1) g ∘ π` and the Hölder norm of
`D^k g ∘ π`; each is controlled by the corresponding part of the `C^{k,α}` norm of `g`, and
`D^(k-1) g` and `D^k g` are counted twice, which gives the factor `2`.

## Main declarations

* `TauCeti.CkHolderSpace.compSlabSpaceL`: the time-independent lift
  `C_b^{k,α}(E) → C_{par,b}^{k+α}(E × [a, b])`.
* `TauCeti.CkHolderSpace.compSlabSpaceL_apply`: its value at `(x, t)` is `g x`.
* `TauCeti.CkHolderSpace.mixedDerivL_zero_compSlabSpaceL_apply` and
  `TauCeti.CkHolderSpace.mixedDerivL_succ_compSlabSpaceL`: its mixed derivatives, and
  `TauCeti.CkHolderSpace.mixedDerivHolderL_zero_compSlabSpaceL`: its top-order Hölder field is the
  order-zero lift of the Hölder field `D^k g`.
* `TauCeti.CkHolderSpace.equivHolderSpace_compSlabSpaceL`: at order zero it is the order-zero lift
  `TauCeti.HolderSpace.compSlabSpaceL`.
* `TauCeti.CkHolderSpace.norm_compSlabSpaceL_le`: its operator norm is at most `2`; and
  `TauCeti.CkHolderSpace.compSlabSpaceL_injective`.

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3
  (the parabolic Hölder spaces `C^{k+α,(k+α)/2}`).
-/

public section
noncomputable section

namespace TauCeti

namespace CkHolderSpace

open Set ParabolicSpaceTime ParabolicCkHolderSpace
open scoped NNReal BoundedContinuousFunction

variable {k : ℕ} {α : ℝ≥0} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The spatial position on the slab `E × [a, b]`, as a continuous map. -/
private def slabSpace : C(slab (E := E) a b, E) :=
  ⟨fun p ↦ (p : ParabolicSpaceTime E).space, lipschitzWith_slabSpace.continuous⟩

/-- The field `D_t^r D_x^m` of the time-independent map `g ∘ π`: the field `D^m g ∘ π` when
`r = 0` and `m ≤ k`, and zero otherwise. -/
private def slabField (g : CkHolderSpace k α E F) (r m : ℕ) :
    slab (E := E) a b →ᵇ (E [×m]→L[ℝ] F) :=
  if h : r = 0 ∧ m ≤ k then (g.iteratedFDeriv ⟨m, Nat.lt_succ_of_le h.2⟩).compContinuous slabSpace
  else 0

private theorem slabField_zero_apply (g : CkHolderSpace k α E F) {m : ℕ} (hm : m ≤ k)
    (p : slab (E := E) a b) :
    slabField g 0 m p = _root_.iteratedFDeriv ℝ m g (p : ParabolicSpaceTime E).space := by
  rw [slabField, dite_eq_left ⟨rfl, hm⟩, BoundedContinuousFunction.compContinuous_apply,
    coe_iteratedFDeriv]
  -- `slabSpace p` is the spatial position of `p` by definition.
  rfl

private theorem slabField_succ (g : CkHolderSpace k α E F) (r m : ℕ) :
    slabField (a := a) (b := b) g (r + 1) m = 0 :=
  dite_eq_right fun h ↦ r.succ_ne_zero h.1

private theorem norm_slabField_succ (g : CkHolderSpace k α E F) (r m : ℕ) :
    ‖slabField (a := a) (b := b) g (r + 1) m‖ = 0 :=
  le_antisymm ((BoundedContinuousFunction.norm_le le_rfl).2 fun p ↦ by simp [slabField_succ])
    (by positivity)

/-- Every field of `g ∘ π` is constant along each time slice. -/
private theorem slabField_slabMk (g : CkHolderSpace k α E F) (r m : ℕ) (x : E)
    (t s : Icc a b) : slabField g r m (slabMk x t) = slabField g r m (slabMk x s) := by
  rcases r with _ | r
  · by_cases hm : m ≤ k
    · rw [slabField_zero_apply g hm, slabField_zero_apply g hm, space_slabMk, space_slabMk]
    · rw [slabField, dite_eq_right fun h ↦ hm h.2, FunLike.coe_zero,
        Pi.zero_apply, Pi.zero_apply]
  · rw [slabField_succ, FunLike.coe_zero, Pi.zero_apply, Pi.zero_apply]

/-- The norm of the field `D^m g ∘ π` is at most that of `D^m g`. -/
private theorem norm_slabField_zero_le (g : CkHolderSpace k α E F) {m : ℕ} (hm : m ≤ k) :
    ‖slabField (a := a) (b := b) g 0 m‖ ≤ ‖g.iteratedFDeriv ⟨m, Nat.lt_succ_of_le hm⟩‖ := by
  rw [slabField, dite_eq_left ⟨rfl, hm⟩]
  exact BoundedContinuousFunction.norm_compContinuous_le _ _

/-- The top-order field `D^k g ∘ π` is `α`-Hölder with the Hölder constant of `D^k g`. -/
private theorem holderWith_slabField_zero (g : CkHolderSpace k α E F) :
    HolderWith (nnHolderNorm α (_root_.iteratedFDeriv ℝ k g)) α
      (slabField (a := a) (b := b) g 0 k) := by
  have h := g.memHolder_iteratedFDeriv.holderWith.comp_lipschitzWith_one
    (lipschitzWith_slabSpace (E := E) (a := a) (b := b))
  convert h using 1
  exact funext fun p ↦ slabField_zero_apply g le_rfl p

/-- The time-independent map `g ∘ π` as an element of `C_{par,b}^{k+α}`. -/
private def compSlabSpace (g : CkHolderSpace k α E F) : ParabolicCkHolderSpace k α E F hab :=
  mk (slabField g)
    (fun r m h t x ↦ by
      rcases r with _ | r
      · have hd : DifferentiableAt ℝ (_root_.iteratedFDeriv ℝ m g) x :=
          g.contDiff.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : m < k)) x
        have hfun : (fun y ↦ slabField g 0 m (slabMk y t)) = _root_.iteratedFDeriv ℝ m g :=
          funext fun y ↦ by rw [slabField_zero_apply g (by omega), space_slabMk]
        rw [hfun, slabField_zero_apply g (by omega), space_slabMk]
        convert hd.hasFDerivAt using 1
        rw [fderiv_iteratedFDeriv]
        -- The left-currying equivalence applied to a map is `curryLeft` by definition.
        rfl
      · simp only [slabField_succ, FunLike.coe_zero, Pi.zero_apply]
        convert hasFDerivAt_const (0 : E [×m]→L[ℝ] F) x using 1
        ext
        simp)
    (fun r m _ x t ↦ by
      have hconst : ParabolicC2HolderSpace.timeExtension hab.le (slabField g r m) x =
          fun _ ↦ slabField g r m (slabMk x t) :=
        funext fun s ↦ by
          rw [ParabolicC2HolderSpace.timeExtension_def]
          exact slabField_slabMk g r m x _ t
      rw [hconst, slabField_succ, FunLike.coe_zero, Pi.zero_apply]
      exact hasDerivWithinAt_const _ _ _)
    (fun r m _ ↦ ⟨0, fun x ↦ holderWith_zero_iff.2 fun t s ↦ slabField_slabMk g r m x t s⟩)
    (fun r m h ↦ by
      rcases r with _ | r
      · obtain rfl : m = k := by omega
        exact (holderWith_slabField_zero g).memHolder
      · rw [slabField_succ]
        exact (HolderWith.zero (C := 0)).memHolder)

private theorem mixedDerivL_compSlabSpace (g : CkHolderSpace k α E F) {r m : ℕ}
    (h : 2 * r + m ≤ k) : mixedDerivL r m (compSlabSpace (hab := hab) g) = slabField g r m :=
  mixedDerivL_mk _ _ _ _ h

private theorem compSlabSpace_apply (g : CkHolderSpace k α E F) (p : slab (E := E) a b) :
    compSlabSpace (hab := hab) g p = g (p : ParabolicSpaceTime E).space := by
  rw [compSlabSpace, mk_apply, slabField_zero_apply g (Nat.zero_le k)]
  simp

/-- The contribution of the pair `(r, m)` to the norm of `g ∘ π`: twice the supremum norm of
`D^m g` and, at the top order, the Hölder constant of `D^k g`, when `r = 0`; nothing when
`r ≥ 1`. -/
private theorem norm_add_norm_add_norm_compSlabSpace_le (g : CkHolderSpace k α E F) {r m : ℕ}
    (h : 2 * r + m ≤ k) :
    ‖mixedDerivL r m (compSlabSpace (hab := hab) g)‖ +
        (‖timeSliceL r m (compSlabSpace (hab := hab) g)‖ +
          ‖mixedDerivHolderL r m (compSlabSpace (hab := hab) g)‖) ≤
      if r = 0 then 2 * ‖slabField (a := a) (b := b) g 0 m‖ +
        (if m = k then (nnHolderNorm α (_root_.iteratedFDeriv ℝ k g) : ℝ) else 0) else 0 := by
  set u := compSlabSpace (hab := hab) g
  have hD : mixedDerivL r m u = slabField g r m := mixedDerivL_compSlabSpace g h
  have hS : ‖timeSliceL r m u‖ ≤
      if 2 * r + m + 1 = k then ‖slabField (a := a) (b := b) g r m‖ else 0 := by
    split_ifs with hs
    · have := norm_timeSliceL_le_of_holderWith u hs (C := 0) fun x ↦
        holderWith_zero_iff.2 fun t s ↦ by rw [hD]; exact slabField_slabMk g r m x t s
      rwa [hD, NNReal.coe_zero, add_zero] at this
    · rw [timeSliceL_of_ne hs, zero_apply, norm_zero]
  have hH : ‖mixedDerivHolderL r m u‖ ≤
      if 2 * r + m = k then ‖slabField (a := a) (b := b) g r m‖ +
      (if r = 0 then (nnHolderNorm α (_root_.iteratedFDeriv ℝ k g) : ℝ) else 0) else 0 := by
    split_ifs with hh hr
    · subst hr
      obtain rfl : m = k := by omega
      have hcoe : ⇑(mixedDerivHolderL 0 m u) = slabField g 0 m := by
        rw [← HolderSpace.coe_toBoundedContinuousFunction,
          toBoundedContinuousFunction_mixedDerivHolderL u hh, hD]
      exact HolderSpace.norm_le_of_norm_le_of_holderWith (by positivity)
        (fun p ↦ by rw [hcoe]; exact (slabField g 0 m).norm_coe_le_norm p)
        (hcoe ▸ holderWith_slabField_zero g)
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
      have hcoe : ⇑(mixedDerivHolderL (r + 1) m u) = 0 := by
        rw [← HolderSpace.coe_toBoundedContinuousFunction,
          toBoundedContinuousFunction_mixedDerivHolderL u hh, hD, slabField_succ, FunLike.coe_zero]
      have := HolderSpace.norm_le_of_norm_le_of_holderWith (M := 0) (K := 0) le_rfl
        (fun p ↦ by rw [hcoe, Pi.zero_apply, norm_zero]) (hcoe ▸ HolderWith.zero)
      rw [NNReal.coe_zero, add_zero] at this
      rw [norm_slabField_succ, zero_add]
      exact this
    · rw [mixedDerivHolderL_of_ne hh, zero_apply, norm_zero]
  rw [hD]
  rcases r with _ | r
  · have hn := norm_nonneg (slabField (a := a) (b := b) g 0 m)
    have hK := (nnHolderNorm α (_root_.iteratedFDeriv ℝ k g)).coe_nonneg
    simp only [↓reduceIte] at hH ⊢
    split_ifs at hS hH ⊢ <;> first | omega | linarith [hn, hK]
  · simp only [norm_slabField_succ, Nat.add_one_ne_zero, ↓reduceIte, ite_self, zero_add,
      add_zero] at hS hH ⊢
    linarith [norm_nonneg (timeSliceL (r + 1) m u), norm_nonneg (mixedDerivHolderL (r + 1) m u)]

/-- Summing over the pairs `(r, m)` with `2 r + m ≤ k` a function that vanishes unless `r = 0`
sums it over `m ≤ k`. -/
private theorem sum_parabolicDerivPairs_ite_eq (G : ℕ → ℝ) :
    ∑ p ∈ parabolicDerivPairs k, (if p.1 = 0 then G p.2 else 0) =
      ∑ m ∈ Finset.range (k + 1), G m := by
  rw [← Finset.sum_filter]
  have hfilter : {p ∈ parabolicDerivPairs k | p.1 = 0} =
      (Finset.range (k + 1)).map (Function.Embedding.sectR 0 ℕ) := by
    ext ⟨r, m⟩
    simp only [Finset.mem_filter, mem_parabolicDerivPairs, Finset.mem_map, Finset.mem_range,
      Function.Embedding.sectR_apply]
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨m, by omega, rfl⟩
    · rintro ⟨n, hn, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨by omega, rfl⟩
  rw [hfilter, Finset.sum_map]
  simp only [Function.Embedding.sectR_apply]

/-- The norm of `g ∘ π` is at most twice the `C^{k,α}` norm of `g`. -/
private theorem norm_compSlabSpace_le (g : CkHolderSpace k α E F) :
    ‖compSlabSpace (hab := hab) g‖ ≤ 2 * ‖g‖ := by
  set H : ℝ := (nnHolderNorm α (_root_.iteratedFDeriv ℝ k g) : ℝ)
  set N : ℕ → ℝ := fun m ↦ if h : m ≤ k then ‖g.iteratedFDeriv ⟨m, Nat.lt_succ_of_le h⟩‖ else 0
  have hsum : ∑ m ∈ Finset.range (k + 1), N m = ∑ i : Fin (k + 1), ‖g.iteratedFDeriv i‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [N, dite_eq_left (Nat.lt_succ_iff.1 i.isLt)]
  rw [ParabolicCkHolderSpace.norm_eq]
  calc ∑ p ∈ parabolicDerivPairs k, (‖mixedDerivL p.1 p.2 (compSlabSpace (hab := hab) g)‖ +
          (‖timeSliceL p.1 p.2 (compSlabSpace (hab := hab) g)‖ +
            ‖mixedDerivHolderL p.1 p.2 (compSlabSpace (hab := hab) g)‖))
      ≤ ∑ p ∈ parabolicDerivPairs k,
          (if p.1 = 0 then 2 * N p.2 + (if p.2 = k then H else 0) else 0) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hp' := mem_parabolicDerivPairs.1 hp
        refine (norm_add_norm_add_norm_compSlabSpace_le g hp').trans ?_
        by_cases hr : p.1 = 0
        · have hk : p.2 ≤ k := by omega
          simp only [hr, ↓reduceIte, N, dite_eq_left hk]
          gcongr
          exact norm_slabField_zero_le g hk
        · simp only [hr, ↓reduceIte, le_refl]
    _ = 2 * ∑ i : Fin (k + 1), ‖g.iteratedFDeriv i‖ + H := by
        rw [sum_parabolicDerivPairs_ite_eq (fun m ↦ 2 * N m + if m = k then H else 0),
          Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
          Finset.sum_ite_eq' (Finset.range (k + 1)) k, ite_eq_left (Finset.self_mem_range_succ k)]
    _ ≤ 2 * ‖g‖ := by
        rw [CkHolderSpace.norm_eq]
        have hH : 0 ≤ H := NNReal.coe_nonneg _
        linarith

variable (hab) in
/-- **Time-independent maps of every order.** A bounded `C^{k,α}` map `g` on space, viewed as the
time-independent map `(x, t) ↦ g x` on the slab `E × [a, b]`, is a bounded parabolic Hölder map
of order `k`: its mixed derivatives `D_t^r D_x^m` are `D^m g` for `r = 0` and vanish for `r ≥ 1`.
This lift `C_b^{k,α}(E) → C_{par,b}^{k+α}(E × [a, b])` is a bounded linear map of norm at most
`2` (`CkHolderSpace.norm_compSlabSpaceL_le`). At order zero it is `HolderSpace.compSlabSpaceL`. -/
def compSlabSpaceL : CkHolderSpace k α E F →L[ℝ] ParabolicCkHolderSpace k α E F hab :=
  LinearMap.mkContinuous
    { toFun := compSlabSpace
      map_add' f g := ParabolicCkHolderSpace.ext fun p ↦ by
        simp only [compSlabSpace_apply, ParabolicCkHolderSpace.coe_add, Pi.add_apply,
          CkHolderSpace.coe_add]
      map_smul' c f := ParabolicCkHolderSpace.ext fun p ↦ by
        simp only [compSlabSpace_apply, ParabolicCkHolderSpace.coe_smul, Pi.smul_apply,
          CkHolderSpace.coe_smul, RingHom.id_apply] }
    2 norm_compSlabSpace_le

/-- The time-independent lift of `g` takes the value `g x` at `(x, t)`. -/
@[simp]
theorem compSlabSpaceL_apply (g : CkHolderSpace k α E F) (p : slab (E := E) a b) :
    compSlabSpaceL hab g p = g (p : ParabolicSpaceTime E).space :=
  compSlabSpace_apply g p

/-- The purely spatial fields `D_x^m` of the time-independent lift of `g` are the iterated
derivatives `D^m g`, for `m ≤ k`. -/
@[simp]
theorem mixedDerivL_zero_compSlabSpaceL_apply (g : CkHolderSpace k α E F) {m : ℕ} (hm : m ≤ k)
    (p : slab (E := E) a b) :
    mixedDerivL 0 m (compSlabSpaceL hab g) p =
      _root_.iteratedFDeriv ℝ m g (p : ParabolicSpaceTime E).space := by
  rw [← slabField_zero_apply g hm p]
  exact DFunLike.congr_fun (mixedDerivL_compSlabSpace g (by omega)) p

/-- The time-independent lift of `g` has no time derivatives: every field `D_t^(r+1) D_x^m`
vanishes. -/
@[simp]
theorem mixedDerivL_succ_compSlabSpaceL (g : CkHolderSpace k α E F) (r m : ℕ) :
    mixedDerivL (r + 1) m (compSlabSpaceL hab g) = 0 := by
  by_cases h : 2 * (r + 1) + m ≤ k
  · rw [← slabField_succ (a := a) (b := b) g r m]
    exact mixedDerivL_compSlabSpace g h
  · rw [mixedDerivL_of_lt (by omega), zero_apply]

/-- The top-order Hölder field `D_x^k` of the time-independent lift of `g` is the
time-independent lift of the Hölder field `D^k g`, through the order-zero lift
`HolderSpace.compSlabSpaceL`. -/
@[simp]
theorem mixedDerivHolderL_zero_compSlabSpaceL (g : CkHolderSpace k α E F) :
    mixedDerivHolderL 0 k (compSlabSpaceL hab g) =
      HolderSpace.compSlabSpaceL g.iteratedFDerivHolder := by
  refine HolderSpace.ext fun p ↦ ?_
  rw [← HolderSpace.toBoundedContinuousFunction_apply,
    toBoundedContinuousFunction_mixedDerivHolderL _ (by omega),
    mixedDerivL_zero_compSlabSpaceL_apply g le_rfl, HolderSpace.compSlabSpaceL_apply,
    iteratedFDerivHolder_apply]

/-- At order zero the time-independent lift is the order-zero lift `HolderSpace.compSlabSpaceL`,
through the identifications `CkHolderSpace.equivHolderSpace` and
`ParabolicCkHolderSpace.equivHolderSpace` with the bounded Hölder spaces. -/
@[simp]
theorem equivHolderSpace_compSlabSpaceL (g : CkHolderSpace 0 α E F) :
    ParabolicCkHolderSpace.equivHolderSpace (compSlabSpaceL hab g) =
      HolderSpace.compSlabSpaceL (CkHolderSpace.equivHolderSpace g) :=
  HolderSpace.ext fun p ↦ by
    rw [ParabolicCkHolderSpace.equivHolderSpace_apply, compSlabSpaceL_apply,
      HolderSpace.compSlabSpaceL_apply, CkHolderSpace.equivHolderSpace_apply]

/-- **The norm of the time-independent lift.** The lift `C_b^{k,α}(E) → C_{par,b}^{k+α}` has norm
at most `2`, for every order `k`, exponent `α` and slab. -/
theorem norm_compSlabSpaceL_le :
    ‖compSlabSpaceL (k := k) (α := α) (E := E) (F := F) hab‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

/-- The norm of the time-independent lift of `g` is at most twice the `C^{k,α}` norm of `g`. -/
theorem norm_compSlabSpaceL_apply_le (g : CkHolderSpace k α E F) :
    ‖compSlabSpaceL hab g‖ ≤ 2 * ‖g‖ :=
  norm_compSlabSpace_le g

/-- The time-independent lift is injective. -/
theorem compSlabSpaceL_injective :
    Function.Injective (compSlabSpaceL (k := k) (α := α) (E := E) (F := F) hab) :=
  fun f g hfg ↦ CkHolderSpace.ext fun x ↦ by
    have := DFunLike.congr_fun hfg (slabMk x ⟨a, left_mem_Icc.2 hab.le⟩)
    rwa [compSlabSpaceL_apply, compSlabSpaceL_apply, space_slabMk] at this

end CkHolderSpace

end TauCeti
