/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.PrefixSum
public import TauCeti.LinearAlgebra.RootSystem.Weyl.IntervalBondGcd
public import TauCeti.RepresentationTheory.LSPath.Realization

import Mathlib.Data.Finset.Sort
import TauCeti.Data.Fin.Tuple.Basic
import TauCeti.Geometry.Convex.ConvexSpace.Cardinality
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Fixed-chain simplices, monotone face/merge identifications, and LS break integrality

Fixing a finite sequence of velocities `v₀, …, v_l` in a vector space `V` over an ordered field `𝕜`
parametrizes a family of duration-one piecewise-linear paths indexed by the standard `l`-simplex
`Convexity.StdSimplex 𝕜 (Fin (l + 1))`: a weight vector `w` traverses `v_j` for duration `w_j`,
producing the displacement `w_j • v_j` on the interval `[t_j, t_{j+1}]` between cumulative prefix
sums `t_k = ∑_{j < k} w_j`.

Up to piecewise-linear reparametrization (`TauCeti.PLPath`), this evaluation `chainSimplexPath`
satisfies a universal simplicial law (`TauCeti.PLPath.chainSimplexPath_map_orderHom`): pushing
barycentric weights forward along any monotone map `φ : Fin m →o Fin n` gives the same path as
pulling velocities back along `φ`. Two elementary identifications are special cases:

* **Face inclusion** (`φ = p.succAboveOrderEmb`): setting the `p`-th weight to `0` identifies the
  facet opposite vertex `p` with the `(l - 1)`-simplex obtained by omitting direction `v_p`.
* **Adjacent-direction merge** (`φ = p.predAboveOrderHom`): when `v_p = v_{p+1}`, adding the two
  adjacent weights `w_p + w_{p+1}` and deleting the internal prefix sum `t_{p+1}` identifies the
  `l`-simplex with the `(l - 1)`-simplex in which the duplicate direction has been merged.

Conversely, when no two velocities at distinct indices lie in the same ray (as on distinct orbit
weights in `W λ`), `chainSimplexPath` is injective on the **entire closed simplex**
(`TauCeti.PLPath.chainSimplexPath_injective`), recovering both the support face of nonvanishing
weights and the weights themselves from the unparametrized path.

Specializing to a direction sequence `τ₀ > τ₁ > ⋯ > τ_l` of minimal coset representatives for
`P.wallIndices b lam`, the rational break-chain integrality predicate
`TauCeti.LSPath.IsLSChainBreak` on `StdSimplex ℚ (Fin (l + 1))` is characterized for dominant `λ`
by positivity of weights and divisibility of internal break denominators by the interval bond gcds
`d_λ(τ_j, τ_{j+1})` (`TauCeti.LSPath.isLSChainBreak_iff_den_dvd_intervalBondGcd`). Over any ordered
field `𝕜`, the Lakshmibai–Seshadri paths of shape `λ` supported on order-embedded subchains of `τ`
cut out the subset `TauCeti.LSPath.lsChainSimplexSet 𝕜 τ` of the closed simplex, whose open-simplex
points are precisely the scalar pushforwards along `Rat.castHom 𝕜` of rational points satisfying
`IsLSChainBreak` (`TauCeti.LSPath.mem_lsChainSimplexSet_and_weights_pos_iff`). For dominant `λ`,
this subset is finite (`TauCeti.LSPath.finite_lsChainSimplexSet`) and strictly smaller than the
simplex whenever `1 ≤ l` (`TauCeti.LSPath.lsChainSimplexSet_ssubset_univ_iff`).

## Main definitions

* `TauCeti.PLPath.chainSimplexTimed`, `TauCeti.PLPath.chainSimplexPath`: the duration-one list of
  `(duration, displacement)` pairs (a timed presentation on the open simplex) and reparametrization
  class of a standard-simplex weight vector along a velocity sequence.
* `TauCeti.LSPath.durationSimplex`: the rational standard-simplex point of segment durations of an
  LS path.
* `TauCeti.LSPath.IsLSChainBreak`, `TauCeti.LSPath.ofChainSimplex`: the break-chain integrality
  predicate on `StdSimplex ℚ (Fin (l + 1))` and the LS encoding it constructs.
* `TauCeti.LSPath.lsChainSimplexSet`: the subset of `StdSimplex 𝕜 (Fin (l + 1))` cut out by LS paths
  on order-embedded subchains of a fixed direction chain.

## Main results

* `TauCeti.PLPath.chainSimplexPath_map_orderHom`: functoriality of `chainSimplexPath` under all
  monotone maps `Fin m →o Fin n`, with specializations `chainSimplexPath_map_succAbove` (faces) and
  `TauCeti.PLPath.chainSimplexPath_map_predAbove` (merging equal adjacent directions).
* `TauCeti.PLPath.chainSimplexPath_injective`: injectivity on the closed simplex when distinct
  indices have velocities in distinct rays.
* `TauCeti.LSPath.isLSChainBreak_iff_den_dvd_intervalBondGcd`: break-chain integrality via interval
  bond gcds for dominant shapes.
* `TauCeti.LSPath.mem_lsChainSimplexSet_and_weights_pos_iff` and
  `TauCeti.LSPath.chainSimplexPath_mem_range_toPLPath_iff`: open-simplex and closed-simplex
  characterizations of `lsChainSimplexSet`.
* `TauCeti.LSPath.finite_lsChainSimplexSet`, `TauCeti.LSPath.lsChainSimplexSet_ssubset_univ_iff`:
  finiteness of the LS subset and strict containment in the simplex whenever `1 ≤ l`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.PLPath

section FixedChainSimplex

variable {𝕜 V : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

omit [IsStrictOrderedRing 𝕜] in
/-- The duration-one list of `(duration, displacement)` pairs associated to a velocity sequence
`v : Fin n → V` and a barycentric weight vector `w : StdSimplex 𝕜 (Fin n)`: the `j`-th entry is
`(w_j, w_j • v_j)`. On the open simplex where every weight is positive, this is a timed
presentation (`PLPath.IsTimed`). -/
def chainSimplexTimed {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    List (𝕜 × V) :=
  List.ofFn fun j ↦ (w.weights j, w.weights j • v j)

omit [IsStrictOrderedRing 𝕜] in
/-- Defining formula for `TauCeti.PLPath.chainSimplexTimed`. -/
theorem chainSimplexTimed_def {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    chainSimplexTimed v w = List.ofFn fun j ↦ (w.weights j, w.weights j • v j) :=
  (rfl)

/-- The piecewise-linear path up to reparametrization presented by a velocity sequence `v` and
barycentric weights `w` in the standard simplex. -/
noncomputable def chainSimplexPath {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    PLPath 𝕜 V :=
  ofSegments 𝕜 (List.ofFn fun j ↦ w.weights j • v j)

/-- Defining formula for `TauCeti.PLPath.chainSimplexPath`. -/
theorem chainSimplexPath_def {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    chainSimplexPath v w = ofSegments 𝕜 (List.ofFn fun j ↦ w.weights j • v j) :=
  (rfl)

/-- `chainSimplexPath` is the path presented by the displacements of `chainSimplexTimed`. -/
theorem ofSegments_map_snd_chainSimplexTimed {n : ℕ} (v : Fin n → V)
    (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    ofSegments 𝕜 ((chainSimplexTimed v w).map Prod.snd) = chainSimplexPath v w := by
  simp [chainSimplexTimed_def, chainSimplexPath_def, Function.comp_def]

omit [IsStrictOrderedRing 𝕜] in
/-- `chainSimplexTimed v w` has total duration `1`. -/
@[simp]
theorem duration_chainSimplexTimed {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    duration (chainSimplexTimed v w) = 1 := by
  rw [duration_def, chainSimplexTimed_def, List.map_ofFn, List.sum_ofFn]
  exact w.total_of_fintype

/-- The endpoint of a fixed-chain simplex path is the barycentric combination `∑_j w_j • v_j` of
its vertex velocities. -/
@[simp]
theorem endpoint_chainSimplexPath {n : ℕ} (v : Fin n → V) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    (chainSimplexPath v w).endpoint = ∑ j, w.weights j • v j := by
  rw [chainSimplexPath_def, endpoint_ofSegments, List.sum_ofFn]

/-- Helper for `chainSimplexPath_map_orderHom`: grouping nonnegative scalar multiples along the
contiguous fibres of any monotone map `φ : Fin m →o Fin n` preserves the presented path. -/
private theorem ofSegments_sum_ite_orderHom {m n : ℕ} {a : Fin m → 𝕜} (ha : ∀ i, 0 ≤ a i)
    (v : Fin n → V) (φ : Fin m →o Fin n) :
    ofSegments 𝕜 (List.ofFn fun k : Fin n ↦ (∑ i, if φ i = k then a i else 0) • v k) =
      ofSegments 𝕜 (List.ofFn fun i : Fin m ↦ a i • v (φ i)) := by
  induction m generalizing n with
  | zero =>
    simp [ofSegments_eq_one_iff]
  | succ m ih_m =>
    induction n with
    | zero => exact (φ 0).elim0
    | succ n ih_n =>
      by_cases h0 : φ 0 = 0
      · have htail :
            ofSegments 𝕜
                (List.ofFn fun k ↦ (∑ i : Fin m, if φ i.succ = k then a i.succ else 0) • v k) =
              ofSegments 𝕜 (List.ofFn fun i : Fin m ↦ a i.succ • v (φ i.succ)) :=
          ih_m (ha := fun i ↦ ha i.succ) v
            (φ.comp ⟨Fin.succ, fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h⟩)
        rw [List.ofFn_succ (f := fun i : Fin (m + 1) ↦ a i • v (φ i)), h0, ofSegments_cons,
          ← htail, ← ofSegments_cons,
          List.ofFn_succ (f := fun k : Fin (n + 1) ↦
            (∑ i : Fin m, if φ i.succ = k then a i.succ else 0) • v k),
          ofSegments_smul_cons_smul_cons (ha 0)
            (Finset.sum_nonneg fun i _ ↦ by split_ifs <;> [exact ha i.succ; exact le_rfl])]
        rw [List.ofFn_succ]
        congr 2
        · simp [Fin.sum_univ_succ, h0]
        · congr 1
          funext k
          simp [Fin.sum_univ_succ, h0, (Fin.succ_ne_zero k).symm]
      · have hpos (i : Fin (m + 1)) : φ i ≠ 0 :=
          ((Fin.pos_iff_ne_zero.mpr h0).trans_le (φ.monotone (Fin.zero_le i))).ne'
        let ψ : Fin (m + 1) →o Fin n :=
          ⟨fun i ↦ (φ i).pred (hpos i), fun i j hij ↦ by
            rw [← Fin.succ_le_succ_iff, Fin.succ_pred, Fin.succ_pred]
            exact φ.monotone hij⟩
        have hψ : ⇑ψ = fun i ↦ (φ i).pred (hpos i) := OrderHom.coe_mk _ _
        have hstep := ih_n (v ∘ Fin.succ) ψ
        rw [List.ofFn_succ]
        simp only [hpos, ↓reduceIte, Finset.sum_const_zero, zero_smul, ofSegments_zero_cons]
        convert hstep using 2
        · congr 1
          funext k
          have hiff (i : Fin (m + 1)) : φ i = k.succ ↔ ψ i = k := by
            simp [hψ, Fin.pred_eq_iff_eq_succ]
          simp [hiff]
        · congr 1
          funext i
          simp [hψ]

/-- **Simplicial functoriality of fixed-chain simplex paths.** Pushing barycentric weights forward
along any monotone map `φ : Fin m →o Fin n` produces the same path modulo reparametrization as
pulling the velocity sequence back along `φ`: empty fibres contribute stationary zero segments and
nonempty fibres merge collinear segments in the same ray. -/
theorem chainSimplexPath_map_orderHom {m n : ℕ} (v : Fin n → V) (φ : Fin m →o Fin n)
    (w : Convexity.StdSimplex 𝕜 (Fin m)) :
    chainSimplexPath v (w.map φ) = chainSimplexPath (v ∘ φ) w := by
  simp only [chainSimplexPath_def, Convexity.StdSimplex.weights_map_apply, Finset.sum_filter,
    Function.comp_apply]
  exact ofSegments_sum_ite_orderHom w.nonneg v φ

/-- At the `j`-th vertex of the standard simplex, `chainSimplexPath` is the straight path along
`v j`. -/
@[simp]
theorem chainSimplexPath_single {n : ℕ} (v : Fin n → V) (j : Fin n) :
    chainSimplexPath v (Convexity.StdSimplex.single j) = straight 𝕜 (v j) := by
  have h := chainSimplexPath_map_orderHom v (OrderHom.const (Fin 1) j)
    (Convexity.StdSimplex.single (R := 𝕜) 0)
  simpa [Convexity.StdSimplex.map_single, chainSimplexPath_def, straight_def] using h

/-- **Face identification.** Embedding the `(n - 1)`-simplex as the facet opposite vertex `p`
(`w_p = 0`) identifies its path with the path along the subchain `v ∘ p.succAbove` omitting
`v p`. -/
@[simp]
theorem chainSimplexPath_map_succAbove {n : ℕ} (v : Fin (n + 1) → V) (p : Fin (n + 1))
    (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    chainSimplexPath v (w.map p.succAbove) = chainSimplexPath (v ∘ p.succAbove) w :=
  chainSimplexPath_map_orderHom v p.succAboveOrderEmb.toOrderHom w

/-- **Merging equal adjacent directions.** When `v p.castSucc = v p.succ`, collapsing the two
adjacent vertices along `p.predAbove` (summing weights `w p.castSucc + w p.succ` and deleting the
internal prefix sum `p.castSucc.succ`) leaves the presented piecewise-linear path unchanged. -/
theorem chainSimplexPath_map_predAbove {n : ℕ} {v : Fin (n + 1) → V} {p : Fin n}
    (hv : v p.castSucc = v p.succ) (w : Convexity.StdSimplex 𝕜 (Fin (n + 1))) :
    chainSimplexPath (v ∘ p.succ.succAbove) (w.map p.predAbove) = chainSimplexPath v w := by
  have hord : chainSimplexPath (v ∘ p.succ.succAbove) (w.map p.predAbove) =
      chainSimplexPath ((v ∘ p.succ.succAbove) ∘ p.predAbove) w :=
    chainSimplexPath_map_orderHom (v ∘ p.succ.succAbove) p.predAboveOrderHom w
  rw [hord, Fin.comp_succ_succAbove_comp_predAbove hv]

/-- Linear images commute with `chainSimplexPath`. -/
@[simp]
theorem map_chainSimplexPath {W : Type*} [AddCommGroup W] [Module 𝕜 W] {n : ℕ} (v : Fin n → V)
    (w : Convexity.StdSimplex 𝕜 (Fin n)) (g : V →ₗ[𝕜] W) :
    (chainSimplexPath v w).map g = chainSimplexPath (g ∘ v) w := by
  simp [chainSimplexPath_def, Function.comp_def]

end FixedChainSimplex

section Injectivity

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

omit [IsStrictOrderedRing 𝕜] in
/-- On the open interior of a standard simplex (where every weight is strictly positive),
`chainSimplexTimed v w` for a velocity sequence in `S` with distinct adjacent velocities is a
distinguished timed presentation. -/
theorem isDistinguished_chainSimplexTimed {n : ℕ} {S : Set V} {v : Fin n → V}
    (hvS : ∀ j, v j ∈ S) (hvne : ∀ i : Fin n, ∀ h : i.val + 1 < n, v i ≠ v ⟨i.val + 1, h⟩)
    {w : Convexity.StdSimplex 𝕜 (Fin n)} (hw : ∀ j, 0 < w.weights j) :
    IsDistinguished S (chainSimplexTimed v w) where
  isTimed := by
    simp only [isTimed_iff, chainSimplexTimed_def, List.forall_mem_ofFn_iff]
    exact hw
  duration_eq_one := duration_chainSimplexTimed v w
  slope_mem := by
    simp only [chainSimplexTimed_def, List.forall_mem_ofFn_iff]
    intro j
    rw [inv_smul_smul₀ (hw j).ne']
    exact hvS j
  isChain_slope := by
    have hslope (j : Fin n) : (w.weights j)⁻¹ • (w.weights j • v j) = v j :=
      inv_smul_smul₀ (hw j).ne' (v j)
    simp only [chainSimplexTimed_def, List.map_ofFn, Function.comp_def, hslope, List.isChain_ofFn]
    intro i hi
    exact hvne ⟨i, by omega⟩ hi

/-- Restricting a standard-simplex point `w` to the order-embedded face of its weight support yields
a distinguished timed presentation of `chainSimplexPath v w`. -/
private theorem isDistinguished_support_chainSimplexTimed {n : ℕ} {S : Set V} {v : Fin n → V}
    (hv : Function.Injective v) (hvS : ∀ j, v j ∈ S) (w : Convexity.StdSimplex 𝕜 (Fin n)) :
    let φ : Fin w.weights.support.card ↪o Fin n := w.weights.support.orderEmbOfFin rfl
    ∃ w' : Convexity.StdSimplex 𝕜 (Fin w.weights.support.card),
      w'.map φ = w ∧
        (∀ i, w'.weights i = w.weights (φ i)) ∧
        IsDistinguished S (chainSimplexTimed (v ∘ φ) w') ∧
        (chainSimplexTimed (v ∘ φ) w').map (fun x ↦ x.1⁻¹ • x.2) = List.ofFn (v ∘ φ) := by
  intro φ
  have hrange : ↑w.weights.support ⊆ Set.range φ := by
    simp [φ]
  let w' := w.comap φ.injective hrange
  have hw'pos (i : Fin w.weights.support.card) : 0 < w'.weights i := by
    rw [Convexity.StdSimplex.weights_comap_apply]
    exact (w.nonneg (φ i)).lt_of_ne' (Finsupp.mem_support_iff.mp (Finset.orderEmbOfFin_mem _ _ i))
  have hslope (i : Fin w.weights.support.card) :
      (w'.weights i)⁻¹ • (w'.weights i • v (φ i)) = v (φ i) :=
    inv_smul_smul₀ (hw'pos i).ne' _
  refine ⟨w', Convexity.StdSimplex.map_comap φ.injective w hrange,
    fun i ↦ Convexity.StdSimplex.weights_comap_apply φ.injective w hrange i,
    isDistinguished_chainSimplexTimed (fun i ↦ hvS (φ i))
      (fun i hi h ↦ (Fin.ne_of_lt (Nat.lt_succ_self i.val) : i ≠ ⟨i.val + 1, hi⟩)
        (φ.injective (hv h))) hw'pos, ?_⟩
  simp [chainSimplexTimed_def, Function.comp_def, hslope]

/-- **Closed-simplex injectivity of `chainSimplexPath`.** When velocities at distinct indices never
lie in the same ray (for example distinct images `f (w • λ)` of a Weyl orbit lying in pairwise
distinct rays; note that `0` cannot appear when `2 ≤ n` since `SameRay 𝕜 0 v` always holds),
`chainSimplexPath v` is injective on the entire closed standard simplex `StdSimplex 𝕜 (Fin n)`. -/
theorem chainSimplexPath_injective {n : ℕ} {v : Fin n → V}
    (hv : Pairwise fun i j ↦ ¬ SameRay 𝕜 (v i) (v j)) :
    Function.Injective (chainSimplexPath (𝕜 := 𝕜) v) := by
  have hvinj : Function.Injective v := fun i j hij ↦
    by_contra fun hne ↦ hv hne (hij ▸ SameRay.refl _)
  have hS : (Set.range v).Pairwise fun x y ↦ ¬ SameRay 𝕜 x y := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hv (ne_of_apply_ne v hne)
  intro w₁ w₂ hpath
  set φ₁ : Fin w₁.weights.support.card ↪o Fin n := w₁.weights.support.orderEmbOfFin rfl
  set φ₂ : Fin w₂.weights.support.card ↪o Fin n := w₂.weights.support.orderEmbOfFin rfl
  obtain ⟨w₁', hw₁map, -, hd₁, hsl₁⟩ :=
    isDistinguished_support_chainSimplexTimed (S := Set.range v) hvinj (fun j ↦ ⟨j, rfl⟩) w₁
  obtain ⟨w₂', hw₂map, -, hd₂, hsl₂⟩ :=
    isDistinguished_support_chainSimplexTimed (S := Set.range v) hvinj (fun j ↦ ⟨j, rfl⟩) w₂
  have hp : chainSimplexTimed (v ∘ φ₁) w₁' = chainSimplexTimed (v ∘ φ₂) w₂' := by
    refine hd₁.unique hd₂ hS ?_
    have hm₁ : chainSimplexPath v (w₁'.map φ₁) = chainSimplexPath (v ∘ φ₁) w₁' :=
      chainSimplexPath_map_orderHom v φ₁.toOrderHom w₁'
    have hm₂ : chainSimplexPath v (w₂'.map φ₂) = chainSimplexPath (v ∘ φ₂) w₂' :=
      chainSimplexPath_map_orderHom v φ₂.toOrderHom w₂'
    rw [ofSegments_map_snd_chainSimplexTimed, ofSegments_map_snd_chainSimplexTimed,
      ← hm₁, ← hm₂, hw₁map, hw₂map, hpath]
  have hsl : List.ofFn (v ∘ φ₁) = List.ofFn (v ∘ φ₂) := by
    rw [← hsl₁, ← hsl₂, hp]
  have hwt : List.ofFn w₁'.weights = List.ofFn w₂'.weights := by
    simpa [chainSimplexTimed_def, Function.comp_def] using congrArg (List.map Prod.fst) hp
  have hcard : w₁.weights.support.card = w₂.weights.support.card := by
    simpa using congrArg List.length hsl
  rw [List.ofFn_congr hcard.symm] at hsl hwt
  let e : Fin w₁.weights.support.card ≃ Fin w₂.weights.support.card := finCongr hcard
  have hw₁₂ : w₁'.map e = w₂' := by
    ext k
    obtain ⟨i, rfl⟩ := e.surjective k
    rw [Convexity.StdSimplex.weights_map_apply_of_injective e.injective]
    exact congrFun (List.ofFn_injective hwt) i
  have hcomp : (φ₂ : Fin w₂.weights.support.card → Fin n) ∘ e = φ₁ := by
    funext i
    exact (hvinj (congrFun (List.ofFn_injective hsl) i)).symm
  rw [← hw₁map, ← hw₂map, ← hw₁₂, ← Convexity.StdSimplex.map_comp, hcomp]

end Injectivity

end TauCeti.PLPath

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

section DurationSimplex

/-- The point of the rational standard `π.length`-simplex whose weights are the segment durations
`a_{j+1} - a_j` of an LS path `π`. -/
noncomputable def durationSimplex (π : LSPath P b lam) :
    Convexity.StdSimplex ℚ (Fin (π.length + 1)) where
  weights := Finsupp.equivFunOnFinite.symm π.duration
  nonneg j := (π.duration_pos j).le
  total := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp

/-- The `j`-th barycentric weight of `π.durationSimplex` is `π.duration j`. -/
@[simp]
theorem weights_durationSimplex_apply (π : LSPath P b lam) (j : Fin (π.length + 1)) :
    π.durationSimplex.weights j = π.duration j := by
  simp [durationSimplex]

/-- Every barycentric weight of `π.durationSimplex` is strictly positive. -/
theorem weights_durationSimplex_pos (π : LSPath P b lam) (j : Fin (π.length + 1)) :
    0 < π.durationSimplex.weights j := by
  simpa using π.duration_pos j

/-- `π.durationSimplex` lies in the open interior of `StdSimplex ℚ (Fin (π.length + 1))`: its
support is all of `Finset.univ`. -/
@[simp]
theorem support_weights_durationSimplex (π : LSPath P b lam) :
    π.durationSimplex.weights.support = Finset.univ := by
  ext j
  simp [Finsupp.mem_support_iff, (π.duration_pos j).ne']

/-- The duration simplex of `LSPath.single τ` is the unique point `single 0` of the `0`-simplex. -/
@[simp]
theorem durationSimplex_single
    (τ : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    (single τ : LSPath P b lam).durationSimplex = Convexity.StdSimplex.single 0 := by
  ext j
  have hj : j = 0 := Fin.ext (by have := j.isLt; have := length_single τ; simp; omega)
  simp [hj]

/-- The duration simplex of `LSPath.straight lam` is the unique point `single 0` of the
`0`-simplex. -/
@[simp]
theorem durationSimplex_straight :
    (straight lam : LSPath P b lam).durationSimplex = Convexity.StdSimplex.single 0 := by
  rw [← single_one, durationSimplex_single]

/-- The cumulative prefix sums of `π.durationSimplex` recover `π.time`. -/
@[simp]
theorem prefixSum_durationSimplex (π : LSPath P b lam) (k : Fin (π.length + 2)) :
    π.durationSimplex.prefixSum k = π.time k := by
  have heq : π.durationSimplex =
      (Convexity.StdSimplex.equivPrefixSum ℚ (π.length + 1)).symm
        ⟨π.time, π.time_zero, π.time_last, π.strictMono_time.monotone⟩ := by
    ext j
    simp [duration_def]
  rw [heq, Convexity.StdSimplex.prefixSum_equivPrefixSum_symm]

/-- Evaluating `chainSimplexTimed` at the scalar pushforward of `π.durationSimplex` recovers
`π.timed`. -/
theorem chainSimplexTimed_durationSimplex (π : LSPath P b lam) (𝕜 : Type*) {V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) :
    PLPath.chainSimplexTimed (fun j ↦ f ((π.dir j).val • lam))
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) = π.timed 𝕜 f := by
  simp [PLPath.chainSimplexTimed_def, timed_def]

/-- Evaluating `chainSimplexPath` at the scalar pushforward of `π.durationSimplex` recovers
`π.toPLPath`. -/
theorem chainSimplexPath_durationSimplex (π : LSPath P b lam) (𝕜 : Type*) {V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) :
    PLPath.chainSimplexPath (fun j ↦ f ((π.dir j).val • lam))
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) = π.toPLPath 𝕜 f := by
  rw [← PLPath.ofSegments_map_snd_chainSimplexTimed, chainSimplexTimed_durationSimplex,
    toPLPath_def]

end DurationSimplex

section BreakChainIntegrality

/-- A rational standard-simplex point `w` satisfies the **Lakshmibai–Seshadri break-chain
condition** along a direction sequence `dir` of shape `λ` if every weight is strictly positive (so
`w` lies in the open simplex) and each internal cumulative prefix sum `w.prefixSum (j + 1)` admits
an `a`-chain from `dir j` down to `dir (j + 1)` for `P.wallIndices b lam`. -/
def IsLSChainBreak {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) : Prop :=
  (∀ j, 0 < w.weights j) ∧
    ∀ j : Fin l, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head = dir j.castSucc ∧ C.last = dir j.succ ∧
        IsAChain (w.prefixSum j.castSucc.succ) lam C

/-- Defining characterization of `TauCeti.LSPath.IsLSChainBreak`. -/
theorem isLSChainBreak_iff {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    {w : Convexity.StdSimplex ℚ (Fin (l + 1))} :
    IsLSChainBreak dir w ↔
      (∀ j, 0 < w.weights j) ∧
        ∀ j : Fin l, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
          C.head = dir j.castSucc ∧ C.last = dir j.succ ∧
            IsAChain (w.prefixSum j.castSucc.succ) lam C :=
  Iff.rfl

/-- On a `0`-simplex (`l = 0`), the LS break-chain condition holds automatically at the unique
point. -/
@[simp]
theorem isLSChainBreak_fin_one
    (dir : Fin 1 → {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (w : Convexity.StdSimplex ℚ (Fin 1)) : IsLSChainBreak dir w :=
  ⟨fun j ↦ by rw [w.weights_apply_eq_one j]; exact zero_lt_one, fun j ↦ j.elim0⟩

/-- The duration simplex of any LS path satisfies `IsLSChainBreak` along its direction sequence. -/
@[simp]
theorem isLSChainBreak_durationSimplex (π : LSPath P b lam) :
    IsLSChainBreak π.dir π.durationSimplex := by
  refine ⟨π.weights_durationSimplex_pos, fun j ↦ ?_⟩
  simpa only [prefixSum_durationSimplex] using π.exists_isAChain j

/-- **Interval bond gcd criterion for `IsLSChainBreak`.** For a dominant shape `λ` and a decreasing
direction sequence in `W / W_λ`, a rational simplex point `w` satisfies `IsLSChainBreak` if and
only if all its weights are positive and the denominator of each internal cumulative prefix sum
`w.prefixSum (j + 1)` divides the interval bond gcd `d_λ(dir j, dir (j + 1))`. -/
theorem isLSChainBreak_iff_den_dvd_intervalBondGcd (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).val (dir j.castSucc).val)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) :
    IsLSChainBreak dir w ↔
      (∀ j, 0 < w.weights j) ∧
        ∀ j : Fin l, (w.prefixSum j.castSucc.succ).den ∣
          intervalBondGcd b lam (dir j.castSucc).val (dir j.succ).val := by
  refine and_congr_right' (forall_congr' fun j ↦ ?_)
  simpa only [Subtype.ext_iff] using
    exists_isAChain_iff_den_dvd_intervalBondGcd hlam (dir j.castSucc).property (dir j.succ).property
        (hdir j)

/-- Construct the Lakshmibai–Seshadri path of shape `λ` from a direction sequence with distinct
adjacent directions and a rational simplex point satisfying `IsLSChainBreak`. -/
noncomputable def ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w) :
    LSPath P b lam where
  length := l
  dir := dir
  time := w.prefixSum
  time_zero := w.prefixSum_zero
  time_last := w.prefixSum_last
  strictMono_time := w.strictMono_prefixSum_iff.mpr hw.1
  dir_succ_ne := hne
  exists_isAChain := hw.2

/-- `ofChainSimplex` has `l` internal breaks. -/
@[simp]
theorem length_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w) :
    (ofChainSimplex dir hne w hw).length = l :=
  (rfl)

/-- The direction sequence of `ofChainSimplex` is `dir`. -/
@[simp]
theorem dir_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (j : Fin ((ofChainSimplex dir hne w hw).length + 1)) :
    (ofChainSimplex dir hne w hw).dir j =
      dir (j.cast (congrArg (· + 1) (length_ofChainSimplex dir hne w hw))) :=
  (rfl)

/-- The break-time sequence of `ofChainSimplex` is `w.prefixSum`. -/
@[simp]
theorem time_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (k : Fin ((ofChainSimplex dir hne w hw).length + 2)) :
    (ofChainSimplex dir hne w hw).time k =
      w.prefixSum (k.cast (congrArg (· + 2) (length_ofChainSimplex dir hne w hw))) :=
  (rfl)

/-- The segment durations of `ofChainSimplex` recover the weights of `w`. -/
@[simp]
theorem duration_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (j : Fin ((ofChainSimplex dir hne w hw).length + 1)) :
    (ofChainSimplex dir hne w hw).duration j =
      w.weights (j.cast (congrArg (· + 1) (length_ofChainSimplex dir hne w hw))) := by
  simp only [duration_def, time_ofChainSimplex]
  exact w.prefixSum_succ_sub_castSucc
    (j.cast (congrArg (· + 1) (length_ofChainSimplex dir hne w hw)))

/-- Taking `durationSimplex` of `ofChainSimplex` recovers `w` up to index casting. -/
@[simp]
theorem durationSimplex_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w) :
    (ofChainSimplex dir hne w hw).durationSimplex =
      w.map (finCongr (congrArg (· + 1) (length_ofChainSimplex dir hne w hw)).symm) := by
  let e := finCongr (congrArg (· + 1) (length_ofChainSimplex dir hne w hw)).symm
  ext k
  obtain ⟨j, rfl⟩ := e.surjective k
  rw [Convexity.StdSimplex.weights_map_apply_of_injective e.injective,
    weights_durationSimplex_apply, duration_ofChainSimplex]
  simp [e]

/-- Reconstructing an LS path from `π.dir` and `π.durationSimplex` recovers `π`. -/
@[simp]
theorem ofChainSimplex_durationSimplex (π : LSPath P b lam)
    (hne : ∀ j : Fin π.length, π.dir j.succ ≠ π.dir j.castSucc)
    (hw : IsLSChainBreak π.dir π.durationSimplex) :
    ofChainSimplex π.dir hne π.durationSimplex hw = π := by
  apply LSPath.ext
  · -- Direction lists agree by definition of `ofChainSimplex` (`length` and `dir` are unchanged).
    rfl
  · exact congrArg List.ofFn (funext π.prefixSum_durationSimplex)

/-- `ofChainSimplex` determines the underlying rational simplex point `w`. -/
theorem ofChainSimplex_injective {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    {w₁ w₂ : Convexity.StdSimplex ℚ (Fin (l + 1))}
    (hw₁ : IsLSChainBreak dir w₁) (hw₂ : IsLSChainBreak dir w₂)
    (h : ofChainSimplex dir hne w₁ hw₁ = ofChainSimplex dir hne w₂ hw₂) :
    w₁ = w₂ :=
  Convexity.StdSimplex.prefixSum_injective
    (List.ofFn_injective (congrArg (fun π ↦ List.ofFn π.time) h))

/-- Realizing `ofChainSimplex` gives `chainSimplexPath` at the scalar pushforward of `w`. -/
@[simp]
theorem toPLPath_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) :
    (ofChainSimplex dir hne w hw).toPLPath 𝕜 f =
      PLPath.chainSimplexPath (fun j ↦ f ((dir j).val • lam))
        (w.mapRange (Rat.castHom 𝕜) Rat.cast_mono) := by
  simp only [toPLPath_def, timed_def, PLPath.chainSimplexPath_def]
  rw [List.map_ofFn, List.ofFn_congr (congrArg (· + 1) (length_ofChainSimplex dir hne w hw))]
  simp

/-- For dominant `λ` and distinct adjacent directions, only finitely many points of the rational
`l`-simplex satisfy `IsLSChainBreak`. -/
theorem finite_setOf_isLSChainBreak (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc) :
    {w : Convexity.StdSimplex ℚ (Fin (l + 1)) | IsLSChainBreak dir w}.Finite := by
  have := LSPath.finite hlam
  rw [← Set.finite_coe_iff]
  exact Finite.of_injective
    (fun w : {w // IsLSChainBreak dir w} ↦ ofChainSimplex dir hne w.val w.property)
    fun w₁ w₂ h ↦ Subtype.ext (ofChainSimplex_injective hne w₁.property w₂.property h)

/-- Inside the rational `l`-simplex, the points satisfying `IsLSChainBreak` form a strict subset
whenever `1 ≤ l` (and exhaust the `0`-simplex when `l = 0`). -/
theorem setOf_isLSChainBreak_ssubset_univ_iff {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    {w : Convexity.StdSimplex ℚ (Fin (l + 1)) | IsLSChainBreak dir w} ⊂ Set.univ ↔ 1 ≤ l := by
  rw [Set.ssubset_univ_iff]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · refine iff_of_true (fun huniv ↦ ?_) hl
    have hmem : Convexity.StdSimplex.single (0 : Fin (l + 1)) ∈
        {w : Convexity.StdSimplex ℚ (Fin (l + 1)) | IsLSChainBreak dir w} :=
      huniv ▸ Set.mem_univ _
    have hpos := hmem.1 ⟨1, by omega⟩
    simp at hpos

end BreakChainIntegrality

section ClosedChainSimplex

variable (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- The subset of the closed fixed-chain simplex `StdSimplex 𝕜 (Fin (l + 1))` consisting of the
barycentric weight vectors of Lakshmibai–Seshadri paths of shape `λ` whose direction sequence is an
order-embedded subchain of `dir` (including all boundary faces where weights vanish). -/
def lsChainSimplexSet {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    Set (Convexity.StdSimplex 𝕜 (Fin (l + 1))) :=
  {x | ∃ (π : LSPath P b lam) (φ : Fin (π.length + 1) ↪o Fin (l + 1)),
    dir ∘ φ = π.dir ∧
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ = x}

variable {𝕜}

/-- Membership characterization of `TauCeti.LSPath.lsChainSimplexSet`. -/
theorem mem_lsChainSimplexSet_iff {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    {x : Convexity.StdSimplex 𝕜 (Fin (l + 1))} :
    x ∈ lsChainSimplexSet 𝕜 dir ↔
      ∃ (π : LSPath P b lam) (φ : Fin (π.length + 1) ↪o Fin (l + 1)),
        dir ∘ φ = π.dir ∧
          (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ = x :=
  Iff.rfl

/-- **Open-simplex characterization of `lsChainSimplexSet`.** For a direction sequence `dir` with
distinct adjacent directions, a point `x` in the open interior of `StdSimplex 𝕜 (Fin (l + 1))`
(where every weight is strictly positive) belongs to `lsChainSimplexSet 𝕜 dir` if and only if it is
the scalar pushforward along `Rat.castHom 𝕜` of a rational simplex point satisfying
`IsLSChainBreak dir`. -/
theorem mem_lsChainSimplexSet_and_weights_pos_iff {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (x : Convexity.StdSimplex 𝕜 (Fin (l + 1))) :
    x ∈ lsChainSimplexSet 𝕜 dir ∧ (∀ j, 0 < x.weights j) ↔
      ∃ w : Convexity.StdSimplex ℚ (Fin (l + 1)),
        IsLSChainBreak dir w ∧ w.mapRange (Rat.castHom 𝕜) Rat.cast_mono = x := by
  constructor
  · rintro ⟨⟨π, φ, hdir, rfl⟩, hpos⟩
    have hsurj : Function.Surjective φ := fun j ↦ by
      by_contra hj
      have h0 :
          ((π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ).weights j = 0 := by
        rw [Convexity.StdSimplex.weights_map_apply]
        exact Finset.sum_eq_zero fun i hi ↦
          absurd (Finset.mem_filter.mp hi).2 fun h ↦ hj ⟨i, h⟩
      exact (hpos j).ne' h0
    have hcard := Fintype.card_of_bijective ⟨φ.injective, hsurj⟩
    simp only [Fintype.card_fin] at hcard
    have hlen : π.length = l := Nat.add_right_cancel hcard
    cases π with | mk plen pdir ptime hz hlast hmono hpne hchain =>
    dsimp only at hlen φ hdir hpos hsurj
    subst hlen
    have hφ : (φ : Fin (plen + 1) → Fin (plen + 1)) = id :=
      (φ.strictMono.range_inj_of_wellFoundedLT strictMono_id).mp
        (hsurj.range_eq.trans Set.range_id.symm)
    have hdir' : dir = pdir := by simpa [hφ] using hdir
    refine ⟨(LSPath.mk plen pdir ptime hz hlast hmono hpne hchain).durationSimplex,
      hdir' ▸ (LSPath.mk plen pdir ptime hz hlast hmono hpne hchain).isLSChainBreak_durationSimplex,
      ?_⟩
    rw [hφ, Convexity.StdSimplex.map_id]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, fun j ↦ ?_⟩
    · let π := ofChainSimplex dir hne w hw
      let e := Fin.castOrderIso (congrArg (· + 1) (length_ofChainSimplex dir hne w hw))
      let φ : Fin (π.length + 1) ↪o Fin (l + 1) := e.toOrderEmbedding
      refine ⟨π, φ, by funext j; simp [π, φ, e], ?_⟩
      have hcomp :
          (φ : Fin (π.length + 1) → Fin (l + 1)) ∘
            finCongr (congrArg (· + 1) (length_ofChainSimplex dir hne w hw)).symm = id := by
        funext k
        simp [φ, e]
      rw [durationSimplex_ofChainSimplex, Convexity.StdSimplex.mapRange_map,
        ← Convexity.StdSimplex.map_comp, hcomp, Convexity.StdSimplex.map_id]
    · rw [Convexity.StdSimplex.weights_mapRange_apply]
      exact Rat.cast_pos.mpr (hw.1 j)

/-- Pushing `lsChainSimplexSet` along an order embedding of subchains carries LS points of the face
into LS points of the ambient simplex. -/
theorem map_mem_lsChainSimplexSet {m l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (ψ : Fin (m + 1) ↪o Fin (l + 1)) {x : Convexity.StdSimplex 𝕜 (Fin (m + 1))}
    (hx : x ∈ lsChainSimplexSet 𝕜 (dir ∘ ψ)) :
    x.map ψ ∈ lsChainSimplexSet 𝕜 dir := by
  obtain ⟨π, φ, hdir, rfl⟩ := hx
  refine ⟨π, φ.trans ψ, hdir, ?_⟩
  rw [RelEmbedding.coe_trans, Convexity.StdSimplex.map_comp]

/-- Every vertex of a fixed-chain simplex belongs to `lsChainSimplexSet`, realized by the
zero-break LS path `LSPath.single (dir j)`. -/
theorem single_mem_lsChainSimplexSet {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (j : Fin (l + 1)) : Convexity.StdSimplex.single j ∈ lsChainSimplexSet 𝕜 dir := by
  let e : Fin ((single (dir j)).length + 1) ≃o Fin 1 :=
    Fin.castOrderIso (congrArg (· + 1) (length_single (dir j)))
  let c : Fin 1 ↪o Fin (l + 1) :=
    ⟨⟨fun _ ↦ j, Function.injective_of_subsingleton _⟩,
      fun {a b} ↦ by simp [Subsingleton.elim a b]⟩
  refine ⟨single (dir j), e.toOrderEmbedding.trans c, by funext k; simp [c], ?_⟩
  rw [durationSimplex_single, Convexity.StdSimplex.mapRange_single, Convexity.StdSimplex.map_single]
  simp [c]

/-- Every point of `lsChainSimplexSet` realizes a Lakshmibai–Seshadri path of shape `λ`. -/
theorem chainSimplexPath_mem_range_toPLPath_of_mem_lsChainSimplexSet {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    {x : Convexity.StdSimplex 𝕜 (Fin (l + 1))} (hx : x ∈ lsChainSimplexSet 𝕜 dir) :
    PLPath.chainSimplexPath (fun j ↦ f ((dir j).val • lam)) x ∈
      Set.range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  obtain ⟨π, φ, hdir, rfl⟩ := hx
  refine ⟨π, ?_⟩
  have hcomp : ((fun j ↦ f ((dir j).val • lam)) ∘ φ) = fun i ↦ f ((π.dir i).val • lam) := by
    funext i
    exact congrArg (fun τ ↦ f (τ.val • lam)) (congrFun hdir i)
  have hmap : PLPath.chainSimplexPath (fun j ↦ f ((dir j).val • lam))
      ((π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ) =
      PLPath.chainSimplexPath ((fun j ↦ f ((dir j).val • lam)) ∘ φ)
        (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) :=
    PLPath.chainSimplexPath_map_orderHom (fun j ↦ f ((dir j).val • lam)) φ.toOrderHom _
  rw [hmap, hcomp, π.chainSimplexPath_durationSimplex 𝕜 f]

/-- **Characterization of LS paths inside a closed fixed-chain simplex.** For a dominant shape `λ`,
an additive map `f` injective on the Weyl orbit of `λ` whose realized orbit has no two distinct
weights in the same ray, and an injective direction sequence `dir` (such as any strictly decreasing
Bruhat chain in `W / W_λ`), a point `x` of the closed simplex `StdSimplex 𝕜 (Fin (l + 1))` presents
an LS path of shape `λ` if and only if `x ∈ lsChainSimplexSet 𝕜 dir`. -/
theorem chainSimplexPath_mem_range_toPLPath_iff {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {f : M →+ V} (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : Function.Injective dir) (x : Convexity.StdSimplex 𝕜 (Fin (l + 1))) :
    PLPath.chainSimplexPath (fun j ↦ f ((dir j).val • lam)) x ∈
        Set.range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      x ∈ lsChainSimplexSet 𝕜 dir := by
  have := P.flip_isReduced
  refine ⟨?_, chainSimplexPath_mem_range_toPLPath_of_mem_lsChainSimplexSet f⟩
  rintro ⟨π, hπ⟩
  let v : Fin (l + 1) → V := fun j ↦ f ((dir j).val • lam)
  have hv : Function.Injective v := fun j₁ j₂ h ↦
    hdir (eq_of_isMinimalCosetRep_of_apply_smul_eq hlam hf h)
  set ψ : Fin x.weights.support.card ↪o Fin (l + 1) := x.weights.support.orderEmbOfFin rfl
  obtain ⟨x', hx'map, hx'wt, hdist, -⟩ :=
    PLPath.isDistinguished_support_chainSimplexTimed
      (S := Set.range fun w : P.weylGroup ↦ f (w • lam)) hv (fun j ↦ ⟨(dir j).val, rfl⟩) x
  have htimed : PLPath.chainSimplexTimed (v ∘ ψ) x' = π.timed 𝕜 f := by
    refine hdist.unique (π.isDistinguished_timed 𝕜 f hlam hf) hS ?_
    have hmap : PLPath.chainSimplexPath v (x'.map ψ) = PLPath.chainSimplexPath (v ∘ ψ) x' :=
      PLPath.chainSimplexPath_map_orderHom v ψ.toOrderHom x'
    rw [PLPath.ofSegments_map_snd_chainSimplexTimed, ← hmap, hx'map, ← toPLPath_def]
    exact hπ.symm
  have hcard : π.length + 1 = x.weights.support.card := by
    simpa [PLPath.chainSimplexTimed_def, timed_def] using (congrArg List.length htimed).symm
  let φ : Fin (π.length + 1) ↪o Fin (l + 1) := (Fin.castOrderIso hcard).toOrderEmbedding.trans ψ
  have hφcoe : (φ : Fin (π.length + 1) → Fin (l + 1)) = ψ ∘ Fin.castOrderIso hcard := by
    dsimp only [φ]
    rw [RelEmbedding.coe_trans, OrderIso.coe_toOrderEmbedding]
  rw [PLPath.chainSimplexTimed_def, timed_def, List.ofFn_congr hcard.symm] at htimed
  have hentry (i : Fin (π.length + 1)) :
      (x.weights (φ i), x.weights (φ i) • f ((dir (φ i)).val • lam)) =
        ((π.duration i : 𝕜), (π.duration i : 𝕜) • f ((π.dir i).val • lam)) := by
    simpa [φ, ψ, hx'wt, v] using congrFun (List.ofFn_injective htimed) i
  refine ⟨π, φ, ?_, ?_⟩
  · funext i
    have hd : x.weights (φ i) = (π.duration i : 𝕜) := congrArg Prod.fst (hentry i)
    have hsnd := congrArg Prod.snd (hentry i)
    rw [hd] at hsnd
    have hne : (π.duration i : 𝕜) ≠ 0 := Rat.cast_ne_zero.mpr (π.duration_pos i).ne'
    exact eq_of_isMinimalCosetRep_of_smul_apply_smul_eq hlam hf hne hsnd
  · rw [← hx'map, hφcoe, Convexity.StdSimplex.map_comp]
    congr 1
    ext k
    obtain ⟨i, rfl⟩ := (Fin.castOrderIso hcard).surjective k
    rw [Convexity.StdSimplex.weights_map_apply_of_injective (Fin.castOrderIso hcard).injective]
    simpa [hx'wt, φ, ψ] using (congrArg Prod.fst (hentry i)).symm

/-- **Finiteness of the LS subset in a closed fixed-chain simplex.** For a dominant shape `λ`,
`lsChainSimplexSet 𝕜 dir` is finite. -/
theorem finite_lsChainSimplexSet (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    (lsChainSimplexSet 𝕜 dir).Finite := by
  have := LSPath.finite hlam
  let S (π : LSPath P b lam) : Set (Convexity.StdSimplex 𝕜 (Fin (l + 1))) :=
    Set.range fun φ : Fin (π.length + 1) ↪o Fin (l + 1) ↦
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ
  refine (Set.finite_iUnion (f := S) fun π ↦ ?_).subset ?_
  · have : Finite (Fin (π.length + 1) ↪o Fin (l + 1)) :=
      Finite.of_injective (fun φ : Fin (π.length + 1) ↪o Fin (l + 1) ↦
        (φ : Fin (π.length + 1) → Fin (l + 1))) DFunLike.coe_injective
    exact Set.finite_range _
  · rintro _ ⟨π, φ, -, rfl⟩
    exact Set.mem_iUnion.mpr ⟨π, φ, rfl⟩

/-- **The LS subset is not the whole continuum of a positive-dimensional chain simplex.** For a
dominant shape `λ`, `lsChainSimplexSet 𝕜 dir` is a strict subset of `StdSimplex 𝕜 (Fin (l + 1))`
if and only if `1 ≤ l` (and equals the unique point of the `0`-simplex when `l = 0`). -/
theorem lsChainSimplexSet_ssubset_univ_iff (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    lsChainSimplexSet 𝕜 dir ⊂ Set.univ ↔ 1 ≤ l := by
  rw [Set.ssubset_univ_iff]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · refine iff_of_false (fun hne ↦ hne (Set.eq_univ_iff_forall.mpr fun x ↦ ?_)) (by omega)
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    rw [Subsingleton.elim x (Convexity.StdSimplex.single 0)]
    exact single_mem_lsChainSimplexSet dir 0
  · refine iff_of_true (fun huniv ↦ ?_) hl
    have : Nontrivial (Fin (l + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    exact Set.infinite_univ (huniv ▸ finite_lsChainSimplexSet hlam dir)

end ClosedChainSimplex

end TauCeti.LSPath
