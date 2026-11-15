/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Fin.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.PrefixSum
public import TauCeti.LinearAlgebra.RootSystem.Weyl.IntervalBondGcd
public import TauCeti.RepresentationTheory.LSPath.Realization
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# Fixed-chain simplices, monotone face/merge identifications, and LS break integrality

Fixing a finite sequence of velocities `v₀, …, v_l` in a vector space `V` over an ordered field `𝕜`
parametrizes a family of duration-one piecewise-linear paths indexed by the standard `l`-simplex
`Convexity.StdSimplex 𝕜 (Fin (l + 1))`: a weight vector `w` traverses `v_j` for duration `w_j`,
producing the displacement `w_j • v_j` on the interval `[t_j, t_{j+1}]` between cumulative break
times `t_k = ∑_{j < k} w_j`.

Up to piecewise-linear reparametrization (`TauCeti.PLPath`), this evaluation `chainSimplexPath`
satisfies a universal simplicial law (`TauCeti.PLPath.chainSimplexPath_map_orderHom`): pushing
barycentric weights forward along any monotone map `φ : Fin m →o Fin n` gives the same path as
pulling velocities back along `φ`. Two elementary identifications are special cases:

* **Face inclusion** (`φ = p.succAboveOrderEmb`): setting the `p`-th weight to `0` identifies the
  facet opposite vertex `p` with the `(l - 1)`-simplex obtained by omitting direction `v_p`.
* **Adjacent-direction merge** (`φ = p.predAboveOrderHom`): when `v_p = v_{p+1}`, adding the two
  adjacent weights `w_p + w_{p+1}` and deleting the internal break time `t_{p+1}` identifies the
  `(l + 1)`-simplex with the `l`-simplex in which the duplicate direction has been merged.

Conversely, when the velocities `v_j` are pairwise distinct elements of a set `S` with no two
distinct vectors in the same ray (such as a Weyl orbit `W λ`), `chainSimplexPath` is injective on
the **entire closed simplex** (`TauCeti.PLPath.chainSimplexPath_injective`), recovering both the
support face of nonvanishing weights and the weights themselves from the unparametrized path.

Specializing to a direction sequence `τ₀ > τ₁ > ⋯ > τ_l` in the parabolic quotient `W / W_λ` of a
root datum, the Lakshmibai–Seshadri paths of dominant shape `λ` supported on subchains of `τ` cut
out a **finite** subset `TauCeti.LSPath.lsChainSimplexSet` of the closed simplex, characterized on
the open simplex by positivity of weights and divisibility of internal break denominators by the
interval bond gcds `d_λ(τ_j, τ_{j+1})`
(`TauCeti.LSPath.isLSChainBreak_iff_den_dvd_intervalBondGcd`). Whenever `1 ≤ l`, this finite LS
subset is a strict subset of the simplex continuum (both over `ℚ` and over `ℝ`); only at a
single-direction vertex `l = 0` does it exhaust the `0`-simplex.

## Main definitions

* `TauCeti.PLPath.chainSimplexTimed`, `TauCeti.PLPath.chainSimplexPath`: the timed presentation and
  reparametrization class of a standard-simplex weight vector along a velocity sequence.
* `TauCeti.LSPath.durationSimplex`: the rational standard-simplex point of segment durations of an
  LS path.
* `TauCeti.LSPath.IsLSChainBreak`, `TauCeti.LSPath.ofChainSimplex`: the break-chain integrality
  predicate on `StdSimplex ℚ (Fin (l + 1))` and the LS encoding it constructs.
* `TauCeti.LSPath.single`: the zero-break LS path running along any minimal coset representative.
* `TauCeti.LSPath.lsChainSimplexSet`: the subset of `StdSimplex 𝕜 (Fin (l + 1))` cut out by LS paths
  on order-embedded subchains of a fixed direction chain.

## Main results

* `TauCeti.PLPath.chainSimplexPath_map_orderHom`: functoriality of `chainSimplexPath` under all
  monotone maps `Fin m →o Fin n`, with specializations `chainSimplexPath_map_succAbove` (faces) and
  `chainSimplexPath_map_predAbove` (merging equal adjacent directions).
* `TauCeti.PLPath.chainSimplexPath_injective`: injectivity on the closed simplex when velocities
  are distinct and pairwise non-collinear along rays.
* `TauCeti.LSPath.isLSChainBreak_iff_den_dvd_intervalBondGcd`: break-chain integrality via interval
  bond gcds for dominant shapes.
* `TauCeti.LSPath.chainSimplexPath_mem_range_toPLPath_iff`: a closed-simplex point realizes an LS
  path of dominant shape `λ` if and only if it belongs to `lsChainSimplexSet`.
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
/-- The duration-one timed presentation associated to a velocity sequence `v : Fin n → V` and a
barycentric weight vector `w : StdSimplex 𝕜 (Fin n)`: the `j`-th piece has duration `w_j` and
displacement `w_j • v_j`. -/
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
/-- The timed presentation of a standard-simplex point has total duration `1`. -/
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
        have hstep := ih_n (v ∘ Fin.succ) ψ
        rw [List.ofFn_succ]
        simp only [hpos, ↓reduceIte, Finset.sum_const_zero, zero_smul, ofSegments_zero_cons]
        convert hstep using 2
        · congr 1
          funext k
          have hiff (i : Fin (m + 1)) : φ i = k.succ ↔ ψ i = k := by
            change φ i = k.succ ↔ (φ i).pred (hpos i) = k
            rw [Fin.pred_eq_iff_eq_succ]
          simp [hiff]
        · congr 1
          funext i
          change a i • v (φ i) = a i • v (ψ i).succ
          rw [show (ψ i).succ = φ i from Fin.succ_pred (φ i) (hpos i)]

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
internal break `p.castSucc.succ`) leaves the presented piecewise-linear path unchanged. -/
theorem chainSimplexPath_map_predAbove {n : ℕ} {v : Fin (n + 2) → V} {p : Fin (n + 1)}
    (hv : v p.castSucc = v p.succ) (w : Convexity.StdSimplex 𝕜 (Fin (n + 2))) :
    chainSimplexPath (v ∘ p.succ.succAbove) (w.map p.predAbove) = chainSimplexPath v w := by
  have hord : chainSimplexPath (v ∘ p.succ.succAbove) (w.map p.predAbove) =
      chainSimplexPath ((v ∘ p.succ.succAbove) ∘ p.predAbove) w :=
    chainSimplexPath_map_orderHom (v ∘ p.succ.succAbove) p.predAboveOrderHom w
  rw [hord]
  congr 1
  funext i
  by_cases hi : i = p.succ
  · subst hi
    have hpred : p.predAbove p.succ = p := by
      rw [Fin.predAbove_of_castSucc_lt _ _ p.castSucc_lt_succ, Fin.pred_succ]
    simp [Function.comp_apply, hpred, Fin.succAbove_of_castSucc_lt _ _ p.castSucc_lt_succ, hv]
  · simp [Function.comp_apply, Fin.succ_succAbove_predAbove hi]

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
/-- On the open interior of a standard simplex (where every weight is strictly positive), the timed
presentation of a velocity sequence in `S` with distinct adjacent velocities is distinguished. -/
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
    let φ : Fin w.weights.support.card ↪o Fin n :=
      (w.weights.support.orderIsoOfFin rfl).toOrderEmbedding.trans
        (OrderEmbedding.subtype (· ∈ w.weights.support))
    ∃ w' : Convexity.StdSimplex 𝕜 (Fin w.weights.support.card),
      w'.map φ = w ∧
        (∀ i, w'.weights i = w.weights (φ i)) ∧
        IsDistinguished S (chainSimplexTimed (v ∘ φ) w') ∧
        (chainSimplexTimed (v ∘ φ) w').map (fun x ↦ x.1⁻¹ • x.2) = List.ofFn (v ∘ φ) := by
  intro φ
  have hrange : ↑w.weights.support ⊆ Set.range φ := by
    intro j hj
    exact ⟨(w.weights.support.orderIsoOfFin rfl).symm ⟨j, hj⟩,
      congrArg Subtype.val ((w.weights.support.orderIsoOfFin rfl).apply_symm_apply ⟨j, hj⟩)⟩
  let w' := w.comap φ.injective hrange
  have hw'pos (i : Fin w.weights.support.card) : 0 < w'.weights i := by
    rw [Convexity.StdSimplex.weights_comap_apply]
    have hmem : φ i ∈ w.weights.support := ((w.weights.support.orderIsoOfFin rfl) i).2
    exact (w.nonneg (φ i)).lt_of_ne' (Finsupp.mem_support_iff.mp hmem)
  have hslope (i : Fin w.weights.support.card) :
      (w'.weights i)⁻¹ • (w'.weights i • v (φ i)) = v (φ i) :=
    inv_smul_smul₀ (hw'pos i).ne' _
  refine ⟨w', Convexity.StdSimplex.map_comap φ.injective w hrange,
    fun i ↦ Convexity.StdSimplex.weights_comap_apply φ.injective w hrange i,
    isDistinguished_chainSimplexTimed (fun i ↦ hvS (φ i))
      (fun i hi h ↦ (Fin.ne_of_lt (Nat.lt_succ_self i.val) : i ≠ ⟨i.val + 1, hi⟩)
        (φ.injective (hv h))) hw'pos, ?_⟩
  simp [chainSimplexTimed_def, Function.comp_def, hslope]

/-- **Closed-simplex injectivity of `chainSimplexPath`.** When `v : Fin n → V` takes pairwise
distinct values in a set `S` with no two distinct vectors in the same ray (such as a Weyl orbit of
any weight, including `0`), `chainSimplexPath v` is injective on the entire closed standard simplex
`StdSimplex 𝕜 (Fin n)`. -/
theorem chainSimplexPath_injective {n : ℕ} {S : Set V} {v : Fin n → V}
    (hv : Function.Injective v) (hvS : ∀ j, v j ∈ S)
    (hS : S.Pairwise fun x y ↦ ¬ SameRay 𝕜 x y) :
    Function.Injective (chainSimplexPath (𝕜 := 𝕜) v) := by
  intro w₁ w₂ hpath
  set φ₁ : Fin w₁.weights.support.card ↪o Fin n :=
    (w₁.weights.support.orderIsoOfFin rfl).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ w₁.weights.support))
  set φ₂ : Fin w₂.weights.support.card ↪o Fin n :=
    (w₂.weights.support.orderIsoOfFin rfl).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ w₂.weights.support))
  obtain ⟨w₁', hw₁map, hw₁wt, hd₁, hsl₁⟩ := isDistinguished_support_chainSimplexTimed hv hvS w₁
  obtain ⟨w₂', hw₂map, hw₂wt, hd₂, hsl₂⟩ := isDistinguished_support_chainSimplexTimed hv hvS w₂
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
  have hφeq (i : Fin w₁.weights.support.card) : φ₁ i = φ₂ (i.cast hcard) :=
    hv (congrFun (List.ofFn_injective hsl) i)
  have hwteq (i : Fin w₁.weights.support.card) :
      w₁.weights (φ₁ i) = w₂.weights (φ₂ (i.cast hcard)) := by
    rw [← hw₁wt i, ← hw₂wt (i.cast hcard)]
    exact congrFun (List.ofFn_injective hwt) i
  ext j
  by_cases hj₁ : j ∈ w₁.weights.support
  · obtain ⟨i, hi⟩ : ∃ i, φ₁ i = j :=
      ⟨(w₁.weights.support.orderIsoOfFin rfl).symm ⟨j, hj₁⟩,
        congrArg Subtype.val ((w₁.weights.support.orderIsoOfFin rfl).apply_symm_apply ⟨j, hj₁⟩)⟩
    rw [← hi, hwteq i, ← hφeq i]
  · have hj₂ : j ∉ w₂.weights.support := by
      intro hj₂
      obtain ⟨i₂, hi₂⟩ : ∃ i₂, φ₂ i₂ = j :=
        ⟨(w₂.weights.support.orderIsoOfFin rfl).symm ⟨j, hj₂⟩,
          congrArg Subtype.val ((w₂.weights.support.orderIsoOfFin rfl).apply_symm_apply ⟨j, hj₂⟩)⟩
      have hmem : φ₁ (i₂.cast hcard.symm) ∈ w₁.weights.support :=
        ((w₁.weights.support.orderIsoOfFin rfl) (i₂.cast hcard.symm)).2
      rw [hφeq, Fin.cast_cast, Fin.cast_eq_self, hi₂] at hmem
      exact hj₁ hmem
    rw [Finsupp.notMem_support_iff.mp hj₁, Finsupp.notMem_support_iff.mp hj₂]

end Injectivity

end TauCeti.PLPath

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

section DurationSimplex

/-- The zero-break Lakshmibai–Seshadri path running along a single minimal coset representative `τ`
of `W / W_λ` from time `0` to time `1`. When `τ = 1` this is `TauCeti.LSPath.straight`. -/
noncomputable def single
    (τ : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    LSPath P b lam where
  length := 0
  dir _ := τ
  time := ![0, 1]
  time_zero := rfl
  time_last := rfl
  strictMono_time := Fin.strictMono_iff_lt_succ.mpr fun j ↦ by
    fin_cases j
    simp
  dir_succ_ne j := j.elim0
  exists_isAChain j := j.elim0

/-- `LSPath.single τ` has zero internal breaks. -/
@[simp]
theorem length_single
    (τ : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}) :
    (single τ : LSPath P b lam).length = 0 :=
  (rfl)

/-- The sole segment direction of `LSPath.single τ` is `τ`. -/
@[simp]
theorem dir_single
    (τ : {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (j : Fin ((single τ : LSPath P b lam).length + 1)) :
    (single τ : LSPath P b lam).dir j = τ :=
  (rfl)

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

/-- The cumulative break times of `π.durationSimplex` recover `π.time`. -/
@[simp]
theorem breakTime_durationSimplex (π : LSPath P b lam) (k : Fin (π.length + 2)) :
    π.durationSimplex.breakTime k = π.time k := by
  have heq : π.durationSimplex =
      (Convexity.StdSimplex.equivBreakTime ℚ π.length).symm
        ⟨π.time, π.time_zero, π.time_last, π.strictMono_time.monotone⟩ := by
    ext j
    simp [duration_def]
  have happ := congrFun (congrArg Subtype.val
    ((Convexity.StdSimplex.equivBreakTime ℚ π.length).apply_symm_apply
      ⟨π.time, π.time_zero, π.time_last, π.strictMono_time.monotone⟩)) k
  rw [Convexity.StdSimplex.equivBreakTime_apply_coe] at happ
  rwa [heq]

/-- Evaluating `chainSimplexTimed` at the scalar pushforward of `π.durationSimplex` recovers
`π.timed`. -/
theorem chainSimplexTimed_durationSimplex (π : LSPath P b lam) (𝕜 : Type*) {V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) :
    PLPath.chainSimplexTimed (fun j ↦ f ((π.dir j).1 • lam))
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) = π.timed 𝕜 f := by
  simp [PLPath.chainSimplexTimed_def, timed_def]

/-- Evaluating `chainSimplexPath` at the scalar pushforward of `π.durationSimplex` recovers
`π.toPLPath`. -/
theorem chainSimplexPath_durationSimplex (π : LSPath P b lam) (𝕜 : Type*) {V : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (f : M →+ V) :
    PLPath.chainSimplexPath (fun j ↦ f ((π.dir j).1 • lam))
      (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) = π.toPLPath 𝕜 f := by
  rw [← PLPath.ofSegments_map_snd_chainSimplexTimed, chainSimplexTimed_durationSimplex,
    toPLPath_def]

end DurationSimplex

section BreakChainIntegrality

/-- A rational standard-simplex point `w` satisfies the **Lakshmibai–Seshadri break-chain
condition** along a direction sequence `dir` of shape `λ` if every weight is strictly positive (so
`w` lies in the open simplex) and each internal cumulative break time `w.breakTime (j + 1)` admits
an `a`-chain from `dir j` down to `dir (j + 1)` in `W / W_λ`. -/
def IsLSChainBreak {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) : Prop :=
  (∀ j, 0 < w.weights j) ∧
    ∀ j : Fin l, ∃ C : (weylCoxeterSystem P b).MinimalCosetRepChain (P.wallIndices b lam),
      C.head = dir j.castSucc ∧ C.last = dir j.succ ∧
        IsAChain (w.breakTime j.castSucc.succ) lam C

/-- On a `0`-simplex (`l = 0`), the LS break-chain condition holds automatically at the unique
point. -/
@[simp]
theorem isLSChainBreak_fin_one
    (dir : Fin 1 → {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (w : Convexity.StdSimplex ℚ (Fin 1)) : IsLSChainBreak dir w :=
  ⟨fun j ↦ by rw [w.weights_apply_eq_one j]; exact zero_lt_one, fun j ↦ j.elim0⟩

/-- The duration simplex of any LS path satisfies `IsLSChainBreak` along its direction sequence. -/
theorem isLSChainBreak_durationSimplex (π : LSPath P b lam) :
    IsLSChainBreak π.dir π.durationSimplex := by
  refine ⟨π.weights_durationSimplex_pos, fun j ↦ ?_⟩
  simpa only [breakTime_durationSimplex] using π.exists_isAChain j

/-- **Interval bond gcd criterion for `IsLSChainBreak`.** For a dominant shape `λ` and a decreasing
direction sequence in `W / W_λ`, a rational simplex point `w` satisfies `IsLSChainBreak` if and
only if all its weights are positive and the denominator of each internal cumulative break time
`w.breakTime (j + 1)` divides the interval bond gcd `d_λ(dir j, dir (j + 1))`. -/
theorem isLSChainBreak_iff_den_dvd_intervalBondGcd (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : ∀ j : Fin l, (weylCoxeterSystem P b).BruhatLE (dir j.succ).1 (dir j.castSucc).1)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) :
    IsLSChainBreak dir w ↔
      (∀ j, 0 < w.weights j) ∧
        ∀ j : Fin l, (w.breakTime j.castSucc.succ).den ∣
          intervalBondGcd b lam (dir j.castSucc).1 (dir j.succ).1 := by
  refine and_congr_right' (forall_congr' fun j ↦ ?_)
  simpa only [Subtype.ext_iff] using
    exists_isAChain_iff_den_dvd_intervalBondGcd hlam (dir j.castSucc).2 (dir j.succ).2 (hdir j)

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
  time := w.breakTime
  time_zero := w.breakTime_zero
  time_last := w.breakTime_last
  strictMono_time := w.strictMono_breakTime_iff.mpr hw.1
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

/-- The break-time sequence of `ofChainSimplex` is `w.breakTime`. -/
@[simp]
theorem time_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (k : Fin ((ofChainSimplex dir hne w hw).length + 2)) :
    (ofChainSimplex dir hne w hw).time k =
      w.breakTime (k.cast (congrArg (· + 2) (length_ofChainSimplex dir hne w hw))) :=
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
  exact w.breakTime_succ_sub_castSucc
    (j.cast (congrArg (· + 1) (length_ofChainSimplex dir hne w hw)))

/-- Realizing `ofChainSimplex` gives `chainSimplexPath` at the scalar pushforward of `w`. -/
theorem toPLPath_ofChainSimplex {l : ℕ}
    (dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w})
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc)
    (w : Convexity.StdSimplex ℚ (Fin (l + 1))) (hw : IsLSChainBreak dir w)
    (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) :
    (ofChainSimplex dir hne w hw).toPLPath 𝕜 f =
      PLPath.chainSimplexPath (fun j ↦ f ((dir j).1 • lam))
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
  refine Finite.of_injective (fun w : {w // IsLSChainBreak dir w} ↦ ofChainSimplex dir hne w.1 w.2)
    fun w₁ w₂ h ↦ Subtype.ext ?_
  have hd : List.ofFn (ofChainSimplex dir hne w₁.1 w₁.2).duration =
      List.ofFn (ofChainSimplex dir hne w₂.1 w₂.2).duration :=
    congrArg (fun π ↦ List.ofFn π.duration) h
  have hw (u : {w // IsLSChainBreak dir w}) :
       List.ofFn (ofChainSimplex dir hne u.1 u.2).duration = List.ofFn u.1.weights := by
    rw [List.ofFn_congr (congrArg (· + 1) (length_ofChainSimplex dir hne u.1 u.2))]
    simp
  rw [hw w₁, hw w₂] at hd
  ext j
  exact congrFun (List.ofFn_injective hd) j

/-- Even inside the rational `l`-simplex, the break-integral points form a strict subset whenever
`1 ≤ l` (and exhaust the `0`-simplex when `l = 0`). -/
theorem setOf_isLSChainBreak_ssubset_univ_iff (hlam : lam ∈ dominantChamber P b) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hne : ∀ j : Fin l, dir j.succ ≠ dir j.castSucc) :
    {w : Convexity.StdSimplex ℚ (Fin (l + 1)) | IsLSChainBreak dir w} ⊂ Set.univ ↔ 1 ≤ l := by
  rw [Set.ssubset_univ_iff]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · refine iff_of_true (fun huniv ↦ ?_) hl
    have : Nontrivial (Fin (l + 1)) := ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
    have : Infinite (Convexity.StdSimplex ℚ (Fin (l + 1))) := Convexity.StdSimplex.infinite
    exact Set.infinite_univ (huniv ▸ finite_setOf_isLSChainBreak hlam hne)

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
  have hsub : Subsingleton (Fin ((single (dir j)).length + 1)) := e.toEquiv.subsingleton
  refine ⟨single (dir j), e.toOrderEmbedding.trans c, by funext k; simp [c], ?_⟩
  rw [Subsingleton.elim ((single (dir j)).durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono)
    (Convexity.StdSimplex.single 0), Convexity.StdSimplex.map_single]
  rfl

/-- Every point of `lsChainSimplexSet` realizes a Lakshmibai–Seshadri path of shape `λ`. -/
theorem chainSimplexPath_mem_range_toPLPath_of_mem_lsChainSimplexSet {V : Type*}
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    {x : Convexity.StdSimplex 𝕜 (Fin (l + 1))} (hx : x ∈ lsChainSimplexSet 𝕜 dir) :
    PLPath.chainSimplexPath (fun j ↦ f ((dir j).1 • lam)) x ∈
      Set.range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) := by
  obtain ⟨π, φ, hdir, rfl⟩ := hx
  refine ⟨π, ?_⟩
  have hcomp : ((fun j ↦ f ((dir j).1 • lam)) ∘ φ) = fun i ↦ f ((π.dir i).1 • lam) := by
    funext i
    exact congrArg (fun τ ↦ f (τ.1 • lam)) (congrFun hdir i)
  have hmap : PLPath.chainSimplexPath (fun j ↦ f ((dir j).1 • lam))
      ((π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono).map φ) =
      PLPath.chainSimplexPath ((fun j ↦ f ((dir j).1 • lam)) ∘ φ)
        (π.durationSimplex.mapRange (Rat.castHom 𝕜) Rat.cast_mono) :=
    PLPath.chainSimplexPath_map_orderHom (fun j ↦ f ((dir j).1 • lam)) φ.toOrderHom _
  rw [hmap, hcomp, π.chainSimplexPath_durationSimplex 𝕜 f]

/-- **Characterization of LS paths inside a closed fixed-chain simplex.** For a dominant shape `λ`
whose realized orbit has no two distinct weights in the same ray, and an injective direction
sequence `dir` (such as any strictly decreasing Bruhat chain in `W / W_λ`), a point `x` of the
closed simplex `StdSimplex 𝕜 (Fin (l + 1))` presents an LS path of shape `λ` if and only if
`x ∈ lsChainSimplexSet 𝕜 dir`. -/
theorem chainSimplexPath_mem_range_toPLPath_iff {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {f : M →+ V} (hlam : lam ∈ dominantChamber P b)
    (hf : Set.InjOn f (Set.range fun w : P.weylGroup ↦ w • lam))
    (hS : (Set.range fun w : P.weylGroup ↦ f (w • lam)).Pairwise fun u v ↦ ¬ SameRay 𝕜 u v)
    {l : ℕ}
    {dir : Fin (l + 1) →
      {w // (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w}}
    (hdir : Function.Injective dir) (x : Convexity.StdSimplex 𝕜 (Fin (l + 1))) :
    PLPath.chainSimplexPath (fun j ↦ f ((dir j).1 • lam)) x ∈
        Set.range (fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ↔
      x ∈ lsChainSimplexSet 𝕜 dir := by
  have := P.flip_isReduced
  refine ⟨?_, chainSimplexPath_mem_range_toPLPath_of_mem_lsChainSimplexSet f⟩
  rintro ⟨π, hπ⟩
  let v : Fin (l + 1) → V := fun j ↦ f ((dir j).1 • lam)
  have hv : Function.Injective v := fun j₁ j₂ h ↦
    hdir (Subtype.ext (eq_of_isMinimalCosetRep_of_smul_eq hlam (dir j₁).2 (dir j₂).2
      (hf ⟨_, rfl⟩ ⟨_, rfl⟩ h)))
  set ψ : Fin x.weights.support.card ↪o Fin (l + 1) :=
    (x.weights.support.orderIsoOfFin rfl).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ x.weights.support))
  obtain ⟨x', hx'map, hx'wt, hdist, -⟩ :=
    PLPath.isDistinguished_support_chainSimplexTimed
      (S := Set.range fun w : P.weylGroup ↦ f (w • lam)) hv (fun j ↦ ⟨(dir j).1, rfl⟩) x
  have htimed : PLPath.chainSimplexTimed (v ∘ ψ) x' = π.timed 𝕜 f := by
    refine hdist.unique (π.isDistinguished_timed 𝕜 f hlam hf) hS ?_
    have hmap : PLPath.chainSimplexPath v (x'.map ψ) = PLPath.chainSimplexPath (v ∘ ψ) x' :=
      PLPath.chainSimplexPath_map_orderHom v ψ.toOrderHom x'
    rw [PLPath.ofSegments_map_snd_chainSimplexTimed, ← hmap, hx'map, ← toPLPath_def]
    exact hπ.symm
  have hcard : π.length + 1 = x.weights.support.card := by
    simpa [PLPath.chainSimplexTimed_def, timed_def] using (congrArg List.length htimed).symm
  let φ : Fin (π.length + 1) ↪o Fin (l + 1) := (Fin.castOrderIso hcard).toOrderEmbedding.trans ψ
  rw [PLPath.chainSimplexTimed_def, timed_def, List.ofFn_congr hcard.symm] at htimed
  have hentry (i : Fin (π.length + 1)) :
      (x.weights (φ i), x.weights (φ i) • f ((dir (φ i)).1 • lam)) =
        ((π.duration i : 𝕜), (π.duration i : 𝕜) • f ((π.dir i).1 • lam)) := by
    simpa [φ, ψ, hx'wt, v] using congrFun (List.ofFn_injective htimed) i
  refine ⟨π, φ, ?_, ?_⟩
  · funext i
    have hd : x.weights (φ i) = (π.duration i : 𝕜) := congrArg Prod.fst (hentry i)
    have hsnd := congrArg Prod.snd (hentry i)
    rw [hd] at hsnd
    have hne : (π.duration i : 𝕜) ≠ 0 := Rat.cast_ne_zero.mpr (π.duration_pos i).ne'
    exact Subtype.ext (eq_of_isMinimalCosetRep_of_smul_eq hlam (dir (φ i)).2 (π.dir i).2
      (hf ⟨_, rfl⟩ ⟨_, rfl⟩ (smul_right_injective V hne hsnd)))
  · rw [← hx'map, show ⇑φ = ⇑ψ ∘ ⇑(Fin.castOrderIso hcard) from rfl,
      Convexity.StdSimplex.map_comp]
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
    have : Infinite (Convexity.StdSimplex 𝕜 (Fin (l + 1))) := Convexity.StdSimplex.infinite
    exact Set.infinite_univ (huniv ▸ finite_lsChainSimplexSet hlam dir)

end ClosedChainSimplex

end TauCeti.LSPath
