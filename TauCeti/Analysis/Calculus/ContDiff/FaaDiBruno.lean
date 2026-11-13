/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Continuity, smoothness, and algebra of the Faà di Bruno composition

The `m`-th coefficient of `q.taylorComp p` is a finite sum, over the ordered partitions of `m`,
of continuous multilinear expressions in the coefficients of `q` and `p` of order at most `m`.
It depends only on `q 0, …, q m` and `p 1, …, p m` (`FormalMultilinearSeries.taylorComp_congr`),
depends continuously and smoothly on those finitely many coefficients (`Filter.Tendsto.taylorComp`,
`ContDiffOn.taylorComp`), distributes over products (`FormalMultilinearSeries.prod_taylorComp`),
admits `FormalMultilinearSeries.id` as a two-sided unit (`FormalMultilinearSeries.taylorComp_id`,
`FormalMultilinearSeries.id_taylorComp`), and is associative across arbitrary formal multilinear
series (`FormalMultilinearSeries.taylorComp_assoc`).

For `0 < m`, the single-block partition `OrderedFinpartition.indiscrete m` is the unique ordered
partition of length `1`, and every other partition has strictly smaller parts
(`OrderedFinpartition.partSize_lt_of_ne_indiscrete`). Consequently, when two inner series agree in
orders `1` through `m - 1`, all nonlinear partition terms cancel in the `m`-th composite
coefficient, leaving the linear outer coefficient composed with the top-order difference
(`FormalMultilinearSeries.taylorComp_sub_of_eq_lt`).

The same expansion bounds the norm of the `m`-th coefficient
(`FormalMultilinearSeries.norm_taylorComp_le`): if the coefficients of `p` of orders `1` through
`m` have norm at most `B`, it is at most `max 1 B ^ m` times the sum, over the ordered partitions
`c` of `m`, of `‖q c.length‖`. For a composite `g ∘ f` this bounds the `m`-th derivative by the
derivatives of `g` of order at most `m` (`ContDiffAt.norm_iteratedFDeriv_comp_le_sum`), keeping
track of each order separately, as needed for changes of variables in Sobolev spaces.
-/

public section

open Filter Topology
open scoped ContDiff

namespace OrderedFinpartition

/-- The single-block ordered partition of `Fin n` for `0 < n`. -/
def indiscrete (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint _ _ _ _ h := (h (Subsingleton.elim _ _)).elim
  cover x := ⟨0, x, rfl⟩

@[simp]
theorem indiscrete_length (n : ℕ) (hn : 0 < n) : (indiscrete n hn).length = 1 :=
  (rfl)

theorem indiscrete_partSize (n : ℕ) (hn : 0 < n) (i : Fin (indiscrete n hn).length) :
    (indiscrete n hn).partSize i = n :=
  (rfl)

/-- For `0 < n`, an ordered partition of `Fin n` has a single part if and only if it is
`OrderedFinpartition.indiscrete n hn`. -/
@[simp]
theorem length_eq_one_iff {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n) :
    c.length = 1 ↔ c = indiscrete n hn := by
  constructor
  · intro hl
    have hsum : ∑ i, c.partSize i = n := by simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
    rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
    dsimp at hl hsum
    subst l
    have hs0 : s 0 = n := by simpa using hsum
    obtain rfl : s = fun _ ↦ n := funext fun i ↦ by rw [Subsingleton.elim i 0, hs0]
    refine OrderedFinpartition.ext (y := indiscrete n hn) rfl (heq_of_eq rfl) (heq_of_eq ?_)
    funext i
    rw [Subsingleton.elim i 0]
    exact (hm 0).eq_id
  · rintro rfl
    rfl

/-- Every part of a partition other than the single-block partition has size strictly less than
`n`. -/
theorem partSize_lt_of_ne_indiscrete {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n)
    (hc : c ≠ indiscrete n hn) (i : Fin c.length) : c.partSize i < n := by
  refine lt_of_le_of_ne (c.partSize_le i) fun hi ↦ hc ((c.length_eq_one_iff hn).mp ?_)
  have hsum : ∑ j, c.partSize j = n := by simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
  rw [← Fintype.card_fin c.length]
  refine Fintype.card_eq_one_iff.mpr ⟨i, fun j ↦ by_contra fun hji ↦ ?_⟩
  have hle : c.partSize i + c.partSize j ≤ ∑ k, c.partSize k :=
    Finset.add_le_sum (fun k _ ↦ Nat.zero_le _) (Finset.mem_univ i) (Finset.mem_univ j)
      (Ne.symm hji)
  have hj : 0 < c.partSize j := c.partSize_pos j
  omega

end OrderedFinpartition

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The `m`-th coefficient of the Taylor composition `q.taylorComp p` is continuous in the
coefficients of `q` of order at most `m` and of `p` of orders `1` through `m` (the constant
coefficient of `p` does not enter). -/
theorem Filter.Tendsto.taylorComp {α : Type*} {l : Filter α}
    {q : α → FormalMultilinearSeries 𝕜 F G} {p : α → FormalMultilinearSeries 𝕜 E F}
    {q₀ : FormalMultilinearSeries 𝕜 F G} {p₀ : FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, Tendsto (fun a ↦ q a k) l (𝓝 (q₀ k)))
    (hp : ∀ k, 1 ≤ k → k ≤ m → Tendsto (fun a ↦ p a k) l (𝓝 (p₀ k))) :
    Tendsto (fun a ↦ (q a).taylorComp (p a) m) l (𝓝 (q₀.taylorComp p₀ m)) := by
  refine tendsto_finsetSum _ fun c _ ↦ ?_
  have hB := ((c.compAlongOrderedFinpartitionL 𝕜 E F G).continuous.tendsto _).comp
    (hq c.length c.length_le)
  have hP : Tendsto (fun a i ↦ p a (c.partSize i)) l (𝓝 fun i ↦ p₀ (c.partSize i)) :=
    tendsto_pi_nhds.2 fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)
  exact (continuous_eval.tendsto _).comp (hB.prodMk_nhds hP)

/-- The `m`-th coefficient of `x ↦ (q x).taylorComp (p x)` is `C^n` on `s` whenever the
coefficients `x ↦ q x k` (`k ≤ m`) and `x ↦ p x k` (`1 ≤ k ≤ m`) are `C^n` on `s`. -/
theorem ContDiffOn.taylorComp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {n : ℕ∞ω} {s : Set M}
    {q : M → FormalMultilinearSeries 𝕜 F G} {p : M → FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, ContDiffOn 𝕜 n (fun x ↦ q x k) s)
    (hp : ∀ k, 1 ≤ k → k ≤ m → ContDiffOn 𝕜 n (fun x ↦ p x k) s) :
    ContDiffOn 𝕜 n (fun x ↦ (q x).taylorComp (p x) m) s := by
  refine ContDiffOn.sum fun c _ ↦ ?_
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  exact B.analyticOnNhd_uncurry_of_multilinear.contDiff.comp_contDiffOn
    ((hq c.length c.length_le).prodMk
      (contDiffOn_pi.mpr fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)))

/-- Pointwise version of `ContDiffOn.taylorComp`. -/
theorem ContDiffAt.taylorComp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {n : ℕ∞ω} {x : M}
    {q : M → FormalMultilinearSeries 𝕜 F G} {p : M → FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, ContDiffAt 𝕜 n (fun y ↦ q y k) x)
    (hp : ∀ k, 1 ≤ k → k ≤ m → ContDiffAt 𝕜 n (fun y ↦ p y k) x) :
    ContDiffAt 𝕜 n (fun y ↦ (q y).taylorComp (p y) m) x := by
  refine ContDiffAt.sum fun c _ ↦ ?_
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  exact B.analyticOnNhd_uncurry_of_multilinear.contDiff.contDiffAt.comp x
    ((hq c.length c.length_le).prodMk
      (contDiffAt_pi.mpr fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)))

namespace FormalMultilinearSeries

/-- The `m`-th coefficient of `q.taylorComp p` depends only on `q 0, …, q m` and `p 1, …, p m`. -/
theorem taylorComp_congr {q₁ q₂ : FormalMultilinearSeries 𝕜 F G}
    {p₁ p₂ : FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, q₁ k = q₂ k) (hp : ∀ k, 1 ≤ k → k ≤ m → p₁ k = p₂ k) :
    q₁.taylorComp p₁ m = q₂.taylorComp p₂ m := by
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  rw [hq c.length c.length_le]
  congr 1
  funext i
  exact hp _ (c.partSize_pos i) (c.partSize_le i)

@[simp]
theorem taylorComp_zero_apply (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 → E) :
    q.taylorComp p 0 v = q 0 0 := by
  rw [FormalMultilinearSeries.taylorComp, Fintype.sum_unique, OrderedFinpartition.default_eq]
  exact congrArg (q 0) (Subsingleton.elim _ _)

theorem taylorComp_zero (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    q.taylorComp p 0 = (continuousMultilinearCurryFin0 𝕜 E G).symm (q 0 0) := by
  ext v
  simp

@[simp]
theorem compAlongOrderedFinpartition_indiscrete (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hm : 0 < m) :
    q.compAlongOrderedFinpartition p (OrderedFinpartition.indiscrete m hm) =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p m) := by
  ext v
  simp only [OrderedFinpartition.indiscrete, compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    continuousMultilinearCurryFin1_apply]
  congr 1

@[simp]
theorem taylorComp_one (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    q.taylorComp p 1 =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p 1) := by
  have hu : (default : OrderedFinpartition 1) = OrderedFinpartition.indiscrete 1 zero_lt_one :=
    Subsingleton.elim _ _
  rw [FormalMultilinearSeries.taylorComp, Fintype.sum_unique, hu,
    compAlongOrderedFinpartition_indiscrete]

theorem taylorComp_one_apply (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 1 → E) :
    q.taylorComp p 1 v = q 1 ![p 1 v] := by
  simp

/-- Faà di Bruno composition distributes over Cartesian products of outer formal multilinear
series. -/
@[simp]
theorem prod_taylorComp (q₁ : FormalMultilinearSeries 𝕜 F G)
    (q₂ : FormalMultilinearSeries 𝕜 F H) (p : FormalMultilinearSeries 𝕜 E F) :
    (q₁.prod q₂).taylorComp p = (q₁.taylorComp p).prod (q₂.taylorComp p) := by
  funext m
  refine ContinuousMultilinearMap.ext fun v ↦ Prod.ext ?_ ?_ <;>
    simp [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.prod,
      compAlongOrderedFinpartition_apply, sum_apply, Prod.fst_sum, Prod.snd_sum]

/-- Composing a formal multilinear series on the right with `FormalMultilinearSeries.id` leaves it
unchanged. -/
@[simp]
theorem taylorComp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorComp (FormalMultilinearSeries.id 𝕜 E x) = p := by
  classical
  funext m
  rw [FormalMultilinearSeries.taylorComp, Finset.sum_eq_single (OrderedFinpartition.atomic m)]
  · ext v
    simp only [compAlongOrderedFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply, OrderedFinpartition.atomic_emb]
    rfl
  · intro c _ hc
    have hex : ∃ i : Fin c.length, 1 < c.partSize i := by
      by_contra! hle
      have hs (i : Fin c.length) : c.partSize i = 1 :=
        le_antisymm (hle i) (c.partSize_pos i)
      have hsum : ∑ i, c.partSize i = m := by
        simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
      have hl : c.length = m := by simpa [hs] using hsum
      rcases c with ⟨l, s, hp, e, hm, ho, hd, hcov⟩
      dsimp at hl hs
      subst l
      obtain rfl : s = fun _ ↦ 1 := funext hs
      have he : (fun i ↦ e i 0) = _root_.id := ho.eq_id
      refine hc (OrderedFinpartition.ext (y := OrderedFinpartition.atomic m)
        rfl (heq_of_eq rfl) (heq_of_eq ?_))
      funext i j
      simpa only [Subsingleton.elim j 0, id_eq, OrderedFinpartition.atomic_emb] using congrFun he i
    obtain ⟨i, hi⟩ := hex
    ext v
    rw [compAlongOrderedFinpartition_apply, _root_.zero_apply]
    refine ContinuousMultilinearMap.map_coord_zero _ i ?_
    simp [OrderedFinpartition.applyOrderedFinpartition_apply, id_apply_of_one_lt _ _ _ hi]
  · simp

/-- Composing `FormalMultilinearSeries.id` on the left with a formal multilinear series `p` gives
`p` (with constant term matching `p 0 ![]`). -/
@[simp]
theorem id_taylorComp (p : FormalMultilinearSeries 𝕜 E F) :
    (FormalMultilinearSeries.id 𝕜 F (p 0 ![])).taylorComp p = p := by
  classical
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · ext v
    simp [Subsingleton.elim v 0]
  · rw [FormalMultilinearSeries.taylorComp,
      Finset.sum_eq_single (OrderedFinpartition.indiscrete m hm)]
    · rw [compAlongOrderedFinpartition_indiscrete]
      ext v
      simp
    · intro c _ hc
      have hlen_pos : 0 < c.length := by
        by_contra! h0
        have hsum : ∑ i, c.partSize i = m := by
          simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))
        obtain hlen0 : c.length = 0 := Nat.eq_zero_of_le_zero h0
        rw [Finset.sum_eq_zero fun i _ ↦ (Fin.elim0 (hlen0 ▸ i))] at hsum
        omega
      have hlen_ne : c.length ≠ 1 := mt (c.length_eq_one_iff hm).mp hc
      have hgt : 1 < c.length := by omega
      ext v
      simp [compAlongOrderedFinpartition_apply, id_apply_of_one_lt _ _ _ hgt]
    · simp

/-- When two inner formal multilinear series agree in all positive orders strictly below `m`,
all nonlinear partition terms in `q.taylorComp p₁ m - q.taylorComp p₂ m` cancel, leaving only the
single-block term. -/
theorem taylorComp_sub_of_eq_lt (q : FormalMultilinearSeries 𝕜 F G)
    {p₁ p₂ : FormalMultilinearSeries 𝕜 E F} {m : ℕ} (hm : 0 < m)
    (hp : ∀ k, 1 ≤ k → k < m → p₁ k = p₂ k) :
    q.taylorComp p₁ m - q.taylorComp p₂ m =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p₁ m - p₂ m) := by
  classical
  let c₀ := OrderedFinpartition.indiscrete m hm
  rw [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.taylorComp,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)]
  have hrest : ∑ c ∈ Finset.univ.erase c₀, q.compAlongOrderedFinpartition p₁ c =
      ∑ c ∈ Finset.univ.erase c₀, q.compAlongOrderedFinpartition p₂ c := by
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    have hne : c ≠ c₀ := (Finset.mem_erase.mp hc).1
    unfold FormalMultilinearSeries.compAlongOrderedFinpartition
    congr 1
    funext i
    exact hp _ (c.partSize_pos i) (c.partSize_lt_of_ne_indiscrete hm hne i)
  rw [hrest, add_sub_add_right_eq_sub, compAlongOrderedFinpartition_indiscrete,
    compAlongOrderedFinpartition_indiscrete]
  ext v
  exact (map_sub (continuousMultilinearCurryFin1 𝕜 F G (q 1)) (p₁ m v) (p₂ m v)).symm

private noncomputable def curryLeftSeries (p : FormalMultilinearSeries 𝕜 E F) (e : E) :
    FormalMultilinearSeries 𝕜 E F :=
  fun k ↦ (p (k + 1)).curryLeft e

private noncomputable def taylorCompDeriv (q : FormalMultilinearSeries 𝕜 F G)
    (p d : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E G :=
  fun m ↦ ∑ c : OrderedFinpartition m, ∑ i : Fin c.length,
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun j ↦ p (c.partSize j)) i) (d (c.partSize i))

private theorem hasFDerivAt_taylorComp_right (q : FormalMultilinearSeries 𝕜 F G)
    {p : 𝕜 → FormalMultilinearSeries 𝕜 E F} {dp : FormalMultilinearSeries 𝕜 E F} (m : ℕ)
    (hp : ∀ k, HasFDerivAt (fun t ↦ p t k) ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)) 0) :
    HasFDerivAt (fun t ↦ q.taylorComp (p t) m)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv q (p 0) dp m)) 0 := by
  classical
  have hsum : HasFDerivAt (fun t ↦ ∑ c : OrderedFinpartition m,
      c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length) (fun i ↦ p t (c.partSize i)))
      (∑ c : OrderedFinpartition m,
        (((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear
            (fun i ↦ p 0 (c.partSize i))) ∘L (0 : 𝕜 →L[𝕜] F [×c.length]→L[𝕜] G) +
        ∑ i : Fin c.length,
          (((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
            (fun j ↦ p 0 (c.partSize j)) i) ∘L
            ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp (c.partSize i)))))) 0 :=
    HasFDerivAt.fun_sum fun (c : OrderedFinpartition m) _ ↦
      HasFDerivAt.linear_multilinear_comp (hasFDerivAt_const (q c.length) (0 : 𝕜))
        (fun i ↦ hp (c.partSize i)) (c.compAlongOrderedFinpartitionL 𝕜 E F G)
  refine (HasFDerivAt.congr_of_eventuallyEq hsum
    (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_fderiv ?_
  ext v
  simp [taylorCompDeriv, sum_apply, Finset.smul_sum]

private theorem hasFDerivAt_taylorComp_left
    {q : 𝕜 → FormalMultilinearSeries 𝕜 F G} {dq : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) (m : ℕ)
    (hq : ∀ k, HasFDerivAt (fun t ↦ q t k) ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq k)) 0) :
    HasFDerivAt (fun t ↦ (q t).taylorComp p m)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq.taylorComp p m)) 0 := by
  classical
  have hsum : HasFDerivAt (fun t ↦ ∑ c : OrderedFinpartition m,
      c.compAlongOrderedFinpartitionL 𝕜 E F G (q t c.length) (fun i ↦ p (c.partSize i)))
      (∑ c : OrderedFinpartition m,
        (((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear
            (fun i ↦ p (c.partSize i))) ∘L
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq c.length)))) 0 :=
    HasFDerivAt.fun_sum fun (c : OrderedFinpartition m) _ ↦ by
      let L := (c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear
        (fun i ↦ p (c.partSize i))
      exact L.hasFDerivAt.comp (0 : 𝕜) (hq c.length)
  refine (HasFDerivAt.congr_of_eventuallyEq hsum
    (Filter.Eventually.of_forall fun _ ↦ rfl)).congr_fderiv ?_
  ext v
  simp [FormalMultilinearSeries.taylorComp, sum_apply, Finset.smul_sum]

private theorem curryLeftSeries_taylorComp (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (e : E) (m : ℕ) :
    curryLeftSeries (q.taylorComp p) e m =
      (curryLeftSeries q (continuousMultilinearCurryFin1 𝕜 E F (p 1) e)).taylorComp p m +
        taylorCompDeriv q p (curryLeftSeries p e) m := by
  classical
  ext v
  change (∑ c : OrderedFinpartition (m + 1), q.compAlongOrderedFinpartition p c) (Fin.cons e v) = _
  rw [← (OrderedFinpartition.extendEquiv m).sum_comp, Fintype.sum_sigma, sum_apply]
  simp only [Fintype.sum_option, OrderedFinpartition.extendEquiv_apply, _root_.add_apply,
    sum_apply, FormalMultilinearSeries.taylorComp, taylorCompDeriv, Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ ↦ ?_)
    (Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_)
  · simp only [OrderedFinpartition.extend, OrderedFinpartition.extendLeft,
      compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
      curryLeftSeries, ContinuousMultilinearMap.curryLeft_apply,
      continuousMultilinearCurryFin1_apply]
    congr 1
    ext j
    refine Fin.cases ?_ (fun _ ↦ rfl) j
    simp only [Fin.cons_zero]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    have ha0 : a = 0 := by omega
    subst ha0
    rfl
  · simp only [OrderedFinpartition.extend, OrderedFinpartition.extendMiddle,
      compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply,
      OrderedFinpartition.compAlongOrderedFinpartitionL_apply,
      OrderedFinpartition.compAlongOrderFinpartition_apply, curryLeftSeries]
    congr 1
    ext j
    rcases eq_or_ne j i with rfl | hij
    · simp only [↓reduceDIte, Function.update_self, ContinuousMultilinearMap.curryLeft_apply]
      apply FormalMultilinearSeries.congr _ (by simp)
      intro a ha h'a
      cases a with
      | zero => simp
      | succ a => simp [Fin.cons]
    · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, Function.update_of_ne]
      apply FormalMultilinearSeries.congr _ (by simp [hij])
      simp

/-- **Associativity of Faà di Bruno composition.** Formal Taylor composition of formal multilinear
series is associative, with no symmetry or convergence hypotheses. -/
theorem taylorComp_assoc (r : FormalMultilinearSeries 𝕜 G H)
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    (r.taylorComp q).taylorComp p = r.taylorComp (q.taylorComp p) := by
  funext m
  induction m generalizing r q p with
  | zero =>
    ext v
    simp
  | succ m ih =>
    apply (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (m + 1) ↦ E) H).injective
    ext e : 1
    change curryLeftSeries ((r.taylorComp q).taylorComp p) e m =
      curryLeftSeries (r.taylorComp (q.taylorComp p)) e m
    -- Differentiating the degree-`m` induction hypothesis along lines in `p` and `q` gives the
    -- chain rules for `taylorCompDeriv`.
    have hlin_p (dp : FormalMultilinearSeries 𝕜 E F) :
        taylorCompDeriv (r.taylorComp q) p dp m =
          taylorCompDeriv r (q.taylorComp p) (taylorCompDeriv q p dp) m := by
      let P : 𝕜 → FormalMultilinearSeries 𝕜 E F := fun t k ↦ p k + t • dp k
      have hP0 : P 0 = p := by funext k; simp [P]
      have hP (k : ℕ) : HasFDerivAt (fun t ↦ P t k)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)) 0 :=
        (((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)).hasFDerivAt (x := 0)).const_add (p k)
      have hQ (k : ℕ) : HasFDerivAt (fun t ↦ q.taylorComp (P t) k)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv q p dp k)) 0 := by
        simpa [hP0] using hasFDerivAt_taylorComp_right q k hP
      have hL : HasFDerivAt (fun t ↦ ((r.taylorComp q).taylorComp (P t)) m)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv (r.taylorComp q) p dp m)) 0 := by
        simpa [hP0] using hasFDerivAt_taylorComp_right (r.taylorComp q) m hP
      have hR : HasFDerivAt (fun t ↦ (r.taylorComp (q.taylorComp (P t))) m)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight
            (taylorCompDeriv r (q.taylorComp p) (taylorCompDeriv q p dp) m)) 0 := by
        simpa [hP0] using hasFDerivAt_taylorComp_right r m hQ
      have heq : (fun t ↦ ((r.taylorComp q).taylorComp (P t)) m) =
          fun t ↦ (r.taylorComp (q.taylorComp (P t))) m := funext fun t ↦ ih r q (P t)
      rw [heq] at hL
      simpa using congrArg (fun L : 𝕜 →L[𝕜] (E [×m]→L[𝕜] H) ↦ L 1) (hL.unique hR)
    have hlin_q (dq : FormalMultilinearSeries 𝕜 F G) :
        (taylorCompDeriv r q dq).taylorComp p m =
          taylorCompDeriv r (q.taylorComp p) (dq.taylorComp p) m := by
      let Q : 𝕜 → FormalMultilinearSeries 𝕜 F G := fun t k ↦ q k + t • dq k
      have hQ0 : Q 0 = q := by funext k; simp [Q]
      have hQ (k : ℕ) : HasFDerivAt (fun t ↦ Q t k)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq k)) 0 :=
        (((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq k)).hasFDerivAt (x := 0)).const_add (q k)
      have hRQ (k : ℕ) : HasFDerivAt (fun t ↦ r.taylorComp (Q t) k)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv r q dq k)) 0 := by
        simpa [hQ0] using hasFDerivAt_taylorComp_right r k hQ
      have hQP (k : ℕ) : HasFDerivAt (fun t ↦ (Q t).taylorComp p k)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq.taylorComp p k)) 0 :=
        hasFDerivAt_taylorComp_left p k hQ
      have hL : HasFDerivAt (fun t ↦ ((r.taylorComp (Q t)).taylorComp p) m)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight ((taylorCompDeriv r q dq).taylorComp p m)) 0 :=
        hasFDerivAt_taylorComp_left p m hRQ
      have hR : HasFDerivAt (fun t ↦ (r.taylorComp ((Q t).taylorComp p)) m)
          ((ContinuousLinearMap.id 𝕜 𝕜).smulRight
            (taylorCompDeriv r (q.taylorComp p) (dq.taylorComp p) m)) 0 := by
        simpa [hQ0] using hasFDerivAt_taylorComp_right r m hQP
      have heq : (fun t ↦ ((r.taylorComp (Q t)).taylorComp p) m) =
          fun t ↦ (r.taylorComp ((Q t).taylorComp p)) m := funext fun t ↦ ih r (Q t) p
      rw [heq] at hL
      simpa using congrArg (fun L : 𝕜 →L[𝕜] (E [×m]→L[𝕜] H) ↦ L 1) (hL.unique hR)
    let pe : F := continuousMultilinearCurryFin1 𝕜 E F (p 1) e
    let qpe : G := continuousMultilinearCurryFin1 𝕜 F G (q 1) pe
    have hq_shift : ((curryLeftSeries (r.taylorComp q) pe).taylorComp p) m =
        (((curryLeftSeries r qpe).taylorComp q).taylorComp p) m +
          ((taylorCompDeriv r q (curryLeftSeries q pe)).taylorComp p) m := by
      ext u
      simp only [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply,
        curryLeftSeries_taylorComp r q pe, sum_apply, _root_.add_apply, Finset.sum_add_distrib]
      rfl
    have hp_shift : taylorCompDeriv r (q.taylorComp p) (curryLeftSeries (q.taylorComp p) e) m =
        taylorCompDeriv r (q.taylorComp p) ((curryLeftSeries q pe).taylorComp p) m +
          taylorCompDeriv r (q.taylorComp p) (taylorCompDeriv q p (curryLeftSeries p e)) m := by
      ext u
      simp only [curryLeftSeries_taylorComp q p e, taylorCompDeriv, sum_apply, _root_.add_apply,
        map_add, Finset.sum_add_distrib]
      rfl
    have hp1 : continuousMultilinearCurryFin1 𝕜 E G (q.taylorComp p 1) e = qpe := by
      simp [qpe, pe]
    calc curryLeftSeries ((r.taylorComp q).taylorComp p) e m
      _ = (curryLeftSeries (r.taylorComp q) pe).taylorComp p m +
            taylorCompDeriv (r.taylorComp q) p (curryLeftSeries p e) m :=
          curryLeftSeries_taylorComp (r.taylorComp q) p e m
      _ = ((curryLeftSeries r qpe).taylorComp q).taylorComp p m +
            ((taylorCompDeriv r q (curryLeftSeries q pe)).taylorComp p m +
              taylorCompDeriv (r.taylorComp q) p (curryLeftSeries p e) m) := by
          rw [hq_shift, add_assoc]
      _ = (curryLeftSeries r qpe).taylorComp (q.taylorComp p) m +
            taylorCompDeriv r (q.taylorComp p) (curryLeftSeries (q.taylorComp p) e) m := by
          rw [ih (curryLeftSeries r qpe) q p, hlin_q, hlin_p, ← hp_shift]
      _ = curryLeftSeries (r.taylorComp (q.taylorComp p)) e m := by
          rw [← hp1, ← curryLeftSeries_taylorComp r (q.taylorComp p) e m]

/-- **A norm bound for the Faà di Bruno composition.** If the coefficients of `p` of orders `1`
through `m` have norm at most `B`, then the `m`-th coefficient of `q.taylorComp p` has norm at
most `max 1 B ^ m` times the sum, over the ordered partitions `c` of `m`, of `‖q c.length‖`. -/
theorem norm_taylorComp_le (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} {B : ℝ}
    (hp : ∀ k, 1 ≤ k → k ≤ m → ‖p k‖ ≤ B) :
    ‖q.taylorComp p m‖ ≤ max 1 B ^ m * ∑ c : OrderedFinpartition m, ‖q c.length‖ := by
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ ↦ ?_)
  refine (c.norm_compAlongOrderedFinpartition_le _ _).trans ?_
  rw [mul_comm (max 1 B ^ m)]
  gcongr
  calc ∏ i, ‖p (c.partSize i)‖ ≤ ∏ _i : Fin c.length, max 1 B := by
        gcongr with i
        exact (hp _ (c.partSize_pos i) (c.partSize_le i)).trans (le_max_right _ _)
    _ = max 1 B ^ c.length := by simp
    _ ≤ max 1 B ^ m := pow_le_pow_right₀ (le_max_left _ _) c.length_le

end FormalMultilinearSeries

/-- **A norm bound for the derivatives of a composite.** If `g` is `Cᵐ` at `f x`, `f` is `Cᵐ` at
`x`, and the derivatives of `f` at `x` of orders `1` through `m` have norm at most `B`, then the
`m`-th derivative of `g ∘ f` at `x` has norm at most `max 1 B ^ m` times the sum, over the ordered
partitions `c` of `m`, of the norms of the derivatives of `g` at `f x` of order `c.length ≤ m`. -/
theorem ContDiffAt.norm_iteratedFDeriv_comp_le_sum {g : F → G} {f : E → F} {x : E} {m : ℕ}
    (hg : ContDiffAt 𝕜 m g (f x)) (hf : ContDiffAt 𝕜 m f x) {B : ℝ}
    (hB : ∀ k, 1 ≤ k → k ≤ m → ‖iteratedFDeriv 𝕜 k f x‖ ≤ B) :
    ‖iteratedFDeriv 𝕜 m (g ∘ f) x‖ ≤
      max 1 B ^ m * ∑ c : OrderedFinpartition m, ‖iteratedFDeriv 𝕜 c.length g (f x)‖ := by
  rw [iteratedFDeriv_comp hg hf le_rfl]
  exact FormalMultilinearSeries.norm_taylorComp_le _ _ hB
