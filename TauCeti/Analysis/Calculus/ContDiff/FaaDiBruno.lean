/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Continuity, smoothness, and algebra of the Faà di Bruno composition

The `m`-th coefficient of `q.taylorComp p` is a finite sum, over the ordered partitions of `m`,
of continuous multilinear expressions in the coefficients of `q` and `p` of order at most `m`.
It depends only on `q 0, …, q m` and `p 1, …, p m` (`FormalMultilinearSeries.taylorComp_congr`),
depends continuously and smoothly on those finitely many coefficients (`Filter.Tendsto.taylorComp`,
`ContDiffOn.taylorComp`), distributes over products (`FormalMultilinearSeries.prod_taylorComp`),
admits `FormalMultilinearSeries.id` as a two-sided unit (`FormalMultilinearSeries.taylorComp_id`,
`FormalMultilinearSeries.id_taylorComp`), postcomposes along the formal Taylor series of continuous
linear maps (`FormalMultilinearSeries.ftaylorSeries_clm_taylorComp`), and is associative across
arbitrary formal multilinear series (`FormalMultilinearSeries.taylorComp_assoc`).

For `0 < m`, the single-block partition `OrderedFinpartition.single m` is the unique ordered
partition of length `1`, and every other partition has strictly smaller parts
(`OrderedFinpartition.partSize_lt_of_ne_single`) and length at least `2`
(`OrderedFinpartition.one_lt_length_of_ne_single`). Consequently, an outer series vanishing in
orders `2` and above reduces `q.taylorComp p m` to its linear term
(`FormalMultilinearSeries.taylorComp_of_eq_zero`), and when two inner series agree in orders `1`
through `m - 1`, all nonlinear partition terms cancel in the `m`-th composite coefficient
(`FormalMultilinearSeries.taylorComp_sub_of_eq_lt`). Dually, using the singleton partition
`OrderedFinpartition.atomic m` (`OrderedFinpartition.length_lt_of_ne_atomic`), when two outer
series agree strictly below order `m`, their composite difference reduces to the atomic term
(`FormalMultilinearSeries.sub_taylorComp_of_eq_lt`).

The inductive step in `FormalMultilinearSeries.taylorComp_assoc` splits ordered partitions of
`m + 1` via `OrderedFinpartition.extendEquiv` and differentiates along lines in formal series
space; the partition-extension term matching in `curryLeftSeries_taylorComp` is adapted from
`faaDiBruno_aux1`, `faaDiBruno_aux2`, and `HasFTaylorSeriesUpToOn.comp` in
`Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` (Sébastien Gouëzel).

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

/-- The sizes of the parts of an ordered partition add up to the size of the ground set. -/
@[simp]
theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) : ∑ i, c.partSize i = n := by
  simpa using c.sum_sigma_eq_sum (fun _ ↦ (1 : ℕ))

/-- A partition has as many parts as elements exactly when it is the singleton partition. -/
@[simp]
theorem length_eq_iff {n : ℕ} (c : OrderedFinpartition n) :
    c.length = n ↔ c = atomic n := by
  constructor
  · intro h
    have hs (i : Fin c.length) : c.partSize i = 1 := by
      have he : (∑ _ : Fin c.length, (1 : ℕ)) = ∑ j, c.partSize j := by
        simp [h]
      exact ((Finset.sum_eq_sum_iff_of_le (fun j _ ↦ c.partSize_pos j)).mp he i
        (Finset.mem_univ i)).symm
    rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
    dsimp at h hs
    subst l
    obtain rfl : s = fun _ ↦ 1 := funext hs
    have he : (fun i ↦ e i 0) = id := ho.eq_id
    refine OrderedFinpartition.ext (y := atomic n) rfl (heq_of_eq rfl) (heq_of_eq ?_)
    funext i j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj, id_eq, atomic_emb] using congrFun he i
  · rintro rfl
    rfl

/-- A partition other than the singleton partition has strictly fewer parts than elements. -/
theorem length_lt_of_ne_atomic {n : ℕ} (c : OrderedFinpartition n) (hc : c ≠ atomic n) :
    c.length < n :=
  lt_of_le_of_ne c.length_le fun h ↦ hc (c.length_eq_iff.mp h)

/-- The single-block ordered partition of `Fin n` for `0 < n`. -/
def single (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint _ _ _ _ h := (h (Subsingleton.elim _ _)).elim
  cover x := ⟨0, x, rfl⟩

@[simp]
theorem single_length (n : ℕ) (hn : 0 < n) : (single n hn).length = 1 :=
  (rfl)

@[simp]
theorem single_partSize (n : ℕ) (hn : 0 < n) (i : Fin (single n hn).length) :
    (single n hn).partSize i = n :=
  (rfl)

/-- For `0 < n`, an ordered partition of `Fin n` equals `OrderedFinpartition.single n hn` if and
only if it has a single part. -/
theorem eq_single_iff_length {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n} :
    c = single n hn ↔ c.length = 1 := by
  constructor
  · rintro rfl
    rfl
  · intro hl
    have hsum : ∑ i, c.partSize i = n := c.sum_partSize
    rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
    dsimp at hl hsum
    subst l
    have hs0 : s 0 = n := by simpa using hsum
    obtain rfl : s = fun _ ↦ n := funext fun i ↦ by rw [Subsingleton.elim i 0, hs0]
    refine OrderedFinpartition.ext (y := single n hn) rfl (heq_of_eq rfl) (heq_of_eq ?_)
    funext i
    rw [Subsingleton.elim i 0]
    exact (hm 0).eq_id

/-- Every partition of a positive `n` other than `OrderedFinpartition.single n hn` has at least two
parts. -/
theorem one_lt_length_of_ne_single {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n}
    (hc : c ≠ single n hn) : 1 < c.length := by
  have hpos : 0 < c.length := c.length_pos hn
  have hne : c.length ≠ 1 := mt (c.eq_single_iff_length hn).mpr hc
  omega

/-- Every part of a partition other than `OrderedFinpartition.single n hn` has size strictly less
than `n`. -/
theorem partSize_lt_of_ne_single {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n}
    (hc : c ≠ single n hn) (i : Fin c.length) : c.partSize i < n := by
  refine lt_of_le_of_ne (c.partSize_le i) fun hi ↦ hc ((c.eq_single_iff_length hn).mpr ?_)
  have hsum : ∑ j, c.partSize j = n := c.sum_partSize
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

@[simp]
theorem prod_apply (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G)
    (n : ℕ) : p.prod q n = (p n).prod (q n) :=
  (rfl)

/-- Unfold `ftaylorSeries` at a given order `n` to `iteratedFDeriv`. -/
theorem ftaylorSeries_apply (f : E → F) (x : E) (n : ℕ) :
    ftaylorSeries 𝕜 f x n = iteratedFDeriv 𝕜 n f x :=
  (rfl)

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

/-- The singleton partition term of Taylor composition precomposes each variable with the linear
coefficient of the inner series. -/
@[simp]
theorem compAlongOrderedFinpartition_atomic (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (m : ℕ) :
    q.compAlongOrderedFinpartition p (OrderedFinpartition.atomic m) =
      (q m).compContinuousLinearMap (fun _ ↦ continuousMultilinearCurryFin1 𝕜 E F (p 1)) := by
  ext v
  simp only [OrderedFinpartition.atomic, compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, continuousMultilinearCurryFin1_apply]
  exact congrArg (q m) (funext fun i ↦ congrArg (p 1) (funext fun j ↦ by
    rw [Subsingleton.elim j 0]; simp))

/-- The single-block partition term of Taylor composition postcomposes the `m`-th inner
coefficient with the linear outer coefficient. -/
@[simp]
theorem compAlongOrderedFinpartition_single (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hm : 0 < m) :
    q.compAlongOrderedFinpartition p (OrderedFinpartition.single m hm) =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p m) := by
  ext v
  simp only [OrderedFinpartition.single, compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    continuousMultilinearCurryFin1_apply, Function.comp_id]
  exact congrArg (q 1) (funext fun i ↦ by rw [Subsingleton.elim i 0]; simp)

@[simp]
theorem taylorComp_one (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    q.taylorComp p 1 =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p 1) := by
  have hu : (default : OrderedFinpartition 1) = OrderedFinpartition.single 1 zero_lt_one :=
    Subsingleton.elim _ _
  rw [FormalMultilinearSeries.taylorComp, Fintype.sum_unique, hu,
    compAlongOrderedFinpartition_single]

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
    simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply, sum_apply,
      Prod.fst_sum, Prod.snd_sum]

/-- If an outer formal multilinear series vanishes in all orders `k ≥ 2`, then for `0 < m` only the
single-block partition contributes to `q.taylorComp p m`. -/
theorem taylorComp_of_eq_zero {q : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hm : 0 < m)
    (hq : ∀ k, 2 ≤ k → q k = 0) :
    q.taylorComp p m =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p m) := by
  classical
  rw [FormalMultilinearSeries.taylorComp,
    Finset.sum_eq_single (OrderedFinpartition.single m hm)]
  · exact compAlongOrderedFinpartition_single q p hm
  · intro c _ hc
    have hgt : 1 < c.length := c.one_lt_length_of_ne_single hm hc
    ext v
    simp [compAlongOrderedFinpartition_apply, hq c.length hgt]
  · simp

/-- Composing a formal multilinear series on the right with `FormalMultilinearSeries.id` leaves it
unchanged. -/
@[simp]
theorem taylorComp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorComp (FormalMultilinearSeries.id 𝕜 E x) = p := by
  classical
  funext m
  rw [FormalMultilinearSeries.taylorComp, Finset.sum_eq_single (OrderedFinpartition.atomic m)]
  · rw [compAlongOrderedFinpartition_atomic]
    ext v
    simp
  · intro c _ hc
    have hlt : c.length < m := c.length_lt_of_ne_atomic hc
    have hex : ∃ i : Fin c.length, 1 < c.partSize i := by
      by_contra! hle
      have hle_len := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hle i
      simp only [c.sum_partSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one] at hle_len
      omega
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
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · ext v
    simp [Subsingleton.elim v ![]]
  · rw [taylorComp_of_eq_zero p hm fun k hk ↦ id_apply_of_one_lt 𝕜 F (p 0 ![]) hk]
    ext v
    simp

/-- Composing the formal Taylor series of a continuous linear map `L` on the left with a formal
multilinear series `p` postcomposes every term of `p` with `L`. -/
theorem ftaylorSeries_clm_taylorComp (L : F →L[𝕜] G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    (ftaylorSeries 𝕜 L (p 0 0)).taylorComp p = L.compFormalMultilinearSeries p := by
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · ext v
    simp [ftaylorSeries_apply, Subsingleton.elim v 0]
  · rw [taylorComp_of_eq_zero p hm fun k hk ↦ by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hk
      exact L.iteratedFDeriv_add_two d (p 0 0)]
    ext v
    simp [ftaylorSeries_apply, TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one]

/-- The formal Taylor series of the identity map at `x` is `FormalMultilinearSeries.id 𝕜 E x`. -/
@[simp]
theorem ftaylorSeries_id (x : E) :
    ftaylorSeries 𝕜 (_root_.id : E → E) x = FormalMultilinearSeries.id 𝕜 E x := by
  have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.id 𝕜 E)
    (FormalMultilinearSeries.id 𝕜 E x)
  rw [id_apply_zero, taylorComp_id, ContinuousLinearMap.coe_id'] at h
  refine h.trans ?_
  funext m
  ext v
  simp

/-- Composing the formal Taylor series of `Prod.fst` with a product series `p.prod q` recovers
`p`. -/
theorem ftaylorSeries_fst_taylorComp_prod (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 E G) :
    (ftaylorSeries 𝕜 (Prod.fst : F × G → F) (p 0 0, q 0 0)).taylorComp (p.prod q) = p := by
  have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.fst 𝕜 F G) (p.prod q)
  simp only [prod_apply, ContinuousMultilinearMap.prod_apply, ContinuousLinearMap.coe_fst'] at h
  refine h.trans ?_
  funext m
  ext v
  simp

/-- Composing the formal Taylor series of `Prod.snd` with a product series `p.prod q` recovers
`q`. -/
theorem ftaylorSeries_snd_taylorComp_prod (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 E G) :
    (ftaylorSeries 𝕜 (Prod.snd : F × G → G) (p 0 0, q 0 0)).taylorComp (p.prod q) = q := by
  have h := ftaylorSeries_clm_taylorComp (ContinuousLinearMap.snd 𝕜 F G) (p.prod q)
  simp only [prod_apply, ContinuousMultilinearMap.prod_apply, ContinuousLinearMap.coe_snd'] at h
  refine h.trans ?_
  funext m
  ext v
  simp

/-- When two inner formal multilinear series agree in all positive orders strictly below `m`,
all nonlinear partition terms in `q.taylorComp p₁ m - q.taylorComp p₂ m` cancel, leaving only the
single-block term. -/
theorem taylorComp_sub_of_eq_lt (q : FormalMultilinearSeries 𝕜 F G)
    {p₁ p₂ : FormalMultilinearSeries 𝕜 E F} {m : ℕ} (hm : 0 < m)
    (hp : ∀ k, 1 ≤ k → k < m → p₁ k = p₂ k) :
    q.taylorComp p₁ m - q.taylorComp p₂ m =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p₁ m - p₂ m) := by
  classical
  let c₀ := OrderedFinpartition.single m hm
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
    exact hp _ (c.partSize_pos i) (c.partSize_lt_of_ne_single hm hne i)
  rw [hrest, add_sub_add_right_eq_sub, compAlongOrderedFinpartition_single,
    compAlongOrderedFinpartition_single]
  ext v
  exact (map_sub (continuousMultilinearCurryFin1 𝕜 F G (q 1)) (p₁ m v) (p₂ m v)).symm

/-- When two outer formal multilinear series agree in all orders strictly below `m`, all non-atomic
partition terms in `q₁.taylorComp p m - q₂.taylorComp p m` cancel, leaving only the singleton
partition term. -/
theorem sub_taylorComp_of_eq_lt {q₁ q₂ : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hq : ∀ k < m, q₁ k = q₂ k) :
    q₁.taylorComp p m - q₂.taylorComp p m =
      (q₁ m - q₂ m).compContinuousLinearMap
        (fun _ ↦ continuousMultilinearCurryFin1 𝕜 E F (p 1)) := by
  classical
  let c₀ := OrderedFinpartition.atomic m
  rw [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.taylorComp,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)]
  have hrest : ∑ c ∈ Finset.univ.erase c₀, q₁.compAlongOrderedFinpartition p c =
      ∑ c ∈ Finset.univ.erase c₀, q₂.compAlongOrderedFinpartition p c := by
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    have hlt : c.length < m := c.length_lt_of_ne_atomic (Finset.mem_erase.mp hc).1
    unfold FormalMultilinearSeries.compAlongOrderedFinpartition
    rw [hq c.length hlt]
  rw [hrest, add_sub_add_right_eq_sub, compAlongOrderedFinpartition_atomic,
    compAlongOrderedFinpartition_atomic]
  ext v
  simp

private noncomputable def curryLeftSeries (p : FormalMultilinearSeries 𝕜 E F) (e : E) :
    FormalMultilinearSeries 𝕜 E F :=
  fun k ↦ (p (k + 1)).curryLeft e

@[simp]
private theorem curryLeftSeries_apply (p : FormalMultilinearSeries 𝕜 E F) (e : E) (k : ℕ) :
    curryLeftSeries p e k = (p (k + 1)).curryLeft e :=
  (rfl)

private noncomputable def taylorCompDeriv (q : FormalMultilinearSeries 𝕜 F G)
    (p d : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E G :=
  fun m ↦ ∑ c : OrderedFinpartition m, ∑ i : Fin c.length,
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun j ↦ p (c.partSize j)) i) (d (c.partSize i))

private theorem add_taylorComp (q₁ q₂ : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    (q₁ + q₂).taylorComp p = q₁.taylorComp p + q₂.taylorComp p := by
  funext m
  ext v
  simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply, sum_apply,
    Finset.sum_add_distrib]

private theorem taylorCompDeriv_add (q : FormalMultilinearSeries 𝕜 F G)
    (p d₁ d₂ : FormalMultilinearSeries 𝕜 E F) :
    taylorCompDeriv q p (d₁ + d₂) = taylorCompDeriv q p d₁ + taylorCompDeriv q p d₂ := by
  funext m
  ext v
  simp [taylorCompDeriv, sum_apply, map_add, Finset.sum_add_distrib]

private theorem hasFDerivAt_line (p dp : FormalMultilinearSeries 𝕜 E F) (k : ℕ) :
    HasFDerivAt (fun t : 𝕜 ↦ p k + t • dp k)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)) 0 :=
  (((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)).hasFDerivAt (x := 0)).const_add (p k)

private theorem eq_of_hasFDerivAt_smulRight {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {f₁ f₂ : 𝕜 → V} {v₁ v₂ : V}
    (h₁ : HasFDerivAt f₁ ((ContinuousLinearMap.id 𝕜 𝕜).smulRight v₁) 0)
    (h₂ : HasFDerivAt f₂ ((ContinuousLinearMap.id 𝕜 𝕜).smulRight v₂) 0)
    (hf : f₁ = f₂) : v₁ = v₂ := by
  rw [hf] at h₁
  simpa using congrArg (fun L : 𝕜 →L[𝕜] V ↦ L 1) (h₁.unique h₂)

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
    (Filter.Eventually.of_forall fun _ ↦ by
      simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition])).congr_fderiv ?_
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
    (Filter.Eventually.of_forall fun _ ↦ by
      simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition])).congr_fderiv ?_
  ext v
  simp [FormalMultilinearSeries.taylorComp, sum_apply, Finset.smul_sum]

private theorem taylorCompDeriv_taylorComp_left
    {r : FormalMultilinearSeries 𝕜 G H} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} (dp : FormalMultilinearSeries 𝕜 E F) {m : ℕ}
    (ih : ∀ p' : FormalMultilinearSeries 𝕜 E F,
      ((r.taylorComp q).taylorComp p') m = (r.taylorComp (q.taylorComp p')) m) :
    taylorCompDeriv (r.taylorComp q) p dp m =
      taylorCompDeriv r (q.taylorComp p) (taylorCompDeriv q p dp) m := by
  let P : 𝕜 → FormalMultilinearSeries 𝕜 E F := fun t k ↦ p k + t • dp k
  have hP0 : P 0 = p := by funext k; simp [P]
  have hP : ∀ k, HasFDerivAt (fun t ↦ P t k)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dp k)) 0 := hasFDerivAt_line p dp
  have hQ (k : ℕ) : HasFDerivAt (fun t ↦ q.taylorComp (P t) k)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv q p dp k)) 0 := by
    simpa [hP0] using hasFDerivAt_taylorComp_right q k hP
  exact eq_of_hasFDerivAt_smulRight
    (by simpa [hP0] using hasFDerivAt_taylorComp_right (r.taylorComp q) m hP)
    (by simpa [hP0] using hasFDerivAt_taylorComp_right r m hQ)
    (funext fun t ↦ ih (P t))

private theorem taylorCompDeriv_taylorComp_right
    {r : FormalMultilinearSeries 𝕜 G H} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} (dq : FormalMultilinearSeries 𝕜 F G) {m : ℕ}
    (ih : ∀ q' : FormalMultilinearSeries 𝕜 F G,
      ((r.taylorComp q').taylorComp p) m = (r.taylorComp (q'.taylorComp p)) m) :
    (taylorCompDeriv r q dq).taylorComp p m =
      taylorCompDeriv r (q.taylorComp p) (dq.taylorComp p) m := by
  let Q : 𝕜 → FormalMultilinearSeries 𝕜 F G := fun t k ↦ q k + t • dq k
  have hQ0 : Q 0 = q := by funext k; simp [Q]
  have hQ : ∀ k, HasFDerivAt (fun t ↦ Q t k)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (dq k)) 0 := hasFDerivAt_line q dq
  have hRQ (k : ℕ) : HasFDerivAt (fun t ↦ r.taylorComp (Q t) k)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (taylorCompDeriv r q dq k)) 0 := by
    simpa [hQ0] using hasFDerivAt_taylorComp_right r k hQ
  exact eq_of_hasFDerivAt_smulRight
    (hasFDerivAt_taylorComp_left p m hRQ)
    (by simpa [hQ0] using
      hasFDerivAt_taylorComp_right r m (fun k ↦ hasFDerivAt_taylorComp_left p k hQ))
    (funext fun t ↦ ih (Q t))

/-- Left-currying a Taylor composite splits into left-currying the outer series and
differentiating the inner series (`taylorCompDeriv`). The partition-extension term matching via
`OrderedFinpartition.extendEquiv` (`extendLeft` and `extendMiddle`) is adapted from
`faaDiBruno_aux1`, `faaDiBruno_aux2`, and `HasFTaylorSeriesUpToOn.comp` in
`Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno` (Sébastien Gouëzel). -/
private theorem curryLeftSeries_taylorComp (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (e : E) :
    curryLeftSeries (q.taylorComp p) e =
      (curryLeftSeries q (continuousMultilinearCurryFin1 𝕜 E F (p 1) e)).taylorComp p +
        taylorCompDeriv q p (curryLeftSeries p e) := by
  classical
  funext m
  ext v
  rw [curryLeftSeries_apply, ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.taylorComp, ← (OrderedFinpartition.extendEquiv m).sum_comp,
    Fintype.sum_sigma, sum_apply]
  simp only [Fintype.sum_option, OrderedFinpartition.extendEquiv_apply, add_apply,
    _root_.add_apply, sum_apply, FormalMultilinearSeries.taylorComp, taylorCompDeriv,
    Finset.sum_add_distrib]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ ↦ ?_)
    (Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_)
  · simp only [OrderedFinpartition.extend, OrderedFinpartition.extendLeft,
      compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
      curryLeftSeries_apply, ContinuousMultilinearMap.curryLeft_apply,
      continuousMultilinearCurryFin1_apply]
    congr 1
    ext j
    refine Fin.cases ?_ (fun _ ↦ rfl) j
    simp only [Fin.cons_zero]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha _
    obtain rfl : a = 0 := by omega
    simp
  · simp only [OrderedFinpartition.extend, OrderedFinpartition.extendMiddle,
      compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply,
      OrderedFinpartition.compAlongOrderedFinpartitionL_apply,
      OrderedFinpartition.compAlongOrderFinpartition_apply, curryLeftSeries_apply]
    congr 1
    ext j
    rcases eq_or_ne j i with rfl | hij
    · simp only [↓reduceDIte, Function.update_self, ContinuousMultilinearMap.curryLeft_apply]
      apply FormalMultilinearSeries.congr _ (by simp)
      intro a _ _
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
  -- Induct on the arity `m`, quantified over all triples `(r, q, p)`. In the inductive step
  -- `m + 1`, uncurrying the first vector argument `e` expresses both sides in degree `m` via
  -- `curryLeftSeries_taylorComp`, and differentiating the degree-`m` induction hypothesis along
  -- affine lines in `p` and `q` relates the resulting `taylorCompDeriv` terms.
  funext m
  induction m generalizing r q p with
  | zero =>
    ext v
    simp
  | succ m ih =>
    apply Function.LeftInverse.injective ContinuousMultilinearMap.uncurry_curryLeft
    ext e : 1
    rw [← curryLeftSeries_apply, ← curryLeftSeries_apply]
    let pe : F := continuousMultilinearCurryFin1 𝕜 E F (p 1) e
    let qpe : G := continuousMultilinearCurryFin1 𝕜 F G (q 1) pe
    have hp1 : continuousMultilinearCurryFin1 𝕜 E G (q.taylorComp p 1) e = qpe := by
      simp [qpe, pe]
    calc curryLeftSeries ((r.taylorComp q).taylorComp p) e m
      _ = (curryLeftSeries (r.taylorComp q) pe).taylorComp p m +
            taylorCompDeriv (r.taylorComp q) p (curryLeftSeries p e) m := by
          rw [curryLeftSeries_taylorComp, add_apply]
      _ = ((curryLeftSeries r qpe).taylorComp q).taylorComp p m +
            ((taylorCompDeriv r q (curryLeftSeries q pe)).taylorComp p m +
              taylorCompDeriv (r.taylorComp q) p (curryLeftSeries p e) m) := by
          rw [curryLeftSeries_taylorComp r q pe, add_taylorComp, add_apply, add_assoc]
      _ = (curryLeftSeries r qpe).taylorComp (q.taylorComp p) m +
            taylorCompDeriv r (q.taylorComp p) (curryLeftSeries (q.taylorComp p) e) m := by
          rw [ih (curryLeftSeries r qpe) q p,
            taylorCompDeriv_taylorComp_right (curryLeftSeries q pe) (fun q' ↦ ih r q' p),
            taylorCompDeriv_taylorComp_left (curryLeftSeries p e) (fun p' ↦ ih r q p'),
            ← add_apply, ← taylorCompDeriv_add, ← curryLeftSeries_taylorComp q p e]
      _ = curryLeftSeries (r.taylorComp (q.taylorComp p)) e m := by
          rw [curryLeftSeries_taylorComp r (q.taylorComp p) e, hp1, add_apply]

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
