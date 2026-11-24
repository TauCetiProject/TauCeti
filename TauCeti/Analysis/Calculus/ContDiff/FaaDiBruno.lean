/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import TauCeti.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear

/-!
# Continuity, smoothness, and algebra of the Faà di Bruno composition

The `m`-th coefficient of `q.taylorComp p` is a finite sum, over the ordered partitions of `m`,
of continuous multilinear expressions in the coefficients of `q` and `p` of order at most `m`.
It depends only on `q 0, …, q m` and `p 1, …, p m` (`FormalMultilinearSeries.taylorComp_congr`),
depends continuously and smoothly on those finitely many coefficients (`Filter.Tendsto.taylorComp`,
`ContDiffWithinAt.taylorComp`, `ContDiffOn.taylorComp`, `ContDiffAt.taylorComp`), distributes over
sums and products (`FormalMultilinearSeries.add_taylorComp`,
`FormalMultilinearSeries.prod_taylorComp`), admits `FormalMultilinearSeries.id` as a two-sided unit
(`FormalMultilinearSeries.taylorComp_id`, `FormalMultilinearSeries.id_taylorComp`), postcomposes
along the formal Taylor series of continuous linear maps
(`ContinuousLinearMap.ftaylorSeries_taylorComp`), preserves slot symmetry
(`FormalMultilinearSeries.taylorComp_comp_perm`), and is associative across arbitrary formal
multilinear series (`FormalMultilinearSeries.taylorComp_assoc`).

For `0 < m`, the single-block partition `OrderedFinpartition.single m` is the unique ordered
partition of length `1`, and every other partition has strictly smaller parts
(`OrderedFinpartition.partSize_lt_of_ne_single`) and length at least `2`
(`OrderedFinpartition.one_lt_length_of_ne_single`). Consequently, an outer series vanishing in
orders `2` through `m` reduces `q.taylorComp p m` to its linear term
(`FormalMultilinearSeries.taylorComp_of_eq_zero`), and when two inner series agree in orders `1`
through `m - 1`, all nonlinear partition terms cancel in the `m`-th composite coefficient
(`FormalMultilinearSeries.taylorComp_sub_taylorComp_of_eq_lt_right`). Dually, using the singleton
partition `OrderedFinpartition.atomic m` (`OrderedFinpartition.length_lt_of_ne_atomic`), when two
outer series agree in orders `1` through `m - 1`, their composite difference reduces to the atomic
term (`FormalMultilinearSeries.taylorComp_sub_taylorComp_of_eq_lt_left`). An ordered partition is
uniquely determined by its unordered family of block ranges
(`OrderedFinpartition.eq_of_forall_exists_range_emb_eq`), so permutations of `Fin n` act on
`OrderedFinpartition n` via pushforward (`OrderedFinpartition.mapPerm`,
`OrderedFinpartition.permEquiv`).

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
track of each order separately, as needed for changes of variables in Sobolev spaces. In
particular, a `Cᵐ` function on a proper space composed with a `Cᵐ` map that is bounded together
with its derivatives of order at most `m` has a bounded `m`-th derivative
(`ContDiff.exists_norm_iteratedFDeriv_comp_le`).
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
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hs (i : Fin c.length) : c.partSize i = 1 :=
    ((Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun _ ↦ 1) (g := c.partSize)
      fun j _ ↦ c.partSize_pos j).mp (by simp [h]) i (Finset.mem_univ i)).symm
  rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
  dsimp at h hs; subst l
  obtain rfl : s = fun _ ↦ 1 := funext hs
  refine OrderedFinpartition.ext (y := atomic n) rfl (heq_of_eq rfl)
    (heq_of_eq <| funext₂ fun i j ↦ ?_)
  exact (congrArg (e i) (Subsingleton.elim j _)).trans (congrFun ho.eq_id i)

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
theorem single_length (n : ℕ) (hn : 0 < n) : (single n hn).length = 1 := (rfl)

@[simp]
theorem single_partSize (n : ℕ) (hn : 0 < n) (i : Fin (single n hn).length) :
    (single n hn).partSize i = n := (rfl)

@[simp]
theorem single_emb (n : ℕ) (hn : 0 < n) (i : Fin (single n hn).length)
    (j : Fin ((single n hn).partSize i)) :
    (single n hn).emb i j = j.cast (single_partSize n hn i) := (rfl)

/-- For `0 < n`, an ordered partition of `Fin n` equals `OrderedFinpartition.single n hn` if and
only if it has a single part. -/
theorem eq_single_iff_length {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n} :
    c = single n hn ↔ c.length = 1 := by
  refine ⟨fun h ↦ h ▸ rfl, fun hl ↦ ?_⟩
  have hsum := c.sum_partSize
  rcases c with ⟨l, s, hp, e, hm, ho, hd, hc⟩
  dsimp at hl hsum; subst l
  obtain rfl : s = fun _ ↦ n := funext fun i ↦ by rw [Subsingleton.elim i 0]; simpa using hsum
  exact OrderedFinpartition.ext (y := single n hn) rfl (heq_of_eq rfl)
    (heq_of_eq <| funext fun i ↦ by rw [Subsingleton.elim i 0]; exact (hm 0).eq_id)

/-- Every partition of a positive `n` other than `OrderedFinpartition.single n hn` has at least two
parts. -/
theorem one_lt_length_of_ne_single {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n}
    (hc : c ≠ single n hn) : 1 < c.length := by
  have := c.length_pos hn; have : c.length ≠ 1 := mt (c.eq_single_iff_length hn).mpr hc; omega

/-- Every part of a partition other than `OrderedFinpartition.single n hn` has size strictly less
than `n`. -/
theorem partSize_lt_of_ne_single {n : ℕ} (hn : 0 < n) {c : OrderedFinpartition n}
    (hc : c ≠ single n hn) (i : Fin c.length) : c.partSize i < n := by
  refine lt_of_le_of_ne (c.partSize_le i) fun hi ↦ hc ((c.eq_single_iff_length hn).mpr ?_)
  rw [← Fintype.card_fin c.length]
  refine Fintype.card_eq_one_iff.mpr ⟨i, fun j ↦ by_contra fun hji ↦ ?_⟩
  have hle := Finset.add_le_sum (fun k _ ↦ Nat.zero_le (c.partSize k))
    (Finset.mem_univ i) (Finset.mem_univ j) (Ne.symm hji)
  have := c.partSize_pos j; rw [c.sum_partSize] at hle; omega

/-- Two ordered partitions of `Fin n` are equal if every block of the first has the same range as
some block of the second. -/
theorem eq_of_forall_exists_range_emb_eq {n : ℕ} {c₁ c₂ : OrderedFinpartition n}
    (h : ∀ i, ∃ j, Set.range (c₁.emb i) = Set.range (c₂.emb j)) : c₁ = c₂ := by
  choose f hf using h
  have hfinj : Function.Injective f := fun i₁ i₂ hfi ↦ by_contra fun hne ↦
    Set.disjoint_left.mp (c₁.disjoint (Set.mem_univ _) (Set.mem_univ _) hne)
      ⟨⟨0, c₁.partSize_pos i₁⟩, rfl⟩ (by dsimp only; rw [hf i₂, ← hfi, ← hf i₁]; exact ⟨_, rfl⟩)
  have hfsurj : Function.Surjective f := fun j ↦ by
    obtain ⟨i, a, ha⟩ := c₁.cover (c₂.emb j ⟨0, c₂.partSize_pos j⟩)
    exact ⟨i, by_contra fun hne ↦ Set.disjoint_left.mp
      (c₂.disjoint (Set.mem_univ _) (Set.mem_univ _) hne)
      (by dsimp only; rw [← hf i]; exact ⟨a, ha⟩) ⟨_, rfl⟩⟩
  have hlen : c₁.length = c₂.length := by
    simpa using Fintype.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  rcases c₁ with ⟨l₁, s₁, hp₁, e₁, hm₁, ho₁, hd₁, hc₁⟩
  rcases c₂ with ⟨l₂, s₂, hp₂, e₂, hm₂, ho₂, hd₂, hc₂⟩
  dsimp at f hf hlen; subst hlen
  have hmax (i : Fin l₁) : e₁ i ⟨s₁ i - 1, Nat.sub_one_lt_of_lt (hp₁ i)⟩ =
      e₂ (f i) ⟨s₂ (f i) - 1, Nat.sub_one_lt_of_lt (hp₂ (f i))⟩ :=
    IsGreatest.unique (s := Set.range (e₁ i))
      ⟨⟨_, rfl⟩, Set.forall_mem_range.2 fun _ ↦ (hm₁ i).monotone (Fin.mk_le_mk.2 (by omega))⟩
      (by rw [hf i]; exact ⟨⟨_, rfl⟩, Set.forall_mem_range.2 fun _ ↦
        (hm₂ (f i)).monotone (Fin.mk_le_mk.2 (by omega))⟩)
  have hf_id : f = id := StrictMono.eq_id fun a b hab ↦
    ho₂.lt_iff_lt.mp (hmax a ▸ hmax b ▸ ho₁ hab)
  subst hf_id
  obtain rfl : s₁ = s₂ := funext fun i ↦ by
    have hcard := congrArg Finset.card (Finset.coe_inj.mp (by simpa using hf i) :
      Finset.univ.image (e₁ i) = Finset.univ.image (e₂ i))
    simpa [Finset.card_image_of_injective _ (hm₁ i).injective,
      Finset.card_image_of_injective _ (hm₂ i).injective] using hcard
  exact OrderedFinpartition.ext rfl (heq_of_eq rfl)
    (heq_of_eq <| funext fun i ↦ ((hm₁ i).range_inj_of_wellFoundedLT (hm₂ i)).mp (hf i))

private def permEmb {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n))
    (i : Fin c.length) : Fin (c.partSize i) ↪o Fin n :=
  (Finset.univ.image (σ ∘ c.emb i)).orderEmbOfFin <| by
    rw [Finset.card_image_of_injective _ (σ.injective.comp (c.emb_strictMono i).injective),
      Finset.card_univ, Fintype.card_fin]

private theorem range_permEmb {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n))
    (i : Fin c.length) : Set.range (permEmb c σ i) = σ '' Set.range (c.emb i) := by
  simpa [permEmb, Finset.range_orderEmbOfFin, Function.comp_def] using Set.range_comp σ (c.emb i)

private def permMax {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n))
    (i : Fin c.length) : Fin n :=
  permEmb c σ i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩

private theorem permMax_injective {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permMax c σ) := fun i₁ i₂ h ↦ by_contra fun hne ↦
  Set.disjoint_left.mp (Set.disjoint_image_of_injective σ.injective <|
    c.disjoint (Set.mem_univ _) (Set.mem_univ _) hne)
    (range_permEmb c σ i₁ ▸ ⟨_, rfl⟩ : permMax c σ i₁ ∈ σ '' Set.range (c.emb i₁))
    (range_permEmb c σ i₂ ▸ ⟨_, h.symm⟩ : permMax c σ i₁ ∈ σ '' Set.range (c.emb i₂))

/-- Push forward an ordered partition of `Fin n` along a permutation `σ`, sorting each mapped block
and reordering the blocks by increasing maximum element. -/
def mapPerm {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    OrderedFinpartition n where
  length := c.length
  partSize i := c.partSize (Tuple.sort (permMax c σ) i)
  partSize_pos i := c.partSize_pos _
  emb i := permEmb c σ (Tuple.sort (permMax c σ) i)
  emb_strictMono i := (permEmb c σ _).strictMono
  parts_strictMono := (Tuple.monotone_sort (permMax c σ)).strictMono_of_injective
    ((permMax_injective c σ).comp (Tuple.sort (permMax c σ)).injective)
  disjoint i₁ _ i₂ _ hne := by
    rw [Function.onFun, range_permEmb, range_permEmb]
    exact Set.disjoint_image_of_injective σ.injective <|
      c.disjoint (Set.mem_univ _) (Set.mem_univ _) ((Tuple.sort (permMax c σ)).injective.ne hne)
  cover x := by
    obtain ⟨i, j, hj⟩ := c.cover (σ.symm x)
    exact ⟨(Tuple.sort (permMax c σ)).symm i, by
      rw [Equiv.apply_symm_apply, range_permEmb]; exact ⟨σ.symm x, ⟨j, hj⟩, σ.apply_symm_apply x⟩⟩

@[simp]
theorem mapPerm_length {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    (c.mapPerm σ).length = c.length := (rfl)

/-- The blocks of `c.mapPerm σ` are the `σ`-images of the blocks of `c`, matched by a bijection of
part indices that preserves part sizes. -/
theorem exists_equiv_mapPerm {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    ∃ π : Fin (c.mapPerm σ).length ≃ Fin c.length,
      ∀ i, (c.mapPerm σ).partSize i = c.partSize (π i) ∧
        Set.range ((c.mapPerm σ).emb i) = σ '' Set.range (c.emb (π i)) :=
  ⟨Tuple.sort (permMax c σ), fun _ ↦ ⟨rfl, range_permEmb c σ _⟩⟩

@[simp]
theorem mapPerm_one {n : ℕ} (c : OrderedFinpartition n) : c.mapPerm 1 = c :=
  let ⟨π, hπ⟩ := c.exists_equiv_mapPerm 1
  eq_of_forall_exists_range_emb_eq fun i ↦ ⟨π i, by simpa using (hπ i).2⟩

/-- Pushing forward an ordered partition successively along `σ` and `τ` equals pushing forward
along `τ * σ`. -/
theorem mapPerm_mapPerm {n : ℕ} (c : OrderedFinpartition n) (σ τ : Equiv.Perm (Fin n)) :
    (c.mapPerm σ).mapPerm τ = c.mapPerm (τ * σ) := by
  obtain ⟨π₁, hπ₁⟩ := (c.mapPerm σ).exists_equiv_mapPerm τ
  obtain ⟨π₂, hπ₂⟩ := c.exists_equiv_mapPerm σ
  obtain ⟨π₃, hπ₃⟩ := c.exists_equiv_mapPerm (τ * σ)
  exact eq_of_forall_exists_range_emb_eq fun i ↦ ⟨π₃.symm (π₂ (π₁ i)), by
    rw [(hπ₁ i).2, (hπ₂ (π₁ i)).2, (hπ₃ _).2, Equiv.apply_symm_apply, ← Set.image_comp]; rfl⟩

@[simp]
theorem mapPerm_mapPerm_symm {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    (c.mapPerm σ).mapPerm σ.symm = c := by
  rw [mapPerm_mapPerm, ← Equiv.Perm.inv_def, inv_mul_cancel, mapPerm_one]

@[simp]
theorem mapPerm_symm_mapPerm {n : ℕ} (c : OrderedFinpartition n) (σ : Equiv.Perm (Fin n)) :
    (c.mapPerm σ.symm).mapPerm σ = c := by
  rw [mapPerm_mapPerm, ← Equiv.Perm.inv_def, mul_inv_cancel, mapPerm_one]

/-- Action of a permutation `σ : Equiv.Perm (Fin n)` as a bijection on `OrderedFinpartition n`. -/
def permEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OrderedFinpartition n ≃ OrderedFinpartition n where
  toFun c := c.mapPerm σ
  invFun c := c.mapPerm σ.symm
  left_inv c := c.mapPerm_mapPerm_symm σ
  right_inv c := c.mapPerm_symm_mapPerm σ

@[simp]
theorem permEquiv_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : OrderedFinpartition n) :
    permEquiv σ c = c.mapPerm σ := (rfl)

@[simp]
theorem permEquiv_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permEquiv σ).symm = permEquiv σ.symm := (rfl)

@[simp]
theorem permEquiv_one {n : ℕ} : permEquiv (1 : Equiv.Perm (Fin n)) = Equiv.refl _ :=
  Equiv.ext mapPerm_one

theorem permEquiv_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    permEquiv (σ * τ) = (permEquiv τ).trans (permEquiv σ) :=
  Equiv.ext fun c ↦ (c.mapPerm_mapPerm τ σ).symm

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

/-- The `m`-th coefficient of `y ↦ (q y).taylorComp (p y)` is `C^n` within `s` at `x` whenever the
coefficients `y ↦ q y k` (`k ≤ m`) and `y ↦ p y k` (`1 ≤ k ≤ m`) are `C^n` within `s` at `x`. -/
theorem ContDiffWithinAt.taylorComp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {n : ℕ∞ω} {s : Set M} {x : M}
    {q : M → FormalMultilinearSeries 𝕜 F G} {p : M → FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, ContDiffWithinAt 𝕜 n (fun y ↦ q y k) s x)
    (hp : ∀ k, 1 ≤ k → k ≤ m → ContDiffWithinAt 𝕜 n (fun y ↦ p y k) s x) :
    ContDiffWithinAt 𝕜 n (fun y ↦ (q y).taylorComp (p y) m) s x := by
  refine ContDiffWithinAt.sum fun c _ ↦ ?_
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  exact B.analyticOnNhd_uncurry_of_multilinear.contDiff.comp_contDiffWithinAt
    ((hq c.length c.length_le).prodMk
      (contDiffWithinAt_pi.mpr fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i)))

/-- The `m`-th coefficient of `x ↦ (q x).taylorComp (p x)` is `C^n` on `s` whenever the
coefficients `x ↦ q x k` (`k ≤ m`) and `x ↦ p x k` (`1 ≤ k ≤ m`) are `C^n` on `s`. -/
theorem ContDiffOn.taylorComp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {n : ℕ∞ω} {s : Set M}
    {q : M → FormalMultilinearSeries 𝕜 F G} {p : M → FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, ContDiffOn 𝕜 n (fun x ↦ q x k) s)
    (hp : ∀ k, 1 ≤ k → k ≤ m → ContDiffOn 𝕜 n (fun x ↦ p x k) s) :
    ContDiffOn 𝕜 n (fun x ↦ (q x).taylorComp (p x) m) s :=
  fun x hx ↦ ContDiffWithinAt.taylorComp (fun k hk ↦ hq k hk x hx)
    (fun k hk₁ hk₂ ↦ hp k hk₁ hk₂ x hx)

/-- Pointwise version of `ContDiffWithinAt.taylorComp`. -/
theorem ContDiffAt.taylorComp {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
    {n : ℕ∞ω} {x : M}
    {q : M → FormalMultilinearSeries 𝕜 F G} {p : M → FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, ContDiffAt 𝕜 n (fun y ↦ q y k) x)
    (hp : ∀ k, 1 ≤ k → k ≤ m → ContDiffAt 𝕜 n (fun y ↦ p y k) x) :
    ContDiffAt 𝕜 n (fun y ↦ (q y).taylorComp (p y) m) x :=
  contDiffWithinAt_univ.mp <| ContDiffWithinAt.taylorComp
    (fun k hk ↦ (hq k hk).contDiffWithinAt)
    (fun k hk₁ hk₂ ↦ (hp k hk₁ hk₂).contDiffWithinAt)

namespace FormalMultilinearSeries

/-- The `m`-th coefficient of `q.taylorComp p` depends only on `q 0, …, q m` and `p 1, …, p m`. -/
theorem taylorComp_congr {q₁ q₂ : FormalMultilinearSeries 𝕜 F G}
    {p₁ p₂ : FormalMultilinearSeries 𝕜 E F} {m : ℕ}
    (hq : ∀ k ≤ m, q₁ k = q₂ k) (hp : ∀ k, 1 ≤ k → k ≤ m → p₁ k = p₂ k) :
    q₁.taylorComp p₁ m = q₂.taylorComp p₂ m :=
  Finset.sum_congr rfl fun c _ ↦ by
    unfold FormalMultilinearSeries.compAlongOrderedFinpartition
    rw [hq c.length c.length_le]
    exact congrArg _ (funext fun i ↦ hp _ (c.partSize_pos i) (c.partSize_le i))

@[simp]
theorem taylorComp_zero_apply (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 → E) :
    q.taylorComp p 0 v = q 0 0 := by
  rw [FormalMultilinearSeries.taylorComp, Fintype.sum_unique, OrderedFinpartition.default_eq]
  exact congrArg (q 0) (Subsingleton.elim _ _)

theorem taylorComp_zero (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    q.taylorComp p 0 = (continuousMultilinearCurryFin0 𝕜 E G).symm (q 0 0) :=
  ContinuousMultilinearMap.ext fun _ ↦ by simp

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
  rw [FormalMultilinearSeries.taylorComp, Fintype.sum_unique,
    Subsingleton.elim (default : OrderedFinpartition 1) (OrderedFinpartition.single 1 zero_lt_one),
    compAlongOrderedFinpartition_single]

theorem taylorComp_one_apply (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 1 → E) :
    q.taylorComp p 1 v = q 1 ![p 1 v] := by simp

/-- Faà di Bruno composition is additive in the outer formal multilinear series. -/
@[simp]
theorem add_taylorComp (q₁ q₂ : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) :
    (q₁ + q₂).taylorComp p = q₁.taylorComp p + q₂.taylorComp p :=
  funext fun _ ↦ ContinuousMultilinearMap.ext fun _ ↦ by
    simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply, sum_apply,
      Finset.sum_add_distrib]

/-- Faà di Bruno composition distributes over Cartesian products of outer formal multilinear
series. -/
@[simp]
theorem prod_taylorComp (q₁ : FormalMultilinearSeries 𝕜 F G)
    (q₂ : FormalMultilinearSeries 𝕜 F H) (p : FormalMultilinearSeries 𝕜 E F) :
    (q₁.prod q₂).taylorComp p = (q₁.taylorComp p).prod (q₂.taylorComp p) :=
  funext fun _ ↦ ContinuousMultilinearMap.ext fun _ ↦ Prod.ext
    (by simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply, sum_apply,
      Prod.fst_sum])
    (by simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition_apply, sum_apply,
      Prod.snd_sum])

/-- If an outer formal multilinear series vanishes in all orders `2 ≤ k ≤ m`, then for `0 < m` only
the single-block partition contributes to `q.taylorComp p m`. -/
theorem taylorComp_of_eq_zero {q : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hm : 0 < m)
    (hq : ∀ k, 2 ≤ k → k ≤ m → q k = 0) :
    q.taylorComp p m =
      (continuousMultilinearCurryFin1 𝕜 F G (q 1)).compContinuousMultilinearMap (p m) := by
  classical
  rw [FormalMultilinearSeries.taylorComp,
    Finset.sum_eq_single (OrderedFinpartition.single m hm)]
  · exact compAlongOrderedFinpartition_single q p hm
  · intro c _ hc
    ext v
    simp [compAlongOrderedFinpartition_apply,
      hq c.length (c.one_lt_length_of_ne_single hm hc) c.length_le]
  · simp

/-- Composing a formal multilinear series on the right with `FormalMultilinearSeries.id` leaves it
unchanged. -/
@[simp]
theorem taylorComp_id (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    p.taylorComp (FormalMultilinearSeries.id 𝕜 E x) = p := by
  classical
  funext m
  rw [FormalMultilinearSeries.taylorComp, Finset.sum_eq_single (OrderedFinpartition.atomic m)]
  · rw [compAlongOrderedFinpartition_atomic]; ext v; simp
  · intro c _ hc
    have hlt := c.length_lt_of_ne_atomic hc
    have ⟨i, hi⟩ : ∃ i : Fin c.length, 1 < c.partSize i := by
      by_contra! hle
      have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hle i
      simp only [c.sum_partSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one] at hsum
      omega
    ext v
    rw [compAlongOrderedFinpartition_apply, _root_.zero_apply]
    exact ContinuousMultilinearMap.map_coord_zero _ i <| by
      simp [OrderedFinpartition.applyOrderedFinpartition_apply, id_apply_of_one_lt _ _ _ hi]
  · simp

/-- Composing `FormalMultilinearSeries.id` on the left with a formal multilinear series `p` gives
`p` (with constant term matching `p 0 v₀`). -/
@[simp]
theorem id_taylorComp (p : FormalMultilinearSeries 𝕜 E F) (v₀ : Fin 0 → E) :
    (FormalMultilinearSeries.id 𝕜 F (p 0 v₀)).taylorComp p = p := by
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · exact ContinuousMultilinearMap.ext fun v ↦ by simp [Subsingleton.elim v v₀]
  · rw [taylorComp_of_eq_zero p hm fun k hk _ ↦ id_apply_of_one_lt 𝕜 F (p 0 v₀) hk]
    exact ContinuousMultilinearMap.ext fun _ ↦ by simp

/-- Composing the formal Taylor series of a continuous linear map `L` on the left with a formal
multilinear series `p` postcomposes every term of `p` with `L`, provided `L y = L (p 0 v₀)`. -/
theorem _root_.ContinuousLinearMap.ftaylorSeries_taylorComp (L : F →L[𝕜] G)
    (p : FormalMultilinearSeries 𝕜 E F) {y : F} {v₀ : Fin 0 → E} (hy : L y = L (p 0 v₀)) :
    (ftaylorSeries 𝕜 L y).taylorComp p = L.compFormalMultilinearSeries p := by
  funext m
  rcases m.eq_zero_or_pos with rfl | hm
  · exact ContinuousMultilinearMap.ext fun v ↦ by
      simp [TauCeti.ftaylorSeries_apply, hy, Subsingleton.elim v v₀]
  · rw [taylorComp_of_eq_zero p hm fun k hk _ ↦ by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hk; exact L.iteratedFDeriv_add_two d y]
    exact ContinuousMultilinearMap.ext fun _ ↦ by
      simp [TauCeti.ftaylorSeries_apply, TauCeti.continuousMultilinearCurryFin1_iteratedFDeriv_one]

/-- Composing the formal Taylor series of `Prod.fst` with a product series `p.prod q` recovers
`p`, regardless of the second coordinate of the base point. -/
theorem ftaylorSeries_fst_taylorComp_prod (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 E G) (v₀ : Fin 0 → E) (y : G) :
    (ftaylorSeries 𝕜 (Prod.fst : F × G → F) (p 0 v₀, y)).taylorComp (p.prod q) = p := by
  have h := (ContinuousLinearMap.fst 𝕜 F G).ftaylorSeries_taylorComp (p.prod q)
    (y := (p 0 v₀, y)) (v₀ := v₀) rfl
  simp only [ContinuousLinearMap.coe_fst'] at h
  exact h.trans (funext fun _ ↦ ContinuousMultilinearMap.ext fun _ ↦ by simp)

/-- Composing the formal Taylor series of `Prod.snd` with a product series `p.prod q` recovers
`q`, regardless of the first coordinate of the base point. -/
theorem ftaylorSeries_snd_taylorComp_prod (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 E G) (x : F) (v₀ : Fin 0 → E) :
    (ftaylorSeries 𝕜 (Prod.snd : F × G → G) (x, q 0 v₀)).taylorComp (p.prod q) = q := by
  have h := (ContinuousLinearMap.snd 𝕜 F G).ftaylorSeries_taylorComp (p.prod q)
    (y := (x, q 0 v₀)) (v₀ := v₀) rfl
  simp only [ContinuousLinearMap.coe_snd'] at h
  exact h.trans (funext fun _ ↦ ContinuousMultilinearMap.ext fun _ ↦ by simp)

/-- When two inner formal multilinear series agree in all positive orders strictly below `m`,
all nonlinear partition terms in `q.taylorComp p₁ m - q.taylorComp p₂ m` cancel, leaving only the
single-block term. -/
theorem taylorComp_sub_taylorComp_of_eq_lt_right (q : FormalMultilinearSeries 𝕜 F G)
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
      ∑ c ∈ Finset.univ.erase c₀, q.compAlongOrderedFinpartition p₂ c :=
    Finset.sum_congr rfl fun c hc ↦ congrArg _ <| funext fun i ↦
      hp _ (c.partSize_pos i) (c.partSize_lt_of_ne_single hm (Finset.mem_erase.mp hc).1 i)
  rw [hrest, add_sub_add_right_eq_sub, compAlongOrderedFinpartition_single,
    compAlongOrderedFinpartition_single]
  exact ContinuousMultilinearMap.ext fun v ↦
    (map_sub (continuousMultilinearCurryFin1 𝕜 F G (q 1)) (p₁ m v) (p₂ m v)).symm

/-- When two outer formal multilinear series agree in all positive orders strictly below `m`, all
non-atomic partition terms in `q₁.taylorComp p m - q₂.taylorComp p m` cancel, leaving only the
singleton partition term. -/
theorem taylorComp_sub_taylorComp_of_eq_lt_left {q₁ q₂ : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ} (hq : ∀ k, 1 ≤ k → k < m → q₁ k = q₂ k) :
    q₁.taylorComp p m - q₂.taylorComp p m =
      (q₁ m - q₂ m).compContinuousLinearMap
        (fun _ ↦ continuousMultilinearCurryFin1 𝕜 E F (p 1)) := by
  classical
  let c₀ := OrderedFinpartition.atomic m
  rw [FormalMultilinearSeries.taylorComp, FormalMultilinearSeries.taylorComp,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ c₀)]
  have hrest : ∑ c ∈ Finset.univ.erase c₀, q₁.compAlongOrderedFinpartition p c =
      ∑ c ∈ Finset.univ.erase c₀, q₂.compAlongOrderedFinpartition p c :=
    Finset.sum_congr rfl fun c hc ↦ by
      have hlt := c.length_lt_of_ne_atomic (Finset.mem_erase.mp hc).1
      unfold FormalMultilinearSeries.compAlongOrderedFinpartition
      rw [hq c.length (c.length_pos (Nat.zero_lt_of_lt hlt)) hlt]
  rw [hrest, add_sub_add_right_eq_sub, compAlongOrderedFinpartition_atomic,
    compAlongOrderedFinpartition_atomic]
  exact ContinuousMultilinearMap.ext fun _ ↦ by simp

/-- Faà di Bruno composition preserves slot symmetry: if every coefficient of `q` and `p` in orders
`2` through `m` is invariant under slot permutations, then `(q.taylorComp p) m` is invariant under
slot permutations. -/
theorem taylorComp_comp_perm (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) {m : ℕ}
    (hq : ∀ k, 2 ≤ k → k ≤ m → ∀ (w : Fin k → F) (π : Equiv.Perm (Fin k)), q k (w ∘ π) = q k w)
    (hp : ∀ k, 2 ≤ k → k ≤ m → ∀ (u : Fin k → E) (τ : Equiv.Perm (Fin k)), p k (u ∘ τ) = p k u)
    (v : Fin m → E) (σ : Equiv.Perm (Fin m)) :
    q.taylorComp p m (v ∘ σ) = q.taylorComp p m v := by
  classical
  rw [FormalMultilinearSeries.taylorComp, sum_apply, sum_apply,
    ← (OrderedFinpartition.permEquiv σ.symm).sum_comp]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [OrderedFinpartition.permEquiv_apply, compAlongOrderedFinpartition_apply,
    compAlongOrderedFinpartition_apply]
  obtain ⟨π, hπ⟩ := c.exists_equiv_mapPerm σ.symm
  let π' : Equiv.Perm (Fin c.length) := (finCongr (c.mapPerm_length σ.symm)).symm.trans π
  refine (FormalMultilinearSeries.congr q (c.mapPerm_length σ.symm)
    (w := (c.applyOrderedFinpartition (fun i ↦ p (c.partSize i)) v) ∘ π') fun a ha₁ _ ↦ ?_).trans ?_
  · let i : Fin (c.mapPerm σ.symm).length := ⟨a, ha₁⟩
    simp only [OrderedFinpartition.applyOrderedFinpartition_apply, Function.comp_apply]
    have hmem (j : Fin ((c.mapPerm σ.symm).partSize i)) :
        ∃ k, c.emb (π i) k = σ ((c.mapPerm σ.symm).emb i j) := by
      obtain ⟨_, ⟨k, rfl⟩, hy⟩ :
          (c.mapPerm σ.symm).emb i j ∈ σ.symm '' Set.range (c.emb (π i)) := (hπ i).2 ▸ ⟨j, rfl⟩
      exact ⟨k, by rw [← hy, σ.apply_symm_apply]⟩
    let τ : Equiv.Perm (Fin (c.partSize (π i))) :=
      (finCongr (hπ i).1).symm.trans <| Equiv.ofBijective (fun j ↦ (hmem j).choose) <|
        (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun j₁ j₂ h ↦
          ((c.mapPerm σ.symm).emb_strictMono i).injective <| σ.injective <|
            ((hmem j₁).choose_spec.symm.trans (congrArg _ h)).trans (hmem j₂).choose_spec,
          by simp [(hπ i).1]⟩
    refine (FormalMultilinearSeries.congr p (hπ i).1 (w := (v ∘ c.emb (π i)) ∘ τ)
      fun b hb₁ _ ↦ congrArg v (hmem ⟨b, hb₁⟩).choose_spec.symm).trans ?_
    by_cases h2 : 2 ≤ c.partSize (π i)
    · exact hp _ h2 (c.partSize_le (π i)) _ τ
    · have : Subsingleton (Fin (c.partSize (π i))) := ⟨fun _ _ ↦ Fin.ext (by omega)⟩
      rw [Equiv.Perm.coe_subsingleton τ]; rfl
  · by_cases h2 : 2 ≤ c.length
    · exact hq _ h2 c.length_le _ π'
    · have : Subsingleton (Fin c.length) := ⟨fun _ _ ↦ Fin.ext (by omega)⟩
      rw [Equiv.Perm.coe_subsingleton π']; rfl

private noncomputable def curryLeftSeries (p : FormalMultilinearSeries 𝕜 E F) (e : E) :
    FormalMultilinearSeries 𝕜 E F :=
  fun k ↦ (p (k + 1)).curryLeft e

@[simp]
private theorem curryLeftSeries_apply (p : FormalMultilinearSeries 𝕜 E F) (e : E) (k : ℕ) :
    curryLeftSeries p e k = (p (k + 1)).curryLeft e := (rfl)

private noncomputable def taylorCompDeriv (q : FormalMultilinearSeries 𝕜 F G)
    (p d : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E G :=
  fun m ↦ ∑ c : OrderedFinpartition m, ∑ i : Fin c.length,
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun j ↦ p (c.partSize j)) i) (d (c.partSize i))

private theorem taylorCompDeriv_add (q : FormalMultilinearSeries 𝕜 F G)
    (p d₁ d₂ : FormalMultilinearSeries 𝕜 E F) :
    taylorCompDeriv q p (d₁ + d₂) = taylorCompDeriv q p d₁ + taylorCompDeriv q p d₂ :=
  funext fun _ ↦ ContinuousMultilinearMap.ext fun _ ↦ by
    simp [taylorCompDeriv, sum_apply, map_add, Finset.sum_add_distrib]

private theorem hasDerivAt_taylorComp_right (q : FormalMultilinearSeries 𝕜 F G)
    {p : 𝕜 → FormalMultilinearSeries 𝕜 E F} {dp : FormalMultilinearSeries 𝕜 E F} (m : ℕ)
    (hp : ∀ k, HasDerivAt (fun t ↦ p t k) (dp k) 0) :
    HasDerivAt (fun t ↦ q.taylorComp (p t) m) (taylorCompDeriv q (p 0) dp m) 0 := by
  classical
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun (c : OrderedFinpartition m) _ ↦
    HasFDerivAt.linear_multilinear_comp (hasFDerivAt_const (q c.length) (0 : 𝕜))
      (fun i ↦ (hp (c.partSize i)).hasFDerivAt) (c.compAlongOrderedFinpartitionL 𝕜 E F G)
  refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ by
    simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition])).hasDerivAt.congr_deriv
      ?_
  ext v
  simp [taylorCompDeriv, sum_apply]

private theorem hasDerivAt_taylorComp_left
    {q : 𝕜 → FormalMultilinearSeries 𝕜 F G} {dq : FormalMultilinearSeries 𝕜 F G}
    (p : FormalMultilinearSeries 𝕜 E F) (m : ℕ)
    (hq : ∀ k, HasDerivAt (fun t ↦ q t k) (dq k) 0) :
    HasDerivAt (fun t ↦ (q t).taylorComp p m) (dq.taylorComp p m) 0 := by
  classical
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun (c : OrderedFinpartition m) _ ↦
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear
      (fun i ↦ p (c.partSize i))).hasFDerivAt.comp (0 : 𝕜) (hq c.length).hasFDerivAt
  refine (hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ by
    simp [FormalMultilinearSeries.taylorComp, compAlongOrderedFinpartition])).hasDerivAt.congr_deriv
      ?_
  ext v
  simp [FormalMultilinearSeries.taylorComp, sum_apply]

private theorem taylorCompDeriv_taylorComp_left
    {r : FormalMultilinearSeries 𝕜 G H} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} (dp : FormalMultilinearSeries 𝕜 E F) {m : ℕ}
    (ih : ∀ p' : FormalMultilinearSeries 𝕜 E F,
      ((r.taylorComp q).taylorComp p') m = (r.taylorComp (q.taylorComp p')) m) :
    taylorCompDeriv (r.taylorComp q) p dp m =
      taylorCompDeriv r (q.taylorComp p) (taylorCompDeriv q p dp) m := by
  let P : 𝕜 → FormalMultilinearSeries 𝕜 E F := fun t k ↦ p k + t • dp k
  have hP0 : P 0 = p := funext fun k ↦ by simp [P]
  have hP (k : ℕ) : HasDerivAt (fun t ↦ P t k) (dp k) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0 : 𝕜)).smul_const (dp k)).const_add (p k)
  have hQ (k : ℕ) := by simpa only [hP0] using hasDerivAt_taylorComp_right q k hP
  have h1 := hasDerivAt_taylorComp_right (r.taylorComp q) m hP
  have h2 := hasDerivAt_taylorComp_right r m hQ
  rw [hP0] at h1 h2
  exact (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ (ih (P t)).symm)).unique h2

private theorem taylorCompDeriv_taylorComp_right
    {r : FormalMultilinearSeries 𝕜 G H} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} (dq : FormalMultilinearSeries 𝕜 F G) {m : ℕ}
    (ih : ∀ q' : FormalMultilinearSeries 𝕜 F G,
      ((r.taylorComp q').taylorComp p) m = (r.taylorComp (q'.taylorComp p)) m) :
    (taylorCompDeriv r q dq).taylorComp p m =
      taylorCompDeriv r (q.taylorComp p) (dq.taylorComp p) m := by
  let Q : 𝕜 → FormalMultilinearSeries 𝕜 F G := fun t k ↦ q k + t • dq k
  have hQ0 : Q 0 = q := funext fun k ↦ by simp [Q]
  have hQ (k : ℕ) : HasDerivAt (fun t ↦ Q t k) (dq k) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0 : 𝕜)).smul_const (dq k)).const_add (q k)
  have hRQ (k : ℕ) := by simpa only [hQ0] using hasDerivAt_taylorComp_right r k hQ
  have h1 := hasDerivAt_taylorComp_left p m hRQ
  have h2 := hasDerivAt_taylorComp_right r m fun k ↦ hasDerivAt_taylorComp_left p k hQ
  rw [hQ0] at h2
  exact (h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ (ih (Q t)).symm)).unique h2

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
    congr 1; ext j
    refine Fin.cases ?_ (fun _ ↦ rfl) j
    simp only [Fin.cons_zero]
    exact FormalMultilinearSeries.congr _ (by simp) fun a ha _ ↦ by
      obtain rfl : a = 0 := by omega
      simp [Fin.snoc]
  · simp only [OrderedFinpartition.extend, OrderedFinpartition.extendMiddle,
      compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply,
      OrderedFinpartition.compAlongOrderedFinpartitionL_apply,
      OrderedFinpartition.compAlongOrderFinpartition_apply, curryLeftSeries_apply]
    congr 1; ext j
    rcases eq_or_ne j i with rfl | hij
    · simp only [↓reduceDIte, Function.update_self, ContinuousMultilinearMap.curryLeft_apply]
      exact FormalMultilinearSeries.congr _ (by simp) fun a _ _ ↦ by cases a <;> simp [Fin.cons]
    · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, Function.update_of_ne]
      exact FormalMultilinearSeries.congr _ (by simp [hij]) (by simp)

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
  | zero => exact ContinuousMultilinearMap.ext fun _ ↦ by simp
  | succ m ih =>
    apply Function.LeftInverse.injective ContinuousMultilinearMap.uncurry_curryLeft
    ext e : 1
    rw [← curryLeftSeries_apply, ← curryLeftSeries_apply]
    let pe : F := continuousMultilinearCurryFin1 𝕜 E F (p 1) e
    let qpe : G := continuousMultilinearCurryFin1 𝕜 F G (q 1) pe
    have hp1 : continuousMultilinearCurryFin1 𝕜 E G (q.taylorComp p 1) e = qpe := by simp [qpe, pe]
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

/-- Up to the order of smoothness, composing the formal Taylor series of `g ∘ f` with `p` agrees
with nested Taylor composition via Faà di Bruno and associativity. -/
theorem ContDiffAt.ftaylorSeries_comp_taylorComp {M : Type*} [NormedAddCommGroup M]
    [NormedSpace 𝕜 M] {n : ℕ∞ω} {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    (p : FormalMultilinearSeries 𝕜 M E) {m : ℕ} (hm : m ≤ n) :
    (ftaylorSeries 𝕜 (g ∘ f) x).taylorComp p m =
      (ftaylorSeries 𝕜 g (f x)).taylorComp ((ftaylorSeries 𝕜 f x).taylorComp p) m := by
  rw [← FormalMultilinearSeries.taylorComp_assoc]
  exact FormalMultilinearSeries.taylorComp_congr
    (fun k hk ↦ iteratedFDeriv_comp hg hf ((Nat.cast_le.mpr hk).trans hm))
    (fun _ _ _ ↦ rfl)

/-- Up to the order of smoothness, composing the formal Taylor series of a pair map
`y ↦ (f y, g y)` with `p` is the product of the individual Taylor compositions. -/
theorem ContDiffAt.ftaylorSeries_prodMk_taylorComp {M : Type*} [NormedAddCommGroup M]
    [NormedSpace 𝕜 M] {n : ℕ∞ω} {f : E → F} {g : E → G} {x : E}
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (p : FormalMultilinearSeries 𝕜 M E) {m : ℕ} (hm : m ≤ n) :
    (ftaylorSeries 𝕜 (fun y ↦ (f y, g y)) x).taylorComp p m =
      (((ftaylorSeries 𝕜 f x).taylorComp p).prod ((ftaylorSeries 𝕜 g x).taylorComp p)) m := by
  rw [← FormalMultilinearSeries.prod_taylorComp]
  exact FormalMultilinearSeries.taylorComp_congr
    (fun k hk ↦ iteratedFDeriv_prodMk hf hg ((Nat.cast_le.mpr hk).trans hm))
    (fun _ _ _ ↦ rfl)

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

/-- **Composites with bounded derivatives.** Let `f` be `Cᵐ`, bounded, with bounded derivatives
of order at most `m`, and let `g` be `Cᵐ` on a proper space. Then the `m`-th derivative of `g ∘ f`
is bounded: the derivatives of `g` are bounded on the compact ball containing the range of `f`. -/
theorem ContDiff.exists_norm_iteratedFDeriv_comp_le [ProperSpace F] {g : F → G} {f : E → F}
    {m : ℕ} (hg : ContDiff 𝕜 m g) (hf : ContDiff 𝕜 m f)
    (hb : ∀ n ≤ m, ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 n f x‖ ≤ C) :
    ∃ C, ∀ x, ‖iteratedFDeriv 𝕜 m (g ∘ f) x‖ ≤ C := by
  obtain ⟨R, hR⟩ := hb 0 (Nat.zero_le _)
  obtain ⟨A, -, hA⟩ := hg.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ
    (isCompact_closedBall (0 : F) R) (Set.subset_univ _)
  have hB (k : ℕ) : ∃ B, ∀ x, k ≤ m → ‖iteratedFDeriv 𝕜 k f x‖ ≤ B := by
    by_cases hk : k ≤ m
    · exact (hb k hk).imp fun B hB x _ ↦ hB x
    · exact ⟨0, fun _ hk' ↦ absurd hk' hk⟩
  choose B hB using hB
  set B' := ∑ k ∈ Finset.range (m + 1), |B k|
  refine ⟨max 1 B' ^ m * ∑ _c : OrderedFinpartition m, A, fun x ↦ ?_⟩
  have hx : f x ∈ Metric.closedBall (0 : F) R := by simpa using hR x
  refine (hg.contDiffAt.norm_iteratedFDeriv_comp_le_sum hf.contDiffAt (B := B')
    fun k _ hkm ↦ ?_).trans ?_
  · exact (hB k x hkm).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun k ↦ |B k|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (by omega))))
  · gcongr with c
    exact hA _ c.length_le _ hx
