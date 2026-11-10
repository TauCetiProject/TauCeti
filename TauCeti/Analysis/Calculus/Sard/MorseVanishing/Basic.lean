/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Chart
import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Analysis.Calculus.Sard.MorseVanishing.Disk

/-! # The Morse vanishing lemma

Every subset `A` of `Fin n → ℝ` and every order `k` have a **Morse decomposition**: a countable
set together with countably many pieces, each carried by a `C¹` parametrized disk that is
antilipschitz on the closed unit ball, such that *every* `C^k` function vanishing on `A` is flat of
order `k` along the disk on each piece.

The proof is A. P. Morse's double induction on the pair `(dimension, order)`, in the `C^k`
formulation of A. Norton. Dimension reduction preserves the order of the vanishing-set
decomposition; it does not apply lower-dimensional Sard to a derivative stratum:

* order `0`, any dimension: uniform continuity on the compact body of a translated unit ball;
* dimension `0`, any order: the whole space is a point, so the set is countable;
* order `k → k + 1` in a fixed dimension: split `A` into the set `U` of points at which *every*
  `C^(k+1)` function vanishing on `A` is critical, and the rest.  On `U` the coordinates of the
  differential are `C^k` and vanish on `U`, so the order-`k` decomposition of `U` makes them flat
  of order `k`, and the mean value step `TauCeti.MorseSard.abs_sub_le_of_flat_fderiv` raises the
  order by one.
* dimension `n → n + 1` at the **same** order: near a point of the rest some `C^(k+1)` function
  vanishing on `A` has nonvanishing differential, so `A` lies locally on the graph of a `C^(k+1)`
  function of `n` coordinates (`TauCeti.MorseSard.exists_graph`); the decomposition of the
  preimage is pushed forward along the graph map, which is `1`-antilipschitz
  (`TauCeti.MorseSard.norm_sub_le_insertNth`), so no constant changes.  Second countability makes
  countably many of these neighbourhoods suffice.

Adapted from [KLS](https://github.com/human-ai-mathematics/kls-lean) at commit
`65810c73f9dd7945fc646ab484cb19d673f5291d`, `formalization/FunctionalInequalities/Analysis/Sard/`.
The decomposition follows A. Norton, *A critical set with nonnull image has large Hausdorff
dimension*, Trans. Amer. Math. Soc. 296 (1986), Section 4, in its integer-regularity case.
-/

public section

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace TauCeti.MorseSard

variable {n k : ℕ}

/-- A piece of a decomposition together with the parameter dimension and the map of the disk
carrying it. -/
private structure Piece (n : ℕ) where
  /-- The subset carried by the parametrized disk. -/
  carrier : Set (Fin n → ℝ)
  /-- The dimension of the parameter space. -/
  dimension : ℕ
  /-- The parametrization of the disk carrying the piece. -/
  parametrization : (Fin dimension → ℝ) → (Fin n → ℝ)

/-- The piece sits inside `A` and inside the body of its disk, and that disk is a disk. -/
private def Carries (A : Set (Fin n → ℝ)) (q : Piece n) : Prop :=
  q.carrier ⊆ A ∧ q.carrier ⊆ q.parametrization '' closedBall (0 : Fin q.dimension → ℝ) 1 ∧
    ∃ κ : ℝ, IsDisk q.parametrization κ

/-- `B` admits a Morse decomposition of order `k` **relative to** `A`: the pieces lie in `A`, and
every `C^k` function vanishing on `A` is flat of order `k` along the disk on each piece.  The
absolute statement is the case `B = A`. -/
private def HasDecompRel (k : ℕ) (A B : Set (Fin n → ℝ)) : Prop :=
  ∃ (A₀ : Set (Fin n → ℝ)) (P : Set (Piece n)), A₀.Countable ∧ P.Countable ∧
    B ⊆ A₀ ∪ ⋃ q ∈ P, q.carrier ∧ (∀ q ∈ P, Carries A q) ∧
    ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ k f → (∀ x ∈ A, f x = 0) → ∀ q ∈ P,
      FlatAlong q.parametrization q.carrier k f

namespace HasDecompRel

/-- A relative Morse decomposition covers every subset of the set it covers. -/
private theorem mono_right {A B B' : Set (Fin n → ℝ)} (h : HasDecompRel k A B) (hB : B' ⊆ B) :
    HasDecompRel k A B' := by
  obtain ⟨A₀, P, hA₀, hP, hcov, hcar, hflat⟩ := h
  exact ⟨A₀, P, hA₀, hP, hB.trans hcov, hcar, hflat⟩

end HasDecompRel

/-- A countable union of relative decompositions is a relative decomposition. -/
private theorem hasDecompRel_iUnion {A : Set (Fin n → ℝ)} {ι : Type*} {I : Set ι}
    {B : ι → Set (Fin n → ℝ)} (hI : I.Countable) (h : ∀ i ∈ I, HasDecompRel k A (B i)) :
    HasDecompRel k A (⋃ i ∈ I, B i) := by
  classical
  have := hI.to_subtype
  choose A₀ P hA₀ hP hcov hcar hflat using fun i : ↥I => h i i.2
  refine ⟨⋃ i : ↥I, A₀ i, ⋃ i : ↥I, P i, countable_iUnion hA₀, countable_iUnion hP, ?_, ?_, ?_⟩
  · refine iUnion₂_subset fun i hi x hx => ?_
    rcases hcov ⟨i, hi⟩ hx with h1 | h1
    · exact Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, h1⟩)
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp h1
      exact Or.inr (mem_iUnion₂.mpr ⟨q, mem_iUnion.mpr ⟨⟨i, hi⟩, hq⟩, hxq⟩)
  · intro q hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact hcar i q hi
  · intro f hf hf0 q hq
    obtain ⟨i, hi⟩ := mem_iUnion.mp hq
    exact hflat i f hf hf0 q hi

/-- Two relative Morse decompositions over the same vanishing set can be united. -/
private theorem HasDecompRel.union {A B₁ B₂ : Set (Fin n → ℝ)} (h₁ : HasDecompRel k A B₁)
    (h₂ : HasDecompRel k A B₂) : HasDecompRel k A (B₁ ∪ B₂) := by
  classical
  have hcov : B₁ ∪ B₂ ⊆ ⋃ i ∈ (univ : Set Bool), (fun b => if b then B₁ else B₂) i := by
    rintro x (hx | hx)
    · exact mem_iUnion₂.mpr ⟨true, mem_univ _, by simpa using hx⟩
    · exact mem_iUnion₂.mpr ⟨false, mem_univ _, by simpa using hx⟩
  refine (hasDecompRel_iUnion countable_univ ?_).mono_right hcov
  rintro (_ | _) _
  · simpa using h₂
  · simpa using h₁

/-! ### The two bases of the double induction -/

/-- Dimension zero: the whole space is a point, so every set is countable. -/
private theorem hasDecompRel_dim_zero (k : ℕ) (A : Set (Fin 0 → ℝ)) : HasDecompRel k A A := by
  refine ⟨A, ∅, (Set.toFinite A).countable, countable_empty, fun x hx => Or.inl hx, ?_, ?_⟩
  · simp
  · simp

/--
Order zero, any dimension: uniform continuity on the compact body of a translated closed unit
ball.  The disks are the translations `a ↦ c + a` with integer centres, which are isometries. -/
private theorem hasDecompRel_order_zero (A : Set (Fin n → ℝ)) : HasDecompRel 0 A A := by
  classical
  set P : Set (Piece n) :=
    Set.range
      (fun c : Fin n → ℤ =>
        (⟨A ∩ closedBall (fun j => (c j : ℝ)) 1,
            n, fun a : Fin n → ℝ => (fun j => (c j : ℝ)) + a⟩ : Piece n)) with
    hPdef
  refine ⟨∅, P, countable_empty, countable_range _, ?_, ?_, ?_⟩
  · intro x hx
    refine Or.inr (mem_iUnion₂.mpr ⟨_, ⟨fun j => ⌊x j⌋, rfl⟩, hx, ?_⟩)
    rw [mem_closedBall_iff_norm]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
    have h1 : (⌊x j⌋ : ℝ) ≤ x j := Int.floor_le _
    have h2 : x j < (⌊x j⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  · rintro q ⟨c, rfl⟩
    refine ⟨inter_subset_left, ?_, 1, isDisk_iff.mpr ⟨?_, zero_le_one, ?_⟩⟩
    · intro x hx
      refine ⟨x - fun j => (c j : ℝ), ?_, by simp⟩
      rw [mem_closedBall_iff_norm, sub_zero]
      exact mem_closedBall_iff_norm.mp hx.2
    · exact contDiff_const.add contDiff_id
    · intro a _ b _
      simp
  · rintro f hf hf0 q ⟨c, rfl⟩
    apply flatAlong_iff.mpr
    intro ε hε
    have hfc : Continuous f := contDiff_zero.mp hf
    obtain ⟨δ, hδ, hδspec⟩ :=
      Metric.uniformContinuousOn_iff_le.mp
        ((isCompact_closedBall (fun j => (c j : ℝ)) 1).uniformContinuousOn_of_continuous
          hfc.continuousOn)
        ε hε
    refine ⟨δ, hδ, ?_⟩
    intro a ha b hb haS _ hab s hs
    set cc : Fin n → ℝ := fun j => (c j : ℝ) with hccdef
    have hmem : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → cc + (a + t • (b - a)) ∈ closedBall cc 1 := by
      intro t ht
      rw [mem_closedBall_iff_norm]
      have hm := (convex_closedBall (0 : Fin n → ℝ) 1).add_smul_sub_mem ha hb ht
      simpa only [mem_closedBall_iff_norm, add_sub_cancel_left, sub_zero] using hm
    have hpt : cc + (a + s • (b - a)) ∈ closedBall cc 1 := hmem s hs
    have ha' : cc + a ∈ closedBall cc 1 := by
      have := hmem 0 ⟨le_refl 0, zero_le_one⟩
      simpa using this
    have hdist : dist (cc + (a + s • (b - a))) (cc + a) ≤ δ := by
      have heq : cc + (a + s • (b - a)) - (cc + a) = s • (b - a) := by module
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      have h1 : ‖b - a‖ = ‖cc + a - (cc + b)‖ := by
        rw [show cc + a - (cc + b) = -(b - a) by module, norm_neg]
      calc
        s * ‖b - a‖ ≤ 1 * ‖b - a‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖cc + a - (cc + b)‖ := by rw [one_mul, h1]
        _ ≤ δ := hab.le
    have hzero : f (cc + a) = 0 := hf0 _ haS.1
    have := hδspec _ hpt _ ha' hdist
    rw [Real.dist_eq, hzero, sub_zero] at this
    simpa using this

/-! ### The critical step: raising the order -/

/-- Raising the order on the set where every `C^(k+1)` function vanishing on `A` is critical.
The coordinates of the differential are `C^k` and vanish there, so the order-`k` decomposition
makes them flat of order `k`, and the mean value step raises the order. -/
private theorem hasDecompRel_succ_of_critical {A U : Set (Fin n → ℝ)} (hUA : U ⊆ A)
    (hcrit : ∀ x ∈ U, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ (k + 1) f →
      (∀ y ∈ A, f y = 0) → fderiv ℝ f x = 0)
    (h : HasDecompRel k U U) : HasDecompRel (k + 1) A U := by
  obtain ⟨A₀, P, hA₀, hP, hcov, hcar, hflat⟩ := h
  refine ⟨A₀, P, hA₀, hP, hcov,
    fun q hq => ⟨(hcar q hq).1.trans hUA, (hcar q hq).2.1, (hcar q hq).2.2⟩, ?_⟩
  intro f hf hf0 q hq
  obtain ⟨hq1, _, κ, hdisk⟩ := hcar q hq
  have hfd : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hcoord : ∀ j : Fin n,
      FlatAlong q.parametrization q.carrier k fun x => fderiv ℝ f x (Pi.single j (1 : ℝ)) := by
    intro j
    refine hflat _ (hfd.clm_apply contDiff_const) (fun x hx => ?_) q hq
    rw [hcrit x hx f hf hf0]
    simp
  apply flatAlong_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδspec⟩ := abs_sub_le_of_flat_fderiv hdisk hdiff hcoord ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a ha b hb haS hbS hab s hs
  have hzero : f (q.parametrization a) = 0 := hf0 _ (hUA (hq1 haS))
  have := hδspec a ha b hb haS hbS hab s hs
  rwa [hzero, sub_zero] at this

/-! ### The regular step: pushing a decomposition forward along a graph chart -/

/-- Pushing a decomposition of the preimage forward along a `C^k` graph map.  The graph map is
injective and `1`-antilipschitz, so every constant of the decomposition is preserved. -/
private theorem hasDecompRel_graph {A N : Set (Fin (n + 1) → ℝ)} (hk : 1 ≤ k) (i : Fin (n + 1))
    {θ : (Fin n → ℝ) → ℝ} (hθ : ContDiff ℝ k θ)
    (hN : ∀ x ∈ A, x ∈ N →
      x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x))
    (h : HasDecompRel k ((fun y => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) ⁻¹' A)
      ((fun y => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) ⁻¹' A)) :
    HasDecompRel k A (A ∩ N) := by
  classical
  set Γ : (Fin n → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => Fin.insertNth (α := fun _ => ℝ) i (θ y) y with hΓdef
  have hΓinj : Function.Injective Γ := fun _ _ h ↦ (Fin.insertNth_injective2 h).2
  have hΓk : ContDiff ℝ k Γ := hθ.finInsertNth i contDiff_id
  have hΓ1 : ContDiff ℝ 1 Γ := hΓk.of_le (by exact_mod_cast hk)
  have hΓanti : ∀ a b : Fin n → ℝ, ‖a - b‖ ≤ ‖Γ a - Γ b‖ := norm_sub_le_insertNth i θ
  obtain ⟨A₀, P, hA₀, hP, hcov, hcar, hflat⟩ := h
  refine ⟨Γ '' A₀,
    (fun q' : Piece n ↦
      (⟨Γ '' q'.carrier, q'.dimension, Γ ∘ q'.parametrization⟩ : Piece (n + 1))) '' P,
    hA₀.image _, hP.image _, ?_, ?_, ?_⟩
  · rintro x ⟨hxA, hxN⟩
    have hx : x = Γ (Fin.removeNth i x) := hN x hxA hxN
    have hmem : Fin.removeNth (α := fun _ => ℝ) i x ∈ Γ ⁻¹' A := by
      simp only [mem_preimage]
      rw [← hx]
      exact hxA
    rcases hcov hmem with h1 | h1
    · exact Or.inl ⟨_, h1, hx.symm⟩
    · obtain ⟨q', hq', hmq'⟩ := mem_iUnion₂.mp h1
      exact Or.inr (mem_iUnion₂.mpr ⟨_, ⟨q', hq', rfl⟩, ⟨_, hmq', hx.symm⟩⟩)
  · rintro q ⟨q', hq', rfl⟩
    obtain ⟨h1, h2, κ, hdisk⟩ := hcar q' hq'
    obtain ⟨hd1, hd2, hd3⟩ := isDisk_iff.mp hdisk
    refine ⟨?_, ?_, κ, isDisk_iff.mpr ⟨?_, hd2, ?_⟩⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact h1 hy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := h2 hy
      exact ⟨z, hz, rfl⟩
    · exact hΓ1.comp hd1
    · intro a ha b hb
      exact (hd3 a ha b hb).trans
        (mul_le_mul_of_nonneg_left (hΓanti _ _) hd2)
  · rintro f hf hf0 q ⟨q', hq', rfl⟩
    have hfΓ : ContDiff ℝ k (f ∘ Γ) := hf.comp hΓk
    have hflat' := hflat (f ∘ Γ) hfΓ (fun y hy => hf0 _ hy) q' hq'
    apply flatAlong_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδspec⟩ := (flatAlong_iff.mp hflat') ε hε
    refine ⟨δ, hδ, ?_⟩
    intro a ha b hb haS hbS hab s hs
    have hmem : ∀ c : Fin q'.dimension → ℝ,
        Γ (q'.parametrization c) ∈ Γ '' q'.carrier → q'.parametrization c ∈ q'.carrier := by
      intro c hc
      obtain ⟨z, hz, hzeq⟩ := hc
      rwa [hΓinj hzeq] at hz
    have hab' : ‖q'.parametrization a - q'.parametrization b‖ < δ := lt_of_le_of_lt (hΓanti _ _) hab
    have hmain := hδspec a ha b hb (hmem a haS) (hmem b hbS) hab' s hs
    refine hmain.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hε.le
    exact pow_le_pow_left₀ (norm_nonneg _) (hΓanti _ _) k

/-! ### The Morse vanishing lemma -/

/-- **The Morse vanishing lemma.**  Every subset of `Fin n → ℝ` has a Morse decomposition of
every order.  Double induction on the order and then on the dimension; the order never drops. -/
private theorem hasDecompRel_self : ∀ (k n : ℕ) (A : Set (Fin n → ℝ)), HasDecompRel k A A := by
  intro k
  induction k with
  | zero => exact fun n A => hasDecompRel_order_zero A
  | succ k ihk =>
    intro n
    induction n with
    | zero => exact fun A => hasDecompRel_dim_zero _ A
    | succ m ihm =>
      intro A
      classical
      -- the set of points at which every `C^(k+1)` function vanishing on `A` is critical
      set U : Set (Fin (m + 1) → ℝ) :=
        {x | x ∈ A ∧ ∀ f : (Fin (m + 1) → ℝ) → ℝ, ContDiff ℝ (k + 1) f →
          (∀ y ∈ A, f y = 0) → fderiv ℝ f x = 0} with hUdef
      have hUA : U ⊆ A := fun x hx => hx.1
      have hUdec : HasDecompRel (k + 1) A U :=
        hasDecompRel_succ_of_critical hUA (fun x hx => hx.2) (ihk (m + 1) U)
      -- the remaining points lie locally on a `C^(k+1)` graph
      have hV : ∀ x₀ : ↥(A \ U), ∃ N : Set (Fin (m + 1) → ℝ), IsOpen N ∧ (x₀ : Fin (m + 1) → ℝ) ∈ N
          ∧ HasDecompRel (k + 1) A (A ∩ N) := by
        rintro ⟨x₀, hx₀A, hx₀U⟩
        have hex : ∃ g : (Fin (m + 1) → ℝ) → ℝ, ContDiff ℝ (k + 1) g ∧ (∀ y ∈ A, g y = 0) ∧
            fderiv ℝ g x₀ ≠ 0 := by
          by_contra hcon
          push Not at hcon
          exact hx₀U ⟨hx₀A, fun f hf hf0 => hcon f hf hf0⟩
        obtain ⟨g, hgc, hg0, hgd⟩ := hex
        obtain ⟨i, θ, hθ, hev⟩ :=
          exists_graph (k := k + 1) (by omega) hgc (hg0 x₀ hx₀A) hgd
        obtain ⟨N, hNsub, hNopen, hNmem⟩ := _root_.mem_nhds_iff.mp hev
        refine ⟨N, hNopen, hNmem, ?_⟩
        refine hasDecompRel_graph (by omega) i hθ (fun x hxA hxN => hNsub hxN (hg0 x hxA)) ?_
        exact ihm _
      choose N hNopen hNmem hNdec using hV
      obtain ⟨T, hT, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable N hNopen
      have hcover : A \ U ⊆ ⋃ i ∈ T, A ∩ N i := by
        intro x hx
        have hxmem : x ∈ ⋃ i, N i := mem_iUnion.mpr ⟨⟨x, hx⟩, hNmem _⟩
        rw [← hTeq] at hxmem
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxmem
        exact mem_iUnion₂.mpr ⟨i, hi, hx.1, hxi⟩
      have hVdec : HasDecompRel (k + 1) A (A \ U) :=
        (hasDecompRel_iUnion hT fun i _ => hNdec i).mono_right hcover
      exact (hUdec.union hVdec).mono_right (fun x hx => by
        by_cases hxU : x ∈ U
        · exact Or.inl hxU
        · exact Or.inr ⟨hx, hxU⟩)

/-- **The Morse criticality lemma.**  The set on which a `C^(k+1)` function is critical is covered
by a countable set and countably many bounded pieces, on each of which the function has a uniform
`o(‖y - x‖ ^ (k + 1))` modulus.  Neither the set nor the pieces are assumed measurable. -/
theorem _root_.TauCeti.exists_cover_of_critical (A : Set (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ (k + 1) f) (hA : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∃ (A₀ : Set (Fin n → ℝ)) (P : Set (Set (Fin n → ℝ))), A₀.Countable ∧ P.Countable ∧
      A ⊆ A₀ ∪ ⋃₀ P ∧
      ∀ S ∈ P, Bornology.IsBounded S ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ (k + 1) := by
  classical
  obtain ⟨A₀, P, hA₀, hP, hcov, hcar, hflat⟩ := MorseSard.hasDecompRel_self k n A
  have hfd : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  refine ⟨A₀, (fun q : MorseSard.Piece n => q.carrier) '' P, hA₀, hP.image _, ?_, ?_⟩
  · rw [sUnion_image]
    exact hcov
  · rintro S ⟨q, hq, rfl⟩
    obtain ⟨hq1, hq2, κ, hdisk⟩ := hcar q hq
    have hbody : IsCompact (q.parametrization '' closedBall (0 : Fin q.dimension → ℝ) 1) :=
      (isCompact_closedBall _ _).image ((isDisk_iff.mp hdisk).1.continuous)
    refine ⟨hbody.isBounded.subset hq2, ?_⟩
    have hcoord : ∀ j : Fin n,
        MorseSard.FlatAlong q.parametrization q.carrier k
          fun x ↦ fderiv ℝ f x (Pi.single j (1 : ℝ)) := by
      intro j
      refine hflat _ (hfd.clm_apply contDiff_const) (fun x hx => ?_) q hq
      rw [hA x hx]
      simp
    intro ε hε
    obtain ⟨δ, hδ, hδspec⟩ := MorseSard.abs_sub_le_of_flat_fderiv hdisk hdiff hcoord ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := hq2 hx
    obtain ⟨b, hb, rfl⟩ := hq2 hy
    have hb' : a + (1 : ℝ) • (b - a) = b := by module
    have hlt : ‖q.parametrization a - q.parametrization b‖ < δ := by rwa [norm_sub_rev]
    have := hδspec a ha b hb hx hy hlt 1 ⟨zero_le_one, le_refl 1⟩
    rw [hb'] at this
    rw [norm_sub_rev]
    exact this

end TauCeti.MorseSard
