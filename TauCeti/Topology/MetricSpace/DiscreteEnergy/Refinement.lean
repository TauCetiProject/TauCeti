/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.DiscreteEnergy.Basic
import TauCeti.Algebra.BigOperators.Fin

/-!
# Forgetting vertices of discrete paths

Selecting an increasing subsequence of the vertices of a metric path cannot increase
its discrete energy, when the retained vertices keep their original times. This is the
energy estimate for the vertex-forgetting maps between finite-dimensional approximations
of fixed-endpoint path spaces. No geodesic interpolation or mesh condition is needed.

`discreteEnergy_comp_le` covers arbitrary increasing subsequences, including those
that discard endpoints. `discreteEnergyForgetMap` restricts endpoint-preserving selections
to continuous maps of the existing open energy carriers. These maps preserve identities
and composition, so different subdivisions are related by maps rather than identified.

The estimate is the discrete Cauchy–Schwarz argument in J. Milnor, *Morse Theory*, §16,
with energy normalized by a factor of `½`. We use Mathlib's interval triangle inequality
and Engel form of Cauchy–Schwarz, and sum the estimates over the disjoint coarse edges.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {M : Type*}

section Metric

variable [PseudoMetricSpace M]

/-- The energy of the single edge joining the ends of a finite metric chain is no
larger than the sum of its edge energies. The sum here omits the normalization `½`. -/
theorem dist_sq_div_le_sum_Ico (t : ℕ → ℝ) (x : ℕ → M) {a b : ℕ} (hab : a ≤ b)
    (ht : StrictMonoOn t (Set.Icc a b)) :
    dist (x a) (x b) ^ 2 / (t b - t a) ≤
      ∑ i ∈ Finset.Ico a b, dist (x i) (x (i + 1)) ^ 2 / (t (i + 1) - t i) := by
  have hstep (i : ℕ) (hi : i ∈ Finset.Ico a b) : 0 < t (i + 1) - t i := by
    obtain ⟨hai, hib⟩ := Finset.mem_Ico.mp hi
    exact sub_pos.mpr (ht ⟨hai, hib.le⟩ ⟨by omega, by omega⟩ (by omega))
  have hCS := Finset.sq_sum_div_le_sum_sq_div (Finset.Ico a b)
    (fun i ↦ dist (x i) (x (i + 1))) hstep
  rw [Finset.sum_Ico_sub t hab] at hCS
  refine le_trans ?_ hCS
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ dist_nonneg (dist_le_Ico_sum_dist x hab) 2)
    (sub_nonneg.mpr (ht.monotoneOn ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))

/-- Selecting any increasing subsequence of vertices, with their original times,
does not increase discrete energy. Endpoints need not be retained. -/
theorem discreteEnergy_comp_le {m n : ℕ} {t : Fin (n + 1) → ℝ}
    (ht : StrictMono t) (x : Fin (n + 1) → M)
    (r : Fin (m + 1) ↪o Fin (n + 1)) :
    discreteEnergy (t ∘ r) (x ∘ r) ≤ discreteEnergy t x := by
  -- Extend the finite tuples only to apply interval-sum lemmas on natural numbers.
  let T : ℕ → ℝ := fun k ↦ t (Fin.ofNat (n + 1) k)
  let X : ℕ → M := fun k ↦ x (Fin.ofNat (n + 1) k)
  let e : ℕ → ℝ := fun k ↦ dist (X k) (X (k + 1)) ^ 2 / (T (k + 1) - T k)
  have hT : StrictMonoOn T (Set.Icc 0 n) := by
    intro i hi j hj hij
    have hi' : i < n + 1 := Nat.lt_succ_of_le hi.2
    have hj' : j < n + 1 := Nat.lt_succ_of_le hj.2
    dsimp only [T]
    apply ht
    simpa only [Fin.lt_def, Fin.val_ofNat, Nat.mod_eq_of_lt hi',
      Nat.mod_eq_of_lt hj'] using hij
  have hnat (i : Fin (n + 1)) : Fin.ofNat (n + 1) i.val = i := by simp
  have he (i : Fin n) : e i.val =
      dist (x i.castSucc) (x i.succ) ^ 2 / (t i.succ - t i.castSucc) := by
    have h₁ : Fin.ofNat (n + 1) i.val = i.castSucc := hnat i.castSucc
    have h₂ : Fin.ofNat (n + 1) (i.val + 1) = i.succ := by
      apply Fin.ext
      simp [Nat.mod_eq_of_lt (by omega : i.val + 1 < n + 1)]
    simp only [e, X, T, h₁, h₂]
  -- Each coarse edge is bounded by the energy of the fine block that it spans.
  have hblock (i : Fin m) :
      dist (x (r i.castSucc)) (x (r i.succ)) ^ 2 /
          (t (r i.succ) - t (r i.castSucc)) ≤
        ∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k := by
    have hab := r.strictMono i.castSucc_lt_succ
    have h := dist_sq_div_le_sum_Ico T X (Fin.le_iff_val_le_val.mp hab.le)
      (hT.mono fun k hk ↦ ⟨Nat.zero_le _, hk.2.trans (r i.succ).is_le⟩)
    simpa only [T, X, hnat] using h
  -- Adjacent blocks telescope. Any discarded initial or final block has nonnegative energy.
  have hsum : (∑ i : Fin m,
      ∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k) =
      ∑ k ∈ Finset.Ico (r 0).val (r (Fin.last m)).val, e k := by
    simp_rw [Finset.sum_Ico_eq_sub e (r.monotone (Fin.castSucc_le_succ _))]
    rw [Finset.sum_Ico_eq_sub e (r.monotone (Fin.zero_le _))]
    exact Fin.sum_univ_succ_sub_castSucc (fun i ↦ ∑ k ∈ Finset.range (r i).val, e k)
  have hnonneg (k : ℕ) (hk : k < n) : 0 ≤ e k := by
    exact div_nonneg (sq_nonneg _) (sub_nonneg.mpr
      (hT.monotoneOn ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)))
  have hsub : (∑ k ∈ Finset.Ico (r 0).val (r (Fin.last m)).val, e k) ≤
      ∑ k ∈ Finset.range n, e k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun k hk ↦ Finset.mem_range.mpr ((Finset.mem_Ico.mp hk).2.trans_le
        (r (Fin.last m)).is_le)) (fun k hk _ ↦ hnonneg k (Finset.mem_range.mp hk))
  have h := (Finset.sum_le_sum fun i _ ↦ hblock i).trans (hsum.trans_le hsub)
  rw [← Fin.sum_univ_eq_sum_range] at h
  simp only [he] at h
  simpa only [discreteEnergy_def, Function.comp_apply] using
    mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)

end Metric

section FixedEndpoints

variable {l m n : ℕ}

/-- Retain the selected interior vertices of a fixed-endpoint tuple. The selected
indices include two endpoint slots; endpoint preservation is imposed by the theorems
that use this map, not by its definition. -/
def discreteEnergyForget (r : Fin (m + 2) ↪o Fin (n + 2)) (p q : M)
    (x : Fin n → M) : Fin m → M :=
  fun j ↦ (Fin.cons p (Fin.snoc x q) : Fin (n + 2) → M) (r j.castSucc.succ)

/-- The retained interior vertex at an index is the corresponding fine vertex. -/
@[simp]
theorem discreteEnergyForget_apply (r : Fin (m + 2) ↪o Fin (n + 2)) (p q : M)
    (x : Fin n → M) (j : Fin m) :
    discreteEnergyForget r p q x j =
      (Fin.cons p (Fin.snoc x q) : Fin (n + 2) → M) (r j.castSucc.succ) := (rfl)

/-- Reattaching the endpoints to the retained interior tuple gives precisely the
selected subsequence of the full fine tuple. -/
theorem cons_snoc_discreteEnergyForget (r : Fin (m + 2) ↪o Fin (n + 2))
    (h0 : r 0 = 0) (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (p q : M) (x : Fin n → M) :
    Fin.cons p (Fin.snoc (discreteEnergyForget r p q x) q) =
      Fin.cons p (Fin.snoc x q) ∘ r := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [h0]
  · refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [hlast]
    · simp

/-- Vertex-forgetting is continuous in all interior vertices. -/
@[fun_prop]
theorem continuous_discreteEnergyForget [TopologicalSpace M]
    (r : Fin (m + 2) ↪o Fin (n + 2)) (p q : M) :
    Continuous (discreteEnergyForget r p q) := by
  unfold discreteEnergyForget
  fun_prop

/-- Retaining every vertex is the identity. -/
@[simp]
theorem discreteEnergyForget_refl (p q : M) (x : Fin n → M) :
    discreteEnergyForget (RelEmbedding.refl (· ≤ · : Fin (n + 2) → Fin (n + 2) → Prop))
      p q x = x := by
  ext j
  simp

/-- Successive vertex-forgetting agrees with selecting the composite subsequence. -/
@[simp]
theorem discreteEnergyForget_trans (r : Fin (m + 2) ↪o Fin (n + 2))
    (s : Fin (l + 2) ↪o Fin (m + 2)) (p q : M) (x : Fin n → M) :
    discreteEnergyForget s p q (discreteEnergyForget r p q x) =
      discreteEnergyForget (s.trans r) p q x := by
  ext j
  -- An increasing selection sends every interior index to an interior index.
  have hpos : 0 < s j.castSucc.succ :=
    (Fin.zero_le (s 0)).trans_lt (s.strictMono (Fin.succ_pos _))
  have hlt : s j.castSucc.succ < Fin.last (m + 1) :=
    (s.strictMono (Fin.succ_lt_succ_iff.mpr j.castSucc_lt_last)).trans_le (Fin.le_last _)
  obtain ⟨k, hk⟩ := (s j.castSucc.succ).eq_succ_of_ne_zero (ne_of_gt hpos)
  obtain ⟨i, hi⟩ := k.eq_castSucc_of_ne_last (by
    intro h
    simp only [hk, h, Fin.succ_last, lt_self_iff_false] at hlt)
  simp only [discreteEnergyForget_apply, RelEmbedding.trans_apply, hk, ← hi,
    Fin.cons_succ, Fin.snoc_castSucc]

variable [PseudoMetricSpace M]

/-- Forgetting interior vertices, while retaining both endpoints and the original
times, cannot increase fixed-endpoint discrete energy. -/
theorem discreteEnergy_cons_snoc_discreteEnergyForget_le {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (x : Fin n → M) :
    discreteEnergy (t ∘ r) (Fin.cons p (Fin.snoc (discreteEnergyForget r p q x) q)) ≤
      discreteEnergy t (Fin.cons p (Fin.snoc x q)) := by
  rw [cons_snoc_discreteEnergyForget r h0 hlast]
  exact discreteEnergy_comp_le ht _ r

/-- Vertex-forgetting takes a strict energy sublevel into the corresponding coarse
sublevel. The cutoff is unchanged. -/
theorem mapsTo_discreteEnergyForget {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ) :
    Set.MapsTo (discreteEnergyForget r p q) (discreteEnergyStrictSublevel t p q c)
      (discreteEnergyStrictSublevel (t ∘ r) p q c) := by
  intro x hx
  exact mem_discreteEnergyStrictSublevel.mpr
    ((discreteEnergy_cons_snoc_discreteEnergyForget_le ht r h0 hlast p q x).trans_lt
      (mem_discreteEnergyStrictSublevel.mp hx))

/-- The continuous vertex-forgetting map between fixed-endpoint strict energy
sublevels. Neither an admissible mesh nor a choice of interpolating segments is needed. -/
def discreteEnergyForgetMap {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ) :
    C(discreteEnergyStrictSublevel t p q c, discreteEnergyStrictSublevel (t ∘ r) p q c) where
  toFun x := ⟨discreteEnergyForget r p q x, mapsTo_discreteEnergyForget ht r h0 hlast p q c x.prop⟩
  continuous_toFun :=
    ((continuous_discreteEnergyForget r p q).comp continuous_subtype_val).subtype_mk _

/-- The sublevel map has the same underlying vertex tuple as the ambient
vertex-forgetting map. -/
@[simp]
theorem discreteEnergyForgetMap_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ)
    (x : discreteEnergyStrictSublevel t p q c) :
    (discreteEnergyForgetMap ht r h0 hlast p q c x : Fin m → M) =
      discreteEnergyForget r p q x := (rfl)

/-- The identity selection induces the identity on the strict energy sublevel.

The time tuple `t ∘ RelEmbedding.refl _` is definitionally `t`, so the source and
target sublevels coincide. -/
@[simp]
theorem discreteEnergyForgetMap_refl {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (p q : M) (c : ℝ) :
    discreteEnergyForgetMap ht (RelEmbedding.refl (· ≤ ·)) (by simp) (by simp) p q c =
      ContinuousMap.id (discreteEnergyStrictSublevel t p q c) := by
  apply ContinuousMap.ext
  intro x
  exact (Subtype.ext ((discreteEnergyForgetMap_apply ht _ _ _ p q c x).trans
    (discreteEnergyForget_refl p q (x : Fin n → M)))).trans
      (ContinuousMap.id_apply x).symm

/-- The continuous sublevel maps commute with further vertex-forgetting.

The time tuples `(t ∘ r) ∘ s` and `t ∘ (s.trans r)` are definitionally equal, so
both sides have the same target sublevel. -/
@[simp]
theorem discreteEnergyForgetMap_trans {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (s : Fin (l + 2) ↪o Fin (m + 2))
    (hr0 : r 0 = 0) (hrlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (hs0 : s 0 = 0) (hslast : s (Fin.last (l + 1)) = Fin.last (m + 1))
    (p q : M) (c : ℝ) :
    (discreteEnergyForgetMap (ht.comp r.strictMono) s hs0 hslast p q c).comp
        (discreteEnergyForgetMap ht r hr0 hrlast p q c) =
      discreteEnergyForgetMap ht (s.trans r)
        (by simp only [RelEmbedding.trans_apply, hs0, hr0])
        (by simp only [RelEmbedding.trans_apply, hslast, hrlast]) p q c := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  calc
    _ = discreteEnergyForget s p q (discreteEnergyForget r p q x) := by
      rw [ContinuousMap.comp_apply, discreteEnergyForgetMap_apply,
        discreteEnergyForgetMap_apply]
    _ = discreteEnergyForget (s.trans r) p q x :=
      discreteEnergyForget_trans r s p q x
    _ = _ := (discreteEnergyForgetMap_apply ht (s.trans r) _ _ p q c x).symm

end FixedEndpoints

end TauCeti
