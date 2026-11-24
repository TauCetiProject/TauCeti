/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Combinatorics.NoncrossingPartition.Pairing
public import TauCeti.Probability.FreeProbability.Distribution.Basic
public import TauCeti.Probability.FreeProbability.Semicircular.Basic
import TauCeti.Analysis.StarAlgebra.GNS.Basic
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Semicircular systems

Let `φ : A →ₗ[R] R` be a linear functional on an algebra `A` over a commutative ring `R`. A family
`s : ι → A` is a *semicircular system with covariance `C : Matrix ι ι R`* for `φ` when `φ` is
normalised and the only nonvanishing joint free cumulants of positive order of the family are
those of order two, given by the covariance: `κ₂(s i, s j) = C i j`, and
`κ_n(s_{w 1}, …, s_{w n}) = 0` for every word `w` of length `n ≥ 1` with `n ≠ 2`.
Equivalently, by the moment–cumulant formula and Möbius uniqueness, `s` satisfies the algebraic
*Wick formula* over noncrossing pairings:

`φ (s (w 1) * ⋯ * s (w n)) = ∑_{P ∈ NC₂(n)} ∏_{(i, j) ∈ P} C (w i) (w j)`.

This is the free analogue of a centred Gaussian family with covariance `C`.

The joint distribution of a semicircular system is determined by its covariance, and every member
`s i` is semicircular of variance `C i i`. Real (or `R`-linear) changes of coordinates preserve
semicircular systems: if `t k = ∑ i, M i k • s i`, then `t` is a semicircular system with covariance
`Mᵀ * C * M`.

Semicircularity of each member does not determine the joint distribution; for a semicircular
system, freeness is the same as orthogonality. A semicircular system is freely independent exactly
when its covariance is diagonal, and a family is a semicircular system with diagonal covariance
`v` exactly when it is a free family of semicircular elements of variances `v i`. In particular,
a single element is a semicircular system exactly when it is semicircular.

No positivity, symmetry of `C`, or traciality of `φ` is assumed in the algebraic theory; when
`φ : A →ₚ[ℂ] ℂ` is a positive linear functional on a `StarOrderedRing` and the `s i` are
self-adjoint, positivity forces any real covariance `C` to be symmetric and positive semidefinite
(`TauCeti.IsSemicircularSystem.posSemidef_of_isSelfAdjoint`).

## Main definitions

* `TauCeti.IsSemicircularSystem φ s C` — `s` is a semicircular system with covariance `C` for `φ`.

## Main results

* `TauCeti.IsSemicircularSystem.apply_eq_zero`, `TauCeti.IsSemicircularSystem.apply_mul` — the
  members are centred, with second moments `φ (s i * s j) = C i j`.
* `TauCeti.IsSemicircularSystem.apply_prod`, `TauCeti.IsSemicircularSystem.apply_prod_ofFn`, and
  `TauCeti.isSemicircularSystem_iff_apply_prod_ofFn` — the algebraic Wick formula over noncrossing
  pairings and its converse characterizing semicircular systems.
* `TauCeti.IsSemicircularSystem.isSemicircular` — each member `s i` is semicircular of variance
  `C i i`.
* `TauCeti.IsSemicircularSystem.jointDistribution_eq` — the joint distribution of a semicircular
  system is determined by its covariance.
* `TauCeti.IsSemicircularSystem.comp` and `TauCeti.IsSemicircularSystem.sum_smul` — relabelling
  and linear changes of coordinates, with covariances `C.submatrix e e` and `Mᵀ * C * M`.
* `TauCeti.IsSemicircularSystem.isFreelyIndependentElements_iff` — a semicircular system is
  freely independent exactly when its covariance is diagonal.
* `TauCeti.isSemicircularSystem_diagonal_iff` — the semicircular systems with diagonal covariance
  `v` are the free families of semicircular elements of variances `v i`.
* `TauCeti.isSemicircularSystem_iff_isSemicircular` — a family indexed by a one-element type is a
  semicircular system exactly when its member is semicircular.
* `TauCeti.IsSemicircularSystem.posSemidef_of_isSelfAdjoint` — under a positive linear functional on
  a `StarOrderedRing`, a real covariance of a self-adjoint semicircular system is symmetric and
  positive semidefinite.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Definition 8.15 and
  Proposition 8.17 for semicircular families and their Wick formula, and Lecture 11 (Theorem 11.20
  for the generated-algebra test).
-/

public section

open Finset Matrix
open scoped ComplexOrder

namespace TauCeti

variable {R A B ι κ : Type*} [CommRing R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  {φ : A →ₗ[R] R} {s : ι → A} {C : Matrix ι ι R}

/-- A family `s` is a *semicircular system with covariance `C`* for the functional `φ` if `φ` is
normalised and the only nonvanishing joint free cumulants of `s` of positive order are those of
order two, `κ₂(s i, s j) = C i j`. -/
structure IsSemicircularSystem (φ : A →ₗ[R] R) (s : ι → A) (C : Matrix ι ι R) : Prop where
  /-- The functional is normalised. -/
  apply_one : φ 1 = 1
  /-- The second joint free cumulants are given by the covariance. -/
  freeCumulant_two (w : Fin 2 → ι) : freeCumulant φ (s ∘ w) univ = C (w 0) (w 1)
  /-- The joint free cumulants of every order `n ≠ 2`, `n ≥ 1`, vanish. -/
  freeCumulant_eq_zero {n : ℕ} (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) (w : Fin n → ι) :
    freeCumulant φ (s ∘ w) univ = 0

namespace IsSemicircularSystem

/-- The members of a semicircular system are centred. -/
theorem apply_eq_zero (h : IsSemicircularSystem φ s C) (i : ι) : φ (s i) = 0 := by
  simpa [univ_unique] using h.freeCumulant_eq_zero one_ne_zero (by decide) fun _ => i

/-- The second moments of a semicircular system are given by its covariance,
`φ (s i * s j) = C i j`. -/
theorem apply_mul (h : IsSemicircularSystem φ s C) (i j : ι) : φ (s i * s j) = C i j := by
  have hκ := h.freeCumulant_two ![i, j]
  have huniv : (univ : Finset (Fin 2)) = {0, 1} := by decide
  have h01 : (0 : Fin 2) < 1 := by decide
  rw [huniv, freeCumulant_pair φ _ h01] at hκ
  simpa [h.apply_eq_zero] using hκ

/-- The joint free cumulants of a semicircular system depend only on its covariance: two
semicircular systems with the same covariance, possibly in different algebras, have the same joint
free cumulant along every word `w`, including the empty word. -/
theorem freeCumulant_comp_eq {φ' : B →ₗ[R] R} {t : ι → B} (h : IsSemicircularSystem φ s C)
    (h' : IsSemicircularSystem φ' t C) {n : ℕ} (w : Fin n → ι) :
    freeCumulant φ (s ∘ w) univ = freeCumulant φ' (t ∘ w) univ := by
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [univ_eq_empty, freeCumulant_empty]
  rcases eq_or_ne n 2 with rfl | hn₂
  · rw [h.freeCumulant_two, h'.freeCumulant_two]
  · rw [h.freeCumulant_eq_zero hn₀ hn₂, h'.freeCumulant_eq_zero hn₀ hn₂]

/-- *The covariance determines the joint distribution*: two semicircular systems with the same
covariance, possibly in different algebras, have the same joint distribution. -/
theorem jointDistribution_eq {φ' : B →ₗ[R] R} {t : ι → B} (h : IsSemicircularSystem φ s C)
    (h' : IsSemicircularSystem φ' t C) : jointDistribution φ s = jointDistribution φ' t := by
  refine jointDistribution_eq_iff.2 fun w => ?_
  rcases eq_or_ne w.length 0 with hw | hw
  · simp [List.length_eq_zero_iff.1 hw, h.apply_one, h'.apply_one]
  -- Expand both moments by the moment–cumulant formula; the cumulants of every part agree.
  rw [← List.ofFn_getElem_eq_map, ← List.ofFn_getElem_eq_map,
    apply_prod_ofFn_eq_sum_prod_freeCumulant φ hw, apply_prod_ofFn_eq_sum_prod_freeCumulant φ' hw]
  refine sum_congr rfl fun π _ => prod_congr rfl fun X _ => ?_
  rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ _ X,
    freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ' _ X]
  exact h.freeCumulant_comp_eq h' fun k => w[(X.orderEmbOfFin rfl k : ℕ)]

/-- Each member `s i` of a semicircular system is semicircular of variance `C i i`. -/
theorem isSemicircular (h : IsSemicircularSystem φ s C) (i : ι) :
    IsSemicircular φ (s i) (C i i) := by
  refine (isSemicircular_iff_freeCumulant_const h.apply_one).2 fun n hn => ?_
  rcases eq_or_ne n 2 with rfl | hn₂
  · simpa [Function.comp_def] using h.freeCumulant_two fun _ => i
  · simpa [Function.comp_def, hn₂] using h.freeCumulant_eq_zero hn hn₂ fun _ => i

/-- *Relabelling*: a relabelled family `s ∘ e`, in particular a subfamily, of a semicircular
system with covariance `C` is a semicircular system with covariance `C.submatrix e e`. -/
theorem comp (h : IsSemicircularSystem φ s C) (e : κ → ι) :
    IsSemicircularSystem φ (s ∘ e) (C.submatrix e e) where
  apply_one := h.apply_one
  freeCumulant_two w := h.freeCumulant_two (e ∘ w)
  freeCumulant_eq_zero hn₀ hn₂ w := h.freeCumulant_eq_zero hn₀ hn₂ (e ∘ w)

/-- *Linear changes of coordinates*: if `s` is a semicircular system with covariance `C` and `M`
is a matrix, then the linear combinations `t k = ∑ i, M i k • s i` form a semicircular system with
covariance `Mᵀ * C * M`. -/
theorem sum_smul [Fintype ι] (h : IsSemicircularSystem φ s C) (M : Matrix ι κ R) :
    IsSemicircularSystem φ (fun k => ∑ i, M i k • s i) (Mᵀ * C * M) where
  apply_one := h.apply_one
  freeCumulant_two w := by
    classical
    rw [Function.comp_def, freeCumulant_sum_smul φ s, ← (finTwoArrowEquiv ι).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [h.freeCumulant_two, finTwoArrowEquiv_symm_apply, Fin.prod_univ_two,
      cons_val_zero, cons_val_one, Matrix.mul_apply, transpose_apply, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  freeCumulant_eq_zero hn₀ hn₂ w := by
    rw [Function.comp_def, freeCumulant_sum_smul φ s]
    simp [h.freeCumulant_eq_zero hn₀ hn₂]

/-- *Freeness is orthogonality*: a semicircular system is freely independent exactly when its
covariance is diagonal. -/
theorem isFreelyIndependentElements_iff (h : IsSemicircularSystem φ s C) :
    IsFreelyIndependentElements φ s ↔ ∀ i j, i ≠ j → C i j = 0 := by
  rw [isFreelyIndependentElements_iff_freeCumulant_eq_zero h.apply_one]
  refine ⟨fun hfree i j hij => ?_, fun hC n w k k' hkk' => ?_⟩
  · simpa [h.freeCumulant_two] using hfree 2 ![i, j] 0 1 hij
  -- Only the cumulants of order two can be mixed, and these are off-diagonal entries of `C`.
  rcases eq_or_ne n 2 with rfl | hn₂
  · rw [h.freeCumulant_two]
    refine hC _ _ fun h01 => hkk' ?_
    fin_cases k <;> fin_cases k' <;> simp [h01]
  · exact h.freeCumulant_eq_zero (fun hn => (Fin.cast hn k).elim0) hn₂ w

/-- Along any nonempty finite set `B` of positions in a linear order, the joint free cumulant of a
semicircular system `s` with covariance `C` along `w : α → ι` is `C (w (min B)) (w (max B))` when
`#B = 2` and `0` otherwise. -/
theorem freeCumulant_comp {α : Type*} [LinearOrder α] (h : IsSemicircularSystem φ s C)
    (w : α → ι) {B : Finset α} (hB : B.Nonempty) :
    freeCumulant φ (s ∘ w) B =
      if #B = 2 then C (w (B.min' hB)) (w (B.max' hB)) else 0 := by
  split_ifs with hcard
  · conv_lhs => rw [← image_orderEmbOfFin_univ B hcard]
    have h0 : B.orderEmbOfFin hcard 0 = B.min' hB := orderEmbOfFin_zero hcard (by omega)
    have h1 : B.orderEmbOfFin hcard 1 = B.max' hB := orderEmbOfFin_last hcard (by omega)
    rw [← freeCumulant_comp_of_strictMonoOn φ
        ((B.orderEmbOfFin hcard).strictMono.strictMonoOn _) (s ∘ w),
      Function.comp_assoc, h.freeCumulant_two]
    simp [h0, h1]
  · rw [freeCumulant_eq_freeCumulant_comp_orderEmbOfFin φ (s ∘ w) B, Function.comp_assoc,
      h.freeCumulant_eq_zero hB.card_pos.ne' hcard]

/-- **Algebraic Wick formula** for a semicircular system along a finite ordered index set `t`:
`φ (∏_{x ∈ t} s (w x)) = ∑_{P ∈ NC₂(t)} ∏_{(x, y) ∈ P} C (w x) (w y)`. -/
theorem apply_prod {α : Type*} [LinearOrder α] (h : IsSemicircularSystem φ s C) (t : Finset α)
    (w : α → ι) :
    φ ((t.sort.map (s ∘ w)).prod) =
      ∑ P : {P : NoncrossingPartition t // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, C (w p.1) (w p.2) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · rw [sort_empty, List.map_nil, List.prod_nil, h.apply_one,
      NoncrossingPartition.sum_isPairing_prod_orderedPairs_empty fun x y => C (w x) (w y)]
  rw [apply_prod_eq_sum_prod_freeCumulant φ (s ∘ w) ht]
  refine NoncrossingPartition.sum_prod_eq_sum_isPairing_prod_orderedPairs
    (fun x y => C (w x) (w y)) (fun {_ _} _ _ hij => ?_) fun B _ hB hcard => ?_
  · rw [h.freeCumulant_comp w ⟨_, mem_insert_self _ _⟩]
    simp [card_pair hij.ne, min_eq_left hij.le, max_eq_right hij.le]
  · simp [h.freeCumulant_comp w hB, hcard]

/-- **Algebraic Wick formula** for words indexed by `Fin n` in a semicircular system. -/
theorem apply_prod_ofFn (h : IsSemicircularSystem φ s C) {n : ℕ} (w : Fin n → ι) :
    φ (List.ofFn (s ∘ w)).prod =
      ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, C (w p.1) (w p.2) := by
  rw [List.ofFn_eq_map, ← Fin.sort_univ]
  exact h.apply_prod univ w

/-- Moments of odd length in a semicircular system vanish. -/
theorem apply_prod_eq_zero_of_odd {α : Type*} [LinearOrder α] (h : IsSemicircularSystem φ s C)
    {t : Finset α} (ht : Odd #t) (w : α → ι) :
    φ ((t.sort.map (s ∘ w)).prod) = 0 := by
  rw [h.apply_prod, NoncrossingPartition.sum_isPairing_eq_zero ht]

end IsSemicircularSystem

/-- Target block weight for the converse of the algebraic Wick formula. -/
private def wickBlockWeight (C : Matrix ι ι R) {α : Type*} [LinearOrder α] (w : α → ι)
    (B : Finset α) : R :=
  if hB : B.Nonempty then if #B = 2 then C (w (B.min' hB)) (w (B.max' hB)) else 0 else 0

private theorem sum_prod_wickBlockWeight_eq {α : Type*} [LinearOrder α] (s : Finset α)
    (w : α → ι) :
    (∑ π : NoncrossingPartition s, ∏ B ∈ π.val.parts, wickBlockWeight C w B) =
      ∑ P : {P : NoncrossingPartition s // P.val.IsPairing},
        ∏ p ∈ P.val.val.orderedPairs, C (w p.1) (w p.2) := by
  refine NoncrossingPartition.sum_prod_eq_sum_isPairing_prod_orderedPairs
    (fun i j => C (w i) (w j)) (fun {i j} _ _ hij => ?_) fun B _ hB hcard => ?_
  · have hne : ({i, j} : Finset α).Nonempty := ⟨i, mem_insert_self i _⟩
    simp [wickBlockWeight, hne, card_pair hij.ne, min_eq_left hij.le, max_eq_right hij.le]
  · simp [wickBlockWeight, hB, hcard]

private theorem wickBlockWeight_image_orderEmbedding {α β : Type*} [LinearOrder α] [LinearOrder β]
    (w : α → ι) (e : β ↪o α) (D : Finset β) :
    wickBlockWeight C w (D.image e) = wickBlockWeight C (w ∘ e) D := by
  by_cases hD : D.Nonempty
  · simp [wickBlockWeight, hD, hD.image, card_image_of_injective D e.injective,
      min'_image e.monotone, max'_image e.monotone]
  · simp [wickBlockWeight, not_nonempty_iff_eq_empty.1 hD]

private theorem freeCumulant_eq_wickBlockWeight_of_apply_prod_ofFn
    (hprod : ∀ {n : ℕ} (w : Fin n → ι),
      φ (List.ofFn (s ∘ w)).prod =
        ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.val.IsPairing},
          ∏ p ∈ P.val.val.orderedPairs, C (w p.1) (w p.2))
    {n : ℕ} (hn : n ≠ 0) (w : Fin n → ι) :
    freeCumulant φ (s ∘ w) univ = wickBlockWeight C w univ := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  refine freeCumulant_eq_of_forall_apply_prod_eq_sum_prod φ (s ∘ w) (wickBlockWeight C w)
    (fun X _ _ => ?_) univ_nonempty
  set e := X.orderEmbOfFin rfl
  have hlist : X.sort.map (s ∘ w) = List.ofFn (s ∘ (w ∘ e)) := by
    rw [← listMap_orderEmbOfFin_finRange X rfl, List.map_map, List.ofFn_eq_map]
    rfl
  rw [hlist, hprod (w ∘ e), ← sum_prod_wickBlockWeight_eq]
  have hmono : MonotoneOn e ((univ : Finset (Fin #X)) : Set (Fin #X)) :=
    e.strictMono.monotone.monotoneOn _
  have hbij : Function.Bijective (NoncrossingPartition.comap hmono) :=
    ⟨(NoncrossingPartition.comap hmono).injective, fun σ =>
      NoncrossingPartition.exists_comap_eq_iff.2 <| by
        refine Finpartition.le_iff_forall_part_subset.2 fun x y hy => ?_
        rw [NoncrossingPartition.coe_comap, NoncrossingPartition.coe_bot,
          Finpartition.part_comap_bot (mem_univ x), mem_filter] at hy
        cases e.injective hy.2
        exact σ.val.mem_part_self.2 (mem_univ _)⟩
  rw [← (Equiv.ofBijective _ hbij).sum_comp]
  have himg : univ.image (e : Fin #X → Fin n) = X := image_orderEmbOfFin_univ X rfl
  refine (sum_congr rfl fun ρ _ => ?_).trans
    (congrArg (fun Y : Finset (Fin n) =>
      ∑ ρ : NoncrossingPartition Y, ∏ B ∈ ρ.val.parts, wickBlockWeight C w B) himg)
  rw [Equiv.ofBijective_apply, NoncrossingPartition.coe_comap, Finpartition.prod_parts_comap]
  refine prod_congr rfl fun B hB => ?_
  rw [← wickBlockWeight_image_orderEmbedding w e, Finpartition.image_filter_mem_of_mem_parts hB]

/-- **Wick characterization of semicircular systems**: a family `s : ι → A` is a semicircular
system with covariance `C` for `φ` if and only if every word `w : Fin n → ι` (including the empty
word `n = 0`) satisfies the noncrossing-pairing Wick formula. -/
theorem isSemicircularSystem_iff_apply_prod_ofFn :
    IsSemicircularSystem φ s C ↔
      ∀ {n : ℕ} (w : Fin n → ι),
        φ (List.ofFn (s ∘ w)).prod =
          ∑ P : {P : NoncrossingPartition (univ : Finset (Fin n)) // P.val.IsPairing},
            ∏ p ∈ P.val.val.orderedPairs, C (w p.1) (w p.2) := by
  refine ⟨fun h {n} w => h.apply_prod_ofFn w, fun hprod => ?_⟩
  have h1 : φ 1 = 1 := by
    have h0 := hprod (n := 0) Fin.elim0
    have hempty : (univ : Finset (Fin 0)) = ∅ := univ_eq_empty
    rw [List.ofFn_zero, List.prod_nil, hempty,
      NoncrossingPartition.sum_isPairing_prod_orderedPairs_empty
        fun i j => C (Fin.elim0 i) (Fin.elim0 j)] at h0
    exact h0
  refine ⟨h1, fun w => ?_, fun {n} hn₀ hn₂ w => ?_⟩
  · rw [freeCumulant_eq_wickBlockWeight_of_apply_prod_ofFn hprod two_ne_zero w]
    have hmin : (univ : Finset (Fin 2)).min' univ_nonempty = 0 := by decide
    have hmax : (univ : Finset (Fin 2)).max' univ_nonempty = 1 := by decide
    simp [wickBlockWeight, hmin, hmax]
  · rw [freeCumulant_eq_wickBlockWeight_of_apply_prod_ofFn hprod hn₀ w]
    have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn₀⟩⟩
    simp [wickBlockWeight, hn₂]

/-- *Free semicircular families*: a family `s` is a semicircular system with diagonal covariance
`diagonal v` for `φ` exactly when `φ` is normalised and the `s i` are freely independent
semicircular elements of variances `v i`. -/
theorem isSemicircularSystem_diagonal_iff [DecidableEq ι] {v : ι → R} :
    IsSemicircularSystem φ s (diagonal v) ↔
      φ 1 = 1 ∧ IsFreelyIndependentElements φ s ∧ ∀ i, IsSemicircular φ (s i) (v i) := by
  refine ⟨fun h => ⟨h.apply_one, h.isFreelyIndependentElements_iff.2 fun i j hij =>
    diagonal_apply_ne v hij, fun i => by simpa using h.isSemicircular i⟩,
    fun ⟨hφ, hfree, hs⟩ => ?_⟩
  -- A constant word has the cumulants of one semicircular element; any other word is mixed.
  have hκ {n : ℕ} (hn₀ : n ≠ 0) (w : Fin n → ι) :
      freeCumulant φ (s ∘ w) univ = if n = 2 ∧ ∀ m, w m = w ⟨0, by omega⟩ then v (w ⟨0, by omega⟩)
        else 0 := by
    by_cases hw : ∀ m, w m = w ⟨0, by omega⟩
    · have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have hsw : s ∘ w = fun _ => s (w ⟨0, by omega⟩) := funext fun m => congrArg s (hw m)
      rw [hsw, (hs _).freeCumulant_const univ_nonempty]
      simp [hw]
    · push Not at hw
      obtain ⟨m, hm⟩ := hw
      have hw : ¬(n = 2 ∧ ∀ m, w m = w ⟨0, by omega⟩) := fun h' => hm (h'.2 m)
      simp only [hw, ↓reduceIte]
      exact (isFreelyIndependentElements_iff_freeCumulant_eq_zero hφ).1 hfree n w m _ hm
  refine ⟨hφ, fun w => ?_, fun hn₀ hn₂ w => by simp [hκ hn₀, hn₂]⟩
  rw [hκ two_ne_zero]
  by_cases h01 : w 1 = w 0
  · simp [Fin.forall_fin_two, h01]
  · simp [Fin.forall_fin_two, h01, diagonal_apply_ne v (Ne.symm h01)]

/-- A single element is a semicircular system, with the `1 × 1` covariance given by its variance,
exactly when it is semicircular. -/
theorem isSemicircularSystem_iff_isSemicircular [Unique ι] :
    IsSemicircularSystem φ s C ↔ IsSemicircular φ (s default) (C default default) := by
  classical
  have hC : C = diagonal fun i => C i i := by
    ext i j
    simp [Subsingleton.elim i j]
  rw [hC, isSemicircularSystem_diagonal_iff]
  exact ⟨fun h => h.2.2 default, fun h => ⟨h.apply_one,
    isFreelyIndependentElements_of_subsingleton φ s, fun i => Unique.eq_default i ▸ h⟩⟩

/-- If `s : ι → A` is a self-adjoint semicircular system with real covariance `C` for a positive
linear functional `φ : A →ₚ[ℂ] ℂ` on a `StarOrderedRing`, then `C` is symmetric and positive
semidefinite. -/
theorem IsSemicircularSystem.posSemidef_of_isSelfAdjoint {A ι : Type*} [Ring A] [PartialOrder A]
    [StarRing A] [StarOrderedRing A] [Algebra ℂ A] [StarModule ℂ A] {φ : A →ₚ[ℂ] ℂ}
    {s : ι → A} {C : Matrix ι ι ℝ}
    (h : IsSemicircularSystem φ.toLinearMap s (C.map Complex.ofReal))
    (hs : ∀ i, IsSelfAdjoint (s i)) :
    C.PosSemidef := by
  have hmul (i j : ι) : φ (s i * s j) = C i j := by simpa using h.apply_mul i j
  refine posSemidef_iff_finite_sum.{0, _, 0}.2 ⟨fun i j => ?_, fun {κ} _ v x => ?_⟩
  · have hsymm := (StarPositiveFunctional.ofPositiveLinearMap φ).star_apply_star_mul (s i) (s j)
    simp only [StarPositiveFunctional.ofPositiveLinearMap_apply, (hs _).star_eq, hmul] at hsymm
    simpa [star_trivial] using congrArg Complex.re hsymm
  · let b : A := ∑ p : κ, (x p : ℂ) • s (v p)
    have hb_star : star b = b := by
      simp [b, star_sum, star_smul, (hs _).star_eq]
    have hbb : star b * b =
        ∑ p : κ, ∑ q : κ, ((x p : ℂ) * (x q : ℂ)) • (s (v p) * s (v q)) := by
      rw [hb_star]
      simp only [b, sum_mul_sum, smul_mul_smul_comm]
    have hφ : φ (star b * b) =
        ((∑ p : κ, ∑ q : κ, star (x p) * C (v p) (v q) * x q : ℝ) : ℂ) := by
      rw [hbb, map_sum]
      simp only [map_sum, LinearMapClass.map_smul, hmul, smul_eq_mul, star_trivial,
        Complex.ofReal_sum, Complex.ofReal_mul]
      refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
      ring
    have hnonneg : 0 ≤ φ (star b * b) := φ.map_nonneg (star_mul_self_nonneg b)
    rw [hφ] at hnonneg
    exact Complex.zero_le_real.1 hnonneg

end TauCeti
