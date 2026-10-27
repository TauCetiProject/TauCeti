/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Pivots of a subspace relative to a basis flag and Schubert cells

Let `b` be a basis of a vector space `V` over a division ring `K`, indexed by `Fin n`, and let
`F_j = b.flag j` be the increasing flag spanned by its first `j` vectors. The relative position of
a subspace `W` with respect to this flag is recorded by its *pivots*, the finite set
`b.flagPivots W ⊆ Fin n` of indices `i` at which `W ⊓ F_j` jumps, from `j = i` to `j = i + 1`.
In the one-based notation of Schubert calculus the pivots of an `r`-dimensional `W` are
`p₁ < ⋯ < p_r`, the elements of `b.flagPivots W` being the zero-based indices `p_k - 1 : Fin n`,
and the dimension formula reads `dim (W ⊓ F_j) = #{k | p_k ≤ j}`.

The set of subspaces with a given pivot set `S` is the Schubert cell of `S` relative to the flag.
On points, it is an affine space: every such subspace has a unique reduced echelon basis
(the row with pivot `s` has coordinate `1` at `s`, `0` at the other pivots and after `s`), and the
cell is in bijection with the free entries of these echelon matrices. There are `∑ k, (p_k - k)`
free entries, which is `r (n - r) - |λ|` for the partition `λ_k = n - r + k - p_k` in the
`r × (n - r)` rectangle.

These statements concern the points of Grassmannians over fields: they compare subspaces,
pivot positions and the Schubert cells of the increasing flag as sets of subspaces, and do not
construct the Schubert cells or their closures as schemes.

## Main definitions

* `Module.Basis.flagPivots b W`: the pivots of `W` relative to `b.flag`.
* `Module.Basis.flagEchelon b W`: the reduced echelon basis of `W` adapted to `b.flag`. Its
  pivots are the *last* nonzero coordinates of its vectors, as suits the increasing flag; this is
  the reverse of the leading-entry convention of Mathlib's `Matrix.IsReducedRowEchelon`.
* `Finset.echelonFreeEntries S`: the free entries of a reduced echelon matrix with pivot set `S`.
* `Module.Basis.flagCellEquiv b S`: the Schubert cell of `S` is in bijection with
  `S.echelonFreeEntries → K`.

## Main results

* `Module.Basis.finrank_inf_flag`: `dim (W ⊓ F_j)` is the number of pivots of `W` below `j`.
* `Module.Basis.card_flagPivots`: `W` has `dim W` pivots.
* `Module.Basis.flagPivots_eq_iff`, `Module.Basis.flagPivots_eq_image_iff`: the pivot set is the
  only set (or strictly increasing sequence) of indices counting the dimensions of `W ⊓ F_j`, so
  every subspace lies in exactly one Schubert cell.
* `Module.Basis.existsUnique_flagEchelon`, `Module.Basis.span_flagEchelon`: existence and
  uniqueness of the reduced echelon basis.
* `StrictMono.card_echelonFreeEntries_image`: the number of free entries of a cell is
  `∑ k, (p_k - k)`. This is `r (n - r) - |λ|` by `StrictMono.sum_sub_add_sum_sub_eq_mul`, and
  `λ_k = n - r + k - p_k` is a partition by `StrictMono.antitone_sub_sub`; both are in
  `TauCeti.Data.Fin.StrictMono`.

## References

* W. Fulton, *Young tableaux*, London Mathematical Society Student Texts 35, Cambridge University
  Press (1997), §9.4.
-/

public section

open Module Submodule Finset

namespace Finset

variable {n : ℕ}

/-- The free entries of a reduced echelon matrix with pivot set `S` relative to the increasing
flag: the positions `(s, j)` with `s ∈ S` a pivot and `j < s` a non-pivot column. The row with
pivot `s` has entry `1` at `s`, zero entries at the other pivots and after `s`, and arbitrary
entries at the free positions. -/
def echelonFreeEntries (S : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  {x | x.1 ∈ S ∧ x.2 < x.1 ∧ x.2 ∉ S}

@[simp]
theorem mem_echelonFreeEntries {S : Finset (Fin n)} {x : Fin n × Fin n} :
    x ∈ S.echelonFreeEntries ↔ x.1 ∈ S ∧ x.2 < x.1 ∧ x.2 ∉ S := by
  simp [echelonFreeEntries]

end Finset

namespace StrictMono

variable {n r : ℕ} {p : Fin r → Fin n}

/-- The number of free entries of a reduced echelon matrix with pivots `p 0 < ⋯ < p (r - 1)` is
`∑ i, (p i - i)`. -/
theorem card_echelonFreeEntries_image (hp : StrictMono p) :
    #(univ.image p).echelonFreeEntries = ∑ i, ((p i : ℕ) - i) := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ.image p) fun x hx ↦
      (mem_echelonFreeEntries.mp hx).1, sum_image fun i _ k _ h ↦ hp.injective h]
  refine sum_congr rfl fun i _ ↦ ?_
  -- The fibre over `p i` is the set of non-pivots below `p i`.
  have hfib : {x ∈ (univ.image p).echelonFreeEntries | x.1 = p i} =
      ({j ∈ Iio (p i) | j ∉ univ.image p}).map ⟨(p i, ·), fun _ _ h ↦ (Prod.mk.inj h).2⟩ := by
    ext ⟨s, j⟩
    simp only [mem_filter, mem_echelonFreeEntries, mem_map, mem_Iio]
    constructor
    · rintro ⟨⟨-, hj, hjS⟩, rfl⟩
      exact ⟨j, ⟨hj, hjS⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hjS⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨⟨mem_image_of_mem _ (mem_univ _), hj, hjS⟩, rfl⟩
  -- The pivots below `p i` are the `p k` with `k < i`.
  have hpiv : {j ∈ Iio (p i) | j ∈ univ.image p} = (Iio i).image p := by
    ext j
    simp only [mem_filter, mem_Iio, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨hj, k, rfl⟩
      exact ⟨k, hp.lt_iff_lt.mp hj, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hp hk, k, rfl⟩
  have h := card_filter_add_card_filter_not (s := Iio (p i)) (· ∈ univ.image p)
  rw [hpiv, card_image_of_injective _ hp.injective, Fin.card_Iio, Fin.card_Iio] at h
  rw [hfib, card_map]
  omega

end StrictMono

namespace Module.Basis

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}
  (b : Basis (Fin n) R M) (W : Submodule R M)

open scoped Classical in
/-- The pivots of a subspace `W` relative to the flag `b.flag` of a basis `b` indexed by `Fin n`:
the indices `i` at which the flag `W ⊓ b.flag` jumps, that is, at which `W ⊓ b.flag i.succ` is not
contained in `b.flag i.castSucc`. These are the (zero-based) Schubert symbol of `W`. -/
noncomputable def flagPivots : Finset (Fin n) :=
  {i | ¬ W ⊓ b.flag i.succ ≤ b.flag i.castSucc}

variable {b W}

theorem mem_flagPivots_iff_not_le {i : Fin n} :
    i ∈ b.flagPivots W ↔ ¬ W ⊓ b.flag i.succ ≤ b.flag i.castSucc := by
  classical
  simp [flagPivots]

/-- A vector of `b.flag i.succ` lies in `b.flag i.castSucc` exactly when its `i`-th coordinate
vanishes. -/
theorem mem_flag_castSucc_iff_of_mem_flag_succ {i : Fin n} {x : M} (hx : x ∈ b.flag i.succ) :
    x ∈ b.flag i.castSucc ↔ b.repr x i = 0 := by
  rw [mem_flag_iff_repr_eq_zero] at hx ⊢
  refine ⟨fun h ↦ h i le_rfl, fun h j hj ↦ ?_⟩
  rcases hj.eq_or_lt with hij | hij
  · rwa [Fin.castSucc_inj.mp hij] at h
  · exact hx j (Fin.castSucc_lt_iff_succ_le.mp hij)

/-- `i` is a pivot of `W` exactly when `W` contains a vector whose last nonzero coordinate is the
`i`-th one. -/
theorem mem_flagPivots {i : Fin n} :
    i ∈ b.flagPivots W ↔ ∃ x ∈ W, x ∈ b.flag i.succ ∧ b.repr x i ≠ 0 := by
  rw [mem_flagPivots_iff_not_le, IsConcreteLE.not_le_iff_exists]
  constructor
  · rintro ⟨x, ⟨hxW, hxF⟩, hx⟩
    exact ⟨x, hxW, hxF, fun h ↦ hx ((mem_flag_castSucc_iff_of_mem_flag_succ hxF).mpr h)⟩
  · rintro ⟨x, hxW, hxF, hx⟩
    exact ⟨x, ⟨hxW, hxF⟩, fun h ↦ hx ((mem_flag_castSucc_iff_of_mem_flag_succ hxF).mp h)⟩

end Semiring

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}
  {b : Basis (Fin n) K V} {W : Submodule K V}

/-- Passing from `b.flag i.castSucc` to `b.flag i.succ`, the dimension of `W ⊓ b.flag` grows by
one at a pivot of `W` and stays constant otherwise. -/
theorem finrank_inf_flag_succ (i : Fin n) :
    finrank K ↥(W ⊓ b.flag i.succ) =
      finrank K ↥(W ⊓ b.flag i.castSucc) + if i ∈ b.flagPivots W then 1 else 0 := by
  have := Module.Finite.of_basis b
  split_ifs with hi
  · obtain ⟨x, hxW, hxF, hx⟩ := mem_flagPivots.mp hi
    have hxF' : x ∉ W ⊓ b.flag i.castSucc := fun h ↦
      hx ((mem_flag_castSucc_iff_of_mem_flag_succ hxF).mp h.2)
    have heq : W ⊓ b.flag i.succ = W ⊓ b.flag i.castSucc ⊔ K ∙ x := by
      refine le_antisymm (fun y hy ↦ ?_) (sup_le (inf_le_inf_left _ (b.flag_mono
        Fin.castSucc_lt_succ.le)) ((span_singleton_le_iff_mem _ _).mpr ⟨hxW, hxF⟩))
      have hz : y - (b.repr y i / b.repr x i) • x ∈ W ⊓ b.flag i.castSucc := by
        refine ⟨W.sub_mem hy.1 (W.smul_mem _ hxW), ?_⟩
        refine (mem_flag_castSucc_iff_of_mem_flag_succ
          (sub_mem hy.2 (smul_mem _ _ hxF))).mpr ?_
        simp [div_mul_cancel₀ _ hx]
      simpa using add_mem_sup hz (mem_span_singleton.mpr ⟨b.repr y i / b.repr x i, rfl⟩ :
        (b.repr y i / b.repr x i) • x ∈ K ∙ x)
    rw [heq]
    exact finrank_sup_span_singleton hxF'
  · rw [add_zero, le_antisymm
      (le_inf inf_le_left (not_not.mp (mem_flagPivots_iff_not_le.not.mp hi)))
      (inf_le_inf_left _ (b.flag_mono Fin.castSucc_lt_succ.le))]

variable (b W) in
/-- The dimension of `W ⊓ b.flag j` is the number of pivots of `W` below `j`. In one-based
notation, with pivots `p₁ < ⋯ < p_r` and `F_j` spanned by the first `j` basis vectors, this reads
`dim (W ⊓ F_j) = #{i | p_i ≤ j}`. -/
theorem finrank_inf_flag (j : Fin (n + 1)) :
    finrank K ↥(W ⊓ b.flag j) = #{i ∈ b.flagPivots W | i.castSucc < j} := by
  induction j using Fin.induction with
  | zero => rw [b.flag_zero, inf_bot_eq, finrank_bot]; simp
  | succ i ih => rw [finrank_inf_flag_succ, ih, Finset.card_filter_castSucc_lt_succ]

variable (b W) in
/-- A subspace has as many pivots as its dimension. -/
@[simp]
theorem card_flagPivots : #(b.flagPivots W) = finrank K W := by
  have h := finrank_inf_flag b W (Fin.last n)
  rw [flag_last, inf_top_eq, filter_true_of_mem fun i _ ↦ Fin.castSucc_lt_last i] at h
  exact h.symm

@[simp]
theorem flagPivots_bot : b.flagPivots (⊥ : Submodule K V) = ∅ := by
  rw [← card_eq_zero, card_flagPivots, finrank_bot]

@[simp]
theorem flagPivots_top : b.flagPivots (⊤ : Submodule K V) = univ := by
  rw [← card_eq_iff_eq_univ, card_flagPivots, finrank_top, finrank_eq_card_basis b]

/-- The pivots of `W` are the only set of indices counting the dimensions of `W ⊓ b.flag j`: a
subspace lies in exactly one Schubert cell of the flag `b.flag`. -/
theorem flagPivots_eq_iff {S : Finset (Fin n)} :
    b.flagPivots W = S ↔ ∀ j, finrank K ↥(W ⊓ b.flag j) = #{i ∈ S | i.castSucc < j} := by
  refine ⟨fun h ↦ h ▸ finrank_inf_flag b W, fun h ↦ ?_⟩
  ext i
  have h₁ := finrank_inf_flag_succ (b := b) (W := W) i
  rw [h, h, Finset.card_filter_castSucc_lt_succ] at h₁
  split_ifs at h₁ with h₂ h₃ h₃ <;> simp_all

/-- The pivot set of `W` is the image of a strictly increasing `p : Fin r → Fin n` exactly when
`p` counts the dimensions of `W ⊓ b.flag j`. -/
theorem flagPivots_eq_image_iff {r : ℕ} {p : Fin r → Fin n} (hp : StrictMono p) :
    b.flagPivots W = univ.image p ↔
      ∀ j, finrank K ↥(W ⊓ b.flag j) = #{i | (p i).castSucc < j} := by
  rw [flagPivots_eq_iff]
  refine forall_congr' fun j ↦ ?_
  rw [filter_image, card_image_of_injective _ hp.injective]

/-- A vector of `W` whose coordinates at the pivots of `W` all vanish is zero. -/
theorem eq_zero_of_repr_flagPivots_eq_zero {x : V} (hx : x ∈ W)
    (h : ∀ i ∈ b.flagPivots W, b.repr x i = 0) : x = 0 := by
  by_contra hx₀
  have hs : (b.repr x).support.Nonempty := by
    simpa [Finsupp.support_nonempty_iff] using hx₀
  set i := (b.repr x).support.max' hs
  have hi : b.repr x i ≠ 0 := Finsupp.mem_support_iff.mp ((b.repr x).support.max'_mem hs)
  refine hi (h i (mem_flagPivots.mpr ⟨x, hx, ?_, hi⟩))
  rw [mem_flag_iff_repr_eq_zero]
  intro j hj
  by_contra hj'
  exact (Fin.castSucc_lt_iff_succ_le.mpr hj).not_ge
    (Fin.castSucc_le_castSucc_iff.mpr ((b.repr x).support.le_max' j (by simpa using hj')))

/-- For a pivot `i` of `W`, there is a unique vector of `W ⊓ b.flag i.succ` whose coordinates at
the pivots of `W` are those of `b i`: the row with pivot `i` of the reduced echelon basis of `W`
adapted to the flag. -/
theorem existsUnique_flagEchelon {i : Fin n} (hi : i ∈ b.flagPivots W) :
    ∃! x, x ∈ W ⊓ b.flag i.succ ∧ ∀ j ∈ b.flagPivots W, b.repr x j = Finsupp.single i 1 j := by
  have := Module.Finite.of_basis b
  refine existsUnique_of_exists_of_unique ?_ fun x y hx hy ↦ ?_
  · -- The coordinates at the pivots up to `i` form an isomorphism on `W ⊓ b.flag i.succ`.
    set T : Finset (Fin n) := {j ∈ b.flagPivots W | j.castSucc < i.succ}
    let φ : ↥(W ⊓ b.flag i.succ) →ₗ[K] (T → K) :=
      LinearMap.pi fun j ↦ (b.coord j).comp (Submodule.subtype _)
    have hlt {x : V} (hx : x ∈ b.flag i.succ) {j : Fin n} (hj : ¬ j.castSucc < i.succ) :
        b.repr x j = 0 :=
      (b.mem_flag_iff_repr_eq_zero.mp hx) j (not_lt.mp hj)
    have hφ : Function.Injective φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      refine Subtype.ext (eq_zero_of_repr_flagPivots_eq_zero (b := b) x.2.1 fun j hj ↦ ?_)
      by_cases hji : j.castSucc < i.succ
      · simpa [φ] using congr_fun hx ⟨j, mem_filter.mpr ⟨hj, hji⟩⟩
      · exact hlt x.2.2 hji
    have hrank : finrank K ↥(W ⊓ b.flag i.succ) = finrank K (T → K) := by
      rw [finrank_inf_flag, finrank_fintype_fun_eq_card, Fintype.card_coe]
    have hiT : i ∈ T := mem_filter.mpr ⟨hi, Fin.castSucc_lt_succ⟩
    obtain ⟨x, hx⟩ :=
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hφ)
        (Pi.single ⟨i, hiT⟩ 1)
    refine ⟨x, x.2, fun j hj ↦ ?_⟩
    by_cases hji : j.castSucc < i.succ
    · have := congr_fun hx ⟨j, mem_filter.mpr ⟨hj, hji⟩⟩
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, coe_subtype, coord_apply, φ] at this
      simp [this, Finsupp.single_apply, Pi.single_apply, eq_comm]
    · rw [hlt x.2.2 hji, Finsupp.single_eq_of_ne]
      rintro rfl
      exact hji Fin.castSucc_lt_succ
  · rw [← sub_eq_zero]
    refine eq_zero_of_repr_flagPivots_eq_zero (b := b) (W.sub_mem hx.1.1 hy.1.1) fun j hj ↦ ?_
    rw [map_sub, Finsupp.sub_apply, hx.2 j hj, hy.2 j hj, sub_self]

/-- The span of a family indexed by `S`, whose `s`-th member lies in `b.flag s.succ` and has the
coordinates of `b s` at the indices in `S`, has pivot set `S`. -/
theorem flagPivots_span_eq {S : Finset (Fin n)} {v : S → V}
    (hv : ∀ s : S, v s ∈ b.flag (s : Fin n).succ)
    (hv' : ∀ s : S, ∀ t ∈ S, b.repr (v s) t = Finsupp.single (s : Fin n) 1 t) :
    b.flagPivots (span K (Set.range v)) = S := by
  refine (eq_of_subset_of_card_le (fun s hs ↦ ?_) ?_).symm
  · refine mem_flagPivots.mpr ⟨v ⟨s, hs⟩, subset_span (Set.mem_range_self _), hv ⟨s, hs⟩, ?_⟩
    rw [hv' ⟨s, hs⟩ s hs, Finsupp.single_eq_same]
    exact one_ne_zero
  · rw [card_flagPivots, finrank_span_eq_card (linearIndependent_of_repr_eq_single hv'),
      Fintype.card_coe]

variable (b W) in
/-- The reduced echelon basis of `W` adapted to the flag `b.flag`: for a pivot `i` of `W`, the
unique vector of `W ⊓ b.flag i.succ` whose coordinates at the pivots of `W` are those of `b i`
(see `Module.Basis.existsUnique_flagEchelon`); it is `0` at an index which is not a pivot. -/
noncomputable def flagEchelon (i : Fin n) : V :=
  if hi : i ∈ b.flagPivots W then (existsUnique_flagEchelon hi).exists.choose else 0

private theorem flagEchelon_spec {i : Fin n} (hi : i ∈ b.flagPivots W) :
    b.flagEchelon W i ∈ W ⊓ b.flag i.succ ∧
      ∀ j ∈ b.flagPivots W, b.repr (b.flagEchelon W i) j = Finsupp.single i 1 j := by
  rw [flagEchelon, dite_eq_left hi]
  exact (existsUnique_flagEchelon hi).exists.choose_spec

theorem flagEchelon_mem (i : Fin n) : b.flagEchelon W i ∈ W := by
  by_cases hi : i ∈ b.flagPivots W
  · exact (flagEchelon_spec hi).1.1
  · simp [flagEchelon, hi]

theorem flagEchelon_mem_flag {i : Fin n} (hi : i ∈ b.flagPivots W) :
    b.flagEchelon W i ∈ b.flag i.succ :=
  (flagEchelon_spec hi).1.2

@[simp]
theorem repr_flagEchelon {i j : Fin n} (hi : i ∈ b.flagPivots W) (hj : j ∈ b.flagPivots W) :
    b.repr (b.flagEchelon W i) j = Finsupp.single i 1 j :=
  (flagEchelon_spec hi).2 j hj

@[simp]
theorem flagEchelon_of_notMem {i : Fin n} (hi : i ∉ b.flagPivots W) : b.flagEchelon W i = 0 := by
  simp [flagEchelon, hi]

/-- The characterization of the reduced echelon basis vectors. -/
theorem eq_flagEchelon {i : Fin n} (hi : i ∈ b.flagPivots W) {x : V} (hx : x ∈ W)
    (hxF : x ∈ b.flag i.succ) (h : ∀ j ∈ b.flagPivots W, b.repr x j = Finsupp.single i 1 j) :
    x = b.flagEchelon W i :=
  (existsUnique_flagEchelon hi).unique ⟨⟨hx, hxF⟩, h⟩ (flagEchelon_spec hi)

theorem linearIndependent_flagEchelon :
    LinearIndependent K fun i : b.flagPivots W ↦ b.flagEchelon W i :=
  linearIndependent_of_repr_eq_single fun i _ hj ↦ repr_flagEchelon i.2 hj

/-- The reduced echelon basis vectors of `W` span `W`. -/
theorem span_flagEchelon : span K (Set.range fun i : b.flagPivots W ↦ b.flagEchelon W i) = W := by
  have := Module.Finite.of_basis b
  refine eq_of_le_of_finrank_eq (span_le.mpr (Set.range_subset_iff.mpr fun i ↦ flagEchelon_mem _))
    ?_
  rw [finrank_span_eq_card linearIndependent_flagEchelon, Fintype.card_coe, card_flagPivots]

end DivisionRing

/-! ### Schubert cells as affine spaces -/

section Semiring

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}
  {b : Basis (Fin n) R M}

variable (b) in
/-- The row with pivot `s` of the reduced echelon matrix with pivot set `S` and free entries
`a`: its coordinates are `1` at `s`, `a (s, j)` at a free position `(s, j)`, and `0` elsewhere. -/
noncomputable def echelonRow (S : Finset (Fin n)) (a : S.echelonFreeEntries → R) (s : Fin n) :
    M :=
  b.equivFun.symm fun j ↦ if j = s then 1 else if h : (s, j) ∈ S.echelonFreeEntries then
    a ⟨(s, j), h⟩ else 0

theorem repr_echelonRow (S : Finset (Fin n)) (a : S.echelonFreeEntries → R) (s j : Fin n) :
    b.repr (b.echelonRow S a s) j = if j = s then 1 else if h : (s, j) ∈ S.echelonFreeEntries then
      a ⟨(s, j), h⟩ else 0 := by
  rw [echelonRow, ← equivFun_apply, LinearEquiv.apply_symm_apply]

@[simp]
theorem repr_echelonRow_of_mem {S : Finset (Fin n)} (a : S.echelonFreeEntries → R) (s : Fin n)
    {j : Fin n} (hj : j ∈ S) : b.repr (b.echelonRow S a s) j = Finsupp.single s 1 j := by
  rw [repr_echelonRow, Finsupp.single_apply]
  by_cases hjs : j = s
  · simp [hjs]
  · rw [ite_eq_right hjs, ite_eq_right (Ne.symm hjs),
      dite_eq_right fun h ↦ (mem_echelonFreeEntries.mp h).2.2 hj]

theorem echelonRow_mem_flag (S : Finset (Fin n)) (a : S.echelonFreeEntries → R) (s : Fin n) :
    b.echelonRow S a s ∈ b.flag s.succ := by
  rw [mem_flag_iff_repr_eq_zero]
  intro j hj
  have hsj : s < j := Fin.succ_le_castSucc_iff.mp hj
  rw [repr_echelonRow, ite_eq_right hsj.ne',
    dite_eq_right fun h ↦ (mem_echelonFreeEntries.mp h).2.1.not_gt hsj]

end Semiring

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {n : ℕ}
  {b : Basis (Fin n) K V}

/-- The span of the rows of the reduced echelon matrix with pivot set `S` and free entries `a` has
pivot set `S`. -/
theorem flagPivots_span_echelonRow (S : Finset (Fin n)) (a : S.echelonFreeEntries → K) :
    b.flagPivots (span K (Set.range fun s : S ↦ b.echelonRow S a s)) = S :=
  flagPivots_span_eq (fun _ ↦ echelonRow_mem_flag _ _ _) fun s _ ht ↦ repr_echelonRow_of_mem a s ht

variable (b) in
/-- The Schubert cell of the flag `b.flag` with pivot set `S`, that is the set of subspaces `W`
with `b.flagPivots W = S`, is in bijection with the affine space `K ^ S.echelonFreeEntries`: a
subspace corresponds to the free entries of its reduced echelon basis. -/
noncomputable def flagCellEquiv (S : Finset (Fin n)) :
    {W : Submodule K V // b.flagPivots W = S} ≃ (S.echelonFreeEntries → K) where
  toFun W x := b.repr (b.flagEchelon W x.1.1) x.1.2
  invFun a := ⟨span K (Set.range fun s : S ↦ b.echelonRow S a s), flagPivots_span_echelonRow S a⟩
  left_inv := by
    rintro ⟨W, rfl⟩
    refine Subtype.ext ((congrArg (span K) (congrArg Set.range (funext fun s ↦ ?_))).trans
      span_flagEchelon)
    -- The row built from the free entries of the echelon basis vector is that vector.
    refine b.repr.injective (Finsupp.ext fun j ↦ ?_)
    by_cases hj : j ∈ b.flagPivots W
    · rw [repr_echelonRow_of_mem _ _ hj, repr_flagEchelon s.2 hj]
    rw [repr_echelonRow, ite_eq_right (fun h : j = s ↦ hj (h ▸ s.2))]
    split_ifs with h
    · rfl
    · have hsj : (s : Fin n) < j := lt_of_not_ge fun hjs ↦ h (mem_echelonFreeEntries.mpr
        ⟨s.2, lt_of_le_of_ne hjs fun h' : j = s ↦ hj (h' ▸ s.2), hj⟩)
      exact ((b.mem_flag_iff_repr_eq_zero.mp (flagEchelon_mem_flag s.2)) j
        (Fin.succ_le_castSucc_iff.mpr hsj)).symm
  right_inv a := by
    funext ⟨⟨s, j⟩, hx⟩
    have hs : s ∈ S := (mem_echelonFreeEntries.mp hx).1
    have hS := flagPivots_span_echelonRow (b := b) S a
    have hsU : s ∈ b.flagPivots (span K (Set.range fun s : S ↦ b.echelonRow S a s)) := by
      rwa [hS]
    have h := eq_flagEchelon hsU (subset_span ⟨⟨s, hs⟩, rfl⟩) (echelonRow_mem_flag S a s)
      fun t ht ↦ repr_echelonRow_of_mem a s (by rwa [hS] at ht)
    dsimp only
    rw [← h, repr_echelonRow, ite_eq_right (mem_echelonFreeEntries.mp hx).2.1.ne,
      dite_eq_left hx]

@[simp]
theorem flagCellEquiv_apply (S : Finset (Fin n)) (W : {W : Submodule K V // b.flagPivots W = S})
    (x : S.echelonFreeEntries) : b.flagCellEquiv S W x = b.repr (b.flagEchelon W x.1.1) x.1.2 :=
  (rfl)

@[simp]
theorem coe_flagCellEquiv_symm_apply (S : Finset (Fin n)) (a : S.echelonFreeEntries → K) :
    ((b.flagCellEquiv S).symm a : Submodule K V) =
      span K (Set.range fun s : S ↦ b.echelonRow S a s) :=
  (rfl)

end DivisionRing

end Module.Basis
