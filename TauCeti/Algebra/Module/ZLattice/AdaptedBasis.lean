/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Algebra.Module.ZLattice.Basic
import TauCeti.LinearAlgebra.Basis.Triangular
import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# Lattice bases adapted to a flag

Let `L` be a discrete subgroup of a finite-dimensional real normed space `E`, and let
`a 0, …, a (n - 1)` be lattice vectors forming an `ℝ`-basis of `E`. They need not span `L`: they
span a sublattice of finite index. This file constructs a `ℤ`-basis `b` of `L` adapted to the
flag of subspaces `span ℝ {a i | i ≤ j}`: each `b j` is a combination of `a 0, …, a j`, and it is
reduced, being either `a j` itself or a combination all of whose coefficients have absolute value
at most `1 / 2` (`ZLattice.exists_basis_triangular`). In particular `b` and `a` define the same
flag: for every `k`, the first `k` vectors of `b` span over `ℝ` the same subspace as
`a 0, …, a (k - 1)` (`ZLattice.exists_basis_span_image_eq_flag`).

The coordinate-level triangular basis is used by
`TauCeti.Algebra.Module.ZLattice.GaugeBasis` to prove the canonical gauge estimate.
The lattice is not assumed to be full: this follows from the given basis.

For a real subspace `W` of `E`, the intersection `Δ ∩ W` of a finitely generated subgroup `Δ`
with `W` is recorded as the lattice `ZLattice.comap ℝ Δ W.subtype` in `W`. Since `W` is a real
subspace, the quotient `Δ ⧸ (Δ ∩ W)` is torsion-free, hence free, so every `ℤ`-basis of `Δ ∩ W`
extends to a `ℤ`-basis of `Δ` (`ZLattice.exists_basis_sum_inl_eq`). When `Δ` is a discrete full
lattice in a finite-dimensional `E` and `Δ ∩ W` spans `W`, this gives a basis of `Δ` whose first
`dim W` vectors form a basis of `Δ ∩ W` (`ZLattice.exists_basis_sum_finrank`), and the first
block of such a basis spans `W` over `ℝ` (`ZLattice.span_range_ofZLatticeBasis_inl`).

## Main results

* `ZLattice.exists_basis_triangular`: a reduced basis of `L` that is triangular with respect to an
  `ℝ`-basis of `E` consisting of lattice vectors.
* `ZLattice.exists_basis_span_image_eq_flag`: a basis of `L` with the same real flag as an
  `ℝ`-basis of `E` consisting of lattice vectors.
* `ZLattice.equivFun_ofZLatticeBasis_apply_eq_zero`: coordinates past an adapted flag vanish.
* `ZLattice.exists_basis_sum_inl_eq`: for a finitely generated subgroup `Δ` and a real subspace
  `W`, a `ℤ`-basis of `Δ ∩ W` extends to a `ℤ`-basis of `Δ`.
* `ZLattice.exists_basis_sum_finrank`: if `Δ` is a discrete full lattice in a finite-dimensional
  `E` and `Δ ∩ W` spans `W`, then `Δ` has a basis indexed by `Fin (dim W) ⊕ Fin s`, with
  `dim W + s = dim E`, whose first block is a basis of `Δ ∩ W`.
* `ZLattice.span_range_ofZLatticeBasis_inl`: if `Δ ∩ W` spans `W`, the first block of a basis of
  `Δ` that extends a basis of `Δ ∩ W` spans `W` over `ℝ`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter I,
  Theorem I and Corollary 1, and Chapter V, Lemma 8.
* T. Horesh and Y. Karasik, *Equidistribution of primitive lattices in ℝⁿ*, Q. J. Math. 74
  (2023), 1253–1294, Proposition B.4, p. 1290.
* M. Henk, *Successive minima and lattice points*, Rend. Circ. Mat. Palermo (2) Suppl. 70 (2002),
  377–384, p. 3 of arXiv:math/0204158.
-/

public section

open Module Submodule ZSpan Set

namespace ZLattice

section Algebraic

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {L : Submodule ℤ E} {n : ℕ}

/-- A family of lattice vectors, triangular with respect to `e`, whose diagonal coordinates
generate the corresponding coordinates of the lattice, spans the lattice. -/
theorem le_span_of_triangular (e : Basis (Fin n) ℝ E) {v : Fin n → E}
    (hv : ∀ j, v j ∈ L) (htri : ∀ j i, j < i → e.repr (v j) i = 0)
    (hgen : ∀ j, ∀ x ∈ L, (∀ i, j < i → e.repr x i = 0) →
      ∃ m : ℤ, e.repr x j = m * e.repr (v j) j) :
    L ≤ span ℤ (Set.range v) := by
  -- Induction on the number `k` of leading coordinates that may be nonzero.
  suffices h : ∀ k ≤ n, ∀ x ∈ L, (∀ i : Fin n, k ≤ i → e.repr x i = 0) →
      x ∈ span ℤ (Set.range v) from
    fun x hx ↦ h n le_rfl x hx fun i hi ↦ absurd i.isLt (not_lt.2 hi)
  intro k
  induction k with
  | zero =>
    intro _ x _ hx
    rw [e.repr.map_eq_zero_iff.1 (Finsupp.ext fun i ↦ hx i (Nat.zero_le _))]
    exact zero_mem _
  | succ k ih =>
    intro hk x hx hxk
    set j : Fin n := ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hgen j x hx fun i hi ↦ hxk i hi
    have hx' : x - m • v j ∈ span ℤ (Set.range v) := by
      refine ih (by omega) _ (L.sub_mem hx (zsmul_mem (hv j) m)) fun i hi ↦ ?_
      rcases hi.eq_or_lt with hi | hi
      · obtain rfl : i = j := Fin.ext hi.symm
        simp [hm]
      · simp [hxk i hi, htri j i hi]
    simpa using add_mem hx' (zsmul_mem (subset_span (Set.mem_range_self j)) m)

end Algebraic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E}
  [DiscreteTopology L] {n : ℕ}

/-- Among the lattice vectors in `span ℝ {e i | i ≤ j}`, some vector has the least positive
`j`-th coordinate, and the `j`-th coordinate of every such vector is an integer multiple of it. -/
private theorem exists_repr_generator (e : Basis (Fin n) ℝ E) (he : ∀ i, e i ∈ L) (j : Fin n) :
    ∃ y ∈ L, (∀ i, j < i → e.repr y i = 0) ∧ 0 < e.repr y j ∧ e.repr y j ≤ 1 ∧
      ∀ x ∈ L, (∀ i, j < i → e.repr x i = 0) → ∃ m : ℤ, e.repr x j = m * e.repr y j := by
  have := e.finiteDimensional_of_finite
  have hspan : span ℤ (Set.range e) ≤ L := span_le.2 (Set.range_subset_iff.2 he)
  -- This finite fundamental-domain argument follows Mathlib's `ZLattice.FG`.
  -- A bounded subset of a discrete (hence closed) subgroup is finite.
  have hfin : (fundamentalDomain e ∩ L).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (fundamentalDomain_isBounded e) L.toAddSubgroup.isClosed_of_discreteTopology
  -- So the attained coordinates in `(0, 1]` form a finite set, which contains `1`.
  set T : Set ℝ :=
    {t | t ∈ Set.Ioc 0 1 ∧ ∃ x ∈ L, (∀ i, j < i → e.repr x i = 0) ∧ e.repr x j = t}
  have hT : T.Finite := by
    refine ((hfin.image fun x ↦ e.repr x j).insert 1).subset ?_
    rintro t ⟨⟨ht0, ht1⟩, x, hx, -, rfl⟩
    rcases ht1.eq_or_lt with h | h
    · exact Or.inl h
    · refine Or.inr ⟨fract e x, ⟨fract_mem_fundamentalDomain e x, ?_⟩, ?_⟩
      · exact L.sub_mem hx (hspan (floor e x).property)
      · dsimp only
        rw [repr_fract_apply, Int.fract_eq_self.2 ⟨ht0.le, h⟩]
  have h1 : (1 : ℝ) ∈ T :=
    ⟨⟨one_pos, le_rfl⟩, e j, he j, fun i hi ↦ by simp [hi.ne], by simp⟩
  obtain ⟨_, ⟨⟨hd0, hd1⟩, y, hy, hyj, rfl⟩, hmin⟩ := Set.exists_min_image T id hT ⟨1, h1⟩
  refine ⟨y, hy, hyj, hd0, hd1, fun x hx hxj ↦ ⟨⌊e.repr x j / e.repr y j⌋, ?_⟩⟩
  -- Subtracting the right multiple of `y` leaves a coordinate in `[0, e.repr y j)`.
  set m := ⌊e.repr x j / e.repr y j⌋
  have hlo : m * e.repr y j ≤ e.repr x j := (le_div_iff₀ hd0).1 (Int.floor_le _)
  have hhi : e.repr x j < (m + 1) * e.repr y j := (div_lt_iff₀ hd0).1 (Int.lt_floor_add_one _)
  by_contra hne
  have hz : e.repr x j - m * e.repr y j ∈ T := by
    refine ⟨⟨by grind, by linarith⟩, x - m • y, L.sub_mem hx (zsmul_mem hy m),
      fun i hi ↦ ?_, ?_⟩
    · simp [hxj i hi, hyj i hi]
    · simp
  have := hmin _ hz
  simp only [id] at this
  linarith

/-- For each `j`, a lattice vector in `span ℝ {e i | i ≤ j}` whose `j`-th coordinate generates
the `j`-th coordinates of all such lattice vectors, and which is either `e j` or has all its
coordinates of absolute value at most `1 / 2`. -/
private theorem exists_reduced (e : Basis (Fin n) ℝ E) (he : ∀ i, e i ∈ L) (j : Fin n) :
    ∃ v ∈ L, (∀ i, j < i → e.repr v i = 0) ∧
      (∀ x ∈ L, (∀ i, j < i → e.repr x i = 0) → ∃ m : ℤ, e.repr x j = m * e.repr v j) ∧
      (v = e j ∨ ∀ i, |e.repr v i| ≤ 1 / 2) := by
  obtain ⟨y, hy, hyj, hy0, hy1, hgen⟩ := exists_repr_generator e he j
  rcases hy1.eq_or_lt with h | h
  · exact ⟨e j, he j, fun i hi ↦ by simp [hi.ne], by simpa [h] using hgen,
      Or.inl rfl⟩
  -- `1` is an integer multiple `m * d` of `d = e.repr y j < 1`, so `2 ≤ m` and `d ≤ 1 / 2`.
  obtain ⟨m, hm⟩ := hgen (e j) (he j) fun i hi ↦ by simp [hi.ne]
  simp only [Basis.repr_self, Finsupp.single_eq_same] at hm
  have hm1 : (1 : ℝ) < m := by nlinarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (by exact_mod_cast hm1 : (1 : ℤ) < m)
  have hd : e.repr y j ≤ 1 / 2 := by nlinarith
  -- Reduce the coordinates below `j` modulo the lattice vectors `e i`.
  set v := y - ∑ i ∈ Finset.Iio j, round (e.repr y i) • e i
  have hv (k : Fin n) :
      e.repr v k = e.repr y k - if k < j then (round (e.repr y k) : ℝ) else 0 := by
    simp [v, map_sum, Finsupp.single_apply, Finset.sum_ite_eq', zsmul_eq_mul]
  have hvj : e.repr v j = e.repr y j := by simp [hv]
  refine ⟨v, L.sub_mem hy (L.sum_mem fun i _ ↦ zsmul_mem (he i) _), fun i hi ↦ ?_,
    fun x hx hxj ↦ hvj ▸ hgen x hx hxj, Or.inr fun i ↦ ?_⟩
  · simp [hv, hyj i hi, hi.not_gt]
  · rw [hv]
    rcases lt_trichotomy i j with hij | rfl | hij
    · simpa [hij] using abs_sub_round (e.repr y i)
    · simpa [abs_of_pos hy0] using hd
    · simp [hyj i hij, hij.not_gt]

/-- **Adapted basis.** Let `e` be an `ℝ`-basis of `E` consisting of vectors of a discrete
subgroup `L`. Then `L` has a `ℤ`-basis `b` that is triangular with respect to `e`, in that
`b j ∈ span ℝ {e i | i ≤ j}`, and reduced: each `b j` is either `e j` or has all its
coordinates with respect to `e` of absolute value at most `1 / 2`. -/
theorem exists_basis_triangular (e : Basis (Fin n) ℝ E) (he : ∀ i, e i ∈ L) :
    ∃ b : Basis (Fin n) ℤ L, ∀ j, (∀ i, j < i → e.repr (b j) i = 0) ∧
      ((b j : E) = e j ∨ ∀ i, |e.repr (b j) i| ≤ 1 / 2) := by
  choose v hvL htri hgen hred using exists_reduced e he
  have hspan : span ℤ (Set.range v) = L :=
    le_antisymm (span_le.2 (Set.range_subset_iff.2 hvL)) (le_span_of_triangular e hvL htri hgen)
  have hli : LinearIndependent ℝ v := by
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_
      (by rw [finrank_eq_card_basis e])
    rw [← e.span_eq]
    exact span_le.2 (Set.range_subset_iff.2 fun i ↦
      span_le_restrictScalars ℤ ℝ _ (hspan ▸ he i))
  refine ⟨(Basis.span (hli.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hspan), fun j ↦ ?_⟩
  have hb : (((Basis.span (hli.restrict_scalars' ℤ)).map (LinearEquiv.ofEq _ _ hspan) j : L) : E) =
      v j := by
    simp
  exact hb ▸ ⟨htri j, hred j⟩

/-- **Lattice basis with a prescribed flag.** Let `e` be an `ℝ`-basis of `E` consisting of vectors
of a discrete subgroup `L`. Then `L` has a `ℤ`-basis `b` with the same real flag as `e`: for every
`k`, the vectors `b 0, …, b (k - 1)` span over `ℝ` the subspace `e.flag k` spanned by
`e 0, …, e (k - 1)`. The vectors `b j` and `e j` differ in general, since the `e j` need not span
`L` over `ℤ`. -/
theorem exists_basis_span_image_eq_flag (e : Basis (Fin n) ℝ E) (he : ∀ i, e i ∈ L) :
    ∃ b : Basis (Fin n) ℤ L, ∀ k : Fin (n + 1),
      span ℝ ((fun j ↦ (b j : E)) '' {j | j.castSucc < k}) = e.flag k := by
  have := e.finiteDimensional_of_finite
  -- The lattice vectors `e i` already force `L` to span `E`.
  have : IsZLattice ℝ L := ⟨eq_top_iff.2 (e.span_eq ▸ span_mono (Set.range_subset_iff.2 he))⟩
  obtain ⟨b, hb⟩ := exists_basis_triangular e he
  have htri (l i : Fin n) (hli : l < i) : e.repr (b.ofZLatticeBasis ℝ L l) i = 0 := by
    rw [b.ofZLatticeBasis_apply ℝ L]
    exact (hb l).1 i hli
  refine ⟨b, fun k ↦ ?_⟩
  rw [← (b.ofZLatticeBasis ℝ L).flag_eq_of_triangular htri k, Basis.flag]
  simp only [Basis.ofZLatticeBasis_apply]

/-- In coordinates of a lattice basis adapted to the flag of `e`, the `j`-th coordinate
vanishes on the span of the first `j` basis vectors of `e`. -/
theorem equivFun_ofZLatticeBasis_apply_eq_zero [FiniteDimensional ℝ E] [IsZLattice ℝ L]
    {e : Basis (Fin n) ℝ E} {b : Basis (Fin n) ℤ L}
    (hb : ∀ k : Fin (n + 1), span ℝ ((fun j ↦ (b j : E)) '' {j | j.castSucc < k}) = e.flag k)
    (j : Fin n) {v : E} (hv : v ∈ span ℝ (e '' Iio j)) :
    (b.ofZLatticeBasis ℝ L).equivFun v j = 0 := by
  refine (b.ofZLatticeBasis ℝ L).mem_flag_iff_repr_eq_zero.1 ?_ j le_rfl
  simp only [Basis.flag, Basis.ofZLatticeBasis_apply]
  rw [hb, Basis.flag]
  simp only [Fin.castSucc_lt_castSucc_iff]
  exact hv

section Saturated

/-- The intersection `Δ ∩ W`, seen as a submodule of `Δ`, is linearly equivalent to the lattice
`ZLattice.comap ℝ Δ W.subtype` in `W`. -/
private def comapSubtypeEquiv (Δ : Submodule ℤ E) (W : Submodule ℝ E) :
    (W.restrictScalars ℤ).comap Δ.subtype ≃ₗ[ℤ] ZLattice.comap ℝ Δ W.subtype where
  toFun x := ⟨⟨x.val, x.property⟩, x.val.property⟩
  invFun y := ⟨⟨y.val, y.property⟩, y.val.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Extending a basis of `Δ ∩ W` to a basis of `Δ`.** For a finitely generated subgroup `Δ` of a
real normed space and a real subspace `W`, every `ℤ`-basis `c` of `Δ ∩ W` extends to a `ℤ`-basis
`b` of `Δ` indexed by `ι ⊕ Fin s`, with `b (inl i) = c i`. -/
theorem exists_basis_sum_inl_eq (Δ : Submodule ℤ E) [Module.Finite ℤ Δ] (W : Submodule ℝ E)
    {ι : Type*} (c : Basis ι ℤ (ZLattice.comap ℝ Δ W.subtype)) :
    ∃ (s : ℕ) (b : Basis (ι ⊕ Fin s) ℤ Δ),
      Nat.card ι + s = finrank ℤ Δ ∧ ∀ i, (b (.inl i) : E) = c i := by
  have : IsTorsionFree ℤ (Δ ⧸ (W.restrictScalars ℤ).comap Δ.subtype) :=
    isTorsionFree_quotient_of_smul_mem _ fun n x hn hx ↦ by
      have hx' : (n : ℝ) • (x : E) ∈ W := by simpa [Int.cast_smul_eq_zsmul] using hx
      simpa using (W.smul_mem_iff (Int.cast_ne_zero.2 hn)).1 hx'
  have : Module.Free ℤ (Δ ⧸ (W.restrictScalars ℤ).comap Δ.subtype) :=
    Module.free_of_finite_type_torsion_free'
  let b := (c.map (comapSubtypeEquiv Δ W).symm).sumQuot
    (Module.finBasis ℤ (Δ ⧸ (W.restrictScalars ℤ).comap Δ.subtype))
  refine ⟨_, b, ?_, fun i ↦ by simp [b, comapSubtypeEquiv]⟩
  have := Module.Finite.finite_basis b
  have : Finite ι := .of_injective (β := ι ⊕ Fin (finrank ℤ (Δ ⧸ (W.restrictScalars ℤ).comap
    Δ.subtype))) Sum.inl Sum.inl_injective
  rw [Module.finrank_eq_nat_card_basis b, Nat.card_sum, Nat.card_fin]

/-- **A basis adapted to a rational subspace.** If the intersection of a full lattice `Δ` with a
real subspace `W` spans `W`, then `Δ` has a `ℤ`-basis `b` indexed by `Fin (dim W) ⊕ Fin s`, with
`dim W + s = dim E`, whose first block is a `ℤ`-basis `c` of `Δ ∩ W`. No orthogonality of the
second block to `W` is asserted. -/
theorem exists_basis_sum_finrank [FiniteDimensional ℝ E] (Δ : Submodule ℤ E) [DiscreteTopology Δ]
    [IsZLattice ℝ Δ] {W : Submodule ℝ E}
    (hW : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤) :
    ∃ (s : ℕ) (b : Basis (Fin (finrank ℝ W) ⊕ Fin s) ℤ Δ)
      (c : Basis (Fin (finrank ℝ W)) ℤ (ZLattice.comap ℝ Δ W.subtype)),
      finrank ℝ W + s = finrank ℝ E ∧ ∀ i, (b (.inl i) : E) = c i := by
  have : IsZLattice ℝ (ZLattice.comap ℝ Δ W.subtype) := ⟨hW⟩
  let c := Module.finBasisOfFinrankEq ℤ _ (ZLattice.rank ℝ (ZLattice.comap ℝ Δ W.subtype))
  obtain ⟨s, b, hs, hb⟩ := exists_basis_sum_inl_eq Δ W c
  exact ⟨s, b, c, by rwa [Nat.card_fin, ZLattice.rank ℝ Δ] at hs, hb⟩

/-- If the first block of a basis `b` of `Δ` is a basis `c` of `Δ ∩ W`, and `Δ ∩ W` spans `W`, then
the first block of `b` spans `W` over `ℝ`. -/
theorem span_range_ofZLatticeBasis_inl [FiniteDimensional ℝ E] {Δ : Submodule ℤ E}
    [DiscreteTopology Δ] [IsZLattice ℝ Δ] {W : Submodule ℝ E} {ι κ : Type*}
    (hL : span ℝ (ZLattice.comap ℝ Δ W.subtype : Set W) = ⊤) (b : Basis (ι ⊕ κ) ℤ Δ)
    (c : Basis ι ℤ (ZLattice.comap ℝ Δ W.subtype)) (hbc : ∀ i, (b (.inl i) : E) = c i) :
    span ℝ (Set.range (b.ofZLatticeBasis ℝ Δ ∘ Sum.inl)) = W := by
  have : IsZLattice ℝ (ZLattice.comap ℝ Δ W.subtype) := ⟨hL⟩
  have hcomp : b.ofZLatticeBasis ℝ Δ ∘ Sum.inl = W.subtype ∘ c.ofZLatticeBasis ℝ _ := by
    ext i
    simp [hbc]
  rw [hcomp, Set.range_comp, ← Submodule.map_span, Basis.span_eq, Submodule.map_top,
    range_subtype]

end Saturated

end ZLattice
