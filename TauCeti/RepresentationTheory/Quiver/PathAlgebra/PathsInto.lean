/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Combinatorics.Quiver.BoundedPaths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Corner
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# Paths ending at a vertex

For a quiver `R`, `pathsInto k n j` is the span in its path algebra of paths of length `n`
ending at `j`. This file describes the span through the path-length grading and the vertex
idempotent, proves its multiplication and last-arrow decomposition, and counts its dimension.
The last-arrow decomposition is unique: `∑_{b : i ⟶ j} b f_b` determines each `eᵢ f_b`. These
results apply to path algebras independently of any relations.

## Main results

* `TauCeti.PathAlgebra.pathsInto`: the span of paths of length `n` ending at `j`.
* `TauCeti.PathAlgebra.mem_pathsInto_iff`: the span is the degree-`n` part of the corner at `j`.
* `TauCeti.PathAlgebra.pathsBetween`: the degree-`n` part of the corner cut out by two vertices.
* `TauCeti.PathAlgebra.mem_pathsBetween_iff`: membership in that degree-`n` corner.
* `TauCeti.PathAlgebra.finrank_pathsBetween`: the dimension of that corner is the number of
  paths of the prescribed length between the vertices.
* `TauCeti.PathAlgebra.mul_mem_pathsInto`: multiplication adds path lengths.
* `TauCeti.PathAlgebra.exists_eq_sum_ofArrow_mul` and
  `TauCeti.PathAlgebra.sum_ofArrow_mul_eq_zero_iff`: existence and uniqueness of the last-arrow
  decomposition.
* `TauCeti.PathAlgebra.finrank_pathsInto`: its dimension is the number of paths into `j`.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

namespace PathAlgebra

variable {R : Type u} [Quiver.{v} R]

/-- The paths of length `n` ending at `j`, recorded together with their source. -/
abbrev PathInto (R : Type u) [Quiver.{v} R] (n : ℕ) (j : R) : Type _ :=
  {p : Σ s : R, Path s j // p.2.length = n}

/-- The paths of length `n` from `i` to `j`. -/
abbrev PathBetween (R : Type u) [Quiver.{v} R] (n : ℕ) (i j : R) : Type _ :=
  {p : Path i j // p.length = n}

private theorem pathInto_injective (n : ℕ) (j : R) :
    Function.Injective fun p : PathInto R n j => (⟨p.1.1, j, p.1.2⟩ : Quiver.TotalPath R) := by
  rintro ⟨⟨s, p⟩, hp⟩ ⟨⟨s', p'⟩, hp'⟩ h
  simp only [Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Sigma.mk.injEq, true_and] at h
  subst h
  rfl

/-- For a finite quiver, the paths of a fixed length into one vertex form a finite type. -/
instance finite_pathInto [Finite R] [∀ a b : R, Finite (a ⟶ b)] (n : ℕ) (j : R) :
    Finite (PathInto R n j) := by
  have := (TauCeti.Quiver.finite_setOf_length_le (V := R) n).to_subtype
  refine Finite.of_injective
    (fun p : PathInto R n j =>
      (⟨⟨p.1.1, j, p.1.2⟩, p.2.le⟩ : {x : Σ a b : R, Path a b | x.2.2.length ≤ n})) ?_
  intro p q h
  exact pathInto_injective n j (congrArg Subtype.val h)

/-- For a finite quiver, the paths of a fixed length between two vertices form a finite type. -/
instance finite_pathBetween [Finite R] [∀ a b : R, Finite (a ⟶ b)]
    (n : ℕ) (i j : R) : Finite (PathBetween R n i j) :=
  Finite.of_injective
    (fun p : PathBetween R n i j =>
      (⟨(⟨i, p.1⟩ : Σ s : R, Path s j), p.2⟩ : PathInto R n j))
    fun ⟨p, hp⟩ ⟨q, hq⟩ h => by
      simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] at h
      exact Subtype.ext h

/-- Every path of length `n + 1` into `j` has a unique last arrow and a length-`n` prefix. -/
theorem card_arrow_mul_card_pathInto_eq [Fintype R] [∀ a b : R, Fintype (a ⟶ b)]
    (n : ℕ) (j : R) :
    ∑ i : R, Fintype.card (i ⟶ j) * Nat.card (PathInto R n i) =
      Nat.card (PathInto R (n + 1) j) := by
  let g : (Σ i : R, (i ⟶ j) × PathInto R n i) → PathInto R (n + 1) j :=
    fun x => ⟨⟨x.2.2.1.1, x.2.2.1.2.cons x.2.1⟩, by simp [x.2.2.2]⟩
  have hg : Function.Injective g := by
    rintro ⟨i, b, ⟨⟨s, p⟩, hp⟩⟩ ⟨i', b', ⟨⟨s', p'⟩, hp'⟩⟩ h
    simp only [g, Subtype.mk.injEq, Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h' := eq_of_heq h
    obtain rfl := Path.obj_eq_of_cons_eq_cons h'
    simp only [Path.cons.injEq, heq_eq_eq, true_and] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rfl
  have hs : Function.Surjective g := by
    rintro ⟨⟨s, p⟩, hp⟩
    cases p with
    | nil => simp at hp
    | @cons i _ q b =>
      simp only [Path.length_cons, Nat.add_right_cancel_iff] at hp
      exact ⟨⟨i, b, ⟨⟨s, q⟩, hp⟩⟩, rfl⟩
  calc ∑ i : R, Fintype.card (i ⟶ j) * Nat.card (PathInto R n i)
      = Nat.card (Σ i : R, (i ⟶ j) × PathInto R n i) := by
        rw [Nat.card_sigma]
        simp [Nat.card_prod, Nat.card_eq_fintype_card]
    _ = Nat.card (PathInto R (n + 1) j) := Nat.card_congr (Equiv.ofBijective g ⟨hg, hs⟩)

variable (k : Type w)

section Semiring

variable [CommSemiring k]

/-- The span of the paths of length `n` ending at `j`: the degree-`n` part of the left corner
`e_j kR` (`TauCeti.PathAlgebra.mem_pathsInto_iff`). -/
noncomputable def pathsInto (n : ℕ) (j : R) : Submodule k (pathAlgebra k R) :=
  Submodule.span k
    (Set.range fun p : PathInto R n j => (ofPath ⟨p.1.1, j, p.1.2⟩ : pathAlgebra k R))

/-- The span of paths of length `n` from `i` to `j`: the degree-`n` part of the corner
`e_j kR e_i`. -/
noncomputable def pathsBetween (n : ℕ) (i j : R) : Submodule k (pathAlgebra k R) :=
  Submodule.span k
    (Set.range fun p : PathBetween R n i j => (ofPath ⟨i, j, p.1⟩ : pathAlgebra k R))

variable {k}

/-- A path ending at `j` lies in the span of the paths of its length into `j`. -/
theorem ofPath_mem_pathsInto {s j : R} (p : Path s j) :
    (ofPath ⟨s, j, p⟩ : pathAlgebra k R) ∈ pathsInto k p.length j :=
  Submodule.subset_span ⟨⟨⟨s, p⟩, rfl⟩, rfl⟩

/-- A path of length `n` ending at `j` lies in the span of the paths of length `n` into `j`. -/
theorem ofPath_mem_pathsInto_of_length {s j : R} {n : ℕ} (p : Path s j)
    (hp : p.length = n) : (ofPath ⟨s, j, p⟩ : pathAlgebra k R) ∈ pathsInto k n j :=
  hp ▸ ofPath_mem_pathsInto p

private theorem ofArrow_mem_pathsInto {i j : R} (b : i ⟶ j) :
    (ofArrow b : pathAlgebra k R) ∈ pathsInto k 1 j := by
  rw [ofArrow_eq_ofPath]
  exact ofPath_mem_pathsInto_of_length _ (Path.length_toPath b)

/-- The paths of length `n` into `j` span a subspace of the degree-`n` part of the path algebra. -/
theorem pathsInto_le_grade (n : ℕ) (j : R) : pathsInto k n j ≤ grade k R n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨⟨s, p⟩, hp⟩, rfl⟩
  exact ofPath_mem_grade_of_length hp

/-- A vertex idempotent acts as the identity on paths ending at that vertex. -/
theorem vertexIdempotent_mul_of_mem_pathsInto {n : ℕ} {j : R} {x : pathAlgebra k R}
    (hx : x ∈ pathsInto k n j) : vertexIdempotent k j * x = x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨⟨s, p⟩, hp⟩, rfl⟩ := hy
    exact vertexIdempotent_mul_ofPath p
  | zero => exact mul_zero _
  | add y z _ _ hy hz => rw [mul_add, hy, hz]
  | smul c y _ hy => rw [mul_smul_comm, hy]

/-- Projecting a homogeneous element to the corner at `j` gives a path span into `j`. -/
theorem vertexIdempotent_mul_mem_pathsInto {n : ℕ} (j : R) {x : pathAlgebra k R}
    (hx : x ∈ grade k R n) : vertexIdempotent k j * x ∈ pathsInto k n j := by
  rw [grade_eq_span_range] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨⟨s, t, p⟩, hp⟩, rfl⟩ := hy
    by_cases h : t = j
    · subst h
      rw [vertexIdempotent_mul_ofPath]
      exact ofPath_mem_pathsInto_of_length p hp
    · rw [vertexIdempotent_mul_ofPath_of_ne _ (Ne.symm h)]
      exact zero_mem _
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy

/-- **The span of the paths of length `n` into `j` is the degree-`n` part of the corner
`e_j kR`.** -/
@[simp]
theorem mem_pathsInto_iff {n : ℕ} {j : R} {x : pathAlgebra k R} :
    x ∈ pathsInto k n j ↔ x ∈ grade k R n ∧ vertexIdempotent k j * x = x :=
  ⟨fun hx => ⟨pathsInto_le_grade n j hx, vertexIdempotent_mul_of_mem_pathsInto hx⟩,
    fun ⟨hx, hjx⟩ => hjx ▸ vertexIdempotent_mul_mem_pathsInto j hx⟩

/-- **The paths of length `n` from `i` to `j` span the degree-`n` part of the corner
`e_j kR e_i`.** -/
@[simp]
theorem mem_pathsBetween_iff {n : ℕ} {i j : R} {x : pathAlgebra k R} :
    x ∈ pathsBetween k n i j ↔
      x ∈ grade k R n ∧ vertexIdempotent k j * x * vertexIdempotent k i = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨p, rfl⟩ := hy
        exact ⟨ofPath_mem_grade_of_length p.2,
          by rw [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent]⟩
    | zero => simp
    | add y z _ _ hy hz =>
        exact ⟨add_mem hy.1 hz.1, by rw [mul_add, add_mul, hy.2, hz.2]⟩
    | smul c y _ hy =>
        exact ⟨Submodule.smul_mem _ c hy.1, by rw [mul_smul_comm, smul_mul_assoc, hy.2]⟩
  · rintro ⟨hgrade, hcorner⟩
    rw [← hcorner]
    clear hcorner
    rw [grade_eq_span_range] at hgrade
    induction hgrade using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨⟨a, b, p⟩, hp⟩, rfl⟩ := hx
        dsimp only
        by_cases ha : a = i
        · subst a
          by_cases hb : b = j
          · subst b
            rw [vertexIdempotent_mul_ofPath, ofPath_mul_vertexIdempotent, pathsBetween]
            exact Submodule.subset_span
              (Set.mem_range_self (⟨p, hp⟩ : PathBetween R n i j))
          · rw [vertexIdempotent_mul_ofPath_of_ne _ (Ne.symm hb), zero_mul]
            exact Submodule.zero_mem _
        · rw [mul_assoc, ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm ha), mul_zero]
          exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add, add_mul] using add_mem hx hy
    | smul r x _ hx =>
        simpa only [mul_smul_comm, smul_mul_assoc] using Submodule.smul_mem _ r hx

/-- **The paths of fixed length between two vertices form the corresponding graded corner.** -/
theorem pathsBetween_eq_cornerSubmodule_inf_grade (n : ℕ) (i j : R) :
    pathsBetween k n i j =
      cornerSubmodule k (vertexIdempotent k j) (vertexIdempotent k i) ⊓ grade k R n := by
  ext x
  rw [mem_pathsBetween_iff, Submodule.mem_inf, mem_cornerSubmodule_iff k
    (vertexIdempotent_mul_self (k := k) j) (vertexIdempotent_mul_self (k := k) i), and_comm]

/-- The product of an element of `pathsInto k a i` and one of `pathsInto k c j` lies in
`pathsInto k (c + a) i`: the paths of the right factor are followed by those of the left one. -/
theorem mul_mem_pathsInto {a c : ℕ} {i j : R} {x y : pathAlgebra k R}
    (hx : x ∈ pathsInto k a i) (hy : y ∈ pathsInto k c j) : x * y ∈ pathsInto k (c + a) i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨⟨s, p⟩, hp⟩, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨⟨s', q⟩, hq⟩, rfl⟩ := hy
      by_cases h : j = s
      · subst h
        rw [ofPath_mul_ofPath_of_comp]
        exact ofPath_mem_pathsInto_of_length _ (by rw [Path.length_comp, hp, hq])
      · rw [ofPath_mul_ofPath_of_not_composable h]
        exact zero_mem _
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul r y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx

private theorem ofArrow_mul_mem_pathsInto {n : ℕ} {i j : R} (b : i ⟶ j) {x : pathAlgebra k R}
    (hx : x ∈ pathsInto k n i) : ofArrow b * x ∈ pathsInto k (n + 1) j :=
  mul_mem_pathsInto (ofArrow_mem_pathsInto b) hx

/-- **Last-arrow decomposition.** An element of the span of the paths of length `n + 1` into `j`
is a sum, over the arrows `b : i ⟶ j`, of `b` times an element of the span of the paths of length
`n` into `i`. -/
theorem exists_eq_sum_ofArrow_mul [Fintype R] [∀ a b : R, Fintype (a ⟶ b)] {n : ℕ} {j : R}
    {x : pathAlgebra k R} (hx : x ∈ pathsInto k (n + 1) j) :
    ∃ z : (i : R) → (i ⟶ j) → pathAlgebra k R, (∀ i b, z i b ∈ pathsInto k n i) ∧
      x = ∑ i, ∑ b : i ⟶ j, ofArrow b * z i b := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨⟨s, p⟩, hp⟩, rfl⟩ := hx
    cases p with
    | nil => simp at hp
    | @cons m _ q b =>
      simp only [Path.length_cons, Nat.add_right_cancel_iff] at hp
      refine ⟨fun i b' => if (⟨i, b'⟩ : Σ i, (i ⟶ j)) = ⟨m, b⟩ then ofPath ⟨s, m, q⟩ else 0,
        fun i b' => ?_, ?_⟩
      · dsimp only
        split_ifs with h
        · obtain ⟨rfl, _⟩ := Sigma.mk.inj h
          exact ofPath_mem_pathsInto_of_length q hp
        · exact zero_mem _
      · dsimp only
        rw [Finset.sum_eq_single m, Finset.sum_eq_single b]
        · simp
        · intro b' _ hb'
          simp [hb']
        · simp
        · intro i _ hi
          refine Finset.sum_eq_zero fun b' _ => ?_
          simp [hi]
        · simp
  | zero => exact ⟨0, fun _ _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨z', hz', rfl⟩ := hy
    refine ⟨z + z', fun i b => add_mem (hz i b) (hz' i b), ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    refine ⟨c • z, fun i b => Submodule.smul_mem _ c (hz i b), ?_⟩
    simp only [Pi.smul_apply, mul_smul_comm, Finset.smul_sum]

/-- **Uniqueness of the last-arrow decomposition.** A sum `∑_{b : i ⟶ j} b f_b` vanishes exactly
when each `f_b` is killed by the vertex idempotent at the source of `b`: the paths `q` followed by
distinct arrows `b` into `j` are distinct basis paths. Only the part `eᵢ f_b` of `f_b` on paths
ending at `i` contributes to `b f_b`. -/
theorem sum_ofArrow_mul_eq_zero_iff [Fintype R] [∀ a b : R, Fintype (a ⟶ b)] {j : R}
    {f : (i : R) → (i ⟶ j) → pathAlgebra k R} :
    ∑ i, ∑ b : i ⟶ j, ofArrow b * f i b = 0 ↔ ∀ i b, vertexIdempotent k i * f i b = 0 := by
  classical
  constructor
  · intro h i b
    refine (pathAlgebraBasis k R).repr.injective (Finsupp.ext fun x => ?_)
    obtain ⟨s, t, q⟩ := x
    rw [pathAlgebraBasis_repr_vertexIdempotent_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with ht
    · subst ht
      -- Read off the coordinate of the sum on the path `q` followed by `b`.
      have h' := congrArg (fun F => (pathAlgebraBasis k R).repr F ⟨s, j, q.cons b⟩) h
      simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at h'
      rw [Finset.sum_eq_single t, Finset.sum_eq_single b,
        pathAlgebraBasis_repr_ofArrow_mul_cons] at h'
      · exact h'
      · intro b' _ hb'
        exact pathAlgebraBasis_repr_ofArrow_mul_cons_of_ne b b' (by simpa using hb') q _
      · simp
      · intro i' _ hi'
        exact Finset.sum_eq_zero fun b' _ => pathAlgebraBasis_repr_ofArrow_mul_cons_of_ne b b'
          (fun he => hi' (congrArg Sigma.fst he)) q _
      · simp
    · rfl
  · intro h
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
    rw [ofArrow_eq_ofPath, ← ofPath_mul_vertexIdempotent, mul_assoc, h, mul_zero]

end Semiring

section Field

variable [Field k]

instance finiteDimensional_pathsInto [Finite R] [∀ a b : R, Finite (a ⟶ b)] (n : ℕ)
    (j : R) : FiniteDimensional k (pathsInto k n j) :=
  FiniteDimensional.span_of_finite k (Set.finite_range _)

/-- The dimension of the span of the paths of length `n` into `j` is the number of such paths:
distinct paths are linearly independent in the path algebra. -/
theorem finrank_pathsInto [Finite R] [∀ a b : R, Finite (a ⟶ b)] (n : ℕ) (j : R) :
    Module.finrank k (pathsInto k n j) =
      Nat.card {p : Σ s : R, Path s j // p.2.length = n} := by
  have := Fintype.ofFinite (PathInto R n j)
  have hli : LinearIndependent k
      fun p : PathInto R n j => (ofPath ⟨p.1.1, j, p.1.2⟩ : pathAlgebra k R) := by
    have h := (pathAlgebraBasis k R).linearIndependent.comp _ (pathInto_injective n j)
    simpa only [coe_pathAlgebraBasis, Function.comp_def] using h
  rw [pathsInto, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

instance finiteDimensional_pathsBetween (n : ℕ) (i j : R) [Finite (PathBetween R n i j)] :
    FiniteDimensional k (pathsBetween k n i j) :=
  FiniteDimensional.span_of_finite k (Set.finite_range _)

/-- The dimension of the length-`n` corner from `i` to `j` is the number of length-`n` paths
from `i` to `j`. -/
theorem finrank_pathsBetween (n : ℕ) (i j : R) [Finite (PathBetween R n i j)] :
    Module.finrank k (pathsBetween k n i j) = Nat.card (PathBetween R n i j) := by
  have := Fintype.ofFinite (PathBetween R n i j)
  have hli : LinearIndependent k
      fun p : PathBetween R n i j => (ofPath ⟨i, j, p.1⟩ : pathAlgebra k R) := by
    have h := (pathAlgebraBasis k R).linearIndependent.comp
      (fun p : PathBetween R n i j => (⟨i, j, p.1⟩ : Quiver.TotalPath R))
      (fun ⟨p, hp⟩ ⟨q, hq⟩ h => by
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
        exact Subtype.ext h)
    simpa only [coe_pathAlgebraBasis, Function.comp_def] using h
  rw [pathsBetween, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

end Field

end PathAlgebra

end TauCeti
