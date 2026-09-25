/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Combinatorics.Quiver.BoundedPaths
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Grading

/-!
# Paths ending at a vertex

For a quiver `R`, `pathsInto k n j` is the span in its path algebra of paths of length `n`
ending at `j`. This file describes the span through the path-length grading and the vertex
idempotent, proves its multiplication and last-arrow decomposition, and counts its dimension.
These results apply to path algebras independently of any relations.

## Main results

* `TauCeti.PathAlgebra.pathsInto`: the span of paths of length `n` ending at `j`.
* `TauCeti.PathAlgebra.mem_pathsInto_iff`: the span is the degree-`n` part of the corner at `j`.
* `TauCeti.PathAlgebra.mul_mem_pathsInto`: multiplication adds path lengths.
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

/-- Prolonging a path of length `n` by an arrow into `j` gives a path of length `n + 1` into `j`,
and distinct arrows or paths give distinct prolongations. -/
theorem card_arrow_mul_card_pathInto_le [Fintype R] [∀ a b : R, Fintype (a ⟶ b)]
    (n : ℕ) (j : R) :
    ∑ i : R, Fintype.card (i ⟶ j) * Nat.card (PathInto R n i) ≤
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
  calc ∑ i : R, Fintype.card (i ⟶ j) * Nat.card (PathInto R n i)
      = Nat.card (Σ i : R, (i ⟶ j) × PathInto R n i) := by
        rw [Nat.card_sigma]
        simp [Nat.card_prod, Nat.card_eq_fintype_card]
    _ ≤ Nat.card (PathInto R (n + 1) j) := Nat.card_le_card_of_injective g hg

variable (k : Type w)

section Semiring

variable [CommSemiring k]

/-- The span of the paths of length `n` ending at `j`: the degree-`n` part of the left corner
`e_j kR` (`TauCeti.PathAlgebra.mem_pathsInto_iff`). -/
noncomputable def pathsInto (n : ℕ) (j : R) : Submodule k (pathAlgebra k R) :=
  Submodule.span k
    (Set.range fun p : PathInto R n j => (ofPath ⟨p.1.1, j, p.1.2⟩ : pathAlgebra k R))

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
        · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
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

end Field

end PathAlgebra

end TauCeti
