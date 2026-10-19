/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Linear maps with range in a finitely generated submodule

A linear map `f : M →ₗ[R] N` is of *finite rank* (`LinearMap.IsFiniteRank`) if its range is
contained in a finitely generated submodule of `N`. This is the notion of finite image used for
operators on Banach modules over a coefficient ring: the completely continuous operators
(`ContinuousLinearMap.IsCompletelyContinuous`) are those that, for every `ε > 0`, are uniformly
within `ε * ‖x‖` of a continuous map of finite rank; over Tate scalars this is approximation in
the operator norm.

Mathlib's `LinearMap.HasFiniteRange` asks the range itself to be finitely generated. Over a
general ring a submodule of a finitely generated module need not be finitely generated, so that
predicate is not stable under addition or under precomposition. Asking only for a finitely
generated submodule containing the range repairs this: maps of finite rank are closed under
addition, negation, scalar multiplication and composition on either side by arbitrary linear maps,
over any ring. Over a Noetherian ring the two notions coincide
(`LinearMap.isFiniteRank_iff_hasFiniteRange`).

## Main definitions

* `LinearMap.IsFiniteRank`: the range of `f` is contained in a finitely generated submodule.

## Main results

* `LinearMap.HasFiniteRange.isFiniteRank`: a map with finitely generated range has finite rank.
* `LinearMap.isFiniteRank_iff_hasFiniteRange`: over a Noetherian ring, finite rank is equivalent to
  finitely generated range.
* `LinearMap.IsFiniteRank.add`, `LinearMap.IsFiniteRank.smul`, `LinearMap.IsFiniteRank.comp_left`,
  `LinearMap.IsFiniteRank.comp_right`: the closure properties, with no Noetherian hypothesis.

## References

* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
-/

public section

open Submodule

namespace LinearMap

variable {R M N P : Type*}

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- A linear map is of **finite rank** if its range is contained in a finitely generated
submodule of its codomain. Over a Noetherian ring this is `LinearMap.HasFiniteRange`
(`LinearMap.isFiniteRank_iff_hasFiniteRange`); in general it is weaker. -/
def IsFiniteRank (f : M →ₗ[R] N) : Prop :=
  ∃ Q : Submodule R N, Q.FG ∧ range f ≤ Q

theorem isFiniteRank_iff {f : M →ₗ[R] N} :
    f.IsFiniteRank ↔ ∃ Q : Submodule R N, Q.FG ∧ range f ≤ Q :=
  Iff.rfl

/-- A linear map has finite rank if and only if all its values lie in a common finitely generated
submodule. -/
theorem isFiniteRank_iff_forall_mem {f : M →ₗ[R] N} :
    f.IsFiniteRank ↔ ∃ Q : Submodule R N, Q.FG ∧ ∀ x, f x ∈ Q :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦ ⟨fun h x ↦ h (mem_range_self f x),
    fun h ↦ by rintro _ ⟨x, rfl⟩; exact h x⟩

theorem HasFiniteRange.isFiniteRank {f : M →ₗ[R] N} (hf : f.HasFiniteRange) : f.IsFiniteRank :=
  ⟨range f, hf, le_rfl⟩

@[simp]
theorem IsFiniteRank.zero : (0 : M →ₗ[R] N).IsFiniteRank :=
  HasFiniteRange.zero.isFiniteRank

/-- Every linear map into a finitely generated module has finite rank. -/
@[simp]
theorem IsFiniteRank.of_finite_rng [Module.Finite R N] {f : M →ₗ[R] N} : f.IsFiniteRank :=
  ⟨⊤, Module.Finite.fg_top, le_top⟩

theorem IsFiniteRank.add {f g : M →ₗ[R] N} (hf : f.IsFiniteRank) (hg : g.IsFiniteRank) :
    (f + g).IsFiniteRank := by
  obtain ⟨Q₁, hQ₁, hf⟩ := hf
  obtain ⟨Q₂, hQ₂, hg⟩ := hg
  exact ⟨Q₁ ⊔ Q₂, hQ₁.sup hQ₂, (range_add_le f g).trans (sup_le_sup hf hg)⟩

/-- Postcomposing a map of finite rank with any linear map gives a map of finite rank. -/
theorem IsFiniteRank.comp_left {f : M →ₗ[R] N} (hf : f.IsFiniteRank) (g : N →ₗ[R] P) :
    (g ∘ₗ f).IsFiniteRank := by
  obtain ⟨Q, hQ, hf⟩ := hf
  exact ⟨Q.map g, hQ.map g, by rw [range_comp]; exact map_mono hf⟩

/-- Precomposing a map of finite rank with any linear map gives a map of finite rank. Unlike
`LinearMap.HasFiniteRange.comp_right`, this needs no Noetherian hypothesis. -/
theorem IsFiniteRank.comp_right {g : N →ₗ[R] P} (hg : g.IsFiniteRank) (f : M →ₗ[R] N) :
    (g ∘ₗ f).IsFiniteRank := by
  obtain ⟨Q, hQ, hg⟩ := hg
  exact ⟨Q, hQ, (range_comp_le_range f g).trans hg⟩

theorem IsFiniteRank.smul {S : Type*} [Monoid S] [DistribMulAction S N] [SMulCommClass R S N]
    {f : M →ₗ[R] N} (hf : f.IsFiniteRank) (c : S) : (c • f).IsFiniteRank := by
  have h : (c • LinearMap.id) ∘ₗ f = c • f := by ext; simp
  exact h ▸ hf.comp_left _

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem IsFiniteRank.neg {f : M →ₗ[R] N} (hf : f.IsFiniteRank) : (-f).IsFiniteRank := by
  rwa [IsFiniteRank, range_neg]

/-- Finite rank is invariant under negation. -/
@[simp]
theorem IsFiniteRank.neg_iff {f : M →ₗ[R] N} : (-f).IsFiniteRank ↔ f.IsFiniteRank :=
  ⟨fun hf ↦ by simpa using hf.neg, IsFiniteRank.neg⟩

theorem IsFiniteRank.sub {f g : M →ₗ[R] N} (hf : f.IsFiniteRank) (hg : g.IsFiniteRank) :
    (f - g).IsFiniteRank :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

/-- Over a Noetherian ring, a map of finite rank has finitely generated range. -/
theorem IsFiniteRank.hasFiniteRange [IsNoetherianRing R] {f : M →ₗ[R] N} (hf : f.IsFiniteRank) :
    f.HasFiniteRange := by
  obtain ⟨Q, hQ, hf⟩ := hf
  exact hQ.of_le hf

/-- Over a Noetherian ring, a linear map has finite rank if and only if its range is finitely
generated. -/
theorem isFiniteRank_iff_hasFiniteRange [IsNoetherianRing R] {f : M →ₗ[R] N} :
    f.IsFiniteRank ↔ f.HasFiniteRange :=
  ⟨IsFiniteRank.hasFiniteRange, HasFiniteRange.isFiniteRank⟩

end Ring

end LinearMap
