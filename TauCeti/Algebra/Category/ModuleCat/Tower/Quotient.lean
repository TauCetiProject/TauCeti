/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Topology

/-!
# Completion of a module along a decreasing family of submodules

Let `J₀ ⊇ J₁ ⊇ J₂ ⊇ ⋯` be a decreasing family of submodules of a module `M` over a ring `R`, which
need not be commutative. The quotients `M ⧸ J₀ ← M ⧸ J₁ ← M ⧸ J₂ ← ⋯`, with the quotient maps
`Submodule.factor` as transitions, form a tower (`TauCeti.ModuleTower.quotients`). Its limit,
with the inverse limit topology of `TauCeti.Algebra.Category.ModuleCat.Tower.Topology`, is the
completion of `M` for the linear topology in which the `Jₙ` form a basis of neighbourhoods of
zero.

The canonical map `M → lim M ⧸ Jₙ` (`TauCeti.ModuleTower.toLimQuotients`) sends `x` to the family
of its classes. Its kernel is the intersection of the `Jₙ`, so it is injective exactly when this
topology on `M` is Hausdorff; the preimage of the kernel of the `n`-th projection is `Jₙ`, so the
topology induced on `M` is the `J`-topology; and its range is dense. The projections of the limit
are surjective, since the transitions are.

The ideal-power filtrations `Iⁿ⁺¹ M` of a commutative ring are handled by the dedicated tower
`TauCeti.ModuleTower.reduction`, whose limit is Mathlib's `AdicCompletion`. The present
construction allows arbitrary decreasing families over noncommutative rings, such as the left
ideals of high-order currents in an enveloping algebra of an affine Lie algebra at a fixed level.

## Main definitions

* `TauCeti.ModuleTower.quotients`: the tower of quotients `M ⧸ Jₙ`.
* `TauCeti.ModuleTower.quotientsπ`: the quotient maps `M → M ⧸ Jₙ`.
* `TauCeti.ModuleTower.toLimQuotients`: the canonical map `M → lim M ⧸ Jₙ`.

## Main results

* `TauCeti.ModuleTower.limπ_quotients_surjective`: the projections of the limit are surjective.
* `TauCeti.ModuleTower.ker_toLimQuotients`: the kernel of the canonical map is `⨅ n, Jₙ`.
* `TauCeti.ModuleTower.comap_toLimQuotients_ker_limπ`: the canonical map pulls the kernel of the
  `n`-th projection back to `Jₙ`.
* `TauCeti.ModuleTower.denseRange_toLimQuotients`: the canonical map has dense range.

## References

* N. Bourbaki, *Commutative Algebra*, Chapter III, §2, for completions of modules for linear
  topologies.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite

universe v u

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
  (J : ℕ → Submodule R M) (hJ : Antitone J)

/-- The tower `M ⧸ J₀ ← M ⧸ J₁ ← M ⧸ J₂ ← ⋯` of quotients of a module `M` by a decreasing family
of submodules `Jₙ`, with the quotient maps as transitions. Its terms are handled through the
quotient maps `ModuleTower.quotientsπ`. -/
def quotients : ModuleTower.{v} R where
  obj n := ModuleCat.of R (M ⧸ J n.unop)
  map f := ModuleCat.ofHom (Submodule.factor (hJ (leOfHom f.unop)))
  -- The composites of quotient maps are quotient maps, by definition of `Submodule.factor`.
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The `n`-th term of the tower of quotients is `M ⧸ Jₙ`. -/
theorem quotients_obj (n : ℕ) : (quotients J hJ).obj (op n) = ModuleCat.of R (M ⧸ J n) :=
  (rfl)

/-- The quotient map from `M` onto the `n`-th term `M ⧸ Jₙ` of the tower of quotients. -/
def quotientsπ (n : ℕ) : M →ₗ[R] (quotients J hJ).obj (op n) :=
  (J n).mkQ

theorem quotientsπ_surjective (n : ℕ) : Function.Surjective (quotientsπ J hJ n) :=
  Submodule.mkQ_surjective _

@[simp]
theorem ker_quotientsπ (n : ℕ) : LinearMap.ker (quotientsπ J hJ n) = J n :=
  Submodule.ker_mkQ _

@[simp]
theorem quotientsπ_eq_zero_iff {n : ℕ} {x : M} : quotientsπ J hJ n x = 0 ↔ x ∈ J n := by
  rw [← LinearMap.mem_ker, ker_quotientsπ]

@[simp]
theorem transitionOfLE_quotientsπ {n k : ℕ} (h : n ≤ k) (x : M) :
    (quotients J hJ).transitionOfLE h (quotientsπ J hJ k x) = quotientsπ J hJ n x := by
  -- The transitions of `quotients` are the quotient maps `Submodule.factor`, by definition.
  rw [transitionOfLE_def]
  rfl

@[simp]
theorem transitionOfLE_comp_quotientsπ {n k : ℕ} (h : n ≤ k) :
    (quotients J hJ).transitionOfLE h ∘ₗ quotientsπ J hJ k = quotientsπ J hJ n :=
  LinearMap.ext (transitionOfLE_quotientsπ J hJ h)

@[simp]
theorem transition_comp_quotientsπ (n : ℕ) :
    (quotients J hJ).transition n ∘ₗ quotientsπ J hJ (n + 1) = quotientsπ J hJ n := by
  rw [← transitionOfLE_succ, transitionOfLE_comp_quotientsπ]

@[simp]
theorem transition_quotientsπ (n : ℕ) (x : M) :
    (quotients J hJ).transition n (quotientsπ J hJ (n + 1) x) = quotientsπ J hJ n x :=
  LinearMap.congr_fun (transition_comp_quotientsπ J hJ n) x

/-- The transitions of the tower of quotients are surjective. -/
theorem transition_quotients_surjective (n : ℕ) :
    Function.Surjective ((quotients J hJ).transition n) := by
  rw [transition_def]
  exact Submodule.factor_surjective (hJ (Nat.le_succ n))

/-- The projections `lim M ⧸ Jₖ → M ⧸ Jₙ` of the limit of the tower of quotients are
surjective. -/
theorem limπ_quotients_surjective (n : ℕ) : Function.Surjective ((quotients J hJ).limπ n) :=
  limπ_surjective _ (transition_quotients_surjective J hJ) n

/-- The canonical map `M → lim M ⧸ Jₙ`, sending `x` to the family of its classes. -/
def toLimQuotients : M →ₗ[R] (quotients J hJ).lim :=
  (quotients J hJ).limLift (quotientsπ J hJ) (transition_comp_quotientsπ J hJ)

@[simp]
theorem limπ_comp_toLimQuotients (n : ℕ) :
    (quotients J hJ).limπ n ∘ₗ toLimQuotients J hJ = quotientsπ J hJ n := by
  rw [toLimQuotients, limπ_comp_limLift]

@[simp]
theorem coe_toLimQuotients_apply (x : M) (n : ℕ) :
    (toLimQuotients J hJ x : (quotients J hJ).Product) n = quotientsπ J hJ n x := by
  rw [← limπ_apply, ← LinearMap.comp_apply, limπ_comp_toLimQuotients]

/-- The canonical map pulls the kernel of the `n`-th projection back to `Jₙ`: the topology which
the limit induces on `M` is the linear topology defined by the `Jₙ`. -/
@[simp]
theorem comap_toLimQuotients_ker_limπ (n : ℕ) :
    (LinearMap.ker ((quotients J hJ).limπ n)).comap (toLimQuotients J hJ) = J n := by
  rw [← LinearMap.ker_comp, limπ_comp_toLimQuotients, ker_quotientsπ]

/-- The kernel of the canonical map `M → lim M ⧸ Jₙ` is the intersection of the `Jₙ`. -/
@[simp]
theorem ker_toLimQuotients : LinearMap.ker (toLimQuotients J hJ) = ⨅ n, J n := by
  simp only [toLimQuotients, ker_limLift, ker_quotientsπ]

/-- The canonical map `M → lim M ⧸ Jₙ` is injective exactly when the `Jₙ` intersect to zero. -/
theorem toLimQuotients_injective_iff :
    Function.Injective (toLimQuotients J hJ) ↔ ⨅ n, J n = ⊥ := by
  rw [← LinearMap.ker_eq_bot, ker_toLimQuotients]

/-- The canonical map `M → lim M ⧸ Jₙ` has dense range. -/
theorem denseRange_toLimQuotients : DenseRange (toLimQuotients J hJ) :=
  denseRange_iff.mpr fun x n ↦ by
    obtain ⟨y, hy⟩ := quotientsπ_surjective J hJ n ((quotients J hJ).limπ n x)
    exact ⟨y, by rw [limπ_apply, coe_toLimQuotients_apply, hy]⟩

end TauCeti.ModuleTower
