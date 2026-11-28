/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Generation
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Descent of characters to cyclic quotients

Let `g` generate a dense subgroup of `G`, and let `q : G → Q` be a continuous
surjection onto a discrete group. The image of `g` generates `Q` algebraically.
A continuous character `χ` descends through `q` exactly when the order of `χ g`
divides the order of `q g`. The forward implication tests the relation on the
generator. For the converse, Mathlib's `monoidHomOfForallMemZpowers` constructs
the character downstairs, and density identifies its pullback.

In a tower of cyclic quotients of orders `p ^ n`, this computes the first level
of a character of exact order `p ^ r`, including the trivial character at level zero.
For the use of the first level in the conductor of anticyclotomic characters, see
Burungale, Kobayashi and Ota, *Rubin's conjecture on local units in the
anticyclotomic tower at inert primes*, §2.
-/

public section

namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {g : G}

/-- A continuous character factors through a discrete quotient exactly when the order of
its value on a topological generator divides the cardinality of the quotient. -/
theorem exists_comp_eq_iff_orderOf_apply_dvd_natCard
    {A Q : Type*} [Monoid A] [TopologicalSpace A] [T2Space A]
    [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (χ : G →ₜ* A) (q : G →ₜ* Q) (hq : Function.Surjective q)
    (hg : (Subgroup.closure {g}).topologicalClosure = ⊤) :
    (∃ ψ : Q →ₜ* A, ψ.comp q = χ) ↔ orderOf (χ g) ∣ Nat.card Q := by
  have hgen : Subgroup.zpowers (q g) = ⊤ := by
    simpa [Subgroup.zpowers_eq_closure] using
      TauCeti.closure_image_eq_top_of_discreteTopology hg (f := q.toMonoidHom) q.continuous hq
  have hQ := (Subgroup.zpowers (q g)).eq_top_iff'.mp hgen
  rw [← orderOf_eq_card_of_forall_mem_zpowers hQ]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact orderOf_map_dvd ψ.toMonoidHom (q g)
  · intro h
    have hu : orderOf (χ.toMonoidHom.toHomUnits g) ∣ orderOf (q g) := by
      rwa [← orderOf_units, MonoidHom.coe_toHomUnits]
    let f := (Units.coeHom A).comp (monoidHomOfForallMemZpowers hQ hu)
    let ψ : Q →ₜ* A := ⟨f, continuous_of_discreteTopology⟩
    refine ⟨ψ, toMonoidHom_injective ?_⟩
    apply MonoidHom.eq_of_eqOn_of_topologicalClosure_closure_eq_top hg
      (ψ.comp q).continuous χ.continuous
    simp [Set.eqOn_singleton, ψ, f]

variable {A : Type*} [CommMonoid A] [TopologicalSpace A] [ContinuousMul A] [T2Space A]

/-- In a family of discrete quotients of sizes `p ^ n` of a topologically cyclic group, the
least level through which a character of order `p ^ r` factors is `r`. -/
theorem isLeast_level_of_orderOf_eq_pow (χ : G →ₜ* A)
    (hg : (Subgroup.closure {g}).topologicalClosure = ⊤)
    {p r : ℕ} (hp : 1 < p) (hχ : orderOf χ = p ^ r)
    {Q : ℕ → Type*} [∀ n, Group (Q n)] [∀ n, TopologicalSpace (Q n)]
    [∀ n, DiscreteTopology (Q n)] (q : ∀ n, G →ₜ* Q n)
    (hq : ∀ n, Function.Surjective (q n)) (hcard : ∀ n, Nat.card (Q n) = p ^ n) :
    IsLeast {n | ∃ ψ : Q n →ₜ* A, ψ.comp (q n) = χ} r := by
  have hlevel (n : ℕ) : (∃ ψ : Q n →ₜ* A, ψ.comp (q n) = χ) ↔ r ≤ n := by
    rw [χ.exists_comp_eq_iff_orderOf_apply_dvd_natCard (q n) (hq n) hg,
      χ.orderOf_apply_eq_of_topologicalGenerator hg, hχ, hcard, Nat.pow_dvd_pow_iff_le_right hp]
  exact ⟨(hlevel r).2 le_rfl, fun n hn ↦ (hlevel n).1 hn⟩

end ContinuousMonoidHom
