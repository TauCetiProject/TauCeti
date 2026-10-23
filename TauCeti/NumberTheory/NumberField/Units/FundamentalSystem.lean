/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.NumberField.Units.Log.Embedding
import Mathlib.Data.Fin.Tuple.Sort
import TauCeti.Algebra.Module.ZLattice.GaugeBasis
import TauCeti.Algebra.Order.BigOperators.Factorial
import TauCeti.NumberTheory.NumberField.Units.Log.Ball

/-!
# Fundamental systems of units of bounded height

A family of units `ε` of a number field `K` is a fundamental system when, together with the
torsion subgroup, it generates the units: `Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤`. This
happens exactly when the logarithmic embeddings of the `ε i` span the unit lattice over `ℤ`, so
every `ℤ`-basis of the unit lattice lifts to a fundamental system.

A family `u` of `rank K` units with linearly independent logarithmic embeddings need not be a
fundamental system: it may generate a subgroup of finite index greater than one. Cassels' basis
lemma, applied to the unit lattice and the `ℓ¹` unit ball of the logarithmic space, replaces `u`
by a fundamental system `ε` whose logarithmic embeddings are almost as short in the `ℓ¹` norm.
When the `ℓ¹` norms of the `u j` increase with `j`, the `j`-th member of `ε` is at most
`max 1 ((j + 1) / 2)` times as long as `u j` (`ZLattice.exists_basis_gauge_le_max_one_mul`), so
the product of the norms grows at most by `r! / 2 ^ (r - 1)`, where `r = rank K`. The height of a
unit is bounded by the `ℓ¹` norm of its logarithmic embedding, so this bounds the product of the
heights of `ε` by `r! / 2 ^ (r - 1)` times the product of the `ℓ¹` norms of the `u j`. That
product does not depend on the order of the `u j`, so after sorting `u` by `ℓ¹` norm the product
bounds hold for every independent family.

Units realizing the successive minima of the unit lattice with respect to the `ℓ¹` ball have
increasing `ℓ¹` norms, and Minkowski's second theorem bounds the product of these norms by
`r! * regulator K`. For such `u` the product bound becomes Bugeaud and Győry's reduced fundamental
system, `∏ i, absLogHeight₁ (ε i) ≤ (r!) ^ 2 / (2 ^ (r - 1) * [K : ℚ] ^ r) * regulator K`.
Minkowski's second theorem is not proved in this file.

## Main results

* `TauCeti.NumberField.Units.span_logEmbedding_eq_unitLattice_iff`: a family of units is a
  fundamental system exactly when its logarithmic embeddings span the unit lattice.
* `TauCeti.NumberField.Units.closure_sup_torsion_eq_top_of_basis`: units whose logarithmic
  embeddings form a `ℤ`-basis of the unit lattice are a fundamental system.
* `TauCeti.NumberField.Units.exists_fundSystem_sum_abs_logEmbedding_le_max_one_mul`: a
  fundamental system whose `j`-th member has `ℓ¹` norm at most `max 1 ((j + 1) / 2)` times that of
  the `j`-th member of a given independent family with increasing `ℓ¹` norms.
* `TauCeti.NumberField.Units.exists_fundSystem_prod_logHeight₁_le_of_isMaxRank` and
  `TauCeti.NumberField.Units.exists_fundSystem_prod_absLogHeight₁_le_of_isMaxRank`: the resulting
  bounds for the product of the heights of the fundamental system.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959, Chapter V,
  Lemma 8.
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3, Lemma 1.

The construction follows Ralf Stephan's Apache-2.0 formalization in `rwst/Subspace-Theorems`
(`ArithmeticHeights/Regulator.lean`, the lemma `closure_sup_torsion_eq_top_of_span` and the proof
of `exists_fundSystem_prod_absLogHeight₁_le`).
-/

public section

open Height Module NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-! ### Fundamental systems and bases of the unit lattice -/

/-- A family of units generates the units together with the torsion subgroup exactly when the
logarithmic embeddings of its members span the unit lattice over `ℤ`. -/
theorem span_logEmbedding_eq_unitLattice_iff {ι : Type*} (ε : ι → (𝓞 K)ˣ) :
    Submodule.span ℤ (Set.range fun i ↦ logEmbedding K (Additive.ofMul (ε i))) =
        unitLattice K ↔
      Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ := by
  have hspan :
      (Submodule.span ℤ (Set.range fun i ↦ logEmbedding K (Additive.ofMul (ε i)))).toAddSubgroup =
        (Subgroup.closure (Set.range ε)).toAddSubgroup.map (logEmbedding K) := by
    rw [Subgroup.toAddSubgroup_closure, AddMonoidHom.map_closure,
      ← Submodule.span_int_eq_addSubgroupClosure]
    congr
    ext
    simp
  have hlat : (unitLattice K).toAddSubgroup = (⊤ : AddSubgroup (Additive (𝓞 K)ˣ)).map
      (logEmbedding K) := by
    ext
    simp [unitLattice]
  rw [← Submodule.toAddSubgroup_inj, hspan, hlat, AddSubgroup.map_eq_map_iff, logEmbedding_ker]
  simp [← map_sup]

/-- Units whose logarithmic embeddings form a `ℤ`-basis of the unit lattice generate the units
together with the torsion subgroup. -/
theorem closure_sup_torsion_eq_top_of_basis {ι : Type*} (b : Basis ι ℤ (unitLattice K))
    {ε : ι → (𝓞 K)ˣ} (hε : ∀ i, logEmbedding K (Additive.ofMul (ε i)) = b i) :
    Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ := by
  have h : (fun i ↦ logEmbedding K (Additive.ofMul (ε i))) = (unitLattice K).subtype ∘ b :=
    funext hε
  rw [← span_logEmbedding_eq_unitLattice_iff, h, Set.range_comp, ← Submodule.map_span, b.span_eq]
  simp

/-! ### Fundamental systems of controlled `ℓ¹` norm -/

open Classical in
/-- **A fundamental system from an increasing independent family of units.** If the logarithmic
embeddings of `u 0, …, u (r - 1)` are linearly independent and their `ℓ¹` norms increase, as
they do for units realizing the successive minima of the unit lattice with respect to the `ℓ¹`
ball, some fundamental system `ε` satisfies `‖log ε j‖₁ ≤ max 1 ((j + 1) / 2) * ‖log u j‖₁` for
every `j`. -/
theorem exists_fundSystem_sum_abs_logEmbedding_le_max_one_mul {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u)
    (hmono : Monotone fun i ↦ ∑ w, |logEmbedding K (Additive.ofMul (u i)) w|) :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
      ∀ j, ∑ w, |logEmbedding K (Additive.ofMul (ε j)) w| ≤
        max 1 ((((j : ℕ) : ℝ) + 1) / 2) * ∑ w, |logEmbedding K (Additive.ofMul (u j)) w| := by
  obtain ⟨b, hb⟩ := ZLattice.exists_basis_gauge_le_max_one_mul (unitLattice K)
    (convex_logBall K) (fun x ↦ (neg_mem_logBall K x).2) (absorbent_logBall K)
    (Units.finrank_eq_rank K).symm (a := fun i ↦ logEmbedding K (Additive.ofMul (u i)))
    (fun i ↦ logEmbedding_mem_unitLattice _) hu (by simpa only [gauge_logBall] using hmono)
  choose ε hε using fun j ↦ mem_unitLattice_iff.1 (b j).2
  refine ⟨ε, closure_sup_torsion_eq_top_of_basis b hε, fun j ↦ ?_⟩
  simpa only [gauge_logBall, hε] using hb j

/-! ### Fundamental systems of controlled height -/

open Classical in
/-- **A fundamental system of controlled height.** If the logarithmic embeddings of
`u 0, …, u (r - 1)` are linearly independent, where `r = rank K`, some fundamental system `ε` has
`∏ i, logHeight₁ (ε i) ≤ r! / 2 ^ (r - 1) * ∏ i, ‖log u i‖₁`, where `‖log x‖₁` is the `ℓ¹` norm
of the logarithmic embedding of `x`. -/
theorem exists_fundSystem_prod_logHeight₁_le_of_isMaxRank {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
      ∏ i, logHeight₁ (ε i : K) ≤ ((rank K).factorial : ℝ) / 2 ^ (rank K - 1) *
        ∏ i, ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| := by
  let n : Fin (rank K) → ℝ := fun i ↦ ∑ w, |logEmbedding K (Additive.ofMul (u i)) w|
  obtain ⟨ε, hε, hle⟩ := exists_fundSystem_sum_abs_logEmbedding_le_max_one_mul
    (u := u ∘ Tuple.sort n) (hu.comp _ (Tuple.sort n).injective) (Tuple.monotone_sort n)
  refine ⟨ε, hε, ?_⟩
  rw [← Equiv.prod_comp (Tuple.sort n) n, ← prod_max_one_add_one_div_two,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i _ ↦ zero_le_logHeight₁ _) fun i _ ↦ ?_
  exact (le_of_mul_le_mul_left (two_mul_logHeight₁_le_two_mul_sum_abs_logEmbedding (ε i))
    two_pos).trans (hle i)

open Classical in
/-- **A fundamental system of controlled absolute height.** If the logarithmic embeddings of
`u 0, …, u (r - 1)` are linearly independent, where `r = rank K`, some fundamental system `ε`
has `∏ i, absLogHeight₁ (ε i) ≤ r! / (2 ^ (r - 1) * [K : ℚ] ^ r) * ∏ i, ‖log u i‖₁`, where
`‖log x‖₁` is the `ℓ¹` norm of the logarithmic embedding of `x`. -/
theorem exists_fundSystem_prod_absLogHeight₁_le_of_isMaxRank {u : Fin (rank K) → (𝓞 K)ˣ}
    (hu : IsMaxRank u) :
    ∃ ε : Fin (rank K) → (𝓞 K)ˣ, Subgroup.closure (Set.range ε) ⊔ torsion K = ⊤ ∧
      ∏ i, absLogHeight₁ (ε i : K) ≤
        ((rank K).factorial : ℝ) / (2 ^ (rank K - 1) * (finrank ℚ K : ℝ) ^ rank K) *
          ∏ i, ∑ w, |logEmbedding K (Additive.ofMul (u i)) w| := by
  obtain ⟨ε, hε, hle⟩ := exists_fundSystem_prod_logHeight₁_le_of_isMaxRank hu
  refine ⟨ε, hε, ?_⟩
  have hd : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  simp_rw [absLogHeight₁_eq_div, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [div_le_iff₀ (by positivity)]
  calc ∏ i, logHeight₁ (ε i : K) ≤ _ := hle
    _ = _ := by field_simp

end TauCeti.NumberField.Units
