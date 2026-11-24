/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Descend
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix

/-!
# Residual descent of continuous representations with discrete coefficients

Let `Γ` be a compact topological group and `K` a commutative ring with the discrete topology,
for instance the field `AlgebraicClosure (ZMod p)`. A continuous homomorphism
`ρ : Γ →* GL_n(K)`, where `GL_n(K)` carries the units topology, takes only finitely many values:
its image is a compact subset of a discrete space. Hence only finitely many elements occur as
matrix entries of `ρ`. When `K` is a field algebraic over a finite field `F`, these entries
generate a finite subfield `k` of `K`, and `ρ` takes values in `GL_n(k)`. The descent itself,
`TauCeti.CoefficientDescent.descend`, works for any subring of `K` containing the entries, so `ρ`
descends to every finite `k' ⊇ k` (via `TauCeti.CoefficientDescent.entries_subset_range_of_le`);
here we show that the descended homomorphism is continuous.

## Main results

* `TauCeti.ResidualDescent.finite_range`: a continuous `ρ` has finite image.
* `TauCeti.ResidualDescent.continuous_descend`: the descended homomorphism is continuous.
* `TauCeti.ResidualDescent.exists_finite_descend`: for `K` algebraic over a finite field `F`, a
  continuous `ρ` is the image of a continuous `Γ →* GL_n(k)` for a finite subfield `k`.
* `TauCeti.ResidualDescent.finite_entryField`: for `K` algebraic over a finite field `F`, the
  entries generate a finite field.

## References

* J.-P. Serre, *Sur les représentations modulaires de degré 2 de Gal(ℚ-bar/ℚ)*, Duke Math. J. 54
  (1987), 179–230, 1.1, p. 180.
* H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, revised version (2007) of Current
  Developments in Mathematics 1995, §2.1, p. 53.
-/

public section

open Matrix TauCeti.CoefficientDescent

namespace TauCeti.ResidualDescent

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {n : Type*} [Fintype n] [DecidableEq n]

section CommRing

variable {K : Type*} [CommRing K] [TopologicalSpace K]

/-- Each matrix entry of a continuous `ρ : Γ →* GL_n(K)` is continuous. -/
theorem continuous_entry {ρ : Γ →* GL n K} (hρ : Continuous ρ) (i j : n) :
    Continuous fun g ↦ (ρ g : Matrix n n K) i j :=
  ((Units.continuous_val (M := Matrix n n K)).comp hρ).matrix_elem i j

variable [DiscreteTopology K]

/-- The descended homomorphism is continuous for every topology on `R`: its matrix entries are
functions of the entries of `ρ`, which take values in the discrete space `K`. -/
theorem continuous_descend {R : Type*} [CommRing R] [TopologicalSpace R]
    {ρ : Γ →* GL n K} (hρ : Continuous ρ) {f : R →+* K} (hf : Function.Injective f)
    (h : entries ρ ⊆ Set.range f) : Continuous (descend hf h) := by
  refine Units.continuous_iff.2 ⟨continuous_pi fun i ↦ continuous_pi fun j ↦ ?_,
    continuous_pi fun i ↦ continuous_pi fun j ↦ ?_⟩
  · refine ((continuous_of_discreteTopology (f := Function.invFun f)).comp
      (continuous_entry hρ i j)).congr fun g ↦ ?_
    rw [Function.comp_apply, Function.comp_apply, ← map_descend_apply hf h,
      Function.leftInverse_invFun hf]
  · refine ((continuous_of_discreteTopology (f := Function.invFun f)).comp
      (((Units.continuous_coe_inv (M := Matrix n n K)).comp hρ).matrix_elem i j)).congr fun g ↦ ?_
    rw [Function.comp_apply, Function.comp_apply, ← map_inv, ← map_inv (descend hf h),
      ← map_descend_apply hf h, Function.leftInverse_invFun hf]

variable [CompactSpace Γ]

/-- **Finite image.** A continuous homomorphism from a compact group to `GL_n(K)`, `K` discrete,
takes finitely many values. -/
theorem finite_range {ρ : Γ →* GL n K} (hρ : Continuous ρ) : (Set.range ρ).Finite :=
  (isCompact_range hρ).finite_of_discrete

/-- Only finitely many ring elements are matrix entries of a continuous `ρ`. -/
theorem finite_entries {ρ : Γ →* GL n K} (hρ : Continuous ρ) : (entries ρ).Finite :=
  (Set.finite_iUnion fun i ↦ Set.finite_iUnion fun j ↦
    (isCompact_range (continuous_entry hρ i j)).finite_of_discrete).subset <| by
    intro x hx
    obtain ⟨g, i, j, rfl⟩ := mem_entries_iff.1 hx
    exact Set.mem_iUnion₂.2 ⟨i, j, g, rfl⟩

end CommRing

section EntryField

variable [CompactSpace Γ] {K : Type*} [Field K] [TopologicalSpace K] [DiscreteTopology K]
  (F : Type*) [Field F] [Algebra F K]

/-- For `K` algebraic over `F`, the entries of a continuous `ρ` generate a finite extension
of `F`. -/
theorem finiteDimensional_entryField [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) : FiniteDimensional F (entryField F ρ) := by
  have := (finite_entries hρ).to_subtype
  rw [entryField_def]
  exact IntermediateField.finiteDimensional_adjoin fun x _ ↦
    (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

/-- **Residual descent.** For `K` algebraic over a finite field `F`, the entries of a continuous
`ρ` generate a finite field. -/
theorem finite_entryField [Finite F] [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) : Finite (entryField F ρ) :=
  have := finiteDimensional_entryField F hρ
  Module.finite_of_finite F

/-- **Residual descent.** For `K` algebraic over a finite field `F` and `Γ` compact, a continuous
`ρ : Γ →* GL_n(K)` is the image of a continuous `Γ →* GL_n(k)` for a finite subfield `k` of `K`. -/
theorem exists_finite_descend [Finite F] [Algebra.IsAlgebraic F K] {ρ : Γ →* GL n K}
    (hρ : Continuous ρ) :
    ∃ (k : IntermediateField F K) (ρk : Γ →* GL n k), Finite k ∧ Continuous ρk ∧
      ∀ g, Matrix.GeneralLinearGroup.map (algebraMap k K) (ρk g) = ρ g :=
  ⟨entryField F ρ, descend (algebraMap (entryField F ρ) K).injective
    (entries_subset_range_of_le F le_rfl), finite_entryField F hρ,
    continuous_descend hρ _ _, map_descend _ _⟩

end EntryField

end TauCeti.ResidualDescent
