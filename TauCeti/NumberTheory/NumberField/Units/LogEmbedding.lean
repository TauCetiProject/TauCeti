/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Algebra.GroupAction.TypeTags
public import TauCeti.RepresentationTheory.RestrictScalars
public import TauCeti.NumberTheory.NumberField.AutomorphismAction

/-!
# The Galois action on the logarithmic embedding of the units

Let `L` be a number field. Mathlib's logarithmic embedding sends a unit `x` of `𝓞 L` to the vector
`(mult w * log w(x))_w` indexed by the infinite places `w ≠ w₀` of `L`, for a distinguished
infinite place `w₀`; its image is the unit lattice, a full `ℤ`-lattice in this space
`logSpace L`. The omitted coordinate is recovered from the product formula: the full vector,
indexed by all infinite places, has coordinate sum zero. So `logSpace L` is a coordinate chart
on the sum-zero hyperplane of `ℝ^{InfinitePlace L}` (`TauCeti.NumberField.Units.logSpaceExtend`).

An automorphism `σ` of `L` over a subfield `K` permutes the infinite places of `L`, and so acts
on that hyperplane by permuting coordinates. Read in the chart this is a real representation
`TauCeti.NumberField.Units.logSpaceRep K L` of `Aut(L/K)` on `logSpace L`. The logarithmic
embedding is equivariant for the Galois action on the units
(`TauCeti.NumberField.Units.logEmbedding_smul`), so the unit lattice is a Galois-stable lattice
in this representation (`TauCeti.NumberField.Units.unitLatticeSubrep`). This is the form in
which the unit group enters the computation of Herbrand quotients of units in class field theory.

## Main definitions

* `TauCeti.NumberField.Units.logSpaceExtend`: the extension of a vector of `logSpace L` to the
  infinite place `w₀` by minus the sum of its coordinates.
* `TauCeti.NumberField.Units.logSpaceRep`: the permutation representation of `Aut(L/K)` on
  `logSpace L`.
* `TauCeti.NumberField.Units.unitLatticeSubrep`: the unit lattice as an integral
  subrepresentation.

## Main results

* `TauCeti.NumberField.Units.logSpaceExtend_logSpaceRep`: the extension intertwines
  `logSpaceRep` with the permutation of the infinite places.
* `TauCeti.NumberField.Units.logEmbedding_smul`: the logarithmic embedding is
  `Aut(L/K)`-equivariant.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §3 (the Herbrand quotient of the unit group).
-/

public noncomputable section

open Finset NumberField NumberField.InfinitePlace NumberField.Units
  NumberField.Units.dirichletUnitTheorem

namespace TauCeti.NumberField.Units

/-! ### The sum-zero hyperplane -/

section Extend

variable (L : Type*) [Field L] [NumberField L]

-- the infinite places have no computable equality, so the case split and the sum over
-- `{w // w ≠ w₀}` are classical, as in Mathlib's `NumberField.Units.dirichletUnitTheorem`
open Classical in
/-- The extension of a vector of `logSpace L`, indexed by the infinite places other than `w₀`,
to all infinite places, with coordinate at `w₀` minus the sum of the others. It identifies
`logSpace L` with the vectors of `ℝ^{InfinitePlace L}` of coordinate sum zero
(`TauCeti.NumberField.Units.sum_logSpaceExtend`,
`TauCeti.NumberField.Units.logSpaceExtend_eq_self`). -/
def logSpaceExtend : logSpace L →ₗ[ℝ] InfinitePlace L → ℝ where
  toFun y w := if h : w = w₀ then -∑ i, y i else y ⟨w, h⟩
  map_add' y z := by
    ext w
    by_cases h : w = w₀ <;> simp [h, sum_add_distrib, add_comm]
  map_smul' c y := by
    ext w
    by_cases h : w = w₀ <;> simp [h, mul_sum]

variable {L}

open Classical in
@[simp]
theorem logSpaceExtend_apply_w₀ (y : logSpace L) : logSpaceExtend L y w₀ = -∑ i, y i := by
  simp [logSpaceExtend]

@[simp]
theorem logSpaceExtend_apply_val (y : logSpace L) (w : {w : InfinitePlace L // w ≠ w₀}) :
    logSpaceExtend L y w.1 = y w := by
  simp [logSpaceExtend, w.2]

/-- The coordinates of `logSpaceExtend L y` sum to zero. -/
@[simp]
theorem sum_logSpaceExtend (y : logSpace L) : ∑ w, logSpaceExtend L y w = 0 := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, logSpaceExtend_apply_w₀, neg_add_eq_zero]
  exact Fintype.sum_congr _ _ fun w ↦ (logSpaceExtend_apply_val y w).symm

/-- The coordinates of `logSpaceExtend L y`, permuted by any permutation of the infinite places,
sum to zero. -/
theorem sum_logSpaceExtend_perm (y : logSpace L) (e : Equiv.Perm (InfinitePlace L)) :
    ∑ w, logSpaceExtend L y (e w) = 0 := by
  rw [Equiv.sum_comp e (logSpaceExtend L y), sum_logSpaceExtend]

/-- A vector of coordinate sum zero is the extension of its coordinates away from `w₀`. -/
theorem logSpaceExtend_eq_self {f : InfinitePlace L → ℝ} (hf : ∑ w, f w = 0) :
    logSpaceExtend L (fun w ↦ f w.1) = f := by
  classical
  ext w
  by_cases hw : w = w₀
  · subst hw
    rw [logSpaceExtend_apply_w₀, eq_comm, ← add_eq_zero_iff_eq_neg,
      ← Fintype.sum_eq_add_sum_subtype_ne f w₀, hf]
  · exact logSpaceExtend_apply_val (fun w ↦ f w.1) ⟨w, hw⟩

/-- The extension of the logarithmic embedding of a unit `x` is the full vector
`(mult w * log w(x))_w` over all infinite places, by the product formula. -/
@[simp]
theorem logSpaceExtend_logEmbedding (x : (𝓞 L)ˣ) :
    logSpaceExtend L (logEmbedding L (Additive.ofMul x)) = fun w ↦ w.mult * Real.log (w x) :=
  logSpaceExtend_eq_self (sum_mult_mul_log x)

end Extend

/-! ### The Galois representation -/

variable (K L : Type*) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- The real representation of `Aut(L/K)` on `logSpace L`: an automorphism `σ` permutes the
coordinates of the sum-zero hyperplane of `ℝ^{InfinitePlace L}` by `w ↦ σ • w`, read in the chart
`logSpaceExtend L` (`TauCeti.NumberField.Units.logSpaceExtend_logSpaceRep`). -/
def logSpaceRep : Representation ℝ (L ≃ₐ[K] L) (logSpace L) where
  toFun σ := LinearMap.funLeft ℝ ℝ (fun w : {w : InfinitePlace L // w ≠ w₀} ↦ σ⁻¹ • w.1) ∘ₗ
    logSpaceExtend L
  map_one' := LinearMap.ext fun y ↦ funext fun w ↦ by simp
  map_mul' σ τ := LinearMap.ext fun y ↦ funext fun w ↦ by
    have hτ : ∑ v, logSpaceExtend L y (τ⁻¹ • v) = 0 :=
      sum_logSpaceExtend_perm y (MulAction.toPerm τ⁻¹)
    have h : (LinearMap.funLeft ℝ ℝ fun w : {w : InfinitePlace L // w ≠ w₀} ↦ τ⁻¹ • w.1)
        (logSpaceExtend L y) = fun w ↦ logSpaceExtend L y (τ⁻¹ • w.1) :=
      funext fun w ↦ LinearMap.funLeft_apply _ _ _ _ w
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Module.End.mul_apply, h,
      logSpaceExtend_eq_self hτ, mul_inv_rev, mul_smul]

variable {K L}

@[simp]
theorem logSpaceRep_apply (σ : L ≃ₐ[K] L) (y : logSpace L)
    (w : {w : InfinitePlace L // w ≠ w₀}) :
    logSpaceRep K L σ y w = logSpaceExtend L y (σ⁻¹ • w.1) :=
  (rfl)

/-- **`logSpaceRep` is the permutation of the infinite places**, read through the identification
`logSpaceExtend L` of `logSpace L` with the sum-zero hyperplane. -/
@[simp]
theorem logSpaceExtend_logSpaceRep (σ : L ≃ₐ[K] L) (y : logSpace L) :
    logSpaceExtend L (logSpaceRep K L σ y) =
      fun w : InfinitePlace L ↦ logSpaceExtend L y (σ⁻¹ • w) := by
  have hrep : logSpaceRep K L σ y =
      fun w : {w : InfinitePlace L // w ≠ w₀} ↦ logSpaceExtend L y (σ⁻¹ • w.1) :=
    funext (logSpaceRep_apply σ y)
  rw [hrep]
  exact logSpaceExtend_eq_self (f := fun w ↦ logSpaceExtend L y (σ⁻¹ • w))
    (sum_logSpaceExtend_perm y (MulAction.toPerm σ⁻¹))

/-- **The logarithmic embedding is Galois-equivariant**: the logarithmic embedding of `σ • x` is
`logSpaceRep K L σ` applied to that of `x`. -/
@[simp]
theorem logEmbedding_smul (σ : L ≃ₐ[K] L) (x : Additive (𝓞 L)ˣ) :
    logEmbedding L (σ • x) = logSpaceRep K L σ (logEmbedding L x) := by
  -- The action on the additive tag is defined through `ofMul (σ • x.toMul)`.
  -- Expose that defining equality so the unit-coordinate lemmas can rewrite before
  -- simplification folds `ofMul` back into the additive action.
  change logEmbedding L (Additive.ofMul (σ • x.toMul)) =
    logSpaceRep K L σ (logEmbedding L (Additive.ofMul x.toMul))
  ext w
  have hmult : (σ.symm • w.1).mult = w.1.mult := by
    unfold mult
    rw [isReal_smul_iff]
  rw [logSpaceRep_apply, logSpaceExtend_logEmbedding x.toMul,
    logEmbedding_component (σ • x.toMul)]
  simp [hmult, AlgEquiv.aut_inv]

variable (K L) in
/-- The unit lattice `logEmbedding L ((𝓞 L)ˣ)` as an integral subrepresentation of `logSpaceRep`:
it is stable under `Aut(L/K)` by `TauCeti.NumberField.Units.logEmbedding_smul`. -/
def unitLatticeSubrep : Subrepresentation (logSpaceRep K L).restrictScalarsInt where
  toSubmodule := unitLattice L
  apply_mem_toSubmodule σ y := by
    rintro ⟨x, -, rfl⟩
    exact ⟨Additive.ofMul (σ • x.toMul), trivial, by
      simp⟩

@[simp]
theorem toSubmodule_unitLatticeSubrep : (unitLatticeSubrep K L).toSubmodule = unitLattice L :=
  (rfl)

end TauCeti.NumberField.Units
