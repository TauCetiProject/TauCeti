/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import TauCeti.Topology.Algebra.Valued.Integer

import Mathlib.Algebra.AlgebraicCard
import TauCeti.Analysis.Normed.Field.Approximation

/-!
# `ℂ_p` is separable

The field `ℂ_[p]` of `p`-adic complex numbers is the completion of an algebraic closure of
`ℚ_[p]`. It contains the countable set of algebraic numbers, the elements algebraic over `ℚ`, as
a dense subset. Indeed the image of the algebraic closure of `ℚ_[p]` is dense, and each of its
elements is a limit of algebraic numbers: approximate its minimal polynomial over `ℚ_[p]` by one
over `ℚ` and take a nearby root (`IsAlgebraic.mem_closure_setOf_isAlgebraic`).

Separability is what makes `ℂ_p` fail to be spherically complete, so that the closed unit disc
over `ℂ_p` has points of type (4).

The file also compares the valuation with the norm, records `‖p‖ = p⁻¹ < 1` and the
residue characteristic, and provides the integral coefficient inclusion and topological
nilpotence of `ζ - 1` for `p`-th roots of unity.

## Main results

* `PadicComplex.valuation_coe`: the real value of the valuation is the norm.
* `PadicComplex.residueFieldCharP`: the residue field of `𝓞_ℂ_[p]` has characteristic `p`.
* `PadicComplex.instIsLinearTopologyInt`, `PadicComplex.instCompleteSpaceInt`: the integers
  of `ℂ_p` are complete and linearly topologized.
* `PadicComplex.integralCoefficientMap`: the continuous, injective inclusion `ℤ_[p] →+* 𝓞_ℂ_[p]`.
* `PadicComplex.isTopologicallyNilpotent_sub_one`: `ζ - 1` is topologically nilpotent
  if `ζ ^ p = 1`.
* `PadicComplex.norm_p`: `‖p‖ = p⁻¹` in `ℂ_[p]`.
* `PadicComplex.norm_p_lt_one`: `‖p‖ < 1` in `ℂ_[p]`.
* `PadicComplex.dense_setOf_isAlgebraic`: the algebraic numbers are dense in `ℂ_[p]`.
* `PadicComplex.separableSpace`: `ℂ_[p]` is a separable space.

## References

* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3, for the density of the algebraic numbers in `ℂ_p` and the separability of `ℂ_p`.
-/

public section

open scoped Topology

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- The real value of the valuation on `ℂ_[p]` is its norm. -/
theorem valuation_coe (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm]
  simp [Valuation.norm_def, RankOne.hom_eq_embedding, Valuation.embedding_restrict]

/-- The norm of `p` in `ℂ_[p]` is `p⁻¹`. -/
@[simp]
theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]

/-- `‖p‖ < 1` in `ℂ_[p]`. -/
theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (mod_cast (Fact.out : p.Prime).one_lt)

-- These instances reuse the valued-integer proofs: the underlying subtypes are definitionally
-- equal, but typeclass search does not unfold `PadicComplexInt` to match their instance heads.
/-- The integers of `ℂ_p` have a linear topology. -/
instance instIsLinearTopologyInt : IsLinearTopology 𝓞_ℂ_[p] 𝓞_ℂ_[p] :=
  inferInstanceAs (IsLinearTopology (Valued.integer ℂ_[p]) (Valued.integer ℂ_[p]))

/-- The integers of `ℂ_p` are complete for the induced uniformity. -/
instance instCompleteSpaceInt : CompleteSpace 𝓞_ℂ_[p] :=
  inferInstanceAs (CompleteSpace (Valued.integer ℂ_[p]))

/-- The residue field of the integers of `ℂ_p` has characteristic `p`. -/
instance residueFieldCharP : CharP (IsLocalRing.ResidueField 𝓞_ℂ_[p]) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2
  rw [← map_natCast (IsLocalRing.residue 𝓞_ℂ_[p]), IsLocalRing.residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff ℂ_[p] (PadicComplex.valued p).v).2
  rw [← NNReal.coe_lt_coe, valuation_coe]
  exact norm_p_lt_one p

/-- The coefficient inclusion from the p-adic integers into the integers of `ℂ_p`. -/
noncomputable def integralCoefficientMap : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict _ fun x ↦ by
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe, valuation_coe]
    simpa using x.norm_le_one

@[simp]
theorem integralCoefficientMap_coe (x : ℤ_[p]) :
    (integralCoefficientMap p x : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) := (rfl)

/-- The integral coefficient inclusion is continuous for the induced p-adic topologies. -/
theorem continuous_integralCoefficientMap : Continuous (integralCoefficientMap p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p] |>.comp continuous_subtype_val).subtype_mk _

/-- Extending integral coefficients to `ℂ_p` loses no information. -/
theorem integralCoefficientMap_injective : Function.Injective (integralCoefficientMap p) := by
  intro x y h
  apply Subtype.ext
  exact (algebraMap ℚ_[p] ℂ_[p]).injective (congrArg Subtype.val h)

/-- The translated constant term of a `p`-th root of unity is topologically nilpotent. -/
theorem isTopologicallyNilpotent_sub_one (ζ : 𝓞_ℂ_[p]) (hζ : ζ ^ p = 1) :
    IsTopologicallyNilpotent (ζ - 1) := by
  have hres : IsLocalRing.residue _ (ζ - 1) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := p)
    simp only [map_sub, map_one, sub_pow_char, one_pow, ← map_pow, hζ, sub_self]
  have hm := (IsLocalRing.residue_eq_zero_iff (ζ - 1)).1 hres
  have hv := (Valuation.mem_maximalIdeal_iff ℂ_[p] (PadicComplex.valued p).v).1 hm
  have hn : ‖((ζ - 1 : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1 := by
    rw [← valuation_coe]
    exact_mod_cast hv
  exact tendsto_subtype_rng.mpr (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn)

/-- **The algebraic numbers are dense in `ℂ_[p]`.** -/
theorem dense_setOf_isAlgebraic : Dense {x : ℂ_[p] | IsAlgebraic ℚ x} := by
  have hℚ : DenseRange (algebraMap ℚ ℚ_[p]) := by
    rw [show ⇑(algebraMap ℚ ℚ_[p]) = Rat.cast from funext (eq_ratCast _)]
    exact Padic.denseRange_ratCast p
  refine dense_closure.mp <|
    Dense.mono ?_ (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p))
  rintro _ ⟨x, rfl⟩
  rw [coe_eq]
  exact ((Algebra.IsAlgebraic.isAlgebraic x).algebraMap (A := ℂ_[p])).mem_closure_setOf_isAlgebraic
    hℚ

/-- **`ℂ_[p]` is separable**: the countable set of algebraic numbers is dense. -/
instance separableSpace : TopologicalSpace.SeparableSpace ℂ_[p] :=
  ⟨⟨_, Algebraic.countable ℚ ℂ_[p], dense_setOf_isAlgebraic p⟩⟩

end PadicComplex
