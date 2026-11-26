/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# The absolute value of the field norm

Over a complete ultrametric field, the absolute value of a field norm is the spectral norm
raised to the degree of the extension. The identity applies to inseparable extensions as well.
-/

public section

open scoped IntermediateField

namespace TauCeti

/-- In a finite extension of a complete ultrametric field, the norm of the algebraic norm is
the spectral norm raised to the field degree. -/
theorem norm_algebraNorm_eq_spectralNorm_pow_finrank
    {K L : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) :
    ‖Algebra.norm K x‖ = spectralNorm K L x ^ Module.finrank K L := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  let b := IntermediateField.adjoin.powerBasis hx
  have hgen : b.gen = IntermediateField.AdjoinSimple.gen K x :=
    IntermediateField.adjoin.powerBasis_gen hx
  have hn : ‖Algebra.norm K b.gen‖ = spectralNorm K L x ^ b.dim := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, norm_mul, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, ← spectralNorm_pow_natDegree_minpoly_eq_norm_coeff_zero
        b.isIntegral_gen.isAlgebraic, b.natDegree_minpoly,
      spectralNorm.eq_of_tower (L := L), hgen, IntermediateField.AdjoinSimple.algebraMap_gen]
  rw [Algebra.norm_eq_norm_adjoin, norm_pow, ← hgen, hn, ← pow_mul, ← b.finrank,
    Module.finrank_mul_finrank]

end TauCeti
