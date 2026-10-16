/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Metabolic
public import TauCeti.LinearAlgebra.IntegralLattice.Overlattice.Dual
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# Metabolic discriminant forms and unimodular overlattices

For an even nondegenerate integral lattice, an intermediate carrier is even precisely when
its discriminant subgroup is quadratic-isotropic. It is unimodular precisely when that
subgroup equals its orthogonal complement. Together these identify metabolic discriminant
forms with lattices admitting an even unimodular overlattice.

See Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4.
-/

public section

namespace TauCeti

namespace IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) [L.IsNondegenerate]

/-- The discriminant form of an even lattice is metabolic exactly when the lattice has an
even unimodular intermediate overlattice. -/
theorem isMetabolic_discriminantQuadraticModule_iff (hL : L.IsEven) :
    (L.discriminantQuadraticModule hL).IsMetabolic ↔
      ∃ M : {M : L.IntermediateCarrier // IntermediateCarrier.IsEven M},
        M.2.isIntegral.toIntegralLattice.IsUnimodular := by
  constructor
  · intro hMetabolic
    obtain ⟨H, hH⟩ := (L.discriminantQuadraticModule hL).isMetabolic_def.mp hMetabolic
    have hH' := ((L.discriminantQuadraticModule hL).isLagrangian_def H).mp hH
    have hEven : IntermediateCarrier.IsEven
        (L.intermediateCarrierOfDiscriminantSubgroup H) :=
      (L.isEven_intermediateCarrierOfDiscriminantSubgroup_iff hL H).2 hH'.1
    refine ⟨⟨L.intermediateCarrierOfDiscriminantSubgroup H, hEven⟩, ?_⟩
    have hLag : L.discriminantBilinearModule.IsLagrangian H := by
      simpa only [L.discriminantQuadraticModule_toFiniteBilinearModule hL] using hH'.2
    exact hEven.isIntegral.isUnimodular_toIntegralLattice_iff_dual_eq_self.mpr
      ((L.dual_intermediateCarrierOfDiscriminantSubgroup_eq_self_iff H).mpr hLag)
  · rintro ⟨M, hM⟩
    apply (L.discriminantQuadraticModule hL).isMetabolic_def.mpr
    refine ⟨L.discriminantSubgroup M.1,
      ((L.discriminantQuadraticModule hL).isLagrangian_def _).mpr ⟨?_, ?_⟩⟩
    · exact (IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup hL M.1).1 M.2
    · simpa only [L.discriminantQuadraticModule_toFiniteBilinearModule hL] using
        M.2.isIntegral.isUnimodular_toIntegralLattice_iff_isLagrangian.mp hM

end IntegralLattice

end TauCeti
