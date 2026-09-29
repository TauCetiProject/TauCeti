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
    apply (hEven.isIntegral.toIntegralLattice.isUnimodular_def).2
    rw [hEven.isIntegral.toIntegralLattice_carrier,
      hEven.isIntegral.toIntegralLattice_dualCarrier]
    have hLag : L.discriminantBilinearModule.IsLagrangian H := by
      simpa only [L.discriminantQuadraticModule_toFiniteBilinearModule hL] using hH'.2
    exact congrArg Subtype.val
      ((L.dual_intermediateCarrierOfDiscriminantSubgroup_eq_self_iff H).2
        hLag).symm
  · rintro ⟨M, hM⟩
    have hDual : IntermediateCarrier.dual M.1 = M.1 := by
      apply Subtype.ext
      have h := (M.2.isIntegral.toIntegralLattice.isUnimodular_def).1 hM
      rw [M.2.isIntegral.toIntegralLattice_carrier,
        M.2.isIntegral.toIntegralLattice_dualCarrier] at h
      exact h.symm
    apply (L.discriminantQuadraticModule hL).isMetabolic_def.mpr
    refine ⟨L.discriminantSubgroup M.1,
      ((L.discriminantQuadraticModule hL).isLagrangian_def _).mpr ⟨?_, ?_⟩⟩
    · exact (IntermediateCarrier.isEven_iff_isIsotropic_discriminantSubgroup hL M.1).1 M.2
    · have hLag : L.discriminantBilinearModule.IsLagrangian
          (L.discriminantSubgroup M.1) :=
        (IntermediateCarrier.dual_eq_self_iff_isLagrangian M.1).1 hDual
      simpa only [L.discriminantQuadraticModule_toFiniteBilinearModule hL] using hLag

end IntegralLattice

end TauCeti
