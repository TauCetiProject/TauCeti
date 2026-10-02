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

For a nondegenerate integral lattice `L`, the lattice carried by an integral intermediate carrier
`L ≤ M ≤ Lᵛ` is unimodular precisely when its discriminant subgroup `M / L` equals its
orthogonal complement, that is, when it is Lagrangian. In particular, the even overlattice
`L_H` glued along a quadratic-isotropic subgroup `H` of the discriminant group of an even
lattice is unimodular exactly when `H = H⊥`. These are the unimodularity criteria of the gluing
construction, stated for the bundled lattices.

For an even lattice, an intermediate carrier is moreover even precisely when its discriminant
subgroup is quadratic-isotropic. Together these identify metabolic discriminant forms with
lattices admitting an even unimodular overlattice.

## Main declarations

* `IntermediateCarrier.IsIntegral.isUnimodular_toIntegralLattice_iff_isLagrangian`: an integral
  overlattice is unimodular exactly when its discriminant subgroup is Lagrangian.
* `TauCeti.IntegralLattice.isUnimodular_ofIsotropicSubgroup_iff_isLagrangian`: the glued even
  overlattice `L_H` is unimodular exactly when `H` is Lagrangian.
* `TauCeti.IntegralLattice.isMetabolic_discriminantQuadraticModule_iff`: the discriminant form
  of an even lattice is metabolic exactly when the lattice has an even unimodular overlattice.

See Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.4,
Proposition 1.4.1.
-/

public section

namespace TauCeti

namespace IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {L : IntegralLattice V} [L.IsNondegenerate]

namespace IntermediateCarrier

/-- The lattice carried by an integral intermediate carrier is unimodular exactly when the
carrier is its own dual. -/
theorem IsIntegral.isUnimodular_toIntegralLattice_iff_dual_eq_self {M : L.IntermediateCarrier}
    (hM : IsIntegral M) : hM.toIntegralLattice.IsUnimodular ↔ dual M = M := by
  rw [isUnimodular_def, hM.toIntegralLattice_carrier, hM.toIntegralLattice_dualCarrier, eq_comm,
    Subtype.ext_iff]

/-- **An integral overlattice is unimodular exactly when its discriminant subgroup is
Lagrangian.** For an integral intermediate carrier `L ≤ M ≤ Lᵛ`, the lattice `M` is unimodular
exactly when `M / L` equals its orthogonal complement in the discriminant group of `L`. -/
theorem IsIntegral.isUnimodular_toIntegralLattice_iff_isLagrangian {M : L.IntermediateCarrier}
    (hM : IsIntegral M) :
    hM.toIntegralLattice.IsUnimodular ↔
      L.discriminantBilinearModule.IsLagrangian (L.discriminantSubgroup M) :=
  hM.isUnimodular_toIntegralLattice_iff_dual_eq_self.trans (dual_eq_self_iff_isLagrangian M)

end IntermediateCarrier

open IntermediateCarrier

variable (L)

/-- **The glued overlattice is unimodular exactly when the glue is Lagrangian.** For an even
lattice `L` and a quadratic-isotropic subgroup `H` of its discriminant group, the even
overlattice `L_H` is unimodular exactly when `H = H⊥` for the discriminant pairing. -/
theorem isUnimodular_ofIsotropicSubgroup_iff_isLagrangian (hL : L.IsEven)
    (H : AddSubgroup L.DiscriminantGroup)
    (hH : (L.discriminantQuadraticModule hL).IsIsotropic H) :
    (L.ofIsotropicSubgroup hL H hH).IsUnimodular ↔ L.discriminantBilinearModule.IsLagrangian H := by
  rw [L.ofIsotropicSubgroup_eq_toIntegralLattice hL ⟨H, hH⟩,
    IsIntegral.isUnimodular_toIntegralLattice_iff_isLagrangian,
    evenIntermediateCarrierOrderIsoIsotropicSubgroup_symm_apply_coe,
    discriminantSubgroup_intermediateCarrierOfDiscriminantSubgroup]

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
