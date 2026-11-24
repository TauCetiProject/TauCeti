/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus.Basic
import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Form

/-!
# Discriminant forms as genus invariants

Nondegenerate integral lattices in the same genus have isometric discriminant bilinear modules
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantBilinearModule`), and even ones
have isometric discriminant quadratic modules
(`TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantQuadraticModule`).

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9, §1.16.
-/

public section

namespace TauCeti.IntegralLattice.SameGenus

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **Lattices in one genus have isometric discriminant bilinear forms.** This is the easy half of
Nikulin's Corollary 1.16.3: the genus of a nondegenerate lattice determines its discriminant
bilinear form `b_L`. -/
theorem nonempty_isometry_discriminantBilinearModule {L : IntegralLattice V}
    {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate] (h : L.SameGenus M) :
    Nonempty (FiniteBilinearModule.Isometry L.discriminantBilinearModule
      M.discriminantBilinearModule) :=
  FiniteBilinearModule.nonempty_isometry_of_forall_primaryComponent fun p hp ↦
    have : Fact p.Prime := ⟨hp⟩
    (h.localIntegralForm_equivalent p).map primaryDiscriminantBilinearIsometry

/-- **Even lattices in one genus have isometric discriminant quadratic forms.** This is the easy
half of Nikulin's Corollary 1.9.4: the genus of an even nondegenerate lattice determines its
discriminant quadratic form `q_L`. -/
theorem nonempty_isometry_discriminantQuadraticModule {L : IntegralLattice V}
    {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate] (h : L.SameGenus M)
    (hL : L.IsEven) :
    Nonempty (FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule (h.isEven_iff.mp hL))) :=
  FiniteQuadraticModule.nonempty_isometry_of_forall_primaryComponent fun p hp ↦
    have : Fact p.Prime := ⟨hp⟩
    (h.localIntegralForm_equivalent p).map (primaryDiscriminantQuadraticIsometry _ _)

end TauCeti.IntegralLattice.SameGenus
