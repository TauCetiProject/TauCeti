/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hom.Basic
import TauCeti.RingTheory.FormalGroup.AdditiveSeries

/-!
# Endomorphisms of the additive formal group without additive torsion

Over a commutative ring without additive torsion, every endomorphism of the additive formal
group is multiplication by its linear coefficient. This applies to the homomorphism obtained
by conjugating an integral formal-group homomorphism by integral logarithms.

## References

* M. Hazewinkel, *Formal Groups and Applications*, I §1.
-/

public section

open FormalGroup

namespace TauCeti.FormalGroupHom

variable {R : Type*} [CommRing R] [HasUniqueDiv R]

/-- Over a ring without additive torsion, an endomorphism of the additive formal group is
multiplication by its linear coefficient. -/
theorem toPowerSeries_eq_coeff_one_smul_X (f : FormalGroupHom (𝔾ₐ (R := R)) 𝔾ₐ) :
    f.toPowerSeries = PowerSeries.coeff 1 f.toPowerSeries • PowerSeries.X := by
  have hadd := hom_additive_iff.mp f.hom
  have hc := (PowerSeries.subst_X_add_X_eq_add_iff f.toPowerSeries).mp hadd
  ext n
  rcases n with _ | _ | n
  · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, f.zero_constantCoeff]
  · simp
  · have h := hc.2 (n + 2) 1 (by omega) (by omega)
    have hz : PowerSeries.coeff (n + 2) f.toPowerSeries = 0 := by
      apply nsmul_right_injective (by omega : n + 2 ≠ 0)
      simpa only [Nat.choose_one_right, nsmul_eq_mul, mul_zero] using h
    simp [hz, PowerSeries.coeff_X, Nat.add_assoc]

end TauCeti.FormalGroupHom
