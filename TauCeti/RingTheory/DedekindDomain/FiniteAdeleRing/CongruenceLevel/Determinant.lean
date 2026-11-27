/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.diagGL` occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CongruenceLevel
-- Non-public: the determinants of the levels of `GL₂` over a commutative ring, used only in the
-- proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel.Determinant
-- Non-public: the determinants of the reduction kernel, used only in the proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Determinants of the congruence levels of `GL₂(𝔸_f)`

Over the finite adeles of a Dedekind domain `R` with fraction field `K`, with `Ô` the integral
adeles, the determinants of the levels of `GL₂` over a commutative ring
(`TauCeti.GL2K1.map_det`, `TauCeti.GL2K0.map_det`) and of the reduction kernel
(`Matrix.GeneralLinearGroup.map_det_ker_map_quotientMk`), transported along the inclusion
`GL₂(Ô) → GL₂(𝔸_f)` (`IsDedekindDomain.FiniteAdeleRing.map_det_map_integralGL`), give for every
ideal `N` of `R`:

* `det K₀(N) = det K₁(N) = Ô^×`, the everywhere-integral units `integralUnits R K` of `𝔸_f`;
* `det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`.

For `R = ℤ` these are the determinants of `K₀(N)`, `K₁(N)` and `K(N)` in `GL₂(ℤ̂)`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.map_det_level1`,
  `IsDedekindDomain.FiniteAdeleRing.map_det_level0`: `det K₁(N) = det K₀(N) = Ô^×`.
* `IsDedekindDomain.FiniteAdeleRing.map_det_principalLevel`:
  `det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`.
* `IsDedekindDomain.FiniteAdeleRing.integralGL_diagGL_mem_level1`: for `u ∈ Ô^×`, `diag(u, 1)`
  lies in `K₁(N) ⊆ K₀(N)`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, revision of 16 September 2017, Lemma 5.13,
  p. 57.
-/

public section

open Matrix

namespace IsDedekindDomain.FiniteAdeleRing

open TauCeti

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- **`det K₁(N) = Ô^×`**: the determinants of `K₁(N)` are the everywhere-integral units. -/
theorem map_det_level1 (N : Ideal R) :
    (level1 K N).map GeneralLinearGroup.det = integralUnits R K := by
  rw [level1_def, map_det_map_integralGL, GL2K1.map_det, ← MonoidHom.range_eq_map,
    range_units_map_val_eq_integralUnits]

/-- **`det K₀(N) = Ô^×`**: the determinants of `K₀(N)` are the everywhere-integral units. -/
theorem map_det_level0 (N : Ideal R) :
    (level0 K N).map GeneralLinearGroup.det = integralUnits R K := by
  rw [level0_def, map_det_map_integralGL, GL2K0.map_det, ← MonoidHom.range_eq_map,
    range_units_map_val_eq_integralUnits]

/-- **`det K(N) = {x ∈ Ô^× : x ≡ 1 mod NÔ}`**: the determinants of the principal level `K(N)` are
the images in `𝔸_f^×` of the units of the integral adeles congruent to `1` modulo `NÔ`. -/
theorem map_det_principalLevel (N : Ideal R) :
    (principalLevel K N).map GeneralLinearGroup.det =
      (Units.map (Ideal.Quotient.mk (completedIdeal K N) :
          integralAdeles R K →* integralAdeles R K ⧸ completedIdeal K N)).ker.map
        (Units.map ((integralAdeles R K).val.toRingHom : integralAdeles R K →* 𝔸ᶠ[R, K])) := by
  rw [principalLevel_eq_map_ker, map_det_map_integralGL,
    GeneralLinearGroup.map_det_ker_map_quotientMk]

variable {K}

/-- For a unit `u` of the integral adeles, `diag(u, 1)` lies in `K₁(N)`. -/
theorem integralGL_diagGL_mem_level1 (N : Ideal R) (u : (integralAdeles R K)ˣ) :
    integralGL K (Fin 2) (diagGL ![u, 1]) ∈ level1 K N := by
  rw [level1_def]
  exact Subgroup.mem_map_of_mem _ (GL2K1.diagGL_mem _ u)

/-- For a unit `u` of the integral adeles, `diag(u, 1)` lies in `K₀(N)`. -/
theorem integralGL_diagGL_mem_level0 (N : Ideal R) (u : (integralAdeles R K)ˣ) :
    integralGL K (Fin 2) (diagGL ![u, 1]) ∈ level0 K N :=
  level1_le_level0 K N (integralGL_diagGL_mem_level1 N u)

end IsDedekindDomain.FiniteAdeleRing
