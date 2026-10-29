/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import TauCeti.Analysis.Normed.Ring.Units
public import TauCeti.RingTheory.Jacobson.NonUnital

import TauCeti.Analysis.Normed.Algebra.Spectrum
import TauCeti.RingTheory.Jacobson.Spectrum

/-!
# Closedness and quasinilpotence of Jacobson radicals

We compare membership in the nonunital Jacobson radical with membership in the
Jacobson radical of the external unitization with its ℓ¹ norm. Pulling back
`TauCeti.Ring.isClosed_jacobson` from `TauCeti.Analysis.Normed.Ring.Units` then proves
closedness of the nonunital radical and its underlying scalar submodule.

The statements use summability of geometric series instead of completeness wherever
possible. No normalization of the norm of the identity is assumed.

The radical also consists of the elements all of whose left multiples are quasinilpotent.
Over any normed field this is the vanishing of the spectral radius of every left multiple,
in the unital and the nonunital setting. In a complex Banach algebra, Gelfand's formula
turns it into the vanishing of every `gelfandRadius (b * a)`, the limit of
`‖(b * a) ^ n‖ ^ (1 / n)`.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* We use Mathlib's `WithLp.unitizationAlgEquiv` and
  `Module.comap_jacobson_of_bijective`, and Gelfand's formula
  `spectrum.spectralRadius_eq_gelfandRadius`.
-/

public section

namespace TauCeti

section Closed

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The radical defined with the algebraic unitization can equally be tested in its
ℓ¹-normed version. -/
theorem mem_nonUnitalJacobson_iff_toLp_mem_jacobson {a : A} :
    a ∈ nonUnitalJacobson 𝕜 A ↔
      WithLp.toLp 1 (a : Unitization 𝕜 A) ∈
        Ring.jacobson (WithLp 1 (Unitization 𝕜 A)) := by
  let e := WithLp.unitizationAlgEquiv (𝕜 := 𝕜) (A := A) 𝕜
  have : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  have h := Module.comap_jacobson_of_bijective (f := e.toRingHom.toSemilinearMap) e.bijective
  rw [mem_nonUnitalJacobson]
  have hm := SetLike.ext_iff.mp h (WithLp.toLp 1 (a : Unitization 𝕜 A))
  simpa [Submodule.mem_comap, e] using hm

variable [HasSummableGeomSeries A]

/-- The Jacobson radical of a nonunital normed algebra with summable geometric
series is closed. In particular this applies to every nonunital Banach algebra. -/
theorem isClosed_nonUnitalJacobson : IsClosed (nonUnitalJacobson 𝕜 A : Set A) := by
  have hset : (nonUnitalJacobson 𝕜 A : Set A) =
      (fun a : A => WithLp.toLp 1 (a : Unitization 𝕜 A)) ⁻¹'
        (Ring.jacobson (WithLp 1 (Unitization 𝕜 A)) : Set _) := by
    ext a
    exact mem_nonUnitalJacobson_iff_toLp_mem_jacobson 𝕜 A
  rw [hset]
  exact (Ring.isClosed_jacobson _).preimage WithLp.unitization_isometry_inr.continuous

/-- The scalar submodule underlying the nonunital radical is closed. -/
theorem isClosed_nonUnitalJacobsonSubmodule :
    IsClosed (nonUnitalJacobsonSubmodule 𝕜 A : Set A) := by
  rw [coe_nonUnitalJacobsonSubmodule]
  exact isClosed_nonUnitalJacobson 𝕜 A

end Closed

section Quasinilpotent

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalRing A] [Module 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- An element of a nonunital algebra lies in its Jacobson radical exactly when every left
multiple of it by an element of the algebra has spectral radius zero. -/
theorem mem_nonUnitalJacobson_iff_forall_spectralRadius_mul_eq_zero {a : A} :
    a ∈ nonUnitalJacobson 𝕜 A ↔ ∀ b : A, spectralRadius 𝕜 (b * a) = 0 := by
  simp_rw [spectralRadius_eq_zero_iff,
    mem_nonUnitalJacobson_iff_forall_quasispectrum_mul_subset_singleton_zero]

namespace Ring

/-- An element of a unital algebra lies in its Jacobson radical exactly when every left
multiple of it has spectral radius zero. -/
theorem mem_jacobson_iff_forall_spectralRadius_mul_eq_zero {B : Type*} [Ring B]
    [Algebra 𝕜 B] {a : B} :
    a ∈ Ring.jacobson B ↔ ∀ b : B, spectralRadius 𝕜 (b * a) = 0 := by
  simp_rw [mem_jacobson_iff_forall_spectrum_mul_subset_singleton_zero (𝕜 := 𝕜),
    spectralRadius_eq_zero_iff_spectrum_subset_singleton_zero]

/-- An element of a complex Banach algebra lies in its Jacobson radical exactly when every
left multiple `b * a` is quasinilpotent, that is, `‖(b * a) ^ n‖ ^ (1 / n)` tends to zero. -/
theorem mem_jacobson_iff_forall_gelfandRadius_mul_eq_zero {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] {a : B} :
    a ∈ Ring.jacobson B ↔ ∀ b : B, gelfandRadius (b * a) = 0 := by
  simp_rw [mem_jacobson_iff_forall_spectralRadius_mul_eq_zero (𝕜 := ℂ),
    spectrum.spectralRadius_eq_gelfandRadius, ENNReal.ofReal_eq_zero]
  exact forall_congr' fun b => (gelfandRadius_nonneg (b * a)).ge_iff_eq'

end Ring

end Quasinilpotent

end TauCeti
