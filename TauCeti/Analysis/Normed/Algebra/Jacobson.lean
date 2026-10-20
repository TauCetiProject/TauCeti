/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import TauCeti.Analysis.Normed.Ring.Units
public import TauCeti.RingTheory.Jacobson.NonUnital

/-!
# Closedness of Jacobson radicals

The Jacobson radical of a Banach algebra is closed, including for nonunital algebras.
In the unital case it is an intersection of closed maximal left ideals. In the nonunital
case we use the external unitization with its ℓ¹ norm, not the regular-representation
norm, which need not be available. The underlying scalar submodule is consequently
complete when the original algebra is complete.

The statements use summability of geometric series instead of completeness wherever
possible. No normalization of the norm of the identity is assumed.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* We use Mathlib's `Ideal.IsMaximal.isClosed`, `WithLp.unitizationAlgEquiv`, and
  `Module.comap_jacobson_of_bijective`.
-/

public section

namespace TauCeti

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

/-- The radical defined with the algebraic unitization can equally be tested in its
ℓ¹-normed version. -/
theorem mem_nonUnitalJacobson_iff_mem_unitizationL1 {a : A} :
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
    exact mem_nonUnitalJacobson_iff_mem_unitizationL1 𝕜 A
  rw [hset]
  exact (Ring.isClosed_jacobson _).preimage WithLp.unitization_isometry_inr.continuous

/-- The scalar submodule underlying the nonunital radical is closed. -/
theorem isClosed_nonUnitalJacobsonSubmodule :
    IsClosed (nonUnitalJacobsonSubmodule 𝕜 A : Set A) := by
  rw [coe_nonUnitalJacobsonSubmodule]
  exact isClosed_nonUnitalJacobson 𝕜 A

end TauCeti
