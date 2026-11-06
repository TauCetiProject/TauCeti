/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Torus
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic

import Mathlib.Topology.Homeomorph.Quotient
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.QR
import TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperTriangular
import TauCeti.Topology.Algebra.UnitaryGroup

/-!
# The flag manifold of `GL n` is `U(n) / T`

Let `B` be the upper triangular subgroup of `GL n 𝕜`, for `𝕜 = ℝ` or `ℂ`. The quotient
`GL n 𝕜 ⧸ B` is the **flag manifold**, a homogeneous space of `GL n 𝕜`. (Since `B` is the
stabilizer of the standard complete flag `0 ⊂ 𝕜¹ ⊂ 𝕜² ⊂ ⋯ ⊂ 𝕜ⁿ`, it parametrizes the complete
flags in `𝕜ⁿ`; that identification is not made here.) This file proves the compact picture of it,

`U(n) ⧸ T ≃ₜ GL n 𝕜 ⧸ B`,

where `U(n) = Matrix.unitaryGroup (Fin n) 𝕜` and `T` is the subgroup of diagonal unitary
matrices. For `𝕜 = ℂ` this `T` is the maximal torus `TauCeti.unitaryTorus` of `U(n)`, and the
homeomorphism identifies `G / T` for the compact group `G = U(n)` with `G_ℂ / B` for its
complexification `G_ℂ = GL n ℂ`. Consequently the flag manifold is compact.

The homeomorphism is induced by the inclusion `U(n) → GL n 𝕜` (`Unitary.toUnits`), and is
equivariant for the left actions of `U(n)`. It rests on two facts.

* **`U(n)` acts transitively on `GL n 𝕜 ⧸ B`:** every invertible matrix is `g = U b` with `U`
  unitary and `b` upper triangular
  (`Matrix.GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq`, from
  `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.QR`). This is the `QR` factorization.
* **The stabilizer is `T`:** a unitary upper triangular matrix is diagonal
  (`TauCeti.mem_comap_toUnits_upperTriangularGroup_iff`, from
  `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Unitary`).

The quotient `U(n) ⧸ T` is compact and `GL n 𝕜 ⧸ B` is Hausdorff because `B` is closed
(`TauCeti.isClosed_upperTriangularGroup`, from
`TauCeti.Topology.Algebra.Matrix.GeneralLinearGroup.UpperTriangular`), so the continuous
bijection between them is a homeomorphism.

## Main definitions

* `TauCeti.unitaryQuotientHomeomorph`: the homeomorphism
  `U(n) ⧸ (B ∩ U(n)) ≃ₜ GL n 𝕜 ⧸ B` induced by the inclusion, for `𝕜 = ℝ` or `ℂ`.
* `TauCeti.unitaryTorusQuotientHomeomorph`: the homeomorphism `U(n) ⧸ T ≃ₜ GL n ℂ ⧸ B` with `T`
  the maximal torus of `U(n)`.

## Main results

* `TauCeti.unitaryQuotientHomeomorph_smul` and `TauCeti.unitaryTorusQuotientHomeomorph_smul`:
  the homeomorphisms are `U(n)`-equivariant.
* The instance `CompactSpace (GL ι 𝕜 ⧸ upperTriangularGroup ι 𝕜)`: the flag manifold is compact.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Birkhäuser, 2002,
  Section VI.4 (the Iwasawa decomposition `G = K A N`, here in the form `GL n 𝕜 = U(n) B`).
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 2.1 (the `QR` factorization).
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section RCLike

variable {ι 𝕜 : Type*} [Fintype ι] [LinearOrder ι] [RCLike 𝕜]

variable (ι 𝕜) in
/-- **`U(n)` acts transitively on the flag manifold:** every coset of the upper triangular
subgroup of `GL n 𝕜` has a unitary representative, by the `QR` factorization. -/
private theorem toUnits_mk_surjective :
    Function.Surjective fun U : unitaryGroup ι 𝕜 =>
      (Unitary.toUnits U : GL ι 𝕜 ⧸ upperTriangularGroup ι 𝕜) := by
  intro y
  induction y using QuotientGroup.induction_on with | H g => ?_
  obtain ⟨U, b, hb, rfl⟩ := GeneralLinearGroup.exists_mem_upperTriangularGroup_toUnits_mul_eq g
  exact ⟨U, QuotientGroup.eq.2 (by simpa using hb)⟩

variable (ι 𝕜) in
/-- **The flag manifold of `GL n 𝕜` is `U(n) / T`**: the inclusion `U(n) → GL n 𝕜` induces a
homeomorphism from the quotient of `U(n)` by its unitary upper triangular (equivalently, diagonal)
matrices onto the quotient of `GL n 𝕜` by its upper triangular subgroup, for `𝕜 = ℝ` or `ℂ`. -/
def unitaryQuotientHomeomorph :
    unitaryGroup ι 𝕜 ⧸ (upperTriangularGroup ι 𝕜).comap Unitary.toUnits ≃ₜ
      GL ι 𝕜 ⧸ upperTriangularGroup ι 𝕜 :=
  Continuous.homeoOfEquivCompactToT2 (f := QuotientGroup.congrComapOfSurjectiveMk Unitary.toUnits
      (upperTriangularGroup ι 𝕜) (toUnits_mk_surjective ι 𝕜)) <| by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    exact (continuous_quotient_mk'.comp <| Units.continuous_iff.2
      ⟨continuous_subtype_val, continuous_subtype_val.star⟩).congr fun U =>
        (QuotientGroup.congrComapOfSurjectiveMk_mk _ _ _ U).symm

@[simp]
theorem unitaryQuotientHomeomorph_mk (U : unitaryGroup ι 𝕜) :
    unitaryQuotientHomeomorph ι 𝕜
        (U : unitaryGroup ι 𝕜 ⧸ (upperTriangularGroup ι 𝕜).comap Unitary.toUnits) =
      (Unitary.toUnits U : GL ι 𝕜 ⧸ upperTriangularGroup ι 𝕜) :=
  QuotientGroup.congrComapOfSurjectiveMk_mk _ _ _ U

/-- The homeomorphism `U(n) ⧸ T ≃ₜ GL n 𝕜 ⧸ B` is equivariant for the left actions of `U(n)`. -/
@[simp↓]
theorem unitaryQuotientHomeomorph_smul (U : unitaryGroup ι 𝕜)
    (x : unitaryGroup ι 𝕜 ⧸ (upperTriangularGroup ι 𝕜).comap Unitary.toUnits) :
    unitaryQuotientHomeomorph ι 𝕜 (U • x) =
      Unitary.toUnits U • unitaryQuotientHomeomorph ι 𝕜 x := by
  induction x using QuotientGroup.induction_on
  simp [MulAction.Quotient.smul_mk]

/-- **The flag manifold `GL n 𝕜 ⧸ B` is compact**, for `𝕜 = ℝ` or `ℂ`, being homeomorphic to a
quotient of the compact group `U(n)`. -/
instance : CompactSpace (GL ι 𝕜 ⧸ upperTriangularGroup ι 𝕜) :=
  (unitaryQuotientHomeomorph ι 𝕜).compactSpace

end RCLike

variable (ι : Type*) [Fintype ι] [LinearOrder ι]

/-- **The flag manifold of `GL n ℂ` is `U(n) / T` for the maximal torus `T`** of diagonal unitary
matrices: the inclusion `U(n) → GL n ℂ` induces a homeomorphism `U(n) ⧸ T ≃ₜ GL n ℂ ⧸ B`. -/
def unitaryTorusQuotientHomeomorph :
    unitaryGroup ι ℂ ⧸ unitaryTorus ι ≃ₜ GL ι ℂ ⧸ upperTriangularGroup ι ℂ :=
  (Homeomorph.Quotient.congrRight fun _ _ => by
    rw [comap_toUnits_upperTriangularGroup_eq_unitaryTorus]).trans
    (unitaryQuotientHomeomorph ι ℂ)

@[simp]
theorem unitaryTorusQuotientHomeomorph_mk (U : unitaryGroup ι ℂ) :
    unitaryTorusQuotientHomeomorph ι (U : unitaryGroup ι ℂ ⧸ unitaryTorus ι) =
      (Unitary.toUnits U : GL ι ℂ ⧸ upperTriangularGroup ι ℂ) :=
  unitaryQuotientHomeomorph_mk U

/-- The homeomorphism `U(n) ⧸ T ≃ₜ GL n ℂ ⧸ B` is equivariant for the left actions of `U(n)`. -/
@[simp↓]
theorem unitaryTorusQuotientHomeomorph_smul (U : unitaryGroup ι ℂ)
    (x : unitaryGroup ι ℂ ⧸ unitaryTorus ι) :
    unitaryTorusQuotientHomeomorph ι (U • x) =
      Unitary.toUnits U • unitaryTorusQuotientHomeomorph ι x := by
  induction x using QuotientGroup.induction_on
  simp [MulAction.Quotient.smul_mk]

end TauCeti
