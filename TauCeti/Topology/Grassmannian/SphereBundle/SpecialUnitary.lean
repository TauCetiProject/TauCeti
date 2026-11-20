/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary

/-!
# The sphere bundle `SU(n) → SU(1 + n) → S^(2n+1)`

Evaluating a special unitary matrix on the first coordinate vector `e₀` gives the map
`SU(1 + n) → S^(2n+1)`, `A ↦ A e₀` (`TauCeti.specialUnitarySphereMap`), to the unit sphere of
`ℂ^(1 + n)`. Its fibre over `e₀` is the block subgroup `diag(1, SU(n))`, the image of
`Matrix.SpecialUnitaryGroup.fromBlocksOne ℂ 1 n`, and its fibres are the left cosets of that
subgroup. For `n ≥ 1` this map is surjective and a locally trivial bundle with fibre `SU(n)`, and
hence a Serre fibration. For `n = 0` it is not surjective: `SU(1)` is trivial while the unit circle
of `ℂ` is not a point.

For `n = 2` this is the bundle `SU(2) → SU(3) → S⁵`, `B ↦ diag(1, B)`, `A ↦ A e₀`, with fibre
`SU(2) ≅ S³` and base `S⁵`, from which the integral homology of `SU(3)`, free of rank one in degrees
`0, 3, 5, 8`, is read off by a spectral sequence that collapses for degree reasons.

The map is the special unitary Stiefel map `TauCeti.specialUnitaryFrameMap 1 n` read through the
identification of orthonormal one-frames with unit vectors
(`TauCeti.finiteOrthonormalFrame.sphereHomeomorph`), and its charts are those of
`TauCeti.Topology.Grassmannian.StiefelFibration.SpecialUnitary` transported along that
homeomorphism. The coordinates are indexed by `Fin (1 + n)`, so that the block subgroup
`diag(1, SU(n))` is the image of `fromBlocksOne ℂ 1 n` without reindexing.

## Main definitions

* `TauCeti.specialUnitarySphereMap`: the evaluation map `SU(1 + n) → S^(2n+1)`, `A ↦ A e₀`.
* `TauCeti.specialUnitarySphereFiberHomeomorph`: `SU(n)` is homeomorphic to the fibre of
  `A ↦ A e₀` over `e₀`, through `B ↦ diag(1, B)`.

## Main results

* `TauCeti.specialUnitarySphereMap_eq_specialUnitarySphereMap_iff`: the fibres are the left cosets
  of the block subgroup `diag(1, SU(n))`.
* `TauCeti.surjective_specialUnitarySphereMap`: for `n ≥ 1`, every unit vector is the first column
  of a special unitary matrix.
* `TauCeti.exists_trivialization_specialUnitarySphereMap`: a chart with fibre `SU(n)` around each
  point of the sphere.
* `TauCeti.specialUnitarySphereMap_mem_serreFibrations`: `SU(1 + n) → S^(2n+1)` is a Serre
  fibration.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the fibrations
  `SU(n - 1) → SU(n) → S^(2n-1)`) and §5.1 (the homology of `SU(n)` from these fibrations).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §7.
-/

public section

open Matrix Metric Set Topology

noncomputable section

namespace TauCeti

/-! ### The evaluation map `SU(1 + n) → S^(2n+1)` -/

variable (n : ℕ)

/-- The evaluation map `SU(1 + n) → S^(2n+1)`, `A ↦ A e₀`, on the first coordinate vector `e₀`. -/
def specialUnitarySphereMap (A : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1 :=
  finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n) (specialUnitaryFrameMap 1 n A)

variable {n}

/-- In coordinates, `specialUnitarySphereMap n A` is the first column `A e₀` of `A`. -/
@[simp]
theorem coe_specialUnitarySphereMap (A : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    (specialUnitarySphereMap n A : EuclideanSpace ℂ (Fin (1 + n))) =
      WithLp.toLp 2 ((A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ).col 0) := by
  -- `Fin.castAdd_zero` needs the target written as `Fin (m + 1)`, and `Fin (1 + n)` is not of
  -- that form, so the cast of `0` is normalized by hand.
  simp [specialUnitarySphereMap, show Fin.castAdd n (0 : Fin 1) = 0 from Fin.ext (by simp)]

variable (n) in
/-- The evaluation map `SU(1 + n) → S^(2n+1)` is continuous. -/
@[fun_prop]
theorem continuous_specialUnitarySphereMap : Continuous (specialUnitarySphereMap n) :=
  (finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n)).continuous.comp
    (continuous_specialUnitaryFrameMap 1 n)

/-- The evaluation map is equivariant: `(A B) e₀ = A (B e₀)`. -/
theorem ofLp_specialUnitarySphereMap_mul (A B : specialUnitaryGroup (Fin (1 + n)) ℂ) :
    WithLp.ofLp (specialUnitarySphereMap n (A * B) : EuclideanSpace ℂ (Fin (1 + n))) =
      (A : Matrix (Fin (1 + n)) (Fin (1 + n)) ℂ) *ᵥ
        WithLp.ofLp (specialUnitarySphereMap n B : EuclideanSpace ℂ (Fin (1 + n))) := by
  simp only [coe_specialUnitarySphereMap, Submonoid.coe_mul]
  ext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- The fibres of the evaluation map are the left cosets of the block subgroup
`diag(1, SU(n))`. -/
theorem specialUnitarySphereMap_eq_specialUnitarySphereMap_iff
    {A B : specialUnitaryGroup (Fin (1 + n)) ℂ} :
    specialUnitarySphereMap n A = specialUnitarySphereMap n B ↔
      A⁻¹ * B ∈ (SpecialUnitaryGroup.fromBlocksOne ℂ 1 n).range :=
  (finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n)).injective.eq_iff.trans
    specialUnitaryFrameMap_eq_specialUnitaryFrameMap_iff

/-- The fibre of the evaluation map over `e₀` is the block subgroup `diag(1, SU(n))`. -/
theorem specialUnitarySphereMap_eq_specialUnitarySphereMap_one_iff
    {A : specialUnitaryGroup (Fin (1 + n)) ℂ} :
    specialUnitarySphereMap n A = specialUnitarySphereMap n 1 ↔
      A ∈ (SpecialUnitaryGroup.fromBlocksOne ℂ 1 n).range :=
  (finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n)).injective.eq_iff.trans
    specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff

/-- For `n ≥ 1`, every unit vector of `ℂ^(1 + n)` is the first column of a special unitary
matrix. -/
theorem surjective_specialUnitarySphereMap [NeZero n] :
    Function.Surjective (specialUnitarySphereMap n) :=
  (finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n)).surjective.comp
    surjective_specialUnitaryFrameMap

/-! ### The fibre over `e₀` -/

variable (n) in
/-- The fibre of the evaluation map over `e₀` is `SU(n)`: the block embedding `B ↦ diag(1, B)` is
a homeomorphism of `SU(n)` onto the special unitary matrices fixing `e₀`. -/
def specialUnitarySphereFiberHomeomorph :
    specialUnitaryGroup (Fin n) ℂ ≃ₜ
      specialUnitarySphereMap n ⁻¹' {specialUnitarySphereMap n 1} :=
  (specialUnitaryFrameFiberHomeomorph 1 n).trans
    (Homeomorph.setCongr <| by
      ext A
      rw [mem_preimage, mem_singleton_iff, mem_preimage, mem_singleton_iff,
        specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff,
        specialUnitarySphereMap_eq_specialUnitarySphereMap_one_iff])

@[simp]
theorem coe_specialUnitarySphereFiberHomeomorph_apply (B : specialUnitaryGroup (Fin n) ℂ) :
    (specialUnitarySphereFiberHomeomorph n B : specialUnitaryGroup (Fin (1 + n)) ℂ) =
      SpecialUnitaryGroup.fromBlocksOne ℂ 1 n B :=
  coe_specialUnitaryFrameFiberHomeomorph_apply B

/-- A special unitary matrix fixing `e₀` is the block matrix `diag(1, B)` of its image `B` in
`SU(n)`. -/
@[simp]
theorem fromBlocksOne_specialUnitarySphereFiberHomeomorph_symm_apply
    (A : specialUnitarySphereMap n ⁻¹' {specialUnitarySphereMap n 1}) :
    SpecialUnitaryGroup.fromBlocksOne ℂ 1 n ((specialUnitarySphereFiberHomeomorph n).symm A) =
      A := by
  rw [← coe_specialUnitarySphereFiberHomeomorph_apply, Homeomorph.apply_symm_apply]

/-- The identity of `SU(n)` corresponds to the identity of `SU(1 + n)` in the fibre. -/
@[simp]
theorem specialUnitarySphereFiberHomeomorph_one :
    specialUnitarySphereFiberHomeomorph n 1 = ⟨1, rfl⟩ :=
  Subtype.ext (by simp)

/-! ### Local triviality -/

/-- For `n ≥ 1`, the evaluation map `SU(1 + n) → S^(2n+1)` has a chart with fibre `SU(n)` around
each point of the sphere. -/
theorem exists_trivialization_specialUnitarySphereMap [NeZero n]
    (b : sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1) :
    ∃ e : Bundle.Trivialization (specialUnitaryGroup (Fin n) ℂ) (specialUnitarySphereMap n),
      b ∈ e.baseSet := by
  -- A local section of the frame map near the frame `φ⁻¹ b`, read through the homeomorphism `φ`
  -- between one-frames and unit vectors.
  let φ := finiteOrthonormalFrame.sphereHomeomorph ℂ (1 + n)
  obtain ⟨U, hU, hb, s, hs, hsec⟩ := exists_mem_specialUnitaryFrameMap_localSection (φ.symm b)
  have hsec' : ∀ y ∈ φ.symm ⁻¹' U, specialUnitarySphereMap n (s (φ.symm y)) = y := fun y hy ↦ by
    rw [specialUnitarySphereMap, hsec _ hy, Homeomorph.apply_symm_apply]
  let e := Subgroup.localSectionTrivializationOfCosetFibers
    (SpecialUnitaryGroup.fromBlocksOne ℂ 1 n).range (continuous_specialUnitarySphereMap n)
    (fun _ _ ↦ specialUnitarySphereMap_eq_specialUnitarySphereMap_iff) (φ.symm ⁻¹' U)
    (hU.preimage φ.symm.continuous) (s ∘ φ.symm) (hs.comp φ.symm.continuous.continuousOn
      fun _ hy ↦ hy) hsec'
  refine ⟨e.transFiberHomeomorph
    ((specialUnitaryFrameFiberHomeomorph 1 n).trans (Homeomorph.setCongr ?_)).symm, ?_⟩
  · ext A
    rw [mem_preimage, mem_singleton_iff, specialUnitaryFrameMap_eq_specialUnitaryFrameMap_one_iff,
      SetLike.mem_coe]
  · simpa only [Bundle.Trivialization.transFiberHomeomorph, e,
      Subgroup.localSectionTrivializationOfCosetFibers_baseSet, mem_preimage] using hb

/-- For `n ≥ 1`, the evaluation map `SU(1 + n) → S^(2n+1)`, `A ↦ A e₀`, is a Serre fibration: it is
locally trivial with fibre `SU(n)`. For `n = 2` this is the bundle `SU(2) → SU(3) → S⁵`. -/
theorem specialUnitarySphereMap_mem_serreFibrations [NeZero n] :
    TopCat.serreFibrations
      (_root_.TopCat.ofHom ⟨specialUnitarySphereMap n, continuous_specialUnitarySphereMap n⟩ :
        _root_.TopCat.of (specialUnitaryGroup (Fin (1 + n)) ℂ) ⟶
          _root_.TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (1 + n))) 1)) :=
  TopCat.mem_serreFibrations_of_exists_trivialization
    (F := specialUnitaryGroup (Fin n) ℂ) exists_trivialization_specialUnitarySphereMap

end TauCeti
