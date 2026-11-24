/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Stabilizer
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Real

/-!
# The lower-rank subgroup `Spinᶜ(n) ⊆ Spinᶜ(n + 1)`

Write `Spinᶜ(n)` for `spinCGroup` of the standard positive-definite form on `ℝⁿ`, `n ≥ 1`
(`CliffordAlgebra.realCliffordSpinCGroupZero`). Appending a last coordinate `0` is a quadratic
isometry `ℝⁿ → ℝⁿ⁺¹` (`CliffordAlgebra.realCliffordSpinInclusionIsometry`), and it induces the
injective homomorphism `[s, z] ↦ [s, z]` from `Spinᶜ(n)` to `Spinᶜ(n + 1)`
(`CliffordAlgebra.realCliffordSpinCInclusion`). Its rotation acts on `ℝⁿ ⊕ ℝ` as the rotation of
the source on the first summand and as the identity on the last coordinate
(`CliffordAlgebra.toSpecialOrthogonal_realCliffordSpinCInclusion_snoc`).

Conversely, every element of `Spinᶜ(n + 1)` whose rotation fixes the last coordinate vector comes
from `Spinᶜ(n)`: writing it as `[s, z]`, the Spin element `s` fixes that vector, so it comes from
`Spin(n)` (`CliffordAlgebra.realCliffordSpinStabilizerInclusion_surjective`). Hence `Spinᶜ(n)` is
isomorphic to the stabilizer of the last coordinate vector in `Spinᶜ(n + 1)`
(`CliffordAlgebra.realCliffordSpinCEquivLastStabilizer`).

This is the structure-group step of restricting a `Spinᶜ` structure to a boundary: on a bundle
`E = E' ⊕ ℝν` with unit normal `ν`, the points of a `Spinᶜ(n + 1)` structure whose frames send the
last coordinate vector to `ν` form a principal bundle for this stabilizer, that is, a `Spinᶜ(n)`
structure on `E'`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinCInclusion n`: the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`.
* `CliffordAlgebra.realCliffordSpinCLastStabilizer n`: the subgroup of `Spinᶜ(n + 1)` whose
  rotations fix the last coordinate vector.
* `CliffordAlgebra.realCliffordSpinCEquivLastStabilizer n`: `Spinᶜ(n)` is isomorphic to that
  stabilizer.

## Main results

* `CliffordAlgebra.toSpecialOrthogonal_realCliffordSpinCInclusion_snoc`: the rotation of an
  included element acts on `(v, r)` as `(π v, r)`.
* `CliffordAlgebra.realCliffordSpinCInclusion_injective`: the inclusion is injective.
* `CliffordAlgebra.range_realCliffordSpinCInclusion`: its image is the last-vector stabilizer.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti TauCeti.QuadraticMap

variable (n : ℕ) [NeZero n]

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`**, `[s, z] ↦ [s, z]`, induced by the quadratic
isometry `ℝⁿ → ℝⁿ⁺¹` appending a last coordinate `0`. -/
def realCliffordSpinCInclusion :
    realCliffordSpinCGroupZero n →* realCliffordSpinCGroupZero (n + 1) :=
  (realCliffordSpinInclusionIsometry n).spinCGroupMap _ _

/-- The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is the map induced by its defining quadratic
isometry. -/
theorem realCliffordSpinCInclusion_eq_spinCGroupMap :
    realCliffordSpinCInclusion n = (realCliffordSpinInclusionIsometry n).spinCGroupMap _ _ :=
  (rfl)

/-- The inclusion sends `[s, z]` to `[s, z]`, with `s` included by
`CliffordAlgebra.realCliffordSpinInclusion`. -/
@[simp]
theorem realCliffordSpinCInclusion_mk (p : realCliffordSpinGroupZero n × Circle) :
    realCliffordSpinCInclusion n (spinCGroup.mk _ _ p) =
      spinCGroup.mk _ _ (realCliffordSpinInclusion n p.1, p.2) := by
  rw [realCliffordSpinCInclusion_eq_spinCGroupMap, Isometry.spinCGroupMap_mk,
    realCliffordSpinInclusion_eq_spinGroupMap]

/-- The inclusion sends the Spin element `[s, 1]` to `[s, 1]`. -/
@[simp]
theorem realCliffordSpinCInclusion_ofSpin (s : realCliffordSpinGroupZero n) :
    realCliffordSpinCInclusion n (spinCGroup.ofSpin _ _ s) =
      spinCGroup.ofSpin _ _ (realCliffordSpinInclusion n s) := by
  simp [spinCGroup.ofSpin_apply]

/-- The inclusion sends the central element `[1, z]` to `[1, z]`. -/
@[simp]
theorem realCliffordSpinCInclusion_ofCircle (z : Circle) :
    realCliffordSpinCInclusion n (spinCGroup.ofCircle _ _ z) = spinCGroup.ofCircle _ _ z :=
  Isometry.spinCGroupMap_ofCircle _ _ _ z

/-- The inclusion preserves the determinant character. -/
@[simp]
theorem det_realCliffordSpinCInclusion (x : realCliffordSpinCGroupZero n) :
    spinCGroup.det _ _ (realCliffordSpinCInclusion n x) = spinCGroup.det _ _ x :=
  Isometry.det_spinCGroupMap _ _ _ x

/-- The rotation of an included element fixes the last coordinate vector. -/
@[simp]
theorem toSpecialOrthogonal_realCliffordSpinCInclusion_last (x : realCliffordSpinCGroupZero n) :
    (spinCGroup.toSpecialOrthogonal _ _ (realCliffordSpinCInclusion n x) :
        (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Pi.single (Fin.last n) 1) =
      Pi.single (Fin.last n) 1 := by
  obtain ⟨p, rfl⟩ := spinCGroup.mk_surjective _ _ x
  rw [realCliffordSpinCInclusion_mk, spinCGroup.toSpecialOrthogonal_mk,
    coe_spinToSpecialOrthogonal_apply, realCliffordSpinInclusion_fixed_last]

/-- **The rotation of an included element** acts on `(v, r) ∈ ℝⁿ ⊕ ℝ` as the rotation of the
source on `v`, fixing the last coordinate `r`. -/
@[simp]
theorem toSpecialOrthogonal_realCliffordSpinCInclusion_snoc (x : realCliffordSpinCGroupZero n)
    (v : Fin n → ℝ) (r : ℝ) :
    (spinCGroup.toSpecialOrthogonal _ _ (realCliffordSpinCInclusion n x) :
        (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Fin.snoc v r) =
      Fin.snoc ((spinCGroup.toSpecialOrthogonal _ _ x : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) v) r := by
  have hsplit (w : Fin n → ℝ) :
      (Fin.snoc w r : Fin (n + 1) → ℝ) =
        realCliffordSpinInclusionIsometry n w + r • Pi.single (Fin.last n) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  rw [hsplit, hsplit, map_add, map_smul, toSpecialOrthogonal_realCliffordSpinCInclusion_last,
    realCliffordSpinCInclusion_eq_spinCGroupMap, Isometry.toSpecialOrthogonal_spinCGroupMap_apply]

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is injective.** -/
theorem realCliffordSpinCInclusion_injective :
    Function.Injective (realCliffordSpinCInclusion n) := by
  rw [realCliffordSpinCInclusion_eq_spinCGroupMap]
  refine (realCliffordSpinInclusionIsometry n).spinCGroupMap_injective _ _ ?_
  rw [← realCliffordSpinInclusion_eq_spinGroupMap]
  exact realCliffordSpinInclusion_injective n

/-- **The last-vector stabilizer in `Spinᶜ(n + 1)`**: the elements whose rotation fixes the last
coordinate vector. -/
def realCliffordSpinCLastStabilizer : Subgroup (realCliffordSpinCGroupZero (n + 1)) :=
  Subgroup.comap ((specialOrthogonalGroup (realCliffordForm (n + 1) 0)).subtype.comp
      (spinCGroup.toSpecialOrthogonal _ _))
    (MulAction.stabilizer ((Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
      (Pi.single (Fin.last n) (1 : ℝ) : Fin (n + 1) → ℝ))

omit [NeZero n] in
variable {n} in
/-- An element lies in the last-vector stabilizer exactly when its rotation fixes the last
coordinate vector. -/
@[simp]
theorem mem_realCliffordSpinCLastStabilizer_iff {x : realCliffordSpinCGroupZero (n + 1)} :
    x ∈ realCliffordSpinCLastStabilizer n ↔
      (spinCGroup.toSpecialOrthogonal _ _ x : (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
        (Pi.single (Fin.last n) 1) = Pi.single (Fin.last n) 1 :=
  Iff.rfl

/-- **The image of `Spinᶜ(n) → Spinᶜ(n + 1)` is the last-vector stabilizer**: an element of
`Spinᶜ(n + 1)` comes from `Spinᶜ(n)` exactly when its rotation fixes the last coordinate vector. -/
theorem range_realCliffordSpinCInclusion :
    (realCliffordSpinCInclusion n).range = realCliffordSpinCLastStabilizer n := by
  ext y
  rw [MonoidHom.mem_range, mem_realCliffordSpinCLastStabilizer_iff]
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, rfl⟩
    exact toSpecialOrthogonal_realCliffordSpinCInclusion_last n x
  obtain ⟨⟨s, z⟩, rfl⟩ := spinCGroup.mk_surjective _ _ y
  rw [spinCGroup.toSpecialOrthogonal_mk, coe_spinToSpecialOrthogonal_apply] at hy
  obtain ⟨t, ht⟩ := realCliffordSpinStabilizerInclusion_surjective n
    ⟨s, mem_realCliffordSpinLastStabilizer_iff.2 hy⟩
  refine ⟨spinCGroup.mk _ _ (t, z), ?_⟩
  rw [realCliffordSpinCInclusion_mk, ← coe_realCliffordSpinStabilizerInclusion_apply, ht]

/-- An included element lies in the last-vector stabilizer. -/
theorem realCliffordSpinCInclusion_mem_lastStabilizer (x : realCliffordSpinCGroupZero n) :
    realCliffordSpinCInclusion n x ∈ realCliffordSpinCLastStabilizer n :=
  toSpecialOrthogonal_realCliffordSpinCInclusion_last n x

/-- **`Spinᶜ(n)` is isomorphic to the last-vector stabilizer in `Spinᶜ(n + 1)`**, through the
inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
def realCliffordSpinCEquivLastStabilizer :
    realCliffordSpinCGroupZero n ≃* realCliffordSpinCLastStabilizer n :=
  (MonoidHom.ofInjective (realCliffordSpinCInclusion_injective n)).trans
    (MulEquiv.subgroupCongr (range_realCliffordSpinCInclusion n))

/-- The stabilizer isomorphism is the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
@[simp]
theorem coe_realCliffordSpinCEquivLastStabilizer_apply (x : realCliffordSpinCGroupZero n) :
    (realCliffordSpinCEquivLastStabilizer n x : realCliffordSpinCGroupZero (n + 1)) =
      realCliffordSpinCInclusion n x :=
  (rfl)

/-- The inverse stabilizer isomorphism sends an included element back to its source. -/
@[simp]
theorem realCliffordSpinCEquivLastStabilizer_symm_apply_inclusion
    (x : realCliffordSpinCGroupZero n) :
    (realCliffordSpinCEquivLastStabilizer n).symm
      ⟨realCliffordSpinCInclusion n x, realCliffordSpinCInclusion_mem_lastStabilizer n x⟩ = x :=
  (realCliffordSpinCEquivLastStabilizer n).symm_apply_eq.2 (Subtype.ext (rfl))

/-- The inverse stabilizer isomorphism, followed by the inclusion, is the subgroup inclusion. -/
@[simp]
theorem realCliffordSpinCInclusion_realCliffordSpinCEquivLastStabilizer_symm_apply
    (y : realCliffordSpinCLastStabilizer n) :
    realCliffordSpinCInclusion n ((realCliffordSpinCEquivLastStabilizer n).symm y) = y := by
  rw [← coe_realCliffordSpinCEquivLastStabilizer_apply, MulEquiv.apply_symm_apply]

end CliffordAlgebra
