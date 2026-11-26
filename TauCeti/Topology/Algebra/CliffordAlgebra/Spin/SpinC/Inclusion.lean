/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Inclusion
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Real
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Real.Orbit.Bundle

/-!
# Topology of the lower-rank subgroup `Spinᶜ(n) ⊆ Spinᶜ(n + 1)`

The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`, `[s, z] ↦ [s, z]`
(`CliffordAlgebra.realCliffordSpinCInclusion`), is continuous for the quotient topologies, as is
the map of `Spinᶜ` groups induced by any quadratic isometry. Since `Spinᶜ(n)` is compact and
`Spinᶜ(n + 1)` is Hausdorff, it is a closed embedding
(`CliffordAlgebra.isClosedEmbedding_realCliffordSpinCInclusion`), so `Spinᶜ(n)` is isomorphic as a
topological group to the stabilizer of the last coordinate vector in `Spinᶜ(n + 1)`
(`CliffordAlgebra.realCliffordSpinCContinuousMulEquivLastStabilizer`), which is closed.

The rotation of `Spinᶜ(n + 1)` moves the last coordinate vector `eₙ` to every unit vector, with
continuous local choices: near any unit vector `u₀` there is a map `g` to `Spinᶜ(n + 1)`,
continuous near `u₀`, whose rotation sends `eₙ` to `u` for every `u` near `u₀`
(`CliffordAlgebra.exists_continuousOn_realCliffordSpinCGroupZero_toSpecialOrthogonal_last`). It is
obtained from a local trivialization of the Spin sphere bundle `Spin(n + 1) → Sⁿ` around `u₀`
(`CliffordAlgebra.isFiberBundle_realCliffordSpinOrbitMap`): `g u` is the point of the fibre over `u`
corresponding to `1 ∈ Spin(n)`, included via `s ↦ [s, 1]`.

With the algebraic stabilizer computation, these are the facts about structure groups behind the
restriction of a `Spinᶜ(n + 1)` structure on `E' ⊕ ℝν` to a `Spinᶜ(n)` structure on `E'`: the
points whose frames send `eₙ` to the unit normal `ν` form a principal bundle for the stabilizer,
locally trivialized by correcting a local section with `g`.

## Main definitions

* `CliffordAlgebra.realCliffordSpinCContinuousMulEquivLastStabilizer`: `Spinᶜ(n)` is isomorphic
  as a topological group to the last-vector stabilizer in `Spinᶜ(n + 1)`.

## Main results

* `CliffordAlgebra.continuous_realCliffordSpinCInclusion`,
  `CliffordAlgebra.isClosedEmbedding_realCliffordSpinCInclusion`: the inclusion is a continuous
  closed embedding.
* `CliffordAlgebra.isClosed_realCliffordSpinCLastStabilizer`: the stabilizer is closed.
* `CliffordAlgebra.exists_continuousOn_realCliffordSpinCGroupZero_toSpecialOrthogonal_last`:
  continuous local choices of rotations carrying the last coordinate vector to a varying unit
  vector.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter I, §2
  and Appendix D.
-/

public section

noncomputable section

open TauCeti Topology

namespace CliffordAlgebra

variable (n : ℕ) [NeZero n]

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is continuous** for the quotient topologies. -/
@[fun_prop]
theorem continuous_realCliffordSpinCInclusion :
    Continuous (realCliffordSpinCInclusion n) := by
  rw [realCliffordSpinCInclusion_eq_spinCGroupMap]
  exact (realCliffordSpinInclusionIsometry n).continuous_spinCGroupMap _ _

/-- **The inclusion `Spinᶜ(n) → Spinᶜ(n + 1)` is a closed embedding**: it is a continuous
injection from a compact space to a Hausdorff space. -/
theorem isClosedEmbedding_realCliffordSpinCInclusion :
    IsClosedEmbedding (realCliffordSpinCInclusion n) :=
  (continuous_realCliffordSpinCInclusion n).isClosedEmbedding
    (realCliffordSpinCInclusion_injective n)

/-- The last-vector stabilizer in `Spinᶜ(n + 1)` is closed. -/
theorem isClosed_realCliffordSpinCLastStabilizer :
    IsClosed (realCliffordSpinCLastStabilizer n : Set (realCliffordSpinCGroupZero (n + 1))) := by
  rw [← range_realCliffordSpinCInclusion, MonoidHom.coe_range]
  exact (isClosedEmbedding_realCliffordSpinCInclusion n).isClosed_range

/-- **`Spinᶜ(n)` is isomorphic as a topological group to the last-vector stabilizer in
`Spinᶜ(n + 1)`**, through the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
def realCliffordSpinCContinuousMulEquivLastStabilizer :
    realCliffordSpinCGroupZero n ≃ₜ* realCliffordSpinCLastStabilizer n :=
  ContinuousMulEquiv.mk'
    (Continuous.homeoOfEquivCompactToT2 (f := (realCliffordSpinCEquivLastStabilizer n).toEquiv)
      (((continuous_realCliffordSpinCInclusion n).subtype_mk
        (realCliffordSpinCInclusion_mem_lastStabilizer n)).congr fun x ↦
          Subtype.ext (coe_realCliffordSpinCEquivLastStabilizer_apply n x).symm))
    (map_mul (realCliffordSpinCEquivLastStabilizer n))

/-- The topological stabilizer isomorphism has the algebraic stabilizer isomorphism as its
underlying group isomorphism. -/
@[simp]
theorem realCliffordSpinCContinuousMulEquivLastStabilizer_toMulEquiv :
    (realCliffordSpinCContinuousMulEquivLastStabilizer n : realCliffordSpinCGroupZero n ≃*
      realCliffordSpinCLastStabilizer n) = realCliffordSpinCEquivLastStabilizer n :=
  (rfl)

/-- The topological stabilizer isomorphism is the inclusion `Spinᶜ(n) → Spinᶜ(n + 1)`. -/
@[simp]
theorem coe_realCliffordSpinCContinuousMulEquivLastStabilizer_apply
    (x : realCliffordSpinCGroupZero n) :
    (realCliffordSpinCContinuousMulEquivLastStabilizer n x :
        realCliffordSpinCGroupZero (n + 1)) =
      realCliffordSpinCInclusion n x :=
  coe_realCliffordSpinCEquivLastStabilizer_apply n x

/-- The inverse topological stabilizer isomorphism sends an included element back to its
source. -/
@[simp]
theorem realCliffordSpinCContinuousMulEquivLastStabilizer_symm_apply_inclusion
    (x : realCliffordSpinCGroupZero n) :
    (realCliffordSpinCContinuousMulEquivLastStabilizer n).symm
      ⟨realCliffordSpinCInclusion n x, realCliffordSpinCInclusion_mem_lastStabilizer n x⟩ = x :=
  realCliffordSpinCEquivLastStabilizer_symm_apply_inclusion n x

/-- The inverse topological stabilizer isomorphism, followed by the inclusion, is the subgroup
inclusion. -/
@[simp]
theorem realCliffordSpinCInclusion_realCliffordSpinCContinuousMulEquivLastStabilizer_symm_apply
    (y : realCliffordSpinCLastStabilizer n) :
    realCliffordSpinCInclusion n ((realCliffordSpinCContinuousMulEquivLastStabilizer n).symm y) =
      y :=
  realCliffordSpinCInclusion_realCliffordSpinCEquivLastStabilizer_symm_apply n y

/-- **Continuous local rotations onto the unit sphere.** Near every unit vector `u₀` of `ℝⁿ⁺¹`
there is a map `g` to `Spinᶜ(n + 1)`, continuous near `u₀`, whose rotation carries the last
coordinate vector to `u` for every unit vector `u` near `u₀`. -/
theorem exists_continuousOn_realCliffordSpinCGroupZero_toSpecialOrthogonal_last
    (u₀ : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1}) :
    ∃ U : Set {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1},
      IsOpen U ∧ u₀ ∈ U ∧
      ∃ g : {x : Fin (n + 1) → ℝ // realCliffordForm (n + 1) 0 x = 1} →
          realCliffordSpinCGroupZero (n + 1),
        ContinuousOn g U ∧ ∀ u ∈ U,
          (spinCGroup.toSpecialOrthogonal _ _ (g u) :
              (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ)) (Pi.single (Fin.last n) 1) = u.val := by
  let h := (realCliffordUnitLevelHomeomorphSubtype (n + 1)).symm
  obtain ⟨e, he⟩ := isFiberBundle_realCliffordSpinOrbitMap n (h u₀)
  refine ⟨h ⁻¹' e.baseSet, e.open_baseSet.preimage h.continuous, he,
    fun u ↦ spinCGroup.ofSpin _ _ (e.toOpenPartialHomeomorph.symm (h u, 1)), ?_, fun u hu ↦ ?_⟩
  · exact (spinCGroup.continuous_ofSpin _ _).comp_continuousOn
      (e.continuousOn_symm_prodMk_left.comp h.continuous.continuousOn fun _ hu ↦ hu)
  · have hproj := congrArg Subtype.val (e.proj_symm_apply' (x := 1) hu)
    simp only [realCliffordSpinOrbitMap_apply, SubMulAction.val_smul, spinGroup_smul_apply,
      coe_realCliffordSpinLastUnit, h, coe_realCliffordUnitLevelHomeomorphSubtype_symm_apply]
      at hproj
    rw [spinCGroup.toSpecialOrthogonal_ofSpin, coe_spinToSpecialOrthogonal_apply, hproj]

end CliffordAlgebra
