/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import TauCeti.Topology.Algebra.Group.NoSmallSubgroups

import Mathlib.Analysis.Normed.Operator.NormedSpace
import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
import TauCeti.Topology.Algebra.Group.Units

/-!
# Group homomorphisms induced by continuous representations

A group representation `π : ContRepresentation 𝕜 G V` maps every group element to an invertible
continuous linear operator, giving a homomorphism `π.toMonoidHom.toHomUnits : G →* (V →L[𝕜] V)ˣ`.
Over a normed field `𝕜`, equipping `V →L[𝕜] V` with the topology of bounded convergence makes
`π.toMonoidHom.toHomUnits` continuous whenever both `π` and inversion on `G` are continuous,
yielding `ContRepresentation.toUnitsContinuousMonoidHom`.

When `V` is a normed space over a nontrivially normed field `𝕜` that is a normed `ℝ`-algebra, the
integer homogeneity of the operator norm implies that any group admitting an injective
representation continuous at `1` has no small subgroups
(`ContRepresentation.hasNoSmallSubgroups_of_injective`), without assuming continuity of group
multiplication or inversion. For the same reason a representation of a profinite group on such a
space is continuous exactly when its kernel is open
(`ContRepresentation.continuous_iff_isOpen_ker`); in particular, a continuous complex
representation of a profinite group, such as an absolute Galois group, factors through a finite
quotient.

For the corresponding homomorphisms from unitary representations into `unitary (V →L[𝕜] V)`,
`unitarySubgroup (V →L[𝕜] V)ˣ`, and `Matrix.unitaryGroup ι 𝕜`, see
`TauCeti.RepresentationTheory.Continuous.Unitary.Hom`.

## Main definitions and results

* `ContRepresentation.continuous_toHomUnits`,
  `ContRepresentation.toUnitsContinuousMonoidHom`: continuity of `π.toMonoidHom.toHomUnits` and its
  bundled continuous homomorphism into `(V →L[𝕜] V)ˣ`.
* `ContRepresentation.hasNoSmallSubgroups_of_injective`: a group with an injective representation
  on a normed space over a nontrivially normed field that is a normed `ℝ`-algebra, continuous at
  `1`, has no small subgroups.
* `ContRepresentation.continuous_iff_isOpen_ker`: a representation of a profinite group on a
  normed space over such a field is continuous if and only if its kernel is open.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1, p. 53.
-/

public section

namespace ContRepresentation

section TopologicalVectorSpace

variable {𝕜 G V : Type*} [NormedField 𝕜] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module 𝕜 V]

/-- When inversion on `G` is continuous, continuity of `π` implies continuity of
`π.toMonoidHom.toHomUnits`. -/
theorem continuous_toHomUnits [TopologicalSpace G] [ContinuousInv G]
    {π : ContRepresentation 𝕜 G V} (hπ : Continuous π) :
    Continuous π.toMonoidHom.toHomUnits :=
  (MonoidHom.continuous_iff_continuous_val _).2 hπ

/-- A continuous group representation on a topological vector space over a normed field, bundled as
a continuous group homomorphism into `(V →L[𝕜] V)ˣ`. -/
def toUnitsContinuousMonoidHom [TopologicalSpace G] [ContinuousInv G]
    (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) : G →ₜ* (V →L[𝕜] V)ˣ :=
  ⟨π.toMonoidHom.toHomUnits, π.continuous_toHomUnits hπ⟩

/-- Evaluation of `ContRepresentation.toUnitsContinuousMonoidHom`. -/
@[simp]
theorem coe_toUnitsContinuousMonoidHom [TopologicalSpace G] [ContinuousInv G]
    (π : ContRepresentation 𝕜 G V) (hπ : Continuous π) :
    ⇑(π.toUnitsContinuousMonoidHom hπ) = π.toMonoidHom.toHomUnits :=
  (rfl)

end TopologicalVectorSpace

section NormedSpace

variable {𝕜 G V : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜] [Group G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- **Any group admitting an injective representation on a normed space, continuous at `1`, over a
nontrivially normed field that is a normed `ℝ`-algebra has no small subgroups.** Neither continuity
of multiplication nor continuity of inversion on `G` is needed. -/
theorem hasNoSmallSubgroups_of_injective [TopologicalSpace G]
    (π : ContRepresentation 𝕜 G V) (hπ_cont : ContinuousAt π 1) (hπ_inj : Function.Injective π) :
    TauCeti.HasNoSmallSubgroups G := by
  let _ : NormedSpace ℝ (V →L[𝕜] V) := NormedSpace.restrictScalars ℝ 𝕜 (V →L[𝕜] V)
  have : NormSMulClass ℤ (V →L[𝕜] V) :=
    ⟨fun n a ↦ by simpa only [Int.norm_cast_real] using norm_zsmul ℝ n a⟩
  refine TauCeti.HasNoSmallSubgroups.of_forall_pow_mem
    ⟨(fun g ↦ ‖π g - 1‖) ⁻¹' Set.Iio (1 / 2), ?_, fun g hg ↦ ?_⟩
  · have hcont : ContinuousAt (fun g ↦ ‖π g - 1‖) 1 :=
      continuous_norm.continuousAt.comp (hπ_cont.sub continuousAt_const)
    exact hcont.preimage_mem_nhds (by simpa using Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / 2))
  · refine hπ_inj ?_
    rw [map_one]
    refine TauCeti.eq_one_of_forall_norm_pow_sub_one_le one_half_lt_one fun n ↦ ?_
    have hn : ‖π (g ^ n) - 1‖ < 1 / 2 := hg n
    rw [map_pow] at hn
    exact hn.le

/-- **A representation of a profinite group on a normed space is continuous if and only if its
kernel is open**, for the operator-norm topology on `V →L[𝕜] V` and a nontrivially normed field
`𝕜` that is a normed `ℝ`-algebra, such as `ℝ` or `ℂ`. A continuous representation kills every
subgroup in a small enough neighbourhood of `1`, since `(V →L[𝕜] V)ˣ` has no small subgroups, and a
profinite group has an open subgroup in every neighbourhood of `1`. Conversely, a homomorphism with
open kernel is locally constant. Over a nonarchimedean field such as `ℚ_p` the forward direction
fails: `ℤ_p` acts continuously on `ℚ_p` by `a ↦ (1 + p) ^ a`, with trivial kernel. -/
theorem continuous_iff_isOpen_ker [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (π : ContRepresentation 𝕜 G V) :
    Continuous π ↔ IsOpen (π.toMonoidHom.ker : Set G) := by
  refine ⟨fun hπ ↦ ?_, π.toMonoidHom.continuous_of_isOpen_ker⟩
  let _ : NormedSpace ℝ (V →L[𝕜] V) := NormedSpace.restrictScalars ℝ 𝕜 (V →L[𝕜] V)
  have : NormSMulClass ℤ (V →L[𝕜] V) :=
    ⟨fun n a ↦ by simpa only [Int.norm_cast_real] using norm_zsmul ℝ n a⟩
  rw [← MonoidHom.ker_toHomUnits]
  exact (π.toUnitsContinuousMonoidHom hπ).isOpen_ker_of_compactSpace_of_totallyDisconnectedSpace

end NormedSpace

end ContRepresentation
