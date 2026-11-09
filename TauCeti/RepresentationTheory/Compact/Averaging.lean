/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Haar
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Averaging over compact groups

This file bundles integration against normalized Haar measure as a continuous linear map on
continuous vector-valued functions. It records the norm bound, constants, and invariance under left
and right translation needed for averaging representations.

The implementation reuses Mathlib's Bochner integral, its commutation with continuous linear maps,
and the generic left-, right-, and inversion-invariance lemmas for integrals on groups.

Left invariance also makes averaging along a representation equivariant: for a continuous
representation `σ` and a map `c` from a `G`-space, `y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` intertwines
the action with `σ` for any left-invariant measure `μ`
(`ContRepresentation.integral_apply_inv_smul_smul`). This is the Bochner average that linearizes
a compact group action at a fixed point.

The construction is the averaging operator from Layer 0 of the
[compact-groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/roadmap/representation-theory/TauCetiRoadmap/RepresentationTheory/CompactGroups/README.md).
-/

public section

open MeasureTheory

namespace TauCeti

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {V : Type*} [NormedAddCommGroup V]

/-- A continuous vector-valued function on a compact group is Bochner integrable against
normalized Haar measure: it is continuous on the compact set `univ`, which carries finite
measure. -/
theorem integrable_continuousMap (f : C(G, V)) :
    Integrable f (haarProb G) := by
  simpa only [integrableOn_univ] using
    f.continuous.continuousOn.integrableOn_compact' (μ := haarProb G) isCompact_univ
      MeasurableSet.univ

section NormedFieldScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
  [SMulCommClass ℝ 𝕜 V]

/-- Averaging a continuous vector-valued function against normalized Haar measure, as a
continuous linear map.

`V` is not assumed complete, so this is the Bochner integral's junk value `0` unless it is: the
definition and its linear structure need no completeness, and the lemmas below that talk about the
average's actual value (`haarAverage_const`, `norm_haarAverage_eq_one`, and everything reached
through `haarAverage_comp_comm`) ask for `[CompleteSpace V]` precisely because they do. -/
noncomputable def haarAverage : C(G, V) →L[𝕜] V :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ g, f g ∂haarProb G
      map_add' := fun f h ↦ integral_add
        (integrable_continuousMap G f) (integrable_continuousMap G h)
      map_smul' := fun c f ↦ integral_smul c f }
    1 fun f ↦ by
      rw [one_mul]
      simpa using norm_integral_le_of_norm_le_const
        (μ := haarProb G) (Filter.Eventually.of_forall f.norm_coe_le_norm)

/-- The Haar average is the Bochner integral against normalized Haar measure.

Not a `simp` lemma: `haarAverage` is the normal form here, so that the constant, translation
and inversion lemmas below can be `simp` lemmas. Unfold explicitly with `rw`/`simp` when the
underlying integral is wanted. -/
theorem haarAverage_apply (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) f = ∫ g, f g ∂haarProb G :=
  (rfl)

/-- The operator norm of Haar averaging is at most one. -/
theorem norm_haarAverage_le_one :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Haar averaging is norm-nonincreasing for the uniform norm on continuous maps. -/
theorem norm_haarAverage_apply_le (f : C(G, V)) :
    ‖haarAverage G (𝕜 := 𝕜) f‖ ≤ ‖f‖ := by
  simpa using (haarAverage G (𝕜 := 𝕜) (V := V)).le_of_opNorm_le (norm_haarAverage_le_one G) f

/-- The Haar average of a constant function is that constant. -/
@[simp]
theorem haarAverage_const [CompleteSpace V] (v : V) :
    haarAverage G (𝕜 := 𝕜) (ContinuousMap.const G v) = v := by
  simp [haarAverage_apply]

/-- On a nonzero target, Haar averaging has operator norm one. -/
theorem norm_haarAverage_eq_one [Nontrivial V] [CompleteSpace V] :
    ‖haarAverage G (𝕜 := 𝕜) (V := V)‖ = 1 := by
  apply le_antisymm (norm_haarAverage_le_one G) _
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hnorm : ‖ContinuousMap.const G v‖ = ‖v‖ := by
    rw [← (ContinuousMap.linearIsometryBoundedOfCompact G V 𝕜).norm_map]
    exact BoundedContinuousFunction.norm_const_eq v
  have h := (haarAverage G (𝕜 := 𝕜) (V := V)).ratio_le_opNorm
    (ContinuousMap.const G v)
  simpa [haarAverage_const, hnorm, norm_ne_zero_iff.mpr hv] using h

/-- Haar averaging is unchanged by left translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulLeft (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulLeft g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulLeft]
  exact integral_mul_left_eq_self f g

/-- Haar averaging is unchanged by right translation of the argument. -/
@[simp]
theorem haarAverage_comp_mulRight (f : C(G, V)) (g : G) :
    haarAverage G (𝕜 := 𝕜) (f.comp (ContinuousMap.mulRight g)) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_mulRight]
  exact integral_mul_right_eq_self f g

/-- Haar averaging is unchanged by inversion of the argument. -/
@[simp]
theorem haarAverage_comp_inv (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) (f.comp (Homeomorph.inv G : C(G, G))) =
      haarAverage G (𝕜 := 𝕜) f := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass, Homeomorph.coe_inv]
  exact integral_inv_eq_self f (haarProb G)

end NormedFieldScalars

section RCLikeScalars

variable {𝕜 : Type*} [RCLike 𝕜] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

/-- Continuous linear maps commute with Haar averaging.

The scalars are assumed to be `RCLike` because Mathlib states
`ContinuousLinearMap.integral_comp_comm` under that hypothesis. -/
@[simp]
theorem _root_.ContinuousLinearMap.haarAverage_comp_comm {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedSpace 𝕜 W] [SMulCommClass ℝ 𝕜 W] [CompleteSpace V] [CompleteSpace W]
    (L : V →L[𝕜] W) (f : C(G, V)) :
    haarAverage G (𝕜 := 𝕜) ((L : C(V, W)).comp f) = L (haarAverage G (𝕜 := 𝕜) f) := by
  simp only [haarAverage_apply, ContinuousMap.coe_comp, Function.comp_apply,
    ContinuousMap.coe_ofClass]
  exact L.integral_comp_comm (integrable_continuousMap G f)

end RCLikeScalars

end CompactGroup

end TauCeti

namespace ContRepresentation

/-- **Equivariance of the integral Bochner average.** For a left-invariant measure `μ` on `G`, a
continuous representation `σ` and any map `c : X → F` from a `G`-space, the average
`y ↦ ∫ g, σ g (c (g⁻¹ • y)) ∂μ` intertwines the action on `X` with `σ`. -/
theorem integral_apply_inv_smul_smul {G X F : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [MulAction G X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (σ : ContRepresentation ℝ G F) (c : X → F) (h : G)
    (y : X) : ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := by
  have hσ (a b : G) (hab : a * b = 1) (v : F) : σ a (σ b v) = v := by
    rw [← mul_apply_eq_comp, ← map_mul, hab, map_one, one_apply_eq_self]
  let L : F ≃L[ℝ] F := ContinuousLinearEquiv.equivOfInverse (σ h) (σ h⁻¹)
    (hσ _ _ (inv_mul_cancel h)) (hσ _ _ (mul_inv_cancel h))
  calc ∫ g, σ g (c (g⁻¹ • h • y)) ∂μ = ∫ g, σ (h * g) (c ((h * g)⁻¹ • h • y)) ∂μ :=
        (integral_mul_left_eq_self (fun g ↦ σ g (c (g⁻¹ • h • y))) h).symm
    _ = ∫ g, L (σ g (c (g⁻¹ • y))) ∂μ := by
        congr 1
        ext g
        simp [L, mul_inv_rev, mul_smul, map_mul]
    _ = σ h (∫ g, σ g (c (g⁻¹ • y)) ∂μ) := L.integral_comp_comm _

end ContRepresentation
