/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.StrongUnitary.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import TauCeti.Analysis.InnerProductSpace.Continuous

/-!
# Strongly continuous unitary representations

A unitary representation `π` of a topological monoid is *strongly continuous* when every orbit
`g ↦ π g v` is continuous. Since every operator `π g` is an isometry, the family of operators is
uniformly Lipschitz, so strong continuity upgrades to joint continuity of the action map
`(g, v) ↦ π g v`. Moreover, by `TauCeti.tendsto_of_tendsto_inner_of_norm_eq`, strong continuity of a
unitary monoid representation is equivalent to weak continuity of all its matrix coefficients
`g ↦ ⟪v, π g w⟫_𝕜`, without assuming completeness of the representation space. For a group, orbits
through inverses `g ↦ π g⁻¹ v` are continuous as well, without assuming that inversion is continuous
on the group: the distance `‖π g⁻¹ v - π h⁻¹ v‖` equals `‖π g (π h⁻¹ v) - v‖`.

When the representation space `V` is complete, monoid homomorphisms `G →* TauCeti.StrongUnitary 𝕜 V`
yield unitary representations (`TauCeti.StrongUnitary.toContRepresentation`), and for a group `G`
this is mutually inverse to `ContRepresentation.IsUnitary.toStrongUnitaryHom`, matching strong
continuity of `π` with continuity into `StrongUnitary 𝕜 V`.

## Main declarations

* `ContRepresentation.IsUnitary.continuous_apply_prod`,
  `ContRepresentation.IsUnitary.continuous_inv_apply`, and
  `ContRepresentation.IsUnitary.continuous_apply_iff_continuous_inner`: joint continuity, continuity
  through inverses, and equivalence of strong continuity with continuity of matrix coefficients.
* `TauCeti.StrongUnitary.toContRepresentation` and
  `ContRepresentation.IsUnitary.toStrongUnitaryHom`: correspondence between homomorphisms into
  `StrongUnitary 𝕜 V` and unitary representations on a complete inner product space, with
  `ContRepresentation.IsUnitary.continuous_toStrongUnitaryHom_iff`.
-/

public noncomputable section

open scoped InnerProductSpace

namespace TauCeti.StrongUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- View a monoid homomorphism into `StrongUnitary 𝕜 V` as a `ContRepresentation 𝕜 G V`. -/
def toContRepresentation (φ : G →* StrongUnitary 𝕜 V) : ContRepresentation 𝕜 G V :=
  ContRepresentation.ofMonoidHom (toCLMMonoidHom.comp φ)

@[simp]
theorem toContRepresentation_apply (φ : G →* StrongUnitary 𝕜 V) (g : G) :
    toContRepresentation φ g = (φ g).toCLM :=
  toCLMMonoidHom_apply (φ g)

theorem toContRepresentation_apply_apply (φ : G →* StrongUnitary 𝕜 V) (g : G) (v : V) :
    toContRepresentation φ g v = φ g v := by
  rw [toContRepresentation_apply, toCLM_apply]

/-- Every monoid homomorphism into `StrongUnitary 𝕜 V` defines a unitary representation. -/
theorem isUnitary_toContRepresentation (φ : G →* StrongUnitary 𝕜 V) :
    (toContRepresentation φ).IsUnitary :=
  (ContRepresentation.isUnitary_iff_norm_map _).2 fun g v => by
    rw [toContRepresentation_apply_apply, SemilinearIsometryClass.norm_map]

end TauCeti.StrongUnitary

namespace ContRepresentation.IsUnitary

section Topological

variable {𝕜 G V : Type*} [RCLike 𝕜] [TopologicalSpace G] [NormedAddCommGroup V]
  [InnerProductSpace 𝕜 V]

/-- A strongly continuous unitary representation is jointly continuous. -/
theorem continuous_apply_prod [Monoid G] {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π)
    (hcont : ∀ v, Continuous fun g => π g v) : Continuous fun p : G × V => π p.1 p.2 :=
  continuous_prod_of_continuous_lipschitzWith' _ 1 (fun g => (hπ.isometry g).lipschitzWith) hcont

/-- Orbits of a strongly continuous unitary group representation through inverses are
continuous. Continuity of inversion in `G` is not needed. -/
theorem continuous_inv_apply [Group G] {π : ContRepresentation 𝕜 G V} (hπ : IsUnitary π)
    (hcont : ∀ v, Continuous fun g => π g v) (v : V) : Continuous fun g => π g⁻¹ v := by
  refine continuous_iff_continuousAt.2 fun h => ?_
  have hdist (g : G) : dist (π g⁻¹ v) (π h⁻¹ v) = dist (π g (π h⁻¹ v)) v := by
    rw [← (hπ.isometry g).dist_eq, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one,
      one_apply_eq_self, dist_comm]
  have hlim : Filter.Tendsto (fun g => π g (π h⁻¹ v)) (nhds h) (nhds v) := by
    simpa [← mul_apply_eq_comp, ← map_mul] using (hcont (π h⁻¹ v)).tendsto h
  rw [tendsto_iff_dist_tendsto_zero] at hlim
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simpa only [hdist] using hlim

/-- A unitary monoid representation is strongly continuous if and only if all of its matrix
coefficients `g ↦ ⟪v, π g w⟫_𝕜` are continuous. Completeness of `V` is not needed. -/
theorem continuous_apply_iff_continuous_inner [Monoid G] {π : ContRepresentation 𝕜 G V}
    (hπ : IsUnitary π) :
    (∀ v, Continuous fun g => π g v) ↔ ∀ v w, Continuous fun g => ⟪v, π g w⟫_𝕜 :=
  ⟨fun hc v w => continuous_const.inner (hc w), fun hc w =>
    continuous_iff_continuousAt.2 fun g₀ =>
      TauCeti.tendsto_of_tendsto_inner_of_norm_eq
        (Filter.Eventually.of_forall fun g => by rw [hπ.norm_map, hπ.norm_map])
        ((hc (π g₀ w) w).tendsto g₀)⟩

end Topological

section StrongUnitary

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V] {π : ContRepresentation 𝕜 G V}

/-- Bundle a unitary group representation `π` as a group homomorphism `G →* StrongUnitary 𝕜 V`. -/
def toStrongUnitaryHom (hπ : π.IsUnitary) : G →* TauCeti.StrongUnitary 𝕜 V where
  toFun g := .ofUnitary ⟨π g, hπ.mem_unitary g⟩
  map_one' := TauCeti.StrongUnitary.toUnitary_injective <| Subtype.ext (map_one π)
  map_mul' g₁ g₂ := TauCeti.StrongUnitary.toUnitary_injective <| Subtype.ext (map_mul π g₁ g₂)

@[simp]
theorem toCLM_toStrongUnitaryHom (hπ : π.IsUnitary) (g : G) :
    (hπ.toStrongUnitaryHom g).toCLM = π g := by
  simp [toStrongUnitaryHom]

@[simp]
theorem toStrongUnitaryHom_apply (hπ : π.IsUnitary) (g : G) (v : V) :
    hπ.toStrongUnitaryHom g v = π g v := by
  simp [toStrongUnitaryHom]

@[simp]
theorem toContRepresentation_toStrongUnitaryHom (hπ : π.IsUnitary) :
    TauCeti.StrongUnitary.toContRepresentation hπ.toStrongUnitaryHom = π := by
  apply DFunLike.ext
  intro g
  simp

@[simp]
theorem toStrongUnitaryHom_toContRepresentation (φ : G →* TauCeti.StrongUnitary 𝕜 V) :
    (TauCeti.StrongUnitary.isUnitary_toContRepresentation φ).toStrongUnitaryHom = φ := by
  ext g v
  simp

/-- Continuity of `hπ.toStrongUnitaryHom` into `StrongUnitary 𝕜 V` is strong continuity of `π`. -/
theorem continuous_toStrongUnitaryHom_iff [TopologicalSpace G] (hπ : π.IsUnitary) :
    Continuous hπ.toStrongUnitaryHom ↔ ∀ v, Continuous fun g => π g v := by
  simp_rw [TauCeti.StrongUnitary.continuous_iff_forall_continuous, hπ.toStrongUnitaryHom_apply]

end StrongUnitary

end ContRepresentation.IsUnitary
