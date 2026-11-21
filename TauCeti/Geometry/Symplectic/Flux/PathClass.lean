/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.PathClass
public import TauCeti.Geometry.Symplectic.Flux.Endpoint

/-!
# The flux homomorphism on path classes of symplectic isotopies

Let `σ` be a closed two-form on a manifold `M`, for instance a symplectic form, and let
`G_σ = TauCeti.SmoothForm.diffeomorphStabilizer σ` be the group of diffeomorphisms preserving it.
The **path classes** of `σ` (`TauCeti.Diffeotopy.PathClass G_σ`) are the diffeotopies `φ_t`
preserving `σ` at every time, modulo homotopy fixing both time ends through diffeomorphisms
preserving `σ`, with the pointwise product `(φ ψ)_t = φ_t ∘ ψ_t`. This file shows that the flux
`Flux(φ) ∈ H¹_dR(M)` of a path (`TauCeti.Diffeotopy.flux`) descends to a group homomorphism

`TauCeti.pathClassFlux σ : PathClass G_σ → H¹_dR(M)`,

written multiplicatively (`TauCeti.pathClassFlux_mk`). It is a homomorphism because the flux is
additive on pointwise composites (`TauCeti.Diffeotopy.flux_trans`), and it is well defined
because the flux is invariant under homotopy fixing both time ends
(`TauCeti.Diffeotopy.Homotopic.flux_eq`), in particular under homotopy through `G_σ`.

The final diffeomorphisms of the path classes are exactly the isotopy stabilizer of `σ`
(`TauCeti.range_pathClass_final`), and the flux group `Γ_σ` is the image under the flux of the
classes of loops, those with final diffeomorphism the identity
(`TauCeti.mem_fluxGroup_iff_exists_pathClass`). The endpoint flux
`G_σ-isotopies → H¹_dR(M) / Γ_σ` (`TauCeti.endpointFlux`) factors through the path classes: the
endpoint flux of the final diffeomorphism of a class is the class of its flux modulo `Γ_σ`
(`TauCeti.endpointFlux_pathClass_final`).

## Main definitions

* `TauCeti.pathClassFlux σ`: the flux homomorphism on the path classes of `σ`.

## Main results

* `TauCeti.pathClassFlux_mk`: the flux of the class of a path is the flux of the path.
* `TauCeti.range_pathClass_final`: the final diffeomorphisms of the path classes form the isotopy
  stabilizer of `σ`.
* `TauCeti.Diffeotopy.PathClass.final_mem_isotopyStabilizer`: the final diffeomorphism of a path
  class lies in the isotopy stabilizer of `σ`.
* `TauCeti.mem_fluxGroup_iff_exists_pathClass`: the flux group is the flux image of the loop
  classes.
* `TauCeti.endpointFlux_pathClass_final`: the endpoint flux factors through the path classes.

## References

* Dusa McDuff and Dietmar Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford
  University Press, 2017, Section 10.2 (the flux homomorphism on the universal cover of the
  identity component of the symplectomorphism group).
* Augustin Banyaga, *The Structure of Classical Diffeomorphism Groups*, Kluwer, 1997,
  Chapter 3.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

open SmoothForm Diffeotopy

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

variable (σ : closedForms J M 2)

/-- The flux of a diffeotopy preserving `σ` at every time, as a homomorphism from the group of
such diffeotopies under the pointwise product, written multiplicatively. -/
private def sliceFlux :
    sliceSubgroup (diffeomorphStabilizer σ.val) →* Multiplicative (deRhamCohomology J M 1) where
  toFun Φ := Multiplicative.ofAdd ((Φ : Diffeotopy J ∞ M).flux σ
    (final_mem_of_mem_sliceSubgroup Φ.property))
  map_one' := by
    simp only [OneMemClass.coe_one, one_def]
    rw [flux_refl, ofAdd_zero]
  map_mul' Φ Ψ := by
    simp only [MulMemClass.coe_mul, mul_def]
    rw [flux_trans (Ψ : Diffeotopy J ∞ M) Φ σ (final_mem_of_mem_sliceSubgroup Ψ.property)
      (final_mem_of_mem_sliceSubgroup Φ.property), ofAdd_add, mul_comm]

/-- The **flux homomorphism on path classes** of a closed two-form `σ`: the flux of a diffeotopy
preserving `σ` at every time depends only on its class modulo homotopy through diffeomorphisms
preserving `σ`, and is additive for the pointwise product. It is written multiplicatively. -/
def pathClassFlux :
    PathClass (diffeomorphStabilizer σ.val) le_rfl →* Multiplicative (deRhamCohomology J M 1) :=
  (homotopicWithCon _ le_rfl).lift (sliceFlux σ) fun Φ Ψ h ↦ (Con.ker_rel _).2
    (congrArg Multiplicative.ofAdd
      (((homotopicWithCon_apply _ _ _).1 h).homotopic.flux_eq σ
        (final_mem_of_mem_sliceSubgroup Φ.property) (final_mem_of_mem_sliceSubgroup Ψ.property)))

variable {σ}

/-- **The flux of the class of a path is the flux of the path.** -/
@[simp]
theorem pathClassFlux_mk (Φ : sliceSubgroup (diffeomorphStabilizer σ.val)) :
    pathClassFlux σ (PathClass.mk _ le_rfl Φ) =
      Multiplicative.ofAdd ((Φ : Diffeotopy J ∞ M).flux σ
        (final_mem_of_mem_sliceSubgroup Φ.property)) := by
  rw [PathClass.mk_def]
  exact Con.lift_mk' _ _

/-- **The final diffeomorphisms of the path classes** of `σ` form the isotopy stabilizer of `σ`:
the final diffeomorphisms of the diffeotopies preserving `σ` at every time. -/
theorem range_pathClass_final :
    (PathClass.final (diffeomorphStabilizer σ.val) le_rfl).range = isotopyStabilizer σ.val := by
  rw [PathClass.range_final]
  ext φ
  simp only [Subgroup.mem_map, mem_sliceSubgroup, finalHom_apply, mem_isotopyStabilizer]

/-- The final diffeomorphism of a path class of `σ` lies in the isotopy stabilizer of `σ`. -/
theorem Diffeotopy.PathClass.final_mem_isotopyStabilizer
    (γ : PathClass (diffeomorphStabilizer σ.val) le_rfl) :
    PathClass.final _ _ γ ∈ isotopyStabilizer σ.val :=
  (range_pathClass_final (σ := σ)) ▸ ⟨γ, rfl⟩

/-- **The flux group is the flux image of the loop classes.** A class lies in the flux group of `σ`
exactly when it is the flux of a path class of `σ` whose final diffeomorphism is the identity. -/
theorem mem_fluxGroup_iff_exists_pathClass {c : deRhamCohomology J M 1} :
    c ∈ fluxGroup σ ↔ ∃ γ : PathClass (diffeomorphStabilizer σ.val) le_rfl,
      PathClass.final _ _ γ = 1 ∧ pathClassFlux σ γ = Multiplicative.ofAdd c := by
  rw [mem_fluxGroup]
  constructor
  · rintro ⟨Φ, hΦ, h₁, rfl⟩
    exact ⟨PathClass.mk _ le_rfl ⟨Φ, mem_sliceSubgroup.2 hΦ⟩, by rw [PathClass.final_mk, h₁],
      pathClassFlux_mk _⟩
  · rintro ⟨γ, h₁, hc⟩
    obtain ⟨Φ, rfl⟩ := PathClass.mk_surjective γ
    rw [PathClass.final_mk] at h₁
    rw [pathClassFlux_mk] at hc
    exact ⟨Φ, mem_sliceSubgroup.1 Φ.property, h₁, Multiplicative.ofAdd.injective hc⟩

/-- **The endpoint flux factors through the path classes.** The endpoint flux of the final
diffeomorphism of a path class of `σ` is the class modulo the flux group of the flux of the path
class. -/
theorem endpointFlux_pathClass_final (γ : PathClass (diffeomorphStabilizer σ.val) le_rfl) :
    endpointFlux σ ⟨PathClass.final _ _ γ, γ.final_mem_isotopyStabilizer⟩ =
      Multiplicative.ofAdd ((pathClassFlux σ γ).toAdd :
        deRhamCohomology J M 1 ⧸ fluxGroup σ) := by
  obtain ⟨Φ, rfl⟩ := PathClass.mk_surjective γ
  rw [pathClassFlux_mk, toAdd_ofAdd]
  exact endpointFlux_apply _ (mem_sliceSubgroup.1 Φ.property) (PathClass.final_mk Φ).symm

end TauCeti
