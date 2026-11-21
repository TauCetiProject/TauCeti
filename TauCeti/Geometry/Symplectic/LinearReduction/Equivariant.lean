/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Invariants
public import TauCeti.Geometry.Symplectic.LinearReduction
public import TauCeti.RepresentationTheory.Subrepresentation.Quotient
public import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Equivariant sections of a linear symplectic reduction

Let a group `G` act on a real symplectic vector space `(V, ω)` by linear symplectomorphisms `ρ`
preserving a subspace `U`. Then `G` acts on the reduced space `U ⧸ (U ∩ U^ω)` by `[u] ↦ [ρ g u]`
(`TauCeti.SymplecticForm.reducedSpaceRepresentation`). When `ρ` is semisimple, as for a continuous
finite-dimensional representation of a compact group, the quotient map `U → U ⧸ (U ∩ U^ω)` has a
`G`-equivariant linear section
(`TauCeti.SymplecticForm.exists_equivariant_section_reducedSpace`): the kernel `U ∩ U^ω` is
invariant, so it has an invariant complement in `U`, which the quotient map identifies with the
reduced space.

Such a section lifts the symplectic slice of an orbit equivariantly into the tangent space, as in
the equivariant linear normal form of a Hamiltonian action.

## Main results

* `TauCeti.SymplecticForm.exists_equivariant_section_reducedSpace`: a semisimple symplectic
  representation preserving `U` admits an equivariant linear section of the reduced space of `U`.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-- A semisimple action of `G` on `V` by symplectomorphisms preserving `U` admits a `G`-equivariant
linear section `s` of the quotient map from `U` onto the reduced space `U ⧸ (U ∩ U^ω)`. -/
theorem exists_equivariant_section_reducedSpace {G : Type*} [Group G] {ρ : G →* V ≃ₗ[ℝ] V}
    [Representation.IsSemisimpleRepresentation
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ : Representation ℝ G V)]
    (hρ : ∀ g, IsSymplectomorphism ω ω (ρ g)) (U : Submodule ℝ V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    ∃ s : ω.ReducedSpace U →ₗ[ℝ] U, (∀ v, Submodule.Quotient.mk (s v) = v) ∧
      ∀ g v, (s (ω.reducedSpaceRepresentation ρ hρ U hU g v) : V) = ρ g (s v) := by
  let ρR : Representation ℝ G V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  have hρR (g : G) (v : V) : ρR g v = ρ g v :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_comp_apply ρ g v
  let Uₛ : Subrepresentation ρR := ⟨U, fun g u hu ↦ by rw [hρR]; exact hU g u hu⟩
  have hUₛ (g : G) (u : U) : (Uₛ.toRepresentation g u : V) = ρ g u :=
    (Subrepresentation.coe_toRepresentation_apply Uₛ g u).trans (hρR g u)
  have : Uₛ.toRepresentation.IsSemisimpleRepresentation :=
    (U.subtype.intertwiningMap_of_isIntertwiningMap Uₛ.toRepresentation ρR fun g u ↦ by
      simp only [Submodule.subtype_apply, hUₛ, hρR]).isSemisimpleRepresentation_of_injective
        Subtype.val_injective
  -- The kernel `U ∩ U^ω` of the restriction of `ω` is invariant, so it has an invariant
  -- complement `C`, and `s` is the identification of the quotient with `C`.
  let Kₛ : Subrepresentation Uₛ.toRepresentation :=
    ⟨LinearMap.ker (ω.toBilinForm.restrict U), fun g u hu ↦ by
      rw [mem_ker_restrict_iff] at hu ⊢
      exact apply_mem_orthogonal (ρ := ρR) (fun g ↦ (hρ g).apply)
        (fun g _ hv ↦ Uₛ.apply_mem_toSubmodule g hv) g hu⟩
  obtain ⟨C, hC⟩ := exists_isCompl Kₛ
  let e := Subrepresentation.quotientEquivOfIsCompl hC
  refine ⟨C.toSubmodule.subtype ∘ₗ e.toLinearEquiv.toLinearMap, fun v ↦ ?_, fun g v ↦ ?_⟩ <;>
    induction v using Submodule.Quotient.induction_on with
    | H u => ?_
  · refine (Submodule.Quotient.eq _).2 ?_
    rw [← neg_mem_iff, neg_sub]
    exact Subrepresentation.sub_quotientEquivOfIsCompl_apply_mk_mem hC u
  · have hq : ω.reducedSpaceRepresentation ρ hρ U hU g (Submodule.Quotient.mk u) =
        Kₛ.quotient g (Submodule.Quotient.mk u) := by
      rw [reducedSpaceRepresentation_apply_mk]
      exact (Subrepresentation.quotient_apply_mk Kₛ g u).symm
    have he : e.toLinearEquiv (Kₛ.quotient g (Submodule.Quotient.mk u)) =
        C.toRepresentation g (e.toLinearEquiv (Submodule.Quotient.mk u)) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g _
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, LinearEquiv.coe_coe, he]
    simp only [Submodule.subtype_apply, Subrepresentation.coe_toRepresentation_apply, hρR]

end TauCeti.SymplecticForm
