/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Pseudoreflection
public import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# The reflecting hyperplanes of a finite linear group

The reflecting hyperplanes are the distinct fixed spaces of pseudoreflections, not a list
indexed by pseudoreflections: several complex pseudoreflections can fix the same hyperplane.
Each hyperplane admits a nonzero defining linear form. An element fixing a reflecting
hyperplane pointwise either acts trivially or has precisely that fixed space. For a faithful
representation, its pointwise stabilizer therefore consists of the identity and the
pseudoreflections with that fixed space.

## References

* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- The finite set of distinct fixed hyperplanes of the pseudoreflections of `ρ`. -/
noncomputable def reflectingHyperplanes : Finset (Submodule K V) := by
  classical
  exact (Set.toFinite {g : G | Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1}).toFinset.image
    (fun g ↦ (ρ g).fixedSubmodule)

/-- Membership in the reflecting arrangement means being the fixed space of a
pseudoreflection. -/
@[simp]
theorem mem_reflectingHyperplanes {H : Submodule K V} :
    H ∈ ρ.reflectingHyperplanes ↔
      ∃ g : G, Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1 ∧ (ρ g).fixedSubmodule = H := by
  classical
  simp [reflectingHyperplanes]

/-- The fixed space of a pseudoreflection belongs to the reflecting arrangement. -/
theorem fixedSubmodule_mem_reflectingHyperplanes {g : G}
    (hg : Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1) :
    (ρ g).fixedSubmodule ∈ ρ.reflectingHyperplanes :=
  ρ.mem_reflectingHyperplanes.2 ⟨g, hg, rfl⟩

/-- A reflecting hyperplane has codimension one. -/
theorem finrank_quotient_of_mem_reflectingHyperplanes {H : Submodule K V}
    (hH : H ∈ ρ.reflectingHyperplanes) : Module.finrank K (V ⧸ H) = 1 := by
  obtain ⟨g, hg, rfl⟩ := ρ.mem_reflectingHyperplanes.1 hH
  exact hg

/-- Every reflecting hyperplane is the kernel of a nonzero linear form. -/
theorem exists_dual_ker_eq_of_mem_reflectingHyperplanes {H : Submodule K V}
    (hH : H ∈ ρ.reflectingHyperplanes) :
    ∃ ℓ : Module.Dual K V, ℓ ≠ 0 ∧ LinearMap.ker ℓ = H :=
  H.exists_dual_ker_eq_of_finrank_quotient_eq_one
    (ρ.finrank_quotient_of_mem_reflectingHyperplanes hH)

/-- An element acting nontrivially and fixing a reflecting hyperplane pointwise has that
hyperplane as its entire fixed space. -/
theorem fixedSubmodule_eq_of_mem_reflectingHyperplanes
    {H : Submodule K V} (hH : H ∈ ρ.reflectingHyperplanes) {g : G}
    (hg : ρ g ≠ 1) (hfix : H ≤ (ρ g).fixedSubmodule) : (ρ g).fixedSubmodule = H := by
  obtain ⟨ℓ, hℓ, hker⟩ := ρ.exists_dual_ker_eq_of_mem_reflectingHyperplanes hH
  have hcoatom := LinearMap.isCoatom_ker_of_surjective
    (ℓ.surjective_or_eq_zero.resolve_right hℓ)
  have htop : (ρ g).fixedSubmodule ≠ ⊤ := by
    intro h
    exact hg (LinearMap.fixedSubmodule_eq_top_iff.1 h)
  exact ((hcoatom.le_iff.1 (hker ▸ hfix)).resolve_left htop).trans hker

/-- An element fixes a reflecting hyperplane pointwise exactly when it acts trivially or
has that fixed hyperplane. This includes modular representations. -/
theorem le_fixedSubmodule_iff_of_mem_reflectingHyperplanes
    {H : Submodule K V} (hH : H ∈ ρ.reflectingHyperplanes) (g : G) :
    H ≤ (ρ g).fixedSubmodule ↔ ρ g = 1 ∨ (ρ g).fixedSubmodule = H := by
  by_cases hg : ρ g = 1
  · rw [LinearMap.fixedSubmodule_eq_top_iff.2 hg]
    exact iff_of_true le_top (Or.inl hg)
  · simp only [hg, false_or]
    exact ⟨ρ.fixedSubmodule_eq_of_mem_reflectingHyperplanes hH hg, fun h ↦ h ▸ le_rfl⟩

end Representation
