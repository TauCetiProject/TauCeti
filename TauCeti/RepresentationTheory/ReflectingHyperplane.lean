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
Each hyperplane admits a nonzero defining linear form. For a faithful representation, its
pointwise stabilizer consists of the identity and precisely the pseudoreflections with that
fixed space. Thus counting reflections by hyperplanes assigns multiplicity `e_H - 1`, where
`e_H` is the order of the pointwise stabilizer.

These multiplicities are the exponents of the hyperplane factors in the invariant Jacobian.
No nonmodular hypothesis is needed for this counting statement.

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

/-- In a faithful representation, a nonidentity element fixing a reflecting hyperplane
pointwise has that hyperplane as its entire fixed space. -/
theorem fixedSubmodule_eq_of_mem_reflectingHyperplanes (hρ : Function.Injective ρ)
    {H : Submodule K V} (hH : H ∈ ρ.reflectingHyperplanes) {g : G}
    (hg : g ≠ 1) (hfix : H ≤ (ρ g).fixedSubmodule) : (ρ g).fixedSubmodule = H := by
  obtain ⟨ℓ, hℓ, hker⟩ := ρ.exists_dual_ker_eq_of_mem_reflectingHyperplanes hH
  have hcoatom := LinearMap.isCoatom_ker_of_surjective
    (ℓ.surjective_or_eq_zero.resolve_right hℓ)
  have htop : (ρ g).fixedSubmodule ≠ ⊤ := by
    intro h
    have hρg := LinearMap.fixedSubmodule_eq_top_iff.1 h
    exact hg (hρ (hρg.trans (map_one ρ).symm))
  exact ((hcoatom.le_iff.1 (hker ▸ hfix)).resolve_left htop).trans hker

/-- The nonidentity elements fixing a reflecting hyperplane pointwise are exactly the
pseudoreflections with that fixed hyperplane. This includes modular representations. -/
theorem le_fixedSubmodule_iff_of_mem_reflectingHyperplanes (hρ : Function.Injective ρ)
    {H : Submodule K V} (hH : H ∈ ρ.reflectingHyperplanes) (g : G) :
    H ≤ (ρ g).fixedSubmodule ↔ g = 1 ∨ (ρ g).fixedSubmodule = H := by
  by_cases hg : g = 1
  · subst g
    exact iff_of_true (fun x _ ↦ by simp) (Or.inl rfl)
  · simp only [hg, false_or]
    exact ⟨ρ.fixedSubmodule_eq_of_mem_reflectingHyperplanes hρ hH hg, fun h ↦ h ▸ le_rfl⟩

end Representation
