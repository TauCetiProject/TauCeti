/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import TauCeti.Algebra.Star.StarAlgHom
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Analysis.CStarAlgebra.Representation.Ampliation
import TauCeti.Analysis.CStarAlgebra.State.Series
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Lp
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Faithful representations of separable C⋆-algebras on separable Hilbert space and `ℓ²`

Every separable complex C⋆-algebra `A` (possibly nonunital and possibly zero) admits a faithful
nondegenerate `⋆`-representation on a separable complete complex Hilbert space in the same
universe (`TauCeti.exists_injective_nondegenerate_representation_separable`). When `A` is
nontrivial, the carrier is the GNS Hilbert space of a faithful norm-one positive functional
(`TauCeti.CStarAlgebra.exists_faithful_positiveContinuousLinearMap`); when `A` is zero, the zero
Hilbert space provides a faithful nondegenerate representation. For a unital separable C⋆-algebra,
the GNS representation also carries a canonical cyclic vector, of norm one when `A` is nontrivial
(`TauCeti.exists_injective_starAlgHom_cyclic_separable`,
`TauCeti.exists_injective_starAlgHom_unit_cyclic_separable`).

For every nontrivial separable complex C⋆-algebra `A` (including finite-dimensional ones such as
`ℂ` or `Mₙ(ℂ)`), amplifying the nonzero separable GNS carrier onto the countable Hilbert sum
`lp (fun _ : ℕ => ψ.GNS) 2` produces a faithful nondegenerate representation on an
infinite-dimensional separable Hilbert space. Transporting along the coordinate unitary of a
Hilbert basis indexed by `ℕ` (`lp.exists_hilbertBasis_nat`) yields a faithful nondegenerate
representation directly on `lp (fun _ : ℕ => ℂ) 2`
(`TauCeti.exists_injective_nondegenerate_representation_lp`), and a faithful unital representation
when `A` is unital (`TauCeti.exists_injective_starAlgHom_lp`).

For a zero algebra (`Subsingleton A`), no representation on `lp (fun _ : ℕ => ℂ) 2` is
nondegenerate (`TauCeti.not_exists_nondegenerate_representation_lp_of_subsingleton`), and no unital
representation on `lp (fun _ : ℕ => ℂ) 2` exists
(`TauCeti.isEmpty_starAlgHom_lp_of_subsingleton`), so the nontriviality assumption is sharp.

## Main declarations

* `TauCeti.exists_injective_nondegenerate_representation_separable`: faithful nondegenerate
  representation of any separable C⋆-algebra on a separable Hilbert space in the same universe.
* `TauCeti.exists_injective_starAlgHom_unit_cyclic_separable`,
  `TauCeti.exists_injective_starAlgHom_cyclic_separable`: unital faithful separable representations
  with a cyclic vector.
* `TauCeti.exists_injective_nondegenerate_representation_lp`: faithful nondegenerate representation
  of any nontrivial separable C⋆-algebra on `lp (fun _ : ℕ => ℂ) 2`.
* `TauCeti.exists_injective_starAlgHom_lp`: faithful unital representation of any nontrivial
  separable unital C⋆-algebra on `lp (fun _ : ℕ => ℂ) 2`.
* `TauCeti.not_exists_nondegenerate_representation_lp_of_subsingleton`,
  `TauCeti.isEmpty_starAlgHom_lp_of_subsingleton`: sharp obstructions for the zero algebra on `ℓ²`.

## References

* J. Peterson, *Notes on Operator Algebras*, Propositions 4.1.4–4.1.5 and Corollary 4.1.7.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Sections 3.3–3.4.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder ENNReal

universe u

namespace TauCeti

/-- Every separable complex C⋆-algebra `A : Type u` (possibly nonunital and possibly zero) admits
an injective nondegenerate `⋆`-representation on a separable complete complex Hilbert space in
`Type u`. -/
theorem exists_injective_nondegenerate_representation_separable (A : Type u)
    [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      Function.Injective π ∧ π.IsNondegenerate := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  rcases subsingleton_or_nontrivial A with hA | hA
  · let f₀ : A →ₚ[ℂ] ℂ := 0
    exact ⟨f₀.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
      f₀.gnsNonUnitalStarAlgHom, Function.injective_of_subsingleton _,
      f₀.isNondegenerate_gnsNonUnitalStarAlgHom⟩
  · obtain ⟨ψ, -, hfaith⟩ := CStarAlgebra.exists_faithful_positiveContinuousLinearMap (A := A)
    let f : A →ₚ[ℂ] ℂ := ψ.toPositiveLinearMap
    exact ⟨f.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
      f.gnsNonUnitalStarAlgHom,
      f.gnsNonUnitalStarAlgHom_injective fun _ =>
        ψ.eq_zero_of_faithful_apply_star_mul_self hfaith,
      f.isNondegenerate_gnsNonUnitalStarAlgHom⟩

/-- Every nontrivial separable unital complex C⋆-algebra `A : Type u` admits an injective unital
`⋆`-representation on a separable complete complex Hilbert space in `Type u` with a unit cyclic
vector. -/
theorem exists_injective_starAlgHom_unit_cyclic_separable (A : Type u)
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H),
      Function.Injective π ∧ ‖ξ‖ = 1 ∧ DenseRange (fun a : A => π a ξ) := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  obtain ⟨ψ, hψ_norm, hfaith⟩ := CStarAlgebra.exists_faithful_positiveContinuousLinearMap (A := A)
  let f : A →ₚ[ℂ] ℂ := ψ.toPositiveLinearMap
  have hf1 : f 1 = 1 := by
    have h := ψ.ofReal_opNorm_eq_map_one
    rw [hψ_norm, Complex.ofReal_one] at h
    exact h.symm
  exact ⟨f.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
    f.gnsStarAlgHom, f.gnsVector,
    f.gnsNonUnitalStarAlgHom_injective fun _ =>
      ψ.eq_zero_of_faithful_apply_star_mul_self hfaith,
    f.norm_gnsVector hf1, f.denseRange_gnsStarAlgHom_gnsVector⟩

/-- Every separable unital complex C⋆-algebra `A : Type u` (possibly zero) admits an injective
unital `⋆`-representation on a separable complete complex Hilbert space in `Type u` with a cyclic
vector. -/
theorem exists_injective_starAlgHom_cyclic_separable (A : Type u)
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H),
      Function.Injective π ∧ DenseRange (fun a : A => π a ξ) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · let := _root_.CStarAlgebra.spectralOrder A
    have := _root_.CStarAlgebra.spectralOrderedRing A
    let f₀ : A →ₚ[ℂ] ℂ := 0
    exact ⟨f₀.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
      f₀.gnsStarAlgHom, f₀.gnsVector, Function.injective_of_subsingleton _,
      f₀.denseRange_gnsStarAlgHom_gnsVector⟩
  · obtain ⟨H, _, _, _, _, π, ξ, hinj, -, hcyc⟩ :=
      exists_injective_starAlgHom_unit_cyclic_separable A
    exact ⟨H, inferInstance, inferInstance, inferInstance, inferInstance, π, ξ, hinj, hcyc⟩

/-- Every nontrivial separable complex C⋆-algebra (possibly nonunital, including finite-dimensional
ones) admits an injective nondegenerate `⋆`-representation on `lp (fun _ : ℕ => ℂ) 2`. -/
theorem exists_injective_nondegenerate_representation_lp (A : Type*)
    [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ π : A →⋆ₙₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      Function.Injective π ∧ π.IsNondegenerate := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  obtain ⟨ψ, -, hfaith⟩ := CStarAlgebra.exists_faithful_positiveContinuousLinearMap (A := A)
  let f : A →ₚ[ℂ] ℂ := ψ.toPositiveLinearMap
  have hGNS_nontrivial : Nontrivial f.GNS := by
    obtain ⟨a, ha0⟩ := exists_ne (0 : A)
    refine ⟨f.toGNS a, 0, ?_⟩
    rw [ne_eq, f.toGNS_eq_zero_iff]
    exact fun h => ha0 (ψ.eq_zero_of_faithful_apply_star_mul_self hfaith h)
  have hinj : Function.Injective f.gnsNonUnitalStarAlgHom :=
    f.gnsNonUnitalStarAlgHom_injective fun _ =>
      ψ.eq_zero_of_faithful_apply_star_mul_self hfaith
  let ρ := f.gnsNonUnitalStarAlgHom.ampliation ℕ
  have hρ_inj : Function.Injective ρ := (f.gnsNonUnitalStarAlgHom.ampliation_injective_iff ℕ).2 hinj
  have hρ_nondeg : ρ.IsNondegenerate := f.isNondegenerate_gnsNonUnitalStarAlgHom.ampliation ℕ
  obtain ⟨b⟩ := lp.exists_hilbertBasis_nat (ι := ℕ) (𝕜 := ℂ) (E := fun _ => f.GNS)
  let U : lp (fun _ : ℕ => f.GNS) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 := b.repr
  exact ⟨U.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp ρ,
    U.conjStarAlgEquiv.injective.comp hρ_inj,
    (ρ.isNondegenerate_conjStarAlgEquiv_comp_iff U).2 hρ_nondeg⟩

/-- Every nontrivial separable unital complex C⋆-algebra admits an injective unital
`⋆`-representation on `lp (fun _ : ℕ => ℂ) 2`. -/
theorem exists_injective_starAlgHom_lp (A : Type*)
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ π : A →⋆ₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      Function.Injective π := by
  obtain ⟨π, hinj, hnondeg⟩ := exists_injective_nondegenerate_representation_lp A
  exact ⟨π.toStarAlgHom hnondeg.map_one, hinj⟩

/-- No representation of a zero C⋆-algebra on `lp (fun _ : ℕ => ℂ) 2` is nondegenerate. -/
theorem not_exists_nondegenerate_representation_lp_of_subsingleton (A : Type*)
    [NonUnitalCStarAlgebra A] [Subsingleton A] :
    ¬ ∃ π : A →⋆ₙₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      π.IsNondegenerate := by
  rintro ⟨π, hπ⟩
  exact π.not_isNondegenerate_of_subsingleton hπ

/-- A zero unital `⋆`-algebra admits no unital `⋆`-representation on `lp (fun _ : ℕ => ℂ) 2`. -/
theorem isEmpty_starAlgHom_lp_of_subsingleton (A : Type*)
    [Semiring A] [Algebra ℂ A] [Star A] [Subsingleton A] :
    IsEmpty (A →⋆ₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)) := by
  refine ⟨fun π => ?_⟩
  have : Subsingleton (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2) :=
    π.toRingHom.codomain_trivial
  exact false_of_nontrivial_of_subsingleton (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2)

end TauCeti
