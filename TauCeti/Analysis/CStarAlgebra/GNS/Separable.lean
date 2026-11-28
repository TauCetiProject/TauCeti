/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.CStarAlgebra.Representation.Nondegenerate
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import TauCeti.Algebra.Order.Module.PositiveLinearMap
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
import TauCeti.Analysis.CStarAlgebra.State.Series
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Dimension
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
`ℂ` or `Mₙ(ℂ)`), taking the countable Hilbert sum `NonUnitalStarAlgHom.hilbertSum (fun _ : ℕ => π)`
of a faithful nondegenerate representation on a nonzero separable Hilbert space `H` produces a
faithful nondegenerate representation on the infinite-dimensional separable Hilbert space
`lp (fun _ : ℕ => H) 2`. Transporting along a unitary equivalence with `lp (fun _ : ℕ => ℂ) 2`
(`TauCeti.nonempty_linearIsometryEquiv_lp_nat_iff`) yields a faithful nondegenerate representation
directly on `lp (fun _ : ℕ => ℂ) 2`
(`TauCeti.exists_injective_nondegenerate_representation_lp`), and a faithful unital representation
when `A` is unital (`TauCeti.exists_injective_starAlgHom_lp`).

For a zero algebra (`Subsingleton A`), because `lp (fun _ : ℕ => ℂ) 2` is nontrivial
(`lp.instNontrivial`), no representation on it is nondegenerate
(`NonUnitalStarAlgHom.not_isNondegenerate_of_subsingleton_domain`), and no unital representation
into any nontrivial algebra exists (any unital homomorphism forces `1 = 0` in the codomain), so the
nontriviality assumption is sharp.

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
        f.eq_zero_of_faithful_apply_star_mul_self hfaith,
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
      f.eq_zero_of_faithful_apply_star_mul_self hfaith,
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
  obtain ⟨H, _, _, _, _, π, hinj, hnondeg⟩ :=
    exists_injective_nondegenerate_representation_separable A
  have hH : Nontrivial H := not_subsingleton_iff_nontrivial.1 fun h =>
    haveI : Subsingleton H := h
    haveI : Subsingleton A := hinj.subsingleton
    false_of_nontrivial_of_subsingleton A
  let ρ := NonUnitalStarAlgHom.hilbertSum fun _ : ℕ => π
  have hρ_inj : Function.Injective ρ :=
    (NonUnitalStarAlgHom.injective_hilbertSum_iff _).2 fun a ha => hinj (by simpa using ha 0)
  have hρ_nondeg : ρ.IsNondegenerate :=
    (NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun _ => hnondeg
  have : TopologicalSpace.SeparableSpace (lp (fun _ : ℕ => H) 2) := lp.separableSpace (by norm_num)
  have hnotfin : ¬ FiniteDimensional ℂ (lp (fun _ : ℕ => H) 2) := fun _ => by
    obtain ⟨v, hv⟩ := exists_ne (0 : H)
    have hli : LinearIndependent ℂ (fun n : ℕ => lp.single (E := fun _ => H) 2 n v) := by
      refine LinearIndependent.of_comp
        ({ toFun := (⇑), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
          lp (fun _ : ℕ => H) 2 →ₗ[ℂ] (ℕ → H)) ?_
      convert Pi.linearIndependent_single_of_ne_zero (R := ℂ) (M := H) fun _ => hv
      exact lp.coeFn_single (E := fun _ => H) 2 _ v
    exact Module.Finite.not_linearIndependent_of_infinite _ hli
  obtain ⟨U⟩ := (nonempty_linearIsometryEquiv_lp_nat_iff (𝕜 := ℂ)
    (E := lp (fun _ : ℕ => H) 2)).2 ⟨this, hnotfin⟩
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
  exact ⟨hnondeg.toStarAlgHom, by simpa using hinj⟩

end TauCeti
