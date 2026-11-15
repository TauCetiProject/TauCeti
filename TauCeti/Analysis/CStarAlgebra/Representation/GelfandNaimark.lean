/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.Representation.HilbertSum
public import TauCeti.Analysis.CStarAlgebra.State.Space
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.State.Faithful
import TauCeti.Analysis.CStarAlgebra.State.Separation
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Countable
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# The Gelfand–Naimark representation theorem and separable faithful representations

Every C⋆-algebra `A`, possibly nonunital and nonseparable, admits an injective (hence isometric)
nondegenerate `⋆`-representation on a complete complex Hilbert space in the same universe as `A`,
and when `A` is separable and nonzero this representation can be realized on `ℓ²(ℕ, ℂ)`:

* `TauCeti.gnsUniversalHilbertSpace`, `TauCeti.gnsUniversalRepresentation`: the universal GNS
  representation `⊕_{φ ∈ stateSpace A} π_φ` on the `ℓ²`-direct sum of the GNS Hilbert spaces of all
  states of `A`. When `A` is subsingleton, `stateSpace A = ∅` and the carrier is the zero Hilbert
  space.
* `TauCeti.isNondegenerate_gnsUniversalRepresentation`,
  `TauCeti.gnsUniversalRepresentation_injective`,
  `TauCeti.norm_gnsUniversalRepresentation_apply`: the universal GNS representation is
  nondegenerate, injective, and isometric.
* `TauCeti.exists_faithful_nondegenerate_representation`,
  `TauCeti.exists_faithful_starAlgHom_representation`: the Gelfand–Naimark theorem in existential
  form (requiring only `[NonUnitalCStarAlgebra A]`, respectively `[CStarAlgebra B]`).
* `TauCeti.exists_faithful_nondegenerate_representation_separable`: every separable C⋆-algebra `A`
  admits an injective nondegenerate representation on a separable Hilbert space in `A`'s universe.
* `TauCeti.exists_injective_nondegenerate_representation_lp`,
  `TauCeti.exists_injective_starAlgHom_lp`: every nontrivial separable C⋆-algebra admits an
  injective nondegenerate representation on `lp (fun _ : ℕ => ℂ) 2`, obtained by countably
  amplifying the GNS representation of a faithful state and transporting along a Hilbert basis
  indexed by `ℕ`.

## References

* I. Gelfand and M. Naimark, *On the imbedding of normed rings into the ring of operators in
  Hilbert space*, Mat. Sb. 12 (1943), 197–217.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Theorem 3.4.1.
* Jesse Peterson, *Notes on operator algebras*, Theorem 4.1.6 and Corollary 4.1.7.
-/

public section

noncomputable section

open WeakDual
open scoped CStarAlgebra ComplexOrder ENNReal

universe u

namespace TauCeti

section UniversalGNS

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state `φ ∈ stateSpace A` packaged as a `PositiveLinearMap` `A →ₚ[ℂ] ℂ`. -/
def stateToPositiveLinearMap {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) : A →ₚ[ℂ] ℂ :=
  .mk₀ (toStrongDual φ : A →ₗ[ℂ] ℂ) fun _ => map_nonneg_of_mem_stateSpace hφ

@[simp]
theorem stateToPositiveLinearMap_apply {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) (a : A) :
    stateToPositiveLinearMap hφ a = φ a := by
  rfl

/-- The **universal GNS Hilbert space** of a C⋆-algebra `A`: the `ℓ²`-direct sum over all states
`φ ∈ stateSpace A` of their GNS Hilbert spaces. When `A` is subsingleton, `stateSpace A = ∅` and
this is the zero Hilbert space in `Type u`. -/
abbrev gnsUniversalHilbertSpace (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Type u :=
  lp (fun φ : stateSpace A => (stateToPositiveLinearMap φ.2).GNS) 2

/-- The **universal GNS representation** `⊕_{φ ∈ stateSpace A} π_φ` of a C⋆-algebra `A` on
`gnsUniversalHilbertSpace A`. -/
def gnsUniversalRepresentation (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :
    A →⋆ₙₐ[ℂ] (gnsUniversalHilbertSpace A →L[ℂ] gnsUniversalHilbertSpace A) :=
  NonUnitalStarAlgHom.hilbertSum fun φ : stateSpace A =>
    (stateToPositiveLinearMap φ.2).gnsNonUnitalStarAlgHom

@[simp]
theorem gnsUniversalRepresentation_apply_apply (a : A) (x : gnsUniversalHilbertSpace A)
    (φ : stateSpace A) :
    gnsUniversalRepresentation A a x φ =
      (stateToPositiveLinearMap φ.2).gnsNonUnitalStarAlgHom a (x φ) := by
  simp [gnsUniversalRepresentation]

/-- The universal GNS representation is nondegenerate, also when `A` has no unit or is zero. -/
theorem isNondegenerate_gnsUniversalRepresentation :
    (gnsUniversalRepresentation A).IsNondegenerate :=
  (NonUnitalStarAlgHom.isNondegenerate_hilbertSum_iff _).2 fun φ =>
    (stateToPositiveLinearMap φ.2).isNondegenerate_gnsNonUnitalStarAlgHom

/-- **Faithfulness of the universal GNS representation.** The direct sum of GNS representations over
`stateSpace A` is injective. -/
theorem gnsUniversalRepresentation_injective :
    Function.Injective (gnsUniversalRepresentation A) := by
  rw [gnsUniversalRepresentation, NonUnitalStarAlgHom.hilbertSum_injective_iff]
  intro a ha
  by_contra ha0
  have : Nontrivial A := ⟨a, 0, ha0⟩
  let x : A := a * star a
  have hx : 0 ≤ x := mul_star_self_nonneg a
  obtain ⟨φ, hφ, -, hφx2⟩ := exists_mem_stateSpace_apply_mul_self_eq_norm_sq hx
  let f : A →ₚ[ℂ] ℂ := stateToPositiveLinearMap hφ
  have hclass : f.toGNS x = 0 := by
    simpa [f, x, PositiveLinearMap.toGNS_apply] using
      DFunLike.congr_fun (ha ⟨φ, hφ⟩) (f.toGNS (star a))
  have hfx2 : f (star x * x) = 0 := (f.toGNS_eq_zero_iff x).1 hclass
  rw [hx.isSelfAdjoint.star_eq, stateToPositiveLinearMap_apply, hφx2,
    pow_eq_zero_iff two_ne_zero, Complex.ofReal_eq_zero, norm_eq_zero] at hfx2
  exact ha0 (mul_star_self_eq_zero.1 hfx2)

/-- The universal GNS representation is isometric. -/
@[simp]
theorem norm_gnsUniversalRepresentation_apply (a : A) :
    ‖gnsUniversalRepresentation A a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (gnsUniversalRepresentation A)
    (gnsUniversalRepresentation_injective (A := A)) a

end UniversalGNS

/-- **Gelfand–Naimark theorem.** Every (possibly nonunital and nonseparable) C⋆-algebra `A` admits
an injective nondegenerate `⋆`-representation on a complete complex Hilbert space in the same
universe as `A`. -/
theorem exists_faithful_nondegenerate_representation (A : Type u) [NonUnitalCStarAlgebra A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)), Function.Injective π ∧ π.IsNondegenerate := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  exact ⟨gnsUniversalHilbertSpace A, inferInstance, inferInstance, inferInstance,
    gnsUniversalRepresentation A, gnsUniversalRepresentation_injective,
    isNondegenerate_gnsUniversalRepresentation⟩

/-- **Unital Gelfand–Naimark theorem.** Every unital C⋆-algebra `B` admits an injective unital
`⋆`-representation on a complete complex Hilbert space in the same universe as `B`. -/
theorem exists_faithful_starAlgHom_representation (B : Type u) [CStarAlgebra B] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (π : B →⋆ₐ[ℂ] (K →L[ℂ] K)), Function.Injective π := by
  obtain ⟨K, _, _, _, ρ, hρ_inj, hρ_nondeg⟩ := exists_faithful_nondegenerate_representation B
  exact ⟨K, inferInstance, inferInstance, inferInstance, hρ_nondeg.toStarAlgHom,
    hρ_nondeg.coe_toStarAlgHom.symm ▸ hρ_inj⟩

/-- Every separable (possibly nonunital or zero) C⋆-algebra `A` admits an injective nondegenerate
`⋆`-representation on a separable complete complex Hilbert space in `A`'s universe. -/
theorem exists_faithful_nondegenerate_representation_separable (A : Type u)
    [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A] :
    ∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K)
      (_ : TopologicalSpace.SeparableSpace K) (π : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
        Function.Injective π ∧ π.IsNondegenerate := by
  let := _root_.CStarAlgebra.spectralOrder A
  have := _root_.CStarAlgebra.spectralOrderedRing A
  rcases subsingleton_or_nontrivial A with _ | _
  · let f0 : A →ₚ[ℂ] ℂ := { toLinearMap := 0, monotone' := monotone_const }
    exact ⟨f0.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
      f0.gnsNonUnitalStarAlgHom, Function.injective_of_subsingleton _,
      f0.isNondegenerate_gnsNonUnitalStarAlgHom⟩
  · obtain ⟨ψ, -, -, hstar⟩ := CStarAlgebra.exists_faithful_positiveContinuousLinearMap (A := A)
    let f : A →ₚ[ℂ] ℂ := ψ.toPositiveLinearMap
    exact ⟨f.GNS, inferInstance, inferInstance, inferInstance, inferInstance,
      f.gnsNonUnitalStarAlgHom, f.gnsNonUnitalStarAlgHom_injective hstar,
      f.isNondegenerate_gnsNonUnitalStarAlgHom⟩

/-- **Separable faithful representation on `ℓ²(ℕ)`.** Every nontrivial separable (possibly
nonunital) C⋆-algebra `A` admits an injective nondegenerate `⋆`-representation on
`lp (fun _ : ℕ => ℂ) 2`. -/
theorem exists_injective_nondegenerate_representation_lp (A : Type*)
    [NonUnitalCStarAlgebra A] [TopologicalSpace.SeparableSpace A] [Nontrivial A] :
    ∃ π : A →⋆ₙₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      Function.Injective π ∧ π.IsNondegenerate := by
  obtain ⟨K, _, _, _, _, ρ, hρ_inj, hρ_nondeg⟩ :=
    exists_faithful_nondegenerate_representation_separable A
  have : Nontrivial (K →L[ℂ] K) := hρ_inj.nontrivial
  have : Nontrivial K := by
    by_contra hK
    rw [not_nontrivial_iff_subsingleton] at hK
    exact not_subsingleton (K →L[ℂ] K) inferInstance
  let H := lp (fun _ : ℕ => K) 2
  have : TopologicalSpace.SeparableSpace H := lp.separableSpace (by simp)
  have hinf : ¬ Module.Finite ℂ H := lp.not_finite (𝕜 := ℂ)
  obtain ⟨e⟩ := exists_linearIsometryEquiv_lp_nat ℂ H hinf
  let ρ_amp : A →⋆ₙₐ[ℂ] (H →L[ℂ] H) := ρ.ampliation ℕ
  have hamp_inj : Function.Injective ρ_amp := (ρ.ampliation_injective_iff (ι := ℕ)).2 hρ_inj
  have hamp_nondeg : ρ_amp.IsNondegenerate := hρ_nondeg.ampliation
  refine ⟨e.conjStarAlgEquiv.toNonUnitalStarAlgHom.comp ρ_amp,
    e.conjStarAlgEquiv.injective.comp hamp_inj, ?_⟩
  exact (NonUnitalStarAlgHom.isNondegenerate_conjStarAlgEquiv_comp_iff e ρ_amp).2 hamp_nondeg

/-- Every nontrivial separable unital C⋆-algebra `B` admits an injective unital `⋆`-representation
on `lp (fun _ : ℕ => ℂ) 2`. -/
theorem exists_injective_starAlgHom_lp (B : Type*)
    [CStarAlgebra B] [TopologicalSpace.SeparableSpace B] [Nontrivial B] :
    ∃ π : B →⋆ₐ[ℂ] (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2),
      Function.Injective π := by
  obtain ⟨ρ, hρ_inj, hρ_nondeg⟩ := exists_injective_nondegenerate_representation_lp B
  exact ⟨hρ_nondeg.toStarAlgHom, hρ_nondeg.coe_toStarAlgHom.symm ▸ hρ_inj⟩

end TauCeti

end
