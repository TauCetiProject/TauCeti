/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.UnitaryModel
public import TauCeti.RepresentationTheory.Continuous.InvariantComplement
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Complete reducibility for compact groups

A finite-dimensional representation of a compact group over `ℝ` or `ℂ` whose matrix coefficients
are continuous is semisimple: every subrepresentation has an invariant complement. This is
Maschke's theorem with Haar averaging in place of the average over a finite group.

The statement is about a plain `Representation` on a vector space without any chosen topology or
inner product, so that it applies to representations built algebraically, such as the restriction
of a rational representation of `GL n ℂ` to the unitary group. The continuity hypothesis is
stated through linear functionals: `g ↦ f (ρ g v)` is continuous for every vector `v` and every
linear functional `f`.

The proof transports the representation, along a basis, to a continuous representation on the
Euclidean space `EuclideanSpace 𝕜 (Fin d)`. The unitarian trick
(`ContRepresentation.exists_isUnitary_congr`) conjugates that one into a unitary representation,
in which the orthogonal complement of a subrepresentation is invariant
(`ContRepresentation.IsUnitary.isCompl_orthogonalSubrepresentation`); pulling that complement back
along the composite equivalence gives the complement in the original representation.

## Main results

* `Representation.isSemisimpleRepresentation_of_continuous`: a finite-dimensional representation
  of a compact group with continuous matrix coefficients is semisimple.

## References

* D. Bump, *Lie Groups*, second edition, Springer GTM 225 (2013), Chapter 2, Proposition 2.1.
-/

public section

open ContRepresentation

namespace Representation

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]

/-- **Complete reducibility for compact groups.** A finite-dimensional representation of a compact
group whose matrix coefficients `g ↦ f (ρ g v)` are continuous is semisimple: every
subrepresentation has an invariant complement. -/
theorem isSemisimpleRepresentation_of_continuous (ρ : Representation 𝕜 G V)
    (hρ : ∀ (f : Module.Dual 𝕜 V) (v : V), Continuous fun g => f (ρ g v)) :
    ρ.IsSemisimpleRepresentation := by
  borelize G
  let b := Module.finBasis 𝕜 V
  -- Transport `ρ` to a continuous representation on a Euclidean space along the basis `b`.
  let T : V ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V)) :=
    b.equivFun.trans (EuclideanSpace.equiv _ 𝕜).symm.toLinearEquiv
  let π : ContRepresentation 𝕜 G (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 V))) := .ofMonoidHom
    { toFun g := LinearMap.toContinuousLinearMap (T.conj (ρ g))
      map_one' := by ext; simp
      map_mul' g h := by ext; simp }
  have hπT (g : G) (v : V) : π g (T v) = T (ρ g v) :=
    -- `π g` is `T ∘ ρ g ∘ T⁻¹` by definition.
    congrArg (fun w => T (ρ g w)) (T.symm_apply_apply v)
  have hπ : Continuous π := by
    refine continuous_clm_apply.mpr fun y => ?_
    refine (EuclideanSpace.equiv _ 𝕜).symm.continuous.comp (continuous_pi fun i => ?_)
    exact hρ (b.coord i) (T.symm y)
  obtain ⟨e, he⟩ := exists_isUnitary_congr π hπ
  -- The composite equivalence intertwines `ρ` with the unitary model `e.congr π`.
  let T' := T.trans (e : _ ≃L[𝕜] _).toLinearEquiv
  have hT' (g : G) (v : V) : e.congr π g (T' v) = T' (ρ g v) := by
    rw [ContinuousLinearEquiv.congr_apply]
    simp [T', hπT]
  refine ⟨fun p => ?_⟩
  let S : Subrepresentation (e.congr π).toRepresentation :=
    { toSubmodule := p.toSubmodule.map T'
      apply_mem_toSubmodule g := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨ρ g v, p.apply_mem_toSubmodule g hv, ?_⟩
        exact (hT' g v).symm }
  let q : Subrepresentation ρ :=
    { toSubmodule := (he.orthogonalSubrepresentation S).toSubmodule.comap (T' : V →ₗ[𝕜] _)
      apply_mem_toSubmodule g v hv := by
        simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at hv ⊢
        rw [← hT']
        exact (he.orthogonalSubrepresentation S).apply_mem_toSubmodule g hv }
  refine ⟨q, Subrepresentation.isCompl_toSubmodule.mp ?_⟩
  have hc := Subrepresentation.isCompl_toSubmodule.mpr (he.isCompl_orthogonalSubrepresentation S)
  simpa [S, q, Submodule.comap_map_eq_of_injective T'.injective] using
    (Submodule.orderIsoMapComap T').symm.isCompl hc

end Representation
