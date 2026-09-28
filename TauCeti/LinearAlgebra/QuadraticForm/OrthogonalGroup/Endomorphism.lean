/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup

/-!
# Orthogonal endomorphisms of nondegenerate quadratic spaces

An endomorphism of a finite-dimensional nondegenerate quadratic space that preserves the
quadratic form is automatically invertible. This identifies the orthogonal group with the
form-preserving endomorphisms, a useful description when the latter are studied as a subset of
the endomorphism space.

## References

O. T. O'Meara, *Introduction to Quadratic Forms*, §43.
-/

public section

namespace TauCeti

namespace QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Invertible (2 : K)]

/-- For a nondegenerate form, an endomorphism preserves the form exactly when it is the
underlying map of an orthogonal automorphism. -/
theorem range_orthogonalGroup_toLinearMap (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Set.range (fun g : orthogonalGroup Q => (g : V ≃ₗ[K] V).toLinearMap) =
      {f : Module.End K V | ∀ x : V, Q (f x) = Q x} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩ x
    exact mem_orthogonalGroup_iff.mp g.2 x
  · intro hf
    have hpres : ∀ x : V, Q (f x) = Q x := by
      simpa only [Set.mem_ofPred_eq] using hf
    have hpolar (x y : V) : Q.polarBilin (f x) (f y) = Q.polarBilin x y := by
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hpres]
    have hinj : Function.Injective f :=
      BilinForm.IsIsometry.injective ((QuadraticMap.nondegenerate_polar_iff).mpr hQ).1
        ((BilinForm.isIsometry_iff).mpr hpolar)
    let e : V ≃ₗ[K] V := LinearEquiv.ofBijective f
      ⟨hinj, LinearMap.surjective_of_injective hinj⟩
    refine ⟨⟨e, ?_⟩, ?_⟩
    · apply mem_orthogonalGroup_iff.mpr
      intro x
      simpa [e, LinearEquiv.ofBijective] using hpres x
    · exact LinearMap.ext fun x => rfl

end QuadraticMap

end TauCeti
