/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Basic.Complex.Basic
import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic

/-!
# Examples of the chart topology on scheme-valued points

Checks for the points `X(R)` of a scheme `X` over `Spec k`, the morphisms `Spec R → X` over
`Spec k`:

* the base `Spec k` has exactly one `R`-point over itself;
* the empty scheme has no points over a nonzero ring;
* on the affine line, `r ↦ (t ↦ r)` is a homeomorphism from `R` onto the points;
* complex conjugation induces an endomorphism of `Spec ℂ` that is not a `ℂ`-point of `Spec ℂ`
  over itself;
* on an affine scheme `Spec A`, points are the algebra maps `A →ₐ[k] R`, compatibly with
  composition;
* over a discrete local ring, the points of a scheme locally of finite type form a discrete
  space.
-/

open CategoryTheory AlgebraicGeometry Polynomial Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]

/-- The base `Spec k` has exactly one `R`-point over itself. -/
noncomputable example : Unique (Points (R := R) (𝟙 (Spec (.of k)))) := inferInstance

/-- The empty scheme has no points over a nonzero ring, whose spectrum is nonempty. -/
example [Nontrivial R] (f : (∅ : Scheme.{u}) ⟶ Spec (.of k)) : IsEmpty (Points (R := R) f) :=
  ⟨fun x ↦ isEmptyElim (x.val (Classical.arbitrary (PrimeSpectrum R)))⟩

/-- On the affine line, `r ↦ (t ↦ r)` is a homeomorphism from `R` onto the points. -/
noncomputable example [TopologicalSpace R] [IsTopologicalRing R] :
    R ≃ₜ Points (R := R) (Spec.algebraMap k k[X]) :=
  (PointTopology.polynomialHomeomorph k R).symm.trans (affineHomeomorph k[X])

/-- Complex conjugation induces an endomorphism of `Spec ℂ` that is not a `ℂ`-point of `Spec ℂ`
over itself: the base condition fails, since `Spec.map` is injective and conjugation moves `i`. -/
example : Spec.map (CommRingCat.ofHom (starRingEnd ℂ)) ≫ 𝟙 (Spec (.of ℂ)) ≠
    Spec.algebraMap ℂ ℂ := by
  intro h
  rw [Category.comp_id, Spec.map_inj] at h
  have hI := congrArg (fun φ : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ ↦ φ.hom Complex.I) h
  simp only [CommRingCat.hom_ofHom, Complex.conj_I, Algebra.algebraMap_self, RingHom.id_apply,
    CharZero.neg_eq_self_iff] at hI
  exact Complex.I_ne_zero hI

/-- On an affine scheme, `R`-points are the algebra maps to `R`, for every `k`-algebra `R`. -/
example (A : Type u) [CommRing A] [Algebra k A] :
    Function.Bijective (Spec.homEquivAlgHom.symm :
      (A →ₐ[k] R) → Points (R := R) (Spec.algebraMap k A)) :=
  Spec.homEquivAlgHom.symm.bijective

/-- For `ψ : A → B` and `φ : B → R`, the point `φ ∘ ψ` of `Spec A` is the point `φ` of `Spec B`
followed by `Spec ψ`. -/
example {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (ψ : A →ₐ[k] B)
    (φ : B →ₐ[k] R) (h) :
    map (Spec.map (CommRingCat.ofHom (ψ : A →+* B))) h (Spec.homEquivAlgHom.symm φ) =
      Spec.homEquivAlgHom.symm (φ.comp ψ) :=
  map_homEquivAlgHom_symm ψ φ

/-- Over a discrete local ring, the points of a scheme locally of finite type are discrete: each
affine chart is open, and discrete because its algebra is of finite type. -/
example [TopologicalSpace R] [DiscreteTopology R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] : DiscreteTopology (Points (R := R) f) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦ ?_
  obtain ⟨A, i, hi, _, z, rfl⟩ := exists_mem_range_chartPoint f x
  have : Algebra.FiniteType k A :=
    LocallyOfFiniteType.Spec_algebraMap_iff.mp (hi ▸ inferInstance)
  have := PointTopology.discreteTopology_of_finiteType (k := k) (A := A) (R := R)
  simpa using (isOpenEmbedding_chartPoint (R := R) f A i hi).isOpenMap _ (isOpen_discrete {z})

end TauCeti.SchemePointTopology
