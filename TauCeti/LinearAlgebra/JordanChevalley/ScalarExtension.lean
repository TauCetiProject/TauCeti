/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.End.ScalarExtension
public import TauCeti.LinearAlgebra.JordanChevalley.Multiplicative

/-!
# Scalar extension of multiplicative Jordan decomposition

Let `R` be a commutative semiring, let `K` and `L` be `R`-algebras that are fields, and let
`f : K →ₐ[R] L`. An automorphism of `K ⊗[R] V` extends canonically to an automorphism of
`L ⊗[R] V`. If `K` is perfect, scalar extension preserves semisimplicity: the squarefree
minimal polynomial of the original endomorphism maps to a squarefree annihilating polynomial over
`L`. Scalar extension also preserves unipotence directly, so uniqueness of the multiplicative
Jordan–Chevalley decomposition identifies the extended factors.

## Main declarations

* `LinearMap.GeneralLinearGroup.IsSemisimple.mapValue`: scalar extension preserves semisimple
  automorphisms when the source field is perfect.
* `LinearMap.GeneralLinearGroup.IsUnipotent.mapValue`: scalar extension preserves unipotent
  automorphisms, for arbitrary commutative value rings.
* `LinearMap.GeneralLinearGroup.jordanDecomposition_mapValue`: multiplicative Jordan
  decomposition commutes with scalar extension between perfect fields.

This is the linear-algebra input for value-field naturality of the Jordan decomposition of
algebraic-group points.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* `Mathlib.LinearAlgebra.Semisimple` for the squarefree-minimal-polynomial criterion.
-/

public section

open scoped TensorProduct
open Polynomial

namespace LinearMap.GeneralLinearGroup

universe u v w x

variable {R : Type u} {K : Type v} {L : Type w} {V : Type x}
variable [CommSemiring R] [AddCommMonoid V] [Module R V]

section CommRing

variable [CommRing K] [Algebra R K] [CommRing L] [Algebra R L]

/-- Scalar extension preserves unipotence of a linear automorphism. -/
theorem IsUnipotent.mapValue
    {g : GeneralLinearGroup K (K ⊗[R] V)} (hg : IsUnipotent g)
    (f : K →ₐ[R] L) :
    IsUnipotent (Module.End.mapValueGL f g) := by
  rw [isUnipotent_def] at hg ⊢
  have hsub : Module.End.mapValue f ((g : Module.End K (K ⊗[R] V)) - 1) =
      Module.End.mapValue f (g : Module.End K (K ⊗[R] V)) - 1 := by
    simpa only [Module.End.mapValueRingHom_apply, Module.End.mapValue_one] using
      map_sub (Module.End.mapValueRingHom (M := V) f) (g : Module.End K (K ⊗[R] V)) 1
  rw [Module.End.mapValueGL_coe, ← hsub]
  simpa only [Module.End.mapValueRingHom_apply] using
    hg.map (Module.End.mapValueRingHom (M := V) f)

end CommRing

section Field

variable [Field K] [Algebra R K] [Field L] [Algebra R L]

/-- Extending scalars from a perfect field preserves semisimplicity of an automorphism of a
scalar extension. -/
theorem IsSemisimple.mapValue [PerfectField K]
    [FiniteDimensional K (K ⊗[R] V)]
    {g : GeneralLinearGroup K (K ⊗[R] V)} (hg : IsSemisimple g)
    (f : K →ₐ[R] L) :
    IsSemisimple (Module.End.mapValueGL f g) := by
  rw [isSemisimple_def, Module.End.mapValueGL_coe]
  let p : K[X] := minpoly K (g : Module.End K (K ⊗[R] V))
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := p.map f.toRingHom)
  · have hp : p.Separable := PerfectField.separable_iff_squarefree.mpr
      ((isSemisimple_def g).mp hg).minpoly_squarefree
    exact hp.map.squarefree
  · calc
      aeval (Module.End.mapValue f (g : Module.End K (K ⊗[R] V)))
          (p.map f.toRingHom) =
          Module.End.mapValue f (aeval (g : Module.End K (K ⊗[R] V)) p) :=
        (Module.End.mapValue_aeval f _ p).symm
      _ = 0 := by
        dsimp only [p]
        have hmin : aeval (g : Module.End K (K ⊗[R] V))
            (minpoly K (g : Module.End K (K ⊗[R] V))) = 0 :=
          minpoly.aeval K (g : Module.End K (K ⊗[R] V))
        rw [hmin, Module.End.mapValue_zero]

section PerfectFields

variable [PerfectField K] [PerfectField L]
variable [FiniteDimensional K (K ⊗[R] V)]
variable [FiniteDimensional L (L ⊗[R] V)]

/-- Multiplicative Jordan–Chevalley decomposition commutes with extension between perfect value
fields. -/
theorem jordanDecomposition_mapValue (f : K →ₐ[R] L)
    (g : GeneralLinearGroup K (K ⊗[R] V)) :
    jordanDecomposition (Module.End.mapValueGL f g) =
      (Module.End.mapValueGL f (semisimplePart g),
        Module.End.mapValueGL f (unipotentPart g)) := by
  symm
  apply (eq_jordanDecomposition_iff (Module.End.mapValueGL f g) _ _).2
  refine ⟨(isSemisimple_semisimplePart g).mapValue f,
    (isUnipotent_unipotentPart g).mapValue f, ?_, ?_⟩
  · exact (commute_semisimplePart_unipotentPart g).map (Module.End.mapValueGL f)
  · rw [← map_mul, semisimplePart_mul_unipotentPart]

/-- The semisimple factor of an automorphism commutes with extension between perfect value
fields. -/
@[simp]
theorem semisimplePart_mapValue (f : K →ₐ[R] L)
    (g : GeneralLinearGroup K (K ⊗[R] V)) :
    semisimplePart (Module.End.mapValueGL f g) =
      Module.End.mapValueGL f (semisimplePart g) := by
  simpa only [semisimplePart_def] using
    congrArg Prod.fst (jordanDecomposition_mapValue f g)

/-- The unipotent factor of an automorphism commutes with extension between perfect value
fields. -/
@[simp]
theorem unipotentPart_mapValue (f : K →ₐ[R] L)
    (g : GeneralLinearGroup K (K ⊗[R] V)) :
    unipotentPart (Module.End.mapValueGL f g) =
      Module.End.mapValueGL f (unipotentPart g) := by
  simpa only [unipotentPart_def] using
    congrArg Prod.snd (jordanDecomposition_mapValue f g)

end PerfectFields

end Field

end LinearMap.GeneralLinearGroup
