/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.SemisimplePoint
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality

/-!
# Scalar extension of Jordan decomposition for algebraic-group points

For a morphism `f : K →ₐ[k] L` between perfect value fields, postcomposition sends the
Jordan decomposition of a `K`-valued point to the Jordan decomposition of its resulting
`L`-valued point. The proof compares point actions before and after scalar extension. Their
underlying endomorphisms are related by `Module.End.mapValue`, so semisimplicity is preserved by
the corresponding linear Jordan–Chevalley theorem. Unipotence is already natural in the value
algebra. The point-level result then follows from uniqueness of the commuting
semisimple–unipotent factorization.

Together with coordinate-domain naturality, this supplies both variances needed to compare
geometric Jordan decompositions across affine-group morphisms and extensions of geometric point
fields.

## Main declarations

* `TauCeti.HopfAlgebra.Point.jordanDecomposition_mapValue`: point-level Jordan decomposition
  commutes with extension between perfect value fields.
* `TauCeti.HopfAlgebra.Point.semisimplePart_mapValue` and
  `TauCeti.HopfAlgebra.Point.unipotentPart_mapValue`: the component formulas, with
  `jordanDecomposition_toConv_algHom_comp`, `semisimplePart_toConv_algHom_comp`, and
  `unipotentPart_toConv_algHom_comp` as the simp-normal forms.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti

namespace HopfAlgebra

universe u

variable {k H K L : Type u}
variable [Field k] [CommRing H] [_root_.HopfAlgebra k H]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]

namespace Point

variable [PerfectField K] [PerfectField L]

/-- The Jordan decomposition of an algebraic-group point commutes with extension between perfect
value fields. -/
theorem jordanDecomposition_mapValue (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    jordanDecomposition k H L (AlgHom.mapValue (H := H) f g) =
      (AlgHom.mapValue (H := H) f (semisimplePart k H K g),
        AlgHom.mapValue (H := H) f (unipotentPart k H K g)) := by
  symm
  apply (eq_jordanDecomposition_iff k H L (AlgHom.mapValue (H := H) f g) _ _).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : IsSemisimplePoint (semisimplePart k H K g) := by
      rw [isSemisimplePoint_def]
      exact fun M ↦ isSemisimple_pointsAction_semisimplePart k H K g M
    exact (isSemisimplePoint_def _).mp (hs.mapValue f)
  · have hu : IsUnipotentPoint (unipotentPart k H K g) := by
      rw [isUnipotentPoint_def]
      exact fun M ↦ isUnipotent_pointsAction_unipotentPart k H K g M
    exact hu.mapValue f
  · exact (commute_semisimplePart_unipotentPart k H K g).map
      (AlgHom.mapValue (H := H) f)
  · rw [← map_mul, semisimplePart_mul_unipotentPart]

/-- The semisimple part of an algebraic-group point commutes with extension between perfect value
fields. -/
theorem semisimplePart_mapValue (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    semisimplePart k H L (AlgHom.mapValue (H := H) f g) =
      AlgHom.mapValue (H := H) f (semisimplePart k H K g) := by
  simpa only [jordanDecomposition_fst] using
    congrArg Prod.fst (jordanDecomposition_mapValue f g)

/-- The unipotent part of an algebraic-group point commutes with extension between perfect value
fields. -/
theorem unipotentPart_mapValue (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    unipotentPart k H L (AlgHom.mapValue (H := H) f g) =
      AlgHom.mapValue (H := H) f (unipotentPart k H K g) := by
  simpa only [jordanDecomposition_snd] using
    congrArg Prod.snd (jordanDecomposition_mapValue f g)

/-- Simp-normal form of `jordanDecomposition_mapValue`, with each postcomposed point written
after normalization by `AlgHom.mapValue_apply`. -/
@[simp]
theorem jordanDecomposition_toConv_algHom_comp (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    jordanDecomposition k H L (toConv (f.comp g.ofConv)) =
      (toConv (f.comp (semisimplePart k H K g).ofConv),
        toConv (f.comp (unipotentPart k H K g).ofConv)) := by
  simpa only [AlgHom.mapValue_apply] using jordanDecomposition_mapValue f g

/-- Simp-normal form of `semisimplePart_mapValue`, written after normalization by
`AlgHom.mapValue_apply`. -/
@[simp]
theorem semisimplePart_toConv_algHom_comp (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    semisimplePart k H L (toConv (f.comp g.ofConv)) =
      toConv (f.comp (semisimplePart k H K g).ofConv) := by
  simpa only [AlgHom.mapValue_apply] using semisimplePart_mapValue f g

/-- Simp-normal form of `unipotentPart_mapValue`, written after normalization by
`AlgHom.mapValue_apply`. -/
@[simp]
theorem unipotentPart_toConv_algHom_comp (f : K →ₐ[k] L)
    (g : WithConv (H →ₐ[k] K)) :
    unipotentPart k H L (toConv (f.comp g.ofConv)) =
      toConv (f.comp (unipotentPart k H K g).ofConv) := by
  simpa only [AlgHom.mapValue_apply] using unipotentPart_mapValue f g

end Point

end HopfAlgebra

end TauCeti
