/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# Changing coefficients in a path algebra

A homomorphism of commutative semirings `f : k →+* l` transports the coefficients of a path
algebra while leaving its paths fixed.  More generally, if an `l`-algebra homomorphism out of
`lQ` assigns values to the paths, those same values induce a `k`-algebra homomorphism out of
`kQ`, where the target is regarded as a `k`-algebra through `f`.

The construction packages the common path-algebra step in base-change maps for relation
quotients.  The construction `RingHom.pathAlgebraBaseChangeAlgHom` was generalized from
`TauCeti.RepresentationTheory.Quiver.Preprojective.BaseChange`.
-/

public section

namespace RingHom

open _root_.Quiver TauCeti TauCeti.PathAlgebra

universe u v w z

section BaseChange

variable {k : Type w} {l : Type z} {Q : Type u} {B : Type*}
  [CommSemiring k] [CommSemiring l] [Quiver.{v} Q] [_root_.Finite Q]
  [Semiring B] [Algebra l B]

private theorem pathAlgebraBaseChangeAlgHom_hcomp (g : pathAlgebra l Q →ₐ[l] B)
    {a b c : Q} (p : Path a b) (q : Path c a) :
    g (ofPath ⟨a, b, p⟩) * g (ofPath ⟨c, a, q⟩) = g (ofPath ⟨c, b, q.comp p⟩) := by
  rw [← map_mul, ofPath_mul_ofPath_of_comp]

private theorem pathAlgebraBaseChangeAlgHom_hzero (g : pathAlgebra l Q →ₐ[l] B)
    {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    g (ofPath x) * g (ofPath y) = 0 := by
  rw [← map_mul, ofPath_mul_ofPath_of_not_composable h, map_zero]

private theorem pathAlgebraBaseChangeAlgHom_hone (g : pathAlgebra l Q →ₐ[l] B) :
    letI := Fintype.ofFinite Q
    ∑ x : Q, g (ofPath ⟨x, x, Path.nil⟩) = 1 := by
  let _ := Fintype.ofFinite Q
  rw [← map_sum]
  simp only [← vertexIdempotent_eq_ofPath, ← PathAlgebra.one_def, map_one]

/-- Change the coefficients in a path algebra and then apply an algebra homomorphism, leaving
every path fixed.  The target is regarded as a `k`-algebra through the composite coefficient
map. -/
noncomputable def pathAlgebraBaseChangeAlgHom (f : k →+* l)
    (g : pathAlgebra l Q →ₐ[l] B) :
    letI := Algebra.compHom B f
    pathAlgebra k Q →ₐ[k] B := by
  let _ := Algebra.compHom B f
  exact liftAlgHom k (fun x ↦ g (ofPath x)) (pathAlgebraBaseChangeAlgHom_hcomp g)
    (pathAlgebraBaseChangeAlgHom_hzero g) (pathAlgebraBaseChangeAlgHom_hone g)

/-- Changing coefficients and applying `g` sends a path over the source ring to the value under
`g` of the same path over the target ring. -/
@[simp]
theorem pathAlgebraBaseChangeAlgHom_ofPath (f : k →+* l) (g : pathAlgebra l Q →ₐ[l] B)
    (x : Quiver.TotalPath Q) :
    letI := Algebra.compHom B f
    pathAlgebraBaseChangeAlgHom f g (ofPath x) = g (ofPath x) := by
  let _ := Algebra.compHom B f
  rw [pathAlgebraBaseChangeAlgHom]
  exact liftAlgHom_ofPath k _ (pathAlgebraBaseChangeAlgHom_hcomp g)
    (pathAlgebraBaseChangeAlgHom_hzero g) (pathAlgebraBaseChangeAlgHom_hone g) x

end BaseChange

end RingHom
