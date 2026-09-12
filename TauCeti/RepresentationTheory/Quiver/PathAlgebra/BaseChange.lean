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
quotients.  A companion extensionality theorem says that ring homomorphisms out of any quotient
of a path algebra are determined by scalars and path classes.

This is the path-algebra scaffolding used by the scalar-extension clauses of Layers 1 and 4 of
`TauCetiRoadmap/ZigzagPreprojective/README.md`.
-/

public section

namespace TauCeti.PathAlgebra

open _root_.Quiver

universe u v w z

section BaseChange

variable {k : Type w} {l : Type z} {Q : Type u} {B : Type*}
  [CommSemiring k] [CommSemiring l] [Quiver.{v} Q] [Finite Q]
  [Semiring B] [Algebra l B]

private theorem baseChangeAlgHom_hcomp (g : pathAlgebra l Q →ₐ[l] B)
    {a b c : Q} (p : Path a b) (q : Path c a) :
    g (ofPath ⟨a, b, p⟩) * g (ofPath ⟨c, a, q⟩) = g (ofPath ⟨c, b, q.comp p⟩) := by
  rw [← map_mul, ofPath_mul_ofPath_of_comp]

private theorem baseChangeAlgHom_hzero (g : pathAlgebra l Q →ₐ[l] B)
    {x y : Quiver.TotalPath Q} (h : y.2.1 ≠ x.1) :
    g (ofPath x) * g (ofPath y) = 0 := by
  rw [← map_mul, ofPath_mul_ofPath_of_not_composable h, map_zero]

private theorem baseChangeAlgHom_hone (g : pathAlgebra l Q →ₐ[l] B) :
    letI := Fintype.ofFinite Q
    ∑ x : Q, g (ofPath ⟨x, x, Path.nil⟩) = 1 := by
  let _ := Fintype.ofFinite Q
  calc
    (∑ x : Q, g (ofPath ⟨x, x, Path.nil⟩)) =
        g (∑ x : Q, (ofPath ⟨x, x, Path.nil⟩ : pathAlgebra l Q)) := by
      rw [map_sum]
    _ = g (∑ x : Q, vertexIdempotent l x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      rw [vertexIdempotent_eq_ofPath]
    _ = g 1 := by rw [one_def]
    _ = 1 := g.map_one

/-- Change the coefficients in a path algebra and then apply an algebra homomorphism, leaving
every path fixed.  The target is regarded as a `k`-algebra through the composite coefficient
map. -/
noncomputable def baseChangeAlgHom (f : k →+* l) (g : pathAlgebra l Q →ₐ[l] B) :
    letI : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
      (fun a x ↦ Algebra.commutes (R := l) (A := B) (f a) x)
    pathAlgebra k Q →ₐ[k] B := by
  let _ : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
    (fun a x ↦ Algebra.commutes (R := l) (A := B) (f a) x)
  exact liftAlgHom k (fun x ↦ g (ofPath x)) (baseChangeAlgHom_hcomp g)
    (baseChangeAlgHom_hzero g) (baseChangeAlgHom_hone g)

/-- Changing coefficients and applying `g` sends a path over the source ring to the value under
`g` of the same path over the target ring. -/
@[simp]
theorem baseChangeAlgHom_ofPath (f : k →+* l) (g : pathAlgebra l Q →ₐ[l] B)
    (x : Quiver.TotalPath Q) :
    letI : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
      (fun a y ↦ Algebra.commutes (R := l) (A := B) (f a) y)
    baseChangeAlgHom f g (ofPath x) = g (ofPath x) := by
  let _ : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
    (fun a y ↦ Algebra.commutes (R := l) (A := B) (f a) y)
  rw [baseChangeAlgHom]
  exact liftAlgHom_ofPath k _ (baseChangeAlgHom_hcomp g)
    (baseChangeAlgHom_hzero g) (baseChangeAlgHom_hone g) x

/-- Changing coefficients and applying `g` transports a scalar through `f`. -/
@[simp]
theorem baseChangeAlgHom_algebraMap (f : k →+* l) (g : pathAlgebra l Q →ₐ[l] B)
    (a : k) :
    letI : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
      (fun b y ↦ Algebra.commutes (R := l) (A := B) (f b) y)
    baseChangeAlgHom f g (algebraMap k (pathAlgebra k Q) a) = algebraMap l B (f a) := by
  let _ : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
    (fun b y ↦ Algebra.commutes (R := l) (A := B) (f b) y)
  -- `toAlgebra'` makes the target's `k`-algebra map the displayed composite.
  rw [← RingHom.comp_apply]
  exact (baseChangeAlgHom f g).commutes a

/-- In the algebra structure induced through `f`, the scalar action of `k` is the scalar action
of `l` after applying `f`. -/
theorem smul_def_baseChange (f : k →+* l) (a : k) (x : B) :
    letI : Algebra k B := ((algebraMap l B).comp f).toAlgebra'
      (fun b y ↦ Algebra.commutes (R := l) (A := B) (f b) y)
    a • x = f a • x := by
  simp only [Algebra.smul_def]
  -- Expose the coefficient map supplied by `toAlgebra'` before evaluating the composite.
  change ((algebraMap l B).comp f) a * x = algebraMap l B (f a) * x
  rw [RingHom.comp_apply]

end BaseChange

section Ext

variable {k : Type w} {Q : Type u} {A B : Type*}
  [CommSemiring k] [Quiver.{v} Q] [Finite Q]
  [Semiring A] [Algebra k A] [Semiring B]

/-- Two ring homomorphisms out of a quotient of a path algebra are equal if they agree on
coefficients and on the images of all paths. -/
theorem ringHom_ext_of_surjective (q : pathAlgebra k Q →ₐ[k] A) (hq : Function.Surjective q)
    {g h : A →+* B}
    (hscalar : ∀ r : k, g (algebraMap k A r) = h (algebraMap k A r))
    (hpath : ∀ x : Quiver.TotalPath Q, g (q (ofPath x)) = h (q (ofPath x))) :
    g = h := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := hq y
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single x a =>
      rw [single_eq_smul_ofPath, map_smul]
      simp only [Algebra.smul_def, map_mul, hscalar, hpath]

end Ext

end TauCeti.PathAlgebra
