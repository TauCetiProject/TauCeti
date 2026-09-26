/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Map
public import TauCeti.RepresentationTheory.Quiver.Symmetrify

/-!
# The path algebra of a quiver as a retract of the doubled path algebra

The doubled quiver `Quiver.Symmetrify Q` contains `Q` through the prefunctor `Quiver.Symmetrify.of`,
which is the identity on vertices, so `TauCeti.PathAlgebra.mapAlgHom` includes the path algebra
`kQ` in the doubled path algebra `kQ^sym` (the path algebra of `Quiver.Symmetrify Q`). This file
constructs an algebra homomorphism in the other direction,

```text
kQ^sym → kQ,
```

which fixes the vertex idempotents and the arrows of `Q` and sends every formal reverse to zero: a
path of the doubled quiver goes to itself when it uses only arrows of `Q`, and to zero as soon as
it uses a formal reverse. It is a retraction of the inclusion, so `kQ` is a quotient algebra of
`kQ^sym`.

Its use is that it kills every product in which a formal reverse occurs, such as the two backtracks
`a a*` and `a* a` of an arrow; this is what lets it descend to quotients of `kQ^sym` by relations
built from such products, notably the preprojective algebra.

## Main definitions

* `TauCeti.PathAlgebra.symmetrifyRetraction`: the algebra homomorphism `kQ^sym →ₐ[k] kQ` killing the
  formal reverses.

## Main results

* `TauCeti.PathAlgebra.symmetrifyRetraction_vertexIdempotent`,
  `TauCeti.PathAlgebra.symmetrifyRetraction_ofArrow_of` and
  `TauCeti.PathAlgebra.symmetrifyRetraction_ofArrow_reverse_of`: its values on the generators.
* `TauCeti.PathAlgebra.symmetrifyRetraction_comp_mapAlgHom_of`: **it is a retraction** of the
  inclusion `kQ →ₐ[k] kQ^sym`, which is therefore injective
  (`TauCeti.PathAlgebra.mapAlgHom_of_injective`), while the retraction is surjective
  (`TauCeti.PathAlgebra.symmetrifyRetraction_surjective`).
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v w

namespace PathAlgebra

section Retraction

variable (k : Type w) {Q : Type u} [CommSemiring k] [Quiver.{v} Q]

/-- The image in `kQ` of a path of the doubled quiver: the path itself when it uses only arrows of
`Q`, and zero once it uses a formal reverse. -/
private noncomputable def retractPath :
    {a b : Symmetrify Q} → Path a b → pathAlgebra k Q
  | a, _, .nil => vertexIdempotent (Q := Q) k a
  | _, _, .cons p e =>
    Sum.elim (fun f => ofArrow (Q := Q) f * retractPath p) (fun _ => 0) e

-- The vertices of a doubled path are terms of `Symmetrify Q`, which the path algebra of `Q` reads
-- as vertices of `Q`; rewriting cannot see through that synonym, so the corner identity of an
-- arrow is supplied below as a term with its quiver named.
/-- The image of a doubled path lies in the corner of its target. -/
private theorem vertexIdempotent_mul_retractPath {a b : Symmetrify Q} (p : Path a b) :
    vertexIdempotent (Q := Q) k b * retractPath k p = retractPath k p := by
  cases p with
  | nil => rw [retractPath]; exact vertexIdempotent_mul_self (k := k) (Q := Q) _
  | cons p e =>
    rcases e with f | f
    · rw [retractPath, Sum.elim_inl, ← mul_assoc]
      exact congrArg (· * retractPath k p)
        ((congrArg _ (ofArrow_eq_ofPath (Q := Q) f)).trans
          ((vertexIdempotent_mul_ofPath (k := k) (Q := Q) f.toPath).trans
            (ofArrow_eq_ofPath (Q := Q) f).symm))
    · rw [retractPath, Sum.elim_inr, mul_zero]

/-- The image of a doubled path lies in the corner of its source. -/
private theorem retractPath_mul_vertexIdempotent {a b : Symmetrify Q} (p : Path a b) :
    retractPath k p * vertexIdempotent (Q := Q) k a = retractPath k p := by
  induction p with
  | nil => rw [retractPath]; exact vertexIdempotent_mul_self (k := k) (Q := Q) _
  | cons p e ih =>
    rcases e with f | f
    · rw [retractPath, Sum.elim_inl, mul_assoc, ih]
    · rw [retractPath, Sum.elim_inr, zero_mul]

/-- Concatenation of doubled paths becomes multiplication, later factor first. -/
private theorem retractPath_comp {a b c : Symmetrify Q} (p : Path a b) (q : Path c a) :
    retractPath k p * retractPath k q = retractPath k (q.comp p) := by
  induction p with
  | nil => rw [Path.comp_nil, retractPath, vertexIdempotent_mul_retractPath]
  | cons p e ih =>
    rcases e with f | f
    · rw [Path.comp_cons, retractPath, retractPath, Sum.elim_inl, Sum.elim_inl, mul_assoc, ih]
    · rw [Path.comp_cons, retractPath, retractPath, Sum.elim_inr, Sum.elim_inr, zero_mul]

/-- A path of `Q`, viewed in the doubled quiver, goes back to itself. -/
private theorem retractPath_mapPath {a b : Q} (p : Path a b) :
    retractPath k (Symmetrify.of.mapPath p) = ofPath ⟨a, b, p⟩ := by
  induction p with
  | nil => rw [Prefunctor.mapPath_nil, retractPath]; exact vertexIdempotent_eq_ofPath k a
  | cons p f ih =>
    rw [Prefunctor.mapPath_cons, retractPath]
    exact (congrArg (ofArrow f * ·) ih).trans (ofArrow_mul_ofPath f p)

variable [Finite Q]

private theorem retractPath_hzero {x y : Quiver.TotalPath (Symmetrify Q)} (h : y.2.1 ≠ x.1) :
    retractPath k x.2.2 * retractPath k y.2.2 = 0 := by
  rw [← retractPath_mul_vertexIdempotent k x.2.2, ← vertexIdempotent_mul_retractPath k y.2.2,
    mul_assoc, ← mul_assoc (vertexIdempotent (Q := Q) k x.1),
    vertexIdempotent_mul_vertexIdempotent_of_ne (Q := Q) (Ne.symm h), zero_mul, mul_zero]

private theorem retractPath_hone :
    letI := Fintype.ofFinite (Symmetrify Q)
    ∑ v : Symmetrify Q, retractPath k (Path.nil : Path v v) = 1 := by
  let _ := Fintype.ofFinite Q
  refine (Finset.sum_congr rfl fun v _ => ?_).trans (one_def (k := k) (Q := Q)).symm
  rw [retractPath]

/-- The algebra homomorphism `kQ^sym →ₐ[k] kQ` from the path algebra of the doubled quiver to the
path algebra of `Q` which fixes the vertex idempotents and the arrows of `Q` and kills every formal
reverse. A doubled path goes to itself when it uses only arrows of `Q`, and to zero otherwise. -/
noncomputable def symmetrifyRetraction : pathAlgebra k (Symmetrify Q) →ₐ[k] pathAlgebra k Q :=
  liftAlgHom k (fun x => retractPath k x.2.2) (retractPath_comp k)
    (retractPath_hzero k) (retractPath_hone k)

/-- The retraction fixes every vertex idempotent. -/
@[simp]
theorem symmetrifyRetraction_vertexIdempotent (v : Q) :
    symmetrifyRetraction k (vertexIdempotent (Q := Symmetrify Q) k v) = vertexIdempotent k v :=
  (congrArg _ (vertexIdempotent_eq_ofPath (Q := Symmetrify Q) k v)).trans (by
    rw [symmetrifyRetraction, liftAlgHom_ofPath, retractPath])

-- The two arrow equations below are not `simp` lemmas: `TauCeti.PathAlgebra.ofArrow_eq_ofPath`
-- already rewrites their left-hand sides, and `simp` computes them through
-- `TauCeti.PathAlgebra.symmetrifyRetraction_ofPath_mapTotalPath_of` and the path basis instead.
/-- The retraction fixes every arrow of `Q`. -/
theorem symmetrifyRetraction_ofArrow_of {a b : Q} (f : a ⟶ b) :
    symmetrifyRetraction k (ofArrow (Symmetrify.of.map f)) = ofArrow f := by
  rw [ofArrow_eq_ofPath, ← Prefunctor.mapPath_toPath, symmetrifyRetraction, liftAlgHom_ofPath,
    retractPath_mapPath, ofArrow_eq_ofPath]

/-- The retraction kills every formal reverse. -/
theorem symmetrifyRetraction_ofArrow_reverse_of {a b : Q} (f : a ⟶ b) :
    symmetrifyRetraction k (ofArrow (reverse (Symmetrify.of.map f))) = 0 := by
  rw [ofArrow_eq_ofPath, symmetrifyRetraction, liftAlgHom_ofPath, Hom.toPath, retractPath]
  rfl

/-- The retraction sends a path of `Q`, viewed in the doubled quiver, back to itself. -/
@[simp]
theorem symmetrifyRetraction_ofPath_mapTotalPath_of (x : Quiver.TotalPath Q) :
    symmetrifyRetraction k (ofPath (Symmetrify.of.mapTotalPath x)) = ofPath x := by
  obtain ⟨a, b, p⟩ := x
  rw [symmetrifyRetraction, liftAlgHom_ofPath, Prefunctor.mapTotalPath_mk]
  exact retractPath_mapPath k p

/-- **The retraction is a left inverse of the inclusion** `kQ →ₐ[k] kQ^sym` induced by
`Quiver.Symmetrify.of`. -/
@[simp]
theorem symmetrifyRetraction_comp_mapAlgHom_of :
    (symmetrifyRetraction k).comp (mapAlgHom k Symmetrify.of symmetrify_of_obj_bijective) =
      AlgHom.id k (pathAlgebra k Q) :=
  algHom_ext k fun x => by
    rw [AlgHom.comp_apply, mapAlgHom_ofPath, symmetrifyRetraction_ofPath_mapTotalPath_of,
      AlgHom.id_apply]

/-- The inclusion `kQ →ₐ[k] kQ^sym` induced by `Quiver.Symmetrify.of` is injective. -/
theorem mapAlgHom_of_injective :
    Function.Injective (mapAlgHom k Symmetrify.of (symmetrify_of_obj_bijective (Q := Q))) :=
  Function.LeftInverse.injective (g := symmetrifyRetraction k) fun x => by
    rw [← AlgHom.comp_apply, symmetrifyRetraction_comp_mapAlgHom_of, AlgHom.id_apply]

/-- The retraction `kQ^sym →ₐ[k] kQ` is surjective. -/
theorem symmetrifyRetraction_surjective : Function.Surjective (symmetrifyRetraction k (Q := Q)) :=
  Function.RightInverse.surjective (f := symmetrifyRetraction k)
    (g := mapAlgHom k Symmetrify.of symmetrify_of_obj_bijective) fun x => by
    rw [← AlgHom.comp_apply, symmetrifyRetraction_comp_mapAlgHom_of, AlgHom.id_apply]

end Retraction

end PathAlgebra

end TauCeti
