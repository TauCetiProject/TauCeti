/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Cross products of singular cubes

The cross product of a `p`-cube and a `q`-cube uses the first `p` and last `q` coordinates of
`I^(p+q)`, respectively. This is the geometric operation underlying the cross product of cubical
chains. Faces in either block are the cross products with the corresponding face of that factor.
Degeneracy in a coordinate is equivalent to degeneracy of the corresponding factor, so this
operation preserves Massey's degenerate cubes in both variables.

Associativity holds as an equality after the canonical reindexing of finite coordinates and
reassociation of Cartesian products. For zero-dimensional factors, the formulas retain the
chosen point in the product. No homotopy or shuffle correction is involved.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Chapter VII.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea,
  *Morse homology with differential graded coefficients*, Chapter 5.
-/

public section

open unitInterval

namespace TauCeti.SingularCube

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W] {p q r : ℕ}

/-- The cross product of singular cubes, with the coordinates of the first factor first. -/
def crossProduct (c : SingularCube X p) (d : SingularCube Y q) :
    SingularCube (X × Y) (p + q) :=
  (c.prodMap d).comp (Fin.appendHomeomorph (X := I) p q).symm

-- Simplify before the factors, whose continuous-map types carry the dimensions.
@[simp↓]
theorem crossProduct_apply (c : SingularCube X p) (d : SingularCube Y q)
    (x : Fin (p + q) → I) :
    crossProduct c d x = (c (fun i ↦ x (i.castAdd q)), d (fun j ↦ x (j.natAdd p))) := by
  simp [crossProduct]

/-- The cross product is natural in both spaces. -/
theorem crossProduct_comp (f : C(X, Z)) (g : C(Y, W))
    (c : SingularCube X p) (d : SingularCube Y q) :
    crossProduct (f.comp c) (g.comp d) = (f.prodMap g).comp (crossProduct c d) := by
  ext x <;> simp

/-- Cross products are associative after the canonical coordinate and product identifications. -/
theorem crossProduct_assoc (c : SingularCube X p) (d : SingularCube Y q)
    (e : SingularCube Z r) :
    cast (Nat.add_assoc p q r).symm (crossProduct c (crossProduct d e)) =
      (Homeomorph.prodAssoc X Y Z : C((X × Y) × Z, X × Y × Z)).comp
        (crossProduct (crossProduct c d) e) := by
  apply ContinuousMap.ext
  intro x
  simp only [cast_apply, ContinuousMap.comp_apply, toContinuousMap, Homeomorph.prodAssoc,
    crossProduct_apply, Function.comp_apply]
  congr 2
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp
  omega

/-- The cross product with a zero-dimensional left factor retains its point in the product. -/
-- Not a simp lemma: `crossProduct_apply` already expands the left-hand side.
theorem crossProduct_zero_left (c : SingularCube X 0) (d : SingularCube Y q)
    (x : Fin (0 + q) → I) :
    crossProduct c d x = (c Fin.elim0, d (x ∘ Fin.cast (Nat.zero_add q).symm)) := by
  simp only [crossProduct_apply]
  apply Prod.ext
  · exact congrArg c (Subsingleton.elim _ _)
  · apply congrArg d
    funext i
    exact congrArg x (Fin.ext (by simp))

/-- The cross product with a zero-dimensional right factor retains its point in the product. -/
-- Not a simp lemma: `crossProduct_apply` already expands the left-hand side.
theorem crossProduct_zero_right (c : SingularCube X p) (d : SingularCube Y 0)
    (x : Fin (p + 0) → I) :
    crossProduct c d x = (c (x ∘ Fin.cast (Nat.add_zero p).symm), d Fin.elim0) := by
  simp only [crossProduct_apply]
  apply Prod.ext
  · apply congrArg c
    funext i
    congr 1
  · exact congrArg d (Subsingleton.elim _ _)

/-- Degeneracy in the first coordinate block is exactly degeneracy of the first factor. -/
@[simp]
theorem isDegenerateAt_crossProduct_castAdd_iff (c : SingularCube X p)
    (d : SingularCube Y q) (i : Fin p) :
    IsDegenerateAt (crossProduct c d) (i.castAdd q) ↔ IsDegenerateAt c i := by
  simp only [isDegenerateAt_iff]
  constructor
  · intro h x t
    have hx := congrArg Prod.fst (h (Fin.append x (fun _ ↦ 0)) t)
    simpa only [crossProduct_apply, Prod.fst,
      Function.update_apply_of_injective _ (Fin.castAdd_injective p q), Fin.append_left] using hx
  · intro h x t
    simp only [crossProduct_apply, Prod.mk.injEq]
    constructor
    · simpa only [Function.update_apply_of_injective _ (Fin.castAdd_injective p q)]
        using h (fun j ↦ x (j.castAdd q)) t
    · congr 1
      funext j
      have hne : j.natAdd p ≠ i.castAdd q := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
        have := i.isLt
        omega
      simp [Function.update_of_ne hne]

/-- Degeneracy in the second coordinate block is exactly degeneracy of the second factor. -/
@[simp]
theorem isDegenerateAt_crossProduct_natAdd_iff (c : SingularCube X p)
    (d : SingularCube Y q) (i : Fin q) :
    IsDegenerateAt (crossProduct c d) (i.natAdd p) ↔ IsDegenerateAt d i := by
  simp only [isDegenerateAt_iff]
  constructor
  · intro h x t
    have hx := congrArg Prod.snd (h (Fin.append (fun _ ↦ 0) x) t)
    simpa only [crossProduct_apply, Prod.snd,
      Function.update_apply_of_injective _ (Fin.natAdd_injective q p), Fin.append_right] using hx
  · intro h x t
    simp only [crossProduct_apply, Prod.mk.injEq]
    constructor
    · congr 1
      funext j
      have hne : j.castAdd q ≠ i.natAdd p := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
        have := j.isLt
        omega
      simp [Function.update_of_ne hne]
    · simpa only [Function.update_apply_of_injective _ (Fin.natAdd_injective q p)]
        using h (fun j ↦ x (j.natAdd p)) t

/-- Faces in the first block are cross products with faces of the first factor. -/
@[simp]
theorem face_crossProduct_castAdd (c : SingularCube X (p + 1)) (d : SingularCube Y q)
    (i : Fin (p + 1)) (t : I) :
    face (Fin.cast (by omega) (i.castAdd q)) t
        (cast (by omega : (p + 1) + q = (p + q) + 1) (crossProduct c d)) =
      crossProduct (face i t c) d := by
  apply ContinuousMap.ext
  intro z
  rw [← Fin.append_castAdd_natAdd (f := z)]
  simp only [face_apply, cast_apply, Fin.insertNth_append_castAdd]
  simp [Function.comp_def]

/-- Faces in the second block are cross products with faces of the second factor. -/
@[simp]
theorem face_crossProduct_natAdd (c : SingularCube X p) (d : SingularCube Y (q + 1))
    (i : Fin (q + 1)) (t : I) :
    face (n := p + q) (i.natAdd p) t (crossProduct (p := p) (q := q + 1) c d) =
      crossProduct c (face i t d) := by
  apply ContinuousMap.ext
  intro z
  rw [← Fin.append_castAdd_natAdd (f := z)]
  simp only [face_apply, Fin.insertNth_append_natAdd, crossProduct_apply,
    Fin.append_left, Fin.append_right]

/-- A cross product is degenerate if and only if at least one factor is degenerate. -/
@[simp]
theorem isDegenerate_crossProduct_iff (c : SingularCube X p) (d : SingularCube Y q) :
    IsDegenerate (crossProduct c d) ↔ IsDegenerate c ∨ IsDegenerate d := by
  simp only [isDegenerate_iff]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.addCases with
    | left i => exact Or.inl ⟨i, (isDegenerateAt_crossProduct_castAdd_iff c d i).mp hi⟩
    | right i => exact Or.inr ⟨i, (isDegenerateAt_crossProduct_natAdd_iff c d i).mp hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact ⟨i.castAdd q, (isDegenerateAt_crossProduct_castAdd_iff c d i).mpr hi⟩
    · exact ⟨i.natAdd p, (isDegenerateAt_crossProduct_natAdd_iff c d i).mpr hi⟩

end TauCeti.SingularCube
