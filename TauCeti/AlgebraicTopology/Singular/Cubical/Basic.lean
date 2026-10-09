/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Singular cubes, their faces and degeneracies

A **singular `n`-cube** in a topological space `X` is a continuous map `Iⁿ → X`, where
`Iⁿ = Fin n → I` is the standard cube.  This file sets up the combinatorics of singular cubes that
cubical singular homology is built on, following Massey, *Singular Homology Theory*, Chapter II:

* the **faces** `face i t c : Iⁿ → X` of an `(n+1)`-cube `c`, obtained by fixing the `i`-th
  coordinate at `t ∈ I`; the front and back faces of the literature are `face i 0` and `face i 1`;
* the **cubical identity** `face_face`, which rewrites two successive faces in the other order;
* **degenerate cubes**, in Massey's sense: a cube is degenerate when it does not depend on at least
  one of its coordinates.  This convention, rather than Serre's independence of the last
  coordinate, is the one closed under the cross product.

Faces do not preserve degeneracy: if `c` does not depend on its `i`-th coordinate, then its two
`i`-faces coincide (`face_eq_of_isDegenerateAt`), and need not be degenerate, while its faces in
every other coordinate are degenerate (`isDegenerate_face_of_ne`).  Together these two facts are
exactly what makes the degenerate chains a subcomplex of the cubical chains, which is where this
file is used.

The one piece of `Fin` combinatorics that is not in Mathlib is `Fin.insertNth_insertNth`, the
commutation of two insertions, dual to `Fin.removeNth_removeNth_eq_swap`.

## Main definitions

* `TauCeti.SingularCube X n`: singular `n`-cubes in `X`.
* `TauCeti.SingularCube.face`: the face of a cube in a coordinate, at a parameter `t ∈ I`.
* `TauCeti.SingularCube.IsDegenerateAt`, `TauCeti.SingularCube.IsDegenerate`: degeneracy at a
  coordinate, and degeneracy.

## Main results

* `Fin.insertNth_insertNth`: two insertions commute, up to reindexing by `succAbove` and
  `predAbove`.
* `TauCeti.SingularCube.face_face`: the cubical identity.
* `TauCeti.SingularCube.face_eq_of_isDegenerateAt`, `TauCeti.SingularCube.isDegenerate_face_of_ne`:
  the behaviour of faces on a degenerate cube.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II, for the alternative convention.
-/

public section

open unitInterval

/-- Two insertions commute, up to reindexing: inserting `a` at `i` after inserting `b` at `j` is
inserting `b` at `i.succAbove j` after inserting `a` at `j.predAbove i`.  This is the dual of
`Fin.removeNth_removeNth_eq_swap`. -/
theorem Fin.insertNth_insertNth {n : ℕ} {β : Sort*} (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : β)
    (x : Fin n → β) :
    @Fin.insertNth _ (fun _ ↦ β) i a (@Fin.insertNth _ (fun _ ↦ β) j b x) =
      @Fin.insertNth _ (fun _ ↦ β) (i.succAbove j) b
        (@Fin.insertNth _ (fun _ ↦ β) (j.predAbove i) a x) := by
  rw [Fin.eq_insertNth_iff]
  refine ⟨by simp, ?_⟩
  funext k
  rcases Fin.eq_self_or_eq_succAbove (j.predAbove i) k with rfl | ⟨k, rfl⟩
  · simp only [Fin.removeNth, Fin.succAbove_succAbove_predAbove, Fin.insertNth_apply_same]
  · simp only [Fin.removeNth, Fin.succAbove_succAbove_succAbove_predAbove,
      Fin.insertNth_apply_succAbove]

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A **singular `n`-cube** in `X`: a continuous map from the standard cube `Iⁿ = Fin n → I`. -/
abbrev SingularCube (X : Type*) [TopologicalSpace X] (n : ℕ) := C(Fin n → I, X)

namespace SingularCube

/-- The face of an `(n+1)`-cube in its `i`-th coordinate, at the parameter `t`: the `n`-cube
`x ↦ c (i.insertNth t x)`.  The front and back faces are `face i 0` and `face i 1`. -/
def face {n : ℕ} (i : Fin (n + 1)) (t : I) (c : SingularCube X (n + 1)) : SingularCube X n :=
  c.comp (⟨fun x ↦ i.insertNth t x, by fun_prop⟩ : C(Fin n → I, Fin (n + 1) → I))

@[simp]
theorem face_apply {n : ℕ} (i : Fin (n + 1)) (t : I) (c : SingularCube X (n + 1))
    (x : Fin n → I) : face i t c x = c (i.insertNth t x) := by
  rw [face]
  rfl

/-- The cubical identity: a face of a face, in the other order. -/
theorem face_face {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (a b : I)
    (c : SingularCube X (n + 2)) :
    face j b (face i a c) = face (j.predAbove i) a (face (i.succAbove j) b c) := by
  ext x
  simp only [face_apply]
  rw [Fin.insertNth_insertNth]

/-- Faces commute with composition by a continuous map. -/
theorem face_comp {n : ℕ} (i : Fin (n + 1)) (t : I) (f : C(X, Y)) (c : SingularCube X (n + 1)) :
    face i t (f.comp c) = f.comp (face i t c) := by
  ext x
  simp

/-- A cube is **degenerate at the coordinate `i`** when it does not depend on it. -/
def IsDegenerateAt {n : ℕ} (c : SingularCube X n) (i : Fin n) : Prop :=
  ∀ (x : Fin n → I) (t : I), c (Function.update x i t) = c x

/-- A cube is **degenerate** when it does not depend on at least one of its coordinates (Massey's
convention). -/
def IsDegenerate {n : ℕ} (c : SingularCube X n) : Prop :=
  ∃ i, IsDegenerateAt c i

theorem IsDegenerateAt.isDegenerate {n : ℕ} {c : SingularCube X n} {i : Fin n}
    (h : IsDegenerateAt c i) : IsDegenerate c :=
  ⟨i, h⟩

/-- A `0`-cube, a point, is never degenerate. -/
theorem not_isDegenerate_zero (c : SingularCube X 0) : ¬ IsDegenerate c :=
  fun ⟨i, _⟩ ↦ i.elim0

theorem IsDegenerateAt.comp {n : ℕ} {c : SingularCube X n} {i : Fin n} (h : IsDegenerateAt c i)
    (f : C(X, Y)) : IsDegenerateAt (f.comp c) i := fun x t ↦ by
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply, h x t]

/-- Composition with a continuous map preserves degeneracy. -/
theorem IsDegenerate.comp {n : ℕ} {c : SingularCube X n} (h : IsDegenerate c) (f : C(X, Y)) :
    IsDegenerate (f.comp c) :=
  h.elim fun i hi ↦ ⟨i, hi.comp f⟩

/-- The two faces of a cube in a coordinate it does not depend on coincide. -/
theorem face_eq_of_isDegenerateAt {n : ℕ} {c : SingularCube X (n + 1)} {i : Fin (n + 1)}
    (h : IsDegenerateAt c i) (t t' : I) : face i t c = face i t' c := by
  ext x
  have := h (i.insertNth t' x) t
  rwa [Fin.update_insertNth, ← face_apply, ← face_apply] at this

/-- The faces of a cube in a coordinate it depends on, taken in a coordinate it does not depend
on, are degenerate. -/
theorem isDegenerate_face_of_ne {n : ℕ} {c : SingularCube X (n + 1)} {i j : Fin (n + 1)}
    (h : IsDegenerateAt c i) (hij : i ≠ j) (t : I) : IsDegenerate (face j t c) := by
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij
  refine ⟨k, fun x s ↦ ?_⟩
  rw [face_apply, face_apply, Fin.insertNth_update, hk, h]

end SingularCube

end TauCeti
