/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval
public import TauCeti.Data.Fin.Basic

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

The cubical identity rests on `Fin.insertNth_insertNth` (`TauCeti.Data.Fin.Basic`), the
commutation of two insertions, dual to Mathlib's `Fin.removeNth_removeNth_eq_swap`.

## Main definitions

* `TauCeti.SingularCube X n`: singular `n`-cubes in `X`.
* `TauCeti.SingularCube.cast`: reindexing along an equality of dimensions.
* `TauCeti.SingularCube.point`: the `0`-cube at a point.
* `TauCeti.SingularCube.face`: the face of a cube in a coordinate, at a parameter `t ∈ I`.
* `TauCeti.SingularCube.degeneracy`: the cube obtained by forgetting a coordinate.
* `TauCeti.SingularCube.IsDegenerateAt`, `TauCeti.SingularCube.IsDegenerate`: degeneracy at a
  coordinate, and degeneracy.

## Main results

* `TauCeti.SingularCube.face_face`: the cubical identity.
* `TauCeti.SingularCube.face_degeneracy_self`: a degeneracy followed by the matching face.
* `TauCeti.SingularCube.isDegenerate_iff_exists_eq_degeneracy`: degeneracies exhaust the
  degenerate cubes.
* `TauCeti.SingularCube.isDegenerateAt_iff`, `TauCeti.SingularCube.isDegenerate_iff`,
  `TauCeti.SingularCube.IsDegenerateAt.apply_update`: the characterizations of degeneracy.
* `TauCeti.SingularCube.face_eq_of_isDegenerateAt`, `TauCeti.SingularCube.isDegenerate_face_of_ne`:
  the behaviour of faces on a degenerate cube.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II, for the alternative convention.
-/

public section

open unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A **singular `n`-cube** in `X`: a continuous map from the standard cube `Iⁿ = Fin n → I`. -/
abbrev SingularCube (X : Type*) [TopologicalSpace X] (n : ℕ) := C(Fin n → I, X)

namespace SingularCube

/-- Reindex a singular cube along an equality of dimensions. -/
def cast {n m : ℕ} (h : n = m) (c : SingularCube X n) : SingularCube X m :=
  c.comp ⟨fun x ↦ x ∘ Fin.cast h, by fun_prop⟩

@[simp]
theorem cast_apply {n m : ℕ} (h : n = m) (c : SingularCube X n) (x : Fin m → I) :
    cast h c x = c (x ∘ Fin.cast h) :=
  (rfl)

/-- The `0`-cube at a point. -/
def point (x : X) : SingularCube X 0 := ContinuousMap.const _ x

@[simp]
theorem point_apply (x : X) (t : Fin 0 → I) : point x t = x :=
  (rfl)

/-- Every `0`-cube is the constant cube at its value. -/
theorem eq_point (c : SingularCube X 0) : c = point (c fun i ↦ i.elim0) :=
  ContinuousMap.ext fun t ↦ by
    simp only [point_apply]
    exact congrArg c (Subsingleton.elim _ _)

@[simp]
theorem cast_rfl {n : ℕ} (c : SingularCube X n) : cast rfl c = c := by
  ext x
  simp

/-- Reindexing along successive dimension equalities is reindexing along their composite. -/
@[simp]
theorem cast_cast {n m k : ℕ} (h : n = m) (h' : m = k) (c : SingularCube X n) :
    cast h' (cast h c) = cast (h.trans h') c := by
  subst m k
  simp

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

/-- Faces commute with reindexing. -/
theorem face_cast {n m : ℕ} (h : n = m) (i : Fin (n + 1)) (t : I)
    (c : SingularCube X (n + 1)) :
    face (Fin.cast (congrArg Nat.succ h) i) t
        (cast (congrArg Nat.succ h) c) =
      cast h (face i t c) := by
  subst h
  simp

/-- The degeneracy along coordinate `i` forgets that coordinate before applying the cube. -/
def degeneracy {n : ℕ} (s : SingularCube X n) (i : Fin (n + 1)) : SingularCube X (n + 1) :=
  s.comp (ContinuousMap.precomp (X := fun _ : Fin (n + 1) ↦ I) i.succAbove)

/-- Evaluation of a degeneracy. -/
@[simp]
theorem degeneracy_apply {n : ℕ} (s : SingularCube X n) (i : Fin (n + 1))
    (x : Fin (n + 1) → I) : degeneracy s i x = s (Fin.removeNth i x) :=
  (rfl)

/-- Degeneracies commute with postcomposition by a continuous map. -/
@[simp]
theorem degeneracy_comp {n : ℕ} (f : C(X, Y)) (s : SingularCube X n) (i : Fin (n + 1)) :
    degeneracy (f.comp s) i = f.comp (degeneracy s i) := by
  ext x
  simp only [degeneracy_apply, ContinuousMap.comp_apply]

/-- A degeneracy followed by the face in the forgotten coordinate is the original cube. -/
@[simp]
theorem face_degeneracy_self {n : ℕ} (s : SingularCube X n) (i : Fin (n + 1)) (t : I) :
    face i t (degeneracy s i) = s := by
  ext x
  simp

/-- Degeneracies commute with reindexing along an equality of dimensions. -/
@[simp]
theorem degeneracy_cast {n m : ℕ} (h : n = m) (s : SingularCube X n) (i : Fin (n + 1)) :
    degeneracy (cast h s) (Fin.cast (congrArg Nat.succ h) i) =
      cast (congrArg Nat.succ h) (degeneracy s i) := by
  subst h
  simp

/-- Two degeneracies commute after reindexing the forgotten coordinates. -/
theorem degeneracy_degeneracy {n : ℕ} (s : SingularCube X n)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    degeneracy (degeneracy s i) j =
      degeneracy (degeneracy s (i.predAbove j)) (j.succAbove i) := by
  ext x
  simp only [degeneracy_apply]
  rw [Fin.removeNth_removeNth_eq_swap]

/-- A face in a coordinate other than the forgotten coordinate commutes with degeneracy. -/
@[simp]
theorem face_degeneracy_succAbove {n : ℕ} (s : SingularCube X (n + 1))
    (j : Fin (n + 2)) (i : Fin (n + 1)) (t : I) :
    face (j.succAbove i) t (degeneracy s j) = degeneracy (face i t s) (i.predAbove j) := by
  ext x
  simp only [face_apply, degeneracy_apply]
  congr 1
  funext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨k, rfl⟩
  · simp [Fin.removeNth]
  · simp only [Fin.removeNth]
    rw [← Fin.succAbove_succAbove_succAbove_predAbove j i k]
    simp only [Fin.insertNth_apply_succAbove, Fin.removeNth]

/-- A cube is **degenerate at the coordinate `i`** when it does not depend on it. -/
def IsDegenerateAt {n : ℕ} (c : SingularCube X n) (i : Fin n) : Prop :=
  ∀ (x : Fin n → I) (t : I), c (Function.update x i t) = c x

/-- A cube is **degenerate** when it does not depend on at least one of its coordinates (Massey's
convention). -/
def IsDegenerate {n : ℕ} (c : SingularCube X n) : Prop :=
  ∃ i, IsDegenerateAt c i

theorem isDegenerateAt_iff {n : ℕ} {c : SingularCube X n} {i : Fin n} :
    IsDegenerateAt c i ↔ ∀ (x : Fin n → I) (t : I), c (Function.update x i t) = c x :=
  Iff.rfl

theorem isDegenerate_iff {n : ℕ} {c : SingularCube X n} :
    IsDegenerate c ↔ ∃ i, IsDegenerateAt c i :=
  Iff.rfl

@[simp]
theorem IsDegenerateAt.apply_update {n : ℕ} {c : SingularCube X n} {i : Fin n}
    (h : IsDegenerateAt c i) (x : Fin n → I) (t : I) : c (Function.update x i t) = c x :=
  h x t

theorem IsDegenerateAt.isDegenerate {n : ℕ} {c : SingularCube X n} {i : Fin n}
    (h : IsDegenerateAt c i) : IsDegenerate c :=
  ⟨i, h⟩

/-- A degeneracy is independent of the coordinate it forgets. -/
@[simp]
theorem isDegenerateAt_degeneracy {n : ℕ} (s : SingularCube X n) (i : Fin (n + 1)) :
    IsDegenerateAt (degeneracy s i) i := by
  intro x t
  simp only [degeneracy_apply, Fin.removeNth_update]

/-- Every coordinate-forgetting degeneracy is a degenerate singular cube. -/
@[simp]
theorem isDegenerate_degeneracy {n : ℕ} (s : SingularCube X n) (i : Fin (n + 1)) :
    IsDegenerate (degeneracy s i) :=
  (isDegenerateAt_degeneracy s i).isDegenerate

/-- The degenerate singular cubes are exactly the images of degeneracy operators. -/
theorem isDegenerate_iff_exists_eq_degeneracy {n : ℕ} {s : SingularCube X (n + 1)} :
    IsDegenerate s ↔ ∃ (i : Fin (n + 1)) (t : SingularCube X n), s = degeneracy t i := by
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨i, face i 0 s, ?_⟩, ?_⟩
  · ext x
    simp only [degeneracy_apply, face_apply]
    rw [Fin.insertNth_removeNth]
    exact (hi x 0).symm
  · rintro ⟨i, t, rfl⟩
    exact (isDegenerateAt_degeneracy t i).isDegenerate

/-- A constant cube of positive dimension is degenerate. -/
@[simp]
theorem isDegenerate_const {n : ℕ} (x : X) :
    IsDegenerate (ContinuousMap.const (Fin (n + 1) → I) x) :=
  ⟨0, fun _ _ ↦ rfl⟩

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

/-- An injective continuous map reflects degeneracy in each coordinate. -/
theorem isDegenerateAt_comp_iff_of_injective {n : ℕ} (f : C(X, Y))
    (hf : Function.Injective f) (c : SingularCube X n) (i : Fin n) :
    IsDegenerateAt (f.comp c) i ↔ IsDegenerateAt c i :=
  ⟨fun h x t ↦ hf (h x t), fun h ↦ h.comp f⟩

/-- An injective continuous map preserves and reflects degeneracy. -/
theorem isDegenerate_comp_iff_of_injective {n : ℕ} (f : C(X, Y))
    (hf : Function.Injective f) (c : SingularCube X n) :
    IsDegenerate (f.comp c) ↔ IsDegenerate c := by
  simp only [isDegenerate_iff, isDegenerateAt_comp_iff_of_injective f hf]

/-- The two faces of a cube in a coordinate it does not depend on coincide. -/
theorem face_eq_of_isDegenerateAt {n : ℕ} {c : SingularCube X (n + 1)} {i : Fin (n + 1)}
    (h : IsDegenerateAt c i) (t t' : I) : face i t c = face i t' c := by
  ext x
  have := h (i.insertNth t' x) t
  rwa [Fin.update_insertNth, ← face_apply, ← face_apply] at this

/-- If a cube does not depend on its coordinate `j.succAbove k`, then its faces in the coordinate
`j` do not depend on their coordinate `k`. -/
theorem IsDegenerateAt.face_succAbove {n : ℕ} {c : SingularCube X (n + 1)} {j : Fin (n + 1)}
    {k : Fin n} (h : IsDegenerateAt c (j.succAbove k)) (t : I) : IsDegenerateAt (face j t c) k :=
  fun x s ↦ by rw [face_apply, face_apply, Fin.insertNth_update, h]

/-- If a cube does not depend on its `i`-th coordinate, then its faces in any other coordinate
`j ≠ i` are degenerate. -/
theorem isDegenerate_face_of_ne {n : ℕ} {c : SingularCube X (n + 1)} {i j : Fin (n + 1)}
    (h : IsDegenerateAt c i) (hij : i ≠ j) (t : I) : IsDegenerate (face j t c) := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
  exact (h.face_succAbove t).isDegenerate

end SingularCube

end TauCeti
