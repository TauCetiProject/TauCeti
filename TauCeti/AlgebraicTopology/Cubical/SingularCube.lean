/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# Singular cubes

A *singular `n`-cube* in a topological space `X` is a continuous map `Iⁿ → X`, where `I = [0, 1]`
and `Iⁿ` is modelled as `Fin n → I`. Singular cubes are the generators of the cubical singular
chain complex.

The face `s.face i t` of a singular `(n + 1)`-cube fixes its coordinate `i` to `t`; for `t = 0`
and `t = 1` these are the front and back faces `Aᵢ s` and `Bᵢ s` of Massey. The degeneracy
`s.degeneracy i` of a singular `n`-cube is the `(n + 1)`-cube that forgets its coordinate `i` and
then applies `s`.

A singular cube is *degenerate* when it does not depend on at least one of its coordinates. This
is Massey's convention, which is closed under the cross product of cubes; Serre's convention, which
only asks for independence of the last coordinate, is not. The degenerate cubes are exactly the
degeneracies (`SingularCube.isDegenerate_iff_exists_eq_degeneracy`), and a face of a degenerate
cube in any coordinate other than the one it forgets is again degenerate.

## Main definitions

* `TauCeti.SingularCube X n`: the singular `n`-cubes in `X`.
* `TauCeti.SingularCube.face`: the face of a cube in a given coordinate at a given height.
* `TauCeti.SingularCube.degeneracy`: the degeneracy of a cube along a given coordinate.
* `TauCeti.SingularCube.IsDegenerate`: the cube does not depend on one of its coordinates.

## Main results

* `TauCeti.SingularCube.face_face`: the cubical identity between faces.
* `TauCeti.SingularCube.face_degeneracy_self`: a degeneracy followed by the face in the same
  coordinate is the identity.
* `TauCeti.SingularCube.isDegenerate_iff_exists_eq_degeneracy`: the degenerate cubes are the
  degeneracies.
* `TauCeti.SingularCube.isDegenerate_face_degeneracy`: the faces of a degeneracy in the other
  coordinates are degenerate.

## References

* W. S. Massey, *Singular Homology Theory*, Chapter II.
* J.-P. Serre, *Homologie singulière des espaces fibrés*, Chapter II.
-/

public section

open scoped unitInterval

namespace TauCeti

/-- A **singular `n`-cube** in `X`: a continuous map from the cube `Iⁿ`. -/
abbrev SingularCube (X : Type*) [TopologicalSpace X] (n : ℕ) := C(Fin n → I, X)

namespace SingularCube

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {n : ℕ}

/-- The **face** of a singular `(n + 1)`-cube obtained by fixing its coordinate `i` to the value
`t`. For `t = 0` and `t = 1` these are Massey's front and back faces `Aᵢ` and `Bᵢ`. -/
def face (s : SingularCube X (n + 1)) (i : Fin (n + 1)) (t : I) : SingularCube X n :=
  s.comp ⟨fun x ↦ Fin.insertNth i t x, by fun_prop⟩

/-- Evaluation of a face. -/
@[simp]
lemma face_apply (s : SingularCube X (n + 1)) (i : Fin (n + 1)) (t : I) (x : Fin n → I) :
    s.face i t x = s (Fin.insertNth i t x) :=
  (rfl)

/-- The **degeneracy** of a singular `n`-cube along coordinate `i`: the `(n + 1)`-cube that
forgets its coordinate `i` and then applies `s`. -/
def degeneracy (s : SingularCube X n) (i : Fin (n + 1)) : SingularCube X (n + 1) :=
  s.comp ⟨fun x ↦ Fin.removeNth i x, continuous_pi fun _ ↦ continuous_apply _⟩

/-- Evaluation of a degeneracy. -/
@[simp]
lemma degeneracy_apply (s : SingularCube X n) (i : Fin (n + 1)) (x : Fin (n + 1) → I) :
    s.degeneracy i x = s (Fin.removeNth i x) :=
  (rfl)

/-- Faces commute with postcomposition by a continuous map. -/
@[simp]
lemma comp_face (f : C(X, Y)) (s : SingularCube X (n + 1)) (i : Fin (n + 1)) (t : I) :
    face (f.comp s) i t = f.comp (s.face i t) :=
  (rfl)

/-- Degeneracies commute with postcomposition by a continuous map. -/
@[simp]
lemma comp_degeneracy (f : C(X, Y)) (s : SingularCube X n) (i : Fin (n + 1)) :
    degeneracy (f.comp s) i = f.comp (s.degeneracy i) :=
  (rfl)

/-- The **cubical identity** between faces: for `i ≤ j`, taking the face in coordinate `j + 1`
and then the face in coordinate `i` agrees with taking the face in coordinate `i` and then the
face in coordinate `j`. -/
theorem face_face (s : SingularCube X (n + 2)) {i j : Fin (n + 1)} (h : i ≤ j) (a b : I) :
    (s.face j.succ b).face i a = (s.face i.castSucc a).face j b := by
  ext x
  simp only [face_apply]
  congr 1
  -- both sides are the tuple with `a` inserted at `i` and `b` at `j + 1`
  rw [eq_comm, Fin.insertNth_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [← Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.2 h),
      Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
  · rw [Fin.insertNth_eq_iff]
    simp only [Fin.removeNth]
    refine ⟨?_, funext fun k ↦ ?_⟩
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 h),
        Fin.insertNth_apply_same]
    · -- the simplicial identity `succAbove (castSucc i) ∘ succAbove j` =
      -- `succAbove (succ j) ∘ succAbove i` for `i ≤ j`
      have hk : i.castSucc.succAbove (j.succAbove k) = j.succ.succAbove (i.succAbove k) := by
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        rcases k with ⟨k, hk⟩
        simp only [Fin.le_def] at h
        simp only [Fin.succAbove, Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk]
        split_ifs <;> simp_all <;> omega
      rw [Fin.removeNth, Fin.removeNth, hk, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_succAbove]

/-- A degeneracy followed by the face in the same coordinate is the identity. -/
@[simp]
theorem face_degeneracy_self (s : SingularCube X n) (i : Fin (n + 1)) (t : I) :
    (s.degeneracy i).face i t = s := by
  ext x
  simp

/-- A singular cube is **degenerate** when it does not depend on at least one coordinate
(Massey's convention; it is closed under the cross product, unlike Serre's). -/
def IsDegenerate (s : SingularCube X n) : Prop :=
  ∃ i : Fin n, ∀ x y : Fin n → I, (∀ j, j ≠ i → x j = y j) → s x = s y

/-- A singular `0`-cube is never degenerate. -/
theorem not_isDegenerate_zero (s : SingularCube X 0) : ¬ s.IsDegenerate :=
  fun ⟨i, _⟩ ↦ i.elim0

/-- Postcomposing a degenerate cube with a continuous map gives a degenerate cube. -/
theorem IsDegenerate.comp {s : SingularCube X n} (hs : s.IsDegenerate) (f : C(X, Y)) :
    IsDegenerate (f.comp s) := by
  obtain ⟨i, hi⟩ := hs
  exact ⟨i, fun x y hxy ↦ congrArg f (hi x y hxy)⟩

/-- A degeneracy does not depend on the coordinate it forgets. -/
private lemma degeneracy_apply_eq {s : SingularCube X n} {i : Fin (n + 1)}
    {x y : Fin (n + 1) → I} (hxy : ∀ j, j ≠ i → x j = y j) :
    s.degeneracy i x = s.degeneracy i y := by
  simp only [degeneracy_apply]
  congr 1
  funext k
  exact hxy _ (Fin.succAbove_ne i k)

/-- A degeneracy is degenerate. -/
theorem isDegenerate_degeneracy (s : SingularCube X n) (i : Fin (n + 1)) :
    (s.degeneracy i).IsDegenerate :=
  ⟨i, fun _ _ hxy ↦ degeneracy_apply_eq hxy⟩

/-- The degenerate singular `(n + 1)`-cubes are exactly the degeneracies of singular
`n`-cubes. -/
theorem isDegenerate_iff_exists_eq_degeneracy {s : SingularCube X (n + 1)} :
    s.IsDegenerate ↔ ∃ (i : Fin (n + 1)) (t : SingularCube X n), s = t.degeneracy i := by
  refine ⟨fun ⟨i, hi⟩ ↦ ⟨i, s.face i 0, ?_⟩, ?_⟩
  · ext x
    refine hi _ _ fun j hj ↦ ?_
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    simp [Fin.removeNth]
  · rintro ⟨i, t, rfl⟩
    exact t.isDegenerate_degeneracy i

/-- The face of a degeneracy in any coordinate other than the forgotten one is degenerate. -/
theorem isDegenerate_face_degeneracy (s : SingularCube X n) {i j : Fin (n + 1)}
    (h : j ≠ i) (t : I) : ((s.degeneracy i).face j t).IsDegenerate := by
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h.symm
  refine ⟨k, fun x y hxy ↦ ?_⟩
  simp only [face_apply]
  refine degeneracy_apply_eq fun l hl ↦ ?_
  rcases Fin.eq_self_or_eq_succAbove j l with rfl | ⟨m, rfl⟩
  · simp
  · simp only [Fin.insertNth_apply_succAbove]
    exact hxy m fun hm ↦ hl (hm ▸ rfl)

end SingularCube

end TauCeti
