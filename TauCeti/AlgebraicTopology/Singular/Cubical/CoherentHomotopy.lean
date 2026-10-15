/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# Coherent homotopies of singular cubes

Deformations of all singular cubes of a space, such as `TauCeti.BasedCubeDeformation` and
`TauCeti.SubspaceCubeDeformation`, are built by induction on the dimension of the cubes. This file
holds the part of that induction that does not depend on where the cubes are deformed to.

A `TauCeti.CoherentCubeHomotopies X m` is a homotopy of every singular `m`-cube `c` of `X`,
starting at `c`, such that

* the homotopy of a cube not depending on a coordinate does not depend on it either;
* for every `(m + 1)`-cube, the homotopies of its faces agree where two faces meet.

The second property is what lets the homotopies of the faces of an `(m + 1)`-cube `c` glue to a
homotopy of the restriction of `c` to the boundary of the cube
(`TauCeti.CoherentCubeHomotopies.boundaryHomotopy`), to be extended over the whole cube. If `c`
does not depend on its coordinate `k`, its homotopy is instead read off its face in that coordinate
(`TauCeti.CoherentCubeHomotopies.degenerateHomotopy`). Homotopies of the `(m + 1)`-cubes that
restrict on every face to the homotopy of that face are again coherent
(`TauCeti.CoherentCubeHomotopies.coherent_of_homotopy_insertNth`).

The inductive constructions also leave a time window for each dimension in which the homotopies of
lower-dimensional cubes are stationary: those of cubes of dimension `k` are stationary from the time
`TauCeti.CoherentCubeHomotopies.threshold (k + 1) = (k + 1) / (k + 2)` on.

## Main definitions and results

* `TauCeti.CoherentCubeHomotopies`: coherent homotopies of all singular `m`-cubes.
* `TauCeti.CoherentCubeHomotopies.boundaryHomotopy`: the homotopy of the boundary of an
  `(m + 1)`-cube glued from the homotopies of its faces.
* `TauCeti.CoherentCubeHomotopies.degenerateHomotopy`: the homotopy of an `(m + 1)`-cube read off
  its face in one coordinate.
* `TauCeti.CoherentCubeHomotopies.coherent_of_homotopy_insertNth`: homotopies of the
  `(m + 1)`-cubes compatible with faces are coherent.
* `TauCeti.CoherentCubeHomotopies.threshold`: the times `k / (k + 1)` staggering the dimensions.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for singular cubes
  and their degeneracies.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- Deleting the coordinate `i` of the cube, as a continuous map `Iᵐ⁺¹ → Iᵐ`. -/
private def removeNthCM {m : ℕ} (i : Fin (m + 1)) : C(Fin (m + 1) → I, Fin m → I) :=
  ⟨i.removeNth, continuous_pi fun _ ↦ continuous_apply _⟩

variable (X) in
/-- **Coherent homotopies of the singular `m`-cubes of `X`**: a homotopy of every singular `m`-cube
`c`, with time as the first coordinate, starting at `c`, such that the homotopy of a cube not
depending on a coordinate does not depend on it either, and such that for every `(m + 1)`-cube the
homotopies of its faces agree where two faces meet. -/
structure CoherentCubeHomotopies (m : ℕ) where
  /-- The homotopy of the singular cube `c`. -/
  homotopy : SingularCube X m → C(I × (Fin m → I), X)
  /-- The homotopy of `c` starts at `c`. -/
  homotopy_zero : ∀ c y, homotopy c (0, y) = c y
  /-- If `c` does not depend on a coordinate, then neither does its homotopy at any time. -/
  isDegenerateAt_curry : ∀ c i, c.IsDegenerateAt i → ∀ s,
    SingularCube.IsDegenerateAt ((homotopy c).curry s) i
  /-- The homotopies of the faces of an `(m + 1)`-cube agree where two faces meet. -/
  coherent : ∀ (c : SingularCube X (m + 1)) (i j : Fin (m + 1)) (t u : I), (t = 0 ∨ t = 1) →
    (u = 0 ∨ u = 1) → ∀ z z' : Fin m → I, (i.insertNth t z : Fin (m + 1) → I) = j.insertNth u z' →
      ∀ s, homotopy (SingularCube.face i t c) (s, z) = homotopy (SingularCube.face j u c) (s, z')

namespace CoherentCubeHomotopies

attribute [simp] homotopy_zero

/-- The time `k / (k + 1)`. The inductive deformations of singular cubes make the homotopies of the
cubes of dimension `k` stationary from time `threshold (k + 1)` on, strictly before those of the
cubes of dimension `k + 1`, which leaves room for a further deformation in between. -/
def threshold (k : ℕ) : I :=
  ⟨k / (k + 1), div_nonneg k.cast_nonneg (by positivity),
    div_le_one_of_le₀ (by linarith) (by positivity)⟩

/-- The thresholds increase strictly with the dimension. -/
theorem threshold_lt_succ (k : ℕ) : threshold k < threshold (k + 1) := by
  change (k / (k + 1) : ℝ) < ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) + 1)
  push_cast
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- Every threshold is strictly before the end of the homotopies. -/
theorem threshold_lt_one (k : ℕ) : threshold k < 1 := by
  change (k / (k + 1) : ℝ) < 1
  rw [div_lt_one (by positivity)]
  linarith

variable {m : ℕ} (L : CoherentCubeHomotopies X m)

/-- The homotopy of the boundary of an `(m + 1)`-cube glued from the homotopies of its faces. -/
def boundaryHomotopy (c : SingularCube X (m + 1)) : C(I × Cube.boundary (Fin (m + 1)), X) where
  toFun q := L.homotopy (SingularCube.face q.2.2.choose (q.2.1 q.2.2.choose) c)
    (q.1, q.2.2.choose.removeNth q.2.1)
  continuous_toFun := by
    let e : Bool → I := fun b ↦ if b then 1 else 0
    let F : Fin (m + 1) × Bool → Set (I × Cube.boundary (Fin (m + 1))) :=
      fun jb ↦ {q | (q.2 : Fin (m + 1) → I) jb.1 = e jb.2}
    refine (locallyFinite_of_finite F).continuous ?_ (fun jb ↦ isClosed_eq
      ((continuous_apply jb.1).comp (continuous_subtype_val.comp continuous_snd))
      continuous_const) fun jb ↦ ?_
    · refine Set.eq_univ_of_forall fun q ↦ Set.mem_iUnion.2 ?_
      obtain ⟨j, hj⟩ := q.2.2
      rcases hj with hj | hj
      exacts [⟨(j, false), hj⟩, ⟨(j, true), hj⟩]
    · have hcont : Continuous fun q : I × Cube.boundary (Fin (m + 1)) ↦
          L.homotopy (SingularCube.face jb.1 (e jb.2) c)
            (q.1, jb.1.removeNth (q.2 : Fin (m + 1) → I)) :=
        (L.homotopy _).continuous.comp (continuous_fst.prodMk
          ((removeNthCM jb.1).continuous.comp (continuous_subtype_val.comp continuous_snd)))
      refine hcont.continuousOn.congr ?_
      intro q hq
      have hq : (q.2 : Fin (m + 1) → I) jb.1 = e jb.2 := hq
      refine L.coherent c _ jb.1 _ _ q.2.2.choose_spec (by cases jb.2 <;> simp [e]) _ _ ?_ q.1
      rw [Fin.insertNth_self_removeNth, ← hq, Fin.insertNth_self_removeNth]

/-- The glued boundary homotopy is read off any face containing the point. -/
theorem boundaryHomotopy_apply (c : SingularCube X (m + 1)) (s : I)
    (y : Cube.boundary (Fin (m + 1)))
    (j : Fin (m + 1)) (hj : (y : Fin (m + 1) → I) j = 0 ∨ (y : Fin (m + 1) → I) j = 1) :
    L.boundaryHomotopy c (s, y) = L.homotopy (SingularCube.face j ((y : Fin (m + 1) → I) j) c)
      (s, j.removeNth (y : Fin (m + 1) → I)) :=
  L.coherent c _ j _ _ y.2.choose_spec hj _ _
    (by rw [Fin.insertNth_self_removeNth, Fin.insertNth_self_removeNth]) s

/-- The glued boundary homotopy of `c` starts at the restriction of `c` to the boundary. -/
@[simp]
theorem boundaryHomotopy_zero (c : SingularCube X (m + 1)) (y : Cube.boundary (Fin (m + 1))) :
    L.boundaryHomotopy c (0, y) = c y := by
  obtain ⟨j, hj⟩ := y.2
  rw [L.boundaryHomotopy_apply c 0 y j hj, L.homotopy_zero, SingularCube.face_apply,
    Fin.insertNth_self_removeNth]

/-- The homotopy of an `(m + 1)`-cube `c` read off its face in the coordinate `k`, forgetting that
coordinate. When `c` does not depend on its coordinate `k`, this is a homotopy of `c`. -/
def degenerateHomotopy (c : SingularCube X (m + 1)) (k : Fin (m + 1)) :
    C(I × (Fin (m + 1) → I), X) :=
  (L.homotopy (SingularCube.face k 0 c)).comp ((ContinuousMap.id I).prodMap (removeNthCM k))

/-- Unfolding of `TauCeti.CoherentCubeHomotopies.degenerateHomotopy`. -/
@[simp]
theorem degenerateHomotopy_apply (c : SingularCube X (m + 1)) (k : Fin (m + 1)) (s : I)
    (y : Fin (m + 1) → I) :
    L.degenerateHomotopy c k (s, y) = L.homotopy (SingularCube.face k 0 c) (s, k.removeNth y) :=
  (rfl)

/-- If `c` does not depend on its coordinate `k`, the homotopy read off its face in that coordinate
restricts on each face of `c` to the homotopy of that face. -/
theorem degenerateHomotopy_insertNth {c : SingularCube X (m + 1)} {k : Fin (m + 1)}
    (hk : c.IsDegenerateAt k) (i : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) (s : I)
    (z : Fin m → I) :
    L.degenerateHomotopy c k (s, i.insertNth t z) =
      L.homotopy (SingularCube.face i t c) (s, z) := by
  rw [degenerateHomotopy_apply]
  rcases eq_or_ne i k with rfl | hik
  · rw [Fin.removeNth_insertNth, SingularCube.face_eq_of_isDegenerateAt hk 0 t]
  -- Move the coordinate `k` of the point to `0`, which changes neither side.
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hik.symm
  have hz := SingularCube.isDegenerateAt_iff.1
    (L.isDegenerateAt_curry _ k' (hk.face_succAbove t) s) z 0
  simp only [ContinuousMap.curry_apply] at hz
  rw [← hz, ← Fin.removeNth_update (i.succAbove k') 0, ← Fin.insertNth_update]
  refine L.coherent c _ i 0 t (Or.inl rfl) ht _ _ ?_ s
  rw [Fin.insertNth_removeNth, Function.update_eq_self_iff]
  simp

/-- The homotopy read off a face does not depend on any coordinate the cube does not depend on. -/
theorem isDegenerateAt_curry_degenerateHomotopy {c : SingularCube X (m + 1)}
    {k j : Fin (m + 1)} (hj : c.IsDegenerateAt j) (s : I) :
    SingularCube.IsDegenerateAt ((L.degenerateHomotopy c k).curry s) j := by
  refine SingularCube.isDegenerateAt_iff.2 fun y r ↦ ?_
  simp only [ContinuousMap.curry_apply, degenerateHomotopy_apply]
  rcases eq_or_ne j k with rfl | hjk
  · rw [Fin.removeNth_update]
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hjk
  rw [Fin.removeNth_update_succAbove]
  exact SingularCube.isDegenerateAt_iff.1
    (L.isDegenerateAt_curry _ j' (hj.face_succAbove 0) s) _ r

/-- **Coherence in the next dimension.** Homotopies `G` of the `(m + 1)`-cubes that restrict on
every face of a cube to the homotopy of that face are coherent: for every `(m + 2)`-cube, the
homotopies `G` of its faces agree where two faces meet. -/
theorem coherent_of_homotopy_insertNth (G : SingularCube X (m + 1) → C(I × (Fin (m + 1) → I), X))
    (hG : ∀ (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}, (t = 0 ∨ t = 1) → ∀ s z,
      G c (s, i.insertNth t z) = L.homotopy (SingularCube.face i t c) (s, z))
    (c : SingularCube X (m + 1 + 1)) (i j : Fin (m + 1 + 1)) (t u : I) (ht : t = 0 ∨ t = 1)
    (hu : u = 0 ∨ u = 1) (z z' : Fin (m + 1) → I)
    (h : (i.insertNth t z : Fin (m + 1 + 1) → I) = j.insertNth u z') (s : I) :
    G (SingularCube.face i t c) (s, z) = G (SingularCube.face j u c) (s, z') := by
  rcases eq_or_ne i j with rfl | hij
  · obtain ⟨rfl, rfl⟩ := Fin.insertNth_injective2 h
    rfl
  -- Two distinct faces of `c` meet in a face of codimension two, which is a face of each.
  obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
  obtain ⟨i', hi'⟩ := Fin.exists_succAbove_eq hij
  have hzj : z j' = u := by simpa using congrFun h (i.succAbove j')
  have hzi : t = z' i' := by
    have := congrFun h ((i.succAbove j').succAbove i')
    rwa [Fin.insertNth_apply_succAbove, hi', Fin.insertNth_apply_same] at this
  obtain ⟨w, rfl⟩ : ∃ w, z = j'.insertNth u w :=
    ⟨j'.removeNth z, by rw [← hzj, Fin.insertNth_self_removeNth]⟩
  obtain ⟨w', rfl⟩ : ∃ w', z' = i'.insertNth t w' :=
    ⟨i'.removeNth z', by rw [hzi, Fin.insertNth_self_removeNth]⟩
  rw [hG _ j' hu, hG _ i' ht, SingularCube.face_face]
  rw [Fin.insertNth_insertNth] at h
  exact L.coherent _ _ _ t t ht ht _ _ (Fin.insertNth_injective2 h).2 s

end CoherentCubeHomotopies

end TauCeti
