/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk
public import TauCeti.AlgebraicTopology.Singular.Cubical.CoherentHomotopy

/-!
# Deforming singular cubes into a subspace

Let `A` be a subset of a space `X` and let `n ∈ ℕ∞`. Suppose that `A` is **compressible** in `X`
below dimension `n`, in the sense of Hatcher's compression lemma: every singular cube `c : Iᵐ → X`
with `m < n` sending the boundary of the cube into `A` is homotopic, relative to that boundary, to
a cube with values in `A`. For `m = 0` the boundary is empty, so this says that every point of `X`
is joined by a path to a point of `A`.

This file shows that the singular cubes of `X` then deform coherently, into `A` below dimension
`n`: there is a `TauCeti.SubspaceCubeDeformation A n`, a homotopy of each singular cube `c`
starting at `c`, ending at a cube with values in `A` when the dimension of `c` is less than `n`,
such that

* the homotopy of a face of `c` is the restriction of the homotopy of `c` to that face;
* the homotopy of a cube not depending on a coordinate does not depend on it either;
* the homotopy of a cube with values in `A` is constant.

For `n = ⊤` every singular cube deforms into `A`. Conversely such a deformation compresses every
cube of dimension less than `n` whose boundary lies in `A`, relative to the boundary, so it exists
exactly when `A` is compressible in `X` below dimension `n`
(`TauCeti.nonempty_subspaceCubeDeformation_iff`). By the compression lemma for disks, `A` is
compressible below dimension `n` as soon as every point of `X` is joined by a path to `A` and the
relative homotopy sets `π_{k+1}(X, A, a)` are trivial for every `k + 1 < n` and every `a ∈ A`
(`TauCeti.nonempty_subspaceCubeDeformation_of_relHomotopyGroup`). For `n = ⊤` this is the case for
the bottom face of the mapping cylinder of a weak homotopy equivalence.

The three properties above are what the prism operators of the homotopies need to deform the
normalized cubical chains of `X` by a map chain homotopic to the identity, in the same way as
`TauCeti.BasedCubeDeformation` retracts them onto the based cubes. For `n = ⊤` this retracts them
onto the chains of `A`; applied to the mapping cylinder, this is the input for the invariance of
singular homology under weak homotopy equivalences (Hatcher, Proposition 4.21). For finite `n` it
shows that the relative homology of `(X, A)` vanishes below degree `n`.

## Construction

The homotopies are built by induction on the dimension of the cubes. The homotopy of a cube with
values in `A` is constant, and that of a degenerate cube is read off one of its faces. For any
other `(m + 1)`-cube `c`, the homotopies of the faces of `c` agree where two faces meet, so they
glue to a homotopy of the restriction of `c` to the boundary of the cube, and the homotopy
extension property of the boundary (`TauCeti.hasHomotopyExtensionProperty_cubeBoundary`) extends
it to a homotopy of `c`. If `m + 1 < n`, the boundary homotopy has reached its end, with values in
`A`, by some time `a`; at that time the extension is a cube with boundary in `A`, which is then
compressed into `A` relative to the boundary. To leave room for these compressions, the homotopies
of cubes of dimension `k < n` are stationary from the time `(k + 1) / (k + 2)` on.
The gluing of the face homotopies, the homotopies of degenerate cubes and the coherence of each
new dimension come from `TauCeti.CoherentCubeHomotopies`.

## Main definitions and results

* `TauCeti.SubspaceCubeDeformation`: a coherent deformation of all singular cubes, into `A` below
  dimension `n`.
* `TauCeti.subspaceCubeDeformation`: such a deformation when `A` is compressible in `X` below
  dimension `n`.
* `TauCeti.SubspaceCubeDeformation.homotopicRel`: such a deformation deforms each cube with
  boundary in `A` relative to the boundary.
* `TauCeti.nonempty_subspaceCubeDeformation_iff`: such a deformation exists exactly when `A` is
  compressible in `X` below dimension `n`.
* `TauCeti.SingularCube.exists_homotopicRel_range_subset_of_subsingleton`: a singular cube with
  boundary in `A` compresses into `A` when the relative homotopy sets in its dimension vanish.
* `TauCeti.nonempty_subspaceCubeDeformation_of_relHomotopyGroup`: the deformation exists when the
  relative homotopy sets vanish below dimension `n`.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  deformation of singular chains into the subcomplex of a subspace.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.6 (the compression lemma) and Proposition 4.21 (a weak homotopy
  equivalence induces isomorphisms on homology).
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for singular cubes
  and their degeneracies.
-/

public section

noncomputable section

open Set unitInterval

namespace TauCeti

open CoherentCubeHomotopies

variable {X : Type*} [TopologicalSpace X] {A : Set X} {n : ℕ∞}

/-! ### Extending the deformation over a single cube -/

variable (hA : ∀ m : ℕ, (m : ℕ∞) < n → ∀ c : SingularCube X m,
  MapsTo c (Cube.boundary (Fin m)) A →
    ∃ c' : SingularCube X m, c.HomotopicRel c' (Cube.boundary (Fin m)) ∧ range c' ⊆ A)

include hA in
/-- **The inductive step for a single cube.** Let `c` be a singular `m`-cube and `B` a homotopy of
its restriction to the boundary of the cube. Then `B` extends to a homotopy of `c`. If moreover
`m < n`, and `B` ends in `A` and is stationary from time `threshold m` on, then the extension can
be chosen to end at a cube with values in `A` and to be stationary from time `threshold (m + 1)`
on. -/
private lemma exists_extension {m : ℕ} (c : SingularCube X m)
    (B : C(I × Cube.boundary (Fin m), X)) (hB₀ : ∀ y, B (0, y) = c y)
    (hB₁ : (m : ℕ∞) < n → ∀ y, B (1, y) ∈ A)
    (hB : (m : ℕ∞) < n → ∀ s : I, threshold m ≤ s → ∀ y, B (s, y) = B (1, y)) :
    ∃ G : C(I × (Fin m → I), X), (∀ y, G (0, y) = c y) ∧
      (∀ s (y : Cube.boundary (Fin m)), G (s, y) = B (s, y)) ∧
      ((m : ℕ∞) < n → ∀ y, G (1, y) ∈ A) ∧
      ((m : ℕ∞) < n → ∀ s : I, threshold (m + 1) ≤ s → ∀ y, G (s, y) = G (1, y)) := by
  have hcl : IsClosed (Cube.boundary (Fin m)) := hasHomotopyExtensionProperty_cubeBoundary.isClosed
  obtain ⟨G₀, hG₀, hG₀B⟩ :=
    hasHomotopyExtensionProperty_cubeBoundary.exists_extension_of_isClosed hcl c B hB₀
  by_cases hm : (m : ℕ∞) < n
  swap
  · exact ⟨G₀, hG₀, hG₀B, fun h ↦ absurd h hm, fun h ↦ absurd h hm⟩
  replace hB₁ := hB₁ hm
  replace hB := hB hm
  -- At time `a` the extension sends the boundary into `A`; compress it into `A` during the times
  -- `[a, b]`, relative to the boundary.
  set a := threshold m
  set b := threshold (m + 1)
  have hab : (a : ℝ) < b := threshold_lt_succ m
  have hBa (y : Cube.boundary (Fin m)) : G₀ (a, y) = B (1, y) := (hG₀B a y).trans (hB a le_rfl y)
  obtain ⟨c', ⟨K⟩, hc'⟩ := hA m hm (G₀.curry a) fun y hy ↦ by
    simpa [hBa ⟨y, hy⟩] using hB₁ ⟨y, hy⟩
  let ψ : C(I, I) := ⟨fun s ↦ Set.projIcc 0 1 zero_le_one (((s : ℝ) - a) / (b - a)), by fun_prop⟩
  have hψ₀ {s : I} (hs : (s : ℝ) ≤ a) : ψ s = 0 :=
    Set.projIcc_of_le_left zero_le_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hψ₁ {s : I} (hs : (b : ℝ) ≤ s) : ψ s = 1 :=
    Set.projIcc_of_right_le zero_le_one ((one_le_div (by linarith)).2 (by linarith))
  have hb1 : ¬ ((1 : I) : ℝ) ≤ a := not_le.2 (threshold_lt_one m)
  refine ⟨⟨fun q ↦ if (q.1 : ℝ) ≤ a then G₀ q else K (ψ q.1, q.2), ?_⟩, fun y ↦ ?_,
    fun s y ↦ ?_, fun _ y ↦ ?_, fun _ s hs y ↦ ?_⟩
  · refine Continuous.if_le G₀.continuous (by fun_prop) (by fun_prop) continuous_const
      fun q hq ↦ ?_
    rw [hψ₀ hq.le, K.apply_zero]
    exact congrArg G₀ (Prod.ext (Subtype.ext hq) rfl)
  · simp [hG₀]
  · dsimp only [ContinuousMap.coe_mk]
    split_ifs with hs
    · exact hG₀B s y
    · rw [K.eq_fst _ y.2, ContinuousMap.curry_apply, hBa]
      exact (hB s (Subtype.coe_le_coe.1 (not_le.1 hs).le) y).symm
  · simp only [ContinuousMap.coe_mk, hb1, ite_false]
    rw [hψ₁ (by exact_mod_cast b.2.2), K.apply_one]
    exact hc' ⟨y, rfl⟩
  · have hs' : ¬ (s : ℝ) ≤ a := not_le.2 (hab.trans_le hs)
    simp only [ContinuousMap.coe_mk, hs', hb1, ite_false]
    rw [hψ₁ hs, hψ₁ (by exact_mod_cast b.2.2)]

/-! ### Deforming all cubes of one dimension -/

variable (A n) in
/-- Homotopies of all singular `m`-cubes, into `A` if `m < n`, with the properties maintained by
the inductive construction on top of coherence. -/
private structure Level (m : ℕ) extends CoherentCubeHomotopies X m where
  apply_of_range_subset : ∀ c : SingularCube X m, range c ⊆ A → ∀ s y, homotopy c (s, y) = c y
  apply_one_mem : (m : ℕ∞) < n → ∀ c y, homotopy c (1, y) ∈ A
  apply_of_le : (m : ℕ∞) < n → ∀ c (s : I), threshold (m + 1) ≤ s → ∀ y,
    homotopy c (s, y) = homotopy c (1, y)

namespace Level

variable {m : ℕ}

private lemma bdry_one_mem (L : Level A n m) (c : SingularCube X (m + 1))
    (hm : ((m + 1 : ℕ) : ℕ∞) < n) (y : Cube.boundary (Fin (m + 1))) :
    L.boundaryHomotopy c (1, y) ∈ A := by
  obtain ⟨j, hj⟩ := y.2
  rw [L.boundaryHomotopy_apply c 1 y j hj]
  exact L.apply_one_mem ((Nat.cast_le.2 m.le_succ).trans_lt hm) _ _

private lemma bdry_of_le (L : Level A n m) (c : SingularCube X (m + 1))
    (hm : ((m + 1 : ℕ) : ℕ∞) < n) (s : I) (hs : threshold (m + 1) ≤ s)
    (y : Cube.boundary (Fin (m + 1))) :
    L.boundaryHomotopy c (s, y) = L.boundaryHomotopy c (1, y) := by
  obtain ⟨j, hj⟩ := y.2
  rw [L.boundaryHomotopy_apply c s y j hj, L.boundaryHomotopy_apply c 1 y j hj]
  exact L.apply_of_le ((Nat.cast_le.2 m.le_succ).trans_lt hm) _ s hs _

include hA

open Classical in
/-- The homotopies of the `(m + 1)`-cubes: constant on cubes with values in `A`, read off a face on
degenerate cubes, and otherwise extended from the glued homotopies of the faces. -/
private def nextH (L : Level A n m) (c : SingularCube X (m + 1)) : C(I × (Fin (m + 1) → I), X) :=
  if range c ⊆ A then c.comp ContinuousMap.snd
  else if hd : c.IsDegenerate then
    L.degenerateHomotopy c (SingularCube.isDegenerate_iff.1 hd).choose
  else (exists_extension hA c (L.boundaryHomotopy c) (L.boundaryHomotopy_zero c) (L.bdry_one_mem c)
    (L.bdry_of_le c)).choose

private lemma nextH_of_range_subset (L : Level A n m) {c : SingularCube X (m + 1)}
    (hc : range c ⊆ A) (s : I) (y : Fin (m + 1) → I) : nextH hA L c (s, y) = c y := by
  simp [nextH, hc]

private lemma nextH_of_isDegenerate (L : Level A n m) {c : SingularCube X (m + 1)}
    (hc : ¬ range c ⊆ A) (hd : c.IsDegenerate) :
    nextH hA L c = L.degenerateHomotopy c (SingularCube.isDegenerate_iff.1 hd).choose := by
  simp [nextH, hc, hd]

private lemma nextH_spec (L : Level A n m) {c : SingularCube X (m + 1)} (hc : ¬ range c ⊆ A)
    (hd : ¬ c.IsDegenerate) :
    let G := nextH hA L c
    (∀ y, G (0, y) = c y) ∧
      (∀ s (y : Cube.boundary (Fin (m + 1))), G (s, y) = L.boundaryHomotopy c (s, y)) ∧
      (((m + 1 : ℕ) : ℕ∞) < n → ∀ y, G (1, y) ∈ A) ∧
      (((m + 1 : ℕ) : ℕ∞) < n → ∀ s : I, threshold (m + 1 + 1) ≤ s → ∀ y,
        G (s, y) = G (1, y)) := by
  simp only [nextH, hc, hd, dite_false, ite_false]
  exact (exists_extension hA c (L.boundaryHomotopy c) (L.boundaryHomotopy_zero c) (L.bdry_one_mem c)
    (L.bdry_of_le c)).choose_spec

/-- The homotopies of the `(m + 1)`-cubes restrict on faces to the homotopies of the faces. -/
private lemma nextH_insertNth (L : Level A n m) (c : SingularCube X (m + 1)) (i : Fin (m + 1))
    {t : I} (ht : t = 0 ∨ t = 1) (s : I) (z : Fin m → I) :
    nextH hA L c (s, i.insertNth t z) = L.homotopy (SingularCube.face i t c) (s, z) := by
  by_cases hr : range c ⊆ A
  · rw [nextH_of_range_subset hA L hr,
      L.apply_of_range_subset _ ((SingularCube.range_face_subset i t c).trans hr),
      SingularCube.face_apply]
  by_cases hd : c.IsDegenerate
  · rw [nextH_of_isDegenerate hA L hr hd,
      L.degenerateHomotopy_insertNth (SingularCube.isDegenerate_iff.1 hd).choose_spec i ht]
  have hy : (i.insertNth t z : Fin (m + 1) → I) ∈ Cube.boundary (Fin (m + 1)) :=
    ⟨i, by rwa [Fin.insertNth_apply_same]⟩
  rw [(nextH_spec hA L hr hd).2.1 s ⟨_, hy⟩,
    L.boundaryHomotopy_apply c s ⟨_, hy⟩ i (by simpa using ht)]
  simp

/-- The `(m + 1)`-st level of the construction, built from the `m`-th. -/
private def next (L : Level A n m) : Level A n (m + 1) where
  homotopy := nextH hA L
  homotopy_zero c y := by
    by_cases hr : range c ⊆ A
    · exact nextH_of_range_subset hA L hr 0 y
    by_cases hd : c.IsDegenerate
    · rw [nextH_of_isDegenerate hA L hr hd, degenerateHomotopy_apply, L.homotopy_zero,
        SingularCube.face_apply, Fin.insertNth_removeNth]
      exact (SingularCube.isDegenerate_iff.1 hd).choose_spec.apply_update y 0
    · exact (nextH_spec hA L hr hd).1 y
  apply_of_range_subset _ hc s y := nextH_of_range_subset hA L hc s y
  apply_one_mem hm c y := by
    by_cases hr : range c ⊆ A
    · rw [nextH_of_range_subset hA L hr]
      exact hr ⟨y, rfl⟩
    by_cases hd : c.IsDegenerate
    · rw [nextH_of_isDegenerate hA L hr hd, degenerateHomotopy_apply]
      exact L.apply_one_mem ((Nat.cast_le.2 m.le_succ).trans_lt hm) _ _
    · exact (nextH_spec hA L hr hd).2.2.1 hm y
  isDegenerateAt_curry c j hj s := by
    by_cases hr : range c ⊆ A
    · refine SingularCube.isDegenerateAt_iff.2 fun y r ↦ ?_
      simp only [ContinuousMap.curry_apply, nextH_of_range_subset hA L hr]
      exact hj.apply_update y r
    rw [nextH_of_isDegenerate hA L hr hj.isDegenerate]
    exact L.isDegenerateAt_curry_degenerateHomotopy hj s
  apply_of_le hm c s hs y := by
    by_cases hr : range c ⊆ A
    · rw [nextH_of_range_subset hA L hr, nextH_of_range_subset hA L hr]
    by_cases hd : c.IsDegenerate
    · rw [nextH_of_isDegenerate hA L hr hd, degenerateHomotopy_apply, degenerateHomotopy_apply]
      exact L.apply_of_le ((Nat.cast_le.2 m.le_succ).trans_lt hm) _ s
        (Subtype.coe_le_coe.1 ((threshold_lt_succ (m + 1)).le.trans hs)) _
    · exact (nextH_spec hA L hr hd).2.2.2 hm s hs y
  coherent :=
    L.coherent_of_homotopy_insertNth (nextH hA L) fun c i _ ht ↦ nextH_insertNth hA L c i ht

end Level

include hA in
private lemma exists_extension_zero (c : SingularCube X 0) :
    ∃ G : C(I × (Fin 0 → I), X), (∀ y, G (0, y) = c y) ∧ ((0 : ℕ∞) < n → ∀ y, G (1, y) ∈ A) ∧
      ((0 : ℕ∞) < n → ∀ s : I, threshold (0 + 1) ≤ s → ∀ y, G (s, y) = G (1, y)) := by
  -- The boundary of the `0`-cube is empty, so any homotopy of it will do.
  have hb (y : Cube.boundary (Fin 0)) : False := by simpa using y.2
  obtain ⟨G, hG₀, -, hG⟩ := exists_extension hA c
    ⟨fun q ↦ (hb q.2).elim, continuous_of_const fun q ↦ (hb q.2).elim⟩ (fun y ↦ (hb y).elim)
    (fun _ y ↦ (hb y).elim) fun _ _ _ y ↦ (hb y).elim
  exact ⟨G, hG₀, hG⟩

open Classical in
/-- The homotopies of points: constant on the points of `A`, and otherwise, if `0 < n`, a path into
`A` reaching it by time `1 / 2`. -/
private def baseH (c : SingularCube X 0) : C(I × (Fin 0 → I), X) :=
  if range c ⊆ A then c.comp ContinuousMap.snd else (exists_extension_zero hA c).choose

include hA in
private lemma baseH_of_range_subset {c : SingularCube X 0} (hc : range c ⊆ A) (s : I)
    (y : Fin 0 → I) : baseH hA c (s, y) = c y := by
  simp [baseH, hc]

include hA in
private lemma baseH_spec {c : SingularCube X 0} (hc : ¬ range c ⊆ A) :
    let G := baseH hA c
    (∀ y, G (0, y) = c y) ∧ ((0 : ℕ∞) < n → ∀ y, G (1, y) ∈ A) ∧
      ((0 : ℕ∞) < n → ∀ s : I, threshold (0 + 1) ≤ s → ∀ y, G (s, y) = G (1, y)) := by
  simp only [baseH, hc, ite_false]
  exact (exists_extension_zero hA c).choose_spec

/-- The `0`-th level of the construction. -/
private def base : Level A n 0 where
  homotopy := baseH hA
  homotopy_zero c y := by
    by_cases hr : range c ⊆ A
    · exact baseH_of_range_subset hA hr 0 y
    · exact (baseH_spec hA hr).1 y
  apply_of_range_subset _ hc s y := baseH_of_range_subset hA hc s y
  apply_one_mem hn c y := by
    by_cases hr : range c ⊆ A
    · rw [baseH_of_range_subset hA hr]
      exact hr ⟨y, rfl⟩
    · exact (baseH_spec hA hr).2.1 (by exact_mod_cast hn) y
  isDegenerateAt_curry _ i := i.elim0
  apply_of_le hn c s hs y := by
    by_cases hr : range c ⊆ A
    · rw [baseH_of_range_subset hA hr, baseH_of_range_subset hA hr]
    · exact (baseH_spec hA hr).2.2 (by exact_mod_cast hn) s hs y
  coherent c i j t u _ _ z z' h s := by
    obtain rfl : i = j := Fin.ext (by omega)
    obtain ⟨rfl, rfl⟩ := Fin.insertNth_injective2 h
    rfl

/-- All levels of the construction, built by recursion on the dimension. -/
private def levels : ∀ m, Level A n m
  | 0 => base hA
  | m + 1 => (levels m).next hA

/-! ### The deformation -/

variable (A n) in
/-- A **deformation of the singular cubes of `X` into `A` below dimension `n`**: a homotopy of
every singular cube `c`, with time as the first coordinate, starting at `c`, and ending at a cube
with values in `A` when the dimension of `c` is less than `n`. The homotopies are compatible with
faces and degeneracies, and fix the cubes that already have values in `A`. For `n = ⊤` every cube
deforms into `A`. -/
structure SubspaceCubeDeformation where
  /-- The homotopy deforming the singular cube `c`. -/
  homotopy {m : ℕ} (c : SingularCube X m) : C(I × (Fin m → I), X)
  /-- The homotopy of `c` starts at `c`. -/
  homotopy_zero {m : ℕ} (c : SingularCube X m) (y : Fin m → I) : homotopy c (0, y) = c y
  /-- The homotopy of a cube of dimension less than `n` ends at a cube with values in `A`. -/
  homotopy_one_mem {m : ℕ} (hm : (m : ℕ∞) < n) (c : SingularCube X m) (y : Fin m → I) :
    homotopy c (1, y) ∈ A
  /-- The homotopy of a face of `c` is the restriction of the homotopy of `c` to that face. -/
  homotopy_insertNth {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) (s : I) (z : Fin m → I) :
    homotopy c (s, i.insertNth t z) = homotopy (SingularCube.face i t c) (s, z)
  /-- If `c` does not depend on a coordinate, then neither does its homotopy at any time. -/
  isDegenerateAt_curry {m : ℕ} {c : SingularCube X m} {i : Fin m} (hc : c.IsDegenerateAt i)
    (s : I) : SingularCube.IsDegenerateAt ((homotopy c).curry s) i
  /-- The homotopy of a cube with values in `A` is constant. -/
  homotopy_of_range_subset {m : ℕ} {c : SingularCube X m} (hc : range c ⊆ A) (s : I)
    (y : Fin m → I) : homotopy c (s, y) = c y

attribute [simp] SubspaceCubeDeformation.homotopy_zero SubspaceCubeDeformation.homotopy_insertNth
  SubspaceCubeDeformation.homotopy_of_range_subset

/-- **Below dimension `n`, the singular cubes deform into a compressible subspace.** If every
singular cube of `X` of dimension less than `n` with boundary in `A` is homotopic, relative to the
boundary of the cube, to a cube with values in `A`, then there is a deformation of the singular
cubes of `X` into `A` below dimension `n`, compatible with faces and degeneracies and fixing the
cubes with values in `A`. -/
def subspaceCubeDeformation : SubspaceCubeDeformation A n where
  homotopy {m} c := (levels hA m).homotopy c
  homotopy_zero {m} c y := (levels hA m).homotopy_zero c y
  homotopy_one_mem {m} hm c y := (levels hA m).apply_one_mem hm c y
  homotopy_insertNth {m} c i _ ht s z := Level.nextH_insertNth hA (levels hA m) c i ht s z
  isDegenerateAt_curry {m} c i hc s := (levels hA m).isDegenerateAt_curry c i hc s
  homotopy_of_range_subset {m} c hc s y := (levels hA m).apply_of_range_subset c hc s y

omit hA in
/-- The homotopy of a cube with boundary in `A` is relative to the boundary of the cube. Below
dimension `n` it ends at a cube with values in `A`, so it compresses the cube into `A`. -/
theorem SubspaceCubeDeformation.homotopicRel (D : SubspaceCubeDeformation A n) {m : ℕ}
    {c : SingularCube X m} (hc : MapsTo c (Cube.boundary (Fin m)) A) :
    c.HomotopicRel ((D.homotopy c).curry 1) (Cube.boundary (Fin m)) := by
  -- On the boundary the homotopy follows the homotopies of the faces of `c`, which have values
  -- in `A` and hence are constant.
  have hbd (s : I) (y : Fin m → I) (hy : y ∈ Cube.boundary (Fin m)) :
      D.homotopy c (s, y) = c y := by
    cases m with
    | zero => simp at hy
    | succ _ =>
      obtain ⟨i, hi⟩ := hy
      have hface : range (SingularCube.face i (y i) c) ⊆ A := by
        rintro _ ⟨z, rfl⟩
        rw [SingularCube.face_apply]
        exact hc ⟨i, by simpa using hi⟩
      rw [← Fin.insertNth_self_removeNth i y, D.homotopy_insertNth _ _ hi,
        D.homotopy_of_range_subset hface, SingularCube.face_apply]
  exact ⟨{ toFun := D.homotopy c
           map_zero_left := D.homotopy_zero c
           map_one_left _ := rfl
           prop' := fun s y hy ↦ hbd s y hy }⟩

omit hA in
/-- **The singular cubes of `X` deform into `A` below dimension `n` exactly when `A` is
compressible in `X` below dimension `n`**: when every singular cube of dimension less than `n`
with boundary in `A` is homotopic, relative to the boundary of the cube, to a cube with values in
`A`. -/
theorem nonempty_subspaceCubeDeformation_iff :
    Nonempty (SubspaceCubeDeformation A n) ↔
      ∀ m : ℕ, (m : ℕ∞) < n → ∀ c : SingularCube X m, MapsTo c (Cube.boundary (Fin m)) A →
        ∃ c' : SingularCube X m, c.HomotopicRel c' (Cube.boundary (Fin m)) ∧ range c' ⊆ A := by
  refine ⟨fun ⟨D⟩ _ hm c hc ↦ ⟨_, D.homotopicRel hc, ?_⟩,
    fun hA ↦ ⟨subspaceCubeDeformation hA⟩⟩
  rintro _ ⟨y, rfl⟩
  exact D.homotopy_one_mem hm c y

/-! ### Compressibility from relative homotopy groups -/

section RelHomotopyGroup

variable {X : TopCat} {A : Set X}

omit hA in
/-- **Compressing a singular cube.** Let `A ⊆ X` be such that the relative homotopy set
`π_{n+1}(X, A, a)` is trivial for every `a ∈ A`. Then every singular `(n + 1)`-cube of `X` sending
the boundary of the cube into `A` is homotopic, relative to that boundary, to a cube with values
in `A`. -/
theorem SingularCube.exists_homotopicRel_range_subset_of_subsingleton {n : ℕ}
    (h : ∀ a : A, Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset A, a⟩))
    (c : SingularCube X (n + 1)) (hc : MapsTo c (Cube.boundary (Fin (n + 1))) A) :
    ∃ c' : SingularCube X (n + 1),
      c.HomotopicRel c' (Cube.boundary (Fin (n + 1))) ∧ range c' ⊆ A := by
  -- Read `c` on the closed unit ball of the sup norm, whose unit sphere is the boundary.
  let e := cubeHomeomorphClosedBall (Fin (n + 1))
  have he (y : Fin (n + 1) → I) :
      (e y : Fin (n + 1) → ℝ) ∈ Metric.sphere 0 1 ↔ y ∈ Cube.boundary (Fin (n + 1)) := by
    rw [mem_sphere_zero_iff_norm, norm_cubeHomeomorphClosedBall_eq_one_iff]
  obtain ⟨g', ⟨F⟩, hg'⟩ := TauCeti.exists_homotopicRel_range_subset_of_subsingleton h
    (c.comp (e.symm : C(_, Fin (n + 1) → I))) fun z hz ↦ hc <| by
      rw [← he]
      simpa using hz
  refine ⟨g'.comp (e : C(Fin (n + 1) → I, _)),
    ⟨{ toFun q := F (q.1, e q.2)
       map_zero_left y := by simp
       map_one_left y := by simp
       prop' s y hy := by
         simpa using F.prop s (e y) ((he y).2 hy) }⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hg' ⟨e y, rfl⟩

omit hA in
/-- **The singular cubes deform into `A` below dimension `n` when the relative homotopy sets
vanish below `n`.** If every point of `X` is joined by a path to a point of `A`, and the relative
homotopy set `π_{k+1}(X, A, a)` is trivial for every `k + 1 < n` and every `a ∈ A`, then there is
a deformation of the singular cubes of `X` into `A` below dimension `n`. -/
theorem nonempty_subspaceCubeDeformation_of_relHomotopyGroup
    (h₀ : ∀ x : X, ∃ a ∈ A, Joined x a)
    (h : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < n → ∀ a : A,
      Subsingleton (RelHomotopyGroup (Fin k) ⟨TopPair.ofSubset A, a⟩)) :
    Nonempty (SubspaceCubeDeformation A n) := by
  refine nonempty_subspaceCubeDeformation_iff.2 fun m hm c hc ↦ ?_
  cases m with
  | zero =>
    -- The `0`-cube is a point, and its boundary is empty: join its value to `A` by a path.
    obtain ⟨a, ha, ⟨γ⟩⟩ := h₀ (c default)
    refine ⟨ContinuousMap.const _ a,
      ⟨{ toFun q := γ q.1
         map_zero_left y := by rw [γ.source]; exact congrArg c (Subsingleton.elim _ _)
         map_one_left _ := γ.target
         prop' _ y hy := by simp at hy }⟩, ?_⟩
    rintro _ ⟨_, rfl⟩
    exact ha
  | succ k => exact SingularCube.exists_homotopicRel_range_subset_of_subsingleton (h k hm) c hc

end RelHomotopyGroup

end TauCeti
