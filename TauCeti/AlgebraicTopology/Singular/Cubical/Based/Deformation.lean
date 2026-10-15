/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CoherentHomotopy
public import TauCeti.Topology.Homotopy.Extension.Cube

/-!
# Deforming singular cubes into based cubes

Let `x` be a point of a space `X`. A singular `m`-cube is **`n`-based at `x`**
(`TauCeti.SingularCube.IsBased`) when it sends the `(n - 1)`-skeleton of the cube `Iᵐ`, the points
with fewer than `n` coordinates in the open interval `(0, 1)`, to `x`. In dimension less than `n`
only the constant cube at `x` is `n`-based (`TauCeti.SingularCube.isBased_iff_of_lt`), and an
`n`-cube is `n`-based exactly when it is a generalized loop in `Ω^ (Fin n) X x`
(`TauCeti.SingularCube.isBased_iff_mem_genLoop`). Faces of `n`-based cubes are `n`-based.

This file shows that when `X` is `(n - 1)`-connected, that is, when `π_k(X, x)` is trivial for
every `k < n`, every singular cube deforms into an `n`-based cube, coherently: there is a
`TauCeti.BasedCubeDeformation`, a homotopy of each singular cube `c` from `c` to an `n`-based cube,
such that

* the homotopy of a face of `c` is the restriction of the homotopy of `c` to that face;
* the homotopy of a cube not depending on a coordinate does not depend on it either;
* the homotopy of an `n`-based cube is constant.

Conversely such a deformation contracts every generalized loop of dimension `k < n` relative to
the boundary, so it exists exactly when `X` is `(n - 1)`-connected
(`TauCeti.nonempty_basedCubeDeformation_iff`).

The `n`-based cubes span a subcomplex of the normalized cubical chains, and the three properties
above are what the prism operators of the homotopies need to define a chain homotopy from the
identity to a retraction onto that subcomplex. In positive degrees below `n` that subcomplex is
zero, since the constant cube is degenerate, and in degree `n` it is spanned by generalized loops;
this is how the deformation enters the comparison of homotopy and homology of `(n - 1)`-connected
spaces.

## Construction

The homotopies are built by induction on the dimension of the cubes. The
homotopy of an `n`-based cube is constant, and that of a degenerate cube is read off one of its
faces. For any other `(m + 1)`-cube `c`, the homotopies of the faces of `c` agree where two faces
meet, so they glue to a homotopy of the restriction of `c` to the boundary of the cube, and the
homotopy extension property of the boundary (`TauCeti.hasHomotopyExtensionProperty_cubeBoundary`)
extends it to a homotopy of `c`. Its end sends the `(n - 1)`-skeleton to `x` as soon as
`m + 1 ≥ n`, because the `(n - 1)`-skeleton then lies in the boundary. When `m + 1 < n` the whole
end must be the constant cube: there the boundary homotopy is constant at `x` after some time, at
which the extension is a generalized loop in `Ω^ (Fin (m + 1)) X x`; it is contracted, relative to
the boundary, using that `π_{m + 1}(X, x)` is trivial. To leave room for these contractions, the
homotopies of cubes of dimension `k < n` reach `x` by the increasing times `(k + 1) / (k + 2)`.
The gluing of the face homotopies, the homotopies of degenerate cubes and the coherence of each
new dimension come from `TauCeti.CoherentCubeHomotopies`.

## Main definitions and results

* `TauCeti.SingularCube.IsBased`: cubes sending the `(n - 1)`-skeleton to `x`.
* `TauCeti.BasedCubeDeformation`: a coherent deformation of all singular cubes into `n`-based
  cubes.
* `TauCeti.basedCubeDeformation`: such a deformation for an `(n - 1)`-connected space.
* `TauCeti.nonempty_basedCubeDeformation_iff`: such a deformation exists exactly when `X` is
  `(n - 1)`-connected.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  subcomplex of singular simplices sending the `(n - 1)`-skeleton to the base point, of which the
  `n`-based cubes are the cubical analogue.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for singular cubes
  and their degeneracies.
-/

public section

noncomputable section

open unitInterval

namespace TauCeti

open CoherentCubeHomotopies

variable {X : Type*} [TopologicalSpace X]

namespace SingularCube

/-- A singular `m`-cube `c` is **`n`-based at `x`** when it sends the `(n - 1)`-skeleton of the
cube `Iᵐ` to `x`: every point of `Iᵐ` with fewer than `n` coordinates in the open interval
`(0, 1)` lies on a face of dimension less than `n`, and is sent to `x`. -/
def IsBased (n : ℕ) (x : X) {m : ℕ} (c : SingularCube X m) : Prop :=
  ∀ y : Fin m → I, (Finset.univ.filter fun i ↦ y i ≠ 0 ∧ y i ≠ 1).card < n → c y = x

/-- Unfolding of `TauCeti.SingularCube.IsBased`. -/
theorem isBased_iff {n : ℕ} {x : X} {m : ℕ} {c : SingularCube X m} :
    c.IsBased n x ↔
      ∀ y : Fin m → I, (Finset.univ.filter fun i ↦ y i ≠ 0 ∧ y i ≠ 1).card < n → c y = x :=
  Iff.rfl

/-- The constant cube at `x` is `n`-based at `x`. -/
@[simp]
theorem isBased_const (n : ℕ) (x : X) (m : ℕ) :
    IsBased n x (ContinuousMap.const (Fin m → I) x : SingularCube X m) :=
  fun _ _ ↦ rfl

end SingularCube

/-- The number of coordinates of `y` in the open interval `(0, 1)`, as a sum. -/
private lemma card_free_eq {m : ℕ} (y : Fin m → I) :
    (Finset.univ.filter fun i ↦ y i ≠ 0 ∧ y i ≠ 1).card =
      ∑ i, if y i ≠ 0 ∧ y i ≠ 1 then 1 else 0 :=
  Finset.card_filter _ _

private lemma card_free_removeNth_of_mem {m : ℕ} (i : Fin (m + 1)) {y : Fin (m + 1) → I}
    (hy : y i = 0 ∨ y i = 1) :
    (Finset.univ.filter fun j ↦ i.removeNth y j ≠ 0 ∧ i.removeNth y j ≠ 1).card =
      (Finset.univ.filter fun j ↦ y j ≠ 0 ∧ y j ≠ 1).card := by
  simp only [card_free_eq]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.removeNth_apply]
  rcases hy with h | h <;> simp only [h, ne_eq, not_true_eq_false, false_and, and_false,
    ite_false, zero_add] <;>
  -- the two sums differ only in their decidability instances
  exact Finset.sum_congr rfl fun j _ ↦ if_congr Iff.rfl rfl rfl

private lemma card_free_removeNth_le {m : ℕ} (i : Fin (m + 1)) (y : Fin (m + 1) → I) :
    (Finset.univ.filter fun j ↦ i.removeNth y j ≠ 0 ∧ i.removeNth y j ≠ 1).card ≤
      (Finset.univ.filter fun j ↦ y j ≠ 0 ∧ y j ≠ 1).card := by
  simp only [card_free_eq]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.removeNth_apply]
  exact Nat.le_add_left _ _

private lemma mem_boundary_of_card_free_lt {m : ℕ} {y : Fin m → I}
    (hy : (Finset.univ.filter fun j ↦ y j ≠ 0 ∧ y j ≠ 1).card < m) :
    y ∈ Cube.boundary (Fin m) := by
  by_contra h
  simp only [Cube.boundary, Set.mem_ofPred_eq, not_exists, not_or] at h
  rw [Finset.filter_true_of_mem fun j _ ↦ h j, Finset.card_univ, Fintype.card_fin] at hy
  exact lt_irrefl _ hy

namespace SingularCube

variable {n : ℕ} {x : X}

/-- A face of an `n`-based cube, at an endpoint of the interval, is `n`-based. -/
theorem IsBased.face {m : ℕ} {c : SingularCube X (m + 1)} (hc : c.IsBased n x) (i : Fin (m + 1))
    {t : I} (ht : t = 0 ∨ t = 1) : (face i t c).IsBased n x := by
  intro y hy
  have hti : (i.insertNth t y : Fin (m + 1) → I) i = 0 ∨
      (i.insertNth t y : Fin (m + 1) → I) i = 1 := by
    rwa [Fin.insertNth_apply_same]
  rw [face_apply]
  refine hc _ ?_
  rw [← card_free_removeNth_of_mem i hti, Fin.removeNth_insertNth]
  exact hy

/-- In dimension less than `n`, the only `n`-based cube is the constant cube at `x`. -/
theorem isBased_iff_of_lt {m : ℕ} (hm : m < n) {c : SingularCube X m} :
    c.IsBased n x ↔ ∀ y, c y = x :=
  ⟨fun hc y ↦ hc y ((Finset.card_filter_le _ _).trans_lt (by simpa using hm)),
    fun hc y _ ↦ hc y⟩

/-- An `n`-cube is `n`-based at `x` exactly when it sends the boundary of the cube to `x`, that
is, when it is a generalized loop in `Ω^ (Fin n) X x`. -/
theorem isBased_iff_mem_genLoop {c : SingularCube X n} :
    c.IsBased n x ↔ c ∈ GenLoop (Fin n) X x := by
  refine ⟨fun hc y hy ↦ hc y ?_, fun hc y hy ↦ hc y (mem_boundary_of_card_free_lt hy)⟩
  obtain ⟨i, hi⟩ := hy
  calc (Finset.univ.filter fun j ↦ y j ≠ 0 ∧ y j ≠ 1).card
      ≤ (Finset.univ.erase i).card :=
        Finset.card_le_card fun j hj ↦ Finset.mem_erase.2
          ⟨by rintro rfl; exact hi.elim (Finset.mem_filter.1 hj).2.1 (Finset.mem_filter.1 hj).2.2,
            Finset.mem_univ _⟩
    _ < n := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        exact Nat.sub_lt (Fin.pos i) zero_lt_one

end SingularCube

/-! ### Extending the deformation over a single cube -/

variable {n : ℕ} {x : X}

/-- **The inductive step for a single cube.** Let `c` be a singular `m`-cube and `B` a homotopy of
its restriction to the boundary of the cube that ends at a map sending the `(n - 1)`-skeleton to
`x`, and that, when `m < n`, is constant at `x` from time `threshold m` on. Then `B` extends to a
homotopy of `c` ending at an `n`-based cube, which, when `m < n`, is constant at `x` from time
`threshold (m + 1)` on. When `m < n` the extension contracts a generalized loop in
`Ω^ (Fin m) X x`, using that `π_m(X, x)` is trivial. -/
private lemma exists_extension (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x)) {m : ℕ}
    (c : SingularCube X m) (B : C(I × Cube.boundary (Fin m), X)) (hB₀ : ∀ y, B (0, y) = c y)
    (hB₁ : ∀ y : Cube.boundary (Fin m),
      (Finset.univ.filter fun j ↦ (y : Fin m → I) j ≠ 0 ∧ (y : Fin m → I) j ≠ 1).card < n →
        B (1, y) = x)
    (hB : m < n → ∀ s : I, threshold m ≤ s → ∀ y, B (s, y) = x) :
    ∃ G : C(I × (Fin m → I), X), (∀ y, G (0, y) = c y) ∧
      (∀ s (y : Cube.boundary (Fin m)), G (s, y) = B (s, y)) ∧
      SingularCube.IsBased n x (G.curry 1) ∧
      (m < n → ∀ s : I, threshold (m + 1) ≤ s → ∀ y, G (s, y) = x) := by
  have hcl : IsClosed (Cube.boundary (Fin m)) := hasHomotopyExtensionProperty_cubeBoundary.isClosed
  obtain ⟨G₀, hG₀, hG₀B⟩ :=
    hasHomotopyExtensionProperty_cubeBoundary.exists_extension_of_isClosed hcl c B hB₀
  by_cases hm : m < n
  swap
  · refine ⟨G₀, hG₀, hG₀B, fun y hy ↦ ?_, fun h ↦ absurd h hm⟩
    have hy' := mem_boundary_of_card_free_lt (hy.trans_le (not_lt.1 hm))
    exact (hG₀B 1 ⟨y, hy'⟩).trans (hB₁ ⟨y, hy'⟩ hy)
  -- At time `a` the extension sends the boundary to `x`, so it is a generalized loop; contract it
  -- during the times `[a, b]`.
  set a := threshold m
  set b := threshold (m + 1)
  have hab : (a : ℝ) < b := threshold_lt_succ m
  let p : GenLoop (Fin m) X x :=
    ⟨G₀.curry a, fun y hy ↦ (hG₀B a ⟨y, hy⟩).trans (hB hm a le_rfl _)⟩
  have := hX m hm
  obtain ⟨K⟩ : GenLoop.Homotopic p GenLoop.const :=
    Quotient.exact (this.elim (Quotient.mk _ p) (Quotient.mk _ GenLoop.const))
  let ψ : C(I, I) := ⟨fun s ↦ Set.projIcc 0 1 zero_le_one (((s : ℝ) - a) / (b - a)), by fun_prop⟩
  have hψ₀ {s : I} (hs : (s : ℝ) ≤ a) : ψ s = 0 :=
    Set.projIcc_of_le_left zero_le_one (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hψ₁ {s : I} (hs : (b : ℝ) ≤ s) : ψ s = 1 :=
    Set.projIcc_of_right_le zero_le_one ((one_le_div (by linarith)).2 (by linarith))
  have hK₁ (y : Fin m → I) : K (1, y) = x := K.apply_one y
  refine ⟨⟨fun q ↦ if (q.1 : ℝ) ≤ a then G₀ q else K (ψ q.1, q.2), ?_⟩, fun y ↦ ?_,
    fun s y ↦ ?_, fun y _ ↦ ?_, fun _ s hs y ↦ ?_⟩
  · refine Continuous.if_le G₀.continuous (by fun_prop) (by fun_prop) continuous_const
      fun q hq ↦ ?_
    rw [hψ₀ hq.le, K.apply_zero]
    exact congrArg G₀ (Prod.ext (Subtype.ext hq) rfl)
  · simp [hG₀]
  · dsimp only [ContinuousMap.coe_mk]
    split_ifs with hs
    · exact hG₀B s y
    · rw [K.eq_fst _ y.2]
      exact (hG₀B a y).trans ((hB hm a le_rfl y).trans (hB hm s (not_le.1 hs).le y).symm)
  · have h1 : ¬ ((1 : I) : ℝ) ≤ a := not_le.2 (threshold_lt_one m)
    simp only [ContinuousMap.curry_apply, ContinuousMap.coe_mk, h1, ite_false]
    rw [hψ₁ (by exact_mod_cast b.2.2), hK₁]
  · have hs' : ¬ (s : ℝ) ≤ a := not_le.2 (hab.trans_le hs)
    simp only [ContinuousMap.coe_mk, hs', ite_false]
    rw [hψ₁ hs, hK₁]

/-! ### Deforming all cubes of one dimension -/

/-- Homotopies of all singular `m`-cubes into `n`-based cubes, with the properties maintained by
the inductive construction on top of coherence. -/
private structure Level (n : ℕ) (x : X) (m : ℕ) extends CoherentCubeHomotopies X m where
  apply_of_isBased : ∀ c, c.IsBased n x → ∀ s y, homotopy c (s, y) = c y
  isBased_one : ∀ c, SingularCube.IsBased n x ((homotopy c).curry 1)
  apply_of_lt : m < n → ∀ c (s : I), threshold (m + 1) ≤ s → ∀ y, homotopy c (s, y) = x

namespace Level

variable {m : ℕ}

private lemma bdry_one (L : Level n x m) (c : SingularCube X (m + 1))
    (y : Cube.boundary (Fin (m + 1)))
    (hy : (Finset.univ.filter fun j ↦ (y : Fin (m + 1) → I) j ≠ 0 ∧
      (y : Fin (m + 1) → I) j ≠ 1).card < n) : L.boundaryHomotopy c (1, y) = x := by
  obtain ⟨j, hj⟩ := y.2
  rw [L.boundaryHomotopy_apply c 1 y j hj]
  exact L.isBased_one _ _ ((card_free_removeNth_le j _).trans_lt hy)

private lemma bdry_of_lt (L : Level n x m) (c : SingularCube X (m + 1)) (hm : m + 1 < n) (s : I)
    (hs : threshold (m + 1) ≤ s) (y : Cube.boundary (Fin (m + 1))) :
    L.boundaryHomotopy c (s, y) = x := by
  obtain ⟨j, hj⟩ := y.2
  rw [L.boundaryHomotopy_apply c s y j hj]
  exact L.apply_of_lt (by omega) _ s hs _

variable (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))
include hX

open Classical in
/-- The homotopies of the `(m + 1)`-cubes: constant on `n`-based cubes, read off a face on
degenerate cubes, and otherwise extended from the glued homotopies of the faces. -/
private def nextH (L : Level n x m) (c : SingularCube X (m + 1)) : C(I × (Fin (m + 1) → I), X) :=
  if c.IsBased n x then c.comp ContinuousMap.snd
  else if hd : c.IsDegenerate then
    L.degenerateHomotopy c (SingularCube.isDegenerate_iff.1 hd).choose
  else (exists_extension hX c (L.boundaryHomotopy c) (L.boundaryHomotopy_zero c) (L.bdry_one c)
    (L.bdry_of_lt c)).choose

private lemma nextH_of_isBased (L : Level n x m) {c : SingularCube X (m + 1)}
    (hc : c.IsBased n x) (s : I) (y : Fin (m + 1) → I) : nextH hX L c (s, y) = c y := by
  simp [nextH, hc]

private lemma nextH_of_isDegenerate (L : Level n x m) {c : SingularCube X (m + 1)}
    (hc : ¬ c.IsBased n x) (hd : c.IsDegenerate) :
    nextH hX L c = L.degenerateHomotopy c (SingularCube.isDegenerate_iff.1 hd).choose := by
  simp [nextH, hc, hd]

private lemma nextH_spec (L : Level n x m) {c : SingularCube X (m + 1)} (hc : ¬ c.IsBased n x)
    (hd : ¬ c.IsDegenerate) :
    let G := nextH hX L c
    (∀ y, G (0, y) = c y) ∧
      (∀ s (y : Cube.boundary (Fin (m + 1))), G (s, y) = L.boundaryHomotopy c (s, y)) ∧
      SingularCube.IsBased n x (G.curry 1) ∧
      (m + 1 < n → ∀ s : I, threshold (m + 1 + 1) ≤ s → ∀ y, G (s, y) = x) := by
  simp only [nextH, hc, hd, dite_false, ite_false]
  exact (exists_extension hX c (L.boundaryHomotopy c) (L.boundaryHomotopy_zero c) (L.bdry_one c)
    (L.bdry_of_lt c)).choose_spec

/-- The homotopies of the `(m + 1)`-cubes restrict on faces to the homotopies of the faces. -/
private lemma nextH_insertNth (L : Level n x m) (c : SingularCube X (m + 1)) (i : Fin (m + 1))
    {t : I} (ht : t = 0 ∨ t = 1) (s : I) (z : Fin m → I) :
    nextH hX L c (s, i.insertNth t z) = L.homotopy (SingularCube.face i t c) (s, z) := by
  by_cases hb : c.IsBased n x
  · rw [nextH_of_isBased hX L hb, L.apply_of_isBased _ (hb.face i ht), SingularCube.face_apply]
  by_cases hd : c.IsDegenerate
  · rw [nextH_of_isDegenerate hX L hb hd,
      L.degenerateHomotopy_insertNth (SingularCube.isDegenerate_iff.1 hd).choose_spec i ht]
  have hy : (i.insertNth t z : Fin (m + 1) → I) ∈ Cube.boundary (Fin (m + 1)) :=
    ⟨i, by rwa [Fin.insertNth_apply_same]⟩
  rw [(nextH_spec hX L hb hd).2.1 s ⟨_, hy⟩,
    L.boundaryHomotopy_apply c s ⟨_, hy⟩ i (by simpa using ht)]
  simp

/-- The `(m + 1)`-st level of the construction, built from the `m`-th. -/
private def next (L : Level n x m) : Level n x (m + 1) where
  homotopy := nextH hX L
  homotopy_zero c y := by
    by_cases hb : c.IsBased n x
    · exact nextH_of_isBased hX L hb 0 y
    by_cases hd : c.IsDegenerate
    · rw [nextH_of_isDegenerate hX L hb hd, degenerateHomotopy_apply, L.homotopy_zero,
        SingularCube.face_apply, Fin.insertNth_removeNth]
      exact (SingularCube.isDegenerate_iff.1 hd).choose_spec.apply_update y 0
    · exact (nextH_spec hX L hb hd).1 y
  apply_of_isBased _ hc s y := nextH_of_isBased hX L hc s y
  isBased_one c := by
    by_cases hb : c.IsBased n x
    · intro y hy
      rw [ContinuousMap.curry_apply, nextH_of_isBased hX L hb]
      exact hb y hy
    by_cases hd : c.IsDegenerate
    · intro y hy
      rw [ContinuousMap.curry_apply, nextH_of_isDegenerate hX L hb hd, degenerateHomotopy_apply]
      exact L.isBased_one _ _ ((card_free_removeNth_le _ _).trans_lt hy)
    · exact (nextH_spec hX L hb hd).2.2.1
  isDegenerateAt_curry c j hj s := by
    by_cases hb : c.IsBased n x
    · refine SingularCube.isDegenerateAt_iff.2 fun y r ↦ ?_
      simp only [ContinuousMap.curry_apply, nextH_of_isBased hX L hb]
      exact hj.apply_update y r
    have hd : c.IsDegenerate := hj.isDegenerate
    rw [nextH_of_isDegenerate hX L hb hd]
    exact L.isDegenerateAt_curry_degenerateHomotopy hj s
  apply_of_lt hm c s hs y := by
    by_cases hb : c.IsBased n x
    · rw [nextH_of_isBased hX L hb]
      exact (SingularCube.isBased_iff_of_lt hm).1 hb y
    by_cases hd : c.IsDegenerate
    · rw [nextH_of_isDegenerate hX L hb hd, degenerateHomotopy_apply]
      exact L.apply_of_lt (by omega) _ s
        (Subtype.coe_le_coe.1 ((threshold_lt_succ (m + 1)).le.trans hs)) _
    · exact (nextH_spec hX L hb hd).2.2.2 hm s hs y
  coherent :=
    L.coherent_of_homotopy_insertNth (nextH hX L) fun c i _ ht ↦ nextH_insertNth hX L c i ht

end Level

variable (hX : ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x))

include hX in
private lemma exists_extension_zero (c : SingularCube X 0) :
    ∃ G : C(I × (Fin 0 → I), X), (∀ y, G (0, y) = c y) ∧
      SingularCube.IsBased n x (G.curry 1) ∧
      (0 < n → ∀ s : I, threshold (0 + 1) ≤ s → ∀ y, G (s, y) = x) := by
  -- The boundary of the `0`-cube is empty, so any homotopy of it will do.
  have hb (y : Cube.boundary (Fin 0)) : False := by simpa using y.2
  obtain ⟨G, hG₀, -, hG⟩ := exists_extension hX c
    ⟨fun q ↦ (hb q.2).elim, continuous_of_const fun q ↦ (hb q.2).elim⟩ (fun y ↦ (hb y).elim)
    (fun y ↦ (hb y).elim) fun _ _ _ y ↦ (hb y).elim
  exact ⟨G, hG₀, hG⟩

open Classical in
/-- The homotopies of points: constant at `x`, or a path to `x` reaching it by time `1 / 2`. -/
private def baseH (c : SingularCube X 0) : C(I × (Fin 0 → I), X) :=
  if c.IsBased n x then c.comp ContinuousMap.snd else (exists_extension_zero hX c).choose

include hX in
private lemma baseH_of_isBased {c : SingularCube X 0} (hc : c.IsBased n x) (s : I)
    (y : Fin 0 → I) : baseH hX c (s, y) = c y := by
  simp [baseH, hc]

include hX in
private lemma baseH_spec {c : SingularCube X 0} (hc : ¬ c.IsBased n x) :
    let G := baseH hX c
    (∀ y, G (0, y) = c y) ∧ SingularCube.IsBased n x (G.curry 1) ∧
      (0 < n → ∀ s : I, threshold (0 + 1) ≤ s → ∀ y, G (s, y) = x) := by
  simp only [baseH, hc, ite_false]
  exact (exists_extension_zero hX c).choose_spec

/-- The `0`-th level of the construction. -/
private def base : Level n x 0 where
  homotopy := baseH hX
  homotopy_zero c y := by
    by_cases hb : c.IsBased n x
    · exact baseH_of_isBased hX hb 0 y
    · exact (baseH_spec hX hb).1 y
  apply_of_isBased _ hc s y := baseH_of_isBased hX hc s y
  isBased_one c := by
    by_cases hb : c.IsBased n x
    · intro y hy
      rw [ContinuousMap.curry_apply, baseH_of_isBased hX hb]
      exact hb y hy
    · exact (baseH_spec hX hb).2.1
  isDegenerateAt_curry _ i := i.elim0
  apply_of_lt hn c s hs y := by
    by_cases hb : c.IsBased n x
    · rw [baseH_of_isBased hX hb]
      exact (SingularCube.isBased_iff_of_lt hn).1 hb y
    · exact (baseH_spec hX hb).2.2 hn s hs y
  coherent c i j t u _ _ z z' h s := by
    obtain rfl : i = j := Fin.ext (by omega)
    obtain ⟨rfl, rfl⟩ := Fin.insertNth_injective2 h
    rfl

/-- All levels of the construction, built by recursion on the dimension. -/
private def levels : ∀ m, Level n x m
  | 0 => base hX
  | m + 1 => (levels m).next hX

/-! ### The deformation -/

variable (n x) in
/-- A **deformation of the singular cubes of `X` into `n`-based cubes**: a homotopy of every
singular cube `c`, with time as the first coordinate, starting at `c` and ending at a cube sending
the `(n - 1)`-skeleton to `x`. The homotopies are compatible with faces and degeneracies, and fix
the cubes that are already `n`-based. -/
structure BasedCubeDeformation where
  /-- The homotopy deforming the singular cube `c`. -/
  homotopy {m : ℕ} (c : SingularCube X m) : C(I × (Fin m → I), X)
  /-- The homotopy of `c` starts at `c`. -/
  homotopy_zero {m : ℕ} (c : SingularCube X m) (y : Fin m → I) : homotopy c (0, y) = c y
  /-- The homotopy of `c` ends at an `n`-based cube. -/
  isBased_curry_one {m : ℕ} (c : SingularCube X m) :
    SingularCube.IsBased n x ((homotopy c).curry 1)
  /-- The homotopy of a face of `c` is the restriction of the homotopy of `c` to that face. -/
  homotopy_insertNth {m : ℕ} (c : SingularCube X (m + 1)) (i : Fin (m + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) (s : I) (z : Fin m → I) :
    homotopy c (s, i.insertNth t z) = homotopy (SingularCube.face i t c) (s, z)
  /-- If `c` does not depend on a coordinate, then neither does its homotopy at any time. -/
  isDegenerateAt_curry {m : ℕ} {c : SingularCube X m} {i : Fin m} (hc : c.IsDegenerateAt i)
    (s : I) : SingularCube.IsDegenerateAt ((homotopy c).curry s) i
  /-- The homotopy of an `n`-based cube is constant. -/
  homotopy_of_isBased {m : ℕ} {c : SingularCube X m} (hc : c.IsBased n x) (s : I)
    (y : Fin m → I) : homotopy c (s, y) = c y

attribute [simp] BasedCubeDeformation.homotopy_zero BasedCubeDeformation.homotopy_insertNth
  BasedCubeDeformation.homotopy_of_isBased

/-- **Every singular cube of an `(n - 1)`-connected space deforms into an `n`-based cube.** If
`π_k(X, x)` is trivial for every `k < n` (for `k = 0`, if `X` is path connected), then there is a
deformation of the singular cubes of `X` into cubes sending the `(n - 1)`-skeleton to `x`,
compatible with faces and degeneracies and fixing the `n`-based cubes. -/
def basedCubeDeformation : BasedCubeDeformation n x where
  homotopy {m} c := (levels hX m).homotopy c
  homotopy_zero {m} c y := (levels hX m).homotopy_zero c y
  isBased_curry_one {m} c := (levels hX m).isBased_one c
  homotopy_insertNth {m} c i _ ht s z := Level.nextH_insertNth hX (levels hX m) c i ht s z
  isDegenerateAt_curry {m} c i hc s := (levels hX m).isDegenerateAt_curry c i hc s
  homotopy_of_isBased {m} c hc s y := (levels hX m).apply_of_isBased c hc s y

omit hX in
/-- A deformation of the singular cubes into `n`-based cubes deforms every generalized loop of
dimension `k < n` to the constant loop, relative to the boundary of the cube. -/
theorem BasedCubeDeformation.homotopic_const (D : BasedCubeDeformation n x) {k : ℕ} (hk : k < n)
    (p : GenLoop (Fin k) X x) : GenLoop.Homotopic p GenLoop.const := by
  -- On the boundary the homotopy follows the homotopies of the faces of `p`, which are constant
  -- at `x` and hence `n`-based, so it is fixed there.
  have hbd (s : I) (y : Fin k → I) (hy : y ∈ Cube.boundary (Fin k)) :
      D.homotopy p.1 (s, y) = x := by
    cases k with
    | zero => simp at hy
    | succ _ =>
      obtain ⟨i, hi⟩ := hy
      have hface : (SingularCube.face i (y i) p.1).IsBased n x := fun z _ ↦ by
        rw [SingularCube.face_apply]
        exact p.2 _ ⟨i, by simpa using hi⟩
      rw [← Fin.insertNth_self_removeNth i y, D.homotopy_insertNth _ _ hi,
        D.homotopy_of_isBased hface, SingularCube.face_apply]
      exact p.2 _ ⟨i, by simpa using hi⟩
  exact ⟨{ toFun := D.homotopy p.1
           map_zero_left := D.homotopy_zero p.1
           map_one_left := (SingularCube.isBased_iff_of_lt hk).1 (D.isBased_curry_one p.1)
           prop' := fun s y hy ↦ (hbd s y hy).trans (p.2 y hy).symm }⟩

omit hX in
/-- **The singular cubes of `X` deform into `n`-based cubes exactly when `X` is
`(n - 1)`-connected**: when `π_k(X, x)` is trivial for every `k < n`. -/
theorem nonempty_basedCubeDeformation_iff :
    Nonempty (BasedCubeDeformation n x) ↔ ∀ k < n, Subsingleton (HomotopyGroup (Fin k) X x) :=
  ⟨fun ⟨D⟩ _ hk ↦ ⟨fun a b ↦ Quotient.inductionOn₂ a b fun p q ↦
      Quotient.sound ((D.homotopic_const hk p).trans (D.homotopic_const hk q).symm)⟩,
    fun hX ↦ ⟨basedCubeDeformation hX⟩⟩

end TauCeti
