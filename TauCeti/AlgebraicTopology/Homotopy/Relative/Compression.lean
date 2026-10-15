/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Basic
public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# The compression criterion

Let `X = (X, A, a₀)` be a based pair and let `n` be the cardinality of the index type `N`. This
file proves the compression criterion for the relative homotopy set `π_{n+1}(X, A, a₀)`: a relative
cube `p : I × I^N → X` represents the distinguished class exactly when it is homotopic, relative to
the boundary of the cube `I × I^N`, to a map with values in `A`
(`TauCeti.RelHomotopyGroup.mk_eq_default_iff`). Consequently `π_{n+1}(X, A, a₀)` is trivial
exactly when every relative cube can be compressed into `A` in this way
(`TauCeti.RelHomotopyGroup.subsingleton_iff`).

The criterion turns vanishing of relative homotopy groups into deformations of maps of pairs into
the subspace. Such deformations, for maps out of a closed ball, are the hypothesis of the
compression lemma (`TauCeti.exists_homotopicRel_range_subset`) behind Whitehead's theorem. The
criterion also gives exactness of the homotopy sequence of a pair at `π_{n+1}(X, a₀)`.

## Implementation notes

* A homotopy relative to the boundary of the cube keeps the face `{0} × I^N` inside `A` and the
  rest of the boundary at `a₀`, so it is a homotopy through relative cubes. A relative cube with
  values in `A` is trivial by `TauCeti.RelGenLoop.homotopic_const_of_mem_range`.
* Conversely, let `F : I × (I × I^N) → X` be a homotopy through relative cubes from `p` to the
  constant cube, and read its first two coordinates as a point `(u, s)` of a square. On the edge
  `u = 0` it is `p`, on the edge `s = 0` it takes values in `A`, and on the edges `u = 1` and
  `s = 1` it is constant at `a₀`. Sweeping the edge `u = 0` across the square to the edge `s = 0`,
  keeping the corner `(0, 0)` fixed and the opposite endpoint on the edges `u = 1` and `s = 1`,
  gives a homotopy relative to the boundary of the cube from `p` to the face of `F` in `A`.

## Main declarations

* `TauCeti.RelGenLoop.mapsTo_prodBoundary`: a relative cube is a map of pairs
  `(I × I^N, ∂(I × I^N)) → (X, A)`.
* `TauCeti.RelGenLoop.Homotopic.of_homotopicRel`: relative cubes homotopic relative to the
  boundary of the cube are homotopic through relative cubes.
* `TauCeti.RelGenLoop.exists_homotopicRel_of_homotopic_const`: a relative cube homotopic through
  relative cubes to the constant cube is homotopic, relative to the boundary of the cube, to a map
  into `A`.
* `TauCeti.RelHomotopyGroup.mk_eq_default_iff`: **the compression criterion**.
* `TauCeti.RelHomotopyGroup.subsingleton_iff`: `π_{n+1}(X, A, a₀)` is trivial exactly when every
  relative cube compresses into `A`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the compression criterion preceding Theorem 4.3.
-/

public section

universe u v

open Set
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {N : Type v} {X : BasedTopPair.{u}}

namespace RelGenLoop

/-- A relative cube of the based pair `(X, A, a₀)` is a map of pairs
`(I × I^N, ∂(I × I^N)) → (X, A)`. -/
theorem mapsTo_prodBoundary {p : C(I × (I^N), X.pair.fst)} (hp : p ∈ RelGenLoop N X) :
    MapsTo p (Cube.prodBoundary N) (range X.pair.map) := by
  rintro ⟨s, t⟩ hz
  rcases Cube.mem_prodBoundary_iff.1 hz with (hs | hs) | ht
  · obtain rfl : s = 0 := hs
    exact (mem_iff.1 hp).1 t
  · exact ⟨_, ((mem_iff.1 hp).2 s t (.inl hs)).symm⟩
  · exact ⟨_, ((mem_iff.1 hp).2 s t (.inr ht)).symm⟩

/-- Relative cubes that are homotopic relative to the boundary of the cube `I × I^N` are
homotopic through relative cubes. -/
theorem Homotopic.of_homotopicRel {p q : RelGenLoop N X}
    (h : (p : C(I × (I^N), X.pair.fst)).HomotopicRel q (Cube.prodBoundary N)) :
    Homotopic p q :=
  homotopic_iff.2 <| Nonempty.map (fun F =>
    { toHomotopy := F.toHomotopy
      prop' r := by
        refine mem_iff.2 ⟨fun t => ?_, fun s t hst => ?_⟩
        · simpa [F.eq_fst r (Cube.mk_zero_mem_prodBoundary t)] using apply_zero_mem_range p t
        · simpa [F.eq_fst r (Cube.mk_mem_prodBoundary hst)] using (mem_iff.1 p.2).2 s t hst }) h

/-- A relative cube that is homotopic, relative to the boundary of the cube `I × I^N`, to a map
with values in `A` is homotopic through relative cubes to the constant cube. -/
theorem homotopic_const_of_homotopicRel {p : RelGenLoop N X} {q : C(I × (I^N), X.pair.fst)}
    (h : (p : C(I × (I^N), X.pair.fst)).HomotopicRel q (Cube.prodBoundary N))
    (hq : ∀ y, q y ∈ range X.pair.map) :
    Homotopic p const := by
  obtain ⟨q', rfl⟩ : ∃ q' : RelGenLoop N X, (q' : C(I × (I^N), X.pair.fst)) = q :=
    ⟨mk q (fun _ => hq _) fun s t hst =>
      (h.fst_eq_snd (Cube.mk_mem_prodBoundary hst)).symm.trans
        ((mem_iff.1 p.2).2 s t hst), coe_mk _ _ _⟩
  exact (Homotopic.of_homotopicRel h).trans (homotopic_const_of_mem_range q' hq)

section Sweep

variable {p : RelGenLoop N X}
  (F : (p : C(I × (I^N), X.pair.fst)).HomotopyWith const.1 (· ∈ RelGenLoop N X))

/-- The face in `A` swept out by a homotopy `F` through relative cubes from `p` to the constant
cube, as a map of `I × I^N` with the time of `F` as its first coordinate. -/
private noncomputable def sweepFace : C(I × (I^N), X.pair.fst) :=
  ⟨fun y => F (y.1, (0, y.2)), by fun_prop⟩

private theorem sweepFace_mem_range (y : I × (I^N)) : sweepFace F y ∈ range X.pair.map := by
  simpa [sweepFace] using (mem_iff.1 (F.prop y.1)).1 y.2

/-- The point of the `(u, s)`-square visited at time `y` along the `w`-th segment from the origin.
At `w = 0` this is `(0, y)`, at `w = 1` it is `(y, 0)`, and at `y = 1` it lies on the edge `u = 1`
or `s = 1`, where `F` is constant at the basepoint. -/
private noncomputable def sweep (w y : I) : I × I :=
  (projIcc 0 1 zero_le_one (min 1 (2 * (w : ℝ)) * y),
    projIcc 0 1 zero_le_one (min 1 (2 * (1 - (w : ℝ))) * y))

private theorem continuous_sweep : Continuous fun y : I × I => sweep y.1 y.2 := by
  unfold sweep
  fun_prop

private theorem sweep_zero (y : I) : sweep 0 y = (0, y) := by
  ext <;> simp [sweep]

private theorem sweep_one (y : I) : sweep 1 y = (y, 0) := by
  ext <;> simp [sweep]

private theorem sweep_apply_zero (w : I) : sweep w 0 = (0, 0) := by
  ext <;> simp [sweep]

private theorem sweep_apply_one (w : I) : (sweep w 1).1 = 1 ∨ (sweep w 1).2 = 1 := by
  simp only [sweep, Set.Icc.coe_one, mul_one, projIcc_eq_one]
  rcases le_total (w : ℝ) (1 / 2) with hw | hw
  · exact Or.inr (le_min le_rfl (by linarith))
  · exact Or.inl (le_min le_rfl (by linarith))

/-- Sweeping the path of `F` is a homotopy relative to the boundary of the cube from `p` to the
face swept out in `A`. -/
private theorem homotopicRel_sweepFace :
    (p : C(I × (I^N), X.pair.fst)).HomotopicRel (sweepFace F) (Cube.prodBoundary N) := by
  have hs : Continuous fun y : I × (I × (I^N)) => sweep y.1 y.2.1 :=
    continuous_sweep.comp (f := fun y : I × (I × (I^N)) => (y.1, y.2.1)) (by fun_prop)
  refine ⟨{ toFun y := F ((sweep y.1 y.2.1).1, ((sweep y.1 y.2.1).2, y.2.2))
            continuous_toFun := F.continuous.comp ((continuous_fst.comp hs).prodMk
              ((continuous_snd.comp hs).prodMk (by fun_prop)))
            map_zero_left y := by simp [sweep_zero]
            map_one_left y := by simp [sweep_one, sweepFace]
            prop' w y hy := ?_ }⟩
  obtain ⟨s, t⟩ := y
  rw [ContinuousMap.coe_mk, coe_coe]
  dsimp only
  simp only [Cube.mem_prodBoundary_iff] at hy
  rcases hy with (rfl | rfl) | ht
  · rw [sweep_apply_zero, F.apply_zero, coe_coe]
  · rw [apply_one p]
    rcases sweep_apply_one w with h₁ | h₁
    · rw [h₁, F.apply_one, coe_coe, const_apply]
    · rw [h₁]
      simpa using (mem_iff.1 (F.prop _)).2 1 t (Or.inl rfl)
  · rw [apply_of_mem_boundary p s ht]
    simpa using (mem_iff.1 (F.prop _)).2 _ t (Or.inr ht)

end Sweep

/-- A relative cube that is homotopic through relative cubes to the constant cube is homotopic,
relative to the boundary of the cube `I × I^N`, to a map with values in `A`. -/
theorem exists_homotopicRel_of_homotopic_const {p : RelGenLoop N X} (h : Homotopic p const) :
    ∃ q : C(I × (I^N), X.pair.fst),
      (p : C(I × (I^N), X.pair.fst)).HomotopicRel q (Cube.prodBoundary N) ∧
      ∀ y, q y ∈ range X.pair.map :=
  let ⟨F⟩ := homotopic_iff.1 h
  ⟨sweepFace F, homotopicRel_sweepFace F, sweepFace_mem_range F⟩

end RelGenLoop

namespace RelHomotopyGroup

/-- **The compression criterion** (Hatcher, Section 4.1). A relative cube represents the
distinguished class of `π_{n+1}(X, A, a₀)` exactly when it is homotopic, relative to the boundary
of the cube `I × I^N`, to a map with values in `A`. -/
theorem mk_eq_default_iff {p : RelGenLoop N X} :
    mk p = default ↔
      ∃ q : C(I × (I^N), X.pair.fst),
        (p : C(I × (I^N), X.pair.fst)).HomotopicRel q (Cube.prodBoundary N) ∧
        ∀ y, q y ∈ range X.pair.map := by
  rw [default_eq, mk_eq_mk]
  exact ⟨RelGenLoop.exists_homotopicRel_of_homotopic_const,
    fun ⟨_, h, hq⟩ => RelGenLoop.homotopic_const_of_homotopicRel h hq⟩

/-- The relative homotopy set `π_{n+1}(X, A, a₀)` is trivial exactly when every relative cube is
homotopic, relative to the boundary of the cube `I × I^N`, to a map with values in `A`. -/
theorem subsingleton_iff :
    Subsingleton (RelHomotopyGroup N X) ↔
      ∀ p : RelGenLoop N X, ∃ q : C(I × (I^N), X.pair.fst),
        (p : C(I × (I^N), X.pair.fst)).HomotopicRel q (Cube.prodBoundary N) ∧
        ∀ y, q y ∈ range X.pair.map := by
  refine ⟨fun _ p => mk_eq_default_iff.1 (Subsingleton.elim _ _), fun h => ⟨fun a b => ?_⟩⟩
  obtain ⟨p, rfl⟩ := mk_surjective a
  obtain ⟨q, rfl⟩ := mk_surjective b
  rw [mk_eq_default_iff.2 (h p), mk_eq_default_iff.2 (h q)]

end RelHomotopyGroup

end TauCeti
