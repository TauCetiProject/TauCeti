/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Basic
public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.Topology.PiCurry

/-!
# The exact homotopy sequence of a based pair

Let `X = (X, A, a₀)` be a based pair and let `n` be the cardinality of the index type `N`. This
file constructs the map `j : π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` and proves that the sequence of
pointed sets

`π_{n+1}(A, a₀) → π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀) → π_n(A, a₀) → π_n(X, a₀)`

is exact at its three middle terms, for every `N`. Here the first and last maps are induced by
the inclusion `A ↪ X`, and the third is `TauCeti.RelHomotopyGroup.boundary`. Exactness of a
sequence of pointed sets `f`, `g` means that the elements sent by `g` to the distinguished point
are exactly the image of `f`.

The absolute group `π_{n+1}(X, a₀)` is Mathlib's `HomotopyGroup (Option N) X a₀`, whose cube
`I^(Option N)` is the relative cube `I × I^N` with the coordinate `none` as the distinguished first
direction (`TauCeti.piOptionEquivProdHomeomorph`, `Cube.boundary_option_iff`). The map `j` regards
an absolute cube as a relative one.

Since `N` is arbitrary (and may be empty), the three statements cover every term of the long exact
sequence

`⋯ → π_{n+1}(X, A) → π_n(A) → π_n(X) → π_n(X, A) → ⋯ → π_1(X, A) → π_0(A) → π_0(X)`

of pointed sets. To chain two consecutive degrees, the group `π_n(X, a₀)` receiving the inclusion
from `π_n(A, a₀)` (modelled on `I^N`) is matched with the source of `j` (modelled on `I^(Option M)`
for an index type `M` with `Option M ≃ N`) by reindexing the cube along
`HomotopyGroup.congrEquiv`.

## Implementation notes

The three exactness proofs are the standard cube manipulations of Hatcher, *Algebraic Topology*,
Theorem 4.3.

* At `π_n(A)`: a relative cube is literally a null-homotopy in `X` of its face in `A`, and
  conversely.
* At `π_{n+1}(X, A)`: if the face of a relative cube `p` is null-homotopic in `A`, glue that
  null-homotopy in front of `p` along the distinguished direction. Shrinking the glued part gives
  a homotopy through relative cubes from `p` to a cube whose distinguished face is constant, that
  is, to an absolute cube.
* At `π_{n+1}(X)`: a homotopy through relative cubes `F` from an absolute cube to the constant
  cube restricts on the distinguished face to a cube in `A`. Sweeping the path of `F` from the
  direction of the absolute cube to the direction of its face gives a homotopy in `X`, relative to
  the boundary, between the absolute cube and that cube in `A`.

## Main declarations

* `TauCeti.RelGenLoop.ofGenLoop`, `TauCeti.RelHomotopyGroup.ofHomotopyGroup`: the map
  `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)`, natural by `TauCeti.RelHomotopyGroup.map_ofHomotopyGroup`.
* `TauCeti.RelHomotopyGroup.mem_range_homotopyGroupMap_iff`: exactness at `π_{n+1}(X, a₀)`.
* `TauCeti.RelHomotopyGroup.mem_range_ofHomotopyGroup_iff`: exactness at `π_{n+1}(X, A, a₀)`.
* `TauCeti.RelHomotopyGroup.mem_range_boundary_iff`: exactness at `π_n(A, a₀)`.
-/

public section

universe u v

open CategoryTheory Set
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {N : Type v} {X Y : BasedTopPair.{u}}

namespace RelGenLoop

/-! ### Absolute cubes as relative cubes -/

private theorem piOptionEquivProdHomeomorph_symm_mem_boundary {s : I} {t : I^N}
    (h : (s = 0 ∨ s = 1) ∨ t ∈ Cube.boundary N) :
    (piOptionEquivProdHomeomorph fun _ : Option N => I).symm (s, t) ∈ Cube.boundary (Option N) :=
  Cube.boundary_option_iff.2 (by simpa using h)

/-- An absolute generalized loop `I^(Option N) → X` at the basepoint, regarded as a relative cube
`I × I^N → X` with the coordinate `none` as the distinguished first direction. Its face
`{0} × I^N` is constant at the basepoint. -/
def ofGenLoop (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) : RelGenLoop N X :=
  mk ((γ : C(I^(Option N), X.pair.fst)).comp
      ((piOptionEquivProdHomeomorph fun _ : Option N => I).symm : C(I × (I^N), I^(Option N))))
    (fun _ => mem_range.2 ⟨X.basepoint, by
      simpa using (γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (.inl (.inl rfl)))).symm⟩)
    (fun _ _ h => by
      simpa using γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (h.imp .inr id)))

@[simp]
theorem ofGenLoop_apply (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) (y : I × (I^N)) :
    ofGenLoop γ y = γ ((piOptionEquivProdHomeomorph fun _ => I).symm y) := by
  rw [ofGenLoop, mk_apply]
  rfl

@[simp]
theorem ofGenLoop_const : ofGenLoop (GenLoop.const : Ω^ (Option N) X.pair.fst _) = const := by
  ext y
  rw [ofGenLoop_apply, GenLoop.const_apply, const_apply]

/-- The face of an absolute cube in the distinguished direction is constant. -/
@[simp]
theorem boundary_ofGenLoop (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    boundary (ofGenLoop γ) = GenLoop.const := by
  ext t
  rw [boundary_apply_eq_iff, ofGenLoop_apply, GenLoop.const_apply]
  exact γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (.inl (.inl rfl)))

/-- Regarding absolute cubes as relative cubes commutes with the action of morphisms of based
pairs. -/
theorem map_ofGenLoop (f : X ⟶ Y) (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    map f (ofGenLoop γ) =
      ofGenLoop (GenLoop.map (TopPair.Hom.fst f.toTopPairHom).hom f.fst_map_basepoint γ) := by
  ext y
  rw [map_apply, ofGenLoop_apply, ofGenLoop_apply, GenLoop.map_apply]

/-- A homotopy of absolute cubes relative to the boundary is a homotopy through relative cubes. -/
theorem Homotopic.ofGenLoop {γ δ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)}
    (h : GenLoop.Homotopic γ δ) : Homotopic (ofGenLoop γ) (ofGenLoop δ) :=
  homotopic_iff.2 <| Nonempty.map (fun F =>
    { toFun y := F (y.1, (piOptionEquivProdHomeomorph fun _ => I).symm y.2)
      continuous_toFun := by fun_prop
      map_zero_left y := by simp
      map_one_left y := by simp
      prop' r := by
        have h₀ (t : I^N) :=
          piOptionEquivProdHomeomorph_symm_mem_boundary (s := 0) (t := t) (.inl (.inl rfl))
        refine mem_iff.2
          ⟨fun t => ⟨X.basepoint, ((F.eq_fst r (h₀ t)).trans (γ.2 _ (h₀ t))).symm⟩,
            fun s t h => ?_⟩
        have hb := piOptionEquivProdHomeomorph_symm_mem_boundary (h.imp .inr id)
        exact (F.eq_fst r hb).trans (γ.2 _ hb) }) h

/-! ### Exactness at `π_n(A)` -/

/-- A relative cube is a null-homotopy in `X`, relative to the boundary, of its face in `A`. -/
theorem homotopic_map_boundary_const (p : RelGenLoop N X) :
    GenLoop.Homotopic (GenLoop.map X.pair.map.hom rfl (boundary p)) GenLoop.const :=
  ⟨{ toContinuousMap := p
     map_zero_left t := by simp
     map_one_left t := by simp
     prop' r t ht := by
       simp [apply_of_mem_boundary _ _ ht] }⟩

/-- A generalized loop in `A` that is null-homotopic in `X` is the face of a relative cube. -/
theorem exists_boundary_eq {β : Ω^ N X.pair.snd X.basepoint}
    (h : GenLoop.Homotopic (GenLoop.map X.pair.map.hom rfl β) GenLoop.const) :
    ∃ p : RelGenLoop N X, boundary p = β := by
  obtain ⟨F⟩ := h
  refine ⟨mk F.toContinuousMap (fun t => mem_range.2 ⟨β t, ?_⟩) (fun s t h => ?_), ?_⟩
  · simp
  · rcases h with rfl | ht
    · simp
    · exact (F.eq_fst s ht).trans (congrArg X.pair.map.hom (β.2 t ht))
  · ext t
    rw [boundary_apply_eq_iff]
    simp

/-! ### Exactness at `π_{n+1}(X, A)` -/

section Glue

variable (p : RelGenLoop N X)
  (G : (boundary p : C(I^N, X.pair.snd)).HomotopyRel
    (GenLoop.const : Ω^ N X.pair.snd X.basepoint) (Cube.boundary N))

/-- The relative cube `p` with a null-homotopy `G` of its face glued in front of it: a map
`[-1, 1] × I^N → X` (extended to `ℝ × I^N`), equal to `G` reversed on `[-1, 0]` and to `p` on
`[0, 1]`. -/
private noncomputable def glue : C(ℝ × (I^N), X.pair.fst) where
  toFun y := if y.1 ≤ 0 then X.pair.map (G (projIcc 0 1 zero_le_one (-y.1), y.2))
    else p (projIcc 0 1 zero_le_one y.1, y.2)
  continuous_toFun := by
    refine Continuous.if_le ?_ ?_ continuous_fst continuous_const fun y hy => ?_
    · exact X.pair.map.hom.continuous.comp
        (G.continuous.comp ((continuous_projIcc.comp continuous_fst.neg).prodMk continuous_snd))
    · exact (map_continuous (p : C(I × (I^N), X.pair.fst))).comp
        ((continuous_projIcc.comp continuous_fst).prodMk continuous_snd)
    · rw [hy, neg_zero, projIcc_eq_zero.2 le_rfl, ContinuousMap.HomotopyWith.apply_zero]
      exact map_boundary_apply p y.2

private theorem glue_of_nonpos {r : ℝ} (hr : r ≤ 0) (t : I^N) :
    glue p G (r, t) = X.pair.map (G (projIcc 0 1 zero_le_one (-r), t)) := by
  simp [glue, hr]

private theorem glue_of_pos {r : ℝ} (hr : 0 < r) (t : I^N) :
    glue p G (r, t) = p (projIcc 0 1 zero_le_one r, t) := by
  simp [glue, hr.not_ge]

private theorem glue_coe (s : I) (t : I^N) : glue p G (s, t) = p (s, t) := by
  rcases (unitInterval.nonneg s).eq_or_lt with hs | hs
  · rw [glue_of_nonpos p G hs.ge, ← hs, neg_zero, projIcc_eq_zero.2 le_rfl,
      ContinuousMap.HomotopyWith.apply_zero, GenLoop.coe_coe, map_boundary_apply]
    exact congrArg (fun s => p (s, t)) (Subtype.ext hs)
  · rw [glue_of_pos p G hs, projIcc_val]

private theorem glue_mem_range {r : ℝ} (hr : r ≤ 0) (t : I^N) :
    glue p G (r, t) ∈ range X.pair.map := by
  rw [glue_of_nonpos p G hr]
  exact mem_range_self _

private theorem glue_of_mem_boundary (r : ℝ) {t : I^N} (ht : t ∈ Cube.boundary N) :
    glue p G (r, t) = X.pair.map X.basepoint := by
  rcases le_or_gt r 0 with hr | hr
  · rw [glue_of_nonpos p G hr, G.eq_fst _ ht, (boundary p).2 t ht]
  · rw [glue_of_pos p G hr, apply_of_mem_boundary p _ ht]

private theorem glue_neg_one (t : I^N) : glue p G (-1, t) = X.pair.map X.basepoint := by
  rw [glue_of_nonpos p G (by norm_num), neg_neg, projIcc_eq_one.2 le_rfl,
    ContinuousMap.HomotopyWith.apply_one, GenLoop.coe_coe, GenLoop.const_apply]

private theorem glue_one (t : I^N) : glue p G (1, t) = X.pair.map X.basepoint := by
  rw [glue_of_pos p G one_pos, projIcc_eq_one.2 le_rfl, apply_one]

/-- The absolute cube obtained by gluing the null-homotopy `G` of the face of `p` in front of
`p`, reparametrized to unit length. -/
private noncomputable def glueGenLoop : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint) :=
  ⟨⟨fun y => glue p G ((y none : ℝ) - (1 - y none), fun k => y (some k)), by fun_prop⟩,
    fun y hy => by
    rcases Cube.boundary_option_iff.1 hy with (h | h) | h
    · simpa [h] using glue_neg_one p G _
    · simpa [h] using glue_one p G _
    · exact glue_of_mem_boundary p G _ h⟩

private theorem glueGenLoop_apply (y : I^(Option N)) :
    glueGenLoop p G y = glue p G ((y none : ℝ) - (1 - y none), fun k => y (some k)) :=
  (rfl)

/-- Shrinking the glued null-homotopy is a homotopy through relative cubes from `p` to the
absolute cube `glueGenLoop p G`. -/
private theorem homotopic_ofGenLoop_glueGenLoop : Homotopic p (ofGenLoop (glueGenLoop p G)) :=
  homotopic_iff.2
    ⟨{ toFun y := glue p G ((y.2.1 : ℝ) - y.1 * (1 - y.2.1), y.2.2)
       continuous_toFun := by fun_prop
       map_zero_left y := by simpa using glue_coe p G y.1 y.2
       map_one_left y := by
         simp [glueGenLoop_apply]
       prop' w := by
         refine mem_iff.2
           ⟨fun t => glue_mem_range p G (by simpa using unitInterval.nonneg w) t, fun s t h => ?_⟩
         rcases h with rfl | ht
         · simpa using glue_one p G t
         · exact glue_of_mem_boundary p G _ ht }⟩

end Glue

/-- If the face of a relative cube is null-homotopic in `A`, the cube is homotopic through
relative cubes to an absolute cube. -/
theorem exists_homotopic_ofGenLoop {p : RelGenLoop N X}
    (h : GenLoop.Homotopic (boundary p) GenLoop.const) :
    ∃ γ, Homotopic p (ofGenLoop γ) :=
  let ⟨G⟩ := h
  ⟨glueGenLoop p G, homotopic_ofGenLoop_glueGenLoop p G⟩

/-! ### Exactness at `π_{n+1}(X)` -/

section Sweep

variable {γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)}
  (F : (ofGenLoop γ : C(I × (I^N), X.pair.fst)).HomotopyWith const.1 (· ∈ RelGenLoop N X))

/-- The face in `A` swept out by a homotopy `F` through relative cubes from `ofGenLoop γ` to the
constant cube, as a cube in `A` with the time of `F` as its `none` coordinate. -/
private noncomputable def sweepFace : Ω^ (Option N) X.pair.snd X.basepoint :=
  ⟨X.pair.liftSnd ⟨fun y => F (y none, (0, fun k => y (some k))), by fun_prop⟩
      fun y => by simpa using (mem_iff.1 (F.prop (y none))).1 (fun k => y (some k)),
    fun y hy => by
      rw [TopPair.liftSnd_apply_eq_iff, ContinuousMap.coe_mk]
      rcases Cube.boundary_option_iff.1 hy with (h | h) | h
      · rw [h, F.apply_zero, coe_coe, ofGenLoop_apply]
        exact γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (s := 0) (.inl (.inl rfl)))
      · rw [h, F.apply_one, coe_coe, const_apply]
      · simpa using (mem_iff.1 (F.prop (y none))).2 0 _ (Or.inr h)⟩

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

/-- Sweeping the path of `F` is a homotopy relative to the boundary from `γ` to the cube in `A`
swept out by the face. -/
private theorem homotopic_map_sweepFace :
    GenLoop.Homotopic γ (GenLoop.map X.pair.map.hom rfl (sweepFace F)) := by
  have hs : Continuous fun y : I × (I^(Option N)) => sweep y.1 (y.2 none) :=
    continuous_sweep.comp (f := fun y : I × (I^(Option N)) => (y.1, y.2 none))
      (by fun_prop)
  have h₀ (t : I^N) :=
    piOptionEquivProdHomeomorph_symm_mem_boundary (s := 0) (t := t) (.inl (.inl rfl))
  refine ⟨{ toFun y := F ((sweep y.1 (y.2 none)).1, ((sweep y.1 (y.2 none)).2,
              fun k => y.2 (some k)))
            continuous_toFun := F.continuous.comp ((continuous_fst.comp hs).prodMk
              ((continuous_snd.comp hs).prodMk (by fun_prop)))
            map_zero_left y := ?_
            map_one_left y := ?_
            prop' w y hy := ?_ }⟩
  · dsimp only
    rw [sweep_zero, F.apply_zero, coe_coe, ofGenLoop_apply, GenLoop.coe_coe,
      ← piOptionEquivProdHomeomorph_apply, Homeomorph.symm_apply_apply]
  · rw [sweep_one, GenLoop.coe_coe, GenLoop.map_apply]
    exact (TopPair.map_liftSnd (X := X.pair)
      ⟨fun y => F (y none, (0, fun k => y (some k))), by fun_prop⟩ _ y).symm
  · rw [ContinuousMap.coe_mk, γ.2 y hy]
    dsimp only
    rcases Cube.boundary_option_iff.1 hy with (h | h) | h
    · rw [h, sweep_apply_zero, F.apply_zero, coe_coe, ofGenLoop_apply]
      exact γ.2 _ (h₀ _)
    · rw [h]
      rcases sweep_apply_one w with h₁ | h₁
      · rw [h₁, F.apply_one, coe_coe, const_apply]
      · rw [h₁]
        simpa using (mem_iff.1 (F.prop _)).2 1 _ (Or.inl rfl)
    · simpa using (mem_iff.1 (F.prop _)).2 _ _ (Or.inr h)

end Sweep

/-- If the relative cube of an absolute cube `γ` is homotopic through relative cubes to the
constant cube, then `γ` is homotopic relative to the boundary to a cube in `A`. -/
theorem exists_homotopic_map_of_homotopic_const
    {γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)}
    (h : Homotopic (ofGenLoop γ) const) :
    ∃ α : Ω^ (Option N) X.pair.snd X.basepoint,
      GenLoop.Homotopic γ (GenLoop.map X.pair.map.hom rfl α) :=
  let ⟨F⟩ := homotopic_iff.1 h
  ⟨sweepFace F, homotopic_map_sweepFace F⟩

end RelGenLoop

namespace RelHomotopyGroup

/-- The map `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` regarding an absolute cube as a relative cube,
where `π_{n+1}(X, a₀)` is modelled on the cube `I^(Option N)`. -/
def ofHomotopyGroup :
    HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint) → RelHomotopyGroup N X :=
  Quotient.lift (fun γ => mk (RelGenLoop.ofGenLoop γ)) fun _ _ h =>
    mk_eq_mk.2 (RelGenLoop.Homotopic.ofGenLoop h)

@[simp]
theorem ofHomotopyGroup_mk (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    ofHomotopyGroup (⟦γ⟧ : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) =
      mk (RelGenLoop.ofGenLoop γ) :=
  (rfl)

/-- The map `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` preserves the distinguished points. -/
@[simp]
theorem ofHomotopyGroup_one [DecidableEq N] :
    ofHomotopyGroup (1 : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) =
      (default : RelHomotopyGroup N X) := by
  rw [HomotopyGroup.one_def, ofHomotopyGroup_mk, RelGenLoop.ofGenLoop_const, default_eq]

/-- The map `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` is natural in the based pair. -/
theorem map_ofHomotopyGroup (f : X ⟶ Y)
    (a : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    map f (ofHomotopyGroup a) =
      ofHomotopyGroup (HomotopyGroup.map (TopPair.Hom.fst f.toTopPairHom).hom
        f.fst_map_basepoint a) := by
  induction a using Quotient.inductionOn
  rw [ofHomotopyGroup_mk, map_mk, RelGenLoop.map_ofGenLoop, HomotopyGroup.map_mk,
    ofHomotopyGroup_mk]

/-- The composite `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀) → π_n(A, a₀)` is trivial. -/
@[simp]
theorem boundary_ofHomotopyGroup
    (a : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    boundary (ofHomotopyGroup a) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.snd X.basepoint) := by
  induction a using Quotient.inductionOn
  rw [ofHomotopyGroup_mk, boundary_mk, RelGenLoop.boundary_ofGenLoop]

/-- The composite `π_{n+1}(A, a₀) → π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)` is trivial. -/
@[simp]
theorem ofHomotopyGroup_homotopyGroupMap
    (a : HomotopyGroup (Option N) X.pair.snd X.basepoint) :
    ofHomotopyGroup (HomotopyGroup.map X.pair.map.hom rfl a) =
      (default : RelHomotopyGroup N X) := by
  induction a using Quotient.inductionOn
  rw [HomotopyGroup.map_mk, ofHomotopyGroup_mk]
  exact mk_eq_default_of_mem_range _ fun y => by
    rw [RelGenLoop.ofGenLoop_apply, GenLoop.map_apply]
    exact mem_range_self _

/-- The composite `π_{n+1}(X, A, a₀) → π_n(A, a₀) → π_n(X, a₀)` is trivial. -/
@[simp]
theorem homotopyGroupMap_boundary (a : RelHomotopyGroup N X) :
    HomotopyGroup.map X.pair.map.hom rfl (boundary a) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.fst (X.pair.map X.basepoint)) := by
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [boundary_mk, HomotopyGroup.map_mk]
  exact Quotient.sound (RelGenLoop.homotopic_map_boundary_const p)

/-- **Exactness at `π_{n+1}(X, a₀)`.** A class in `π_{n+1}(X, a₀)` comes from `π_{n+1}(A, a₀)`
exactly when it becomes trivial in `π_{n+1}(X, A, a₀)`. -/
theorem mem_range_homotopyGroupMap_iff
    {a : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)} :
    a ∈ range (HomotopyGroup.map X.pair.map.hom rfl) ↔
      ofHomotopyGroup a = (default : RelHomotopyGroup N X) := by
  refine ⟨fun ⟨b, hb⟩ => hb ▸ ofHomotopyGroup_homotopyGroupMap b, fun h => ?_⟩
  induction a using Quotient.inductionOn with | h γ => ?_
  rw [ofHomotopyGroup_mk, default_eq, mk_eq_mk] at h
  obtain ⟨α, hα⟩ := RelGenLoop.exists_homotopic_map_of_homotopic_const h
  exact ⟨⟦α⟧, (Quotient.sound hα).symm⟩

/-- **Exactness at `π_{n+1}(X, A, a₀)`.** A relative class comes from `π_{n+1}(X, a₀)` exactly
when its boundary in `π_n(A, a₀)` is trivial. -/
theorem mem_range_ofHomotopyGroup_iff {a : RelHomotopyGroup N X} :
    a ∈ range ofHomotopyGroup ↔
      boundary a = (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.snd X.basepoint) := by
  refine ⟨fun ⟨b, hb⟩ => hb ▸ boundary_ofHomotopyGroup b, fun h => ?_⟩
  obtain ⟨p, rfl⟩ := mk_surjective a
  rw [boundary_mk] at h
  obtain ⟨γ, hγ⟩ := RelGenLoop.exists_homotopic_ofGenLoop (Quotient.exact h)
  exact ⟨⟦γ⟧, (mk_eq_mk.2 hγ).symm⟩

/-- **Exactness at `π_n(A, a₀)`.** A class in `π_n(A, a₀)` is the boundary of a relative class
exactly when it becomes trivial in `π_n(X, a₀)`. -/
theorem mem_range_boundary_iff {b : HomotopyGroup N X.pair.snd X.basepoint} :
    b ∈ range (boundary (X := X)) ↔
      HomotopyGroup.map X.pair.map.hom rfl b =
        (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.fst (X.pair.map X.basepoint)) := by
  refine ⟨fun ⟨a, ha⟩ => ha ▸ homotopyGroupMap_boundary a, fun h => ?_⟩
  induction b using Quotient.inductionOn with | h β => ?_
  obtain ⟨p, hp⟩ := RelGenLoop.exists_boundary_eq (Quotient.exact h)
  exact ⟨mk p, by rw [boundary_mk, hp]⟩

end RelHomotopyGroup

end TauCeti
