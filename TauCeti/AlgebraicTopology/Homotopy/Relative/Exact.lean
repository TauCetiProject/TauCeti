/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Compression
public import TauCeti.Topology.Homotopy.Cube.Basic

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
* At `π_{n+1}(X)`: by the compression criterion
  (`TauCeti.RelGenLoop.exists_homotopicRel_of_homotopic_const`), an absolute cube that is
  trivial as a relative cube is homotopic, relative to the boundary, to a cube in `A`.

## Main declarations

* `TauCeti.RelGenLoop.ofGenLoop`, `TauCeti.RelHomotopyGroup.ofHomotopyGroup`: the map
  `π_{n+1}(X, a₀) → π_{n+1}(X, A, a₀)`, natural by `TauCeti.RelHomotopyGroup.map_ofHomotopyGroup`.
* `TauCeti.RelHomotopyGroup.mem_range_homotopyGroupMap_iff`: exactness at `π_{n+1}(X, a₀)`.
* `TauCeti.RelHomotopyGroup.mem_range_ofHomotopyGroup_iff`: exactness at `π_{n+1}(X, A, a₀)`.
* `TauCeti.RelHomotopyGroup.mem_range_boundary_iff`: exactness at `π_n(A, a₀)`.
* `TauCeti.RelHomotopyGroup.subsingleton_of_injective_of_surjective`: `π_{n+1}(X, A, a₀)` is
  trivial when `π_n(A, a₀) → π_n(X, a₀)` is injective and `π_{n+1}(A, a₀) → π_{n+1}(X, a₀)` is
  surjective, and `TauCeti.RelHomotopyGroup.subsingleton_of_subsingleton_homotopyGroup` in
  particular when `π_n(A, a₀)` and `π_{n+1}(X, a₀)` are trivial.
* `TauCeti.RelHomotopyGroup.surjective_ofHomotopyGroup_of_subsingleton`: every class of
  `π_{n+1}(X, A, a₀)` comes from `π_{n+1}(X, a₀)` when `π_n(A, a₀)` is trivial.
-/

public section

universe u v

open CategoryTheory Set
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {N : Type v} {X Y : BasedTopPair.{u}}

namespace RelGenLoop

/-! ### Absolute cubes as relative cubes -/

/-- An absolute generalized loop `I^(Option N) → X` at the basepoint, regarded as a relative cube
`I × I^N → X` with the coordinate `none` as the distinguished first direction. Its face
`{0} × I^N` is constant at the basepoint. -/
def ofGenLoop (γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)) : RelGenLoop N X :=
  mk ((γ : C(I^(Option N), X.pair.fst)).comp
      ((piOptionEquivProdHomeomorph fun _ : Option N => I).symm : C(I × (I^N), I^(Option N))))
    (fun _ => mem_range.2 ⟨X.basepoint, by
      simpa using (γ.2 _ <| piOptionEquivProdHomeomorph_symm_mem_boundary <|
        Cube.mk_zero_mem_prodBoundary _).symm⟩)
    (fun _ _ h => by
      simpa using
        γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_mem_prodBoundary h)))

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
  exact γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_zero_mem_prodBoundary _))

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
          piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_zero_mem_prodBoundary t)
        refine mem_iff.2
          ⟨fun t => ⟨X.basepoint, ((F.eq_fst r (h₀ t)).trans (γ.2 _ (h₀ t))).symm⟩,
            fun s t h => ?_⟩
        have hb := piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_mem_prodBoundary h)
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
    · exact (F.eq_fst s ht).trans
        ((GenLoop.map_apply _ _ β t).trans (congrArg X.pair.map.hom (β.2 t ht)))
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

/-- If the relative cube of an absolute cube `γ` is homotopic through relative cubes to the
constant cube, then `γ` is homotopic relative to the boundary to a cube in `A`. -/
theorem exists_homotopic_map_of_homotopic_const
    {γ : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)}
    (h : Homotopic (ofGenLoop γ) const) :
    ∃ α : Ω^ (Option N) X.pair.snd X.basepoint,
      GenLoop.Homotopic γ (GenLoop.map X.pair.map.hom rfl α) := by
  obtain ⟨q, ⟨H⟩, hq⟩ := exists_homotopicRel_of_homotopic_const h
  let e : C(I^(Option N), I × (I^N)) := piOptionEquivProdHomeomorph fun _ : Option N => I
  have hb {y : I^(Option N)} (hy : y ∈ Cube.boundary (Option N)) : e y ∈ Cube.prodBoundary N :=
    piOptionEquivProdHomeomorph_mem_prodBoundary_iff.2 hy
  have hγ (y : I^(Option N)) : ofGenLoop γ (e y) = γ y := by
    rw [ofGenLoop_apply]
    exact congrArg γ (Homeomorph.symm_apply_apply _ y)
  refine ⟨⟨X.pair.liftSnd (q.comp e) fun y => hq _, fun y hy => ?_⟩, ⟨?_⟩⟩
  · rw [TopPair.liftSnd_apply_eq_iff, ContinuousMap.comp_apply, ← H.fst_eq_snd (hb hy), coe_coe,
      hγ]
    exact γ.2 y hy
  · exact
      { toFun y := H (y.1, e y.2)
        continuous_toFun := by fun_prop
        map_zero_left y := by simpa using hγ y
        map_one_left y := by
          rw [H.apply_one, GenLoop.coe_coe, GenLoop.map_apply]
          exact (TopPair.map_liftSnd (X := X.pair) (q.comp e) _ y).symm
        prop' w y hy := by simpa [hγ] using H.eq_fst w (hb hy) }

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

/-- If the inclusion `A ↪ X` induces an injection `π_n(A, a₀) → π_n(X, a₀)` and a surjection
`π_{n+1}(A, a₀) → π_{n+1}(X, a₀)`, then the relative homotopy set `π_{n+1}(X, A, a₀)` is
trivial. -/
theorem subsingleton_of_injective_of_surjective
    (hinj : Function.Injective
      (HomotopyGroup.map (N := N) (x := X.basepoint) X.pair.map.hom rfl))
    (hsurj : Function.Surjective
      (HomotopyGroup.map (N := Option N) (x := X.basepoint) X.pair.map.hom rfl)) :
    Subsingleton (RelHomotopyGroup N X) := by
  suffices h : ∀ a : RelHomotopyGroup N X, a = default from
    ⟨fun a b => (h a).trans (h b).symm⟩
  intro a
  have hb : boundary a = (⟦GenLoop.const⟧ : HomotopyGroup N X.pair.snd X.basepoint) :=
    hinj <| by rw [homotopyGroupMap_boundary, HomotopyGroup.map_mk, GenLoop.map_const]
  obtain ⟨c, rfl⟩ := mem_range_ofHomotopyGroup_iff.2 hb
  obtain ⟨d, rfl⟩ := hsurj c
  exact ofHomotopyGroup_homotopyGroupMap d

/-- If `π_n(A, a₀)` and `π_{n+1}(X, a₀)` are trivial, then so is `π_{n+1}(X, A, a₀)`. -/
theorem subsingleton_of_subsingleton_homotopyGroup
    (hA : Subsingleton (HomotopyGroup N X.pair.snd X.basepoint))
    (hX : Subsingleton (HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint))) :
    Subsingleton (RelHomotopyGroup N X) :=
  subsingleton_of_injective_of_surjective (fun _ _ _ => Subsingleton.elim _ _)
    fun _ => ⟨⟦GenLoop.const⟧, Subsingleton.elim _ _⟩

/-- If `π_n(A, a₀)` is trivial, then every class of `π_{n+1}(X, A, a₀)` comes from
`π_{n+1}(X, a₀)`. -/
theorem surjective_ofHomotopyGroup_of_subsingleton
    (hA : Subsingleton (HomotopyGroup N X.pair.snd X.basepoint)) :
    Function.Surjective (ofHomotopyGroup : _ → RelHomotopyGroup N X) :=
  fun _ => mem_range_ofHomotopyGroup_iff.2 (Subsingleton.elim _ _)

end RelHomotopyGroup

end TauCeti
