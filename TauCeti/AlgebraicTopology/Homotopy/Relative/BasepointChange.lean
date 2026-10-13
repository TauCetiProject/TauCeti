/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Subpath
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Group
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange

/-!
# Base-point change for relative homotopy groups

Let `X = (X, A, a)` be a based pair and let `γ` be a path in `A` from `a` to a point `b`, so that
`⟨X.pair, b⟩` is the based pair `(X, A, b)`. This file constructs the base-point-change map
`TauCeti.RelHomotopyGroup.transport γ : π_{n+1}(X, A, a) → π_{n+1}(X, A, b)`,
proves that it is a bijection with inverse the transport along the reversed path, and, in
degrees at least two, a group isomorphism `TauCeti.RelHomotopyGroup.mulEquivOfPath γ`. It is
compatible with the maps of the long exact sequence of the pair: with the boundary map to
`π_n(A)` and the absolute base-point change in `A`, and with the map from `π_{n+1}(X)` and the
absolute base-point change in `X`. It is natural in morphisms of based pairs.

A *homotopy along `γ`* (`TauCeti.RelGenLoop.HomotopyAlong`) from a relative cube `p` at `a` to a
relative cube `q` at `b` is a homotopy whose stage at time `t` sends the face `{0} × I^N` into `A`,
and the face `{1} × I^N` and the sides `I × ∂I^N` to `γ t`. The transport is characterised by
these homotopies: whenever there is one from `p` to `q`, the transport of the class of `p` is the
class of `q` (`TauCeti.RelGenLoop.HomotopyAlong.transport_mk`). All the laws are read off from
this characterisation, by composing, reversing or restricting homotopies along paths.

## Construction

* **Existence.** Every relative cube `p` admits a homotopy along `γ`
  (`TauCeti.RelGenLoop.collarHomotopyAlong`), ending at the cube
  `TauCeti.RelGenLoop.transport γ p`. Double `p` along its distinguished coordinate to the
  absolute cube `(u, z) ↦ p (|2u - 1|, z)` of `I^(Option N)`, which is constant on the boundary,
  and apply the collar homotopy `TauCeti.GenLoop.collarHomotopy` of absolute base-point change.
  On the half `u ≥ 1 / 2` this is a homotopy along `γ`: the collar shrinks towards the centre of
  the cube, which lies on the hyperplane `u = 1 / 2` corresponding to the face `{0} × I^N`, so
  that face only sees values of `p` on it and values of `γ`, all in `A`.
* **Canonicity.** Relative cubes at `b` are generalized loops in the space `P_b` of paths from
  `A` to `b` (`TauCeti.RelGenLoop.pathSpaceHomeo`). Following each path of `P_a` by `γ` is a map
  `P_a → P_b`, and following the paths of a homotopy along `γ` at time `t` by the tail
  `γ.subpath t 1` turns it into an absolute homotopy along a fixed path in `P_b`. By canonicity
  of absolute transport (`TauCeti.GenLoop.HomotopyAlong.homotopic_transport`) its end is
  determined up to homotopy by its start. Hence the transport, defined as the composite of these
  maps on homotopy groups, sends the class of `p` to the class of `q`.

## Main declarations

* `TauCeti.RelGenLoop.HomotopyAlong`: homotopies of relative cubes along a path in the subspace.
* `TauCeti.RelGenLoop.transport`, `TauCeti.RelGenLoop.collarHomotopyAlong`: a relative cube
  transported along a path, with a homotopy along the path.
* `TauCeti.RelGenLoop.HomotopyAlong.homotopic_transport`: **canonicity**, any homotopy along `γ`
  starting at `p` ends at a cube homotopic to `TauCeti.RelGenLoop.transport γ p`.
* `TauCeti.RelGenLoop.homotopic_transport_of_path_homotopic`: transport along homotopic paths
  gives homotopic cubes.
* `TauCeti.RelHomotopyGroup.transport`: base-point change on relative homotopy sets, with
  `transport_refl`, `transport_trans`, `transport_congr`, `transport_symm_transport` and
  `transport_default`.
* `TauCeti.RelHomotopyGroup.equivOfPath`, `TauCeti.RelHomotopyGroup.mulEquivOfPath`:
  **a path from `a` to `b` in `A` induces a bijection `π_{n+1}(X, A, a) ≃ π_{n+1}(X, A, b)`, which
  is a group isomorphism when `n ≥ 1`.**
* `TauCeti.RelHomotopyGroup.boundary_transport`,
  `TauCeti.RelHomotopyGroup.transport_ofHomotopyGroup`, `TauCeti.RelHomotopyGroup.map_transport`:
  compatibility with the long exact sequence and naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the change of base point for relative homotopy groups along a path in `A`.
-/

public section

noncomputable section

universe u v

open CategoryTheory Set
open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {N : Type v} {X : BasedTopPair.{u}} {b c : X.pair.snd}

namespace RelGenLoop

/-! ### Homotopies along a path in the subspace -/

/-- A homotopy from a relative cube `p` of the based pair `X = (X, A, a)` to a relative cube `q` of
`(X, A, b)`, along a path `γ` in `A` from `a` to `b`: at time `t` it sends the face `{0} × I^N` into
`A`, and the face `{1} × I^N` and the sides `I × ∂I^N` to `γ t`. -/
structure HomotopyAlong (γ : Path X.basepoint b) (p : RelGenLoop N X)
    (q : RelGenLoop N ⟨X.pair, b⟩) extends
    ContinuousMap.Homotopy (p : C(I × (I^N), X.pair.fst)) (q : C(I × (I^N), X.pair.fst)) where
  /-- at every time the face `{0} × I^N` goes into the subspace -/
  apply_zero_mem_range : ∀ (t : I) (z : I^N), toHomotopy (t, (0, z)) ∈ Set.range X.pair.map
  /-- at every time the rest of the boundary goes to the moving basepoint -/
  apply_eq_path : ∀ (t s : I) (z : I^N), (s = 1 ∨ z ∈ Cube.boundary N) →
    toHomotopy (t, (s, z)) = X.pair.map (γ t)

namespace HomotopyAlong

instance instFunLike {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} :
    FunLike (HomotopyAlong γ p q) (I × (I × (I^N))) X.pair.fst where
  coe h := h.toHomotopy
  coe_injective h k hhk := by
    cases h
    cases k
    congr
    exact ContinuousMap.Homotopy.ext fun y => congrFun hhk y

instance {γ : Path X.basepoint b} {p : RelGenLoop N X} {q : RelGenLoop N ⟨X.pair, b⟩} :
    ContinuousMap.HomotopyLike (HomotopyAlong γ p q)
      (p : C(I × (I^N), X.pair.fst)) (q : C(I × (I^N), X.pair.fst)) where
  map_continuous h := h.toHomotopy.continuous
  map_zero_left h := h.map_zero_left
  map_one_left h := h.map_one_left

/-- The constant homotopy is a homotopy along the constant path. -/
def refl (p : RelGenLoop N X) : HomotopyAlong (Path.refl X.basepoint) p p where
  toHomotopy := ContinuousMap.Homotopy.refl _
  apply_zero_mem_range _ z := RelGenLoop.apply_zero_mem_range p z
  apply_eq_path _ s z h := (mem_iff.1 p.2).2 s z h

/-- Reversing a homotopy along `γ` in time gives a homotopy along the reversed path. -/
def symm {γ : Path X.basepoint b} {p : RelGenLoop N X} {q : RelGenLoop N ⟨X.pair, b⟩}
    (h : HomotopyAlong γ p q) : HomotopyAlong (X := ⟨X.pair, b⟩) γ.symm q p where
  toHomotopy := h.toHomotopy.symm
  apply_zero_mem_range t z := h.apply_zero_mem_range (σ t) z
  apply_eq_path t s z hsz := h.apply_eq_path (σ t) s z hsz

/-- Concatenating two homotopies along paths, in the time direction, gives a homotopy along the
concatenated path. -/
def trans {γ : Path X.basepoint b} {δ : Path b c} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} {r : RelGenLoop N ⟨X.pair, c⟩} (h₁ : HomotopyAlong γ p q)
    (h₂ : HomotopyAlong (X := ⟨X.pair, b⟩) δ q r) : HomotopyAlong (γ.trans δ) p r where
  toHomotopy := h₁.toHomotopy.trans h₂.toHomotopy
  apply_zero_mem_range t z := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    exacts [h₁.apply_zero_mem_range _ z, h₂.apply_zero_mem_range _ z]
  apply_eq_path t s z hsz := by
    rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    exacts [h₁.apply_eq_path _ s z hsz, h₂.apply_eq_path _ s z hsz]

/-- A morphism of based pairs `f : X ⟶ Y` carries a homotopy along `γ` to a homotopy along the
image of `γ`, which starts at the basepoint of `Y`. -/
def map {Y : BasedTopPair.{u}} (f : X ⟶ Y) {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) :
    HomotopyAlong
      ((γ.map (TopPair.Hom.snd f.toTopPairHom).hom.continuous).cast f.map_basepoint.symm rfl)
      (RelGenLoop.map f p)
      (RelGenLoop.map (⟨f.toTopPairHom, rfl⟩ :
        (⟨X.pair, b⟩ : BasedTopPair) ⟶ ⟨Y.pair, TopPair.Hom.snd f.toTopPairHom b⟩) q) where
  toFun y := TopPair.Hom.fst f.toTopPairHom (h.toHomotopy y)
  continuous_toFun :=
    (TopPair.Hom.fst f.toTopPairHom).hom.continuous.comp h.toHomotopy.continuous
  map_zero_left y := by simp
  map_one_left y := by simp
  apply_zero_mem_range t z := by
    obtain ⟨a', ha'⟩ := h.apply_zero_mem_range t z
    exact ⟨TopPair.Hom.snd f.toTopPairHom a',
      (TopPair.Hom.w_apply f.toTopPairHom a').trans
        (congrArg (TopPair.Hom.fst f.toTopPairHom) ha')⟩
  apply_eq_path t s z hsz :=
    (congrArg (TopPair.Hom.fst f.toTopPairHom) (h.apply_eq_path t s z hsz)).trans
      (TopPair.Hom.w_apply f.toTopPairHom (γ t)).symm

/-- Restricting a homotopy along `γ` to the face `{0} × I^N` gives a homotopy along `γ` of
generalized loops in the subspace. -/
def boundary {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) :
    GenLoop.HomotopyAlong γ (RelGenLoop.boundary p) (RelGenLoop.boundary q) where
  toContinuousMap := X.pair.liftSnd
    ⟨fun y => h.toHomotopy (y.1, (0, y.2)),
      h.toHomotopy.continuous.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩
    fun y => h.apply_zero_mem_range y.1 y.2
  map_zero_left z := by
    rw [ContinuousMap.toFun_eq_coe, TopPair.liftSnd_apply_eq_iff]
    exact (h.toHomotopy.apply_zero (0, z)).trans (map_boundary_apply p z).symm
  map_one_left z := by
    rw [ContinuousMap.toFun_eq_coe, TopPair.liftSnd_apply_eq_iff]
    exact (h.toHomotopy.apply_one (0, z)).trans (map_boundary_apply q z).symm
  map_boundary t z hz :=
    (TopPair.liftSnd_apply_eq_iff _ _ _ _).2 (h.apply_eq_path t 0 z (Or.inr hz))

/-- An absolute homotopy along the image of `γ` in `X`, of cubes `I^(Option N)`, is a homotopy
along `γ` of the corresponding relative cubes. -/
def ofGenLoop {γ : Path X.basepoint b}
    {f : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint)}
    {g : Ω^ (Option N) X.pair.fst (X.pair.map b)}
    (h : GenLoop.HomotopyAlong (γ.map X.pair.map.hom.continuous) f g) :
    HomotopyAlong γ (ofGenLoop f) (ofGenLoop (X := ⟨X.pair, b⟩) g) where
  toFun ty := h.toHomotopy (ty.1, (piOptionEquivProdHomeomorph fun _ => I).symm ty.2)
  continuous_toFun := by fun_prop
  map_zero_left y := by simp
  map_one_left y := by simp
  apply_zero_mem_range t z := ⟨γ t, (h.map_boundary t _
    (piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_zero_mem_prodBoundary z))).symm⟩
  apply_eq_path t s z hsz := h.map_boundary t _
    (piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_mem_prodBoundary hsz))

/-- The constant cube at `γ t` is a homotopy along `γ` between the constant relative cubes. -/
protected def const (γ : Path X.basepoint b) :
    HomotopyAlong γ (RelGenLoop.const : RelGenLoop N X) RelGenLoop.const where
  toFun ty := X.pair.map (γ ty.1)
  continuous_toFun := X.pair.map.hom.continuous.comp (γ.continuous.comp continuous_fst)
  map_zero_left _ := by simp
  map_one_left _ := by simp
  apply_zero_mem_range t _ := ⟨γ t, rfl⟩
  apply_eq_path _ _ _ _ := rfl

end HomotopyAlong

/-! ### Existence: the doubled collar -/

/-- The fold `u ↦ |2u - 1|` of the unit interval onto itself. -/
private def foldI (u : I) : I :=
  ⟨|2 * (u : ℝ) - 1|, abs_nonneg _, abs_le.2 ⟨by linarith [u.2.1], by linarith [u.2.2]⟩⟩

private theorem continuous_foldI : Continuous foldI :=
  Continuous.subtype_mk (by fun_prop) _

/-- The affine map `s ↦ (1 + s) / 2` of the unit interval onto its upper half. -/
private def unfoldI (s : I) : I :=
  ⟨(1 + s) / 2, by linarith [s.2.1], by linarith [s.2.2]⟩

private theorem continuous_unfoldI : Continuous unfoldI :=
  Continuous.subtype_mk (by fun_prop) _

private theorem foldI_unfoldI (s : I) : foldI (unfoldI s) = s := by
  apply Subtype.ext
  simp only [foldI, unfoldI]
  rw [abs_of_nonneg (by linarith [s.2.1])]
  ring

private theorem foldI_eq_one {u : I} (hu : u = 0 ∨ u = 1) : foldI u = 1 := by
  apply Subtype.ext
  rcases hu with rfl | rfl <;> norm_num [foldI]

private theorem foldI_eq_zero {u : I} (hu : (u : ℝ) = 1 / 2) : foldI u = 0 := by
  apply Subtype.ext
  simp only [foldI, hu]
  norm_num

/-- The relative cube `p` doubled along its distinguished coordinate: the absolute cube
`v ↦ p (|2 v_none - 1|, (v_(some i))_i)` of `I^(Option N)`, which is constant on its boundary. -/
private def double (p : RelGenLoop N X) : Ω^ (Option N) X.pair.fst (X.pair.map X.basepoint) :=
  ⟨(p : C(I × (I^N), X.pair.fst)).comp
      ⟨fun v => (foldI (v none), fun i => v (some i)),
        (continuous_foldI.comp (continuous_apply none)).prodMk
          (continuous_pi fun i => continuous_apply (some i))⟩,
    fun v hv => by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, coe_coe]
      rcases Cube.boundary_option_iff.1 hv with h | hz
      · rw [foldI_eq_one h]
        exact apply_one p _
      · exact apply_of_mem_boundary p _ hz⟩

private theorem double_apply (p : RelGenLoop N X) (v : I^(Option N)) :
    double p v = p (foldI (v none), fun i => v (some i)) :=
  (rfl)

/-- The embedding `(s, z) ↦ ((1 + s) / 2, z)` of `I × I^N` onto the upper half of `I^(Option N)`,
on which the doubling of a relative cube restricts back to the cube. -/
private def unfoldCube : C(I × (I^N), I^(Option N)) :=
  ((piOptionEquivProdHomeomorph fun _ : Option N => I).symm : C(I × (I^N), I^(Option N))).comp
    ⟨fun y => (unfoldI y.1, y.2), (continuous_unfoldI.comp continuous_fst).prodMk continuous_snd⟩

private theorem unfoldCube_none (y : I × (I^N)) : unfoldCube y none = unfoldI y.1 := by
  simp [unfoldCube]

private theorem unfoldCube_some (y : I × (I^N)) (i : N) : unfoldCube y (some i) = y.2 i := by
  simp [unfoldCube]

private theorem double_unfoldCube (p : RelGenLoop N X) (y : I × (I^N)) :
    double p (unfoldCube y) = p y := by
  simp only [double_apply, unfoldCube_none, foldI_unfoldI, unfoldCube_some]

private theorem unfoldCube_mem_boundary {s : I} {z : I^N} (h : s = 1 ∨ z ∈ Cube.boundary N) :
    unfoldCube (s, z) ∈ Cube.boundary (Option N) := by
  rw [Cube.boundary_option_iff, unfoldCube_none]
  rcases h with rfl | hz
  · exact Or.inl (Or.inr (Subtype.ext (by norm_num [unfoldI])))
  · exact Or.inr (by simpa only [unfoldCube_some] using hz)

section Collar

variable [Fintype N]

/-- The collar homotopy of the doubled cube, restricted to the upper half `I × I^N`. -/
private def relCollarHomotopy (γ : Path X.basepoint b) (p : RelGenLoop N X) :
    C(I × (I × (I^N)), X.pair.fst) :=
  (GenLoop.collarHomotopy (γ.map X.pair.map.hom.continuous) (double p)).comp
    ((ContinuousMap.id I).prodMap unfoldCube)

private theorem relCollarHomotopy_apply (γ : Path X.basepoint b) (p : RelGenLoop N X) (t : I)
    (y : I × (I^N)) :
    relCollarHomotopy γ p (t, y) =
      GenLoop.collarHomotopy (γ.map X.pair.map.hom.continuous) (double p) (t, unfoldCube y) :=
  (rfl)

private theorem relCollarHomotopy_zero (γ : Path X.basepoint b) (p : RelGenLoop N X)
    (y : I × (I^N)) : relCollarHomotopy γ p (0, y) = p y := by
  rw [relCollarHomotopy_apply, GenLoop.collarHomotopy_zero, double_unfoldCube]

private theorem relCollarHomotopy_eq (γ : Path X.basepoint b) (p : RelGenLoop N X) (t s : I)
    (z : I^N) (h : s = 1 ∨ z ∈ Cube.boundary N) :
    relCollarHomotopy γ p (t, (s, z)) = X.pair.map (γ t) := by
  rw [relCollarHomotopy_apply, GenLoop.collarHomotopy_boundary _ _ _ (unfoldCube_mem_boundary h)]
  rfl

/-- The face `{0} × I^N` lies on the hyperplane through the centre of the doubled cube, which a
collar of radius `r` rescales into itself. So on that face a collar of the doubled cube only takes
values of `p` on the face and values `w` of the outer family. -/
private theorem ite_double_unfoldCube_zero_mem_range (p : RelGenLoop N X) {r : ℝ}
    (hr : 1 / 2 ≤ r) (z : I^N) {w : X.pair.fst} (hw : w ∈ Set.range X.pair.map) :
    (if cubeRadius (unfoldCube ((0 : I), z)) ≤ r then
      double p (cubeScale (1 / r) (unfoldCube ((0 : I), z))) else w) ∈ Set.range X.pair.map := by
  split_ifs with hrz
  · rw [double_apply]
    have hpos : (0 : ℝ) < r := by linarith
    have hhalf : ((cubeScale (1 / r) (unfoldCube ((0 : I), z)) none : I) : ℝ) = 1 / 2 := by
      rw [cubeScale_apply_coe (by positivity)
        (by rw [one_div_mul_eq_div, div_le_one hpos]; exact hrz), unfoldCube_none]
      simp [unfoldI]
    rw [foldI_eq_zero hhalf]
    exact apply_zero_mem_range p _
  · exact hw

private theorem relCollarHomotopy_zero_mem_range (γ : Path X.basepoint b) (p : RelGenLoop N X)
    (t : I) (z : I^N) : relCollarHomotopy γ p (t, (0, z)) ∈ Set.range X.pair.map := by
  rw [relCollarHomotopy_apply, GenLoop.collarHomotopy_apply]
  exact ite_double_unfoldCube_zero_mem_range p (by linarith [t.2.2]) z ⟨γ _, rfl⟩

/-- **A relative cube transported along a path in the subspace**: the end of the collar homotopy
of its doubling, restricted to the upper half of the cube. -/
def transport (γ : Path X.basepoint b) (p : RelGenLoop N X) : RelGenLoop N ⟨X.pair, b⟩ :=
  mk ⟨fun y => relCollarHomotopy γ p (1, y),
      (relCollarHomotopy γ p).continuous.comp (Continuous.prodMk_right 1)⟩
    (fun z => relCollarHomotopy_zero_mem_range γ p 1 z)
    fun s z h => (relCollarHomotopy_eq γ p 1 s z h).trans (congrArg X.pair.map γ.target)

/-- The collar homotopy of the doubling is a homotopy along `γ` from `p` to its transport. -/
def collarHomotopyAlong (γ : Path X.basepoint b) (p : RelGenLoop N X) :
    HomotopyAlong γ p (transport γ p) where
  toContinuousMap := relCollarHomotopy γ p
  map_zero_left := relCollarHomotopy_zero γ p
  map_one_left y := by
    rw [ContinuousMap.toFun_eq_coe, coe_coe, transport, mk_apply]
    rfl
  apply_zero_mem_range := relCollarHomotopy_zero_mem_range γ p
  apply_eq_path := relCollarHomotopy_eq γ p

private theorem transport_apply (γ : Path X.basepoint b) (p : RelGenLoop N X) (y : I × (I^N)) :
    transport γ p y = relCollarHomotopy γ p (1, y) := by
  rw [transport, mk_apply]
  rfl

/-- The transported cube, written out on the doubled cube: `p` shrunk to half size, with the
values of `γ` on the collar. -/
private theorem transport_apply_eq (γ : Path X.basepoint b) (p : RelGenLoop N X)
    (y : I × (I^N)) :
    transport γ p y =
      if cubeRadius (unfoldCube y) ≤ 1 / 2 then double p (cubeScale (1 / (1 / 2)) (unfoldCube y))
      else X.pair.map (γ (projIcc 0 1 zero_le_one
        (2 - 2 * (1 / 2) / max (cubeRadius (unfoldCube y)) (1 / 2)))) := by
  have h1 : (2 - ((1 : I) : ℝ)) / 2 = 1 / 2 := by norm_num
  rw [transport_apply, relCollarHomotopy_apply, GenLoop.collarHomotopy_apply, h1]
  rfl

/-- Transport along homotopic paths gives homotopic relative cubes. Collaring the doubled cube
along the paths of a homotopy between the two paths deforms one transported cube into the other
through relative cubes. -/
theorem homotopic_transport_of_path_homotopic {γ γ' : Path X.basepoint b} (h : γ.Homotopic γ')
    (p : RelGenLoop N X) : Homotopic (transport γ p) (transport γ' p) := by
  obtain ⟨G⟩ := h
  let G' : C(I × I, X.pair.fst) := X.pair.map.hom.comp G.toContinuousMap
  have hFG : ∀ s : I, ∀ v ∈ Cube.boundary (Option N),
      ((double p : C(I^(Option N), X.pair.fst)).comp ContinuousMap.snd) (s, v) = G' (s, 0) := by
    intro s v hv
    simp [G', (double p).2 v hv]
  let K := collar (ContinuousMap.const I (1 / 2 : ℝ))
    ((double p : C(I^(Option N), X.pair.fst)).comp ContinuousMap.snd) G' (fun _ => le_rfl) hFG
  have hK (s : I) (y : I × (I^N)) : K (s, unfoldCube y) =
      if cubeRadius (unfoldCube y) ≤ 1 / 2 then double p (cubeScale (1 / (1 / 2)) (unfoldCube y))
      else X.pair.map (G (s, projIcc 0 1 zero_le_one
        (2 - 2 * (1 / 2) / max (cubeRadius (unfoldCube y)) (1 / 2)))) :=
    collar_apply _ _ _ _ _ _ _
  refine homotopic_iff.2
    ⟨{ toFun := fun sy => K (sy.1, unfoldCube sy.2)
       continuous_toFun := K.continuous.comp
         (continuous_fst.prodMk (unfoldCube.continuous.comp continuous_snd))
       map_zero_left := fun y => ?_
       map_one_left := fun y => ?_
       prop' := fun s => mem_iff.2 ⟨fun z => ?_, fun s' z hsz => ?_⟩ }⟩
  · rw [hK, coe_coe, transport_apply_eq]
    split_ifs
    · rfl
    · exact congrArg X.pair.map (G.apply_zero _)
  · rw [hK, coe_coe, transport_apply_eq]
    split_ifs
    · rfl
    · exact congrArg X.pair.map (G.apply_one _)
  · simp only [ContinuousMap.coe_mk]
    rw [hK]
    exact ite_double_unfoldCube_zero_mem_range p le_rfl z ⟨_, rfl⟩
  · simp only [ContinuousMap.coe_mk]
    rw [hK, (cubeRadius_eq_one_iff _).2 (unfoldCube_mem_boundary hsz)]
    norm_num

end Collar

/-! ### Canonicity, through the path space -/

/-- The path `q` followed by the tail `γ.subpath t 1` of `γ`, which runs from `γ t` to `b`, as a
continuous function of the pair `(t, q)` with `q 1 = γ t`. -/
private def concatTail (γ : Path X.basepoint b) :
    C({x : I × C(I, X.pair.fst) // x.2 1 = X.pair.map (γ x.1)}, C(I, X.pair.fst)) :=
  ContinuousMap.curry ⟨↿fun x : {x : I × C(I, X.pair.fst) // x.2 1 = X.pair.map (γ x.1)} =>
      (⟨x.1.2, rfl, x.2⟩ : Path (x.1.2 0) _).trans
        ((γ.map X.pair.map.hom.continuous).subpath x.1.1 1),
    Path.trans_continuous_family _
      (continuous_eval.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
      _ ((γ.map X.pair.map.hom.continuous).subpath_continuous_family.comp
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_const.prodMk continuous_snd)))⟩

private theorem concatTail_apply (γ : Path X.basepoint b)
    (x : {x : I × C(I, X.pair.fst) // x.2 1 = X.pair.map (γ x.1)}) (s : I) :
    concatTail γ x s = if (s : ℝ) ≤ 1 / 2 then x.1.2 (projIcc 0 1 zero_le_one (2 * s))
      else X.pair.map (γ (Icc.convexComb x.1.1 1 (projIcc 0 1 zero_le_one (2 * s - 1)))) :=
  (rfl)

private theorem concatTail_mem (γ : Path X.basepoint b)
    (x : {x : I × C(I, X.pair.fst) // x.2 1 = X.pair.map (γ x.1)})
    (hx : x.1.2 0 ∈ Set.range X.pair.map) :
    concatTail γ x ∈ BasedTopPair.pathSpace ⟨X.pair, b⟩ := by
  refine (BasedTopPair.mem_pathSpace_iff _).2 ⟨?_, ?_⟩
  · simpa [concatTail_apply] using hx
  · norm_num [concatTail_apply]

private theorem pathSpace_apply_one_eq (γ : Path X.basepoint b) (q : BasedTopPair.pathSpace X) :
    (q : C(I, X.pair.fst)) 1 = X.pair.map (γ 0) := by
  rw [γ.source]
  exact ((BasedTopPair.mem_pathSpace_iff _).1 q.2).2

/-- Following each path from `A` to `a` by `γ`, a map from the paths from `A` to `a` to the paths
from `A` to `b`. -/
private def pathSpaceConcat (γ : Path X.basepoint b) :
    C(BasedTopPair.pathSpace X, BasedTopPair.pathSpace ⟨X.pair, b⟩) where
  toFun q := ⟨concatTail γ ⟨(0, q.1), pathSpace_apply_one_eq γ q⟩,
    concatTail_mem γ _ ((BasedTopPair.mem_pathSpace_iff _).1 q.2).1⟩
  continuous_toFun := Continuous.subtype_mk ((concatTail γ).continuous.comp
    (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _)) _

/-- The path `t ↦ c_{γ t} ⋆ γ.subpath t 1` in the space of paths from `A` to `b`, from the image of
the constant path at `a` under `pathSpaceConcat γ` to the constant path at `b`. -/
private def pathSpaceTail (γ : Path X.basepoint b) :
    Path (pathSpaceConcat γ (BasedTopPair.pathSpaceBase X))
      (BasedTopPair.pathSpaceBase ⟨X.pair, b⟩) where
  toFun t := ⟨concatTail γ ⟨(t, ContinuousMap.const I (X.pair.map (γ t))), rfl⟩,
    concatTail_mem γ _ ⟨γ t, rfl⟩⟩
  continuous_toFun := Continuous.subtype_mk ((concatTail γ).continuous.comp
    (Continuous.subtype_mk (continuous_id.prodMk (ContinuousMap.continuous_const'.comp
      (X.pair.map.hom.continuous.comp γ.continuous))) _)) _
  source' := by
    apply Subtype.ext
    ext s
    simp [pathSpaceConcat, concatTail_apply]
  target' := by
    apply Subtype.ext
    ext s
    simp only [concatTail_apply, BasedTopPair.coe_pathSpaceBase, ContinuousMap.const_apply]
    split_ifs <;> simp

private theorem coe_pathSpaceTail_apply (γ : Path X.basepoint b) (t s : I) :
    (pathSpaceTail γ t : C(I, X.pair.fst)) s =
      if (s : ℝ) ≤ 1 / 2 then X.pair.map (γ t)
      else X.pair.map (γ (Icc.convexComb t 1 (projIcc 0 1 zero_le_one (2 * s - 1)))) :=
  (rfl)

/-- The relative cube `q` with its distinguished coordinate run at double speed, the second half
of it constant at the basepoint. -/
private def squash (q : RelGenLoop N ⟨X.pair, b⟩) : RelGenLoop N ⟨X.pair, b⟩ :=
  mk ((q : C(I × (I^N), X.pair.fst)).comp
      ⟨fun y => (projIcc 0 1 zero_le_one (2 * y.1), y.2),
        (continuous_projIcc.comp (continuous_const.mul
          (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd⟩)
    (fun z => by simpa using apply_zero_mem_range q z)
    fun s z h => by
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, coe_coe]
      rcases h with rfl | hz
      · rw [Set.Icc.coe_one, mul_one, projIcc_of_right_le _ one_le_two]
        exact apply_one q z
      · exact apply_of_mem_boundary q _ hz

private theorem squash_apply (q : RelGenLoop N ⟨X.pair, b⟩) (s : I) (z : I^N) :
    squash q (s, z) = q (projIcc 0 1 zero_le_one (2 * s), z) := by
  rw [squash, mk_apply]
  rfl

/-- Running the distinguished coordinate faster does not change the homotopy class. -/
private theorem homotopic_squash (q : RelGenLoop N ⟨X.pair, b⟩) : Homotopic q (squash q) :=
  homotopic_iff.2
    ⟨{ toFun ty := q (projIcc 0 1 zero_le_one ((1 + ty.1) * ty.2.1), ty.2.2)
       continuous_toFun := (map_continuous (q : C(I × (I^N), X.pair.fst))).comp
         ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_snd.comp continuous_snd))
       map_zero_left y := by simp
       map_one_left y := by
         obtain ⟨s, z⟩ := y
         simp only [coe_coe]
         norm_num
         exact (squash_apply q s z).symm
       prop' r := by
         refine mem_iff.2 ⟨fun z => by simpa using apply_zero_mem_range q z, fun s z h => ?_⟩
         rcases h with rfl | hz
         · simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
           rw [projIcc_of_right_le _ (by linarith [r.2.1])]
           exact apply_one q z
         · exact apply_of_mem_boundary q _ hz }⟩

private theorem coe_pathSpaceConcat_apply (γ : Path X.basepoint b)
    (q : BasedTopPair.pathSpace X) (s : I) :
    (pathSpaceConcat γ q : C(I, X.pair.fst)) s =
      if (s : ℝ) ≤ 1 / 2 then (q : C(I, X.pair.fst)) (projIcc 0 1 zero_le_one (2 * s))
      else X.pair.map (γ (Icc.convexComb 0 1 (projIcc 0 1 zero_le_one (2 * s - 1)))) :=
  (rfl)

/-- The stages of a homotopy along `γ` of relative cubes, read as generalized loops in the space
of paths from `A`, each path followed by the tail `γ.subpath t 1` of `γ`. -/
private def HomotopyAlong.pathSpaceFamily {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) :
    C(I × (I^N), BasedTopPair.pathSpace ⟨X.pair, b⟩) where
  toFun tz := ⟨concatTail γ ⟨(tz.1, ContinuousMap.curry
      ⟨fun x : (I × (I^N)) × I => h.toHomotopy (x.1.1, (x.2, x.1.2)), by fun_prop⟩ tz),
        h.apply_eq_path tz.1 1 tz.2 (Or.inl rfl)⟩,
    concatTail_mem γ _ (h.apply_zero_mem_range tz.1 tz.2)⟩
  continuous_toFun := by fun_prop

private theorem HomotopyAlong.coe_pathSpaceFamily_apply {γ : Path X.basepoint b}
    {p : RelGenLoop N X} {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) (t : I)
    (z : I^N) (s : I) :
    (h.pathSpaceFamily (t, z) : C(I, X.pair.fst)) s =
      if (s : ℝ) ≤ 1 / 2 then h.toHomotopy (t, (projIcc 0 1 zero_le_one (2 * s), z))
      else X.pair.map (γ (Icc.convexComb t 1 (projIcc 0 1 zero_le_one (2 * s - 1)))) :=
  (rfl)

section Canonicity

variable [Fintype N]

/-- A homotopy along `γ` of relative cubes, with the paths of each stage followed by the tail of
`γ`, is an absolute homotopy along `pathSpaceTail γ` of generalized loops in the space of paths
from `A` to `b`. -/
private def HomotopyAlong.pathSpace {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) :
    GenLoop.HomotopyAlong (pathSpaceTail γ)
      (_root_.GenLoop.map (pathSpaceConcat γ) rfl (pathSpaceHomeo p))
      (pathSpaceHomeo (squash q)) where
  toContinuousMap := h.pathSpaceFamily
  map_zero_left z := by
    apply Subtype.ext
    ext s
    rw [ContinuousMap.toFun_eq_coe, h.coe_pathSpaceFamily_apply, GenLoop.coe_coe,
      _root_.GenLoop.map_apply, coe_pathSpaceConcat_apply, pathSpaceHomeo_apply_apply,
      h.toHomotopy.apply_zero]
    rfl
  map_one_left z := by
    apply Subtype.ext
    ext s
    rw [ContinuousMap.toFun_eq_coe, h.coe_pathSpaceFamily_apply, GenLoop.coe_coe,
      pathSpaceHomeo_apply_apply, squash_apply, h.toHomotopy.apply_one, coe_coe]
    split_ifs with hs
    · rfl
    · have hq : q (projIcc 0 1 zero_le_one (2 * s), z) = X.pair.map b := by
        rw [projIcc_of_right_le _ (by linarith [lt_of_not_ge hs])]
        exact apply_one q z
      rw [hq, Icc.convexComb_eq, γ.target]
  map_boundary t z hz := by
    apply Subtype.ext
    ext s
    refine (h.coe_pathSpaceFamily_apply t z s).trans ?_
    rw [coe_pathSpaceTail_apply, h.apply_eq_path t _ z (Or.inr hz)]

end Canonicity

end RelGenLoop

namespace RelHomotopyGroup

variable [Fintype N]

/-- **Base-point change for relative homotopy sets.** The map
`π_{n+1}(X, A, a) → π_{n+1}(X, A, b)` induced by a path `γ` in `A` from `a` to `b`. A homotopy
along `γ` from a relative cube `p` to `q` carries the class of `p` to the class of `q`
(`TauCeti.RelGenLoop.HomotopyAlong.transport_mk`). -/
def transport (γ : Path X.basepoint b) (x : RelHomotopyGroup N X) :
    RelHomotopyGroup N ⟨X.pair, b⟩ :=
  pathSpaceEquiv.symm (homotopyGroupTransport (RelGenLoop.pathSpaceTail γ)
    (HomotopyGroup.map (RelGenLoop.pathSpaceConcat γ) rfl (pathSpaceEquiv x)))

end RelHomotopyGroup

namespace RelGenLoop

variable [Fintype N]

/-- **The characterisation of relative base-point change.** If there is a homotopy along `γ` from
`p` to `q`, then transport along `γ` sends the class of `p` to the class of `q`. -/
theorem HomotopyAlong.transport_mk {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) :
    RelHomotopyGroup.transport γ (RelHomotopyGroup.mk p) = RelHomotopyGroup.mk q := by
  rw [RelHomotopyGroup.transport, Equiv.symm_apply_eq, RelHomotopyGroup.pathSpaceEquiv_mk,
    RelHomotopyGroup.pathSpaceEquiv_mk, HomotopyGroup.map_mk, homotopyGroupTransport_mk]
  exact Quotient.sound ((homotopic_pathSpaceHomeo_iff.2 (homotopic_squash q)).trans
    h.pathSpace.homotopic_transport).symm

/-- **Canonicity of the transported relative cube.** A homotopy along `γ` starting at `p` ends at
a relative cube homotopic to `transport γ p`. -/
theorem HomotopyAlong.homotopic_transport {γ : Path X.basepoint b} {p : RelGenLoop N X}
    {q : RelGenLoop N ⟨X.pair, b⟩} (h : HomotopyAlong γ p q) : Homotopic q (transport γ p) :=
  RelHomotopyGroup.mk_eq_mk.1 (h.transport_mk.symm.trans (collarHomotopyAlong γ p).transport_mk)

end RelGenLoop

namespace RelHomotopyGroup

variable [Fintype N]

/-- Transport of the class of a relative cube is the class of its transport. -/
@[simp]
theorem transport_mk (γ : Path X.basepoint b) (p : RelGenLoop N X) :
    transport γ (mk p) = mk (RelGenLoop.transport γ p) :=
  (RelGenLoop.collarHomotopyAlong γ p).transport_mk

/-- Transport along a constant path is the identity. -/
@[simp]
theorem transport_refl : transport (N := N) (Path.refl X.basepoint) = id := by
  funext x
  obtain ⟨p, rfl⟩ := mk_surjective x
  exact (RelGenLoop.HomotopyAlong.refl p).transport_mk

/-- Transport along a concatenation of paths is the composite of the transports. -/
@[simp]
theorem transport_trans (γ : Path X.basepoint b) (δ : Path b c) :
    transport (N := N) (γ.trans δ) = transport (X := ⟨X.pair, b⟩) δ ∘ transport γ := by
  funext x
  obtain ⟨p, rfl⟩ := mk_surjective x
  rw [Function.comp_apply, transport_mk γ, transport_mk (X := ⟨X.pair, b⟩) δ]
  exact ((RelGenLoop.collarHomotopyAlong γ p).trans
    (RelGenLoop.collarHomotopyAlong (X := ⟨X.pair, b⟩) δ _)).transport_mk

/-- Homotopic paths induce the same transport. -/
theorem transport_congr {γ γ' : Path X.basepoint b} (h : γ.Homotopic γ') :
    transport (N := N) γ = transport γ' := by
  funext x
  obtain ⟨p, rfl⟩ := mk_surjective x
  rw [transport_mk, transport_mk]
  exact mk_eq_mk.2 (RelGenLoop.homotopic_transport_of_path_homotopic h p)

/-- Transport along the reversed path undoes transport. -/
@[simp]
theorem transport_symm_transport (γ : Path X.basepoint b) (x : RelHomotopyGroup N X) :
    transport (X := ⟨X.pair, b⟩) γ.symm (transport γ x) = x := by
  obtain ⟨p, rfl⟩ := mk_surjective x
  rw [transport_mk]
  exact (RelGenLoop.collarHomotopyAlong γ p).symm.transport_mk

/-- Transport along a path undoes transport along the reversed path. -/
@[simp]
theorem transport_transport_symm (γ : Path X.basepoint b)
    (x : RelHomotopyGroup N ⟨X.pair, b⟩) :
    transport γ (transport (X := ⟨X.pair, b⟩) γ.symm x) = x := by
  have h := transport_symm_transport (X := ⟨X.pair, b⟩) γ.symm x
  rwa [Path.symm_symm] at h

/-- Transport preserves the distinguished point. -/
@[simp]
theorem transport_default (γ : Path X.basepoint b) :
    transport γ (default : RelHomotopyGroup N X) = default := by
  rw [default_eq, default_eq]
  exact (RelGenLoop.HomotopyAlong.const γ).transport_mk

/-- **Base-point change for relative homotopy sets.** A path from `a` to `b` in the subspace
induces a bijection `π_{n+1}(X, A, a) ≃ π_{n+1}(X, A, b)`. -/
def equivOfPath (γ : Path X.basepoint b) :
    RelHomotopyGroup N X ≃ RelHomotopyGroup N ⟨X.pair, b⟩ where
  toFun := transport γ
  invFun := transport (X := ⟨X.pair, b⟩) γ.symm
  left_inv := transport_symm_transport γ
  right_inv := transport_transport_symm γ

@[simp]
theorem equivOfPath_apply (γ : Path X.basepoint b) (x : RelHomotopyGroup N X) :
    equivOfPath γ x = transport γ x :=
  (rfl)

@[simp]
theorem equivOfPath_symm_apply (γ : Path X.basepoint b) (x : RelHomotopyGroup N ⟨X.pair, b⟩) :
    (equivOfPath γ).symm x = transport (X := ⟨X.pair, b⟩) γ.symm x :=
  (rfl)

/-- The equivalence for a constant path is the identity. -/
@[simp]
theorem equivOfPath_refl :
    equivOfPath (N := N) (Path.refl X.basepoint) = Equiv.refl (RelHomotopyGroup N X) := by
  ext x
  rw [equivOfPath_apply, transport_refl]
  rfl

/-- The equivalence for a concatenated path is the composite equivalence. -/
@[simp]
theorem equivOfPath_trans (γ : Path X.basepoint b) (δ : Path b c) :
    equivOfPath (N := N) (γ.trans δ) =
      (equivOfPath γ).trans (equivOfPath (X := ⟨X.pair, b⟩) δ) := by
  ext x
  rw [equivOfPath_apply, Equiv.trans_apply, equivOfPath_apply, equivOfPath_apply,
    transport_trans, Function.comp_apply]

/-- Reversing the path gives the inverse equivalence. -/
theorem equivOfPath_symm (γ : Path X.basepoint b) :
    (equivOfPath γ).symm = equivOfPath (N := N) (X := ⟨X.pair, b⟩) γ.symm := by
  ext x
  rw [equivOfPath_symm_apply, equivOfPath_apply]

/-- Homotopic paths induce the same equivalence. -/
theorem equivOfPath_congr {γ γ' : Path X.basepoint b} (h : γ.Homotopic γ') :
    equivOfPath (N := N) γ = equivOfPath γ' := by
  ext x
  rw [equivOfPath_apply, equivOfPath_apply, transport_congr h]

/-- Transport commutes with the boundary map: restricted to the face in `A`, it is base-point
change of homotopy groups of `A`. -/
@[simp]
theorem boundary_transport (γ : Path X.basepoint b) (x : RelHomotopyGroup N X) :
    boundary (transport γ x) = homotopyGroupTransport γ (boundary x) := by
  obtain ⟨p, rfl⟩ := mk_surjective x
  rw [transport_mk, boundary_mk, boundary_mk, homotopyGroupTransport_mk]
  exact Quotient.sound (RelGenLoop.collarHomotopyAlong γ p).boundary.homotopic_transport

/-- Transport commutes with the map `π_{n+1}(X, a) → π_{n+1}(X, A, a)`: on absolute classes it is
base-point change of homotopy groups of `X` along the image of `γ`. -/
@[simp]
theorem transport_ofHomotopyGroup (γ : Path X.basepoint b)
    (x : HomotopyGroup (Option N) X.pair.fst (X.pair.map X.basepoint)) :
    transport γ (ofHomotopyGroup (X := X) x) =
      ofHomotopyGroup (X := ⟨X.pair, b⟩)
        (homotopyGroupTransport (γ.map X.pair.map.hom.continuous) x) := by
  induction x using Quotient.inductionOn with | h f => ?_
  rw [ofHomotopyGroup_mk, homotopyGroupTransport_mk, ofHomotopyGroup_mk]
  exact (RelGenLoop.HomotopyAlong.ofGenLoop (GenLoop.collarHomotopyAlong _ f)).transport_mk

/-- Transport is natural in morphisms of based pairs `f : X ⟶ Y`, along the image of the path,
which starts at the basepoint of `Y`. -/
@[simp]
theorem map_transport {Y : BasedTopPair.{u}} (f : X ⟶ Y) (γ : Path X.basepoint b)
    (x : RelHomotopyGroup N X) :
    map (⟨f.toTopPairHom, rfl⟩ :
        (⟨X.pair, b⟩ : BasedTopPair) ⟶ ⟨Y.pair, TopPair.Hom.snd f.toTopPairHom b⟩)
        (transport γ x) =
      transport
        ((γ.map (TopPair.Hom.snd f.toTopPairHom).hom.continuous).cast f.map_basepoint.symm rfl)
        (map f x) := by
  obtain ⟨p, rfl⟩ := mk_surjective x
  rw [transport_mk, map_mk, map_mk]
  exact ((RelGenLoop.collarHomotopyAlong γ p).map f).transport_mk.symm

variable [Nonempty N] [DecidableEq N]

/-- In degrees at least two, transport is a homomorphism. -/
@[simp]
theorem transport_mul (γ : Path X.basepoint b) (x y : RelHomotopyGroup N X) :
    transport γ (x * y) = transport γ x * transport γ y := by
  -- `transport` is the composite of three homomorphisms
  have h : transport γ = (pathSpaceMulEquiv (X := ⟨X.pair, b⟩)).symm.toMonoidHom.comp
      (((homotopyGroupMulEquivOfPath (RelGenLoop.pathSpaceTail γ)).toMonoidHom.comp
        (HomotopyGroup.mapHom (RelGenLoop.pathSpaceConcat γ) rfl)).comp
          (pathSpaceMulEquiv (N := N) (X := X)).toMonoidHom) := by
    funext z
    simp [transport]
  rw [h, _root_.map_mul]

/-- **Base-point change for relative homotopy groups.** A path from `a` to `b` in the subspace
induces a group isomorphism `π_{n+1}(X, A, a) ≃* π_{n+1}(X, A, b)` for `n ≥ 1`. -/
def mulEquivOfPath (γ : Path X.basepoint b) :
    RelHomotopyGroup N X ≃* RelHomotopyGroup N ⟨X.pair, b⟩ where
  toEquiv := equivOfPath γ
  map_mul' := transport_mul γ

@[simp]
theorem mulEquivOfPath_apply (γ : Path X.basepoint b) (x : RelHomotopyGroup N X) :
    mulEquivOfPath γ x = transport γ x :=
  (rfl)

@[simp]
theorem mulEquivOfPath_symm_apply (γ : Path X.basepoint b)
    (x : RelHomotopyGroup N ⟨X.pair, b⟩) :
    (mulEquivOfPath γ).symm x = transport (X := ⟨X.pair, b⟩) γ.symm x :=
  (rfl)

/-- The group isomorphism for a constant path is the identity. -/
@[simp]
theorem mulEquivOfPath_refl :
    mulEquivOfPath (N := N) (Path.refl X.basepoint) = MulEquiv.refl (RelHomotopyGroup N X) := by
  ext x
  rw [mulEquivOfPath_apply, transport_refl]
  rfl

/-- The group isomorphism for a concatenated path is the composite isomorphism. -/
@[simp]
theorem mulEquivOfPath_trans (γ : Path X.basepoint b) (δ : Path b c) :
    mulEquivOfPath (N := N) (γ.trans δ) =
      (mulEquivOfPath γ).trans (mulEquivOfPath (X := ⟨X.pair, b⟩) δ) := by
  ext x
  rw [mulEquivOfPath_apply, MulEquiv.trans_apply, mulEquivOfPath_apply, mulEquivOfPath_apply,
    transport_trans, Function.comp_apply]

/-- Reversing the path gives the inverse group isomorphism. -/
theorem mulEquivOfPath_symm (γ : Path X.basepoint b) :
    (mulEquivOfPath γ).symm = mulEquivOfPath (N := N) (X := ⟨X.pair, b⟩) γ.symm := by
  ext x
  rw [mulEquivOfPath_symm_apply, mulEquivOfPath_apply]

/-- Homotopic paths induce the same group isomorphism. -/
theorem mulEquivOfPath_congr {γ γ' : Path X.basepoint b} (h : γ.Homotopic γ') :
    mulEquivOfPath (N := N) γ = mulEquivOfPath γ' := by
  ext x
  rw [mulEquivOfPath_apply, mulEquivOfPath_apply, transport_congr h]

end RelHomotopyGroup

end TauCeti
