/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.Homotopy.Relative.BasepointChange
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Disk

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Relative cubes homotopic through maps of pairs

A relative cube of a based pair `(X, A, a₀)` is in particular a map of pairs
`(I × Iⁿ, ∂(I × Iⁿ)) → (X, A)` (`TauCeti.RelGenLoop.mapsTo_prodBoundary`), and a homotopy
through relative cubes is a homotopy through maps of pairs
(`TauCeti.RelGenLoop.Homotopic.homotopicWith`). The converse fails in general: along a
homotopy of maps of pairs the open box `{1} × Iⁿ ∪ I × ∂Iⁿ`, which a relative cube sends to `a₀`,
may move inside `A`. This file shows that the only difference is the action of `π₁(A, a₀)` by
base-point change, as for free and based homotopy classes of maps of spheres (Hatcher, Sections 4.1
and 4.A).

* If two relative cubes `p` and `q` at `a₀` are homotopic through maps of pairs, then there is a
  loop `γ` in `A` at `a₀` and a homotopy along `γ` from `p` to `q`
  (`TauCeti.RelGenLoop.exists_homotopyAlong_of_homotopicWith`), so the class of `q` is the
  transport of the class of `p` along `γ`
  (`TauCeti.RelHomotopyGroup.exists_transport_mk_eq_mk_of_homotopicWith`).
* Hence, when `π₁(A, a₀)` is trivial, two relative cubes have the same class in
  `π_{n+1}(X, A, a₀)` exactly when they are homotopic through maps of pairs
  (`TauCeti.RelHomotopyGroup.mk_eq_mk_iff_homotopicWith`). Combined with the deformation of a map
  of pairs into a relative cube (`TauCeti.exists_homotopicWith_relGenLoop`), every map of pairs
  `(I × Iⁿ, ∂(I × Iⁿ)) → (Y, B)` into a simply connected subspace `B` then has a well-defined class
  in `π_{n+1}(Y, B, b)` (`TauCeti.RelHomotopyGroup.existsUnique_homotopicWith`): the free homotopy
  classes of maps of pairs are the relative homotopy group.

So a singular cube with boundary in a simply connected subspace, as it occurs in relative singular
chains, determines an element of the relative homotopy group.

## Proof

Let `H` be a homotopy through maps of pairs from `p` to `q`, a map on the cube `I × (I × Iⁿ)` whose
first coordinate is time. Contract the open box `J = {1} × Iⁿ ∪ I × ∂Iⁿ` to the centre of its top
face (`TauCeti.openBoxContraction`), and precompose `H` at every time with this contraction on `J`.
As `p` and `q` are constant on `J`, this deformation is stationary on the faces at times `0` and
`1`. On the face `{0} × Iⁿ` at all times, whose boundary lies in `J`, the deformation extends to a
deformation with values in `A` by the homotopy extension property of the boundary of `I × Iⁿ`. The
resulting deformation of `H` on the boundary of the cube `I × (I × Iⁿ)` extends over the cube, by
the homotopy extension property again. At its end, every time slice sends `J` to the point
`γ t = H (t, (1, c))`, so it is a homotopy along the loop `γ`.

## Main results

* `TauCeti.RelGenLoop.exists_homotopyAlong_of_homotopicWith`: relative cubes homotopic through
  maps of pairs are homotopic along a loop in the subspace.
* `TauCeti.RelHomotopyGroup.exists_transport_mk_eq_mk_of_homotopicWith`: their classes lie in one
  orbit of the action of `π₁(A, a₀)`.
* `TauCeti.RelHomotopyGroup.mk_eq_mk_iff_homotopicWith`: if `π₁(A, a₀)` is trivial, relative
  cubes have the same class exactly when they are homotopic through maps of pairs.
* `TauCeti.RelHomotopyGroup.existsUnique_homotopicWith`: for simply connected `B`, a map of pairs
  out of the cube is homotopic through maps of pairs to relative cubes of a single class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the action of `π₁(A, x₀)` on `πₙ(X, A, x₀)` by change of base point, and
  Section 4.A, based and free homotopy classes.
-/

public section

noncomputable section

universe u v

open Set Topology
open scoped unitInterval

namespace TauCeti

variable {N : Type v} {X : BasedTopPair.{u}}

/-! ### Deforming a homotopy of maps of pairs into a homotopy along a loop -/

section Deformation

/-- A relative cube sends the open box `{1} × I^N ∪ I × ∂I^N` to the basepoint. -/
private theorem apply_eq_of_openBox (p : RelGenLoop N X) {w : I × I^N}
    (hw : w.1 = 1 ∨ w.2 ∈ Cube.boundary N) : p w = X.pair.map X.basepoint :=
  (RelGenLoop.mem_iff.1 p.2).2 w.1 w.2 hw

variable {p q : RelGenLoop N X}

/-- At times `0` and `1`, a homotopy through maps of pairs from `p` to `q` does not see the
contraction of the open box `{1} × I^N ∪ I × ∂I^N`, since `p` and `q` are constant there. -/
private theorem apply_openBoxContraction
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map))
    {i : I} (hi : i = 0 ∨ i = 1) (u : I) {w : I × I^N} (hw : w.1 = 1 ∨ w.2 ∈ Cube.boundary N) :
    H (i, openBoxContraction u w) = H (i, w) := by
  have hJ := openBoxContraction_mem_openBox hw u
  rcases hi with rfl | rfl
  · rw [H.apply_zero, H.apply_zero, RelGenLoop.coe_coe, apply_eq_of_openBox p hw,
      apply_eq_of_openBox p hJ]
  · rw [H.apply_one, H.apply_one, RelGenLoop.coe_coe, apply_eq_of_openBox q hw,
      apply_eq_of_openBox q hJ]

variable [Finite N]

/-- The deformation on the boundary of the face `I × ({0} × I^N)` of `exists_bottomHomotopy` is
continuous: it is continuous on each of the three closed pieces of the boundary of the face. -/
private theorem continuousOn_bottomBoundary
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map))
    (k : I × (I × I^N) → X.pair.fst) (hk₀ : ∀ (u : I) (z : I^N), k (u, (0, z)) = p (0, z))
    (hk₁ : ∀ (u : I) (z : I^N), k (u, (1, z)) = q (0, z))
    (hk : ∀ {u t : I} {z : I^N}, z ∈ Cube.boundary N →
      k (u, (t, z)) = H (t, openBoxContraction u (0, z))) :
    ContinuousOn k {x | x.2 ∈ Cube.prodBoundary N} := by
  have hS : {x : I × (I × I^N) | x.2 ∈ Cube.prodBoundary N} =
      {x | x.2.1 = 0} ∪ ({x | x.2.1 = 1} ∪ {x | x.2.2 ∈ Cube.boundary N}) := by
    ext x
    simp [or_assoc]
  rw [hS]
  have hc₀ : IsClosed {x : I × (I × I^N) | x.2.1 = 0} := isClosed_eq (by fun_prop) (by fun_prop)
  have hc₁ : IsClosed {x : I × (I × I^N) | x.2.1 = 1} := isClosed_eq (by fun_prop) (by fun_prop)
  have hc₂ : IsClosed {x : I × (I × I^N) | x.2.2 ∈ Cube.boundary N} :=
    hasHomotopyExtensionProperty_cubeBoundary.isClosed.preimage (by fun_prop)
  refine ContinuousOn.union_of_isClosed ?_ (ContinuousOn.union_of_isClosed ?_ ?_ hc₁ hc₂) hc₀
    ((hc₁.union hc₂))
  · refine (by fun_prop : Continuous fun x : I × (I × I^N) ↦
      (p : C(I × (I^N), X.pair.fst)) (0, x.2.2)).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, z⟩ := x
    obtain rfl : t = 0 := hx
    exact hk₀ u z
  · refine (by fun_prop : Continuous fun x : I × (I × I^N) ↦
      (q : C(I × (I^N), X.pair.fst)) (0, x.2.2)).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, z⟩ := x
    obtain rfl : t = 1 := hx
    exact hk₁ u z
  · refine (H.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_openBoxContraction.comp (by fun_prop : Continuous fun x : I × (I × I^N) ↦
        (x.1, ((0 : I), x.2.2)))))).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, z⟩ := x
    exact hk hx

/-- The deformation of a homotopy `H` through maps of pairs, from `p` to `q`, on the face
`I × ({0} × I^N)` of the cube `I × (I × I^N)`, the first coordinate being time: it starts at `H`,
has values in the subspace, is stationary at times `0` and `1`, and on the boundary of the face
precomposes `H` with the contraction of the open box. -/
private theorem exists_bottomHomotopy
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map)) :
    ∃ L : C(I × (I × I^N), X.pair.fst), (∀ t z, L (0, (t, z)) = H (t, (0, z))) ∧
      (∀ u t z, L (u, (t, z)) ∈ range X.pair.map) ∧ (∀ u z, L (u, (0, z)) = p (0, z)) ∧
      (∀ u z, L (u, (1, z)) = q (0, z)) ∧
      ∀ u t z, z ∈ Cube.boundary N → L (u, (t, z)) = H (t, openBoxContraction u (0, z)) := by
  have hH (t : I) {y : I × I^N} (hy : y ∈ Cube.prodBoundary N) : H (t, y) ∈ range X.pair.map :=
    H.prop t hy
  -- The deformation on the boundary of the face, read in the coordinates `(t, z)` of the face.
  let k : I × (I × I^N) → X.pair.fst := fun x ↦
    if x.2.1 = 0 then p (0, x.2.2) else if x.2.1 = 1 then q (0, x.2.2)
    else H (x.2.1, openBoxContraction x.1 (0, x.2.2))
  have hk₀ (u : I) (z : I^N) : k (u, (0, z)) = p (0, z) := by simp [k]
  have hk₁ (u : I) (z : I^N) : k (u, (1, z)) = q (0, z) := by simp [k]
  have hk {u t : I} {z : I^N} (hz : z ∈ Cube.boundary N) :
      k (u, (t, z)) = H (t, openBoxContraction u (0, z)) := by
    simp only [k]
    split_ifs with h₀ h₁
    · subst h₀
      rw [apply_openBoxContraction H (.inl rfl) u (.inr hz), H.apply_zero, RelGenLoop.coe_coe]
    · subst h₁
      rw [apply_openBoxContraction H (.inr rfl) u (.inr hz), H.apply_one, RelGenLoop.coe_coe]
    · rfl
  have hcont := continuousOn_bottomBoundary H k hk₀ hk₁ hk
  have hkB (x : I × (I × I^N)) (hx : x.2 ∈ Cube.prodBoundary N) : k x ∈ range X.pair.map := by
    obtain ⟨u, t, z⟩ := x
    rcases Cube.mem_prodBoundary_iff.1 hx with (rfl | rfl) | hz
    · exact hk₀ u z ▸ RelGenLoop.mapsTo_prodBoundary p.2 (Cube.mk_zero_mem_prodBoundary z)
    · exact hk₁ u z ▸ RelGenLoop.mapsTo_prodBoundary q.2 (Cube.mk_zero_mem_prodBoundary z)
    · exact hk hz ▸ hH t (openBoxContraction_mem_prodBoundary (z := ((0 : I), z)) (.inr hz) u)
  -- Extend the deformation over the face, keeping its values in the subspace.
  have hbd := hasHomotopyExtensionProperty_prodBoundary (N := N)
  obtain ⟨L, hL₀, hL⟩ := hbd.exists_extension_of_isClosed hbd.isClosed
    (⟨fun y ↦ ⟨H (y.1, (0, y.2)), hH y.1 (Cube.mk_zero_mem_prodBoundary y.2)⟩, by fun_prop⟩ :
      C(I × I^N, range X.pair.map))
    ⟨fun x ↦ ⟨k (x.1, x.2), hkB (x.1, x.2) x.2.2⟩,
      (hcont.comp_continuous (by fun_prop) fun x ↦ x.2.2).subtype_mk _⟩
    fun y ↦ by
      obtain ⟨⟨t, z⟩, hy⟩ := y
      ext1
      simp only [ContinuousMap.coe_mk]
      rcases Cube.mem_prodBoundary_iff.1 hy with (rfl | rfl) | hz
      · rw [hk₀, H.apply_zero, RelGenLoop.coe_coe]
      · rw [hk₁, H.apply_one, RelGenLoop.coe_coe]
      · rw [hk hz, openBoxContraction_zero]
  have hL' (u t : I) (z : I^N) (h : ((t, z) : I × I^N) ∈ Cube.prodBoundary N) :
      (L (u, (t, z)) : X.pair.fst) = k (u, (t, z)) :=
    congrArg Subtype.val (hL u ⟨(t, z), h⟩)
  refine ⟨⟨fun x ↦ (L x : X.pair.fst), by fun_prop⟩, fun t z ↦ congrArg Subtype.val (hL₀ (t, z)),
    fun u t z ↦ (L (u, (t, z))).2, fun u z ↦ ?_, fun u z ↦ ?_, fun u t z hz ↦ ?_⟩
  · exact (hL' u 0 z (Cube.mk_zero_mem_prodBoundary z)).trans (hk₀ u z)
  · exact (hL' u 1 z (Cube.mk_mem_prodBoundary (.inl rfl))).trans (hk₁ u z)
  · exact (hL' u t z (Cube.mem_prodBoundary_iff.2 (Or.inr hz))).trans (hk hz)

/-- The deformation `K` of `exists_homotopy_eq_on_openBox` is continuous on `I × T`, where `T` is
the boundary of the cube `I × (I × I^N)`, the union of four closed faces. -/
private theorem continuousOn_openBoxDeformation
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map))
    (K : I × (I × (I × I^N)) → X.pair.fst) {L : C(I × (I × I^N), X.pair.fst)}
    (hK₀ : ∀ (u t : I) (z : I^N), K (u, (t, (0, z))) = L (u, (t, z)))
    (hKp : ∀ (u : I) (w : I × I^N), K (u, (0, w)) = p w)
    (hKq : ∀ (u : I) (w : I × I^N), K (u, (1, w)) = q w)
    (hKJ : ∀ (u t : I) {w : I × I^N}, (w.1 = 1 ∨ w.2 ∈ Cube.boundary N) →
      K (u, (t, w)) = H (t, openBoxContraction u w)) :
    ContinuousOn K {x | (x.2.1 = 0 ∨ x.2.1 = 1) ∨ x.2.2 ∈ Cube.prodBoundary N} := by
  have hS : {x : I × (I × (I × I^N)) | (x.2.1 = 0 ∨ x.2.1 = 1) ∨ x.2.2 ∈ Cube.prodBoundary N} =
      {x | x.2.2.1 = 0} ∪ ({x | x.2.1 = 0} ∪
      ({x | x.2.1 = 1} ∪ {x | x.2.2.1 = 1 ∨ x.2.2.2 ∈ Cube.boundary N})) := by
    ext x
    simp only [Cube.mem_prodBoundary_iff, mem_ofPred_eq, mem_union]
    tauto
  rw [hS]
  have hc₀ : IsClosed {x : I × (I × (I × I^N)) | x.2.2.1 = 0} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hc₁ : IsClosed {x : I × (I × (I × I^N)) | x.2.1 = 0} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hc₂ : IsClosed {x : I × (I × (I × I^N)) | x.2.1 = 1} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hc₃ : IsClosed {x : I × (I × (I × I^N)) | x.2.2.1 = 1 ∨ x.2.2.2 ∈ Cube.boundary N} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).union
      (hasHomotopyExtensionProperty_cubeBoundary.isClosed.preimage (by fun_prop))
  refine ContinuousOn.union_of_isClosed ?_ (ContinuousOn.union_of_isClosed ?_
    (ContinuousOn.union_of_isClosed ?_ ?_ hc₂ hc₃) hc₁ (hc₂.union hc₃)) hc₀
    (hc₁.union (hc₂.union hc₃))
  · refine (by fun_prop : Continuous fun x : I × (I × (I × I^N)) ↦
      L (x.1, (x.2.1, x.2.2.2))).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, s, z⟩ := x
    obtain rfl : s = 0 := hx
    exact hK₀ u t z
  · refine (by fun_prop : Continuous fun x : I × (I × (I × I^N)) ↦
      (p : C(I × (I^N), X.pair.fst)) x.2.2).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, w⟩ := x
    obtain rfl : t = 0 := hx
    exact hKp u w
  · refine (by fun_prop : Continuous fun x : I × (I × (I × I^N)) ↦
      (q : C(I × (I^N), X.pair.fst)) x.2.2).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, w⟩ := x
    obtain rfl : t = 1 := hx
    exact hKq u w
  · refine (H.continuous.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_openBoxContraction.comp (continuous_fst.prodMk
        (continuous_snd.comp continuous_snd))))).continuousOn.congr fun x hx ↦ ?_
    obtain ⟨u, t, w⟩ := x
    exact hKJ u t hx

/-- Let `K` be a deformation of a homotopy `H` of relative cubes on `I × ∂(I × (I × I^N))`: it
agrees with `L` on `s = 0`, with `p` and `q` at the two ends, and with `H ∘ openBoxContraction` on
the open box. Then there is a homotopy `p ≃ q` which sends `{0} × I^N` into the subspace and the
open box to `H (t, (1, cubeCenter))`. -/
private theorem exists_homotopy_of_deformation
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map))
    (L : C(I × (I × I^N), X.pair.fst)) (hL₀ : ∀ t z, L (0, (t, z)) = H (t, (0, z)))
    (hLB : ∀ u t z, L (u, (t, z)) ∈ range X.pair.map)
    (K : I × (I × (I × I^N)) → X.pair.fst)
    (hK₀ : ∀ (u t : I) (z : I^N), K (u, (t, (0, z))) = L (u, (t, z)))
    (hKp : ∀ (u : I) (w : I × I^N), K (u, (0, w)) = p w)
    (hKq : ∀ (u : I) (w : I × I^N), K (u, (1, w)) = q w)
    (hKJ : ∀ (u t : I) {w : I × I^N}, (w.1 = 1 ∨ w.2 ∈ Cube.boundary N) →
      K (u, (t, w)) = H (t, openBoxContraction u w)) :
    ∃ F : (p : C(I × (I^N), X.pair.fst)).Homotopy q,
      (∀ t z, F (t, (0, z)) ∈ range X.pair.map) ∧
      ∀ t w, (w.1 = 1 ∨ w.2 ∈ Cube.boundary N) → F (t, w) = H (t, (1, cubeCenter)) := by
  have hcont := continuousOn_openBoxDeformation H K hK₀ hKp hKq hKJ
  let T : Set (I × (I × I^N)) := {x | (x.1 = 0 ∨ x.1 = 1) ∨ x.2 ∈ Cube.prodBoundary N}
  -- Extend the deformation over the cube, and take its end.
  have hT := hasHomotopyExtensionProperty_boundary_prod (N := N)
  obtain ⟨G, -, hG⟩ := hT.exists_extension_of_isClosed hT.isClosed H.toContinuousMap
    ⟨fun x ↦ K (x.1, x.2), hcont.comp_continuous (by fun_prop) fun x ↦ x.2.2⟩
    fun x ↦ by
      obtain ⟨⟨t, s, z⟩, hx⟩ := x
      simp only [ContinuousMap.coe_mk, ContinuousMap.Homotopy.coe_toContinuousMap]
      rcases hx with (rfl | rfl) | hw
      · exact (hKp 0 (s, z)).trans (H.apply_zero (s, z)).symm
      · exact (hKq 0 (s, z)).trans (H.apply_one (s, z)).symm
      · rcases Cube.mem_prodBoundary_iff.1 hw with (rfl | hs) | hz
        · exact (hK₀ 0 t z).trans (hL₀ t z)
        · exact (hKJ 0 t (.inl hs)).trans (congrArg (H ⟨t, ·⟩) (openBoxContraction_zero _))
        · exact (hKJ 0 t (.inr hz)).trans (congrArg (H ⟨t, ·⟩) (openBoxContraction_zero _))
  have hG' (t : I) (w : I × I^N) (hw : (t, w) ∈ T) : G (1, (t, w)) = K (1, (t, w)) :=
    hG 1 ⟨(t, w), hw⟩
  refine ⟨{
    toFun := fun x ↦ G (1, x)
    map_zero_left := fun w ↦ (hG' 0 w (Or.inl (Or.inl rfl))).trans (hKp 1 w)
    map_one_left := fun w ↦ (hG' 1 w (Or.inl (Or.inr rfl))).trans (hKq 1 w) },
    fun t z ↦ ?_, fun t w hw ↦ ?_⟩
  · have h := hLB 1 t z
    rw [← hK₀, ← hG' t (0, z) (Or.inr (Cube.mk_zero_mem_prodBoundary z))] at h
    exact h
  · exact (hG' t w (Or.inr (Cube.mk_mem_prodBoundary hw))).trans ((hKJ 1 t hw).trans
      (congrArg (H ⟨t, ·⟩) (openBoxContraction_one _)))

/-- A homotopy `H` through maps of pairs from `p` to `q` can be deformed, keeping its ends, into a
homotopy whose stages send the face `{0} × I^N` into the subspace and the open box
`{1} × I^N ∪ I × ∂I^N` to the point `H (t, (1, c))`, the image under `H` of the centre `c` of the
top face. -/
private theorem exists_homotopy_eq_on_openBox
    (H : (p : C(I × (I^N), X.pair.fst)).HomotopyWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map)) :
    ∃ F : (p : C(I × (I^N), X.pair.fst)).Homotopy q,
      (∀ t z, F (t, (0, z)) ∈ range X.pair.map) ∧
      ∀ t w, (w.1 = 1 ∨ w.2 ∈ Cube.boundary N) → F (t, w) = H (t, (1, cubeCenter)) := by
  obtain ⟨L, hL₀, hLB, hLp, hLq, hL⟩ := exists_bottomHomotopy H
  -- The deformation `K` of `H` on the boundary of the cube `I × (I × I^N)`, the first coordinate
  -- being the deformation parameter: it is given by `L` on the face `I × ({0} × I^N)`, it is
  -- stationary at times `0` and `1`, and it precomposes `H` with the contraction of the open box.
  let K : I × (I × (I × I^N)) → X.pair.fst := fun x ↦
    if x.2.2.1 = 0 then L (x.1, (x.2.1, x.2.2.2)) else if x.2.1 = 0 then p x.2.2
    else if x.2.1 = 1 then q x.2.2 else H (x.2.1, openBoxContraction x.1 x.2.2)
  have hK₀ (u t : I) (z : I^N) : K (u, (t, (0, z))) = L (u, (t, z)) := by simp [K]
  have hKp (u : I) (w : I × I^N) : K (u, (0, w)) = p w := by
    obtain ⟨s, z⟩ := w
    by_cases hs : s = 0
    · subst hs
      exact (hK₀ u 0 z).trans (hLp u z)
    · simp [K, hs]
  have hKq (u : I) (w : I × I^N) : K (u, (1, w)) = q w := by
    obtain ⟨s, z⟩ := w
    by_cases hs : s = 0
    · subst hs
      exact (hK₀ u 1 z).trans (hLq u z)
    · simp [K, hs]
  have hKJ (u t : I) {w : I × I^N} (hw : w.1 = 1 ∨ w.2 ∈ Cube.boundary N) :
      K (u, (t, w)) = H (t, openBoxContraction u w) := by
    obtain ⟨s, z⟩ := w
    by_cases hs : s = 0
    · subst hs
      exact (hK₀ u t z).trans (hL u t z (hw.resolve_left fun h ↦ zero_ne_one' I h))
    by_cases ht₀ : t = 0
    · subst ht₀
      rw [hKp, apply_openBoxContraction H (.inl rfl) u hw, H.apply_zero, RelGenLoop.coe_coe]
    by_cases ht₁ : t = 1
    · subst ht₁
      rw [hKq, apply_openBoxContraction H (.inr rfl) u hw, H.apply_one, RelGenLoop.coe_coe]
    simp [K, hs, ht₀, ht₁]
  exact exists_homotopy_of_deformation H L hL₀ hLB K hK₀ hKp hKq hKJ

namespace RelGenLoop

/-- **Relative cubes homotopic through maps of pairs are homotopic along a loop.** If two relative
cubes `p` and `q` of `(X, A, a₀)` are homotopic through maps of pairs
`(I × I^N, ∂(I × I^N)) → (X, A)`, then there is a loop `γ` in `A` at `a₀` and a homotopy along `γ`
from `p` to `q`. -/
theorem exists_homotopyAlong_of_homotopicWith
    (h : (p : C(I × (I^N), X.pair.fst)).HomotopicWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map)) :
    ∃ γ : Path X.basepoint X.basepoint, Nonempty (HomotopyAlong γ p q) := by
  obtain ⟨H⟩ := h
  obtain ⟨F, hF₀, hFJ⟩ := exists_homotopy_eq_on_openBox H
  -- The loop `γ` in the subspace traced by the image of the centre of the top face.
  have hc (t : I) : H (t, (1, cubeCenter)) ∈ range X.pair.map :=
    H.prop t (Cube.mk_mem_prodBoundary (.inl rfl))
  let g : C(I, X.pair.snd) := X.pair.liftSnd ⟨fun t ↦ H (t, (1, cubeCenter)), by fun_prop⟩ hc
  have hg (t : I) : X.pair.map (g t) = H (t, (1, cubeCenter)) := TopPair.map_liftSnd _ hc t
  let γ : Path X.basepoint X.basepoint :=
    { toContinuousMap := g
      source' := X.pair.isEmbedding_map.injective <| by
        rw [ContinuousMap.toFun_eq_coe, hg, H.apply_zero, coe_coe,
          apply_eq_of_openBox p (.inl rfl)]
      target' := X.pair.isEmbedding_map.injective <| by
        rw [ContinuousMap.toFun_eq_coe, hg, H.apply_one, coe_coe,
          apply_eq_of_openBox q (.inl rfl)] }
  exact ⟨γ, ⟨{
    toHomotopy := F
    apply_zero_mem_range := hF₀
    apply_eq_path := fun t s z hsz ↦ (hFJ t (s, z) hsz).trans (hg t).symm }⟩⟩

end RelGenLoop

end Deformation

/-! ### Relative homotopy classes and homotopies of maps of pairs -/

namespace RelHomotopyGroup

variable {p q : RelGenLoop N X}

/-- **Relative cubes homotopic through maps of pairs differ by the action of `π₁(A, a₀)`.** If two
relative cubes of `(X, A, a₀)` are homotopic through maps of pairs, then the class of the second is
the transport of the class of the first along a loop in `A` at `a₀`. -/
theorem exists_transport_mk_eq_mk_of_homotopicWith [Fintype N]
    (h : (p : C(I × (I^N), X.pair.fst)).HomotopicWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map)) :
    ∃ γ : Path X.basepoint X.basepoint, transport γ (mk p) = mk q :=
  let ⟨γ, ⟨F⟩⟩ := RelGenLoop.exists_homotopyAlong_of_homotopicWith h
  ⟨γ, F.transport_mk⟩

/-- **Relative homotopy classes for a subspace with trivial fundamental group.** If `π₁(A, a₀)` is
trivial, two relative cubes of `(X, A, a₀)` have the same class in `π_{n+1}(X, A, a₀)` exactly when
they are homotopic through maps of pairs `(I × I^N, ∂(I × I^N)) → (X, A)`. -/
theorem mk_eq_mk_iff_homotopicWith [Finite N]
    [Subsingleton (FundamentalGroup X.pair.snd X.basepoint)] :
    mk p = mk q ↔ (p : C(I × (I^N), X.pair.fst)).HomotopicWith q
      fun f ↦ MapsTo f (Cube.prodBoundary N) (range X.pair.map) := by
  refine ⟨fun h ↦ (mk_eq_mk.1 h).homotopicWith, fun h ↦ ?_⟩
  have := Fintype.ofFinite N
  obtain ⟨γ, hγ⟩ := exists_transport_mk_eq_mk_of_homotopicWith h
  -- The loop `γ` is null-homotopic, so transport along it is the identity.
  have hγ' := subsingleton_fundamentalGroup_iff.1 ‹_› γ
  rw [← hγ, transport_congr hγ', transport_refl, id]

/-- **The relative homotopy class of a map of pairs.** If `B ⊆ Y` is simply connected and `b ∈ B`,
then every map of pairs `g : (I × I^N, ∂(I × I^N)) → (Y, B)` is homotopic through maps of pairs to
a relative cube at `b`, and all such relative cubes have the same class in `π_{n+1}(Y, B, b)`. -/
theorem existsUnique_homotopicWith [Finite N] {Y : TopCat.{u}} {B : Set Y}
    [SimplyConnectedSpace B] (b : B) (g : C(I × (I^N), Y)) (hg : MapsTo g (Cube.prodBoundary N) B) :
    ∃! x : RelHomotopyGroup N ⟨TopPair.ofSubset B, b⟩,
      ∃ p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩,
        mk p = x ∧ g.HomotopicWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B := by
  have := Fintype.ofFinite N
  have : SimplyConnectedSpace (TopPair.ofSubset B).snd := ‹SimplyConnectedSpace B›
  -- Deform `g` to a relative cube at some point `b'`, and transport it along a path to `b`.
  obtain ⟨b', -, p, hgp⟩ := exists_homotopicWith_relGenLoop g hg
  have hpq := (RelGenLoop.collarHomotopyAlong (PathConnectedSpace.somePath b' b) p).homotopicWith
  rw [TopPair.range_ofSubset_map] at hpq
  refine ⟨mk (RelGenLoop.transport (PathConnectedSpace.somePath b' b) p), ⟨_, rfl, hgp.trans hpq⟩,
    ?_⟩
  rintro _ ⟨q, rfl, hgq⟩
  refine mk_eq_mk_iff_homotopicWith.2 ?_
  rw [TopPair.range_ofSubset_map]
  exact hgq.symm.trans (hgp.trans hpq)

end RelHomotopyGroup

end TauCeti
