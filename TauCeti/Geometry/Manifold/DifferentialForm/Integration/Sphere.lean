/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Cylinder
public import TauCeti.Topology.Homotopy.HomotopyGroup.FundamentalGroupAction
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Homotopy.Homotopic.Rel
import Mathlib.Topology.Order.ProjIcc

/-!
# Integrals of closed two-forms over the second homotopy group

Let `M` be a compact boundaryless manifold, `x ∈ M`, and `φ` a closed `C¹` two-form on `M` with
values in a normed space `F`. This file constructs the integral of `φ` over the classes of the
second homotopy group `π₂(M, x)`, as a homomorphism

`TauCeti.sphereIntegralHom : Additive (π_ 2 M x) →+ F`.

For the symplectic form of a closed symplectic manifold it is the symplectic area of spheres. In
capped Hamiltonian Floer theory this is the area `ω(B)` by which the action of a capped loop
changes when a sphere `B` is glued to its cap.

An element of `π₂(M, x)` is a homotopy class, relative to the boundary of the unit square, of
continuous maps of the unit square sending its boundary to `x`. Such a map need not be
differentiable, so the integral is computed on a smooth representative:

* a **smooth sphere** at `x` (`TauCeti.IsSmoothSphere`) is a smooth map `v : ℝ × ℝ → M` equal to
  `x` off a closed square `[δ, 1 - δ]²` strictly inside the unit square; its restriction to the
  unit square is a generalized loop (`TauCeti.IsSmoothSphere.genLoop`);
* every class of `π₂(M, x)` is the class of a smooth sphere (`TauCeti.exists_isSmoothSphere`).
  A generalized loop is first deformed to one constant near the boundary of the square, by
  shrinking the square, and then smoothed relative to a neighbourhood of the boundary by the
  Whitney approximation theorem (`ContinuousMap.exists_contMDiff_homotopicRel`);
* two smooth spheres in the same class have the same integral
  (`TauCeti.rectangleIntegral_eq_of_isSmoothSphere_of_homotopic`). A homotopy between them,
  relative to the boundary of the square, is again made constant near the boundary of the square
  and then smoothed relative to its ends and to a neighbourhood of that boundary, and the integral
  of a closed form is invariant under smooth homotopies through spheres
  (`TauCeti.rectangleIntegral_eq_of_homotopy`).

So the integral `TauCeti.sphereIntegral φ x a` of `φ` over a class `a` is its integral over the
unit square along any smooth sphere representing `a` (`TauCeti.sphereIntegral_mk`). Concatenating
two smooth spheres along the first coordinate represents the product in `π₂(M, x)`, so the
integral is additive (`TauCeti.sphereIntegral_mul`). It is natural: the integral of the pullback
of a form along a smooth map `f` over a class `a` is the integral of the form over `f_* a`
(`TauCeti.sphereIntegral_mpullback`). A form that vanishes on spheres in the sense of
`TauCeti.VanishesOnSpheres` has zero integral over every class
(`TauCeti.VanishesOnSpheres.sphereIntegral_eq_zero`); in particular this holds for exact forms
(`TauCeti.sphereIntegral_mextDeriv`).

The integral does not depend on the base point: transporting a class along a path from `x` to `y`
(`TauCeti.homotopyGroupTransport`) does not change its integral
(`TauCeti.sphereIntegral_homotopyGroupTransport`). The path is first replaced by a homotopic
smooth path (`Path.exists_homotopic_contMDiff_extend`), along which a smooth sphere is slid by a
smooth homotopy that sends the boundary of the square to the moving base point. The side faces
of this homotopy collapse to the path, so they contribute nothing to the integral. In particular
the integral is invariant under the action of the fundamental group on `π₂(M, x)`
(`TauCeti.sphereIntegral_fundamentalGroup_smul`). This is the form in which the area of a sphere
glued to a cap is compatible with moving the base point of a capped loop.

## Main definitions

* `TauCeti.IsSmoothSphere I x v`: `v` is a smooth sphere at `x`.
* `TauCeti.IsSmoothSphere.genLoop`: the generalized loop of a smooth sphere.
* `TauCeti.sphereIntegral φ x`: the integral of `φ` over the classes of `π₂(M, x)`.
* `TauCeti.sphereIntegralHom`: for a closed form, the same integral as an additive homomorphism.

## Main results

* `TauCeti.exists_isSmoothSphere`: every class of `π₂(M, x)` is represented by a smooth sphere.
* `TauCeti.rectangleIntegral_eq_of_isSmoothSphere_of_homotopic`: homotopic smooth spheres have
  the same integral.
* `TauCeti.sphereIntegral_mk`: the integral over the class of a smooth sphere.
* `TauCeti.sphereIntegral_mul`, `TauCeti.sphereIntegral_one`: additivity.
* `TauCeti.sphereIntegral_mpullback`: naturality under smooth maps.
* `TauCeti.sphereIntegral_homotopyGroupTransport`: invariance under change of base point.
* `TauCeti.sphereIntegral_fundamentalGroup_smul`: invariance under the action of the fundamental
  group.
* `TauCeti.VanishesOnSpheres.sphereIntegral_eq_zero`, `TauCeti.sphereIntegral_mextDeriv`: forms
  vanishing on spheres, such as exact forms, have zero integral over every class.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorems 6.26
  and 6.29 (Whitney approximation, and smooth homotopies between homotopic smooth maps).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (homotopy invariance of integrals of closed forms).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  Section 11.1 (the symplectic area of spherical classes and capped loops).
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology Topology.Homotopy Interval

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {x : M}

/-! ### Smooth spheres -/

/-- The unit cube `I^2` in the plane, `y ↦ (y 0, y 1)`. -/
private def cubeToPlane : C((Fin 2 → unitInterval), ℝ × ℝ) :=
  ⟨fun y ↦ ((y 0 : ℝ), (y 1 : ℝ)), by fun_prop⟩

private theorem cubeToPlane_apply (y : Fin 2 → unitInterval) :
    cubeToPlane y = ((y 0 : ℝ), (y 1 : ℝ)) :=
  rfl

/-- The boundary of the unit cube lies outside every open square `(a, 1 - a)²` with `0 ≤ a`. -/
private theorem cubeToPlane_notMem {a : ℝ} (ha : 0 ≤ a) {y : (Fin 2 → unitInterval)}
    (hy : y ∈ Cube.boundary (Fin 2)) :
    cubeToPlane y ∉ Ioo a (1 - a) ×ˢ Ioo a (1 - a) := by
  obtain ⟨i, hi⟩ := hy
  rintro ⟨⟨h₀, h₀'⟩, ⟨h₁, h₁'⟩⟩
  fin_cases i <;> rcases hi with hi | hi <;> simp_all [cubeToPlane_apply] <;> linarith

/-- The generalized loop of a continuous map of the plane that is constant equal to `x` outside
the open unit square: its restriction to the unit square. -/
private def planeGenLoop (f : C(ℝ × ℝ, M)) (hf : ∀ z ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f z = x) :
    Ω^ (Fin 2) M x :=
  ⟨f.comp cubeToPlane, fun _ hy ↦ hf _ (by simpa using cubeToPlane_notMem le_rfl hy)⟩

/-- Two continuous maps of the plane that are homotopic relative to a set containing the
complement of an open square `(a, 1 - a)²`, `0 ≤ a`, have homotopic generalized loops. -/
private theorem planeGenLoop_homotopic {f g : C(ℝ × ℝ, M)}
    {hf : ∀ z ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, f z = x}
    {hg : ∀ z ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, g z = x} {a : ℝ} (ha : 0 ≤ a)
    (h : f.HomotopicRel g (Ioo a (1 - a) ×ˢ Ioo a (1 - a))ᶜ) :
    GenLoop.Homotopic (planeGenLoop f hf) (planeGenLoop g hg) :=
  (h.precomp cubeToPlane).mono fun _ hy ↦ cubeToPlane_notMem ha hy

variable (I) in
/-- A **smooth sphere** at `x`: a smooth map `v : ℝ × ℝ → M` that is constant equal to `x` off a
closed square `[δ, 1 - δ]²`, for some `δ > 0`. Its restriction to the unit square sends the
boundary of the square to `x`, so it is a generalized loop (`TauCeti.IsSmoothSphere.genLoop`)
and represents an element of `π₂(M, x)`. -/
structure IsSmoothSphere (x : M) (v : ℝ × ℝ → M) : Prop where
  /-- The map is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ v
  /-- The map is constant equal to `x` off a closed square strictly inside the unit square. -/
  exists_pos : ∃ δ > 0, ∀ z ∉ Icc δ (1 - δ) ×ˢ Icc δ (1 - δ), v z = x

namespace IsSmoothSphere

variable {v : ℝ × ℝ → M}

/-- A smooth sphere is constant equal to `x` off `[δ, 1 - δ]²` for all small enough `δ > 0`. -/
theorem exists_forall_le (hv : IsSmoothSphere I x v) :
    ∃ δ > 0, ∀ δ' ≤ δ, ∀ z ∉ Icc δ' (1 - δ') ×ˢ Icc δ' (1 - δ'), v z = x := by
  obtain ⟨δ, hδ, h⟩ := hv.exists_pos
  refine ⟨δ, hδ, fun δ' hδ' z hz ↦ h z fun hm ↦ hz ?_⟩
  have hsub : Icc δ (1 - δ) ⊆ Icc δ' (1 - δ') := Icc_subset_Icc hδ' (by linarith)
  exact prod_mono hsub hsub hm

/-- A smooth sphere is constant equal to `x` outside the open unit square. -/
theorem apply_of_notMem (hv : IsSmoothSphere I x v) {z : ℝ × ℝ}
    (hz : z ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) : v z = x := by
  obtain ⟨δ, hδ, h⟩ := hv.exists_pos
  have hsub : Icc δ (1 - δ) ⊆ Ioo 0 1 := Icc_subset_Ioo hδ (by linarith)
  exact h z fun hm ↦ hz (prod_mono hsub hsub hm)

/-- The generalized loop of a smooth sphere: its restriction to the unit square. -/
def genLoop (hv : IsSmoothSphere I x v) : Ω^ (Fin 2) M x :=
  planeGenLoop ⟨v, hv.contMDiff.continuous⟩ fun _ hz ↦ hv.apply_of_notMem hz

@[simp]
theorem genLoop_apply (hv : IsSmoothSphere I x v) (y : (Fin 2 → unitInterval)) :
    hv.genLoop y = v ((y 0 : ℝ), (y 1 : ℝ)) :=
  (rfl)

end IsSmoothSphere

/-- The constant map is a smooth sphere. -/
theorem isSmoothSphere_const (x : M) : IsSmoothSphere I x fun _ ↦ x :=
  ⟨contMDiff_const, 1, one_pos, fun _ _ ↦ rfl⟩

/-! ### Existence of smooth representatives -/

section Existence

/-- The coordinates of a point of the plane, as a family indexed by `Fin 2`. -/
private def planeCoord (z : ℝ × ℝ) : Fin 2 → ℝ := ![z.1, z.2]

private theorem continuous_planeCoord : Continuous planeCoord := by
  unfold planeCoord
  fun_prop

/-- Shrinking a generalized loop into the square `[1/4, 3/4]²`, as a map of the plane. -/
private def shrinkPlane (p : Ω^ (Fin 2) M x) : C(ℝ × ℝ, M) :=
  ⟨fun z ↦ p fun i ↦ projIcc 0 1 zero_le_one (2 * planeCoord z i - 1 / 2), by
    refine p.1.continuous.comp (continuous_pi fun i ↦ continuous_projIcc.comp ?_)
    exact (continuous_const.mul ((continuous_apply i).comp continuous_planeCoord)).sub
      continuous_const⟩

/-- A coordinate outside `(1/4, 3/4)` is sent to a vertex of the unit interval. -/
private theorem projIcc_shrink_eq {s : ℝ} (hs : s ∉ Ioo (1 / 4 : ℝ) (3 / 4)) :
    projIcc (0 : ℝ) 1 zero_le_one (2 * s - 1 / 2) = 0 ∨
      projIcc (0 : ℝ) 1 zero_le_one (2 * s - 1 / 2) = 1 := by
  rcases le_or_gt s (1 / 4) with h | h
  · exact Or.inl (projIcc_of_le_left _ (by linarith))
  · simp only [mem_Ioo, not_and, not_lt] at hs
    exact Or.inr (projIcc_of_right_le _ (by linarith [hs h]))

private theorem shrinkPlane_of_notMem (p : Ω^ (Fin 2) M x) {z : ℝ × ℝ}
    (hz : z ∉ Ioo (1 / 4 : ℝ) (3 / 4) ×ˢ Ioo (1 / 4 : ℝ) (3 / 4)) : shrinkPlane p z = x := by
  refine p.2 _ ?_
  simp only [mem_prod, not_and_or] at hz
  rcases hz with hz | hz
  · exact ⟨0, projIcc_shrink_eq hz⟩
  · exact ⟨1, projIcc_shrink_eq hz⟩

private theorem Ioo_quarter_subset : Ioo (1 / 4 : ℝ) (3 / 4) ⊆ Ioo 0 1 :=
  Ioo_subset_Ioo (by norm_num) (by norm_num)

/-- Shrinking a generalized loop does not change its class. -/
private theorem homotopic_shrinkPlane (p : Ω^ (Fin 2) M x) :
    GenLoop.Homotopic p (planeGenLoop (shrinkPlane p) fun _ hz ↦ shrinkPlane_of_notMem p
      fun hm ↦ hz (prod_mono Ioo_quarter_subset Ioo_quarter_subset hm)) := by
  -- Move each coordinate `s` linearly to `2 s - 1/2`, clamped to the unit interval.
  refine ⟨{
    toFun := fun q ↦ p fun i ↦ projIcc 0 1 zero_le_one (q.2 i + q.1 * (q.2 i - 1 / 2))
    continuous_toFun := p.1.continuous.comp (continuous_pi fun i ↦ continuous_projIcc.comp
      (by fun_prop))
    map_zero_left := fun y ↦ by simp
    map_one_left := fun y ↦ congrArg p <| funext fun i ↦ by
      fin_cases i <;> simp [planeCoord, cubeToPlane_apply] <;> ring_nf
    prop' := fun t y hy ↦ ?_ }⟩
  obtain ⟨i, hi⟩ := hy
  simp only [ContinuousMap.coe_mk]
  rw [p.2 y ⟨i, hi⟩]
  refine p.2 _ ⟨i, ?_⟩
  have ht : (0 : ℝ) ≤ t := t.2.1
  rcases hi with hi | hi
  · exact Or.inl (projIcc_of_le_left _ (by rw [hi, Icc.coe_zero]; linarith))
  · exact Or.inr (projIcc_of_right_le _ (by rw [hi, Icc.coe_one]; linarith))

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M]

/-- **Smooth representatives.** Every class of `π₂(M, x)` is the class of a smooth sphere. -/
theorem exists_isSmoothSphere (a : π_ 2 M x) :
    ∃ (v : ℝ × ℝ → M) (hv : IsSmoothSphere I x v), ⟦hv.genLoop⟧ = a := by
  induction a using Quotient.inductionOn with | h p => ?_
  -- The shrunk loop is constant near the complement `S` of `(1/5, 4/5)²`; smooth it there.
  set f := shrinkPlane p
  set S : Set (ℝ × ℝ) := (Ioo (1 / 5 : ℝ) (1 - 1 / 5) ×ˢ Ioo (1 / 5 : ℝ) (1 - 1 / 5))ᶜ
  set U : Set (ℝ × ℝ) := (Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Icc (1 / 4 : ℝ) (3 / 4))ᶜ
  have hfU : ∀ z ∈ U, f z = x := fun z hz ↦ shrinkPlane_of_notMem p fun hm ↦
    hz (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm)
  have hsub : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Ioo (1 / 5) (1 - 1 / 5) :=
    Icc_subset_Ioo (by norm_num) (by norm_num)
  have hSU : S ⊆ U := fun z hz hm ↦ hz (prod_mono hsub hsub hm)
  have hS : IsClosed S := (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl
  have hU : U ∈ 𝓝ˢ S := ((isClosed_Icc.prod isClosed_Icc).isOpen_compl.mem_nhdsSet).2 hSU
  obtain ⟨g, hg, hfg⟩ := f.exists_contMDiff_homotopicRel (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) ⊤ hS hU
    (contMDiffOn_const.congr hfU)
  have hgS : ∀ z ∈ S, g z = x := fun z hz ↦ (hfg.fst_eq_snd hz).symm.trans (hfU z (hSU hz))
  have hv : IsSmoothSphere I x g := ⟨hg, 1 / 5, by norm_num, fun z hz ↦ hgS z fun hm ↦
    hz (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm)⟩
  refine ⟨g, hv, Quotient.sound ?_⟩
  exact (planeGenLoop_homotopic (by norm_num) hfg).symm.trans (homotopic_shrinkPlane p).symm

end Existence

/-! ### Homotopy invariance -/

section Invariance

/-- A continuous map of the line onto itself which is the identity on `[δ, 1 - δ]` and doubles
the distance to `δ` below it and to `1 - δ` above it. Clamped to the unit interval, it shrinks
`[δ / 2, 1 - δ / 2]` onto the unit interval. -/
private def collapse (δ s : ℝ) : ℝ :=
  max (min s (2 * s - δ)) (2 * s - (1 - δ))

private theorem continuous_collapse (δ : ℝ) : Continuous (collapse δ) := by
  unfold collapse
  fun_prop

private theorem collapse_of_mem {δ s : ℝ} (hs : s ∈ Icc δ (1 - δ)) : collapse δ s = s := by
  rw [collapse, min_eq_left (by linarith [hs.1]), max_eq_left (by linarith [hs.2])]

private theorem collapse_of_lt {δ s : ℝ} (hδ : δ ≤ 1 / 4) (hs : s < δ) :
    collapse δ s = 2 * s - δ := by
  rw [collapse, min_eq_right (by linarith), max_eq_left (by linarith)]

private theorem collapse_of_gt {δ s : ℝ} (hδ : δ ≤ 1 / 4) (hs : 1 - δ < s) :
    collapse δ s = 2 * s - (1 - δ) := by
  rw [collapse, min_eq_left (by linarith), max_eq_right (by linarith)]

/-- The clamped collapse keeps points outside `[δ, 1 - δ]` outside it. -/
private theorem projIcc_collapse_notMem {δ s : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hs : s ∉ Icc δ (1 - δ)) :
    (projIcc 0 1 zero_le_one (collapse δ s) : ℝ) ∉ Icc δ (1 - δ) := by
  rw [coe_projIcc]
  simp only [mem_Icc, not_and_or, not_le] at hs ⊢
  rcases hs with hs | hs
  · rw [collapse_of_lt hδ' hs]
    exact Or.inl (max_lt hδ ((min_le_right _ _).trans_lt (by linarith)))
  · rw [collapse_of_gt hδ' hs]
    exact Or.inr ((lt_min (by linarith) (by linarith)).trans_le (le_max_right _ _))

/-- The clamped collapse sends points outside `(δ / 2, 1 - δ / 2)` to a vertex of the unit
interval. -/
private theorem projIcc_collapse_eq {δ s : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hs : s ∉ Ioo (δ / 2) (1 - δ / 2)) :
    projIcc (0 : ℝ) 1 zero_le_one (collapse δ s) = 0 ∨
      projIcc (0 : ℝ) 1 zero_le_one (collapse δ s) = 1 := by
  simp only [mem_Ioo, not_and_or, not_lt] at hs
  rcases hs with hs | hs
  · exact Or.inl (projIcc_of_le_left _ (by rw [collapse_of_lt hδ' (by linarith)]; linarith))
  · exact Or.inr (projIcc_of_right_le _ (by rw [collapse_of_gt hδ' (by linarith)]; linarith))

/-- The collapse of the plane, coordinatewise, into the unit cube. -/
private def planeCollapse (δ : ℝ) (z : ℝ × ℝ) : Fin 2 → unitInterval :=
  fun i ↦ projIcc 0 1 zero_le_one (collapse δ (planeCoord z i))

private theorem continuous_planeCollapse (δ : ℝ) : Continuous (planeCollapse δ) :=
  continuous_pi fun i ↦ continuous_projIcc.comp
    ((continuous_collapse δ).comp ((continuous_apply i).comp continuous_planeCoord))

omit [TopologicalSpace M] in
/-- A map equal to `x` off `[δ, 1 - δ]²` does not change when precomposed with the collapse. -/
private theorem apply_planeCollapse {u : ℝ × ℝ → M} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4)
    (hu : ∀ z ∉ Icc δ (1 - δ) ×ˢ Icc δ (1 - δ), u z = x) (z : ℝ × ℝ) :
    u (cubeToPlane (planeCollapse δ z)) = u z := by
  have hc : cubeToPlane (planeCollapse δ z) = ((projIcc 0 1 zero_le_one (collapse δ z.1) : ℝ),
      (projIcc 0 1 zero_le_one (collapse δ z.2) : ℝ)) := (rfl)
  rw [hc]
  by_cases hz : z ∈ Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)
  · have h01 {s : ℝ} (hs : s ∈ Icc δ (1 - δ)) : s ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [collapse_of_mem hz.1, collapse_of_mem hz.2, projIcc_of_mem _ (h01 hz.1),
      projIcc_of_mem _ (h01 hz.2)]
  · rw [hu z hz, hu]
    simp only [mem_prod, not_and_or] at hz ⊢
    exact hz.imp (projIcc_collapse_notMem hδ hδ') (projIcc_collapse_notMem hδ hδ')

/-- Points outside `(δ / 2, 1 - δ / 2)²` collapse to the boundary of the unit cube. -/
private theorem planeCollapse_mem_boundary {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) {z : ℝ × ℝ}
    (hz : z ∉ Ioo (δ / 2) (1 - δ / 2) ×ˢ Ioo (δ / 2) (1 - δ / 2)) :
    planeCollapse δ z ∈ Cube.boundary (Fin 2) := by
  simp only [mem_prod, not_and_or] at hz
  rcases hz with hz | hz
  · exact ⟨0, projIcc_collapse_eq hδ hδ' hz⟩
  · exact ⟨1, projIcc_collapse_eq hδ hδ' hz⟩

/-- A homotopy between the generalized loops of two smooth spheres, relative to the boundary of
the square, collapsed near that boundary: a continuous map of `(ℝ × ℝ) × ℝ` that is `v` at times
`c ≤ 0`, `w` at times `c ≥ 1`, and `x` off a square `(δ, 1 - δ)²`. -/
private theorem exists_continuous_homotopy {v w : ℝ × ℝ → M} (hv : IsSmoothSphere I x v)
    (hw : IsSmoothSphere I x w) (h : GenLoop.Homotopic hv.genLoop hw.genLoop) :
    ∃ δ > 0, ∃ G : C((ℝ × ℝ) × ℝ, M), (∀ q : (ℝ × ℝ) × ℝ, q.2 ≤ 0 → G q = v q.1) ∧
      (∀ q : (ℝ × ℝ) × ℝ, 1 ≤ q.2 → G q = w q.1) ∧
      ∀ q : (ℝ × ℝ) × ℝ, q.1 ∉ Ioo δ (1 - δ) ×ˢ Ioo δ (1 - δ) → G q = x := by
  obtain ⟨δv, hδv, hv'⟩ := hv.exists_forall_le
  obtain ⟨δw, hδw, hw'⟩ := hw.exists_forall_le
  set δ := min (min δv δw) (1 / 4)
  have hδ : 0 < δ := lt_min (lt_min hδv hδw) (by norm_num)
  have hδ' : δ ≤ 1 / 4 := min_le_right _ _
  obtain ⟨K⟩ := h
  refine ⟨δ / 2, by positivity,
    ⟨fun q ↦ K (projIcc 0 1 zero_le_one q.2, planeCollapse δ q.1),
      K.continuous.comp ((continuous_projIcc.comp continuous_snd).prodMk
        ((continuous_planeCollapse δ).comp continuous_fst))⟩, fun q hq ↦ ?_, fun q hq ↦ ?_,
    fun q hq ↦ ?_⟩
  · rw [ContinuousMap.coe_mk, projIcc_of_le_left _ hq]
    exact (K.apply_zero _).trans (apply_planeCollapse hδ hδ'
      (hv' δ ((min_le_left _ _).trans (min_le_left _ _))) q.1)
  · rw [ContinuousMap.coe_mk, projIcc_of_right_le _ hq]
    exact (K.apply_one _).trans (apply_planeCollapse hδ hδ'
      (hw' δ ((min_le_left _ _).trans (min_le_right _ _))) q.1)
  · have hb := planeCollapse_mem_boundary hδ hδ' (z := q.1) (by simpa using hq)
    exact (K.eq_fst _ hb).trans (hv.genLoop.2 _ hb)

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M]

/-- A smooth homotopy between two homotopic smooth spheres: a smooth map of `(ℝ × ℝ) × ℝ` that is
`v` at time `-1`, `w` at time `2`, and `x` off a square `(δ, 1 - δ)²` at all times. It is the
collapsed homotopy of `exists_continuous_homotopy`, smoothed by Whitney approximation relative to
the closed set where it is already smooth. -/
private theorem exists_contMDiff_homotopy {v w : ℝ × ℝ → M} (hv : IsSmoothSphere I x v)
    (hw : IsSmoothSphere I x w) (h : GenLoop.Homotopic hv.genLoop hw.genLoop) :
    ∃ δ > 0, ∃ G : (ℝ × ℝ) × ℝ → M, ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I ∞ G ∧
      (∀ z, G (z, -1) = v z) ∧ (∀ z, G (z, 2) = w z) ∧
      ∀ z ∉ Ioo δ (1 - δ) ×ˢ Ioo δ (1 - δ), ∀ c, G (z, c) = x := by
  obtain ⟨δ, hδ, G₀, hG₀v, hG₀w, hG₀x⟩ := exists_continuous_homotopy hv hw h
  -- `G₀` is smooth on the open set `U`, a neighbourhood of the closed set `S`.
  set S : Set ((ℝ × ℝ) × ℝ) := {q | q.2 ≤ -1} ∪ {q | 2 ≤ q.2} ∪
    {q | q.1 ∉ Ioo (δ / 2) (1 - δ / 2) ×ˢ Ioo (δ / 2) (1 - δ / 2)}
  have hS : IsClosed S :=
    ((isClosed_le continuous_snd continuous_const).union
      (isClosed_le continuous_const continuous_snd)).union
      ((isOpen_Ioo.prod isOpen_Ioo).preimage continuous_fst).isClosed_compl
  have hU₀ : IsOpen {q : (ℝ × ℝ) × ℝ | q.2 < 0} := isOpen_lt continuous_snd continuous_const
  have hU₁ : IsOpen {q : (ℝ × ℝ) × ℝ | 1 < q.2} := isOpen_lt continuous_const continuous_snd
  have hU₂ : IsOpen {q : (ℝ × ℝ) × ℝ | q.1 ∉ Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)} :=
    ((isClosed_Icc.prod isClosed_Icc).preimage continuous_fst).isOpen_compl
  have hSU : S ⊆ {q | q.2 < 0} ∪ {q | 1 < q.2} ∪ {q | q.1 ∉ Icc δ (1 - δ) ×ˢ Icc δ (1 - δ)} := by
    rintro q ((hq | hq) | hq)
    · exact Or.inl (Or.inl (by simp only [mem_ofPred_eq] at hq ⊢; linarith))
    · exact Or.inl (Or.inr (by simp only [mem_ofPred_eq] at hq ⊢; linarith))
    · have hsub : Icc δ (1 - δ) ⊆ Ioo (δ / 2) (1 - δ / 2) :=
        Icc_subset_Ioo (by linarith) (by linarith)
      exact Or.inr fun hm ↦ hq (prod_mono hsub hsub hm)
  have hfst : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (Prod.fst : (ℝ × ℝ) × ℝ → ℝ × ℝ) :=
    contDiff_fst.contMDiff
  obtain ⟨G, hG, hG₀G⟩ := G₀.exists_contMDiff_homotopicRel (I := 𝓘(ℝ, (ℝ × ℝ) × ℝ)) (J := I) ⊤
    hS ((((hU₀.union hU₁).union hU₂).mem_nhdsSet).2 hSU) (by
      rintro q ((hq | hq) | hq)
      · exact ((hv.contMDiff.comp hfst).contMDiffAt.congr_of_eventuallyEq
          (eventually_of_mem (hU₀.mem_nhds hq) fun r hr ↦ hG₀v r (le_of_lt hr))).contMDiffWithinAt
      · exact ((hw.contMDiff.comp hfst).contMDiffAt.congr_of_eventuallyEq
          (eventually_of_mem (hU₁.mem_nhds hq) fun r hr ↦ hG₀w r (le_of_lt hr))).contMDiffWithinAt
      · exact (contMDiffAt_const.congr_of_eventuallyEq (eventually_of_mem (hU₂.mem_nhds hq)
          fun r hr ↦ hG₀x r fun hm ↦ hr (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm))
          ).contMDiffWithinAt)
  have hGS (q : (ℝ × ℝ) × ℝ) (hq : q ∈ S) : G q = G₀ q := (hG₀G.fst_eq_snd hq).symm
  refine ⟨δ / 2, by positivity, G, hG, fun z ↦ ?_, fun z ↦ ?_, fun z hz c ↦ ?_⟩
  · exact (hGS _ (Or.inl (Or.inl (by simp)))).trans (hG₀v _ (by norm_num))
  · exact (hGS _ (Or.inl (Or.inr (by simp)))).trans (hG₀w _ (by norm_num))
  · have hsub : Ioo δ (1 - δ) ⊆ Ioo (δ / 2) (1 - δ / 2) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    exact (hGS _ (Or.inr hz)).trans (hG₀x _ fun hm ↦ hz (prod_mono hsub hsub hm))

/-- **Homotopy invariance.** Two smooth spheres at `x` whose generalized loops are homotopic
relative to the boundary of the unit square have the same integral of a closed `C¹` two-form over
the unit square. -/
theorem rectangleIntegral_eq_of_isSmoothSphere_of_homotopic {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {v w : ℝ × ℝ → M}
    (hv : IsSmoothSphere I x v) (hw : IsSmoothSphere I x w)
    (h : GenLoop.Homotopic hv.genLoop hw.genLoop) :
    rectangleIntegral φ v (0, 0) (1, 1) = rectangleIntegral φ w (0, 0) (1, 1) := by
  obtain ⟨δ, hδ, G, hG, hGv, hGw, hGx⟩ := exists_contMDiff_homotopy hv hw h
  -- Reparametrize time so that `[0, 1]` covers `[-1, 2]`, and apply homotopy invariance.
  let Φ : (ℝ × ℝ) × ℝ → M := fun q ↦ G (q.1, 3 * q.2 - 1)
  have hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ :=
    (hG.comp (contDiff_fst.prodMk (by fun_prop : ContDiff ℝ ∞
      fun q : (ℝ × ℝ) × ℝ ↦ 3 * q.2 - 1)).contMDiff).of_le (by norm_cast)
  -- The edges of the unit square stay at `x`.
  have hΦx (z : ℝ × ℝ) (hz : z ∉ Ioo δ (1 - δ) ×ˢ Ioo δ (1 - δ)) (c : ℝ) : Φ (z, c) = x :=
    hGx z hz _
  have hlo {s : ℝ} (hs : s = 0) : s ∉ Ioo δ (1 - δ) := fun hm ↦ by linarith [hm.1]
  have hhi {s : ℝ} (hs : s = 1) : s ∉ Ioo δ (1 - δ) := fun hm ↦ by linarith [hm.2]
  have key := rectangleIntegral_eq_of_homotopy hφ hdφ hΦ (a := (0, 0)) (b := (1, 1))
    (Or.inr fun t _ c _ ↦ by
      rw [hΦx _ (fun hm ↦ hlo rfl hm.1), hΦx _ (fun hm ↦ hlo rfl hm.1)])
    (Or.inr fun t _ c _ ↦ by
      rw [hΦx _ (fun hm ↦ hhi rfl hm.1), hΦx _ (fun hm ↦ hhi rfl hm.1)])
    (fun s _ c _ ↦ by
      rw [hΦx _ (fun hm ↦ hhi rfl hm.2), hΦx _ (fun hm ↦ hlo rfl hm.2)])
  have hΦ₁ : (fun z ↦ Φ (z, 1)) = w := funext fun z ↦ by
    convert hGw z using 3; norm_num
  have hΦ₀ : (fun z ↦ Φ (z, 0)) = v := funext fun z ↦ by
    convert hGv z using 3; norm_num
  rw [hΦ₁, hΦ₀] at key
  exact key.symm

end Invariance

/-! ### Concatenation of smooth spheres -/

section Concat

/-- The concatenation of two maps of the plane along the first coordinate: `w` reparametrized
on `s ≤ 1/2`, then `v` reparametrized on `s > 1/2`. For generalized loops this is
`GenLoop.transAt 0`. -/
private def sphereConcat (w v : ℝ × ℝ → M) (z : ℝ × ℝ) : M :=
  if z.1 ≤ 1 / 2 then w (2 * z.1, z.2) else v (2 * z.1 - 1, z.2)

variable {v w : ℝ × ℝ → M}

private theorem IsSmoothSphere.concat (hw : IsSmoothSphere I x w) (hv : IsSmoothSphere I x v) :
    IsSmoothSphere I x (sphereConcat w v) := by
  obtain ⟨δw, hδw, hw'⟩ := hw.exists_forall_le
  obtain ⟨δv, hδv, hv'⟩ := hv.exists_forall_le
  set δ := min δw δv
  have hwδ := hw' δ (min_le_left _ _)
  have hvδ := hv' δ (min_le_right _ _)
  have hδ : 0 < δ := lt_min hδw hδv
  -- Near the seam `s = 1/2` both pieces are constant equal to `x`.
  have hseam (z : ℝ × ℝ) (hz : z.1 ∈ Ioo (1 / 2 - δ / 2) (1 / 2 + δ / 2)) :
      sphereConcat w v z = x := by
    unfold sphereConcat
    split_ifs with h
    · exact hwδ _ fun hm ↦ by simp only [mem_prod, mem_Icc] at hm; linarith [hz.1]
    · exact hvδ _ fun hm ↦ by simp only [mem_prod, mem_Icc] at hm; linarith [hz.2]
  refine ⟨fun p ↦ ?_, δ / 2, by positivity, fun z hz ↦ ?_⟩
  · rcases lt_trichotomy p.1 (1 / 2) with hp | hp | hp
    · refine ((hw.contMDiff.comp (by fun_prop : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦
        (2 * z.1, z.2)).contMDiff).contMDiffAt).congr_of_eventuallyEq ?_
      exact eventually_of_mem ((isOpen_lt continuous_fst continuous_const).mem_nhds hp)
        fun z hz ↦ ite_eq_left (le_of_lt hz)
    · refine contMDiffAt_const.congr_of_eventuallyEq
        (eventually_of_mem ((isOpen_Ioo.preimage continuous_fst).mem_nhds ?_) hseam)
      exact ⟨by linarith, by linarith⟩
    · refine ((hv.contMDiff.comp (by fun_prop : ContDiff ℝ ∞ fun z : ℝ × ℝ ↦
        (2 * z.1 - 1, z.2)).contMDiff).contMDiffAt).congr_of_eventuallyEq ?_
      exact eventually_of_mem ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
        fun z hz ↦ ite_eq_right (not_le.2 hz)
  · unfold sphereConcat
    split_ifs with h
    · refine hwδ _ fun hm ↦ hz ?_
      simp only [mem_prod, mem_Icc] at hm
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · refine hvδ _ fun hm ↦ hz ?_
      simp only [mem_prod, mem_Icc] at hm
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- Concatenating smooth spheres concatenates their generalized loops. -/
private theorem IsSmoothSphere.genLoop_concat (hw : IsSmoothSphere I x w)
    (hv : IsSmoothSphere I x v) :
    (hw.concat hv).genLoop = GenLoop.transAt 0 hw.genLoop hv.genLoop := by
  ext y
  rw [GenLoop.transAt, GenLoop.coe_copy, IsSmoothSphere.genLoop_apply]
  have h0 : (y 0 : ℝ) ∈ Icc (0 : ℝ) 1 := (y 0).2
  unfold sphereConcat
  split_ifs with h
  · rw [IsSmoothSphere.genLoop_apply, Function.update_self, Function.update_of_ne (by decide),
      projIcc_of_mem _ ⟨by linarith [h0.1], by linarith⟩]
  · rw [IsSmoothSphere.genLoop_apply, Function.update_self, Function.update_of_ne (by decide),
      projIcc_of_mem _ ⟨by linarith, by linarith [h0.2]⟩]

/-- The integral over a concatenation of smooth spheres is the sum of the integrals. -/
private theorem rectangleIntegral_sphereConcat [IsManifold I 1 M] {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 0 φ) (hw : IsSmoothSphere I x w) (hv : IsSmoothSphere I x v) :
    rectangleIntegral φ (sphereConcat w v) (0, 0) (1, 1) =
      rectangleIntegral φ w (0, 0) (1, 1) + rectangleIntegral φ v (0, 0) (1, 1) := by
  have h1 {u : ℝ × ℝ → M} (hu : IsSmoothSphere I x u) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u :=
    hu.contMDiff.of_le (by simp)
  rw [← rectangleIntegral_add_adjacent_fst hφ (h1 (hw.concat hv)) (0, 0) (1, 1) (1 / 2)]
  congr 1
  · rw [rectangleIntegral_congr (v := w ∘ Prod.map (fun s ↦ 2 * s) id) fun z hz ↦ ?_,
      rectangleIntegral_comp_prodMap hφ (h1 hw) (σ' := fun _ ↦ 2)
        (fun s _ ↦ by simpa using (hasDerivAt_id s).const_mul 2) continuousOn_const]
    · norm_num
    · have hz1 : z.1 ∈ Icc (0 : ℝ) (1 / 2) := uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2) ▸ hz.1
      exact ite_eq_left hz1.2
  · rw [rectangleIntegral_congr (v := v ∘ Prod.map (fun s ↦ 2 * s - 1) id) fun z hz ↦ ?_,
      rectangleIntegral_comp_prodMap hφ (h1 hv) (σ' := fun _ ↦ 2)
        (fun s _ ↦ by simpa using ((hasDerivAt_id s).const_mul 2).sub_const 1)
        continuousOn_const]
    · norm_num
    · have hz1 := (uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1) ▸ hz.1)
      unfold sphereConcat
      split_ifs with h
      · have hz' : z.1 = 1 / 2 := le_antisymm h hz1.1
        have hw1 : w (2 * z.1, z.2) = x :=
          hw.apply_of_notMem fun hm ↦ by rw [hz'] at hm; norm_num at hm
        have hv0 : v (2 * z.1 - 1, z.2) = x :=
          hv.apply_of_notMem fun hm ↦ by rw [hz'] at hm; norm_num at hm
        exact hw1.trans hv0.symm
      · rfl

end Concat

/-! ### The integral over the second homotopy group -/

section Integral

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M]

/-- The integral of a two-form `φ` over a class `a ∈ π₂(M, x)`: its integral over the unit
square along a smooth sphere representing `a`. For a closed `C¹` form it does not depend on the
representative (`TauCeti.sphereIntegral_mk`), and it is additive (`TauCeti.sphereIntegral_mul`).
For the symplectic form of a symplectic manifold it is the symplectic area of spheres. -/
def sphereIntegral (φ : RoughForm I M F 2) (x : M) (a : π_ 2 M x) : F :=
  rectangleIntegral φ (exists_isSmoothSphere (I := I) a).choose (0, 0) (1, 1)

variable {φ : RoughForm I M F 2}

/-- The integral of a closed `C¹` form over the class of a smooth sphere is its integral over the
unit square along the sphere. -/
theorem sphereIntegral_mk (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {v : ℝ × ℝ → M}
    (hv : IsSmoothSphere I x v) :
    sphereIntegral φ x ⟦hv.genLoop⟧ = rectangleIntegral φ v (0, 0) (1, 1) := by
  obtain ⟨hv', h⟩ := (exists_isSmoothSphere (I := I) (⟦hv.genLoop⟧ : π_ 2 M x)).choose_spec
  exact rectangleIntegral_eq_of_isSmoothSphere_of_homotopic hφ hdφ hv' hv (Quotient.exact h)

/-- The integral of a closed `C¹` form over the identity class vanishes. -/
@[simp]
theorem sphereIntegral_one (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    sphereIntegral φ x 1 = 0 := by
  have h : (isSmoothSphere_const (I := I) x).genLoop = GenLoop.const := GenLoop.ext _ _ fun _ ↦ rfl
  rw [HomotopyGroup.one_def, ← h, sphereIntegral_mk hφ hdφ, rectangleIntegral_const]

/-- **Additivity.** The integral of a closed `C¹` form over a product of classes of `π₂(M, x)` is
the sum of the integrals. -/
theorem sphereIntegral_mul (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) (a b : π_ 2 M x) :
    sphereIntegral φ x (a * b) = sphereIntegral φ x a + sphereIntegral φ x b := by
  obtain ⟨v, hv, rfl⟩ := exists_isSmoothSphere (I := I) a
  obtain ⟨w, hw, rfl⟩ := exists_isSmoothSphere (I := I) b
  have hmul := HomotopyGroup.mul_spec (i := (0 : Fin 2)) (p := hv.genLoop) (q := hw.genLoop)
  beta_reduce at hmul
  rw [hmul, ← hw.genLoop_concat hv, sphereIntegral_mk hφ hdφ, sphereIntegral_mk hφ hdφ,
    sphereIntegral_mk hφ hdφ, rectangleIntegral_sphereConcat (hφ.of_le (by simp)) hw hv,
    add_comm]

variable (x) in
/-- The integral of a closed `C¹` two-form over the second homotopy group, as an additive
homomorphism. For the symplectic form of a symplectic manifold it is the symplectic area of
spheres. -/
def sphereIntegralHom (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) :
    Additive (π_ 2 M x) →+ F where
  toFun a := sphereIntegral φ x a.toMul
  map_zero' := sphereIntegral_one hφ hdφ
  map_add' a b := sphereIntegral_mul hφ hdφ a.toMul b.toMul

@[simp]
theorem sphereIntegralHom_apply (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (a : Additive (π_ 2 M x)) :
    sphereIntegralHom x hφ hdφ a = sphereIntegral φ x a.toMul :=
  (rfl)

/-- A form that vanishes on spheres has zero integral over every class of `π₂(M, x)`. -/
theorem VanishesOnSpheres.sphereIntegral_eq_zero (hS : VanishesOnSpheres φ) (a : π_ 2 M x) :
    sphereIntegral φ x a = 0 := by
  obtain ⟨hv, -⟩ := (exists_isSmoothSphere (I := I) a).choose_spec
  have hx {z : ℝ × ℝ} (hz : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1) :
      (exists_isSmoothSphere (I := I) a).choose z = x := by
    refine hv.apply_of_notMem fun hm ↦ ?_
    rcases hz with hz | hz | hz | hz <;> simp [hz] at hm
  refine (vanishesOnSpheres_iff φ).1 hS _ hv.contMDiff (fun t _ ↦ ?_) (fun t _ ↦ ?_) (fun s _ ↦ ?_)
  · rw [hx (Or.inl rfl), hx (Or.inl rfl)]
  · rw [hx (Or.inr (Or.inl rfl)), hx (Or.inr (Or.inl rfl))]
  · rw [hx (Or.inr (Or.inr (Or.inr rfl))), hx (Or.inr (Or.inr (Or.inl rfl)))]

/-- The integral of an exact two-form over every class of `π₂(M, x)` vanishes. -/
@[simp]
theorem sphereIntegral_mextDeriv {α : RoughForm I M F 1} (hα : IsSmoothForm I 1 α)
    (a : π_ 2 M x) : sphereIntegral (mextDeriv α) x a = 0 :=
  (vanishesOnSpheres_mextDeriv hα).sphereIntegral_eq_zero a

/-- **Naturality.** For a smooth map `f : M → M'` of compact manifolds and a closed `C¹` two-form
`φ` on `M'`, the integral of the pullback `f^* φ` over a class `a ∈ π₂(M, x)` is the integral of
`φ` over its image `f_* a ∈ π₂(M', f x)`. -/
theorem sphereIntegral_mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    [I'.Boundaryless] [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [CompactSpace M'] [T2Space M'] {f : M → M'} (hf : ContMDiff I I' ∞ f)
    {φ : RoughForm I' M' F 2} (hφ : IsSmoothForm I' 1 φ) (hdφ : mextDeriv φ = 0)
    (a : π_ 2 M x) :
    sphereIntegral (mpullback I I' f φ) x a =
      sphereIntegral φ (f x) (HomotopyGroup.map ⟨f, hf.continuous⟩ rfl a) := by
  obtain ⟨hv, h⟩ := (exists_isSmoothSphere (I := I) a).choose_spec
  set v := (exists_isSmoothSphere (I := I) a).choose
  have hfv : IsSmoothSphere I' (f x) (f ∘ v) := by
    obtain ⟨δ, hδ, hvx⟩ := hv.exists_pos
    exact ⟨hf.comp hv.contMDiff, δ, hδ, fun z hz ↦ congrArg f (hvx z hz)⟩
  have hmap : GenLoop.map ⟨f, hf.continuous⟩ rfl hv.genLoop = hfv.genLoop :=
    GenLoop.ext _ _ fun _ ↦ by simp
  conv_rhs => rw [← h, HomotopyGroup.map_mk, hmap, sphereIntegral_mk hφ hdφ hfv]
  exact rectangleIntegral_mpullback φ (fun z _ ↦ (hf _).mdifferentiableAt (by simp))
    (fun z _ ↦ (hv.contMDiff z).mdifferentiableAt (by simp))

end Integral

/-! ### Base-point change -/

section Transport

/-- **Sliding a smooth sphere along a smooth curve.** For a smooth sphere `v` at `x` and a smooth
curve `g` with `g 0 = x` there is a smooth homotopy `Φ` from `v` which, at every time `c`, sends
the complement of the open unit square to `g c`, and which ends at a smooth sphere at `g 1`. -/
private theorem IsSmoothSphere.exists_homotopy {v : ℝ × ℝ → M} (hv : IsSmoothSphere I x v)
    {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ g) (hg₀ : g 0 = x) :
    ∃ Φ : (ℝ × ℝ) × ℝ → M, ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I ∞ Φ ∧ (∀ z, Φ (z, 0) = v z) ∧
      (∀ c, ∀ z ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, Φ (z, c) = g c) ∧
      IsSmoothSphere I (g 1) fun z ↦ Φ (z, 1) := by
  classical
  -- `v` is constant equal to `x` off the square `K`.
  obtain ⟨d, hd, hvK⟩ := hv.exists_pos
  set K : Set (ℝ × ℝ) := Icc d (1 - d) ×ˢ Icc d (1 - d)
  -- A smooth cutoff `β` vanishing on a neighbourhood `U` of `K`, equal to `1` off
  -- `[d / 2, 1 - d / 2]²`.
  set U : Set (ℝ × ℝ) := Ioo (3 * d / 4) (1 - 3 * d / 4) ×ˢ Ioo (3 * d / 4) (1 - 3 * d / 4)
  have hsub : Icc (3 * d / 4) (1 - 3 * d / 4) ⊆ Ioo (d / 2) (1 - d / 2) :=
    Icc_subset_Ioo (by linarith) (by linarith)
  obtain ⟨β, hβ, -, hβ₀, hβ₁⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (isClosed_Icc.prod isClosed_Icc) (isOpen_Ioo.prod isOpen_Ioo).isClosed_compl
    (disjoint_compl_right_iff_subset.2 (prod_mono hsub hsub))
  have hKU : K ⊆ U := by
    have h : Icc d (1 - d) ⊆ Ioo (3 * d / 4) (1 - 3 * d / 4) :=
      Icc_subset_Ioo (by linarith) (by linarith)
    exact prod_mono h h
  have hβU {z : ℝ × ℝ} (hz : z ∈ U) : β z = 0 :=
    (hβ₀ z).1 (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hz)
  have hout {z : ℝ × ℝ} (hz : z ∉ Icc (d / 2) (1 - d / 2) ×ˢ Icc (d / 2) (1 - d / 2)) :
      z ∉ K ∧ β z = 1 := by
    have h : Icc d (1 - d) ⊆ Icc (d / 2) (1 - d / 2) := Icc_subset_Icc (by linarith) (by linarith)
    exact ⟨fun hm ↦ hz (prod_mono h h hm),
      (hβ₁ z).1 fun hm ↦ hz (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hm)⟩
  -- Inside `K` the homotopy is `v`; outside it runs along `g` up to time `c β z`.
  let Φ : (ℝ × ℝ) × ℝ → M := fun p ↦ if p.1 ∈ K then v p.1 else g (p.2 * β p.1)
  have hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I ∞ Φ := by
    intro p
    by_cases hp : p.1 ∈ U
    · refine (hv.contMDiff.comp contDiff_fst.contMDiff).contMDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [((isOpen_Ioo.prod isOpen_Ioo).preimage continuous_fst).mem_nhds hp]
        with q hq
      by_cases hqK : q.1 ∈ K
      · simp [Φ, hqK]
      · simp [Φ, hqK, hβU hq, hg₀, hvK _ hqK]
    · refine ContMDiffAt.congr_of_eventuallyEq
        (hg.comp (contDiff_snd.mul (hβ.comp contDiff_fst)).contMDiff).contMDiffAt ?_
      filter_upwards [((isClosed_Icc.prod isClosed_Icc).isOpen_compl.preimage
        continuous_fst).mem_nhds fun h ↦ hp (hKU h)] with q hq
      simp [Φ, show q.1 ∉ K from hq]
  refine ⟨Φ, hΦ, fun z ↦ ?_, fun c z hz ↦ ?_,
    ⟨hΦ.comp (contDiff_id.prodMk contDiff_const).contMDiff, d / 2, by positivity, fun z hz ↦ ?_⟩⟩
  · by_cases h : z ∈ K
    · simp [Φ, h]
    · simp [Φ, h, hg₀, hvK z h]
  · have h : Icc (d / 2) (1 - d / 2) ⊆ Ioo 0 1 := Icc_subset_Ioo (by linarith) (by linarith)
    obtain ⟨hzK, hβz⟩ := hout fun hm ↦ hz (prod_mono h h hm)
    simp [Φ, hzK, hβz]
  · obtain ⟨hzK, hβz⟩ := hout hz
    simp [Φ, hzK, hβz]

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
  [T2Space M] {φ : RoughForm I M F 2}

/-- **Base-point change.** The integral of a closed `C¹` two-form over a class of `π₂(M, x)` is
unchanged by transporting the class along a path from `x` to `y`. In particular the integral is
invariant under the action of the fundamental group on `π₂(M, x)`. -/
theorem sphereIntegral_homotopyGroupTransport (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    {y : M} (γ : Path x y) (a : π_ 2 M x) :
    sphereIntegral φ y (homotopyGroupTransport γ a) = sphereIntegral φ x a := by
  obtain ⟨γ', hγ, hg⟩ := γ.exists_homotopic_contMDiff_extend (J := I) ⊤
  obtain ⟨v, hv, rfl⟩ := exists_isSmoothSphere (I := I) a
  obtain ⟨Φ, hΦ, hΦ₀, hΦb, hw⟩ := hv.exists_homotopy hg γ'.extend_zero
  rw [γ'.extend_one] at hw
  -- On the boundary of the square the homotopy traces `γ'`, so it ends at the transported class.
  let H : GenLoop.HomotopyAlong γ' hv.genLoop hw.genLoop :=
    { toFun := fun p ↦ Φ (cubeToPlane p.2, p.1)
      continuous_toFun := hΦ.continuous.comp (by fun_prop)
      map_zero_left := fun z ↦ by simpa [cubeToPlane_apply] using hΦ₀ (cubeToPlane z)
      map_one_left := fun z ↦ by simp [cubeToPlane_apply, IsSmoothSphere.genLoop_apply]
      map_boundary := fun t z hz ↦
        (hΦb t _ (by simpa using cubeToPlane_notMem le_rfl hz)).trans (γ'.extend_extends' t) }
  have hside {c : ℝ} {z : ℝ × ℝ} (hz : z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1) :
      Φ (z, c) = γ'.extend c :=
    hΦb c z fun hm ↦ by rcases hz with hz | hz | hz | hz <;> simp [hz] at hm
  have hrect := rectangleIntegral_eq_of_homotopy hφ hdφ (hΦ.of_le (by simp))
    (a := (0, 0)) (b := (1, 1))
    (Or.inr fun t _ c _ ↦ (hside (Or.inl rfl)).trans (hside (Or.inl rfl)).symm)
    (Or.inr fun t _ c _ ↦ (hside (Or.inr (Or.inl rfl))).trans (hside (Or.inr (Or.inl rfl))).symm)
    (fun s _ c _ ↦ (hside (Or.inr (Or.inr (Or.inr rfl)))).trans
      (hside (Or.inr (Or.inr (Or.inl rfl)))).symm)
  rw [homotopyGroupTransport_congr hγ, homotopyGroupTransport_mk,
    ← Quotient.sound H.homotopic_transport, sphereIntegral_mk hφ hdφ hw, hrect,
    sphereIntegral_mk hφ hdφ hv]
  exact rectangleIntegral_congr fun z _ ↦ hΦ₀ z

/-- The integral of a closed `C¹` two-form over a class of `π₂(M, x)` is invariant under the action
of the fundamental group at `x`. -/
theorem sphereIntegral_fundamentalGroup_smul (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0)
    (g : FundamentalGroup M x) (a : π_ 2 M x) :
    sphereIntegral φ x (g • a) = sphereIntegral φ x a := by
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g.toPath
  rw [fundamentalGroup_smul_eq_transport hp.symm, sphereIntegral_homotopyGroupTransport hφ hdφ]

end Transport

end TauCeti
