/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The inverse function theorem for manifolds

Mathlib knows that a `C^n` local diffeomorphism has invertible differentials
(`IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`) and lists the converse as a TODO in
`Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`. This file proves that converse for boundaryless
Banach manifolds: a map which is `C^n` on an open set, with `1 ≤ n`, and whose `mfderiv` at a point
of that set is a continuous linear equivalence, is a `C^n` local diffeomorphism at that point.

The proof reads `f` in the extended charts at `x` and at `f x`, restricts their targets to their
interiors, applies the normed-space inverse function theorem of
`TauCeti.ContDiffOn.exists_openPartialHomeomorph`, and conjugates the resulting
`OpenPartialHomeomorph` back by the restricted charts. On a boundaryless manifold every point lies
in these restrictions, even when the ambient models themselves have boundary.

## Main results

* `TauCeti.extChartPartialDiffeomorph`: an extended chart of a boundaryless manifold, as a partial
  diffeomorphism onto its open image in the model space.
* `TauCeti.PartialDiffeomorph.ofOpenPartialHomeomorph`: an open partial homeomorphism between
  model spaces which is `C^n` in both directions, as a partial diffeomorphism.
* `TauCeti.isLocalDiffeomorphAt_of_mfderiv_eq`: the inverse function theorem for manifolds.
* `TauCeti.isLocalDiffeomorphAt_iff_exists_mfderiv_eq`: the resulting characterisation of
  `IsLocalDiffeomorphAt` for a map which is `C^n` on an open set.
* `TauCeti.isLocalDiffeomorphAt_of_eqOn`: a map agreeing with a partial diffeomorphism on its
  source is a local diffeomorphism there.
* `TauCeti.isLocalDiffeomorph_of_mfderiv_eq`: the global version.

## References

* [The Hopf--Rinow roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/HopfRinow/README.md),
  Layer 1, "The manifold inverse-function theorem".
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti

variable {𝕂 : Type*} [RCLike 𝕂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

section Charts

variable (I : ModelWithCorners 𝕂 E H) [I.Boundaryless] (n : WithTop ℕ∞) [IsManifold I n M]

/-- The extended chart at `x`, as a partial diffeomorphism from `M` to the model space `E`. Its
target is open because `I` is boundaryless. -/
def extChartPartialDiffeomorph (x : M) : PartialDiffeomorph I 𝓘(𝕂, E) M E n where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (n := n) (x := x)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm x

@[simp]
theorem extChartPartialDiffeomorph_toPartialEquiv (x : M) :
    (extChartPartialDiffeomorph I n x).toPartialEquiv = extChartAt I x := (rfl)

theorem coe_extChartPartialDiffeomorph (x : M) :
    ⇑(extChartPartialDiffeomorph I n x) = extChartAt I x := (rfl)

end Charts

/-- An open partial homeomorphism between model spaces which is `C^n` in both directions is a
partial diffeomorphism. -/
def PartialDiffeomorph.ofOpenPartialHomeomorph {n : WithTop ℕ∞} (Θ : OpenPartialHomeomorph E F)
    (hΘ : ContDiffOn 𝕂 n Θ Θ.source) (hΘsymm : ContDiffOn 𝕂 n Θ.symm Θ.target) :
    PartialDiffeomorph 𝓘(𝕂, E) 𝓘(𝕂, F) E F n where
  toPartialEquiv := Θ.toPartialEquiv
  open_source := Θ.open_source
  open_target := Θ.open_target
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 hΘ
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 hΘsymm

@[simp]
theorem PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv {n : WithTop ℕ∞}
    (Θ : OpenPartialHomeomorph E F) (hΘ : ContDiffOn 𝕂 n Θ Θ.source)
    (hΘsymm : ContDiffOn 𝕂 n Θ.symm Θ.target) :
    (PartialDiffeomorph.ofOpenPartialHomeomorph Θ hΘ hΘsymm).toPartialEquiv =
      Θ.toPartialEquiv := (rfl)

section EqOn

variable {I : ModelWithCorners 𝕂 E H} {J : ModelWithCorners 𝕂 F G} {n : WithTop ℕ∞}

/-- A map agreeing with a partial diffeomorphism on its source is a `C^n` local diffeomorphism at
every point of that source. -/
theorem isLocalDiffeomorphAt_of_eqOn {Φ : PartialDiffeomorph I J M N n} {f : M → N} {x : M}
    (hx : x ∈ Φ.source) (hf : EqOn f Φ Φ.source) : IsLocalDiffeomorphAt I J n f x :=
  PartialDiffeomorph.isLocalDiffeomorphAt I J n
    ({ toPartialEquiv :=
        { toFun := f
          invFun := Φ.toPartialEquiv.symm
          source := Φ.source
          target := Φ.target
          map_source' := fun _ hy => hf hy ▸ Φ.toPartialEquiv.map_source hy
          map_target' := fun _ hw => Φ.toPartialEquiv.map_target hw
          left_inv' := fun _ hy => hf hy ▸ Φ.toPartialEquiv.left_inv hy
          right_inv' := fun _ hw =>
            (hf (Φ.toPartialEquiv.map_target hw)).trans (Φ.toPartialEquiv.right_inv hw) }
       open_source := Φ.open_source
       open_target := Φ.open_target
       contMDiffOn_toFun := Φ.contMDiffOn_toFun.congr fun _ hy => hf hy
       contMDiffOn_invFun := Φ.contMDiffOn_invFun } : PartialDiffeomorph I J M N n) hx

end EqOn

section InverseFunctionTheorem

variable [CompleteSpace E] {I : ModelWithCorners 𝕂 E H}
  {J : ModelWithCorners 𝕂 F G} {n : WithTop ℕ∞}
  [IsManifold I n M] [IsManifold J n N] {f : M → N} {s : Set M} {x : M}
  [BoundarylessManifold I M] [BoundarylessManifold J N]

private def extChartInteriorPartialDiffeomorph
    (I : ModelWithCorners 𝕂 E H) (n : WithTop ℕ∞) [IsManifold I n M] (x : M) :
    PartialDiffeomorph I 𝓘(𝕂, E) M E n := by
  let chart := extChartAt I x
  let V := interior chart.target
  let ce : PartialEquiv M E := {
    toFun := chart
    invFun := chart.symm
    source := chart.source ∩ chart ⁻¹' V
    target := V
    map_source' := fun _ hy => hy.2
    map_target' := by
      intro y hy
      refine ⟨chart.map_target (interior_subset hy), ?_⟩
      -- The restricted target condition reduces to the chart inverse law on the interior.
      change chart (chart.symm y) ∈ V
      rw [chart.right_inv (interior_subset hy)]
      exact hy
    left_inv' := fun _ hy => chart.left_inv hy.1
    right_inv' := fun _ hy => chart.right_inv (interior_subset hy) }
  exact {
    toPartialEquiv := ce
    open_source :=
      (continuousOn_extChartAt (I := I) x).isOpen_inter_preimage
        (isOpen_extChartAt_source (I := I) x) isOpen_interior
    open_target := isOpen_interior
    contMDiffOn_toFun := by
      apply (contMDiffOn_extChartAt (I := I) (n := n) (x := x)).mono
      intro y hy
      -- Forget the extra target-interior restriction to use smoothness of the full chart.
      change y ∈ chart.source ∩ chart ⁻¹' V at hy
      simpa only [chart, extChartAt_source] using hy.1
    contMDiffOn_invFun :=
      (contMDiffOn_extChartAt_symm (I := I) x).mono interior_subset }

/-- **The inverse function theorem for manifolds.** If `f` is `C^n` on an open set `s` with
`1 ≤ n`, and its differential at `x ∈ s` is a continuous linear equivalence, then `f` is a `C^n`
local diffeomorphism at `x`.

Mathlib's `Mathlib/Geometry/Manifold/LocalDiffeomorph.lean` lists this implication as a TODO. -/
theorem isLocalDiffeomorphAt_of_mfderiv_eq (hf : ContMDiffOn I J n f s) (hs : IsOpen s)
    (hx : x ∈ s) (hn : 1 ≤ n) {e : TangentSpace I x ≃L[𝕂] TangentSpace J (f x)}
    (he : (e : TangentSpace I x →L[𝕂] TangentSpace J (f x)) = mfderiv I J f x) :
    IsLocalDiffeomorphAt I J n f x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  set φ := extChartAt I x with hφ
  set ψ := extChartAt J (f x) with hψ
  set g : E → F := ψ ∘ f ∘ φ.symm with hg
  set t : Set E := interior φ.target ∩ φ.symm ⁻¹' (s ∩ f ⁻¹' ψ.source) with ht
  -- The set on which the chart representative of `f` is known to be `C^n` is open.
  have hu : IsOpen (s ∩ f ⁻¹' ψ.source) :=
    hf.continuousOn.isOpen_inter_preimage hs (isOpen_extChartAt_source (f x))
  have htopen : IsOpen t :=
    ((continuousOn_extChartAt_symm x).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hu
  have hxt : φ x ∈ t := by
    refine ⟨?_, ?_⟩
    · simpa only [hφ] using
        (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
          (BoundarylessManifold.isInteriorPoint : I.IsInteriorPoint x)
    simp only [hφ, hψ, mem_preimage, extChartAt_to_inv]
    exact ⟨hx, mem_extChartAt_source (f x)⟩
  -- `g` on `t` is exactly the chart representative of `f` appearing in `contMDiffOn_iff`.
  have hgt : ContDiffOn 𝕂 n g t := by
    have hfull := (contMDiffOn_iff.1 hf).2 x (f x)
    apply (show ContDiffOn 𝕂 n g
      (φ.target ∩ φ.symm ⁻¹' (s ∩ f ⁻¹' ψ.source)) by
        simpa only [hg, hφ, hψ] using hfull).mono
    intro y hy
    rw [ht] at hy
    exact ⟨interior_subset hy.1, hy.2⟩
  -- Its derivative at `φ x` is the given equivalence: `g` is `f` written in the extended charts,
  -- and `TangentSpace I x` and `TangentSpace J (f x)` are the model spaces `E` and `F`.
  have hmdiff : MDifferentiableAt I J f x := (hf.contMDiffAt (hs.mem_nhds hx)).mdifferentiableAt hn0
  have hwritten : fderiv 𝕂 (writtenInExtChartAt I J x f) (φ x) = fderiv 𝕂 g (φ x) := by
    simp only [hg, hφ, hψ, writtenInExtChartAt]
  have hfd : (e : TangentSpace I x →L[𝕂] TangentSpace J (f x)) = fderiv 𝕂 g (φ x) := by
    rw [he, hmdiff.mfderiv]
    rw [fderivWithin_of_mem_nhds]
    · exact hwritten
    · simpa only [hφ] using
        (mem_interior_iff_mem_nhds.mp
          (show extChartAt I x x ∈ interior (range I) from
            BoundarylessManifold.isInteriorPoint))
  obtain ⟨Θ, hΘcoe, hΘmem, hΘsub, hΘsymm⟩ :=
    ContDiffOn.exists_openPartialHomeomorph hgt htopen hxt hn hfd
  have hΘsmooth : ContDiffOn 𝕂 n Θ Θ.source := hΘcoe ▸ hgt.mono hΘsub
  set Ψ : PartialDiffeomorph 𝓘(𝕂, E) J E N n :=
    (PartialDiffeomorph.ofOpenPartialHomeomorph Θ hΘsmooth hΘsymm).trans
      (extChartInteriorPartialDiffeomorph J n (f x)).symm with hΨ
  set Φ : PartialDiffeomorph I J M N n :=
    (extChartInteriorPartialDiffeomorph I n x).trans Ψ with hΦ
  -- The source of each composite comes from `OpenPartialHomeomorph.trans_source`.
  have hΨsource : Ψ.source = Θ.source ∩ Θ ⁻¹' interior ψ.target := by
    rw [hΨ, PartialDiffeomorph.trans_toPartialEquiv]
    exact OpenPartialHomeomorph.trans_source _ _
  have hsource : Φ.source =
      (φ.source ∩ φ ⁻¹' interior φ.target) ∩
        φ ⁻¹' (Θ.source ∩ Θ ⁻¹' interior ψ.target) := by
    rw [hΦ, PartialDiffeomorph.trans_toPartialEquiv, ← hΨsource]
    exact OpenPartialHomeomorph.trans_source _ _
  -- By construction the composite acts as `ψ.symm ∘ Θ ∘ φ`.
  have hcoe : ∀ y, Φ y = ψ.symm (Θ (φ y)) := fun _ => rfl
  have hinvx : φ.symm (φ x) = x := by rw [hφ]; exact extChartAt_to_inv x
  have hgx : Θ (φ x) = ψ (f x) := by rw [hΘcoe]; simp only [hg, Function.comp_apply, hinvx]
  have hxφ : φ x ∈ interior φ.target := by
    simpa only [hφ] using
      (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
        (BoundarylessManifold.isInteriorPoint : I.IsInteriorPoint x)
  have hxψ : ψ (f x) ∈ interior ψ.target := by
    simpa only [hψ] using
      (ModelWithCorners.isInteriorPoint_iff (I := J)).mp
        (BoundarylessManifold.isInteriorPoint : J.IsInteriorPoint (f x))
  have hxΦ : x ∈ Φ.source := by
    rw [hsource]
    refine ⟨⟨mem_extChartAt_source x, hxφ⟩, hΘmem, ?_⟩
    change Θ (φ x) ∈ interior ψ.target
    rw [hgx]
    exact hxψ
  refine isLocalDiffeomorphAt_of_eqOn hxΦ fun y hy => ?_
  rw [hsource] at hy
  obtain ⟨⟨hy₁, -⟩, hy₂, -⟩ := hy
  have hyinv : φ.symm (φ y) = y := φ.left_inv hy₁
  have hyN : f y ∈ ψ.source := by
    have := (hΘsub hy₂).2.2
    rwa [hyinv] at this
  have hgy : Θ (φ y) = ψ (f y) := by rw [hΘcoe]; simp only [hg, Function.comp_apply, hyinv]
  rw [hcoe y, hgy, ψ.left_inv hyN]

/-- For a map which is `C^n` on an open set, with `1 ≤ n`, being a `C^n` local diffeomorphism at a
point of that set is exactly invertibility of the differential there. -/
theorem isLocalDiffeomorphAt_iff_exists_mfderiv_eq (hf : ContMDiffOn I J n f s) (hs : IsOpen s)
    (hx : x ∈ s) (hn : 1 ≤ n) :
    IsLocalDiffeomorphAt I J n f x ↔
      ∃ e : TangentSpace I x ≃L[𝕂] TangentSpace J (f x),
        (e : TangentSpace I x →L[𝕂] TangentSpace J (f x)) = mfderiv I J f x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  refine ⟨fun h => ⟨h.mfderivToContinuousLinearEquiv hn0, rfl⟩, ?_⟩
  rintro ⟨e, he⟩
  exact isLocalDiffeomorphAt_of_mfderiv_eq hf hs hx hn he

/-- **The inverse function theorem for manifolds**, global form: a `C^n` map (`1 ≤ n`) all of whose
differentials are continuous linear equivalences is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_of_mfderiv_eq (hf : ContMDiff I J n f) (hn : 1 ≤ n)
    (he : ∀ y : M, ∃ e : TangentSpace I y ≃L[𝕂] TangentSpace J (f y),
      (e : TangentSpace I y →L[𝕂] TangentSpace J (f y)) = mfderiv I J f y) :
    IsLocalDiffeomorph I J n f := fun y => by
  obtain ⟨e, hey⟩ := he y
  exact isLocalDiffeomorphAt_of_mfderiv_eq (s := univ) hf.contMDiffOn isOpen_univ (mem_univ y) hn
    hey

end InverseFunctionTheorem

end TauCeti
