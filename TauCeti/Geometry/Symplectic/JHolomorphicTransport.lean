/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Transporting `J`-holomorphic maps along linear coordinate changes

This file records that the local `J`-holomorphic predicate is invariant under continuous
real-linear changes of source and target coordinates. If `f : V → W` is `J`-holomorphic and
`eV : V ≃L[ℝ] V'`, `eW : W ≃L[ℝ] W'`, then the transported map
`v' ↦ eW (f (eV.symm v'))` is `J`-holomorphic for the transported almost complex structures.

These are the chart-change lemmas needed before the analytic Heegaard Floer roadmap upgrades the
normed-vector-space Cauchy--Riemann equation to tangent charts on almost complex manifolds. The
almost complex structures themselves are transported by the linear-algebra API in
`TauCeti.Geometry.Symplectic.Transport`; this file adds the matching map-level calculus.

## Main declarations

* `TauCeti.IsJHolomorphicAt.transport`: pointwise transport of `J`-holomorphicity.
* `TauCeti.IsJHolomorphicWithinAt.transport`: within-set transport along a source coordinate
  change whose inverse maps the transported source set back into the original source set.
* `TauCeti.IsJHolomorphicOn.transport` and `TauCeti.IsJHolomorphic.transport`: setwise and
  global transport.
* `TauCeti.isJHolomorphicAt_transport_iff`,
  `TauCeti.isJHolomorphicWithinAt_transport_iff`, `TauCeti.isJHolomorphicOn_transport_iff`,
  and `TauCeti.isJHolomorphic_transport_iff`: transport equivalences, obtained by applying the
  forward statement in both directions.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: `J`-holomorphicity is the Cauchy--Riemann equation
`df ∘ J = J' ∘ df`, and coordinate changes conjugate both `J` and `df`.
-/

public section

namespace TauCeti

variable {V W V' W' : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup W'] [NormedSpace ℝ W']

section Transport

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}

/-- Transport a pointwise `J`-holomorphic map along continuous real-linear equivalences of the
source and target coordinates. -/
lemma IsJHolomorphicAt.transport {f : V → W} {x : V} (hf : IsJHolomorphicAt J J' f x)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) := by
  have hsource :
      IsJHolomorphicAt (J.transport eV.toLinearEquiv) J (fun y : V' => eV.symm y) (eV x) :=
    (isJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have htarget :
      IsJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have hmiddle : IsJHolomorphicAt J J' f (eV.symm (eV x)) := by
    simpa
  simpa [Function.comp_def] using
    IsJHolomorphicAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (x := eV x)
      htarget (hmiddle.comp hsource)

/-- Transport a within-set `J`-holomorphic map along continuous real-linear equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsJHolomorphicWithinAt.transport {f : V → W} {s : Set V} {x : V} {t : Set V'}
    (hf : IsJHolomorphicWithinAt J J' f s x) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsJHolomorphicWithinAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t (eV x) := by
  intro hts
  have hsourceAt :
      IsJHolomorphicAt (J.transport eV.toLinearEquiv) J (fun y : V' => eV.symm y) (eV x) :=
    (isJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have hsource :
      IsJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) t (eV x) :=
    hsourceAt.isJHolomorphicWithinAt
  have htargetAt :
      IsJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have htarget :
      IsJHolomorphicWithinAt J' (J'.transport eW.toLinearEquiv)
        (fun y : W => eW y) Set.univ (f (eV.symm (eV x))) :=
    htargetAt.isJHolomorphicWithinAt
  have hmiddle : IsJHolomorphicWithinAt J J' f s (eV.symm (eV x)) := by
    simpa
  have hinner : IsJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J'
      (fun y : V' => f (eV.symm y)) t (eV x) := by
    simpa [Function.comp_def] using hmiddle.comp hsource hts
  simpa [Function.comp_def] using
    IsJHolomorphicWithinAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (s := t)
      (t := Set.univ) (x := eV x) htarget hinner (fun _ _ => Set.mem_univ _)

/-- Transport a setwise `J`-holomorphic map along continuous real-linear equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsJHolomorphicOn.transport {f : V → W} {s : Set V} {t : Set V'}
    (hf : IsJHolomorphicOn J J' f s) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t := by
  intro hts y hy
  simpa [eV.apply_symm_apply y] using (hf (eV.symm y) (hts hy)).transport eV eW hts

/-- Transport a globally `J`-holomorphic map along continuous real-linear equivalences of the
source and target coordinates. -/
lemma IsJHolomorphic.transport {f : V → W} (hf : IsJHolomorphic J J' f)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) := by
  intro y
  simpa [eV.apply_symm_apply y] using (hf (eV.symm y)).transport eV eW

/-- Pointwise `J`-holomorphicity is invariant under continuous real-linear coordinate changes. -/
@[simp]
lemma isJHolomorphicAt_transport_iff (f : V → W) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) ↔ IsJHolomorphicAt J J' f x := by
  refine ⟨fun h => ?_, fun h => h.transport eV eW⟩
  have hback := h.transport eV.symm eW.symm
  simpa [AlmostComplexStructure.transport_symm_transport, eV.symm_apply_apply,
    eW.symm_apply_apply] using hback

/-- Within-set `J`-holomorphicity is invariant under continuous real-linear coordinate
changes, with the source set sent to its image. -/
@[simp]
lemma isJHolomorphicWithinAt_transport_iff (f : V → W) (s : Set V) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphicWithinAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) (eV x) ↔
        IsJHolomorphicWithinAt J J' f s x := by
  refine ⟨fun h => ?_, fun h => h.transport eV eW ?_⟩
  · have hmaps : Set.MapsTo (fun y : V => eV.symm.symm y) s (eV '' s) := by
      intro y hy
      refine ⟨y, hy, ?_⟩
      simp
    have hback := h.transport eV.symm eW.symm (t := s) hmaps
    simpa [AlmostComplexStructure.transport_symm_transport, eV.symm_apply_apply,
      eW.symm_apply_apply] using hback
  · rintro y ⟨z, hz, rfl⟩
    simpa using hz

/-- Setwise `J`-holomorphicity is invariant under continuous real-linear coordinate changes,
with the source set sent to its image. -/
@[simp]
lemma isJHolomorphicOn_transport_iff (f : V → W) (s : Set V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) ↔ IsJHolomorphicOn J J' f s := by
  refine ⟨fun h x hx => ?_, fun h => h.transport eV eW ?_⟩
  · exact (isJHolomorphicWithinAt_transport_iff f s x eV eW).mp (h (eV x) ⟨x, hx, rfl⟩)
  · rintro y ⟨z, hz, rfl⟩
    simpa using hz

/-- Global `J`-holomorphicity is invariant under continuous real-linear coordinate changes. -/
@[simp]
lemma isJHolomorphic_transport_iff (f : V → W)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) ↔ IsJHolomorphic J J' f := by
  refine ⟨fun h x => ?_, fun h => h.transport eV eW⟩
  exact (isJHolomorphicAt_transport_iff f x eV eW).mp (h (eV x))

end Transport

end TauCeti
