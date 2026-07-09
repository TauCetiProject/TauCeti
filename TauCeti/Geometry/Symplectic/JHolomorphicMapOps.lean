/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Operations preserving constant-structure `J`-holomorphic maps

This file collects the elementary map-level operations under which the normed-vector-space
constant-structure `J`-holomorphic predicates are invariant, used by the analytic Heegaard Floer
roadmap. All three groups of lemmas share the same mechanism: the analytic content lives in the
Frechet derivative, and the operation acts only through linear algebra on that derivative.

* **Negation.** A real-linear map satisfies `F ∘ J = J' ∘ F` exactly when it satisfies the same
  equation after both almost complex structures are negated, `F ∘ (-J) = (-J') ∘ F`, so the
  predicate is unchanged when both structures change sign.
* **Congruence.** A constant-structure `J`-holomorphic condition depends only on a local
  representative of the map near the point or within the source set, because the underlying
  Frechet derivative has the same locality property.
* **Transport.** The predicate is invariant under continuous real-linear changes of source and
  target coordinates: if `f : V → W` is constant-structure `J`-holomorphic and `eV : V ≃L[ℝ] V'`,
  `eW : W ≃L[ℝ] W'`, then `v' ↦ eW (f (eV.symm v'))` is constant-structure `J`-holomorphic for the
  transported almost complex structures. The structures are transported by the linear-algebra API
  in `TauCeti.Geometry.Symplectic.Transport`; this file adds the matching map-level calculus.

These lemmas are the chart-level bookkeeping needed before the roadmap upgrades the local
Cauchy--Riemann equation to almost complex manifolds, where maps are constantly replaced by equal
local representatives in overlapping charts, restricted domains are reflected or reoriented, and
tangent charts change coordinates.

## Main declarations

* `TauCeti.IsConstStructureJHolomorphicAt.neg_neg` and its within-set, setwise, and global
  analogues, with the rewrite-friendly `TauCeti.isConstStructureJHolomorphicAt_neg_neg_iff` family:
  invariance under negating both almost complex structures.
* `TauCeti.IsConstStructureJHolomorphicAt.congr_of_eventuallyEq`,
  `TauCeti.IsConstStructureJHolomorphicWithinAt.congr_mono`,
  `TauCeti.isConstStructureJHolomorphicWithinAt_congr_set_nhdsNE`,
  `TauCeti.IsConstStructureJHolomorphicOn.congr`, and their equivalence forms: the locality API.
* `TauCeti.IsConstStructureJHolomorphicAt.transport` and its within-set, setwise, and global
  analogues, with the `TauCeti.isConstStructureJHolomorphicAt_transport_iff` family: invariance
  under continuous real-linear coordinate changes.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: constant-structure `J`-holomorphicity is the Cauchy--Riemann equation
`df ∘ J = J' ∘ df`, and coordinate changes conjugate both `J` and `df`. The congruence proofs are
thin wrappers around Mathlib's Frechet-derivative congruence lemmas in
`Mathlib.Analysis.Calculus.FDeriv.Congr`.
-/

public section

namespace TauCeti

open Filter
open scoped Topology

variable {V W : Type*}

section Neg

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f : V → W} {s : Set V} {x : V}

namespace IsConstStructureJHolomorphicAt

/-- Pointwise constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicAt J J' f x) :
    IsConstStructureJHolomorphicAt (-J) (-J') f x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt hf.hasFDerivAt
    hf.derivative_isComplexLinear.neg_neg

end IsConstStructureJHolomorphicAt

/-- Negating both almost complex structures leaves pointwise constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicAt_neg_neg_iff :
    IsConstStructureJHolomorphicAt (-J) (-J') f x ↔ IsConstStructureJHolomorphicAt J J' f x :=
  ⟨fun hf => isConstStructureJHolomorphicAt_of_hasFDerivAt hf.hasFDerivAt
      hf.derivative_isComplexLinear.of_neg_neg,
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphicWithinAt

/-- Within-set constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) :
    IsConstStructureJHolomorphicWithinAt (-J) (-J') f s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt hf.hasFDerivWithinAt
    hf.derivative_isComplexLinear.neg_neg

end IsConstStructureJHolomorphicWithinAt

/-- Negating both almost complex structures leaves within-set constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_neg_neg_iff :
    IsConstStructureJHolomorphicWithinAt (-J) (-J') f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f s x :=
  ⟨fun hf => isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt hf.hasFDerivWithinAt
      hf.derivative_isComplexLinear.of_neg_neg,
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphicOn

/-- Setwise constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg (hf : IsConstStructureJHolomorphicOn J J' f s) :
    IsConstStructureJHolomorphicOn (-J) (-J') f s :=
  isConstStructureJHolomorphicOn_of_forall fun _ hx =>
    (hf.isConstStructureJHolomorphicWithinAt hx).neg_neg

end IsConstStructureJHolomorphicOn

/-- Negating both almost complex structures leaves setwise constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphicOn_neg_neg_iff :
    IsConstStructureJHolomorphicOn (-J) (-J') f s ↔ IsConstStructureJHolomorphicOn J J' f s :=
  ⟨fun hf => isConstStructureJHolomorphicOn_of_forall fun _ hx =>
      (isConstStructureJHolomorphicWithinAt_neg_neg_iff).mp
        (hf.isConstStructureJHolomorphicWithinAt hx),
    fun hf => hf.neg_neg⟩

namespace IsConstStructureJHolomorphic

/-- Global constant-structure `J`-holomorphicity is unchanged after negating both almost complex
structures. -/
lemma neg_neg
    (hf : IsConstStructureJHolomorphic J J' f) : IsConstStructureJHolomorphic (-J) (-J') f :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).neg_neg

end IsConstStructureJHolomorphic

/-- Negating both almost complex structures leaves global constant-structure `J`-holomorphicity
unchanged. -/
@[simp]
lemma isConstStructureJHolomorphic_neg_neg_iff :
    IsConstStructureJHolomorphic (-J) (-J') f ↔ IsConstStructureJHolomorphic J J' f :=
  ⟨fun hf => isConstStructureJHolomorphic_of_forall fun x =>
      (isConstStructureJHolomorphicAt_neg_neg_iff).mp (hf.isConstStructureJHolomorphicAt x),
    fun hf => hf.neg_neg⟩

end Neg

section Congruence

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}
variable {f g : V → W} {s t : Set V} {x : V}

/-- Pointwise constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in a
neighborhood of the point. -/
lemma IsConstStructureJHolomorphicAt.congr_of_eventuallyEq
    (hf : IsConstStructureJHolomorphicAt J J' f x)
    (hfg : g =ᶠ[𝓝 x] f) : IsConstStructureJHolomorphicAt J J' g x :=
  isConstStructureJHolomorphicAt_of_hasFDerivAt
    (hf.hasFDerivAt.congr_of_eventuallyEq hfg) hf.derivative_isComplexLinear

/-- Pointwise constant-structure `J`-holomorphicity is unchanged under local equality near the
point. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicAt_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsConstStructureJHolomorphicAt J J' f x ↔ IsConstStructureJHolomorphicAt J J' g x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm,
    fun hg => hg.congr_of_eventuallyEq hfg⟩

/-- A pointwise constant-structure `J`-holomorphic map may be replaced by a map equal to it
everywhere. -/
lemma IsConstStructureJHolomorphicAt.congr (hf : IsConstStructureJHolomorphicAt J J' f x)
    (hfg : ∀ y, g y = f y) : IsConstStructureJHolomorphicAt J J' g x :=
  hf.congr_of_eventuallyEq (Filter.Eventually.of_forall hfg)

/-- Pointwise constant-structure `J`-holomorphicity is invariant under pointwise equality of
maps. -/
lemma isConstStructureJHolomorphicAt_congr (hfg : ∀ y, f y = g y) :
    IsConstStructureJHolomorphicAt J J' f x ↔ IsConstStructureJHolomorphicAt J J' g x :=
  (Filter.EventuallyEq.isConstStructureJHolomorphicAt_iff (Filter.Eventually.of_forall hfg))

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in the
source-set neighborhood filter, provided the values also agree at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_of_eventuallyEq
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f)
    (hx : g x = f x) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.congr_of_eventuallyEq hfg hx)
    hf.derivative_isComplexLinear

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal
to it in the
source-set neighborhood filter, when the base point belongs to the source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_of_eventuallyEq_of_mem
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (hfg : g =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set constant-structure `J`-holomorphicity is unchanged under local equality in the
source-set
neighborhood filter, provided the values agree at the base point. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : f x = g x) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' g s x :=
  ⟨fun hf => hf.congr_of_eventuallyEq hfg.symm hx.symm,
    fun hg => hg.congr_of_eventuallyEq hfg hx⟩

/-- Within-set constant-structure `J`-holomorphicity is unchanged under local equality in the
source-set
neighborhood filter, when the base point belongs to the source set. -/
lemma Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff_of_mem (hfg : f =ᶠ[𝓝[s] x] g)
    (hx : x ∈ s) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' g s x :=
  Filter.EventuallyEq.isConstStructureJHolomorphicWithinAt_iff hfg (hfg.eq_of_nhdsWithin hx)

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by an equal
map on the
source set and at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : g x = f x) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr_of_eventuallyEq hfg.eventuallyEq_nhdsWithin hx

/-- Within-set constant-structure `J`-holomorphicity is unchanged after replacing a map by an equal
map on the
source set, when the base point belongs to the source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr'
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f s) (hx : x ∈ s) : IsConstStructureJHolomorphicWithinAt J J' g s x :=
  hf.congr hfg (hfg hx)

/-- Restrict the source set and replace a within-set constant-structure `J`-holomorphic map by one
equal to it on
the smaller source set and at the base point. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_mono
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : g x = f x) (hts : t ⊆ s) :
    IsConstStructureJHolomorphicWithinAt J J' g t x :=
  isConstStructureJHolomorphicWithinAt_of_hasFDerivWithinAt
    (hf.hasFDerivWithinAt.congr_mono hfg hx hts) hf.derivative_isComplexLinear

/-- Restrict the source set and replace a within-set constant-structure `J`-holomorphic map by one
equal to it on
the smaller source set, when the base point belongs to that smaller source set. -/
lemma IsConstStructureJHolomorphicWithinAt.congr_mono'
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x)
    (hfg : Set.EqOn g f t) (hx : x ∈ t) (hts : t ⊆ s) :
    IsConstStructureJHolomorphicWithinAt J J' g t x :=
  hf.congr_mono hfg (hfg hx) hts

/-- Within-set constant-structure `J`-holomorphicity is invariant under changing the source set in a
punctured
neighborhood of the base point. -/
lemma isConstStructureJHolomorphicWithinAt_congr_set_nhdsNE (hst : s =ᶠ[𝓝[≠] x] t) :
    IsConstStructureJHolomorphicWithinAt J J' f s x ↔
      IsConstStructureJHolomorphicWithinAt J J' f t x := by
  constructor
  · intro hf
    rcases (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mp hf with
      ⟨f', hf', hlin⟩
    exact (isConstStructureJHolomorphicWithinAt_iff J J' f t x).mpr
      ⟨f', (hasFDerivWithinAt_congr_set_nhdsNE hst).mp hf', hlin⟩
  · intro hf
    rcases (isConstStructureJHolomorphicWithinAt_iff J J' f t x).mp hf with
      ⟨f', hf', hlin⟩
    exact (isConstStructureJHolomorphicWithinAt_iff J J' f s x).mpr
      ⟨f', (hasFDerivWithinAt_congr_set_nhdsNE hst).mpr hf', hlin⟩

/-- Setwise constant-structure `J`-holomorphicity on a smaller source set is unchanged after
replacing a map by
one equal to it on that smaller source set. -/
lemma IsConstStructureJHolomorphicOn.congr_mono (hf : IsConstStructureJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f t) (hts : t ⊆ s) : IsConstStructureJHolomorphicOn J J' g t :=
  isConstStructureJHolomorphicOn_of_forall fun x hx =>
    have hxgf : g x = f x := hfg hx
    (hf.isConstStructureJHolomorphicWithinAt (hts hx)).congr_mono hfg hxgf hts

/-- Setwise constant-structure `J`-holomorphicity is unchanged after replacing a map by one equal to
it on the
source set. -/
lemma IsConstStructureJHolomorphicOn.congr (hf : IsConstStructureJHolomorphicOn J J' f s)
    (hfg : Set.EqOn g f s) : IsConstStructureJHolomorphicOn J J' g s :=
  hf.congr_mono hfg (fun _ hx => hx)

/-- Setwise constant-structure `J`-holomorphicity is invariant under equality of maps on the source
set. -/
lemma isConstStructureJHolomorphicOn_congr (hfg : Set.EqOn f g s) :
    IsConstStructureJHolomorphicOn J J' f s ↔ IsConstStructureJHolomorphicOn J J' g s :=
  ⟨fun hf => hf.congr fun _ hx => (hfg hx).symm,
    fun hg => hg.congr hfg⟩

/-- A globally constant-structure `J`-holomorphic map may be replaced by a pointwise equal map. -/
lemma IsConstStructureJHolomorphic.congr
    (hf : IsConstStructureJHolomorphic J J' f)
    (hfg : ∀ x, g x = f x) :
    IsConstStructureJHolomorphic J J' g :=
  isConstStructureJHolomorphic_of_forall fun x =>
    (hf.isConstStructureJHolomorphicAt x).congr hfg

/-- Global constant-structure `J`-holomorphicity is invariant under pointwise equality of maps. -/
lemma isConstStructureJHolomorphic_congr (hfg : ∀ x, f x = g x) :
    IsConstStructureJHolomorphic J J' f ↔ IsConstStructureJHolomorphic J J' g :=
  ⟨fun hf => hf.congr fun x => (hfg x).symm,
    fun hg => hg.congr hfg⟩

end Congruence

section Transport

variable {V' W' : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup V'] [NormedSpace ℝ V']
variable [NormedAddCommGroup W'] [NormedSpace ℝ W']

variable {J : AlmostComplexStructure V} {J' : AlmostComplexStructure W}

/-- Transport a pointwise constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates. -/
lemma IsConstStructureJHolomorphicAt.transport {f : V → W} {x : V}
    (hf : IsConstStructureJHolomorphicAt J J' f x)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) := by
  have hsource :
      IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) (eV x) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap
      (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have htarget :
      IsConstStructureJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have hmiddle : IsConstStructureJHolomorphicAt J J' f (eV.symm (eV x)) := by
    simpa
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (x := eV x)
      htarget (hmiddle.comp hsource)

/-- Transport a within-set constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsConstStructureJHolomorphicWithinAt.transport {f : V → W} {s : Set V} {x : V} {t : Set V'}
    (hf : IsConstStructureJHolomorphicWithinAt J J' f s x) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv)
      (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t (eV x) := by
  intro hts
  have hsourceAt :
      IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) (eV x) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eV.symm.toContinuousLinearMap
      (eV x)).mpr
      (AlmostComplexStructure.isComplexLinearMap_symm_transport J eV.toLinearEquiv)
  have hsource :
      IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J
        (fun y : V' => eV.symm y) t (eV x) :=
    hsourceAt.isConstStructureJHolomorphicWithinAt
  have htargetAt :
      IsConstStructureJHolomorphicAt J' (J'.transport eW.toLinearEquiv) (fun y : W => eW y)
        (f (eV.symm (eV x))) :=
    (isConstStructureJHolomorphicAt_continuousLinearMap_iff eW.toContinuousLinearMap
      (f (eV.symm (eV x)))).mpr
      (AlmostComplexStructure.isComplexLinearMap_transport J' eW.toLinearEquiv)
  have htarget :
      IsConstStructureJHolomorphicWithinAt J' (J'.transport eW.toLinearEquiv)
        (fun y : W => eW y) Set.univ (f (eV.symm (eV x))) :=
    htargetAt.isConstStructureJHolomorphicWithinAt
  have hmiddle : IsConstStructureJHolomorphicWithinAt J J' f s (eV.symm (eV x)) := by
    simpa
  have hinner : IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv) J'
      (fun y : V' => f (eV.symm y)) t (eV x) := by
    simpa [Function.comp_def] using hmiddle.comp hsource hts
  simpa [Function.comp_def] using
    IsConstStructureJHolomorphicWithinAt.comp
      (J := J.transport eV.toLinearEquiv) (J' := J') (J'' := J'.transport eW.toLinearEquiv)
      (f := fun y : V' => f (eV.symm y)) (g := fun y : W => eW y) (s := t)
      (t := Set.univ) (x := eV x) htarget hinner (fun _ _ => Set.mem_univ _)

/-- Transport a setwise constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates, for any target-domain set whose points map back into the
original source set. -/
lemma IsConstStructureJHolomorphicOn.transport {f : V → W} {s : Set V} {t : Set V'}
    (hf : IsConstStructureJHolomorphicOn J J' f s) (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    Set.MapsTo (fun y : V' => eV.symm y) t s →
    IsConstStructureJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) t := by
  intro hts
  exact isConstStructureJHolomorphicOn_of_forall fun y hy => by
    simpa [eV.apply_symm_apply y] using
      (hf.isConstStructureJHolomorphicWithinAt (hts hy)).transport eV eW hts

/-- Transport a globally constant-structure `J`-holomorphic map along continuous real-linear
equivalences of the
source and target coordinates. -/
lemma IsConstStructureJHolomorphic.transport {f : V → W} (hf : IsConstStructureJHolomorphic J J' f)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) := by
  exact isConstStructureJHolomorphic_of_forall fun y => by
    simpa [eV.apply_symm_apply y] using
      (hf.isConstStructureJHolomorphicAt (eV.symm y)).transport eV eW

/-- Pointwise constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes. -/
@[simp]
lemma isConstStructureJHolomorphicAt_transport_iff (f : V → W) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicAt (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV x) ↔ IsConstStructureJHolomorphicAt J J' f x := by
  refine ⟨fun h => ?_, fun h => h.transport eV eW⟩
  have hback := h.transport eV.symm eW.symm
  simpa [AlmostComplexStructure.transport_symm_transport, eV.symm_apply_apply,
    eW.symm_apply_apply] using hback

/-- Within-set constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate
changes, with the source set sent to its image. -/
@[simp]
lemma isConstStructureJHolomorphicWithinAt_transport_iff (f : V → W) (s : Set V) (x : V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicWithinAt (J.transport eV.toLinearEquiv)
      (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) (eV x) ↔
        IsConstStructureJHolomorphicWithinAt J J' f s x := by
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

/-- Setwise constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes,
with the source set sent to its image. -/
@[simp]
lemma isConstStructureJHolomorphicOn_transport_iff (f : V → W) (s : Set V)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphicOn (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) (eV '' s) ↔ IsConstStructureJHolomorphicOn J J' f s := by
  refine ⟨fun h => isConstStructureJHolomorphicOn_of_forall fun x hx => ?_,
    fun h => h.transport eV eW ?_⟩
  · exact (isConstStructureJHolomorphicWithinAt_transport_iff f s x eV eW).mp
      (h.isConstStructureJHolomorphicWithinAt ⟨x, hx, rfl⟩)
  · rintro y ⟨z, hz, rfl⟩
    simpa using hz

/-- Global constant-structure `J`-holomorphicity is invariant under continuous real-linear
coordinate changes. -/
@[simp]
lemma isConstStructureJHolomorphic_transport_iff (f : V → W)
    (eV : V ≃L[ℝ] V') (eW : W ≃L[ℝ] W') :
    IsConstStructureJHolomorphic (J.transport eV.toLinearEquiv) (J'.transport eW.toLinearEquiv)
      (fun y : V' => eW (f (eV.symm y))) ↔ IsConstStructureJHolomorphic J J' f := by
  refine ⟨fun h => isConstStructureJHolomorphic_of_forall fun x => ?_,
    fun h => h.transport eV eW⟩
  exact (isConstStructureJHolomorphicAt_transport_iff f x eV eW).mp
    (h.isConstStructureJHolomorphicAt (eV x))

end Transport

end TauCeti
