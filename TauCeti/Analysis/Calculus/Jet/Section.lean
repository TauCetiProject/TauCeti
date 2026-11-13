/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Nonlinear
public import Mathlib.Order.Setoid.Basic

/-!
# First jets of local sections in a bundle chart

`TauCeti.FirstJetAt` is the quotient of maps smooth near a point by equality of
value and first derivative there. Its coordinate equivalence identifies the quotient
with a value and a continuous linear map; affine sections realize every such pair.
Representatives need only be smooth near the chosen point, so this carrier applies
to sections defined on chart domains, using arbitrary extensions outside the domain.

Base-dependent nonlinear fibre maps induce maps of these quotients, with coordinates
given by `TauCeti.firstJetCoordChange`. The chain rule, composition and local inverse
laws show that the equivalence relation is independent
of bundle coordinates. No vector-space structure is selected intrinsically on these
quotients, and no global jet bundle or higher-order jet is constructed here.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Kolář, Michor and Slovák, *Natural Operations in Differential Geometry*, Chapter 12.
-/

public section

noncomputable section

open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E E' E'' F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- First jets at `x` of local smooth sections in a bundle chart with fibre `F`.
Only the germ near `x` must be smooth. The equivalence relation identifies sections
having the same value and first derivative. -/
def FirstJetAt (𝕜 : Type*) {E : Type*} (F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (x : E) :=
  Quotient (Setoid.ker (fun s : {s : E → F // ContDiffAt 𝕜 ∞ s x} ↦
    (s.1 x, fderiv 𝕜 s.1 x)))

namespace FirstJetAt

/-- The first jet of a section smooth near `x`. -/
def mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) : FirstJetAt 𝕜 F x :=
  Quotient.mk'' ⟨s, hs⟩

/-- Value and derivative coordinates of a first jet in the selected bundle chart. -/
def coordinates {x : E} : FirstJetAt 𝕜 F x → F × (E →L[𝕜] F) :=
  Setoid.kerLift _

@[simp]
theorem coordinates_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    coordinates (mk s hs) = (s x, fderiv 𝕜 s x) :=
  (rfl)

/-- Two local sections define the same jet exactly when their values and derivatives agree. -/
@[simp]
theorem mk_eq_mk_iff {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) :
    mk s hs = mk t ht ↔ s x = t x ∧ fderiv 𝕜 s x = fderiv 𝕜 t x := by
  constructor
  · intro h
    exact Prod.ext_iff.mp (congrArg coordinates h)
  · rintro ⟨hv, hd⟩
    exact Quotient.sound (Prod.ext hv hd)

/-- The quotient forgets how a local section is extended away from the point. -/
theorem mk_eq_mk_of_eventuallyEq {x : E} {s t : E → F}
    (hs : ContDiffAt 𝕜 ∞ s x) (ht : ContDiffAt 𝕜 ∞ t x) (h : s =ᶠ[𝓝 x] t) :
    mk s hs = mk t ht :=
  (mk_eq_mk_iff hs ht).2 ⟨h.eq_of_nhds, h.fderiv_eq⟩

/-- A jet is determined by its value and first derivative coordinates. -/
@[ext]
theorem ext {x : E} {j k : FirstJetAt 𝕜 F x} (h : coordinates j = coordinates k) :
    j = k :=
  Setoid.kerLift_injective _ h

/-- Every value and derivative pair is realized by an affine, hence smooth, section. -/
theorem exists_section_coordinates (x : E) (j : F × (E →L[𝕜] F)) :
    ∃ s : E → F, ContDiff 𝕜 ∞ s ∧ (s x, fderiv 𝕜 s x) = j := by
  refine ⟨fun y ↦ j.1 + j.2 (y - x), contDiff_const.add
    (j.2.contDiff.comp (contDiff_id.sub contDiff_const)), ?_⟩
  have hd : HasFDerivAt (fun y ↦ j.1 + j.2 (y - x)) j.2 x := by
    simpa using (j.2.hasFDerivAt.comp x (hasFDerivAt_sub_const x)).const_add j.1
  rw [hd.fderiv]
  simp only [sub_self, map_zero, add_zero]

/-- A prescribed jet whose value lies in an open bundle-chart domain is realized
by a smooth section whose graph remains in that domain near the base point. -/
theorem exists_section_coordinates_mem {x : E} (j : F × (E →L[𝕜] F))
    {u : Set (E × F)} (hu : IsOpen u) (hj : (x, j.1) ∈ u) :
    ∃ s : E → F, ContDiff 𝕜 ∞ s ∧ (s x, fderiv 𝕜 s x) = j ∧
      ∀ᶠ y in 𝓝 x, (y, s y) ∈ u := by
  obtain ⟨s, hs, hsj⟩ := exists_section_coordinates x j
  refine ⟨s, hs, hsj, ?_⟩
  have hv : s x = j.1 := congrArg Prod.fst hsj
  have hmem : (x, s x) ∈ u := by simpa only [hv] using hj
  exact (continuousAt_id.prodMk hs.continuous.continuousAt).eventually (hu.mem_nhds hmem)

/-- Coordinates identify section-equivalence classes with all value/derivative pairs.
The inverse is represented by an affine section; this is a chart-dependent identification. -/
def coordinatesEquiv (x : E) : FirstJetAt 𝕜 F x ≃ F × (E →L[𝕜] F) :=
  Setoid.quotientKerEquivOfRightInverse _
    (fun j ↦ ⟨(exists_section_coordinates x j).choose,
      (exists_section_coordinates x j).choose_spec.1.contDiffAt⟩)
    (fun j ↦ (exists_section_coordinates x j).choose_spec.2)

@[simp]
theorem coordinatesEquiv_apply {x : E} (j : FirstJetAt 𝕜 F x) :
    coordinatesEquiv x j = coordinates j :=
  Setoid.quotientKerEquivOfRightInverse_apply _ _ _ j

@[simp]
theorem coordinates_coordinatesEquiv_symm (x : E) (j : F × (E →L[𝕜] F)) :
    coordinates ((coordinatesEquiv x).symm j) = j :=
  (coordinatesEquiv x).apply_symm_apply j

/-- Every quotient class has a globally smooth representative in the chosen chart. -/
theorem exists_section {x : E} (j : FirstJetAt 𝕜 F x) :
    ∃ s : E → F, ∃ hs : ContDiff 𝕜 ∞ s, mk s hs.contDiffAt = j := by
  obtain ⟨s, hs, hj⟩ := exists_section_coordinates x (coordinates j)
  exact ⟨s, hs, ext hj⟩

/-- Order-zero truncation of a first jet, in the selected fibre coordinates. -/
def value {x : E} (j : FirstJetAt 𝕜 F x) : F :=
  (coordinates j).1

@[simp]
theorem fst_coordinates {x : E} (j : FirstJetAt 𝕜 F x) :
    (coordinates j).1 = value j :=
  (rfl)

@[simp]
theorem value_mk {x : E} (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) :
    value (mk s hs) = s x :=
  (rfl)

/-- Order-zero truncation is surjective, including for zero-dimensional fibres. -/
theorem value_surjective (x : E) : Function.Surjective (value : FirstJetAt 𝕜 F x → F) := by
  intro v
  exact ⟨mk (fun _ ↦ v) contDiffAt_const, rfl⟩

/-- Apply the first-jet coordinate formula for a base change and a base-dependent
nonlinear fibre map. For smooth maps this agrees with transforming sections, as in `map_mk`. -/
def map {x : E'} (h : E' → E) (g : E' × F → G) (j : FirstJetAt 𝕜 F (h x)) :
    FirstJetAt 𝕜 G x :=
  (coordinatesEquiv x).symm (firstJetCoordChange h g x (coordinates j))

/-- Nonlinear coordinate changes on the quotient have the usual first-jet coordinates. -/
@[simp]
theorem coordinates_map {x : E'} (h : E' → E) (g : E' × F → G)
    (j : FirstJetAt 𝕜 F (h x)) :
    coordinates (map h g j) = firstJetCoordChange h g x (coordinates j) :=
  coordinates_coordinatesEquiv_symm _ _

@[simp]
theorem value_map {x : E'} (h : E' → E) (g : E' × F → G)
    (j : FirstJetAt 𝕜 F (h x)) :
    value (map h g j) = g (x, value j) := by
  simpa only [firstJetCoordChange_fst, fst_coordinates] using
    congrArg Prod.fst (coordinates_map h g j)

/-- Computing the jet before or after transforming an actual local section agrees.
In particular the transformed section depends only on its input jet. -/
@[simp]
theorem map_mk {x : E'} (h : E' → E) (g : E' × F → G) (s : E → F)
    (hs : ContDiffAt 𝕜 ∞ s (h x)) (hh : ContDiffAt 𝕜 ∞ h x)
    (hg : ContDiffAt 𝕜 ∞ g (x, s (h x))) :
    map h g (mk s hs) =
      mk (fun y ↦ g (y, s (h y))) (hg.comp x (contDiffAt_id.prodMk (hs.comp x hh))) := by
  apply ext
  simpa only [coordinates_map, coordinates_mk] using
    firstJetCoordChange_fderiv (hh.differentiableAt (by simp))
      (hg.differentiableAt (by simp)) (hs.differentiableAt (by simp))

/-- Identity coordinate changes induce the identity on section-equivalence classes. -/
@[simp]
theorem map_id {x : E} (j : FirstJetAt 𝕜 F x) :
    map id Prod.snd j = j := by
  apply ext
  simp

/-- Nonlinear changes of coordinates compose on section-equivalence classes. -/
theorem map_comp {y : E''} (h : E' → E) (k : E'' → E')
    (g : E' × F → G) (l : E'' × G → H) (j : FirstJetAt 𝕜 F (h (k y)))
    (hh : DifferentiableAt 𝕜 h (k y)) (hk : DifferentiableAt 𝕜 k y)
    (hg : DifferentiableAt 𝕜 g (k y, value j))
    (hl : DifferentiableAt 𝕜 l (y, g (k y, value j))) :
    map k l (map h g j) =
      map (h ∘ k) (fun p : E'' × F ↦ l (p.1, g (k p.1, p.2))) j := by
  apply ext
  simp only [coordinates_map]
  exact firstJetCoordChange_comp _ hh hk hg hl

/-- Changes of local sections that are inverse as germs restore the original jet
coordinates. The base points agree by the base germ identity; the coordinate statement
avoids transport between the dependent quotient types at those equal points. -/
theorem coordinates_map_inverse {x : E} (h : E' → E) (k : E → E')
    (g : E' × F → G) (l : E × G → F) (j : FirstJetAt 𝕜 F (h (k x)))
    (hh : DifferentiableAt 𝕜 h (k x)) (hk : DifferentiableAt 𝕜 k x)
    (hg : DifferentiableAt 𝕜 g (k x, value j))
    (hl : DifferentiableAt 𝕜 l (x, g (k x, value j)))
    (hbase : h ∘ k =ᶠ[𝓝 x] id)
    (hfibre : (fun p : E × F ↦ l (p.1, g (k p.1, p.2))) =ᶠ[𝓝 (x, value j)] Prod.snd) :
    coordinates (map k l (map h g j)) = coordinates j := by
  simp only [coordinates_map]
  exact firstJetCoordChange_inverse _ hh hk hg hl hbase hfibre

end FirstJetAt

end TauCeti
