/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Comap
public import TauCeti.Topology.CategoryTheory.ComposableArrows

import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The first face of an étale groupoid's smooth nerve

The charted space of strings is obtained inductively from the object manifold, pulling back
charts along the local homeomorphism that deletes the first vertex. With these charts that face
is a local diffeomorphism, so its local inverse branches can be used to pull back forms in the
weighted insertion operator. The charts are on the existing topological nerve, with no quotient
by isotropy. When source and target are local diffeomorphisms, taking the first vertex is also
a local diffeomorphism, so a smooth cutoff on objects pulls back to a smooth weight.
-/

public noncomputable section

open CategoryTheory Topology
open scoped Manifold ContDiff

namespace CategoryTheory.ComposableArrows

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {C : Type*} [Category C] [IsGroupoid C] [TopologicalSpace C] [ChartedSpace H C]
  [TopologicalSpace (Quiver.Total C)] [TauCeti.IsTopologicalGroupoid C]

open TauCeti.IsTopologicalGroupoid in
/-- Charts on strings in a topological groupoid with étale target: pull back object charts
in degree zero and tail charts along the first face in each successive degree. -/
@[instance_reducible]
def etaleChartedSpace (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) :
    (n : ℕ) → ChartedSpace H (ComposableArrows C n)
  | 0 => (zeroHomeomorph continuous_source continuous_unit).isLocalHomeomorph.chartedSpaceComap
  | n + 1 =>
    letI := etaleChartedSpace ht n
    (isLocalHomeomorph_δ₀ continuous_source continuous_unit
      (by simpa only [Quiver.Total.comp_def] using continuous_comp (C := C)) ht n).chartedSpaceComap

open TauCeti.IsTopologicalGroupoid in
/-- The pulled-back charts make each level of the étale nerve a `C^r` manifold. -/
theorem isManifold_etaleChartedSpace {r : ℕ∞ω} [IsManifold I r C]
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) (n : ℕ) :
    letI := etaleChartedSpace (H := H) ht n
    IsManifold I r (ComposableArrows C n) := by
  induction n with
  | zero =>
    exact (zeroHomeomorph continuous_source continuous_unit).isLocalHomeomorph
      |>.isManifold_chartedSpaceComap
  | succ n ih =>
    let := etaleChartedSpace (H := H) ht n
    let := ih
    exact (isLocalHomeomorph_δ₀ continuous_source continuous_unit
      (by simpa only [Quiver.Total.comp_def] using continuous_comp (C := C)) ht n)
      |>.isManifold_chartedSpaceComap

open TauCeti.IsTopologicalGroupoid in
/-- The first face is a `C^r` local diffeomorphism for the charts pulled back from the tail. -/
theorem isLocalDiffeomorph_δ₀ {r : ℕ∞ω}
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) (n : ℕ) :
    letI := etaleChartedSpace (H := H) ht n
    letI := etaleChartedSpace (H := H) ht (n + 1)
    IsLocalDiffeomorph I I r (fun F : ComposableArrows C (n + 1) ↦ F.δ₀) := by
  let := etaleChartedSpace (H := H) ht n
  exact (isLocalHomeomorph_δ₀ continuous_source continuous_unit
    (by simpa only [Quiver.Total.comp_def] using continuous_comp (C := C)) ht n)
    |>.isLocalDiffeomorph_chartedSpaceComap

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [ChartedSpace H' (Quiver.Total C)]

open TauCeti.IsTopologicalGroupoid in
/-- For a `C^r` étale groupoid, taking the first vertex is a `C^r` local diffeomorphism
on each nerve level. -/
theorem isLocalDiffeomorph_left {r : ℕ∞ω}
    (hs : IsLocalDiffeomorph J I r (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalDiffeomorph J I r (Quiver.Total.right : Quiver.Total C → C)) (n : ℕ) :
    letI := etaleChartedSpace (H := H) ht.isLocalHomeomorph n
    IsLocalDiffeomorph I I r (fun F : ComposableArrows C n ↦ F.left) := by
  induction n with
  | zero =>
    let e := zeroHomeomorph (C := C) continuous_source continuous_unit
    have he : (e : ComposableArrows C 0 → C) = fun F ↦ F.left :=
      funext (zeroHomeomorph_apply continuous_source continuous_unit)
    rw [← he]
    exact e.isLocalHomeomorph.isLocalDiffeomorph_chartedSpaceComap (I := I) (n := r)
  | succ n ih =>
    let := etaleChartedSpace (H := H) ht.isLocalHomeomorph n
    let := etaleChartedSpace (H := H) ht.isLocalHomeomorph (n + 1)
    let a (F : ComposableArrows C (n + 1)) := F.totalArrow 0 1 (Fin.zero_le _)
    have hδ := isLocalDiffeomorph_δ₀ (I := I) (r := r) ht.isLocalHomeomorph n
    have heq : Quiver.Total.right ∘ a = fun F ↦ F.δ₀.left := by
      funext F
      exact (totalArrow_right F 0 1 (Fin.zero_le _)).trans F.δ₀_left.symm
    have htarget : IsLocalDiffeomorph I I r (Quiver.Total.right ∘ a) := by
      rw [heq]
      exact fun F ↦ (hδ F).comp (hg := ih F.δ₀)
    have ha : IsLocalDiffeomorph I J r a := fun F ↦
      (htarget F).of_comp_left (ht (a F)) (continuous_totalArrow 0 1 (Fin.zero_le _)).continuousAt
    have hleft : IsLocalDiffeomorph I I r (Quiver.Total.left ∘ a) := fun F ↦
      (ha F).comp (hg := hs (a F))
    have he : Quiver.Total.left ∘ a = fun F ↦ F.left :=
      funext fun F ↦ totalArrow_left F 0 1 (Fin.zero_le _)
    exact he ▸ hleft

end CategoryTheory.ComposableArrows
