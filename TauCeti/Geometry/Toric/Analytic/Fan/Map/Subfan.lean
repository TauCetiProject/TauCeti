/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Preimage
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Orbit
public import TauCeti.Geometry.Toric.Analytic.Fan.Subfan.Orbit
public import TauCeti.Topology.Category.TopCat.Pullback

/-!
# Restricting analytic toric maps to open subfans

For a morphism of regular fans and a face-closed subfan of the target, the source cones whose
least target cones lie in that subfan form the preimage subfan. The analytic map restricts to a
map between these two subfan realizations. The square formed by the restricted map and the two
open-subfan embeddings is a pullback of topological spaces, so the source open subset is exactly
the inverse image of the target open subset.

No nonemptiness assumption is needed: the pullback statement also covers an empty target subfan
and its empty preimage.

## Main declarations

* `TauCeti.Toric.FanHom.preimageSubfanAnalyticMap_comp_analyticMap`: restriction commutes with
  the ambient analytic toric map.
* `TauCeti.Toric.FanHom.range_preimageSubfanAnalyticMap`: the source open subset is the preimage
  of the target open subset.
* `TauCeti.Toric.FanHom.isPullback_preimageSubfan_analyticMap`: the restriction square is a
  pullback in `TopCat`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

open CategoryTheory Set

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Phi : Fan i} {Psi : Fan i'}
  (f : FanHom Phi Psi) (hPhi : Phi.IsRegular) (hPsi : Psi.IsRegular)
  (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
  (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)

/-- Restricting an analytic toric map to the preimage of an open subfan commutes with the two
open-subfan embeddings. -/
@[reassoc]
theorem preimageSubfanAnalyticMap_comp_analyticMap :
    Phi.subfanAnalyticMap hPhi (f.preimageCones S) (f.preimageCones_subset S)
          (f.preimageCones_closedUnderFaces S hface) ≫ f.analyticMap hPhi hPsi =
      (f.restrictToPreimage S hS hface).analyticMap
          (hPhi.preimageSubfan f S hface) (hPsi.subfan S hS hface) ≫
        Psi.subfanAnalyticMap hPsi S hS hface := by
  calc
    _ = (Phi.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
          (f.preimageCones_closedUnderFaces S hface)).analyticMap
            (hPhi.preimageSubfan f S hface) hPhi ≫ f.analyticMap hPhi hPsi := by
        rw [analyticMap_subfanInclusion]
    _ = (f.comp (Phi.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
          (f.preimageCones_closedUnderFaces S hface))).analyticMap
            (hPhi.preimageSubfan f S hface) hPsi :=
        ((Phi.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
          (f.preimageCones_closedUnderFaces S hface)).analyticMap_comp
            (hPhi.preimageSubfan f S hface) hPhi f hPsi).symm
    _ = ((Psi.subfanInclusion S hS hface).comp (f.restrictToPreimage S hS hface)).analyticMap
          (hPhi.preimageSubfan f S hface) hPsi :=
        congrArg (fun g : FanHom (f.preimageSubfan S hface) Psi ↦
          g.analyticMap (hPhi.preimageSubfan f S hface) hPsi)
          (f.subfanInclusion_comp_restrictToPreimage S hS hface).symm
    _ = (f.restrictToPreimage S hS hface).analyticMap
          (hPhi.preimageSubfan f S hface) (hPsi.subfan S hS hface) ≫
        (Psi.subfanInclusion S hS hface).analyticMap
          (hPsi.subfan S hS hface) hPsi :=
        (f.restrictToPreimage S hS hface).analyticMap_comp
          (hPhi.preimageSubfan f S hface) (hPsi.subfan S hS hface)
          (Psi.subfanInclusion S hS hface) hPsi
    _ = _ := by rw [analyticMap_subfanInclusion]

/-- The image of the preimage subfan is exactly the inverse image of the target subfan's open
subset under the ambient analytic toric map. -/
theorem range_preimageSubfanAnalyticMap :
    range (Phi.subfanAnalyticMap hPhi (f.preimageCones S) (f.preimageCones_subset S)
        (f.preimageCones_closedUnderFaces S hface)) =
      f.analyticMap hPhi hPsi ⁻¹' range (Psi.subfanAnalyticMap hPsi S hS hface) := by
  ext x
  obtain ⟨sigma, hx⟩ := Phi.exists_mem_analyticConeOrbit hPhi x
  rw [Phi.mem_range_subfanAnalyticMap_iff hPhi (f.preimageCones S)
      (f.preimageCones_subset S) (f.preimageCones_closedUnderFaces S hface) hx,
    mem_preimage, Psi.mem_range_subfanAnalyticMap_iff hPsi S hS hface
      (f.mapsTo_analyticConeOrbit hPhi hPsi sigma hx),
    f.mem_preimageCones_iff S sigma.2]

/-- Restriction to an open subfan is a base change: the analytic realization of the preimage
subfan is the pullback of the target open-subfan embedding along the ambient toric map. -/
theorem isPullback_preimageSubfan_analyticMap :
    IsPullback
      (Phi.subfanAnalyticMap hPhi (f.preimageCones S) (f.preimageCones_subset S)
        (f.preimageCones_closedUnderFaces S hface))
      ((f.restrictToPreimage S hS hface).analyticMap
        (hPhi.preimageSubfan f S hface) (hPsi.subfan S hS hface))
      (f.analyticMap hPhi hPsi) (Psi.subfanAnalyticMap hPsi S hS hface) :=
  TauCeti.TopCat.isPullback_of_isEmbedding_of_range_eq_preimage
    (Phi.isOpenEmbedding_subfanAnalyticMap hPhi (f.preimageCones S)
      (f.preimageCones_subset S) (f.preimageCones_closedUnderFaces S hface)).isEmbedding
    (Psi.isOpenEmbedding_subfanAnalyticMap hPsi S hS hface).injective
    (f.preimageSubfanAnalyticMap_comp_analyticMap hPhi hPsi S hS hface)
    (f.range_preimageSubfanAnalyticMap hPhi hPsi S hS hface)

end TauCeti.Toric.FanHom
