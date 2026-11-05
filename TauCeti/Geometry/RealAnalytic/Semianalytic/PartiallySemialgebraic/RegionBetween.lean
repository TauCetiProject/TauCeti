/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.RegionBetween
public import TauCeti.Geometry.RealAnalytic.Semianalytic.PartiallySemialgebraic.Projection
public import TauCeti.Topology.Order.RegionBetween

/-!
# Partial semialgebraicity of band interpolation

The graph of affine interpolation between two pairs of endpoints is partially semialgebraic
if the base map and source endpoints have partially semialgebraic graphs and the target
endpoints have semialgebraic graphs. The analytic base variables are the entire source point
`(u, t)`; only the target variables are polynomial variables. Thus this is the inverse-graph
condition used in transferring triangulations by band maps, not global semialgebraicity.

Endpoint values are introduced as four auxiliary real variables and eliminated by projection.
At a collapsed source fibre the interpolation formula selects the lower target endpoint.
The graph conclusion itself needs neither continuity nor agreement of the target endpoints
there. Continuity on the closed band additionally requires the collapsed-endpoint condition,
as in `TauCeti.continuousOn_regionBetweenMap`.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore
di Pisa (3) 18 (1964), 449–474, §2, Lemma 14.
-/

public section

open Filter MvPolynomial Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
  {g : E → ι → ℝ} {φ φ' : E → ℝ} {ψ ψ' : (ι → ℝ) → ℝ}
  {U : Set E} {T : Set (ι → ℝ)}

/-- **Partial semialgebraicity of a closed-band interpolation graph.** The base map and source
endpoints may have merely partially semialgebraic graphs. The target endpoints are
semialgebraic on a set containing the image of the base. The source height is part of the
analytic base, and the target base and height are the polynomial coordinates.

No strict ordering is required: empty and collapsed fibres are included. For continuity and
endpoint compatibility one separately imposes the collapsed-endpoint condition. -/
theorem isPartiallySemialgebraic_graphOn_regionBetweenMap
    (hg : IsPartiallySemialgebraic (U.graphOn g))
    (hφ : IsPartiallySemialgebraic (U.graphOn (fun u (_ : Unit) => φ u)))
    (hφ' : IsPartiallySemialgebraic (U.graphOn (fun u (_ : Unit) => φ' u)))
    (hψ : IsSemialgebraicOn (fun y (_ : Unit) => ψ y) T)
    (hψ' : IsSemialgebraicOn (fun y (_ : Unit) => ψ' y) T)
    (hgT : MapsTo g U T) :
    IsPartiallySemialgebraic ((closedRegionBetween φ φ' U).graphOn
      (fun p => Sum.elim (g p.1)
        (fun _ : Unit => (regionBetweenMap g φ φ' ψ ψ' p).2))) := by
  let I := (ι ⊕ Unit) ⊕ Fin 4
  let y : (I → ℝ) → ι → ℝ := fun z i => z (.inl (.inl i))
  let height : (I → ℝ) → ℝ := fun z => z (.inl (.inr ()))
  let val : (I → ℝ) → Fin 4 → ℝ := fun z i => z (.inr i)
  -- All graph relations are pulled into the same space without changing their analytic base.
  have hG := (hg.preimage_prodMap (g := (Prod.fst : E × ℝ → E))
    analyticOnNhd_fst).preimage_comp_snd (fun i => (Sum.inl (Sum.inl i) : I))
  have hA := (hφ.preimage_prodMap (g := (Prod.fst : E × ℝ → E))
    analyticOnNhd_fst).preimage_comp_snd (fun _ : Unit => (Sum.inr 0 : I))
  have hB := (hφ'.preimage_prodMap (g := (Prod.fst : E × ℝ → E))
    analyticOnNhd_fst).preimage_comp_snd (fun _ : Unit => (Sum.inr 1 : I))
  have hC := IsSemialgebraic.isPartiallySemialgebraic_preimage_snd (E := E × ℝ)
    (hψ.graph.preimage_comp
      (Sum.elim (fun i => (Sum.inl (Sum.inl i) : I)) (fun _ : Unit => Sum.inr 2)))
  have hD := IsSemialgebraic.isPartiallySemialgebraic_preimage_snd (E := E × ℝ)
    (hψ'.graph.preimage_comp
      (Sum.elim (fun i => (Sum.inl (Sum.inl i) : I)) (fun _ : Unit => Sum.inr 3)))
  -- The interpolation constraint has one analytic coefficient: the source height t.
  have hL : IsPartiallySemialgebraic {p : (E × ℝ) × (I → ℝ) |
      val p.2 0 ≤ p.1.2 ∧ p.1.2 ≤ val p.2 1 ∧
      height p.2 = val p.2 2 + (p.1.2 - val p.2 0) / (val p.2 1 - val p.2 0) *
        (val p.2 3 - val p.2 2)} := by
    have hS := isSemialgebraic_interpolation_constraint (R := ℝ)
      (Sum.inr (Sum.inr 0) : Unit ⊕ I) (.inr (.inr 1)) (.inr (.inr 2))
      (.inr (.inr 3)) (.inl ()) (.inr (.inl (.inr ())))
    have h := hS.isAnalyticCoeffBooleanCombination_preimage_sumElim
      (c := fun p : E × ℝ => fun _ : Unit => p.2) (U := univ)
      (fun _ => analyticOnNhd_snd)
    exact h.isPartiallySemialgebraic
  let R : Set ((E × ℝ) × (I → ℝ)) := {p |
    p.1.1 ∈ U ∧ g p.1.1 = y p.2 ∧ φ p.1.1 = val p.2 0 ∧ φ' p.1.1 = val p.2 1 ∧
    y p.2 ∈ T ∧ ψ (y p.2) = val p.2 2 ∧ ψ' (y p.2) = val p.2 3 ∧
    val p.2 0 ≤ p.1.2 ∧ p.1.2 ≤ val p.2 1 ∧
    height p.2 = val p.2 2 + (p.1.2 - val p.2 0) / (val p.2 1 - val p.2 0) *
      (val p.2 3 - val p.2 2)}
  have hR : IsPartiallySemialgebraic R := by
    convert hG.inter (hA.inter (hB.inter (hC.inter (hD.inter hL)))) using 1
    ext p
    simp only [R, y, val, height, mem_ofPred_eq, mem_inter_iff, mem_preimage,
      Prod.map_apply, id_eq, mem_graphOn,
      Equiv.sumArrowEquivProdArrow_apply_snd,
      Function.comp_def, Sum.elim_inr, funext_iff, forall_const]
    tauto
  -- Eliminate just the four endpoint values, retaining the target base and height.
  have hproj := hR.image_prodMap_comp_inl
  convert hproj using 1
  ext q
  simp only [mem_graphOn, mem_closedRegionBetween, mem_Icc]
  constructor
  · rintro ⟨hq, heq⟩
    have hqU := hq.1
    have hqlo := hq.2.1
    have hqhi := hq.2.2
    let z : I → ℝ := Sum.elim q.2 ![φ q.1.1, φ' q.1.1, ψ (g q.1.1), ψ' (g q.1.1)]
    refine ⟨(q.1, z), ?_, ?_⟩
    · have hy : y z = g q.1.1 := by
        funext i
        exact (congrFun heq (.inl i)).symm
      have hs := congrFun heq (.inr ())
      refine ⟨hqU, hy.symm, rfl, rfl, hy.symm ▸ hgT hqU,
        congrArg ψ hy, congrArg ψ' hy, hqlo, hqhi, ?_⟩
      simpa [height, val, z] using hs.symm
    · simp [z, Prod.map_apply]
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨hu, hgy, ha, hb, hyT, hc, hd, hlo, hhi, hs⟩ := hp
    refine ⟨⟨hu, ha ▸ hlo, hb ▸ hhi⟩, ?_⟩
    funext i
    cases i with
    | inl i => exact congrFun hgy i
    | inr i =>
      cases i
      simpa only [Prod.map_fst, Prod.map_snd, id_eq, Function.comp_apply,
        regionBetweenMap_snd, Sum.elim_inr, hgy, ha, hb, hc, hd] using hs.symm

end TauCeti
