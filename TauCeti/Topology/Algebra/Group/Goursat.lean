/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Connected.PathConnected
public import TauCeti.GroupTheory.Goursat
import Mathlib.Tactic.Group

/-!
# Topological Goursat coordinates for diagonal overgroups

For a topological group `G` and a subgroup `H ≤ G × G` containing `(MonoidHom.id G).graph`, the map
`(g, h) ↦ (g / h, h)` defines a homeomorphism
`Subgroup.goursatCoordHomeomorph : H ≃ₜ H.goursatFst × G` with semidirect multiplication
`(a, h) * (b, k) = (a * (h * b * h⁻¹), h * k)`. Closedness of `H` reduces to that of
`H.goursatFst`, and preconnectedness (resp. path connectedness) of `H` reduces to that of
`H.goursatFst` when `G` is preconnected (resp. path connected).

## References

* Nicolas Bourbaki, *General Topology*, Chapters 1–4, Springer, 1998, Chapter III, §2.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Goursat coordinate homeomorphism** `H ≃ₜ H.goursatFst × G` via `(g, h) ↦ (g / h, h)`. -/
def goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H) :
    H ≃ₜ H.goursatFst × G where
  toFun p := (⟨p.val.1 / p.val.2, (mem_iff_div_mem_goursatFst hH).mp p.property⟩, p.val.2)
  invFun q := ⟨(q.1.val * q.2, q.2),
    (mem_iff_div_mem_goursatFst hH).mpr (by simp [mul_div_cancel_right])⟩
  left_inv p := Subtype.ext (Prod.ext (div_mul_cancel p.val.1 p.val.2) rfl)
  right_inv q := Prod.ext (Subtype.ext (mul_div_cancel_right q.1.val q.2)) rfl
  continuous_toFun :=
    (((continuous_fst.comp continuous_subtypeVal).div'
      (continuous_snd.comp continuous_subtypeVal)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtypeVal)
  continuous_invFun :=
    (((continuous_subtypeVal.comp continuous_fst).mul continuous_snd).prodMk
      continuous_snd).subtype_mk _

@[simp]
theorem coe_fst_goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p : H) : ((goursatCoordHomeomorph hH p).1 : G) = p.val.1 / p.val.2 := by rfl

@[simp] theorem snd_goursatCoordHomeomorph {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p : H) : (goursatCoordHomeomorph hH p).2 = p.val.2 := by rfl

@[simp]
theorem coe_goursatCoordHomeomorph_symm {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (q : H.goursatFst × G) :
    ((goursatCoordHomeomorph hH).symm q : G × G) = (q.1.val * q.2, q.2) := by
  rfl

/-- Semidirect multiplication law `(a, h) * (b, k) = (a * (h * b * h⁻¹), h * k)` in Goursat
coordinates. -/
theorem goursatCoordHomeomorph_mul {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    (p q : H) :
    goursatCoordHomeomorph hH (p * q) =
      (⟨(goursatCoordHomeomorph hH p).1.val *
          ((goursatCoordHomeomorph hH p).2 * (goursatCoordHomeomorph hH q).1.val *
            (goursatCoordHomeomorph hH p).2⁻¹),
        H.goursatFst.mul_mem (goursatCoordHomeomorph hH p).1.property
          ((normal_goursatFst_of_graph_id_le hH).conj_mem _
            (goursatCoordHomeomorph hH q).1.property _)⟩,
        (goursatCoordHomeomorph hH p).2 * (goursatCoordHomeomorph hH q).2) := by
  refine Prod.ext (Subtype.ext ?_) rfl
  simp only [coe_fst_goursatCoordHomeomorph, snd_goursatCoordHomeomorph, coe_mul, Prod.fst_mul,
    Prod.snd_mul, div_eq_mul_inv]; group

/-- `H ≤ G × G` containing the diagonal is closed iff `H.goursatFst` is closed in `G`. -/
theorem isClosed_iff_isClosed_goursatFst {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) :
    IsClosed (H : Set (G × G)) ↔ IsClosed (H.goursatFst : Set G) :=
  ⟨fun hc => by
    convert hc.preimage (continuous_id.prodMk (continuous_const : Continuous fun _ : G => (1 : G)))
    ext; exact mem_goursatFst,
   fun hc => by
    convert hc.preimage (continuous_fst.div' continuous_snd)
    ext; exact mem_iff_div_mem_goursatFst hH⟩

/-- When `G` is preconnected, `H` is preconnected iff `H.goursatFst` is preconnected. -/
theorem isPreconnected_iff_isPreconnected_goursatFst [PreconnectedSpace G] {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) :
    IsPreconnected (H : Set (G × G)) ↔ IsPreconnected (H.goursatFst : Set G) := by
  rw [isPreconnected_iff_preconnectedSpace, isPreconnected_iff_preconnectedSpace]
  refine ⟨fun _ => (Function.Surjective.denseRange
      (f := fun p : H => (goursatCoordHomeomorph hH p).1)
      fun a => ⟨(goursatCoordHomeomorph hH).symm (a, 1), by simp⟩).preconnectedSpace
      (continuous_fst.comp (goursatCoordHomeomorph hH).continuous), ?_⟩
  exact fun _ => (goursatCoordHomeomorph hH).symm.surjective.denseRange.preconnectedSpace
    (goursatCoordHomeomorph hH).symm.continuous

/-- When `G` is path connected, `H` is path connected iff `H.goursatFst` is path connected. -/
theorem pathConnectedSpace_iff_pathConnectedSpace_goursatFst [PathConnectedSpace G]
    {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H) :
    PathConnectedSpace H ↔ PathConnectedSpace H.goursatFst :=
  ⟨fun _ => Function.Surjective.pathConnectedSpace
      (f := fun p : H => (goursatCoordHomeomorph hH p).1)
      (fun a => ⟨(goursatCoordHomeomorph hH).symm (a, 1), by simp⟩)
      (continuous_fst.comp (goursatCoordHomeomorph hH).continuous),
   fun _ => (goursatCoordHomeomorph hH).symm.surjective.pathConnectedSpace
      (goursatCoordHomeomorph hH).symm.continuous⟩

end Subgroup
