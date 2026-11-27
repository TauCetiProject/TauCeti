/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Goursat
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Subgroups of `G × G` containing the diagonal

For `H : Subgroup (G × G)` containing `(MonoidHom.id G).graph`, both coordinate projections are
surjective, `H.goursatFst` is normal in `G`, and `(g, h) ∈ H ↔ g / h ∈ H.goursatFst`. Conversely,
`Subgroup.diagonalExt N = {(g, h) | g / h ∈ N}` gives an order isomorphism
`Subgroup.graphIdIciOrderIsoNormal` between `Set.Ici (MonoidHom.id G).graph` and
`{N : Subgroup G // N.Normal}`. This computes `Subgroup.normalizer_graph_id` and
`Subgroup.normalizer_diagonalExt_center_of_center_quotient_eq_bot`.

## References

* Serge Lang, *Algebra*, rev. 3rd ed., Springer GTM 211, 2002, Chapter I, §9, Exercise 5.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup of `G × G` containing the diagonal projects surjectively onto the first factor. -/
theorem surjective_fst_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : Function.Surjective (Prod.fst ∘ H.subtype) :=
  fun g => ⟨⟨(g, g), hH (MonoidHom.mem_graph.mpr rfl)⟩, rfl⟩

/-- A subgroup of `G × G` containing the diagonal projects surjectively onto the second factor. -/
theorem surjective_snd_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : Function.Surjective (Prod.snd ∘ H.subtype) :=
  fun g => ⟨⟨(g, g), hH (MonoidHom.mem_graph.mpr rfl)⟩, rfl⟩

/-- For `H ≤ G × G` containing the diagonal, `H.goursatFst` is normal in `G`. -/
theorem normal_goursatFst_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : H.goursatFst.Normal :=
  H.normal_goursatFst (surjective_fst_of_graph_id_le hH)

/-- When `(MonoidHom.id G).graph ≤ H`, `p ∈ H ↔ p.1 / p.2 ∈ H.goursatFst`. -/
theorem mem_iff_div_mem_goursatFst {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) {p : G × G} :
    p ∈ H ↔ p.1 / p.2 ∈ H.goursatFst := by
  have hd : (p.2⁻¹, p.2⁻¹) ∈ H := hH (MonoidHom.mem_graph.mpr rfl)
  rw [mem_goursatFst, ← H.mul_mem_cancel_right hd]
  simp [Prod.mul_def, div_eq_mul_inv]

/-- **The diagonal extension of a normal subgroup** `N ⊴ G`: `{(g, h) : G × G | g / h ∈ N}`. -/
def diagonalExt (N : Subgroup G) [hN : N.Normal] : Subgroup (G × G) where
  carrier := {p | p.1 / p.2 ∈ N}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul] at ha hb ⊢
    have h : (a.1 * b.1) / (a.2 * b.2) = (a.1 / a.2) * (a.2 * (b.1 / b.2) * a.2⁻¹) := by
      simp only [div_eq_mul_inv]; group
    exact h ▸ N.mul_mem ha (hN.conj_mem _ hb a.2)
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv] at ha ⊢
    have h : a.1⁻¹ / a.2⁻¹ = a.2⁻¹ * (a.1 / a.2)⁻¹ * (a.2⁻¹)⁻¹ := by
      simp only [div_eq_mul_inv]; group
    exact h ▸ hN.conj_mem _ (N.inv_mem ha) a.2⁻¹

@[simp] theorem mem_diagonalExt {N : Subgroup G} [N.Normal] {p : G × G} :
    p ∈ diagonalExt N ↔ p.1 / p.2 ∈ N := by rfl

theorem graph_id_le_diagonalExt (N : Subgroup G) [N.Normal] :
    (MonoidHom.id G).graph ≤ diagonalExt N :=
  fun p hp => by rw [MonoidHom.mem_graph, MonoidHom.id_apply] at hp; simp [hp]

@[simp] theorem goursatFst_diagonalExt (N : Subgroup G) [N.Normal] :
    (diagonalExt N).goursatFst = N := by ext; simp

theorem diagonalExt_goursatFst {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H) :
    @diagonalExt _ _ H.goursatFst (normal_goursatFst_of_graph_id_le hH) = H :=
  ext fun _ => (mem_iff_div_mem_goursatFst hH).symm

@[simp] theorem diagonalExt_bot : diagonalExt (⊥ : Subgroup G) = (MonoidHom.id G).graph := by
  ext ⟨g, h⟩; simp [MonoidHom.mem_graph, div_eq_one]

@[simp] theorem diagonalExt_top : diagonalExt (⊤ : Subgroup G) = ⊤ := by ext; simp

@[simp] theorem goursatFst_graph_id : ((MonoidHom.id G).graph).goursatFst = ⊥ := by
  ext; simp [MonoidHom.mem_graph]

@[simp] theorem goursatFst_top : (⊤ : Subgroup (G × G)).goursatFst = ⊤ := by ext; simp

/-- **Goursat normal-kernel correspondence** for subgroups of `G × G` containing the diagonal. -/
def graphIdIciOrderIsoNormal (G : Type*) [Group G] :
    Set.Ici (MonoidHom.id G).graph ≃o {N : Subgroup G // N.Normal} where
  toFun H := ⟨H.val.goursatFst, normal_goursatFst_of_graph_id_le H.property⟩
  invFun N := let _ := N.property; ⟨diagonalExt N.val, graph_id_le_diagonalExt N.val⟩
  left_inv H := Subtype.ext (diagonalExt_goursatFst H.property)
  right_inv N := by let _ := N.property; exact Subtype.ext (goursatFst_diagonalExt N.val)
  map_rel_iff' {H₁ H₂} :=
    ⟨fun hle _ hp => (mem_iff_div_mem_goursatFst H₂.property).mpr
      (hle ((mem_iff_div_mem_goursatFst H₁.property).mp hp)),
     fun hle _ hg => mem_goursatFst.mpr (hle (mem_goursatFst.mp hg))⟩

@[simp] theorem coe_graphIdIciOrderIsoNormal_apply (H : Set.Ici (MonoidHom.id G).graph) :
    (graphIdIciOrderIsoNormal G H : Subgroup G) = H.val.goursatFst := by rfl

@[simp] theorem coe_graphIdIciOrderIsoNormal_symm_mk (N : Subgroup G) [hN : N.Normal] :
    ((graphIdIciOrderIsoNormal G).symm ⟨N, hN⟩ : Subgroup (G × G)) = diagonalExt N := by rfl

/-- **The normalizer of the diagonal subgroup in `G × G`** is `diagonalExt (Subgroup.center G)`. -/
theorem normalizer_graph_id (G : Type*) [Group G] :
    normalizer ((MonoidHom.id G).graph : Set (G × G)) = diagonalExt (Subgroup.center G) := by
  ext ⟨g, h⟩
  rw [mem_normalizer_iff, mem_diagonalExt, Subgroup.mem_center_iff]
  refine ⟨fun hnorm y => ?_, fun hc ⟨x, y⟩ => ?_⟩
  · have hconj : g * (h⁻¹ * y * h) * g⁻¹ = h * (h⁻¹ * y * h) * h⁻¹ := by
      simpa [MonoidHom.mem_graph] using
        (hnorm (h⁻¹ * y * h, h⁻¹ * y * h)).mp (MonoidHom.mem_graph.mpr rfl)
    calc y * (g / h) = (h * (h⁻¹ * y * h) * h⁻¹) * (g / h) := by simp only [div_eq_mul_inv]; group
      _ = (g * (h⁻¹ * y * h) * g⁻¹) * (g / h) := by rw [hconj]
      _ = (g / h) * y := by simp only [div_eq_mul_inv]; group
  · simp only [MonoidHom.mem_graph, MonoidHom.id_apply, Prod.mul_def, Prod.inv_mk]
    have hgx : g * x * g⁻¹ = h * x * h⁻¹ := calc
      g * x * g⁻¹ = (g / h) * (h * x * h⁻¹) * (g / h)⁻¹ := by simp only [div_eq_mul_inv]; group
      _ = (h * x * h⁻¹) * (g / h) * (g / h)⁻¹ := by rw [hc (h * x * h⁻¹)]
      _ = h * x * h⁻¹ := by group
    rw [hgx]
    exact ⟨fun hxy => hxy ▸ rfl, fun hconj => by
      calc x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [hconj]
        _ = y := by group⟩

/-- **When `G ⧸ Z(G)` has trivial center, `diagonalExt (center G)` is self-normalizing.** -/
theorem normalizer_diagonalExt_center_of_center_quotient_eq_bot
    (hZ : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) :
    normalizer (diagonalExt (Subgroup.center G) : Set (G × G)) =
      diagonalExt (Subgroup.center G) := by
  refine le_antisymm (fun ⟨g, h⟩ hnorm => ?_) le_normalizer
  rw [mem_diagonalExt, ← QuotientGroup.eq_one_iff, ← mem_bot, ← hZ, Subgroup.mem_center_iff]
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hcalc : (g / h) * y * (g / h)⁻¹ * y⁻¹ =
      (g * (h⁻¹ * y * h) * g⁻¹) / (h * (h⁻¹ * y * h) * h⁻¹) := by
    simp only [div_eq_mul_inv]; group
  have hx : (g / h) * y * (g / h)⁻¹ * y⁻¹ ∈ Subgroup.center G :=
    hcalc.symm ▸ mem_diagonalExt.mp ((mem_normalizer_iff.mp hnorm (h⁻¹ * y * h, h⁻¹ * y * h)).mp
      (graph_id_le_diagonalExt (Subgroup.center G) (MonoidHom.mem_graph.mpr rfl)))
  have h2 : (QuotientGroup.mk (g / h) : G ⧸ Subgroup.center G) * QuotientGroup.mk y *
      (QuotientGroup.mk (g / h))⁻¹ = QuotientGroup.mk y := by
    simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] using
      (QuotientGroup.eq_one_iff _).mpr hx
  calc (QuotientGroup.mk y : G ⧸ Subgroup.center G) * QuotientGroup.mk (g / h)
      = (QuotientGroup.mk (g / h) * QuotientGroup.mk y * (QuotientGroup.mk (g / h))⁻¹) *
          QuotientGroup.mk (g / h) := by rw [h2]
    _ = QuotientGroup.mk (g / h) * QuotientGroup.mk y := by group

end Subgroup
