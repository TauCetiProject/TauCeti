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

For a group `G`, Goursat's lemma (`Mathlib/GroupTheory/Goursat.lean`) simplifies for subgroups
`H : Subgroup (G × G)` containing the diagonal `(MonoidHom.id G).graph`: both coordinate projections
are automatically surjective on `H`, the first Goursat kernel `H.goursatFst = {a | (a, 1) ∈ H}` is
normal in `G`, and `(g, h) ∈ H ↔ g / h ∈ H.goursatFst`. Conversely, any normal subgroup `N ⊴ G`
determines the diagonal extension `Subgroup.diagonalExt N = {(g, h) | g / h ∈ N}`, establishing an
order isomorphism between `{H : Subgroup (G × G) // (MonoidHom.id G).graph ≤ H}` and
`{N : Subgroup G // N.Normal}` (`Subgroup.graphIdIciOrderIsoNormal`).

This description also computes normalizers inside `G × G`:

* `Subgroup.normalizer ((MonoidHom.id G).graph : Set (G × G)) =
  Subgroup.diagonalExt (Subgroup.center G)`;
* when `G ⧸ Subgroup.center G` is centerless, `Subgroup.diagonalExt (Subgroup.center G)` is
  self-normalizing in `G × G`
  (`Subgroup.normalizer_diagonalExt_center_of_center_quotient_eq_bot`).

## Main definitions

* `Subgroup.diagonalExt`: for `N ⊴ G`, the subgroup `{(g, h) : G × G | g / h ∈ N}`.
* `Subgroup.graphIdIciOrderIsoNormal`: order isomorphism between subgroups of `G × G` containing
  `(MonoidHom.id G).graph` and normal subgroups of `G`.

## Main results

* `Subgroup.mem_iff_div_mem_goursatFst`: when `(MonoidHom.id G).graph ≤ H`, `(g, h) ∈ H` iff
  `g / h ∈ H.goursatFst`.
* `Subgroup.normalizer_graph_id`: the normalizer of the diagonal in `G × G` is
  `Subgroup.diagonalExt (Subgroup.center G)`.
* `Subgroup.normalizer_diagonalExt_center_of_center_quotient_eq_bot`: when `G ⧸ Z(G)` has trivial
  center, `Subgroup.diagonalExt (Subgroup.center G)` is self-normalizing.

## References

* Serge Lang, *Algebra*, revised third edition, Springer GTM 211, 2002, Chapter I, §9, Exercise 5.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- A subgroup of `G × G` containing the diagonal projects surjectively onto the first factor. -/
theorem surjective_fst_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : Function.Surjective (Prod.fst ∘ H.subtype) :=
  fun g => ⟨⟨(g, g), hH rfl⟩, rfl⟩

/-- A subgroup of `G × G` containing the diagonal projects surjectively onto the second factor. -/
theorem surjective_snd_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : Function.Surjective (Prod.snd ∘ H.subtype) :=
  fun g => ⟨⟨(g, g), hH rfl⟩, rfl⟩

/-- For a subgroup `H ≤ G × G` containing the diagonal, `H.goursatFst` is normal in `G`. -/
theorem normal_goursatFst_of_graph_id_le {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) : H.goursatFst.Normal :=
  H.normal_goursatFst (surjective_fst_of_graph_id_le hH)

/-- **Membership in a diagonal overgroup via its Goursat kernel**: when
`(MonoidHom.id G).graph ≤ H`, `(g, h) ∈ H` if and only if `g / h ∈ H.goursatFst`. -/
theorem mem_iff_div_mem_goursatFst {H : Subgroup (G × G)}
    (hH : (MonoidHom.id G).graph ≤ H) {p : G × G} :
    p ∈ H ↔ p.1 / p.2 ∈ H.goursatFst := by
  have hdiag : (p.2, p.2) ∈ H := hH rfl
  rw [mem_goursatFst]
  constructor
  · intro hp
    have hmul : p * (p.2, p.2)⁻¹ = (p.1 / p.2, 1) :=
      Prod.ext (div_eq_mul_inv p.1 p.2).symm (mul_inv_cancel p.2)
    exact hmul ▸ H.mul_mem hp (H.inv_mem hdiag)
  · intro hp
    have hmul : (p.1 / p.2, (1 : G)) * (p.2, p.2) = p :=
      Prod.ext (div_mul_cancel p.1 p.2) (one_mul p.2)
    exact hmul ▸ H.mul_mem hp hdiag

/-- **The diagonal extension of a normal subgroup** `N ⊴ G`: the subgroup
`{(g, h) : G × G | g / h ∈ N}` containing the diagonal with first Goursat kernel `N`. -/
def diagonalExt (N : Subgroup G) [hN : N.Normal] : Subgroup (G × G) where
  carrier := {p | p.1 / p.2 ∈ N}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change (a.1 * b.1) / (a.2 * b.2) ∈ N
    have hmul : (a.1 * b.1) / (a.2 * b.2) = (a.1 / a.2) * (a.2 * (b.1 / b.2) * a.2⁻¹) := by
      simp only [div_eq_mul_inv]
      group
    rw [hmul]
    exact N.mul_mem ha (hN.conj_mem _ hb a.2)
  inv_mem' {a} ha := by
    change a.1⁻¹ / a.2⁻¹ ∈ N
    have hinv : a.1⁻¹ / a.2⁻¹ = a.2⁻¹ * (a.1 / a.2)⁻¹ * (a.2⁻¹)⁻¹ := by
      simp only [div_eq_mul_inv]
      group
    rw [hinv]
    exact hN.conj_mem _ (N.inv_mem ha) a.2⁻¹

@[simp]
theorem mem_diagonalExt {N : Subgroup G} [N.Normal] {p : G × G} :
    p ∈ diagonalExt N ↔ p.1 / p.2 ∈ N :=
  Iff.rfl

theorem graph_id_le_diagonalExt (N : Subgroup G) [N.Normal] :
    (MonoidHom.id G).graph ≤ diagonalExt N := by
  intro p hp
  have hp' : p.1 = p.2 := hp
  simp [hp']

@[simp]
theorem goursatFst_diagonalExt (N : Subgroup G) [N.Normal] :
    (diagonalExt N).goursatFst = N := by
  ext g
  simp

theorem diagonalExt_goursatFst {H : Subgroup (G × G)} (hH : (MonoidHom.id G).graph ≤ H)
    [H.goursatFst.Normal] :
    diagonalExt H.goursatFst = H := by
  ext p
  exact (mem_iff_div_mem_goursatFst hH).symm

@[simp]
theorem diagonalExt_bot : diagonalExt (⊥ : Subgroup G) = (MonoidHom.id G).graph := by
  ext ⟨g, h⟩
  simp [MonoidHom.mem_graph, div_eq_one]

@[simp]
theorem diagonalExt_top : diagonalExt (⊤ : Subgroup G) = ⊤ := by
  ext p
  simp

@[simp]
theorem goursatFst_graph_id : ((MonoidHom.id G).graph).goursatFst = ⊥ := by
  ext g
  simp [MonoidHom.mem_graph]

@[simp]
theorem goursatFst_top : (⊤ : Subgroup (G × G)).goursatFst = ⊤ := by
  ext g
  simp

/-- **Goursat normal-kernel correspondence** for subgroups of `G × G` containing the diagonal:
`H ↦ H.goursatFst` is an order isomorphism onto `{N : Subgroup G // N.Normal}`, with inverse
`N ↦ Subgroup.diagonalExt N`. -/
def graphIdIciOrderIsoNormal (G : Type*) [Group G] :
    Set.Ici (MonoidHom.id G).graph ≃o {N : Subgroup G // N.Normal} where
  toFun H := ⟨H.1.goursatFst, normal_goursatFst_of_graph_id_le H.2⟩
  invFun N :=
    let _ := N.2
    ⟨diagonalExt N.1, graph_id_le_diagonalExt N.1⟩
  left_inv H := by
    let _ := normal_goursatFst_of_graph_id_le H.2
    exact Subtype.ext (diagonalExt_goursatFst H.2)
  right_inv N := by
    let _ := N.2
    exact Subtype.ext (goursatFst_diagonalExt N.1)
  map_rel_iff' {H₁ H₂} := by
    constructor
    · intro hle p hp
      exact (mem_iff_div_mem_goursatFst H₂.2).mpr (hle ((mem_iff_div_mem_goursatFst H₁.2).mp hp))
    · intro hle g hg
      exact mem_goursatFst.mpr (hle (mem_goursatFst.mp hg))

@[simp]
theorem coe_graphIdIciOrderIsoNormal_apply (H : Set.Ici (MonoidHom.id G).graph) :
    (graphIdIciOrderIsoNormal G H : Subgroup G) = H.1.goursatFst :=
  (rfl)

@[simp]
theorem coe_graphIdIciOrderIsoNormal_symm_mk (N : Subgroup G) [hN : N.Normal] :
    ((graphIdIciOrderIsoNormal G).symm ⟨N, hN⟩ : Subgroup (G × G)) = diagonalExt N :=
  (rfl)

/-- **The normalizer of the diagonal subgroup in `G × G`** consists of the pairs `(g, h)` whose
ratio `g / h` is central in `G`. -/
theorem normalizer_graph_id (G : Type*) [Group G] :
    normalizer ((MonoidHom.id G).graph : Set (G × G)) = diagonalExt (Subgroup.center G) := by
  ext ⟨g, h⟩
  rw [mem_normalizer_iff, mem_diagonalExt, Subgroup.mem_center_iff]
  constructor
  · intro hnorm y
    have hconj : g * (h⁻¹ * y * h) * g⁻¹ = h * (h⁻¹ * y * h) * h⁻¹ := by
      have hm := (hnorm (h⁻¹ * y * h, h⁻¹ * y * h)).mp rfl
      simpa only [SetLike.mem_coe, MonoidHom.mem_graph, MonoidHom.id_apply, Prod.mul_def,
        Prod.inv_mk] using hm
    calc
      y * (g / h) = (h * (h⁻¹ * y * h) * h⁻¹) * (g / h) := by
        simp only [div_eq_mul_inv]
        group
      _ = (g * (h⁻¹ * y * h) * g⁻¹) * (g / h) := by rw [hconj]
      _ = (g / h) * y := by
        simp only [div_eq_mul_inv]
        group
  · intro hc ⟨x, y⟩
    simp only [MonoidHom.mem_graph, MonoidHom.id_apply, Prod.mul_def, Prod.inv_mk]
    have hgx : g * x * g⁻¹ = h * x * h⁻¹ := by
      calc
        g * x * g⁻¹ = (g / h) * (h * x * h⁻¹) * (g / h)⁻¹ := by
          simp only [div_eq_mul_inv]
          group
        _ = (h * x * h⁻¹) * (g / h) * (g / h)⁻¹ := by rw [hc (h * x * h⁻¹)]
        _ = h * x * h⁻¹ := by group
    rw [hgx]
    exact ⟨fun hxy => hxy ▸ rfl, fun hconj => by
      calc
        x = h⁻¹ * (h * x * h⁻¹) * h := by group
        _ = h⁻¹ * (h * y * h⁻¹) * h := by rw [hconj]
        _ = y := by group⟩

/-- **When `G ⧸ Z(G)` has trivial center, `diagonalExt (center G)` is self-normalizing in
`G × G`.** -/
theorem normalizer_diagonalExt_center_of_center_quotient_eq_bot
    (hZ : Subgroup.center (G ⧸ Subgroup.center G) = ⊥) :
    normalizer (diagonalExt (Subgroup.center G) : Set (G × G)) =
      diagonalExt (Subgroup.center G) := by
  refine le_antisymm ?_ le_normalizer
  intro ⟨g, h⟩ hnorm
  rw [mem_diagonalExt, ← QuotientGroup.eq_one_iff]
  have hmem : (QuotientGroup.mk (g / h) : G ⧸ Subgroup.center G) ∈
      Subgroup.center (G ⧸ Subgroup.center G) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : (g * (h⁻¹ * y * h) * g⁻¹) / (h * (h⁻¹ * y * h) * h⁻¹) ∈ Subgroup.center G := by
      have hd : (h⁻¹ * y * h, h⁻¹ * y * h) ∈ diagonalExt (Subgroup.center G) :=
        graph_id_le_diagonalExt (Subgroup.center G) rfl
      exact mem_diagonalExt.mp ((mem_normalizer_iff.mp hnorm _).mp hd)
    have hq1 : (QuotientGroup.mk ((g * (h⁻¹ * y * h) * g⁻¹) / (h * (h⁻¹ * y * h) * h⁻¹)) :
        G ⧸ Subgroup.center G) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx
    have hq2 : (QuotientGroup.mk (g / h) : G ⧸ Subgroup.center G) * QuotientGroup.mk y *
        (QuotientGroup.mk (g / h))⁻¹ = QuotientGroup.mk y := by
      have hcalc : (g / h) * y * (g / h)⁻¹ * y⁻¹ =
          (g * (h⁻¹ * y * h) * g⁻¹) / (h * (h⁻¹ * y * h) * h⁻¹) := by
        simp only [div_eq_mul_inv]
        group
      have hdiv : (QuotientGroup.mk ((g / h) * y * (g / h)⁻¹ * y⁻¹) :
          G ⧸ Subgroup.center G) = 1 := hcalc ▸ hq1
      simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one] using hdiv
    calc
      (QuotientGroup.mk y : G ⧸ Subgroup.center G) * QuotientGroup.mk (g / h) =
          ((QuotientGroup.mk (g / h) : G ⧸ Subgroup.center G) * QuotientGroup.mk y *
            (QuotientGroup.mk (g / h))⁻¹) * QuotientGroup.mk (g / h) := by rw [hq2]
      _ = QuotientGroup.mk (g / h) * QuotientGroup.mk y := by group
  rwa [hZ, mem_bot] at hmem

end Subgroup
