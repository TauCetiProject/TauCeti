/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Basic
public import Mathlib.GroupTheory.Index

/-!
# Local stars, adjacent vertices, and vertex degrees in the Bass–Serre tree

In the Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` over `Γ`, the outgoing darts at a
vertex `p A_v` correspond bijectively to the disjoint union, over all darts `e` of `Γ` with
`src e = v`, of the left coset spaces `A_v ⧸ α_e(A_e)` (`GraphOfGroups.bassSerreStarEquiv`).
Because `X(𝔸, v₀)` is acyclic, the target map identifies the outgoing darts at any vertex `u` with
its adjacent vertices (`GraphOfGroups.bassSerreStarEquivAdjacent`), yielding the neighbour
bijection `GraphOfGroups.bassSerreAdjacentEquiv` sending `(e, a α_e(A_e))` to `(p a e) A_{tgt e}`
and the vertex degree formula `GraphOfGroups.card_bassSerreStar`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreDartOfSrcEq`: transported dart constructor for an arrow issuing
  from `v`.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`: canonical bijection between the star of `p A_v` in
  `X(𝔸, v₀)` and `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range`.
* `TauCeti.GraphOfGroups.bassSerreStarEquivAdjacent`: bijection between outgoing darts at a vertex
  of `X(𝔸, v₀)` and its adjacent vertices.
* `TauCeti.GraphOfGroups.bassSerreAdjacentEquiv`: canonical bijection identifying the neighbours of
  `p A_v` in `X(𝔸, v₀)`.

## Main results

* `TauCeti.GraphOfGroups.card_bassSerreStar`: when finitely many darts issue from `v` and each
  edge-group image has finite index in `A_v`, the degree of `p A_v` in `X(𝔸, v₀)` equals
  `∑_{src e = v} [A_v : α_e(A_e)]`.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5, pp. 6–7.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-- Transported dart constructor for an arrow `⟨e, he, rfl⟩` issuing from `v`. -/
def bassSerreDartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).E :=
  𝔸.bassSerreDart v₀ e (he.symm ▸ p)

variable {𝔸 v₀}

@[simp] theorem bassSerreDartOfSrcEq_rfl (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.bassSerreDartOfSrcEq v₀ e rfl p = 𝔸.bassSerreDart v₀ e p :=
  (rfl)

@[simp] theorem bassSerreTree_src_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDartOfSrcEq v₀ e he p) = 𝔸.bassSerreVertex v₀ p := by
  subst he
  exact bassSerreTree_src_dart e p

@[simp] theorem bassSerreTree_tgt_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.bassSerreDartOfSrcEq v₀ e he p) =
      𝔸.bassSerreVertex v₀ (p.cons (Letter.dart ⟨e, he, rfl⟩)) := by
  subst he
  rw [← Γ.dart_def]
  exact bassSerreTree_tgt_dart e p

@[simp] theorem bassSerreTypeHom_mapE_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (𝔸.bassSerreDartOfSrcEq v₀ e he p) = e := by
  subst he
  exact bassSerreTypeHom_mapE e p

private theorem bassSerreDartOfSrcEq_cons_eq_iff (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a₁ a₂ : 𝔸.vertexGroup v) :
    𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₁)) =
      𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₂)) ↔
      (a₁ : 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e, he, rfl⟩).range) = a₂ := by
  subst he
  rw [bassSerreDartOfSrcEq_rfl, bassSerreDartOfSrcEq_rfl, bassSerreDart_eq_iff, QuotientGroup.eq,
    MonoidHom.mem_range, αArrow_mk]
  refine ⟨fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩, fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩⟩
  · have hmul : Path.Homotopic (p.cons (Letter.vertex a₁))
        (p.cons (Letter.vertex (a₂ * 𝔸.α e c))) :=
      hc.trans (Path.Homotopic.mul p a₂ (𝔸.α e c))
    have hkey : ∀ x y : 𝔸.vertexGroup (Γ.src e),
        Path.Homotopic (p.cons (Letter.vertex x)) (p.cons (Letter.vertex y)) → x = y := by
      intro x y hxy
      rw [← Path.comp_ofVertex, ← Path.comp_ofVertex] at hxy
      have hx : Path.Homotopic (p.reverse.comp (p.comp (Path.ofVertex x))) (Path.ofVertex x) := by
        simpa using Path.Homotopic.comp_reverse_comp_comp .nil p (Path.ofVertex x)
      have hy : Path.Homotopic (p.reverse.comp (p.comp (Path.ofVertex y))) (Path.ofVertex y) := by
        simpa using Path.Homotopic.comp_reverse_comp_comp .nil p (Path.ofVertex y)
      exact Path.ofVertex_homotopic_ofVertex_iff.mp
        (hx.symm.trans ((hxy.comp_left p.reverse).trans hy))
    have ha : a₁ = a₂ * 𝔸.α e c := hkey _ _ hmul
    rw [ha, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  · have ha : a₁ = a₂ * 𝔸.α e c⁻¹ := by
      rw [map_inv, hc, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [ha]
    exact (Path.Homotopic.mul p a₂ (𝔸.α e c⁻¹)).symm

private def starFromCosets {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) →
      {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} :=
  fun ⟨e, q⟩ => Quotient.liftOn' q
    (fun a => ⟨𝔸.bassSerreDartOfSrcEq v₀ e.1 e.2 (p.cons (Letter.vertex a)), by simp⟩)
    (fun a₁ a₂ h => Subtype.ext <| (bassSerreDartOfSrcEq_cons_eq_iff e.1 e.2 p a₁ a₂).mpr
      (Quotient.sound h))

private theorem starFromCosets_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (starFromCosets p) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨e₁, he₁⟩, q₁⟩ ⟨⟨e₂, he₂⟩, q₂⟩ h
    refine Quotient.inductionOn₂' q₁ q₂ (fun a₁ a₂ h => ?_) h
    have hval : 𝔸.bassSerreDartOfSrcEq v₀ e₁ he₁ (p.cons (Letter.vertex a₁)) =
        𝔸.bassSerreDartOfSrcEq v₀ e₂ he₂ (p.cons (Letter.vertex a₂)) := congrArg Subtype.val h
    have he_eq : e₁ = e₂ := by
      simpa using congrArg (𝔸.bassSerreTypeHom v₀).mapE hval
    subst he_eq
    obtain rfl : he₁ = he₂ := Subsingleton.elim _ _
    exact Sigma.ext rfl (heq_of_eq ((bassSerreDartOfSrcEq_cons_eq_iff e₁ he₁ p a₁ a₂).mp hval))
  · rintro ⟨E, hE⟩
    revert hE
    refine bassSerreDart_induction E fun e₀ q hE => ?_
    have hsrc : 𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p :=
      (bassSerreTree_src_dart e₀ q).symm.trans hE
    have he₀ : Γ.src e₀ = v := (bassSerreVertex_eq_iff_exists_eq.mp hsrc).choose
    -- Generalize `v` along `he₀` so `q` and `p` share the same endpoint without casts.
    have key : ∀ (w : Γ.V), Γ.src e₀ = w → ∀ (p_w : 𝔸.Path ⟨v₀⟩ ⟨w⟩),
        𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p_w →
        ∃ x, (starFromCosets p_w x).1 = 𝔸.bassSerreDart v₀ e₀ q := by
      intro w hw p_w hsrc_w
      subst hw
      obtain ⟨a, ha⟩ := bassSerreVertex_eq_iff.mp hsrc_w
      exact ⟨⟨⟨e₀, rfl⟩, a⟩, (bassSerreDart_congr ha).symm⟩
    obtain ⟨x, hx⟩ := key v he₀ p hsrc
    exact ⟨x, Subtype.ext hx⟩

variable (𝔸 v₀) in
/-- The star of a vertex `p A_v` in `X(𝔸, v₀)` is in bijection with the disjoint union, over all
darts `e` of `Γ` with `src e = v`, of the left coset spaces `A_v ⧸ α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range :=
  (Equiv.ofBijective (starFromCosets p) (starFromCosets_bijective p)).symm

@[simp] theorem bassSerreStarEquiv_symm_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    ((𝔸.bassSerreStarEquiv v₀ p).symm ⟨e, a⟩).1 =
      𝔸.bassSerreDartOfSrcEq v₀ e.1 e.2 (p.cons (Letter.vertex a)) :=
  (rfl)

variable (𝔸 v₀) in
/-- Because `X(𝔸, v₀)` is acyclic, the target map identifies the outgoing darts at any vertex `u`
with the adjacent vertices `{w // Nonempty (u ⟶ w)}`. -/
noncomputable def bassSerreStarEquivAdjacent (u : (𝔸.bassSerreTree v₀).V) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = u} ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (u ⟶ w)} :=
  Equiv.ofBijective (fun E => ⟨(𝔸.bassSerreTree v₀).tgt E.1, ⟨⟨E.1, E.2, rfl⟩⟩⟩)
    ⟨fun ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ h => Subtype.ext <| by
      have htgt : (𝔸.bassSerreTree v₀).tgt E₁ = (𝔸.bassSerreTree v₀).tgt E₂ :=
        congrArg Subtype.val h
      let f₁ : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ := ⟨E₁, h₁, rfl⟩
      let f₂ : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ := ⟨E₂, h₂, htgt.symm⟩
      have hpath := (𝔸.bassSerreGraph_isAcyclic v₀).eq_of_isReduced
        (SerreGraph.Path.isReduced_toPath _ f₁) (SerreGraph.Path.isReduced_toPath _ f₂)
      injection hpath with _ _ _ hf
      exact congrArg (fun f : u ⟶ (𝔸.bassSerreTree v₀).tgt E₁ => f.1) hf,
     fun ⟨w, ⟨f⟩⟩ => ⟨⟨f.1, f.2.1⟩, Subtype.ext f.2.2⟩⟩

@[simp] theorem bassSerreStarEquivAdjacent_apply (u : (𝔸.bassSerreTree v₀).V)
    (E : {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = u}) :
    (𝔸.bassSerreStarEquivAdjacent v₀ u E).1 = (𝔸.bassSerreTree v₀).tgt E.1 :=
  (rfl)

variable (𝔸 v₀) in
/-- The vertices of `X(𝔸, v₀)` adjacent to `p A_v` correspond bijectively to pairs `(e, a α_e(A_e))`
with `src e = v`, sending `(e, a α_e(A_e))` to `(p a e) A_{tgt e}`. -/
noncomputable def bassSerreAdjacentEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (𝔸.bassSerreVertex v₀ p ⟶ w)} :=
  (𝔸.bassSerreStarEquiv v₀ p).symm.trans
    (𝔸.bassSerreStarEquivAdjacent v₀ (𝔸.bassSerreVertex v₀ p))

@[simp] theorem bassSerreAdjacentEquiv_apply {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    (𝔸.bassSerreAdjacentEquiv v₀ p ⟨e, a⟩).1 =
      𝔸.bassSerreVertex v₀ ((p.cons (Letter.vertex a)).cons (Letter.dart ⟨e.1, e.2, rfl⟩)) :=
  bassSerreTree_tgt_dartOfSrcEq e.1 e.2 (p.cons (Letter.vertex a))

/-- When finitely many darts issue from `v` in `Γ` and each edge-group image has finite index in
`A_v`, the degree of `p A_v` in `X(𝔸, v₀)` is `∑_{src e = v} [A_v : α_e(A_e)]`. -/
theorem card_bassSerreStar {v : Γ.V} [Fintype {e : Γ.E // Γ.src e = v}]
    [∀ e : {e : Γ.E // Γ.src e = v}, Finite (𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range)]
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Nat.card {E : (𝔸.bassSerreTree v₀).E //
      (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} =
      ∑ e : {e : Γ.E // Γ.src e = v}, (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range.index := by
  rw [Nat.card_congr (𝔸.bassSerreStarEquiv v₀ p), Nat.card_sigma]
  exact Finset.sum_congr rfl fun _ _ => (Subgroup.index_eq_card _).symm

end GraphOfGroups

end TauCeti
