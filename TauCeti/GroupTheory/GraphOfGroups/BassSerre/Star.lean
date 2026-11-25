/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Tree

/-!
# Outgoing stars and vertex degrees of Bass–Serre trees

For a graph of groups `𝔸` over a Serre graph `Γ` and a base vertex `a : Γ.V`, the outgoing darts of
the Bass–Serre tree `X(𝔸, a) = bassSerreTree 𝔸 a` at a vertex `p A_b` decompose over the darts
`e : b ⟶ c` of `Γ` starting at `b`:

* The darts starting at `p A_b` that project to `e` correspond bijectively to the left cosets
  `A_b / α_e(A_e)`, via `g α_e(A_e) ↦ (p g) α_e(A_e)` (`bassSerreOutDartEquiv`).
* Summing over all outgoing darts of `Γ` at `b` identifies the full outgoing star of `p A_b` in
  `X(𝔸, a)` with `Σ e : {e : Γ.E // Γ.src e = b}, A_b / α_e(A_e)` (`bassSerreStarEquiv`).
* Passing to cardinals and `Nat.card` expresses the degree of any vertex `y` of `X(𝔸, a)` over
  `b = (bassSerreProjection 𝔸 a).mapV y` as the sum of the coset cardinals or subgroup indices
  `[A_b : α_e(A_e)]` (`mk_src_eq_bassSerreTree`, `card_src_eq_bassSerreTree`).

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreOutDartEquiv`: bijection between `A_b / α_e(A_e)` and the
  outgoing darts of `X(𝔸, a)` at `p A_b` over `e`.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`: bijection between
  `Σ e : {e : Γ.E // Γ.src e = b}, A_b / α_e(A_e)` and the outgoing star at `p A_b`.

## Main results

* `TauCeti.GraphOfGroups.mk_src_eq_bassSerreTree`: cardinal formula for the outgoing star of any
  vertex of `X(𝔸, a)`.
* `TauCeti.GraphOfGroups.card_src_eq_bassSerreTree`: finite degree formula as the sum of subgroup
  indices `[A_b : α_e(A_e)]`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5.
-/

public section

universe u v w x

namespace TauCeti.GraphOfGroups

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {a : Γ.V}

/-- Every dart of `X(𝔸, a)` starting at `p A_b` is represented by extending `p` by an element of
`A_b`. -/
private theorem exists_bassSerreDart_of_src_eq {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    {d : (bassSerreTree 𝔸 a).E} (hd : (bassSerreTree 𝔸 a).src d = bassSerreVertex p) :
    ∃ (c : Γ.V) (e : b ⟶ c) (g : 𝔸.vertexGroup b),
      d = bassSerreDart (p.cons (.vertex g)) e := by
  obtain ⟨b', c, q, e, rfl⟩ := bassSerreDart_surjective d
  have hb : b' = b := by simpa using congrArg (bassSerreProjection 𝔸 a).mapV hd
  subst hb
  obtain ⟨g, hq⟩ := bassSerreVertex_eq_bassSerreVertex_iff.1 (by simpa using hd.symm)
  exact ⟨c, e, g, bassSerreDart_congr hq e⟩

private noncomputable def bassSerreOutDartMap {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (q : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range) :
    {d : (bassSerreTree 𝔸 a).E //
      (bassSerreTree 𝔸 a).src d = bassSerreVertex p ∧
        (bassSerreProjection 𝔸 a).mapE d = e.val} :=
  Quotient.liftOn' q
    (fun g : 𝔸.vertexGroup b ↦
      ⟨bassSerreDart (p.cons (.vertex g)) e,
        (src_bassSerreDart _ _).trans (bassSerreVertex_cons_vertex p g),
        bassSerreProjection_mapE_bassSerreDart _ _⟩)
    fun g₁ g₂ h ↦ by
      obtain ⟨c₀, hc₀⟩ : g₁⁻¹ * g₂ ∈ (𝔸.αArrow e).range := QuotientGroup.leftRel_apply.1 h
      apply Subtype.ext
      rw [eq_mul_of_inv_mul_eq hc₀.symm]
      exact bassSerreDart_eq_bassSerreDart_iff.2 ⟨c₀, (Path.Homotopic.mul p g₁ _).symm⟩

private theorem bassSerreOutDartMap_bijective {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    Function.Bijective (bassSerreOutDartMap p e) := by
  refine ⟨fun x₁ x₂ h ↦ ?_, fun ⟨d, hsrc, hproj⟩ ↦ ?_⟩
  · induction x₁ using QuotientGroup.induction_on with | H g₁
    induction x₂ using QuotientGroup.induction_on with | H g₂
    obtain ⟨c₀, hc₀⟩ := bassSerreDart_eq_bassSerreDart_iff.1 (congrArg Subtype.val h)
    have hhom : Path.Homotopic (Path.ofVertex g₂) (Path.ofVertex (g₁ * 𝔸.αArrow e c₀)) := by
      refine (Path.Homotopic.comp_left_iff (p := p)).1 ?_
      rw [Path.comp_ofVertex, Path.comp_ofVertex]
      exact hc₀.trans (Path.Homotopic.mul p g₁ _)
    have hg : g₂ = g₁ * 𝔸.αArrow e c₀ := Path.ofVertex_homotopic_ofVertex_iff.1 hhom
    exact QuotientGroup.eq.2 (MonoidHom.mem_range.2 ⟨c₀, by rw [hg, inv_mul_cancel_left]⟩)
  · obtain ⟨c', e', g, rfl⟩ := exists_bassSerreDart_of_src_eq p hsrc
    have he' : e'.val = e.val := (bassSerreProjection_mapE_bassSerreDart _ _).symm.trans hproj
    have hc' : c' = c := e'.property.2.symm.trans ((congrArg Γ.tgt he').trans e.property.2)
    subst hc'
    obtain rfl : e = e' := (Subtype.ext he').symm
    exact ⟨(g : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range), Subtype.ext (rfl)⟩

/-- Outgoing darts of `X(𝔸, a)` at `p A_b` lifting a fixed arrow `e : b ⟶ c` correspond to left
cosets `A_b / α_e(A_e)`, via `g α_e(A_e) ↦ (p g) α_e(A_e)`. -/
noncomputable def bassSerreOutDartEquiv {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c) :
    𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range ≃
      {d : (bassSerreTree 𝔸 a).E //
        (bassSerreTree 𝔸 a).src d = bassSerreVertex p ∧
          (bassSerreProjection 𝔸 a).mapE d = e.val} :=
  Equiv.ofBijective (bassSerreOutDartMap p e) (bassSerreOutDartMap_bijective p e)

@[simp] theorem bassSerreOutDartEquiv_mk_val {b c : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (e : b ⟶ c)
    (g : 𝔸.vertexGroup b) :
    (bassSerreOutDartEquiv p e (g : 𝔸.vertexGroup b ⧸ (𝔸.αArrow e).range)).val =
      bassSerreDart (p.cons (.vertex g)) e := by
  rw [bassSerreOutDartEquiv, Equiv.ofBijective_apply]
  rfl

/-- The outgoing star of `p A_b` in `X(𝔸, a)` decomposes over the darts of `Γ` starting at `b` into
the coset spaces `A_b / α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (Σ e : {e : Γ.E // Γ.src e = b},
      𝔸.vertexGroup b ⧸ (𝔸.αArrow (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val)).range) ≃
      {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = bassSerreVertex p} :=
  (Equiv.sigmaCongrRight fun e : {e : Γ.E // Γ.src e = b} ↦
    ((bassSerreOutDartEquiv p (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun d : (bassSerreTree 𝔸 a).E ↦ (bassSerreTree 𝔸 a).src d = bassSerreVertex p)
        (fun d : (bassSerreTree 𝔸 a).E ↦ (bassSerreProjection 𝔸 a).mapE d = e.val)).symm).trans
      (Equiv.subtypeEquivRight fun _ ↦ ⟨fun h ↦ Subtype.ext h, congrArg Subtype.val⟩)).trans
    (Equiv.sigmaFiberEquiv fun d : {d : (bassSerreTree 𝔸 a).E //
        (bassSerreTree 𝔸 a).src d = bassSerreVertex p} ↦
      (⟨(bassSerreProjection 𝔸 a).mapE d.val,
        ((bassSerreProjection 𝔸 a).map_src d.val).trans
          ((congrArg (bassSerreProjection 𝔸 a).mapV d.property).trans
            (bassSerreProjection_mapV_bassSerreVertex p))⟩ : {e : Γ.E // Γ.src e = b}))

@[simp] theorem bassSerreStarEquiv_mk_val {b : Γ.V} (p : 𝔸.Path ⟨a⟩ ⟨b⟩)
    (e : {e : Γ.E // Γ.src e = b}) (g : 𝔸.vertexGroup b) :
    (bassSerreStarEquiv p ⟨e, (g : 𝔸.vertexGroup b ⧸ _)⟩).val =
      bassSerreDart (p.cons (.vertex g)) (⟨e.val, e.property, rfl⟩ : b ⟶ Γ.tgt e.val) := by
  simp [bassSerreStarEquiv]

/-- Cardinality of the outgoing star of a vertex `y` in `X(𝔸, a)` with underlying vertex
`b = (bassSerreProjection 𝔸 a).mapV y`, as the sum of the coset cardinals `#(A_b / α_e(A_e))` over
outgoing darts `e` at `b`. -/
theorem mk_src_eq_bassSerreTree (y : (bassSerreTree 𝔸 a).V) :
    Cardinal.mk {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
      Cardinal.lift.{u} (Cardinal.sum
        fun e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y} ↦
          Cardinal.mk (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)) := by
  induction y using bassSerreVertex_induction_on with | h p
  rw [bassSerreProjection_mapV_bassSerreVertex, ← Cardinal.mk_sigma, ← Cardinal.mk_uLift]
  exact Cardinal.mk_congr ((bassSerreStarEquiv p).symm.trans Equiv.ulift.symm)

/-- When `b = (bassSerreProjection 𝔸 a).mapV y` has finitely many outgoing darts in `Γ` and each
edge group image at `b` has finite index in `A_b`, the degree of `y` in `X(𝔸, a)` is the sum of the
subgroup indices `[A_b : α_e(A_e)]`. -/
theorem card_src_eq_bassSerreTree (y : (bassSerreTree 𝔸 a).V)
    [Fintype {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y}]
    [∀ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
      Finite (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
        (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
          (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)] :
    Nat.card {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
      ∑ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
        (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
          (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range.index := by
  have h := @bassSerreVertex_induction_on _ _ _
    (fun y ↦
      ∀ [Fintype {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y}]
        [∀ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
          Finite (𝔸.vertexGroup ((bassSerreProjection 𝔸 a).mapV y) ⧸
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range)],
        Nat.card {d : (bassSerreTree 𝔸 a).E // (bassSerreTree 𝔸 a).src d = y} =
          ∑ e : {e : Γ.E // Γ.src e = (bassSerreProjection 𝔸 a).mapV y},
            (𝔸.αArrow (⟨e.val, e.property, rfl⟩ :
              (bassSerreProjection 𝔸 a).mapV y ⟶ Γ.tgt e.val)).range.index)
    y fun p ↦ by
      rw [bassSerreProjection_mapV_bassSerreVertex]
      intro _ _
      rw [Nat.card_congr (bassSerreStarEquiv p).symm, Nat.card_sigma]
      simp_rw [Subgroup.index_eq_card]
  exact h

end TauCeti.GraphOfGroups
