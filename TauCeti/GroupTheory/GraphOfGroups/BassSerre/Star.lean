/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.GroupTheory.Index
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Local stars, adjacent vertices, and vertex degrees in the Bass–Serre tree

In the Bass–Serre tree `X(𝔸, v₀)` of a graph of groups `𝔸` over `Γ`, the outgoing darts at `p A_v`
correspond bijectively to `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ α_e(A_e)`
(`GraphOfGroups.bassSerreStarEquiv`). Acyclicity identifies outgoing darts with adjacent vertices
(`SerreGraph.IsAcyclic.starEquivAdjacent`), giving `GraphOfGroups.bassSerreAdjacentEquiv` and the
degree formula `GraphOfGroups.card_bassSerreStar`. Specializing to one-edge graphs gives
`segmentStarEquiv`, `segmentAdjacentEquiv`, `coprodStarEquiv`, `coprodAdjacentEquiv`, and
`card_star_loop`.

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreDartOfSrcEq`: transported dart constructor for an arrow from `v`.
* `TauCeti.GraphOfGroups.bassSerreStarEquiv`, `TauCeti.GraphOfGroups.bassSerreAdjacentEquiv`:
  bijections identifying the star and neighbours of `p A_v` in `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.segmentStarEquiv`, `TauCeti.GraphOfGroups.segmentAdjacentEquiv`,
  `TauCeti.GraphOfGroups.coprodStarEquiv`, `TauCeti.GraphOfGroups.coprodAdjacentEquiv`:
  star and neighbour bijections for graphs of groups over `SerreGraph.segment` and `A ∗ B`.

## Main results

* `TauCeti.GraphOfGroups.bassSerreDartOfSrcEq_cons_eq_iff`,
  `TauCeti.GraphOfGroups.bassSerreDart_cons_eq_iff`: left-coset criteria for outgoing darts.
* `TauCeti.GraphOfGroups.card_bassSerreStar`,
  `TauCeti.GraphOfGroups.card_bassSerreStar_bassSerreVertex`: vertex degree formulas in `X(𝔸, v₀)`.
* `TauCeti.GraphOfGroups.card_star_loop`: every vertex in the Bass–Serre tree of
  `GraphOfGroups.loop f g hf hg` with finite-index associated subgroups has degree
  `[G : f(C)] + [G : g(C)]`.

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
    𝔸.bassSerreDartOfSrcEq v₀ e rfl p = 𝔸.bassSerreDart v₀ e p := (rfl)

@[simp] theorem bassSerreTree_src_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDartOfSrcEq v₀ e he p) = 𝔸.bassSerreVertex v₀ p := by
  subst he; exact bassSerreTree_src_dart e p

@[simp] theorem bassSerreTree_tgt_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTree v₀).tgt (𝔸.bassSerreDartOfSrcEq v₀ e he p) =
      𝔸.bassSerreVertex v₀ (p.cons (Letter.dart ⟨e, he, rfl⟩)) := by
  subst he; rw [← Γ.dart_def]; exact bassSerreTree_tgt_dart e p

@[simp] theorem bassSerreTypeHom_mapE_dartOfSrcEq (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (𝔸.bassSerreTypeHom v₀).mapE (𝔸.bassSerreDartOfSrcEq v₀ e he p) = e := by
  subst he; exact bassSerreTypeHom_mapE e p

/-- Two outgoing darts at `p A_v` over the same dart `e` of `Γ` agree if and only if their vertex
group labels lie in the same left coset of `α_e(A_e)`. -/
theorem bassSerreDartOfSrcEq_cons_eq_iff (e : Γ.E) {v : Γ.V} (he : Γ.src e = v)
    (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) (a₁ a₂ : 𝔸.vertexGroup v) :
    𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₁)) =
      𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a₂)) ↔
      (a₁ : 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e, he, rfl⟩).range) = a₂ := by
  subst he
  rw [bassSerreDartOfSrcEq_rfl, bassSerreDartOfSrcEq_rfl, bassSerreDart_eq_iff, QuotientGroup.eq,
    MonoidHom.mem_range, αArrow_mk]
  refine ⟨fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩, fun ⟨c, hc⟩ => ⟨c⁻¹, ?_⟩⟩
  · have ha : a₁ = a₂ * 𝔸.α e c := π₁.vertexHom_injective p <| by
      rw [π₁.vertexHom_apply, π₁.vertexHom_apply, π₁.mk_eq_mk_iff]
      simpa only [Path.comp_ofVertex] using
        (hc.trans (Path.Homotopic.mul p a₂ (𝔸.α e c))).comp_right p.reverse
    simp [ha]
  · have ha : a₁ = a₂ * 𝔸.α e c⁻¹ := by simp [hc]
    rw [ha]
    exact (Path.Homotopic.mul p a₂ (𝔸.α e c⁻¹)).symm

/-- Two darts over `e` extending `p` by vertex group elements `a₁, a₂ ∈ A_{src e}` agree if and only
if `a₁` and `a₂` lie in the same left coset of `α_e(A_e)`. -/
theorem bassSerreDart_cons_eq_iff (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a₁ a₂ : 𝔸.vertexGroup (Γ.src e)) :
    𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a₁)) =
      𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a₂)) ↔
      (a₁ : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range) = a₂ := by
  rw [← bassSerreDartOfSrcEq_rfl, ← bassSerreDartOfSrcEq_rfl, bassSerreDartOfSrcEq_cons_eq_iff,
    QuotientGroup.eq, QuotientGroup.eq, αArrow_mk]

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
    have he_eq : e₁ = e₂ := by simpa using congrArg (𝔸.bassSerreTypeHom v₀).mapE hval
    subst he_eq
    obtain rfl : he₁ = he₂ := Subsingleton.elim _ _
    exact Sigma.ext rfl (heq_of_eq ((bassSerreDartOfSrcEq_cons_eq_iff e₁ he₁ p a₁ a₂).mp hval))
  · rintro ⟨E, hE⟩
    revert hE
    refine bassSerreDart_induction_on E fun e₀ q hE => ?_
    have hsrc : 𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p :=
      (bassSerreTree_src_dart e₀ q).symm.trans hE
    -- Generalize `v` along `Γ.src e₀ = v` so `q` and `p` share the same endpoint without casts.
    have key : ∀ (w : Γ.V), Γ.src e₀ = w → ∀ (p_w : 𝔸.Path ⟨v₀⟩ ⟨w⟩),
        𝔸.bassSerreVertex v₀ q = 𝔸.bassSerreVertex v₀ p_w →
        ∃ x, (starFromCosets p_w x).1 = 𝔸.bassSerreDart v₀ e₀ q := by
      rintro _ rfl p_w hsrc_w
      obtain ⟨a, ha⟩ := bassSerreVertex_eq_iff.mp hsrc_w
      exact ⟨⟨⟨e₀, rfl⟩, a⟩, (bassSerreDart_congr ha).symm⟩
    obtain ⟨x, hx⟩ := key v (bassSerreVertex_eq_iff_exists_eq.mp hsrc).choose p hsrc
    exact ⟨x, Subtype.ext hx⟩

variable (𝔸 v₀) in
/-- The star of a vertex `p A_v` in `X(𝔸, v₀)` is in bijection with the disjoint union, over all
darts `e` of `Γ` with `src e = v`, of the left coset spaces `A_v ⧸ α_e(A_e)`. -/
noncomputable def bassSerreStarEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range :=
  (Equiv.ofBijective (starFromCosets p) (starFromCosets_bijective p)).symm

@[simp] theorem bassSerreStarEquiv_symm_apply_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    ((𝔸.bassSerreStarEquiv v₀ p).symm ⟨e, a⟩).1 =
      𝔸.bassSerreDartOfSrcEq v₀ e.1 e.2 (p.cons (Letter.vertex a)) := (rfl)

@[simp] theorem bassSerreStarEquiv_apply_dartOfSrcEq {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : Γ.E) (he : Γ.src e = v) (a : 𝔸.vertexGroup v)
    (h : (𝔸.bassSerreTree v₀).src
      (𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a))) =
      𝔸.bassSerreVertex v₀ p) :
    𝔸.bassSerreStarEquiv v₀ p
      ⟨𝔸.bassSerreDartOfSrcEq v₀ e he (p.cons (Letter.vertex a)), h⟩ = ⟨⟨e, he⟩, a⟩ :=
  (Equiv.eq_symm_apply _).mp (Subtype.ext (bassSerreStarEquiv_symm_apply_val p ⟨e, he⟩ a).symm)

@[simp] theorem bassSerreStarEquiv_apply_dartOfSrcEq_self {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : Γ.E) (he : Γ.src e = v)
    (h : (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDartOfSrcEq v₀ e he p) =
      𝔸.bassSerreVertex v₀ p) :
    𝔸.bassSerreStarEquiv v₀ p ⟨𝔸.bassSerreDartOfSrcEq v₀ e he p, h⟩ =
      ⟨⟨e, he⟩, QuotientGroup.mk (1 : 𝔸.vertexGroup v)⟩ := by
  subst he
  exact (Equiv.eq_symm_apply _).mp (Subtype.ext (bassSerreDart_congr (Path.Homotopic.one p)).symm)

@[simp] theorem bassSerreStarEquiv_apply_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (a : 𝔸.vertexGroup (Γ.src e))
    (h : (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a))) =
      𝔸.bassSerreVertex v₀ p) :
    𝔸.bassSerreStarEquiv v₀ p
      ⟨𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a)), h⟩ = ⟨⟨e, rfl⟩, a⟩ :=
  bassSerreStarEquiv_apply_dartOfSrcEq p e rfl a h

@[simp] theorem bassSerreStarEquiv_apply_dart_self (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (h : (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e p) = 𝔸.bassSerreVertex v₀ p) :
    𝔸.bassSerreStarEquiv v₀ p ⟨𝔸.bassSerreDart v₀ e p, h⟩ =
      ⟨⟨e, rfl⟩, QuotientGroup.mk (1 : 𝔸.vertexGroup (Γ.src e))⟩ :=
  bassSerreStarEquiv_apply_dartOfSrcEq_self p e rfl h

@[simp] theorem bassSerreStarEquiv_apply_fst_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (E : {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p}) :
    ((𝔸.bassSerreStarEquiv v₀ p E).1).1 = (𝔸.bassSerreTypeHom v₀).mapE E.1 := by
  obtain ⟨⟨e, q⟩, rfl⟩ := (𝔸.bassSerreStarEquiv v₀ p).symm.surjective E
  exact Quotient.inductionOn' q fun _ => by simp

variable (𝔸 v₀) in
/-- The vertices of `X(𝔸, v₀)` adjacent to `p A_v` correspond bijectively to pairs `(e, a α_e(A_e))`
with `src e = v`, sending `(e, a α_e(A_e))` to `(p a e) A_{tgt e}`. -/
noncomputable def bassSerreAdjacentEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    (Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (𝔸.bassSerreVertex v₀ p ⟶ w)} :=
  (𝔸.bassSerreStarEquiv v₀ p).symm.trans
    ((𝔸.bassSerreTree v₀).isTree.isAcyclic.starEquivAdjacent (𝔸.bassSerreVertex v₀ p))

@[simp] theorem bassSerreAdjacentEquiv_apply_val {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (e : {e : Γ.E // Γ.src e = v}) (a : 𝔸.vertexGroup v) :
    (𝔸.bassSerreAdjacentEquiv v₀ p ⟨e, a⟩).1 =
      𝔸.bassSerreVertex v₀ ((p.cons (Letter.vertex a)).cons (Letter.dart ⟨e.1, e.2, rfl⟩)) := by
  rw [bassSerreAdjacentEquiv, Equiv.trans_apply, SerreGraph.IsAcyclic.starEquivAdjacent_apply_val,
    bassSerreStarEquiv_symm_apply_val, bassSerreTree_tgt_dartOfSrcEq]

/-- When each edge-group image at `(𝔸.bassSerreTypeHom v₀).mapV u` has finite index, the degree of
`u` in `X(𝔸, v₀)` is `∑ᶠ e : {e : Γ.E // Γ.src e = mapV u}, [A_{src e} : α_e(A_e)]`. If infinitely
many darts issue from `mapV u` in `Γ`, both sides are `0`. -/
theorem card_bassSerreStar (u : (𝔸.bassSerreTree v₀).V)
    [hfin : ∀ e : {e : Γ.E // Γ.src e = (𝔸.bassSerreTypeHom v₀).mapV u},
      (𝔸.α e.1).range.FiniteIndex] :
    Nat.card {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = u} =
      ∑ᶠ e : {e : Γ.E // Γ.src e = (𝔸.bassSerreTypeHom v₀).mapV u}, (𝔸.α e.1).range.index := by
  obtain ⟨v, p, rfl⟩ : ∃ (v : Γ.V) (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩), 𝔸.bassSerreVertex v₀ p = u :=
    bassSerreVertex_induction_on u fun p => ⟨_, p, rfl⟩
  have : ∀ e : {e : Γ.E // Γ.src e = v},
      Finite (𝔸.vertexGroup v ⧸ (𝔸.αArrow ⟨e.1, e.2, rfl⟩).range) := by
    rintro ⟨e, rfl⟩; rw [αArrow_mk]; have := hfin ⟨e, (bassSerreTypeHom_mapV p).symm⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  let eStar : {e : Γ.E // Γ.src e = (𝔸.bassSerreTypeHom v₀).mapV (𝔸.bassSerreVertex v₀ p)} ≃
      {e : Γ.E // Γ.src e = v} :=
    Equiv.subtypeEquivRight fun _ => by rw [bassSerreTypeHom_mapV]
  rw [Nat.card_congr (𝔸.bassSerreStarEquiv v₀ p), Nat.card_sigma_eq_finsum,
    ← finsum_comp_equiv eStar]
  refine finsum_congr fun ⟨e, he⟩ => ?_
  have hv : Γ.src e = v := he.trans (bassSerreTypeHom_mapV p)
  subst hv; rw [← Subgroup.index_eq_card]; exact congrArg (·.range.index) (𝔸.αArrow_mk e)

/-- When finitely many darts issue from `v` in `Γ` and each edge-group image has finite index in
`A_v`, the degree of `p A_v` in `X(𝔸, v₀)` is `∑_{src e = v} [A_v : α_e(A_e)]`. -/
theorem card_bassSerreStar_bassSerreVertex {v : Γ.V} [Fintype {e : Γ.E // Γ.src e = v}]
    [hfin : ∀ e : {e : Γ.E // Γ.src e = v}, (𝔸.α e.1).range.FiniteIndex] (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Nat.card {E : (𝔸.bassSerreTree v₀).E //
      (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} =
      ∑ e : {e : Γ.E // Γ.src e = v}, (𝔸.α e.1).range.index := by
  have : ∀ e : {e : Γ.E // Γ.src e = (𝔸.bassSerreTypeHom v₀).mapV (𝔸.bassSerreVertex v₀ p)},
      (𝔸.α e.1).range.FiniteIndex := fun e => hfin ⟨e.1, e.2.trans (bassSerreTypeHom_mapV p)⟩
  rw [card_bassSerreStar (𝔸.bassSerreVertex v₀ p),
    ← finsum_comp_equiv (Equiv.subtypeEquivRight fun _ => by rw [bassSerreTypeHom_mapV]),
    finsum_eq_sum_of_fintype]; rfl

/-! ### Stars and degrees for one-edge graphs of groups -/

section Segment

variable (𝔸 : GraphOfGroups.{0, 0, w, x} SerreGraph.segment)
  (v₀ : SerreGraph.segment.V) (e : SerreGraph.segment.E)

/-- For any graph of groups `𝔸` over the segment, the outgoing darts at `p A_{src e}` in `X(𝔸, v₀)`
correspond bijectively to the left coset space `A_{src e} ⧸ α_e(A_e)`. -/
noncomputable def segmentStarEquiv (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩) :
    {E : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src E = 𝔸.bassSerreVertex v₀ p} ≃
      𝔸.vertexGroup (SerreGraph.segment.src e) ⧸ (𝔸.α e).range :=
  ((𝔸.bassSerreStarEquiv v₀ p).trans (Equiv.uniqueSigma _)).trans
    (Subgroup.quotientEquivOfEq <| by
      rw [Subsingleton.elim (default : {d : SerreGraph.segment.E //
        SerreGraph.segment.src d = SerreGraph.segment.src e}) ⟨e, rfl⟩, αArrow_mk])

/-- For any graph of groups `𝔸` over the segment, the neighbours of `p A_{src e}` in `X(𝔸, v₀)`
correspond bijectively to `A_{src e} ⧸ α_e(A_e)`, sending `a α_e(A_e)` to `(p · a · e) A_{tgt e}`.
-/
noncomputable def segmentAdjacentEquiv (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩) :
    𝔸.vertexGroup (SerreGraph.segment.src e) ⧸ (𝔸.α e).range ≃
      {w : (𝔸.bassSerreTree v₀).V // Nonempty (𝔸.bassSerreVertex v₀ p ⟶ w)} :=
  (𝔸.segmentStarEquiv v₀ e p).symm.trans
    ((𝔸.bassSerreTree v₀).isTree.isAcyclic.starEquivAdjacent (𝔸.bassSerreVertex v₀ p))

variable {𝔸 v₀ e}

@[simp] theorem segmentStarEquiv_symm_apply_val (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : 𝔸.vertexGroup (SerreGraph.segment.src e)) :
    ((𝔸.segmentStarEquiv v₀ e p).symm a).1 = 𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a)) := by
  simp only [segmentStarEquiv, Equiv.symm_trans, Equiv.trans_apply, Equiv.uniqueSigma_symm_apply]
  rw [(Equiv.symm_apply_eq _).mpr (Subgroup.quotientEquivOfEq_mk _ a).symm,
    bassSerreStarEquiv_symm_apply_val,
    Subsingleton.elim (default : {d : SerreGraph.segment.E //
      SerreGraph.segment.src d = SerreGraph.segment.src e}) ⟨e, rfl⟩,
    bassSerreDartOfSrcEq_rfl]

@[simp] theorem segmentStarEquiv_apply_dart (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : 𝔸.vertexGroup (SerreGraph.segment.src e))
    (h : (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a))) =
      𝔸.bassSerreVertex v₀ p) :
    𝔸.segmentStarEquiv v₀ e p ⟨𝔸.bassSerreDart v₀ e (p.cons (Letter.vertex a)), h⟩ = a :=
  (Equiv.eq_symm_apply _).mp (Subtype.ext (segmentStarEquiv_symm_apply_val p a).symm)

@[simp] theorem segmentStarEquiv_apply_dart_self (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (h : (𝔸.bassSerreTree v₀).src (𝔸.bassSerreDart v₀ e p) = 𝔸.bassSerreVertex v₀ p) :
    𝔸.segmentStarEquiv v₀ e p ⟨𝔸.bassSerreDart v₀ e p, h⟩ =
      QuotientGroup.mk (1 : 𝔸.vertexGroup (SerreGraph.segment.src e)) :=
  (Equiv.eq_symm_apply _).mp <| Subtype.ext <| by
    rw [segmentStarEquiv_symm_apply_val]; exact (bassSerreDart_congr (Path.Homotopic.one p)).symm

@[simp] theorem segmentAdjacentEquiv_apply_val (p : 𝔸.Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : 𝔸.vertexGroup (SerreGraph.segment.src e)) :
    (𝔸.segmentAdjacentEquiv v₀ e p a).1 =
      𝔸.bassSerreVertex v₀
        ((p.cons (Letter.vertex a)).cons (Letter.dart (SerreGraph.segment.dart e))) := by
  rw [segmentAdjacentEquiv, Equiv.trans_apply, SerreGraph.IsAcyclic.starEquivAdjacent_apply_val,
    segmentStarEquiv_symm_apply_val, bassSerreTree_tgt_dart]

end Segment

section Coprod

variable (A B : Type w) [Group A] [Group B] (v₀ : SerreGraph.segment.V) (e : SerreGraph.segment.E)

/-- In the Bass–Serre tree of `A ∗ B`, the outgoing darts at `p A_{src e}` correspond bijectively
to the vertex group `A_{src e}`. -/
noncomputable def coprodStarEquiv (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩) :
    {E : ((coprod A B).bassSerreTree v₀).E //
      ((coprod A B).bassSerreTree v₀).src E = (coprod A B).bassSerreVertex v₀ p} ≃
      (coprod A B).vertexGroup (SerreGraph.segment.src e) :=
  (((coprod A B).segmentStarEquiv v₀ e p).trans
    (Subgroup.quotientEquivOfEq ((coprod A B).range_α_eq_bot_of_subsingleton e))).trans
    (QuotientGroup.quotientBot (G := (coprod A B).vertexGroup (SerreGraph.segment.src e))).toEquiv

/-- In the Bass–Serre tree of `A ∗ B`, the neighbours of `p A_{src e}` correspond bijectively to
`A_{src e}` via `a ↦ (p · a · e) A_{tgt e}`. -/
noncomputable def coprodAdjacentEquiv (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩) :
    (coprod A B).vertexGroup (SerreGraph.segment.src e) ≃
      {w : ((coprod A B).bassSerreTree v₀).V //
        Nonempty ((coprod A B).bassSerreVertex v₀ p ⟶ w)} :=
  (coprodStarEquiv A B v₀ e p).symm.trans
    (((coprod A B).bassSerreTree v₀).isTree.isAcyclic.starEquivAdjacent
      ((coprod A B).bassSerreVertex v₀ p))

variable {A B v₀ e}

@[simp] theorem coprodStarEquiv_symm_apply_val
    (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : (coprod A B).vertexGroup (SerreGraph.segment.src e)) :
    ((coprodStarEquiv A B v₀ e p).symm a).1 =
      (coprod A B).bassSerreDart v₀ e (p.cons (Letter.vertex a)) := by
  simp [coprodStarEquiv, (Equiv.symm_apply_eq _).mpr (Subgroup.quotientEquivOfEq_mk _ a).symm]

@[simp] theorem coprodStarEquiv_apply_dart (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : (coprod A B).vertexGroup (SerreGraph.segment.src e))
    (h : ((coprod A B).bassSerreTree v₀).src
      ((coprod A B).bassSerreDart v₀ e (p.cons (Letter.vertex a))) =
      (coprod A B).bassSerreVertex v₀ p) :
    coprodStarEquiv A B v₀ e p ⟨(coprod A B).bassSerreDart v₀ e (p.cons (Letter.vertex a)), h⟩ =
      a :=
  (Equiv.eq_symm_apply _).mp (Subtype.ext (coprodStarEquiv_symm_apply_val p a).symm)

@[simp] theorem coprodStarEquiv_apply_dart_self
    (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (h : ((coprod A B).bassSerreTree v₀).src ((coprod A B).bassSerreDart v₀ e p) =
      (coprod A B).bassSerreVertex v₀ p) :
    coprodStarEquiv A B v₀ e p ⟨(coprod A B).bassSerreDart v₀ e p, h⟩ = 1 :=
  (Equiv.eq_symm_apply _).mp <| Subtype.ext <| by
    rw [coprodStarEquiv_symm_apply_val]; exact (bassSerreDart_congr (Path.Homotopic.one p)).symm

@[simp] theorem coprodAdjacentEquiv_apply_val
    (p : (coprod A B).Path ⟨v₀⟩ ⟨SerreGraph.segment.src e⟩)
    (a : (coprod A B).vertexGroup (SerreGraph.segment.src e)) :
    (coprodAdjacentEquiv A B v₀ e p a).1 =
      (coprod A B).bassSerreVertex v₀
        ((p.cons (Letter.vertex a)).cons (Letter.dart (SerreGraph.segment.dart e))) := by
  rw [coprodAdjacentEquiv, Equiv.trans_apply, SerreGraph.IsAcyclic.starEquivAdjacent_apply_val,
    coprodStarEquiv_symm_apply_val, bassSerreTree_tgt_dart]

end Coprod

section Loop

/-- Every vertex of the Bass–Serre tree of an HNN extension `GraphOfGroups.loop f g hf hg` with
finite-index associated subgroups has degree `[G : f(C)] + [G : g(C)]`. -/
theorem card_star_loop {G : Type w} {C : Type x} [Group G] [Group C]
    (f g : C →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    [f.range.FiniteIndex] [g.range.FiniteIndex] (u : ((loop f g hf hg).bassSerreTree ()).V) :
    Nat.card {E : ((loop f g hf hg).bassSerreTree ()).E //
      ((loop f g hf hg).bassSerreTree ()).src E = u} = f.range.index + g.range.index := by
  let eStar : Bool ≃ {e : (SerreGraph.rose Unit).E //
      (SerreGraph.rose Unit).src e = ((loop f g hf hg).bassSerreTypeHom ()).mapV u} :=
    { toFun := fun b => ⟨((), b), rfl⟩, invFun := fun e => e.1.2,
      left_inv := fun _ => rfl, right_inv := fun ⟨⟨⟨⟩, _⟩, _⟩ => rfl }
  -- `loop` is `@[expose]` rather than `abbrev`, so its vertex and edge groups reduce to `G` and `C`
  -- definitionally; transfer `FiniteIndex` and `.range.index` via `loop_α_true` / `loop_α_false`.
  have h_true : ((loop f g hf hg).α ((), true)).range.index = f.range.index :=
    congrArg (fun h : C →* G => h.range.index) (loop_α_true f g hf hg)
  have h_false : ((loop f g hf hg).α ((), false)).range.index = g.range.index :=
    congrArg (fun h : C →* G => h.range.index) (loop_α_false f g hf hg)
  have : ∀ e : {e : (SerreGraph.rose Unit).E //
        (SerreGraph.rose Unit).src e = ((loop f g hf hg).bassSerreTypeHom ()).mapV u},
      ((loop f g hf hg).α e.1).range.FiniteIndex := by
    rintro ⟨⟨⟨⟩, _ | _⟩, _⟩
    · exact Subgroup.finiteIndex_iff.mpr (h_false.symm ▸ Subgroup.FiniteIndex.index_ne_zero)
    · exact Subgroup.finiteIndex_iff.mpr (h_true.symm ▸ Subgroup.FiniteIndex.index_ne_zero)
  rw [card_bassSerreStar u, ← finsum_comp_equiv eStar, finsum_eq_sum_of_fintype, Fintype.sum_bool]
  exact congrArg₂ (· + ·) h_true h_false

end Loop

end GraphOfGroups

end TauCeti
