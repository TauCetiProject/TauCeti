/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Stabilizer
public import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Star
public import TauCeti.GroupTheory.GraphOfGroups.Cyclic
public import Mathlib.SetTheory.Cardinal.Basic
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Index

/-!
# Canonical examples and checks for the Bass–Serre tree

This file verifies `GraphOfGroups.bassSerreTree` on five canonical families and boundary cases:
edgeless components, the free product `ℤ ∗ ℤ`, Baumslag–Solitar groups `BS(m, n)` (and `BS(1, 2)`),
unquotiented homotopy classes of based `𝔸`-paths, and disconnected graphs (two isolated vertices).

## Main results

* `TauCeti.GraphOfGroups.bassSerreTree_point`: edgeless component gives `SerreGraph.noEdge PUnit`.
* `TauCeti.GraphOfGroups.bassSerreTree_free_product`: in `ℤ ∗ ℤ`, neighbours of `⟨a⟩` are indexed
  by `ℤ` (`k ↦ a^k ⟨b⟩`) with degree `ℵ₀`.
* `TauCeti.GraphOfGroups.card_star_baumslagSolitar`, `TauCeti.GraphOfGroups.bassSerreTree_BS12`:
  every vertex of `X` for `BS(m, n)` has degree `|m| + |n|` (and `3` for `BS(1, 2)`).
* `TauCeti.GraphOfGroups.bassSerreTree_not_quotient_paths`: `HomotopyPathFrom` has trivial basepoint
  stabilizer and one point at `v₀` per element of `A_{v₀}`.
* `TauCeti.GraphOfGroups.bassSerreTree_two_isolated`: over two isolated vertices, `X` and `X / π₁`
  each have a single vertex while the ambient graph has two.

## References

* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definition 2.5, pp. 6–7.
* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x u' v'

namespace TauCeti

namespace GraphOfGroups

open _root_.MulAction

variable {Γ : SerreGraph.{u, v}} (𝔸 : GraphOfGroups.{u, v, w, x} Γ) (v₀ : Γ.V)

/-! ### 1. Graphs without edges (`bassSerreTree_point`) -/

section Edgeless

/-- For any graph of groups whose connected component at `v₀` has no darts, the Bass–Serre tree
`X(𝔸, v₀)` is a single point without darts (and in particular isomorphic to
`SerreGraph.noEdge PUnit`). -/
theorem bassSerreTree_point [IsEmpty (Γ.component v₀).E] :
    Nonempty ((𝔸.bassSerreTree v₀).toSerreGraph.Iso (SerreGraph.noEdge.{u', v'} PUnit)) ∧
      Subsingleton (𝔸.bassSerreTree v₀).V ∧
      IsEmpty (𝔸.bassSerreTree v₀).E :=
  ⟨⟨(𝔸.bassSerreTree v₀).toSerreGraph.isoNoEdgePUnit⟩, inferInstance, inferInstance⟩

end Edgeless

/-! ### 2. Free products and `ℤ ∗ ℤ` (`bassSerreTree_free_product`) -/

section FreeProduct

/-- For `ℤ ∗ ℤ`, the base vertex `⟨a⟩` in the Bass–Serre tree has neighbours `a^k ⟨b⟩` indexed
bijectively by `k ∈ ℤ`, and its degree is `ℵ₀`. -/
theorem bassSerreTree_free_product :
    let F2 := coprod (Multiplicative ℤ) (Multiplicative ℤ)
    (∃ equiv : ℤ ≃ {w : (F2.bassSerreTree false).V //
          Nonempty (F2.bassSerreBaseVertex false ⟶ w)},
      ∀ k : ℤ, (equiv k).1 = F2.bassSerreVertex false
        ((Path.ofVertex (Multiplicative.ofAdd k)).cons
          (Letter.dart (SerreGraph.segment.dart false)))) ∧
    Cardinal.mk {E : (F2.bassSerreTree false).E //
      (F2.bassSerreTree false).src E = F2.bassSerreBaseVertex false} =
      Cardinal.aleph0 := by
  let F2 := coprod (Multiplicative ℤ) (Multiplicative ℤ)
  -- `(coprod A B).vertexGroup (SerreGraph.segment.src false)` reduces definitionally to `A` via
  -- `GraphOfGroups.segment` and `SerreGraph.segment`.
  let e : SerreGraph.segment.E := false
  let v₀ : SerreGraph.segment.V := SerreGraph.segment.src e
  have hb : F2.bassSerreBaseVertex v₀ = F2.bassSerreVertex v₀ .nil := F2.bassSerreBaseVertex_def v₀
  refine ⟨⟨Multiplicative.ofAdd.trans
      ((coprodAdjacentEquiv (Multiplicative ℤ) (Multiplicative ℤ) v₀ e .nil).trans
        (Equiv.subtypeEquivRight fun _ => by rw [← hb]; rfl)), fun k => ?_⟩, ?_⟩
  · exact (coprodAdjacentEquiv_apply_val (A := Multiplicative ℤ) (B := Multiplicative ℤ)
        (v₀ := v₀) (e := e) .nil (Multiplicative.ofAdd k)).trans
      (congrArg (fun p => F2.bassSerreVertex v₀ (p.cons (Letter.dart (SerreGraph.segment.dart e))))
        (Path.ofVertex_eq_nil_cons _).symm)
  · exact (Cardinal.mk_congr (((Equiv.subtypeEquivRight fun _ => by rw [← hb]; rfl).trans
      (coprodStarEquiv (Multiplicative ℤ) (Multiplicative ℤ) v₀ e .nil)).trans
        Multiplicative.toAdd)).trans Cardinal.mk_int

end FreeProduct

/-! ### 3. Baumslag–Solitar groups `BS(m, n)` and `BS(1, 2)` (`bassSerreTree_BS12`) -/

section BaumslagSolitar

/-- Every vertex of the Bass–Serre tree of `BS(m, n)` has finite degree `|m| + |n|`. -/
theorem card_star_baumslagSolitar (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (u : ((baumslagSolitar m n hm hn).bassSerreTree ()).V) :
    Nat.card {E : ((baumslagSolitar m n hm hn).bassSerreTree ()).E //
      ((baumslagSolitar m n hm hn).bassSerreTree ()).src E = u} =
      m.natAbs + n.natAbs := by
  have hfin (k : ℤ) (hk : k ≠ 0) : (zpowGroupHom (α := Multiplicative ℤ) k).range.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr <| by
      rw [IsCyclic.index_zpowGroupHom_range_of_infinite]; exact Int.natAbs_ne_zero.mpr hk
  have := hfin m hm; have := hfin n hn
  -- `baumslagSolitar` is `@[expose]` and reduces definitionally to `GraphOfGroups.loop`.
  exact (card_star_loop (zpowGroupHom (α := Multiplicative ℤ) m) (zpowGroupHom n)
      (zpow_left_injective hm) (zpow_left_injective hn) u).trans (by simp)

/-- For `BS(1, 2)`, the boundary images have indices `[A : α(C)] = 1` and `[A : ω(C)] = 2`, and
every vertex of the Bass–Serre tree has degree `3`. -/
theorem bassSerreTree_BS12 :
    let BS := baumslagSolitar 1 2 one_ne_zero two_ne_zero
    (BS.α (((), true) : (SerreGraph.rose Unit).E)).range.index = 1 ∧
      (BS.ω (((), true) : (SerreGraph.rose Unit).E)).range.index = 2 ∧
      ∀ u : (BS.bassSerreTree ()).V,
        Nat.card {E : (BS.bassSerreTree ()).E // (BS.bassSerreTree ()).src E = u} = 3 :=
  ⟨index_range_α_baumslagSolitar 1 2 one_ne_zero two_ne_zero ((), true),
   index_range_ω_baumslagSolitar 1 2 one_ne_zero two_ne_zero ((), true),
   card_star_baumslagSolitar 1 2 one_ne_zero two_ne_zero⟩

end BaumslagSolitar

/-! ### 4. Unquotiented homotopy classes of based `𝔸`-paths (`bassSerreTree_not_quotient_paths`) -/

section UnquotientedPaths

/-- Without the left-coset relation `≈`, homotopy classes of based `𝔸`-paths carry a distinct
point `ofPath (ofVertex a)` at `v₀` for every `a ∈ A_{v₀}`, and the empty path has trivial
stabilizer under `π₁(𝔸, v₀)` instead of `(π₁.vertexHom nil).range ≅ A_{v₀}`. -/
theorem bassSerreTree_not_quotient_paths :
    Function.Injective (fun a : 𝔸.vertexGroup v₀ =>
      HomotopyPathFrom.ofPath (v₀ := v₀) (Path.ofVertex a)) ∧
    stabilizer (π₁ 𝔸 v₀)
      (HomotopyPathFrom.ofPath (𝔸 := 𝔸) (v₀ := v₀) Quiver.Path.nil) = ⊥ := by
  refine ⟨fun a b hab => Path.ofVertex_homotopic_ofVertex_iff.mp
      (HomotopyPathFrom.ofPath_eq_ofPath_iff.mp hab),
    eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_⟩
  refine π₁.induction_on (P := fun g => g ∈ stabilizer (π₁ 𝔸 v₀) _ → g = 1) g (fun s hs => ?_) hg
  rw [mem_stabilizer_iff, HomotopyPathFrom.mk_smul_ofPath, Quiver.Path.comp_nil,
    HomotopyPathFrom.ofPath_eq_ofPath_iff] at hs
  exact (π₁.mk_nil (𝔸 := 𝔸) (a := v₀)) ▸ π₁.mk_eq_mk_iff.mpr hs

end UnquotientedPaths

/-! ### 5. Disconnected underlying graph: two isolated vertices -/

section Disconnected

/-- Over two isolated vertices with basepoint at `false`, both the Bass–Serre tree `X` and its
quotient `X / π₁` have a single vertex, whereas the ambient graph has two vertices and no `𝔸`-path
connects `false` to `true` (so there is no based homomorphism `π₁.vertexHom p` from the vertex group
at `true` into `π₁(𝔸, false)`). -/
theorem bassSerreTree_two_isolated :
    let 𝔸 := GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool)
    Nat.card (𝔸.bassSerreTree false).V = 1 ∧
      Nat.card (𝔸.bassSerreQuotient false).V = 1 ∧
      Nat.card (SerreGraph.noEdge.{0, 0} Bool).V = 2 ∧
      IsEmpty (𝔸.Path ⟨false⟩ ⟨true⟩) :=
  let 𝔸 := GraphOfGroups.trivial (SerreGraph.noEdge.{0, 0} Bool)
  ⟨Nat.card_unique,
    (Nat.card_congr (𝔸.bassSerreQuotientIso false).equivV).trans Nat.card_unique,
    Nat.card_eq_fintype_card.trans Fintype.card_bool,
    ⟨fun p => Bool.false_ne_true (SerreGraph.noEdge_nonempty_path_iff.mp ⟨p.edgePath⟩)⟩⟩

end Disconnected

end GraphOfGroups

end TauCeti
