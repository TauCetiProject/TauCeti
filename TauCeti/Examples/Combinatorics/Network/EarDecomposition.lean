/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Digraph.Ear

/-!
# Directed ear decomposition examples

Concrete examples exercising directed ear decompositions across networks and digraphs:

1. An isolated single-vertex network on `Unit`, decomposed by zero ears (`length = 0`).
2. A single-vertex network on `Unit` with two parallel loops (`Bool`), decomposed by two closed
   ears of length one (`length = 2`).
3. A two-vertex network on `Bool` with two parallel arrows `false → true` and one return arrow
   `true → false`, admitting a cycle-starting ear decomposition.
4. A strongly connected three-vertex digraph on `Fin 3` with a chord and a self-loop, yielding a
   cycle-starting ear decomposition in which every directed edge (including the loop) belongs to a
   unique ear.
-/

namespace TauCeti

open Relation

-- 1. An isolated single vertex has a zero-ear decomposition of `⊤` and is strongly connected.
example :
    let N : Network Unit Unit :=
      { Hom := fun _ _ ↦ Empty
        lower := fun {_ _} e ↦ e.elim
        upper := fun {_ _} e ↦ e.elim
        lower_le_upper := fun e ↦ e.elim }
    ∃ D : N.EarDecomposition ⊤, D.length = 0 ∧ N.IsStronglyConnected := by
  intro N
  have htop : N.singletonSubnetwork () = ⊤ :=
    Network.Subnetwork.ext (Set.ext fun x ↦ by simp)
      (Set.ext fun a ↦ ⟨fun h ↦ by simp at h, fun _ ↦ a.2.2.elim⟩)
  let D : N.EarDecomposition ⊤ := (Network.EarDecomposition.singleton (N := N) ()).copy htop
  exact ⟨D, by simp [D], D.isStronglyConnected_network⟩

-- 2. A single vertex with two parallel loops decomposes into two closed ears of length one.
example :
    let N : Network Unit Unit :=
      { Hom := fun _ _ ↦ Bool
        lower := fun {_ _} _ ↦ ()
        upper := fun {_ _} _ ↦ ()
        lower_le_upper := fun _ ↦ le_rfl }
    ∃ D : N.EarDecomposition ⊤,
      D.length = 2 ∧
      (∀ i : Fin D.length, D.kindAt i = .closed) ∧
      N.IsStronglyConnected := by
  intro N
  let c₀ : ArrowWalk N.Hom () () := (ArrowWalk.nil ()).cons false
  have hc₀ : c₀.IsCycle := ArrowWalk.isCycle_loop (Q := N.Hom) false
  let D₁ : N.EarDecomposition c₀.toSubnetwork := Network.EarDecomposition.ofIsCycle (N := N) hc₀
  let e₁ : N.ClosedEar c₀.toSubnetwork :=
    Network.ClosedEar.ofLoop (N := N) (true : N.Hom () ()) c₀.source_mem_toSubnetwork <| by
      intro ha₀
      simp only [c₀, ArrowWalk.toSubnetwork_arrowSet, Set.mem_ofPred_eq, ArrowWalk.arrows_cons,
        ArrowWalk.arrows_nil, List.nil_append, List.mem_singleton] at ha₀
      injection ha₀ with _ h
      injection h with _ h'
      exact Bool.noConfusion h'
  have htop : (Network.Ear.closed e₁).adjoin = (⊤ : N.Subnetwork) := by
    refine Network.Subnetwork.ext (Set.ext fun x ↦ ?_) (Set.ext fun ⟨x, y, b⟩ ↦ ?_)
    · simp [e₁, c₀, Network.Ear.adjoin_def]
    · cases b <;>
        simp [e₁, c₀, Network.Ear.adjoin_def, ArrowWalk.arrows_cons, ArrowWalk.arrows_nil]
  let D₂ : N.EarDecomposition ⊤ := (D₁.snoc (.closed e₁)).copy htop
  refine ⟨D₂, ?_, ?_, D₂.isStronglyConnected_network⟩
  · simp [D₂, D₁]
  · intro ⟨i, hi⟩
    have hlen : D₂.length = 2 := by simp [D₂, D₁]
    rcases i with _ | _ | i
    · exact D₂.kindAt_zero_eq_closed (by omega)
    · have h1 : (⟨1, hi⟩ : Fin D₂.length) =
          Fin.cast ((D₁.snoc (.closed e₁)).length_copy htop).symm
            (Fin.cast (D₁.length_snoc (.closed e₁)).symm (Fin.last D₁.length)) := by
        apply Fin.ext
        simp [D₁]
      rw [h1, Network.EarDecomposition.kindAt_copy, Network.EarDecomposition.kindAt_snoc_last]
      exact Network.Ear.kind_closed e₁
    · omega

-- 3. Two vertices `Bool` with two parallel forward arrows `false → true` and one return arrow
-- `true → false`: admits a cycle-starting ear decomposition whose initial cycle has length ≥ 2.
example :
    let N : Network Unit Bool :=
      { Hom := fun x y ↦
          match x, y with
          | false, true => Bool
          | true, false => Unit
          | _, _ => Empty
        lower := fun {_ _} _ ↦ ()
        upper := fun {_ _} _ ↦ ()
        lower_le_upper := fun _ ↦ le_rfl }
    ∃ (v₀ : Bool) (c : ArrowWalk N.Hom v₀ v₀) (D : N.EarDecomposition ⊤) (h : 0 < D.length),
      c.IsCycle ∧ 2 ≤ c.length ∧ D.initialVertex = v₀ ∧
        D.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork := by
  intro N
  have : ∀ x y, Finite (N.Hom x y) := fun x y ↦ by
    cases x <;> cases y <;> dsimp [N] <;> infer_instance
  have hN : N.IsStronglyConnected := by
    rw [N.isStronglyConnected_iff]
    intro x y
    cases x <;> cases y
    · exact ⟨ArrowWalk.nil false⟩
    · exact ⟨(ArrowWalk.nil false).cons (false : N.Hom false true)⟩
    · exact ⟨(ArrowWalk.nil true).cons (() : N.Hom true false)⟩
    · exact ⟨ArrowWalk.nil true⟩
  exact N.isStronglyConnected_iff_exists_cycle_earDecomposition.1 hN

-- 4. A strongly connected 3-vertex digraph with a chord and a self-loop at `0`.
example :
    let G : Digraph (Fin 3) :=
      { Adj := fun u v ↦
          (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 0) }
    ∃ (v₀ : Fin 3) (c : ArrowWalk G.AdjHom v₀ v₀) (E : G.toNetwork.EarDecomposition ⊤)
      (h : 0 < E.length),
      c.IsCycle ∧ 2 ≤ c.length ∧ E.initialVertex = v₀ ∧
        E.stage ⟨1, Nat.succ_lt_succ h⟩ = c.toSubnetwork ∧
        ∃! i : Fin E.length,
          (⟨0, 0, ⟨by simp [G]⟩⟩ : Σ x y, G.AdjHom x y) ∈ (E.ear i).toSubnetwork.arrowSet := by
  intro G
  have h01 : G.Adj 0 1 := by simp [G]
  have h12 : G.Adj 1 2 := by simp [G]
  have h20 : G.Adj 2 0 := by simp [G]
  have h00 : G.Adj 0 0 := by simp [G]
  have hG : ∀ u v : Fin 3, ReflTransGen G.Adj u v := by
    intro u v
    fin_cases u <;> fin_cases v
    · exact .refl
    · exact .single h01
    · exact (ReflTransGen.single h01).tail h12
    · exact (ReflTransGen.single h12).tail h20
    · exact .refl
    · exact .single h12
    · exact .single h20
    · exact (ReflTransGen.single h20).tail h01
    · exact .refl
  obtain ⟨v₀, c, E, h, hc, hlen, hinit, hstage⟩ :=
    G.forall_reflTransGen_iff_exists_cycle_earDecomposition.1 hG
  exact ⟨v₀, c, E, h, hc, hlen, hinit, hstage, G.existsUnique_ear_of_adj E h00⟩

end TauCeti
