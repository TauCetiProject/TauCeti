/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import TauCeti.GroupTheory.GraphOfGroups.BassSerreTree.Basic

import TauCeti.GroupTheory.GraphOfGroups.NormalForm

/-!
# Local stars and neighbours in the Bass–Serre tree

At a vertex `[p]` of the Bass–Serre tree `X(𝔸, v₀)` lying over `v : Γ.V`, the outgoing darts
(the star of `[p]`) biject with pairs `(e, g α_e(A_e))` consisting of a dart `e` of `Γ` with
`Γ.src e = v` and a left coset of `α_e(A_e)` in `A_v` (`GraphOfGroups.bassSerreTreeOutgoingEquiv`).
Because `X(𝔸, v₀)` is acyclic, distinct outgoing darts have distinct targets, so the neighbours of
`[p]` satisfy the same coset bijection (`GraphOfGroups.bassSerreTreeNeighborEquiv`).

## Main definitions

* `TauCeti.GraphOfGroups.bassSerreTreeOutgoingEquiv`: bijection between outgoing darts at
  `bassSerreVertex p` and `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ (𝔸.α e).range`.
* `TauCeti.GraphOfGroups.bassSerreTreeNeighborEquiv`: bijection between neighbours of
  `bassSerreVertex p` and `Σ e : {e : Γ.E // Γ.src e = v}, A_v ⧸ (𝔸.α e).range`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.3, Theorem 12.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

open SerreGraph

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ} {v₀ : Γ.V}

private noncomputable def outgoingDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩) :
    𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range → (𝔸.bassSerreTree v₀).E :=
  Quotient.lift (fun g => bassSerreDart e (p.comp (Path.ofVertex g))) fun g₁ g₂ h => by
    obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.mp h
    have hg₂ : g₂ = g₁ * 𝔸.α e c := eq_mul_of_inv_mul_eq hc.symm
    refine (bassSerreDart_eq_iff.mpr ⟨c, ?_⟩).symm
    rw [hg₂]
    simpa only [Path.comp_ofVertex] using (Path.Homotopic.mul p g₁ (𝔸.α e c)).symm

private theorem outgoingDart_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    outgoingDart e p (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range) =
      bassSerreDart e (p.comp (Path.ofVertex g)) := (rfl)

private theorem src_outgoingDart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (q : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range) :
    (𝔸.bassSerreTree v₀).src (outgoingDart e p q) = bassSerreVertex p := by
  induction q using QuotientGroup.induction_on with | H g =>
  rw [outgoingDart_mk, bassSerreTree_src_dart, bassSerreVertex_comp_ofVertex]

private noncomputable def outgoingCosetMap {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (x : Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range) :
    {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = bassSerreVertex p} :=
  ⟨outgoingDart x.1.1 (p.cast rfl (congrArg (fun a : Γ.V => (⟨a⟩ : 𝔸.LetterVertex)) x.1.2.symm))
      x.2, by
    rcases x with ⟨⟨e, he⟩, q⟩
    cases he
    exact src_outgoingDart e p q⟩

private theorem outgoingCosetMap_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (outgoingCosetMap p) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨e₁, he₁⟩, q₁⟩ ⟨⟨e₂, he₂⟩, q₂⟩ h
    cases he₁
    induction q₁ using QuotientGroup.induction_on with | H g₁ =>
    induction q₂ using QuotientGroup.induction_on with | H g₂ =>
    have hval := congrArg Subtype.val h
    simp only [outgoingCosetMap, Quiver.Path.cast_rfl_rfl, outgoingDart_mk] at hval
    have he : e₁ = e₂ := eq_of_bassSerreDart_eq hval
    subst he
    simp only [Quiver.Path.cast_rfl_rfl] at hval
    refine Sigma.ext rfl (heq_of_eq <| QuotientGroup.eq.mpr ?_)
    obtain ⟨c, hc⟩ := bassSerreDart_eq_iff.mp hval
    have hmul : Path.Homotopic (p.comp (Path.ofVertex g₁))
        (p.comp (Path.ofVertex (g₂ * 𝔸.α e₁ c))) := by
      have hc' : Path.Homotopic (p.cons (Letter.vertex g₁))
          ((p.cons (Letter.vertex g₂)).cons (Letter.vertex (𝔸.α e₁ c))) := by
        simpa only [Path.comp_ofVertex] using hc
      simpa only [Path.comp_ofVertex] using hc'.trans (Path.Homotopic.mul p g₂ (𝔸.α e₁ c))
    have hg : g₁ = g₂ * 𝔸.α e₁ c :=
      Path.ofVertex_homotopic_ofVertex_iff.mp ((Path.Homotopic.comp_left_iff p).mp hmul)
    refine ⟨c⁻¹, ?_⟩
    rw [map_inv, hg, mul_inv_rev, inv_mul_cancel_right]
  · rintro ⟨d, hd⟩
    induction d using bassSerreDart_induction_on with | h e q =>
    rw [bassSerreTree_src_dart] at hd
    have he : Γ.src e = v := eq_of_bassSerreVertex_eq hd
    subst he
    obtain ⟨g, hg⟩ := bassSerreVertex_eq_iff.mp hd
    refine ⟨⟨⟨e, rfl⟩, (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)⟩, Subtype.ext ?_⟩
    simpa only [outgoingCosetMap, Quiver.Path.cast_rfl_rfl, outgoingDart_mk] using
      (bassSerreDart_congr hg).symm

/-- The outgoing darts from `bassSerreVertex p` biject with pairs `(e, g α_e(A_e))` of darts `e`
of `Γ` starting at `v` and left cosets of `α_e(A_e)` in `A_v`. -/
noncomputable def bassSerreTreeOutgoingEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = bassSerreVertex p} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range :=
  (Equiv.ofBijective (outgoingCosetMap p) (outgoingCosetMap_bijective p)).symm

@[simp] theorem bassSerreTreeOutgoingEquiv_symm_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    ((bassSerreTreeOutgoingEquiv p).symm
      ⟨⟨e, rfl⟩, (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)⟩).1 =
      bassSerreDart e (p.comp (Path.ofVertex g)) := by
  simp [bassSerreTreeOutgoingEquiv, outgoingCosetMap, outgoingDart_mk]

@[simp] theorem bassSerreTreeOutgoingEquiv_dart (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    bassSerreTreeOutgoingEquiv p
      ⟨bassSerreDart e (p.cons (Letter.vertex g)), by simp⟩ =
      ⟨⟨e, rfl⟩, (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)⟩ :=
  ((bassSerreTreeOutgoingEquiv p).eq_symm_apply).mp
    (Subtype.ext ((bassSerreTreeOutgoingEquiv_symm_mk e p g).trans
      (by rw [Path.comp_ofVertex])).symm)

private def outgoingToNeighbor {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩)
    (d : {d : (𝔸.bassSerreTree v₀).E // (𝔸.bassSerreTree v₀).src d = bassSerreVertex p}) :
    {y : (𝔸.bassSerreTree v₀).V //
      ∃ d : (𝔸.bassSerreTree v₀).E,
        (𝔸.bassSerreTree v₀).src d = bassSerreVertex p ∧ (𝔸.bassSerreTree v₀).tgt d = y} :=
  ⟨(𝔸.bassSerreTree v₀).tgt d.1, d.1, d.2, rfl⟩

private theorem outgoingToNeighbor_bijective {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    Function.Bijective (outgoingToNeighbor p) :=
  ⟨fun d₁ d₂ h => Subtype.ext <|
      (𝔸.bassSerreTree v₀).isAcyclic.eq_of_src_eq_of_tgt_eq
        (d₁.2.trans d₂.2.symm) (congrArg Subtype.val h),
    fun y => let ⟨d, hs, ht⟩ := y.2; ⟨⟨d, hs⟩, Subtype.ext ht⟩⟩

/-- Because the Bass–Serre tree is acyclic, the neighbours of `bassSerreVertex p` biject with its
outgoing darts, and hence with pairs `(e, g α_e(A_e))`. -/
noncomputable def bassSerreTreeNeighborEquiv {v : Γ.V} (p : 𝔸.Path ⟨v₀⟩ ⟨v⟩) :
    {y : (𝔸.bassSerreTree v₀).V //
        ∃ d : (𝔸.bassSerreTree v₀).E,
          (𝔸.bassSerreTree v₀).src d = bassSerreVertex p ∧ (𝔸.bassSerreTree v₀).tgt d = y} ≃
      Σ e : {e : Γ.E // Γ.src e = v}, 𝔸.vertexGroup (Γ.src e.1) ⧸ (𝔸.α e.1).range :=
  (Equiv.ofBijective (outgoingToNeighbor p) (outgoingToNeighbor_bijective p)).symm.trans
    (bassSerreTreeOutgoingEquiv p)

@[simp] theorem bassSerreTreeNeighborEquiv_symm_mk (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    ((bassSerreTreeNeighborEquiv p).symm
      ⟨⟨e, rfl⟩, (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)⟩).1 =
      bassSerreVertex ((p.comp (Path.ofVertex g)).cons (Letter.dart (Γ.dart e))) := by
  rw [bassSerreTreeNeighborEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.ofBijective_apply]
  simp only [outgoingToNeighbor, bassSerreTreeOutgoingEquiv_symm_mk, bassSerreTree_tgt_dart]

@[simp] theorem bassSerreTreeNeighborEquiv_vertex (e : Γ.E) (p : 𝔸.Path ⟨v₀⟩ ⟨Γ.src e⟩)
    (g : 𝔸.vertexGroup (Γ.src e)) :
    bassSerreTreeNeighborEquiv p
      ⟨bassSerreVertex ((p.cons (Letter.vertex g)).cons (Letter.dart (Γ.dart e))),
        bassSerreDart e (p.cons (Letter.vertex g)), by simp, by simp⟩ =
      ⟨⟨e, rfl⟩, (g : 𝔸.vertexGroup (Γ.src e) ⧸ (𝔸.α e).range)⟩ :=
  ((bassSerreTreeNeighborEquiv p).eq_symm_apply).mp
    (Subtype.ext ((bassSerreTreeNeighborEquiv_symm_mk e p g).trans
      (by rw [Path.comp_ofVertex])).symm)

end GraphOfGroups

end TauCeti
