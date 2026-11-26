/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.EquivalenceCartesian
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Extension
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-!
# Horn filling along coCartesian edges

Let `p : X ⟶ S` be a map of simplicial sets. An edge `f : x ⟶ y` of `X` is `p`-coCartesian when
the map of coslices `X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}` is a trivial fibration. Through the
pushout-join description of outer horns, this says that horns `Λ[n + 2, 0] ⟶ X` whose initial
edge is `f` can be filled over every `(n + 2)`-simplex of `S` (HTT Remark 2.4.1.4).

This file proves this horn filling and its form for prisms: for an inner fibration `p`, maps
`(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ X` which are defined on the vertical edge
`(0, 0) ⟶ (1, 0)` and send it to a `p`-coCartesian edge lift to `Δ[m + 1] ⊗ Δ[n]`. Mathlib's
regular pairing of Moss for this inclusion attaches inner horns, which lift along the inner
fibration `p`, and horns `Λ[d + 2, 0]` whose initial edge is this vertical edge
(`SSet.prodStdSimplex.pairingCore.Type₁.map_edge_of_index_eq_zero`), which lift along coCartesian
edges. Over a point, the coCartesian edges of a quasicategory are its
equivalences, and this is the prism form of Joyal's theorem on special outer horns
(`SSet.prodStdSimplex.exists_ext_unionProd_horn_zero`).

## Main results

* `SSet.Edge.IsCoCartesian.exists_lift_horn_zero`: horns `Λ[n + 2, 0]` whose initial edge is
  `p`-coCartesian lift along `p`.
* `SSet.Edge.isEquivalence_iff_isCoCartesian`: the edges of a quasicategory which are coCartesian
  over a point are its equivalences.
* `SSet.prodStdSimplex.exists_lift_unionProd_horn_zero`: lifting along the prism
  `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]` against an inner fibration,
  when the vertical edge `(0, 0) ⟶ (1, 0)` lies in the domain and is sent to a coCartesian edge.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.4 and Proposition 2.4.1.5 (in the dual form of
  Remark 2.4.1.9).
* J. Lurie, *Kerodon*, proof of Theorem 4.4.4.4 (the parametrized horn filling).
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

open CategoryTheory Limits MonoidalCategory Simplicial

universe u

namespace SSet

namespace Edge

variable {X S : SSet.{u}} {x y : X _⦋0⦌}

/-- **Horn filling along a coCartesian edge** (HTT Remark 2.4.1.4). Let `f` be a `p`-coCartesian
edge for `p : X ⟶ S`. A horn `Λ[n + 2, 0] ⟶ X` whose initial edge, from `0` to `1`, is `f`, lying
over an `(n + 2)`-simplex `τ` of `S`, extends to an `(n + 2)`-simplex of `X` over `τ`. -/
theorem IsCoCartesian.exists_lift_horn_zero {f : Edge x y} {p : X ⟶ S} (hf : f.IsCoCartesian p)
    {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ X)
    (hσ₀ : σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = f.edge)
    (τ : Δ[n + 2] ⟶ S) (hτ : σ₀ ≫ p = Λ[n + 2, 0].ι ≫ τ) :
    ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, 0].ι ≫ σ = σ₀ ∧ σ ≫ p = τ := by
  -- Reversing the vertices, this is horn filling along the Cartesian edge of `Xᵒᵖ` reversing
  -- `f` (`SSet.Edge.IsCartesian.exists_lift_horn_last`).
  -- Reversal identifies the opposite of `Λ[n + 2, 0]` with `Λ[n + 2, Fin.last (n + 2)]`.
  let ε : (Λ[n + 2, Fin.rev 0] : SSet.{u}) ≅ Λ[n + 2, Fin.last (n + 2)] :=
    Subcomplex.eqToIso (by rw [Fin.rev_zero])
  have hε : ε.inv ≫ Λ[n + 2, Fin.rev 0].ι = Λ[n + 2, Fin.last (n + 2)].ι := by simp [ε]
  have hε' : Λ[n + 2, Fin.rev 0].ι = ε.hom ≫ Λ[n + 2, Fin.last (n + 2)].ι := by simp [ε]
  have hedge : ε.inv.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) (Fin.le_last _) (by simp)) =
      horn.edge (n + 2) (Fin.rev 0) (Fin.rev 1) (Fin.rev 0) (Fin.rev_anti (Fin.zero_le _))
        (by simpa using Finset.card_le_two.trans (by omega)) :=
    -- Both are the edge of `Δ[n + 2]` from `n + 1` to `n + 2`: `Fin.rev 1` and `Fin.rev 0` are
    -- `n + 1` and `n + 2` by definition.
    Subtype.ext rfl
  obtain ⟨σ', hσ', hσ'p⟩ := ((isCoCartesian_iff_isCartesian_opEquiv f p).1 hf).exists_lift_horn_last
    (ε.inv ≫ (horn.opIso (n + 2) 0).inv ≫ opFunctor.map σ₀) (by
      rw [NatTrans.comp_app_apply, NatTrans.comp_app_apply, hedge,
        horn.opIso_inv_app_edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)]
      simp [opFunctor_map, hσ₀])
    ((stdSimplex.opIso ⦋n + 2⦌).inv ≫ opFunctor.map τ) (by
      rw [Category.assoc, Category.assoc, ← Functor.map_comp, hτ, Functor.map_comp,
        horn.opIso_inv_opFunctor_map_ι_assoc, reassoc_of% hε])
  refine ⟨opFunctor.preimage ((stdSimplex.opIso ⦋n + 2⦌).hom ≫ σ'), opFunctor.map_injective ?_,
    opFunctor.map_injective ?_⟩
  · rw [Functor.map_comp, Functor.map_preimage, ← Category.assoc, ← horn.opIso_hom_ι,
      Category.assoc, hε', Category.assoc, hσ', Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  · rw [Functor.map_comp, Functor.map_preimage, Category.assoc, hσ'p, Iso.hom_inv_id_assoc]


/-- **An edge of a quasicategory is an equivalence exactly when it is coCartesian over a point**
(HTT Proposition 2.4.1.5 over a point, in the dual form of Remark 2.4.1.9): for the map `p` to a
terminal simplicial set, the `p`-coCartesian edges are the equivalences. -/
theorem isEquivalence_iff_isCoCartesian [Quasicategory X] (f : Edge x y) (p : X ⟶ S)
    (hS : IsTerminal S) : f.IsEquivalence ↔ f.IsCoCartesian p := by
  rw [isCoCartesian_iff_isCartesian_opEquiv, ← isEquivalence_iff_isCartesian _ _
    (hS.isTerminalObj opFunctor), isEquivalence_opEquiv_iff]

end Edge

namespace prodStdSimplex

open Subcomplex

variable {X S : SSet.{u}}

/-- **Lifting along a prism with a coCartesian initial vertical edge.** Let `p : X ⟶ S` be an
inner fibration. A map `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ X` over
`b : Δ[m + 1] ⊗ Δ[n] ⟶ S` lifts to a map `Δ[m + 1] ⊗ Δ[n] ⟶ X` over `b` provided that the vertical
edge `(0, 0) ⟶ (1, 0)` lies in its domain and is sent to a `p`-coCartesian edge. The edge lies in
`Λ[m + 1, 0] ⊗ Δ[n]` when `1 ≤ m` and in `Δ[m + 1] ⊗ ∂Δ[n]` when `1 ≤ n`. -/
theorem exists_lift_unionProd_horn_zero (p : X ⟶ S) [InnerFibration p] {m n : ℕ}
    (a : (unionProd Λ[m + 1, 0] ∂Δ[n] : SSet.{u}) ⟶ X) (b : Δ[m + 1] ⊗ Δ[n] ⟶ S)
    (hab : a ≫ p = (unionProd Λ[m + 1, 0] ∂Δ[n]).ι ≫ b)
    (hmem : (stdSimplex.edge (m + 1) 0 1 (Fin.zero_le _), stdSimplex.const n 0 _) ∈
      (unionProd Λ[m + 1, 0] ∂Δ[n]).obj (Opposite.op ⦋1⦌))
    (ha : (Edge.mk' (a.app _ ⟨_, hmem⟩)).IsCoCartesian p) :
    ∃ l : Δ[m + 1] ⊗ Δ[n] ⟶ X, (unionProd Λ[m + 1, 0] ∂Δ[n]).ι ≫ l = a ∧ l ≫ p = b := by
  -- Moss's regular pairing for the inclusion attaches inner horns, which lift along the inner
  -- fibration `p`, and horns `Λ[d + 2, 0]` whose initial edge is the vertical edge
  -- `(0, 0) ⟶ (1, 0)`, which lift along coCartesian edges.
  refine (pairingCore (0 : Fin (m + 1)) n).exists_lift_of_hornFilling p a b hab
    fun s B hB g hg hgp σ₀ hσ₀ ↦ ?_
  have hτ : (σ₀ ≫ g) ≫ p = Λ[(pairingCore (0 : Fin (m + 1)) n).dim s + 1,
      (pairingCore (0 : Fin (m + 1)) n).index s].ι ≫
        yonedaEquiv.symm ((pairingCore (0 : Fin (m + 1)) n).simplex s) ≫ b := by
    rw [Category.assoc, hgp, ← Category.assoc σ₀, hσ₀, Category.assoc]
  by_cases hs : s.index = 0
  · -- The type (I) simplex starts with the vertical edge `(0, 0) ⟶ (1, 0)`, and it has
    -- dimension at least `2`.
    obtain ⟨d, hd⟩ := s.exists_dim_eq_add_one hmem
    -- The initial edge of the horn is the vertical edge `(0, 0) ⟶ (1, 0)` of the prism, which
    -- lies in the domain of `a`, where `g` is `a`.
    have hedge (H) : (σ₀ ≫ g).app _ (horn.edge (s.d + 1) _ 0 1 (Fin.zero_le _) H) =
        a.app _ ⟨_, hmem⟩ := by
      have he : σ₀.app _ (horn.edge (s.d + 1) _ 0 1 (Fin.zero_le _) H) =
          (Subcomplex.homOfLE hB).app _ ⟨_, hmem⟩ := by
        apply Subtype.ext
        exact (congrArg (fun f ↦ f.app _ (horn.edge (s.d + 1) _ 0 1 (Fin.zero_le _) H))
          hσ₀).trans (s.map_edge_of_index_eq_zero hs)
      exact (congrArg (g.app _) he).trans (congrArg (fun f ↦ f.app _
        (⟨_, hmem⟩ : (unionProd Λ[m + 1, 0] ∂Δ[n] : SSet.{u}) _⦋1⦌)) hg)
    -- The horn of the pairing has dimension `s.d + 1` and index `s.index.castSucc`, which are
    -- `d + 2` and `0` only propositionally; `key` generalizes them so that substituting `hd` and
    -- `hs` puts the horn in the form `Λ[d + 2, 0]` required by `exists_lift_horn_zero`.
    have key : ∀ (N : ℕ) (i : Fin (N + 2)) (_ : N = d + 1) (_ : i = 0)
        (φ : (Λ[N + 1, i] : SSet) ⟶ X) (τ : Δ[N + 1] ⟶ S), φ ≫ p = Λ[N + 1, i].ι ≫ τ →
        (∀ H, (Edge.mk' (φ.app _ (horn.edge (N + 1) i 0 1 (Fin.zero_le _) H))).IsCoCartesian p) →
        ∃ σ : Δ[N + 1] ⟶ X, Λ[N + 1, i].ι ≫ σ = φ ∧ σ ≫ p = τ := by
      rintro N i rfl rfl φ τ hφ H
      exact (H (by simp)).exists_lift_horn_zero φ rfl τ hφ
    exact key s.d s.index.castSucc hd (by simp [hs]) (σ₀ ≫ g) _ hτ fun H ↦
      ha.of_edge_eq (hedge H).symm
  · -- An inner horn lifts along the inner fibration `p`.
    have h0 : 0 < s.index.castSucc := by
      rw [Fin.pos_iff_ne_zero, Ne, Fin.castSucc_eq_zero_iff]
      exact hs
    have := (mem_innerFibrations p) _
      (horn_ι_mem_innerHornInclusions h0 (Fin.castSucc_lt_last s.index))
    let sq : CommSq (σ₀ ≫ g) Λ[s.d + 1, s.index.castSucc].ι p
      (yonedaEquiv.symm (s.x.cast s.hd).simplex ≫ b) := ⟨hτ⟩
    obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (this.sq_hasLift sq).exists_lift
    exact ⟨l, hl₁, hl₂⟩

end prodStdSimplex

end SSet
