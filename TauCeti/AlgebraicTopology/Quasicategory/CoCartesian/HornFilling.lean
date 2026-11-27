/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.EquivalenceCartesian
public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Extension
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom
public import TauCeti.AlgebraicTopology.SimplicialSet.Vertex

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

The prism form gives the parametrized form of horn filling: families of horns `Λ[m + 2, 0] ⟶ X`
over a simplex of `S`, parametrized by a simplicial set, whose initial edges are `p`-coCartesian,
can be filled over that simplex compatibly with a filling given over a simplicial subset of the
parameter space. By Mathlib's description of the trivial fibrations as the maps lifting against
boundary inclusions (`SSet.rlp_monomorphisms`), it suffices to treat the families parametrized by
`Δ[n]` with given filling over `∂Δ[n]`, which is lifting along the prism
`(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n]) ⟶ Δ[m + 2] ⊗ Δ[n]`. Its case over a point is the
parametrized form of Joyal's theorem, `SSet.Quasicategory.exists_lift_pre_horn_zero`.

## Main results

* `SSet.Edge.IsCoCartesian.exists_lift_horn_zero`: horns `Λ[n + 2, 0]` whose initial edge is
  `p`-coCartesian lift along `p`.
* `SSet.Edge.isEquivalence_iff_isCoCartesian`: the edges of a quasicategory which are coCartesian
  over a point are its equivalences.
* `SSet.prodStdSimplex.exists_lift_unionProd_horn_zero`: lifting along the prism
  `(Λ[m + 1, 0] ⊗ Δ[n]) ∪ (Δ[m + 1] ⊗ ∂Δ[n]) ⟶ Δ[m + 1] ⊗ Δ[n]` against an inner fibration,
  when the vertical edge `(0, 0) ⟶ (1, 0)` lies in the domain and is sent to a coCartesian edge.
* `SSet.exists_lift_ihomOver_pre_horn_zero`: for an inner fibration `p : X ⟶ S` and
  `β : Δ[m + 2] ⟶ S`, over the horns whose initial edge is `p`-coCartesian, restriction
  `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over `β` has the right lifting property
  with respect to monomorphisms.
* `SSet.exists_lift_tensor_horn_zero`: families of horns `Λ[m + 2, 0]` with coCartesian initial
  edges, parametrized by a simplicial set, lift along an inner fibration.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.4 and Proposition 2.4.1.5 (in the dual form of
  Remark 2.4.1.9).
* J. Lurie, *Kerodon*, proof of Theorem 4.4.4.4 (the parametrized horn filling).
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial

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

section relative

variable {X S : SSet.{u}} (p : X ⟶ S) {m : ℕ} (β : Δ[m + 2] ⟶ S)

/-- The boundary case of `SSet.exists_lift_ihomOver_pre_horn_zero`, in curried form: a lifting
problem of `∂Δ[n] ⟶ Δ[n]` against restriction `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` is a
lifting problem along the prism `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])`. -/
private lemma exists_lift_boundary_pre_horn_zero [InnerFibration p] {n : ℕ}
    (t₀ : (∂Δ[n] : SSet.{u}) ⟶ ihomOver p β) (b₀ : Δ[n] ⟶ ihomOver p (Λ[m + 2, 0].ι ≫ β))
    (w₀ : t₀ ≫ ihomOver.pre Λ[m + 2, 0].ι = ∂Δ[n].ι ≫ b₀)
    (hb₀ : ∀ z : Δ[n] _⦋0⦌, (Edge.mk' ((ihomOver.obj₀Equiv (b₀.app _ z)).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Δ[n] ⟶ ihomOver p β, ∂Δ[n].ι ≫ l = t₀ ∧ l ≫ ihomOver.pre Λ[m + 2, 0].ι = b₀ := by
  have hw : Λ[m + 2, 0].ι ▷ _ ≫ (ihomOver.homEquiv t₀).val =
      _ ◁ ∂Δ[n].ι ≫ (ihomOver.homEquiv b₀).val := by
    rw [← ihomOver.homEquiv_comp_pre_coe, w₀, ihomOver.homEquiv_comp_coe]
  have hpush := Subcomplex.unionProd.isPushout Λ[m + 2, 0] ∂Δ[n]
  let a := hpush.desc (ihomOver.homEquiv t₀).val (ihomOver.homEquiv b₀).val hw
  obtain ⟨L, hL₁, hL₂⟩ := prodStdSimplex.exists_lift_unionProd_horn_zero p a (fst _ _ ≫ β)
    (hpush.hom_ext (by simp [a, (ihomOver.homEquiv t₀).property])
      (by simp [a, (ihomOver.homEquiv b₀).property]))
    ((Subcomplex.unionProd.ι₂ _ _).app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _)).property (by
      have hv := hb₀ (stdSimplex.obj₀Equiv.symm 0)
      rw [ihomOver.obj₀Equiv_app_coe] at hv
      have h₁ : (lift (𝟙 _) (const (stdSimplex.obj₀Equiv.symm 0))).app _
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _) := by
        rw [lift_id_const_app_one, Edge.id_edge, SimplicialObject.σ_def,
          stdSimplex.obj₀Equiv_symm_apply, stdSimplex.map_const]
      have h₂ := hpush.inr_desc (ihomOver.homEquiv t₀).val (ihomOver.homEquiv b₀).val hw
      exact hv.of_edge_eq ((congrArg ((ihomOver.homEquiv b₀).val.app _) h₁).trans
        (congrArg (fun (f : (Λ[m + 2, 0] : SSet.{u}) ⊗ Δ[n] ⟶ X) ↦ f.app _
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), stdSimplex.const n 0 _))
            h₂).symm))
  refine ⟨ihomOver.homEquiv.symm ⟨L, hL₂⟩, ihomOver.homEquiv.injective (Subtype.ext ?_),
    ihomOver.homEquiv.injective (Subtype.ext ?_)⟩
  · rw [ihomOver.homEquiv_comp_coe, Equiv.apply_symm_apply, ← Subcomplex.unionProd.ι₁_ι,
      Category.assoc, hL₁, hpush.inl_desc]
  · rw [ihomOver.homEquiv_comp_pre_coe, Equiv.apply_symm_apply, ← Subcomplex.unionProd.ι₂_ι,
      Category.assoc, hL₁, hpush.inr_desc]

/-- **Lifting along horns with coCartesian initial edges, parametrized.** Let `p : X ⟶ S` be an
inner fibration and `β : Δ[m + 2] ⟶ S`. Over the horns `Λ[m + 2, 0] ⟶ X` over `β` whose initial
edge is `p`-coCartesian, restriction `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over
`β` has the right lifting property with respect to every monomorphism `i : Y ⟶ Z`: a family of
such horns parametrized by `Z`, whose restriction to `Y` is filled over `β`, has a filling over `β`
extending the given one. -/
theorem exists_lift_ihomOver_pre_horn_zero [InnerFibration p] {Y Z : SSet.{u}} (i : Y ⟶ Z)
    [Mono i] (t : Y ⟶ ihomOver p β) (b : Z ⟶ ihomOver p (Λ[m + 2, 0].ι ≫ β))
    (w : t ≫ ihomOver.pre Λ[m + 2, 0].ι = i ≫ b)
    (hb : ∀ z : Z _⦋0⦌, (Edge.mk' ((ihomOver.obj₀Equiv (b.app _ z)).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Z ⟶ ihomOver p β, i ≫ l = t ∧ l ≫ ihomOver.pre Λ[m + 2, 0].ι = b :=
  exists_lift_of_forall_boundary (ihomOver.pre Λ[m + 2, 0].ι)
    (fun v ↦ (Edge.mk' ((ihomOver.obj₀Equiv v).val.app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p)
    (fun _ t₀ b₀ w₀ hb₀ ↦ exists_lift_boundary_pre_horn_zero p β t₀ b₀ w₀ hb₀) i t b w hb

/-- **Lifting families of horns with coCartesian initial edges.** Let `p : X ⟶ S` be an inner
fibration and `β : Δ[m + 2] ⟶ S`. A family `b : Z ⊗ Λ[m + 2, 0] ⟶ X` of horns over `β`,
parametrized by a simplicial set `Z`, whose initial edges `(z, 0 ⟶ 1)` are all `p`-coCartesian,
extends to a family `Z ⊗ Δ[m + 2] ⟶ X` of simplices over `β`. This is the case of the empty
simplicial subset of `Z` in `SSet.exists_lift_ihomOver_pre_horn_zero`. -/
theorem exists_lift_tensor_horn_zero [InnerFibration p] {Z : SSet.{u}}
    (b : Z ⊗ (Λ[m + 2, 0] : SSet) ⟶ X) (hb : b ≫ p = snd _ _ ≫ Λ[m + 2, 0].ι ≫ β)
    (hZ : ∀ z : Z _⦋0⦌, (Edge.mk' (b.app _
      (Z.σ 0 z, horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsCoCartesian p) :
    ∃ l : Z ⊗ Δ[m + 2] ⟶ X, Z ◁ Λ[m + 2, 0].ι ≫ l = b ∧ l ≫ p = snd _ _ ≫ β := by
  -- By adjunction, this is a lifting problem against the restriction
  -- `Fun_S(Δ[m + 2], X) ⟶ Fun_S(Λ[m + 2, 0], X)` of functors over `β`, along `∅ ⟶ Z`.
  -- The braided family `Λ[m + 2, 0] ⊗ Z ⟶ X`, as a map `Z ⟶ Fun_S(Λ[m + 2, 0], X)`.
  let b' : (Λ[m + 2, 0] : SSet) ⊗ Z ⟶ X := (β_ _ _).hom ≫ b
  have hb' : b' ≫ p = fst _ _ ≫ Λ[m + 2, 0].ι ≫ β := by
    rw [Category.assoc, hb, braiding_hom_snd_assoc]
  obtain ⟨l, -, hl⟩ := exists_lift_ihomOver_pre_horn_zero p β (initial.to Z) (initial.to _)
    (ihomOver.homEquiv.symm ⟨b', hb'⟩) (initial.hom_ext _ _)
    fun z ↦ by
      rw [ihomOver.obj₀Equiv_app_coe, Equiv.apply_symm_apply]
      have hz : (lift (𝟙 _) (const z)).app _ (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)) =
          (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp), Z.σ 0 z) :=
        lift_id_const_app_one z _
      exact (hZ z).of_edge_eq (congrArg (fun q ↦ b.app _ ((β_ (Λ[m + 2, 0] : SSet) Z).hom.app _ q))
        hz.symm)
  refine ⟨(β_ _ _).hom ≫ (ihomOver.homEquiv l).val, ?_, ?_⟩
  · rw [BraidedCategory.braiding_naturality_right_assoc, ← ihomOver.homEquiv_comp_pre_coe, hl,
      Equiv.apply_symm_apply, SymmetricCategory.symmetry_assoc]
  · rw [Category.assoc, (ihomOver.homEquiv l).property, braiding_hom_fst_assoc]

end relative

end SSet
