/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import TauCeti.AlgebraicTopology.Quasicategory.FullSubcategory
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Extension
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd
public import TauCeti.AlgebraicTopology.SimplicialSet.InternalHom

/-!
# Joyal's theorem on special outer horns, parametrized

Let `C` be a quasicategory. Joyal's theorem `SSet.Quasicategory.hornFilling_zero` fills a horn
`Λ[m + 2, 0] ⟶ C` whose initial edge is an equivalence. This file proves the parametrized form:
families of such horns, parametrized by a simplicial set, can be filled compatibly with a filling
given over a simplicial subset of the parameter space.

By Mathlib's description of the trivial fibrations as the maps lifting against boundary
inclusions (`SSet.rlp_monomorphisms`), it suffices to treat the families parametrized by `Δ[n]`
with given filling over `∂Δ[n]`, that is extensions along
`(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n]) ⟶ Δ[m + 2] ⊗ Δ[n]`. Mathlib's regular pairing of Moss
for this inclusion attaches inner horns and horns `Λ[d + 1, 0]` whose initial edge is a vertical
edge `(0, t) ⟶ (1, t)` of the prism, which lies in the domain of the extension problem
(`SSet.prodStdSimplex.pairingCore.Type₁.map_edge_of_index_eq_zero`). The extension along a regular
pairing (`SSet.Subcomplex.PairingCore.exists_ext_of_hornFilling`) thus reduces the problem to
inner horn filling and Joyal's theorem (`SSet.Quasicategory.exists_fill_of_ne_last`).

## Main results

* `SSet.prodStdSimplex.exists_ext_unionProd_horn_zero`: a map from
  `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n])` to a quasicategory which sends the vertical edges
  `(0, t) ⟶ (1, t)` to equivalences extends to `Δ[m + 2] ⊗ Δ[n]`.
* `SSet.Quasicategory.exists_lift_pre_horn_zero`: over the horns whose initial edge is an
  equivalence, restriction `Fun(Δ[m + 2], C) ⟶ Fun(Λ[m + 2, 0], C)` has the right lifting property
  with respect to monomorphisms.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002).
* J. Lurie, *Kerodon*, proof of Theorem 4.4.4.4.
* S. Moss, *Another approach to the Kan-Quillen model structure*, J. Homotopy Relat. Struct. 15
  (2020).
-/

public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Simplicial HomotopicalAlgebra

namespace SSet

variable {C : SSet.{u}}

namespace prodStdSimplex

open Subcomplex

/-- **Extension along a prism with invertible vertical edges.** Let `C` be a quasicategory. A map
`(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n]) ⟶ C` extends to `Δ[m + 2] ⊗ Δ[n]` provided that, for
every vertex `t` of `Δ[n]`, it sends the vertical edge `(0, t) ⟶ (1, t)` to an equivalence. -/
theorem exists_ext_unionProd_horn_zero [Quasicategory C] {m n : ℕ}
    (a : (unionProd Λ[m + 2, 0] ∂Δ[n] : SSet.{u}) ⟶ C)
    (ha : ∀ t : Fin (n + 1), (Edge.mk' (a.app _ ((unionProd.ι₂ _ _).app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp),
        stdSimplex.const n t _)))).IsEquivalence) :
    ∃ b : Δ[m + 2] ⊗ Δ[n] ⟶ C, (unionProd Λ[m + 2, 0] ∂Δ[n]).ι ≫ b = a := by
  refine (pairingCore (0 : Fin (m + 2)) n).exists_ext_of_hornFilling a
    fun s B hB g hg σ₀ hσ₀ ↦ ?_
  suffices h0 : s.index.castSucc = 0 → ∀ H, (Edge.mk' ((σ₀ ≫ g).app _
      (horn.edge (s.d + 1) s.index.castSucc 0 1 (Fin.zero_le _) H))).IsEquivalence by
    obtain ⟨σ, hσ⟩ := Quasicategory.exists_fill_of_ne_last (Fin.castSucc_lt_last s.index).ne
      (σ₀ ≫ g) h0
    exact ⟨σ, hσ.symm⟩
  intro hs H
  replace hs : s.index = 0 := Fin.castSucc_eq_zero_iff.1 hs
  -- The initial edge of the horn is the vertical edge at the first vertex of the simplex,
  -- which lies in `Λ[m + 2, 0] ⊗ Δ[n]`, where `g` is `a`.
  have he : σ₀.app _ (horn.edge (s.d + 1) _ 0 1 (Fin.zero_le _) H) =
      (Subcomplex.homOfLE hB).app _ ((unionProd.ι₂ _ _).app _
        (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp),
          stdSimplex.const n ((s.x.cast s.hd).simplex.2 0) _)) := by
    apply Subtype.ext
    exact (congrArg (fun f ↦ f.app _ (horn.edge (s.d + 1) _ 0 1 (Fin.zero_le _) H)) hσ₀).trans
      (s.map_edge_of_index_eq_zero hs)
  have hg' := congrArg (fun f ↦ f.app _ ((unionProd.ι₂ _ _).app _
    (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp),
      stdSimplex.const n ((s.x.cast s.hd).simplex.2 0) _))) hg
  exact (Edge.isEquivalence_iff_of_edge_eq (e := Edge.mk' _) (e' := Edge.mk' _)
    ((congrArg (g.app _) he).trans hg')).2 (ha _)

end prodStdSimplex

namespace Quasicategory

variable {m : ℕ}

/-- The horns `Λ[m + 2, 0] ⟶ C` whose initial edge is an equivalence, as a predicate on the
vertices of `Fun(Λ[m + 2, 0], C)`. -/
private abbrev HasEquivalenceInitialEdge (v : ((ihom (Λ[m + 2, 0] : SSet.{u})).obj C) _⦋0⦌) :
    Prop :=
  (Edge.mk' ((ihomObj₀Equiv _ C v).app _
    (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence

/-- The boundary case of `SSet.Quasicategory.exists_lift_pre_horn_zero`: by adjunction, it is the
extension problem along `(Λ[m + 2, 0] ⊗ Δ[n]) ∪ (Δ[m + 2] ⊗ ∂Δ[n]) ⟶ Δ[m + 2] ⊗ Δ[n]` solved by
`SSet.prodStdSimplex.exists_ext_unionProd_horn_zero`. -/
private lemma exists_lift_boundary [Quasicategory C] {n : ℕ}
    (t : (∂Δ[n] : SSet.{u}) ⟶ (ihom Δ[m + 2]).obj C)
    (b : Δ[n] ⟶ (ihom (Λ[m + 2, 0] : SSet.{u})).obj C)
    (w : t ≫ (pre Λ[m + 2, 0].ι).app C = ∂Δ[n].ι ≫ b)
    (hb : ∀ z : Δ[n] _⦋0⦌, HasEquivalenceInitialEdge (b.app _ z)) :
    ∃ l : Δ[n] ⟶ (ihom Δ[m + 2]).obj C, ∂Δ[n].ι ≫ l = t ∧ l ≫ (pre Λ[m + 2, 0].ι).app C = b := by
  have hw : Λ[m + 2, 0].ι ▷ _ ≫ uncurry t = _ ◁ ∂Δ[n].ι ≫ uncurry b := by
    rw [← uncurry_pre_app, w, uncurry_natural_left]
  let a := (Subcomplex.unionProd.isPushout Λ[m + 2, 0] ∂Δ[n]).desc (uncurry t) (uncurry b) hw
  obtain ⟨L, hL⟩ := prodStdSimplex.exists_ext_unionProd_horn_zero a fun v ↦ by
    have ha := congrArg (fun f ↦ f.app _ (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp),
      stdSimplex.const n v _)) ((Subcomplex.unionProd.isPushout _ _).inr_desc _ _ hw)
    refine (Edge.isEquivalence_iff_of_edge_eq (e := Edge.mk' _) (e' := Edge.mk' _) ?_).1
      (hb (stdSimplex.obj₀Equiv.symm v))
    rw [ihomObj₀Equiv_app]
    exact ha.symm
  refine ⟨curry L, ?_, ?_⟩
  · rw [← curry_natural_left, ← Subcomplex.unionProd.ι₁_ι, Category.assoc, hL,
      IsPushout.inl_desc, curry_uncurry]
  · rw [curry_pre_app, ← Subcomplex.unionProd.ι₂_ι, Category.assoc, hL, IsPushout.inr_desc,
      curry_uncurry]

/-- **Joyal's theorem on special outer horns, parametrized.** Let `C` be a quasicategory. Over the
horns `Λ[m + 2, 0] ⟶ C` whose initial edge is an equivalence, restriction
`Fun(Δ[m + 2], C) ⟶ Fun(Λ[m + 2, 0], C)` has the right lifting property with respect to every
monomorphism `i : Y ⟶ Z`: a family of such horns parametrized by `Z`, whose restriction to `Y` is
filled, has a filling extending the given one. -/
theorem exists_lift_pre_horn_zero [Quasicategory C] {Y Z : SSet.{u}} (i : Y ⟶ Z) [Mono i]
    (t : Y ⟶ (ihom Δ[m + 2]).obj C) (b : Z ⟶ (ihom (Λ[m + 2, 0] : SSet.{u})).obj C)
    (w : t ≫ (pre Λ[m + 2, 0].ι).app C = i ≫ b)
    (hb : ∀ z : Z _⦋0⦌, (Edge.mk' ((ihomObj₀Equiv _ C (b.app _ z)).app _
      (horn.edge (m + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence) :
    ∃ l : Z ⟶ (ihom Δ[m + 2]).obj C, i ≫ l = t ∧ l ≫ (pre Λ[m + 2, 0].ι).app C = b := by
  let H := ((ihom (Λ[m + 2, 0] : SSet.{u})).obj C).fullEnhancedSubcategory
    HasEquivalenceInitialEdge
  let ρ := (pre Λ[m + 2, 0].ι).app C
  -- A map lands in the preimage of `H` when its composite with `ρ` lands in `H`.
  have hpre {W : SSet.{u}} (f : W ⟶ (ihom Δ[m + 2]).obj C) (hf : Subcomplex.range (f ≫ ρ) ≤ H) :
      Subcomplex.range f ≤ H.preimage ρ := by
    rwa [← Subcomplex.image_le_iff, ← Subcomplex.range_comp]
  -- Restriction of `ρ` over `H` is a trivial fibration: it suffices to lift against boundary
  -- inclusions, which is `exists_lift_boundary`.
  have hρ : (MorphismProperty.monomorphisms SSet.{u}).rlp (H.fromPreimage ρ) := by
    rw [rlp_monomorphisms]
    rintro _ _ _ ⟨n⟩
    refine ⟨fun {t b} sq ↦ ?_⟩
    obtain ⟨l, hl₁, hl₂⟩ := exists_lift_boundary (t ≫ (H.preimage ρ).ι) (b ≫ H.ι)
      (by rw [Category.assoc, ← Subcomplex.fromPreimage_ι, ← Category.assoc, sq.w,
        Category.assoc])
      (fun z ↦ (mem_fullEnhancedSubcategory_obj_zero_iff _ _).1 (b.app _ z).property)
    have hl : Subcomplex.range l ≤ H.preimage ρ := hpre l (by
      rw [hl₂, Subcomplex.range_comp]
      exact (Subcomplex.image_le_range _ _).trans (by simp))
    exact ⟨⟨{ l := Subcomplex.lift l hl
              fac_left := by rw [← cancel_mono (H.preimage ρ).ι, Category.assoc,
                Subcomplex.lift_ι, hl₁]
              fac_right := by rw [← cancel_mono H.ι, Category.assoc,
                Subcomplex.fromPreimage_ι, ← Category.assoc, Subcomplex.lift_ι, hl₂] }⟩⟩
  have hb' : Subcomplex.range b ≤ H := (range_le_fullEnhancedSubcategory_iff _ _).2 hb
  have ht : Subcomplex.range t ≤ H.preimage ρ := hpre t (by
    rw [w, Subcomplex.range_comp]
    exact (Subcomplex.image_le_range _ _).trans hb')
  have sq : CommSq (Subcomplex.lift t ht) i (H.fromPreimage ρ) (Subcomplex.lift b hb') :=
    ⟨by rw [← cancel_mono H.ι, Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc,
      Subcomplex.lift_ι, Category.assoc, Subcomplex.lift_ι, w]⟩
  have := hρ i (MorphismProperty.monomorphisms.infer_property i)
  refine ⟨sq.lift ≫ (H.preimage ρ).ι, ?_, ?_⟩
  · rw [← Category.assoc, sq.fac_left, Subcomplex.lift_ι]
  · rw [Category.assoc, ← Subcomplex.fromPreimage_ι, ← Category.assoc, sq.fac_right,
      Subcomplex.lift_ι]

end Quasicategory

end SSet
