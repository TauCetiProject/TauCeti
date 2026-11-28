/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex

/-!
# The horn criteria for Cartesian and coCartesian edges

Let `p : X ⟶ S` be a map of simplicial sets and `f : x ⟶ y` an edge of `X`. The edge `f` is
`p`-Cartesian when the map `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` is a trivial fibration. By
Mathlib's description of the trivial fibrations as the maps lifting against boundary inclusions
(`SSet.rlp_monomorphisms`), it suffices to solve the lifting problems of `∂Δ[n] ⟶ Δ[n]` against
this map. By the universal property of the slice, such a problem is an extension problem for maps
into `X`, over `S`, along `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1]) ⟶ Δ[n] ⋆ Δ[1]`, where `Λ[1, 1]` is the
target vertex of `Δ[1]`. Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]` this is the horn inclusion
`Λ[n + 2, n + 2] ⟶ Δ[n + 2]` (`SSet.join.unionJoinBoundaryHornOneOneIso`), and the final edge of
the horn, from `n + 1` to `n + 2`, is `f`. So `f` is `p`-Cartesian as soon as the horns
`Λ[n + 2, n + 2]` whose final edge is `f` lift along `p` over every `(n + 2)`-simplex of `S`
(HTT Remark 2.4.1.4). Reversing simplices through `SSet.horn.opIso` gives the dual criterion for
coCartesian edges, with the horns `Λ[n + 2, 0]` whose initial edge is `f`.

For instance, these criteria show that edges of a quasicategory are equivalences as soon as they
are Cartesian over a point (`TauCeti.AlgebraicTopology.Quasicategory.EquivalenceCartesian`), and
that strongly coCartesian morphisms of ordinary categories give coCartesian edges of nerves
(`TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Nerve`).

## Main results

* `SSet.Edge.isCartesian_of_hornFilling_last`: the horn criterion for `p`-Cartesian edges.
* `SSet.Edge.isCoCartesian_of_hornFilling_zero`: the horn criterion for `p`-coCartesian edges.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.4 and Remark 2.4.1.9.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6 (the pushout-join description of outer horns).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

namespace Edge

variable {X : SSet.{u}}

section boundary

/-! ### Lifting boundaries against the relative restriction of cones -/

variable {n : ℕ}

/-- Horn filling over `S` gives the extensions of cones `Δ[n] ⋆ Δ[1] ⟶ X` that the map
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` lifts. Let `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` be a cone over the edge
`f` given by `s` and `B : Δ[n] ⋆ Δ[0] ⟶ X` a cone agreeing with `A` on `∂Δ[n] ⋆ Δ[0]`, both lying
under `C : Δ[n] ⋆ Δ[1] ⟶ S`. Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]`, they glue to a horn
`Λ[n + 2, n + 2]` with final edge `s` over `C`, and a filler over `C` is the required
extension. -/
private lemma exists_lift_join_of_hornFilling {S : SSet.{u}} (p : X ⟶ S) (s : X _⦋1⦌)
    (H : ∀ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ)
    (A : join (∂Δ[n] : SSet.{u}) Δ[1] ⟶ X) (B : join Δ[n] Δ[0] ⟶ X) (C : join Δ[n] Δ[1] ⟶ S)
    (hA : join.inr _ _ ≫ A = yonedaEquiv.symm s)
    (hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ B)
    (hAC : A ≫ p = join.map ∂Δ[n].ι (𝟙 _) ≫ C)
    (hBC : B ≫ p = join.map (𝟙 _) (stdSimplex.δ 0) ≫ C) :
    ∃ L : join Δ[n] Δ[1] ⟶ X, join.map ∂Δ[n].ι (𝟙 _) ≫ L = A ∧
      join.map (𝟙 _) (stdSimplex.δ 0) ≫ L = B ∧ L ≫ p = C := by
  -- The horn `Λ[1, 1]` is the target vertex of `Δ[1]`.
  let t := stdSimplex.isTerminalObj₀.{u}.from (Λ[1, 1] : SSet)
  have hΛ : Λ[1, 1].ι = t ≫ stdSimplex.δ 0 := by
    rw [horn_one_ι_eq_const, stdSimplex.δ_zero_eq_const, comp_const]
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[1, 1]
  have hw' : join.map (𝟙 _) Λ[1, 1].ι ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ join.map (𝟙 _) t ≫ B := by
    rw [hΛ, ← Category.id_comp (𝟙 (∂Δ[n] : SSet)), join.map_comp_assoc, hw]
    simp only [← join.map_comp_assoc, Category.id_comp, Category.comp_id, t]
  -- `A` and `B` glue to a map `φ` on the pushout-join, a horn `Λ[n + 2, n + 2]` over `C`.
  let φ := hpush.desc A (join.map (𝟙 _) t ≫ B) hw'
  have hφ : φ ≫ p = (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ C := by
    refine hpush.hom_ext ?_ ?_
    · rw [hpush.inl_desc_assoc, hAC, Subcomplex.unionJoin.ι₁_ι_assoc]
    · rw [hpush.inr_desc_assoc, Category.assoc, hBC, Subcomplex.unionJoin.ι₂_ι_assoc, hΛ,
        ← join.map_comp_assoc, Category.id_comp]
  let e := join.unionJoinBoundaryHornOneOneIso.{u} n
  obtain ⟨τ, hτ, hτp⟩ := H (e.inv ≫ φ) ((join.stdSimplexIso n 1).inv ≫ C) (by
    rw [← join.yonedaEquiv_inr_comp_unionJoinBoundaryHornOneOneIso_hom, ← yonedaEquiv_comp]
    simp [φ, hA, e]) (by
    rw [Category.assoc, hφ, ← Iso.inv_hom_id_assoc e Λ[n + 2, _].ι,
      join.unionJoinBoundaryHornOneOneIso_hom_ι n]
    simp)
  -- The filler, read on `Δ[n] ⋆ Δ[1]`, extends `φ` and lies over `C`.
  let L := (join.stdSimplexIso n 1).hom ≫ τ
  have hL : (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ L = φ := by
    rw [← join.unionJoinBoundaryHornOneOneIso_hom_ι_assoc, hτ, Iso.hom_inv_id_assoc]
  have hL₂ : join.map (𝟙 _) Λ[1, 1].ι ≫ L = join.map (𝟙 _) t ≫ B := by
    rw [← Subcomplex.unionJoin.ι₂_ι_assoc, hL, hpush.inr_desc]
  refine ⟨L, by rw [← Subcomplex.unionJoin.ι₁_ι_assoc, hL, hpush.inl_desc], ?_,
    by rw [Category.assoc, hτp, Iso.hom_inv_id_assoc]⟩
  calc _ = join.map (𝟙 _) (horn.ι 1 0 (by decide)) ≫ join.map (𝟙 _) Λ[1, 1].ι ≫ L := by
        rw [← join.map_comp_assoc, Category.id_comp, horn.ι_ι]
    _ = B := by
        rw [hL₂, ← join.map_comp_assoc, Category.id_comp,
          stdSimplex.isTerminalObj₀.hom_ext (horn.ι 1 0 _ ≫ t) (𝟙 _), join.map_id,
          Category.id_comp]

/-- A lifting problem of `∂Δ[n] ⟶ Δ[n]` against the map `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}`
for the edge `f` given by `s` has a solution when every horn `Λ[n + 2, n + 2]` with final edge `s`
lifts along `p` over every `(n + 2)`-simplex of `S`. -/
private lemma hasLiftingProperty_of_hornFilling {S : SSet.{u}} (p : X ⟶ S) (s : X _⦋1⦌)
    (H : ∀ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    HasLiftingProperty ∂Δ[n].ι (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm s)) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- The square amounts to cones `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` over `s` and `B : Δ[n] ⋆ Δ[0] ⟶ X`
  -- agreeing on `∂Δ[n] ⋆ Δ[0]`, under a cone `C : Δ[n] ⋆ Δ[1] ⟶ S`.
  have hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ (slice.homEquiv a).val =
      join.map ∂Δ[n].ι (𝟙 _) ≫ (slice.homEquiv (b ≫ pullback.fst _ _)).val := by
    have h := congrArg (fun F ↦ (slice.homEquiv F).val) (sq.w =≫ pullback.fst _ _)
    rwa [Category.assoc, slice.homEquiv_comp_restrictionMap_fst_coe, Category.assoc,
      slice.homEquiv_comp_coe] at h
  have hAC : (slice.homEquiv a).val ≫ p =
      join.map ∂Δ[n].ι (𝟙 _) ≫ (slice.homEquiv (b ≫ pullback.snd _ _)).val := by
    have h := congrArg (fun F ↦ (slice.homEquiv F).val) (sq.w =≫ pullback.snd _ _)
    rwa [Category.assoc, slice.homEquiv_comp_restrictionMap_snd_coe, Category.assoc,
      slice.homEquiv_comp_coe] at h
  have hBC : (slice.homEquiv (b ≫ pullback.fst _ _)).val ≫ p =
      join.map (𝟙 _) (stdSimplex.δ 0) ≫ (slice.homEquiv (b ≫ pullback.snd _ _)).val := by
    have h := b ≫= pullback.condition
    rw [← Category.assoc b, ← Category.assoc b] at h
    have h' := congrArg (fun F ↦ (slice.homEquiv F).val) h
    rwa [slice.homEquiv_comp_map_coe, slice.homEquiv_comp_map_coe, join.map_id, Category.id_comp,
      Category.comp_id] at h'
  obtain ⟨L, hL₁, hL₂, hLC⟩ := exists_lift_join_of_hornFilling p s H _ _ _
    (slice.homEquiv a).property hw hAC hBC
  refine ⟨⟨⟨slice.homEquiv.symm ⟨L, ?_⟩, ?_, ?_⟩⟩⟩
  · have hinr : join.inr (∂Δ[n] : SSet.{u}) Δ[1] ≫ join.map ∂Δ[n].ι (𝟙 _) = join.inr _ _ := by
      rw [join.inr_map, Category.id_comp]
    rw [← hinr, Category.assoc, hL₁]
    exact (slice.homEquiv a).property
  · exact slice.hom_ext (by rw [slice.homEquiv_comp_coe, Equiv.apply_symm_apply, hL₁])
  · refine pullback.hom_ext (slice.hom_ext ?_) (slice.hom_ext ?_)
    · rw [Category.assoc, slice.homEquiv_comp_restrictionMap_fst_coe, Equiv.apply_symm_apply, hL₂]
    · rw [Category.assoc, slice.homEquiv_comp_restrictionMap_snd_coe, Equiv.apply_symm_apply, hLC]

end boundary

variable {x y : X _⦋0⦌}

/-- **The horn criterion for Cartesian edges** (HTT Remark 2.4.1.4). An edge `f` of `X` is
`p`-Cartesian for `p : X ⟶ S` as soon as every horn `Λ[n + 2, n + 2] ⟶ X` whose final edge, from
`n + 1` to `n + 2`, is `f`, lying over an `(n + 2)`-simplex `τ` of `S`, extends to an
`(n + 2)`-simplex of `X` over `τ`. -/
theorem isCartesian_of_hornFilling_last {S : SSet.{u}} (f : Edge x y) (p : X ⟶ S)
    (H : ∀ (n : ℕ) (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = f.edge →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    f.IsCartesian p := by
  rw [isCartesian_iff, rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  exact hasLiftingProperty_of_hornFilling p f.edge (H n)

/-- **The horn criterion for coCartesian edges** (HTT Remark 2.4.1.4, in the dual form of
Remark 2.4.1.9). An edge `f` of `X` is `p`-coCartesian for `p : X ⟶ S` as soon as every horn
`Λ[n + 2, 0] ⟶ X` whose initial edge, from `0` to `1`, is `f`, lying over an `(n + 2)`-simplex `τ`
of `S`, extends to an `(n + 2)`-simplex of `X` over `τ`. -/
theorem isCoCartesian_of_hornFilling_zero {S : SSet.{u}} (f : Edge x y) (p : X ⟶ S)
    (H : ∀ (n : ℕ) (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = f.edge →
      σ₀ ≫ p = Λ[n + 2, 0].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, 0].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    f.IsCoCartesian p := by
  rw [isCoCartesian_iff_isCartesian_opEquiv]
  refine isCartesian_of_hornFilling_last _ _ fun n σ₀ τ hσ₀ hτ ↦ ?_
  -- Reversing the vertices, through `Λ[n + 2, 0]ᵒᵖ ≅ Λ[n + 2, n + 2]` and `Δ[n + 2]ᵒᵖ ≅ Δ[n + 2]`,
  -- turns the horn `σ₀` of `Xᵒᵖ` over `τ` into a horn `ρ₀ : Λ[n + 2, 0] ⟶ X` over `τ'`.
  -- The reversed vertex `Fin.rev 0` is `Fin.last (n + 2)` by definition.
  let e : opFunctor.obj (Λ[n + 2, 0] : SSet.{u}) ≅ (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
    horn.opIso (n + 2) 0
  let ρ₀ : (Λ[n + 2, 0] : SSet) ⟶ X := opFunctor.preimage (e.hom ≫ σ₀)
  let τ' : Δ[n + 2] ⟶ S := opFunctor.preimage ((stdSimplex.opIso ⦋n + 2⦌).hom ≫ τ)
  have hι : e.hom ≫ Λ[n + 2, Fin.last (n + 2)].ι =
      opFunctor.map Λ[n + 2, 0].ι ≫ (stdSimplex.opIso ⦋n + 2⦌).hom :=
    horn.opIso_hom_ι _ _
  -- The initial edge of `ρ₀` is `f`: horn reversal sends the edge from `0` to `1` to the edge
  -- from `n + 1` to `n + 2`.
  have hedge : ρ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = f.edge := by
    have h₁ : e.hom.app _ (opObjEquiv.symm (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp))) =
        horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
          (Fin.le_last _) (by simp) := by
      rw [← horn.opIso_inv_app_edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)
        (by simpa using Finset.card_le_two.trans (by omega))]
      exact Iso.inv_hom_id_app_apply e _ _
    have h₂ := congrArg (fun g ↦ g.app _ (opObjEquiv.symm
      (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)))) (opFunctor.map_preimage (e.hom ≫ σ₀))
    simp only [opFunctor_map, NatTrans.comp_app_apply, h₁, hσ₀, opEquiv_edge,
      Equiv.apply_symm_apply] at h₂
    exact opObjEquiv.symm.injective h₂
  obtain ⟨ρ, hρ, hρp⟩ := H n ρ₀ τ' hedge (opFunctor.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_comp, Functor.map_preimage,
      Category.assoc, hτ, reassoc_of% hι]))
  -- The reversal of the filler `ρ` fills `σ₀` over `τ`.
  have hι' : Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplex.opIso ⦋n + 2⦌).inv =
      e.inv ≫ opFunctor.map Λ[n + 2, 0].ι := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨(stdSimplex.opIso ⦋n + 2⦌).inv ≫ opFunctor.map ρ, ?_, ?_⟩
  · rw [reassoc_of% hι', ← Functor.map_comp, hρ, Functor.map_preimage, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, ← Functor.map_comp, hρp, Functor.map_preimage, Iso.inv_hom_id_assoc]

end Edge

end SSet
