/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Transfer.Basic

/-!
# Composition of singular transfer

For a tower of finite covering maps `E → B → X`, lifting a singular simplex first to
`B` and then to `E` enumerates each lift through the composite exactly once. Consequently
the singular transfer of the composite is the composite of the two transfers. This is the
chain-level composition law used for transfer through intermediate, possibly nonregular,
coverings.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.G, for transfer as the sum over lifts.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti.TopCat

namespace IsCoveringMap

universe w v u

variable {E B X : TopCat.{w}} {p : E ⟶ B} {q : B ⟶ X}

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C]

/-- **Transfer composes through a tower of finite coverings.** The sum over lifts through
`p ≫ q` equals the iterated sum over lifts through `q` and then `p`. -/
theorem singularTransfer_comp (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hcomp : IsCoveringMap (p ≫ q))
    (hfinp : ∀ b, Finite ↥(p ⁻¹' {b})) (hfinq : ∀ x, Finite ↥(q ⁻¹' {x}))
    (hfincomp : ∀ x, Finite ↥((p ≫ q) ⁻¹' {x})) (R : C) :
    hcomp.singularTransfer hfincomp R =
      hq.singularTransfer hfinq R ≫ hp.singularTransfer hfinp R := by
  classical
  ext n σ
  let sq := (hq.finite_preimage_singleton_toSSet_map_app hfinq σ).toFinset
  let sp (τ : (TopCat.toSSet.obj B) _⦋n⦌) :=
    (hp.finite_preimage_singleton_toSSet_map_app hfinp τ).toFinset
  let sc := (hcomp.finite_preimage_singleton_toSSet_map_app hfincomp σ).toFinset
  have hmap (ρ : (TopCat.toSSet.obj E) _⦋n⦌) :
      (TopCat.toSSet.map (p ≫ q)).app _ ρ =
        (TopCat.toSSet.map q).app _ ((TopCat.toSSet.map p).app _ ρ) := by
    rw [Functor.map_comp, NatTrans.comp_app_apply]
  have hunion : sq.biUnion sp = sc := by
    ext ρ
    simp only [sq, sp, sc, Finset.mem_biUnion, Set.Finite.mem_toFinset,
      Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨τ, hτ, hρ⟩
      rw [hmap, hρ]
      exact hτ
    · intro hρ
      exact ⟨(TopCat.toSSet.map p).app _ ρ, by rwa [hmap] at hρ, rfl⟩
  have hdisj : Set.PairwiseDisjoint (sq : Set _) sp := by
    intro τ hτ υ hυ hne
    apply Finset.disjoint_left.mpr
    intro ρ hρτ hρυ
    have hpt : (TopCat.toSSet.map p).app _ ρ = τ := by
      simpa only [sp, Set.Finite.mem_toFinset, Set.mem_preimage,
        Set.mem_singleton_iff] using hρτ
    have hpu : (TopCat.toSSet.map p).app _ ρ = υ := by
      simpa only [sp, Set.Finite.mem_toFinset, Set.mem_preimage,
        Set.mem_singleton_iff] using hρυ
    exact hne (hpt.symm.trans hpu)
  rw [ιChainComplex_singularTransfer_f, HomologicalComplex.comp_f,
    ιChainComplex_singularTransfer_f_assoc, Preadditive.sum_comp]
  simp only [ιChainComplex_singularTransfer_f]
  rw [← Finset.sum_biUnion hdisj, hunion]

/-- The homology transfer of a tower of finite coverings is the composite of the two
homology transfers. -/
theorem homologyMap_singularTransfer_comp [CategoryWithHomology C]
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (hcomp : IsCoveringMap (p ≫ q))
    (hfinp : ∀ b, Finite ↥(p ⁻¹' {b})) (hfinq : ∀ x, Finite ↥(q ⁻¹' {x}))
    (hfincomp : ∀ x, Finite ↥((p ≫ q) ⁻¹' {x})) (R : C) (n : ℕ) :
    HomologicalComplex.homologyMap (hcomp.singularTransfer hfincomp R) n =
      HomologicalComplex.homologyMap (hq.singularTransfer hfinq R) n ≫
        HomologicalComplex.homologyMap (hp.singularTransfer hfinp R) n := by
  rw [singularTransfer_comp hp hq hcomp hfinp hfinq hfincomp,
    HomologicalComplex.homologyMap_comp]

end IsCoveringMap
