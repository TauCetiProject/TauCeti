/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Additivity of relative cubical chains

Let maps `f i : Pᵢ ⟶ X` exhibit a topological pair `X` as the coproduct in `TopPair` of a family
of pairs `Pᵢ = (Xᵢ, Aᵢ)`, as for the disjoint union `∐ᵢ (Xᵢ, Aᵢ)`. Relative normalized cubical
homology carries this cofan to a coproduct cofan in every degree
(`TopPair.isColimitCofanCubicalHomologyOfIsColimit`): the maps `Hₙ(Pᵢ) ⟶ Hₙ(X)` induced by the
`f i` exhibit `Hₙ(X)` as the direct sum of the `Hₙ(Pᵢ)`. This is transported from the additivity
of relative singular homology (`TopPair.isColimitCofanSingularHomologyOfIsColimit`) along the
natural comparison of relative cubical and singular homology (`TopPair.singularCubicalHomologyIso`).

On chains this says that the map `⨁ᵢ N(Pᵢ) ⟶ N(X)` out of the coproduct of the relative cubical
chain complexes, given on the summand of `i` by `f i`, is a quasi-isomorphism
(`TopPair.quasiIso_sigmaDesc_cubicalChainComplexMap`). Chain-level comparisons over the cells of a
CW complex, such as those of Brown's twisted tensor products, assemble the cells in this form.

Given identifications `Mᵢ ≃ₗ[k] Hₙ(Pᵢ; k)`, additivity assembles them into an identification
`⨁ᵢ Mᵢ ≃ₗ[k] Hₙ(X; k)` (`TopPair.cubicalHomologyDirectSumEquiv`), given on the summand of `i` by the
map induced by `f i` (`TopPair.cubicalHomologyDirectSumEquiv_lof`). This is how a computation of
the relative homology over one cell, such as the homology of a fibre over the cell, becomes the
computation over all cells of a given dimension. In particular `Hₙ(X; k)` vanishes when every
`Hₙ(Pᵢ; k)` does (`TopPair.isZero_cubicalHomology_of_isColimit`).

## Main results

* `TopPair.isColimitCofanCubicalHomologyOfIsColimit`: additivity of relative cubical homology.
* `TopPair.cubicalHomologyDirectSumEquiv`: the identification `⨁ᵢ Mᵢ ≃ₗ[k] Hₙ(X; k)` assembled
  from identifications `Mᵢ ≃ₗ[k] Hₙ(Pᵢ; k)`.
* `TopPair.isZero_cubicalHomology_of_isColimit`: the relative homology of a coproduct of pairs
  vanishes in every degree in which that of each summand does.
* `TopPair.quasiIso_sigmaDesc_cubicalChainComplexMap`: additivity of relative cubical chains, up to
  quasi-isomorphism.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton, 1952,
  Chapters I–III, the additivity axiom.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

open CategoryTheory Limits

universe u

namespace TopPair

variable (k : Type u) [Ring k]

variable {ι : Type u} {P : ι → TopPair.{u}} {X : TopPair.{u}} {f : ∀ i, P i ⟶ X}

/-- **Additivity of relative cubical homology.** Relative normalized cubical homology carries every
coproduct cofan of topological pairs to a coproduct cofan in every degree: if the maps
`f i : Pᵢ ⟶ X` exhibit `X` as the coproduct of the `Pᵢ` in `TopPair`, the maps
`Hₙ(Pᵢ; k) ⟶ Hₙ(X; k)` they induce exhibit `Hₙ(X; k)` as the coproduct of the `Hₙ(Pᵢ; k)`. -/
noncomputable def isColimitCofanCubicalHomologyOfIsColimit (hc : IsColimit (Cofan.mk X f))
    (n : ℕ) :
    IsColimit (Cofan.mk ((X.cubicalChainComplex k).homology n)
      fun i ↦ HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n) :=
  have : IsIso (Sigma.desc fun i ↦ (P i).singularHomologyMap (f i) (ModuleCat.of k k) n) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).1
      ⟨isColimitCofanSingularHomologyOfIsColimit (ModuleCat.{u} k) (ModuleCat.of k k) n hc⟩
  have : IsIso (Sigma.desc fun i ↦
      HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n) := by
    -- Each leg is the singular leg conjugated by the comparison isomorphisms.
    rw [show (Sigma.desc fun i ↦
        HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n) =
          (Sigma.mapIso fun i ↦ (singularCubicalHomologyIso k (P i) n).symm).hom ≫
            (Sigma.desc fun i ↦ (P i).singularHomologyMap (f i) (ModuleCat.of k k) n) ≫
              (singularCubicalHomologyIso k X n).hom by
      refine Sigma.hom_ext _ _ fun i ↦ ?_
      simp [homologyMap_cubicalChainComplexMap_eq]]
    infer_instance
  Cofan.isColimitOfIsIsoSigmaDesc (hc := this) _

/-- **Additivity of relative cubical chains.** If the maps `f i : Pᵢ ⟶ X` exhibit `X` as the
coproduct of the topological pairs `Pᵢ`, the map `⨁ᵢ N(Pᵢ) ⟶ N(X)` out of the coproduct of the
relative normalized cubical chain complexes, given on the summand of `i` by `f i`, is a
quasi-isomorphism. -/
theorem quasiIso_sigmaDesc_cubicalChainComplexMap (hc : IsColimit (Cofan.mk X f)) :
    QuasiIso (Sigma.desc fun i ↦ cubicalChainComplexMap k (f i)) :=
  (quasiIso_iff _).2 fun n ↦
    (TauCeti.quasiIsoAt_sigmaDesc_iff _).2 ⟨isColimitCofanCubicalHomologyOfIsColimit k hc n⟩

/-- The relative cubical homology of a coproduct of topological pairs vanishes in every degree in
which the relative homology of each summand vanishes. -/
theorem isZero_cubicalHomology_of_isColimit (hc : IsColimit (Cofan.mk X f)) {n : ℕ}
    (h : ∀ i, Limits.IsZero (((P i).cubicalChainComplex k).homology n)) :
    Limits.IsZero ((X.cubicalChainComplex k).homology n) :=
  (Limits.IsZero.iff_id_eq_zero _).2 <|
    Cofan.IsColimit.hom_ext (isColimitCofanCubicalHomologyOfIsColimit k hc n) _ _ fun i ↦
      (h i).eq_of_src _ _

section DirectSum

open scoped DirectSum

variable [DecidableEq ι] {M : ι → ModuleCat.{u} k} (hc : IsColimit (Cofan.mk X f)) (n : ℕ)
  (e : ∀ i, M i ≃ₗ[k] ((P i).cubicalChainComplex k).homology n)

/-- The map `Mᵢ ⟶ Hₙ(X; k)`: the identification of `Mᵢ` with `Hₙ(Pᵢ; k)`, followed by the map
induced by `f i`. -/
private noncomputable def cubicalHomologyLeg (i : ι) : M i ⟶ (X.cubicalChainComplex k).homology n :=
  (e i).toModuleIso.hom ≫ HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n

include hc in
/-- The maps `Mᵢ ⟶ Hₙ(X; k)` exhibit `Hₙ(X; k)` as a coproduct of the `Mᵢ`. -/
private noncomputable def isColimitCofanCubicalHomologyLeg :
    IsColimit (Cofan.mk ((X.cubicalChainComplex k).homology n)
      (cubicalHomologyLeg (f := f) k n e)) :=
  have : IsIso (Sigma.desc fun i ↦
      HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).1
      ⟨isColimitCofanCubicalHomologyOfIsColimit k hc n⟩
  have : IsIso (Sigma.desc (cubicalHomologyLeg (f := f) k n e)) := by
    -- Each leg is the leg of additivity precomposed with an isomorphism.
    rw [show Sigma.desc (cubicalHomologyLeg (f := f) k n e) =
        (Sigma.mapIso fun i ↦ (e i).toModuleIso).hom ≫
          Sigma.desc fun i ↦ HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n from
      Sigma.hom_ext _ _ fun i ↦ by simp [cubicalHomologyLeg]]
    infer_instance
  Cofan.isColimitOfIsIsoSigmaDesc (hc := this) _

/-- **The relative cubical homology of a coproduct of pairs as a direct sum.** If the maps
`f i : Pᵢ ⟶ X` exhibit `X` as the coproduct of the topological pairs `Pᵢ`, identifications
`Mᵢ ≃ₗ[k] Hₙ(Pᵢ; k)` assemble to an identification `⨁ᵢ Mᵢ ≃ₗ[k] Hₙ(X; k)`, given on the summand
of `i` by the map induced by `f i` (`TopPair.cubicalHomologyDirectSumEquiv_lof`). -/
noncomputable def cubicalHomologyDirectSumEquiv :
    (⨁ i, M i) ≃ₗ[k] (X.cubicalChainComplex k).homology n :=
  ((ModuleCat.coproductCoconeIsColimit M).coconePointUniqueUpToIso
    (isColimitCofanCubicalHomologyLeg k hc n e)).toLinearEquiv

/-- On the summand of `i`, `TopPair.cubicalHomologyDirectSumEquiv` is the identification of `Mᵢ`
with `Hₙ(Pᵢ; k)` followed by the map induced by `f i`. -/
theorem cubicalHomologyDirectSumEquiv_lof (i : ι) (x : M i) :
    cubicalHomologyDirectSumEquiv k hc n e (DirectSum.lof k ι (fun i ↦ M i) i x) =
      HomologicalComplex.homologyMap (cubicalChainComplexMap k (f i)) n (e i x) :=
  ConcreteCategory.congr_hom
    ((ModuleCat.coproductCoconeIsColimit M).comp_coconePointUniqueUpToIso_hom
      (isColimitCofanCubicalHomologyLeg k hc n e) ⟨i⟩) x

end DirectSum

end TopPair
