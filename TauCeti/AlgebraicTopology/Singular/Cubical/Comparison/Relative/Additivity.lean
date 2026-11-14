/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

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

## Main results

* `TopPair.isColimitCofanCubicalHomologyOfIsColimit`: additivity of relative cubical homology.
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

end TopPair
