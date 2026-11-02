/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Relative.Basic

/-!
# The long exact sequence and excision for cubical singular chains

The short exact sequence `0 ⟶ N(A) ⟶ N(X) ⟶ N(X, A) ⟶ 0` of normalized cubical chains of a
topological pair gives the **long exact sequence of the pair** in cubical homology, with
connecting morphism `TopPair.cubicalHomologyδ`.  The comparison maps form a morphism of short
exact sequences from the simplicial one, so this connecting morphism corresponds to the singular
one under the comparison isomorphisms (`TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ`).

Conversely, a relative class `c ∈ Hₘ₊₁(X, A)` lifts to a normalized cubical chain of `X` with a
prescribed boundary: any cycle `z` of `A` representing the image of `c` under the connecting
morphism is the boundary of a chain of `X` which is a relative cycle representing `c`
(`TopPair.exists_boundary_eq_of_cubicalHomologyδ_eq`), and two such chains differ by a boundary
plus a cycle of `A` (`TopPair.exists_sub_eq_boundary_add_map`). The class `c` may equally be given
in relative singular homology (`TopPair.exists_boundary_eq_of_singularHomologyδ_eq`). Applied to
a compact oriented manifold `M` with boundary, with `c = [M, ∂M]` and `z` a fundamental cycle of
`∂M` (so that the connecting morphism sends `c` to the class of `z`), this gives a fundamental
chain of `M` relative to its boundary whose boundary is exactly `z`.

**Excision** is transported from relative singular homology: a map of pairs inducing isomorphisms
on relative singular homology induces isomorphisms on relative cubical homology
(`TopPair.isIso_homologyMap_cubicalChainComplexMap_of_isIso`), which applies to the excision maps
of `TauCeti.AlgebraicTopology.Singular.Excision`.

## Main definitions

* `TopPair.cubicalHomologyδ`: the connecting morphism `Hₙ(X, A) ⟶ Hₘ(A)` of cubical homology.

## Main results

* `TopPair.cubicalHomology_exact_subspace`, `TopPair.cubicalHomology_exact_space`,
  `TopPair.cubicalHomology_exact_relative`: exactness of the long exact sequence.
* `TopPair.singularCubicalHomologyIso_hom_cubicalHomologyδ`: compatibility of the connecting
  morphisms with the comparison.
* `TopPair.exists_boundary_eq_of_cubicalHomologyδ_eq`,
  `TopPair.exists_boundary_eq_of_singularHomologyδ_eq`: relative classes lift to chains with a
  prescribed boundary.
* `TopPair.exists_sub_eq_boundary_add_map`: such chains are unique up to boundaries and cycles of
  the subspace.
* `TopPair.isIso_homologyMap_cubicalChainComplexMap_excisionMap`,
  `TopPair.isIso_homologyMap_cubicalChainComplexMap_excisionMap_compl`: excision.

## References

* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Princeton, 1952,
  Chapters I–III and VII.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology TauCeti Topology

universe u

namespace TopPair

variable (k : Type u) [Ring k] (P : TopPair.{u})

/-! ### The long exact sequence of a pair -/

/-- The **connecting morphism** `Hₙ(X, A) ⟶ Hₘ(A)` of the long exact sequence of a pair in cubical
homology, for `m + 1 = n`. -/
def cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (P.cubicalChainComplex k).homology n ⟶
      ((normalizedCubicalChainComplex k).obj P.snd).homology m :=
  (shortExact_cubicalChainComplexShortComplex k P).δ n m h

theorem cubicalHomologyδ_def (n m : ℕ) (h : m + 1 = n := by lia) :
    P.cubicalHomologyδ k n m h = (shortExact_cubicalChainComplexShortComplex k P).δ n m h :=
  (rfl)

/-- The connecting morphism followed by the map induced by the inclusion of the subspace is
zero. -/
@[reassoc (attr := simp)]
theorem cubicalHomologyδ_comp (n m : ℕ) (h : m + 1 = n := by lia) :
    P.cubicalHomologyδ k n m h ≫
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) m = 0 :=
  (shortExact_cubicalChainComplexShortComplex k P).δ_comp n m h

/-- The map to relative homology followed by the connecting morphism is zero. -/
@[reassoc (attr := simp)]
theorem comp_cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n ≫
      P.cubicalHomologyδ k n m h = 0 :=
  (shortExact_cubicalChainComplexShortComplex k P).comp_δ n m h

/-- Exactness at the cubical homology of the subspace. -/
theorem cubicalHomology_exact_subspace (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk (P.cubicalHomologyδ k n m h)
      (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) m)
      (P.cubicalHomologyδ_comp k n m h)).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₁ n m h

/-- Exactness at the cubical homology of the ambient space. -/
theorem cubicalHomology_exact_space (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap ((normalizedCubicalChainComplex k).map P.map) n)
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n)
      (by rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
        HomologicalComplex.homologyMap_zero])).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₂ n

/-- Exactness at the relative cubical homology. -/
theorem cubicalHomology_exact_relative (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map P.map)) n)
      (P.cubicalHomologyδ k n m h)
      (P.comp_cubicalHomologyδ k n m h)).Exact :=
  (shortExact_cubicalChainComplexShortComplex k P).homology_exact₃ n m h

/-- **The connecting morphisms of cubical and singular homology correspond** under the comparison
isomorphisms. -/
theorem singularCubicalHomologyIso_hom_cubicalHomologyδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (singularCubicalHomologyIso k P n).hom ≫ P.cubicalHomologyδ k n m h =
      (P.shortExact_singularChainComplexShortComplex (ModuleCat.of k k)).δ n m h ≫
        (TauCeti.singularCubicalHomologyIso k P.snd m).hom := by
  rw [singularCubicalHomologyIso_hom, TauCeti.singularCubicalHomologyIso_hom,
    ← singularToCubicalShortComplex_τ₁, ← singularToCubicalShortComplex_τ₃]
  exact (HomologicalComplex.HomologySequence.δ_naturality (singularToCubicalShortComplex k P)
    (P.shortExact_singularChainComplexShortComplex _)
    (shortExact_cubicalChainComplexShortComplex k P) n m h).symm

/-! ### Chains with a prescribed boundary -/

/-- **Relative cubical classes lift to chains with a prescribed boundary.** Let `c` be a class of
`Hₘ₊₁(X, A)` and `z` an `m`-cycle of `A` representing the image of `c` under the connecting
morphism. Then some normalized cubical `(m + 1)`-chain `s` of `X` has boundary exactly the image
of `z` in `X`, and is a relative cycle representing `c`.

Applied to a compact manifold `M` with boundary, `c = [M, ∂M]` and a fundamental cycle `z` of
`∂M`, this produces a fundamental chain of `M` relative to its boundary whose boundary is `z`. -/
theorem exists_boundary_eq_of_cubicalHomologyδ_eq (m : ℕ)
    (c : (P.cubicalChainComplex k).homology (m + 1))
    (z : ((normalizedCubicalChainComplex k).obj P.snd).cycles m)
    (hz : (P.cubicalHomologyδ k (m + 1) m).hom c =
      (((normalizedCubicalChainComplex k).obj P.snd).homologyπ m).hom z) :
    ∃ (s : NormalizedCubicalChain P.fst k (m + 1)) (r : (P.cubicalChainComplex k).cycles (m + 1)),
      NormalizedCubicalChain.boundary P.fst k m s =
          NormalizedCubicalChain.map k P.map.hom m
            ((((normalizedCubicalChainComplex k).obj P.snd).iCycles m).hom z) ∧
        ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (m + 1)).hom s =
          ((P.cubicalChainComplex k).iCycles (m + 1)).hom r ∧
        ((P.cubicalChainComplex k).homologyπ (m + 1)).hom r = c := by
  obtain ⟨s, r, hs, hr, rfl⟩ :=
    (shortExact_cubicalChainComplexShortComplex k P).moduleCat_exists_d_eq_of_δ_eq (m + 1) m
      rfl c z hz
  refine ⟨normalizedCubicalChainComplexXEquiv P.fst (m + 1) s, r, ?_, ?_, rfl⟩
  · rw [← normalizedCubicalChainComplexXEquiv_d_apply, normalizedCubicalChainComplexXEquiv_apply]
    exact hs.trans (normalizedCubicalChainComplex_map_f_apply P.map m _)
  · rw [normalizedCubicalChainComplexXEquiv_apply]
    exact hr

/-- **Chains with a prescribed boundary are unique up to boundaries and cycles of the subspace.**
Let `s, s'` be normalized cubical `(m + 1)`-chains of `X` with the same boundary which are relative
cycles representing the same class of `Hₘ₊₁(X, A)`. Then `s - s'` is the sum of a boundary and
the image of a cycle of `A`. -/
theorem exists_sub_eq_boundary_add_map (m : ℕ) (s s' : NormalizedCubicalChain P.fst k (m + 1))
    (hd : NormalizedCubicalChain.boundary P.fst k m s =
      NormalizedCubicalChain.boundary P.fst k m s')
    (r r' : (P.cubicalChainComplex k).cycles (m + 1))
    (hs : ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (m + 1)).hom s =
      ((P.cubicalChainComplex k).iCycles (m + 1)).hom r)
    (hs' : ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (m + 1)).hom s' =
      ((P.cubicalChainComplex k).iCycles (m + 1)).hom r')
    (hr : ((P.cubicalChainComplex k).homologyπ (m + 1)).hom r =
      ((P.cubicalChainComplex k).homologyπ (m + 1)).hom r') :
    ∃ (b : NormalizedCubicalChain P.fst k (m + 2)) (a : NormalizedCubicalChain P.snd k (m + 1)),
      NormalizedCubicalChain.boundary P.snd k m a = 0 ∧
        s - s' = NormalizedCubicalChain.boundary P.fst k (m + 1) b +
          NormalizedCubicalChain.map k P.map.hom (m + 1) a := by
  obtain ⟨b, a, ha, hab⟩ :=
    (shortExact_cubicalChainComplexShortComplex k P).moduleCat_exists_sub_eq_d_add (m + 1) m
      (m + 2) (ChainComplex.prev ℕ (m + 1))
      ((normalizedCubicalChainComplexXEquiv P.fst (m + 1)).symm s)
      ((normalizedCubicalChainComplexXEquiv P.fst (m + 1)).symm s')
      (by
        rw [normalizedCubicalChainComplexXEquiv_symm_apply,
          normalizedCubicalChainComplexXEquiv_symm_apply, normalizedCubicalChainComplex_obj_d_apply,
          normalizedCubicalChainComplex_obj_d_apply, hd])
      r r' (by rw [normalizedCubicalChainComplexXEquiv_symm_apply]; exact hs)
      (by rw [normalizedCubicalChainComplexXEquiv_symm_apply]; exact hs') hr
  rw [normalizedCubicalChainComplexXEquiv_symm_apply,
    normalizedCubicalChainComplexXEquiv_symm_apply] at hab
  refine ⟨normalizedCubicalChainComplexXEquiv P.fst (m + 2) b,
    normalizedCubicalChainComplexXEquiv P.snd (m + 1) a, ?_, ?_⟩
  · rw [← normalizedCubicalChainComplexXEquiv_d_apply, ha, map_zero]
  · rw [← normalizedCubicalChainComplexXEquiv_d_apply, normalizedCubicalChainComplexXEquiv_apply,
      normalizedCubicalChainComplexXEquiv_apply]
    exact hab.trans (congrArg _ (normalizedCubicalChainComplex_map_f_apply P.map (m + 1) a))

/-- **Singular relative classes lift to cubical chains with a prescribed boundary.** Let `μ` be a
class of the relative singular homology `Hₘ₊₁(X, A)` and `z` a normalized cubical `m`-cycle of
`A` representing, under the comparison of cubical and singular homology, the image of `μ` under
the singular connecting morphism. Then some normalized cubical `(m + 1)`-chain `s` of `X` has
boundary exactly the image of `z` in `X`, and is a relative cycle whose cubical class corresponds
to `μ`.

The hypothesis on `z` is a statement about singular homology alone once `z` is fixed, so this is
the form in which singular fundamental classes rel boundary produce cubical fundamental chains
with a prescribed boundary. -/
theorem exists_boundary_eq_of_singularHomologyδ_eq (m : ℕ)
    (μ : (P.singularHomology (ModuleCat.of k k) (m + 1) : ModuleCat.{u} k))
    (z : ((normalizedCubicalChainComplex k).obj P.snd).cycles m)
    (hz : (TauCeti.singularCubicalHomologyIso k P.snd m).hom.hom
        ((P.singularHomologyδ (ModuleCat.of k k) (m + 1) m).hom μ) =
      (((normalizedCubicalChainComplex k).obj P.snd).homologyπ m).hom z) :
    ∃ (s : NormalizedCubicalChain P.fst k (m + 1)) (r : (P.cubicalChainComplex k).cycles (m + 1)),
      NormalizedCubicalChain.boundary P.fst k m s =
          NormalizedCubicalChain.map k P.map.hom m
            ((((normalizedCubicalChainComplex k).obj P.snd).iCycles m).hom z) ∧
        ((cokernel.π ((normalizedCubicalChainComplex k).map P.map)).f (m + 1)).hom s =
          ((P.cubicalChainComplex k).iCycles (m + 1)).hom r ∧
        ((P.cubicalChainComplex k).homologyπ (m + 1)).hom r =
          (singularCubicalHomologyIso k P (m + 1)).hom.hom μ := by
  -- `P.singularHomologyδ` is by definition (`SSetPair.homologyδ`) the connecting morphism of the
  -- short exact sequence of singular chains that the comparison lemma is stated with.
  have key : (singularCubicalHomologyIso k P (m + 1)).hom ≫ P.cubicalHomologyδ k (m + 1) m =
      P.singularHomologyδ (ModuleCat.of k k) (m + 1) m ≫
        (TauCeti.singularCubicalHomologyIso k P.snd m).hom :=
    singularCubicalHomologyIso_hom_cubicalHomologyδ k P (m + 1) m
  refine P.exists_boundary_eq_of_cubicalHomologyδ_eq k m _ z ?_
  rw [← hz, ← ModuleCat.comp_apply, key]
  -- The goal is an instance of `ModuleCat.comp_apply`, but `rw` cannot use it because the singular
  -- homology of `A` appears in two definitionally equal forms, `(toSSetPair.obj P).left.homology`
  -- and `((singularChains k).obj A).homology`.
  exact ModuleCat.comp_apply _ _ _

/-! ### Excision -/

variable {k}

/-- A map of pairs inducing isomorphisms on relative singular homology induces isomorphisms on
relative cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_of_isIso {P P' : TopPair.{u}} (f : P ⟶ P')
    (n : ℕ) [IsIso (P.singularHomologyMap f (ModuleCat.of k k) n)] :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k f) n) := by
  have := singularCubicalHomologyIso_hom_naturality k f n
  rw [← Iso.eq_inv_comp] at this
  rw [this]
  infer_instance

/-- **Excision for cubical homology.** If the interiors of `A` and `B` cover `X`, the inclusion of
pairs `(A, A ∩ B) ⟶ (X, B)` induces isomorphisms on relative cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_excisionMap {X : TopCat.{u}} (A B : Set X)
    (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k (excisionMap A B)) n) :=
  have := isIso_singularHomologyMap_excisionMap (ModuleCat.of k k) A B h n
  isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n

/-- **Excision of a set with closure in the interior of the subspace**, for cubical homology. -/
theorem isIso_homologyMap_cubicalChainComplexMap_excisionMap_compl {X : TopCat.{u}} (B Z : Set X)
    (h : closure Z ⊆ interior B) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (cubicalChainComplexMap k (excisionMap Zᶜ B)) n) :=
  have := isIso_singularHomologyMap_excisionMap_compl (ModuleCat.of k k) B Z h n
  isIso_homologyMap_cubicalChainComplexMap_of_isIso _ n

end TopPair
