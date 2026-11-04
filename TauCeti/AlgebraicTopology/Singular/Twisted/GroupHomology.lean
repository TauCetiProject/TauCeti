/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.RepresentationTheory.Homological.GroupHomology.Naturality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

/-!
# Twisted homology of the base of a contractible free cover is group homology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, let `k` be a commutative ring and `A` a `k`-linear
representation of `G`. The local coefficient system on `B` associated to `A`
(`IsQuotientCoveringMap.associatedLocalSystem`) has fibre `(A ⊗ k[p⁻¹ x])_G` over `x`, with
transport induced by monodromy; it is the system of local coefficients of the bundle `E ×_G A`.

The chains of `B` twisted by this system are the coinvariants `(A ⊗ C(E; k))_G`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`): the class of `a ⊗ τ`
goes to the class of `a ⊗ e` in the summand of the simplex `p ∘ τ`, where `e` is the point of
`τ` over the initial vertex of `p ∘ τ`. The proof reduces to the identification of the chains of
`E` with the chains of `B` twisted by the permutation local system
(`IsCoveringMap.singularChainComplexPermutationIso`), which is `G`-equivariant.

If `E` is contractible, its singular chains are a projective resolution of the trivial
representation (`TauCeti.singularChainsResolution`), and group homology with coefficients in `A`
is the homology of `(A ⊗ P)_G` for any such resolution `P` (`groupHomologyIso`). Hence the
homology of `B` with local coefficients in `A` is the group homology of `G` with coefficients in
`A` (`IsQuotientCoveringMap.twistedHomologyIsoGroupHomology`):

`Hₙ(B; A) ≅ Hₙ(G, A)`.

Both identifications are natural in the coefficients and in the group: a morphism of
representations `f : A ⟶ A'` induces a morphism of associated local systems
(`IsQuotientCoveringMap.associatedLocalSystemMap`) corresponding on homology to
`groupHomology.map (MonoidHom.id G) f`
(`IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_naturality`). More generally, for a
second quotient covering `q : F ⟶ C` of a group `H`, an equivariant map `f : E ⟶ F` along
`φ : G →* H` over `b : B ⟶ C`, and a compatible morphism `ψ : A ⟶ Rep.res φ M`, the composite of
the coefficient map `IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap` with the base
pushforward `twistedHomologyMap b` corresponds to `groupHomology.map φ ψ`
(`IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_changeOfGroups`).

The identification also respects the coefficient long exact sequences. A short exact sequence
`0 ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ 0` of representations gives a short exact sequence of associated local
systems (`IsQuotientCoveringMap.shortExact_associatedLocalSystem`), whose connecting map
`Hₙ(B; A₃) ⟶ Hₘ(B; A₁)`, `m + 1 = n`, in twisted homology corresponds to Mathlib's connecting map
`groupHomology.δ`
(`IsQuotientCoveringMap.twistedHomologyδ_comp_twistedHomologyIsoGroupHomology_hom`).
On chains the identification is induced by a chain map from the inhomogeneous chains of `A` to the
twisted chains, natural in `A`, so it is a morphism between the two short exact sequences of chain
complexes whose connecting maps these are.

## Main definitions

* `IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted`: the chains of `B` with
  local coefficients in `A` are the coinvariants `(A ⊗ C(E; k))_G`.
* `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology`: for contractible `E`, the homology of
  `B` with local coefficients in `A` is the group homology `Hₙ(G, A)`.

## Main results

* `IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality`,
  `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_naturality`,
  `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_inv_naturality`: the comparisons of
  chains and of homology are natural in the coefficients.
* `IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_changeOfGroups`,
  `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_changeOfGroups`,
  `IsQuotientCoveringMap.twistedHomologyIsoGroupHomology_hom_pullback`: the comparisons of chains
  and of homology are natural with respect to equivariant maps of quotient covers along arbitrary
  group homomorphisms.
* `IsQuotientCoveringMap.twistedHomologyδ_comp_twistedHomologyIsoGroupHomology_hom`,
  `IsQuotientCoveringMap.groupHomology_δ_comp_twistedHomologyIsoGroupHomology_inv`: the comparison
  of homology carries the coefficient connecting map of twisted homology to the connecting map of
  group homology.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4, III.1, and III.8.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Simplicial TauCeti TauCeti.TopCat TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] {A : Rep.{u} k G}

/-- The morphism of local systems from the permutation local system to the associated local
system sending `v` to the class of `a ⊗ v`. -/
private def coinvariantsTensorMkLocalSystem (a : A) :
    hG.isCoveringMap.permutationLocalSystem k ⟶ hG.associatedLocalSystem k A where
  app x := ModuleCat.ofHom (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj x) a)
  naturality _ _ _ := rfl

/-- The action of an element of `G` on the permutation local system, translating the sheets. -/
private def permutationLocalSystemSMul (g : G) :
    hG.isCoveringMap.permutationLocalSystem k ⟶ hG.isCoveringMap.permutationLocalSystem k where
  app x := ModuleCat.ofHom (hG.fiberRepresentation k x.as g)
  naturality _ _ γ :=
    ModuleCat.hom_ext (((hG.permutationRepFunctor k).map γ).hom.isIntertwining' g).symm

private lemma permutationLocalSystemSMul_app_single (g : G) (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) (r : k) :
    letI := hG.mulActionFiber x.as
    ((permutationLocalSystemSMul hG k g).app x).hom
        ((hG.isCoveringMap.permutationLocalSystemSingle k x e).hom r) =
      (hG.isCoveringMap.permutationLocalSystemSingle k x (g • e)).hom r :=
  (congrArg ((permutationLocalSystemSMul hG k g).app x).hom
    (hG.isCoveringMap.permutationLocalSystemSingle_hom_apply k x e r)).trans
    ((hG.fiberRepresentation_single k x.as g e r).trans
      (hG.isCoveringMap.permutationLocalSystemSingle_hom_apply k x _ r).symm)

/-- Translating the sheets by `g` and then sending `v` to the class of `g a ⊗ v` agrees with
sending `v` to the class of `a ⊗ v`. -/
private lemma permutationLocalSystemSMul_comp_coinvariantsTensorMkLocalSystem (g : G) (a : A) :
    permutationLocalSystemSMul hG k g ≫ coinvariantsTensorMkLocalSystem hG k (A.ρ g a) =
      coinvariantsTensorMkLocalSystem hG k a := by
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_))
  exact Representation.Coinvariants.mk_self_apply
    (A.ρ.tprod (hG.fiberRepresentation k x.as)) g (a ⊗ₜ[k] (v : p ⁻¹' {x.as} →₀ k))

/-- The comparison of the chains of `E` with the chains of `B` twisted by the permutation local
system, with its source written as the singular chain complex of `E`. -/
private def permIso :
    (singularChains k).obj E ≅
      twistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k) :=
  hG.isCoveringMap.singularChainComplexPermutationIso k

/-- The comparison sends a simplex `τ` of `E` to its initial sheet in the summand of `p ∘ τ`. -/
private lemma permIso_hom_simplexChain (n : ℕ) (τ : (TopCat.toSSet.obj E) _⦋n⦌) :
    ((permIso hG k).hom.f n).hom (simplexChain τ 1) =
      (ιTwistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k) n
        ((TopCat.toSSet.map p).app _ τ)).hom
          ((hG.isCoveringMap.permutationLocalSystemSingle k _ (initialSheet τ)).hom 1) :=
  congrArg (fun f ↦ f.hom 1)
    (hG.isCoveringMap.ιChainComplex_singularChainComplexPermutationIso_hom_f k τ)

/-- **The comparison of chains of a quotient cover with twisted chains of the base is
equivariant**: translating a chain of `E` by `g` corresponds to translating the sheets of the
permutation local system by `g`. -/
private lemma permIso_hom_smul (n : ℕ) (g : G) (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ((permIso hG k).hom.f n).hom (singularChainsRepresentation k E G n g c) =
      ((twistedChainComplexCoefficientMap.{u, u, u} (permutationLocalSystemSMul hG k g)).f n).hom
        (((permIso hG k).hom.f n).hom c) := by
  have := hG.toContinuousConstSMul
  refine LinearMap.congr_fun (singularChains_linearMap_ext
    (L := ((permIso hG k).hom.f n).hom ∘ₗ singularChainsRepresentation k E G n g)
    (L' := ((twistedChainComplexCoefficientMap.{u, u, u} (permutationLocalSystemSMul hG k g)).f
      n).hom ∘ₗ ((permIso hG k).hom.f n).hom) fun τ ↦ ?_) c
  let := hG.mulActionFiber (initialVertex ((TopCat.toSSet.map p).app _ τ)).as
  simp only [LinearMap.comp_apply, singularChainsRepresentation_simplexChain,
    permIso_hom_simplexChain, twistedChainComplexCoefficientMap_f_ι_apply]
  -- `simp` does not apply this lemma here, while `rw` matches it up to unfolding.
  rw [permutationLocalSystemSMul_app_single]
  -- Translating `τ` does not change `p ∘ τ`, and translates its initial sheet.
  exact congrArg (fun f ↦ f.hom 1)
    (IsCoveringMap.single_initialSheet_ιTwistedChainComplex hG.isCoveringMap k
      ((hG.toSSet_map_app_eq_iff (g • τ) τ).2 ⟨g, rfl⟩) (e := g • initialSheet τ) rfl)

/-- On twisted chains, translating the sheets by `g` and then sending `v` to the class of
`g a ⊗ v` agrees with sending `v` to the class of `a ⊗ v`. -/
private lemma twistedChainComplexCoefficientMap_permutationLocalSystemSMul_coinvariantsTensorMk
    (n : ℕ) (g : G) (a : A)
    (x : (twistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k)).X n) :
    ((twistedChainComplexCoefficientMap.{u, u, u}
        (coinvariantsTensorMkLocalSystem hG k (A.ρ g a))).f n).hom
        (((twistedChainComplexCoefficientMap.{u, u, u} (permutationLocalSystemSMul hG k g)).f
          n).hom x) =
      ((twistedChainComplexCoefficientMap.{u, u, u} (coinvariantsTensorMkLocalSystem hG k a)).f
        n).hom x := by
  have h := congrArg twistedChainComplexCoefficientMap.{u, u, u}
    (permutationLocalSystemSMul_comp_coinvariantsTensorMkLocalSystem hG k g a)
  rw [twistedChainComplexCoefficientMap_comp] at h
  exact congrArg (fun f ↦ (f.f n).hom x) h

/-- The linear map `A ⟶ Cₙ(B; L_A)` attached to a simplex `τ` of `E`: `a` goes to the class of
`a ⊗ e` in the summand of `p ∘ τ`, where `e` is the initial sheet of `τ`. -/
private def simplexToTwisted (n : ℕ) (τ : (TopCat.toSSet.obj E) _⦋n⦌) :
    A →ₗ[k] (twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).X n :=
  (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n
      ((TopCat.toSSet.map p).app _ τ)).hom ∘ₗ
    (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj
      (initialVertex ((TopCat.toSSet.map p).app _ τ)))).flip
      ((hG.isCoveringMap.permutationLocalSystemSingle k _ (initialSheet τ)).hom 1)

/-- The bilinear map `A × Cₙ(E) ⟶ Cₙ(B; L_A)` underlying the comparison. -/
private def tensorToTwisted (n : ℕ) :
    A →ₗ[k] ((singularChains k).obj E).X n →ₗ[k]
      (twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).X n :=
  (chainsDesc (simplexToTwisted hG k n)).flip

/-- The bilinear map underlying the comparison is the map on twisted chains induced by
`v ↦ ⟦a ⊗ v⟧`, after identifying the chains of `E` with chains of `B` twisted by the permutation
local system. -/
private lemma tensorToTwisted_apply (n : ℕ) (a : A) (c : ((singularChains k).obj E).X n) :
    tensorToTwisted hG k n a c =
      ((twistedChainComplexCoefficientMap.{u, u, u} (coinvariantsTensorMkLocalSystem hG k a)).f
        n).hom (((permIso hG k).hom.f n).hom c) := by
  refine LinearMap.congr_fun (singularChains_linearMap_ext (L := tensorToTwisted hG k n a)
    (L' := ((twistedChainComplexCoefficientMap.{u, u, u}
      (coinvariantsTensorMkLocalSystem hG k a)).f n).hom ∘ₗ ((permIso hG k).hom.f n).hom)
    fun τ ↦ ?_) c
  rw [LinearMap.comp_apply, permIso_hom_simplexChain, twistedChainComplexCoefficientMap_f_ι_apply]
  exact LinearMap.congr_fun (chainsDesc_simplexChain_one (simplexToTwisted hG k n) τ) a

/-- The comparison map `(A ⊗ Cₙ(E))_G ⟶ Cₙ(B; L_A)` in degree `n`. -/
private def coinvariantsTensorToTwistedX (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    ((Rep.coinvariantsTensor k G).obj A).obj (Rep.of (singularChainsRepresentation k E G n)) ⟶
      (twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).X n :=
  haveI := hG.toContinuousConstSMul
  ModuleCat.ofHom <| Representation.Coinvariants.lift _
    (TensorProduct.lift (tensorToTwisted hG k n)) fun g ↦ TensorProduct.ext' fun a c ↦ by
      -- The action of `g` on `A ⊗ Cₙ(E)` is `ρ_A g ⊗ ρ g` (`Rep.tensor_ρ`); the tensor object
      -- appears through `curriedTensor`, under which `simp` cannot rewrite its representation.
      change tensorToTwisted hG k n (A.ρ g a) (singularChainsRepresentation k E G n g c) =
        tensorToTwisted hG k n a c
      rw [tensorToTwisted_apply, tensorToTwisted_apply, permIso_hom_smul,
        twistedChainComplexCoefficientMap_permutationLocalSystemSMul_coinvariantsTensorMk]

/-- The inverse comparison on the summand of a simplex `σ` of `B` comes from the map of
representations `k[p⁻¹ x] ⟶ Cₙ(E)` sending a sheet `e` over the initial vertex `x` of `σ` to the
lift of `σ` through `e`. -/
private def liftRepHom (n : ℕ) (σ : (TopCat.toSSet.obj B) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    (hG.permutationRepFunctor k).obj (initialVertex σ) ⟶
      Rep.of (singularChainsRepresentation k E G n) :=
  haveI := hG.toContinuousConstSMul
  Rep.ofHom
    { toLinearMap := ((permIso hG k).inv.f n).hom ∘ₗ
        (ιTwistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k) n σ).hom
      isIntertwining' g := LinearMap.ext
          fun (v : (hG.isCoveringMap.permutationLocalSystem k).obj (initialVertex σ)) ↦ by
        have h := (permIso_hom_smul hG k n g (((permIso hG k).inv.f n).hom
          ((ιTwistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k) n σ).hom
            v))).trans <| congrArg
          ((twistedChainComplexCoefficientMap.{u, u, u}
            (permutationLocalSystemSMul hG k g)).f n).hom
          (ModuleCat.hom_inv_apply (HomologicalComplex.Hom.isoApp (permIso hG k) n) _)
        rw [twistedChainComplexCoefficientMap_f_ι_apply] at h
        exact (congrArg ((permIso hG k).inv.f n).hom h.symm).trans
          (ModuleCat.inv_hom_apply (HomologicalComplex.Hom.isoApp (permIso hG k) n) _) }

/-- The inverse comparison map `Cₙ(B; L_A) ⟶ (A ⊗ Cₙ(E))_G` in degree `n`. -/
private def twistedToCoinvariantsTensorX (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).X n ⟶
      ((Rep.coinvariantsTensor k G).obj A).obj (Rep.of (singularChainsRepresentation k E G n)) :=
  haveI := hG.toContinuousConstSMul
  twistedChainComplexDesc.{u, u, u} _ fun σ ↦
    ((Rep.coinvariantsTensor k G).obj A).map (liftRepHom hG k n σ)

private lemma twistedToCoinvariantsTensorX_ι_mk (n : ℕ) (σ : (TopCat.toSSet.obj B) _⦋n⦌) (a : A)
    (v : (hG.permutationRepFunctor k).obj (initialVertex σ)) :
    haveI := hG.toContinuousConstSMul
    (twistedToCoinvariantsTensorX hG k n).hom
        ((ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n σ).hom
          (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj (initialVertex σ)) a v)) =
      Rep.coinvariantsTensorMk A (Rep.of (singularChainsRepresentation k E G n)) a
        (((permIso hG k).inv.f n).hom
          ((ιTwistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k) n σ).hom
            v)) :=
  haveI := hG.toContinuousConstSMul
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (ιTwistedChainComplex_twistedChainComplexDesc.{u, u, u} (hG.associatedLocalSystem k A)
      (fun σ ↦ ((Rep.coinvariantsTensor k G).obj A).map (liftRepHom hG k n σ)) σ)) _

private lemma twistedToCoinvariantsTensorX_coefficientMap (n : ℕ) (a : A)
    (x : (twistedChainComplex.{u, u, u} (hG.isCoveringMap.permutationLocalSystem k)).X n) :
    haveI := hG.toContinuousConstSMul
    (twistedToCoinvariantsTensorX hG k n).hom
        (((twistedChainComplexCoefficientMap.{u, u, u}
          (coinvariantsTensorMkLocalSystem hG k a)).f n).hom x) =
      Rep.coinvariantsTensorMk A (Rep.of (singularChainsRepresentation k E G n)) a
        (((permIso hG k).inv.f n).hom x) := by
  have := hG.toContinuousConstSMul
  refine LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (twistedChainComplex_hom_ext.{u, u, u}
    (hG.isCoveringMap.permutationLocalSystem k) (f := (twistedChainComplexCoefficientMap.{u, u, u}
      (coinvariantsTensorMkLocalSystem hG k a)).f n ≫ twistedToCoinvariantsTensorX hG k n)
    (g := (permIso hG k).inv.f n ≫
      ModuleCat.ofHom
        (Rep.coinvariantsTensorMk A (Rep.of (singularChainsRepresentation k E G n)) a))
    fun σ ↦ ModuleCat.hom_ext (LinearMap.ext fun v ↦ ?_))) x
  exact (congrArg (twistedToCoinvariantsTensorX hG k n).hom
    (twistedChainComplexCoefficientMap_f_ι_apply (coinvariantsTensorMkLocalSystem hG k a) n σ
      v)).trans
      (twistedToCoinvariantsTensorX_ι_mk hG k n σ a v)

/-- The degreewise isomorphism `(A ⊗ Cₙ(E))_G ≅ Cₙ(B; L_A)`. -/
private def coinvariantsTensorIsoTwistedX (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    ((Rep.coinvariantsTensor k G).obj A).obj (Rep.of (singularChainsRepresentation k E G n)) ≅
      (twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).X n :=
  haveI := hG.toContinuousConstSMul
  { hom := coinvariantsTensorToTwistedX hG k n
    inv := twistedToCoinvariantsTensorX hG k n
    hom_inv_id := Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦
      ((congrArg (twistedToCoinvariantsTensorX hG k n).hom (tensorToTwisted_apply hG k n a c)).trans
        (twistedToCoinvariantsTensorX_coefficientMap hG k n a _)).trans
        (congrArg _ (ModuleCat.inv_hom_apply (HomologicalComplex.Hom.isoApp (permIso hG k) n) c)))
    inv_hom_id := twistedChainComplex_hom_ext.{u, u, u} _ fun σ ↦ Rep.coinvariantsTensor_hom_ext
      (A := A) (B := (hG.permutationRepFunctor k).obj (initialVertex σ))
      (LinearMap.ext₂ fun a v ↦
        (congrArg (coinvariantsTensorToTwistedX hG k n).hom
          (twistedToCoinvariantsTensorX_ι_mk hG k n σ a v)).trans
          ((tensorToTwisted_apply hG k n a _).trans
            ((congrArg _
              (ModuleCat.hom_inv_apply (HomologicalComplex.Hom.isoApp (permIso hG k) n) _)).trans
              (twistedChainComplexCoefficientMap_f_ι_apply
                (coinvariantsTensorMkLocalSystem hG k a) n σ v)))) }

variable (A) in
/-- **Twisted chains of the base of a quotient cover are coinvariant chains of the total space**:
for the quotient covering map `p : E ⟶ B` of an action of `G` and a representation `A` of `G`,
the chain complex `(A ⊗ C(E; k))_G` is isomorphic to the chain complex of `B` with local
coefficients in the associated local system. The class of `a ⊗ τ` goes to the class of `a ⊗ e`
in the summand of `p ∘ τ`, where `e` is the point of `τ` over the initial vertex of `p ∘ τ`
(`IsQuotientCoveringMap.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk`). -/
def coinvariantsTensorSingularChainsRepIsoTwisted :
    haveI := hG.toContinuousConstSMul
    (singularChainsRep k E G).coinvariantsTensorObj A ≅
      twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) :=
  haveI := hG.toContinuousConstSMul
  HomologicalComplex.Hom.isoOfComponents (coinvariantsTensorIsoTwistedX hG k)
    fun i j (h : j + 1 = i) ↦ by
      subst h
      rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d, singularChainsRep_d]
      refine Rep.coinvariantsTensor_hom_ext (LinearMap.ext₂ fun a c ↦ ?_)
      -- Both sides send the class of `a ⊗ c` to the image of `∂ c`; the twisted side commutes
      -- with the boundary because the coefficient map and the comparison are chain maps.
      have h₁ := congrArg (fun f ↦ f.hom (((permIso hG k).hom.f (j + 1)).hom c))
        ((twistedChainComplexCoefficientMap.{u, u, u}
          (coinvariantsTensorMkLocalSystem hG k a)).comm (j + 1) j)
      have h₂ := congrArg (fun f ↦ f.hom c) ((permIso hG k).hom.comm (j + 1) j)
      exact (congrArg ((twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A)).d
        (j + 1) j).hom (tensorToTwisted_apply hG k (j + 1) a c)).trans (h₁.trans
          ((congrArg _ h₂).trans ((tensorToTwisted_apply hG k j a _).symm.trans
            (congrArg (tensorToTwisted hG k j a)
              (singularChainsRepDifferential_hom_apply k E G j c).symm))))

/-- The comparison sends the class of `a ⊗ τ` to the class of `a ⊗ e` in the summand of `p ∘ τ`,
where `e` is the initial sheet of `τ`. -/
theorem coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk (n : ℕ) (a : A)
    (τ : (TopCat.toSSet.obj E) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    ((hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom.f n).hom
        (Rep.coinvariantsTensorMk A (Rep.of (singularChainsRepresentation k E G n)) a
          (simplexChain τ 1)) =
      (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n
        ((TopCat.toSSet.map p).app _ τ)).hom
          (Rep.coinvariantsTensorMk A
            ((hG.permutationRepFunctor k).obj (initialVertex ((TopCat.toSSet.map p).app _ τ))) a
            (Finsupp.single (initialSheet τ) 1)) := by
  have := hG.toContinuousConstSMul
  exact (LinearMap.congr_fun (chainsDesc_simplexChain_one (simplexToTwisted hG k n) τ) a).trans
    (congrArg (fun v ↦ (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n
      ((TopCat.toSSet.map p).app _ τ)).hom (Rep.coinvariantsTensorMk A
        ((hG.permutationRepFunctor k).obj (initialVertex ((TopCat.toSSet.map p).app _ τ))) a v))
      (hG.isCoveringMap.permutationLocalSystemSingle_hom_apply k _ (initialSheet τ) 1))

variable (A) in
/-- **The homology of the base of a contractible free cover with local coefficients is group
homology**: for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total
space and a representation `A` of `G`, the homology of `B` with coefficients in the local system
associated to `A` is Mathlib's group homology `Hₙ(G, A)`. The singular chains of `E` form a free
resolution of `k` over `k[G]`, and the coinvariants `(A ⊗ C(E; k))_G` are the twisted chains. -/
def twistedHomologyIsoGroupHomology [ContractibleSpace E] (n : ℕ) :
    twistedHomology.{u, u, u} (hG.associatedLocalSystem k A) n ≅ groupHomology A n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  letI := Classical.decEq G
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A)).symm ≪≫
    (groupHomologyIso A n (singularChainsResolution k E G)).symm

variable {A' : Rep.{u} k G}

/-- **The comparison of twisted chains with coinvariant chains is natural in the coefficients**:
for a morphism of representations `f : A ⟶ A'`, the map `(A ⊗ C(E; k))_G ⟶ (A' ⊗ C(E; k))_G`
induced by `f` corresponds to the map of twisted chains induced by the morphism of associated
local systems `IsQuotientCoveringMap.associatedLocalSystemMap`. -/
@[reassoc]
theorem coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality (f : A ⟶ A') :
    haveI := hG.toContinuousConstSMul
    (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map f) _).app
        (singularChainsRep k E G) ≫ (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A').hom =
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom ≫
        twistedChainComplexCoefficientMap.{u, u, u} (hG.associatedLocalSystemMap k f) := by
  have := hG.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ Rep.coinvariantsTensor_hom_ext
    (LinearMap.ext fun a ↦ singularChains_linearMap_ext fun τ ↦ ?_)
  -- Both sides send the class of `a ⊗ τ` to the class of `f a ⊗ e` in the summand of `p ∘ τ`.
  exact (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n (f.hom a) τ).trans
    ((congrArg (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A') n
        ((TopCat.toSSet.map p).app _ τ)).hom
      (hG.associatedLocalSystemMap_app_coinvariantsTensorMk k f _ a _)).symm.trans
    ((twistedChainComplexCoefficientMap_f_ι_apply _ n _ _).symm.trans
      (congrArg ((twistedChainComplexCoefficientMap.{u, u, u}
        (hG.associatedLocalSystemMap k f)).f n).hom
        (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n a τ).symm)))

/-- **The identification of twisted homology with group homology is natural in the
coefficients**: for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible
total space and a morphism of representations `f : A ⟶ A'`, the identifications
`Hₙ(B; A) ≅ Hₙ(G, A)` and `Hₙ(B; A') ≅ Hₙ(G, A')` carry the map on twisted homology induced by
the morphism of associated local systems to Mathlib's map `groupHomology.map (MonoidHom.id G) f`. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_hom_naturality [ContractibleSpace E] (f : A ⟶ A')
    (n : ℕ) :
    twistedHomologyCoefficientMap.{u, u, u} (hG.associatedLocalSystemMap k f) n ≫
        (hG.twistedHomologyIsoGroupHomology k A' n).hom =
      (hG.twistedHomologyIsoGroupHomology k A n).hom ≫ groupHomology.map (MonoidHom.id G) f n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  let := Classical.decEq G
  -- Pass the coefficient map first through `groupHomologyIso`, then through the comparison of
  -- coinvariant chains with twisted chains.
  have h₁ : (groupHomologyIso A n (singularChainsResolution k E G)).inv ≫
      groupHomology.map (MonoidHom.id G) f n =
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex
          ((Rep.coinvariantsTensor k G).map f) _).app (singularChainsResolution k E G).complex) n ≫
          (groupHomologyIso A' n (singularChainsResolution k E G)).inv :=
    (groupHomology.groupHomologyIso_inv_naturality f n _).symm
  have h₂ : (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).inv ≫
      (NatTrans.mapHomologicalComplex ((Rep.coinvariantsTensor k G).map f) _).app
        (singularChainsRep k E G) =
        twistedChainComplexCoefficientMap.{u, u, u} (hG.associatedLocalSystemMap k f) ≫
          (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
      hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality k f]
  have e (C : Rep.{u} k G) : (hG.twistedHomologyIsoGroupHomology k C n).hom =
      HomologicalComplex.homologyMap (hG.coinvariantsTensorSingularChainsRepIsoTwisted k C).inv n ≫
        (groupHomologyIso C n (singularChainsResolution k E G)).inv :=
    (rfl)
  rw [e, e]
  -- `singularChainsResolution` and `singularChainsRep` agree only up to unfolding, so the
  -- remaining steps are explicit transitivity rather than rewriting.
  exact ((HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans
    (congrArg (fun φ ↦ HomologicalComplex.homologyMap φ n ≫ _) h₂.symm)).trans
    (((HomologicalComplex.homologyMap_comp_assoc _ _ _ _).trans (congrArg _ h₁.symm)).trans
      (Category.assoc _ _ _).symm)

/-- The inverse identification of group homology with twisted homology is natural in the
coefficients. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_inv_naturality [ContractibleSpace E] (f : A ⟶ A')
    (n : ℕ) :
    groupHomology.map (MonoidHom.id G) f n ≫ (hG.twistedHomologyIsoGroupHomology k A' n).inv =
      (hG.twistedHomologyIsoGroupHomology k A n).inv ≫
        twistedHomologyCoefficientMap.{u, u, u} (hG.associatedLocalSystemMap k f) n := by
  rw [Iso.comp_inv_eq, Category.assoc, hG.twistedHomologyIsoGroupHomology_hom_naturality k f n,
    Iso.inv_hom_id_assoc]

section LongExactSequence

variable [ContractibleSpace E]

/-- A comparison map from the bar resolution to the singular chains of `E`. It is stated between
`Rep.barComplex` and `singularChainsRep` rather than the complexes of the two resolutions, which
agree with them only up to unfolding, so that composites with it can be rewritten. -/
private def barToSingularChains :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    Rep.barComplex k G ⟶ singularChainsRep k E G :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  ProjectiveResolution.lift (𝟙 _) (Rep.barResolution k G) (singularChainsResolution k E G)

variable (A) in
/-- The chain map from the inhomogeneous chains of `A` to the chains of `B` twisted by the
associated local system inducing `(twistedHomologyIsoGroupHomology k A n).inv`: the identification
of the inhomogeneous chains with `(A ⊗ bar)_G`, followed by a comparison map from the bar
resolution to the singular chains of `E`, and the identification of `(A ⊗ C(E; k))_G` with the
twisted chains. -/
private def chainsToTwisted :
    groupHomology.inhomogeneousChains A ⟶
      twistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  letI := Classical.decEq G
  (groupHomology.inhomogeneousChainsIso A).hom ≫
    (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map (barToSingularChains hG k) ≫
    (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom

variable (A) in
private lemma twistedHomologyIsoGroupHomology_inv_eq_homologyMap (n : ℕ) :
    (hG.twistedHomologyIsoGroupHomology k A n).inv =
      HomologicalComplex.homologyMap (chainsToTwisted hG k A) n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  let := Classical.decEq G
  have hβ := (ProjectiveResolution.lift_commutes_zero (𝟙 _) (Rep.barResolution k G)
    (singularChainsResolution k E G)).trans (Category.comp_id _)
  have h₁ : (hG.twistedHomologyIsoGroupHomology k A n).inv = _ := Iso.trans_inv _ _
  rw [h₁, Iso.symm_inv, Iso.symm_inv, Rep.groupHomologyIso_hom_eq_homologyMap A _ _ hβ]
  -- The bar resolution and `singularChainsResolution` are the complexes `Rep.barComplex` and
  -- `singularChainsRep` only up to unfolding, so the composite is assembled in term mode.
  exact (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    (congrArg (HomologicalComplex.homologyMap · n) (Category.assoc _ _ _))

private lemma chainsToTwisted_naturality (f : A ⟶ A') :
    groupHomology.chainsMap (MonoidHom.id G) f ≫ chainsToTwisted hG k A' =
      chainsToTwisted hG k A ≫
        twistedChainComplexCoefficientMap.{u, u, u} (hG.associatedLocalSystemMap k f) := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  let := Classical.decEq G
  -- Each of the three factors is natural in the coefficients: the inhomogeneous chain
  -- identification, the comparison map tensored with `A`, and the twisted chain identification.
  simp only [chainsToTwisted, Category.assoc]
  rw [TauCeti.groupHomology.inhomogeneousChainsIso_hom_naturality_assoc,
    ← NatTrans.naturality_assoc, coinvariantsTensorSingularChainsRepIsoTwisted_hom_naturality]

variable {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)

/-- **The identification of twisted homology with group homology respects the long exact
sequences**, inverse form: for a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations,
the inverses of the identifications `Hₙ(B; Xᵢ) ≅ Hₙ(G, Xᵢ)` carry Mathlib's connecting map
`groupHomology.δ` to the coefficient connecting map of twisted homology for the short exact
sequence of associated local systems. -/
@[reassoc]
theorem groupHomology_δ_comp_twistedHomologyIsoGroupHomology_inv (n m : ℕ) (h : m + 1 = n) :
    groupHomology.δ hX n m h ≫ (hG.twistedHomologyIsoGroupHomology k X.X₁ m).inv =
      (hG.twistedHomologyIsoGroupHomology k X.X₃ n).inv ≫
        (hG.shortExact_associatedLocalSystem k hX).twistedHomologyδ n m h := by
  rw [twistedHomologyIsoGroupHomology_inv_eq_homologyMap,
    twistedHomologyIsoGroupHomology_inv_eq_homologyMap,
    ShortComplex.ShortExact.twistedHomologyδ_eq_δ]
  -- The chain maps `chainsToTwisted` form a morphism from the short exact sequence of
  -- inhomogeneous chains, whose connecting map is `groupHomology.δ`, to the short exact sequence
  -- of twisted chains, whose connecting map is `twistedHomologyδ`.
  let ψ : X.map (groupHomology.chainsFunctor k G) ⟶
      (X.map (hG.associatedLocalSystemFunctor k)).map (twistedChainComplexFunctor k B) :=
    { τ₁ := chainsToTwisted hG k X.X₁
      τ₂ := chainsToTwisted hG k X.X₂
      τ₃ := chainsToTwisted hG k X.X₃
      comm₁₂ := by
        rw [ShortComplex.map_f, ShortComplex.map_f, twistedChainComplexFunctor_map,
          associatedLocalSystemFunctor_map]
        exact (chainsToTwisted_naturality hG k X.f).symm
      comm₂₃ := by
        rw [ShortComplex.map_g, ShortComplex.map_g, twistedChainComplexFunctor_map,
          associatedLocalSystemFunctor_map]
        exact (chainsToTwisted_naturality hG k X.g).symm }
  exact HomologicalComplex.HomologySequence.δ_naturality ψ
    (groupHomology.map_chainsFunctor_shortExact hX)
    ((hG.shortExact_associatedLocalSystem k hX).map_of_exact _) n m h

/-- **The identification of twisted homology with group homology respects the long exact
sequences**: for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total
space and a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of representations, the identifications
`Hₙ(B; Xᵢ) ≅ Hₙ(G, Xᵢ)` carry the coefficient connecting map `Hₙ(B; X₃) ⟶ Hₘ(B; X₁)`, `m + 1 = n`,
of the short exact sequence of associated local systems to Mathlib's connecting map
`groupHomology.δ`. -/
@[reassoc]
theorem twistedHomologyδ_comp_twistedHomologyIsoGroupHomology_hom (n m : ℕ) (h : m + 1 = n) :
    (hG.shortExact_associatedLocalSystem k hX).twistedHomologyδ n m h ≫
        (hG.twistedHomologyIsoGroupHomology k X.X₁ m).hom =
      (hG.twistedHomologyIsoGroupHomology k X.X₃ n).hom ≫ groupHomology.δ hX n m h := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    groupHomology_δ_comp_twistedHomologyIsoGroupHomology_inv]

end LongExactSequence

section ChangeOfGroups

/-- Two twisted `n`-chains supported on equal simplices of `B`, with the same representation
element and sheets over the initial vertices having the same underlying point in `E`, are equal. -/
private lemma ιTwistedChainComplex_coinvariantsTensorMk_congr (n : ℕ) (a : A)
    {σ₁ σ₂ : (TopCat.toSSet.obj B) _⦋n⦌} (hσ : σ₁ = σ₂)
    (e₁ : p ⁻¹' {(initialVertex σ₁).as}) (e₂ : p ⁻¹' {(initialVertex σ₂).as})
    (he : (e₁ : E) = e₂) (r : k) :
    (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n σ₁).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj (initialVertex σ₁)) a
          (Finsupp.single e₁ r)) =
      (ιTwistedChainComplex.{u, u, u} (hG.associatedLocalSystem k A) n σ₂).hom
        (Rep.coinvariantsTensorMk A ((hG.permutationRepFunctor k).obj (initialVertex σ₂)) a
          (Finsupp.single e₂ r)) := by
  subst hσ
  exact congrArg _ (congrArg _ (congrArg (Finsupp.single · r) (Subtype.ext he)))

variable {F C : _root_.TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

/-- **The comparison of twisted chains with coinvariant chains is natural in the covering and the
group**: for an equivariant map `f : E ⟶ F` along `φ : G →* H` lying over `b : B ⟶ C` and a
compatible morphism `ψ : A ⟶ Rep.res φ M`, the change-of-groups map `(A ⊗ C(E; k))_G ⟶
(M ⊗ C(F; k))_H` corresponds to changing local coefficients along
`IsQuotientCoveringMap.associatedLocalSystemChangeOfGroupsMap` and pushing twisted chains forward
along `b`. No contractibility hypothesis is needed at the chain level. -/
@[reassoc]
theorem coinvariantsTensorSingularChainsRepIsoTwisted_hom_changeOfGroups
    {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    φ.coinvariantsTensorChainMap ψ (singularChainsRepResMap k f hf) ≫
        (hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).hom =
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom ≫
        twistedChainComplexCoefficientMap.{u, u, u}
          (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) ≫
        twistedChainComplexMap.{u, u, u} b (hH.associatedLocalSystem k M) := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ Rep.coinvariantsTensor_hom_ext
    (LinearMap.ext fun a ↦ singularChains_linearMap_ext fun τ ↦ ?_)
  let σ₁ : (TopCat.toSSet.obj C) _⦋n⦌ :=
    (TopCat.toSSet.map b).app _ ((TopCat.toSSet.map p).app _ τ)
  let σ₂ : (TopCat.toSSet.obj C) _⦋n⦌ :=
    (TopCat.toSSet.map q).app _ ((TopCat.toSSet.map f).app _ τ)
  have hσ : σ₁ = σ₂ := by
    simpa only [σ₁, σ₂, Functor.map_comp, NatTrans.comp_app, types_comp_apply] using
      congrArg (fun t ↦ (TopCat.toSSet.map t).app _ τ) hb
  let e' : q ⁻¹' {(initialVertex σ₁).as} :=
    ⟨f (initialSheet τ).1, (ConcreteCategory.congr_hom hb (initialSheet τ).1).symm.trans
      (congrArg b.hom (initialSheet τ).2)⟩
  -- Both sides send `⟦a ⊗ τ⟧` to `⟦ψ a ⊗ f (initialSheet τ)⟧` in the summand of `b ∘ p ∘ τ =
  -- q ∘ f ∘ τ`.
  have hlhs : ((φ.coinvariantsTensorChainMap ψ (singularChainsRepResMap k f hf) ≫
        (hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).hom).f n).hom
      (Rep.coinvariantsTensorMk A ((singularChainsRep k E G).X n) a (simplexChain τ 1)) =
      (ιTwistedChainComplex.{u, u, u} (hH.associatedLocalSystem k M) n σ₂).hom
        (Rep.coinvariantsTensorMk M ((hH.permutationRepFunctor k).obj (initialVertex σ₂))
          (ψ.hom a) (Finsupp.single (initialSheet ((TopCat.toSSet.map f).app _ τ)) 1)) :=
    (congrArg ((hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).hom.f n).hom
      ((φ.coinvariantsTensorChainMap_f_mk ψ (singularChainsRepResMap k f hf) n a
        (simplexChain τ 1)).trans
        (congrArg (Rep.coinvariantsTensorMk M ((singularChainsRep k F H).X n) (ψ.hom a))
          ((singularChainsRepResMap_f_hom_apply k f hf n (simplexChain τ 1)).trans
            (singularChains_map_f_simplexChain f τ 1))))).trans
      (hH.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n (ψ.hom a)
        ((TopCat.toSSet.map f).app _ τ))
  have hrhs : (((hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).hom ≫
        twistedChainComplexCoefficientMap.{u, u, u}
          (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) ≫
        twistedChainComplexMap.{u, u, u} b (hH.associatedLocalSystem k M)).f n).hom
      (Rep.coinvariantsTensorMk A ((singularChainsRep k E G).X n) a (simplexChain τ 1)) =
      (ιTwistedChainComplex.{u, u, u} (hH.associatedLocalSystem k M) n σ₁).hom
        (Rep.coinvariantsTensorMk M ((hH.permutationRepFunctor k).obj (initialVertex σ₁))
          (ψ.hom a) (Finsupp.single e' 1)) :=
    (congrArg ((twistedChainComplexCoefficientMap.{u, u, u}
          (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) ≫
        twistedChainComplexMap.{u, u, u} b (hH.associatedLocalSystem k M)).f n).hom
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_f_mk k n a τ)).trans <|
      (congrArg ((twistedChainComplexMap.{u, u, u} b (hH.associatedLocalSystem k M)).f n).hom
        ((twistedChainComplexCoefficientMap_f_ι_apply
          (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) n
          ((TopCat.toSSet.map p).app _ τ) _).trans
          (congrArg (ιTwistedChainComplex.{u, u, u}
              ((LocalCoefficientSystem.pullback b.hom).obj (hH.associatedLocalSystem k M)) n
              ((TopCat.toSSet.map p).app _ τ)).hom
            (hG.associatedLocalSystemChangeOfGroupsMap_app_coinvariantsTensorMk_single k hH
              f hf b hb ψ (initialVertex ((TopCat.toSSet.map p).app _ τ)) a
              (initialSheet τ) e' rfl 1)))).trans
        (twistedChainComplexMap_f_ι_apply b (hH.associatedLocalSystem k M) n
          ((TopCat.toSSet.map p).app _ τ) _)
  exact hlhs.trans ((ιTwistedChainComplex_coinvariantsTensorMk_congr hH k n (ψ.hom a) hσ e'
    (initialSheet ((TopCat.toSSet.map f).app _ τ)) rfl 1).symm.trans hrhs.symm)

/-- The inverse comparison of twisted chains with coinvariant chains is natural with respect to
equivariant maps of quotient covers. -/
@[reassoc]
theorem coinvariantsTensorSingularChainsRepIsoTwisted_inv_changeOfGroups
    {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    twistedChainComplexCoefficientMap.{u, u, u}
        (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) ≫
      twistedChainComplexMap.{u, u, u} b (hH.associatedLocalSystem k M) ≫
      (hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).inv =
      (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).inv ≫
        φ.coinvariantsTensorChainMap ψ (singularChainsRepResMap k f hf) := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  apply (cancel_mono (hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hG.coinvariantsTensorSingularChainsRepIsoTwisted_hom_changeOfGroups k hH f hf b hb ψ,
    Iso.inv_hom_id_assoc]

/-- **The identification of twisted homology with group homology is natural in the covering and the
group**: for quotient covering maps `p : E ⟶ B` and `q : F ⟶ C` with contractible total spaces, an
equivariant map `f : E ⟶ F` along any group homomorphism `φ : G →* H` lying over `b : B ⟶ C`, and a
compatible morphism `ψ : A ⟶ Rep.res φ M`, the identifications `Hₙ(B; A) ≅ Hₙ(G, A)` and
`Hₙ(C; M) ≅ Hₙ(H, M)` carry the composite of the change-of-groups coefficient map with `b_*` to
Mathlib's change-of-group map `groupHomology.map φ ψ`. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_hom_changeOfGroups [ContractibleSpace E]
    [ContractibleSpace F] {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) (n : ℕ) :
    twistedHomologyCoefficientMap.{u, u, u}
        (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) n ≫
      twistedHomologyMap.{u, u, u} b (hH.associatedLocalSystem k M) n ≫
      (hH.twistedHomologyIsoGroupHomology k M n).hom =
      (hG.twistedHomologyIsoGroupHomology k A n).hom ≫ groupHomology.map φ ψ n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  let := Classical.decEq G
  let := Classical.decEq H
  have h₁ : HomologicalComplex.homologyMap
        (φ.coinvariantsTensorChainMap ψ (singularChainsRepResMap k f hf)) n ≫
      (groupHomologyIso M n (singularChainsResolution k F H)).inv =
      (groupHomologyIso A n (singularChainsResolution k E G)).inv ≫ groupHomology.map φ ψ n :=
    φ.groupHomologyIso_inv_naturality ψ (singularChainsResolution k E G)
      (singularChainsResolution k F H) (singularChainsRepResMap k f hf)
      (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n
  have h₂ := hG.coinvariantsTensorSingularChainsRepIsoTwisted_inv_changeOfGroups k hH f hf b hb ψ
  have eG : (hG.twistedHomologyIsoGroupHomology k A n).hom =
      HomologicalComplex.homologyMap (hG.coinvariantsTensorSingularChainsRepIsoTwisted k A).inv n ≫
        (groupHomologyIso A n (singularChainsResolution k E G)).inv := (rfl)
  have eH : (hH.twistedHomologyIsoGroupHomology k M n).hom =
      HomologicalComplex.homologyMap (hH.coinvariantsTensorSingularChainsRepIsoTwisted k M).inv n ≫
        (groupHomologyIso M n (singularChainsResolution k F H)).inv := (rfl)
  rw [eG, eH]
  -- `singularChainsResolution` and `singularChainsRep` agree only up to unfolding, so the
  -- homology-level steps are assembled by explicit transitivity.
  exact ((HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans <|
    (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).symm.trans <|
    (congrArg (fun t ↦ HomologicalComplex.homologyMap t n ≫ _) h₂).trans <|
    (HomologicalComplex.homologyMap_comp_assoc _ _ _ _).trans <|
    (congrArg _ h₁).trans (Category.assoc _ _ _).symm)

/-- The inverse identification of group homology with twisted homology is natural in the covering
and the group. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_inv_changeOfGroups [ContractibleSpace E]
    [ContractibleSpace F] {M : Rep.{u} k H} (ψ : A ⟶ Rep.res φ M) (n : ℕ) :
    groupHomology.map φ ψ n ≫ (hH.twistedHomologyIsoGroupHomology k M n).inv =
      (hG.twistedHomologyIsoGroupHomology k A n).inv ≫
        twistedHomologyCoefficientMap.{u, u, u}
          (hG.associatedLocalSystemChangeOfGroupsMap k hH f hf b hb ψ) n ≫
        twistedHomologyMap.{u, u, u} b (hH.associatedLocalSystem k M) n := by
  rw [Iso.comp_inv_eq, Category.assoc, Category.assoc,
    hG.twistedHomologyIsoGroupHomology_hom_changeOfGroups k hH f hf b hb ψ n,
    Iso.inv_hom_id_assoc]

/-- Pushing twisted homology forward along `b : B ⟶ C` from the pulled-back associated local system
`b^* L_M` corresponds, via `IsQuotientCoveringMap.associatedLocalSystemPullbackIso`, to the
change-of-group map `groupHomology.map φ (𝟙 (Rep.res φ M))` in group homology. -/
@[reassoc]
theorem twistedHomologyIsoGroupHomology_hom_pullback [ContractibleSpace E] [ContractibleSpace F]
    (M : Rep.{u} k H) (n : ℕ) :
    twistedHomologyMap.{u, u, u} b (hH.associatedLocalSystem k M) n ≫
        (hH.twistedHomologyIsoGroupHomology k M n).hom =
      twistedHomologyCoefficientMap.{u, u, u}
          (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).inv n ≫
        (hG.twistedHomologyIsoGroupHomology k (Rep.res φ M) n).hom ≫
        groupHomology.map φ (𝟙 (Rep.res φ M)) n := by
  have h := hG.twistedHomologyIsoGroupHomology_hom_changeOfGroups k hH f hf b hb
    (𝟙 (Rep.res φ M)) n
  rw [← associatedLocalSystemPullbackIso_hom] at h
  calc
    twistedHomologyMap.{u, u, u} b (hH.associatedLocalSystem k M) n ≫
        (hH.twistedHomologyIsoGroupHomology k M n).hom
      = (twistedHomologyCoefficientMap.{u, u, u}
            (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).inv n ≫
          twistedHomologyCoefficientMap.{u, u, u}
            (hG.associatedLocalSystemPullbackIso k hH f hf b hb M).hom n) ≫
        twistedHomologyMap.{u, u, u} b (hH.associatedLocalSystem k M) n ≫
        (hH.twistedHomologyIsoGroupHomology k M n).hom := by
      rw [← twistedHomologyCoefficientMap_comp, Iso.inv_hom_id,
        twistedHomologyCoefficientMap_id, Category.id_comp]
    _ = _ := by rw [Category.assoc, h]

end ChangeOfGroups

end IsQuotientCoveringMap
