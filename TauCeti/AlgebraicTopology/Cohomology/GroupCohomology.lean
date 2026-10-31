/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.GroupHomology
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups
import TauCeti.RepresentationTheory.Rep.CoinvariantsTensor

/-!
# The singular cohomology of the base of a contractible free cover is group cohomology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, let `k` be a commutative ring and let `M` be a `k`-module. An
`M`-valued singular `n`-cochain `f` of `B` pulls back to the cochain `f ∘ p_*` of `E`, which is
invariant under `G`, that is, a morphism from the representation
`TauCeti.singularChainsRepresentation k E G n` to the trivial representation on `M`. Every
`G`-invariant cochain of `E` arises in this way from exactly one cochain of `B`, because every
singular simplex of `B` lifts to `E` and two lifts differ by an element of `G`. So the singular
cochains of `B` are the complex `Hom_G(C(E; k), M)`
(`IsQuotientCoveringMap.singularCochainComplexIsoLinearYonedaObj`).

If `E` is contractible, the singular chains of `E` are a projective resolution of the trivial
representation `k` (`TauCeti.singularChainsResolution`). Group cohomology is the cohomology of
`Hom_G(P, M)` for any projective resolution `P` of `k` (`groupCohomologyIso`), so the singular
cohomology of `B` with coefficients in `M` is the group cohomology of `G` with coefficients in the
trivial representation `M` (`IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology`):

`Hⁿ(B; M) ≅ Hⁿ(G, M)`.

Both identifications are natural in the coefficients: postcomposing cochains with a linear map
`f : M →ₗ[k] N` corresponds to Mathlib's map `groupCohomology.map (MonoidHom.id G)` induced by `f`
on trivial representations
(`IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology_hom_naturality`).

Both identifications are also natural for maps of quotient covers equivariant along arbitrary group
homomorphisms. For a map `b : B ⟶ C` of bases covered by a map `f : E ⟶ F` of total spaces
equivariant along `φ : G →* H`, pulling cochains back along `b` corresponds to the cochain map
`u ↦ f_* ≫ u` on invariant cochains of the total spaces
(`singularCochainComplexMap_comp_singularCochainComplexIsoLinearYonedaObj_hom`, in the namespace
`IsQuotientCoveringMap`), and, for contractible total spaces, `b^*` on singular cohomology
corresponds to Mathlib's change-of-group map `groupCohomology.map φ` with the identity on the
trivial coefficients `M`
(`IsQuotientCoveringMap.singularCohomologyMap_comp_singularCohomologyIsoGroupCohomology_hom`). No
hypothesis on `φ` is needed.

This is the cohomological counterpart of `IsQuotientCoveringMap.singularHomologyIsoGroupHomology`.

## Main definitions

* `IsQuotientCoveringMap.singularCochainComplexIsoLinearYonedaObj`: the singular cochains of `B`
  are the `G`-invariant cochains of `E`.
* `IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology`: for contractible `E`, the singular
  cohomology of `B` is the group cohomology of `G` with trivial coefficients.

## Main results

* `IsQuotientCoveringMap.singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply`: the
  comparison of cochains is pulling back along `p`.
* `IsQuotientCoveringMap.singularCochainComplexIsoLinearYonedaObj_inv_f_hom_apply`: its inverse
  descends an invariant cochain of `E` along `p`.
* `IsQuotientCoveringMap.singularCochainComplexIsoLinearYonedaObj_hom_naturality`,
  `IsQuotientCoveringMap.singularCohomologyIsoGroupCohomology_hom_naturality`: the comparisons of
  cochains and of cohomology are natural in the coefficients.
* `singularCochainComplexMap_comp_singularCochainComplexIsoLinearYonedaObj_hom`,
  `IsQuotientCoveringMap.singularCohomologyMap_comp_singularCohomologyIsoGroupCohomology_hom`: the
  comparisons of cochains and of cohomology are natural in the covering and the group.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4, Section III.1, and
  Section III.8.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Simplicial TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M]
  [Module k M]

/-- Pulling back along `p` identifies the `M`-valued singular `n`-cochains of the base with the
`G`-invariant cochains of the total space: by `singularChainsRepCoinvariantsTensorIso`, they are
the `M`-valued maps on the coinvariants `(k ⊗ Cₙ(E))_G`, which are the morphisms
`k ⊗ Cₙ(E) ⟶ M` of representations to the trivial representation
(`Rep.coinvariantsHomLinearEquiv`). -/
private def singularCochainLinearEquiv (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (((singularChains k).obj B).X n ⟶ ModuleCat.of k M) ≃ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M) :=
  haveI := hG.toContinuousConstSMul
  Linear.homCongr k
      (HomologicalComplex.Hom.isoApp (hG.singularChainsRepCoinvariantsTensorIso k) n).symm
      (Iso.refl _) ≪≫ₗ
    Rep.coinvariantsHomLinearEquiv M _ ≪≫ₗ
    Linear.homCongr k (λ_ _) (Iso.refl _)

/-- The pulled-back cochain evaluates a chain of the total space on its image in the base. -/
private lemma singularCochainLinearEquiv_apply_hom_apply (n : ℕ)
    (f : ((singularChains k).obj B).X n ⟶ ModuleCat.of k M) (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    (singularCochainLinearEquiv hG k M n f).hom c = f (((singularChains k).map p).f n c) := by
  have := hG.toContinuousConstSMul
  -- The equivalence sends `f` to the cochain `c ↦ f (φ (1 ⊗ c))`, where `φ` is the comparison
  -- `(k ⊗ Cₙ(E))_G ≅ Cₙ(B)`, which sends the class of `1 ⊗ c` to `p_* c`. The equivalence is
  -- unfolded by `change` rather than rewritten with `Linear.homCongr_apply` and the unitor's simp
  -- lemmas: `λ_` is stated for `𝟙_ (Rep k G) ⊗ Cₙ(E)`, while the coinvariants of
  -- `singularChainsRepCoinvariantsTensorIso` are taken of `Rep.trivial k G k ⊗ Cₙ(E)`, and of
  -- `Rep.of (singularChainsRepresentation k E G n)` rather than `(singularChainsRep k E G).X n`.
  -- These objects agree only by definition, so the composite is not type-correct at reducible
  -- transparency and those lemmas do not fire on it. The middle step is evaluated by
  -- `Rep.coinvariantsHomLinearEquiv_apply_hom_apply`, applied up to definitional equality.
  change (Rep.coinvariantsHomLinearEquiv M (Rep.trivial k G k ⊗ (singularChainsRep k E G).X n)
    ((HomologicalComplex.Hom.isoApp (hG.singularChainsRepCoinvariantsTensorIso k) n).hom ≫
      f ≫ 𝟙 _)).hom ((λ_ (Rep.of (singularChainsRepresentation k E G n))).inv.hom c) = _
  refine (Rep.coinvariantsHomLinearEquiv_apply_hom_apply M _ _).trans ?_
  change f ((HomologicalComplex.Hom.isoApp (hG.singularChainsRepCoinvariantsTensorIso k) n).hom
    (Rep.coinvariantsTensorMk _ _ 1 c)) = _
  exact congrArg f.hom
    ((singularChainsRepCoinvariantsTensorIso_hom_f_coinvariantsTensorMk hG k n 1 c).trans
      (one_smul _ _))

/-- **The singular cochains of the base of a quotient covering are the invariant cochains of the
total space**: for the quotient covering map `p : E ⟶ B` of an action of `G`, pulling back along
`p` is an isomorphism from the complex of `M`-valued singular cochains of `B` to the complex
`Hom_G(C(E; k), M)` of morphisms to the trivial representation `M`. -/
def singularCochainComplexIsoLinearYonedaObj :
    haveI := hG.toContinuousConstSMul
    B.singularCochainComplex (ModuleCat.of k k) k (ModuleCat.of k M) ≅
      (singularChainsRep k E G).linearYonedaObj k (Rep.trivial k G M) :=
  haveI := hG.toContinuousConstSMul
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (singularCochainLinearEquiv hG k M n).toModuleIso)
    fun i j (h : i + 1 = j) ↦ by
      subst h
      refine ModuleCat.hom_ext <| LinearMap.ext fun f ↦ Rep.hom_ext <|
        Representation.IntertwiningMap.ext <| LinearMap.ext fun c ↦ ?_
      -- Both sides evaluate `f` on the image of the chain `c` in the base, before and after
      -- taking boundaries: pushing chains forward along `p` commutes with the boundary.
      have h : ((singularChains k).map p).f i (((singularChains k).obj E).d (i + 1) i c) =
          ((singularChains k).obj B).d (i + 1) i (((singularChains k).map p).f (i + 1) c) :=
        (ConcreteCategory.congr_hom (((singularChains k).map p).comm (i + 1) i) c).symm
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply, TauCeti.ChainComplex.linearYonedaObj_d_apply,
        TauCeti.ChainComplex.linearYonedaObj_d_apply, singularChainsRep_d]
      -- Unfold the components of the comparison to the degreewise equivalences. This is a
      -- `change` rather than a rewrite with `ModuleCat.ofHom_apply` and `Rep.hom_comp_toLinearMap`:
      -- the goal composes `singularChainsRepDifferential`, between the representations
      -- `Rep.of (singularChainsRepresentation k E G n)`, with maps out of the terms
      -- `(singularChainsRep k E G).X n`. These agree only by definition, so, as in
      -- `singularCochainLinearEquiv_apply_hom_apply`, the goal is not type-correct at reducible
      -- transparency and those lemmas do not fire on it.
      change (singularCochainLinearEquiv hG k M i f).hom
          ((singularChainsRepDifferential k E G i).hom c) =
        (singularCochainLinearEquiv hG k M (i + 1)
          (((singularChains k).obj B).d (i + 1) i ≫ f)).hom c
      have hd := congrArg (((singularChains k).map p).f i)
        (singularChainsRepDifferential_hom_apply k E G i c)
      exact (singularCochainLinearEquiv_apply_hom_apply hG k M i f _).trans <|
        (congrArg f.hom (hd.trans h)).trans (singularCochainLinearEquiv_apply_hom_apply hG k M
          (i + 1) (((singularChains k).obj B).d (i + 1) i ≫ f) c).symm

/-- The comparison of cochains pulls an `M`-valued cochain `f` of the base back to the cochain
`f ∘ p_*` of the total space. -/
@[simp]
lemma singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply (n : ℕ)
    (f : ((singularChains k).obj B).X n ⟶ ModuleCat.of k M) (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ((hG.singularCochainComplexIsoLinearYonedaObj k M).hom.f n f).hom c =
      f (((singularChains k).map p).f n c) :=
  singularCochainLinearEquiv_apply_hom_apply hG k M n f c

/-- The inverse comparison descends a `G`-invariant cochain `f` of the total space to the cochain
of the base whose value on the image `p_* c` of a chain `c` is `f c`. -/
lemma singularCochainComplexIsoLinearYonedaObj_inv_f_hom_apply (n : ℕ)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ∀ f : Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M,
      ModuleCat.Hom.hom (A := ((singularChains k).obj B).X n) (B := ModuleCat.of k M)
          ((hG.singularCochainComplexIsoLinearYonedaObj k M).inv.f n f)
          (((singularChains k).map p).f n c) = f.hom c := fun f ↦ by
  -- Pulling back the descended cochain recovers `f`, since the comparison is an isomorphism.
  have h := singularCochainLinearEquiv_apply_hom_apply hG k M n
    ((singularCochainLinearEquiv hG k M n).symm f) c
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

variable {N : Type u} [AddCommGroup N] [Module k N]

/-- **The comparison of cochains is natural in the coefficients**: postcomposing an `M`-valued
cochain of the base with a linear map `f : M →ₗ[k] N` and then pulling back along `p` is pulling
back first and then postcomposing with `f`, viewed as a morphism of trivial representations. -/
@[reassoc]
lemma singularCochainComplexIsoLinearYonedaObj_hom_naturality (f : M →ₗ[k] N) :
    haveI := hG.toContinuousConstSMul
    ((singularChains k).obj B).linearYonedaObjMap k (ModuleCat.ofHom f) ≫
        (hG.singularCochainComplexIsoLinearYonedaObj k N).hom =
      (hG.singularCochainComplexIsoLinearYonedaObj k M).hom ≫
        (singularChainsRep k E G).linearYonedaObjMap k
          ((Rep.trivialFunctor k G).map (ModuleCat.ofHom f)) := by
  have := hG.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun g ↦ ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun c ↦ ?_
  -- Both cochains of the total space send a chain `c` to `f (g (p_* c))`: the coefficient maps
  -- are postcomposition with `f` (`linearYonedaObjMap_f_hom_apply`), and the comparison is
  -- pulling back along `p`. The rewrites are applied through `congrArg`, since the composites are
  -- stated between `linearYonedaObj` complexes and singular cochain complexes, which agree only by
  -- unfolding, so `simp` cannot split them into their components.
  exact (congrArg
      (fun x ↦ (((hG.singularCochainComplexIsoLinearYonedaObj k N).hom.f n).hom x).hom c)
    (((singularChains k).obj B).linearYonedaObjMap_f_hom_apply k (ModuleCat.ofHom f) n g)).trans <|
    (hG.singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply k N n _ c).trans <|
    (congrArg f (hG.singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply k M n g c).symm).trans
      (congrArg (fun x ↦ x.hom c) ((singularChainsRep k E G).linearYonedaObjMap_f_hom_apply k
        ((Rep.trivialFunctor k G).map (ModuleCat.ofHom f)) n
        (((hG.singularCochainComplexIsoLinearYonedaObj k M).hom.f n).hom g))).symm

/-- **The singular cohomology of the base of a contractible free covering is group cohomology**:
for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total space, the
singular cohomology `Hⁿ(B; M)` with coefficients in a `k`-module `M` is Mathlib's group cohomology
`Hⁿ(G, M)` of the trivial representation `M`. The singular chains of `E` form a free resolution of
`k` over `k[G]`, whose `G`-invariant `M`-valued cochains are the singular cochains of `B`. -/
def singularCohomologyIsoGroupCohomology [ContractibleSpace E] (n : ℕ) :
    B.singularCohomology (ModuleCat.of k k) k (ModuleCat.of k M) n ≅
      groupCohomology (Rep.trivial k G M) n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (hG.singularCochainComplexIsoLinearYonedaObj k M) ≪≫
    (groupCohomologyIso _ n (singularChainsResolution k E G)).symm

/-- The comparison `Hⁿ(B; M) ≅ Hⁿ(G, M)` is the cohomology of the comparison of cochains followed
by the inverse of `groupCohomologyIso` for the resolution by singular chains of `E`. -/
lemma singularCohomologyIsoGroupCohomology_hom_eq [ContractibleSpace E] (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    (hG.singularCohomologyIsoGroupCohomology k M n).hom =
      HomologicalComplex.homologyMap (hG.singularCochainComplexIsoLinearYonedaObj k M).hom n ≫
        (groupCohomologyIso _ n (singularChainsResolution k E G)).inv :=
  Iso.trans_hom _ _

/-- **The comparison of singular cohomology with group cohomology is natural in the
coefficients**: for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible
total space and a `k`-linear map `f : M →ₗ[k] N`, the isomorphisms `Hⁿ(B; M) ≅ Hⁿ(G, M)` and
`Hⁿ(B; N) ≅ Hⁿ(G, N)` carry the map on singular cohomology induced by postcomposing cochains with
`f` to Mathlib's map `groupCohomology.map (MonoidHom.id G)` induced by `f` on trivial
representations. -/
@[reassoc]
theorem singularCohomologyIsoGroupCohomology_hom_naturality [ContractibleSpace E] (f : M →ₗ[k] N)
    (n : ℕ) :
    HomologicalComplex.homologyMap
        (((singularChains k).obj B).linearYonedaObjMap k (ModuleCat.ofHom f)) n ≫
        (hG.singularCohomologyIsoGroupCohomology k N n).hom =
      (hG.singularCohomologyIsoGroupCohomology k M n).hom ≫
        groupCohomology.map (MonoidHom.id G) ((Rep.trivialFunctor k G).map (ModuleCat.ofHom f))
          n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  -- The comparison is the cohomology of the comparison of cochains followed by the inverse of
  -- `groupCohomologyIso` for the resolution by singular chains of `E`, and both are natural.
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (hG.singularCochainComplexIsoLinearYonedaObj_hom_naturality k M f)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  rw [singularCohomologyIsoGroupCohomology_hom_eq, singularCohomologyIsoGroupCohomology_hom_eq]
  -- The two naturality squares are pasted in term mode: the complex of
  -- `singularChainsResolution k E G` is `singularChainsRep k E G` only by unfolding, so the
  -- composites do not typecheck at the transparency `rw` uses.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (TauCeti.Rep.groupCohomologyIso_inv_naturality _
      (singularChainsResolution k E G) n)).trans (Category.assoc _ _ _).symm


section ChangeOfGroups

variable {F C : TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H} (f : E ⟶ F) (hf : ∀ g x, f (g • x) = φ g • f x)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

include hb in
/-- **The comparison of cochains is natural for maps of quotient covers.** For quotient covers
`p : E ⟶ B` and `q : F ⟶ C`, a map `f : E ⟶ F` equivariant along any group homomorphism
`φ : G →* H` and lying over `b : B ⟶ C`, pulling an `M`-valued cochain of `C` back along `b` and
then along `p` is pulling it back along `q` and then along `f`, viewed as the change-of-group map
`MonoidHom.linearYonedaObjMap` of invariant cochains with the identity on the trivial
coefficients `M`. -/
@[reassoc]
lemma singularCochainComplexMap_comp_singularCochainComplexIsoLinearYonedaObj_hom :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    TopCat.singularCochainComplexMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k M) b ≫
        (hG.singularCochainComplexIsoLinearYonedaObj k M).hom =
      (hH.singularCochainComplexIsoLinearYonedaObj k M).hom ≫
        φ.linearYonedaObjMap (A := Rep.trivial k H M) (B := Rep.trivial k G M)
          (𝟙 (Rep.trivial k G M)) (singularChainsRepResMap k f hf) := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun (u : ((singularChains k).obj C).X n ⟶ ModuleCat.of k M) ↦ ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <| LinearMap.ext fun c ↦ ?_
  have hc : ((singularChains k).map b).f n (((singularChains k).map p).f n c) =
      ((singularChains k).map q).f n (((singularChains k).map f).f n c) := by
    have h := ConcreteCategory.congr_hom (congrArg (fun t ↦ ((singularChains k).map t).f n) hb) c
    simp only [Functor.map_comp, HomologicalComplex.comp_f] at h
    exact h
  -- Both cochains of `E` send a chain `c` to the value of `u` on its image in `C`, through `B`
  -- on the left and through `F` on the right. The composites are stated between singular cochain
  -- complexes and `linearYonedaObj` complexes, which agree only by unfolding, so the comparison
  -- lemmas are applied in term mode rather than by `simp`.
  have hY (w : Rep.of (singularChainsRepresentation k F H n) ⟶ Rep.trivial k H M) :
      (((φ.linearYonedaObjMap (A := Rep.trivial k H M) (B := Rep.trivial k G M)
        (𝟙 (Rep.trivial k G M)) (singularChainsRepResMap k f hf)).f n) w).hom c =
        w.hom (((singularChains k).map f).f n c) :=
    -- The cochain map precomposes with the pushforward `f_*` of chains; composing morphisms of
    -- representations and evaluating is evaluating in turn.
    (congrArg (fun t : (singularChainsRep k E G).X n ⟶ Rep.trivial k G M ↦ t.hom c)
      (φ.linearYonedaObjMap_f_apply (A := Rep.trivial k H M) (B := Rep.trivial k G M)
        (𝟙 (Rep.trivial k G M)) (singularChainsRepResMap k f hf) n w)).trans
      (congrArg w.hom (singularChainsRepResMap_f_hom_apply k f hf n c))
  exact (hG.singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply k M n _ c).trans <|
    (congrArg (fun x ↦ u x) hc).trans <|
      (hH.singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply k M n u _).symm.trans (hY _).symm

include hf hb in
/-- **The comparison of singular cohomology with group cohomology is natural in the covering and
the group.** For quotient covers `p : E ⟶ B` and `q : F ⟶ C` with contractible total spaces, a map
`f : E ⟶ F` equivariant along any group homomorphism `φ : G →* H` and lying over `b : B ⟶ C`, the
identifications `Hⁿ(C; M) ≅ Hⁿ(H, M)` and `Hⁿ(B; M) ≅ Hⁿ(G, M)` carry `b^*` to Mathlib's
change-of-group map `groupCohomology.map φ`, with the identity on the trivial coefficients `M`. -/
@[reassoc]
theorem singularCohomologyMap_comp_singularCohomologyIsoGroupCohomology_hom [ContractibleSpace E]
    [ContractibleSpace F] (n : ℕ) :
    TopCat.singularCohomologyMap (R := ModuleCat.of k k) (k := k) (M := ModuleCat.of k M) b n ≫
        (hG.singularCohomologyIsoGroupCohomology k M n).hom =
      (hH.singularCohomologyIsoGroupCohomology k M n).hom ≫
        groupCohomology.map φ (A := Rep.trivial k H M) (B := Rep.trivial k G M)
          (𝟙 (Rep.trivial k G M)) n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  -- The comparison is the cohomology of the comparison of cochains followed by the inverse of
  -- `groupCohomologyIso` for the resolution by singular chains, and both are natural.
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (hG.singularCochainComplexMap_comp_singularCochainComplexIsoLinearYonedaObj_hom k M hH f hf b
        hb)).trans (HomologicalComplex.homologyMap_comp _ _ n)
  rw [hG.singularCohomologyIsoGroupCohomology_hom_eq,
    hH.singularCohomologyIsoGroupCohomology_hom_eq]
  -- The two naturality squares are pasted in term mode: the complex of
  -- `singularChainsResolution k E G` is `singularChainsRep k E G` only by unfolding, so the
  -- composites do not typecheck at the transparency `rw` uses.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) (φ.groupCohomologyIso_inv_naturality (A := Rep.trivial k H M)
      (B := Rep.trivial k G M) (𝟙 (Rep.trivial k G M)) (singularChainsResolution k E G)
      (singularChainsResolution k F H) (singularChainsRepResMap k f hf)
      (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
    (Category.assoc _ _ _).symm

end ChangeOfGroups

end IsQuotientCoveringMap
