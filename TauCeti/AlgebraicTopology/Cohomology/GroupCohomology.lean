/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.GroupHomology

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

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section II.4 and Section III.1.
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
`k ⊗ Cₙ(E) ⟶ M` of representations to the trivial representation (`Rep.coinvariantsAdjunction`). -/
private def singularCochainLinearEquiv (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (((singularChains k).obj B).X n ⟶ ModuleCat.of k M) ≃ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M) :=
  haveI := hG.toContinuousConstSMul
  Linear.homCongr k
      (HomologicalComplex.Hom.isoApp (hG.singularChainsRepCoinvariantsTensorIso k) n).symm
      (Iso.refl _) ≪≫ₗ
    { (Rep.coinvariantsAdjunction k G).homEquiv _ (ModuleCat.of k M) with
      map_add' _ _ := by ext; simp [Rep.add_hom, Adjunction.homEquiv_unit]
      map_smul' _ _ := by ext; simp [Rep.smul_hom, Adjunction.homEquiv_unit] } ≪≫ₗ
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
  -- transparency and those lemmas do not fire on it.
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

end IsQuotientCoveringMap
