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

open CategoryTheory Simplicial TauCeti

universe u

namespace IsQuotientCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (M : Type u) [AddCommGroup M]
  [Module k M]

/-- Pulling back an `M`-valued singular `n`-cochain `f` of the base along `p` gives the
`G`-invariant cochain `f ∘ p_*` of the total space, a morphism to the trivial representation. -/
private def singularCochainPullback (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (((singularChains k).obj B).X n ⟶ ModuleCat.of k M) →ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M) :=
  haveI := hG.toContinuousConstSMul
  { toFun f := Rep.ofHom
      { toLinearMap := f.hom ∘ₗ (((singularChains k).map p).f n).hom
        isIntertwining' g := LinearMap.ext fun c ↦
          congrArg f.hom (singularChains_map_f_singularChainsRepresentation hG k n g c) }
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- The pulled-back cochain evaluates a chain of the total space on its image in the base. -/
private lemma singularCochainPullback_hom_apply (n : ℕ)
    (f : ((singularChains k).obj B).X n ⟶ ModuleCat.of k M) (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    (singularCochainPullback hG k M n f).hom c = f (((singularChains k).map p).f n c) :=
  (rfl)

/-- A `G`-invariant `M`-valued singular `n`-cochain of the total space descends to the base: its
value on a simplex of the base is its value on a chosen lift. -/
private def singularCochainDescend (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M) →
      (((singularChains k).obj B).X n ⟶ ModuleCat.of k M) :=
  haveI := hG.toContinuousConstSMul
  fun f ↦ ModuleCat.ofHom <| chainsDesc fun τ ↦
    f.hom (simplexChain (hG.toSSet_map_app_surjective _ τ).choose 1)

/-- The descended cochain takes a simplex of the base to the value on its chosen lift. -/
private lemma singularCochainDescend_simplexChain (n : ℕ) (τ : (TopCat.toSSet.obj B) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    ∀ f : Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M,
      singularCochainDescend hG k M n f (simplexChain τ 1) =
        f.hom (simplexChain (hG.toSSet_map_app_surjective _ τ).choose 1) :=
  fun _ ↦ chainsDesc_simplexChain_one _ τ

/-- Pulling back along `p` identifies the `M`-valued singular `n`-cochains of the base with the
`G`-invariant cochains of the total space. -/
private def singularCochainLinearEquiv (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (((singularChains k).obj B).X n ⟶ ModuleCat.of k M) ≃ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M) :=
  haveI := hG.toContinuousConstSMul
  { singularCochainPullback hG k M n with
    invFun := singularCochainDescend hG k M n
    left_inv f := ModuleCat.hom_ext <| singularChains_linearMap_ext fun τ ↦ by
      rw [singularCochainDescend_simplexChain, LinearMap.toFun_eq_coe,
        singularCochainPullback_hom_apply, singularChains_map_f_simplexChain,
        (hG.toSSet_map_app_surjective _ τ).choose_spec]
    right_inv f := Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      singularChains_linearMap_ext fun σ ↦ by
        -- The chosen lift of `p_* σ` is a translate `g • σ` of `σ`, on which the invariant
        -- cochain `f` takes the same value as on `σ`.
        obtain ⟨g, hg⟩ := (hG.toSSet_map_app_eq_iff _ σ).1
          (hG.toSSet_map_app_surjective _ ((TopCat.toSSet.map p).app _ σ)).choose_spec
        simp only [LinearMap.toFun_eq_coe, Representation.IntertwiningMap.toLinearMap_apply]
        rw [singularCochainPullback_hom_apply, singularChains_map_f_simplexChain,
          singularCochainDescend_simplexChain, ← hg,
          ← singularChainsRepresentation_simplexChain]
        exact (Rep.hom_comm_apply f g _).trans (Rep.trivial_ρ_apply g _) }

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
      exact congrArg f.hom
        ((congrArg _ (singularChainsRepDifferential_hom_apply k E G i c)).trans h)

/-- The comparison of cochains pulls an `M`-valued cochain `f` of the base back to the cochain
`f ∘ p_*` of the total space. -/
@[simp]
lemma singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply (n : ℕ)
    (f : ((singularChains k).obj B).X n ⟶ ModuleCat.of k M) (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ((hG.singularCochainComplexIsoLinearYonedaObj k M).hom.f n f).hom c =
      f (((singularChains k).map p).f n c) :=
  (rfl)

/-- The inverse comparison descends a `G`-invariant cochain `f` of the total space to the cochain
of the base whose value on the image `p_* c` of a chain `c` is `f c`. -/
lemma singularCochainComplexIsoLinearYonedaObj_inv_f_hom_apply (n : ℕ)
    (c : ((singularChains k).obj E).X n) :
    haveI := hG.toContinuousConstSMul
    ∀ f : Rep.of (singularChainsRepresentation k E G n) ⟶ Rep.trivial k G M,
      ModuleCat.Hom.hom (A := ((singularChains k).obj B).X n) (B := ModuleCat.of k M)
          ((hG.singularCochainComplexIsoLinearYonedaObj k M).inv.f n f)
          (((singularChains k).map p).f n c) = f.hom c := fun f ↦ by
  have := hG.toContinuousConstSMul
  refine (singularCochainComplexIsoLinearYonedaObj_hom_f_hom_apply hG k M n _ c).symm.trans ?_
  -- Pulling back the descended cochain recovers `f`, since the comparison is an isomorphism.
  exact congrArg (fun φ ↦ Rep.Hom.hom φ c) (ConcreteCategory.congr_hom
    (HomologicalComplex.congr_hom (hG.singularCochainComplexIsoLinearYonedaObj k M).inv_hom_id n) f)

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
