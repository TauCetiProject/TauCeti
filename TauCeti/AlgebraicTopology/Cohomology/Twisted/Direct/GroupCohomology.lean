/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Coefficients
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Pullback
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Pullback
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.EquivariantMap
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ChangeOfGroups

/-!
# Local-coefficient cohomology of the base of a contractible free cover is group cohomology

Let `p : E ⟶ B` be the quotient covering map of an action of a group `G` on `E`, in the sense of
Mathlib's `IsQuotientCoveringMap`, let `k` be a commutative ring, and let `A` be a `k`-linear
representation of `G`. The direct singular cochain complex
`TauCeti.LocalCoefficientSystem.cochainComplex` of `B` with coefficients in the associated local
system `L_A = hG.associatedLocalSystem k A` assigns to each singular `n`-simplex of `B` an element
of the fibre of `L_A` at its initial vertex, without dualizing `A`.

Pulling a direct cochain of `B` back along `p` and applying the canonical trivialization
`IsQuotientCoveringMap.associatedLocalSystemPullbackIso` on `E` assigns to each singular
`n`-simplex `τ` of `E` an element of `A`, namely the coordinate of `c (p ∘ τ)` in the initial sheet
of `τ`. Translating `τ` by `g : G` leaves `p ∘ τ` fixed and multiplies the sheet coordinate by
`A.ρ g` (`IsQuotientCoveringMap.associatedLocalSystemFiberIso_hom_smul`), so the linear extension to
singular chains of `E` is a morphism of representations `Cₙ(E; k) ⟶ A`. Conversely, every singular
simplex of `B` lifts to `E` and any two lifts differ by an element of `G`, so every `G`-equivariant
cochain on `E` descends uniquely to a direct cochain of `B` valued in `L_A`. This gives an
isomorphism of cochain complexes (`IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj`):

`C•(B; L_A) ≅ Hom_G(C•(E; k), A)`.

When `E` is contractible, its singular chains form a projective resolution of the trivial
representation (`TauCeti.singularChainsResolution`), and composing with `groupCohomologyIso`
identifies the direct local-coefficient cohomology of `B` with Mathlib's group cohomology of `A`
(`IsQuotientCoveringMap.cohomologyIsoGroupCohomology`):

`Hⁿ(B; L_A) ≅ Hⁿ(G, A)`.

Unlike the fixed-value dual comparison `IsQuotientCoveringMap.twistedCohomologyIsoGroupCohomology`,
this identification takes values in `A` itself rather than `Homₖ(A, N)`, and its compatibility with
coefficient long exact sequences requires no projectivity or flatness assumption on the
representations (`IsQuotientCoveringMap.cohomologyδ_comp_cohomologyIsoGroupCohomology_hom`).

Both the cochain isomorphism and the cohomology isomorphism are natural in the representation `A`
and contravariantly natural with respect to equivariant maps of quotient covers along arbitrary
group homomorphisms `φ : G →* H` and compatible morphisms `ξ : Rep.res φ D ⟶ A`
(`IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality_over`).

## Main definitions

* `IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj`: direct cochains of `B` valued in `L_A`
  are isomorphic to `Hom_G(C•(E; k), A)`.
* `IsQuotientCoveringMap.cohomologyIsoGroupCohomology`: for contractible `E`, the cohomology
  `Hⁿ(B; L_A)` is Mathlib's `groupCohomology A n`.
* `IsQuotientCoveringMap.associatedCochainComplexMap`,
  `IsQuotientCoveringMap.associatedCohomologyMap`: the contravariant change-of-groups maps on
  direct cochains and cohomology along an equivariant map of quotient covers and a compatible
  coefficient morphism `ξ : Rep.res φ D ⟶ A`.

## Main results

* `IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj_hom_f_simplexChain`,
  `IsQuotientCoveringMap.cochainComplexEval_cochainComplexIsoLinearYonedaObj_inv_f`: explicit
  sheet-coordinate formulas for the forward and inverse cochain comparisons.
* `IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj_hom_naturality`,
  `IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality`: naturality in the
  coefficient representation.
* `IsQuotientCoveringMap.cohomologyδ_comp_cohomologyIsoGroupCohomology_hom`,
  `IsQuotientCoveringMap.groupCohomology_δ_comp_cohomologyIsoGroupCohomology_inv`: compatibility
  with the coefficient connecting maps, with no projectivity hypothesis.
* `IsQuotientCoveringMap.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom`,
  `IsQuotientCoveringMap.cohomologyIsoGroupCohomology_hom_naturality_over`: naturality with respect
  to equivariant maps of quotient covers along arbitrary group homomorphisms.
* `IsQuotientCoveringMap.cohomologyδ_comp_associatedCohomologyMap`: naturality of the geometric
  connecting map with respect to change of groups on quotient covers.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4, III.1, and III.8.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory Simplicial TauCeti TauCeti.TopCat
  TauCeti.LocalCoefficientSystem

universe u

namespace IsQuotientCoveringMap

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {G : Type u} [Group G] [MulAction G E]
  (hG : IsQuotientCoveringMap p G) (k : Type u) [CommRing k] (A : Rep.{u} k G)

/-- Pullback of direct cochains to the covering space followed by the canonical sheet
trivialization into the constant coefficient system with fibre `A`. -/
private def pullbackTrivialize :
    (hG.associatedLocalSystem k A).cochainComplex ⟶
      ((constantFunctor E).obj (ModuleCat.of k A)).cochainComplex :=
  cochainComplexPullback p (hG.associatedLocalSystem k A) ≫
    cochainComplexCoefficientMap (hG.associatedLocalSystemPullbackIso k A).hom

/-- Evaluating a pulled-back and trivialized cochain on a simplex `τ` of `E`, typed directly in the
underlying module `A`. -/
private def pullbackTrivializeAt (n : ℕ) (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    (hG.associatedLocalSystem k A).cochainComplex.X n →ₗ[k] A where
  toFun c := cochainComplexEval ((constantFunctor E).obj (ModuleCat.of k A)) n τ
    ((pullbackTrivialize hG k A).f n c)
  map_add' c d := by
    rw [map_add, map_add]
    rfl
  map_smul' r c := by
    rw [map_smul, map_smul]
    rfl

/-- Evaluating a pulled-back and trivialized cochain on a simplex `τ` of `E` reads the coordinate
of `c (p ∘ τ)` in the initial sheet of `τ`. -/
private lemma pullbackTrivializeAt_apply (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    pullbackTrivializeAt hG k A n τ c =
      (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c) := by
  change cochainComplexEval ((constantFunctor E).obj (ModuleCat.of k A)) n τ
      ((pullbackTrivialize hG k A).f n c) = _
  simp only [pullbackTrivialize, HomologicalComplex.comp_f, ModuleCat.comp_apply,
    cochainComplexCoefficientMap_eval.{u, u, u}, associatedLocalSystemPullbackIso_hom_app,
    cochainComplexPullback_eval.{u, u, u}]
  rfl

/-- Sheet coordinates on equal base simplices transform by `A.ρ g` when the sheet is translated
by `g`. -/
private lemma fiberIso_hom_eval_smul {n : ℕ}
    {σ₁ σ₀ : (_root_.TopCat.toSSet.obj B) _⦋n⦌} (hσ : σ₁ = σ₀)
    (e₁ : p ⁻¹' {(initialVertex σ₁).as}) (e₀ : p ⁻¹' {(initialVertex σ₀).as})
    (g : G) (he : (e₁ : E) = g • (e₀ : E))
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n) :
    (hG.associatedLocalSystemFiberIso k A e₁).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₁ c) =
      A.ρ g ((hG.associatedLocalSystemFiberIso k A e₀).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₀ c)) := by
  subst hσ
  let := hG.mulActionFiber (initialVertex σ₁).as
  obtain rfl : e₁ = g • e₀ := Subtype.ext he
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (hG.associatedLocalSystemFiberIso_hom_smul k A (x := initialVertex σ₁) e₀ g)) _

/-- Sheet coordinates on equal base simplices depend only on the simplex and underlying point in
the total space. -/
private lemma fiberIso_hom_eval_congr {n : ℕ}
    {σ₁ σ₀ : (_root_.TopCat.toSSet.obj B) _⦋n⦌} (hσ : σ₁ = σ₀)
    (e₁ : p ⁻¹' {(initialVertex σ₁).as}) (e₀ : p ⁻¹' {(initialVertex σ₀).as})
    (he : (e₁ : E) = (e₀ : E))
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n) :
    (hG.associatedLocalSystemFiberIso k A e₁).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₁ c) =
      (hG.associatedLocalSystemFiberIso k A e₀).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n σ₀ c) := by
  subst hσ
  obtain rfl : e₁ = e₀ := Subtype.ext he
  rfl

/-- Translating a simplex `τ` of `E` by `g` multiplies its trivialized cochain value by `A.ρ g`. -/
private lemma pullbackTrivializeAt_smul_simplex (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n) (g : G)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    pullbackTrivializeAt hG k A n (g • τ) c =
      A.ρ g (pullbackTrivializeAt hG k A n τ c) := by
  have := hG.toContinuousConstSMul
  rw [pullbackTrivializeAt_apply, pullbackTrivializeAt_apply]
  refine fiberIso_hom_eval_smul hG k A ((hG.toSSet_map_app_eq_iff (g • τ) τ).2 ⟨g, rfl⟩)
    (initialSheet (g • τ)) (initialSheet τ) g ?_ c
  change simplexMap (g • τ) (toTopInitialVertex ⦋n⦌) =
    g • simplexMap τ (toTopInitialVertex ⦋n⦌)
  simp [toSSetObj_smul_def, simplexMap_app]

/-- The `G`-equivariant cochain `Cₙ(E; k) ⟶ A` associated to a direct cochain `c` of `B`. -/
private def cochainToRepHom (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n) :
    haveI := hG.toContinuousConstSMul
    Rep.of (singularChainsRepresentation k E G n) ⟶ A :=
  haveI := hG.toContinuousConstSMul
  Rep.ofHom
    { toLinearMap := chainsDesc fun τ ↦ pullbackTrivializeAt hG k A n τ c
      isIntertwining' g := singularChains_linearMap_ext fun τ ↦ by
        simp only [LinearMap.comp_apply, singularChainsRepresentation_simplexChain,
          chainsDesc_simplexChain, one_smul]
        exact pullbackTrivializeAt_smul_simplex hG k A n c g τ }

/-- The forward degree-`n` linear map from direct cochains of `B` to `G`-equivariant cochains of
`E`. -/
private def cochainToRepLinearMap (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (hG.associatedLocalSystem k A).cochainComplex.X n →ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ A) where
  toFun := cochainToRepHom hG k A n
  map_add' c d := by
    have := hG.toContinuousConstSMul
    refine Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      singularChains_linearMap_ext fun τ ↦ ?_
    simp [cochainToRepHom, Rep.add_hom]
  map_smul' r c := by
    have := hG.toContinuousConstSMul
    refine Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      singularChains_linearMap_ext fun τ ↦ ?_
    simp [cochainToRepHom, Rep.smul_hom]

/-- Evaluating `cochainToRepLinearMap` on a simplex chain reads the sheet coordinate at the
initial vertex. -/
private lemma cochainToRepLinearMap_simplexChain (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) (r : k) :
    haveI := hG.toContinuousConstSMul
    (cochainToRepLinearMap hG k A n c).hom (simplexChain τ r) =
      r • (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c) := by
  have := hG.toContinuousConstSMul
  change chainsDesc (fun τ ↦ pullbackTrivializeAt hG k A n τ c) (simplexChain τ r) = _
  rw [chainsDesc_simplexChain, pullbackTrivializeAt_apply]

/-- The initial sheet of the chosen lift of a base simplex `σ` lies in the fibre over the initial
vertex of `σ`. -/
private def chosenLiftSheet (n : ℕ) (σ : (_root_.TopCat.toSSet.obj B) _⦋n⦌) :
    p ⁻¹' {(initialVertex σ).as} :=
  ⟨(initialVertex (hG.toSSet_map_app_surjective _ σ).choose).as,
    congrArg (fun ρ ↦ (initialVertex ρ).as)
      (hG.toSSet_map_app_surjective (Opposite.op ⦋n⦌) σ).choose_spec⟩

/-- Descending a `G`-equivariant cochain `u : Cₙ(E; k) ⟶ A` to a direct cochain of `B` by
evaluating `u` on a chosen lift of each base simplex and inserting into its initial sheet. -/
private def repHomToCochain (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (Rep.of (singularChainsRepresentation k E G n) ⟶ A) →ₗ[k]
      (hG.associatedLocalSystem k A).cochainComplex.X n where
  toFun u :=
    haveI := hG.toContinuousConstSMul
    (cochainComplexXIso (hG.associatedLocalSystem k A) n).inv fun σ ↦
      (hG.associatedLocalSystemFiberIso k A (chosenLiftSheet hG n σ)).inv
        (u.hom (simplexChain (hG.toSSet_map_app_surjective _ σ).choose 1))
  map_add' u v := by
    have := hG.toContinuousConstSMul
    apply cochainComplex_ext (hG.associatedLocalSystem k A)
    intro σ
    rw [map_add, cochainComplexXIso_inv_eval.{u, u, u}, cochainComplexXIso_inv_eval.{u, u, u},
      cochainComplexXIso_inv_eval.{u, u, u}, Rep.add_hom, Representation.IntertwiningMap.coe_add,
      Pi.add_apply, map_add]
  map_smul' r u := by
    have := hG.toContinuousConstSMul
    apply cochainComplex_ext (hG.associatedLocalSystem k A)
    intro σ
    rw [map_smul, cochainComplexXIso_inv_eval.{u, u, u}, cochainComplexXIso_inv_eval.{u, u, u},
      RingHom.id_apply, Rep.smul_hom, Representation.IntertwiningMap.coe_smul, Pi.smul_apply,
      map_smul]

/-- On the image `p ∘ τ` of any simplex `τ` of `E`, the descended cochain takes the value of `u`
on `τ` inserted into the initial sheet of `τ`, independently of the chosen lift. -/
private lemma repHomToCochain_eval_map_p (n : ℕ)
    (u : haveI := hG.toContinuousConstSMul; Rep.of (singularChainsRepresentation k E G n) ⟶ A)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    cochainComplexEval (hG.associatedLocalSystem k A) n ((_root_.TopCat.toSSet.map p).app _ τ)
        (repHomToCochain hG k A n u) =
      (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).inv
        (u.hom (simplexChain τ 1)) := by
  have := hG.toContinuousConstSMul
  let σ := (_root_.TopCat.toSSet.map p).app (Opposite.op ⦋n⦌) τ
  let τ₀ := (hG.toSSet_map_app_surjective (Opposite.op ⦋n⦌) σ).choose
  have hτ₀ : (_root_.TopCat.toSSet.map p).app (Opposite.op ⦋n⦌) τ₀ = σ :=
    (hG.toSSet_map_app_surjective (Opposite.op ⦋n⦌) σ).choose_spec
  obtain ⟨g, hg⟩ := (hG.toSSet_map_app_eq_iff τ₀ τ).1 hτ₀
  let := hG.mulActionFiber (initialVertex σ).as
  have he : chosenLiftSheet hG n σ = g • initialSheet τ := by
    apply Subtype.ext
    change simplexMap τ₀ (toTopInitialVertex ⦋n⦌) =
      g • simplexMap τ (toTopInitialVertex ⦋n⦌)
    rw [← hg, toSSetObj_smul_def, simplexMap_app]
    rfl
  have hu : u.hom (simplexChain τ₀ 1) = A.ρ g (u.hom (simplexChain τ 1)) := by
    rw [← hg, ← singularChainsRepresentation_simplexChain]
    exact LinearMap.congr_fun (u.hom.isIntertwining' g) (simplexChain τ 1)
  have hval :
      cochainComplexEval (hG.associatedLocalSystem k A) n σ (repHomToCochain hG k A n u) =
        (hG.associatedLocalSystemFiberIso k A (chosenLiftSheet hG n σ)).inv
          (u.hom (simplexChain τ₀ 1)) :=
    cochainComplexXIso_inv_eval.{u, u, u} (hG.associatedLocalSystem k A) n _ σ
  rw [hval, he, hu]
  have hinv := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (hG.associatedLocalSystemFiberIso_inv_smul k A (x := initialVertex σ) (initialSheet τ) g))
    (A.ρ g (u.hom (simplexChain τ 1)))
  exact hinv.trans (by rw [ModuleCat.comp_apply, ModuleCat.ofHom_apply, A.ρ.inv_self_apply])

/-- The degree-`n` linear equivalence between direct cochains of `B` valued in `L_A` and
`G`-equivariant cochains of `E` valued in `A`. -/
private def cochainLinearEquiv (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    (hG.associatedLocalSystem k A).cochainComplex.X n ≃ₗ[k]
      (Rep.of (singularChainsRepresentation k E G n) ⟶ A) :=
  haveI := hG.toContinuousConstSMul
  LinearEquiv.ofLinearMap (cochainToRepLinearMap hG k A n) (repHomToCochain hG k A n)
    (LinearMap.ext fun u ↦ Rep.hom_ext <| Representation.IntertwiningMap.ext <|
      singularChains_linearMap_ext fun τ ↦ by
        simp only [LinearMap.comp_apply, LinearMap.id_apply,
          Representation.IntertwiningMap.coe_toLinearMap]
        rw [cochainToRepLinearMap_simplexChain, one_smul, repHomToCochain_eval_map_p]
        exact ModuleCat.hom_inv_apply (hG.associatedLocalSystemFiberIso k A (initialSheet τ)) _)
    (LinearMap.ext fun c ↦ cochainComplex_ext (hG.associatedLocalSystem k A) fun σ ↦ by
      obtain ⟨τ, rfl⟩ := hG.toSSet_map_app_surjective (Opposite.op ⦋n⦌) σ
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [repHomToCochain_eval_map_p, cochainToRepLinearMap_simplexChain, one_smul]
      exact ModuleCat.inv_hom_apply (hG.associatedLocalSystemFiberIso k A (initialSheet τ)) _)

/-- **Direct local-coefficient cochains of a quotient covering are equivariant cochains of the
total space**: for a quotient covering map `p : E ⟶ B` by `G` and a representation `A` of `G`,
pulling cochains back along `p` and reading coordinates in the initial sheet is an isomorphism
from `C•(B; L_A)` to `Hom_G(C•(E; k), A)`. -/
def cochainComplexIsoLinearYonedaObj :
    haveI := hG.toContinuousConstSMul
    (hG.associatedLocalSystem k A).cochainComplex ≅
      (singularChainsRep k E G).linearYonedaObj k A :=
  haveI := hG.toContinuousConstSMul
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cochainLinearEquiv hG k A n).toModuleIso)
    fun i j (h : i + 1 = j) ↦ by
      subst h
      refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦ Rep.hom_ext <|
        Representation.IntertwiningMap.ext <| singularChains_linearMap_ext fun τ ↦ ?_
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
        TauCeti.ChainComplex.linearYonedaObj_d_apply, singularChainsRep_d]
      change (cochainToRepLinearMap hG k A i c).hom
          ((singularChainsRepDifferential k E G i).hom (simplexChain τ 1)) =
        (cochainToRepLinearMap hG k A (i + 1)
          (((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) c)).hom
          (simplexChain τ 1)
      have hd_right :
          pullbackTrivializeAt hG k A (i + 1) τ
              (((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) c) =
            ∑ m : Fin (i + 2), (-1 : ℤ) ^ (m : ℕ) •
              pullbackTrivializeAt hG k A i
                ((_root_.TopCat.toSSet.obj E).map (δ m).op τ) c :=
        (congrArg (cochainComplexEval ((constantFunctor E).obj (ModuleCat.of k A)) (i + 1) τ)
          (ConcreteCategory.congr_hom ((pullbackTrivialize hG k A).comm i (i + 1)) c).symm).trans
          (cochainComplex_d_eval_constant (ModuleCat.of k A) i
            ((pullbackTrivialize hG k A).f i c) τ)
      rw [singularChainsRepDifferential_hom_apply, singularChains_d_simplexChain, map_sum,
        cochainToRepLinearMap_simplexChain, one_smul, ← pullbackTrivializeAt_apply, hd_right]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [map_zsmul, cochainToRepLinearMap_simplexChain, one_smul, ← pullbackTrivializeAt_apply]
      rfl

/-- The forward cochain comparison evaluates on `simplexChain τ r` by reading the coordinate of
`c (p ∘ τ)` in the initial sheet of `τ` and scaling by `r`. -/
theorem cochainComplexIsoLinearYonedaObj_hom_f_simplexChain (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) (r : k) :
    haveI := hG.toContinuousConstSMul
    (((hG.cochainComplexIsoLinearYonedaObj k A).hom.f n c) :
        Rep.of (singularChainsRepresentation k E G n) ⟶ A).hom (simplexChain τ r) =
      r • (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c) :=
  cochainToRepLinearMap_simplexChain hG k A n c τ r

/-- Evaluating the inverse cochain comparison on the image `p ∘ τ` of a simplex `τ` of `E` inserts
the value of the equivariant cochain on `τ` into the initial sheet of `τ`. -/
theorem cochainComplexEval_cochainComplexIsoLinearYonedaObj_inv_f (n : ℕ)
    (u : haveI := hG.toContinuousConstSMul; Rep.of (singularChainsRepresentation k E G n) ⟶ A)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    cochainComplexEval (hG.associatedLocalSystem k A) n ((_root_.TopCat.toSSet.map p).app _ τ)
        ((hG.cochainComplexIsoLinearYonedaObj k A).inv.f n u) =
      (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).inv
        (u.hom (simplexChain τ 1)) :=
  repHomToCochain_eval_map_p hG k A n u τ

variable {A} {A' : Rep.{u} k G}

/-- **The direct cochain comparison is natural in the representation**: changing local
coefficients along `f : A ⟶ A'` commutes with postcomposing equivariant cochains on `E` by `f`. -/
@[reassoc]
theorem cochainComplexIsoLinearYonedaObj_hom_naturality (f : A ⟶ A') :
    haveI := hG.toContinuousConstSMul
    cochainComplexCoefficientMap (hG.associatedLocalSystemMap k f) ≫
        (hG.cochainComplexIsoLinearYonedaObj k A').hom =
      (hG.cochainComplexIsoLinearYonedaObj k A).hom ≫
        (singularChainsRep k E G).linearYonedaObjMap k f := by
  have := hG.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun c ↦ ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    singularChains_linearMap_ext fun τ ↦ ?_
  have hnat := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (hG.associatedLocalSystemFiberIso_hom_naturality k f (initialSheet τ)))
    (cochainComplexEval (hG.associatedLocalSystem k A) n
      ((_root_.TopCat.toSSet.map p).app _ τ) c)
  have hleft :
      (((cochainComplexCoefficientMap (hG.associatedLocalSystemMap k f) ≫
          (hG.cochainComplexIsoLinearYonedaObj k A').hom).f n c) :
        Rep.of (singularChainsRepresentation k E G n) ⟶ A').hom (simplexChain τ 1) =
      (hG.associatedLocalSystemFiberIso k A' (initialSheet τ)).hom
        (((hG.associatedLocalSystemMap k f).app _)
          (cochainComplexEval (hG.associatedLocalSystem k A) n
            ((_root_.TopCat.toSSet.map p).app _ τ) c)) := by
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul,
      cochainComplexCoefficientMap_eval.{u, u, u}]
  have hright :
      ((((hG.cochainComplexIsoLinearYonedaObj k A).hom ≫
          (singularChainsRep k E G).linearYonedaObjMap k f).f n c) :
        Rep.of (singularChainsRepresentation k E G n) ⟶ A').hom (simplexChain τ 1) =
      f.hom ((hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c)) := by
    -- `(singularChainsRep k E G).linearYonedaObjMap k f` acts by postcomposition with `f` on
    -- `((singularChainsRep k E G).linearYonedaObj k A).X n`, which unfolds to morphisms into `A`.
    refine (congrArg (fun u : (singularChainsRep k E G).X n ⟶ A' ↦ u.hom (simplexChain τ 1))
      (((singularChainsRep k E G).linearYonedaObjMap_f_hom_apply k f n)
        ((hG.cochainComplexIsoLinearYonedaObj k A).hom.f n c))).trans ?_
    change f.hom ((((hG.cochainComplexIsoLinearYonedaObj k A).hom.f n c) :
      Rep.of (singularChainsRepresentation k E G n) ⟶ A).hom (simplexChain τ 1)) = _
    rw [cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul]
  exact hleft.trans (hnat.trans hright.symm)

/-- The inverse cochain comparison is natural in the representation. -/
@[reassoc]
theorem cochainComplexIsoLinearYonedaObj_inv_naturality (f : A ⟶ A') :
    haveI := hG.toContinuousConstSMul
    (singularChainsRep k E G).linearYonedaObjMap k f ≫
        (hG.cochainComplexIsoLinearYonedaObj k A').inv =
      (hG.cochainComplexIsoLinearYonedaObj k A).inv ≫
        cochainComplexCoefficientMap (hG.associatedLocalSystemMap k f) := by
  have := hG.toContinuousConstSMul
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.cochainComplexIsoLinearYonedaObj_hom_naturality k f, Iso.inv_hom_id_assoc]

variable (A)

/-- **The local-coefficient cohomology of the base of a contractible free cover is group
cohomology**: for the quotient covering map `p : E ⟶ B` of an action of `G` with contractible total
space and a representation `A` of `G`, the direct cohomology `Hⁿ(B; L_A)` with values in the
associated local system is Mathlib's `groupCohomology A n`. -/
def cohomologyIsoGroupCohomology [ContractibleSpace E] (n : ℕ) :
    (hG.associatedLocalSystem k A).cohomology n ≅ groupCohomology A n :=
  haveI := hG.toContinuousConstSMul
  haveI := hG.isCancelSMul
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
      (hG.cochainComplexIsoLinearYonedaObj k A) ≪≫
    (groupCohomologyIso A n (singularChainsResolution k E G)).symm

/-- `cohomologyIsoGroupCohomology` is the map on cohomology induced by
`cochainComplexIsoLinearYonedaObj` followed by the inverse of `groupCohomologyIso` for the singular
chain resolution of `E`. -/
theorem cohomologyIsoGroupCohomology_hom_eq [ContractibleSpace E] (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    (hG.cohomologyIsoGroupCohomology k A n).hom =
      HomologicalComplex.homologyMap (hG.cochainComplexIsoLinearYonedaObj k A).hom n ≫
        (groupCohomologyIso A n (singularChainsResolution k E G)).inv :=
  Iso.trans_hom _ _

/-- The inverse of `cohomologyIsoGroupCohomology` is `groupCohomologyIso` for the singular chain
resolution of `E` followed by the map on cohomology induced by the inverse of
`cochainComplexIsoLinearYonedaObj`. -/
theorem cohomologyIsoGroupCohomology_inv_eq [ContractibleSpace E] (n : ℕ) :
    haveI := hG.toContinuousConstSMul
    haveI := hG.isCancelSMul
    (hG.cohomologyIsoGroupCohomology k A n).inv =
      (groupCohomologyIso A n (singularChainsResolution k E G)).hom ≫
        HomologicalComplex.homologyMap (hG.cochainComplexIsoLinearYonedaObj k A).inv n :=
  Iso.trans_inv _ _

variable {A}

/-- **The local-coefficient cohomology of the base of a contractible free cover is naturally group
cohomology, in the representation**: for `f : A ⟶ A'`, the identifications `Hⁿ(B; L_A) ≅ Hⁿ(G, A)`
and `Hⁿ(B; L_A') ≅ Hⁿ(G, A')` carry `cohomologyCoefficientMap (hG.associatedLocalSystemMap k f) n`
to `groupCohomology.map (MonoidHom.id G) f n`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_hom_naturality [ContractibleSpace E] (f : A ⟶ A') (n : ℕ) :
    cohomologyCoefficientMap (hG.associatedLocalSystemMap k f) n ≫
        (hG.cohomologyIsoGroupCohomology k A' n).hom =
      (hG.cohomologyIsoGroupCohomology k A n).hom ≫
        groupCohomology.map (MonoidHom.id G) f n := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (hG.cochainComplexIsoLinearYonedaObj_hom_naturality k f)).trans
        (HomologicalComplex.homologyMap_comp _ _ n)
  rw [cohomologyCoefficientMap_eq, cohomologyIsoGroupCohomology_hom_eq,
    cohomologyIsoGroupCohomology_hom_eq]
  -- The complex of `singularChainsResolution k E G` is `singularChainsRep k E G` by definition;
  -- pasting in term mode avoids transparency mismatches in `rw`.
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (TauCeti.Rep.groupCohomologyIso_inv_naturality f (singularChainsResolution k E G) n)).trans
    (Category.assoc _ _ _).symm

/-- The inverse identification of group cohomology with local-coefficient cohomology on a
contractible free cover is natural in the representation. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_inv_naturality [ContractibleSpace E] (f : A ⟶ A') (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) f n ≫
        (hG.cohomologyIsoGroupCohomology k A' n).inv =
      (hG.cohomologyIsoGroupCohomology k A n).inv ≫
        cohomologyCoefficientMap (hG.associatedLocalSystemMap k f) n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.cohomologyIsoGroupCohomology_hom_naturality k f n, Iso.inv_hom_id_assoc]

section LongExactSequence

/-- **The local-coefficient cohomology of the base of a contractible free cover respects the
coefficient long exact sequences**: for any short exact sequence `0 ⟶ S₁ ⟶ S₂ ⟶ S₃ ⟶ 0` of
representations of `G` (with no projectivity or flatness assumption), the identifications
`Hⁿ(B; L_{Sᵢ}) ≅ Hⁿ(G, Sᵢ)` carry the geometric connecting map `cohomologyδ` of the associated
short exact sequence of local systems to Mathlib's `groupCohomology.δ`. -/
@[reassoc]
theorem cohomologyδ_comp_cohomologyIsoGroupCohomology_hom [ContractibleSpace E]
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n m : ℕ) (h : n + 1 = m := by lia) :
    (hG.shortExact_associatedLocalSystem k hS).cohomologyδ n m h ≫
        (hG.cohomologyIsoGroupCohomology k S.X₁ m).hom =
      (hG.cohomologyIsoGroupCohomology k S.X₃ n).hom ≫
        groupCohomology.δ hS n m h := by
  have := hG.toContinuousConstSMul
  have := hG.isCancelSMul
  let ψ : (S.map (hG.associatedLocalSystemFunctor k)).map (cochainComplexFunctor k B) ⟶
      S.map ((singularChainsRep k E G).linearYonedaObjFunctor k) :=
    { τ₁ := (hG.cochainComplexIsoLinearYonedaObj k S.X₁).hom
      τ₂ := (hG.cochainComplexIsoLinearYonedaObj k S.X₂).hom
      τ₃ := (hG.cochainComplexIsoLinearYonedaObj k S.X₃).hom
      comm₁₂ := (hG.cochainComplexIsoLinearYonedaObj_hom_naturality k S.f).symm
      comm₂₃ := (hG.cochainComplexIsoLinearYonedaObj_hom_naturality k S.g).symm }
  have hcochains := HomologicalComplex.HomologySequence.δ_naturality ψ
    ((hG.shortExact_associatedLocalSystem k hS).map_cochainComplexFunctor)
    ((singularChainsResolution k E G).complex.shortExact_map_linearYonedaObjFunctor k hS) n m h
  rw [ShortComplex.ShortExact.cohomologyδ_eq_δ, cohomologyIsoGroupCohomology_hom_eq,
    cohomologyIsoGroupCohomology_hom_eq]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (TauCeti.Rep.δ_comp_groupCohomologyIso_inv hS (singularChainsResolution k E G) n m h)).trans
    (Category.assoc _ _ _).symm

/-- Inverse form of `cohomologyδ_comp_cohomologyIsoGroupCohomology_hom`: the inverse
identifications carry `groupCohomology.δ` to the geometric connecting map `cohomologyδ`. -/
@[reassoc]
theorem groupCohomology_δ_comp_cohomologyIsoGroupCohomology_inv [ContractibleSpace E]
    {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact) (n m : ℕ) (h : n + 1 = m := by lia) :
    groupCohomology.δ hS n m h ≫ (hG.cohomologyIsoGroupCohomology k S.X₁ m).inv =
      (hG.cohomologyIsoGroupCohomology k S.X₃ n).inv ≫
        (hG.shortExact_associatedLocalSystem k hS).cohomologyδ n m h := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.cohomologyδ_comp_cohomologyIsoGroupCohomology_hom k hS n m h, Iso.inv_hom_id_assoc]

end LongExactSequence

section ChangeOfGroups

variable {F C : _root_.TopCat.{u}} {q : F ⟶ C} {H : Type u} [Group H] [MulAction H F]
  (hH : IsQuotientCoveringMap q H) {φ : G →* H}
  (f : E ⟶ F) (hf : ∀ g e, f (g • e) = φ g • f e)
  (b : B ⟶ C) (hb : p ≫ b = f ≫ q)

/-- In sheet coordinates at `e` over `x` and `e'` over `b x` with `f e = e'`, the morphism
`(associatedLocalSystemBaseChangeIso D).inv ≫ associatedLocalSystemMap ξ` acts as the underlying
linear map of `ξ : Rep.res φ D ⟶ A`. -/
private lemma baseChangeIso_inv_comp_map_fiberIso_hom
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A)
    {x : FundamentalGroupoid B} (e : p ⁻¹' {x.as})
    (e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj x).as}) (he : f e = e') :
    ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv.app x ≫
        (hG.associatedLocalSystemMap k ξ).app x) ≫
        (hG.associatedLocalSystemFiberIso k A e).hom =
      (hH.associatedLocalSystemFiberIso k D e').hom ≫
        ModuleCat.ofHom ξ.hom.toLinearMap := by
  have hbase :
      (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv.app x ≫
          (hG.associatedLocalSystemFiberIso k (Rep.res φ D) e).hom =
        (hH.associatedLocalSystemFiberIso k D e').hom := by
    apply (cancel_epi ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom.app x)).1
    have h1 := (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom_inv_id_app x
    have h2 := (congrArg (fun t ↦ t.app x ≫ (hH.associatedLocalSystemFiberIso k D e').hom)
        (hG.associatedLocalSystemBaseChangeIso_hom k hH f hf b hb D)).trans <|
      (hG.associatedLocalSystemMapOver_app_comp_fiberIso_hom k hH f hf b hb
        (𝟙 (Rep.res φ D)) e e' he).trans (Category.comp_id _)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h1).trans ((Category.id_comp _).trans h2.symm))
  rw [Category.assoc, hG.associatedLocalSystemFiberIso_hom_naturality k ξ e, ← Category.assoc,
    hbase]
  rfl

/-- The contravariant cochain map `C•(C; L_D) ⟶ C•(B; L_A)` induced by an equivariant map of
quotient covers along `φ : G →* H` over `b : B ⟶ C` and a compatible coefficient morphism
`ξ : Rep.res φ D ⟶ A`: pull cochains back along `b`, identify `b^* L_D` with `L_{Res(φ)(D)}`, and
apply `ξ`. -/
def associatedCochainComplexMap {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) :
    (hH.associatedLocalSystem k D).cochainComplex ⟶
      (hG.associatedLocalSystem k A).cochainComplex :=
  cochainComplexPullback b (hH.associatedLocalSystem k D) ≫
    cochainComplexCoefficientMap
      ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
        hG.associatedLocalSystemMap k ξ)

/-- `associatedCochainComplexMap` is cochain pullback followed by the base-change and coefficient
morphisms of local systems. -/
theorem associatedCochainComplexMap_def {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) :
    hG.associatedCochainComplexMap k hH f hf b hb ξ =
      cochainComplexPullback b (hH.associatedLocalSystem k D) ≫
        cochainComplexCoefficientMap
          ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
            hG.associatedLocalSystemMap k ξ) :=
  (rfl)

/-- `associatedCochainComplexMap` is natural with respect to compatible morphisms of coefficient
representations: if `ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂`, then the induced cochain maps form a
commutative square. -/
@[reassoc]
theorem associatedCochainComplexMap_naturality
    {D₁ D₂ : Rep.{u} k H} {A₁ A₂ : Rep.{u} k G}
    (β : D₁ ⟶ D₂) (α : A₁ ⟶ A₂)
    (ξ₁ : Rep.res φ D₁ ⟶ A₁) (ξ₂ : Rep.res φ D₂ ⟶ A₂)
    (hcomm : ξ₁ ≫ α = (Rep.resFunctor φ).map β ≫ ξ₂) :
    cochainComplexCoefficientMap (hH.associatedLocalSystemMap k β) ≫
        hG.associatedCochainComplexMap k hH f hf b hb ξ₂ =
      hG.associatedCochainComplexMap k hH f hf b hb ξ₁ ≫
        cochainComplexCoefficientMap (hG.associatedLocalSystemMap k α) := by
  have hbase :
      (LocalCoefficientSystem.pullback b.hom).map (hH.associatedLocalSystemMap k β) ≫
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D₂).inv =
        (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D₁).inv ≫
          hG.associatedLocalSystemMap k ((Rep.resFunctor φ).map β) := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact (hG.associatedLocalSystemBaseChangeIso_hom_naturality k hH f hf b hb β).symm
  rw [associatedCochainComplexMap_def, associatedCochainComplexMap_def,
    cochainComplexPullback_coefficient_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  rw [← cochainComplexCoefficientMap_comp, ← cochainComplexCoefficientMap_comp]
  congr 1
  rw [reassoc_of% hbase, ← associatedLocalSystemMap_comp, ← hcomm, associatedLocalSystemMap_comp,
    Category.assoc]

/-- **The direct cochain comparison is natural for equivariant maps of quotient covers.**
Pulling direct cochains back along `b : B ⟶ C` and changing local coefficients by
`ξ : Rep.res φ D ⟶ A` corresponds to the change-of-groups map
`φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf)` on equivariant cochains of the total
spaces. -/
@[reassoc]
theorem associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) :
    haveI := hG.toContinuousConstSMul
    haveI := hH.toContinuousConstSMul
    hG.associatedCochainComplexMap k hH f hf b hb ξ ≫
        (hG.cochainComplexIsoLinearYonedaObj k A).hom =
      (hH.cochainComplexIsoLinearYonedaObj k D).hom ≫
        φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf) := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun c ↦ ?_
  refine Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    singularChains_linearMap_ext fun τ ↦ ?_
  let σB := (_root_.TopCat.toSSet.map p).app (Opposite.op ⦋n⦌) τ
  let τF := (_root_.TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ
  have hσC : (_root_.TopCat.toSSet.map b).app (Opposite.op ⦋n⦌) σB =
      (_root_.TopCat.toSSet.map q).app (Opposite.op ⦋n⦌) τF := by
    simpa only [σB, τF, Functor.map_comp, NatTrans.comp_app, types_comp_apply] using
      congrArg (fun m : E ⟶ C ↦ (_root_.TopCat.toSSet.map m).app (Opposite.op ⦋n⦌) τ) hb
  let e' : q ⁻¹' {((FundamentalGroupoid.map b.hom).obj (initialVertex σB)).as} :=
    ⟨f (initialSheet (p := p) τ).1, by
      change q (f (simplexMap τ (toTopInitialVertex ⦋n⦌))) =
        b (p (simplexMap τ (toTopInitialVertex ⦋n⦌)))
      exact (ConcreteCategory.congr_hom hb.symm (simplexMap τ (toTopInitialVertex ⦋n⦌)))⟩
  have hcoord := LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      (hG.baseChangeIso_inv_comp_map_fiberIso_hom k hH f hf b hb ξ
        (initialSheet (p := p) τ) e' rfl))
    (cochainComplexEval (hH.associatedLocalSystem k D) n
      ((_root_.TopCat.toSSet.map b).app _ σB) c)
  have hcongr :
      (hH.associatedLocalSystemFiberIso k D e').hom
          (cochainComplexEval (hH.associatedLocalSystem k D) n
            ((_root_.TopCat.toSSet.map b).app _ σB) c) =
        (hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
          (cochainComplexEval (hH.associatedLocalSystem k D) n
            ((_root_.TopCat.toSSet.map q).app _ τF) c) :=
    fiberIso_hom_eval_congr hH k D hσC e' (initialSheet τF)
      (by
        change f (simplexMap τ (toTopInitialVertex ⦋n⦌)) =
          simplexMap ((_root_.TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ)
            (toTopInitialVertex ⦋n⦌)
        rw [simplexMap_app]
        rfl) c
  have hleft :
      (((hG.associatedCochainComplexMap k hH f hf b hb ξ ≫
          (hG.cochainComplexIsoLinearYonedaObj k A).hom).f n c) :
        Rep.of (singularChainsRepresentation k E G n) ⟶ A).hom (simplexChain τ 1) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map q).app _ τF) c)) := by
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul,
      associatedCochainComplexMap_def, HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cochainComplexCoefficientMap_eval.{u, u, u}, cochainComplexPullback_eval.{u, u, u}]
    exact hcoord.trans (congrArg ξ.hom hcongr)
  have hright :
      ((((hH.cochainComplexIsoLinearYonedaObj k D).hom ≫
          φ.linearYonedaObjMap ξ (singularChainsRepResMap k f hf)).f n c) :
        Rep.of (singularChainsRepresentation k E G n) ⟶ A).hom (simplexChain τ 1) =
      ξ.hom ((hH.associatedLocalSystemFiberIso k D (initialSheet τF)).hom
        (cochainComplexEval (hH.associatedLocalSystem k D) n
          ((_root_.TopCat.toSSet.map q).app _ τF) c)) := by
    refine (congrArg (fun u : (singularChainsRep k E G).X n ⟶ A ↦ u.hom (simplexChain τ 1))
      (φ.linearYonedaObjMap_f_apply ξ (singularChainsRepResMap k f hf) n
        ((hH.cochainComplexIsoLinearYonedaObj k D).hom.f n c))).trans ?_
    change ξ.hom ((((hH.cochainComplexIsoLinearYonedaObj k D).hom.f n c) :
      Rep.of (singularChainsRepresentation k F H n) ⟶ D).hom
        (((singularChainsRepResMap k f hf).f n).hom (simplexChain τ 1))) = _
    rw [singularChainsRepResMap_f_hom_apply, singularChains_map_f_simplexChain,
      cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul]
  exact hleft.trans hright.symm

/-- The contravariant map `Hⁿ(C; L_D) ⟶ Hⁿ(B; L_A)` on direct local-coefficient cohomology induced
by an equivariant map of quotient covers along `φ : G →* H` over `b : B ⟶ C` and a compatible
coefficient morphism `ξ : Rep.res φ D ⟶ A`. -/
def associatedCohomologyMap {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    (hH.associatedLocalSystem k D).cohomology n ⟶
      (hG.associatedLocalSystem k A).cohomology n :=
  cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
    cohomologyCoefficientMap
      ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
        hG.associatedLocalSystemMap k ξ) n

/-- `associatedCohomologyMap` is cohomology pullback along `b` followed by the base-change and
coefficient maps. -/
theorem associatedCohomologyMap_def {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n =
      cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
        cohomologyCoefficientMap
          ((hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv ≫
            hG.associatedLocalSystemMap k ξ) n :=
  (rfl)

/-- `associatedCohomologyMap` is the map on cohomology induced by `associatedCochainComplexMap`. -/
theorem associatedCohomologyMap_eq_homologyMap {D : Rep.{u} k H} {A : Rep.{u} k G}
    (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n =
      HomologicalComplex.homologyMap (hG.associatedCochainComplexMap k hH f hf b hb ξ) n := by
  rw [associatedCohomologyMap_def, cohomologyPullback_eq, cohomologyCoefficientMap_eq,
    ← HomologicalComplex.homologyMap_comp, associatedCochainComplexMap_def]

/-- **The geometric connecting map of local-coefficient cohomology commutes with change of groups
on quotient covers**, without assuming contractibility of the total spaces. -/
@[reassoc]
theorem cohomologyδ_comp_associatedCohomologyMap
    {Y : ShortComplex (Rep.{u} k H)} {X : ShortComplex (Rep.{u} k G)}
    (hY : Y.ShortExact) (hX : X.ShortExact)
    (Φ : Y.map (Rep.resFunctor φ) ⟶ X) (n m : ℕ) (h : n + 1 = m := by lia) :
    (hH.shortExact_associatedLocalSystem k hY).cohomologyδ n m h ≫
        hG.associatedCohomologyMap k hH f hf b hb Φ.τ₁ m =
      hG.associatedCohomologyMap k hH f hf b hb Φ.τ₃ n ≫
        (hG.shortExact_associatedLocalSystem k hX).cohomologyδ n m h := by
  let ψ : (Y.map (hH.associatedLocalSystemFunctor k)).map (cochainComplexFunctor k C) ⟶
      (X.map (hG.associatedLocalSystemFunctor k)).map (cochainComplexFunctor k B) :=
    { τ₁ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₁
      τ₂ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₂
      τ₃ := hG.associatedCochainComplexMap k hH f hf b hb Φ.τ₃
      comm₁₂ := (hG.associatedCochainComplexMap_naturality k hH f hf b hb Y.f X.f Φ.τ₁ Φ.τ₂
        Φ.comm₁₂).symm
      comm₂₃ := (hG.associatedCochainComplexMap_naturality k hH f hf b hb Y.g X.g Φ.τ₂ Φ.τ₃
        Φ.comm₂₃).symm }
  rw [ShortComplex.ShortExact.cohomologyδ_eq_δ, ShortComplex.ShortExact.cohomologyδ_eq_δ,
    associatedCohomologyMap_eq_homologyMap, associatedCohomologyMap_eq_homologyMap]
  exact HomologicalComplex.HomologySequence.δ_naturality ψ
    ((hH.shortExact_associatedLocalSystem k hY).map_cochainComplexFunctor)
    ((hG.shortExact_associatedLocalSystem k hX).map_cochainComplexFunctor) n m h

/-- **The local-coefficient cohomology of the base of a contractible free cover is naturally group
cohomology, in the covering and the group**: for quotient covering maps `p : E ⟶ B` and `q : F ⟶ C`
with contractible total spaces, an equivariant map `f : E ⟶ F` along any `φ : G →* H` over
`b : B ⟶ C`, and a compatible morphism `ξ : Rep.res φ D ⟶ A`, the identifications
`Hⁿ(C; L_D) ≅ Hⁿ(H, D)` and `Hⁿ(B; L_A) ≅ Hⁿ(G, A)` carry `associatedCohomologyMap` to Mathlib's
`groupCohomology.map φ ξ n`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_hom_naturality_over
    [ContractibleSpace E] [ContractibleSpace F]
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    hG.associatedCohomologyMap k hH f hf b hb ξ n ≫
        (hG.cohomologyIsoGroupCohomology k A n).hom =
      (hH.cohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ ξ n := by
  have := hG.toContinuousConstSMul
  have := hH.toContinuousConstSMul
  have := hG.isCancelSMul
  have := hH.isCancelSMul
  have hcochains := (HomologicalComplex.homologyMap_comp _ _ n).symm.trans <|
    (congrArg (HomologicalComplex.homologyMap · n)
      (hG.associatedCochainComplexMap_comp_cochainComplexIsoLinearYonedaObj_hom k hH f hf b hb
        ξ)).trans
      (HomologicalComplex.homologyMap_comp _ _ n)
  rw [associatedCohomologyMap_eq_homologyMap, cohomologyIsoGroupCohomology_hom_eq,
    cohomologyIsoGroupCohomology_hom_eq]
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) hcochains).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·)
      (φ.groupCohomologyIso_inv_naturality ξ (singularChainsResolution k E G)
        (singularChainsResolution k F H) (singularChainsRepResMap k f hf)
        (singularChainsRepResMap_f_zero_comp_augmentation k f hf) n)).trans
    (Category.assoc _ _ _).symm

/-- Inverse form of `cohomologyIsoGroupCohomology_hom_naturality_over`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_inv_naturality_over
    [ContractibleSpace E] [ContractibleSpace F]
    {D : Rep.{u} k H} {A : Rep.{u} k G} (ξ : Rep.res φ D ⟶ A) (n : ℕ) :
    groupCohomology.map φ ξ n ≫
        (hG.cohomologyIsoGroupCohomology k A n).inv =
      (hH.cohomologyIsoGroupCohomology k D n).inv ≫
        hG.associatedCohomologyMap k hH f hf b hb ξ n := by
  rw [Iso.comp_inv_eq, Category.assoc,
    hG.cohomologyIsoGroupCohomology_hom_naturality_over k hH f hf b hb ξ n, Iso.inv_hom_id_assoc]

/-- Pulling direct local-coefficient cohomology back along `b : B ⟶ C` from `L_D` to `b^* L_D`
corresponds, via `IsQuotientCoveringMap.associatedLocalSystemBaseChangeIso`, to
`groupCohomology.map φ (𝟙 (Rep.res φ D)) n`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_hom_pullback
    [ContractibleSpace E] [ContractibleSpace F] (D : Rep.{u} k H) (n : ℕ) :
    cohomologyPullback b (hH.associatedLocalSystem k D) n ≫
        cohomologyCoefficientMap
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv n ≫
        (hG.cohomologyIsoGroupCohomology k (Rep.res φ D) n).hom =
      (hH.cohomologyIsoGroupCohomology k D n).hom ≫
        groupCohomology.map φ (𝟙 (Rep.res φ D)) n := by
  have h := hG.cohomologyIsoGroupCohomology_hom_naturality_over k hH f hf b hb
    (𝟙 (Rep.res φ D)) n
  rw [associatedCohomologyMap_def, associatedLocalSystemMap_id, Category.comp_id,
    Category.assoc] at h
  exact h

/-- Inverse pullback compatibility: `cohomologyPullback b` on the inverse comparison carries
`groupCohomology.map φ (𝟙 (Rep.res φ D)) n` to `associatedLocalSystemBaseChangeIso`. -/
@[reassoc]
theorem cohomologyIsoGroupCohomology_inv_pullback
    [ContractibleSpace E] [ContractibleSpace F] (D : Rep.{u} k H) (n : ℕ) :
    (hH.cohomologyIsoGroupCohomology k D n).inv ≫
        cohomologyPullback b (hH.associatedLocalSystem k D) n =
      groupCohomology.map φ (𝟙 (Rep.res φ D)) n ≫
        (hG.cohomologyIsoGroupCohomology k (Rep.res φ D) n).inv ≫
        cohomologyCoefficientMap
          (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n := by
  have h := hG.cohomologyIsoGroupCohomology_inv_naturality_over k hH f hf b hb
    (𝟙 (Rep.res φ D)) n
  rw [associatedCohomologyMap_def, associatedLocalSystemMap_id, Category.comp_id] at h
  have hcancel :
      cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).inv n ≫
        cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n =
      𝟙 _ := by
    rw [← cohomologyCoefficientMap_comp, Iso.inv_hom_id, cohomologyCoefficientMap_id]
  have h' := h =≫
    cohomologyCoefficientMap (hG.associatedLocalSystemBaseChangeIso k hH f hf b hb D).hom n
  simpa only [Category.assoc, hcancel, Category.comp_id] using h'.symm

end ChangeOfGroups

end IsQuotientCoveringMap
