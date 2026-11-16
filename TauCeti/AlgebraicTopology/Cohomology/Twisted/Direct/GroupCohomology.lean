/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Coefficients
public import TauCeti.AlgebraicTopology.LocalCoefficient.QuotientCovering.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Coinvariants
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Resolution
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Resolution

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

Both the cochain isomorphism and the cohomology isomorphism are natural in the representation `A`.
Contravariant functoriality and naturality along equivariant maps of quotient covers and arbitrary
group homomorphisms are developed in `Cohomology/Twisted/Direct/EquivariantMap`.

## Main definitions

* `IsQuotientCoveringMap.cochainComplexIsoLinearYonedaObj`: direct cochains of `B` valued in `L_A`
  are isomorphic to `Hom_G(C•(E; k), A)`.
* `IsQuotientCoveringMap.cohomologyIsoGroupCohomology`: for contractible `E`, the cohomology
  `Hⁿ(B; L_A)` is Mathlib's `groupCohomology A n`.

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

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Sections II.4 and III.1.
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
    -- Addition on the constant-functor fibre `ModuleCat.of k A` is addition on `A` by definition.
    rfl
  map_smul' r c := by
    rw [map_smul, map_smul]
    -- Scalar multiplication on the constant-functor fibre `ModuleCat.of k A` is scalar
    -- multiplication on `A` by definition.
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
  simp only [pullbackTrivializeAt, LinearMap.coe_mk, pullbackTrivialize,
    HomologicalComplex.comp_f, ModuleCat.comp_apply, cochainComplexCoefficientMap_eval.{u, u, u},
    associatedLocalSystemPullbackIso_hom_app, cochainComplexPullback_eval.{u, u, u}]
  -- The fibre of `constantFunctor` is `A` and `⟨(initialVertex τ).as, rfl⟩` is `initialSheet τ` by
  -- definition.
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
  simp only [cochainToRepLinearMap, LinearMap.coe_mk, AddHom.coe_mk, cochainToRepHom,
    Rep.hom_ofHom, Representation.IntertwiningMap.coe_mk, chainsDesc_simplexChain,
    pullbackTrivializeAt_apply]

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
    rw [hG.coe_mulActionFiber_smul (initialVertex σ).as g (initialSheet τ)]
    simp [chosenLiftSheet, τ₀, ← hg, toSSetObj_smul_def, simplexMap_app]
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

/-- Evaluating `cochainToRepLinearMap` on the coboundary `d c` at a simplex `τ` agrees with
evaluating `cochainToRepLinearMap` on `c` at the singular chain boundary of `τ`. -/
private lemma cochainToRepLinearMap_d_simplexChain (i : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X i)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋i + 1⦌) :
    haveI := hG.toContinuousConstSMul
    (cochainToRepLinearMap hG k A (i + 1)
        (((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) c)).hom
        (simplexChain τ 1) =
      (cochainToRepLinearMap hG k A i c).hom
        ((singularChainsRepDifferential k E G i).hom (simplexChain τ 1)) := by
  have := hG.toContinuousConstSMul
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
  -- `(-1 : ℤ) ^ m • ·` on `A` and on the constant fibre `ModuleCat.of k A` agree by definition.
  rfl

/-- The degreewise equivalences `cochainLinearEquiv` commute with the coboundary maps of
`cochainComplex` and `linearYonedaObj`. -/
private lemma cochainLinearEquiv_comm_d (i : ℕ) :
    haveI := hG.toContinuousConstSMul
    -- `((singularChainsRep k E G).linearYonedaObj k A).X n` unfolds to
    -- `(singularChainsRep k E G).X n ⟶ A` (`ChainComplex.linearYonedaObj_X`), and
    -- `(singularChainsRep k E G).X n` unfolds to `Rep.of (singularChainsRepresentation k E G n)`.
    (cochainLinearEquiv hG k A i).toModuleIso.hom ≫
        ((singularChainsRep k E G).linearYonedaObj k A).d i (i + 1) =
      ((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) ≫
        (cochainLinearEquiv hG k A (i + 1)).toModuleIso.hom := by
  have := hG.toContinuousConstSMul
  refine ModuleCat.hom_ext <| LinearMap.ext fun c ↦ Rep.hom_ext <|
    Representation.IntertwiningMap.ext <| singularChains_linearMap_ext fun τ ↦ ?_
  let u : (singularChainsRep k E G).X i ⟶ A := cochainToRepLinearMap hG k A i c
  have hu : (cochainLinearEquiv hG k A i).toModuleIso.hom c = u := by
    simp [u, cochainLinearEquiv, LinearEquiv.toModuleIso_hom]
  have hleft :
      ((((cochainLinearEquiv hG k A i).toModuleIso.hom ≫
          ((singularChainsRep k E G).linearYonedaObj k A).d i (i + 1)) c :
        (singularChainsRep k E G).X (i + 1) ⟶ A)).hom (simplexChain τ 1) =
      (cochainToRepLinearMap hG k A i c).hom
        ((singularChainsRepDifferential k E G i).hom (simplexChain τ 1)) :=
    (congrArg (fun g : (singularChainsRep k E G).X (i + 1) ⟶ A ↦ g.hom (simplexChain τ 1))
        ((ModuleCat.comp_apply _ _ c).trans <|
          (congrArg (((singularChainsRep k E G).linearYonedaObj k A).d i (i + 1)) hu).trans
            (TauCeti.ChainComplex.linearYonedaObj_d_apply (X := singularChainsRep k E G)
              i (i + 1) u))).trans <|
      (DFunLike.congr_fun
          (Rep.hom_comp _ _ _ ((singularChainsRep k E G).d (i + 1) i) u)
        (simplexChain τ 1)).trans
        (congrArg u.hom (DFunLike.congr_fun
          (congrArg (fun g : (singularChainsRep k E G).X (i + 1) ⟶
              (singularChainsRep k E G).X i ↦ g.hom)
            (singularChainsRep_d k E G i)) (simplexChain τ 1)))
  have hright :
      (((((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) ≫
          (cochainLinearEquiv hG k A (i + 1)).toModuleIso.hom) c :
        (singularChainsRep k E G).X (i + 1) ⟶ A)).hom (simplexChain τ 1) =
      (cochainToRepLinearMap hG k A (i + 1)
        (((hG.associatedLocalSystem k A).cochainComplex).d i (i + 1) c)).hom
        (simplexChain τ 1) := by
    simp [cochainLinearEquiv, LinearEquiv.toModuleIso_hom]
  exact hleft.trans ((cochainToRepLinearMap_d_simplexChain hG k A i c τ).symm.trans hright.symm)

/-- **Direct local-coefficient cochains of a quotient covering are equivariant cochains of the
total space**: for a quotient covering map `p : E ⟶ B` by `G` and a representation `A` of `G`,
pulling cochains back along `p` and reading coordinates in the initial sheet is an isomorphism
from `C•(B; L_A)` to `Hom_G(C•(E; k), A)`. -/
def cochainComplexIsoLinearYonedaObj :
    haveI := hG.toContinuousConstSMul
    (hG.associatedLocalSystem k A).cochainComplex ≅
      (singularChainsRep k E G).linearYonedaObj k A :=
  haveI := hG.toContinuousConstSMul
  -- `((singularChainsRep k E G).linearYonedaObj k A).X n` unfolds to
  -- `(singularChainsRep k E G).X n ⟶ A`, where `(singularChainsRep k E G).X n` unfolds to
  -- `Rep.of (singularChainsRepresentation k E G n)`.
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (cochainLinearEquiv hG k A n).toModuleIso)
    fun i j (h : i + 1 = j) ↦ by
      subst h
      exact cochainLinearEquiv_comm_d hG k A i

/-- The forward cochain comparison evaluates on `simplexChain τ r` by reading the coordinate of
`c (p ∘ τ)` in the initial sheet of `τ` and scaling by `r`. -/
-- Match before `singularChainsRep_X` rewrites the representation carrier in the morphism type.
@[simp↓]
theorem cochainComplexIsoLinearYonedaObj_hom_f_simplexChain (n : ℕ)
    (c : (hG.associatedLocalSystem k A).cochainComplex.X n)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) (r : k) :
    haveI := hG.toContinuousConstSMul
    (((hG.cochainComplexIsoLinearYonedaObj k A).hom.f n c) :
        (singularChainsRep k E G).X n ⟶ A).hom (simplexChain τ r) =
      r • (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c) :=
  -- `isoOfComponents` and `toModuleIso` reduce `.hom.f n` to `cochainToRepLinearMap`, and
  -- `((singularChainsRep k E G).linearYonedaObj k A).X n` has carrier
  -- `(singularChainsRep k E G).X n ⟶ A = (Rep.of (singularChainsRepresentation k E G n) ⟶ A)` by
  -- definition, so term mode avoids transparency mismatches in `rw`/`simp`.
  cochainToRepLinearMap_simplexChain hG k A n c τ r

/-- Evaluating the inverse cochain comparison on the image `p ∘ τ` of a simplex `τ` of `E` inserts
the value of the equivariant cochain on `τ` into the initial sheet of `τ`. -/
-- Match before `singularChainsRep_X` rewrites the representation carrier in the morphism type.
@[simp↓]
theorem cochainComplexEval_cochainComplexIsoLinearYonedaObj_inv_f (n : ℕ)
    (u : haveI := hG.toContinuousConstSMul; (singularChainsRep k E G).X n ⟶ A)
    (τ : (_root_.TopCat.toSSet.obj E) _⦋n⦌) :
    haveI := hG.toContinuousConstSMul
    cochainComplexEval (hG.associatedLocalSystem k A) n ((_root_.TopCat.toSSet.map p).app _ τ)
        ((hG.cochainComplexIsoLinearYonedaObj k A).inv.f n u) =
      (hG.associatedLocalSystemFiberIso k A (initialSheet τ)).inv
        (u.hom (simplexChain τ 1)) :=
  -- As above, `isoOfComponents` and `toModuleIso` reduce `.inv.f n` to `repHomToCochain` across
  -- `(singularChainsRep k E G).X n = Rep.of (singularChainsRepresentation k E G n)` by definition.
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
        (singularChainsRep k E G).X n ⟶ A').hom (simplexChain τ 1) =
      (hG.associatedLocalSystemFiberIso k A' (initialSheet τ)).hom
        (((hG.associatedLocalSystemMap k f).app _)
          (cochainComplexEval (hG.associatedLocalSystem k A) n
            ((_root_.TopCat.toSSet.map p).app _ τ) c)) := by
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply,
      cochainComplexIsoLinearYonedaObj_hom_f_simplexChain, one_smul,
      cochainComplexCoefficientMap_eval.{u, u, u}]
  -- `(singularChainsRep k E G).linearYonedaObjMap k f` acts by postcomposition with `f` on
  -- `((singularChainsRep k E G).linearYonedaObj k A).X n`, which unfolds to morphisms into `A`.
  let u : (singularChainsRep k E G).X n ⟶ A :=
    (hG.cochainComplexIsoLinearYonedaObj k A).hom.f n c
  have hright :
      ((((hG.cochainComplexIsoLinearYonedaObj k A).hom ≫
          (singularChainsRep k E G).linearYonedaObjMap k f).f n c) :
        (singularChainsRep k E G).X n ⟶ A').hom (simplexChain τ 1) =
      f.hom ((hG.associatedLocalSystemFiberIso k A (initialSheet τ)).hom
        (cochainComplexEval (hG.associatedLocalSystem k A) n
          ((_root_.TopCat.toSSet.map p).app _ τ) c)) :=
    (congrArg (fun g : (singularChainsRep k E G).X n ⟶ A' ↦ g.hom (simplexChain τ 1))
        ((ModuleCat.comp_apply _ _ c).trans
          (((singularChainsRep k E G).linearYonedaObjMap_f_hom_apply k f n) u))).trans <|
      (DFunLike.congr_fun (Rep.hom_comp _ _ _ u f) (simplexChain τ 1)).trans
        (congrArg f.hom
          ((hG.cochainComplexIsoLinearYonedaObj_hom_f_simplexChain k A n c τ 1).trans
            (one_smul k _)))
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

end IsQuotientCoveringMap
