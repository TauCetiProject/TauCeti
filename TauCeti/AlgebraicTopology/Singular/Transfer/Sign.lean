/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Singular chains of a double cover and the sign local system

Let `p : E ⟶ B` be a covering map and `σ : E → E` a continuous map over `B`. The singular chains
of `E` are the chains of `B` twisted by the permutation local system of `p`, whose fibre over `b`
is the free module on the sheets over `b`
(`IsCoveringMap.singularChainComplexPermutationIso`). Under this identification the map
`σ_* : C(E; R) ⟶ C(E; R)` is induced by the morphism of permutation local systems that moves each
sheet by `σ` (`IsCoveringMap.permutationLocalSystemFiberMap`,
`IsCoveringMap.chainComplexMap_comp_singularChainComplexPermutationIso_hom`).

When `σ` is an involution, a formal sum `f` of sheets over `b` gives the function
`e ↦ f e - f (σ e)` on the fibre, which changes sign under `σ`. This antisymmetrization is a
morphism from the permutation local system to the sign local system of `σ`
(`IsCoveringMap.permutationLocalSystemToSign`), and it changes sign when precomposed with the
action of `σ`. So the composite

`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`

satisfies `σ_* c ↦ -(image of c)`
(`IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`). When the fibres
are finite, a function on a fibre is a formal sum of its sheets, which gives a morphism back
(`IsCoveringMap.signLocalSystemToPermutation`), and the round trip on `Hₖ(E; R)` is `1 - σ_*`
(`IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`).

For the orientation double cover of a manifold with its deck involution, the sign local system is
the orientation local system, and these maps carry the fundamental class of the orientation cover
to the fundamental class of the manifold with orientation-twisted coefficients
(`TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass`).

## Main definitions

* `IsCoveringMap.permutationLocalSystemFiberMap`: the endomorphism of the permutation local system
  moving the sheets by `σ`.
* `IsCoveringMap.permutationLocalSystemToSign`: antisymmetrization, from the permutation local
  system to the sign local system of an involution.
* `IsCoveringMap.signLocalSystemToPermutation`: for finite fibres, a function on a fibre as the
  formal sum of its sheets.

## Main results

* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom`: on homology, `σ_*` is the
  coefficient map of `permutationLocalSystemFiberMap`.
* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`: antisymmetrizing
  the image of `σ_* c` gives the negative of antisymmetrizing the image of `c`.
* `IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`: the round
  trip through the sign local system is `1 - σ_*`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients, the local
  system of a covering space and the orientation local system of a manifold.
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

universe u

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  (σ : C(E, E)) (hσ : ⇑p ∘ ⇑σ = ⇑p)

/-! ### Moving the sheets by a map over the base -/

/-- The endomorphism of the permutation local system of `p` moving each sheet by a map `σ` over
the base: on the fibre over `x` it is the linear extension of `σ` restricted to that fibre. It
commutes with transport because `σ` commutes with monodromy. -/
def permutationLocalSystemFiberMap :
    hp.permutationLocalSystem R ⟶ hp.permutationLocalSystem R where
  app x := ModuleCat.ofHom (Finsupp.lmapDomain R R (Function.fiberMap σ hσ x.as))
  naturality x y γ := by
    dsimp only [permutationLocalSystem]
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    refine Finsupp.lhom_ext' fun e ↦ LinearMap.ext_ring ?_
    simp [hp.fiberMap_monodromy hp σ hσ]

/-- The endomorphism moving the sheets by `σ` is the linear extension of `σ` on each fibre. -/
theorem permutationLocalSystemFiberMap_app_apply (x : FundamentalGroupoid B)
    (f : (p ⁻¹' {x.as}) →₀ R) :
    ((hp.permutationLocalSystemFiberMap R σ hσ).app x).hom f =
      Finsupp.mapDomain (Function.fiberMap σ hσ x.as) f :=
  (rfl)

/-- The endomorphism moving the sheets by `σ` sends the coefficients at a sheet `e` to the
coefficients at `σ e`. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemSingle_fiberMap_app (x : FundamentalGroupoid B)
    (e : p ⁻¹' {x.as}) :
    hp.permutationLocalSystemSingle R x e ≫ (hp.permutationLocalSystemFiberMap R σ hσ).app x =
      hp.permutationLocalSystemSingle R x (Function.fiberMap σ hσ x.as e) := by
  ext : 1
  refine LinearMap.ext_ring ?_
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, permutationLocalSystemSingle_hom_apply,
    permutationLocalSystemSingle_hom_apply, permutationLocalSystemFiberMap_app_apply,
    Finsupp.mapDomain_single]

/-- **The map of chains induced by a map over the base, as a coefficient map**: under the
comparison of singular chains of `E` with chains of `B` twisted by the permutation local system,
`σ_* : C(E; R) ⟶ C(E; R)` is induced by the endomorphism moving the sheets by `σ`. -/
theorem chainComplexMap_comp_singularChainComplexPermutationIso_hom :
    SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) ≫
        (hp.singularChainComplexPermutationIso R).hom =
      (hp.singularChainComplexPermutationIso R).hom ≫
        twistedChainComplexCoefficientMap (hp.permutationLocalSystemFiberMap R σ hσ) := by
  have hσp : TopCat.ofHom σ ≫ p = p := TopCat.hom_ext (ContinuousMap.ext (congrFun hσ))
  refine HomologicalComplex.hom_ext _ _ fun k ↦ SSet.chainComplex_hom_ext fun τ ↦ ?_
  simp only [HomologicalComplex.comp_f, SSet.ι_chainComplexMap_f_assoc,
    ιChainComplex_singularChainComplexPermutationIso_hom_f,
    ιChainComplex_singularChainComplexPermutationIso_hom_f_assoc,
    ιTwistedChainComplex_twistedChainComplexCoefficientMap_f,
    permutationLocalSystemSingle_fiberMap_app_assoc]
  -- Moving `τ` by `σ` does not change `p ∘ τ`, and moves its initial sheet by `σ`.
  exact single_initialSheet_ιTwistedChainComplex hp R
    (by conv_rhs => rw [← hσp]
        rw [Functor.map_comp]
        rfl)
    ((DFunLike.congr_fun (TauCeti.TopCat.simplexMap_app _ τ) _).trans
      (Function.fiberMap_apply_coe σ hσ _ (initialSheet τ)).symm)

/-- **The map on homology induced by a map over the base, as a coefficient map**: under the
comparison of singular homology of `E` with homology of `B` twisted by the permutation local
system, `σ_*` is induced by the endomorphism moving the sheets by `σ`. -/
@[reassoc]
theorem homologyMap_comp_singularHomologyPermutationIso_hom (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k ≫
        (hp.singularHomologyPermutationIso R k).hom =
      (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemFiberMap R σ hσ) k := by
  rw [singularHomologyPermutationIso_hom, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp,
    chainComplexMap_comp_singularChainComplexPermutationIso_hom]

/-! ### Antisymmetrization for an involution -/

variable {σ} (hσσ : Function.Involutive σ)

include hσσ in
/-- Moving the sheets of a formal sum by an involution reads its coefficients at the image. -/
private theorem mapDomain_fiberMap_apply_of_involutive (x : B) (f : (p ⁻¹' {x}) →₀ R)
    (e : p ⁻¹' {x}) :
    Finsupp.mapDomain (Function.fiberMap σ hσ x) f e = f (Function.fiberMap σ hσ x e) := by
  conv_lhs => rw [← Function.fiberMap_fiberMap_of_involutive hσσ hσ x e]
  exact Finsupp.mapDomain_apply_of_injective
    (Function.injective_fiberMap_of_involutive hσσ hσ x) f _

/-- Antisymmetrization on the fibre of `p` over `x`: a formal sum `f` of sheets goes to the
function `e ↦ f e - f (σ e)`, which changes sign under the involution `σ`. -/
def antisymmetrize (x : B) : ((p ⁻¹' {x}) →₀ R) →ₗ[R] TauCeti.signFiber R σ hσ x :=
  LinearMap.codRestrict (TauCeti.signFiber R σ hσ x)
    ((LinearMap.id - LinearMap.funLeft R R (Function.fiberMap σ hσ x)) ∘ₗ Finsupp.lcoeFun)
    fun f ↦ TauCeti.mem_signFiber_iff.2 fun e ↦ by
      simp [Function.fiberMap_fiberMap_of_involutive hσσ hσ]

@[simp]
theorem coe_antisymmetrize_apply (x : B) (f : (p ⁻¹' {x}) →₀ R) (e : p ⁻¹' {x}) :
    (antisymmetrize R hσ hσσ x f : p ⁻¹' {x} → R) e = f e - f (Function.fiberMap σ hσ x e) :=
  (rfl)

/-- The component over `x` of antisymmetrization, from the fibre of the permutation local system
to the fibre of the sign local system. -/
def permutationLocalSystemToSignApp (x : FundamentalGroupoid B) :
    ((p ⁻¹' {x.as}) →₀ R) →ₗ[R] (hp.signLocalSystem R σ hσ).obj x :=
  (hp.signLocalSystemObjEquiv σ hσ x).symm.toLinearMap ∘ₗ antisymmetrize R hσ hσσ x.as

/-- Antisymmetrization sends a formal sum `f` of sheets to the function `e ↦ f e - f (σ e)`. -/
@[simp]
theorem signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply
    (x : FundamentalGroupoid B) (f : (p ⁻¹' {x.as}) →₀ R) (e : p ⁻¹' {x.as}) :
    (hp.signLocalSystemObjEquiv σ hσ x (hp.permutationLocalSystemToSignApp R hσ hσσ x f) :
        p ⁻¹' {x.as} → R) e =
      f e - f (Function.fiberMap σ hσ x.as e) :=
  congrArg (fun g : TauCeti.signFiber R σ hσ x.as ↦ (g : p ⁻¹' {x.as} → R) e)
    ((hp.signLocalSystemObjEquiv σ hσ x).apply_symm_apply (antisymmetrize R hσ hσσ x.as f))

/-- **Antisymmetrization**: the morphism from the permutation local system of `p` to the sign
local system of an involution `σ` over the base sending a formal sum `f` of sheets over `x` to the
function `e ↦ f e - f (σ e)` on the fibre. -/
def permutationLocalSystemToSign :
    hp.permutationLocalSystem R ⟶ hp.signLocalSystem R σ hσ where
  app x := ConcreteCategory.ofHom (C := ModuleCat R) (hp.permutationLocalSystemToSignApp R hσ hσσ x)
  naturality x y γ := by
    dsimp only [permutationLocalSystem]
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (hp.signLocalSystemObjEquiv σ hσ y).injective (Subtype.ext (funext fun e ↦ ?_)))
    obtain ⟨e, rfl⟩ := (hp.monodromy_bijective γ).2 e
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ConcreteCategory.hom_ofHom,
      Finsupp.lmapDomain_apply, signLocalSystemObjEquiv_map_apply_monodromy,
      signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply, hp.fiberMap_monodromy hp σ hσ,
      Finsupp.mapDomain_apply_of_injective (hp.monodromy_bijective γ).1]

/-- The component over `x` of antisymmetrization. -/
theorem permutationLocalSystemToSign_app_hom (x : FundamentalGroupoid B) :
    ((hp.permutationLocalSystemToSign R hσ hσσ).app x).hom =
      hp.permutationLocalSystemToSignApp R hσ hσσ x :=
  (rfl)

/-- Moving the sheets by the involution `σ` and then antisymmetrizing is the negative of
antisymmetrizing. -/
@[reassoc (attr := simp)]
theorem permutationLocalSystemFiberMap_comp_toSign :
    hp.permutationLocalSystemFiberMap R σ hσ ≫ hp.permutationLocalSystemToSign R hσ hσσ =
      -hp.permutationLocalSystemToSign R hσ hσσ := by
  have key (x : FundamentalGroupoid B) (g : (p ⁻¹' {x.as}) →₀ R) (e : p ⁻¹' {x.as}) :
      (hp.signLocalSystemObjEquiv σ hσ x (hp.permutationLocalSystemToSignApp R hσ hσσ x
          (Finsupp.mapDomain (Function.fiberMap σ hσ x.as) g)) : p ⁻¹' {x.as} → R) e =
        -(hp.signLocalSystemObjEquiv σ hσ x (hp.permutationLocalSystemToSignApp R hσ hσσ x g) :
          p ⁻¹' {x.as} → R) e := by
    simp only [signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
      mapDomain_fiberMap_apply_of_involutive R hσ hσσ,
      Function.fiberMap_fiberMap_of_involutive hσσ hσ,
      neg_sub]
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (hp.signLocalSystemObjEquiv σ hσ x).injective (Subtype.ext (funext fun e ↦ ?_))))
  rw [NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply, map_neg, Submodule.coe_neg,
    Pi.neg_apply]
  -- Both components are the explicit linear maps of the definitions.
  exact key x f e

/-- **Antisymmetrizing anti-commutes with an involution over the base**: for the composite
`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`, the image of `σ_* c` is the negative of the image
of `c`. -/
theorem homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k ≫
        (hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k =
      -((hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k) := by
  rw [homologyMap_comp_singularHomologyPermutationIso_hom_assoc hp R σ hσ,
    ← twistedHomologyCoefficientMap_comp, permutationLocalSystemFiberMap_comp_toSign]
  have h := (twistedChainComplexFunctor.{u, u, u} R B).map_neg
    (f := hp.permutationLocalSystemToSign R hσ hσσ)
  rw [twistedChainComplexFunctor_map, twistedChainComplexFunctor_map] at h
  rw [twistedHomologyCoefficientMap, h, HomologicalComplex.homologyMap_neg, Preadditive.comp_neg]

/-! ### From functions on the fibres back to formal sums of sheets -/

variable (hfin : ∀ b, Finite (p ⁻¹' {b}))

/-- For a covering with finite fibres, the component over `x` of the morphism from the sign local
system to the permutation local system: a function on the fibre over `x` is read as the formal sum
of the sheets over `x` with these coefficients. -/
def signLocalSystemToPermutationApp (x : FundamentalGroupoid B) :
    (hp.signLocalSystem R σ hσ).obj x →ₗ[R] (p ⁻¹' {x.as}) →₀ R :=
  haveI := hfin x.as
  (Finsupp.linearEquivFunOnFinite R R _).symm.toLinearMap ∘ₗ
    (TauCeti.signFiber R σ hσ x.as).subtype ∘ₗ (hp.signLocalSystemObjEquiv σ hσ x).toLinearMap

/-- Reading a function on a fibre as a formal sum of sheets: the coefficient at `e` is the value
at `e`. -/
@[simp]
theorem signLocalSystemToPermutationApp_apply (x : FundamentalGroupoid B)
    (f : (hp.signLocalSystem R σ hσ).obj x) (e : p ⁻¹' {x.as}) :
    hp.signLocalSystemToPermutationApp R hσ hfin x f e =
      (hp.signLocalSystemObjEquiv σ hσ x f : p ⁻¹' {x.as} → R) e := by
  have := hfin x.as
  exact congrFun (Finsupp.linearEquivFunOnFinite_symm_apply R R (p ⁻¹' {x.as}) _) e

/-- For a covering with finite fibres, the morphism from the sign local system of `σ` to the
permutation local system of `p` reading a function on the fibre over `x` as the formal sum of the
sheets over `x` with these coefficients. -/
def signLocalSystemToPermutation :
    hp.signLocalSystem R σ hσ ⟶ hp.permutationLocalSystem R where
  app x :=
    ConcreteCategory.ofHom (C := ModuleCat R) (hp.signLocalSystemToPermutationApp R hσ hfin x)
  naturality x y γ := by
    have key (f : (hp.signLocalSystem R σ hσ).obj x) (e : p ⁻¹' {x.as}) :
        Finsupp.lmapDomain R R (hp.monodromy γ) (hp.signLocalSystemToPermutationApp R hσ hfin x f)
            (hp.monodromy γ e) =
          hp.signLocalSystemToPermutationApp R hσ hfin y
            (((hp.signLocalSystem R σ hσ).map γ).hom f) (hp.monodromy γ e) := by
      rw [Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_apply_of_injective (hp.monodromy_bijective γ).1,
        signLocalSystemToPermutationApp_apply, signLocalSystemToPermutationApp_apply,
        signLocalSystemObjEquiv_map_apply_monodromy]
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ Finsupp.ext fun e ↦ ?_)
    obtain ⟨e, rfl⟩ := (hp.monodromy_bijective γ).2 e
    -- Both components are the explicit linear maps of the definitions.
    exact (key f e).symm

/-- The component over `x` of reading functions on fibres as formal sums of sheets. -/
theorem signLocalSystemToPermutation_app_hom (x : FundamentalGroupoid B) :
    ((hp.signLocalSystemToPermutation R hσ hfin).app x).hom =
      hp.signLocalSystemToPermutationApp R hσ hfin x :=
  (rfl)

/-- Antisymmetrizing a formal sum of sheets and reading the result back as a formal sum of sheets
is `1 - σ`. -/
theorem permutationLocalSystemToSign_comp_toPermutation :
    hp.permutationLocalSystemToSign R hσ hσσ ≫ hp.signLocalSystemToPermutation R hσ hfin =
      𝟙 _ - hp.permutationLocalSystemFiberMap R σ hσ := by
  have key (x : FundamentalGroupoid B) (f : (p ⁻¹' {x.as}) →₀ R) (e : p ⁻¹' {x.as}) :
      hp.signLocalSystemToPermutationApp R hσ hfin x
          (hp.permutationLocalSystemToSignApp R hσ hσσ x f) e =
        f e - Finsupp.mapDomain (Function.fiberMap σ hσ x.as) f e := by
    rw [signLocalSystemToPermutationApp_apply,
      signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
      mapDomain_fiberMap_apply_of_involutive R hσ hσσ]
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    Finsupp.ext fun e ↦ ?_))
  rw [NatTrans.app_sub, NatTrans.id_app, ModuleCat.hom_sub, ModuleCat.hom_id]
  -- Both sides are the explicit linear maps of the definitions, evaluated on a formal sum.
  exact key x f e

/-- **The round trip through the sign local system is `1 - σ_*`**: antisymmetrizing the image of
a class `c ∈ Hₖ(E; R)` in `Hₖ(B; R[p⁻¹ b])`, reading it back as a formal sum of sheets and
returning to `Hₖ(E; R)` gives `c - σ_* c`. -/
theorem singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k ≫
          twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k ≫
            (hp.singularHomologyPermutationIso R k).inv =
      𝟙 _ - SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k := by
  rw [← twistedHomologyCoefficientMap_comp_assoc,
    permutationLocalSystemToSign_comp_toPermutation]
  have h := (twistedChainComplexFunctor.{u, u, u} R B).map_sub
    (f := 𝟙 (hp.permutationLocalSystem R)) (g := hp.permutationLocalSystemFiberMap R σ hσ)
  rw [twistedChainComplexFunctor_map, twistedChainComplexFunctor_map,
    twistedChainComplexFunctor_map, twistedChainComplexCoefficientMap_id] at h
  rw [twistedHomologyCoefficientMap, h, HomologicalComplex.homologyMap_sub,
    HomologicalComplex.homologyMap_id, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Iso.hom_inv_id, ← twistedHomologyCoefficientMap,
    ← homologyMap_comp_singularHomologyPermutationIso_hom_assoc, Iso.hom_inv_id, Category.comp_id]

end IsCoveringMap
