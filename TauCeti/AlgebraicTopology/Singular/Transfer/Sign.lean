/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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

When every fibre is a pair `{e, σ e}` with `σ e ≠ e`, reading functions as formal sums of sheets
followed by the augmentation is a short exact sequence `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0`
(`IsCoveringMap.shortExact_signPermutationShortComplex`). Its coefficient long exact sequence
shows that a class `c ∈ Hₖ(E; R)` with `p_* c = 0` comes from `Hₖ(B; sign)`
(`IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq`), from a
unique class when `Hₖ₊₁(B; R) = 0`
(`IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`).

For the orientation double cover of a manifold with its deck involution, the sign local system is
the orientation local system, and the class of the fundamental class of the orientation cover is
the fundamental class of the manifold with orientation-twisted coefficients
(`TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass`).

## Main definitions

* `IsCoveringMap.permutationLocalSystemFiberMap`: the endomorphism of the permutation local system
  moving the sheets by `σ`.
* `IsCoveringMap.permutationLocalSystemToSign`: antisymmetrization, from the permutation local
  system to the sign local system of an involution.
* `IsCoveringMap.signLocalSystemToPermutation`: for finite fibres, a function on a fibre as the
  formal sum of its sheets.
* `IsCoveringMap.signPermutationShortComplex`: the short complex `sign ⟶ R[p⁻¹ b] ⟶ R`.

## Main results

* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom`: on homology, `σ_*` is the
  coefficient map of `permutationLocalSystemFiberMap`.
* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`: antisymmetrizing
  the image of `σ_* c` gives the negative of antisymmetrizing the image of `c`.
* `IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`: the round
  trip through the sign local system is `1 - σ_*`.
* `IsCoveringMap.shortExact_signPermutationShortComplex`: for a double cover,
  `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` is short exact.
* `IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq` and
  `IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`: classes of
  a double cover killed by `p_*` come from the sign local system, uniquely when
  `Hₖ₊₁(B; R) = 0`.

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
@[simp]
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
        rw [Functor.map_comp, NatTrans.comp_app, ConcreteCategory.comp_apply])
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

/-- The component over `x` of antisymmetrization, from the fibre of the permutation local system
to the fibre of the sign local system. -/
def permutationLocalSystemToSignApp (x : FundamentalGroupoid B) :
    ((p ⁻¹' {x.as}) →₀ R) →ₗ[R] (hp.signLocalSystem R σ hσ).obj x :=
  (hp.signLocalSystemObjEquiv σ hσ x).symm.toLinearMap ∘ₗ TauCeti.antisymmetrize R hσ hσσ x.as

/-- Antisymmetrization sends a formal sum `f` of sheets to the function `e ↦ f e - f (σ e)`. -/
@[simp]
theorem signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply
    (x : FundamentalGroupoid B) (f : (p ⁻¹' {x.as}) →₀ R) (e : p ⁻¹' {x.as}) :
    (hp.signLocalSystemObjEquiv σ hσ x (hp.permutationLocalSystemToSignApp R hσ hσσ x f) :
        p ⁻¹' {x.as} → R) e =
      f e - f (Function.fiberMap σ hσ x.as e) :=
  (congrArg (fun g : TauCeti.signFiber R σ hσ x.as ↦ (g : p ⁻¹' {x.as} → R) e)
    ((hp.signLocalSystemObjEquiv σ hσ x).apply_symm_apply
      (TauCeti.antisymmetrize R hσ hσσ x.as f))).trans
    (TauCeti.coe_antisymmetrize_apply hσ hσσ x.as f e)

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
@[simp]
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
      Function.mapDomain_fiberMap_apply_of_involutive hσσ hσ,
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
    ← twistedHomologyCoefficientMap_comp, permutationLocalSystemFiberMap_comp_toSign,
    twistedHomologyCoefficientMap_neg, Preadditive.comp_neg]

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
@[simp]
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
      Function.mapDomain_fiberMap_apply_of_involutive hσσ hσ]
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
    permutationLocalSystemToSign_comp_toPermutation, twistedHomologyCoefficientMap_sub,
    twistedHomologyCoefficientMap_id, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Iso.hom_inv_id, ← homologyMap_comp_singularHomologyPermutationIso_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! ### The short exact sequence of a double cover -/

section DoubleCover

variable (hfix : ∀ e, σ e ≠ e)

include hσσ hfix in
/-- A function changing sign under a fixed-point-free involution has coefficients summing to zero:
reading it as a formal sum of sheets and taking the augmentation gives `0`. -/
@[reassoc (attr := simp)]
theorem signLocalSystemToPermutation_comp_augmentation :
    hp.signLocalSystemToPermutation R hσ hfin ≫ hp.permutationLocalSystemAugmentation R = 0 := by
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_))
  have := hfin x.as
  have := Fintype.ofFinite (p ⁻¹' {x.as})
  rw [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply, NatTrans.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  refine (hp.permutationLocalSystemAugmentation_app_apply_eq_sum R x _).trans ?_
  -- The fibres of the permutation and constant systems are `(p ⁻¹' {x.as}) →₀ R` and `R` only
  -- after unfolding their definitions, so neither evaluation at a sheet nor `0 : R` is visible to
  -- `rw` or `simp`. `change` states the goal through the component of the definition.
  change ∑ e, hp.signLocalSystemToPermutationApp R hσ hfin x f e = (0 : R)
  simp only [signLocalSystemToPermutationApp_apply]
  exact TauCeti.sum_eq_zero_of_mem_signFiber hfix hσσ (hp.signLocalSystemObjEquiv σ hσ x f).2

/-- The short complex `sign ⟶ R[p⁻¹ b] ⟶ R` of local systems of a covering with finite fibres and
a fixed-point-free involution `σ` over the base: functions changing sign under `σ`, read as formal
sums of sheets, followed by the augmentation. -/
@[expose, simps]
def signPermutationShortComplex : ShortComplex (TauCeti.LocalCoefficientSystem R B) :=
  ShortComplex.mk (hp.signLocalSystemToPermutation R hσ hfin)
    (hp.permutationLocalSystemAugmentation R)
    (hp.signLocalSystemToPermutation_comp_augmentation R hσ hσσ hfin hfix)

variable (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)

variable (hsurj : Function.Surjective p)

include hfib hsurj in
/-- **The sign sequence of a double cover is short exact**: when every fibre of `p` is a pair
`{e, σ e}` with `σ e ≠ e`, the sequence `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` is exact. -/
theorem shortExact_signPermutationShortComplex :
    (hp.signPermutationShortComplex R hσ hσσ hfin hfix).ShortExact := by
  have hS (x : FundamentalGroupoid B) :
      (ShortComplex.mk ((hp.signLocalSystemToPermutation R hσ hfin).app x)
        ((hp.permutationLocalSystemAugmentation R).app x) (by
          rw [← NatTrans.comp_app, signLocalSystemToPermutation_comp_augmentation _ _ _ hσσ _ hfix,
            NatTrans.app_zero])).ShortExact := by
    have := hfin x.as
    have := Fintype.ofFinite (p ⁻¹' {x.as})
    obtain ⟨e₀, he₀⟩ := hsurj x.as
    refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 fun f g hfg ↦ ?_)
      ((ModuleCat.epi_iff_surjective _).2 fun r ↦ ⟨Finsupp.single ⟨e₀, he₀⟩ r, ?_⟩)
    · refine (ShortComplex.moduleCat_exact_iff _).2 fun (g : (p ⁻¹' {x.as}) →₀ R) hg ↦ ?_
      -- A formal sum with coefficients summing to zero changes sign under `σ`.
      have hg' : ∑ e, g e = 0 :=
        (hp.permutationLocalSystemAugmentation_app_apply_eq_sum R x g).symm.trans hg
      refine ⟨(hp.signLocalSystemObjEquiv σ hσ x).symm
        ⟨_, TauCeti.mem_signFiber_of_sum_eq_zero hfix hfib hg'⟩, Finsupp.ext fun e ↦ ?_⟩
      -- As above, the fibre of the permutation system is a type of formal sums only after
      -- unfolding, so `change` evaluates the component of the definition at the sheet `e`.
      change hp.signLocalSystemToPermutationApp R hσ hfin x _ e = g e
      rw [signLocalSystemToPermutationApp_apply, LinearEquiv.apply_symm_apply]
    · -- The values of the component are formal sums only after unfolding the permutation
      -- system, so `change` states `hfg` through the component of the definition.
      change hp.signLocalSystemToPermutationApp R hσ hfin x f =
        hp.signLocalSystemToPermutationApp R hσ hfin x g at hfg
      refine (hp.signLocalSystemObjEquiv σ hσ x).injective (Subtype.ext (funext fun e ↦ ?_))
      have h := DFunLike.congr_fun hfg e
      rwa [signLocalSystemToPermutationApp_apply, signLocalSystemToPermutationApp_apply] at h
    · exact (hp.permutationLocalSystemAugmentation_app_apply R x _).trans
        (Finsupp.sum_single_index rfl)
  refine ShortComplex.ShortExact.mk' ?_ ((NatTrans.mono_iff_mono_app _).2 fun x ↦ (hS x).mono_f)
    ((NatTrans.epi_iff_epi_app _).2 fun x ↦ (hS x).epi_g)
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun x ↦ ?_
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (hS x).exact).of_iso
    (ShortComplex.mapHomologyIso _ ((evaluation _ (ModuleCat R)).obj x)).symm

include hσσ hfix hfib hsurj in
/-- **Reading sign classes as classes of the cover is injective below a vanishing degree**: for a
double cover, if `Hₖ₊₁(B; R) = 0` then the map `Hₖ(B; sign) ⟶ Hₖ(B; R[p⁻¹ b])` reading functions
on fibres as formal sums of sheets is injective, by the coefficient long exact sequence of
`0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0`. -/
theorem injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation (k : ℕ)
    (hk : Limits.IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj B)) :
    Function.Injective
      (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  have := (hS.twistedHomology_exact₁ (k + 1) k rfl).mono_g
    ((hk.of_iso (twistedHomologyConstantIso B (ModuleCat.of R R) (k + 1))).eq_of_src _ _)
  exact (ModuleCat.mono_iff_injective _).1 this

include hσσ hfix hfib hsurj in
/-- **Classes of the cover killed by the projection come from the sign local system**: for a
double cover, a class `c ∈ Hₖ(E; R)` with `p_* c = 0` is, as a class of `B` twisted by the
permutation local system, the image of a class of `Hₖ(B; sign)` read as formal sums of sheets.
This is exactness of the coefficient long exact sequence of `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` at
`Hₖ(B; R[p⁻¹ b])`. -/
theorem exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq (k : ℕ)
    (c : ((TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R))
    (hc : (SSet.homologyMap (TopCat.toSSet.map p) (ModuleCat.of R R) k).hom c = 0) :
    ∃ g, (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom g =
      (hp.singularHomologyPermutationIso R k).hom.hom c := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  refine (ShortComplex.moduleCat_exact_iff _).1 (hS.twistedHomology_exact₂ k) _ ?_
  -- The augmentation of the image of `c` is `p_* c = 0`.
  have h := congrArg (fun φ ↦ φ.hom c) (hp.singularHomologyPermutationIso_hom_comp_augmentation R k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine (ModuleCat.mono_iff_injective
    (twistedHomologyConstantIso B (ModuleCat.of R R) k).hom).1 inferInstance ?_
  exact h.trans (hc.trans (map_zero _).symm)

end DoubleCover

end IsCoveringMap
