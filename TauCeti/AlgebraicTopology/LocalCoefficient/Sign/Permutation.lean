/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Covering
public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Basic
public import TauCeti.Data.Finsupp.Fiber
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# The sign and permutation local systems of a covering with an involution

Let `p : E ⟶ B` be a covering map and `σ : E → E` a continuous involution over `B`. A formal sum
`f` of sheets over `b` gives the function `e ↦ f e - f (σ e)` on the fibre, which changes sign
under `σ`. This antisymmetrization is a morphism from the permutation local system of `p` to the
sign local system of `σ` (`IsCoveringMap.permutationLocalSystemToSign`), and it changes sign when
precomposed with the endomorphism moving the sheets by `σ`
(`IsCoveringMap.permutationLocalSystemFiberMap_comp_toSign`). When the fibres are finite, a
function on a fibre is a formal sum of its sheets, which gives a morphism back
(`IsCoveringMap.signLocalSystemToPermutation`), and the round trip on the permutation local system
is `1 - σ` (`IsCoveringMap.permutationLocalSystemToSign_comp_toPermutation`). In the other order,
reading a function changing sign under `σ` as a formal sum of sheets and antisymmetrizing again
doubles it (`IsCoveringMap.signLocalSystemToPermutation_comp_toSign`), and moving the sheets of
that formal sum by `σ` negates it
(`IsCoveringMap.signLocalSystemToPermutation_comp_permutationLocalSystemFiberMap`).

When every fibre is a pair `{e, σ e}` with `σ e ≠ e`, reading functions as formal sums of sheets
followed by the augmentation is a short exact sequence `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` of local
systems (`IsCoveringMap.shortExact_signPermutationShortComplex`). Its consequences for singular
homology are in `TauCeti.AlgebraicTopology.Singular.Transfer.Sign`. A continuous section `s`
trivializes the sign local system, and through this trivialization reading functions as formal
sums of sheets sends `r` to `r • s x - r • σ (s x)`
(`IsCoveringMap.signLocalSystemIsoOfSection_inv_comp_signLocalSystemToPermutation`).

## Main definitions

* `IsCoveringMap.permutationLocalSystemToSign`: antisymmetrization, from the permutation local
  system to the sign local system of an involution.
* `IsCoveringMap.signLocalSystemToPermutation`: for finite fibres, a function on a fibre as the
  formal sum of its sheets.
* `IsCoveringMap.signPermutationShortComplex`: the short complex `sign ⟶ R[p⁻¹ b] ⟶ R`.

## Main results

* `IsCoveringMap.permutationLocalSystemFiberMap_comp_toSign`: moving the sheets by `σ` and then
  antisymmetrizing is the negative of antisymmetrizing.
* `IsCoveringMap.permutationLocalSystemToSign_comp_toPermutation`: the round trip through the
  sign local system is `1 - σ`.
* `IsCoveringMap.signLocalSystemToPermutation_comp_toSign`: the round trip through the permutation
  local system is multiplication by `2`.
* `IsCoveringMap.shortExact_signPermutationShortComplex`: for a double cover,
  `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` is short exact.
* `IsCoveringMap.signLocalSystemIsoOfSection_inv_comp_signLocalSystemToPermutation`: through the
  trivialization by a section `s`, formal sums of sheets are the difference of the sections `s`
  and `σ ∘ s`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients, the local
  system of a covering space and the orientation local system of a manifold.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  {σ : C(E, E)} (hσ : ⇑p ∘ ⇑σ = ⇑p) (hσσ : Function.Involutive σ)

/-! ### Antisymmetrization for an involution -/

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
    Pi.neg_apply, NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    hp.permutationLocalSystemFiberMap_app_apply R σ hσ x f]
  -- Both components are the explicit linear maps of the definitions.
  exact key x f e

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
  rw [NatTrans.app_sub, NatTrans.id_app, ModuleCat.hom_sub, ModuleCat.hom_id, LinearMap.sub_apply,
    LinearMap.id_apply, hp.permutationLocalSystemFiberMap_app_apply R σ hσ x f]
  -- Both sides are the explicit linear maps of the definitions, evaluated on a formal sum.
  exact key x f e

include hσσ in
/-- Reading a function changing sign under `σ` as a formal sum of sheets and then moving the
sheets by `σ` gives the negative formal sum. -/
@[reassoc (attr := simp)]
theorem signLocalSystemToPermutation_comp_permutationLocalSystemFiberMap :
    hp.signLocalSystemToPermutation R hσ hfin ≫ hp.permutationLocalSystemFiberMap R σ hσ =
      -hp.signLocalSystemToPermutation R hσ hfin := by
  have key (x : FundamentalGroupoid B) (f : (hp.signLocalSystem R σ hσ).obj x)
      (e : p ⁻¹' {x.as}) :
      Finsupp.mapDomain (Function.fiberMap σ hσ x.as)
          (hp.signLocalSystemToPermutationApp R hσ hfin x f) e =
        -hp.signLocalSystemToPermutationApp R hσ hfin x f e := by
    rw [Function.mapDomain_fiberMap_apply_of_involutive hσσ hσ,
      signLocalSystemToPermutationApp_apply, signLocalSystemToPermutationApp_apply,
      TauCeti.mem_signFiber_iff.1 (hp.signLocalSystemObjEquiv σ hσ x f).property]
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    Finsupp.ext fun e ↦ ?_))
  rw [NatTrans.app_neg, ModuleCat.hom_neg, LinearMap.neg_apply, NatTrans.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply]
  -- Both sides are the explicit linear maps of the definitions, evaluated at a sheet; the fibres
  -- of the permutation system are formal sums only after unfolding, so this is not a rewrite.
  exact (congrArg (fun g : (p ⁻¹' {x.as}) →₀ R ↦ g e)
    (hp.permutationLocalSystemFiberMap_app_apply R σ hσ x _)).trans
      ((key x f e).trans (Finsupp.neg_apply _ _).symm)

/-- Reading a function changing sign under `σ` as a formal sum of sheets and antisymmetrizing
again doubles it: `e ↦ f e - f (σ e) = 2 f e`. -/
theorem signLocalSystemToPermutation_comp_toSign :
    hp.signLocalSystemToPermutation R hσ hfin ≫ hp.permutationLocalSystemToSign R hσ hσσ =
      𝟙 _ + 𝟙 _ := by
  have key (x : FundamentalGroupoid B) (f : (hp.signLocalSystem R σ hσ).obj x)
      (e : p ⁻¹' {x.as}) :
      (hp.signLocalSystemObjEquiv σ hσ x (hp.permutationLocalSystemToSignApp R hσ hσσ x
          (hp.signLocalSystemToPermutationApp R hσ hfin x f)) : p ⁻¹' {x.as} → R) e =
        (hp.signLocalSystemObjEquiv σ hσ x (f + f) : p ⁻¹' {x.as} → R) e := by
    rw [signLocalSystemObjEquiv_permutationLocalSystemToSignApp_apply,
      signLocalSystemToPermutationApp_apply, signLocalSystemToPermutationApp_apply,
      TauCeti.mem_signFiber_iff.1 (hp.signLocalSystemObjEquiv σ hσ x f).property, sub_neg_eq_add,
      map_add, Submodule.coe_add, Pi.add_apply]
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (hp.signLocalSystemObjEquiv σ hσ x).injective (Subtype.ext (funext fun e ↦ ?_))))
  rw [NatTrans.app_add, NatTrans.id_app, ModuleCat.hom_add, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.id_apply]
  -- Both sides are the explicit linear maps of the definitions, evaluated at a point of the fibre.
  exact key x f e

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
  exact TauCeti.sum_eq_zero_of_mem_signFiber hfix hσσ (hp.signLocalSystemObjEquiv σ hσ x f).property

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

/-- **Formal sums of sheets through the trivialization by a section.** Let `s` be a continuous
section of a double cover whose sheets are exchanged by `σ`, and `t = σ ∘ s` the section through
the other sheets. Under the trivialization of the sign local system given by `s`, reading a
function on a fibre as a formal sum of sheets sends `r` to `r • s x - r • t x`: it is the
difference of the morphisms from the constant system given by the sections `s` and `t`, after
identifying `ULift R` with `R`. -/
theorem signLocalSystemIsoOfSection_inv_comp_signLocalSystemToPermutation
    (s t : C(B, E)) (hs : ∀ b, s b ∈ p ⁻¹' {b}) (ht : ∀ b, t b ∈ p ⁻¹' {b})
    (hst : ∀ b, t b = σ (s b)) :
    (hp.signLocalSystemIsoOfSection hfix hfib s hs).inv ≫
        hp.signLocalSystemToPermutation R hσ hfin =
      (TauCeti.LocalCoefficientSystem.constantFunctor B).map
          (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso.hom ≫
        (hp.permutationLocalSystemSection R s hs - hp.permutationLocalSystemSection R t ht) := by
  refine NatTrans.ext (funext fun x ↦ ModuleCat.hom_ext (LinearMap.ext fun r ↦
    Finsupp.ext fun e ↦ ?_))
  obtain ⟨r⟩ := r
  -- The two sheets over `x`: the value of `s`, and its image `t x` under `σ`.
  have hσs : (⟨t x.as, ht x.as⟩ : p ⁻¹' {x.as}) =
      Function.fiberMap σ hσ x.as ⟨s x.as, hs x.as⟩ :=
    Subtype.ext ((hst x.as).trans (Function.fiberMap_apply_coe σ hσ x.as ⟨s x.as, hs x.as⟩).symm)
  have hne := Function.fiberMap_ne_self hfix hσ x.as ⟨s x.as, hs x.as⟩
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.app_sub, permutationLocalSystemSection_app,
    permutationLocalSystemSection_app]
  -- Evaluate both components at `r` and at the sheet `e`: the left one reads the function
  -- `triv⁻¹ r` at `e`, the right one is `r • s x - r • t x`, since the component of the
  -- constant system at `x` is `ULift.moduleEquiv` itself.
  have hR : ((((TauCeti.LocalCoefficientSystem.constantFunctor B).map
      (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso.hom).app x ≫
        (hp.permutationLocalSystemSingle R x ⟨s x.as, hs x.as⟩ -
          hp.permutationLocalSystemSingle R x ⟨t x.as, ht x.as⟩)).hom (ULift.up r) :
        p ⁻¹' {x.as} →₀ R) =
      (hp.permutationLocalSystemSingle R x ⟨s x.as, hs x.as⟩).hom r -
        (hp.permutationLocalSystemSingle R x ⟨t x.as, ht x.as⟩).hom r :=
    (rfl)
  rw [permutationLocalSystemSingle_hom_apply, permutationLocalSystemSingle_hom_apply] at hR
  refine (hp.signLocalSystemToPermutationApp_apply R hσ hfin x _ e).trans
    (Eq.trans ?_ ((congrArg (fun f : p ⁻¹' {x.as} →₀ R ↦ f e) hR).trans
      (Finsupp.sub_apply _ _ e)).symm)
  rw [hσs]
  rcases hfib (s x.as) e (e.property.trans (hs x.as).symm) with he | he
  · obtain rfl : e = ⟨s x.as, hs x.as⟩ := Subtype.ext he
    refine (hp.signLocalSystemIsoOfSection_inv_app_apply hfix hfib s hs x r).trans ?_
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne.symm, sub_zero]
  · obtain rfl : e = Function.fiberMap σ hσ x.as ⟨s x.as, hs x.as⟩ :=
      Subtype.ext (he.trans (Function.fiberMap_apply_coe σ hσ x.as ⟨s x.as, hs x.as⟩).symm)
    refine (hp.signLocalSystemIsoOfSection_inv_app_apply_fiberMap hfix hfib s hs x r).trans ?_
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, zero_sub]

end DoubleCover

end IsCoveringMap
