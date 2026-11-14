/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Abelian
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map
public import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence

/-!
# Torsor classes of an abelian sheaf and sheaf cohomology

Let `F` be an abelian sheaf on a site `(C, J)`. Viewing `F` as a sheaf of groups, it has a pointed
set `NonabelianH1` of classes of `F`-torsors, and Mathlib's sheaf cohomology `Sheaf.H F 1`, the
group `Ext¹(ℤ, F)`. This file identifies the two (Stacks, Lemma 21.4.3 (03AJ)), compatibly with the
connecting maps of short exact sequences: for `0 → F → B → Q → 0` short exact, the class of the
torsor of lifts of a global section `q` of `Q` corresponds to `δ q`, where
`δ : H⁰(Q) → H¹(F)` is the connecting map of the long exact cohomology sequence.

To define the bijection, embed `F` into an injective abelian sheaf `I`, with cokernel `Q`. Both
sides are quotients of the global sections of `Q`: every `F`-torsor is a torsor of lifts
(`CategoryTheory.Sheaf.NonabelianH1.connecting_surjective_of_injective`), and `δ` is onto
`H¹(F)` since `H¹(I) = 0`. Two global sections of `Q` have isomorphic torsors of lifts if and
only if they differ by a global section of `I`, which by exactness of `H⁰(I) → H⁰(Q) → H¹(F)` is
the condition for them to have the same image under `δ`. The compatibility with an arbitrary
short exact sequence follows by comparing it with the injective one.

## Main declarations

* `CategoryTheory.Sheaf.H.zeroMulEquivSections F`: `H⁰(F)` is the group of global sections of
  `F`, written multiplicatively as the global sections of the underlying sheaf of groups.
* `CategoryTheory.Sheaf.NonabelianH1.connecting_eq_connecting_iff_δ_eq_δ`: for a short exact
  sequence of abelian sheaves, two global sections of the quotient have isomorphic torsors of
  lifts if and only if they have the same image under `δ`.
* `CategoryTheory.Sheaf.NonabelianH1.equivSheafH F`: the bijection between torsor classes and
  `H¹(F)`.
* `CategoryTheory.Sheaf.NonabelianH1.equivSheafH_connecting`: it sends the connecting map of
  torsors of lifts to the connecting map `δ` of sheaf cohomology, and `equivSheafH_one` says that
  it is a map of pointed sets.
* `CategoryTheory.Sheaf.NonabelianH1.equivSheafH_map`: extending the structure group of a torsor
  along a morphism of abelian sheaves corresponds to the induced map on `H¹`.

## References

* [The Stacks project, Lemma 21.4.3 (03AJ)](https://stacks.math.columbia.edu/tag/03AJ).
-/

public noncomputable section

open CategoryTheory Opposite Abelian AddCommGrpCat

universe w' w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace H

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The degree-zero cohomology `H⁰(F) = Hom(ℤ, F)` of an abelian sheaf `F` is the group of global
sections of `F`, written multiplicatively as the global sections of the underlying sheaf of
groups. A class is sent to the image of `1` under the corresponding morphism from the constant
presheaf `ℤ` (`zeroMulEquivSections_apply_coe`). No terminal object of the site is needed, unlike
for Mathlib's `CategoryTheory.Sheaf.H.equiv₀`. -/
def zeroMulEquivSections (F : Sheaf J AddCommGrpCat.{w}) :
    Multiplicative (H F 0) ≃*
      (((abelianSheafToGrpSheaf J).obj F).obj ⋙ forget GrpCat).sections :=
  (Ext.addEquiv₀.trans
    ((sheafificationAdjunction J AddCommGrpCat.{w}).homAddEquiv _ F)).toMultiplicative.trans
    (constIntHomMulEquivSections F)

/-- The global section of `F` given by a class `x` in `H⁰(F)`: its value over `U` is the image
of `1` under the morphism from the constant presheaf `ℤ` to `F` adjoint to `x`. -/
lemma zeroMulEquivSections_apply_coe (F : Sheaf J AddCommGrpCat.{w})
    (x : Multiplicative (H F 0)) (U : Cᵒᵖ) :
    (zeroMulEquivSections F x).1 U = abelianSheafToGrpSheafObjEquiv F U (.ofAdd
      (((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ F (Ext.addEquiv₀ x.toAdd)).app U
        ⟨1⟩)) :=
  constIntHomMulEquivSections_apply_coe F _ U

/-- The degree-zero class corresponding to a global section is the class of the sheaf morphism
adjoint to the morphism from the constant integer presheaf determined by that section. -/
lemma zeroMulEquivSections_symm_apply_toAdd (F : Sheaf J AddCommGrpCat.{w})
    (s : (((abelianSheafToGrpSheaf J).obj F).obj ⋙ forget GrpCat).sections) :
    ((zeroMulEquivSections F).symm s).toAdd =
      Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ F).symm
        (((constIntHomMulEquivSections F).symm s).toAdd)) :=
  (rfl)

/-- The identification of `H⁰` with global sections is natural in the abelian sheaf. -/
@[simp]
lemma zeroMulEquivSections_map {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (x : H F 0)
    (U : Cᵒᵖ) :
    (zeroMulEquivSections G (.ofAdd (H.map f 0 x))).1 U =
      ((abelianSheafToGrpSheaf J).map f).hom.app U ((zeroMulEquivSections F (.ofAdd x)).1 U) := by
  rw [zeroMulEquivSections_apply_coe, zeroMulEquivSections_apply_coe,
    abelianSheafToGrpSheaf_map_hom_app_abelianSheafToGrpSheafObjEquiv]
  -- `H.addEquiv₀_map` cannot be used by `rw` or `simp` here: `H G 0` is `Ext` out of the
  -- constant sheaf, which is only definitionally the sheafification of the constant presheaf
  -- appearing in `zeroMulEquivSections_apply_coe`.
  have h := congrArg ((sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv _ G)
    (H.addEquiv₀_map f x)
  have h' := (sheafificationAdjunction J AddCommGrpCat.{w}).homEquiv_naturality_right
    (Ext.addEquiv₀ x) f
  -- Evaluating `ψ ≫ (sheafToPresheaf J _).map f` at `1` over `U` applies `f` to `ψ.app U ⟨1⟩`.
  exact congrArg (fun ψ ↦ abelianSheafToGrpSheafObjEquiv G U (.ofAdd (ψ.app U ⟨1⟩)))
    (h.trans h')

/-- The global section given by a difference `x' - x` in `H⁰(F)` is `s⁻¹ * s'`, for `s` and `s'`
the global sections given by `x` and `x'`. -/
private lemma zeroMulEquivSections_sub (F : Sheaf J AddCommGrpCat.{w}) (x x' : H F 0) :
    zeroMulEquivSections F (.ofAdd (x' - x)) =
      (zeroMulEquivSections F (.ofAdd x))⁻¹ * zeroMulEquivSections F (.ofAdd x') := by
  rw [sub_eq_neg_add, ofAdd_add, ofAdd_neg, map_mul, map_inv]

end H

namespace NonabelianH1

variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

section

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)

/-- For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves, two global
sections of `S.X₃` have isomorphic torsors of lifts if and only if they have the same image under
the connecting map `δ : H⁰(S.X₃) → H¹(S.X₁)`: both conditions say that they differ by a global
section of `S.X₂`. -/
theorem connecting_eq_connecting_iff_δ_eq_δ
    (q q' : (((abelianSheafToGrpSheaf J).obj S.X₃).obj ⋙ forget GrpCat).sections) :
    connecting hS.isGroupExtension q = connecting hS.isGroupExtension q' ↔
      H.δ hS 0 1 rfl ((H.zeroMulEquivSections S.X₃).symm q).toAdd =
        H.δ hS 0 1 rfl ((H.zeroMulEquivSections S.X₃).symm q').toAdd := by
  obtain ⟨x, rfl⟩ :=
    ((H.zeroMulEquivSections S.X₃).surjective.comp Multiplicative.ofAdd.surjective) q
  obtain ⟨x', rfl⟩ :=
    ((H.zeroMulEquivSections S.X₃).surjective.comp Multiplicative.ofAdd.surjective) q'
  simp only [Function.comp_apply, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  rw [connecting_eq_connecting_iff, eq_comm, ← sub_eq_zero, ← map_sub,
    H.exact_map_δ hS 0 1 rfl (x' - x)]
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨((H.zeroMulEquivSections S.X₂).symm c).toAdd, ?_⟩,
    fun ⟨z, hz⟩ ↦ ⟨H.zeroMulEquivSections S.X₂ (.ofAdd z), fun U ↦ ?_⟩⟩
  · refine Multiplicative.ofAdd.injective ((H.zeroMulEquivSections S.X₃).injective
      (Subtype.ext (funext fun U ↦ ?_)))
    rw [H.zeroMulEquivSections_map, ofAdd_toAdd, MulEquiv.apply_symm_apply, hc,
      H.zeroMulEquivSections_sub,
      GrpCat.sections_mul_val, GrpCat.sections_inv_val]
  · rw [← H.zeroMulEquivSections_map, hz, H.zeroMulEquivSections_sub, GrpCat.sections_mul_val,
      GrpCat.sections_inv_val]

variable [Injective S.X₂]

/-- For an injective middle term, every torsor class of `S.X₁` is the class of the torsor of
lifts of a global section of `S.X₃`. -/
private lemma surjective_connecting :
    Function.Surjective fun x : H S.X₃ 0 ↦
      connecting hS.isGroupExtension (H.zeroMulEquivSections S.X₃ (.ofAdd x)) :=
  (connecting_surjective_of_injective hS.isGroupExtension).comp
    ((H.zeroMulEquivSections S.X₃).surjective.comp Multiplicative.ofAdd.surjective)

/-- For an injective middle term, the map from torsor classes of `S.X₁` to `H¹(S.X₁)` sending the
class of the torsor of lifts of `x` to `δ x`. -/
private def toHOfInjective (y : NonabelianH1 ((abelianSheafToGrpSheaf J).obj S.X₁)) :
    H S.X₁ 1 :=
  H.δ hS 0 1 rfl (Function.surjInv (surjective_connecting hS) y)

private lemma toHOfInjective_connecting (x : H S.X₃ 0) :
    toHOfInjective hS (connecting hS.isGroupExtension (H.zeroMulEquivSections S.X₃ (.ofAdd x))) =
      H.δ hS 0 1 rfl x :=
  by
  have h := (connecting_eq_connecting_iff_δ_eq_δ hS _ (H.zeroMulEquivSections S.X₃ (.ofAdd x))).1
    (Function.surjInv_eq (surjective_connecting hS) _)
  rwa [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, toAdd_ofAdd, toAdd_ofAdd] at h

private lemma bijective_toHOfInjective : Function.Bijective (toHOfInjective hS) := by
  refine ⟨fun y y' h ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := surjective_connecting hS y
    obtain ⟨x', rfl⟩ := surjective_connecting hS y'
    rw [toHOfInjective_connecting, toHOfInjective_connecting] at h
    exact (connecting_eq_connecting_iff_δ_eq_δ hS _ _).2 (by simpa using h)
  · -- `δ` is onto `H¹(S.X₁)` because `H¹(S.X₂)` vanishes.
    obtain ⟨x, rfl⟩ := H.δ_surjective hS 0 1 rfl inferInstance z
    exact ⟨_, toHOfInjective_connecting hS x⟩

end

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]

/-- The classes of torsors under an abelian sheaf `F` are in bijection with the sheaf cohomology
`H¹(F)` (Stacks, Lemma 21.4.3 (03AJ)). The bijection is characterised by
`equivSheafH_connecting`: for every short exact sequence `0 → F → B → Q → 0`, the class of the
torsor of lifts of a global section of `Q` goes to its image under the connecting map
`δ : H⁰(Q) → H¹(F)`; in particular it does not depend on the injective embedding of `F` used to
construct it. -/
def equivSheafH (F : Sheaf J AddCommGrpCat.{w}) :
    NonabelianH1 ((abelianSheafToGrpSheaf J).obj F) ≃ H F 1 :=
  Equiv.ofBijective _ (bijective_toHOfInjective (TauCeti.injectiveCokernelSequence_shortExact F))

/-- For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0` of abelian sheaves, `equivSheafH`
sends the class of the torsor of lifts of a global section `q` of `S.X₃` to `δ q ∈ H¹(S.X₁)`,
viewing `q` as a class in `H⁰(S.X₃)`. -/
@[simp]
theorem equivSheafH_connecting {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (q : (((abelianSheafToGrpSheaf J).obj S.X₃).obj ⋙ forget GrpCat).sections) :
    equivSheafH S.X₁ (connecting hS.isGroupExtension q) =
      H.δ hS 0 1 rfl ((H.zeroMulEquivSections S.X₃).symm q).toAdd := by
  obtain ⟨x, rfl⟩ :=
    ((H.zeroMulEquivSections S.X₃).surjective.comp Multiplicative.ofAdd.surjective) q
  simp only [Function.comp_apply, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  have := hS.mono_f
  have := hS.epi_g
  have hS₀ := TauCeti.injectiveCokernelSequence_shortExact S.X₁
  -- Compare `S` with the extension `0 → S.X₁ → I → I / S.X₁ → 0` defining `equivSheafH`, through
  -- an extension `β : S.X₂ ⟶ I` of the embedding into the injective sheaf `I`.
  let β : S.X₂ ⟶ Injective.under S.X₁ := Injective.factorThru (Injective.ι S.X₁) S.f
  have hβ : S.f ≫ β = Injective.ι S.X₁ := Injective.comp_factorThru _ _
  let γ : S.X₃ ⟶ Limits.cokernel (Injective.ι S.X₁) :=
    hS.exact.desc (β ≫ Limits.cokernel.π _) (by rw [reassoc_of% hβ, Limits.cokernel.condition])
  have hγ : S.g ≫ γ = β ≫ Limits.cokernel.π _ := hS.exact.g_desc _ _
  let φ : S ⟶ TauCeti.injectiveCokernelSequence S.X₁ :=
    { τ₁ := 𝟙 _, τ₂ := β, τ₃ := γ, comm₁₂ := by simpa using hβ.symm, comm₂₃ := hγ.symm }
  have hδ : H.δ hS₀ 0 1 rfl (H.map γ 0 x) = H.δ hS 0 1 rfl x :=
    (H.δ_naturality 0 1 rfl hS hS₀ φ x).trans (H.map_id_apply _)
  rw [← hδ, connecting_eq_connecting_of_comp_eq hS.isGroupExtension hS₀.isGroupExtension
    ((abelianSheafToGrpSheaf J).map β) ((abelianSheafToGrpSheaf J).map γ)
    (by rw [← Functor.map_comp, hβ]) (by rw [← Functor.map_comp, ← Functor.map_comp, hγ]) _
    _ fun U ↦ (H.zeroMulEquivSections_map γ x U).symm]
  exact toHOfInjective_connecting hS₀ _

/-- The inverse comparison sends a cohomological connecting class to the class of its torsor
of lifts. -/
@[simp]
theorem equivSheafH_symm_δ {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
    (x : H S.X₃ 0) :
    (equivSheafH S.X₁).symm (H.δ hS 0 1 rfl x) =
      connecting hS.isGroupExtension (H.zeroMulEquivSections S.X₃ (.ofAdd x)) :=
  (equivSheafH S.X₁).symm_apply_eq.2 ((equivSheafH_connecting hS _).trans (by simp)).symm

/-- `equivSheafH` sends the class of the trivial torsor to `0`. -/
@[simp]
theorem equivSheafH_one (F : Sheaf J AddCommGrpCat.{w}) : equivSheafH F 1 = 0 := by
  have h := toHOfInjective_connecting (TauCeti.injectiveCokernelSequence_shortExact F) 0
  rwa [ofAdd_zero, _root_.map_one, connecting_one, map_zero] at h

/-- The inverse of `equivSheafH` sends `0` to the class of the trivial torsor. -/
@[simp]
theorem equivSheafH_symm_zero (F : Sheaf J AddCommGrpCat.{w}) : (equivSheafH F).symm 0 = 1 :=
  (equivSheafH F).symm_apply_eq.2 (equivSheafH_one F).symm

/-- A torsor class goes to `0` under `equivSheafH` exactly when it is the trivial class. -/
@[simp]
theorem equivSheafH_eq_zero_iff {F : Sheaf J AddCommGrpCat.{w}}
    {y : NonabelianH1 ((abelianSheafToGrpSheaf J).obj F)} : equivSheafH F y = 0 ↔ y = 1 := by
  rw [← equivSheafH_one F, (equivSheafH F).apply_eq_iff_eq]

/-- The inverse of `equivSheafH` sends a class to the trivial torsor class exactly when the class
is `0`. -/
@[simp]
theorem equivSheafH_symm_eq_one_iff {F : Sheaf J AddCommGrpCat.{w}} {z : H F 1} :
    (equivSheafH F).symm z = 1 ↔ z = 0 := by
  rw [← equivSheafH_symm_zero F, (equivSheafH F).symm.apply_eq_iff_eq]

section Naturality

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- The comparison between torsor classes and `H¹` is natural in the coefficient sheaf:
extending the structure group along `f` agrees with the cohomological map `H.map f 1`. -/
@[simp]
theorem equivSheafH_map {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G)
    (x : NonabelianH1 ((abelianSheafToGrpSheaf J).obj F)) :
    equivSheafH G (map ((abelianSheafToGrpSheaf J).map f) x) =
      H.map f 1 (equivSheafH F x) := by
  let φ := TauCeti.injectiveCokernelSequenceMap f
  have hφ : φ.τ₁ = f := TauCeti.injectiveCokernelSequenceMap_τ₁ f
  have hF := TauCeti.injectiveCokernelSequence_shortExact F
  have hG := TauCeti.injectiveCokernelSequence_shortExact G
  -- Every torsor is a torsor of lifts for the chosen injective embedding. Extend `f` to a
  -- morphism of these short exact sequences and compare their connecting maps.
  obtain ⟨q, rfl⟩ := surjective_connecting hF x
  rw [map_connecting_of_comp_eq hF.isGroupExtension hG.isGroupExtension
    ((abelianSheafToGrpSheaf J).map f) ((abelianSheafToGrpSheaf J).map φ.τ₂)
    ((abelianSheafToGrpSheaf J).map φ.τ₃)
    (by
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg _ (by simpa only [hφ] using φ.comm₁₂.symm))
    (by rw [← Functor.map_comp, ← Functor.map_comp]; exact congrArg _ φ.comm₂₃)
    _ (H.zeroMulEquivSections _ (.ofAdd (H.map φ.τ₃ 0 q)))
    (fun U ↦ (H.zeroMulEquivSections_map φ.τ₃ q U).symm)]
  simp only [equivSheafH_connecting hG, equivSheafH_connecting hF,
    MulEquiv.symm_apply_apply, toAdd_ofAdd]
  simpa only [hφ] using H.δ_naturality 0 1 rfl hF hG φ q

/-- The inverse comparison from `H¹` to torsor classes also commutes with change of
coefficients. -/
@[simp]
theorem equivSheafH_symm_map {F G : Sheaf J AddCommGrpCat.{w}} (f : F ⟶ G) (x : H F 1) :
    (equivSheafH G).symm (H.map f 1 x) =
      map ((abelianSheafToGrpSheaf J).map f) ((equivSheafH F).symm x) := by
  apply (equivSheafH G).injective
  simp

end Naturality

end NonabelianH1

end CategoryTheory.Sheaf
