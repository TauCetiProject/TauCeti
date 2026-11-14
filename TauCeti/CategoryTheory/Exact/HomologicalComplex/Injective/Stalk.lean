/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Tail
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Injective.Basic
public import TauCeti.CategoryTheory.Exact.Injective

/-!
# Injective resolutions of objects

Let `E` be an exact structure with enough injectives, and `M` an object. Splicing chosen injective
presentations `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹`, starting from `Z⁰ = M`, gives an injective resolution

```text
M ↣ I⁰ → I¹ → I² → ⋯
```

as a cochain complex `I` vanishing in negative degrees, with the presentations as a tail
(`TauCeti.ExactStructure.TailData`) whose object of cycles in degree `0` is `M`. The map from `M`
in degree `0` to `I` has acyclic mapping cone, by
`TauCeti.ExactStructure.acyclic_mappingCone_of_isPushout`.

## Main definitions

* `TauCeti.ExactStructure.EnoughInjectives.stalkResolution`: the injective resolution of `M`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkTailData`: its tail, with cycles `M` in degree `0`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkResolutionι`: the map from `M` in degree `0`.

## Main results

* `TauCeti.ExactStructure.EnoughInjectives.acyclic_mappingCone_stalkResolutionι`: the mapping cone
  of the resolution map is acyclic.
* `TauCeti.ExactStructure.EnoughInjectives.single_map_comp_stalkResolutionι`: a map of
  resolutions extends its map of cycles in degree `0`.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {E : ExactStructure C}

namespace EnoughInjectives

variable (hE : E.EnoughInjectives) (M : C)

/-- The objects of cycles of the resolution: `Z⁰ = M`, and `Zᵏ⁺¹` the cokernel term of the chosen
injective presentation of `Zᵏ`. -/
-- Exposed so that the cycles in degree zero are `M` by definition.
@[expose] noncomputable def stalkZ : ℕ → C
  | 0 => M
  | k + 1 => (hE.injectivePresentation (stalkZ k)).K

/-- The chosen injective presentation `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹`. -/
noncomputable abbrev stalkPresentation (k : ℕ) : E.InjectivePresentation (hE.stalkZ M k) :=
  hE.injectivePresentation _

/-- The deflation `Iᵏ ↠ Zᵏ⁺¹` of the chosen presentation, with its target written as `Zᵏ⁺¹`. -/
-- Exposed so that the presentation, with this deflation, is a conflation by definition.
@[expose] noncomputable def stalkP (k : ℕ) : (hE.stalkPresentation M k).I ⟶ hE.stalkZ M (k + 1) :=
  (hE.stalkPresentation M k).p

/-- The chosen presentation `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹` composes to zero. -/
@[reassoc (attr := simp)]
theorem i_stalkP (k : ℕ) : (hE.stalkPresentation M k).i ≫ hE.stalkP M k = 0 :=
  (hE.stalkPresentation M k).zero

/-- The terms of the resolution, zero in negative degrees. -/
-- Exposed so that the terms are the chosen injective objects by definition.
@[expose] noncomputable def stalkX : ℤ → C
  | Int.ofNat k => (hE.stalkPresentation M k).I
  | Int.negSucc _ => 0

/-- The differentials of the resolution, `Iᵏ ↠ Zᵏ⁺¹ ↣ Iᵏ⁺¹`. -/
-- Exposed together with `stalkX`, so that the complex has the chosen terms by definition.
@[expose] noncomputable def stalkD : ∀ n, stalkX hE M n ⟶ stalkX hE M (n + 1)
  | Int.ofNat k => hE.stalkP M k ≫ (hE.stalkPresentation M (k + 1)).i
  | Int.negSucc _ => 0

/-- The differentials of the resolution compose to zero. -/
theorem stalkD_comp_stalkD (n : ℤ) : stalkD hE M n ≫ stalkD hE M (n + 1) = 0 :=
  match n with
  | Int.ofNat k => by
    change (hE.stalkP M k ≫ (hE.stalkPresentation M (k + 1)).i) ≫
      hE.stalkP M (k + 1) ≫ (hE.stalkPresentation M (k + 1 + 1)).i = 0
    rw [Category.assoc, i_stalkP_assoc, zero_comp, comp_zero]
  | Int.negSucc _ => zero_comp

/-- The **injective resolution** of `M`: the complex `I⁰ → I¹ → ⋯` of the chosen injective
presentations. -/
-- Exposed so that its terms are the chosen injective objects by definition.
@[expose] noncomputable def stalkResolution : CochainComplex C ℤ :=
  CochainComplex.of (stalkX hE M) (stalkD hE M) (stalkD_comp_stalkD hE M)

/-- The terms of the resolution are injective. -/
theorem isInjective_stalkResolution_X (n : ℤ) : E.isInjective ((hE.stalkResolution M).X n) :=
  match n with
  | Int.ofNat k => (hE.stalkPresentation M k).isInjective
  | Int.negSucc _ => E.isInjective.prop_of_isZero (isZero_zero C)

instance : (hE.stalkResolution M).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  exact isZero_zero C

/-- The differential of the resolution is `Iᵏ ↠ Zᵏ⁺¹ ↣ Iᵏ⁺¹`. -/
theorem stalkResolution_d (k : ℕ) :
    hE.stalkP M k ≫ (hE.stalkPresentation M (k + 1)).i = (hE.stalkResolution M).d k (k + 1) := by
  dsimp only [stalkResolution]
  rw [CochainComplex.of_d]
  rfl

/-- The tail of the resolution: the chosen presentations, with cycles `M` in degree `0`. -/
-- Exposed so that its cycles are `stalkZ` by definition.
@[expose] noncomputable def stalkTailData : E.TailData (hE.stalkResolution M) where
  Z := hE.stalkZ M
  i k := (hE.stalkPresentation M k).i
  p k := hE.stalkP M k
  zero k := hE.i_stalkP M k
  conflation k := (hE.stalkPresentation M k).conflation
  fac k := hE.stalkResolution_d M k

/-- The resolution map from `M` in degree `0`: the inflation `M ↣ I⁰`. -/
noncomputable def stalkResolutionι :
    (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ hE.stalkResolution M :=
  HomologicalComplex.mkHomFromSingle ((hE.stalkTailData M).i 0) (by
    rintro _ rfl
    exact (hE.stalkTailData M).i_d 0)

/-- In degree `0`, the resolution map is the inflation `M ↣ I⁰`. -/
theorem stalkResolutionι_f_zero :
    (hE.stalkResolutionι M).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ (hE.stalkTailData M).i 0 :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- A map of resolutions `Φ : I_M ⟶ I_N` extends its map of cycles `f : M ⟶ N` in degree `0`,
along the resolution maps. -/
@[reassoc]
theorem single_map_comp_stalkResolutionι {N : C}
    (Φ : hE.stalkResolution M ⟶ hE.stalkResolution N) (f : M ⟶ N)
    (hf : (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) Φ 0 = f) :
    (HomologicalComplex.single C (.up ℤ) 0).map f ≫ hE.stalkResolutionι N =
      hE.stalkResolutionι M ≫ Φ := by
  have hf' : f ≫ (hE.stalkTailData N).i 0 = (hE.stalkTailData M).i 0 ≫ Φ.f 0 := by
    subst hf
    exact TailData.cyclesMap_i _ _ Φ 0
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hE.stalkResolutionι_f_zero M,
    hE.stalkResolutionι_f_zero N, HomologicalComplex.single_map_f_self]
  have e : (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).hom ≫ (hE.stalkTailData N).i 0 =
        (hE.stalkTailData N).i 0 :=
    Iso.inv_hom_id_assoc _ _
  refine (Category.assoc _ _ _).trans ((congrArg (fun z ↦ _ ≫ z) (Category.assoc _ _ _)).trans ?_)
  exact (congrArg (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ _ ≫ z)
    e).trans ((congrArg (fun z ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ z)
      hf').trans (Category.assoc _ _ _).symm)

/-- The cycles of the mapping cone of the resolution map: those of the resolution in nonnegative
degrees, zero in negative degrees. -/
private noncomputable def coneB : ℤ → C
  | Int.ofNat k => hE.stalkZ M k
  | Int.negSucc _ => 0

private noncomputable def coneJ : ∀ m, coneB hE M m ⟶ (hE.stalkResolution M).X m
  | Int.ofNat k => (hE.stalkTailData M).i k
  | Int.negSucc _ => 𝟙 0

private noncomputable def coneU : ∀ m, (hE.stalkResolution M).X m ⟶ coneB hE M (m + 1)
  | Int.ofNat k => (hE.stalkTailData M).p k
  | Int.negSucc _ => 0

private noncomputable def coneV :
    ∀ m, ((HomologicalComplex.single C (.up ℤ) 0).obj M).X m ⟶ coneB hE M m
  | Int.ofNat 0 => (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom
  | Int.ofNat (_ + 1) => 0
  | Int.negSucc _ => 0

omit [HasBinaryBiproducts C] in
private theorem isZero_single_X {m : ℤ} (hm : m ≠ 0) :
    IsZero (((HomologicalComplex.single C (.up ℤ) 0).obj M).X m) :=
  HomologicalComplex.isZero_single_obj_X _ 0 M m hm

/-- **The mapping cone of the resolution map is acyclic.** -/
theorem acyclic_mappingCone_stalkResolutionι :
    E.acyclic (CochainComplex.mappingCone (hE.stalkResolutionι M)) := by
  refine E.acyclic_mappingCone_of_isPushout _ (coneB hE M) (coneJ hE M) (fun _ ↦ 0) (coneU hE M)
    (coneV hE M) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_)
  · match m with
    | Int.ofNat k => exact E.isInflation_f ((hE.stalkTailData M).conflation k)
    | Int.negSucc _ => exact E.isInflation_id 0
  · match m with
    | Int.ofNat k =>
      exact (E.isKernelCokernelPair _ ((hE.stalkTailData M).conflation k)).isPushout_of_isZero
        (isZero_single_X M (by lia))
    | Int.negSucc 0 =>
      have : IsIso (coneJ hE M (Int.negSucc 0)) := inferInstanceAs (IsIso (𝟙 _))
      have : IsIso (coneV hE M (Int.negSucc 0 + 1)) :=
        inferInstanceAs (IsIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom)
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_src _ _⟩
    | Int.negSucc (k + 1) =>
      have : IsIso (coneJ hE M (Int.negSucc (k + 1))) := inferInstanceAs (IsIso (𝟙 _))
      have : IsIso (coneV hE M (Int.negSucc (k + 1) + 1)) :=
        isIso_of_source_target_iso_zero _ (isZero_single_X M (by lia)).isoZero (Iso.refl 0)
      exact IsPushout.of_horiz_isIso ⟨(isZero_zero C).eq_of_src _ _⟩
  · match m with
    | Int.ofNat k => exact (hE.stalkTailData M).fac k
    | Int.negSucc _ => exact (isZero_zero C).eq_of_src _ _
  · match m with
    | Int.ofNat 0 => exact (hE.stalkResolutionι_f_zero M).symm
    | Int.ofNat (k + 1) => exact (isZero_single_X M (by lia)).eq_of_src _ _
    | Int.negSucc _ => exact (isZero_single_X M (by lia)).eq_of_src _ _
  · simp
  · simp

end EnoughInjectives

end TauCeti.ExactStructure
