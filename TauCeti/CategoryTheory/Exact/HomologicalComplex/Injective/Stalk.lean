/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.HomologicalComplex.Tail

/-!
# Injective resolutions of objects

Let `E` be an exact structure with enough injectives, and `M` an object. Splicing chosen injective
presentations `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹`, starting from `Z⁰ = M`, gives an injective resolution

```text
M ↣ I⁰ → I¹ → I² → ⋯
```

as a cochain complex `I` vanishing in negative degrees, with the presentations as a tail
(`TauCeti.ExactStructure.TailData`) whose object of cycles in degree `0` is `M`
(`TauCeti.ExactStructure.EnoughInjectives.stalkTailDataZZeroIso`). The map from `M` in degree `0`
to `I` is the map `TauCeti.ExactStructure.TailData.ι` of this tail, so its mapping cone is acyclic.

## Main definitions

* `TauCeti.ExactStructure.EnoughInjectives.stalkResolution`: the injective resolution of `M`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkTailData`: its tail.
* `TauCeti.ExactStructure.EnoughInjectives.stalkTailDataZZeroIso`: the cycles of the tail in
  degree `0` are `M`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkResolutionι`: the map from `M` in degree `0`.

## Main results

* `TauCeti.ExactStructure.EnoughInjectives.isInjective_stalkResolution_X`: the terms of the
  resolution are injective.
* `TauCeti.ExactStructure.EnoughInjectives.acyclic_mappingCone_stalkResolutionι`: the resolution
  map has acyclic mapping cone.
* `TauCeti.ExactStructure.EnoughInjectives.single_map_comp_stalkResolutionι` and
  `TauCeti.ExactStructure.EnoughInjectives.cyclesMap_stalkTailData_zero_eq_of_homotopy`: a map of
  resolutions restricts in degree `0` to a morphism `M ⟶ N`, which it extends.

## Implementation notes

The bodies of the resolution, its tail and the resolution map are not exposed, and the helpers of
the construction are private. Downstream code uses the lemmas above, and identifies the cycles of
the tail in degree `0` with `M` through the isomorphism `stalkTailDataZZeroIso` instead of by
unfolding definitions.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 12, for resolutions spliced from presentations.
* Bernhard Keller, *Chain complexes and stable categories*, Manuscripta Math. **67** (1990),
  379--417, Section 4.1, for injective resolutions in exact categories.
* The splicing dualizes `TauCeti.ExactStructure.EnoughProjectives.projectiveResolution`
  (`TauCeti/CategoryTheory/Exact/Resolution/Unbounded/Basic.lean`).
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
private noncomputable def stalkZ : ℕ → C
  | 0 => M
  | k + 1 => (hE.injectivePresentation (stalkZ k)).K

/-- The chosen injective presentation `Zᵏ ↣ Iᵏ ↠ Zᵏ⁺¹`. -/
private noncomputable abbrev stalkPresentation (k : ℕ) : E.InjectivePresentation (stalkZ hE M k) :=
  hE.injectivePresentation _

/-- The deflation `Iᵏ ↠ Zᵏ⁺¹` of the chosen presentation, with its target written as `Zᵏ⁺¹`. -/
private noncomputable def stalkP (k : ℕ) : (stalkPresentation hE M k).I ⟶ stalkZ hE M (k + 1) :=
  (stalkPresentation hE M k).p

/-- The inflation of the chosen presentation followed by `stalkP` is zero. -/
@[reassoc]
private theorem i_comp_stalkP (k : ℕ) : (stalkPresentation hE M k).i ≫ stalkP hE M k = 0 :=
  -- `stalkP` is the deflation of the presentation, with its target written as `Zᵏ⁺¹`.
  (stalkPresentation hE M k).zero

/-- The terms of the resolution, zero in negative degrees. -/
private noncomputable def stalkX : ℤ → C
  | Int.ofNat k => (stalkPresentation hE M k).I
  | Int.negSucc _ => 0

/-- The differentials of the resolution, `Iᵏ ↠ Zᵏ⁺¹ ↣ Iᵏ⁺¹`. -/
private noncomputable def stalkD : ∀ n, stalkX hE M n ⟶ stalkX hE M (n + 1)
  | Int.ofNat k => stalkP hE M k ≫ (stalkPresentation hE M (k + 1)).i
  | Int.negSucc _ => 0

private theorem stalkD_comp_stalkD (n : ℤ) : stalkD hE M n ≫ stalkD hE M (n + 1) = 0 :=
  match n with
  | Int.ofNat k => by
    -- `stalkD` is defined by matching on the degree, and `Int.ofNat k + 1` reduces to
    -- `Int.ofNat (k + 1)` only by evaluation, so `change` states the two differentials.
    change (stalkP hE M k ≫ (stalkPresentation hE M (k + 1)).i) ≫
      stalkP hE M (k + 1) ≫ (stalkPresentation hE M (k + 1 + 1)).i = 0
    rw [Category.assoc, i_comp_stalkP_assoc, zero_comp, comp_zero]
  | Int.negSucc _ => zero_comp

/-- The **injective resolution** of `M`: the complex `I⁰ → I¹ → ⋯` of the chosen injective
presentations. -/
noncomputable def stalkResolution : CochainComplex C ℤ :=
  CochainComplex.of (stalkX hE M) (stalkD hE M) (stalkD_comp_stalkD hE M)

/-- The terms of the resolution are injective. -/
theorem isInjective_stalkResolution_X (n : ℤ) : E.isInjective ((hE.stalkResolution M).X n) :=
  match n with
  | Int.ofNat k => (stalkPresentation hE M k).isInjective
  | Int.negSucc _ => E.isInjective.prop_of_isZero (isZero_zero C)

instance : (hE.stalkResolution M).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  obtain ⟨k, rfl⟩ := Int.eq_negSucc_of_lt_zero hi
  exact isZero_zero C

private theorem stalkResolution_d (k : ℕ) :
    (hE.stalkResolution M).d k (k + 1) = stalkP hE M k ≫ (stalkPresentation hE M (k + 1)).i := by
  dsimp only [stalkResolution]
  rw [CochainComplex.of_d]
  rfl

/-- The tail of the resolution: the chosen presentations. -/
noncomputable def stalkTailData : E.TailData (hE.stalkResolution M) where
  Z := stalkZ hE M
  i k := (stalkPresentation hE M k).i
  p k := stalkP hE M k
  zero k := (stalkPresentation hE M k).zero
  conflation k := (stalkPresentation hE M k).conflation
  fac k := (stalkResolution_d hE M k).symm

/-- The cycles of the resolution in degree `0` are `M`. -/
theorem stalkTailData_Z_zero : (hE.stalkTailData M).Z 0 = M :=
  (rfl)

/-- The cycles of the resolution in degree `k + 1` are the cokernel term of the chosen injective
presentation of the cycles in degree `k`. -/
theorem stalkTailData_Z_succ (k : ℕ) :
    (hE.stalkTailData M).Z (k + 1) = (hE.injectivePresentation ((hE.stalkTailData M).Z k)).K :=
  (rfl)

/-- The cycles of the resolution in degree `0` are `M`, as an isomorphism. -/
noncomputable def stalkTailDataZZeroIso : (hE.stalkTailData M).Z 0 ≅ M :=
  Iso.refl M

/-- The **resolution map** from `M` in degree `0`: the inflation `M ↣ I⁰`. -/
noncomputable def stalkResolutionι :
    (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ hE.stalkResolution M :=
  (hE.stalkTailData M).ι

/-- The resolution map is the map `TauCeti.ExactStructure.TailData.ι` of the tail, along
`stalkTailDataZZeroIso`. -/
@[reassoc]
theorem single_map_stalkTailDataZZeroIso_hom_comp_stalkResolutionι :
    (HomologicalComplex.single C (.up ℤ) 0).map (hE.stalkTailDataZZeroIso M).hom ≫
      hE.stalkResolutionι M = (hE.stalkTailData M).ι :=
  -- `stalkTailDataZZeroIso` is the identity of `M`.
  (congrArg (· ≫ hE.stalkResolutionι M) ((HomologicalComplex.single C (.up ℤ) 0).map_id M)).trans
    (Category.id_comp _)

@[simp]
theorem stalkResolutionι_f_zero :
    (hE.stalkResolutionι M).f 0 = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫
      (hE.stalkTailDataZZeroIso M).inv ≫ (hE.stalkTailData M).i 0 := by
  rw [← Iso.inv_hom_id_assoc ((HomologicalComplex.single C (.up ℤ) 0).mapIso
      (hE.stalkTailDataZZeroIso M)) (hE.stalkResolutionι M), Functor.mapIso_hom,
    single_map_stalkTailDataZZeroIso_hom_comp_stalkResolutionι, Functor.mapIso_inv,
    HomologicalComplex.comp_f, TailData.ι_f_zero, HomologicalComplex.single_map_f_self,
    Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]

@[simp]
theorem stalkResolutionι_f_of_ne {n : ℤ} (hn : n ≠ 0) : (hE.stalkResolutionι M).f n = 0 :=
  (hE.stalkTailData M).ι_f_of_ne hn

/-- **The resolution map has acyclic mapping cone**: `I` resolves `M`. -/
theorem acyclic_mappingCone_stalkResolutionι :
    E.acyclic (CochainComplex.mappingCone (hE.stalkResolutionι M)) :=
  (hE.stalkTailData M).acyclic_mappingCone_ι

variable {M} {N : C}

/-- A map of resolutions `Φ` extends its map of cycles in degree `0`, read as a morphism
`M ⟶ N`. -/
@[reassoc]
theorem single_map_comp_stalkResolutionι
    (Φ : hE.stalkResolution M ⟶ hE.stalkResolution N) :
    (HomologicalComplex.single C (.up ℤ) 0).map ((hE.stalkTailDataZZeroIso M).inv ≫
        (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) Φ 0 ≫
          (hE.stalkTailDataZZeroIso N).hom) ≫ hE.stalkResolutionι N =
      hE.stalkResolutionι M ≫ Φ :=
  -- `stalkTailDataZZeroIso` is the identity.
  (congrArg (fun g ↦ (HomologicalComplex.single C (.up ℤ) 0).map g ≫ hE.stalkResolutionι N)
    ((Category.id_comp _).trans (Category.comp_id _))).trans
      ((hE.stalkTailData M).single_map_comp_ι (hE.stalkTailData N) Φ)

/-- If the resolution map followed by a map of resolutions `Φ` is homotopic to `f : M ⟶ N`
followed by the resolution map, then `f` is the map of cycles of `Φ` in degree `0`. -/
theorem cyclesMap_stalkTailData_zero_eq_of_homotopy
    (Φ : hE.stalkResolution M ⟶ hE.stalkResolution N) (f : M ⟶ N)
    (h : Homotopy (hE.stalkResolutionι M ≫ Φ)
      ((HomologicalComplex.single C (.up ℤ) 0).map f ≫ hE.stalkResolutionι N)) :
    (hE.stalkTailDataZZeroIso M).inv ≫ (hE.stalkTailData M).cyclesMap (hE.stalkTailData N) Φ 0 ≫
      (hE.stalkTailDataZZeroIso N).hom = f :=
  -- `stalkTailDataZZeroIso` is the identity.
  ((Category.id_comp _).trans (Category.comp_id _)).trans
    ((hE.stalkTailData M).cyclesMap_zero_eq_of_homotopy (hE.stalkTailData N) Φ f h)

end EnoughInjectives

end TauCeti.ExactStructure
