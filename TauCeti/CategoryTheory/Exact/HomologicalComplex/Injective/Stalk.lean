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
(`TauCeti.ExactStructure.TailData`) whose object of cycles in degree `0` is `M` by definition. The
map from `M` in degree `0` to `I` is the map `TauCeti.ExactStructure.TailData.ι` of this tail, so
its mapping cone is acyclic by `TauCeti.ExactStructure.TailData.acyclic_mappingCone_ι`.

## Main definitions

* `TauCeti.ExactStructure.EnoughInjectives.stalkResolution`: the injective resolution of `M`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkTailData`: its tail, with cycles `M` in degree `0`.
* `TauCeti.ExactStructure.EnoughInjectives.stalkResolutionι`: the map from `M` in degree `0`.

## Main results

* `TauCeti.ExactStructure.EnoughInjectives.isInjective_stalkResolution_X`: the terms of the
  resolution are injective.
* `TauCeti.ExactStructure.EnoughInjectives.stalkResolution_d`: its differentials.
* `TauCeti.ExactStructure.EnoughInjectives.stalkTailData_Z_zero`: its cycles in degree `0` are
  `M`.

## Implementation notes

`stalkZ` and `stalkTailData` are exposed and implicitly reducible so that the cycles of the tail
in degree `0` are `M` by definition: a map of resolutions then restricts in degree `0` to a
morphism `M ⟶ N` of `C`, with no transport along an isomorphism. `stalkResolution`, with `stalkX`
and `stalkD`, is exposed so that its terms are the chosen injective objects in the statement of
`stalkTailData`.

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
-- Exposed and implicitly reducible so that the cycles in degree zero are `M` by definition, also
-- when type checking rewritten goals.
@[expose, implicit_reducible] noncomputable def stalkZ : ℕ → C
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
    -- `stalkD` is defined by matching on the degree, and `Int.ofNat k + 1` reduces to
    -- `Int.ofNat (k + 1)` only by evaluation, so `change` states the two differentials.
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
    (hE.stalkResolution M).d k (k + 1) = hE.stalkP M k ≫ (hE.stalkPresentation M (k + 1)).i := by
  dsimp only [stalkResolution]
  rw [CochainComplex.of_d]
  rfl

/-- The tail of the resolution: the chosen presentations, with cycles `M` in degree `0`. -/
-- Exposed and implicitly reducible so that its cycles are `stalkZ` by definition, also when type
-- checking rewritten goals.
@[expose, implicit_reducible]
noncomputable def stalkTailData : E.TailData (hE.stalkResolution M) where
  Z := hE.stalkZ M
  i k := (hE.stalkPresentation M k).i
  p k := hE.stalkP M k
  zero k := hE.i_stalkP M k
  conflation k := (hE.stalkPresentation M k).conflation
  fac k := (stalkResolution_d hE M k).symm

/-- The cycles of the resolution in degree `0` are `M`. -/
@[simp]
theorem stalkTailData_Z_zero : (hE.stalkTailData M).Z 0 = M :=
  rfl

/-- The cycles of the resolution in degree `k + 1` are the cokernel term of the chosen
presentation in degree `k`. -/
@[simp]
theorem stalkTailData_Z_succ (k : ℕ) :
    (hE.stalkTailData M).Z (k + 1) = (hE.stalkPresentation M k).K :=
  rfl

/-- The resolution map from `M` in degree `0`: the inflation `M ↣ I⁰`, as the map
`TauCeti.ExactStructure.TailData.ι` of the tail. -/
noncomputable abbrev stalkResolutionι :
    (HomologicalComplex.single C (.up ℤ) 0).obj M ⟶ hE.stalkResolution M :=
  (hE.stalkTailData M).ι

end EnoughInjectives

end TauCeti.ExactStructure
