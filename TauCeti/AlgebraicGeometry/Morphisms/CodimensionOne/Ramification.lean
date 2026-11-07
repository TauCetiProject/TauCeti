/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint
public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified

import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk
import TauCeti.AlgebraicGeometry.Scheme.StalkSpecializes
import TauCeti.RingTheory.DiscreteValuationRing.BaseChange.Unramified

/-!
# Unramified and tamely ramified covers in codimension one

Let `X` be a scheme, `U ⊆ X` an open subscheme and `f : Y ⟶ U` a morphism, typically a finite
étale cover of `U`. Following Stacks, Section 58.31, `Y` is *unramified* (resp. *tamely
ramified*) *over `X` in codimension one* if for every codimension-one point `ξ ∉ U` of `X` the
generic fibre of `Y` over `Spec 𝒪_{X,ξ}` is unramified (resp. tamely ramified) with respect to
`𝒪_{X,ξ}`, in the sense of `TauCeti.Algebra.IsUnramifiedWRT` (resp.
`TauCeti.Algebra.IsTamelyRamifiedWRT`).

Stacks writes the generic fibre as `Y ×_U Spec K_ξ = Spec L_ξ`, where `K_ξ` is the fraction field
of the discrete valuation ring `𝒪_{X,ξ}`, and asks the condition of each field factor of the
finite separable `K_ξ`-algebra `L_ξ`. Here the condition is stated pointwise. The points of
`Spec 𝒪_{X,ξ}` map bijectively onto the generizations of `ξ`; for a discrete valuation ring the
only one other than `ξ` is the image `η` of the generic point, and `κ(η)` is `K_ξ`
(`TauCeti.AlgebraicGeometry.Scheme.isFractionRing_residueField_of_specializes`). The field
factors of `L_ξ` are the residue fields `κ(y)` of the points `y` of `Y` over `η`, as
`𝒪_{X,ξ}`-algebras through `𝒪_{X,ξ} ⟶ κ(η) ⟶ κ(y)`. So the definitions ask, for every `y : Y`
whose image in `X` generizes `ξ`, that `κ(y)` be unramified (resp. tamely ramified) with respect
to `𝒪_{X,ξ}`. Since `ξ ∉ U`, such an image is never `ξ` itself.

Hypotheses such as `X` locally Noetherian, `U` dense, `f` finite étale and `𝒪_{X,ξ}` a discrete
valuation ring are carried by the statements that use them, not by the definitions.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.IsUnramifiedInCodimOne f`: `f : Y ⟶ U` is unramified over `X`
  in codimension one.
* `AlgebraicGeometry.Scheme.Hom.IsTamelyRamifiedInCodimOne f`: `f : Y ⟶ U` is tamely ramified
  over `X` in codimension one.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsUnramifiedInCodimOne.isTamelyRamifiedInCodimOne`: unramified
  in codimension one implies tamely ramified in codimension one.
* `AlgebraicGeometry.Scheme.Hom.isUnramifiedInCodimOne_of_isOpenImmersion`: if the codimension
  one points outside `U` have regular local rings, every open subscheme of `U`, for instance the
  trivial cover `𝟙 U`, is unramified over `X` in codimension one.
* `AlgebraicGeometry.Scheme.Hom.IsUnramifiedInCodimOne.baseChange`: being unramified in
  codimension one is stable under base change along `g : X' ⟶ X`, if `g` maps the
  codimension-one points of `X'` outside `g⁻¹ U` to codimension-one points of `X`, and the local
  rings at these points are discrete valuation rings (Stacks, Lemma 58.31.1 (0EYD), the
  unramified case).

The base change theorem reduces to the base change of unramified extensions of discrete
valuation rings, `TauCeti.Algebra.IsUnramifiedWRT.baseChange` (Stacks, Lemma 15.116.9 (0EXY)):
for a point `y'` of the base change over `y ∈ Y`, the residue field `κ(y')` is a quotient of
`κ(x') ⊗[κ(x)] κ(y)`, where `x` and `x'` are the images of `y` and `y'` in `X` and `X'`
(`AlgebraicGeometry.Scheme.Pullback.closure_range_residueFieldMap_eq_top`). Because the
definitions are pointwise, Stacks' hypotheses that `X` and `X'` are locally Noetherian and that
`g⁻¹ U` is dense are not needed.

## References

* [Stacks Project, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE), the definitions
  preceding Lemma 58.31.1, and [Lemma 58.31.1](https://stacks.math.columbia.edu/tag/0EYD).
-/

public section

open CategoryTheory Limits TauCeti.AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} {U : X.Opens} (f : Y ⟶ U)

/-- `f : Y ⟶ U` is **unramified over `X` in codimension one**: for every codimension-one point `ξ`
of `X` outside `U` and every point `y` of `Y` whose image in `X` generizes `ξ`, the residue field
`κ(y)` is unramified with respect to `𝒪_{X,ξ}`, as an algebra through `𝒪_{X,ξ} ⟶ κ(f y) ⟶ κ(y)`.
For `f` finite étale and `𝒪_{X,ξ}` a discrete valuation ring, these residue fields are the field
factors of the generic fibre `L_ξ` of `Y` over `Spec 𝒪_{X,ξ}`. -/
@[stacks 0BSE "unramified over `X` in codimension one, stated on residue fields of points"]
def IsUnramifiedInCodimOne : Prop :=
  ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
    letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
      (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
    TauCeti.Algebra.IsUnramifiedWRT (X.presheaf.stalk ξ) (Y.residueField y)

/-- `f : Y ⟶ U` is **tamely ramified over `X` in codimension one**: for every codimension-one point
`ξ` of `X` outside `U` and every point `y` of `Y` whose image in `X` generizes `ξ`, the residue
field `κ(y)` is tamely ramified with respect to `𝒪_{X,ξ}`, as an algebra through
`𝒪_{X,ξ} ⟶ κ(f y) ⟶ κ(y)`. For `f` finite étale and `𝒪_{X,ξ}` a discrete valuation ring, these
residue fields are the field factors of the generic fibre `L_ξ` of `Y` over `Spec 𝒪_{X,ξ}`. -/
@[stacks 0BSE "tamely ramified over `X` in codimension one, stated on residue fields of points"]
def IsTamelyRamifiedInCodimOne : Prop :=
  ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
    letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
      (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
    TauCeti.Algebra.IsTamelyRamifiedWRT (X.presheaf.stalk ξ) (Y.residueField y)

/-- Unfolds `IsUnramifiedInCodimOne` to its condition on the residue fields of points. -/
theorem isUnramifiedInCodimOne_def :
    f.IsUnramifiedInCodimOne ↔
      ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
        letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
          (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
        TauCeti.Algebra.IsUnramifiedWRT (X.presheaf.stalk ξ) (Y.residueField y) :=
  Iff.rfl

/-- Unfolds `IsTamelyRamifiedInCodimOne` to its condition on the residue fields of points. -/
theorem isTamelyRamifiedInCodimOne_def :
    f.IsTamelyRamifiedInCodimOne ↔
      ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → ∀ (y : Y) (h : (f ≫ U.ι) y ⤳ ξ),
        letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
          (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
        TauCeti.Algebra.IsTamelyRamifiedWRT (X.presheaf.stalk ξ) (Y.residueField y) :=
  Iff.rfl

variable {f}

/-- A cover unramified over `X` in codimension one is tamely ramified over `X` in codimension
one. -/
theorem IsUnramifiedInCodimOne.isTamelyRamifiedInCodimOne (hf : f.IsUnramifiedInCodimOne) :
    f.IsTamelyRamifiedInCodimOne := fun ξ hξ y h ↦
  letI := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
    (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  (hf ξ hξ y h).isTamelyRamifiedWRT

/-- If the local rings of `X` at the codimension-one points outside `U` are regular, so discrete
valuation rings, then an open immersion into `U`, for instance the trivial cover `𝟙 U`, is
unramified over `X` in codimension one: each residue field `κ(y)` is the fraction field `K_ξ`. -/
theorem isUnramifiedInCodimOne_of_isOpenImmersion [IsOpenImmersion f]
    (hX : ∀ ξ : CodimensionOnePoint X, (ξ : X) ∉ U → IsRegularLocalRing (X.presheaf.stalk ξ)) :
    f.IsUnramifiedInCodimOne := by
  intro ξ hξ y h
  have := hX ξ hξ
  have hne : (f ≫ U.ι) y ≠ ξ := fun he ↦ hξ (he ▸ (f y).2)
  -- The residue field at the image of `y` is the fraction field of `𝒪_{X,ξ}`.
  let := (X.presheaf.stalkSpecializes h ≫ X.residue _).hom.toAlgebra
  have := Scheme.isFractionRing_residueField_of_specializes h hne
  -- An open immersion induces an isomorphism of residue fields.
  let := (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫
    (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  have : IsFractionRing (X.presheaf.stalk ξ) (Y.residueField y) :=
    IsLocalization.isLocalization_of_algEquiv _ (AlgEquiv.ofRingEquiv
      (f := (asIso ((f ≫ U.ι).residueFieldMap y)).commRingCatIsoToRingEquiv) fun _ ↦ rfl)
  exact TauCeti.Algebra.isUnramifiedWRT_of_isFractionRing _ _

variable {X' : Scheme.{u}} (g : X' ⟶ X)

/-- The residue field map of `g` and the stalk maps are compatible with the specializations
`x ⤳ g ξ'` and `x' ⤳ ξ'`, after identifying the residue fields at `x = g x'`. -/
private lemma stalkSpecializes_residue_residueFieldCongr_residueFieldMap {X X' : Scheme.{u}}
    (g : X' ⟶ X) {x : X} {x' ξ' : X'} (hx : x = g x') (h : x ⤳ g ξ') (h' : x' ⤳ ξ') :
    X.presheaf.stalkSpecializes h ≫ X.residue x ≫ (X.residueFieldCongr hx).hom ≫
        g.residueFieldMap x' =
      g.stalkMap ξ' ≫ X'.presheaf.stalkSpecializes h' ≫ X'.residue x' := by
  subst hx
  simp [Scheme.residue_residueFieldMap, ← Scheme.Hom.stalkSpecializes_stalkMap_assoc]

/-- The fibre square of a base change commutes. -/
private lemma fst_comp_comp_eq {X' : Scheme.{u}} (g : X' ⟶ X) :
    pullback.fst f (g ∣_ U) ≫ f ≫ U.ι = pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι ≫ g := by
  rw [pullback.condition_assoc, morphismRestrict_ι]

/-- The fibre square of a base change commutes on points. -/
private lemma fst_apply_eq_snd_apply {X' : Scheme.{u}} {g : X' ⟶ X}
    (y' : (pullback f (g ∣_ U) : Scheme.{u})) :
    (f ≫ U.ι) (pullback.fst f (g ∣_ U) y') = g ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y') := by
  exact congr($(fst_comp_comp_eq (f := f) g) y')

/-- The two ways around the residue fields of the fibre square of a base change agree. -/
private lemma residueFieldMap_fst_comp_eq {X' : Scheme.{u}} {g : X' ⟶ X}
    {y' : (pullback f (g ∣_ U) : Scheme.{u})}
    (hx : (f ≫ U.ι) (pullback.fst f (g ∣_ U) y') =
      g ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y')) :
    (f ≫ U.ι).residueFieldMap (pullback.fst f (g ∣_ U) y') ≫
        (pullback.fst f (g ∣_ U)).residueFieldMap y' =
      ((X.residueFieldCongr hx).hom ≫ g.residueFieldMap _) ≫
        (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y' := by
  rw [← Scheme.residueFieldMap_comp, Category.assoc, ← Scheme.residueFieldMap_comp,
    Scheme.Hom.residueFieldMap_congr (fst_comp_comp_eq (f := f) g)]
  -- The two sides differ only by associativity of composition, which holds definitionally.
  rfl

/-- Let `y'` be a point of the base change `Y ×_U g⁻¹ U`, over `y ∈ Y` and `x' ∈ X'`, and let
`ψ : κ(y) → κ(y')` be the residue field map of the first projection, an algebra map over `κ(x)`.
Then the induced `κ(x')`-algebra map `κ(x') ⊗[κ(x)] κ(y) → κ(y')` is surjective, where `κ(y')` is a
`κ(x')`-algebra through the residue field map of the second projection. -/
private lemma surjective_liftEquiv_residueFieldMap [FormallyUnramified f] [LocallyOfFiniteType f]
    {g : X' ⟶ X} (y' : (pullback f (g ∣_ U) : Scheme.{u}))
    [Algebra (X.residueField ((f ≫ U.ι) (pullback.fst f (g ∣_ U) y')))
      (Y.residueField (pullback.fst f (g ∣_ U) y'))]
    [Algebra (X.residueField ((f ≫ U.ι) (pullback.fst f (g ∣_ U) y')))
      (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'))]
    [Algebra (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'))
      ((pullback f (g ∣_ U)).residueField y')]
    [Algebra (X.residueField ((f ≫ U.ι) (pullback.fst f (g ∣_ U) y')))
      ((pullback f (g ∣_ U)).residueField y')]
    [IsScalarTower (X.residueField ((f ≫ U.ι) (pullback.fst f (g ∣_ U) y')))
      (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'))
      ((pullback f (g ∣_ U)).residueField y')]
    (ψ : Y.residueField (pullback.fst f (g ∣_ U) y') →ₐ[X.residueField
      ((f ≫ U.ι) (pullback.fst f (g ∣_ U) y'))] (pullback f (g ∣_ U)).residueField y')
    (hψ : ∀ l, ψ l = (pullback.fst f (g ∣_ U)).residueFieldMap y' l)
    (hK' : ∀ k, algebraMap (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'))
      ((pullback f (g ∣_ U)).residueField y') k =
        (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y' k) :
    Function.Surjective (AlgHom.liftEquiv _
      (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y')) _ _ ψ) := by
  set R := (AlgHom.liftEquiv _
    (X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y')) _ _ ψ).range
  have h₁ (l : Y.residueField (pullback.fst f (g ∣_ U) y')) :
      (pullback.fst f (g ∣_ U)).residueFieldMap y' l ∈ R :=
    (AlgHom.mem_range _).mpr ⟨1 ⊗ₜ l, by rw [AlgHom.liftEquiv_tmul, one_smul, hψ]⟩
  have h₂ (k : (g ⁻¹ᵁ U).toScheme.residueField (pullback.snd f (g ∣_ U) y')) :
      (pullback.snd f (g ∣_ U)).residueFieldMap y' k ∈ R := by
    obtain ⟨k, rfl⟩ : ∃ k₀ : X'.residueField ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'),
        (g ⁻¹ᵁ U).ι.residueFieldMap _ k₀ = k :=
      (ConcreteCategory.bijective_of_isIso ((g ⁻¹ᵁ U).ι.residueFieldMap _)).2 k
    have hk : (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y' k =
        (pullback.snd f (g ∣_ U)).residueFieldMap y' ((g ⁻¹ᵁ U).ι.residueFieldMap _ k) := by
      rw [Scheme.residueFieldMap_comp]
      -- The point `(snd ≫ ι) y'` is `ι (snd y')` by definition, but `rw` cannot see it.
      rfl
    refine (AlgHom.mem_range _).mpr ⟨k ⊗ₜ 1, ?_⟩
    exact (AlgHom.liftEquiv_tmul _ _ _).trans <| ((congrArg (k • ·) (map_one ψ)).trans
      (Algebra.algebraMap_eq_smul_one k).symm).trans ((hK' k).trans hk)
  have hle := (Subring.closure_le (t := R.toSubring)).mpr
    (Set.union_subset (Set.range_subset_iff.mpr h₁) (Set.range_subset_iff.mpr h₂))
  rw [Scheme.Pullback.closure_range_residueFieldMap_eq_top y'
    (RingHom.Finite.to_isIntegral (Scheme.Hom.finite_residueField f _))] at hle
  exact fun z ↦ (AlgHom.mem_range _).mp (hle (Subring.mem_top z))

/-- **Base change of covers unramified in codimension one.** Let `f : Y ⟶ U` be unramified over
`X` in codimension one, formally unramified and locally of finite type (for instance finite
étale), and let `g : X' ⟶ X` map each codimension-one point `ξ'` of `X'` outside `g⁻¹ U` to a
codimension-one point of `X`, with `𝒪_{X,g ξ'}` and `𝒪_{X',ξ'}` regular, so discrete valuation
rings. Then the base change `Y ×_U g⁻¹ U ⟶ g⁻¹ U` is unramified over `X'` in codimension one. -/
@[stacks 0EYD "unramified case"]
theorem IsUnramifiedInCodimOne.baseChange [FormallyUnramified f] [LocallyOfFiniteType f]
    (hf : f.IsUnramifiedInCodimOne)
    (hg : ∀ ξ' : CodimensionOnePoint X', (ξ' : X') ∉ g ⁻¹ᵁ U → Order.coheight (g ξ') = 1)
    (hX : ∀ ξ' : CodimensionOnePoint X', (ξ' : X') ∉ g ⁻¹ᵁ U →
      IsRegularLocalRing (X.presheaf.stalk (g ξ')))
    (hX' : ∀ ξ' : CodimensionOnePoint X', (ξ' : X') ∉ g ⁻¹ᵁ U →
      IsRegularLocalRing (X'.presheaf.stalk ξ')) :
    (pullback.snd f (g ∣_ U)).IsUnramifiedInCodimOne := by
  -- Let `y'` lie over `y ∈ Y`, with images `x ∈ X` and `x' ∈ X'`, and `x' ⤳ ξ'`. With
  -- `A = 𝒪_{X,g ξ'}`, `K = κ(x)`, `L = κ(y)` and `A' = 𝒪_{X',ξ'}`, `K' = κ(x')`, `L' = κ(y')`,
  -- the field `L` is unramified with respect to `A` by assumption, and `L'` is a quotient of
  -- `K' ⊗[K] L`, so `IsUnramifiedWRT.baseChange` applies.
  intro ξ' hξ' y' h'
  let ξ : CodimensionOnePoint X := ⟨g ξ', hg ξ' hξ'⟩
  set y := pullback.fst f (g ∣_ U) y'
  set x' := (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι) y'
  have hx : (f ≫ U.ι) y = g x' := fst_apply_eq_snd_apply y'
  have h : (f ≫ U.ι) y ⤳ ξ := hx ▸ h'.map g.continuous
  have := hX ξ' hξ'
  have := hX' ξ' hξ'
  have := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ
  have := CodimensionOnePoint.isDiscreteValuationRing_stalk ξ'
  set K := X.residueField ((f ≫ U.ι) y)
  set L := Y.residueField y
  set K' := X'.residueField x'
  set L' := (pullback f (g ∣_ U)).residueField y'
  -- The fields `K ⊆ L` over `A`, with the algebra structure of `hfy`.
  let : Algebra (X.presheaf.stalk ξ) K :=
    (X.presheaf.stalkSpecializes h ≫ X.residue _).hom.toAlgebra
  let : Algebra K L := ((f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  let : Algebra (X.presheaf.stalk ξ) L :=
    (X.presheaf.stalkSpecializes h ≫ X.residue _ ≫ (f ≫ U.ι).residueFieldMap y).hom.toAlgebra
  have : IsScalarTower (X.presheaf.stalk ξ) K L := .of_algebraMap_eq fun _ ↦ rfl
  have := Scheme.isFractionRing_residueField_of_specializes h
    (fun e ↦ hξ' (show (ξ : X) ∈ U from e ▸ (f y).2) : (f ≫ U.ι) y ≠ ξ)
  have : FormallyUnramified (f ≫ U.ι) := MorphismProperty.comp_mem _ _ _ ‹_› inferInstance
  -- The fields `K' ⊆ L'` over `A'`, with the algebra structure of the conclusion.
  let : Algebra (X'.presheaf.stalk ξ') K' :=
    (X'.presheaf.stalkSpecializes h' ≫ X'.residue _).hom.toAlgebra
  let : Algebra K' L' :=
    ((pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y').hom.toAlgebra
  let : Algebra (X'.presheaf.stalk ξ') L' := (X'.presheaf.stalkSpecializes h' ≫ X'.residue _ ≫
    (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y').hom.toAlgebra
  have : IsScalarTower (X'.presheaf.stalk ξ') K' L' := .of_algebraMap_eq fun _ ↦ rfl
  have := Scheme.isFractionRing_residueField_of_specializes h'
    (fun e ↦ hξ' (e ▸ (pullback.snd f (g ∣_ U) y').2) : x' ≠ ξ')
  -- The maps `A ⟶ A'` and `K ⟶ K'` induced by `g`, and their compatibility.
  let : Algebra (X.presheaf.stalk ξ) (X'.presheaf.stalk ξ') := (g.stalkMap ξ').hom.toAlgebra
  let : Algebra (X.presheaf.stalk ξ) K' :=
    (g.stalkMap ξ' ≫ X'.presheaf.stalkSpecializes h' ≫ X'.residue _).hom.toAlgebra
  let : Algebra K K' := ((X.residueFieldCongr hx).hom ≫ g.residueFieldMap x').hom.toAlgebra
  have : IsScalarTower (X.presheaf.stalk ξ) (X'.presheaf.stalk ξ') K' :=
    .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (X.presheaf.stalk ξ) K K' :=
    .of_algebraMap_eq' <| congrArg CommRingCat.Hom.hom <| Eq.symm <|
      stalkSpecializes_residue_residueFieldCongr_residueFieldMap g hx h h'
  -- The map `K' ⊗[K] L ⟶ L'` given by the two projections of the fibre product.
  let : Algebra K L' := (((X.residueFieldCongr hx).hom ≫ g.residueFieldMap x') ≫
    (pullback.snd f (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι).residueFieldMap y').hom.toAlgebra
  have : IsScalarTower K K' L' := .of_algebraMap_eq fun _ ↦ rfl
  let ψ : L →ₐ[K] L' :=
    { ((pullback.fst f (g ∣_ U)).residueFieldMap y').hom with
      commutes' := fun k ↦ ConcreteCategory.congr_hom (residueFieldMap_fst_comp_eq hx) k }
  -- It is surjective: its range contains the images of `κ(y)` and of `κ(x')`.
  have hφ : Function.Surjective (AlgHom.liftEquiv _ K' _ _ ψ) :=
    surjective_liftEquiv_residueFieldMap y' ψ (fun _ ↦ rfl) fun _ ↦ rfl
  exact (hf ξ hξ' y h).baseChange _ hφ

end AlgebraicGeometry.Scheme.Hom
