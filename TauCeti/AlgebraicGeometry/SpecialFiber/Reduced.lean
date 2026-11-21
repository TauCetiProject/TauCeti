/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.SpecialFiber.Divisor
public import TauCeti.AlgebraicGeometry.SpecialFiber.Subscheme
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Reduced
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme

/-!
# Reduced special fibres and component multiplicities

For any scheme `X` over a local ring `R`, the **reduced special fibre** `X_{s,red}`
(`TauCeti.reducedSpecialFiber`) is the reduced induced closed subscheme on the closed subset
`toBase ⁻¹' {closedPoint R}` of `X`. Its closed immersion into `X` factors uniquely through a
closed immersion `TauCeti.reducedSpecialFiberToSpecialFiber` into the scheme-theoretic special
fibre `X_s`, which is an isomorphism if and only if `X_s` is reduced
(`TauCeti.isIso_reducedSpecialFiberToSpecialFiber_iff`), and through which every closed subscheme of
`X` whose ideal sheaf contains `(reducedSpecialFiberι R toBase).ker` — in particular the reduced
closure of every point of the special fibre — factors (`TauCeti.subschemeToReducedSpecialFiber`).

For an integral Noetherian scheme with factorial local rings over a one-dimensional local
base with principal maximal ideal, the special fibre is reduced exactly when every component
has multiplicity one. The generic point must lie outside the special fibre. No flatness,
properness, or residue-field perfection hypothesis is needed for this criterion.

On a regular scheme of dimension at most two, the factoriality hypothesis follows from
regularity. Thus the criterion applies to regular models over discrete valuation rings. It
concerns reducedness over the residue field, not geometric reducedness; the latter additionally
requires control after residue-field extension.

## References

* The Stacks Project, Section 55.9 (Tag 0C5Y), the special fibre of a regular model.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

section ReducedSpecialFiber

variable (R : Type u) [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- The **reduced special fibre** `X_{s,red}` of a scheme `X` over a local ring `R`: the reduced
induced closed subscheme on the preimage of the closed point of `Spec R`, realized as the closed
subscheme cut out by `(specialFiberι R toBase).ker.radical`. -/
@[expose]
noncomputable def reducedSpecialFiber : Scheme.{u} :=
  (specialFiberι R toBase).ker.radical.subscheme

/-- The reduced special fibre `X_{s,red}` is a reduced scheme. -/
instance isReduced_reducedSpecialFiber : IsReduced (reducedSpecialFiber R toBase) := by
  rw [reducedSpecialFiber, ← Scheme.IdealSheafData.vanishingIdeal_support]
  infer_instance

/-- The canonical closed immersion `X_{s,red} ⟶ X` of the reduced special fibre into the total
space. -/
noncomputable def reducedSpecialFiberι : reducedSpecialFiber R toBase ⟶ X :=
  (specialFiberι R toBase).ker.radical.subschemeι

/-- The inclusion `X_{s,red} ⟶ X` is `(specialFiberι R toBase).ker.radical.subschemeι`. -/
lemma reducedSpecialFiberι_eq_subschemeι :
    reducedSpecialFiberι R toBase = (specialFiberι R toBase).ker.radical.subschemeι := by
  unfold reducedSpecialFiberι
  rfl

/-- The canonical inclusion `X_{s,red} ⟶ X` is a closed immersion. -/
instance isClosedImmersion_reducedSpecialFiberι :
    IsClosedImmersion (reducedSpecialFiberι R toBase) :=
  inferInstanceAs (IsClosedImmersion (specialFiberι R toBase).ker.radical.subschemeι)

/-- As a set, the image of the reduced special fibre in `X` is the preimage of the closed point. -/
@[simp]
theorem range_reducedSpecialFiberι :
    Set.range (reducedSpecialFiberι R toBase) = toBase ⁻¹' {closedPoint R} := by
  have := isClosedImmersion_specialFiberι R toBase
  refine (Scheme.IdealSheafData.range_subschemeι (specialFiberι R toBase).ker.radical).trans ?_
  rw [Scheme.IdealSheafData.support_radical, Scheme.Hom.support_ker, range_specialFiberι,
    IsClosed.closure_eq]
  exact (isClosed_singleton_closedPoint R).preimage toBase.continuous

/-- The ideal sheaf of the reduced special fibre equals `(specialFiberι R toBase).ker.radical`. -/
lemma ker_reducedSpecialFiberι_eq_radical :
    (reducedSpecialFiberι R toBase).ker = (specialFiberι R toBase).ker.radical := by
  unfold reducedSpecialFiberι
  exact Scheme.IdealSheafData.ker_subschemeι (specialFiberι R toBase).ker.radical

/-- The ideal sheaf of the reduced special fibre is `(specialFiberι R toBase).ker.radical`, which
equals the vanishing ideal of the preimage of the closed point. -/
theorem ker_reducedSpecialFiberι :
    (reducedSpecialFiberι R toBase).ker =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨toBase ⁻¹' {closedPoint R},
          (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩ := by
  have := isClosedImmersion_specialFiberι R toBase
  rw [ker_reducedSpecialFiberι_eq_radical, ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1; ext1
  refine (Scheme.Hom.support_ker (specialFiberι R toBase)).trans ?_
  rw [range_specialFiberι, IsClosed.closure_eq]
  · rfl
  · exact (isClosed_singleton_closedPoint R).preimage toBase.continuous

variable {R toBase} in
/-- A closed subset of `X` lies in the special fibre if and only if its vanishing ideal contains
the ideal sheaf of the reduced special fibre. -/
theorem ker_reducedSpecialFiberι_le_vanishingIdeal_iff {Z : TopologicalSpace.Closeds X} :
    (reducedSpecialFiberι R toBase).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z ↔
      (Z : Set X) ⊆ toBase ⁻¹' {closedPoint R} := by
  rw [ker_reducedSpecialFiberι, ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal,
    ← SetLike.coe_subset_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl

/-- The ideal sheaf of the scheme-theoretic special fibre is contained in that of the reduced
special fibre. -/
theorem ker_specialFiberι_le_ker_reducedSpecialFiberι :
    (specialFiberι R toBase).ker ≤ (reducedSpecialFiberι R toBase).ker :=
  (specialFiberι R toBase).ker.le_radical.trans_eq
    (ker_reducedSpecialFiberι_eq_radical R toBase).symm

/-- The canonical closed immersion `X_{s,red} ⟶ X_s` of the reduced special fibre into the
scheme-theoretic special fibre. -/
noncomputable def reducedSpecialFiberToSpecialFiber :
    reducedSpecialFiber R toBase ⟶ (specialFiber R toBase).left :=
  subschemeToSpecialFiber (specialFiberι R toBase).ker.le_radical

/-- `reducedSpecialFiberToSpecialFiber` is `subschemeToSpecialFiber` applied to `le_radical`. -/
lemma reducedSpecialFiberToSpecialFiber_eq_subschemeToSpecialFiber :
    reducedSpecialFiberToSpecialFiber R toBase =
      subschemeToSpecialFiber (specialFiberι R toBase).ker.le_radical := by
  unfold reducedSpecialFiberToSpecialFiber
  rfl

/-- The inclusion of the reduced special fibre into the total space factors through the
scheme-theoretic special fibre. -/
@[reassoc (attr := simp)]
lemma reducedSpecialFiberToSpecialFiber_specialFiberι :
    reducedSpecialFiberToSpecialFiber R toBase ≫ specialFiberι R toBase =
      reducedSpecialFiberι R toBase :=
  subschemeToSpecialFiber_specialFiberι _

/-- The canonical morphism `X_{s,red} ⟶ X_s` is a closed immersion. -/
instance isClosedImmersion_reducedSpecialFiberToSpecialFiber :
    IsClosedImmersion (reducedSpecialFiberToSpecialFiber R toBase) :=
  isClosedImmersion_subschemeToSpecialFiber _

/-- The reduced special fibre is a scheme over the residue field of `R`, through the special
fibre. -/
noncomputable instance reducedSpecialFiberOverResidueField :
    (reducedSpecialFiber R toBase).Over (Spec (.of (ResidueField R))) :=
  ⟨reducedSpecialFiberToSpecialFiber R toBase ≫ (specialFiber R toBase).hom⟩

/-- The structure morphism of `X_{s,red}` over the residue field factors through `X_{s,red} ⟶ X_s`.
-/
lemma reducedSpecialFiber_over :
    reducedSpecialFiber R toBase ↘ Spec (.of (ResidueField R)) =
      reducedSpecialFiberToSpecialFiber R toBase ≫ (specialFiber R toBase).hom :=
  rfl

/-- When `X` is proper over `Spec R`, its reduced special fibre is proper over the residue field. -/
instance isProper_reducedSpecialFiber [IsProper toBase] :
    IsProper (reducedSpecialFiber R toBase ↘ Spec (.of (ResidueField R))) := by
  rw [reducedSpecialFiber_over]
  exact isProper_subschemeOverResidueField (specialFiberι R toBase).ker.le_radical

/-- The canonical closed immersion `X_{s,red} ⟶ X_s` is an isomorphism if and only if the
scheme-theoretic special fibre `X_s` is reduced. -/
theorem isIso_reducedSpecialFiberToSpecialFiber_iff :
    IsIso (reducedSpecialFiberToSpecialFiber R toBase) ↔
      IsReduced (specialFiber R toBase).left := by
  refine ⟨fun _ ↦ (ObjectProperty.prop_iff_of_iso (IsReduced ·)
    (asIso (reducedSpecialFiberToSpecialFiber R toBase))).mp inferInstance, fun _ ↦ ?_⟩
  have : Surjective (reducedSpecialFiberToSpecialFiber R toBase) := ⟨fun y ↦ ?_⟩
  · exact isIso_of_isClosedImmersion_of_surjective (reducedSpecialFiberToSpecialFiber R toBase)
  · have hy : specialFiberι R toBase y ∈ Set.range (reducedSpecialFiberι R toBase) := by
      rw [range_reducedSpecialFiberι, ← range_specialFiberι]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    have := isClosedImmersion_specialFiberι R toBase
    refine ⟨x, (specialFiberι R toBase).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, reducedSpecialFiberToSpecialFiber_specialFiberι, hx]

section Subscheme

variable {R toBase}

/-- A closed subscheme of `X` whose ideal sheaf contains `(reducedSpecialFiberι R toBase).ker`
embeds as a closed subscheme of the reduced special fibre `X_{s,red}`. -/
noncomputable def subschemeToReducedSpecialFiber {I : X.IdealSheafData}
    (hI : (reducedSpecialFiberι R toBase).ker ≤ I) :
    I.subscheme ⟶ reducedSpecialFiber R toBase :=
  Scheme.IdealSheafData.inclusion
    ((ker_reducedSpecialFiberι_eq_radical R toBase).symm.trans_le hI)

/-- `subschemeToReducedSpecialFiber` is `Scheme.IdealSheafData.inclusion`. -/
lemma subschemeToReducedSpecialFiber_eq_inclusion {I : X.IdealSheafData}
    (hI : (reducedSpecialFiberι R toBase).ker ≤ I) :
    subschemeToReducedSpecialFiber hI =
      Scheme.IdealSheafData.inclusion
        ((ker_reducedSpecialFiberι_eq_radical R toBase).symm.trans_le hI) := by
  unfold subschemeToReducedSpecialFiber
  rfl

/-- The inclusion of a closed subscheme contained in the reduced special fibre factors through
`X_{s,red}`. -/
@[reassoc (attr := simp)]
lemma subschemeToReducedSpecialFiber_reducedSpecialFiberι {I : X.IdealSheafData}
    (hI : (reducedSpecialFiberι R toBase).ker ≤ I) :
    subschemeToReducedSpecialFiber hI ≫ reducedSpecialFiberι R toBase = I.subschemeι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- A closed subscheme of `X` contained in the reduced special fibre is a closed subscheme of
`X_{s,red}`. -/
instance isClosedImmersion_subschemeToReducedSpecialFiber {I : X.IdealSheafData}
    (hI : (reducedSpecialFiberι R toBase).ker ≤ I) :
    IsClosedImmersion (subschemeToReducedSpecialFiber hI) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.inclusion _))

/-- Composing the inclusion into `X_{s,red}` with `X_{s,red} ⟶ X_s` recovers the inclusion into
`X_s`. -/
@[reassoc (attr := simp)]
lemma subschemeToReducedSpecialFiber_reducedSpecialFiberToSpecialFiber {I : X.IdealSheafData}
    (hI : (reducedSpecialFiberι R toBase).ker ≤ I) :
    subschemeToReducedSpecialFiber hI ≫ reducedSpecialFiberToSpecialFiber R toBase =
      subschemeToSpecialFiber
        ((ker_specialFiberι_le_ker_reducedSpecialFiberι R toBase).trans hI) := by
  have := isClosedImmersion_specialFiberι R toBase
  rw [← cancel_mono (specialFiberι R toBase), Category.assoc,
    reducedSpecialFiberToSpecialFiber_specialFiberι,
    subschemeToReducedSpecialFiber_reducedSpecialFiberι, subschemeToSpecialFiber_specialFiberι]

end Subscheme

end ReducedSpecialFiber

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The reduced closure of a point of the special fibre has ideal sheaf containing
`(reducedSpecialFiberι R toBase).ker`. -/
theorem ker_reducedSpecialFiberι_le_vanishingIdeal_closure_singleton
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))
    {x : X} (hx : toBase x = closedPoint R) :
    (reducedSpecialFiberι R toBase).ker ≤
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩ :=
  (ker_reducedSpecialFiberι_eq_radical R toBase).trans_le
    (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton hx)

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]

local instance : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩

/-- The special fibre of a locally factorial integral Noetherian scheme is reduced exactly
when all its component multiplicities are one. The maximal ideal of the base is generated by
`π`, and the generic point of the total space lies outside the special fibre. -/
theorem isReduced_specialFiber_iff_specialFiberMultiplicity_eq_one
    [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) :
    IsReduced (specialFiber R toBase).left ↔
      ∀ x : CodimensionOnePoint X, toBase x = closedPoint R →
        toBase.specialFiberMultiplicity π x = 1 := by
  have hπ0 := toBase.ne_zero_of_base_ne_closedPoint hη hπ
  have hπm : π ∈ maximalIdeal R := hπ ▸ Ideal.mem_span_singleton_self π
  have hiso := ObjectProperty.prop_iff_of_iso (IsReduced ·) (specialFiberIsoSubscheme R toBase)
  rw [hπ, Ideal.map_span, Set.image_singleton, RingHom.comp_apply] at hiso
  rw [hiso, Scheme.IdealSheafData.isReduced_subscheme_ofIdealTop_span_singleton_iff_ord_le_one
    (toBase.appTop_ΓSpecIso_inv_ne_zero hη hπm hπ0)]
  constructor
  · intro h x hx
    have hpos := toBase.specialFiberMultiplicity_pos hη hπm hπ0 x hx
    have hcoe := toBase.specialFiberMultiplicity_coe π x
    have hle := h x
    omega
  · intro h x
    have hcoe := toBase.specialFiberMultiplicity_coe π x
    by_cases hx : toBase x = closedPoint R
    · rw [h x hx, Nat.cast_one] at hcoe
      exact hcoe.symm.le
    · rw [toBase.specialFiberMultiplicity_eq_zero_of_ne hη
        (by simpa using hπm) hπ0 x hx] at hcoe
      omega

/-- On a regular integral Noetherian scheme of dimension at most two, the special fibre is
reduced exactly when every component has multiplicity one. -/
theorem isReduced_specialFiber_iff_specialFiberMultiplicity_eq_one_of_isRegular
    [TauCeti.AlgebraicGeometry.IsRegular X] (hX : ∀ x : X, Order.coheight x ≤ 2)
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) :
    IsReduced (specialFiber R toBase).left ↔
      ∀ x : CodimensionOnePoint X, toBase x = closedPoint R →
        toBase.specialFiberMultiplicity π x = 1 := by
  have := fun x ↦ TauCeti.AlgebraicGeometry.IsRegular.uniqueFactorizationMonoid_stalk x (hX x)
  exact toBase.isReduced_specialFiber_iff_specialFiberMultiplicity_eq_one hη hπ

end AlgebraicGeometry.Scheme.Hom
