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
(`TauCeti.isIso_reducedSpecialFiberToSpecialFiber_iff`), and through which the reduced closure of
every point of the special fibre factors
(`AlgebraicGeometry.Scheme.Hom.subschemeToReducedSpecialFiber`).

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
induced closed subscheme on the preimage of the closed point of `Spec R`. -/
noncomputable def reducedSpecialFiber : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨toBase ⁻¹' {closedPoint R},
      (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩).subscheme

/-- The reduced special fibre `X_{s,red}` is a reduced scheme. -/
instance isReduced_reducedSpecialFiber : IsReduced (reducedSpecialFiber R toBase) :=
  inferInstanceAs (IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme)

/-- The canonical closed immersion `X_{s,red} ⟶ X` of the reduced special fibre into the total
space. -/
noncomputable def reducedSpecialFiberι : reducedSpecialFiber R toBase ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨toBase ⁻¹' {closedPoint R},
      (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩).subschemeι

/-- The canonical inclusion `X_{s,red} ⟶ X` is a closed immersion. -/
instance isClosedImmersion_reducedSpecialFiberι :
    IsClosedImmersion (reducedSpecialFiberι R toBase) :=
  inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal _).subschemeι)

/-- As a set, the image of the reduced special fibre in `X` is the preimage of the closed point. -/
@[simp]
theorem range_reducedSpecialFiberι :
    Set.range (reducedSpecialFiberι R toBase) = toBase ⁻¹' {closedPoint R} :=
  (Scheme.IdealSheafData.range_subschemeι _).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The ideal sheaf of the reduced special fibre is the vanishing ideal of the preimage of the
closed point. -/
theorem ker_reducedSpecialFiberι :
    (reducedSpecialFiberι R toBase).ker =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨toBase ⁻¹' {closedPoint R},
          (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩ :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- The ideal sheaf of the scheme-theoretic special fibre is contained in that of the reduced
special fibre. -/
theorem ker_specialFiberι_le_ker_reducedSpecialFiberι :
    (specialFiberι R toBase).ker ≤ (reducedSpecialFiberι R toBase).ker :=
  (ker_specialFiberι_le_vanishingIdeal_iff
    (Z := ⟨toBase ⁻¹' {closedPoint R},
      (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩).mpr
    Set.Subset.rfl).trans_eq (ker_reducedSpecialFiberι R toBase).symm

/-- The canonical closed immersion `X_{s,red} ⟶ X_s` of the reduced special fibre into the
scheme-theoretic special fibre. -/
noncomputable def reducedSpecialFiberToSpecialFiber :
    reducedSpecialFiber R toBase ⟶ (specialFiber R toBase).left :=
  haveI := isClosedImmersion_specialFiberι R toBase
  IsClosedImmersion.lift (specialFiberι R toBase) (reducedSpecialFiberι R toBase)
    (ker_specialFiberι_le_ker_reducedSpecialFiberι R toBase)

/-- The inclusion of the reduced special fibre into the total space factors through the
scheme-theoretic special fibre. -/
@[reassoc (attr := simp)]
lemma reducedSpecialFiberToSpecialFiber_specialFiberι :
    reducedSpecialFiberToSpecialFiber R toBase ≫ specialFiberι R toBase =
      reducedSpecialFiberι R toBase :=
  haveI := isClosedImmersion_specialFiberι R toBase
  IsClosedImmersion.lift_fac _ _ _

/-- The canonical morphism `X_{s,red} ⟶ X_s` is a closed immersion. -/
instance isClosedImmersion_reducedSpecialFiberToSpecialFiber :
    IsClosedImmersion (reducedSpecialFiberToSpecialFiber R toBase) := by
  have := isClosedImmersion_specialFiberι R toBase
  have : IsClosedImmersion
      (reducedSpecialFiberToSpecialFiber R toBase ≫ specialFiberι R toBase) := by
    rw [reducedSpecialFiberToSpecialFiber_specialFiberι]
    infer_instance
  exact .of_comp_isClosedImmersion _ (specialFiberι R toBase)

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
    IsProper (reducedSpecialFiber R toBase ↘ Spec (.of (ResidueField R))) :=
  inferInstanceAs (IsProper (reducedSpecialFiberToSpecialFiber R toBase ≫ pullback.snd toBase _))

/-- The canonical closed immersion `X_{s,red} ⟶ X_s` is an isomorphism if and only if the
scheme-theoretic special fibre `X_s` is reduced. -/
theorem isIso_reducedSpecialFiberToSpecialFiber_iff :
    IsIso (reducedSpecialFiberToSpecialFiber R toBase) ↔
      IsReduced (specialFiber R toBase).left := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact (ObjectProperty.prop_iff_of_iso (IsReduced ·)
      (asIso (reducedSpecialFiberToSpecialFiber R toBase))).mp inferInstance
  · have := isClosedImmersion_specialFiberι R toBase
    have hle : (reducedSpecialFiberι R toBase).ker ≤ (specialFiberι R toBase).ker :=
      (ker_reducedSpecialFiberι R toBase).trans_le <|
        Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset (specialFiberι R toBase)
          (Z := ⟨toBase ⁻¹' {closedPoint R},
            (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩)
          (by rw [range_specialFiberι]; exact Set.Subset.rfl)
    exact IsClosedImmersion.isIso_lift (specialFiberι R toBase) (reducedSpecialFiberι R toBase)
      (le_antisymm (ker_specialFiberι_le_ker_reducedSpecialFiberι R toBase) hle)

variable {R} in
/-- The reduced closure of a point of the special fibre embeds as a closed subscheme of the reduced
special fibre `X_{s,red}`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.subschemeToReducedSpecialFiber {x : X}
    (hx : toBase x = closedPoint R) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subscheme ⟶
      reducedSpecialFiber R toBase :=
  IsClosedImmersion.lift (reducedSpecialFiberι R toBase)
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι <| by
      have hsub : closure ({x} : Set X) ⊆ toBase ⁻¹' {closedPoint R} :=
        closure_minimal (Set.singleton_subset_iff.mpr hx)
          ((isClosed_singleton_closedPoint R).preimage toBase.continuous)
      exact (ker_reducedSpecialFiberι R toBase).trans_le
        (Scheme.IdealSheafData.vanishingIdeal_le_ker_of_range_subset
          (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι
          (Z := ⟨toBase ⁻¹' {closedPoint R},
            (isClosed_singleton_closedPoint R).preimage toBase.continuous⟩)
          (by rw [Scheme.IdealSheafData.range_subschemeι,
                Scheme.IdealSheafData.coe_support_vanishingIdeal]; exact hsub))

variable {R} in
/-- The inclusion of the reduced closure of a point of the special fibre into `X` factors through
the reduced special fibre. -/
@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.Scheme.Hom.subschemeToReducedSpecialFiber_reducedSpecialFiberι
    {x : X} (hx : toBase x = closedPoint R) :
    toBase.subschemeToReducedSpecialFiber hx ≫ reducedSpecialFiberι R toBase =
      (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).subschemeι :=
  IsClosedImmersion.lift_fac _ _ _

variable {R} in
/-- The embedding of the reduced closure of a point of the special fibre into `X_{s,red}` is a
closed immersion. -/
instance _root_.AlgebraicGeometry.Scheme.Hom.isClosedImmersion_subschemeToReducedSpecialFiber
    {x : X} (hx : toBase x = closedPoint R) :
    IsClosedImmersion (toBase.subschemeToReducedSpecialFiber hx) := by
  have : IsClosedImmersion
      (toBase.subschemeToReducedSpecialFiber hx ≫ reducedSpecialFiberι R toBase) := by
    rw [toBase.subschemeToReducedSpecialFiber_reducedSpecialFiberι hx]
    infer_instance
  exact .of_comp_isClosedImmersion _ (reducedSpecialFiberι R toBase)

end ReducedSpecialFiber

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Composing the inclusion into the reduced special fibre with `X_{s,red} ⟶ X_s` recovers the
inclusion into the scheme-theoretic special fibre. -/
@[reassoc (attr := simp)]
lemma subschemeToReducedSpecialFiber_reducedSpecialFiberToSpecialFiber
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))
    {x : X} (hx : toBase x = closedPoint R) :
    toBase.subschemeToReducedSpecialFiber hx ≫ reducedSpecialFiberToSpecialFiber R toBase =
      subschemeToSpecialFiber
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hx) := by
  have := isClosedImmersion_specialFiberι R toBase
  rw [← cancel_mono (specialFiberι R toBase), Category.assoc,
    reducedSpecialFiberToSpecialFiber_specialFiberι,
    toBase.subschemeToReducedSpecialFiber_reducedSpecialFiberι,
    subschemeToSpecialFiber_specialFiberι]

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
