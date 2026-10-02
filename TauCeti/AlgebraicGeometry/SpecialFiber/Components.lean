/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DedekindDomain.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.SpecialFiber.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ZeroLocus

/-!
# Irreducible components and multiplicities of the special fibre

Let `R` be a local ring of Krull dimension at most one (`Ring.DimensionLEOne R`), for instance a
discrete valuation ring, and let `X → Spec R` be a scheme over `R`. The special fibre of `X` is
the fibre over the closed point of `Spec R`. For a nonzero element `π` of the maximal ideal of
`R`, for instance a uniformizer, the special fibre is the zero locus of the pullback of `π` to
`X`: a point of `X` lies over the closed point exactly when `π` vanishes there, because the only
prime of `R` containing `π` is the maximal ideal.

When `X` is integral and locally Noetherian and its generic point lies over the generic point of
`Spec R`, as it does when `X → Spec R` is flat, the results of
`TauCeti.AlgebraicGeometry.Scheme.ZeroLocusComponents` describe the special fibre: its
irreducible components are the closures of the codimension-one points of `X` lying over the closed
point, every point of the special fibre lies on such a component, and, for `X` Noetherian, there
are finitely many components. The divisor of the pullback of `π` is an effective Weil divisor on
`X` supported exactly on these components, so that

`div_X(π) = ∑ᵢ mᵢ [Cᵢ]`, with `mᵢ = ord_{Cᵢ}(π) > 0`

the coefficient of the component `Cᵢ` in the divisor of `π`. When `R` is a discrete valuation
ring and `π` is a uniformizer, this divisor is the special fibre `X_s` and `mᵢ` is the
multiplicity of `Cᵢ` in `X_s`; these multiplicities and the finite component set are the first
invariants of the numerical type of a regular model of a curve over a discrete valuation ring.
For a general nonzero `π` in the maximal ideal the coefficients depend on `π`: replacing `π` by
`π ^ 2` doubles them.

The statements are phrased for an explicit structure morphism `toBase : X ⟶ Spec R` rather than
for a bundled model, so that they apply to the total space `M.total` of any
`TauCeti.Model` through `M.toBase`, whose flatness is an instance. For a discrete valuation
ring the hypothesis `maximalIdeal R ≠ ⊥` is `IsDiscreteValuationRing.not_a_field R`, and the
dimension hypothesis is the instance `Ring.DimensionLEOne.principal_ideal_ring`. The results about
`toBase` are stated in the namespace `AlgebraicGeometry.Scheme.Hom`, so they are available by dot
notation on the structure morphism.

## Main results

* `TauCeti.range_specialFiberι`: the special fibre of a scheme over a local ring is the preimage
  of the closed point;
* `PrimeSpectrum.mem_asIdeal_iff_eq_closedPoint`: in a local ring of dimension at most one, a
  nonzero element of the maximal ideal lies in a prime exactly when that prime is the maximal
  ideal;
* `AlgebraicGeometry.Scheme.Hom.base_eq_closedPoint_iff_mem_zeroLocus` and
  `AlgebraicGeometry.Scheme.Hom.preimage_closedPoint_eq_zeroLocus`: the special fibre is the zero
  locus of the pullback of a nonzero element of the maximal ideal;
* `AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint`: the generic point of an
  irreducible scheme flat over `R` does not lie in the special fibre;
* `AlgebraicGeometry.Scheme.Hom.maximal_base_eq_closedPoint_iff`: the generic points of the
  irreducible components of the special fibre are the codimension-one points of `X` lying in it;
* `AlgebraicGeometry.Scheme.Hom.exists_maximal_base_eq_closedPoint_specializes`: every point of
  the special fibre lies on an irreducible component of it;
* `AlgebraicGeometry.Scheme.Hom.finite_setOf_base_eq_closedPoint`: the special fibre of a
  Noetherian integral scheme has finitely many irreducible components;
* `AlgebraicGeometry.Scheme.Hom.ord_germToFunctionField_appTop_pos_iff`: the order of the
  pullback of `π` at a codimension-one point is positive exactly when the point lies in the special
  fibre;
* `AlgebraicGeometry.Scheme.Hom.mem_support_principalDivisor_appTop`: the divisor of the pullback
  of `π` is supported exactly on the components of the special fibre.

## References

* [The Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C9U), the geometry of
  a regular model, in particular the description of the special fibre as the divisor of a
  uniformizer.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 8.3, on models of curves and the
  multiplicities of the components of their special fibres.
-/

public section

open CategoryTheory AlgebraicGeometry IsLocalRing Order TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- The special fibre of a scheme over a local ring is, as a set, the preimage of the closed
point: the special fibre is isomorphic over `X` to Mathlib's fibre of `toBase` at the closed
point. -/
theorem range_specialFiberι :
    Set.range (specialFiberι R toBase) = toBase ⁻¹' {closedPoint R} :=
  calc Set.range (specialFiberι R toBase)
      = Set.range (specialFiberι R toBase ∘ (specialFiberIsoFiberClosedPoint (.of R) toBase).inv) :=
        ((specialFiberIsoFiberClosedPoint (.of R) toBase).inv.surjective.range_comp _).symm
    _ = Set.range ((specialFiberIsoFiberClosedPoint (.of R) toBase).inv ≫ specialFiberι R toBase) :=
        congrArg Set.range (funext fun x ↦ (Scheme.Hom.comp_apply _ _ x).symm)
    _ = Set.range (toBase.fiberι (closedPoint R)) :=
        congrArg (fun g : toBase.fiber (closedPoint R) ⟶ X ↦ Set.range g)
          (specialFiberIsoFiberClosedPoint_inv_specialFiberι (.of R) toBase)
    _ = toBase ⁻¹' {closedPoint R} := Scheme.Hom.range_fiberι toBase (closedPoint R)

end LocalRing

section DimensionLEOne

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]

/-- In a local ring of Krull dimension at most one, a nonzero element of the maximal ideal lies
in a prime ideal exactly when that prime is the maximal ideal. -/
theorem _root_.PrimeSpectrum.mem_asIdeal_iff_eq_closedPoint (p : PrimeSpectrum R) {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) : π ∈ p.asIdeal ↔ p = closedPoint R := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ hπ⟩
  have hne : p.asIdeal ≠ ⊥ := fun hbot ↦ hπ0 (Ideal.mem_bot.mp (hbot ▸ h))
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (p.isPrime.isMaximal hne))

variable {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))

/-- A point of a scheme over a local ring of dimension at most one lies over the closed point
exactly when the pullback of a nonzero element `π` of the maximal ideal vanishes at it. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.base_eq_closedPoint_iff_mem_zeroLocus {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) (x : X) :
    toBase x = closedPoint R ↔
      x ∈ X.zeroLocus {toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)} := by
  rw [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe,
    ← Scheme.preimage_basicOpen_top, Scheme.Hom.mem_preimage,
    AlgebraicGeometry.basicOpen_eq_of_affine]
  exact ((toBase x).mem_asIdeal_iff_eq_closedPoint hπ hπ0).symm.trans
    ⟨fun h hb ↦ hb h, not_not.mp⟩

/-- The special fibre of a scheme over a local ring of dimension at most one is the zero locus of
the pullback of a nonzero element of the maximal ideal. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_closedPoint_eq_zeroLocus {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    toBase ⁻¹' {closedPoint R} =
      X.zeroLocus {toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)} :=
  Set.ext fun x ↦ toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0 x

section Irreducible

variable [IrreducibleSpace X]

omit [Ring.DimensionLEOne R] in
/-- The generic point of an irreducible scheme flat over a local domain which is not a field does
not lie in the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint [IsDomain R]
    [Flat toBase] (hR : maximalIdeal R ≠ ⊥) : toBase (genericPoint X) ≠ closedPoint R := by
  rw [toBase.genericPoint_eq_of_flat, genericPoint_eq_bot_of_affine]
  intro h
  have h' : (⊥ : Ideal R) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal h
  exact hR h'.symm

/-- If the generic point of an irreducible scheme over a one-dimensional local ring does not lie
in the special fibre, the pullback of a nonzero element of the maximal ideal is a nonzero global
function. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.appTop_ΓSpecIso_inv_ne_zero
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π) ≠ 0 := by
  intro h
  apply hη
  rw [toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0, h, Scheme.zeroLocus_singleton,
    Scheme.basicOpen_zero]
  simp

end Irreducible

variable [IsIntegral X]

/-- The pullback of a nonzero element of the maximal ideal is a nonzero rational function. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.germToFunctionField_appTop_ne_zero
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    X.germToFunctionField ⊤ (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)) ≠ 0 :=
  (map_ne_zero_iff _ (X.germToFunctionField_injective ⊤)).mpr
    (toBase.appTop_ΓSpecIso_inv_ne_zero hη hπ hπ0)

variable [IsLocallyNoetherian X]

/-- **The irreducible components of the special fibre.** For an integral locally Noetherian scheme
over a local ring of dimension at most one which is not a field, whose generic point does not lie
in the special fibre, the generic points of the irreducible components of the special fibre, that
is, its points maximal for the specialization order, are exactly the codimension-one points of `X`
lying in the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.maximal_base_eq_closedPoint_iff
    (hR : maximalIdeal R ≠ ⊥) (hη : toBase (genericPoint X) ≠ closedPoint R) {x : X} :
    Maximal (fun y ↦ toBase y = closedPoint R) x ↔
      toBase x = closedPoint R ∧ coheight x = 1 := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  simp only [toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0]
  exact Scheme.maximal_mem_zeroLocus_iff (toBase.appTop_ΓSpecIso_inv_ne_zero hη hπ hπ0)

omit [IsIntegral X] in
/-- Every point of the special fibre of a locally Noetherian scheme over a local ring of dimension
at most one which is not a field lies on an irreducible component of the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.exists_maximal_base_eq_closedPoint_specializes
    (hR : maximalIdeal R ≠ ⊥) {x : X} (hx : toBase x = closedPoint R) :
    ∃ y, Maximal (fun y ↦ toBase y = closedPoint R) y ∧ y ⤳ x := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  simp only [toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0] at hx ⊢
  exact Scheme.exists_maximal_mem_zeroLocus_specializes hx

/-- At a codimension-one point of `X`, the order of vanishing of the pullback of a nonzero
element `π` of the maximal ideal is positive exactly when the point lies in the special fibre.
This order is the coefficient of the corresponding component of the special fibre in the divisor
of the pullback of `π`; when `R` is a discrete valuation ring and `π` is a uniformizer, it is the
multiplicity of that component in the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ord_germToFunctionField_appTop_pos_iff
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    {x : X} (hx : coheight x = 1) :
    0 < X.ord (X.germToFunctionField ⊤ (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π))) x ↔
      toBase x = closedPoint R := by
  rw [Scheme.ord_germToFunctionField_pos_iff (toBase.appTop_ΓSpecIso_inv_ne_zero hη hπ hπ0)
    trivial hx, toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0]

end DimensionLEOne

section Noetherian

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]

/-- The special fibre of a Noetherian integral scheme over a local ring of dimension at most one
which is not a field, whose generic point does not lie in the special fibre, has finitely many
irreducible components: only finitely many codimension-one points of `X` lie in it. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.finite_setOf_base_eq_closedPoint
    (hR : maximalIdeal R ≠ ⊥) (hη : toBase (genericPoint X) ≠ closedPoint R) :
    {x : CodimensionOnePoint X | toBase x = closedPoint R}.Finite := by
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hR
  simp only [toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0]
  exact SchemeWeilDivisor.finite_setOf_mem_zeroLocus (toBase.appTop_ΓSpecIso_inv_ne_zero hη hπ hπ0)

/-- **The divisor of a uniformizer is supported on the special fibre.** The principal divisor of
the pullback of a nonzero element `π` of the maximal ideal is supported exactly on the
codimension-one points of the special fibre, the generic points of its irreducible components.
Together with `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.isEffective_principalDivisor_ofMul_mk0`
this is the decomposition `div_X(π) = ∑ᵢ mᵢ [Cᵢ]` with positive coefficients `mᵢ`; when `R` is a
discrete valuation ring and `π` is a uniformizer, these are the multiplicities of the components
of the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.mem_support_principalDivisor_appTop
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0)
    (x : CodimensionOnePoint X) :
    x ∈ ((WeilDivisor.OrderSystem.ofScheme X).principalDivisor (Additive.ofMul
        (Units.mk0 _ (toBase.germToFunctionField_appTop_ne_zero hη hπ hπ0)))).support ↔
      toBase x = closedPoint R := by
  rw [SchemeWeilDivisor.mem_support_principalDivisor_ofMul_mk0,
    toBase.base_eq_closedPoint_iff_mem_zeroLocus hπ hπ0]

end Noetherian

end TauCeti
