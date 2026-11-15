/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.DedekindDomain.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.Basic
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

* `TauCeti.range_specialFiberι` and `TauCeti.specialFiberHomeomorph`: the special fibre of a
  scheme over a local ring is homeomorphic to the preimage of the closed point, and is nonempty
  whenever `X` is nonempty and universally closed over `R`
  (`TauCeti.nonempty_specialFiber`, `TauCeti.connectedSpace_specialFiber_iff_isPreconnected`);
* `TauCeti.ker_specialFiberι_le_vanishingIdeal_iff`: a closed subset lies in the special fibre
  exactly when its reduced induced closed subscheme is a closed subscheme of the special fibre, as
  for the closure of a point of the special fibre
  (`AlgebraicGeometry.Scheme.Hom.ker_specialFiberι_le_vanishingIdeal_closure_singleton`);
* `AlgebraicGeometry.Scheme.Hom.maximalIdeal_ne_bot_of_base_ne_closedPoint`: a local ring over
  which some point of a scheme lies away from the closed point is not a field;
* `AlgebraicGeometry.Scheme.Hom.ne_zero_of_base_ne_closedPoint`: under the same hypothesis, a
  generator of the maximal ideal is nonzero;
* `PrimeSpectrum.mem_asIdeal_iff_eq_closedPoint`: in a local ring of dimension at most one, a
  nonzero element of the maximal ideal lies in a prime exactly when that prime is the maximal
  ideal;
* `AlgebraicGeometry.Scheme.Hom.base_eq_closedPoint_iff_mem_zeroLocus` and
  `AlgebraicGeometry.Scheme.Hom.preimage_closedPoint_eq_zeroLocus`: the special fibre is the zero
  locus of the pullback of a nonzero element of the maximal ideal;
* `AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint`,
  `AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint_of_not_isNilpotent`, and
  `AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint_of_isSMulRegular`: the generic
  point of an irreducible scheme flat over `R` does not lie in the special fibre;
* `AlgebraicGeometry.Scheme.Hom.maximal_base_eq_closedPoint_iff`: the generic points of the
  irreducible components of the special fibre are the codimension-one points of `X` lying in it;
* `AlgebraicGeometry.Scheme.Hom.exists_maximal_base_eq_closedPoint_specializes`: every point of
  the special fibre lies on an irreducible component of it;
* `AlgebraicGeometry.Scheme.Hom.biUnion_closure_eq_preimage_closedPoint` and
  `AlgebraicGeometry.Scheme.Hom.nonempty_setOf_base_eq_closedPoint`: the special fibre is the
  union of its irreducible components, and has at least one component when `X` is universally
  closed over `R`;
* `AlgebraicGeometry.Scheme.Hom.finite_setOf_base_eq_closedPoint`: the special fibre of a
  Noetherian integral scheme has finitely many irreducible components;
* `AlgebraicGeometry.Scheme.Hom.ord_germToFunctionField_appTop_pos_iff`: the order of the
  pullback of `π` at a codimension-one point is positive exactly when the point lies in the special
  fibre;
* `AlgebraicGeometry.Scheme.Hom.mem_support_principalDivisor_appTop`: the divisor of the pullback
  of `π` is supported exactly on the components of the special fibre.

## References

* [The Stacks Project, Section 55.9 (Tag 0C5Y)](https://stacks.math.columbia.edu/tag/0C5Y), the
  geometry of a regular model, in particular the description of the special fibre as the divisor of
  a uniformizer.
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

variable {R toBase} in
/-- A closed subset of `X` lies in the special fibre exactly when its vanishing ideal, the ideal
sheaf of its reduced induced closed subscheme, contains the ideal sheaf of the special fibre. -/
theorem ker_specialFiberι_le_vanishingIdeal_iff {Z : TopologicalSpace.Closeds X} :
    (specialFiberι R toBase).ker ≤ Scheme.IdealSheafData.vanishingIdeal Z ↔
      (Z : Set X) ⊆ toBase ⁻¹' {closedPoint R} := by
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, ← SetLike.coe_subset_coe,
    Scheme.Hom.support_ker, range_specialFiberι, IsClosed.closure_eq]
  exact (isClosed_singleton_closedPoint R).preimage toBase.continuous

variable {R} in
/-- The closure of a point of the special fibre, with its reduced structure, is a closed subscheme
of the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ker_specialFiberι_le_vanishingIdeal_closure_singleton
    {x : X} (hx : toBase x = closedPoint R) :
    (specialFiberι R toBase).ker ≤
      Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩ :=
  ker_specialFiberι_le_vanishingIdeal_iff.mpr <| closure_minimal (Set.singleton_subset_iff.mpr hx)
    ((isClosed_singleton_closedPoint R).preimage toBase.continuous)

variable {R} in
/-- If some point of a scheme over a local ring does not lie over the closed point, then the local
ring is not a field: over a field every point maps to the closed point. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.maximalIdeal_ne_bot_of_base_ne_closedPoint {x : X}
    (hx : toBase x ≠ closedPoint R) : maximalIdeal R ≠ ⊥ := fun h ↦
  hx (PrimeSpectrum.ext (le_antisymm (le_maximalIdeal (toBase x).isPrime.ne_top)
    (h.le.trans bot_le)))

variable {R} in
/-- If some point of a scheme over a local ring does not lie over the closed point, then a
generator of the maximal ideal is nonzero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ne_zero_of_base_ne_closedPoint {x : X}
    (hx : toBase x ≠ closedPoint R) {π : R} (hπ : maximalIdeal R = Ideal.span {π}) : π ≠ 0 :=
  fun h ↦ toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hx
    (by rw [hπ, h, Ideal.span_singleton_eq_bot])

/-- The underlying topological space of the special fibre is homeomorphic to the preimage of the
closed point, compatibly with the inclusion into `X` (`coe_specialFiberHomeomorph_apply`). -/
noncomputable def specialFiberHomeomorph :
    (specialFiber R toBase).left ≃ₜ ↥(toBase ⁻¹' {closedPoint R}) :=
  (specialFiberIsoFiberClosedPoint (.of R) toBase).hom.homeomorph.trans
    (toBase.fiberHomeo (closedPoint R))

/-- Under `specialFiberHomeomorph`, inclusion into `X` is `specialFiberι`. -/
lemma coe_specialFiberHomeomorph_apply (x : (specialFiber R toBase).left) :
    ((specialFiberHomeomorph R toBase x : ↥(toBase ⁻¹' {closedPoint R})) : X) =
      specialFiberι R toBase x :=
  (congrArg Subtype.val (Homeomorph.trans_apply
    (specialFiberIsoFiberClosedPoint (.of R) toBase).hom.homeomorph
    (toBase.fiberHomeo (closedPoint R)) x)).trans <|
    (toBase.fiberHomeo_apply (closedPoint R) _).trans <|
    (congrArg (toBase.fiberι (closedPoint R))
      ((specialFiberIsoFiberClosedPoint (.of R) toBase).hom.homeomorph_apply x)).trans <|
    (Scheme.Hom.comp_apply (specialFiberIsoFiberClosedPoint (.of R) toBase).hom
      (toBase.fiberι (closedPoint R)) x).symm.trans <|
    congr($(specialFiberIsoFiberClosedPoint_hom_fiberι (.of R) toBase) x)

/-- The special fibre is nonempty if and only if some point of `X` lies over the closed point. -/
theorem nonempty_specialFiber_iff :
    Nonempty (specialFiber R toBase).left ↔ (toBase ⁻¹' {closedPoint R}).Nonempty :=
  (specialFiberHomeomorph R toBase).nonempty_congr.trans Set.nonempty_coe_sort

/-- The special fibre is preconnected if and only if the preimage of the closed point is
preconnected. -/
theorem preconnectedSpace_specialFiber_iff :
    PreconnectedSpace (specialFiber R toBase).left ↔
      _root_.IsPreconnected (toBase ⁻¹' {closedPoint R}) :=
  ⟨fun _ ↦ _root_.isPreconnected_iff_preconnectedSpace.mpr <|
      (specialFiberHomeomorph R toBase).surjective.denseRange.preconnectedSpace
        (specialFiberHomeomorph R toBase).continuous,
    fun h ↦
      have := Subtype.preconnectedSpace h
      (specialFiberHomeomorph R toBase).symm.surjective.denseRange.preconnectedSpace
        (specialFiberHomeomorph R toBase).symm.continuous⟩

/-- The special fibre is connected if and only if the preimage of the closed point is connected. -/
theorem connectedSpace_specialFiber_iff :
    ConnectedSpace (specialFiber R toBase).left ↔
      _root_.IsConnected (toBase ⁻¹' {closedPoint R}) :=
  (specialFiberHomeomorph R toBase).connectedSpace_iff.trans
    _root_.isConnected_iff_connectedSpace.symm

section UniversallyClosed

variable [UniversallyClosed toBase] [Nonempty X]

variable {R} in
/-- The preimage of the closed point under a universally closed morphism from a nonempty scheme to
the spectrum of a local ring is nonempty. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.preimage_closedPoint_nonempty :
    (toBase ⁻¹' {closedPoint R}).Nonempty :=
  let ⟨x⟩ := ‹Nonempty X›
  (IsLocalRing.specializes_closedPoint (toBase x)).mem_closed
    toBase.isClosedMap.isClosed_range ⟨x, rfl⟩

/-- The special fibre of a nonempty scheme universally closed over a local ring is nonempty. -/
instance nonempty_specialFiber : Nonempty (specialFiber R toBase).left :=
  (nonempty_specialFiber_iff R toBase).mpr toBase.preimage_closedPoint_nonempty

/-- For a nonempty scheme universally closed over a local ring, the special fibre is connected if
and only if the preimage of the closed point is preconnected. -/
theorem connectedSpace_specialFiber_iff_isPreconnected :
    ConnectedSpace (specialFiber R toBase).left ↔
      _root_.IsPreconnected (toBase ⁻¹' {closedPoint R}) :=
  (connectedSpace_specialFiber_iff R toBase).trans
    (and_iff_right toBase.preimage_closedPoint_nonempty)

end UniversallyClosed

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

omit [Ring.DimensionLEOne R] in
/-- If the maximal ideal of a local ring `R` contains a non-nilpotent element `π`, then the generic
point of an irreducible scheme flat over `R` does not lie in the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint_of_not_isNilpotent
    [Flat toBase] {π : R} (hπ : π ∈ maximalIdeal R) (hπ0 : ¬IsNilpotent π) :
    toBase (genericPoint X) ≠ closedPoint R := by
  intro h
  have hnil : π ∈ nilradical R := by
    rw [nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    have hspec : (⟨J, hJ⟩ : Spec (.of R)) ⤳ toBase (genericPoint X) :=
      h.symm ▸ IsLocalRing.specializes_closedPoint ⟨J, hJ⟩
    obtain ⟨η, hη, hfη⟩ := Flat.generalizingMap toBase hspec
    rw [(hη.antisymm (genericPoint_specializes η)).eq, h] at hfη
    have hmax : maximalIdeal R = J := congrArg PrimeSpectrum.asIdeal hfη
    exact hmax ▸ hπ
  exact hπ0 hnil

omit [Ring.DimensionLEOne R] in
/-- If the maximal ideal of a local ring `R` contains a nonzerodivisor `π`, then the generic point
of an irreducible scheme flat over `R` does not lie in the special fibre. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.base_genericPoint_ne_closedPoint_of_isSMulRegular
    [Flat toBase] {π : R} (hπ : π ∈ maximalIdeal R) (hreg : IsSMulRegular R π) :
    toBase (genericPoint X) ≠ closedPoint R :=
  toBase.base_genericPoint_ne_closedPoint_of_not_isNilpotent hπ fun ⟨n, hn⟩ ↦
    (hreg.pow n).isLeftRegular.ne_zero hn

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

/-- **The special fibre is the union of its irreducible components.** For an integral locally
Noetherian scheme over a local ring of dimension at most one, whose generic point does not lie in
the special fibre, the special fibre is the union of the closures of the codimension-one points of
`X` lying in it. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.biUnion_closure_eq_preimage_closedPoint
    (hη : toBase (genericPoint X) ≠ closedPoint R) :
    ⋃ η ∈ {η : CodimensionOnePoint X | toBase η = closedPoint R}, closure {(η : X)} =
      toBase ⁻¹' {closedPoint R} := by
  have hR := toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη
  refine subset_antisymm (Set.iUnion₂_subset fun η hη' ↦ closure_minimal
    (Set.singleton_subset_iff.mpr hη')
    ((isClosed_singleton_closedPoint R).preimage toBase.continuous)) fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := toBase.exists_maximal_base_eq_closedPoint_specializes hR hx
  obtain ⟨hy', hcod⟩ := (toBase.maximal_base_eq_closedPoint_iff hR hη).mp hy
  exact Set.mem_biUnion (x := ⟨y, hcod⟩) hy' (specializes_iff_mem_closure.mp hyx)

/-- The special fibre of an integral locally Noetherian scheme universally closed over a local ring
of dimension at most one, whose generic point does not lie in the special fibre, has at least one
irreducible component. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.nonempty_setOf_base_eq_closedPoint
    [UniversallyClosed toBase] (hη : toBase (genericPoint X) ≠ closedPoint R) :
    {η : CodimensionOnePoint X | toBase η = closedPoint R}.Nonempty := by
  have h := toBase.preimage_closedPoint_nonempty
  rw [← toBase.biUnion_closure_eq_preimage_closedPoint hη, Set.nonempty_biUnion] at h
  obtain ⟨η, hη', -⟩ := h
  exact ⟨η, hη'⟩

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
Together with `TauCeti.AlgebraicGeometry.SchemeWeilDivisor.principalDivisor_ofMul_mk0_nonneg`
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
