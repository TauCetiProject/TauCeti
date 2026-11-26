/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Model.Normalization
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Locus

import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Normal
import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.AlgebraicGeometry.SpecialFiber.Components
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber
import TauCeti.RingTheory.RegularLocalRing.FiniteNonregularLocus
import TauCeti.RingTheory.UniversallyJapanese

/-!
# The singular points of a normal model of a curve

Let `R` be a discrete valuation ring with fraction field `K`, and let `M` be a model over `R` of a
scheme `C` over `K` of dimension at most one, for instance a smooth curve. The generic fibre `C`
is open in the total space `X` of `M`, so `X` is regular along it when `C` is regular. If `X` is
normal, then `C` is normal of dimension at most one, hence regular, and `X` is regular at the
generic points of its special fibre as well; it is then regular at all but finitely many points,
which lie in the special fibre. No excellence assumption on `R` is needed.

This is the finiteness of the singular locus in Lipman's criterion for resolving the
singularities of a two-dimensional scheme by normalized blowups in closed points. The
normalization of any model of a smooth curve in its generic fibre is such a normal model
(`TauCeti.Model.isNormalScheme_normalization_of_smooth`), so it has finitely many singular
points.

The proof is affine-local. Over an affine open `Spec A` of `X`, with `π` a uniformizer of `R`,
the image of `π` is a nonzerodivisor of `A` since `A` is flat over `R`, the special fibre
`A ⧸ π A` is of finite type over the residue field, hence Nagata, of dimension at most one, and
normality makes `A` regular at the minimal primes of `π A`; the ring-level theorem
`TauCeti.Excellence.finite_zeroLocus_diff_regularLocus` then applies.

## Main results

* `TauCeti.Model.range_genericι_subset_regularLocus`: a model is regular along its generic fibre
  when the generic fibre is regular.
* `TauCeti.Model.finite_compl_regularLocus`: a normal model of a scheme of dimension at most one
  over `K` has finitely many non-regular points.
* `TauCeti.Model.finite_compl_regularLocus_normalization`: the normalization of a model of a
  smooth curve has finitely many non-regular points.

## References

* The Stacks Project, Lemma 55.8.3 (0C2U) and Theorem 54.14.5 (0BGP).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Oxford University Press, 2002, Section 8.3
  (desingularization of arithmetic surfaces).
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry IsLocalRing

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable (M : Model R K C toK)

/-- A model of a regular scheme is regular along its generic fibre: the generic fibre is an open
subscheme of the total space. -/
theorem range_genericι_subset_regularLocus [IsRegular C] :
    Set.range M.genericι ⊆ M.total.regularLocus := by
  have := M.isOpenImmersion_genericι
  rintro _ ⟨c, rfl⟩
  exact Scheme.mem_regularLocus.mpr
    ((isRegularLocalRing_stalk_iff_of_isOpenImmersion M.genericι c).mpr inferInstance)

variable {M}

/-- Over an affine open `U` of a model, a nonzero element of `R` is a nonzerodivisor on the
sections, which are flat over `R`. -/
private lemma algebraMap_mem_nonZeroDivisors_sections {U : M.total.Opens} (hU : IsAffineOpen U)
    {π : R} (hπ : π ≠ 0) :
    letI := M.toBase.sectionsAlgebra U
    algebraMap R Γ(M.total, U) π ∈ nonZeroDivisors Γ(M.total, U) := by
  let := M.toBase.sectionsAlgebra U
  have : Module.Flat R Γ(M.total, U) := by
    refine RingHom.flat_algebraMap_iff.mp ?_
    rw [M.toBase.algebraMap_sections, CommRingCat.hom_comp]
    exact (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)).comp
      (M.toBase.flat_appLE (isAffineOpen_top _) hU _)
  exact mem_nonZeroDivisors_iff_right.mpr fun z hz ↦
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(M.total, U))
      (mem_nonZeroDivisors_of_ne_zero hπ)
      (by dsimp only; rw [smul_zero, Algebra.smul_def, mul_comm, hz])

/-- Over an affine open `U` of a model, the special fibre `Γ(U) ⧸ π Γ(U)` is of finite type over
the residue field of `R`, hence a Nagata ring. -/
private lemma isNagata_sections_quotient {U : M.total.Opens} (hU : IsAffineOpen U) {π : R}
    (hπ : Irreducible π) :
    letI := M.toBase.sectionsAlgebra U
    Ring.IsNagata (Γ(M.total, U) ⧸ Ideal.span {algebraMap R Γ(M.total, U) π}) := by
  let := M.toBase.sectionsAlgebra U
  have : Algebra.FiniteType R Γ(M.total, U) := RingHom.finiteType_algebraMap.mp <|
    M.toBase.algebraMap_sections U ▸ M.toBase.finiteType_ΓSpecIso_inv_comp_appLE hU
  have hmap : (maximalIdeal R).map (algebraMap R Γ(M.total, U)) =
      Ideal.span {algebraMap R Γ(M.total, U) π} := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have : Ring.IsNagata ((maximalIdeal R).Fiber Γ(M.total, U)) :=
    Ring.IsUniversallyJapanese.isNagata_of_finiteType (maximalIdeal R).ResidueField _
  exact ((Ideal.Fiber.algEquivQuotientMap (maximalIdeal R)).toRingEquiv.trans
    (Ideal.quotEquivOfEq hmap)).isNagata

/-- Over an affine open `U` of a normal locally Noetherian scheme, the sections are regular at
every minimal prime over a principal ideal: the localization there is an integrally closed local
domain of dimension at most one. -/
private lemma mem_regularLocus_sections_of_mem_minimalPrimes {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormalScheme X] {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)}
    (q : PrimeSpectrum Γ(X, U)) (hq : q.asIdeal ∈ (Ideal.span {a}).minimalPrimes) :
    q ∈ Excellence.regularLocus Γ(X, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨_, _⟩ := (isNormalScheme_Spec_iff_forall_localization Γ(X, U)).mp
    (isNormalScheme_iff_forall_affineOpens.mp ‹_› ⟨U, hU⟩) q.asIdeal
  have : Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := Ring.krullDimLE_iff.mpr <| by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal]
    exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq
  have : IsPrincipalIdealRing (Localization.AtPrime q.asIdeal) := .of_krullDimLE_one
  exact Excellence.mem_regularLocus.mpr inferInstance

/-- Over an affine open `U` of a normal model, only finitely many points of `U` are not regular. -/
private lemma finite_compl_regularLocus_inter [IsNormalScheme M.total] [IsRegular C]
    [AlgebraicGeometry.RelativeDimensionLE 1 toK] {U : M.total.Opens} (hU : IsAffineOpen U) :
    (M.total.regularLocusᶜ ∩ U).Finite := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := M.toBase.sectionsAlgebra U
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : IsNoetherianRing Γ(M.total, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := isNagata_sections_quotient hU hπ
  have := krullDimLE_sections_quotient (M := M) hU hπ
  -- On `Spec Γ(U)`, only finitely many primes containing `π` are not regular.
  have hfin := Excellence.finite_zeroLocus_diff_regularLocus
    (algebraMap_mem_nonZeroDivisors_sections hU hπ.ne_zero)
    (mem_regularLocus_sections_of_mem_minimalPrimes hU)
  refine (hfin.image hU.fromSpec).subset ?_
  rintro x ⟨hx, hxU⟩
  set p := hU.primeIdealOf ⟨x, hxU⟩
  have hpx : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  refine ⟨p, ⟨?_, fun hp ↦ hx ?_⟩, hpx⟩
  · -- A non-regular point lies in the special fibre, where `π` vanishes.
    have hx' : M.toBase x = closedPoint R := by
      by_contra h
      exact hx (M.range_genericι_subset_regularLocus
        (M.range_genericι_eq_setOf_base_ne_closedPoint ▸ h))
    rw [← hpx, ← Scheme.Hom.comp_apply hU.fromSpec M.toBase p, M.toBase.fromSpec_toSpec hU] at hx'
    have hcomap : PrimeSpectrum.comap (algebraMap R Γ(M.total, U)) p = closedPoint R :=
      (Spec.map_apply (CommRingCat.ofHom (algebraMap R Γ(M.total, U))) p).symm.trans hx'
    have := ((PrimeSpectrum.comap _ p).mem_asIdeal_iff_eq_closedPoint
      ((mem_maximalIdeal π).mpr hπ.not_isUnit) hπ.ne_zero).mpr hcomap
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr (Set.singleton_subset_iff.mpr this)
  · rw [← hpx]
    exact Scheme.mem_regularLocus.mpr <|
      (isRegularLocalRing_stalk_iff_of_isOpenImmersion hU.fromSpec p).mpr <|
        (isRegularLocalRing_stalk_Spec_iff _ p).mpr (Excellence.mem_regularLocus.mp hp)

variable (M)

/-- **A normal model of a curve has finitely many singular points.** If the total space of a
model `M` is normal and the generic fibre `C` has dimension at most one over `K`, then only
finitely many points of the total space are not regular; by
`TauCeti.Model.range_genericι_subset_regularLocus` they lie in the special fibre. This holds over
any, possibly non-excellent, discrete valuation ring. -/
theorem finite_compl_regularLocus [IsNormalScheme M.total]
    [AlgebraicGeometry.RelativeDimensionLE 1 toK] : M.total.regularLocusᶜ.Finite := by
  -- The generic fibre is open in the normal total space, so it is normal of dimension at most one,
  -- hence regular.
  have := M.isOpenImmersion_genericι
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have := isLocallyNoetherian_of_isOpenImmersion M.genericι
  have := IsNormalScheme.of_isOpenImmersion M.genericι
  have : IsRegular C := .of_isNormalScheme_of_topologicalKrullDim_le_one
    ((AlgebraicGeometry.relativeDimensionLE_iff_of_field toK).mp inferInstance)
  have : CompactSpace M.total := QuasiCompact.compactSpace_of_compactSpace M.toBase
  have hcov (x : M.total) : ∃ U : M.total.Opens, IsAffineOpen U ∧ x ∈ U := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      M.total.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨U, hU, hxU⟩
  choose U hU hxU using hcov
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x ↦ (U x : Set M.total))
    fun x _ ↦ (U x).isOpen.mem_nhds (hxU x)
  refine (t.finite_toSet.biUnion fun x _ ↦ finite_compl_regularLocus_inter (hU x)).subset
    fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  exact Set.mem_biUnion hx ⟨hy, hyx⟩

/-- **The normalization of a model of a smooth curve has finitely many singular points.** If the
generic fibre `C` is smooth of relative dimension one over `K`, the normalization of the total
space of `M` in `C` is a normal model of `C` with only finitely many non-regular points. -/
theorem finite_compl_regularLocus_normalization [SmoothOfRelativeDimension 1 toK] :
    M.normalization.total.regularLocusᶜ.Finite := by
  have := SmoothOfRelativeDimension.smooth 1 toK
  have := M.isNormalScheme_normalization_of_smooth
  exact M.normalization.finite_compl_regularLocus

end Model

end TauCeti
