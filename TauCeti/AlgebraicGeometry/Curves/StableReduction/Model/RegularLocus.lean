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
import TauCeti.AlgebraicGeometry.Scheme.SpecOver
import TauCeti.AlgebraicGeometry.SpecialFiber.Components
import TauCeti.RingTheory.RegularLocalRing.FiniteNonregularLocus

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
`TauCeti.Excellence.finite_zeroLocus_sdiff_regularLocus` then applies.

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
  rw [← Set.image_univ, Set.image_subset_iff, M.genericι.preimage_regularLocus,
    Scheme.regularLocus_eq_univ]

variable {M}

/-- Over an affine open `U` of a normal model, only finitely many points of `U` are not regular. -/
private lemma finite_compl_regularLocus_inter [IsNormalScheme M.total] [IsRegular C]
    [AlgebraicGeometry.RelativeDimensionLE 1 toK] {U : M.total.Opens} (hU : IsAffineOpen U) :
    (M.total.regularLocusᶜ ∩ U).Finite := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let := M.toBase.sectionsAlgebra U
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  have : IsNoetherianRing Γ(M.total, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have := M.isNagata_sections_quotient hU hπ
  have := M.krullDimLE_sections_quotient (d := 1) hU hπ
  -- On `Spec Γ(U)`, only finitely many primes containing `π` are not regular.
  have hfin := Excellence.finite_zeroLocus_sdiff_regularLocus
    (M.algebraMap_mem_nonZeroDivisors_sections hU hπ.ne_zero)
    hU.mem_regularLocus_of_mem_minimalPrimes_span_singleton
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
  · rwa [← hpx, ← Set.mem_preimage (f := hU.fromSpec) (a := p), hU.fromSpec.preimage_regularLocus,
      Scheme.regularLocus_Spec]

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
  -- Cover the quasi-compact total space by finitely many affine opens.
  let 𝒰 := M.total.affineCover.finiteSubcover
  refine (Set.finite_iUnion fun j ↦
    finite_compl_regularLocus_inter (isAffineOpen_opensRange (𝒰.f j))).subset fun y hy ↦ ?_
  obtain ⟨j, z, rfl⟩ := 𝒰.exists_eq y
  exact Set.mem_iUnion.mpr ⟨j, hy, z, rfl⟩

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
