/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Prod
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.JordanSplitting
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.Sum
import TauCeti.NumberTheory.IntegralLattice.JordanSplitting

/-!
# The dyadic density profile of an orthogonal sum

The sum of Jordan splittings of the summands, constituent by constituent, is a Jordan splitting
of the orthogonal sum (`LinearMap.BilinForm.IsJordanSplitting.prod`). The constituent of scale
`π ^ i` of that splitting has rank the sum of the two ranks, and it is of type I exactly when one
of the two summed constituents is: a self-pairing `B x x + C y y` escapes `π ^ (i + 1)` only if
one of `B x x` and `C y y` does. So the dyadic density profile of `L ⊕ M` is the sum of the
profiles of `L` and `M`, and Cho's exponents of `L ⊕ M` are computed from those of `L` and `M` by
`TauCeti.DyadicJordanProfile.nM_add`, `TauCeti.DyadicJordanProfile.nQ_add` and
`TauCeti.DyadicJordanProfile.densityExponent_add` when the dyadic scales of `L` lie below those
of `M`.

The lattice `⟨1⟩ ⊕ ⟨2⟩` is the first example where a type-I pair straddles the two summands:
its profile is two type-I constituents at the adjacent scales `1` and `2`, and its density
exponent is `2`, not the sum `1 + 2` of the exponents of `⟨1⟩` and `⟨2⟩`.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.dyadicJordanProfile_prod`: the profile of the product
  of two Jordan splittings is the sum of their profiles.
* `TauCeti.IntegralLattice.dyadicJordanProfile_orthogonalSum`: the dyadic profile of the
  orthogonal sum of two nondegenerate lattices is the sum of their dyadic profiles.
* `TauCeti.IntegralLattice.densityExponent_dyadicJordanProfile_rankOne_one_orthogonalSum_two`:
  the lattice `⟨1⟩ ⊕ ⟨2⟩` has dyadic density exponent `2`.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Definition 2.1, Section 2.3, and Lemma 5.1.
-/

public section

open Module

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M M' : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] [AddCommGroup M'] [Module R M'] [Module.Free R M']
  [Module.Finite R M'] {B : BilinForm R M} {C : BilinForm R M'} {π : R}
  {N : ℕ → Submodule R M} {N' : ℕ → Submodule R M'}

/-- **The profile of an orthogonal sum.** The profile of the Jordan splitting of `B.prod C` by
the products `N i × N' i` is the sum of the profiles of the splittings `N` and `N'`. -/
theorem IsJordanSplitting.dyadicJordanProfile_prod (h : B.IsJordanSplitting π N)
    (h' : C.IsJordanSplitting π N') (hB : B.IsSymm) (hC : C.IsSymm) (hπ : π ≠ 0)
    (hπ' : ¬IsUnit π) :
    (h.prod h').dyadicJordanProfile
        (isSymm_prod_iff.mpr ⟨hB, hC⟩) hπ hπ' =
      h.dyadicJordanProfile hB hπ hπ' + h'.dyadicJordanProfile hC hπ hπ' := by
  ext i
  · have : Module.Free R (N i) := h.free i
    have : Module.Finite R (N i) := h.finite i
    have : Module.Free R (N' i) := h'.free i
    have : Module.Finite R (N' i) := h'.finite i
    simp [(Submodule.prodEquiv (N i) (N' i)).finrank_eq, Module.finrank_prod]
  · rw [TauCeti.DyadicJordanProfile.add_typeI, Finset.mem_union,
      IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff_exists,
      IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff_exists,
      IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff_exists]
    constructor
    · rintro ⟨x, hx, hxx⟩
      by_contra! hall
      exact hxx (by
        rw [prod_apply]
        exact dvd_add (hall.1 x.1 hx.1) (hall.2 x.2 hx.2))
    · rintro (⟨x, hx, hxx⟩ | ⟨y, hy, hyy⟩)
      · exact ⟨(x, 0), ⟨hx, (N' i).zero_mem⟩, by simpa using hxx⟩
      · exact ⟨(0, y), ⟨(N i).zero_mem, hy⟩, by simpa using hyy⟩

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **The dyadic profile of an orthogonal sum** of two nondegenerate lattices is the sum of their
dyadic profiles. -/
theorem dyadicJordanProfile_orthogonalSum {L : IntegralLattice V} {M : IntegralLattice W}
    (hL : L.form.Nondegenerate) (hM : M.form.Nondegenerate) :
    (L.orthogonalSum M).dyadicJordanProfile = L.dyadicJordanProfile + M.dyadicJordanProfile := by
  obtain ⟨N, hN⟩ := L.exists_isJordanSplitting_localIntegralForm 2 hL
  obtain ⟨N', hN'⟩ := M.exists_isJordanSplitting_localIntegralForm 2 hM
  rw [Nat.cast_ofNat] at hN hN'
  have hprod := hN.prod hN'
  have hsum := hprod.map_isometryEquiv (L.localOrthogonalSumIsometry M 2).symm
  rw [dyadicJordanProfile_eq hsum, dyadicJordanProfile_eq hN, dyadicJordanProfile_eq hN',
    ← hN.dyadicJordanProfile_prod hN']
  exact hsum.dyadicJordanProfile_eq_of_equivalent _ _ _ hprod _
    ⟨L.localOrthogonalSumIsometry M 2⟩

/-- **The lattice `⟨1⟩ ⊕ ⟨2⟩` is two adjacent type I constituents** at the scales `1` and `2`. -/
theorem dyadicJordanProfile_rankOne_one_orthogonalSum_two :
    ((rankOne 1).orthogonalSum (rankOne 2)).dyadicJordanProfile =
      DyadicJordanProfile.adjacentUnaryTypeI := by
  have h1 : (rankOne 1).dyadicJordanProfile = .unaryTypeI 0 := by
    simpa using dyadicJordanProfile_rankOne_two_pow_mul 0 odd_one
  have h2 : (rankOne 2).dyadicJordanProfile = .unaryTypeI 1 := by
    simpa using dyadicJordanProfile_rankOne_two_pow_mul 1 odd_one
  rw [dyadicJordanProfile_orthogonalSum
      ((isPosDef_iff_isPosSemidef_and_nondegenerate _).mp (isPosDef_rankOne one_pos)).2
      ((isPosDef_iff_isPosSemidef_and_nondegenerate _).mp (isPosDef_rankOne two_pos)).2,
    h1, h2, DyadicJordanProfile.unaryTypeI_zero_add_unaryTypeI_one]

/-- **The lattice `⟨1⟩ ⊕ ⟨2⟩` has dyadic density exponent `2`**, while `⟨1⟩` and `⟨2⟩` have
density exponents `1` and `2`: the adjacent type I pair straddling the two summands lowers the
sum by one. -/
theorem densityExponent_dyadicJordanProfile_rankOne_one_orthogonalSum_two :
    ((rankOne 1).orthogonalSum (rankOne 2)).dyadicJordanProfile.densityExponent = 2 := by
  rw [dyadicJordanProfile_rankOne_one_orthogonalSum_two,
    DyadicJordanProfile.densityExponent_adjacentUnaryTypeI]

end TauCeti.IntegralLattice
