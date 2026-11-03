/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.DensityExponent.Basic
public import TauCeti.NumberTheory.IntegralLattice.Genus
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.RankOne.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic
public import TauCeti.NumberTheory.IntegralLattice.Dyadic.Unimodular
public import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The density profile of a dyadic Jordan splitting

The exponents `N_M`, `N_Q` and `N` of Cho's dyadic local density formula are functions of the
ranks and parity types of the constituents of a Jordan splitting
(`TauCeti.DyadicJordanProfile`). This file reads that profile off an actual splitting and shows
that it is an invariant of the form.

Let `B` be a symmetric bilinear form on a finite free module over a local domain `R`, and let
`N` be a Jordan splitting of `B` with respect to a nonzero non-unit `π`. Its profile
`LinearMap.BilinForm.IsJordanSplitting.dyadicJordanProfile` records the rank of each
constituent `N i`, and declares `N i` of type I when it is not even at its own scale: some
`x ∈ N i` has `π ^ (i + 1) ∤ B x x`. The type is measured against the scale `π ^ i` of the
constituent, not against `R`, so that the unary form `⟨2⟩` over `ℤ_2` is of type I. A
constituent of type II has even rank, because its unimodular rescaling is a perfect pairing with
non-unit diagonal (`LinearMap.BilinForm.IsJordanSplitting.even_finrank_of_isScaleEven`). The
profile is the same for any two splittings of isometric forms, since the
ranks and the scale-relative parities of the constituents are isometry invariants
(`LinearMap.BilinForm.IsJordanSplitting.dyadicJordanProfile_eq_of_equivalent`).

For an integral lattice `L`, `TauCeti.IntegralLattice.dyadicJordanProfile` is the profile of any
Jordan splitting of the dyadic localization `ℤ_2 ⊗[ℤ] L`. It depends only on the isometry class
of that localization, hence only on the genus of `L`, and so do the density exponents.

The file computes the worked values. An even lattice of odd determinant and rank `n`, such as
`U` or `E₈`, is a single type II constituent of scale `1`, with density exponent `N = n`, and not
`0`. The lattice `⟨2 ^ i u⟩` with `u` odd is a single type I constituent of scale `2 ^ i`, with
`N = i + 1`; thus `⟨1⟩` has `N = 1` and `⟨2⟩` has `N = 2`.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting.dyadicJordanProfile`: the ranks and parity types of the
  constituents of a Jordan splitting.
* `TauCeti.IntegralLattice.dyadicJordanProfile`: the profile of the dyadic localization of an
  integral lattice.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.dyadicJordanProfile_eq_of_equivalent`: Jordan
  splittings of isometric forms have the same profile.
* `LinearMap.BilinForm.IsModular.dyadicJordanProfile_ranks`,
  `LinearMap.BilinForm.IsModular.mem_dyadicJordanProfile_typeI_iff`: the profile of a
  `π ^ i`-modular form is a single constituent of scale `π ^ i`.
* `TauCeti.IntegralLattice.dyadicJordanProfile_eq_of_equivalent`,
  `TauCeti.IntegralLattice.SameGenus.dyadicJordanProfile_eq`: the dyadic profile is an invariant
  of the dyadic localization, and of the genus.
* `TauCeti.IntegralLattice.IsEven.densityExponent_dyadicJordanProfile`: an even lattice of odd
  determinant has density exponent equal to its rank.
* `TauCeti.IntegralLattice.densityExponent_dyadicJordanProfile_rankOne_two_pow_mul`: the
  lattice `⟨2 ^ i u⟩` with `u` odd has density exponent `i + 1`.

## References

* S. Cho, *Group schemes and local densities of quadratic lattices in residue characteristic 2*,
  Compositio Math. 151 (2015), Definition 2.1, Section 2.3, and Lemma 5.1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, 93:28--29, for the invariance of the ranks
  and types of dyadic Jordan constituents.
-/

public section

open Module

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M] {B : BilinForm R M} {π : R} {N : ℕ → Submodule R M}

open Classical in
/-- **The density profile of a Jordan splitting.** The rank of the constituent of scale
`π ^ i` is `finrank R (N i)`, and the constituent is of type I when it is not even at its own
scale. For `R = ℤ_2` and `π = 2` this is the dyadic Jordan data of Cho's Definition 2.1. -/
noncomputable def IsJordanSplitting.dyadicJordanProfile (h : B.IsJordanSplitting π N)
    (hB : B.IsSymm) (hπ : π ≠ 0) (hπ' : ¬IsUnit π) : TauCeti.DyadicJordanProfile where
  ranks := Finsupp.ofSupportFinite (fun i ↦ finrank R (N i)) h.finite_support_finrank
  typeI := h.finite_support_finrank.toFinset.filter fun i ↦ ¬(B.restrict (N i)).IsScaleEven π
  typeI_subset_support := by
    rw [Finsupp.ofSupportFinite_support]
    exact Finset.filter_subset _ _
  even_rank_of_notMem_typeI i hi := by
    rw [Finsupp.ofSupportFinite_coe]
    by_cases h0 : finrank R (N i) = 0
    · simp [h0]
    · simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, h0,
        not_false_eq_true, true_and, not_not] at hi
      exact h.even_finrank_of_isScaleEven hB (mem_nonZeroDivisors_of_ne_zero hπ) hπ' hi

variable (h : B.IsJordanSplitting π N) (hB : B.IsSymm) (hπ : π ≠ 0) (hπ' : ¬IsUnit π)

/-- The profile of a Jordan splitting records the ranks of its constituents. -/
@[simp]
theorem IsJordanSplitting.dyadicJordanProfile_ranks_apply (i : ℕ) :
    (h.dyadicJordanProfile hB hπ hπ').ranks i = finrank R (N i) := by
  rw [dyadicJordanProfile, Finsupp.ofSupportFinite_coe]

/-- A constituent is of type I in the profile exactly when it is not even at its own scale. -/
@[simp]
theorem IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff {i : ℕ} :
    i ∈ (h.dyadicJordanProfile hB hπ hπ').typeI ↔ ¬(B.restrict (N i)).IsScaleEven π := by
  simp only [dyadicJordanProfile, Finset.mem_filter, Set.Finite.mem_toFinset,
    Function.mem_support, and_iff_right_iff_imp]
  intro he h0
  have : Module.Free R (N i) := h.free i
  have : Module.Finite R (N i) := h.finite i
  have : Subsingleton (N i) := (Module.finrank_eq_zero_iff_of_free R (N i)).mp h0
  refine he ((h.isScaleEven_restrict_iff i).mpr fun x hx ↦ ?_)
  obtain rfl : x = 0 := congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : N i) 0)
  simp

/-- A constituent is of type I in the profile exactly when one of its vectors has self-pairing
not divisible by `π ^ (i + 1)`. -/
theorem IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff_exists {i : ℕ} :
    i ∈ (h.dyadicJordanProfile hB hπ hπ').typeI ↔ ∃ x ∈ N i, ¬π ^ (i + 1) ∣ B x x := by
  have : Module.Free R (N i) := h.free i
  rw [h.mem_dyadicJordanProfile_typeI_iff, h.isScaleEven_restrict_iff]
  simp only [not_forall, exists_prop]

/-- **The profile is an isometry invariant.** Jordan splittings of isometric symmetric forms with
respect to the same nonzero non-unit `π` have the same profile. In particular the profile does
not depend on the chosen splitting. -/
theorem IsJordanSplitting.dyadicJordanProfile_eq_of_equivalent {M' : Type*} [AddCommGroup M']
    [Module R M'] [Module.Free R M'] [Module.Finite R M'] {B' : BilinForm R M'}
    {N' : ℕ → Submodule R M'} (h' : B'.IsJordanSplitting π N') (hB' : B'.IsSymm)
    (hBB' : B.Equivalent B') :
    h.dyadicJordanProfile hB hπ hπ' = h'.dyadicJordanProfile hB' hπ hπ' := by
  have hrank (i : ℕ) : finrank R (N i) = finrank R (N' i) :=
    h.finrank_eq_of_equivalent h' hBB' hπ hπ' i
  ext i
  · simp [hrank]
  · have : Module.Free R (N i) := h.free i
    have : Module.Free R (N' i) := h'.free i
    rw [h.mem_dyadicJordanProfile_typeI_iff, h'.mem_dyadicJordanProfile_typeI_iff,
      h.isScaleEven_iff_of_equivalent h' hBB' (mem_nonZeroDivisors_of_ne_zero hπ) i]

/-- The profile of a `π ^ i`-modular form, split as a single constituent
(`LinearMap.BilinForm.IsModular.isJordanSplitting`), has all its rank at scale `π ^ i`. -/
theorem IsModular.dyadicJordanProfile_ranks {i : ℕ} (hmod : B.IsModular (π ^ i)) :
    (hmod.isJordanSplitting.dyadicJordanProfile hB hπ hπ').ranks =
      Finsupp.single i (finrank R M) := by
  ext j
  rw [IsJordanSplitting.dyadicJordanProfile_ranks_apply]
  by_cases hj : j = i
  · rw [ite_eq_left hj, finrank_top, hj, Finsupp.single_eq_same]
  · rw [ite_eq_right hj, finrank_bot, Finsupp.single_apply, ite_eq_right (Ne.symm hj)]

/-- The profile of a `π ^ i`-modular form, split as a single constituent
(`LinearMap.BilinForm.IsModular.isJordanSplitting`), is of type I exactly at `i`, and only when
some vector has self-pairing not divisible by `π ^ (i + 1)`. -/
theorem IsModular.mem_dyadicJordanProfile_typeI_iff {i j : ℕ} (hmod : B.IsModular (π ^ i)) :
    j ∈ (hmod.isJordanSplitting.dyadicJordanProfile hB hπ hπ').typeI ↔
      j = i ∧ ∃ x, ¬π ^ (i + 1) ∣ B x x := by
  rw [IsJordanSplitting.mem_dyadicJordanProfile_typeI_iff_exists]
  by_cases hj : j = i
  · subst hj
    simp
  · simp [hj]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

open Classical in
/-- **The dyadic density profile of an integral lattice.** This is the profile of any Jordan
splitting of the dyadic localization `ℤ_2 ⊗[ℤ] L`
(`TauCeti.IntegralLattice.dyadicJordanProfile_eq`); such a splitting exists whenever `L` is
nondegenerate (`TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`). If there is
none, the profile is the empty profile. -/
noncomputable def dyadicJordanProfile (L : IntegralLattice V) : DyadicJordanProfile :=
  if h : ∃ N, (L.localIntegralForm 2).IsJordanSplitting 2 N then
    h.choose_spec.dyadicJordanProfile (L.isSymm_localIntegralForm 2) two_ne_zero
      PadicInt.not_isUnit_two
  else .empty

/-- The dyadic profile of a lattice is the profile of any Jordan splitting of its dyadic
localization. -/
theorem dyadicJordanProfile_eq {L : IntegralLattice V}
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    (hN : (L.localIntegralForm 2).IsJordanSplitting 2 N) :
    L.dyadicJordanProfile =
      hN.dyadicJordanProfile (L.isSymm_localIntegralForm 2) two_ne_zero
        PadicInt.not_isUnit_two := by
  have h : ∃ N, (L.localIntegralForm 2).IsJordanSplitting 2 N := ⟨N, hN⟩
  rw [dyadicJordanProfile, dite_eq_left h]
  exact h.choose_spec.dyadicJordanProfile_eq_of_equivalent _ _ _ hN _
    ⟨LinearMap.BilinForm.IsometryEquiv.refl _⟩

/-- **The dyadic profile is a local invariant.** Lattices with isometric dyadic localizations
have the same dyadic profile. -/
theorem dyadicJordanProfile_eq_of_equivalent {L : IntegralLattice V} {M : IntegralLattice W}
    (h : (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2)) :
    L.dyadicJordanProfile = M.dyadicJordanProfile := by
  obtain ⟨e⟩ := id h
  by_cases hL : ∃ N, (L.localIntegralForm 2).IsJordanSplitting 2 N
  · obtain ⟨N, hN⟩ := hL
    rw [dyadicJordanProfile_eq hN, dyadicJordanProfile_eq (hN.map_isometryEquiv e)]
    exact hN.dyadicJordanProfile_eq_of_equivalent _ _ _ (hN.map_isometryEquiv e) _ h
  · have hM : ¬∃ N, (M.localIntegralForm 2).IsJordanSplitting 2 N := fun ⟨N, hN⟩ ↦
      hL ⟨_, hN.map_isometryEquiv e.symm⟩
    rw [dyadicJordanProfile, dyadicJordanProfile, dite_eq_right hL, dite_eq_right hM]

/-- **The dyadic profile is a genus invariant.** -/
theorem SameGenus.dyadicJordanProfile_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : L.dyadicJordanProfile = M.dyadicJordanProfile :=
  dyadicJordanProfile_eq_of_equivalent (h.localIntegralForm_equivalent 2)

/-! ### Worked values -/

/-- **An even lattice of odd determinant is one free type II constituent.** Its dyadic
localization is unimodular and even, so its profile is that of a single type II constituent of
scale `1` whose rank is the rank of the lattice. -/
theorem IsEven.dyadicJordanProfile_eq_unimodularTypeII {L : IntegralLattice V} (heven : L.IsEven)
    (hdet : IsUnit (L.determinant : ℤ_[2])) :
    L.dyadicJordanProfile = DyadicJordanProfile.unimodularTypeII (finrank ℤ L)
      (heven.even_finrank_of_isUnit_determinant hdet) := by
  have hmod : (L.localIntegralForm 2).IsModular (2 ^ 0) := by
    rw [pow_zero, LinearMap.BilinForm.isModular_one_iff]
    exact L.isPerfPair_localIntegralForm_of_isUnit_determinant 2 hdet
  rw [dyadicJordanProfile_eq hmod.isJordanSplitting]
  ext i
  · rw [hmod.dyadicJordanProfile_ranks, Module.finrank_baseChange,
      DyadicJordanProfile.unimodularTypeII_ranks]
  · rw [hmod.mem_dyadicJordanProfile_typeI_iff, DyadicJordanProfile.unimodularTypeII_typeI]
    simpa using fun _ ↦ heven.two_dvd_localIntegralForm_apply_self

/-- **The density exponent of an even lattice of odd determinant is its rank**, and not `0`. -/
theorem IsEven.densityExponent_dyadicJordanProfile {L : IntegralLattice V} (heven : L.IsEven)
    (hdet : IsUnit (L.determinant : ℤ_[2])) :
    L.dyadicJordanProfile.densityExponent = finrank ℤ L := by
  rw [heven.dyadicJordanProfile_eq_unimodularTypeII hdet,
    DyadicJordanProfile.densityExponent_unimodularTypeII]

/-- The hyperbolic plane `U` has dyadic density exponent `2`. -/
theorem densityExponent_dyadicJordanProfile_hyperbolicPlane :
    hyperbolicPlane.dyadicJordanProfile.densityExponent = 2 := by
  rw [isEven_hyperbolicPlane.densityExponent_dyadicJordanProfile (by
    simp [hyperbolicPlane_determinant]), hyperbolicPlane.finrank_carrier, Module.finrank_fin_fun]

/-- The `E₈` lattice has dyadic density exponent `8`. -/
theorem densityExponent_dyadicJordanProfile_typeE₈RootLattice :
    typeE₈RootLattice.dyadicJordanProfile.densityExponent = 8 := by
  have hdet : IsUnit typeE₈RootLattice.determinant :=
    typeE₈RootLattice.isUnimodular_iff_isUnit_determinant.mp isUnimodular_typeE₈RootLattice
  rw [isEven_typeE₈RootLattice.densityExponent_dyadicJordanProfile (hdet.map (Int.castRingHom _)),
    typeE₈RootLattice.finrank_carrier, Module.finrank_fin_fun]

/-- **The lattice `⟨2 ^ i u⟩` with `u` odd is one type I constituent of scale `2 ^ i`.** Its
type is measured against its own scale: although every self-pairing is divisible by `2 ^ i`,
the generator has self-pairing not divisible by `2 ^ (i + 1)`. -/
theorem dyadicJordanProfile_rankOne_two_pow_mul (i : ℕ) {u : ℤ} (hu : Odd u) :
    (rankOne (2 ^ i * u)).dyadicJordanProfile = DyadicJordanProfile.unaryTypeI i := by
  classical
  have hu' : IsUnit (u : ℤ_[2]) := PadicInt.isUnit_intCast_iff.mpr fun h ↦
    Int.not_even_iff_odd.mpr hu (even_iff_two_dvd.mpr (by exact_mod_cast h))
  let L := rankOne (2 ^ i * u)
  let b := (Module.finBasisOfFinrankEq ℤ L (finrank_rankOne _)).baseChange ℤ_[2]
  have hdet : ((L.localIntegralForm 2).toMatrix b).det = 2 ^ i * u := by
    rw [L.det_toMatrix_localIntegralForm, rankOne_determinant, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat]
  have hb : L.localIntegralForm 2 (b 0) (b 0) = 2 ^ i * u := by
    rwa [Matrix.det_unique, LinearMap.BilinForm.toMatrix_apply] at hdet
  have hb' (j k : Fin 1) :
      L.localIntegralForm 2 (b j) (b k) = 2 ^ i * Matrix.of (fun _ _ ↦ (u : ℤ_[2])) j k := by
    rw [Subsingleton.elim j 0, Subsingleton.elim k 0, hb, Matrix.of_apply]
  have hmod : (L.localIntegralForm 2).IsModular (2 ^ i) :=
    b.isModular_of_isUnit_det (pow_mem (mem_nonZeroDivisors_of_ne_zero two_ne_zero) i) hb'
      (by simpa using hu')
  rw [dyadicJordanProfile_eq hmod.isJordanSplitting]
  ext j
  · rw [hmod.dyadicJordanProfile_ranks, Module.finrank_baseChange, finrank_rankOne,
      DyadicJordanProfile.unaryTypeI_ranks]
  · rw [hmod.mem_dyadicJordanProfile_typeI_iff, DyadicJordanProfile.unaryTypeI_typeI,
      Finset.mem_singleton, and_iff_left_iff_imp]
    refine fun _ ↦ ⟨b 0, ?_⟩
    rw [hb, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ two_ne_zero)]
    exact fun h2 ↦ PadicInt.not_isUnit_two (isUnit_of_dvd_unit h2 hu')

/-- **`⟨2 ^ i u⟩` with `u` odd has dyadic density exponent `i + 1`.** -/
theorem densityExponent_dyadicJordanProfile_rankOne_two_pow_mul (i : ℕ) {u : ℤ} (hu : Odd u) :
    (rankOne (2 ^ i * u)).dyadicJordanProfile.densityExponent = i + 1 := by
  rw [dyadicJordanProfile_rankOne_two_pow_mul i hu, DyadicJordanProfile.densityExponent_unaryTypeI]

/-- The lattice `⟨1⟩` has dyadic density exponent `1`. -/
theorem densityExponent_dyadicJordanProfile_rankOne_one :
    (rankOne 1).dyadicJordanProfile.densityExponent = 1 := by
  simpa using densityExponent_dyadicJordanProfile_rankOne_two_pow_mul 0 odd_one

/-- The lattice `⟨2⟩` has dyadic density exponent `2`: it is a type I constituent of scale `2`,
although all its self-pairings are even. -/
theorem densityExponent_dyadicJordanProfile_rankOne_two :
    (rankOne 2).dyadicJordanProfile.densityExponent = 2 := by
  simpa using densityExponent_dyadicJordanProfile_rankOne_two_pow_mul 1 odd_one

end TauCeti.IntegralLattice

end
