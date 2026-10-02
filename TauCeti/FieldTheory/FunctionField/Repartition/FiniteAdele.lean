/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Indicator
public import TauCeti.FieldTheory.FunctionField.Place.Adic
public import TauCeti.FieldTheory.FunctionField.Repartition.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Repartitions and the finite adeles of an affine model

For a Dedekind `k`-algebra `R` with fraction field `F`, a repartition of `F / k` gives a
finite adele of `R`: retain the entries at the adic places of `R` and embed each into its
adic completion. This map forgets the places outside the affine chart. Its kernel consists
exactly of repartitions vanishing on that chart, and it preserves the valuation bounds
defining the divisor filtration.

Every finite adele can be approximated to any divisor bound by the image of a finitely
supported repartition. This is the comparison between repartitions with entries in `F`
and completion-valued adeles; it imposes no restriction on the residue fields. In particular
the comparison map has dense image in the restricted product topology.

The approximation uses the existing strong approximation theorem for finite adeles,
`IsDedekindDomain.FiniteAdeleRing.exists_forall_valued_sub_le_and_forall_valued_sub_le_one`,
followed by truncation to the finitely many exceptional coordinates.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.5 and I.7
  (repartitions and local components).
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II,
  Sections 14–15 (completion-valued adeles).
-/

public section

open IsDedekindDomain WithZero

namespace TauCeti

open AlgebraicGeometry

variable {k F R : Type*} [Field k] [Field F] [CommRing R] [IsDedekindDomain R]
  [Algebra k R] [Algebra R F] [IsFractionRing R F] [Algebra k F] [IsScalarTower k R F]

variable (R) in
/-- Restriction of a repartition to an affine chart, followed by the embeddings into the
adic completions. The omitted places, such as the places at infinity, are forgotten. -/
noncomputable def repartitionToFiniteAdeles : repartitionSpace k F →+ FiniteAdeleRing R F where
  toFun b := ⟨fun p ↦ algebraMap F (p.adicCompletion F) (b.1 (Place.adic k F p)), by
    have hb := mem_repartitionSpace_iff_finite.mp b.2
    have hfin := hb.preimage (Place.adic_injective k F (R := R)).injOn
    simpa only [Filter.eventually_cofinite, SetLike.mem_coe, Set.preimage_ofPred_eq,
      HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      Place.valuation_adic] using hfin⟩
  map_zero' := FiniteAdeleRing.ext F fun p ↦
    map_zero (algebraMap F (p.adicCompletion F))
  map_add' b c := FiniteAdeleRing.ext F fun p ↦
    map_add (algebraMap F (p.adicCompletion F)) _ _

/-- The comparison map is computed separately at each finite place. -/
@[simp]
theorem repartitionToFiniteAdeles_apply (b : repartitionSpace k F) (p : HeightOneSpectrum R) :
    repartitionToFiniteAdeles R b p =
      algebraMap F (p.adicCompletion F) (b.1 (Place.adic k F p)) :=
  (rfl)

/-- Scalar multiplication is preserved, with constants embedded diagonally in the finite
adeles. This formula does not require choosing a separate constant-field algebra instance
on the finite adele ring. -/
theorem repartitionToFiniteAdeles_smul (c : k) (b : repartitionSpace k F) :
    repartitionToFiniteAdeles R (c • b) =
      algebraMap F (FiniteAdeleRing R F) (algebraMap k F c) * repartitionToFiniteAdeles R b := by
  apply FiniteAdeleRing.ext F
  intro p
  simp only [repartitionToFiniteAdeles_apply, Submodule.coe_smul, Pi.smul_apply,
    Algebra.smul_def, map_mul, FiniteAdeleRing.mul_apply, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]

/-- The comparison preserves the value of each retained entry. -/
theorem valued_repartitionToFiniteAdeles (b : repartitionSpace k F) (p : HeightOneSpectrum R) :
    Valued.v (repartitionToFiniteAdeles R b p) =
      (Place.adic k F p).valuation (b.1 (Place.adic k F p)) := by
  simp only [repartitionToFiniteAdeles_apply, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    Place.valuation_adic]

/-- The kernel consists exactly of the repartitions vanishing at every place on the
affine chart. Thus the map can have a kernel even though each local embedding is injective. -/
@[simp]
theorem repartitionToFiniteAdeles_eq_zero_iff (b : repartitionSpace k F) :
    repartitionToFiniteAdeles R b = 0 ↔ ∀ p : HeightOneSpectrum R, b.1 (Place.adic k F p) = 0 := by
  constructor
  · intro h p
    have hp := congrArg (fun a : FiniteAdeleRing R F ↦ a p) h
    simpa only [repartitionToFiniteAdeles_apply, FiniteAdeleRing.zero_apply,
      map_eq_zero] using hp
  · intro h
    apply FiniteAdeleRing.ext F
    intro p
    simp only [repartitionToFiniteAdeles_apply, h p, map_zero, FiniteAdeleRing.zero_apply]

/-- A diagonal repartition maps to the diagonal finite adele of the same function. -/
@[simp]
theorem repartitionToFiniteAdeles_const (hF : IsFunctionField k F) (f : F) :
    repartitionToFiniteAdeles R ⟨Function.const (Place k F) f, const_mem_repartitionSpace hF f⟩ =
      algebraMap F (FiniteAdeleRing R F) f := by
  apply FiniteAdeleRing.ext F
  intro p
  simp only [repartitionToFiniteAdeles_apply, Function.const_apply,
    HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply,
    FiniteAdeleRing.algebraMap_apply]

/-- A divisor bound on a repartition remains the same bound at each completed finite place. -/
theorem repartitionToFiniteAdeles_valuation_le {D : Divisor k F} {b : repartitionSpace k F}
    (hb : b.1 ∈ adeleFiltration D) (p : HeightOneSpectrum R) :
    Valued.v (repartitionToFiniteAdeles R b p) ≤ exp (D.coeff (Place.adic k F p)) := by
  rw [valued_repartitionToFiniteAdeles]
  exact (mem_adeleFiltration_iff.mp hb) (Place.adic k F p)

/-- **Approximation to every divisor bound by finitely supported repartitions.** For a
finite adele `a` and any divisor `D`, there is a repartition `b` with finite support such
that the error at each finite place `P` has valuation at most `exp (D P)`.

The bound is multiplicative, so it includes zero errors even at negative coefficients
of `D`. No function-field, exact-constants, or perfectness hypothesis is needed. -/
theorem exists_finite_support_repartition_valuation_sub_le (a : FiniteAdeleRing R F)
    (D : Divisor k F) :
    ∃ b : repartitionSpace k F, (Function.support b.1).Finite ∧
      ∀ p : HeightOneSpectrum R,
        Valued.v (repartitionToFiniteAdeles R b p - a p) ≤ exp (D.coeff (Place.adic k F p)) := by
  classical
  let S : Set (HeightOneSpectrum R) :=
    (Place.adic k F) ⁻¹' (D.support : Set (Place k F)) ∪ {p | 1 < Valued.v (a p)}
  have hS : S.Finite :=
    (D.support.finite_toSet.preimage (Place.adic_injective k F).injOn).union a.finite_valued_one_lt
  obtain ⟨x, hx, -⟩ :=
    FiniteAdeleRing.exists_forall_valued_sub_le_and_forall_valued_sub_le_one a hS.toFinset
      (fun p ↦ (-D.coeff (Place.adic k F p)).toNat)
  let T : Set (Place k F) := Place.adic k F '' S
  let b : Place k F → F := T.indicator (Function.const _ x)
  have hb : (Function.support b).Finite :=
    (hS.image (Place.adic k F)).subset Set.support_indicator_subset
  have hbmem : b ∈ repartitionSpace k F := by
    apply mem_repartitionSpace_iff_finite.mpr
    exact hb.subset fun P hP ↦ by
      by_contra hzero
      exact hP (by simp [Function.notMem_support.mp hzero])
  refine ⟨⟨b, hbmem⟩, hb, fun p ↦ ?_⟩
  have hpT : Place.adic k F p ∈ T ↔ p ∈ S :=
    (Place.adic_injective k F).mem_set_image
  by_cases hp : p ∈ S
  · have hbx : b (Place.adic k F p) = x := by
      simp [b, Set.indicator_of_mem (hpT.mpr hp)]
    simp only [repartitionToFiniteAdeles_apply, hbx]
    exact (hx p (hS.mem_toFinset.mpr hp)).trans
      (exp_le_exp.mpr (by omega))
  · have hbzero : b (Place.adic k F p) = 0 := by
      simp [b, Set.indicator_of_notMem (mt hpT.mp hp)]
    have hD : D.coeff (Place.adic k F p) = 0 := by
      apply Finsupp.notMem_support_iff.mp
      exact fun h ↦ hp (Or.inl h)
    have ha : Valued.v (a p) ≤ 1 := le_of_not_gt fun h ↦ hp (Or.inr h)
    simpa only [repartitionToFiniteAdeles_apply, Submodule.coe_mk, hbzero, map_zero,
      zero_sub, Valuation.map_neg, hD, exp_zero] using ha

/-- Repartitions have dense image in the finite adeles of every Dedekind affine model.
This holds even without a function-field hypothesis. -/
theorem denseRange_repartitionToFiniteAdeles :
    DenseRange (repartitionToFiniteAdeles R (k := k) (F := F)) := by
  classical
  intro a
  refine mem_closure_iff_nhds.mpr fun U hU ↦ ?_
  have hU0 : (a + ·) ⁻¹' U ∈ nhds (0 : FiniteAdeleRing R F) :=
    (continuous_const_add a).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  obtain ⟨I, n, hIn⟩ := FiniteAdeleRing.exists_finset_forall_mem_of_mem_nhds_zero hU0
  let D : Divisor k F := Finsupp.mapDomain (Place.adic k F)
    (Finsupp.indicator I fun p _ ↦ -(n p : ℤ))
  have hD (p : HeightOneSpectrum R) :
      D.coeff (Place.adic k F p) = if p ∈ I then -(n p : ℤ) else 0 := by
    simp [D, WeilDivisor.coeff, Finsupp.mapDomain_apply_of_injective
      (Place.adic_injective k F), Finsupp.indicator_apply]
  obtain ⟨b, -, hb⟩ := exists_finite_support_repartition_valuation_sub_le a D
  have hmem := hIn (repartitionToFiniteAdeles R b - a)
    (fun p ↦ by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.sub_apply]
      exact (hb p).trans (exp_le_one_iff.mpr (by rw [hD]; split <;> omega)))
    (fun p hp ↦ by
      rw [FiniteAdeleRing.sub_apply]
      simpa only [hD, ite_eq_left hp] using hb p)
  refine ⟨repartitionToFiniteAdeles R b, ?_, b, rfl⟩
  simpa only [Set.mem_preimage, add_sub_cancel] using hmem

end TauCeti
