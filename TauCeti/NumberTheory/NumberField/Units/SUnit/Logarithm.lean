/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit
public import TauCeti.NumberTheory.NumberField.Global.Places.Basic

/-!
# The logarithmic map of S-units

For a set `S` of finite places of a number field, `sUnitLog` sends an S-unit to the logarithms
of its normalized absolute values at `S` and at every infinite place. Complex places have
weight two. Keeping every infinite coordinate makes the map independent of a distinguished
place, as needed when studying the Galois action on unit lattices.

For `u : S.unit K`, apply the map as `TauCeti.sUnitLog S (.ofMul u)`; its coordinate equations
are `TauCeti.sUnitLog_inl S u` and `TauCeti.sUnitLog_inr S u`.

The kernel is exactly the torsion subgroup, and is finite. For finite `S`, the product formula
puts the image in the hyperplane where the sum of coordinates is zero. These are the kernel
and ambient-space calculations for the S-unit logarithmic lattice; discreteness and spanning
of that hyperplane are separate assertions.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §4 (S-unit logarithmic lattices).

The kernel calculation uses Mathlib's `NumberField.Units.mem_torsion`; the hyperplane equation
uses `finprod_normalizedAbsValue_eq_one`.
-/

public noncomputable section

open IsDedekindDomain NumberField TauCeti.GlobalNumberFields
open scoped NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The logarithmic map of S-units, with all infinite places retained and complex places
weighted twice. The finite coordinates are indexed only by the allowed primes. -/
def sUnitLog : Additive (S.unit K) →+ ((S ⊕ InfinitePlace K) → ℝ) where
  toFun u p := Real.log (normalizedAbsValue (Sum.map Subtype.val id p) (u.toMul : Kˣ))
  map_zero' := by ext p; simp
  map_add' u v := by
    ext p
    simp only [toMul_add, Subgroup.coe_mul, Units.val_mul, map_mul, Pi.add_apply]
    exact Real.log_mul (normalizedAbsValue_pos _ (Units.ne_zero (u.toMul : Kˣ))).ne'
      (normalizedAbsValue_pos _ (Units.ne_zero (v.toMul : Kˣ))).ne'

/-- The finite coordinate of the S-unit logarithmic map. -/
@[simp]
theorem sUnitLog_inl (u : S.unit K) (v : S) :
    sUnitLog S (.ofMul u) (.inl v) = Real.log (normalizedAbsValue (.inl v.val) (u : Kˣ)) :=
  (rfl)

/-- The infinite coordinate is the logarithm weighted by the place's multiplicity. -/
@[simp]
theorem sUnitLog_inr (u : S.unit K) (w : InfinitePlace K) :
    sUnitLog S (.ofMul u) (.inr w) = w.mult * Real.log (w (u : Kˣ)) := by
  simp [sUnitLog, Real.log_pow]

private theorem exists_torsionUnit_of_sUnitLog_eq_zero (u : S.unit K)
    (hu : sUnitLog S (.ofMul u) = 0) :
    ∃ a : NumberField.Units.torsion K, (a.val : K) = (u : Kˣ) := by
  have hfinite (v : HeightOneSpectrum (𝓞 K)) : v.valuation K (u : Kˣ) = 1 := by
    by_cases hv : v ∈ S
    · have h := congrFun hu (.inl ⟨v, hv⟩)
      have hp := normalizedAbsValue_pos (.inl v) (Units.ne_zero (u : Kˣ))
      have habs : normalizedAbsValue (.inl v) (u : Kˣ) = 1 := by
        have hz : Real.log (normalizedAbsValue (.inl v) (u : Kˣ)) = 0 := by
          simpa using h
        exact Real.eq_one_of_pos_of_log_eq_zero hp hz
      exact (normalizedAbsValue_inl_eq_one_iff v _).mp habs
    · exact Set.unit_valuation_eq_one S K u hv
  let a := Set.unitEmptyEquivUnits K
    ⟨(u : Kˣ), (Set.mem_unit_iff _ _).mpr fun v _ => hfinite v⟩
  have ha : (a : K) = (u : Kˣ) := Set.algebraMap_unitEmptyEquivUnits_apply K _
  refine ⟨⟨a, (NumberField.Units.mem_torsion K).mpr fun w => ?_⟩, ha⟩
  apply NumberField.Units.dirichletUnitTheorem.mult_log_place_eq_zero.mp
  rw [ha]
  simpa using congrFun hu (.inr w)

/-- An S-unit has zero logarithmic vector exactly when it has finite multiplicative order. -/
@[simp]
theorem sUnitLog_eq_zero_iff (u : S.unit K) :
    sUnitLog S (.ofMul u) = 0 ↔ IsOfFinOrder u := by
  constructor
  · intro hu
    obtain ⟨a, ha⟩ := exists_torsionUnit_of_sUnitLog_eq_zero S u hu
    have h := ((algebraMap (𝓞 K) K).toMonoidHom.comp (Units.coeHom (𝓞 K))).isOfFinOrder
      ((CommGroup.mem_torsion a.val).mp a.property)
    have huK : IsOfFinOrder ((u : Kˣ) : K) := ha ▸ h
    exact (Function.Injective.isOfFinOrder_iff
      (f := (Units.coeHom K).comp (S.unit K).subtype)
      (Units.val_injective.comp (S.unit K).subtype_injective)).mp huK
  · intro hu
    exact (isOfFinAddOrder_iff_eq_zero _).mp
      ((sUnitLog S).isOfFinAddOrder (isOfFinAddOrder_ofMul_iff.mpr hu))

/-- The kernel of the logarithmic map is the additive torsion subgroup of the S-units. -/
theorem sUnitLog_ker :
    (sUnitLog S).ker = AddCommGroup.torsion (Additive (S.unit K)) := by
  ext u
  rw [AddMonoidHom.mem_ker, AddCommGroup.mem_torsion, ← ofMul_toMul u,
    isOfFinAddOrder_ofMul_iff]
  exact sUnitLog_eq_zero_iff S u.toMul

/-- The S-unit logarithmic map has finite kernel, even if the set of allowed primes is infinite. -/
instance finite_ker_sUnitLog : Finite (sUnitLog S).ker := by
  let f : (sUnitLog S).ker → NumberField.Units.torsion K := fun u =>
    (exists_torsionUnit_of_sUnitLog_eq_zero S u.val.toMul u.property).choose
  have hf (u : (sUnitLog S).ker) : ((f u).val : K) = (u.val.toMul : Kˣ) :=
    (exists_torsionUnit_of_sUnitLog_eq_zero S u.val.toMul u.property).choose_spec
  apply Finite.of_injective f
  intro u v h
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.val_injective
  exact (hf u).symm.trans ((congrArg (fun a : NumberField.Units.torsion K =>
    (a.val : K)) h).trans (hf v))

/-- For finite S, the coordinates of the S-unit logarithmic vector sum to zero. -/
-- This is an explicit rewrite lemma: `simp` first splits sums over a disjoint union.
theorem sum_sUnitLog_eq_zero [Fintype S] (u : S.unit K) :
    ∑ p : S ⊕ InfinitePlace K, sUnitLog S (.ofMul u) p = 0 := by
  classical
  have hprod : (∏ v : S, normalizedAbsValue (.inl v.val) (u : Kˣ)) *
      (∏ w : InfinitePlace K, normalizedAbsValue (.inr w) (u : Kˣ)) = 1 := by
    have hs : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
        normalizedAbsValue (.inl v) (u : Kˣ)) ⊆ S := by
      intro v hv
      by_contra h
      exact hv ((normalizedAbsValue_inl_eq_one_iff v _).mpr
        (Set.unit_valuation_eq_one S K u h))
    have heq : (∏ v : S, normalizedAbsValue (.inl v.val) (u : Kˣ)) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), normalizedAbsValue (.inl v) (u : Kˣ) := by
      rw [← finprod_eq_prod_of_fintype,
        finprod_set_coe_eq_finprod_mem (f := fun v =>
          normalizedAbsValue (.inl v) ((u : Kˣ) : K)) S]
      exact (finprod_mem_inter_mulSupport_eq _ S Set.univ (by
        ext v
        simp only [Set.mem_inter_iff, Set.mem_univ, true_and]
        exact and_iff_right_of_imp (fun hv => hs hv))).trans (finprod_mem_univ _)
    rw [heq]
    have h := finprod_normalizedAbsValue_eq_one (K := K) (Units.ne_zero (u : Kˣ))
    rw [TauCeti.finprod_sum_type _ (by
      simpa [Function.comp_def] using hasFiniteMulSupport_adicAbv (Units.ne_zero (u : Kˣ)))
      (Set.toFinite _), finprod_eq_prod_of_fintype
        (fun w : InfinitePlace K => normalizedAbsValue (.inr w) ((u : Kˣ) : K))] at h
    exact h
  have h := congrArg Real.log hprod
  rw [Real.log_mul (Finset.prod_ne_zero_iff.mpr fun v _ =>
      (normalizedAbsValue_pos _ (Units.ne_zero (u : Kˣ))).ne')
    (Finset.prod_ne_zero_iff.mpr fun w _ =>
      (normalizedAbsValue_pos _ (Units.ne_zero (u : Kˣ))).ne'),
    Real.log_prod (fun v _ => (normalizedAbsValue_pos _ (Units.ne_zero (u : Kˣ))).ne'),
    Real.log_prod (fun w _ => (normalizedAbsValue_pos _ (Units.ne_zero (u : Kˣ))).ne'),
    Real.log_one] at h
  simpa [Fintype.sum_sum_type, sUnitLog, Real.log_pow] using h

end TauCeti
