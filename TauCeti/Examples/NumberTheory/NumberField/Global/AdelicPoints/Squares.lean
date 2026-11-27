/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits

/-!
# The squaring map on the ideles of `ℚ`

The squaring map `x ↦ x²` of `𝔾ₘ` induces on adelic points the squaring map of the ideles `𝔸_ℚ^×`.
Its image `(𝔸_ℚ^×)²` is not open, and has infinite index. At every odd prime `p` there is a unit
`u_p ∈ ℤ_p^×` that is not a square in `ℚ_p` (a lift of a quadratic nonresidue modulo `p`,
`IsDedekindDomain.HeightOneSpectrum.exists_unit_not_isSquare`). Every open subgroup of the ideles
contains, at almost every prime, the units of `ℚ_p` embedded at that single place
(`eventually_unitsOfAdicCompletion_mem_of_isOpen`), so it contains a nonsquare idele; and the ideles
concentrated at distinct odd primes with value `u_p` lie in distinct cosets of the squares. So the
adelic squaring map is neither surjective nor open. The ideles are the adelic points of `𝔾ₘ`
(`TauCeti.MultiplicativeGroup.pointsContinuousMulEquiv`), and squaring on them is the map induced by
`x ↦ x²`.

## Main results

* `TauCeti.Examples.AdelicSquares.not_isOpen_range_sq`: `(𝔸_ℚ^×)²` is not open.
* `TauCeti.Examples.AdelicSquares.not_finiteIndex_range_sq`: `(𝔸_ℚ^×)²` has infinite index.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField Rat.HeightOneSpectrum

namespace TauCeti.Examples.AdelicSquares

/-- The places of `ℚ` at the prime `2`: a single place. -/
theorem finite_setOf_primesEquiv_eq_two :
    {v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) = 2}.Finite :=
  (Set.finite_singleton (primesEquiv.symm ⟨2, Nat.prime_two⟩)).subset fun _ hv ↦
    (Equiv.eq_symm_apply _).2 (Subtype.ext hv)

/-- At the place `v` of `ℚ` of an odd prime `p`, there is a unit of `ℚ_p` of valuation one which
is not a square: the image of a unit of `ℤ_p` that is not a square in `ℚ_p`
(`HeightOneSpectrum.exists_unit_not_isSquare`). -/
theorem exists_valued_eq_one_not_isSquare (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (primesEquiv v : ℕ) ≠ 2) :
    ∃ u : (v.adicCompletion ℚ)ˣ, Valued.v (u : v.adicCompletion ℚ) = 1 ∧
      ¬IsSquare (u : v.adicCompletion ℚ) := by
  have : Finite (𝓞 ℚ ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  -- `2 ∈ v` would make the prime of `v` divide `2`
  have h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal := fun hmem ↦ hv <|
    (Nat.prime_dvd_prime_iff_eq (primesEquiv v).property Nat.prime_two).1 <| by
      change natGenerator v ∣ 2
      rw [natGenerator_dvd_iff, Nat.cast_ofNat, ← map_ofNat (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))]
      exact Ideal.mem_map_of_mem _ hmem
  obtain ⟨c, hc⟩ := v.exists_unit_not_isSquare (K := ℚ) h2
  exact ⟨Units.map (algebraMap _ _).toMonoidHom c,
    (HeightOneSpectrum.adicCompletionIntegers.integers ℚ v).valuation_unit c, hc⟩

/-- An idele of `ℚ` concentrated at the single place `v` with value `u` is a square only if `u` is
a square in `ℚ_v`. -/
theorem isSquare_of_isSquare_ofFiniteIdele {v : HeightOneSpectrum (𝓞 ℚ)}
    {u : (v.adicCompletion ℚ)ˣ}
    (h : IsSquare (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ (unitsOfAdicCompletion ℚ v u))) :
    IsSquare (u : v.adicCompletion ℚ) := by
  obtain ⟨y, hy⟩ := h
  have := congrArg v.ideleFiniteCoord hy
  rw [HeightOneSpectrum.ideleFiniteCoord_ofFiniteIdele, unitsProj_unitsOfAdicCompletion,
    map_mul] at this
  exact ⟨_, by rw [this, Units.val_mul]⟩

/-- **The squares are not open in the ideles of `ℚ`.** -/
theorem not_isOpen_range_sq :
    ¬IsOpen ((powMonoidHom 2 : IdeleGroup (𝓞 ℚ) ℚ →* IdeleGroup (𝓞 ℚ) ℚ).range :
      Set (IdeleGroup (𝓞 ℚ) ℚ)) := by
  intro hS
  let H := (powMonoidHom 2 : IdeleGroup (𝓞 ℚ) ℚ →* IdeleGroup (𝓞 ℚ) ℚ).range.comap
    (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ)
  have hH : IsOpen (H : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    hS.preimage (IdeleGroup.continuous_ofFiniteIdele (𝓞 ℚ) ℚ)
  obtain ⟨v, hv, hodd⟩ := ((eventually_unitsOfAdicCompletion_mem_of_isOpen hH).and
    finite_setOf_primesEquiv_eq_two.eventually_cofinite_notMem).exists
  obtain ⟨u, hu1, hu⟩ := exists_valued_eq_one_not_isSquare v hodd
  obtain ⟨y, hy⟩ := hv u hu1
  exact hu (isSquare_of_isSquare_ofFiniteIdele ⟨y, by simpa [sq] using hy.symm⟩)

/-- **The squares have infinite index in the ideles of `ℚ`.** -/
theorem not_finiteIndex_range_sq :
    ¬(powMonoidHom 2 : IdeleGroup (𝓞 ℚ) ℚ →* IdeleGroup (𝓞 ℚ) ℚ).range.FiniteIndex := by
  intro hfin
  -- For each odd prime choose a nonsquare unit at that prime; the ideles concentrated there lie in
  -- pairwise distinct cosets of the squares.
  let P := ({v : HeightOneSpectrum (𝓞 ℚ) | (primesEquiv v : ℕ) = 2}ᶜ : Set _)
  have : Infinite P := finite_setOf_primesEquiv_eq_two.infinite_compl.to_subtype
  choose u _ hu using fun w : P ↦ exists_valued_eq_one_not_isSquare w.val w.property
  let e : P → IdeleGroup (𝓞 ℚ) ℚ ⧸
      (powMonoidHom 2 : IdeleGroup (𝓞 ℚ) ℚ →* IdeleGroup (𝓞 ℚ) ℚ).range :=
    fun w ↦ QuotientGroup.mk
      (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ (unitsOfAdicCompletion ℚ w.val (u w)))
  have he : Function.Injective e := by
    intro w w' h
    by_contra hne
    have hne' : w.val ≠ w'.val := fun h ↦ hne (Subtype.ext h)
    obtain ⟨y, hy⟩ := QuotientGroup.eq.1 h
    -- The coordinate at `w` of the quotient is `(u w)⁻¹`, which would be a square.
    have := congrArg w.val.ideleFiniteCoord hy
    simp only [powMonoidHom_apply, map_pow, map_mul, map_inv,
      HeightOneSpectrum.ideleFiniteCoord_ofFiniteIdele, unitsProj_unitsOfAdicCompletion,
      unitsProj_unitsOfAdicCompletion_of_ne hne', mul_one] at this
    refine hu w ⟨((w.val.ideleFiniteCoord y)⁻¹ : (w.val.adicCompletion ℚ)ˣ), ?_⟩
    rw [← Units.val_mul, ← mul_inv, ← sq, this, inv_inv]
  have : Finite P := Finite.of_injective e he
  exact not_finite P

end TauCeti.Examples.AdelicSquares
