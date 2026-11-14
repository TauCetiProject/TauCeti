/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis

import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Artinian.Module

/-!
# Spectral norms on finite reduced algebras

Let `K` be an ultrametric normed field and `E` a finite reduced commutative `K`-algebra. Because `E`
is Artinian and reduced, `IsArtinianRing.equivPi` decomposes `E` into the finite product of its
residue fields `E ⧸ m` over `m : MaximalSpectrum E`, each of which is a finite field extension of
`K`.

This file shows that for every `x : E`, the spectral value `spectralValue (minpoly K x)` equals the
supremum over `m : MaximalSpectrum E` of `spectralNorm K (E ⧸ m.asIdeal)` on the residue of `x`, and
bundles `x ↦ spectralValue (minpoly K x)` into a power-multiplicative nonarchimedean `K`-algebra
norm `TauCeti.reducedSpectralAlgNorm K E`. Over a weakly stable field `K`, every `K`-linear
functional on `E` is bounded by `reducedSpectralAlgNorm K E`, and `reducedSpectralAlgNorm K E` is
equivalent to every finite-basis coordinate norm `b.norm`.

No completeness or nontriviality of the valuation on `K` is assumed. This supplies the
fraction-field tensor-product algebra norm in Bosch–Güntzer–Remmert, §3.8.3, Theorem 7, without
restricting `E` to be a field.

## Main definitions

* `TauCeti.reducedSpectralAlgNorm K E`: the `K`-algebra norm `x ↦ spectralValue (minpoly K x)` on a
  finite reduced commutative `K`-algebra `E`.

## Main results

* `Polynomial.Monic.spectralValue_mul` and `Polynomial.Monic.spectralValue_le_of_dvd`: over an
  ultrametric normed field, `spectralValue (p * q) = max (spectralValue p) (spectralValue q)` for
  monic polynomials, so monic divisors have smaller `spectralValue`.
* `TauCeti.spectralValue_minpoly_eq_iSup_spectralNorm`: `spectralValue (minpoly K x)` is the
  supremum of the residue-field spectral norms across `MaximalSpectrum E`.
* `TauCeti.isPowMul_reducedSpectralAlgNorm` and `TauCeti.isNonarchimedean_reducedSpectralAlgNorm`:
  power-multiplicativity and ultrametricity of `reducedSpectralAlgNorm K E`.
* `TauCeti.IsWeaklyStable.exists_bound_reducedSpectralAlgNorm` and
  `TauCeti.IsWeaklyStable.exists_basis_reducedSpectralAlgNorm_comparison`: over a weakly stable
  field `K`, linear functionals and basis coordinate norms on `E` are controlled by
  `reducedSpectralAlgNorm K E`.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.1.2, 3.2.1, 3.5.1, and 3.8.3.
-/

public section

open Polynomial

namespace Polynomial

/-- The constant polynomial `1` over a nontrivial seminormed ring has spectral value `0`. -/
@[simp]
theorem spectralValue_one {R : Type*} [SeminormedRing R] [Nontrivial R] :
    spectralValue (1 : R[X]) = 0 := by
  simpa using spectralValue_X_pow (R := R) 0

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

open scoped Classical in
/-- Expresses `spectralValue p` for a monic polynomial `p : K[X]` as the maximum of
`spectralAlgNorm` over the roots of `p` in `AlgebraicClosure K`. -/
private theorem monic_spectralValue_eq_iSup_roots {p : K[X]} (hp : p.Monic) :
    (⨆ x : AlgebraicClosure K,
      if x ∈ (mapAlg K (AlgebraicClosure K) p).roots then
        spectralAlgNorm K (AlgebraicClosure K) x
      else 0) = spectralValue p := by
  let L := AlgebraicClosure K
  have hmap : mapAlg K L p = ((mapAlg K L p).roots.map fun a : L ↦ X - C a).prod := by
    have hmon : (mapAlg K L p).Monic := by
      rw [mapAlg_eq_map]
      exact hp.map _
    exact (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (IsAlgClosed.splits (mapAlg K L p)).natDegree_eq_card_roots.symm).symm
  exact max_norm_root_eq_spectralValue spectralAlgNorm_isPowMul
    isNonarchimedean_spectralNorm spectralAlgNorm_one p _ hmap

/-- Over an ultrametric normed field, the spectral value of a product of two monic polynomials is
the maximum of their spectral values. -/
theorem Monic.spectralValue_mul {p q : K[X]} (hp : p.Monic) (hq : q.Monic) :
    spectralValue (p * q) = max (spectralValue p) (spectralValue q) := by
  classical
  let L := AlgebraicClosure K
  let f : AlgebraNorm K L := spectralAlgNorm K L
  have hp0 : mapAlg K L p ≠ 0 := by
    rw [mapAlg_eq_map]
    exact (hp.map _).ne_zero
  have hq0 : mapAlg K L q ≠ 0 := by
    rw [mapAlg_eq_map]
    exact (hq.map _).ne_zero
  have hroots : (mapAlg K L (p * q)).roots = (mapAlg K L p).roots + (mapAlg K L q).roots := by
    rw [map_mul, roots_mul (mul_ne_zero hp0 hq0)]
  rw [← monic_spectralValue_eq_iSup_roots (hp.mul hq), ← monic_spectralValue_eq_iSup_roots hp,
    ← monic_spectralValue_eq_iSup_roots hq]
  have hbdd (r : K[X]) (hr : r.Monic) : BddAbove
      (Set.range fun x : L ↦ if x ∈ (mapAlg K L r).roots then f x else 0) := by
    refine ⟨spectralValue r, ?_⟩
    rintro _ ⟨x, rfl⟩
    dsimp only
    split_ifs with hx
    · have hxr : aeval x r = 0 := by
        have h0 := (mem_roots (by rw [mapAlg_eq_map]; exact (hr.map _).ne_zero)).mp hx
        rwa [mapAlg_eq_map, IsRoot.def, eval_map_algebraMap] at h0
      exact norm_root_le_spectralValue spectralAlgNorm_isPowMul isNonarchimedean_spectralNorm hr hxr
    · exact spectralValue_nonneg r
  have hterm (x : L) :
      (if x ∈ (mapAlg K L (p * q)).roots then f x else 0) =
        max (if x ∈ (mapAlg K L p).roots then f x else 0)
          (if x ∈ (mapAlg K L q).roots then f x else 0) := by
    have hfx : 0 ≤ f x := apply_nonneg f x
    simp only [hroots, Multiset.mem_add]
    by_cases hxp : x ∈ (mapAlg K L p).roots <;> by_cases hxq : x ∈ (mapAlg K L q).roots <;>
      simp [hxp, hxq, hfx]
  refine le_antisymm (ciSup_le fun x ↦ ?_) (max_le (ciSup_le fun x ↦ ?_) (ciSup_le fun x ↦ ?_))
  · rw [hterm x]
    exact max_le_max (le_ciSup (hbdd p hp) x) (le_ciSup (hbdd q hq) x)
  · exact (le_max_left _ _).trans ((hterm x).symm.trans_le (le_ciSup (hbdd (p * q) (hp.mul hq)) x))
  · exact (le_max_right _ _).trans ((hterm x).symm.trans_le (le_ciSup (hbdd (p * q) (hp.mul hq)) x))

/-- Over an ultrametric normed field, if a monic polynomial `p` divides a monic polynomial `q`,
then `spectralValue p ≤ spectralValue q`. -/
theorem Monic.spectralValue_le_of_dvd {p q : K[X]} (hp : p.Monic) (hq : q.Monic) (hdvd : p ∣ q) :
    spectralValue p ≤ spectralValue q := by
  obtain ⟨r, rfl⟩ := hdvd
  have hr : r.Monic := hp.of_mul_monic_left hq
  rw [hp.spectralValue_mul hr]
  exact le_max_left _ _

/-- Over an ultrametric normed field, a uniform upper bound `r ≥ 0` on the spectral values of monic
polynomials bounds the spectral value of their product. -/
theorem Monic.spectralValue_prod_le {ι : Type*} {s : Finset ι} {f : ι → K[X]}
    (hf : ∀ i ∈ s, (f i).Monic) {r : ℝ} (hr : 0 ≤ r)
    (hle : ∀ i ∈ s, spectralValue (f i) ≤ r) :
    spectralValue (∏ i ∈ s, f i) ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    have hfa : (f a).Monic := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, (f i).Monic := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, hfa.spectralValue_mul (monic_prod_of_monic s f hfs)]
    exact max_le (hle a (Finset.mem_insert_self a s))
      (ih hfs fun i hi ↦ hle i (Finset.mem_insert_of_mem hi))

end NormedField

end Polynomial

namespace TauCeti

section ReducedAlgebra

variable {K E : Type*} [NormedField K] [CommRing E] [Algebra K E]

private noncomputable local instance instFieldQuotient (m : MaximalSpectrum E) :
    Field (E ⧸ m.asIdeal) :=
  Ideal.Quotient.field m.asIdeal

private theorem finiteDimensional_quotient [Module.Finite K E] (m : MaximalSpectrum E) :
    FiniteDimensional K (E ⧸ m.asIdeal) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

private theorem iSup_quotient_spectralNorm_nonneg (x : E) :
    0 ≤ ⨆ m : MaximalSpectrum E, spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) :=
  Real.iSup_nonneg fun _ ↦ spectralNorm_nonneg _

private theorem spectralNorm_quotient_le_iSup [Finite (MaximalSpectrum E)] (x : E)
    (m : MaximalSpectrum E) :
    spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) ≤
      ⨆ n : MaximalSpectrum E,
        spectralNorm K (E ⧸ n.asIdeal) (Ideal.Quotient.mk n.asIdeal x) :=
  le_ciSup (f := fun n : MaximalSpectrum E ↦
    spectralNorm K (E ⧸ n.asIdeal) (Ideal.Quotient.mk n.asIdeal x))
    (Set.finite_range _).bddAbove m

variable [IsUltrametricDist K] [IsReduced E] [Module.Finite K E]

/-- **Residue-field formula for the spectral value of a minimal polynomial.** In a finite reduced
commutative `K`-algebra `E` over an ultrametric normed field `K`, `spectralValue (minpoly K x)` is
the supremum over `m : MaximalSpectrum E` of the spectral norm of `x mod m` in `E ⧸ m`. -/
theorem spectralValue_minpoly_eq_iSup_spectralNorm (x : E) :
    spectralValue (minpoly K x) =
      ⨆ m : MaximalSpectrum E,
        letI := Ideal.Quotient.field m.asIdeal
        spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) := by
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  let _ : Fintype (MaximalSpectrum E) := Fintype.ofFinite (MaximalSpectrum E)
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hxm (m : MaximalSpectrum E) : IsIntegral K (Ideal.Quotient.mk m.asIdeal x) :=
    hx.map (Ideal.Quotient.mkₐ K m.asIdeal)
  set r := ⨆ m : MaximalSpectrum E,
    spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x)
  refine le_antisymm ?_ ?_
  · let Q : K[X] := ∏ m : MaximalSpectrum E, minpoly K (Ideal.Quotient.mk m.asIdeal x)
    have hQ_monic : Q.Monic := monic_prod_of_monic _ _ fun m _ ↦ minpoly.monic (hxm m)
    have hQ_aeval : aeval x Q = 0 := by
      apply (IsArtinianRing.equivPi E).injective
      ext m
      rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply,
        ← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, ← aeval_algHom_apply]
      obtain ⟨R, hR⟩ := Finset.dvd_prod_of_mem
        (fun n : MaximalSpectrum E ↦ minpoly K (Ideal.Quotient.mk n.asIdeal x))
        (Finset.mem_univ m)
      dsimp only [Q]
      rw [hR, map_mul, Ideal.Quotient.mkₐ_eq_mk, minpoly.aeval, zero_mul]
    exact ((minpoly.monic hx).spectralValue_le_of_dvd hQ_monic (minpoly.dvd K x hQ_aeval)).trans
      (Monic.spectralValue_prod_le (fun m _ ↦ minpoly.monic (hxm m))
        (iSup_quotient_spectralNorm_nonneg x) fun m _ ↦
        spectralNorm_quotient_le_iSup x m)
  · rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · rw [show r = 0 from Real.iSup_of_isEmpty _]
      exact spectralValue_nonneg _
    · refine ciSup_le fun m ↦ ?_
      have hdvd : minpoly K (Ideal.Quotient.mk m.asIdeal x) ∣ minpoly K x := by
        refine minpoly.dvd K _ ?_
        rw [← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, aeval_algHom_apply, minpoly.aeval, map_zero]
      exact (minpoly.monic (hxm m)).spectralValue_le_of_dvd (minpoly.monic hx) hdvd

variable (K E) in
/-- **The spectral algebra norm on a finite reduced `K`-algebra.** Sends `x : E` to
`spectralValue (minpoly K x)`, equivalently the supremum of `spectralNorm K (E ⧸ m)` across
`m : MaximalSpectrum E`. -/
noncomputable def reducedSpectralAlgNorm : AlgebraNorm K E where
  toFun x := spectralValue (minpoly K x)
  map_zero' := by
    rw [spectralValue_minpoly_eq_iSup_spectralNorm]
    simp_rw [map_zero, spectralNorm_zero]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · exact Real.iSup_of_isEmpty _
    · exact ciSup_const
  add_le' x y := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm,
      spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, add_zero, le_rfl]
    · refine ciSup_le fun m ↦ ?_
      have := finiteDimensional_quotient (K := K) m
      rw [map_add]
      exact (isNonarchimedean_spectralNorm.add_le spectralNorm_nonneg).trans
        (add_le_add (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m))
  neg' x := by
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm]
    congr 1 with m
    have := finiteDimensional_quotient (K := K) m
    rw [map_neg, spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic _)]
  mul_le' x y := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm,
      spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, mul_zero, le_rfl]
    · refine ciSup_le fun m ↦ ?_
      have := finiteDimensional_quotient (K := K) m
      rw [map_mul]
      exact (spectralNorm_mul (Algebra.IsAlgebraic.isAlgebraic _)
        (Algebra.IsAlgebraic.isAlgebraic _)).trans
        (mul_le_mul (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m)
          (spectralNorm_nonneg _) (iSup_quotient_spectralNorm_nonneg x))
  smul' k x := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm, spectralValue_minpoly_eq_iSup_spectralNorm]
    rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
    · simp only [Real.iSup_of_isEmpty, mul_zero]
    · rw [Real.mul_iSup_of_nonneg (norm_nonneg k)]
      congr 1 with m
      have := finiteDimensional_quotient (K := K) m
      rw [← Ideal.Quotient.mkₐ_eq_mk K m.asIdeal, map_smul, Ideal.Quotient.mkₐ_eq_mk,
        spectralNorm_smul k (Algebra.IsAlgebraic.isAlgebraic _), coe_nnNorm]
  eq_zero_of_map_eq_zero' x hx := by
    have : IsArtinianRing E := isArtinian_of_tower K inferInstance
    rw [spectralValue_minpoly_eq_iSup_spectralNorm] at hx
    apply (IsArtinianRing.equivPi E).injective
    ext m
    have := finiteDimensional_quotient (K := K) m
    rw [map_zero, Pi.zero_apply, IsArtinianRing.equivPi_apply]
    have hm0 : spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) = 0 :=
      le_antisymm ((spectralNorm_quotient_le_iSup x m).trans hx.le) (spectralNorm_nonneg _)
    exact eq_zero_of_map_spectralNorm_eq_zero hm0 (Algebra.IsAlgebraic.isAlgebraic _)

/-- `reducedSpectralAlgNorm K E x` is defined as `spectralValue (minpoly K x)`. -/
theorem reducedSpectralAlgNorm_def (x : E) :
    reducedSpectralAlgNorm K E x = spectralValue (minpoly K x) := (rfl)

/-- `reducedSpectralAlgNorm K E x` is the supremum of the residue-field spectral norms across
`MaximalSpectrum E`. -/
theorem reducedSpectralAlgNorm_eq_iSup_spectralNorm (x : E) :
    reducedSpectralAlgNorm K E x =
      ⨆ m : MaximalSpectrum E,
        letI := Ideal.Quotient.field m.asIdeal
        spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) :=
  spectralValue_minpoly_eq_iSup_spectralNorm x

/-- `reducedSpectralAlgNorm K E` is nonarchimedean. -/
theorem isNonarchimedean_reducedSpectralAlgNorm :
    IsNonarchimedean (reducedSpectralAlgNorm K E) := by
  intro x y
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  simp only [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
  · simp only [Real.iSup_of_isEmpty, max_self, le_rfl]
  · refine ciSup_le fun m ↦ ?_
    have := finiteDimensional_quotient (K := K) m
    rw [map_add]
    exact (isNonarchimedean_spectralNorm _ _).trans
      (max_le_max (spectralNorm_quotient_le_iSup x m) (spectralNorm_quotient_le_iSup y m))

/-- `reducedSpectralAlgNorm K E` is power-multiplicative. -/
theorem isPowMul_reducedSpectralAlgNorm :
    IsPowMul (reducedSpectralAlgNorm K E) := by
  intro x n hn
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  simp only [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  rcases isEmpty_or_nonempty (MaximalSpectrum E) with _ | _
  · rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty, zero_pow (Nat.one_le_iff_ne_zero.mp hn)]
  · refine le_antisymm (ciSup_le fun m ↦ ?_) ?_
    · have := finiteDimensional_quotient (K := K) m
      rw [map_pow, isPowMul_spectralNorm _ hn]
      exact pow_le_pow_left₀ (spectralNorm_nonneg _) (spectralNorm_quotient_le_iSup x m) n
    · obtain ⟨m, hm⟩ := exists_eq_ciSup_of_finite
        (f := fun m : MaximalSpectrum E ↦
          spectralNorm K (E ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x))
      have := finiteDimensional_quotient (K := K) m
      rw [← hm, ← isPowMul_spectralNorm _ hn, ← map_pow]
      exact spectralNorm_quotient_le_iSup (x ^ n) m

/-- On a nontrivial finite reduced `K`-algebra, `reducedSpectralAlgNorm K E` extends the norm on
`K`. -/
@[simp]
theorem reducedSpectralAlgNorm_algebraMap [Nontrivial E] (k : K) :
    reducedSpectralAlgNorm K E (algebraMap K E k) = ‖k‖ := by
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  obtain ⟨M, hM⟩ := Ideal.exists_maximal E
  have : Nonempty (MaximalSpectrum E) := ⟨⟨M, hM⟩⟩
  rw [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
  simp_rw [Ideal.Quotient.mk_algebraMap, spectralNorm_extends]
  exact ciSup_const

/-- On a nontrivial finite reduced `K`-algebra, `reducedSpectralAlgNorm K E 1 = 1`. -/
@[simp]
theorem reducedSpectralAlgNorm_one [Nontrivial E] :
    reducedSpectralAlgNorm K E 1 = 1 := by
  simpa using reducedSpectralAlgNorm_algebraMap (K := K) (E := E) 1

/-- On a finite field extension `L / K`, `reducedSpectralAlgNorm K L` coincides with
`spectralAlgNorm K L`. -/
@[simp]
theorem reducedSpectralAlgNorm_eq_spectralAlgNorm (K L : Type*) [NormedField K]
    [IsUltrametricDist K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    reducedSpectralAlgNorm K L = spectralAlgNorm K L := by
  ext x
  rfl

end ReducedAlgebra

end TauCeti

section Morphisms

variable {K E E' : Type*} [NormedField K] [IsUltrametricDist K]
  [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
  [CommRing E'] [IsReduced E'] [Algebra K E'] [Module.Finite K E']

/-- Any `K`-algebra homomorphism between finite reduced `K`-algebras is contractive for
`TauCeti.reducedSpectralAlgNorm`. -/
theorem AlgHom.reducedSpectralAlgNorm_map_le (φ : E →ₐ[K] E') (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (φ x) ≤ TauCeti.reducedSpectralAlgNorm K E x := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hφx : IsIntegral K (φ x) := Algebra.IsIntegral.isIntegral (φ x)
  refine (minpoly.monic hφx).spectralValue_le_of_dvd (minpoly.monic hx) (minpoly.dvd K (φ x) ?_)
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

/-- An injective `K`-algebra homomorphism between finite reduced `K`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
theorem AlgHom.reducedSpectralAlgNorm_map_of_injective (φ : E →ₐ[K] E')
    (hφ : Function.Injective φ) (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (φ x) = TauCeti.reducedSpectralAlgNorm K E x := by
  rw [TauCeti.reducedSpectralAlgNorm_def, TauCeti.reducedSpectralAlgNorm_def,
    minpoly.algHom_eq φ hφ]

/-- A `K`-algebra isomorphism between finite reduced `K`-algebras preserves
`TauCeti.reducedSpectralAlgNorm`. -/
@[simp]
theorem AlgEquiv.reducedSpectralAlgNorm_map (e : E ≃ₐ[K] E') (x : E) :
    TauCeti.reducedSpectralAlgNorm K E' (e x) = TauCeti.reducedSpectralAlgNorm K E x :=
  e.toAlgHom.reducedSpectralAlgNorm_map_of_injective e.injective x

end Morphisms

namespace Module.Basis

variable {K E ι : Type*} [NormedField K] [IsUltrametricDist K]
  [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E] [Fintype ι] [Nonempty ι]

/-- On a finite reduced `K`-algebra, `TauCeti.reducedSpectralAlgNorm K E` is bounded above by the
coordinate norm of any finite `K`-basis. -/
theorem reducedSpectralAlgNorm_le_sum_mul_norm (b : Basis ι K E) (x : E) :
    TauCeti.reducedSpectralAlgNorm K E x ≤
      (∑ i, TauCeti.reducedSpectralAlgNorm K E (b i)) * b.norm x := by
  calc
    TauCeti.reducedSpectralAlgNorm K E x =
        TauCeti.reducedSpectralAlgNorm K E (∑ i, b.repr x i • b i) := by
      rw [b.sum_repr]
    _ ≤ ∑ i, TauCeti.reducedSpectralAlgNorm K E (b.repr x i • b i) :=
      Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _
    _ = ∑ i, ‖b.repr x i‖ * TauCeti.reducedSpectralAlgNorm K E (b i) := by
      simp only [map_smul_eq_mul]
    _ ≤ ∑ i, b.norm x * TauCeti.reducedSpectralAlgNorm K E (b i) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (b.norm_repr_le_norm i)
        (apply_nonneg _ _)
    _ = (∑ i, TauCeti.reducedSpectralAlgNorm K E (b i)) * b.norm x := by
      rw [← Finset.mul_sum, mul_comm]

end Module.Basis

namespace TauCeti.IsWeaklyStable

universe u v

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- **Spectral boundedness of linear functionals on finite reduced algebras.** Over a weakly stable
ultrametric normed field `K`, every `K`-linear functional on a finite reduced commutative
`K`-algebra `E` (in any universe) is bounded by `reducedSpectralAlgNorm K E`. -/
theorem exists_bound_reducedSpectralAlgNorm (hK : IsWeaklyStable K)
    {E : Type v} [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
    (φ : Module.Dual K E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖φ x‖ ≤ C * reducedSpectralAlgNorm K E x := by
  classical
  have : IsArtinianRing E := isArtinian_of_tower K inferInstance
  let _ : Fintype (MaximalSpectrum E) := Fintype.ofFinite (MaximalSpectrum E)
  let _ (m : MaximalSpectrum E) : Field (E ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum E) : FiniteDimensional K (E ⧸ m.asIdeal) :=
    finiteDimensional_quotient (K := K) m
  let e : E ≃ₐ[K] ∀ m : MaximalSpectrum E, E ⧸ m.asIdeal :=
    (IsArtinianRing.equivPi E).restrictScalars K
  let ψ (m : MaximalSpectrum E) : Module.Dual K (E ⧸ m.asIdeal) :=
    (φ.comp e.symm.toLinearMap).comp (LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m)
  choose C hC using fun m ↦ hK.exists_bound_spectralNorm (ψ m)
  refine ⟨1 + ∑ m : MaximalSpectrum E, |C m|, by positivity, fun x ↦ ?_⟩
  have hx : φ x = ∑ m : MaximalSpectrum E, ψ m (e x m) := by
    have hsum : ∑ m : MaximalSpectrum E,
        LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m (e x m) = e x := by
      simp_rw [LinearMap.single_apply]
      exact Finset.univ_sum_single (e x)
    calc
      φ x = (φ.comp e.symm.toLinearMap) (e x) := by
        rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, e.symm_apply_apply]
      _ = (φ.comp e.symm.toLinearMap)
            (∑ m : MaximalSpectrum E, LinearMap.single K (fun m ↦ E ⧸ m.asIdeal) m (e x m)) := by
        rw [hsum]
      _ = ∑ m : MaximalSpectrum E, ψ m (e x m) := map_sum _ _ _
  calc
    ‖φ x‖ = ‖∑ m : MaximalSpectrum E, ψ m (e x m)‖ := by rw [hx]
    _ ≤ ∑ m : MaximalSpectrum E, ‖ψ m (e x m)‖ := norm_sum_le _ _
    _ ≤ ∑ m : MaximalSpectrum E, |C m| * spectralNorm K (E ⧸ m.asIdeal) (e x m) := by
      refine Finset.sum_le_sum fun m _ ↦ (hC m (e x m)).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self (C m)) (spectralNorm_nonneg _)
    _ ≤ ∑ m : MaximalSpectrum E, |C m| * reducedSpectralAlgNorm K E x := by
      refine Finset.sum_le_sum fun m _ ↦ mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [reducedSpectralAlgNorm_eq_iSup_spectralNorm]
      exact spectralNorm_quotient_le_iSup x m
    _ = (∑ m : MaximalSpectrum E, |C m|) * reducedSpectralAlgNorm K E x := by
      rw [← Finset.sum_mul]
    _ ≤ (1 + ∑ m : MaximalSpectrum E, |C m|) * reducedSpectralAlgNorm K E x :=
      mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)

/-- **Equivalence of basis coordinate norms and `reducedSpectralAlgNorm`.** On every finite reduced
algebra over a weakly stable ultrametric field `K`, `reducedSpectralAlgNorm K E` is equivalent to
the coordinate norm of any finite `K`-basis. -/
theorem exists_basis_reducedSpectralAlgNorm_comparison (hK : IsWeaklyStable K)
    {E : Type v} [CommRing E] [IsReduced E] [Algebra K E] [Module.Finite K E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (b : Module.Basis ι K E) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x : E,
      b.norm x ≤ C * reducedSpectralAlgNorm K E x ∧
        reducedSpectralAlgNorm K E x ≤ D * b.norm x := by
  choose C hCpos hC using fun i ↦ hK.exists_bound_reducedSpectralAlgNorm (b.coord i)
  let Ctot := ∑ i, C i
  have hCtot : 0 < Ctot := Finset.sum_pos (fun i _ ↦ hCpos i) Finset.univ_nonempty
  have : 0 ≤ ∑ i, reducedSpectralAlgNorm K E (b i) :=
    Finset.sum_nonneg fun i _ ↦ apply_nonneg _ _
  refine ⟨Ctot, 1 + ∑ i, reducedSpectralAlgNorm K E (b i), hCtot, by positivity, fun x ↦ ⟨?_, ?_⟩⟩
  · refine Finset.sup'_le _ _ fun i _ ↦ (hC i x).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (apply_nonneg _ _)
    exact Finset.single_le_sum (fun j _ ↦ (hCpos j).le) (Finset.mem_univ i)
  · exact (b.reducedSpectralAlgNorm_le_sum_mul_norm x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (b.norm_nonneg x))

end TauCeti.IsWeaklyStable
