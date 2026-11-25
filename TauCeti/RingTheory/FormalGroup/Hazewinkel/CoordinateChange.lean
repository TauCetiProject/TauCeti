/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.PTypical
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
import Mathlib.Algebra.MvPolynomial.CommRing
import TauCeti.Data.Nat.Pow
import TauCeti.RingTheory.FormalGroup.Hazewinkel.LeadingDifference
import TauCeti.RingTheory.FormalGroup.Typical.Expansion
import TauCeti.RingTheory.FormalGroup.Typical.Universal
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Strict `p`-typical coordinate changes and classification of Hazewinkel isomorphisms

Importing the generic strict `p`-typical curves `FormalGroup.pTypicalStrictCurve` and coordinates
`FormalGroup.pTypicalStrictCoordinate` from
`TauCeti.RingTheory.FormalGroup.CoordinateChange.PTypical` and their `p`-typical parametrization
`FormalGroup.IsPTypical.existsUnique_pTypicalStrictCoordinate_eq_of_isPTypical_smul` from
`TauCeti.RingTheory.FormalGroup.Typical.Expansion`, we classify strict `p`-typical coordinate
changes on Hazewinkel's formal group laws.

Over a `ℚ`-algebra, substituting `pTypicalStrictCurve` into Hazewinkel's logarithm `f_v` satisfies
Ravenel's recursion (`TauCeti.coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog`,
`TauCeti.coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero`). Combining universal
`p`-typicality over `ℤ[v₁, …, t₁, …] ↪ ℚ[v₁, …, t₁, …]` with universal injectivity of
`TauCeti.hazewinkelIntegralFormalGroup` yields unconditional integrality of strict `p`-typical
coordinate transport
(`TauCeti.existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup`), `p`-local
classification (`TauCeti.existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq`,
`TauCeti.exists_hazewinkelIntegralFormalGroup_eq_smul_iff`), and coordinate descent along injective
ring homomorphisms (`TauCeti.existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective`).

## References

* D. Quillen, *On the formal group laws of unoriented and complex cobordism theory*, 1969.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter IV.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1.
-/

public section

noncomputable section

open Finset

namespace TauCeti

section Rational

variable {K : Type*} [CommRing K] [Algebra ℚ K] {p : ℕ}

private theorem subst_pTypicalStrictCurve_hazewinkelLog_stage (hp : 1 < p) (v t : ℕ+ → K) (N k : ℕ)
    (hk : k < p ^ (N + 1)) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) =
      PowerSeries.coeff k ((hazewinkelLog p v).toPowerSeries + ∑ i ∈ range N,
        PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
          (hazewinkelLog p v).toPowerSeries) := by
  let F := hazewinkelFormalGroup p v
  let s : F.Curve := F.tautologicalCurve + ∑ i ∈ range N,
    F.monomialCurve (p ^ (i + 1)) (pow_ne_zero _ (Nat.ne_zero_of_lt hp)) (t i.succPNat)
  have hsub := PowerSeries.X_pow_dvd_iff.mp (PowerSeries.X_pow_dvd_subst_sub_subst
    (b := s.toPowerSeries) (F.pTypicalStrictCurve p t).constantCoeff_toPowerSeries
    (PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by
      rw [map_sub, F.coeff_pTypicalStrictCurve_eq_coeff_tautologicalCurve_add_sum hp t hj,
        sub_self])
    (hazewinkelLog p v).toPowerSeries) k hk
  rw [map_sub, sub_eq_zero] at hsub
  rw [hsub]
  congr 1
  have hcurve (M : ℕ) :
      (F.logHom.mapCurve (F.tautologicalCurve + ∑ i ∈ range M,
        F.monomialCurve (p ^ (i + 1)) (pow_ne_zero _ (Nat.ne_zero_of_lt hp))
          (t i.succPNat))).toPowerSeries =
      (hazewinkelLog p v).toPowerSeries + ∑ i ∈ range M,
        PowerSeries.subst (t i.succPNat • PowerSeries.X ^ p ^ (i + 1))
          (hazewinkelLog p v).toPowerSeries := by
    induction M with
    | zero => simp [F]
    | succ M ih =>
      rw [sum_range_succ, ← add_assoc, map_add, FormalGroup.Curve.toPowerSeries_add_𝔾ₐ,
        ih, sum_range_succ, add_assoc, FormalGroupHom.toPowerSeries_mapCurve,
        FormalGroup.logHom_toPowerSeries, log_hazewinkelFormalGroup,
        FormalGroup.toPowerSeries_monomialCurve]
  simpa only [F, s, FormalGroupHom.toPowerSeries_mapCurve, FormalGroup.logHom_toPowerSeries,
    log_hazewinkelFormalGroup] using hcurve N

/-- **Ravenel's logarithm formula for a strict `p`-typical coordinate change**: over a `ℚ`-algebra,
the coefficient of `X^(pⁿ)` in `f_v((F_v.pTypicalStrictCurve p t)(X))` is
`mₙ(v) + ∑_{i < n} mᵢ(v) t_{n - i}^(pⁱ)`. -/
theorem coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog (hp : 1 < p) (v t : ℕ+ → K) (n : ℕ) :
    PowerSeries.coeff (p ^ n)
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) =
      hazewinkelLogCoeff p v n +
        ∑ i ∈ range n, hazewinkelLogCoeff p v i * t (n - 1 - i).succPNat ^ p ^ i := by
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t n (p ^ n)
      (Nat.pow_lt_pow_right hp (Nat.lt_succ_self n)),
    map_add, coeff_hazewinkelLog_pow v hp n, map_sum]; congr 1
  refine Finset.sum_bij (fun m _ ↦ n - 1 - m)
    (fun m hm ↦ mem_range.mpr (by have := mem_range.mp hm; omega))
    (fun m₁ hm₁ m₂ hm₂ h ↦ by have := mem_range.mp hm₁; have := mem_range.mp hm₂; omega)
    (fun i hi ↦ ⟨n - 1 - i, mem_range.mpr (by have := mem_range.mp hi; omega),
      by have := mem_range.mp hi; omega⟩) fun m hm ↦ ?_
  have hle : m + 1 ≤ n := Nat.succ_le_of_lt (mem_range.mp hm)
  rw [coeff_pow_subst_smul_X_pow_hazewinkelLog v hp (t m.succPNat) (m + 1) n, ite_eq_left hle,
    (by omega : n - (m + 1) = n - 1 - m),
    (by congr 1; omega : (n - 1 - (n - 1 - m)).succPNat = m.succPNat)]

/-- Outside the degrees `pⁿ`, `f_v((F_v.pTypicalStrictCurve p t)(X))` vanishes. -/
theorem coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero (hp : 1 < p) (v t : ℕ+ → K) {k : ℕ}
    (hk : ∀ n, p ^ n ≠ k) :
    PowerSeries.coeff k
        (PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
          (hazewinkelLog p v).toPowerSeries) = 0 := by
  rw [subst_pTypicalStrictCurve_hazewinkelLog_stage hp v t k k (Nat.lt_pow_add_one_self hp k),
    map_add, coeff_hazewinkelLog_eq_zero v hk, zero_add, map_sum]
  exact sum_eq_zero fun m _ ↦
    coeff_subst_smul_X_pow_hazewinkelLog_eq_zero v hp (t m.succPNat) (m + 1) hk

/-- The formal logarithm of `(F_v.pTypicalStrictCoordinate p t) • F_v` is
`f_v((F_v.pTypicalStrictCurve p t)(X))`. -/
theorem log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (v t : ℕ+ → K) :
    (((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) • hazewinkelFormalGroup p v).log =
      PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
        (hazewinkelLog p v).toPowerSeries := by
  rw [FormalGroup.log_smul, log_hazewinkelFormalGroup,
    FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate]; simp

/-- Over a `ℚ`-algebra, transporting `hazewinkelFormalGroup p v` along `pTypicalStrictCoordinate`
produces `hazewinkelFormalGroup p w` for a unique sequence `w : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup (hp : 1 < p)
    (v t : ℕ+ → K) :
    ∃! w : ℕ+ → K,
      ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t) • hazewinkelFormalGroup p v =
        hazewinkelFormalGroup p w :=
  existsUnique_eq_hazewinkelFormalGroup hp fun k hk ↦ by
    rw [log_pTypicalStrictCoordinate_smul_hazewinkelFormalGroup,
      coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hk]

private def pTypicalCoordParamsRat (p : ℕ) (v w : ℕ+ → K) : ℕ → K
  | n => hazewinkelLogCoeff p w (n + 1) - hazewinkelLogCoeff p v (n + 1) -
      ∑ i : Fin n, hazewinkelLogCoeff p v ((i : ℕ) + 1) *
        pTypicalCoordParamsRat p v w (n - ((i : ℕ) + 1)) ^ p ^ ((i : ℕ) + 1)
decreasing_by have := i.isLt; omega

/-- Over a `ℚ`-algebra, `(hazewinkelLog p w)⁻¹ * hazewinkelLog p v` equals
`(hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → K`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_inv_hazewinkelLog_mul (hp : 1 < p)
    (v w : ℕ+ → K) :
    ∃! t : ℕ+ → K,
      (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
        (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
  let t : ℕ+ → K := fun j ↦ pTypicalCoordParamsRat p v w j.natPred
  have hlog : PowerSeries.subst ((hazewinkelFormalGroup p v).pTypicalStrictCurve p t).toPowerSeries
      (hazewinkelLog p v).toPowerSeries = (hazewinkelLog p w).toPowerSeries := by
    ext k; by_cases hpow : ∃ n, p ^ n = k
    · obtain ⟨_ | n, rfl⟩ := hpow
      · rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp, coeff_hazewinkelLog_pow _ hp]
        simp
      · have ht_n : t n.succPNat = hazewinkelLogCoeff p w (n + 1) -
            hazewinkelLogCoeff p v (n + 1) - ∑ i ∈ range n,
              hazewinkelLogCoeff p v (i + 1) * t (n - (i + 1)).succPNat ^ p ^ (i + 1) := by
          simp only [t, Nat.natPred_succPNat]
          rw [pTypicalCoordParamsRat]
          dsimp only
          rw [Fin.sum_univ_eq_sum_range (fun j ↦ hazewinkelLogCoeff p v (j + 1) *
            pTypicalCoordParamsRat p v w (n - (j + 1)) ^ p ^ (j + 1))]
        rw [coeff_pow_subst_pTypicalStrictCurve_hazewinkelLog hp v t (n + 1),
          coeff_hazewinkelLog_pow w hp (n + 1), sum_range_succ', pow_zero, pow_one,
          hazewinkelLogCoeff_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero, ht_n]; ring
    · push Not at hpow
      rw [coeff_subst_pTypicalStrictCurve_hazewinkelLog_eq_zero hp v t hpow,
        coeff_hazewinkelLog_eq_zero w hpow]
  have hcoord : (hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t =
      (hazewinkelLog p w)⁻¹ * hazewinkelLog p v := by
    apply inv_injective; rw [mul_inv_rev, inv_inv]
    rw [← (FormalCoordinate.ext <| by
      rw [FormalCoordinate.toPowerSeries_mul,
        FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate, hlog] :
      hazewinkelLog p v * ((hazewinkelFormalGroup p v).pTypicalStrictCoordinate p t)⁻¹ =
        hazewinkelLog p w), inv_mul_cancel_left]
  exact ⟨t, hcoord, fun t' ht' ↦
    (hazewinkelFormalGroup p v).pTypicalStrictCoordinate_injective hp (ht'.trans hcoord.symm)⟩

end Rational

section Classification

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- **Integrality of strict `p`-typical coordinate changes**: over every commutative ring `R`,
transporting `hazewinkelIntegralFormalGroup p v` along its `p`-typical strict coordinate `t`
produces `hazewinkelIntegralFormalGroup p w` for a unique sequence `w : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup (v t : ℕ+ → R) :
    ∃! w : ℕ+ → R,
      ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
          hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w := by
  let UZ := MvPolynomial (ℕ+ ⊕ ℕ+) ℤ
  let vZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let tZ : ℕ+ → UZ := fun i ↦ MvPolynomial.X (Sum.inr i)
  have hGZ : (((hazewinkelIntegralFormalGroup p vZ).pTypicalStrictCoordinate p tZ) •
      hazewinkelIntegralFormalGroup p vZ).IsPTypical p :=
    (isPTypical_hazewinkelIntegralFormalGroup p vZ).pTypicalStrictCoordinate_smul hp.out tZ
  obtain ⟨wZ, hwZ⟩ := hGZ.exists_eq_hazewinkelIntegralFormalGroup_of_injective
    (K := MvPolynomial (ℕ+ ⊕ ℕ+) ℚ) (ι := MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective _ Int.cast_injective)
  let ev : UZ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v t)
  have hR : ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t) •
      hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p (ev ∘ wZ) := by
    simpa only [FormalGroup.map_smul, FormalGroup.map_pTypicalStrictCoordinate,
      map_hazewinkelIntegralFormalGroup, (funext fun _ ↦ by simp [UZ, ev, vZ] : ev ∘ vZ = v),
      (funext fun _ ↦ by simp [UZ, ev, tZ] : ev ∘ tZ = t)] using
      congrArg (fun F : FormalGroup UZ ↦ F.map ev) hwZ
  exact ⟨ev ∘ wZ, hR, fun w' hw' ↦ hazewinkelIntegralFormalGroup_injective p (hw'.symm.trans hR)⟩

/-- **Classification of strict isomorphisms between Hazewinkel laws over `p`-local rings**:
when every prime `q ≠ p` is a unit in `R`, any strict coordinate `φ` satisfying
`φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w` equals
`pTypicalStrictCoordinate p t` for a unique `t : ℕ+ → R`. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {v w : ℕ+ → R}
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) :
    ∃! t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t :=
  (isPTypical_hazewinkelIntegralFormalGroup p v)
    |>.existsUnique_pTypicalStrictCoordinate_eq_of_isPTypical_smul hp.out hlocal hφ <|
      (FormalGroup.isPTypical_congr hsmul p).mpr (isPTypical_hazewinkelIntegralFormalGroup p w)

/-- When every prime `q ≠ p` is invertible in `R`, a strict formal coordinate `φ` transports
`hazewinkelIntegralFormalGroup p v` into `Set.range (hazewinkelIntegralFormalGroup p)` if and only
if `φ` is `(hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t` for some `t`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_smul_iff
    (hlocal : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (v : ℕ+ → R)
    {φ : FormalCoordinate R} (hφ : FormalCoordinate.linearCoeff φ = 1) :
    (∃ w : ℕ+ → R, φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) ↔
      ∃ t : ℕ+ → R, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t :=
  ⟨fun ⟨_, hw⟩ ↦ (existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocal hφ hw).exists,
    fun ⟨t, ht⟩ ↦ ht ▸
      (existsUnique_pTypicalStrictCoordinate_smul_hazewinkelIntegralFormalGroup p v t).exists⟩

private theorem pTypicalParams_mem_range_of_injective
    {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} (v : ℕ+ → A) (φ : FormalCoordinate A)
    {tB : ℕ+ → B}
    (hcurveB : (FormalCoordinate.map ι φ)⁻¹.toPowerSeries =
      ((hazewinkelIntegralFormalGroup p (ι ∘ v)).pTypicalStrictCurve p tB).toPowerSeries)
    (i : ℕ+) : tB i ∈ ι.range := by
  induction i using PNat.strongInductionOn with | _ i ih =>
  obtain ⟨n, rfl⟩ : ∃ n, n.succPNat = i := ⟨i.natPred, i.succPNat_natPred⟩
  let t_trunc : ℕ+ → A := fun j ↦ if hj : j < n.succPNat then (ih j hj).choose else 0
  have hsub := (hazewinkelIntegralFormalGroup p (ι ∘ v)).coeff_pow_succ_pTypicalStrictCurve_sub
    hp.out.one_lt (t := tB) (t' := ι ∘ t_trunc) (n := n) fun j hj ↦ by
      have hlt : j < n.succPNat :=
        (PNat.coe_lt_coe j n.succPNat).mp (by simpa using Nat.lt_succ_of_le hj)
      simp only [t_trunc, Function.comp_apply, dite_eq_left hlt]
      exact (ih j hlt).choose_spec.symm
  rw [(by simp [t_trunc] : (ι ∘ t_trunc) n.succPNat = 0), sub_zero, ← hcurveB, ← map_inv,
    FormalCoordinate.toPowerSeries_map, ← map_hazewinkelIntegralFormalGroup,
    ← FormalGroup.map_pTypicalStrictCurve, FormalGroup.Curve.toPowerSeries_map,
    ← map_sub (PowerSeries.map ι), PowerSeries.coeff_map] at hsub
  exact ⟨_, hsub⟩

/-- **Integral descent of `p`-typical strict coordinates** along an injection into a ring `B` in
which every prime `q ≠ p` is a unit. -/
theorem existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq_of_injective
    {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B}
    (hι : Function.Injective ι) (hlocalB : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : B))
    {v w : ℕ+ → A} {φ : FormalCoordinate A} (hφ : FormalCoordinate.linearCoeff φ = 1)
    (hsmul : φ • hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w) :
    ∃! t : ℕ+ → A, φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p t := by
  obtain ⟨tB, htB, _⟩ := existsUnique_pTypicalStrictCoordinate_eq_of_smul_eq p hlocalB
    (φ := FormalCoordinate.map ι φ)
    (by ext; rw [FormalCoordinate.val_linearCoeff, FormalCoordinate.toPowerSeries_map,
      PowerSeries.coeff_map, ← FormalCoordinate.val_linearCoeff, hφ, Units.val_one, map_one,
      Units.val_one])
    (by simpa only [FormalGroup.map_smul, map_hazewinkelIntegralFormalGroup] using
      congrArg (fun F : FormalGroup A ↦ F.map ι) hsmul)
  have hmem := pTypicalParams_mem_range_of_injective p v φ
    (by rw [htB, FormalGroup.toPowerSeries_inv_pTypicalStrictCoordinate])
  let tA : ℕ+ → A := fun i ↦ (hmem i).choose
  have htA : φ = (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p tA := by
    have hmap : FormalCoordinate.map ι φ = FormalCoordinate.map ι
        ((hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate p tA) := by
      rw [htB, FormalGroup.map_pTypicalStrictCoordinate, map_hazewinkelIntegralFormalGroup]
      exact congrArg _ (funext fun i ↦ (hmem i).choose_spec.symm)
    ext1; refine PowerSeries.ext fun k ↦ hι ?_
    simpa only [FormalCoordinate.toPowerSeries_map, PowerSeries.coeff_map] using
      congrArg (fun ψ : FormalCoordinate B ↦ PowerSeries.coeff k ψ.toPowerSeries) hmap
  exact ⟨tA, htA, fun t' ht' ↦
    (hazewinkelIntegralFormalGroup p v).pTypicalStrictCoordinate_injective hp.out.one_lt
      (ht'.symm.trans htA)⟩

end Classification

end TauCeti
