/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.KerReduction
public import TauCeti.RingTheory.FormalGroup.NSMul
-- Proof-only: evaluating a substitution, and evaluating a renamed series.
import TauCeti.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.MvPowerSeries.Substitution
import TauCeti.RingTheory.PowerSeries.Evaluation

/-!
# Torsion in the formal group when `p` is small

Let `I` be an adic ideal of a complete Hausdorff linearly topologised integral domain `O`. On the
group `Ê(I)` of formal-group parameters of a Weierstrass curve, multiplication by `n` is
evaluation of the multiplication-by-`n` series `[n](T)` of the elliptic formal group law. For a
prime `p` that series has the shape `[p](T) = p T u(T) + Tᵖ h(T)` with `u(0) = 1`
(`FormalGroup.exists_nsmulSeries_eq_of_prime`). So if `t ∈ I` is a nonzero parameter with
`[p] t = 0`, then `p u(t) = -t ^ (p - 1) h(t)`, and `u(t)` is a unit: `p` lies in `I ^ (p - 1)`.
Contrapositively, `Ê(I)` has no nonzero `p`-torsion when `p ∉ I ^ (p - 1)`. This is the case
`n = 1` of Silverman AEC IV.6.1, which over a discrete valuation ring bounds the valuation of a
point of exact order `pⁿ` by `v(p) / (pⁿ - pⁿ⁻¹)`.

A prime `ℓ` that is a unit of `O` never lies in `I ^ (ℓ - 1)` for a proper ideal `I`, so the
condition only matters for the residue characteristic. Over the completion of a Dedekind domain at
a height-one prime `u` of residue characteristic `p`, it says that the ramification index of `p`
at `u` is less than `p - 1`. Then the kernel of reduction `E₁(F_u)` is torsion-free; over `ℚ` this
holds at every odd prime. This extends the prime-to-`p` case
(`WeierstrassCurve.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero`, Silverman AEC VII.3.1) to all of
the torsion, which is what makes reduction injective on the whole torsion subgroup at such a
prime.

## Main results

* `WeierstrassCurve.FormalGroupPoint.coe_nsmul`: the parameter of `n • P` is `[n]` evaluated at
  the parameter of `P`.
* `WeierstrassCurve.FormalGroupPoint.eq_zero_of_prime_nsmul_eq_zero`: `Ê(I)` has no nonzero
  `p`-torsion when `p ∉ I ^ (p - 1)`.
* `WeierstrassCurve.FormalGroupPoint.eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd`: `Ê(I)` has no
  nonzero `n`-torsion when every prime factor `p` of `n` satisfies `p ∉ I ^ (p - 1)`.
* `WeierstrassCurve.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero_of_forall_prime_dvd`: the kernel
  of reduction `E₁(F_u)` has no nonzero `n`-torsion when every prime factor `p` of `n` satisfies
  `p ∉ u ^ (p - 1)`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4.4, IV.6.1 and VII.3.1.
-/

public section

namespace WeierstrassCurve

namespace FormalGroupPoint

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {W : WeierstrassCurve O} {I : Ideal O} [Fact (IsAdic I)]

/-- Evaluation at a parameter, through the identity ring hom, is the algebra map `aeval`. -/
private theorem eval₂_eq_aeval (P : FormalGroupPoint W I) :
    PowerSeries.eval₂ (RingHom.id O) (P : O) = PowerSeries.aeval (R := O) P.hasEval := by
  rw [PowerSeries.coe_aeval, Algebra.algebraMap_self]

open MvPowerSeries.WithPiTopology in
/-- **Multiplication by `n` on `Ê(I)` is evaluation of `[n]`**: the parameter of `n • P` is the
multiplication-by-`n` series of the elliptic formal group law evaluated at the parameter of `P`. -/
theorem coe_nsmul (n : ℕ) (P : FormalGroupPoint W I) :
    ((n • P : FormalGroupPoint W I) : O) =
      PowerSeries.eval₂ (RingHom.id O) (P : O) ((formalGroup W).nsmulSeries n) := by
  have hI : IsAdic I := Fact.out
  rw [eval₂_eq_aeval]
  induction n with
  | zero => simp
  | succ n ih =>
    set a : Fin 2 → PowerSeries O := ![(formalGroup W).nsmulSeries n, PowerSeries.X]
    have ha : MvPowerSeries.HasSubst a :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun s ↦ by
        fin_cases s
        · exact (formalGroup W).constantCoeff_nsmulSeries n
        · exact PowerSeries.constantCoeff_X
    -- the values of the substituted family are the parameters of `n • P` and of `P`
    have hval : (fun s ↦ PowerSeries.aeval P.hasEval (a s)) = ![((n • P : FormalGroupPoint W I) :
        O), (P : O)] := by
      funext s
      fin_cases s
      · exact ih.symm
      · exact PowerSeries.aeval_X P.hasEval
    have hb : MvPowerSeries.HasEval fun s ↦ PowerSeries.aeval P.hasEval (a s) := by
      rw [hval]
      exact MvPowerSeries.hasEval_of_mem hI fun s ↦ by
        fin_cases s
        · exact (n • P).property
        · exact P.property
    rw [succ_nsmul, coe_add, (formalGroup W).nsmulSeries_succ, formalGroup_toPowerSeries,
      MvPowerSeries.aeval_subst ha (PowerSeries.continuous_aeval P.hasEval) hb,
      MvPowerSeries.aeval_rename _ hb (b := Sum.elim (fun _ ↦ ((n • P : FormalGroupPoint W I) :
        O)) fun _ ↦ (P : O)) (by rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> simp [a, ih, PowerSeries.aeval_X]),
      Algebra.algebraMap_self,
      formalAddEval_def]

/-- **`Ê(I)` has no `p`-torsion when `p` is small** (Silverman AEC IV.6.1, for points of order
`p`): over an integral domain, if the prime `p` does not lie in `I ^ (p - 1)`, the only parameter
`t ∈ I` with `p • t = 0` in `Ê(I)` is `t = 0`. -/
theorem eq_zero_of_prime_nsmul_eq_zero [IsDomain O] {p : ℕ} (hp : p.Prime)
    (hpI : (p : O) ∉ I ^ (p - 1)) {P : FormalGroupPoint W I} (h : p • P = 0) : P = 0 := by
  have hI : IsAdic I := Fact.out
  have : NonarchimedeanRing O := hI ▸ I.nonarchimedean
  obtain ⟨u, g, hu, hN⟩ := (formalGroup W).exists_nsmulSeries_eq_of_prime hp
  set t : O := P.val
  set ev := PowerSeries.aeval (R := O) P.hasEval
  -- `0 = p t u(t) + t ^ p g(t)`
  have h0 : (p : O) * t * ev u + t ^ p * ev g = 0 := by
    have := coe_nsmul p P
    rw [h, coe_zero, hN, eval₂_eq_aeval] at this
    simpa [ev, PowerSeries.aeval_X] using this.symm
  -- `u(t)` is a unit, being `1` modulo `I`
  have hunit : IsUnit (ev u) := by
    have hsub : ev u - 1 ∈ I := by
      have key := MvPowerSeries.eval₂_sub_constantCoeff_mem (φ := RingHom.id O)
        continuous_id (PowerSeries.hasEval P.hasEval) hI (fun _ ↦ P.property) u
      rw [← PowerSeries.constantCoeff_eq, hu, map_one] at key
      simpa [ev, PowerSeries.coe_aeval, PowerSeries.eval₂] using key
    simpa using (hI.isTopologicallyNilpotent_of_mem hsub).isUnit_one_add
  by_contra hP
  have ht : t ≠ 0 := fun ht ↦ hP (FormalGroupPoint.ext ht)
  -- cancelling `t`, `p u(t) = -t ^ (p - 1) g(t) ∈ I ^ (p - 1)`
  have hpu : (p : O) * ev u = -(t ^ (p - 1) * ev g) := by
    have htp : t ^ p = t * t ^ (p - 1) := by rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
    refine mul_left_cancel₀ ht ?_
    linear_combination h0 - ev g * htp
  apply hpI
  have hmem : (p : O) * ev u ∈ I ^ (p - 1) := by
    rw [hpu]
    exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow P.property _))
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  simpa [mul_assoc, hv] using Ideal.mul_mem_right v _ hmem

/-- **`Ê(I)` has no `n`-torsion when the prime factors of `n` are small**: over an integral
domain, if every prime factor `p` of `n ≠ 0` satisfies `p ∉ I ^ (p - 1)`, the only parameter
`t ∈ I` with `n • t = 0` in `Ê(I)` is `t = 0`. -/
theorem eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd [IsDomain O] {n : ℕ} (hn : n ≠ 0)
    (hnI : ∀ p : ℕ, p.Prime → p ∣ n → (p : O) ∉ I ^ (p - 1)) {P : FormalGroupPoint W I}
    (h : n • P = 0) : P = 0 := by
  induction n using Nat.recOnMul generalizing P with
  | zero => exact absurd rfl hn
  | one => simpa using h
  | prime p hp => exact eq_zero_of_prime_nsmul_eq_zero hp (hnI p hp dvd_rfl) h
  | mul a b ha hb =>
    obtain ⟨ha0, hb0⟩ := mul_ne_zero_iff.mp hn
    rw [mul_comm, mul_nsmul] at h
    exact hb hb0 (fun p hp hpb ↦ hnI p hp (dvd_mul_of_dvd_right hpb a))
      (ha ha0 (fun p hp hpa ↦ hnI p hp (dvd_mul_of_dvd_left hpa b)) h)

end FormalGroupPoint

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u

local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **The kernel of reduction has no torsion of small residue-characteristic order** (Silverman AEC
IV.6.1 and VII.3.1): a point of `E₁(F_u)` killed by an integer `n ≠ 0` whose prime factors `p` all
satisfy `p ∉ u ^ (p - 1)` is the point at infinity. When the residue characteristic `p` has
ramification index less than `p - 1` at `u`, as at every odd prime of `ℤ`, this holds for every
`n ≠ 0`, and `E₁(F_u)` is torsion-free. -/
theorem eq_zero_of_mem_kerReduction_of_nsmul_eq_zero_of_forall_prime_dvd {n : ℕ} (hn : n ≠ 0)
    (hnu : ∀ p : ℕ, p.Prime → p ∣ n → (p : A) ∉ u.asIdeal ^ (p - 1))
    {P : (C.baseChange F_u).toAffine.Point} (hP : P ∈ C.kerReduction u) (h : n • P = 0) :
    P = 0 := by
  -- the condition on `p` in `A` is the condition on `p` in the completion
  have hnO : ∀ p : ℕ, p.Prime → p ∣ n → (p : O_u) ∉ m_u ^ (p - 1) := fun p hp hpn ↦ by
    rw [HeightOneSpectrum.mem_maximalIdeal_pow_iff]
    have := hnu p hp hpn
    rwa [HeightOneSpectrum.mem_asIdeal_pow_iff_valued_algebraMap_le (K := F), map_natCast]
      at this
  set e := C.formalPointAddEquivKerReduction u
  have hQ : n • e.symm ⟨P, hP⟩ = 0 := by
    rw [← map_nsmul, AddEquiv.map_eq_zero_iff]
    exact Subtype.ext h
  simpa using congrArg Subtype.val
    (e.symm.map_eq_zero_iff.mp (FormalGroupPoint.eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd hn
      hnO hQ))

end WeierstrassCurve
