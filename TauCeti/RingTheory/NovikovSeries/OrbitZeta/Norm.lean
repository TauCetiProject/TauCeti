/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.OrderOfElement.Basic
public import TauCeti.RingTheory.NovikovSeries.Norm
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# Norms of orbit zeta functions along finite covers

Let `γ : ι → H` be the classes of the primitive periodic orbits of a flow and `ε i n` the sign of
the `n`-th iterate of the `i`-th orbit, with orbit zeta function `ζ = exp L`
(`TauCeti.NovikovSeries.orbitZeta`). Let `K` be a finite-index subgroup of an additive commutative
group `H`, the deck group of an abelian covering over the intermediate finite covering with deck
group `H ⧸ K`. If `d i` is the order of `γ i` in `H ⧸ K`, the `i`-th primitive orbit has
`[H : K] / d i` primitive lifts to the intermediate covering, each of class `d i • γ i ∈ K`
(`AddSubgroup.liftClass`), and the `n`-th iterate of a lift is the `(d i * n)`-th iterate of the
orbit. The norm of the orbit zeta function over `Nov(R, K, N|K)` is the orbit zeta function of
this family of lifts (`TauCeti.NovikovSeries.algebraNorm_orbitZeta`). Indeed
`Norm (exp L) = exp (Tr L)`, and the trace is `[H : K]` times the restriction of coefficients to
`K`, which keeps exactly the `n`-th iterates of `γ i` with `d i ∣ n`, those whose class `n • γ i`
lies in `K`. No hypothesis on the torsion of `H` or on the cyclicity of `H ⧸ K` is needed.

## Main results

* `TauCeti.NovikovSeries.algebraNorm_orbitZeta`: the norm of an orbit zeta function along a
  finite-index subgroup is the orbit zeta function of the lifted orbits.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.NovikovSeries

section FiniteCover

variable {ι H R : Type*} [AddCommGroup H] {N : H →+ ℝ} {γ : ι → H} [CommRing R] [Algebra ℚ R]
  (K : AddSubgroup H)

variable [K.FiniteIndex]

/-- The least positive multiple of an orbit class lying in `K` has positive period, and these
periods tend to `∞` along with those of the orbit classes. -/
private theorem pos_tendsto_period_nsmul_addOrderOf (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) :
    (∀ i, 0 < N.comp K.subtype (K.liftClass (γ i))) ∧
      Tendsto (fun i => N.comp K.subtype (K.liftClass (γ i))) cofinite atTop := by
  have hle (i : ι) : N (γ i) ≤ N.comp K.subtype (K.liftClass (γ i)) := by
    simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, AddSubgroup.coe_liftClass,
      map_nsmul, nsmul_eq_mul]
    exact le_mul_of_one_le_left (hpos i).le (by exact_mod_cast addOrderOf_pos _)
  exact ⟨fun i => (hpos i).trans_le (hle i), tendsto_atTop_mono hle hfin⟩

/-- `[H : K]` times the restriction to `K` of an orbit logarithm is the orbit logarithm over `K`
of the least positive multiples `d i • γ i` lying in `K`, with the signs of the iterates `d i * n`
scaled by `[H : K] / d i`, where `d i` is the order of `γ i` in `H ⧸ K`. -/
private theorem index_smul_comap_orbitLog (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    K.index • comap K.subtype (exists_period_rescale_subtype K) (by simp) (orbitLog R N γ ε) =
      orbitLog R (N.comp K.subtype) (fun i => K.liftClass (γ i))
        (fun i n => ((K.index / addOrderOf (γ i : H ⧸ K) : ℕ) : ℤ) *
          ε i (addOrderOf (γ i : H ⧸ K) * n)) := by
  obtain ⟨hpos', hfin'⟩ := pos_tendsto_period_nsmul_addOrderOf K hpos hfin
  have hd₀ (i : ι) : 0 < addOrderOf (γ i : H ⧸ K) := addOrderOf_pos _
  -- The `n`-th iterate of the `i`-th orbit restricts to `K` exactly when `d i ∣ n`, so the
  -- restricted terms are those at the iterates `d i * (k + 1)`.
  let g (p : ι × ℕ) : ι × ℕ := (p.1, addOrderOf (γ p.1 : H ⧸ K) * (p.2 + 1) - 1)
  have hg : Function.Injective g := by
    rintro ⟨i, k⟩ ⟨i', k'⟩ h
    simp only [g, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have h := Nat.eq_of_mul_eq_mul_left (hd₀ i) (Nat.sub_one_cancel
      (Nat.mul_pos (hd₀ i) (Nat.add_one_pos k)) (Nat.mul_pos (hd₀ i) (Nat.add_one_pos k')) h)
    simp only [Prod.mk.injEq, true_and]
    omega
  have hoff : ∀ p ∉ Set.range g, K.index • comap K.subtype (exists_period_rescale_subtype K)
      (by simp) (single ((p.2 + 1) • γ p.1)
        (algebraMap ℚ R ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) : NovikovSeries R H N) = 0 := by
    rintro ⟨i, n⟩ hp
    rw [comap_single_of_notMem_range, smul_zero]
    rintro ⟨k, hk⟩
    rw [AddSubgroup.subtype_apply] at hk
    obtain ⟨j, hj⟩ := (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).2
      (hk ▸ k.2 : (n + 1) • γ i ∈ K)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := j) (by rintro rfl; simp at hj)
    dsimp only at hj
    exact hp ⟨(i, j), Prod.ext rfl (Nat.sub_eq_of_eq_add hj.symm)⟩
  have h := ((hg.hasSum_iff hoff).2 (((hasSum_orbitLog hpos hfin ε).map _
    (continuous_comap (R := R) _ (exists_period_rescale_subtype K) (by simp))).const_smul
      K.index))
  refine ((hasSum_orbitLog (K := R) hpos' hfin' fun i n =>
    ((K.index / addOrderOf (γ i : H ⧸ K) : ℕ) : ℤ) * ε i (addOrderOf (γ i : H ⧸ K) * n)).unique
      (h.congr_fun fun p => ?_)).symm
  obtain ⟨i, k⟩ := p
  have hdk := Nat.sub_add_cancel (Nat.mul_pos (hd₀ i) (Nat.add_one_pos k))
  have hdvd : addOrderOf (γ i : H ⧸ K) ∣ K.index := addOrderOf_dvd_natCard _
  simp only [Function.comp_apply, g, hdk]
  rw [← AddSubgroup.coe_nsmul_liftClass, ← AddSubgroup.subtype_apply,
    comap_single_of_injective _ _ _ Subtype.val_injective, smul_single, ← map_nsmul]
  congr 2
  rw [nsmul_eq_mul]
  have hd : (addOrderOf (γ i : H ⧸ K) : ℚ) ≠ 0 := by exact_mod_cast (hd₀ i).ne'
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hdvd hd]
  push_cast
  field_simp

/-- **Norms of orbit zeta functions along a finite cover.** Let `K` be a finite-index subgroup of
`H`, and for each orbit class `γ i` let `d i` be the order of its image in `H ⧸ K`. The norm of
the orbit zeta function over `Nov(R, K, N|K)` is the orbit zeta function of the family that lists
`[H : K] / d i` copies of the class `d i • γ i ∈ K`, whose `n`-th iterates carry the signs
`ε i (d i * n)`. Geometrically, these are the primitive lifts of the `i`-th orbit to the covering
with deck group `H ⧸ K`, the `n`-th iterate of a lift being the `(d i * n)`-th iterate of the
orbit. -/
theorem algebraNorm_orbitZeta (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    Algebra.norm (NovikovSeries R K (N.comp K.subtype)) (orbitZeta R N γ ε) =
      orbitZeta R (N.comp K.subtype)
        (fun p : (i : ι) × Fin (K.index / addOrderOf (γ i : H ⧸ K)) => K.liftClass (γ p.1))
        (fun p n => ε p.1 (addOrderOf (γ p.1 : H ⧸ K) * n)) := by
  obtain ⟨c, hc₀, hc⟩ := hfin.exists_gt_forall_le hpos
  have h := algebraNorm_exp K (orbitLog_mem_posIdeal (K := R) hc₀ hc ε)
  dsimp only at h
  rw [orbitZeta_def, h, trace_eq_index_smul_comap (exists_period_rescale_subtype K) (by simp),
    index_smul_comap_orbitLog K hpos hfin ε, ← orbitZeta_def]
  exact (orbitZeta_sigma (fun i n => ε i (addOrderOf (γ i : H ⧸ K) * n))
    fun i => K.index / addOrderOf (γ i : H ⧸ K)).symm

end FiniteCover

end TauCeti.NovikovSeries
