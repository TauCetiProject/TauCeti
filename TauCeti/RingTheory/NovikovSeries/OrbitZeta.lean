/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Cofinite.Basic
public import TauCeti.RingTheory.NovikovSeries.ExpLog
public import TauCeti.RingTheory.NovikovSeries.InfiniteProduct

/-!
# Orbit zeta functions and their Euler products

Let `γ : ι → H` be a family of exponents of positive period `N (γ i) > 0`, with only finitely many
below each cutoff, that is `N ∘ γ` tends to `∞` along the cofinite filter. Think of `γ i` as the
class of the `i`-th primitive periodic orbit of a flow, of the `(k + 1)`-fold iterate of that orbit
as having class `(k + 1) • γ i` and multiplicity `k + 1`, and of `ε i (k + 1)` as the Lefschetz sign
of that iterate. Over a commutative `ℚ`-algebra `K`, the *orbit logarithm*
(`TauCeti.NovikovSeries.orbitLog`) is the series of all iterates of all orbits, each weighted by
its sign divided by its multiplicity,

`L = ∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · e^((k + 1) • γ i)`,

and the *orbit zeta function* (`TauCeti.NovikovSeries.orbitZeta`) is its exponential `ζ = exp L`.
The orbit logarithm lies in the positive ideal, so `ζ` is a unit whose difference with `1` is
supported in positive periods (`TauCeti.NovikovSeries.isUnit_orbitZeta`,
`TauCeti.NovikovSeries.orbitZeta_sub_one_mem_periodFiltration`).

Over any commutative ring `R`, for coefficients `r : ι → R` and integer exponents `m : ι → ℤ`, the
*Euler product* `∏ᵢ (1 - r i e^(γ i)) ^ m i` (`TauCeti.NovikovSeries.eulerProduct`, in
`TauCeti.RingTheory.NovikovSeries.InfiniteProduct`) converges in the period topology, and it is
natural in the coefficient ring and in exponent maps rescaling periods
(`TauCeti.NovikovSeries.mapRingHom_eulerProduct`).

**Product formula.** Suppose that the signs of the iterates of each orbit form a geometric
sequence: `ε i (k + 1) = ε i 1 * σ i ^ k` for a sign `σ i = ±1`. For the iterates of a periodic
orbit whose return map has `i₋` real eigenvalues below `-1`, this holds with `σ = (-1) ^ i₋`. Then
the logarithm `log (1 - σ e^γ) = -∑ₖ σᵏ⁺¹ e^((k + 1) • γ) / (k + 1)` shows that each orbit
contributes `exp (∑ₖ ε (k + 1) / (k + 1) · e^((k + 1) • γ)) = (1 - σ e^γ) ^ (-ε 1 * σ)`, and since
the exponential carries convergent sums in the positive ideal to convergent products,

`ζ = ∏ᵢ (1 - σ i e^(γ i)) ^ (-(ε i 1 * σ i))`

(`TauCeti.NovikovSeries.orbitZeta_eq_eulerProduct`). The right side is the image of the same
Euler product with integer coefficients, so `ζ` has integer coefficients
(`TauCeti.NovikovSeries.orbitZeta_eq_mapRingHom_eulerProduct`). Neither the injectivity of `N` nor
the discreteness of its image is used, and the exponent group may have torsion.

## Main definitions

* `TauCeti.NovikovSeries.orbitLog`: the orbit logarithm `∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) ·
  e^((k + 1) • γ i)`.
* `TauCeti.NovikovSeries.orbitZeta`: the orbit zeta function, the exponential of the orbit
  logarithm.

## Main results

* `TauCeti.NovikovSeries.orbitZeta_def`: the orbit zeta function is the exponential of the orbit
  logarithm.
* `TauCeti.NovikovSeries.hasSum_orbitLog`, `TauCeti.NovikovSeries.orbitLog_mem_periodFiltration`:
  convergence and support of the orbit logarithm.
* `TauCeti.NovikovSeries.orbitLog_mem_nonnegSubring`, `TauCeti.NovikovSeries.orbitLog_mem_posIdeal`:
  the orbit logarithm lies in the positive ideal of the nonnegative subring.
* `TauCeti.NovikovSeries.isUnit_orbitZeta`,
  `TauCeti.NovikovSeries.orbitZeta_sub_one_mem_periodFiltration`: the orbit zeta function is a unit
  congruent to `1` above every positive lower bound of the periods.
* `TauCeti.NovikovSeries.orbitZeta_eq_eulerProduct`: the product formula.
* `TauCeti.NovikovSeries.orbitZeta_eq_mapRingHom_eulerProduct`: integrality of the orbit zeta
  function.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

open Filter Topology

namespace TauCeti.NovikovSeries

variable {ι H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {γ : ι → H}

section OrbitZeta

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- The **orbit logarithm** `∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · e^((k + 1) • γ i)`: for primitive
periodic orbits of classes `γ i`, with `ε i n` the sign of the `n`-fold iterate of the `i`-th
orbit, each iterate contributes its class weighted by its sign divided by its multiplicity. The
value `ε i 0` is not used. -/
def orbitLog (K : Type*) [CommRing K] [Algebra ℚ K] (N : H →+ ℝ) (γ : ι → H) (ε : ι → ℕ → ℤ) :
    NovikovSeries K H N :=
  ∑' p : ι × ℕ, single ((p.2 + 1) • γ p.1) (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ)))

/-- The **orbit zeta function** `exp (∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · e^((k + 1) • γ i))`, the
exponential of the orbit logarithm `TauCeti.NovikovSeries.orbitLog`. -/
def orbitZeta (K : Type*) [CommRing K] [Algebra ℚ K] (N : H →+ ℝ) (γ : ι → H)
    (ε : ι → ℕ → ℤ) : NovikovSeries K H N :=
  NormedSpace.exp (orbitLog K N γ ε)

/-- The orbit zeta function is the exponential of the orbit logarithm. -/
theorem orbitZeta_def (ε : ι → ℕ → ℤ) :
    orbitZeta K N γ ε = NormedSpace.exp (orbitLog K N γ ε) :=
  (rfl)

/-- The `(k + 1)`-fold iterate of an orbit of class `g` has period `(k + 1) * N g`. -/
private theorem period_succ_nsmul (g : H) (k : ℕ) : N ((k + 1) • g) = ((k : ℝ) + 1) * N g := by
  rw [map_nsmul, nsmul_eq_mul]
  push_cast
  ring

/-- The term of the orbit logarithm of the `(k + 1)`-fold iterate of an orbit of class `g` lies
above the period `N g` when `N g ≥ 0`. -/
private theorem single_iterate_mem_periodFiltration {g : H} (hg : 0 ≤ N g) (k : ℕ) (q : ℚ) :
    (single ((k + 1) • g) (algebraMap ℚ K q) : NovikovSeries K H N) ∈ periodFiltration K N (N g) :=
  antitone_periodFiltration (by
    rw [period_succ_nsmul]
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (single_mem_periodFiltration _ _)

/-- The orbit logarithm converges in the period topology when only finitely many periods lie below
each cutoff. -/
theorem hasSum_orbitLog (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    HasSum (fun p : ι × ℕ => (single ((p.2 + 1) • γ p.1)
      (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) : NovikovSeries K H N))
      (orbitLog K N γ ε) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (hasBasis_nhds_zero.tendsto_right_iff.2 fun C _ => eventually_cofinite.2 ?_)).hasSum
  obtain ⟨c, hc, hcγ⟩ := hfin.exists_gt_forall_le hpos
  -- A term below the cutoff `C` comes from an orbit of period below `C`, iterated fewer than
  -- `C / c` times.
  refine ((((northcott_iff_tendsto _).2 hfin).finite_le C).prod
    (Set.finite_Iio ⌈C / c⌉₊)).subset ?_
  rintro ⟨i, k⟩ hik
  have hlt : ((k : ℝ) + 1) * N (γ i) < C := by
    refine lt_of_not_ge fun hC =>
      hik (antitone_periodFiltration ?_ (single_mem_periodFiltration _ _))
    rwa [period_succ_nsmul]
  have hk : (k : ℝ) < C / c := by
    rw [lt_div_iff₀ hc]
    nlinarith [hcγ i, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ⟨?_, Nat.lt_ceil.2 hk⟩
  simp only [Set.mem_ofPred_eq]
  nlinarith [hpos i, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The orbit logarithm lies above every nonnegative lower bound of the periods. -/
theorem orbitLog_mem_periodFiltration {c : ℝ} (hc₀ : 0 ≤ c) (hc : ∀ i, c ≤ N (γ i))
    (ε : ι → ℕ → ℤ) : orbitLog K N γ ε ∈ periodFiltration K N c :=
  tsum_mem (isClosed_periodFiltration c) fun p =>
    antitone_periodFiltration (hc p.1) (single_iterate_mem_periodFiltration (hc₀.trans (hc p.1))
      _ _)

/-- The orbit logarithm lies in the nonnegative subring when all periods are nonnegative. -/
theorem orbitLog_mem_nonnegSubring (hγ : ∀ i, 0 ≤ N (γ i)) (ε : ι → ℕ → ℤ) :
    orbitLog K N γ ε ∈ nonnegSubring K N :=
  mem_nonnegSubring.2 (mem_periodFiltration.1 (orbitLog_mem_periodFiltration le_rfl hγ ε))

/-- The orbit logarithm lies in the positive ideal when the periods have a positive lower bound. -/
theorem orbitLog_mem_posIdeal {c : ℝ} (hc₀ : 0 < c) (hc : ∀ i, c ≤ N (γ i)) (ε : ι → ℕ → ℤ) :
    (⟨orbitLog K N γ ε, orbitLog_mem_nonnegSubring (fun i => hc₀.le.trans (hc i)) ε⟩ :
      nonnegSubring K N) ∈ posIdeal K N :=
  mem_posIdeal.2 (exists_pos_mem_periodFiltration_iff.1
    ⟨c, hc₀, orbitLog_mem_periodFiltration hc₀.le hc ε⟩)

/-- The orbit zeta function is congruent to `1` above every positive lower bound of the periods.
In particular its coefficients of nonpositive period are those of `1`. -/
theorem orbitZeta_sub_one_mem_periodFiltration {c : ℝ} (hc₀ : 0 < c) (hc : ∀ i, c ≤ N (γ i))
    (ε : ι → ℕ → ℤ) : orbitZeta K N γ ε - 1 ∈ periodFiltration K N c := by
  have hLpos := orbitLog_mem_posIdeal (K := K) hc₀ hc ε
  have h := (isTopologicallyNilpotent_of_mem_posIdeal' hLpos).exp_sub_one_mem
    (I := periodIdeal K N c) (mem_periodIdeal.2 (orbitLog_mem_periodFiltration hc₀.le hc ε))
  rw [orbitZeta_def, ← coe_exp_of_mem_posIdeal hLpos]
  simpa using h

/-- The orbit zeta function is a unit. -/
theorem isUnit_orbitZeta (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    IsUnit (orbitZeta K N γ ε) := by
  obtain ⟨c, hc₀, hc⟩ := hfin.exists_gt_forall_le hpos
  have hLpos := orbitLog_mem_posIdeal (K := K) hc₀ hc ε
  rw [orbitZeta_def, ← coe_exp_of_mem_posIdeal hLpos,
    ← coe_expMulEquiv_apply (K := K) (N := N) ⟨_, hLpos⟩]
  exact (Units.isUnit _).map (nonnegSubring K N).subtype

/-- The orbit logarithm of a single orbit whose iterates have signs `ε (k + 1) = ε 1 * σ ^ k` is
`-(ε 1 * σ)` times the logarithm of `1 - σ e^g`. -/
private theorem hasSum_single_iterate {g : H} (hg : 0 < N g) (ε : ℕ → ℤ) (σ : ℤˣ)
    (hε : ∀ k, ε (k + 1) = ε 1 * σ ^ k) :
    HasSum (fun k : ℕ => (single ((k + 1) • g) (algebraMap ℚ K ((ε (k + 1) : ℚ) / (k + 1 : ℕ))) :
      NovikovSeries K H N)) ((-(ε 1 * σ) : ℤ) •
        ((NormedSpace.log ((unitsOneSubSingle hg ((σ : ℤ) : K) : nonnegSubring K N)) :
          nonnegSubring K N) : NovikovSeries K H N)) := by
  have h := ((isTopologicallyNilpotent_of_mem_posIdeal' (single_mem_posIdeal hg ((σ : ℤ) : K))
    ).hasSum_log_one_sub.map (nonnegSubring K N).subtype continuous_subtype_val).const_smul
      (-(ε 1 * σ) : ℤ)
  rw [Subring.coe_subtype] at h
  rw [val_unitsOneSubSingle]
  convert h using 1
  funext k
  simp only [Function.comp_apply, NegMemClass.coe_neg, coe_smul_nonnegSubring,
    SubmonoidClass.coe_pow, single_pow, smul_single, smul_neg, ← single_neg]
  congr 1
  have hq : ((ε (k + 1) : ℚ) / (k + 1 : ℕ)) =
      ((-(ε 1 * σ) : ℤ) : ℚ) * -(((k + 1 : ℕ) : ℚ)⁻¹ * ((σ : ℤ) : ℚ) ^ (k + 1)) := by
    rw [hε]
    rcases Int.units_eq_one_or σ with rfl | rfl <;> push_cast <;> ring
  rw [hq]
  simp [Algebra.smul_def]

/-- **The product formula.** If the signs of the iterates of each orbit form a geometric sequence,
`ε i (k + 1) = ε i 1 * σ i ^ k` with `σ i = ±1`, then the orbit zeta function is the Euler product
`∏ᵢ (1 - σ i e^(γ i)) ^ (-(ε i 1 * σ i))`. -/
theorem orbitZeta_eq_eulerProduct (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) (σ : ι → ℤˣ)
    (hε : ∀ i k, ε i (k + 1) = ε i 1 * σ i ^ k) :
    orbitZeta K N γ ε =
      eulerProduct γ hpos (fun i => ((σ i : ℤ) : K)) (fun i => -(ε i 1 * σ i)) := by
  obtain ⟨c, hc₀, hc⟩ := hfin.exists_gt_forall_le hpos
  have hLpos := orbitLog_mem_posIdeal (K := K) hc₀ hc ε
  -- `u i = 1 - σ i e^(γ i)` is a principal unit for the positive ideal; `ℓ i` is the multiple
  -- `-(ε i 1 * σ i) • log (u i)` of its logarithm.
  let u (i : ι) := unitsOneSubSingle (hpos i) ((σ i : ℤ) : K)
  have hu (i : ι) : u i ∈ (posIdeal K N).principalUnitGroup :=
    unitsOneSubSingle_mem_principalUnitGroup_posIdeal (hpos i) _
  let ℓ (i : ι) : posIdeal K N := (-(ε i 1 * σ i) : ℤ) •
    ((expMulEquiv K N).symm ⟨u i, hu i⟩).toAdd
  have hℓ (i : ι) : ((ℓ i : nonnegSubring K N) : NovikovSeries K H N) =
      (-(ε i 1 * σ i) : ℤ) •
        ((NormedSpace.log (u i : nonnegSubring K N) : nonnegSubring K N) :
          NovikovSeries K H N) := by
    simp [ℓ]
  -- The orbit logarithm is the sum over the orbits of the `ℓ i`, computed in the nonnegative
  -- subring.
  have hsum : HasSum (fun i => (ℓ i : nonnegSubring K N))
      ⟨_, orbitLog_mem_nonnegSubring (fun i => (hpos i).le) ε⟩ := by
    refine (Topology.IsInducing.subtypeVal.hasSum_iff (g := (nonnegSubring K N).subtype)
      _ _).1 ?_
    refine (hasSum_orbitLog hpos hfin ε).prod_fiberwise fun i => ?_
    rw [Function.comp_apply, Subring.coe_subtype, hℓ]
    exact hasSum_single_iterate (hpos i) (ε i) (σ i) (hε i)
  -- So its exponential is the product of the `exp (ℓ i) = u i ^ (-(ε i 1 * σ i))`.
  have hprod := HasSum.exp_of_mem_ideal (S := nonnegSubring K N) (I := posIdeal K N)
    (fun _ => isTopologicallyNilpotent_of_mem_posIdeal') hsum (fun i => (ℓ i).2) hLpos
  have hexp (i : ι) : NormedSpace.exp (ℓ i : nonnegSubring K N) =
      (↑(u i ^ (-(ε i 1 * σ i))) : nonnegSubring K N) := by
    have h1 : expMulEquiv K N (.ofAdd (ℓ i)) = ⟨u i, hu i⟩ ^ (-(ε i 1 * σ i)) := by
      rw [ofAdd_zsmul, map_zpow, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    rw [← coe_expMulEquiv_apply (K := K) (N := N) (ℓ i), h1, SubgroupClass.coe_zpow]
  have h := hprod.map (nonnegSubring K N).subtype continuous_subtype_val
  rw [Subring.coe_subtype] at h
  rw [orbitZeta_def, ← coe_exp_of_mem_posIdeal hLpos]
  exact h.unique ((hasProd_eulerProduct hfin _ _).congr_fun fun i => by simp [hexp, u])

/-- **Integrality of the orbit zeta function.** Under the hypotheses of the product formula, the
orbit zeta function is the image of the Euler product `∏ᵢ (1 - σ i e^(γ i)) ^ (-(ε i 1 * σ i))`
with integer coefficients. -/
theorem orbitZeta_eq_mapRingHom_eulerProduct (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) (σ : ι → ℤˣ)
    (hε : ∀ i k, ε i (k + 1) = ε i 1 * σ i ^ k) :
    orbitZeta K N γ ε = mapRingHom (Int.castRingHom K) (AddMonoidHom.id H) ⟨1, one_pos, by simp⟩
      (eulerProduct γ hpos (fun i => (σ i : ℤ)) (fun i => -(ε i 1 * σ i))) := by
  rw [orbitZeta_eq_eulerProduct hpos hfin ε σ hε, mapRingHom_eulerProduct _ _ _ hpos hfin]
  simp

end OrbitZeta

end TauCeti.NovikovSeries
