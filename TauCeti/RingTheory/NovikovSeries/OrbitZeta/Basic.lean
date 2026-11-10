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

The specialisation of the product formula to the Lefschetz signs `sgn det (1 - f ^ k)` of
linearized return maps `f` is in `TauCeti.RingTheory.NovikovSeries.OrbitZeta.ReturnMap`.

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
* `TauCeti.NovikovSeries.orbitLog_sigma`, `TauCeti.NovikovSeries.orbitZeta_sigma`: listing the
  `i`-th orbit `c i` times multiplies its signs by `c i`.

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

section OrbitZeta

variable {ι H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {γ : ι → H} {K : Type*} [CommRing K]
  [Algebra ℚ K]

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
  rw [orbitZeta_def, ← coe_exp_nonnegSubring ⟨orbitLog K N γ ε, _⟩]
  simpa using h

/-- Positive periods give a positive lower bound for the support of the orbit logarithm, with no
finiteness assumption: if the terms are not summable the orbit logarithm is `0`, and if they are,
only finitely many of them lie below any cutoff. -/
private theorem exists_pos_orbitLog_mem_periodFiltration (hpos : ∀ i, 0 < N (γ i))
    (ε : ι → ℕ → ℤ) : ∃ c > 0, orbitLog K N γ ε ∈ periodFiltration K N c := by
  by_cases hs : Summable fun p : ι × ℕ => (single ((p.2 + 1) • γ p.1)
      (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) : NovikovSeries K H N)
  · have hE := eventually_cofinite.1 (hasBasis_nhds_zero.tendsto_right_iff.1
      hs.tendsto_cofinite_zero 1 trivial)
    obtain ⟨c, hc₀, hc⟩ : ∃ c > 0, ∀ p ∈ hE.toFinset, c ≤ N (γ p.1) := by
      rcases hE.toFinset.eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, fun p hp => by rw [h] at hp; exact absurd hp (Finset.notMem_empty _)⟩
      · obtain ⟨p₀, -, hp₀⟩ := hE.toFinset.exists_min_image (fun p => N (γ p.1)) h
        exact ⟨N (γ p₀.1), hpos _, hp₀⟩
    refine ⟨min c 1, lt_min hc₀ one_pos, tsum_mem (isClosed_periodFiltration _) fun p => ?_⟩
    by_cases hp : p ∈ hE.toFinset
    · exact antitone_periodFiltration ((min_le_left _ _).trans (hc p hp))
        (single_iterate_mem_periodFiltration (hpos p.1).le _ _)
    · exact antitone_periodFiltration (min_le_right _ _) (by simpa using hp)
  · exact ⟨1, one_pos, by rw [orbitLog, tsum_eq_zero_of_not_summable hs]; exact zero_mem _⟩

/-- The orbit zeta function is a unit. -/
theorem isUnit_orbitZeta (hpos : ∀ i, 0 < N (γ i)) (ε : ι → ℕ → ℤ) :
    IsUnit (orbitZeta K N γ ε) := by
  obtain ⟨c, hc₀, hc⟩ := exists_pos_orbitLog_mem_periodFiltration (K := K) hpos ε
  have hLpos : (⟨orbitLog K N γ ε, mem_nonnegSubring.2
      (mem_periodFiltration.1 (antitone_periodFiltration hc₀.le hc))⟩ :
        nonnegSubring K N) ∈ posIdeal K N :=
    mem_posIdeal.2 (exists_pos_mem_periodFiltration_iff.1 ⟨c, hc₀, hc⟩)
  rw [orbitZeta_def, ← coe_exp_nonnegSubring ⟨orbitLog K N γ ε, mem_nonnegSubring.2
    (mem_periodFiltration.1 (antitone_periodFiltration hc₀.le hc))⟩,
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
  rw [orbitZeta_def, ← coe_exp_nonnegSubring ⟨orbitLog K N γ ε, _⟩]
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

/-- A natural multiple of a monomial with rational coefficient is the monomial whose rational
coefficient is scaled by that multiple. -/
private theorem nsmul_single_algebraMap (n : ℕ) (h : H) (q : ℚ) :
    n • (single h (algebraMap ℚ K q) : NovikovSeries K H N) =
      single h (algebraMap ℚ K (n * q)) := by
  rw [smul_single, nsmul_eq_mul, ← map_natCast (algebraMap ℚ K) n, ← _root_.map_mul]

/-- Listing an orbit `c i` times does not change whether the terms of the orbit logarithm are
summable: the terms of the repeated family are those of the original one, and a nonzero natural
multiple of a monomial with rational coefficient lies in a period neighbourhood of `0` exactly
when the monomial does. -/
private theorem summable_repeated_iff (ε : ι → ℕ → ℤ) (c : ι → ℕ) :
    (Summable fun x : (p : ι × ℕ) × Fin (c p.1) => (single ((x.1.2 + 1) • γ x.1.1)
      (algebraMap ℚ K ((ε x.1.1 (x.1.2 + 1) : ℚ) / (x.1.2 + 1 : ℕ))) : NovikovSeries K H N)) ↔
    Summable fun p : ι × ℕ => (single ((p.2 + 1) • γ p.1)
      (algebraMap ℚ K (((c p.1 * ε p.1 (p.2 + 1) : ℤ) : ℚ) / (p.2 + 1 : ℕ))) :
        NovikovSeries K H N) := by
  have key (C : ℝ) (g : H) (r : K) :
      (single g r : NovikovSeries K H N) ∈ periodFiltration K N C ↔ r = 0 ∨ C ≤ N g := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_contra hcon
      rw [not_or, not_le] at hcon
      exact hcon.1 (by simpa using mem_periodFiltration.1 h g hcon.2)
    · rcases h with rfl | h
      · simp
      · exact antitone_periodFiltration h (single_mem_periodFiltration _ _)
  have hmem (C : ℝ) (g : H) (q : ℚ) {n : ℕ} (hn : n ≠ 0) :
      (single g (algebraMap ℚ K (n * q)) : NovikovSeries K H N) ∈ periodFiltration K N C ↔
        (single g (algebraMap ℚ K q) : NovikovSeries K H N) ∈ periodFiltration K N C := by
    rw [key, key]
    refine or_congr_left ⟨fun h0 => ?_, fun h0 => ?_⟩
    · rw [show q = (n : ℚ)⁻¹ * (n * q) by rw [inv_mul_cancel_left₀ (by exact_mod_cast hn)],
        _root_.map_mul, h0, mul_zero]
    · rw [_root_.map_mul, h0, mul_zero]
  have hq (p : ι × ℕ) : (((c p.1 * ε p.1 (p.2 + 1) : ℤ) : ℚ) / (p.2 + 1 : ℕ)) =
      (c p.1 : ℕ) * ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ)) := by
    push_cast
    ring
  simp only [hq]
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero,
    hasBasis_nhds_zero.tendsto_right_iff, hasBasis_nhds_zero.tendsto_right_iff]
  refine forall₂_congr fun C _ => ?_
  simp only [eventually_cofinite, SetLike.mem_coe]
  have gen (g : ι × ℕ → H) (q : ι × ℕ → ℚ) :
      {x : (p : ι × ℕ) × Fin (c p.1) | (single (g x.1) (algebraMap ℚ K (q x.1)) :
        NovikovSeries K H N) ∉ periodFiltration K N C}.Finite ↔
      {p : ι × ℕ | (single (g p) (algebraMap ℚ K ((c p.1 : ℕ) * q p)) :
        NovikovSeries K H N) ∉ periodFiltration K N C}.Finite := by
    have hB (p : ι × ℕ) : (single (g p) (algebraMap ℚ K ((c p.1 : ℕ) * q p)) :
        NovikovSeries K H N) ∉ periodFiltration K N C ↔
        c p.1 ≠ 0 ∧ (single (g p) (algebraMap ℚ K (q p)) :
          NovikovSeries K H N) ∉ periodFiltration K N C := by
      by_cases h0 : c p.1 = 0
      · simp [h0]
      · rw [not_congr (hmem C _ _ h0), and_iff_right h0]
    refine ⟨fun hA => (hA.image Sigma.fst).subset fun p hp => ?_, fun hB' => ?_⟩
    · obtain ⟨hc, hT⟩ := (hB p).1 hp
      exact ⟨⟨p, ⟨0, Nat.pos_of_ne_zero hc⟩⟩, hT, rfl⟩
    · refine (hB'.biUnion fun p _ => Set.finite_range (Sigma.mk p)).subset fun x hx => ?_
      exact Set.mem_biUnion ((hB x.1).2 ⟨(Fin.pos x.2).ne', hx⟩) ⟨x.2, rfl⟩
  exact gen (fun p => (p.2 + 1) • γ p.1) fun p => (ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ)

/-- **Repeated orbits.** The orbit logarithm of the family in which the `i`-th orbit is listed
`c i` times is the orbit logarithm of the original family with the signs of the `i`-th orbit
multiplied by `c i`. -/
theorem orbitLog_sigma (ε : ι → ℕ → ℤ) (c : ι → ℕ) :
    orbitLog K N (fun p : (i : ι) × Fin (c i) => γ p.1) (fun p => ε p.1) =
      orbitLog K N γ (fun i n => c i * ε i n) := by
  -- Group the terms of the repeated family by orbit and iterate: each group has `c i` equal terms.
  let e : ((p : ι × ℕ) × Fin (c p.1)) ≃ ((i : ι) × Fin (c i)) × ℕ :=
    { toFun q := (⟨q.1.1, q.2⟩, q.1.2)
      invFun q := ⟨(q.1.1, q.2), q.1.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have hiff := summable_repeated_iff (K := K) (N := N) (γ := γ) ε c
  by_cases hs : Summable fun p : ι × ℕ => (single ((p.2 + 1) • γ p.1)
      (algebraMap ℚ K (((c p.1 * ε p.1 (p.2 + 1) : ℤ) : ℚ) / (p.2 + 1 : ℕ))) :
        NovikovSeries K H N)
  · have hF := (e.summable_iff (f := fun q : ((i : ι) × Fin (c i)) × ℕ =>
      (single ((q.2 + 1) • γ q.1.1)
        (algebraMap ℚ K ((ε q.1.1 (q.2 + 1) : ℚ) / (q.2 + 1 : ℕ))) : NovikovSeries K H N))).1
      (hiff.2 hs)
    have h := e.hasSum_iff.2 hF.hasSum
    refine (h.sigma fun p => ?_).unique hs.hasSum
    have hc : (single ((p.2 + 1) • γ p.1)
        (algebraMap ℚ K (((c p.1 * ε p.1 (p.2 + 1) : ℤ) : ℚ) / (p.2 + 1 : ℕ))) :
          NovikovSeries K H N) = ∑ _j : Fin (c p.1),
        single ((p.2 + 1) • γ p.1) (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_single_algebraMap]
      congr 2
      push_cast
      ring
    rw [hc]
    exact hasSum_fintype _
  · rw [orbitLog, orbitLog, tsum_eq_zero_of_not_summable hs, tsum_eq_zero_of_not_summable]
    intro h
    exact hs (hiff.1 (e.summable_iff.2 h))

/-- **Repeated orbits.** The orbit zeta function of the family in which the `i`-th orbit is listed
`c i` times is the orbit zeta function of the original family with the signs of the `i`-th orbit
multiplied by `c i`. -/
theorem orbitZeta_sigma (ε : ι → ℕ → ℤ) (c : ι → ℕ) :
    orbitZeta K N (fun p : (i : ι) × Fin (c i) => γ p.1) (fun p => ε p.1) =
      orbitZeta K N γ (fun i n => c i * ε i n) := by
  rw [orbitZeta_def, orbitZeta_def, orbitLog_sigma]

end OrbitZeta

end TauCeti.NovikovSeries
