/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovSeries.ExpLog
public import TauCeti.RingTheory.NovikovSeries.Functoriality
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
*Euler product* (`TauCeti.NovikovSeries.eulerProduct`)

`∏ᵢ (1 - r i e^(γ i)) ^ m i`

converges in the period topology, since its factors are units of the nonnegative subring congruent
to `1` above the period `N (γ i)`. It is a unit with inverse the Euler product with exponents
`-m`, and it is natural in the coefficient ring and in exponent maps rescaling periods
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

* `TauCeti.NovikovSeries.eulerProduct`: the Euler product `∏ᵢ (1 - r i e^(γ i)) ^ m i`.
* `TauCeti.NovikovSeries.orbitLog`: the orbit logarithm `∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) ·
  e^((k + 1) • γ i)`.
* `TauCeti.NovikovSeries.orbitZeta`: the orbit zeta function, the exponential of the orbit
  logarithm.

## Main results

* `TauCeti.NovikovSeries.hasProd_eulerProduct`, `TauCeti.NovikovSeries.isUnit_eulerProduct`,
  `TauCeti.NovikovSeries.eulerProduct_sub_one_mem_periodFiltration`: convergence of the Euler
  product, which is a unit congruent to `1` above every lower bound of the periods.
* `TauCeti.NovikovSeries.mapRingHom_eulerProduct`: naturality of the Euler product.
* `TauCeti.NovikovSeries.hasSum_orbitLog`, `TauCeti.NovikovSeries.orbitLog_mem_periodFiltration`:
  convergence and support of the orbit logarithm.
* `TauCeti.NovikovSeries.isUnit_orbitZeta`,
  `TauCeti.NovikovSeries.orbitZeta_sub_one_mem_periodFiltration`: the orbit zeta function is a unit
  congruent to `1` above every lower bound of the periods.
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

/-- A family of positive periods tending to `∞` along the cofinite filter is bounded below by a
positive constant. -/
private theorem exists_pos_le_period (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) : ∃ c, 0 < c ∧ ∀ i, c ≤ N (γ i) := by
  cases isEmpty_or_nonempty ι
  · exact ⟨1, one_pos, isEmptyElim⟩
  · obtain ⟨j, hj⟩ := hfin.exists_forall_le
    exact ⟨N (γ j), hpos j, hj⟩

/-- Only finitely many periods of a family tending to `∞` along the cofinite filter lie below a
cutoff. -/
private theorem finite_setOf_lt_period (hfin : Tendsto (fun i => N (γ i)) cofinite atTop)
    (C : ℝ) : {i | N (γ i) < C}.Finite := by
  simpa only [not_le] using eventually_cofinite.1 (tendsto_atTop.1 hfin C)

section EulerProduct

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Every integer power of `1 - r e^g` is congruent to `1` above the period `N g`. -/
theorem coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration {g : H} (hg : 0 < N g) (r : R)
    (m : ℤ) :
    ((↑(unitsOneSubSingle hg r ^ m) : nonnegSubring R N) : NovikovSeries R H N) - 1 ∈
      periodFiltration R N (N g) := by
  have h : unitsOneSubSingle hg r ∈ (periodIdeal R N (N g)).principalUnitGroup := by
    simpa using neg_mem (single_mem_periodFiltration (R := R) (N := N) g r)
  simpa using Ideal.mem_principalUnitGroup.1 (zpow_mem h m)

variable (γ) in
/-- The **Euler product** `∏ᵢ (1 - r i e^(γ i)) ^ m i` of a family of exponents `γ i` of positive
period, with coefficients `r i` and integer exponents `m i`. It converges when only finitely many
periods `N (γ i)` lie below each cutoff (`TauCeti.NovikovSeries.hasProd_eulerProduct`). -/
def eulerProduct (hγ : ∀ i, 0 < N (γ i)) (r : ι → R) (m : ι → ℤ) : NovikovSeries R H N :=
  ∏' i, ((↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N) : NovikovSeries R H N)

variable {hγ : ∀ i, 0 < N (γ i)}

/-- The Euler product converges in the period topology when only finitely many periods lie below
each cutoff. -/
theorem hasProd_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R)
    (m : ι → ℤ) :
    HasProd (fun i => ((↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N) :
      NovikovSeries R H N)) (eulerProduct γ hγ r m) :=
  (multipliable_of_nonneg_finite_cutoffs fun C => (finite_setOf_lt_period hfin C).subset
    fun i hi => lt_of_not_ge fun hC => hi <| antitone_periodFiltration hC <|
      coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration (hγ i) (r i) (m i)).hasProd

/-- The Euler product lies in the nonnegative subring. -/
theorem eulerProduct_mem_nonnegSubring (r : ι → R) (m : ι → ℤ) :
    eulerProduct γ hγ r m ∈ nonnegSubring R N :=
  tprod_mem isClosed_nonnegSubring fun i => (↑(unitsOneSubSingle (hγ i) (r i) ^ m i) :
    nonnegSubring R N).2

/-- The Euler product is congruent to `1` above every lower bound of the periods. In particular its
coefficients of nonpositive period are those of `1`. -/
theorem eulerProduct_sub_one_mem_periodFiltration
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) {c : ℝ} (hc : ∀ i, c ≤ N (γ i))
    (r : ι → R) (m : ι → ℤ) :
    eulerProduct γ hγ r m - 1 ∈ periodFiltration R N c := by
  have h := tprod_sub_prod_mem_periodFiltration (C := c)
    (f := fun i => (↑(unitsOneSubSingle (hγ i) (r i) ^ m i) : nonnegSubring R N))
    (fun D => (finite_setOf_lt_period hfin D).subset fun i hi => lt_of_not_ge fun hD => hi <|
      antitone_periodFiltration hD <|
        coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration (hγ i) (r i) (m i))
    ∅ fun i _ => antitone_periodFiltration (hc i) <|
      coe_zpow_unitsOneSubSingle_sub_one_mem_periodFiltration (hγ i) (r i) (m i)
  simpa only [Finset.prod_empty, eulerProduct] using h

/-- The Euler product with all exponents `0` is `1`. -/
@[simp]
theorem eulerProduct_zero (r : ι → R) : eulerProduct γ hγ r 0 = 1 := by
  simp [eulerProduct]

/-- Euler products of the same factors multiply by adding exponents. -/
theorem eulerProduct_mul_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop)
    (r : ι → R) (m m' : ι → ℤ) :
    eulerProduct γ hγ r m * eulerProduct γ hγ r m' = eulerProduct γ hγ r (m + m') := by
  rw [eulerProduct, eulerProduct, ← (hasProd_eulerProduct hfin r m).multipliable.tprod_mul
    (hasProd_eulerProduct hfin r m').multipliable, eulerProduct]
  simp [zpow_add]

/-- The Euler product is a unit, with inverse the Euler product with the opposite exponents. -/
theorem isUnit_eulerProduct (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R)
    (m : ι → ℤ) : IsUnit (eulerProduct γ hγ r m) :=
  IsUnit.of_mul_eq_one _ <| by rw [eulerProduct_mul_eulerProduct hfin, add_neg_cancel,
    eulerProduct_zero]

/-- **Naturality of the Euler product.** The pushforward along a coefficient homomorphism `ρ` and
an exponent homomorphism `φ` rescaling periods by a positive constant sends the Euler product of
the factors `1 - r i e^(γ i)` to that of the factors `1 - ρ (r i) e^(φ (γ i))`, with the same
exponents. -/
theorem mapRingHom_eulerProduct {H' : Type*} [AddCommMonoid H'] {N' : H' →+ ℝ} (ρ : R →+* S)
    (φ : H →+ H') (hφ : ∃ c > 0, ∀ h, N' (φ h) = c * N h) (hγ' : ∀ i, 0 < N' (φ (γ i)))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (r : ι → R) (m : ι → ℤ) :
    mapRingHom ρ φ hφ (eulerProduct γ hγ r m) =
      eulerProduct (fun i => φ (γ i)) hγ' (fun i => ρ (r i)) m := by
  rw [eulerProduct, (hasProd_eulerProduct hfin r m).multipliable.map_tprod _
    (continuous_mapRingHom ρ φ hφ), eulerProduct]
  refine tprod_congr fun i => ?_
  have hu : Units.map (mapNonnegSubring ρ φ hφ : nonnegSubring R N →* nonnegSubring S N')
      (unitsOneSubSingle (hγ i) (r i)) = unitsOneSubSingle (hγ' i) (ρ (r i)) :=
    Units.ext <| Subtype.ext <| by
      rw [Units.coe_map, MonoidHom.coe_ofClass, coe_mapNonnegSubring, ← mapRingHom_apply,
        coe_unitsOneSubSingle, coe_unitsOneSubSingle, map_sub, map_one, mapRingHom_apply,
        map_single, AddMonoidHom.coe_ofClass]
  rw [← hu, ← map_zpow, Units.coe_map, MonoidHom.coe_ofClass, coe_mapNonnegSubring,
    mapRingHom_apply]

end EulerProduct

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

/-- The term of the orbit logarithm of the `(k + 1)`-fold iterate of an orbit of class `g` lies
above the period `N g` when `N g ≥ 0`. -/
private theorem single_iterate_mem_periodFiltration {g : H} (hg : 0 ≤ N g) (k : ℕ) (q : ℚ) :
    (single ((k + 1) • g) (algebraMap ℚ K q) : NovikovSeries K H N) ∈ periodFiltration K N (N g) :=
  antitone_periodFiltration (by
    rw [map_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
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
  obtain ⟨c, hc, hcγ⟩ := exists_pos_le_period hpos hfin
  -- A term below the cutoff `C` comes from an orbit of period below `C`, iterated fewer than
  -- `C / c` times.
  refine ((finite_setOf_lt_period hfin C).prod (Set.finite_Iio ⌈C / c⌉₊)).subset ?_
  rintro ⟨i, k⟩ hik
  have hlt : ((k : ℝ) + 1) * N (γ i) < C := by
    refine lt_of_not_ge fun hC =>
      hik (antitone_periodFiltration ?_ (single_mem_periodFiltration _ _))
    rwa [map_nsmul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  have hk : (k : ℝ) < C / c := by
    rw [lt_div_iff₀ hc]
    nlinarith [hcγ i, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  refine ⟨?_, Nat.lt_ceil.2 hk⟩
  change N (γ i) < C
  nlinarith [hpos i, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The orbit logarithm lies above every nonnegative lower bound of the periods. -/
theorem orbitLog_mem_periodFiltration {c : ℝ} (hc₀ : 0 ≤ c) (hc : ∀ i, c ≤ N (γ i))
    (ε : ι → ℕ → ℤ) : orbitLog K N γ ε ∈ periodFiltration K N c :=
  tsum_mem (isClosed_periodFiltration c) fun p =>
    antitone_periodFiltration (hc p.1) (single_iterate_mem_periodFiltration (hc₀.trans (hc p.1))
      _ _)

/-- The orbit logarithm, as an element of the positive ideal. -/
private theorem orbitLog_mem_posIdeal (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    ∃ hL : orbitLog K N γ ε ∈ nonnegSubring K N, ⟨_, hL⟩ ∈ posIdeal K N := by
  obtain ⟨c, hc, hcγ⟩ := exists_pos_le_period hpos hfin
  have hL := orbitLog_mem_periodFiltration (K := K) hc.le hcγ ε
  exact ⟨mem_nonnegSubring.2 (mem_periodFiltration.1 (antitone_periodFiltration hc.le hL)),
    mem_posIdeal.2 (exists_pos_mem_periodFiltration_iff.1 ⟨c, hc, hL⟩)⟩

/-- The orbit zeta function is congruent to `1` above every positive lower bound of the periods.
In particular its coefficients of nonpositive period are those of `1`. -/
theorem orbitZeta_sub_one_mem_periodFiltration {c : ℝ} (hc₀ : 0 < c) (hc : ∀ i, c ≤ N (γ i))
    (ε : ι → ℕ → ℤ) : orbitZeta K N γ ε - 1 ∈ periodFiltration K N c := by
  have hL := orbitLog_mem_periodFiltration hc₀.le hc ε (K := K)
  have hL₀ : orbitLog K N γ ε ∈ nonnegSubring K N :=
    mem_nonnegSubring.2 (mem_periodFiltration.1 (antitone_periodFiltration hc₀.le hL))
  have hLpos : (⟨_, hL₀⟩ : nonnegSubring K N) ∈ posIdeal K N :=
    mem_posIdeal.2 (exists_pos_mem_periodFiltration_iff.1 ⟨c, hc₀, hL⟩)
  have h := (isTopologicallyNilpotent_of_mem_posIdeal' hLpos).exp_sub_one_mem
    (I := periodIdeal K N c) (mem_periodIdeal.2 hL)
  rw [orbitZeta, ← coe_exp_of_mem_posIdeal hLpos]
  simpa using h

/-- The orbit zeta function is a unit. -/
theorem isUnit_orbitZeta (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    IsUnit (orbitZeta K N γ ε) := by
  obtain ⟨hL₀, hLpos⟩ := orbitLog_mem_posIdeal hpos hfin ε (K := K)
  rw [orbitZeta, ← coe_exp_of_mem_posIdeal hLpos,
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
    rcases Int.units_eq_one_or σ with rfl | rfl
    · push_cast
      ring
    · push_cast
      ring
  rw [hq, _root_.map_mul, _root_.map_neg, _root_.map_mul, map_intCast, map_pow, map_intCast,
    zsmul_eq_mul, Algebra.smul_def, mul_neg]

/-- **The product formula.** If the signs of the iterates of each orbit form a geometric sequence,
`ε i (k + 1) = ε i 1 * σ i ^ k` with `σ i = ±1`, then the orbit zeta function is the Euler product
`∏ᵢ (1 - σ i e^(γ i)) ^ (-(ε i 1 * σ i))`. -/
theorem orbitZeta_eq_eulerProduct (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) (σ : ι → ℤˣ)
    (hε : ∀ i k, ε i (k + 1) = ε i 1 * σ i ^ k) :
    orbitZeta K N γ ε =
      eulerProduct γ hpos (fun i => ((σ i : ℤ) : K)) (fun i => -(ε i 1 * σ i)) := by
  obtain ⟨hL₀, hLpos⟩ := orbitLog_mem_posIdeal hpos hfin ε (K := K)
  -- `u i = 1 - σ i e^(γ i)` is a principal unit for the positive ideal; `ℓ i` is the multiple
  -- `-(ε i 1 * σ i) • log (u i)` of its logarithm.
  let u (i : ι) := unitsOneSubSingle (hpos i) ((σ i : ℤ) : K)
  have hu (i : ι) : u i ∈ (posIdeal K N).principalUnitGroup := by
    rw [Ideal.mem_principalUnitGroup, val_unitsOneSubSingle, sub_sub_cancel_left]
    exact neg_mem (single_mem_posIdeal (hpos i) ((σ i : ℤ) : K))
  let ℓ (i : ι) : posIdeal K N := (-(ε i 1 * σ i) : ℤ) •
    ((expMulEquiv K N).symm ⟨u i, hu i⟩).toAdd
  have hℓ (i : ι) : ((ℓ i : nonnegSubring K N) : NovikovSeries K H N) =
      (-(ε i 1 * σ i) : ℤ) •
        ((NormedSpace.log (u i : nonnegSubring K N) : nonnegSubring K N) :
          NovikovSeries K H N) := by
    simp [ℓ]
  -- The orbit logarithm is the sum over the orbits of the `ℓ i`, computed in the nonnegative
  -- subring.
  have hsum : HasSum (fun i => (ℓ i : nonnegSubring K N)) ⟨_, hL₀⟩ := by
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
  rw [orbitZeta, ← coe_exp_of_mem_posIdeal hLpos, eulerProduct, ← h.tprod_eq]
  exact tprod_congr fun i => by simp [hexp, u]

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
