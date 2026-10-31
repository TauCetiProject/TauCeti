/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Filter.Cofinite.Basic
public import TauCeti.RingTheory.NovikovSeries.ExpLog
public import TauCeti.RingTheory.NovikovSeries.InfiniteProduct
public import TauCeti.RingTheory.NovikovSeries.Norm
public import TauCeti.GroupTheory.OrderOfElement.Basic

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

**Finite covers.** Let `K` be a finite-index subgroup of an additive commutative group `H`, the
deck group of an abelian covering over the intermediate finite covering with deck group `H ⧸ K`.
If `d i` is the order of `γ i` in `H ⧸ K`, the `i`-th primitive orbit has `[H : K] / d i`
primitive lifts to the intermediate covering, each of class `d i • γ i ∈ K`, and the `n`-th
iterate of a lift is the `(d i * n)`-th iterate of the orbit. The norm of the orbit zeta
function over `Nov(R, K, N|K)` is the orbit zeta function of this family of lifts
(`TauCeti.NovikovSeries.algebraNorm_orbitZeta`). Indeed `Norm (exp L) = exp (Tr L)`, and the
trace is `[H : K]` times the restriction of coefficients to `K`, which keeps exactly the
iterates of `γ i` whose order is a multiple of `d i`. No hypothesis on the torsion of `H` or on
the cyclicity of `H ⧸ K` is needed.

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
* `TauCeti.NovikovSeries.algebraNorm_orbitZeta`: the norm of an orbit zeta function along a
  finite-index subgroup is the orbit zeta function of the lifted orbits.

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

/-- **Repeated orbits.** The orbit logarithm of the family in which the `i`-th orbit is listed
`c i` times is the orbit logarithm of the original family with the signs of the `i`-th orbit
multiplied by `c i`. -/
theorem orbitLog_sigma (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) (c : ι → ℕ) :
    orbitLog K N (fun p : (i : ι) × Fin (c i) => γ p.1) (fun p => ε p.1) =
      orbitLog K N γ (fun i n => c i * ε i n) := by
  have hfin' : Tendsto (fun p : (i : ι) × Fin (c i) => N (γ p.1)) cofinite atTop :=
    hfin.comp (Tendsto.cofinite_of_finite_preimage_singleton fun i => by
      rw [← Set.range_sigmaMk]
      exact (Set.finite_range _).to_subtype)
  -- Group the terms of the repeated family by orbit and iterate: each group has `c i` equal terms.
  let e : ((p : ι × ℕ) × Fin (c p.1)) ≃ ((i : ι) × Fin (c i)) × ℕ :=
    { toFun q := (⟨q.1.1, q.2⟩, q.1.2)
      invFun q := ⟨(q.1.1, q.2), q.1.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have h := e.hasSum_iff.2 (hasSum_orbitLog (K := K) (fun p => hpos p.1) hfin' fun p => ε p.1)
  refine (h.sigma fun p => ?_).unique (hasSum_orbitLog hpos hfin fun i n => c i * ε i n)
  have hc : (single ((p.2 + 1) • γ p.1)
      (algebraMap ℚ K (((c p.1 * ε p.1 (p.2 + 1) : ℤ) : ℚ) / (p.2 + 1 : ℕ))) :
        NovikovSeries K H N) = ∑ _j : Fin (c p.1),
      single ((p.2 + 1) • γ p.1) (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_single, nsmul_eq_mul,
      ← map_natCast (algebraMap ℚ K) (c p.1), ← _root_.map_mul]
    congr 2
    push_cast
    ring
  rw [hc]
  exact hasSum_fintype _

/-- **Repeated orbits.** The orbit zeta function of the family in which the `i`-th orbit is listed
`c i` times is the orbit zeta function of the original family with the signs of the `i`-th orbit
multiplied by `c i`. -/
theorem orbitZeta_sigma (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) (c : ι → ℕ) :
    orbitZeta K N (fun p : (i : ι) × Fin (c i) => γ p.1) (fun p => ε p.1) =
      orbitZeta K N γ (fun i n => c i * ε i n) := by
  rw [orbitZeta_def, orbitZeta_def, orbitLog_sigma hpos hfin]

end OrbitZeta

section FiniteCover

variable {ι H R : Type*} [AddCommGroup H] {N : H →+ ℝ} {γ : ι → H} [CommRing R] [Algebra ℚ R]
  (K : AddSubgroup H) [K.FiniteIndex]

/-- The least positive multiple of an orbit class lying in `K` has positive period, and these
periods tend to `∞` along with those of the orbit classes. -/
private theorem pos_tendsto_period_nsmul_addOrderOf (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) :
    (∀ i, 0 < N.comp K.subtype ⟨addOrderOf (γ i : H ⧸ K) • γ i,
      (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩) ∧
      Tendsto (fun i => N.comp K.subtype ⟨addOrderOf (γ i : H ⧸ K) • γ i,
        (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩) cofinite atTop := by
  have hle (i : ι) : N (γ i) ≤ N.comp K.subtype ⟨addOrderOf (γ i : H ⧸ K) • γ i,
      (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩ := by
    simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, map_nsmul, nsmul_eq_mul]
    exact le_mul_of_one_le_left (hpos i).le (by exact_mod_cast addOrderOf_pos _)
  exact ⟨fun i => (hpos i).trans_le (hle i), tendsto_atTop_mono hle hfin⟩

/-- `[H : K]` times the restriction to `K` of an orbit logarithm is the orbit logarithm over `K`
of the least multiples `d i • γ i` lying in `K`, with the signs of the iterates `d i * n` scaled
by `[H : K] / d i`, where `d i` is the order of `γ i` in `H ⧸ K`. -/
private theorem index_smul_comap_orbitLog (hpos : ∀ i, 0 < N (γ i))
    (hfin : Tendsto (fun i => N (γ i)) cofinite atTop) (ε : ι → ℕ → ℤ) :
    K.index • comap K.subtype (exists_period_rescale_subtype K) (by simp) (orbitLog R N γ ε) =
      orbitLog R (N.comp K.subtype)
        (fun i => ⟨addOrderOf (γ i : H ⧸ K) • γ i,
          (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩)
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
  rw [show (addOrderOf (γ i : H ⧸ K) * (k + 1)) • γ i =
      K.subtype ((k + 1) • ⟨addOrderOf (γ i : H ⧸ K) • γ i,
        (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩) by
      simp [smul_smul, mul_comm],
    comap_single_of_injective _ _ _ Subtype.val_injective, smul_single, nsmul_eq_mul,
    ← map_natCast (algebraMap ℚ R), ← _root_.map_mul]
  congr 2
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
        (fun p : (i : ι) × Fin (K.index / addOrderOf (γ i : H ⧸ K)) =>
          ⟨addOrderOf (γ p.1 : H ⧸ K) • γ p.1,
            (QuotientAddGroup.addOrderOf_mk_dvd_iff_nsmul_mem K _ _).1 dvd_rfl⟩)
        (fun p n => ε p.1 (addOrderOf (γ p.1 : H ⧸ K) * n)) := by
  obtain ⟨hpos', hfin'⟩ := pos_tendsto_period_nsmul_addOrderOf K hpos hfin
  obtain ⟨c, hc₀, hc⟩ := hfin.exists_gt_forall_le hpos
  have h := algebraNorm_exp K (orbitLog_mem_posIdeal (K := R) hc₀ hc ε)
  dsimp only at h
  rw [orbitZeta_def, h, trace_eq_index_smul_comap (exists_period_rescale_subtype K) (by simp),
    index_smul_comap_orbitLog K hpos hfin ε]
  exact (orbitZeta_sigma hpos' hfin' (fun i n => ε i (addOrderOf (γ i : H ⧸ K) * n))
    fun i => K.index / addOrderOf (γ i : H ⧸ K)).symm

end FiniteCover

end TauCeti.NovikovSeries
