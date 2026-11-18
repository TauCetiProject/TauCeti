/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.BaseChange
public import TauCeti.RingTheory.FormalGroup.Hazewinkel.FunctionalEquation
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
public import TauCeti.RingTheory.MvPolynomial.Expand
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Hazewinkel's integral polynomial law

The rational law with logarithm `∑ mₙ X^(pⁿ)` descends to a commutative formal group
law over `ℤ[v₁, v₂, …]`. Its specialization defines `hazewinkelIntegralFormalGroup p v`
for a family `v` in any commutative ring, including rings with torsion. Over a
`ℚ`-algebra this recovers `hazewinkelFormalGroup p v`, and hence its logarithm
and Hazewinkel recursion.

Integrality follows from the functional equation with coefficient endomorphism
`vᵢ ↦ vᵢ^p`: expansion of an integer polynomial lifts Frobenius modulo `p`.
In particular one may extend the integral law to `ℤ_(p)[v₁, v₂, …]`; no
classification of p-typical laws over rings with torsion is asserted here.

Degreewise comparison via Lazard's `2`-cocycle `C_{p^(n + 1)}`
(`TauCeti.le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le`,
`TauCeti.homogeneousComponent_hazewinkelIntegralFormalGroup_sub`) gives parameter recovery from
order bounds (`TauCeti.eq_of_le_order_hazewinkelIntegralFormalGroup_sub`), universal injectivity
over every commutative ring (`TauCeti.hazewinkelIntegralFormalGroup_injective`), and parameter
descent along injective ring homomorphisms
(`TauCeti.exists_hazewinkelIntegralFormalGroup_eq_of_map_eq`).

## References

* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*,
  J. Pure Appl. Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- Every coefficient of the rational universal Hazewinkel law is an integer polynomial
in its generators. -/
private theorem coeff_hazewinkelFormalGroup_X_mem_range (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d
      (hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)).toPowerSeries ∈
        (MvPolynomial.map (Int.castRingHom ℚ) :
          MvPolynomial ℕ+ ℤ →+* MvPolynomial ℕ+ ℚ).range := by
  apply coeff_hazewinkelFormalGroup_mem (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)
    (MvPolynomial.expand p).toRingHom
  · rintro a ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := MvPolynomial.natCast_dvd_expand_sub_pow p f
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) g, ⟨g, rfl⟩, ?_⟩
    simpa only [map_sub, MvPolynomial.map_expand, map_pow, map_mul, map_natCast,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
      congrArg (MvPolynomial.map (Int.castRingHom ℚ)) hg
  · intro j
    exact MvPolynomial.expand_X p j
  · intro j
    exact ⟨MvPolynomial.X j, MvPolynomial.map_X _ _⟩

/-- Coefficientwise descent of the rational universal law. -/
private def integralSeries : MvPowerSeries (Fin 2) (MvPolynomial ℕ+ ℤ) :=
  fun d ↦ (coeff_hazewinkelFormalGroup_X_mem_range p d).choose

private theorem map_integralSeries :
    (integralSeries p).map (MvPolynomial.map (Int.castRingHom ℚ)) =
      (hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ)).toPowerSeries := by
  ext1 d
  exact (coeff_hazewinkelFormalGroup_X_mem_range p d).choose_spec

/-- Hazewinkel's commutative formal group law over the integer polynomial ring
on the generators `v₁, v₂, …`. -/
def universalHazewinkelIntegralFormalGroup : FormalGroup (MvPolynomial ℕ+ ℤ) :=
  FormalGroup.ofMap (MvPolynomial.map (Int.castRingHom ℚ))
    (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)
    (integralSeries p) (hazewinkelFormalGroup p MvPolynomial.X) (map_integralSeries p)

/-- Extending the integral polynomial law to rational coefficients recovers the law
defined by Hazewinkel's logarithm. -/
@[simp high] -- Prefer the rational comparison to the general specialization rule.
theorem map_intCast_universalHazewinkelIntegralFormalGroup :
    (universalHazewinkelIntegralFormalGroup p).map (MvPolynomial.map (Int.castRingHom ℚ)) =
      hazewinkelFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℚ) := by
  apply FormalGroup.map_ofMap

instance : (universalHazewinkelIntegralFormalGroup p).IsComm := by
  have : ((universalHazewinkelIntegralFormalGroup p).map
      (MvPolynomial.map (Int.castRingHom ℚ))).IsComm := by
    rw [map_intCast_universalHazewinkelIntegralFormalGroup]
    infer_instance
  exact FormalGroup.isComm_of_map
    (MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

/-- The integral Hazewinkel formal group law specialized at a family of generators in
an arbitrary commutative ring. -/
def hazewinkelIntegralFormalGroup (v : ℕ+ → R) : FormalGroup R :=
  (universalHazewinkelIntegralFormalGroup p).map (MvPolynomial.eval₂Hom (Int.castRingHom R) v)

/-- Specialization of the integral polynomial law is coefficient evaluation. -/
theorem hazewinkelIntegralFormalGroup_def (v : ℕ+ → R) :
    hazewinkelIntegralFormalGroup p v =
      (universalHazewinkelIntegralFormalGroup p).map
        (MvPolynomial.eval₂Hom (Int.castRingHom R) v) :=
  (rfl)

instance (v : ℕ+ → R) : (hazewinkelIntegralFormalGroup p v).IsComm := by
  rw [hazewinkelIntegralFormalGroup_def]
  infer_instance

/-- Specialization of the integral Hazewinkel law commutes with arbitrary coefficient maps,
including maps to rings with torsion. -/
@[simp]
theorem map_hazewinkelIntegralFormalGroup (v : ℕ+ → R) (f : R →+* S) :
    (hazewinkelIntegralFormalGroup p v).map f = hazewinkelIntegralFormalGroup p (f ∘ v) := by
  rw [hazewinkelIntegralFormalGroup_def, hazewinkelIntegralFormalGroup_def, FormalGroup.map_comp]
  congr 1
  ext j
  · simp
  · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]

/-- Specializing at the polynomial generators returns the integral polynomial law. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_X :
    hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ ℤ) =
      universalHazewinkelIntegralFormalGroup p := by
  rw [hazewinkelIntegralFormalGroup_def]
  have h : MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial ℕ+ ℤ)) MvPolynomial.X =
      RingHom.id (MvPolynomial ℕ+ ℤ) := by ext <;> simp
  rw [h, FormalGroup.map_id]

/-- Mapping the integral polynomial law is specialization at the images of its generators. -/
@[simp]
theorem map_universalHazewinkelIntegralFormalGroup
    (f : MvPolynomial ℕ+ ℤ →+* S) :
    (universalHazewinkelIntegralFormalGroup p).map f =
      hazewinkelIntegralFormalGroup p (f ∘ MvPolynomial.X) := by
  rw [← hazewinkelIntegralFormalGroup_X, map_hazewinkelIntegralFormalGroup]

/-- Over a rational algebra, integral specialization agrees with the formal group law
defined using Hazewinkel's logarithm. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup [Algebra ℚ R] (v : ℕ+ → R) :
    hazewinkelIntegralFormalGroup p v = hazewinkelFormalGroup p v := by
  have h : (MvPolynomial.eval₂Hom (algebraMap ℚ R) v).comp
      (MvPolynomial.map (Int.castRingHom ℚ)) = MvPolynomial.eval₂Hom (Int.castRingHom R) v := by
    ext <;> simp
  rw [hazewinkelIntegralFormalGroup_def, ← h, ← FormalGroup.map_comp,
    map_intCast_universalHazewinkelIntegralFormalGroup, map_hazewinkelFormalGroup]
  congr 1
  funext j
  exact MvPolynomial.eval₂_X _ _ _

/-- At `v = 0`, `hazewinkelIntegralFormalGroup p 0` is the additive formal group law `𝔾ₐ`. -/
@[simp]
theorem hazewinkelIntegralFormalGroup_zero :
    hazewinkelIntegralFormalGroup p (0 : ℕ+ → R) = FormalGroup.𝔾ₐ := by
  have h0Q : Int.castRingHom ℚ ∘ (0 : ℕ+ → ℤ) = 0 := funext fun _ ↦ map_zero _
  have h0R : Int.castRingHom R ∘ (0 : ℕ+ → ℤ) = 0 := funext fun _ ↦ map_zero _
  have hZ : hazewinkelIntegralFormalGroup p (0 : ℕ+ → ℤ) = FormalGroup.𝔾ₐ :=
    FormalGroup.map_injective (f := Int.castRingHom ℚ) Int.cast_injective <| by
      dsimp only
      rw [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ,
        hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup, h0Q, hazewinkelFormalGroup_zero]
  simpa only [map_hazewinkelIntegralFormalGroup, FormalGroup.map_𝔾ₐ, h0R] using
    congrArg (fun F : FormalGroup ℤ ↦ F.map (Int.castRingHom R)) hZ

section Comparison

open Finset MvPowerSeries

/-- Over a `ℚ`-algebra, agreeing parameters up to `n` give the degree-`p ^ (n + 1)` order bound
and leading Lazard cocycle difference for `hazewinkelFormalGroup`. -/
private theorem hazewinkelFormalGroup_sub_of_forall_le_rat {K : Type*} [CommRing K] [Algebra ℚ K]
    {v w : ℕ+ → K} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤
        ((hazewinkelFormalGroup p v).toPowerSeries -
          (hazewinkelFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelFormalGroup p v).toPowerSeries -
          (hazewinkelFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) K :
            MvPolynomial (Fin 2) K) : MvPowerSeries (Fin 2) K) := by
  have hp : p.Prime := Fact.out
  set N := p ^ (n + 1); have hN0 : N ≠ 0 := pow_ne_zero _ hp.ne_zero
  -- Stage 1: Compare `f_v` and `f_w` to obtain the coordinate change `η = f_w⁻¹ * f_v`.
  obtain ⟨r, hfv, hr0⟩ := exists_hazewinkelLog_eq_add_X_pow_mul hp.one_lt hvw
  let η : FormalCoordinate K := (hazewinkelLog p w)⁻¹ * hazewinkelLog p v
  have hη_smul : η • hazewinkelFormalGroup p v = hazewinkelFormalGroup p w := by
    simp only [η, hazewinkelFormalGroup_def, mul_smul, smul_inv_smul]
  obtain ⟨s, hη_series, hs_c⟩ := FormalCoordinate.exists_toPowerSeries_mul_eq_X_add_X_pow_mul
    (φ := (hazewinkelLog p w)⁻¹) (ψ := hazewinkelLog p v) hN0 (by simpa using hfv)
  have hη_ord : (N : ℕ∞) ≤ (η.toPowerSeries - PowerSeries.X).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by
      rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.2 hk)]
  have hη_coeff : PowerSeries.coeff N (η.toPowerSeries - PowerSeries.X) =
      (p : ℚ)⁻¹ • (v n.succPNat - w n.succPNat) := by
    rw [hη_series, add_sub_cancel_left, PowerSeries.coeff_X_pow_mul', ite_eq_left le_rfl,
      Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, hs_c, map_inv,
      linearCoeff_hazewinkelLog, inv_one, Units.val_one, one_mul, hr0]
  -- Stage 2: Transfer the order bound and leading homogeneous component from `η` to `F_v - F_w`.
  refine ⟨FormalGroup.le_order_sub_of_smul_eq hη_smul hη_ord, ?_⟩
  rw [FormalGroup.homogeneousComponent_sub_of_smul_eq hη_smul hN0 hη_ord, hη_coeff]; congr 1
  have hcoc := lazardGcd_nsmul_lazardCocycle (R := K) hN0
  rw [lazardGcd_prime_pow hp n.succ_ne_zero] at hcoc
  rw [← hcoc, ← Nat.cast_smul_eq_nsmul ℚ, smul_comm _ (p : ℚ), ← smul_assoc,
    smul_inv_smul₀ (Nat.cast_ne_zero.2 hp.ne_zero)]

/-- Rational-to-integral comparison along an injection into a `ℚ`-algebra `K`. -/
private theorem hazewinkelIntegralFormalGroup_sub_of_injective_rat {A K : Type*}
    [CommRing A] [CommRing K] [Algebra ℚ K] {ι : A →+* K} (hι : Function.Injective ι)
    {v w : ℕ+ → A} {n : ℕ} (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) A :
            MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) := by
  set D := (hazewinkelIntegralFormalGroup p v).toPowerSeries -
    (hazewinkelIntegralFormalGroup p w).toPowerSeries
  have hmap_D : D.map ι = (hazewinkelFormalGroup p (ι ∘ v)).toPowerSeries -
      (hazewinkelFormalGroup p (ι ∘ w)).toPowerSeries := by
    simp only [D, map_sub, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
      hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup]
  have hrat := hazewinkelFormalGroup_sub_of_forall_le_rat p (v := ι ∘ v) (w := ι ∘ w)
    (fun i hi ↦ congrArg ι (hvw i hi))
  refine ⟨nat_le_order fun d hd ↦ hι <| by
      rw [map_zero, ← coeff_map, hmap_D]
      exact coeff_of_lt_order ((Nat.cast_lt.mpr hd).trans_le hrat.1),
    ext fun d ↦ hι <| by
      have hcoeff := congrArg (coeff d) hrat.2
      rw [← hmap_D, coeff_homogeneousComponent, coeff_map] at hcoeff
      rw [coeff_homogeneousComponent, apply_ite ι, map_zero, hcoeff]
      simp only [map_neg, MvPolynomial.coeff_coe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul,
        map_sub, ← MvPolynomial.coeff_map, map_lazardCocycle, Function.comp_apply]⟩

/-- Over an arbitrary ring `R`, specialize the universal comparison over `ℤ[v₁, …, w₁, …]`. -/
private theorem hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries).order ∧
      homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
          (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
        -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
            MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  let vU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ MvPolynomial.X (Sum.inl i)
  let wU : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦
    if (i : ℕ) ≤ n then MvPolynomial.X (Sum.inl i) else MvPolynomial.X (Sum.inr i)
  have hU := hazewinkelIntegralFormalGroup_sub_of_injective_rat p
    (ι := MvPolynomial.map (Int.castRingHom ℚ)) (MvPolynomial.map_injective _ Int.cast_injective)
    (v := vU) (w := wU) (n := n) fun _ hi ↦ by simp [vU, wU, hi]
  let ev : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v w)
  have hD_R : ((hazewinkelIntegralFormalGroup p vU).toPowerSeries -
      (hazewinkelIntegralFormalGroup p wU).toPowerSeries).map ev =
      (hazewinkelIntegralFormalGroup p v).toPowerSeries -
        (hazewinkelIntegralFormalGroup p w).toPowerSeries := by
    simp only [map_sub, ← FormalGroup.map_toPowerSeries, map_hazewinkelIntegralFormalGroup,
      (funext fun _ ↦ by simp [ev, vU] : ev ∘ vU = v),
      (funext fun _ ↦ by dsimp [ev, wU]; split_ifs with hi <;> simp [hvw, hi] : ev ∘ wU = w)]
  refine ⟨hD_R ▸ hU.1.trans (le_order_map ev), ext fun d ↦ ?_⟩
  have hcoeff := congrArg (fun f ↦ ev (coeff d f)) hU.2
  rw [coeff_homogeneousComponent, apply_ite ev, map_zero, ← coeff_map, hD_R] at hcoeff
  rw [coeff_homogeneousComponent, hcoeff]
  simp only [map_neg, MvPolynomial.coeff_coe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul,
    map_sub, ← MvPolynomial.coeff_map, map_lazardCocycle, ev, vU, wU, MvPolynomial.eval₂Hom_X',
    Sum.elim_inl, Sum.elim_inr, Nat.succPNat_coe, Nat.not_succ_le_self, ite_false]

/-- **Degreewise congruence of Hazewinkel's integral formal group law**: if `v` and `w` agree up to
index `n`, `hazewinkelIntegralFormalGroup p v` and `w` agree strictly below degree `p^(n + 1)`. -/
theorem le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    ((p ^ (n + 1) : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).1

/-- If `v` and `w` agree on `i ≤ n`, the homogeneous component of degree `p^(n + 1)` of
`hazewinkelIntegralFormalGroup p v - hazewinkelIntegralFormalGroup p w` is
`-(v_{n + 1} - w_{n + 1}) • C_{p^(n + 1)}`. -/
theorem homogeneousComponent_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {n : ℕ}
    (hvw : ∀ i : ℕ+, (i : ℕ) ≤ n → v i = w i) :
    homogeneousComponent (p ^ (n + 1)) ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries) =
      -(((v n.succPNat - w n.succPNat) • lazardCocycle (p ^ (n + 1)) R :
          MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) :=
  (hazewinkelIntegralFormalGroup_sub_of_forall_le p hvw).2

/-- **Parameter recovery from order bounds**: if `hazewinkelIntegralFormalGroup p v` and
`hazewinkelIntegralFormalGroup p w` agree below degree `m`, then `v i = w i` for every `i : ℕ+`
with `p ^ (i : ℕ) < m`. -/
theorem eq_of_le_order_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {m : ℕ}
    (hord : (m : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order)
    {i : ℕ+} (hi : p ^ (i : ℕ) < m) : v i = w i := by
  have hp : p.Prime := Fact.out
  suffices ∀ r, ∀ j : ℕ+, (j : ℕ) ≤ r → p ^ (j : ℕ) < m → v j = w j from this i i le_rfl hi
  intro r; induction r with
  | zero => intro j hj _; have := j.pos; omega
  | succ r ih =>
    intro j hj hpj; rcases lt_or_eq_of_le hj with hlt | heq
    · exact ih j (Nat.lt_succ_iff.mp hlt) hpj
    · obtain rfl : j = r.succPNat := PNat.coe_injective heq
      rw [Nat.succPNat_coe] at hpj
      have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (v := v) (w := w)
        (n := r) fun k hk ↦
          ih k hk ((Nat.pow_le_pow_right hp.pos (Nat.le_succ_of_le hk)).trans_lt hpj)
      rw [homogeneousComponent_of_lt_order_eq_zero ((Nat.cast_lt.mpr hpj).trans_le hord),
        eq_comm, neg_eq_zero] at hhom
      exact sub_eq_zero.mp <| (smul_lazardCocycle_eq_zero_iff
        (hp.two_le.trans (Nat.le_self_pow r.succ_ne_zero p))).mp <|
        MvPolynomial.coe_injective (Fin 2) R (by rwa [MvPolynomial.coe_zero])

/-- If `m ≠ 0` is not a positive power of `p` and `hazewinkelIntegralFormalGroup p v` agrees with
`hazewinkelIntegralFormalGroup p w` below degree `m`, then they agree in degree `m` as well. -/
theorem succ_le_order_hazewinkelIntegralFormalGroup_sub_of_not_pow {v w : ℕ+ → R} {m : ℕ}
    (hm : m ≠ 0) (hpow : ∀ k : ℕ+, p ^ (k : ℕ) ≠ m)
    (hord : (m : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order) :
    ((m + 1 : ℕ) : ℕ∞) ≤ ((hazewinkelIntegralFormalGroup p v).toPowerSeries -
      (hazewinkelIntegralFormalGroup p w).toPowerSeries).order := by
  have hp : p.Prime := Fact.out
  exact (Nat.cast_le.mpr (Nat.lt_pow_succ_log_self hp.one_lt m)).trans <|
    le_order_hazewinkelIntegralFormalGroup_sub_of_forall_le p fun i hi ↦
      eq_of_le_order_hazewinkelIntegralFormalGroup_sub p hord <|
        lt_of_le_of_ne ((Nat.pow_le_pow_right hp.pos hi).trans
          (Nat.pow_log_le_self p hm)) (hpow i)

/-- **Universal injectivity of Hazewinkel's integral formal group law** over every commutative ring
`R` (including rings with arbitrary torsion). -/
theorem hazewinkelIntegralFormalGroup_injective :
    Function.Injective (hazewinkelIntegralFormalGroup p : (ℕ+ → R) → FormalGroup R) :=
  fun _ _ h ↦ funext fun i ↦ eq_of_le_order_hazewinkelIntegralFormalGroup_sub p
    (m := p ^ (i : ℕ) + 1) (by rw [h, sub_self, order_zero]; exact le_top) (Nat.lt_succ_self _)

/-- Two integral Hazewinkel formal group laws coincide if and only if their parameter sequences
agree. -/
@[simp] theorem hazewinkelIntegralFormalGroup_eq_iff {v w : ℕ+ → R} :
    hazewinkelIntegralFormalGroup p v = hazewinkelIntegralFormalGroup p w ↔ v = w :=
  (hazewinkelIntegralFormalGroup_injective p).eq_iff

/-- **Parameter descent for Hazewinkel's integral formal group law**: along any injective ring
homomorphism `ι : A →+* B`, if `G.map ι = hazewinkelIntegralFormalGroup p wB`, then every
parameter `wB i` lies in `ι.range` and `G = hazewinkelIntegralFormalGroup p wA` for some `wA`. -/
theorem exists_hazewinkelIntegralFormalGroup_eq_of_map_eq
    {A B : Type*} [CommRing A] [CommRing B] {ι : A →+* B} (hι : Function.Injective ι)
    {G : FormalGroup A} {wB : ℕ+ → B}
    (hG : G.map ι = hazewinkelIntegralFormalGroup p wB) :
    ∃ wA : ℕ+ → A, G = hazewinkelIntegralFormalGroup p wA ∧ ι ∘ wA = wB := by
  have hp : p.Prime := Fact.out
  -- Descend `wB i` into `ι.range` inductively using the degree-`p ^ (n + 1)` Lazard cocycle.
  have hwB_mem : ∀ n (i : ℕ+), (i : ℕ) ≤ n → wB i ∈ ι.range := fun n ↦ by
    induction n with
    | zero => intro i hi; have := i.pos; omega
    | succ n ih =>
      intro i hi; rcases lt_or_eq_of_le hi with hlt | heq
      · exact ih i (Nat.lt_succ_iff.mp hlt)
      · obtain rfl : i = n.succPNat := PNat.coe_injective heq
        let w_trunc : ℕ+ → A := fun j ↦ if hj : (j : ℕ) ≤ n then (ih j hj).choose else 0
        have htrunc : ∀ j : ℕ+, (j : ℕ) ≤ n → wB j = (ι ∘ w_trunc) j := fun j hj ↦ by
          dsimp only [w_trunc, Function.comp_apply]; rw [dite_eq_left hj]
          exact (ih j hj).choose_spec.symm
        have hhom := homogeneousComponent_hazewinkelIntegralFormalGroup_sub p (n := n) htrunc
        rw [(by simp [w_trunc] : (ι ∘ w_trunc) n.succPNat = 0), sub_zero, ← hG,
          ← map_hazewinkelIntegralFormalGroup] at hhom
        refine mem_range_of_coeff_smul_lazardCocycle_mem ι (m := p ^ (n + 1))
          (hp.two_le.trans (Nat.le_self_pow n.succ_ne_zero p)) fun j hj ↦ ?_
        rw [mem_Icc] at hj
        let d : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 (p ^ (n + 1) - j)
        have hd : d.degree = p ^ (n + 1) := by
          simp [d, Finsupp.degree_eq_sum, Fin.sum_univ_two]; omega
        have hcoeff := congrArg (coeff d) hhom
        rw [coeff_homogeneousComponent, ite_eq_left hd, FormalGroup.map_toPowerSeries,
          FormalGroup.map_toPowerSeries, ← map_sub (MvPowerSeries.map ι), coeff_map, map_neg,
          MvPolynomial.coeff_coe] at hcoeff
        exact ⟨-coeff d _, by rw [map_neg, hcoeff, neg_neg]⟩
  choose wA hwA using fun i : ℕ+ ↦ RingHom.mem_range.mp (hwB_mem i.val i le_rfl)
  refine ⟨wA, FormalGroup.map_injective hι ?_, funext hwA⟩
  dsimp only; rw [hG, map_hazewinkelIntegralFormalGroup]
  exact congrArg _ (funext fun i ↦ (hwA i).symm)

end Comparison

end TauCeti
