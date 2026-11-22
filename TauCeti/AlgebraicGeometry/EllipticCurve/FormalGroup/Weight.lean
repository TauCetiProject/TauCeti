/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.ModularForm
public import TauCeti.RingTheory.FormalGroup.LazardRing.Basic
public import TauCeti.RingTheory.FormalGroup.Rescale.Basic

/-!
# Weights of the formal group of a Weierstrass curve

Give the coefficient `aᵢ` of a Weierstrass equation the weight `i`
(`WeierstrassCurve.coefficientWeight`). The scaling `(x, y) ↦ (u²x, u³y)`, the change of variables
`C = (u, 0, 0, 0)`, multiplies `aᵢ` by `u⁻ⁱ`, and in the formal parameter `z = -x / y` it is the
homothety `z ↦ u⁻¹ z` (`WeierstrassCurve.VariableChange.formalCoordinate_mk`). So the formal group
law of `C • W` is the rescaling `u Ê_W(u⁻¹ X, u⁻¹ Y)` of that of `W`
(`WeierstrassCurve.formalGroup_mk_smul`), whose coefficient of `X^(d 0) Y^(d 1)` is that of `Ê_W`
times `u^-(d 0 + d 1 - 1)`. Testing this on the universal curve shows that the formal group law of
the universal Weierstrass curve over `ℤ[a₁, a₂, a₃, a₄, a₆]` is graded:

* its coefficient of `X^(d 0) Y^(d 1)` is weighted homogeneous of weight `d 0 + d 1 - 1`
  (`WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_formalGroup`);
* the coefficient of `Tⁿ` in its invariant differential has weight `n`
  (`WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_invariantDifferential`), so the lift
  `coeff (p - 1) ω` of the Hasse invariant has weight `p - 1`;
* the coefficient of `Tᵐ` in its `k`-series has weight `m - 1`
  (`WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_nsmulSeries`), so Landweber's
  `vⱼ`, the coefficient of `T^(pʲ)` in the `p`-series, has weight `pʲ - 1`.

Consequently, for a Weierstrass curve over a graded ring whose coefficient `aᵢ` has degree `w i`,
the coefficients of the formal group law, its invariant differential and its `k`-series are
homogeneous of the corresponding degrees (`WeierstrassCurve.coeff_formalGroup_mem` and its
companions). With `w = 2`, the topological degree of `aᵢ` in a ring of graded modular forms, the
homomorphism from the Lazard ring classifying the formal group law is graded
(`WeierstrassCurve.lift_formalGroup_mem`). For the universal curve this makes
`ℤ[a₁, a₂, a₃, a₄, a₆]`, with `aᵢ` in degree `2i`, a graded algebra over the Lazard ring, with
`v₁` homogeneous of degree `2 (p - 1)`.

Modulo `p` the Hasse invariant moreover transforms with weight `p - 1` under the whole
coordinate-change group, not only under the scalings: for every change of variables
`C = (u, r, s, t)` over every commutative ring, `A(C • W) ≡ u^-(p - 1) A(W)` modulo `p`, by
`WeierstrassCurve.VariableChange.natCast_dvd_coeff_invariantDifferential_formalGroup_smul_sub`.
In characteristic `p` this is an equality: the Hasse invariant transforms like a modular form of
weight `p - 1`. The proof compares the `p`-series of the isomorphic formal group laws of `C • W` and
`W`, whose coefficients of `Tᵖ` are `v₁` and are congruent to the Hasse invariant modulo `p`.

## Main results

* `WeierstrassCurve.formalGroup_mk_smul`: the formal group law of `(u, 0, 0, 0) • W` is the
  rescaling of that of `W` by `u⁻¹`.
* `WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_formalGroup`,
  `WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_invariantDifferential` and
  `WeierstrassCurve.Universal.isWeightedHomogeneous_coeff_nsmulSeries`: the weights of the
  coefficients of the universal formal group law, invariant differential and `k`-series.
* `WeierstrassCurve.coeff_formalGroup_mem`, `WeierstrassCurve.coeff_invariantDifferential_mem` and
  `WeierstrassCurve.coeff_nsmulSeries_mem`: the same over a graded coefficient ring.
* `WeierstrassCurve.lift_formalGroup_mem`: the classifying homomorphism from the Lazard ring is
  graded when `aᵢ` has degree `2i`.
* `WeierstrassCurve.VariableChange.natCast_dvd_coeff_invariantDifferential_formalGroup_smul_sub`
  and `WeierstrassCurve.VariableChange.coeff_invariantDifferential_formalGroup_smul`: the
  Hasse invariant transforms with weight `p - 1` modulo `p`, and exactly in characteristic `p`.

## References

* N. M. Katz, *p-adic properties of modular schemes and modular forms*, in *Modular functions of
  one variable III*, Lecture Notes in Math. 350, Springer, 1973, §2.0 (the Hasse invariant as a
  modular form of weight `p - 1` modulo `p`).
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire Bourbaki
  1005 (2009), §3.2.
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and IV.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The scaling `(u, 0, 0, 0)` on the formal group law -/

namespace VariableChange

/-- The formal parameter transition of the scaling `(x, y) ↦ (u²x, u³y)`, the change of variables
`(u, 0, 0, 0)`, is the homothety `z ↦ u⁻¹ z`. -/
@[simp]
theorem formalCoordinate_mk (u : Rˣ) :
    (⟨u, 0, 0, 0⟩ : VariableChange R).formalCoordinate W = FormalCoordinate.homothety u⁻¹ := by
  -- The denominator `u³ - su²z - t w(z)` of the transition is the constant `u³`.
  have hinv : PowerSeries.invOfUnit (PowerSeries.C (u : R) ^ 3) (u ^ 3) =
      PowerSeries.C (↑u⁻¹ ^ 3 : R) := by
    have h := PowerSeries.mul_invOfUnit (PowerSeries.C (u : R) ^ 3) (u ^ 3) (by simp)
    have hu : PowerSeries.C (↑u⁻¹ ^ 3 : R) * PowerSeries.C (u : R) ^ 3 = 1 := by
      rw [← map_pow, ← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one]
    linear_combination PowerSeries.C (↑u⁻¹ ^ 3 : R) * h -
      PowerSeries.invOfUnit (PowerSeries.C (u : R) ^ 3) (u ^ 3) * hu
  refine FormalCoordinate.ext ?_
  rw [formalCoordinate_toPowerSeries, formalDenom_def, FormalCoordinate.toPowerSeries_homothety]
  simp only [map_zero, zero_mul, add_zero, sub_zero]
  rw [hinv, PowerSeries.smul_eq_C_mul, mul_right_comm, ← map_pow, ← map_mul,
    ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 3
  group

end VariableChange

/-- **The formal group law under a scaling.** The formal group law of `(u, 0, 0, 0) • W`, whose
coefficients are `u⁻ⁱ aᵢ`, is the rescaling `u Ê_W(u⁻¹ X, u⁻¹ Y)` of that of `W`. -/
@[simp]
theorem formalGroup_mk_smul (u : Rˣ) :
    formalGroup ((⟨u, 0, 0, 0⟩ : VariableChange R) • W) = (formalGroup W).rescale ↑u⁻¹ := by
  rw [VariableChange.formalGroup_smul, VariableChange.formalCoordinate_mk, ← map_inv, inv_inv,
    FormalGroup.homothety_smul]

/-! ### Weights over the universal Weierstrass curve -/

/-- Specializing a coefficient of the universal formal group law at `W` gives the corresponding
coefficient of the formal group law of `W`. -/
private theorem specialize_coeff_formalGroup (d : Fin 2 →₀ ℕ) :
    W.specialize (MvPowerSeries.coeff d (formalGroup Universal.curve).toPowerSeries) =
      MvPowerSeries.coeff d (formalGroup W).toPowerSeries := by
  rw [← MvPowerSeries.coeff_map, ← FormalGroup.map_toPowerSeries, ← map_formalGroup]
  simp only [map_specialize]

/-- Specializing a coefficient of the universal invariant differential at `W` gives the
corresponding coefficient of the invariant differential of `W`. -/
private theorem specialize_coeff_invariantDifferential (n : ℕ) :
    W.specialize (PowerSeries.coeff n (formalGroup Universal.curve).invariantDifferential) =
      PowerSeries.coeff n (formalGroup W).invariantDifferential := by
  rw [← PowerSeries.coeff_map, FormalGroup.map_invariantDifferential, ← map_formalGroup]
  simp only [map_specialize]

/-- Specializing a coefficient of the universal `k`-series at `W` gives the corresponding
coefficient of the `k`-series of `W`. -/
private theorem specialize_coeff_nsmulSeries (k m : ℕ) :
    W.specialize (PowerSeries.coeff m ((formalGroup Universal.curve).nsmulSeries k)) =
      PowerSeries.coeff m ((formalGroup W).nsmulSeries k) := by
  rw [← PowerSeries.coeff_map, FormalGroup.map_nsmulSeries, ← map_formalGroup]
  simp only [map_specialize]

namespace Universal

/-- **The universal formal group law is graded.** The coefficient of `X^(d 0) Y^(d 1)` in the
formal group law of the universal Weierstrass curve is weighted homogeneous of weight
`d 0 + d 1 - 1`, for the weight `i` of `aᵢ`. -/
theorem isWeightedHomogeneous_coeff_formalGroup (d : Fin 2 →₀ ℕ) :
    (MvPowerSeries.coeff d (formalGroup curve).toPowerSeries).IsWeightedHomogeneous
      coefficientWeight (d.degree - 1) :=
  isWeightedHomogeneous_iff_forall_specialize_mk_smul.2 fun _ _ W u ↦ by
    rw [specialize_coeff_formalGroup, specialize_coeff_formalGroup, formalGroup_mk_smul,
      FormalGroup.coeff_rescale]

/-- The coefficient of `Tⁿ` in the invariant differential of the universal Weierstrass curve is
weighted homogeneous of weight `n`. For `n = p - 1` this is the weight `p - 1` of the Hasse
invariant. -/
theorem isWeightedHomogeneous_coeff_invariantDifferential (n : ℕ) :
    (PowerSeries.coeff n (formalGroup curve).invariantDifferential).IsWeightedHomogeneous
      coefficientWeight n :=
  isWeightedHomogeneous_iff_forall_specialize_mk_smul.2 fun _ _ W u ↦ by
    rw [specialize_coeff_invariantDifferential, specialize_coeff_invariantDifferential,
      formalGroup_mk_smul, FormalGroup.invariantDifferential_rescale, PowerSeries.coeff_rescale]

/-- The coefficient of `Tᵐ` in the `k`-series of the universal Weierstrass curve is weighted
homogeneous of weight `m - 1`. In particular Landweber's `vⱼ`, the coefficient of `T^(pʲ)` in the
`p`-series, has weight `pʲ - 1`. -/
theorem isWeightedHomogeneous_coeff_nsmulSeries (k m : ℕ) :
    (PowerSeries.coeff m ((formalGroup curve).nsmulSeries k)).IsWeightedHomogeneous
      coefficientWeight (m - 1) := by
  classical
  let := MvPolynomial.weightedGradedAlgebra ℤ coefficientWeight
  simpa using FormalGroup.coeff_nsmulSeries_mem (formalGroup curve) (w := 1)
    (𝒜 := MvPolynomial.weightedHomogeneousSubmodule ℤ coefficientWeight)
    (fun d ↦ by simpa using isWeightedHomogeneous_coeff_formalGroup d) k m

end Universal

/-! ### Weierstrass curves over graded rings -/

section Graded

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [SetLike.GradedMonoid 𝒜] {W : WeierstrassCurve A} {w : ℕ}

/-- Specializing a polynomial of weight `k` at a Weierstrass curve whose coefficient `aᵢ` has
degree `w i` gives an element of degree `w k`. -/
private theorem specialize_mem {f : MvPolynomial Coeff ℤ} {k : ℕ}
    (hf : f.IsWeightedHomogeneous coefficientWeight k)
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i)) :
    W.specialize f ∈ 𝒜 (w * k) := by
  have hf' : f.IsWeightedHomogeneous (fun i ↦ w * coefficientWeight i) (w * k) :=
    hf.comp_weight (AddMonoidHom.mulLeft w)
  have hspec : W.specialize f = MvPolynomial.aeval (fun i ↦ W.specialize (MvPolynomial.X i)) f :=
    DFunLike.congr_fun (MvPolynomial.aeval_unique W.specialize.toIntAlgHom) f
  rw [hspec, MvPolynomial.aeval_def]
  exact hf'.eval₂_mem (fun r ↦ by simpa using SetLike.intCast_mem_graded 𝒜 r) hW

variable (h₁ : W.a₁ ∈ 𝒜 w) (h₂ : W.a₂ ∈ 𝒜 (w * 2)) (h₃ : W.a₃ ∈ 𝒜 (w * 3))
  (h₄ : W.a₄ ∈ 𝒜 (w * 4)) (h₆ : W.a₆ ∈ 𝒜 (w * 6))
include h₁ h₂ h₃ h₄ h₆

omit [AddSubgroupClass σ A] [SetLike.GradedMonoid 𝒜] in
private theorem specialize_X_mem (i : Coeff) :
    W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i) := by
  cases i <;> simpa [specialize_X]

/-- **A Weierstrass curve over a graded ring has a graded formal group law.** If the coefficient
`aᵢ` of `W` has degree `w i`, then the coefficient of `X^(d 0) Y^(d 1)` in the formal group law
of `W` has degree `w (d 0 + d 1 - 1)`. -/
theorem coeff_formalGroup_mem (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (formalGroup W).toPowerSeries ∈ 𝒜 (w * (d.degree - 1)) := by
  rw [← specialize_coeff_formalGroup]
  exact specialize_mem (Universal.isWeightedHomogeneous_coeff_formalGroup d)
    (specialize_X_mem h₁ h₂ h₃ h₄ h₆)

/-- If the coefficient `aᵢ` of `W` has degree `w i`, then the coefficient of `Tⁿ` in the invariant
differential of the formal group law of `W` has degree `w n`. -/
theorem coeff_invariantDifferential_mem (n : ℕ) :
    PowerSeries.coeff n (formalGroup W).invariantDifferential ∈ 𝒜 (w * n) := by
  rw [← specialize_coeff_invariantDifferential]
  exact specialize_mem (Universal.isWeightedHomogeneous_coeff_invariantDifferential n)
    (specialize_X_mem h₁ h₂ h₃ h₄ h₆)

/-- If the coefficient `aᵢ` of `W` has degree `w i`, then the coefficient of `Tᵐ` in the
`k`-series of the formal group law of `W` has degree `w (m - 1)`. -/
theorem coeff_nsmulSeries_mem (k m : ℕ) :
    PowerSeries.coeff m ((formalGroup W).nsmulSeries k) ∈ 𝒜 (w * (m - 1)) := by
  rw [← specialize_coeff_nsmulSeries]
  exact specialize_mem (Universal.isWeightedHomogeneous_coeff_nsmulSeries k m)
    (specialize_X_mem h₁ h₂ h₃ h₄ h₆)

end Graded

/-- **The classifying homomorphism of a graded Weierstrass curve is graded.** If the coefficient
`aᵢ` of `W` has degree `2i`, then the homomorphism from the Lazard ring classifying the formal group
law of `W` maps the piece `Lₙ` of degree `n` into degree `n`. For the universal curve over
`ℤ[a₁, a₂, a₃, a₄, a₆]` with `aᵢ` in degree `2i`, this makes the Weierstrass coefficient ring a
graded algebra over the Lazard ring. -/
theorem lift_formalGroup_mem {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [SetLike.GradedMonoid 𝒜] {W : WeierstrassCurve A} (h₁ : W.a₁ ∈ 𝒜 2)
    (h₂ : W.a₂ ∈ 𝒜 4) (h₃ : W.a₃ ∈ 𝒜 6) (h₄ : W.a₄ ∈ 𝒜 8) (h₆ : W.a₆ ∈ 𝒜 12) {n : ℕ}
    {x : LazardRing} (hx : x ∈ LazardRing.grading n) :
    LazardRing.lift ⟨formalGroup W, inferInstance⟩ x ∈ 𝒜 n :=
  (LazardRing.lift_mem_iff (.id ℕ) ⟨formalGroup W, inferInstance⟩).2
    (coeff_formalGroup_mem (w := 2) h₁ h₂ h₃ h₄ h₆) hx

/-! ### The Hasse invariant modulo `p` -/

namespace VariableChange

variable {p : ℕ}

/-- **Landweber's `v₁` has weight `p - 1` modulo `p`.** For every change of variables
`C = (u, r, s, t)`, the coefficient of `Tᵖ` in the `p`-series of the formal group law of `C • W` is
`u^-(p - 1)` times that of `W`, modulo `p`. -/
theorem natCast_dvd_coeff_nsmulSeries_formalGroup_smul_sub (C : VariableChange R)
    (hp : p.Prime) :
    (p : R) ∣ PowerSeries.coeff p ((formalGroup (C • W)).nsmulSeries p) -
      ↑C.u⁻¹ ^ (p - 1) * PowerSeries.coeff p ((formalGroup W).nsmulSeries p) := by
  -- The transition `ψ` from `C • W` to `W` is an isomorphism of formal group laws with linear
  -- coefficient `u⁻¹`; compare the coefficients `v₁` of the two `p`-series modulo `I₁ = (p)`.
  have h := (FormalGroup.smulIso (C.formalCoordinate W) (formalGroup (C • W))).toHom
    |>.coeff_nsmulSeries_mul_coeff_one_pow_sub_mem_heightIdeal p 1
  rw [FormalGroup.smulIso_toHom_toPowerSeries, coeff_one_formalCoordinate,
    formalCoordinate_smul_formalGroup, pow_one, FormalGroup.heightIdeal_one _ hp,
    FormalGroup.heightIdeal_one _ hp, sup_idem, Ideal.mem_span_singleton] at h
  -- Multiply `v₁(W) u^-p - u⁻¹ v₁(C • W)` by `-u`.
  convert dvd_mul_of_dvd_left h (-(C.u : R)) using 1
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  rw [Nat.add_sub_cancel]
  linear_combination (PowerSeries.coeff (q + 1) ((formalGroup W).nsmulSeries (q + 1)) *
    ↑C.u⁻¹ ^ q - PowerSeries.coeff (q + 1) ((formalGroup (C • W)).nsmulSeries (q + 1))) *
    C.u.inv_mul

/-- **The Hasse invariant has weight `p - 1` modulo `p`.** For every change of variables
`C = (u, r, s, t)` over every commutative ring, the coefficient `A` of `Tᵖ⁻¹` in the invariant
differential, a lift of the Hasse invariant, satisfies `A(C • W) ≡ u^-(p - 1) A(W)` modulo `p`. -/
theorem natCast_dvd_coeff_invariantDifferential_formalGroup_smul_sub
    (C : VariableChange R) (hp : p.Prime) :
    (p : R) ∣ PowerSeries.coeff (p - 1) (formalGroup (C • W)).invariantDifferential -
      ↑C.u⁻¹ ^ (p - 1) * PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential := by
  have h₁ := (C • W).natCast_dvd_coeff_nsmulSeries_formalGroup_sub_coeff_invariantDifferential hp
  have h₂ := W.natCast_dvd_coeff_nsmulSeries_formalGroup_sub_coeff_invariantDifferential hp
  have h := natCast_dvd_coeff_nsmulSeries_formalGroup_smul_sub W C hp
  convert (h.sub h₁).add (dvd_mul_of_dvd_right h₂ (↑C.u⁻¹ ^ (p - 1))) using 1
  ring

/-- **The Hasse invariant transforms like a modular form of weight `p - 1`.** In characteristic
`p`, for every change of variables `C = (u, r, s, t)`, the coefficient of `Tᵖ⁻¹` in the invariant
differential of `C • W` is `u^-(p - 1)` times that of `W`. -/
theorem coeff_invariantDifferential_formalGroup_smul [CharP R p] (C : VariableChange R)
    (hp : p.Prime) :
    PowerSeries.coeff (p - 1) (formalGroup (C • W)).invariantDifferential =
      ↑C.u⁻¹ ^ (p - 1) * PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential := by
  have h := natCast_dvd_coeff_invariantDifferential_formalGroup_smul_sub W C hp
  rwa [CharP.cast_eq_zero R p, zero_dvd_iff, sub_eq_zero] at h

end VariableChange

end WeierstrassCurve
