/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Star

/-!
# The Temperley–Lieb comparison homomorphism into the cubic quantum torus

At loop parameter `δ = √3 = 2 cos (π / 6)` (Jones index `δ² = 3`), the site unitaries
`U_j = cubicSite N j = weyl N (ofAdd (Pi.single j 1))` of `CubicTorus N` satisfy `U_j ^ 3 = 1`,
`U_j * U_{j + 1} = ω • (U_{j + 1} * U_j)`, and commute at distance at least two. The self-adjoint
projections `p_j = cubicProjection N j = 3⁻¹ • (1 + U_j + U_j²)` lie in the inversion-fixed
subalgebra `cubicFixed N`, satisfy `p_j * p_k * p_j = 3⁻¹ • p_j` for `|j - k| = 1`, and commute
for `|j - k| ≥ 2`. Rescaling by `√3` therefore defines the `ℂ`-algebra homomorphism
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`, which intertwines the
Temperley–Lieb analytic adjoint with `cubicFixedAdjoint (m - 1)`.

To prove surjectivity of `cubicFixedHom m`, observe that `3 • p_j - 1 = W(e_j) + W(-e_j)` lies in
the image for every `j`. For `S(a) = W(a) + W(-a)`, the product law
`S(a) * S(b) = α(a, b) • S(a + b) + α(b, a) • S(a - b)` allows solving for `S(a + b)` and
`S(a - b)` whenever `chainForm (m - 1) a b ≠ 0` (since `α(a, b)² ≠ α(b, a)²`), and induction on
the support prefix shows that every `S(a)` — hence all of `cubicFixed (m - 1)` — lies in the image.

## Main definitions

* `TauCeti.TemperleyLieb.cubicSite`, `TauCeti.TemperleyLieb.cubicProjection`: the site unitaries
  `U_j` and self-adjoint projections `p_j = 3⁻¹ • (1 + U_j + U_j²)`.
* `TauCeti.TemperleyLieb.cubicFixedHom`: the comparison homomorphism
  `TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicProjection_mul_self`,
  `TauCeti.TemperleyLieb.cubicProjection_mul_cubicProjection_mul_cubicProjection`, and
  `TauCeti.TemperleyLieb.commute_cubicProjection`: Temperley–Lieb relations at `δ² = 3`.
* `TauCeti.TemperleyLieb.cubicFixedHom_star`: star compatibility of `cubicFixedHom`.
* `TauCeti.TemperleyLieb.cubicFixedHom_surjective`: surjectivity of `cubicFixedHom` for every `m`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topology
  8 (2017), 1–33.
-/

public section

open scoped ComplexConjugate

namespace TauCeti.TemperleyLieb

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact` so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint instances
`TemperleyLieb.instStarRing` and `TemperleyLieb.instStarModule`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

/-! ### Site unitaries, cubic projections, and the comparison homomorphism -/

/-- The `j`-th **site unitary** `U_j = W(e_j)` of `CubicTorus N`. -/
noncomputable def cubicSite (N : ℕ) (j : Fin N) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd (Pi.single j 1))

/-- Unfolding `cubicSite`. -/
theorem cubicSite_def (N : ℕ) (j : Fin N) :
    cubicSite N j = weyl N (Multiplicative.ofAdd (Pi.single j 1)) :=
  (rfl)

/-- Every site unitary satisfies `U_j ^ 3 = 1`. -/
@[simp]
theorem cubicSite_pow_three (N : ℕ) (j : Fin N) : cubicSite N j ^ 3 = 1 :=
  weyl_pow_three N _

/-- `U_j ^ 2 = W(-e_j)`. -/
theorem cubicSite_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 = weyl N (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod 3)))) := by
  rw [cubicSite_def, weyl_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  ext i
  simp only [toAdd_pow, toAdd_ofAdd, Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, Pi.neg_apply]
  by_cases hi : i = j
  · subst hi; simp only [Pi.single_eq_same]; decide
  · simp [hi]

/-- `cubicAdjoint` sends `U_j` to `U_j ^ 2`. -/
@[simp]
theorem cubicAdjoint_cubicSite (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_sq, cubicSite_def, cubicAdjoint_weyl]; rfl

/-- `cubicInversion` sends `U_j` to `U_j ^ 2`. -/
@[simp]
theorem cubicInversion_cubicSite (N : ℕ) (j : Fin N) :
    cubicInversion N (cubicSite N j) = cubicSite N j ^ 2 := by
  rw [cubicSite_sq, cubicSite_def, cubicInversion_weyl]; rfl

/-- Adjacent site unitaries satisfy the Weyl commutation relation
`U_i * U_j = ω • (U_j * U_i)` when `i + 1 = j`. -/
theorem cubicSite_mul_of_succ {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 1 = j) :
    cubicSite N i * cubicSite N j = (cubeRootOfUnity : ℂ) • (cubicSite N j * cubicSite N i) := by
  rw [cubicSite_def, cubicSite_def, weyl_mul, weyl_mul, smul_smul,
    mul_comm (Multiplicative.ofAdd (Pi.single j 1))]
  congr 1
  have hform := chainForm_single_single_of_succ h
  have hform' : chainForm N (Pi.single j 1) (Pi.single i 1) = 2 := by
    rw [chainForm_swap, hform]; decide
  rw [cubicFactor_def, cubicFactor_def, toAdd_ofAdd, toAdd_ofAdd, hform, hform']
  have hmul : cubeRootOfUnity * cubeRootPow (2 * 2) = cubeRootPow (2 * 1) := by
    rw [← cubeRootPow_one, ← cubeRootPow_add]; congr 1
  exact_mod_cast hmul.symm

/-- Distant site unitaries commute. -/
theorem commute_cubicSite {N : ℕ} {i j : Fin N} (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicSite N i) (cubicSite N j) := by
  rw [Commute, SemiconjBy, cubicSite_def, cubicSite_def, weyl_mul, weyl_mul,
    mul_comm (Multiplicative.ofAdd (Pi.single i 1))]
  have hform := chainForm_single_single_of_distant h
  have hform' : chainForm N (Pi.single j 1) (Pi.single i 1) = 0 := by
    rw [chainForm_swap, hform, neg_zero]
  simp [cubicFactor_def, hform, hform']

/-- The `j`-th **cubic projection** `p_j = 3⁻¹ • (1 + U_j + U_j²)` in `CubicTorus N`. -/
noncomputable def cubicProjection (N : ℕ) (j : Fin N) : CubicTorus N :=
  (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2)

/-- Unfolding `cubicProjection`. -/
theorem cubicProjection_def (N : ℕ) (j : Fin N) :
    cubicProjection N j = (3 : ℂ)⁻¹ • (1 + cubicSite N j + cubicSite N j ^ 2) :=
  (rfl)

private theorem cubicSite_sq_sq (N : ℕ) (j : Fin N) :
    cubicSite N j ^ 2 * cubicSite N j ^ 2 = cubicSite N j := by
  have h4 : (2 : ℕ) + 2 = 3 + 1 := rfl
  rw [← pow_add, h4, pow_succ, cubicSite_pow_three, one_mul]

/-- Every cubic projection lies in `cubicFixed N`. -/
theorem cubicProjection_mem_cubicFixed (N : ℕ) (j : Fin N) :
    cubicProjection N j ∈ cubicFixed N := by
  have hsq : (cubicSite N j ^ 2) ^ 2 = cubicSite N j := by rw [sq, cubicSite_sq_sq]
  rw [mem_cubicFixed_iff, cubicProjection_def, map_smul, map_add, map_add, map_one, map_pow,
    cubicInversion_cubicSite, hsq]
  congr 1; abel

/-- Every cubic projection has scalar part `3⁻¹`. -/
@[simp]
theorem cubicScalarCoefficient_cubicProjection (N : ℕ) (j : Fin N) :
    cubicScalarCoefficient N (cubicProjection N j) = (3 : ℂ)⁻¹ := by
  have hne1 : Multiplicative.ofAdd (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) ≠ 1 := by
    intro h; have := congrFun (congrArg Multiplicative.toAdd h) j; simp at this
  rw [cubicProjection_def, map_smul, map_add, map_add, cubicScalarCoefficient_one,
    cubicSite_def, cubicScalarCoefficient_weyl, ← cubicSite_def, cubicSite_sq,
    cubicScalarCoefficient_weyl]
  simp [hne1]

/-- Every cubic projection is self-adjoint for `cubicAdjoint N`. -/
@[simp]
theorem cubicAdjoint_cubicProjection (N : ℕ) (j : Fin N) :
    cubicAdjoint N (cubicProjection N j) = cubicProjection N j := by
  rw [cubicProjection_def, map_smulₛₗ, map_add, map_add, cubicAdjoint_one, cubicAdjoint_cubicSite,
    sq, cubicAdjoint_mul, cubicAdjoint_cubicSite, cubicSite_sq_sq, starRingEnd_apply]
  have h3 : star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by simp
  rw [h3]; congr 1; abel

private theorem cubicSite_mul_sum_eq (N : ℕ) (j : Fin N) :
    cubicSite N j * (1 + cubicSite N j + cubicSite N j ^ 2) =
      1 + cubicSite N j + cubicSite N j ^ 2 := by
  rw [mul_add, mul_add, mul_one, ← sq, ← pow_succ', cubicSite_pow_three]; abel

private theorem cubicSite_sum_mul_self (N : ℕ) (j : Fin N) :
    (1 + cubicSite N j + cubicSite N j ^ 2) * (1 + cubicSite N j + cubicSite N j ^ 2) =
      (3 : ℂ) • (1 + cubicSite N j + cubicSite N j ^ 2) := by
  have h1 := cubicSite_mul_sum_eq N j
  have h2 : cubicSite N j ^ 2 * (1 + cubicSite N j + cubicSite N j ^ 2) =
      1 + cubicSite N j + cubicSite N j ^ 2 := by
    conv_lhs => arg 1; rw [sq]
    rw [mul_assoc, h1, h1]
  have h3 : (3 : ℂ) = 1 + 1 + 1 := by norm_num
  rw [add_mul, add_mul, one_mul, h1, h2, h3, add_smul, add_smul, one_smul]

/-- Every cubic projection is idempotent. -/
@[simp]
theorem cubicProjection_mul_self (N : ℕ) (j : Fin N) :
    cubicProjection N j * cubicProjection N j = cubicProjection N j := by
  rw [cubicProjection_def, smul_mul_smul_comm, cubicSite_sum_mul_self, smul_smul]; norm_num

/-- Helper: if `u * v = ζ • (v * u)` in `CubicTorus N` with `u = cubicSite N i` and
`1 + ζ + ζ² = 0`, then `(1 + u + u²) * v * (1 + u + u²) = 0`. -/
private theorem cubicSite_sum_mul_mul_sum_eq_zero {N : ℕ} {i : Fin N} {v : CubicTorus N} {ζ : ℂ}
    (hζ : 1 + ζ + ζ ^ 2 = 0) (hcomm : cubicSite N i * v = ζ • (v * cubicSite N i)) :
    (1 + cubicSite N i + cubicSite N i ^ 2) * v * (1 + cubicSite N i + cubicSite N i ^ 2) = 0 := by
  set u := cubicSite N i
  have hcomm2 : u ^ 2 * v = (ζ ^ 2) • (v * u ^ 2) := by
    calc u ^ 2 * v = u * (u * v) := by rw [sq, mul_assoc]
      _ = u * (ζ • (v * u)) := by rw [hcomm]
      _ = ζ • ((u * v) * u) := by rw [mul_smul_comm, mul_assoc]
      _ = ζ • ((ζ • (v * u)) * u) := by rw [hcomm]
      _ = (ζ ^ 2) • (v * u ^ 2) := by rw [smul_mul_assoc, smul_smul, ← sq, mul_assoc, ← sq]
  have hleft : (1 + u + u ^ 2) * v = v * (1 + ζ • u + (ζ ^ 2) • u ^ 2) := by
    simp only [add_mul, one_mul, mul_add, mul_one, hcomm, hcomm2, mul_smul_comm]
  have hu_abs : u * (1 + u + u ^ 2) = 1 + u + u ^ 2 := cubicSite_mul_sum_eq N i
  have hu2_abs : u ^ 2 * (1 + u + u ^ 2) = 1 + u + u ^ 2 := by
    conv_lhs => arg 1; rw [sq]
    rw [mul_assoc, hu_abs, hu_abs]
  rw [hleft, mul_assoc]
  have hzero : (1 + ζ • u + (ζ ^ 2) • u ^ 2) * (1 + u + u ^ 2) = 0 := by
    simp only [add_mul, one_mul, smul_mul_assoc, hu_abs, hu2_abs]
    have hcomb : (1 + u + u ^ 2) + ζ • (1 + u + u ^ 2) + (ζ ^ 2) • (1 + u + u ^ 2) =
        (1 + ζ + ζ ^ 2) • (1 + u + u ^ 2) := by module
    rw [hcomb, hζ, zero_smul]
  rw [hzero, mul_zero]

private theorem exists_primitive_comm_of_adj {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    ∃ ζ : ℂ, 1 + ζ + ζ ^ 2 = 0 ∧
      cubicSite N i * cubicSite N j = ζ • (cubicSite N j * cubicSite N i) := by
  rcases h with hij | hji
  · exact ⟨cubeRootOfUnity, one_add_cubeRootOfUnity_add_sq, cubicSite_mul_of_succ hij⟩
  · refine ⟨(cubeRootOfUnity : ℂ) ^ 2, ?_, ?_⟩
    · linear_combination (1 - (cubeRootOfUnity : ℂ) + (cubeRootOfUnity : ℂ) ^ 2) *
        one_add_cubeRootOfUnity_add_sq
    · have hmul := congrArg (fun x ↦ ((cubeRootOfUnity : ℂ) ^ 2) • x) (cubicSite_mul_of_succ hji)
      have h3 : (2 : ℕ) + 1 = 3 := rfl
      rw [smul_smul, ← pow_succ, h3, coe_cubeRootOfUnity_pow_three, one_smul] at hmul
      exact hmul.symm

/-- Adjacent cubic projections satisfy `p_i * p_j * p_i = 3⁻¹ • p_i`. -/
theorem cubicProjection_mul_cubicProjection_mul_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) :
    cubicProjection N i * cubicProjection N j * cubicProjection N i =
      (3 : ℂ)⁻¹ • cubicProjection N i := by
  obtain ⟨ζ, hζ, hcomm⟩ := exists_primitive_comm_of_adj h
  have hζ2 : 1 + ζ ^ 2 + (ζ ^ 2) ^ 2 = 0 := by linear_combination (1 - ζ + ζ ^ 2) * hζ
  have hcomm2 : cubicSite N i * cubicSite N j ^ 2 =
      (ζ ^ 2) • (cubicSite N j ^ 2 * cubicSite N i) := by
    calc cubicSite N i * cubicSite N j ^ 2
          = (cubicSite N i * cubicSite N j) * cubicSite N j := by rw [sq, mul_assoc]
      _ = (ζ • (cubicSite N j * cubicSite N i)) * cubicSite N j := by rw [hcomm]
      _ = ζ • (cubicSite N j * (cubicSite N i * cubicSite N j)) := by
            rw [smul_mul_assoc, mul_assoc]
      _ = ζ • (cubicSite N j * (ζ • (cubicSite N j * cubicSite N i))) := by rw [hcomm]
      _ = (ζ ^ 2) • (cubicSite N j ^ 2 * cubicSite N i) := by
            rw [mul_smul_comm, smul_smul, ← sq, ← mul_assoc, ← sq]
  have hv1 := cubicSite_sum_mul_mul_sum_eq_zero hζ hcomm
  have hv2 := cubicSite_sum_mul_mul_sum_eq_zero hζ2 hcomm2
  have h1 : (1 + cubicSite N i + cubicSite N i ^ 2) * 1 * (1 + cubicSite N i + cubicSite N i ^ 2) =
      (3 : ℂ) • (1 + cubicSite N i + cubicSite N i ^ 2) := by
    rw [mul_one]; exact cubicSite_sum_mul_self N i
  have hprod : (1 + cubicSite N i + cubicSite N i ^ 2) * (1 + cubicSite N j + cubicSite N j ^ 2) *
      (1 + cubicSite N i + cubicSite N i ^ 2) =
      (3 : ℂ) • (1 + cubicSite N i + cubicSite N i ^ 2) := by
    rw [mul_add (1 + cubicSite N i + cubicSite N i ^ 2),
      mul_add (1 + cubicSite N i + cubicSite N i ^ 2), add_mul, add_mul, hv1, hv2, h1,
      add_zero, add_zero]
  rw [cubicProjection_def N i, cubicProjection_def N j]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [hprod, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1; norm_num

/-- Distant cubic projections commute. -/
theorem commute_cubicProjection {N : ℕ} {i j : Fin N}
    (h : (i : ℕ) + 2 ≤ j ∨ (j : ℕ) + 2 ≤ i) :
    Commute (cubicProjection N i) (cubicProjection N j) := by
  have hc := commute_cubicSite h
  have h1 := ((Commute.one_left _).add_left hc).add_left (hc.pow_left 2)
  rw [cubicProjection_def, cubicProjection_def]
  exact (((Commute.one_right _).add_right h1).add_right (h1.pow_right 2)).smul_left _
    |>.smul_right _

private noncomputable def cubicFixedGenerator (m : ℕ) (j : Fin (m - 1)) : cubicFixed (m - 1) :=
  ⟨(Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j,
    Subalgebra.smul_mem _ (cubicProjection_mem_cubicFixed (m - 1) j) _⟩

/-- The **cubic quantum torus comparison homomorphism**
`TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)`, sending `e (√3 : ℂ) j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`. -/
noncomputable def cubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1) :=
  lift (cubicFixedGenerator m)
    (fun i ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, SetLike.val_smul, cubicFixedGenerator, smul_mul_smul_comm,
        cubicProjection_mul_self, smul_smul])
    (fun {i j} h ↦ Subtype.ext <| by
      have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
        exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      simp only [Subalgebra.coe_mul, cubicFixedGenerator, smul_mul_assoc, mul_smul_comm,
        cubicProjection_mul_cubicProjection_mul_cubicProjection h, smul_smul]
      congr 1; rw [hsqrt]; norm_num)
    (fun {i j} h ↦ Subtype.ext <| by
      simp only [Subalgebra.coe_mul, cubicFixedGenerator]
      exact ((commute_cubicProjection h).smul_left _ |>.smul_right _).eq)

/-- Action of `cubicFixedHom` on the `j`-th Temperley–Lieb generator, coerced to
`CubicTorus (m - 1)`. -/
@[simp]
theorem coe_cubicFixedHom_e (m : ℕ) (j : Fin (m - 1)) :
    (cubicFixedHom m (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := by
  simp [cubicFixedHom, cubicFixedGenerator]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with `cubicAdjoint`. -/
theorem coe_cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicFixedHom m (star x) : CubicTorus (m - 1)) =
      cubicAdjoint (m - 1) (cubicFixedHom m x) := by
  induction x using TemperleyLieb.induction with
  | e j =>
    rw [star_e, coe_cubicFixedHom_e, map_smulₛₗ, cubicAdjoint_cubicProjection]
    simp [Complex.conj_ofReal]
  | algebraMap z =>
    have hstar : star (algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) z) =
        algebraMap ℂ (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) (conj z) := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, ← Algebra.algebraMap_eq_smul_one]
      rfl
    rw [hstar, (cubicFixedHom m).commutes, (cubicFixedHom m).commutes, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, cubicAdjoint_algebraMap]
  | add x y hx hy =>
    have hadd : ∀ a b, cubicFixedHom m (a + b) = cubicFixedHom m a + cubicFixedHom m b :=
      (cubicFixedHom m).map_add'
    rw [star_add, hadd, hadd, Subalgebra.coe_add, Subalgebra.coe_add, map_add, hx, hy]
  | mul x y hx hy =>
    have hmul : ∀ a b, cubicFixedHom m (a * b) = cubicFixedHom m a * cubicFixedHom m b :=
      (cubicFixedHom m).map_mul'
    rw [star_mul, hmul, hmul, Subalgebra.coe_mul, Subalgebra.coe_mul, cubicAdjoint_mul, hx, hy]

/-- `cubicFixedHom` intertwines the Temperley–Lieb analytic adjoint with `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedHom m (star x) = cubicFixedAdjoint (m - 1) (cubicFixedHom m x) :=
  Subtype.ext (by rw [coe_cubicFixedHom_star, coe_cubicFixedAdjoint])

/-! ### Surjectivity of `cubicFixedHom` -/

private noncomputable def ambientCubicFixedHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] CubicTorus (m - 1) :=
  (cubicFixed (m - 1)).val.comp (cubicFixedHom m)

/-- The symmetrized Weyl element `S(a) = W(a) + W(-a)` in `CubicTorus N`. -/
private noncomputable def symWeyl (N : ℕ) (a : Fin N → ZMod 3) : CubicTorus N :=
  weyl N (Multiplicative.ofAdd a) + weyl N (Multiplicative.ofAdd (-a))

private theorem symWeyl_neg (N : ℕ) (a : Fin N → ZMod 3) : symWeyl N (-a) = symWeyl N a := by
  simp [symWeyl, add_comm]

private theorem symWeyl_zero (N : ℕ) : symWeyl N 0 = (2 : ℂ) • (1 : CubicTorus N) := by
  simp [symWeyl, two_smul]

private theorem symWeyl_mul_symWeyl (N : ℕ) (a b : Fin N → ZMod 3) :
    symWeyl N a * symWeyl N b =
      (cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) : ℂ) • symWeyl N (a + b) +
      (cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a) : ℂ) •
        symWeyl N (a - b) := by
  have h1 : cubicFactor N (Multiplicative.ofAdd (-a)) (Multiplicative.ofAdd (-b)) =
      cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) := by
    simp [cubicFactor_def]
  have h2 : cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd (-b)) =
      cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a) := by
    simp only [cubicFactor_def, toAdd_ofAdd]; rw [chainForm_neg_right, chainForm_swap, neg_neg]
  have h3 : cubicFactor N (Multiplicative.ofAdd (-a)) (Multiplicative.ofAdd b) =
      cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a) := by
    simp only [cubicFactor_def, toAdd_ofAdd]; rw [chainForm_neg_left, chainForm_swap, neg_neg]
  simp only [symWeyl, add_mul, mul_add, weyl_mul, smul_add, h1, h2, h3, ← ofAdd_add]
  have hneg1 : -a + -b = -(a + b) := by abel
  have hneg2 : a + -b = a - b := by abel
  have hneg3 : -a + b = -(a - b) := by abel
  rw [hneg1, hneg2, hneg3]; abel

private theorem cubicFactor_sq_sub_swap_sq_ne_zero {N : ℕ} {a b : Fin N → ZMod 3}
    (hB : chainForm N a b ≠ 0) :
    (cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) : ℂ) ^ 2 -
      (cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a) : ℂ) ^ 2 ≠ 0 := by
  set u := cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
  set v := cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)
  have hvu : v = u⁻¹ := cubicFactor_swap N _ _
  have huv_u : u * v = 1 := by rw [hvu, mul_inv_cancel]
  have huv : (u : ℂ) * (v : ℂ) = 1 := by simpa using congrArg Units.val huv_u
  have hu3_u : u ^ 3 = 1 := by
    dsimp only [u]
    rw [cubicFactor_def, cubeRootPow_def, pow_right_comm, cubeRootOfUnity_pow_three, one_pow]
  have hu3 : (u : ℂ) ^ 3 = 1 := by simpa using congrArg Units.val hu3_u
  intro h0
  have hsq : (u : ℂ) ^ 2 = (v : ℂ) ^ 2 := sub_eq_zero.mp h0
  have h4 : (u : ℂ) ^ 4 = 1 := by
    calc (u : ℂ) ^ 4 = (u : ℂ) ^ 2 * (v : ℂ) ^ 2 := by rw [← hsq]; ring
      _ = ((u : ℂ) * (v : ℂ)) ^ 2 := by ring
      _ = 1 := by rw [huv, one_pow]
  have hu1 : u = 1 := Units.ext <| by
    calc (u : ℂ) = (u : ℂ) ^ 3 * (u : ℂ) := by rw [hu3, one_mul]
      _ = (u : ℂ) ^ 4 := by ring
      _ = 1 := h4
  have h2B : (2 : ZMod 3) * chainForm N a b = 0 := by simpa [u, cubicFactor_def] using hu1
  have h4B := congrArg (2 * ·) h2B
  have h22 : (2 * 2 : ZMod 3) = 1 := rfl
  rw [← mul_assoc, h22, one_mul, mul_zero] at h4B
  exact hB h4B

private theorem symWeyl_add_and_sub_mem_of_chainForm_ne_zero {N : ℕ}
    {A : Subalgebra ℂ (CubicTorus N)} {a b : Fin N → ZMod 3}
    (ha : symWeyl N a ∈ A) (hb : symWeyl N b ∈ A) (hB : chainForm N a b ≠ 0) :
    symWeyl N (a + b) ∈ A ∧ symWeyl N (a - b) ∈ A := by
  set c : ℂ := (cubicFactor N (Multiplicative.ofAdd a) (Multiplicative.ofAdd b) : ℂ)
  set d : ℂ := (cubicFactor N (Multiplicative.ofAdd b) (Multiplicative.ofAdd a) : ℂ)
  have hneq := cubicFactor_sq_sub_swap_sq_ne_zero hB
  have hab := symWeyl_mul_symWeyl N a b
  have hba : symWeyl N b * symWeyl N a = d • symWeyl N (a + b) + c • symWeyl N (a - b) := by
    have h := symWeyl_mul_symWeyl N b a
    rwa [add_comm b a, ← neg_sub a b, symWeyl_neg] at h
  have hcomb1 : c • (symWeyl N a * symWeyl N b) + (-d) • (symWeyl N b * symWeyl N a) =
      (c ^ 2 - d ^ 2) • symWeyl N (a + b) := by rw [hab, hba]; module
  have hcomb2 : c • (symWeyl N b * symWeyl N a) + (-d) • (symWeyl N a * symWeyl N b) =
      (c ^ 2 - d ^ 2) • symWeyl N (a - b) := by rw [hab, hba]; module
  have hmem1 : (c ^ 2 - d ^ 2) • symWeyl N (a + b) ∈ A := by
    rw [← hcomb1]
    exact A.add_mem (A.smul_mem (mul_mem ha hb) c) (A.smul_mem (mul_mem hb ha) (-d))
  have hmem2 : (c ^ 2 - d ^ 2) • symWeyl N (a - b) ∈ A := by
    rw [← hcomb2]
    exact A.add_mem (A.smul_mem (mul_mem hb ha) c) (A.smul_mem (mul_mem ha hb) (-d))
  refine ⟨?_, ?_⟩
  · have h := A.smul_mem hmem1 (c ^ 2 - d ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hneq, one_smul] at h
  · have h := A.smul_mem hmem2 (c ^ 2 - d ^ 2)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hneq, one_smul] at h

private theorem symWeyl_mul_symWeyl_of_chainForm_eq_zero {N : ℕ} {a b : Fin N → ZMod 3}
    (hB : chainForm N a b = 0) :
    symWeyl N a * symWeyl N b = symWeyl N (a + b) + symWeyl N (a - b) := by
  have hB' : chainForm N b a = 0 := by rw [chainForm_swap, hB, neg_zero]
  simp [symWeyl_mul_symWeyl, cubicFactor_def, hB, hB']

private theorem symWeyl_single_mem_range_ambient (m : ℕ) (j : Fin (m - 1)) :
    symWeyl (m - 1) (Pi.single j 1) ∈ (ambientCubicFixedHom m).range := by
  rw [AlgHom.mem_range]
  refine ⟨(Real.sqrt 3 : ℂ) • e (Real.sqrt 3 : ℂ) j - 1, ?_⟩
  have he : ambientCubicFixedHom m (e (Real.sqrt 3 : ℂ) j) =
      (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j := coe_cubicFixedHom_e m j
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hscale : ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹ = 1 := by
    rw [hsqrt]; norm_num
  rw [map_sub, map_smul, map_one, he, cubicProjection_def, smul_smul, smul_smul, hscale, one_smul,
    cubicSite_sq, cubicSite_def, symWeyl]
  abel

private theorem symWeyl_add_single_mem_range_ambient {m k : ℕ} (hk : k + 1 ≤ m - 1)
    (ih : ∀ c : Fin (m - 1) → ZMod 3, (∀ i : Fin (m - 1), k ≤ (i : ℕ) → c i = 0) →
      symWeyl (m - 1) c ∈ (ambientCubicFixedHom m).range)
    {c : Fin (m - 1) → ZMod 3} (hc_supp : ∀ i : Fin (m - 1), k ≤ (i : ℕ) → c i = 0) :
    symWeyl (m - 1) (c + Pi.single ⟨k, by omega⟩ 1) ∈ (ambientCubicFixedHom m).range := by
  set j : Fin (m - 1) := ⟨k, by omega⟩
  have hc_mem := ih c hc_supp
  have hej_mem := symWeyl_single_mem_range_ambient m j
  by_cases hk0 : k = 0
  · have hc0 : c = 0 := funext fun i ↦ hc_supp i (by omega)
    simpa [hc0] using hej_mem
  · by_cases hB : chainForm (m - 1) c (Pi.single j 1) ≠ 0
    · exact (symWeyl_add_and_sub_mem_of_chainForm_ne_zero hc_mem hej_mem hB).1
    · push Not at hB
      set j' : Fin (m - 1) := ⟨k - 1, by omega⟩
      set v : Fin (m - 1) → ZMod 3 := Pi.single j' 1
      have hv_supp : ∀ i : Fin (m - 1), k ≤ (i : ℕ) → v i = 0 := fun i hi ↦
        Pi.single_eq_of_ne (fun h ↦ by subst h; dsimp [j'] at hi; omega) 1
      have hBv : chainForm (m - 1) v (Pi.single j 1) = 1 :=
        chainForm_single_single_of_succ (by dsimp [j', j]; omega)
      have hvej_mem : symWeyl (m - 1) (v + Pi.single j 1) ∈ (ambientCubicFixedHom m).range :=
        (symWeyl_add_and_sub_mem_of_chainForm_ne_zero (ih v hv_supp) hej_mem
          (by rw [hBv]; decide)).1
      have hBsub : chainForm (m - 1) (c - v) (v + Pi.single j 1) = chainForm (m - 1) c v - 1 := by
        rw [chainForm_sub_left, chainForm_add_right, chainForm_add_right, hB, chainForm_self, hBv]
        ring
      have hBadd : chainForm (m - 1) (c + v) (v + Pi.single j 1) = chainForm (m - 1) c v + 1 := by
        rw [chainForm_add_left, chainForm_add_right, chainForm_add_right, hB, chainForm_self, hBv]
        ring
      by_cases h1 : chainForm (m - 1) (c - v) (v + Pi.single j 1) ≠ 0
      · have hcv_mem := ih (c - v) (fun i hi ↦ by simp [hc_supp i hi, hv_supp i hi])
        have hres := (symWeyl_add_and_sub_mem_of_chainForm_ne_zero hcv_mem hvej_mem h1).1
        have heq : c - v + (v + Pi.single j 1) = c + Pi.single j 1 := by abel
        rwa [heq] at hres
      · push Not at h1
        have h2 : chainForm (m - 1) (c + v) (v + Pi.single j 1) ≠ 0 := by
          rw [hBsub] at h1; rw [hBadd]
          intro h2
          have : (2 : ZMod 3) = 0 := by
            calc (2 : ZMod 3) = (chainForm (m - 1) c v + 1) - (chainForm (m - 1) c v - 1) := by ring
              _ = 0 := by rw [h2, h1, sub_self]
          exact absurd this (by decide)
        have hcv_mem := ih (c + v) (fun i hi ↦ by simp [hc_supp i hi, hv_supp i hi])
        have hsub_mem : symWeyl (m - 1) (c - Pi.single j 1) ∈ (ambientCubicFixedHom m).range := by
          have hres := (symWeyl_add_and_sub_mem_of_chainForm_ne_zero hcv_mem hvej_mem h2).2
          have heq : c + v - (v + Pi.single j 1) = c - Pi.single j 1 := by abel
          rwa [heq] at hres
        have hmul_eq : symWeyl (m - 1) (c + Pi.single j 1) =
            symWeyl (m - 1) c * symWeyl (m - 1) (Pi.single j 1) +
              (-1 : ℂ) • symWeyl (m - 1) (c - Pi.single j 1) := by
          rw [symWeyl_mul_symWeyl_of_chainForm_eq_zero hB]; module
        rw [hmul_eq]
        exact add_mem (mul_mem hc_mem hej_mem)
          ((ambientCubicFixedHom m).range.smul_mem hsub_mem (-1))

private theorem symWeyl_mem_range_ambient_of_support_lt {m : ℕ} :
    ∀ (k : ℕ) (_hk : k ≤ m - 1) (a : Fin (m - 1) → ZMod 3),
      (∀ i : Fin (m - 1), k ≤ (i : ℕ) → a i = 0) →
        symWeyl (m - 1) a ∈ (ambientCubicFixedHom m).range
  | 0, _, a, ha => by
    have ha0 : a = 0 := funext fun i ↦ ha i (Nat.zero_le _)
    rw [ha0, symWeyl_zero]
    exact Subalgebra.smul_mem _ (one_mem _) _
  | k + 1, hk, a, ha => by
    set j : Fin (m - 1) := ⟨k, by omega⟩
    let a' : Fin (m - 1) → ZMod 3 := Function.update a j 0
    have ha'_supp : ∀ i : Fin (m - 1), k ≤ (i : ℕ) → a' i = 0 := fun i hi ↦ by
      by_cases hij : i = j
      · subst hij; simp [a']
      · have hik : k + 1 ≤ (i : ℕ) := by have : (i : ℕ) ≠ k := fun h ↦ hij (Fin.ext h); omega
        simp [a', hij, ha i hik]
    have ih := symWeyl_mem_range_ambient_of_support_lt (m := m) k (by omega)
    generalize haj : a j = v
    fin_cases v
    · have ha_eq : a = a' := funext fun i ↦ by
        by_cases hij : i = j
        · subst hij; simp [a', haj]; rfl
        · simp [a', hij]
      rw [ha_eq]; exact ih a' ha'_supp
    · have ha_eq : a = a' + Pi.single j 1 := funext fun i ↦ by
        by_cases hij : i = j
        · subst hij; simp [a', haj]; rfl
        · simp [a', hij]
      rw [ha_eq]; exact symWeyl_add_single_mem_range_ambient hk ih ha'_supp
    · have ha_eq : -a = (-a') + Pi.single j 1 := funext fun i ↦ by
        by_cases hij : i = j
        · subst hij
          simp only [Pi.neg_apply, Pi.add_apply, Pi.single_eq_same, a', Function.update_self,
            neg_zero, zero_add, haj]
          decide
        · simp [a', hij]
      rw [← symWeyl_neg, ha_eq]
      exact symWeyl_add_single_mem_range_ambient hk ih (fun i hi ↦ by simp [ha'_supp i hi])

/-- **Surjectivity of the cubic quantum torus comparison homomorphism**: for every `m : ℕ`,
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` is surjective. -/
theorem cubicFixedHom_surjective (m : ℕ) : Function.Surjective (cubicFixedHom m) := by
  rintro ⟨x, hx⟩
  have hmem : x ∈ (ambientCubicFixedHom m).range := by
    let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin (m - 1) → ZMod 3))
      (cubicFactor (m - 1))
    have hdecomp : x = (2 : ℂ)⁻¹ •
        ∑ g : Multiplicative (Fin (m - 1) → ZMod 3), b.repr x g • symWeyl (m - 1) g.toAdd := by
      have havg : x = (2 : ℂ)⁻¹ • (x + cubicInversion (m - 1) x) := by
        rw [mem_cubicFixed_iff.mp hx, ← two_smul ℂ, smul_smul]; norm_num
      conv_lhs => rw [havg]
      congr 1
      conv_lhs => rw [(b.sum_repr x).symm, map_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ ↦ by simp [b, ← weyl_def, symWeyl, smul_add]
    rw [hdecomp]
    refine Subalgebra.smul_mem _ (sum_mem fun g _ ↦ Subalgebra.smul_mem _ ?_ _) _
    exact symWeyl_mem_range_ambient_of_support_lt (m - 1) le_rfl g.toAdd
      (fun i hi ↦ absurd i.isLt (not_lt.mpr hi))
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, Subtype.ext ht⟩

end TauCeti.TemperleyLieb
