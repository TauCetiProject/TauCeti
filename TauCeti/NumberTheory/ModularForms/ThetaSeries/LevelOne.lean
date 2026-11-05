/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import TauCeti.Algebra.Module.ZLattice.OrthSum
public import TauCeti.NumberTheory.ModularForms.LevelOne.E4Discriminant
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Cusp
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Inversion
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion

/-!
# Theta series of even unimodular lattices

Let `L` be an even unimodular lattice in a real inner product space `E` of dimension `n`. This
file proves that `n` is divisible by `8` and that, writing `n = 2k`, the theta series `Θ_L` is a
modular form of weight `k` for `SL(2, ℤ)`.

For a unimodular lattice `L^∨ = L` and `covol L = 1`, so the inversion law reads
`Θ_L ∣[k] S = (-i)^k Θ_L` (`ZLattice.IsUnimodular.thetaSeries_slash_S`). The rank argument is
the elementary one. If `n ≡ 4 (mod 8)`, then `k ≡ 2 (mod 4)` and `Θ_L ∣[k] S = -Θ_L`, while
`Θ_L ∣[k] T = Θ_L` because `L` is even. The relation `S³ T S T S = T⁻¹` in `SL(2, ℤ)` then
gives `-Θ_L = Θ_L`, which is impossible since `Θ_L(i) ≠ 0`. A general rank `n` reduces to this
case: the orthogonal direct sums `L ⊕ L` and `(L ⊕ L) ⊕ (L ⊕ L)` are again even unimodular, of
ranks `2n` and `4n`, and none of `n`, `2n`, `4n` being `4` modulo `8` forces `8 ∣ n`.

Once `8 ∣ n`, the factor `(-i)^k` is `1`, so `Θ_L` is invariant under both generators `S` and
`T` of `SL(2, ℤ)`; with holomorphy and boundedness at `i∞` this makes `Θ_L` a level-one modular
form, `ZLattice.thetaForm`, built as Mathlib builds `CuspForm.discriminant`. Its `q`-expansion
coefficients are the representation numbers `r_L(2m)` (`ZLattice.coe_thetaForm` and
`ZLattice.IsEven.qExpansion_thetaSeries_coeff`), it is nonzero since `Θ_L(i) ≠ 0`, it is
invariant under linear isometries, and the theta form of an orthogonal direct sum `L ⊕ M` is the
product of the theta forms of `L` and `M`, in weight `k + k'`.

Since `4 ∣ k`, the theta series is then a unique combination of the products `E₄ ^ a * Δ ^ b`
with `4 a + 12 b = k`. Its `q`-expansion coefficients are the representation numbers `r_L(2m)`,
and those of `E₄` and `Δ` are rational, so the coefficients of this combination are rational.
This is the shape in which the theta series of a particular even unimodular lattice is identified
inside the ring of level-one modular forms.

## Main definitions

* `ZLattice.thetaForm`: the theta series of an even unimodular lattice of rank `2k`, as a modular
  form of weight `k` for `SL(2, ℤ)`.

## Main statements

* `ZLattice.IsEven.eight_dvd_finrank`: the rank of an even unimodular lattice is divisible by `8`.
* `ZLattice.IsEven.thetaSeries_slash_S`: `Θ_L ∣[k] S = Θ_L` for even unimodular `L`.
* `ZLattice.thetaForm_ne_zero`: `Θ_L` is a nonzero modular form.
* `ZLattice.thetaForm_comap`: `Θ_L` is invariant under linear isometries.
* `ZLattice.thetaForm_orthSum`: `Θ_{L ⊕ M} = Θ_L Θ_M` as modular forms of weight `k + k'`.
* `ZLattice.IsEven.existsUnique_finsupp_thetaSeries_eq_E₄_discriminant`: for even unimodular `L`
  of rank `2k`, `Θ_L = ∑_{4 a + 12 b = k} c (a, b) • E₄ ^ a * Δ ^ b` for a unique family of
  rational coefficients `c (a, b)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, §3.2.
-/

public section

open Complex Module ModularGroup SlashInvariantForm ModularForm
open UpperHalfPlane (qExpansion)
open scoped ModularForm MatrixGroups

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {k : ℕ}

namespace IsEven

/-- The rank of an even unimodular lattice is not `4` modulo `8`. -/
private theorem finrank_mod_eight_ne_four (hL : IsEven L) (hU : IsUnimodular L) :
    finrank ℝ E % 8 ≠ 4 := by
  intro h8
  obtain ⟨k, hk, hk4⟩ : ∃ k, finrank ℝ E = 2 * k ∧ k % 4 = 2 :=
    ⟨finrank ℝ E / 2, by omega, by omega⟩
  -- Since `k ≡ 2 (mod 4)`, the factor `(-i)^k` of the inversion law is `-1`.
  have hI : (-I) ^ k = -1 := by
    rw [← Nat.div_add_mod k 4, hk4, pow_add, pow_mul, (by decide : Even 4).neg_pow, I_pow_four]
    simp
  have hS : thetaSeries L ∣[(k : ℤ)] S = -thetaSeries L := by
    rw [hU.thetaSeries_slash_S hk, hI, neg_one_smul]
  have hT := hL.thetaSeries_slash_T (k : ℤ)
  -- `T⁻¹ = S³ T S T S` acts on `Θ_L` by `(-1)^5 = -1`, and also trivially.
  have h : -thetaSeries L = thetaSeries L := by
    calc -thetaSeries L = thetaSeries L ∣[(k : ℤ)] (S • S • S • T • S • T • S) := by
          simp [smul_eq_mul, SlashAction.slash_mul, hS, hT, SlashAction.neg_slash]
      _ = thetaSeries L := by
          rw [T_S_rel]
          conv_lhs => rw [← hT, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  have hi := congrFun h UpperHalfPlane.I
  rw [Pi.neg_apply] at hi
  exact thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re
    (by linear_combination (-1 / 2 : ℂ) * hi)

/-- **The rank of an even unimodular lattice is divisible by `8`.** -/
theorem eight_dvd_finrank (hL : IsEven L) (hU : IsUnimodular L) : 8 ∣ finrank ℝ E := by
  have hL₂ : IsEven (orthSum L L) := isEven_orthSum_iff.2 ⟨hL, hL⟩
  have hU₂ : IsUnimodular (orthSum L L) := isUnimodular_orthSum_iff.2 ⟨hU, hU⟩
  have h₁ := hL.finrank_mod_eight_ne_four hU
  have h₂ := hL₂.finrank_mod_eight_ne_four hU₂
  have h₄ := (isEven_orthSum_iff.2 ⟨hL₂, hL₂⟩).finrank_mod_eight_ne_four
    (isUnimodular_orthSum_iff.2 ⟨hU₂, hU₂⟩)
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, finrank_prod] at h₂ h₄
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, finrank_prod] at h₄
  omega

/-- **The inversion law of an even unimodular lattice**: if `L` is even unimodular and
`dim E = 2k`, then `Θ_L ∣[k] S = Θ_L`. -/
theorem thetaSeries_slash_S (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    thetaSeries L ∣[(k : ℤ)] S = thetaSeries L := by
  obtain ⟨m, rfl⟩ : 4 ∣ k := by have := hL.eight_dvd_finrank hU; omega
  rw [hU.thetaSeries_slash_S hk, pow_mul, (by decide : Even 4).neg_pow, I_pow_four]
  simp

end IsEven

/-- **The theta series of an even unimodular lattice is a level-one modular form**: if `L` is
even unimodular and `dim E = 2k`, then `Θ_L` is a modular form of weight `k` for `SL(2, ℤ)`. Its
coercion is `thetaSeries L` (`ZLattice.coe_thetaForm`). -/
noncomputable def thetaForm (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    ModularForm 𝒮ℒ k where
  toFun := thetaSeries L
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z (hL.thetaSeries_slash_S hU hk) (hL.thetaSeries_slash_T _) A
  holo' := mdifferentiable_thetaSeries L
  bdd_at_cusps' hc := (OnePoint.isBoundedAt_iff_forall_SL2Z hc).mpr fun γ _ ↦ by
    rw [slash_action_generators_SL2Z (hL.thetaSeries_slash_S hU hk) (hL.thetaSeries_slash_T _)]
    exact isBoundedAtImInfty_thetaSeries L

/-- The coercion of `ZLattice.thetaForm` to a function is the theta series. -/
@[simp]
theorem coe_thetaForm (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    ⇑(thetaForm hL hU hk) = thetaSeries L :=
  (rfl)

/-- The theta series of an even unimodular lattice is a nonzero modular form. -/
@[simp]
theorem thetaForm_ne_zero (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    thetaForm hL hU hk ≠ 0 := fun h ↦
  thetaSeries_ne_zero_of_re_eq_zero L UpperHalfPlane.I_re (by
    rw [← coe_thetaForm hL hU hk, h, zero_apply])

section Functoriality

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The theta form is invariant under linear isometries: pulling `L` back along a linear
isometry equivalence `e : F ≃ₗᵢ[ℝ] E` does not change it. -/
theorem thetaForm_comap (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k)
    (e : F ≃ₗᵢ[ℝ] E) (hL' : IsEven (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap))
    (hU' : IsUnimodular (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap))
    (hk' : finrank ℝ F = 2 * k) :
    thetaForm hL' hU' hk' = thetaForm hL hU hk :=
  ModularForm.ext fun τ ↦ by simp

variable {M : Submodule ℤ F} [DiscreteTopology M] [IsZLattice ℝ M] {k' : ℕ}

/-- The theta form of an orthogonal direct sum of even unimodular lattices is the product of the
theta forms of the summands, `Θ_{L ⊕ M} = Θ_L Θ_M`, as modular forms of weight `k + k'`. -/
theorem thetaForm_orthSum (hL : IsEven L) (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k)
    (hM : IsEven M) (hUM : IsUnimodular M) (hk' : finrank ℝ F = 2 * k') :
    thetaForm (isEven_orthSum_iff.mpr ⟨hL, hM⟩) (isUnimodular_orthSum_iff.mpr ⟨hU, hUM⟩)
        (by rw [(WithLp.linearEquiv 2 ℝ (E × F)).finrank_eq, finrank_prod, hk, hk', mul_add]) =
      mcast (Nat.cast_add k k').symm ((thetaForm hL hU hk).mul (thetaForm hM hUM hk')) :=
  ModularForm.ext fun τ ↦ by rw [coe_thetaForm]; simp

end Functoriality

/-- **The theta series of an even unimodular lattice is a rational polynomial in `E₄` and `Δ`.**
If `L` is even unimodular and `dim E = 2k`, then
`Θ_L = ∑_{4 a + 12 b = k} c (a, b) • E₄ ^ a * Δ ^ b` for a unique finitely supported family of
rational coefficients `c (a, b)`. -/
theorem IsEven.existsUnique_finsupp_thetaSeries_eq_E₄_discriminant (hL : IsEven L)
    (hU : IsUnimodular L) (hk : finrank ℝ E = 2 * k) :
    ∃! c : ℕ × ℕ →₀ ℚ, (∀ ab ∈ c.support, 4 * ab.1 + 12 * ab.2 = k) ∧
      thetaSeries L = fun τ ↦ c.sum fun ab z ↦ (z : ℂ) * E₄ τ ^ ab.1 * discriminant τ ^ ab.2 := by
  have h4 : 4 ∣ (k : ℤ) := by have := hL.eight_dvd_finrank hU; omega
  -- The `q`-expansion of `Θ_L` has the representation numbers `r_L(2m)` as coefficients.
  have hq : qExpansion 1 (thetaForm hL hU hk) ∈ (PowerSeries.map (Rat.castHom ℂ)).range :=
    RingHom.mem_range.2 ⟨PowerSeries.mk fun m ↦ (representationNumber L (2 * m) : ℚ), by
      ext m
      simp [hL.qExpansion_thetaSeries_coeff]⟩
  obtain ⟨c, ⟨hc, hfc⟩, huniq⟩ := existsUnique_finsupp_E₄_discriminant_of_qExpansion_mem_range
    (Rat.castHom ℂ) (thetaForm hL hU hk) h4 hq
  refine ⟨c, ⟨fun ab hab ↦ by exact_mod_cast hc ab hab, by simpa using hfc⟩,
    fun c' ⟨hc', hfc'⟩ ↦ huniq c' ⟨fun ab hab ↦ by exact_mod_cast hc' ab hab, by simpa using hfc'⟩⟩

end ZLattice
