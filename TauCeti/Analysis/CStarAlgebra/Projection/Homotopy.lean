/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Topology.UnitInterval
public import TauCeti.Algebra.Star.PartialIsometry
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Projection similarity, nearby projections, and projection homotopy in C⋆-algebras

This file develops the basic homotopy and perturbation theory of projections in (possibly
non-unital) complex C⋆-algebras:

* Closed-form exponential of a scaled idempotent `IsIdempotentElem.exp_smul` and the resulting
  explicit exponential path `Unitary.selfAdjointExpPath` connecting `1` to any self-adjoint
  unitary `w` via `t ↦ exp (i π t r)` where `r = (1 - w) / 2`.
* Equivalence of every idempotent to a star projection in a (possibly non-unital) C⋆-algebra,
  with explicit similarity unit `1 - (p - e)` when unital, and upgrade of algebraic equivalence
  `x * y = p`, `y * x = q` of star projections to Murray–von Neumann equivalence.
* Unitary conjugation of nearby star projections (`‖p - q‖ < 1`) by a unitary `u` in the
  identity component satisfying the quantitative bound `‖u - 1‖ ≤ √2 * ‖p - q‖`, together with
  its non-unital unitization and partial-isometry variants.
* Lifting a norm-continuous path of star projections to conjugation by a unitary in the identity
  component (and a partial isometry in the non-unital case), plus the converse projection path
  from a unitary path.
* Explicit reflection and rotation unitaries for orthogonal Murray–von Neumann equivalent
  projections, yielding a continuous path of projections between them.

## Main declarations

* `IsIdempotentElem.exp_smul`: `exp (c • e) = 1 + (exp c - 1) • e` for an idempotent `e`.
* `Unitary.selfAdjointExpPath`: the explicit path `t ↦ exp (i π t ((1 - w) / 2))` from `1` to a
  self-adjoint unitary `w`.
* `IsIdempotentElem.exists_isStarProjection_mul_eq`: every idempotent in a (possibly non-unital)
  C⋆-algebra has an associated star projection `p` with `e * p = p` and `p * e = e`.
* `IsStarProjection.exists_isPartialIsometry_of_mul_eq`: algebraically equivalent star
  projections (`x * y = p`, `y * x = q`) are Murray–von Neumann equivalent.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one`: star projections at distance `< 1`
  are conjugate by a unitary `u` joined to `1` with `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`.
* `IsStarProjection.exists_unitary_conj_of_continuous_path`: homotopic star projections are
  conjugate by a unitary joined to `1`.
* `TauCeti.IsPartialIsometry.reflectionUnitary` and
  `TauCeti.IsPartialIsometry.rotationUnitary`: the self-adjoint reflection
  `1 - p - q + v + star v` and rotation `1 - p - q + v - star v` conjugating orthogonal
  equivalent projections.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Chapter III, §4.6 (Propositions 4.6.2
  and 4.6.4–4.6.6).
-/

public section

open scoped ComplexOrder CStarAlgebra unitInterval

section IdempotentExp

/-- The exponential of a scalar multiple of an idempotent element in a complete normed algebra
simplifies to `1 + (exp c - 1) • e`. -/
theorem IsIdempotentElem.exp_smul {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {e : A} (he : IsIdempotentElem e) (c : 𝕜) :
    NormedSpace.exp (c • e) = 1 + (NormedSpace.exp c - 1) • e := by
  have hpow : ∀ n : ℕ, (c • e) ^ (n + 1) = c ^ (n + 1) • e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, smul_mul_smul_comm, he.eq, ← pow_succ]
  have hscalar : HasSum (fun n : ℕ => ((n + 1).factorial : 𝕜)⁻¹ • c ^ (n + 1))
      (NormedSpace.exp c - 1) := by
    have h0 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) c)
    rw [← hasSum_nat_add_iff' 1] at h0
    simpa [Finset.sum_range_one] using h0
  have htail : HasSum (fun n : ℕ => ((n + 1).factorial : 𝕜)⁻¹ • (c • e) ^ (n + 1))
      ((NormedSpace.exp c - 1) • e) := by
    simpa [hpow, smul_smul] using hscalar.smul_const e
  have hfull : HasSum (fun n : ℕ => (n.factorial : 𝕜)⁻¹ • (c • e) ^ n)
      (1 + (NormedSpace.exp c - 1) • e) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one, add_sub_cancel_left] using htail
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (c • e)).unique hfull

/-- For a star projection `p`, the exponential unitary `exp (i t p)` equals
`1 + (exp (i t) - 1) • p`. -/
theorem IsStarProjection.coe_expUnitary_smul {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
    [CompleteSpace A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • (⟨p, hp.isSelfAdjoint⟩ : selfAdjoint A)) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, ← Complex.coe_smul t p, smul_smul,
    hp.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- For a star projection `p`, the exponential unitary `exp (i π p)` equals `1 - 2 • p`. -/
theorem IsStarProjection.coe_expUnitary_pi_smul {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
    [CompleteSpace A] [StarModule ℂ A]
    {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (Real.pi • (⟨p, hp.isSelfAdjoint⟩ : selfAdjoint A)) : A) =
      1 - (2 : ℂ) • p := by
  rw [hp.coe_expUnitary_smul, mul_comm, Complex.exp_pi_mul_I]
  have h : ((-1 : ℂ) - 1) = -(2 : ℂ) := by norm_num
  rw [h, neg_smul, sub_eq_add_neg]

end IdempotentExp

section SelfAdjointUnitaryPath

namespace Unitary

/-- If `w` is a self-adjoint unitary, then `(1 - w) / 2` is a star projection. -/
theorem isStarProjection_half_one_sub {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    (w : unitary A) (hw : IsSelfAdjoint (w : A)) :
    IsStarProjection ((2 : ℂ)⁻¹ • (1 - (w : A))) where
  isIdempotentElem := by
    rw [IsIdempotentElem, smul_mul_smul_comm]
    have hww : (w : A) * (w : A) = 1 := by
      nth_rw 1 [← hw.star_eq]
      exact Unitary.star_mul_self_of_mem w.property
    have hsq : (1 - (w : A)) * (1 - (w : A)) = (2 : ℂ) • (1 - (w : A)) := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, hww, two_smul]
      abel
    rw [hsq, smul_smul]
    congr 1
    norm_num
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_smul, star_sub, star_one, hw.star_eq]
    congr 1
    norm_num

/-- Every self-adjoint unitary `w` is realized as `exp (i π ((1 - w) / 2))`. -/
theorem expUnitary_pi_smul_half_one_sub {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
    [CompleteSpace A] [StarModule ℂ A]
    (w : unitary A) (hw : IsSelfAdjoint (w : A)) :
    selfAdjoint.expUnitary
        (Real.pi • (⟨(2 : ℂ)⁻¹ • (1 - (w : A)),
          (isStarProjection_half_one_sub w hw).isSelfAdjoint⟩ : selfAdjoint A)) = w := by
  ext
  rw [(isStarProjection_half_one_sub w hw).coe_expUnitary_pi_smul, smul_smul]
  have h2 : (2 : ℂ) * (2 : ℂ)⁻¹ = 1 := by norm_num
  rw [h2, one_smul, sub_sub_cancel]

/-- The explicit exponential path `t ↦ exp (i π t ((1 - w) / 2))` from `1` to a self-adjoint
unitary `w`. -/
noncomputable def selfAdjointExpPath {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
    [CompleteSpace A] [StarModule ℂ A]
    (w : unitary A) (hw : IsSelfAdjoint (w : A)) : Path (1 : unitary A) w where
  toFun t := selfAdjoint.expUnitary
    (((t : ℝ) * Real.pi) •
      (⟨(2 : ℂ)⁻¹ • (1 - (w : A)),
        (isStarProjection_half_one_sub w hw).isSelfAdjoint⟩ : selfAdjoint A))
  continuous_toFun := selfAdjoint.continuous_expUnitary.comp
    ((continuous_subtype_val.mul continuous_const).smul continuous_const)
  source' := by simp
  target' := by simpa using expUnitary_pi_smul_half_one_sub w hw

@[simp]
theorem coe_selfAdjointExpPath {A : Type*}
    [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
    [CompleteSpace A] [StarModule ℂ A]
    (w : unitary A) (hw : IsSelfAdjoint (w : A)) (t : I) :
    ((selfAdjointExpPath w hw t : unitary A) : A) =
      1 + (Complex.exp (Complex.I * (((t : ℝ) : ℂ) * Real.pi)) - 1) •
        ((2 : ℂ)⁻¹ • (1 - (w : A))) := by
  dsimp only [selfAdjointExpPath, Path.coe_mk_mk]
  simpa only [Complex.ofReal_mul] using
    (isStarProjection_half_one_sub w hw).coe_expUnitary_smul ((t : ℝ) * Real.pi)

end Unitary

end SelfAdjointUnitaryPath

section UnitaryConjugation

/-- Conjugating a star projection by a unitary element yields a star projection. -/
theorem IsStarProjection.unitaryConj {A : Type*} [Monoid A] [StarMul A]
    {p : A} (hp : IsStarProjection p) (u : unitary A) :
    IsStarProjection ((u : A) * p * star (u : A)) where
  isIdempotentElem := by
    rw [IsIdempotentElem]
    calc (u : A) * p * star (u : A) * ((u : A) * p * star (u : A))
        = (u : A) * p * (star (u : A) * (u : A)) * p * star (u : A) := by simp only [mul_assoc]
      _ = (u : A) * (p * p) * star (u : A) := by
          rw [Unitary.star_mul_self_of_mem u.property, mul_one]
          simp only [mul_assoc]
      _ = (u : A) * p * star (u : A) := by rw [hp.isIdempotentElem.eq]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_mul, star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]

/-- A path of unitaries starting at `1` induces a continuous path `t ↦ γ t * a * star (γ t)`
conjugating any element `a`. -/
def Unitary.conjPath {A : Type*} [Monoid A] [StarMul A] [TopologicalSpace A]
    [ContinuousMul A] [ContinuousStar A]
    (a : A) {u : unitary A} (γ : Path (1 : unitary A) u) :
    Path a ((u : A) * a * star (u : A)) where
  toFun t := (γ t : A) * a * star (γ t : A)
  continuous_toFun :=
    ((continuous_subtype_val.comp γ.continuous).mul continuous_const).mul
      (continuous_star.comp (continuous_subtype_val.comp γ.continuous))
  source' := by simp
  target' := by simp

@[simp]
theorem Unitary.conjPath_apply {A : Type*} [Monoid A] [StarMul A] [TopologicalSpace A]
    [ContinuousMul A] [ContinuousStar A]
    (a : A) {u : unitary A} (γ : Path (1 : unitary A) u) (t : I) :
    Unitary.conjPath a γ t = (γ t : A) * a * star (γ t : A) := (rfl)

theorem IsStarProjection.isStarProjection_conjPath {A : Type*} [Monoid A] [StarMul A]
    [TopologicalSpace A] [ContinuousMul A] [ContinuousStar A]
    {p : A} (hp : IsStarProjection p) {u : unitary A} (γ : Path (1 : unitary A) u) (t : I) :
    IsStarProjection (Unitary.conjPath p γ t) :=
  hp.unitaryConj (γ t)

/-- Conjugating an element `a : A` by a unitary `u : unitary (Unitization R A)` stays inside the
image of `Unitization.inr`. -/
theorem Unitary.inr_unitizationConj {R A : Type*} [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] (a : A) (u : unitary (Unitization R A)) :
    ((((u : Unitization R A) * (a : Unitization R A) * star (u : Unitization R A)).snd : A) :
        Unitization R A) =
      (u : Unitization R A) * (a : Unitization R A) * star (u : Unitization R A) := by
  apply Unitization.ext
  · simp [Unitization.fst_mul, Unitization.fst_inr]
  · rfl

/-- Conjugating a star projection `p : A` by a unitary `u : unitary (Unitization R A)` yields a
star projection in `A`. -/
theorem IsStarProjection.unitizationConj {R A : Type*} [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [StarModule R A] {p : A} (hp : IsStarProjection p) (u : unitary (Unitization R A)) :
    IsStarProjection
      (((u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A)).snd) := by
  have hp' : IsStarProjection (p : Unitization R A) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom R A)
  have hconj := hp'.unitaryConj u
  rw [← Unitary.inr_unitizationConj p u] at hconj
  refine ⟨?_, ?_⟩
  · exact Unitization.inr_injective (R := R)
      (by simpa [Unitization.inr_mul] using hconj.isIdempotentElem.eq)
  · exact Unitization.inr_injective (R := R)
      (by simpa [Unitization.inr_star] using hconj.isSelfAdjoint.star_eq)

/-- A path of unitaries in `A⁺¹` starting at `1` induces a norm-continuous path inside `A` via
`t ↦ ((γ t) * a * star (γ t)).snd`. -/
def Unitary.unitizationConjPath {A : Type*} [NonUnitalCStarAlgebra A]
    (a : A) {u : unitary A⁺¹} (γ : Path (1 : unitary A⁺¹) u) :
    Path a (((u : A⁺¹) * (a : A⁺¹) * star (u : A⁺¹)).snd) where
  toFun t := ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd
  continuous_toFun := by
    rw [(Unitization.isometry_inr (𝕜 := ℂ) (A := A)).isEmbedding.continuous_iff]
    have hfn :
        Unitization.inr ∘
          (fun t : I => ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd) =
        fun t : I => (γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹) :=
      funext fun t => Unitary.inr_unitizationConj a (γ t)
    rw [hfn]
    exact ((continuous_subtype_val.comp γ.continuous).mul continuous_const).mul
      (continuous_star.comp (continuous_subtype_val.comp γ.continuous))
  source' := by simp
  target' := by simp

@[simp]
theorem Unitary.unitizationConjPath_apply {A : Type*} [NonUnitalCStarAlgebra A]
    (a : A) {u : unitary A⁺¹} (γ : Path (1 : unitary A⁺¹) u) (t : I) :
    Unitary.unitizationConjPath a γ t =
      ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd := (rfl)

theorem IsStarProjection.isStarProjection_unitizationConjPath {A : Type*}
    [NonUnitalCStarAlgebra A] {p : A} (hp : IsStarProjection p)
    {u : unitary A⁺¹} (γ : Path (1 : unitary A⁺¹) u) (t : I) :
    IsStarProjection (Unitary.unitizationConjPath p γ t) :=
  hp.unitizationConj (γ t)

/-- If two star projections in a non-unital star algebra `A` are conjugate by a unitary in
`Unitization R A`, then they are Murray–von Neumann equivalent via a partial isometry in `A`. -/
theorem IsStarProjection.exists_isPartialIsometry_of_unitization_unitary_conj {R A : Type*}
    [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
    {p q : A} (hp : IsStarProjection p) {u : unitary (Unitization R A)}
    (hconj : (u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A) =
      (q : Unitization R A)) :
    ∃ v : A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  let v' : Unitization R A := (u : Unitization R A) * (p : Unitization R A)
  have hfst : v'.fst = 0 := by simp [v', Unitization.fst_mul, Unitization.fst_inr]
  have hv'_eq : (v'.snd : Unitization R A) = v' :=
    Unitization.ext (by simp [Unitization.fst_inr, hfst]) rfl
  have hsv : star v'.snd * v'.snd = p := Unitization.inr_injective (R := R) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hv'_eq]
    calc star ((u : Unitization R A) * (p : Unitization R A)) *
            ((u : Unitization R A) * (p : Unitization R A))
        = (p : Unitization R A) * (star (u : Unitization R A) * (u : Unitization R A)) *
            (p : Unitization R A) := by
          rw [star_mul, ← Unitization.inr_star, hp.isSelfAdjoint.star_eq]
          simp only [mul_assoc]
      _ = (p : Unitization R A) * (p : Unitization R A) := by
          rw [Unitary.star_mul_self_of_mem u.property, mul_one]
      _ = (p : Unitization R A) := by rw [← Unitization.inr_mul, hp.isIdempotentElem.eq]
  have hvs : v'.snd * star v'.snd = q := Unitization.inr_injective (R := R) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hv'_eq]
    calc ((u : Unitization R A) * (p : Unitization R A)) *
            star ((u : Unitization R A) * (p : Unitization R A))
        = (u : Unitization R A) * ((p : Unitization R A) * (p : Unitization R A)) *
            star (u : Unitization R A) := by
          rw [star_mul, ← Unitization.inr_star, hp.isSelfAdjoint.star_eq]
          simp only [mul_assoc]
      _ = (u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A) := by
          rw [← Unitization.inr_mul, hp.isIdempotentElem.eq]
      _ = (q : Unitization R A) := hconj
  have hpi : TauCeti.IsPartialIsometry v'.snd := by
    rw [TauCeti.isPartialIsometry_iff]
    exact Unitization.inr_injective (R := R) <| by
      rw [Unitization.inr_mul, Unitization.inr_mul, Unitization.inr_star, mul_assoc,
        ← Unitization.inr_star, ← Unitization.inr_mul, hsv, hv'_eq]
      dsimp only [v']
      rw [mul_assoc, ← Unitization.inr_mul, hp.isIdempotentElem.eq]
  exact ⟨v'.snd, hpi, hsv, hvs⟩

end UnitaryConjugation

section IdempotentToProjection

/-- If `e` and `p` are idempotents in a ring with `e * p = p` and `p * e = e`, then
`1 - (p - e)` is an invertible element with inverse `1 + (p - e)` conjugating `e` to `p`. -/
def IsIdempotentElem.similarityUnit {A : Type*} [Ring A] {e p : A}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : e * p = p) (hpe : p * e = e) : Aˣ where
  val := 1 - (p - e)
  inv := 1 + (p - e)
  val_inv := by
    have hsq : (p - e) * (p - e) = 0 := by
      rw [mul_sub, sub_mul, sub_mul, hp.eq, he.eq, hep, hpe]
      abel
    calc (1 - (p - e)) * (1 + (p - e))
        = 1 - (p - e) * (p - e) := by
          simp only [mul_add, sub_mul, one_mul, mul_one]
          abel
      _ = 1 := by rw [hsq, sub_zero]
  inv_val := by
    have hsq : (p - e) * (p - e) = 0 := by
      rw [mul_sub, sub_mul, sub_mul, hp.eq, he.eq, hep, hpe]
      abel
    calc (1 + (p - e)) * (1 - (p - e))
        = 1 - (p - e) * (p - e) := by
          simp only [mul_sub, add_mul, one_mul, mul_one]
          abel
      _ = 1 := by rw [hsq, sub_zero]

@[simp]
theorem IsIdempotentElem.coe_similarityUnit {A : Type*} [Ring A] {e p : A}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : e * p = p) (hpe : p * e = e) :
    (he.similarityUnit hp hep hpe : A) = 1 - (p - e) := (rfl)

@[simp]
theorem IsIdempotentElem.coe_similarityUnit_inv {A : Type*} [Ring A] {e p : A}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : e * p = p) (hpe : p * e = e) :
    (↑(he.similarityUnit hp hep hpe)⁻¹ : A) = 1 + (p - e) := (rfl)

theorem IsIdempotentElem.similarityUnit_conj {A : Type*} [Ring A] {e p : A}
    (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
    (hep : e * p = p) (hpe : p * e = e) :
    (he.similarityUnit hp hep hpe : A) * e * (↑(he.similarityUnit hp hep hpe)⁻¹ : A) = p := by
  rw [coe_similarityUnit, coe_similarityUnit_inv]
  have h1 : (1 - (p - e)) * e = e := by
    rw [sub_mul, one_mul, sub_mul, hpe, he.eq]
    abel
  rw [h1, mul_add, mul_one, mul_sub, hep, he.eq]
  abel

private theorem IsIdempotentElem.exists_isStarProjection_mul_eq_unital {A : Type*}
    [CStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let z : A := 1 + Star.star (e - Star.star e) * (e - Star.star e)
  have hz_sa : IsSelfAdjoint z :=
    (IsSelfAdjoint.one (R := A)).add (IsSelfAdjoint.star_mul_self _)
  obtain ⟨zu, hzu⟩ :=
    CStarAlgebra.isUnit_of_le (1 : A)
      (le_add_of_nonneg_right (star_mul_self_nonneg (e - Star.star e)))
  let zinv : A := (zu⁻¹ : Aˣ)
  have hmul_right : z * zinv = 1 := by dsimp only [z]; rw [← hzu]; exact zu.mul_inv
  have hzinv_sa : IsSelfAdjoint zinv := hz_sa.of_mul_eq_one hmul_right
  have hz_expand : z = 1 + Star.star e * e - Star.star e - e + e * Star.star e := by
    have hse_idem : Star.star e * Star.star e = Star.star e := by rw [← star_mul, he.eq]
    dsimp only [z]
    rw [star_sub, star_star, sub_mul, mul_sub, mul_sub, hse_idem, he.eq]
    abel
  have hez : e * z = e * Star.star e * e := by
    rw [hz_expand]
    simp only [mul_add, mul_sub, mul_one, ← mul_assoc, he.eq]
    abel
  have hze : z * e = e * Star.star e * e := by
    rw [hz_expand]
    simp only [add_mul, sub_mul, one_mul, mul_assoc, he.eq]
    abel
  have hcomm_e_inv : Commute e zinv := by
    have hcomm_zu : Commute e (zu : A) := by rw [hzu, Commute, SemiconjBy, hez, hze]
    exact hcomm_zu.units_inv_right
  have hcomm_se_inv : Commute (Star.star e) zinv := by
    rw [Commute, SemiconjBy]
    have := congr_arg Star.star hcomm_e_inv.eq
    simpa [star_mul, hzinv_sa.star_eq] using this.symm
  refine ⟨e * Star.star e * zinv, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsIdempotentElem]
    calc (e * Star.star e * zinv) * (e * Star.star e * zinv)
        = (e * Star.star e * (zinv * e)) * (Star.star e * zinv) := by simp only [mul_assoc]
      _ = (e * Star.star e * (e * zinv)) * (Star.star e * zinv) := by rw [hcomm_e_inv.eq]
      _ = ((e * Star.star e * e) * zinv) * (Star.star e * zinv) := by simp only [mul_assoc]
      _ = (e * (z * zinv)) * (Star.star e * zinv) := by rw [← hez]; simp only [mul_assoc]
      _ = e * Star.star e * zinv := by rw [hmul_right, mul_one, mul_assoc]
  · rw [IsSelfAdjoint, star_mul, star_mul, star_star, hzinv_sa.star_eq,
      ← mul_assoc zinv e, ← hcomm_e_inv.eq, mul_assoc, ← hcomm_se_inv.eq, ← mul_assoc]
  · rw [← mul_assoc, ← mul_assoc, he.eq]
  · calc (e * Star.star e * zinv) * e = e * Star.star e * (zinv * e) := mul_assoc _ _ _
      _ = (e * Star.star e * e) * zinv := by rw [← hcomm_e_inv.eq, ← mul_assoc]
      _ = e * (z * zinv) := by rw [← hez, mul_assoc]
      _ = e := by rw [hmul_right, mul_one]

/-- Every idempotent in a (possibly non-unital) C⋆-algebra has an associated star projection `p`
with `e * p = p` and `p * e = e` (Blackadar, Proposition 4.6.2). When `A` is unital, `e` is
similar to `p` via `IsIdempotentElem.similarityUnit`. -/
theorem IsIdempotentElem.exists_isStarProjection_mul_eq {A : Type*}
    [NonUnitalCStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  have he' : IsIdempotentElem (e : A⁺¹) := by
    rw [IsIdempotentElem, ← Unitization.inr_mul, he.eq]
  obtain ⟨p', hp', hep', hp'e⟩ := he'.exists_isStarProjection_mul_eq_unital
  have hfst : p'.fst = 0 := by
    have := congr_arg (fun x : A⁺¹ => x.fst) hep'
    simpa [Unitization.fst_mul, Unitization.fst_inr] using this.symm
  have hp'_eq : (p'.snd : A⁺¹) = p' :=
    Unitization.ext (by simp [Unitization.fst_inr, hfst]) rfl
  refine ⟨p'.snd, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact Unitization.inr_injective (R := ℂ) (by
      rw [Unitization.inr_mul, hp'_eq]
      exact hp'.isIdempotentElem.eq)
  · exact Unitization.inr_injective (R := ℂ) (by
      rw [Unitization.inr_star, hp'_eq]
      exact hp'.isSelfAdjoint.star_eq)
  · exact Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hp'_eq, hep'])
  · exact Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hp'_eq, hp'e])

end IdempotentToProjection

section AlgebraicEquivalence

/-- Spectral inverse square root identities for a self-adjoint element with strictly positive
real spectrum. -/
private theorem cfc_inv_sqrt_spec {A : Type*} [CStarAlgebra A]
    {b : A} (hb : IsSelfAdjoint b) (hb_pos : ∀ t ∈ spectrum ℝ b, 0 < t) :
    let r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
    IsSelfAdjoint r ∧ b * (r * r) = 1 ∧ (r * r) * b = 1 ∧ b * r = cfc Real.sqrt b := by
  intro r
  have hf_cont : ContinuousOn (fun t : ℝ => (Real.sqrt t)⁻¹) (spectrum ℝ b) :=
    ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun t ht =>
      (Real.sqrt_pos.mpr (hb_pos t ht)).ne'
  have hr_sa : IsSelfAdjoint r := cfc_predicate _ b
  have hrr : r * r = cfc (fun t : ℝ => t⁻¹) b := by
    dsimp only [r]
    rw [← cfc_mul (hf := hf_cont) (hg := hf_cont)]
    refine cfc_congr fun t ht => ?_
    rw [← mul_inv, Real.mul_self_sqrt (hb_pos t ht).le]
  have hb_rr : b * (r * r) = 1 := by
    have hinv_cont : ContinuousOn (fun t : ℝ => t⁻¹) (spectrum ℝ b) :=
      ContinuousOn.inv₀ continuousOn_id fun t ht => (hb_pos t ht).ne'
    nth_rw 1 [← cfc_id ℝ b]
    rw [hrr, ← cfc_mul (hf := continuousOn_id) (hg := hinv_cont)]
    trans cfc (fun _ : ℝ => (1 : ℝ)) b
    · refine cfc_congr fun t ht => mul_inv_cancel₀ (hb_pos t ht).ne'
    · rw [cfc_const (1 : ℝ) b, map_one]
  have hrr_b : (r * r) * b = 1 := by
    have hcomm : Commute r b := (Commute.refl b).cfc_real _
    rw [(hcomm.mul_left hcomm).eq, hb_rr]
  have hb_r : b * r = cfc Real.sqrt b := by
    nth_rw 1 [← cfc_id ℝ b]
    dsimp only [r]
    rw [← cfc_mul (hf := continuousOn_id) (hg := hf_cont)]
    refine cfc_congr fun t ht => ?_
    nth_rw 1 [← Real.mul_self_sqrt (hb_pos t ht).le]
    rw [id_eq, mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hb_pos t ht)).ne', mul_one]
  exact ⟨hr_sa, hb_rr, hrr_b, hb_r⟩

private theorem IsStarProjection.exists_mul_cfc_of_mul_eq_unital {A : Type*} [CStarAlgebra A]
    {p q x y : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hxy : x * y = p) (hyx : y * x = q)
    (hpx : p * x = x) (hqy : q * y = y) (hyp : y * p = y) :
    ∃ r : A, star (y * r) * (y * r) = p ∧ (y * r) * star (y * r) = q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hpsy : p * star y = star y := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congr_arg star hyp
  let a : A := star y * y
  let b : A := a + (1 - p)
  have ha_nonneg : 0 ≤ a := star_mul_self_nonneg y
  have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (add_nonneg ha_nonneg hp.one_sub.nonneg)
  let M : ℝ := ‖star x * x‖ + 1
  have hM_pos : 0 < M := by positivity
  have hMinv_pos : 0 < M⁻¹ := inv_pos.mpr hM_pos
  have hMinv_le_one : M⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_add_of_nonneg_left (norm_nonneg _))
  have hP_le_Ma : p ≤ M • a := by
    have hp_eq : p = star y * (star x * x) * y := by
      calc p = star p * p := by rw [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
        _ = star (x * y) * (x * y) := by rw [hxy]
        _ = star y * (star x * x) * y := by simp only [star_mul, mul_assoc]
    calc p = star y * (star x * x) * y := hp_eq
      _ ≤ ‖star x * x‖ • a :=
        CStarAlgebra.star_left_conjugate_le_norm_smul y (star x * x) (IsSelfAdjoint.star_mul_self x)
      _ ≤ M • a := smul_le_smul_of_nonneg_right (by linarith) ha_nonneg
  have hMinv_le_b : algebraMap ℝ A M⁻¹ ≤ b := by
    have h1 : M⁻¹ • p ≤ a := by
      have := smul_le_smul_of_nonneg_left hP_le_Ma hMinv_pos.le
      rwa [inv_smul_smul₀ hM_pos.ne'] at this
    have h2 : M⁻¹ • ((1 : A) - p) ≤ 1 - p := by
      simpa only [one_smul] using smul_le_smul_of_nonneg_right hMinv_le_one hp.one_sub.nonneg
    calc algebraMap ℝ A M⁻¹ = M⁻¹ • (p + (1 - p)) := by
          rw [Algebra.algebraMap_eq_smul_one, add_sub_cancel]
      _ = M⁻¹ • p + M⁻¹ • (1 - p) := smul_add M⁻¹ p (1 - p)
      _ ≤ a + (1 - p) := add_le_add h1 h2
  have hb_pos : ∀ t ∈ spectrum ℝ b, 0 < t := fun t ht =>
    hMinv_pos.trans_le ((algebraMap_le_iff_le_spectrum hb_sa).mp hMinv_le_b t ht)
  obtain ⟨hr_sa, hb_rr, hrr_b, -⟩ := cfc_inv_sqrt_spec hb_sa hb_pos
  set r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
  have hbp : b * p = a := by
    dsimp only [b, a]; rw [add_mul, mul_assoc, hyp, hp.one_sub_mul_self, add_zero]
  have hpb : p * b = a := by
    dsimp only [b, a]; rw [mul_add, ← mul_assoc, hpsy, hp.mul_one_sub_self, add_zero]
  have hcomm_rp : Commute r p := (by rw [Commute, SemiconjBy, hbp, hpb] : Commute b p).cfc_real _
  have hcomm_rb : Commute r b := (Commute.refl b).cfc_real _
  refine ⟨r, ?_, ?_⟩
  · calc star (y * r) * (y * r) = r * a * r := by
          simp only [a, star_mul, hr_sa.star_eq, mul_assoc]
      _ = (r * b) * (p * r) := by rw [← hbp]; simp only [mul_assoc]
      _ = (b * (r * r)) * p := by rw [hcomm_rb.eq, ← hcomm_rp.eq]; simp only [mul_assoc]
      _ = p := by rw [hb_rr, one_mul]
  · have hqyr : q * (y * r) = y * r := by rw [← mul_assoc, hqy]
    have h1 : q * ((y * r) * star (y * r)) = (y * r) * star (y * r) := by rw [← mul_assoc, hqyr]
    have h2 : ((y * r) * star (y * r)) * q = (y * r) * star (y * r) := by
      simpa only [star_mul, star_star, hq.isSelfAdjoint.star_eq] using congr_arg star h1
    rw [← h2]
    calc ((y * r) * star (y * r)) * q = y * (r * r) * a * x := by
          rw [← hyx]; simp only [a, star_mul, hr_sa.star_eq, mul_assoc]
      _ = y * ((r * r) * b) * (p * x) := by rw [← hbp]; simp only [mul_assoc]
      _ = q := by rw [hrr_b, mul_one, hpx, hyx]

/-- Algebraic equivalence of star projections implies Murray–von Neumann equivalence: if `p` and
`q` are star projections in a (possibly non-unital) C⋆-algebra and `x * y = p`, `y * x = q`, then
there exists a partial isometry `v` in `A` with `star v * v = p` and `v * star v = q`
(Blackadar, Proposition 4.6.4). -/
theorem IsStarProjection.exists_isPartialIsometry_of_mul_eq {A : Type*} [NonUnitalCStarAlgebra A]
    {p q x y : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hxy : x * y = p) (hyx : y * x = q) :
    ∃ v : A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  let x' : A := p * x * q
  let y' : A := q * y * p
  have hx'y' : x' * y' = p := by
    calc p * x * q * (q * y * p)
        = p * x * (q * q) * y * p := by simp only [mul_assoc]
      _ = p * (x * y) * (x * y) * p := by rw [hq.isIdempotentElem.eq, ← hyx]; simp only [mul_assoc]
      _ = p := by rw [hxy]; simp only [hp.isIdempotentElem.eq]
  have hy'x' : y' * x' = q := by
    calc q * y * p * (p * x * q)
        = q * y * (p * p) * x * q := by simp only [mul_assoc]
      _ = q * (y * x) * (y * x) * q := by rw [hp.isIdempotentElem.eq, ← hxy]; simp only [mul_assoc]
      _ = q := by rw [hyx]; simp only [hq.isIdempotentElem.eq]
  have hpx' : p * x' = x' := by
    dsimp only [x']; rw [← mul_assoc, ← mul_assoc, hp.isIdempotentElem.eq]
  have hqy' : q * y' = y' := by
    dsimp only [y']; rw [← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq]
  have hy'p : y' * p = y' := by dsimp only [y']; rw [mul_assoc, hp.isIdempotentElem.eq]
  have hP : IsStarProjection (p : A⁺¹) := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hQ : IsStarProjection (q : A⁺¹) := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨r, hsV_V, hV_sV⟩ := hP.exists_mul_cfc_of_mul_eq_unital hQ
    (by rw [← Unitization.inr_mul, hx'y']) (by rw [← Unitization.inr_mul, hy'x'])
    (by rw [← Unitization.inr_mul, hpx']) (by rw [← Unitization.inr_mul, hqy'])
    (by rw [← Unitization.inr_mul, hy'p])
  let V : A⁺¹ := (y' : A⁺¹) * r
  have hv_eq : (V.snd : A⁺¹) = V := Unitization.ext (by simp [V]) rfl
  have hvp : star V.snd * V.snd = p := Unitization.inr_injective (R := ℂ) (by
    rw [Unitization.inr_mul, Unitization.inr_star, hv_eq, hsV_V])
  have hvq : V.snd * star V.snd = q := Unitization.inr_injective (R := ℂ) (by
    rw [Unitization.inr_mul, Unitization.inr_star, hv_eq, hV_sV])
  exact ⟨V.snd, TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hvp ▸ hp),
    hvp, hvq⟩

end AlgebraicEquivalence

section NearbyProjections

/-- Purely algebraic identities for the intertwining element `z = q * p + (1 - q) * (1 - p)`
and `b = 1 - (p - q) ^ 2` of two star projections `p` and `q` in a star ring. -/
private theorem nearby_proj_algebra {A : Type*} [Ring A] [StarRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    let z : A := q * p + (1 - q) * (1 - p)
    let b : A := 1 - (p - q) * (p - q)
    z * p = q * p ∧ q * z = q * p ∧ star z * z = b ∧ z * star z = b ∧
      z + star z = b + b ∧ Commute b z ∧ Commute b p := by
  intro z b
  have hps : star p = p := hp.isSelfAdjoint.star_eq
  have hqs : star q = q := hq.isSelfAdjoint.star_eq
  have hpp : p * p = p := hp.isIdempotentElem.eq
  have hqq : q * q = q := hq.isIdempotentElem.eq
  have hzp : z * p = q * p := by
    dsimp only [z]
    rw [add_mul, mul_assoc, hpp, mul_assoc, hp.one_sub_mul_self, mul_zero, add_zero]
  have hqz : q * z = q * p := by
    dsimp only [z]
    rw [mul_add, ← mul_assoc, hqq, ← mul_assoc, hq.mul_one_sub_self, zero_mul, add_zero]
  have hsz : star z = p * q + (1 - p) * (1 - q) := by
    dsimp only [z]
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hps, hqs]
  have hmul : ∀ {r s : A}, IsStarProjection r → IsStarProjection s →
      (r * s + (1 - r) * (1 - s)) * (s * r + (1 - s) * (1 - r)) = 1 - (r - s) * (r - s) := by
    intro r s hr hs
    rw [add_mul, mul_add, mul_add]
    have h1 : r * s * (s * r) = r * s * r := by
      rw [mul_assoc, ← mul_assoc s s, hs.isIdempotentElem.eq, ← mul_assoc]
    have h2 : r * s * ((1 - s) * (1 - r)) = 0 := by
      rw [mul_assoc, ← mul_assoc s (1 - s), hs.mul_one_sub_self, zero_mul, mul_zero]
    have h3 : (1 - r) * (1 - s) * (s * r) = 0 := by
      rw [mul_assoc, ← mul_assoc (1 - s) s, hs.one_sub_mul_self, zero_mul, mul_zero]
    have h4 : (1 - r) * (1 - s) * ((1 - s) * (1 - r)) = (1 - r) * (1 - s) * (1 - r) := by
      rw [mul_assoc, ← mul_assoc (1 - s) (1 - s), hs.one_sub.isIdempotentElem.eq, ← mul_assoc]
    rw [h1, h2, h3, h4, add_zero, zero_add]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hr.isIdempotentElem.eq, hs.isIdempotentElem.eq]
    abel
  have hsz_z : star z * z = b := by rw [hsz]; exact hmul hp hq
  have hz_sz : z * star z = b := by
    rw [hsz]
    have hqp : (q - p) * (q - p) = (p - q) * (p - q) := by
      simp only [sub_mul, mul_sub]; abel
    simpa only [b, hqp] using hmul hq hp
  have hz_add : z + star z = b + b := by
    rw [hsz]; dsimp only [z, b]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hpp, hqq]; abel
  have hcomm_bz : Commute b z := by
    rw [Commute, SemiconjBy]
    calc b * z = (z * star z) * z := by rw [hz_sz]
      _ = z * (star z * z) := mul_assoc _ _ _
      _ = z * b := by rw [hsz_z]
  have hcomm_bp : Commute b p := by
    refine (Commute.one_left p).sub_left ?_
    rw [Commute, SemiconjBy]
    simp only [sub_mul, mul_sub, ← mul_assoc, hpp, hqq]
    simp only [mul_assoc, hpp]
    abel
  exact ⟨hzp, hqz, hsz_z, hz_sz, hz_add, hcomm_bz, hcomm_bp⟩

/-- Two star projections in a unital C⋆-algebra at distance `< 1` are conjugate by a unitary in
the identity component satisfying the quantitative bound `‖(u : A) - 1‖ ≤ √2 * ‖p - q‖`
(Blackadar, Proposition 4.6.5). -/
theorem IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one {A : Type*} [CStarAlgebra A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) (hnorm : ‖p - q‖ < 1) :
    ∃ u : unitary A, (u : A) * p * star (u : A) = q ∧
      ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A) u := by
  rcases subsingleton_or_nontrivial A with _ | _
  · exact ⟨1, Subsingleton.elim _ _, by simp, Joined.refl 1⟩
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let z : A := q * p + (1 - q) * (1 - p)
  let d : A := (p - q) * (p - q)
  let b : A := 1 - d
  obtain ⟨hzp, hqz, hsz_z, hz_sz, hz_add, hcomm_bz, hcomm_bp⟩ := nearby_proj_algebra hp hq
  -- Spectral localization: `spectrum ℝ b ⊆ [1 - ‖p - q‖^2, 1] ⊂ (0, 1]`.
  have hsub_sa : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hd_nonneg : 0 ≤ d := by simpa only [d, hsub_sa.star_eq] using star_mul_self_nonneg (p - q)
  have hd_sa : IsSelfAdjoint d := IsSelfAdjoint.of_nonneg hd_nonneg
  have hb_sa : IsSelfAdjoint b := (IsSelfAdjoint.one (R := A)).sub hd_sa
  have hd_norm : ‖d‖ = ‖p - q‖ ^ 2 := by
    calc ‖d‖ = ‖star (p - q) * (p - q)‖ := by rw [hsub_sa.star_eq]
      _ = ‖p - q‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
  have hd_le : d ≤ algebraMap ℝ A (‖p - q‖ ^ 2) := by
    refine (le_algebraMap_iff_spectrum_le hd_sa).mpr fun t ht => ?_
    have hle : ‖t‖ ≤ ‖d‖ := spectrum.norm_le_norm_of_mem ht
    rw [Real.norm_eq_abs, hd_norm] at hle
    exact (le_abs_self t).trans hle
  have hb_spec : ∀ s ∈ spectrum ℝ b, 1 - ‖p - q‖ ^ 2 ≤ s ∧ s ≤ 1 := fun s hs => by
    have hlow : algebraMap ℝ A (1 - ‖p - q‖ ^ 2) ≤ b := by
      rw [map_sub, map_one]; exact sub_le_sub_left hd_le 1
    have hhigh : b ≤ algebraMap ℝ A 1 := by rw [map_one]; exact sub_le_self 1 hd_nonneg
    exact ⟨(algebraMap_le_iff_le_spectrum hb_sa).mp hlow s hs,
      (le_algebraMap_iff_spectrum_le hb_sa).mp hhigh s hs⟩
  have hb_pos : ∀ s ∈ spectrum ℝ b, 0 < s := fun s hs => by
    have hsq : ‖p - q‖ ^ 2 < 1 := by nlinarith [norm_nonneg (p - q)]
    linarith [(hb_spec s hs).1]
  -- Polar unitary `u = z * b⁻¹/²` and conjugation `u * p * u⋆ = q`.
  obtain ⟨hr_sa, hb_rr, -, hb_r⟩ := cfc_inv_sqrt_spec hb_sa hb_pos
  set r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
  have hcomm_rz : Commute r z := hcomm_bz.cfc_real _
  have hcomm_rp : Commute r p := hcomm_bp.cfc_real _
  have hcomm_rb : Commute r b := (Commute.refl b).cfc_real _
  have hcomm_rsz : Commute r (star z) := by
    rw [Commute, SemiconjBy]
    simpa only [star_mul, hr_sa.star_eq] using (congr_arg star hcomm_rz.eq).symm
  let uVal : A := z * r
  have hu_mem : uVal ∈ unitary A := by
    rw [Unitary.mem_iff]
    constructor
    · calc star uVal * uVal = r * b * r := by
            dsimp only [uVal, b, d, z]
            rw [← hsz_z]
            simp only [star_mul, hr_sa.star_eq, mul_assoc]
        _ = 1 := by rw [hcomm_rb.eq, mul_assoc, hb_rr]
    · calc uVal * star uVal = z * (r * r) * star z := by
            simp only [uVal, star_mul, hr_sa.star_eq, mul_assoc]
        _ = b * (r * r) := by
            rw [mul_assoc z (r * r), (hcomm_rsz.mul_left hcomm_rsz).eq, ← mul_assoc, hz_sz]
        _ = 1 := hb_rr
  let u : unitary A := ⟨uVal, hu_mem⟩
  have hu_conj : (u : A) * p * star (u : A) = q := by
    dsimp only [u, uVal]
    calc z * r * p * star (z * r) = (z * p) * ((r * r) * star z) := by
          rw [star_mul, hr_sa.star_eq, mul_assoc z r p, hcomm_rp.eq]; simp only [mul_assoc]
      _ = q * (b * (r * r)) := by
          rw [hzp, ← hqz, (hcomm_rsz.mul_left hcomm_rsz).eq]
          dsimp only [b, d, z]
          rw [← hz_sz]
          simp only [mul_assoc]
      _ = q := by rw [hb_rr, mul_one]
  -- Quantitative bound `‖u - 1‖ ≤ √2 * ‖p - q‖` via `|u - 1|² = 2 (1 - √b)`.
  have hu_sub_sq : star ((u : A) - 1) * ((u : A) - 1) =
      cfc (fun s : ℝ => 2 * (1 - Real.sqrt s)) b := by
    have hu_add : (u : A) + star (u : A) = (2 : ℝ) • cfc Real.sqrt b := by
      dsimp only [u, uVal]
      rw [star_mul, hr_sa.star_eq, hcomm_rsz.eq, ← add_mul, hz_add, ← two_smul ℝ b,
        smul_mul_assoc, hb_r]
    have h1 : star ((u : A) - 1) * ((u : A) - 1) =
        (2 : ℝ) • (1 : A) - ((u : A) + star (u : A)) := by
      simp only [star_sub, star_one, sub_mul, mul_sub, one_mul, mul_one,
        Unitary.star_mul_self_of_mem u.property, two_smul]; abel
    rw [h1, hu_add, ← smul_sub, ← map_one (algebraMap ℝ A), ← cfc_const (1 : ℝ) b,
      ← cfc_sub (hf := continuousOn_const) (hg := Real.continuous_sqrt.continuousOn),
      ← cfc_const_mul (2 : ℝ) (fun s : ℝ => 1 - Real.sqrt s) b]
  have hnorm_bound : ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := by
    have hsq_le : ‖(u : A) - 1‖ ^ 2 ≤ (√2 * ‖p - q‖) ^ 2 := by
      rw [sq, ← CStarRing.norm_star_mul_self, hu_sub_sq, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      refine norm_cfc_le (by positivity) fun s hs => ?_
      have hs0 : 0 ≤ s := (hb_pos s hs).le
      obtain ⟨hs_lo, hs_hi⟩ := hb_spec s hs
      have hsqrt_le : Real.sqrt s ≤ 1 := by simpa using Real.sqrt_le_sqrt hs_hi
      have hle_sqrt : s ≤ Real.sqrt s := by
        calc s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs0).symm
          _ ≤ Real.sqrt s := Real.sqrt_le_sqrt (by nlinarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h_nonneg : 0 ≤ √2 * ‖p - q‖ := by positivity
    nlinarith [norm_nonneg ((u : A) - 1)]
  have hlt2 : ‖(u : A) - 1‖ < 2 := by
    have hsqrt2 : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    calc ‖(u : A) - 1‖ ≤ √2 * ‖p - q‖ := hnorm_bound
      _ ≤ √2 * 1 := mul_le_mul_of_nonneg_left hnorm.le (Real.sqrt_nonneg 2)
      _ < 2 := by linarith
  exact ⟨u, hu_conj, hnorm_bound, Unitary.joined 1 u hlt2⟩

/-- Non-unital version of `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one` via the
unitization `A⁺¹`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hnorm : ‖p - q‖ < 1) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      ‖(u : A⁺¹) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A⁺¹) u := by
  have hp' : IsStarProjection (p : A⁺¹) := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' : IsStarProjection (q : A⁺¹) := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hnorm' : ‖(p : A⁺¹) - (q : A⁺¹)‖ < 1 := by
    rwa [← Unitization.inr_sub, Unitization.norm_inr]
  obtain ⟨u, hconj, hbd, hjoin⟩ := hp'.exists_unitary_conj_of_norm_sub_lt_one hq' hnorm'
  rw [← Unitization.inr_sub, Unitization.norm_inr] at hbd
  exact ⟨u, hconj, hbd, hjoin⟩

/-- Star projections at distance `< 1` in a (possibly non-unital) C⋆-algebra are Murray–von
Neumann equivalent via a partial isometry inside `A`. -/
theorem IsStarProjection.exists_isPartialIsometry_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hnorm : ‖p - q‖ < 1) :
    ∃ v : A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  obtain ⟨u, hconj, -, -⟩ := hp.exists_unitization_unitary_conj_of_norm_sub_lt_one hq hnorm
  exact hp.exists_isPartialIsometry_of_unitization_unitary_conj hconj

end NearbyProjections

section ProjectionHomotopy

/-- If `γ : I → A` is a continuous path of star projections in a unital C⋆-algebra, then `γ 0`
and `γ 1` are conjugate by a unitary in the identity component (Blackadar, Proposition 4.6.6). -/
theorem IsStarProjection.exists_unitary_conj_of_continuous_path {A : Type*} [CStarAlgebra A]
    {γ : I → A} (hγ : Continuous γ) (hproj : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A, (u : A) * γ 0 * star (u : A) = γ 1 ∧ Joined (1 : unitary A) u := by
  have hunif : UniformContinuous γ := CompactSpace.uniformContinuous_of_continuous hγ
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuous_iff.mp hunif 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  let M : ℕ := N + 1
  have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
  let pt : ∀ k : ℕ, k ≤ M → I := fun k hk =>
    ⟨(k : ℝ) / (M : ℝ), by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hM_pos]
      exact_mod_cast hk⟩
  have hstep : ∀ k : ℕ, (hk : k ≤ M) →
      ∃ u : unitary A,
        (u : A) * γ 0 * star (u : A) = γ (pt k hk) ∧ Joined (1 : unitary A) u := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨1, ?_, Joined.refl 1⟩
      have h0 : pt 0 hk = 0 := Subtype.ext (by simp [pt])
      simp [h0]
    | succ k ih =>
      intro hk
      have hk' : k ≤ M := Nat.le_of_succ_le hk
      obtain ⟨u, hu_conj, hu_join⟩ := ih hk'
      have hdiff_lt : ‖γ (pt k hk') - γ (pt (k + 1) hk)‖ < 1 := by
        rw [← dist_eq_norm]
        apply hdist
        rw [Subtype.dist_eq, Real.dist_eq]
        have hsub : ((k : ℝ) / (M : ℝ)) - (((k + 1 : ℕ) : ℝ) / (M : ℝ)) =
            -(1 / (M : ℝ)) := by
          push_cast
          ring
        rw [hsub, abs_neg, abs_of_pos (by positivity)]
        simpa [M] using hN
      obtain ⟨v, hv_conj, -, hv_join⟩ :=
        (hproj (pt k hk')).exists_unitary_conj_of_norm_sub_lt_one (hproj (pt (k + 1) hk)) hdiff_lt
      refine ⟨v * u, ?_, ?_⟩
      · calc ((v * u : unitary A) : A) * γ 0 * star ((v * u : unitary A) : A)
            = (v : A) * ((u : A) * γ 0 * star (u : A)) * star (v : A) := by
              simp only [Submonoid.coe_mul, star_mul, mul_assoc]
          _ = (v : A) * γ (pt k hk') * star (v : A) := by rw [hu_conj]
          _ = γ (pt (k + 1) hk) := hv_conj
      · simpa using hv_join.mul hu_join
  obtain ⟨u, hu_conj, hu_join⟩ := hstep M le_rfl
  have h1 : pt M le_rfl = 1 := Subtype.ext (by simp [pt])
  exact ⟨u, h1 ▸ hu_conj, hu_join⟩

/-- Non-unital version of `IsStarProjection.exists_unitary_conj_of_continuous_path` via `A⁺¹`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_continuous_path {A : Type*}
    [NonUnitalCStarAlgebra A] {γ : I → A} (hγ : Continuous γ)
    (hproj : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (γ 0 : A⁺¹) * star (u : A⁺¹) = (γ 1 : A⁺¹) ∧
      Joined (1 : unitary A⁺¹) u :=
  IsStarProjection.exists_unitary_conj_of_continuous_path
    (γ := fun t => (γ t : A⁺¹))
    (Unitization.continuous_inr.comp hγ)
    (fun t => (hproj t).map (Unitization.inrNonUnitalStarAlgHom ℂ A))

/-- Endpoints of a continuous path of star projections in a (possibly non-unital) C⋆-algebra are
Murray–von Neumann equivalent via a partial isometry in `A`. -/
theorem IsStarProjection.exists_isPartialIsometry_of_continuous_path {A : Type*}
    [NonUnitalCStarAlgebra A] {γ : I → A} (hγ : Continuous γ)
    (hproj : ∀ t : I, IsStarProjection (γ t)) :
    ∃ v : A, TauCeti.IsPartialIsometry v ∧ star v * v = γ 0 ∧ v * star v = γ 1 := by
  obtain ⟨u, hconj, -⟩ :=
    IsStarProjection.exists_unitization_unitary_conj_of_continuous_path hγ hproj
  exact (hproj 0).exists_isPartialIsometry_of_unitization_unitary_conj hconj

end ProjectionHomotopy

section OrthogonalUnitaries

namespace TauCeti.IsPartialIsometry

variable {A : Type*} [Ring A] [StarRing A]

private theorem orth_relations {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    (v * star v) * (star v * v) = 0 ∧
      v * v = 0 ∧ star v * star v = 0 ∧
      (star v * v) * v = 0 ∧ v * (v * star v) = 0 ∧
      (v * star v) * star v = 0 ∧ star v * (star v * v) = 0 ∧
      v * (star v * v) = v ∧ (v * star v) * v = v ∧
      (star v * v) * star v = star v ∧ star v * (v * star v) = star v := by
  have hqp : (v * star v) * (star v * v) = 0 := by
    simpa [star_mul, mul_assoc] using congr_arg star hpq
  have hvp : v * (star v * v) = v := by rw [← mul_assoc, hv.mul_star_mul_self]
  have hqv : (v * star v) * v = v := hv.mul_star_mul_self
  have hps : (star v * v) * star v = star v := by
    simpa [star_mul, mul_assoc] using congr_arg star hvp
  have hsq : star v * (v * star v) = star v := by
    simpa [star_mul, mul_assoc] using congr_arg star hqv
  have hvv : v * v = 0 := by
    calc v * v = (v * (star v * v)) * ((v * star v) * v) := by rw [hvp, hqv]
      _ = v * ((star v * v) * (v * star v)) * v := by simp only [mul_assoc]
      _ = 0 := by rw [hpq, mul_zero, zero_mul]
  have hss : star v * star v = 0 := by simpa [star_mul] using congr_arg star hvv
  have hpv : (star v * v) * v = 0 := by rw [mul_assoc, hvv, mul_zero]
  have hvq : v * (v * star v) = 0 := by rw [← mul_assoc, hvv, zero_mul]
  have hqs : (v * star v) * star v = 0 := by rw [mul_assoc, hss, mul_zero]
  have hsp : star v * (star v * v) = 0 := by rw [← mul_assoc, hss, zero_mul]
  exact ⟨hqp, hvv, hss, hpv, hvq, hqs, hsp, hvp, hqv, hps, hsq⟩

/-- The self-adjoint reflection unitary `1 - p - q + v + star v` exchanging orthogonal initial
and final projections `p = star v * v` and `q = v * star v` of a partial isometry `v`. -/
def reflectionUnitary {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) : unitary A :=
  ⟨1 - star v * v - v * star v + v + star v, by
    obtain ⟨hqp, hvv, hss, hpv, hvq, hqs, hsp, hvp, hqv, hps, hsq⟩ := orth_relations hv hpq
    have hp := hv.isStarProjection_star_mul_self
    have hq := hv.isStarProjection_mul_star_self
    set p := star v * v
    set q := v * star v
    have hsa : star (1 - p - q + v + star v) = 1 - p - q + v + star v := by
      simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_star]
      abel
    have h1 : (1 - p - q) * (1 - p - q) = 1 - p - q := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hp.isIdempotentElem.eq,
        hq.isIdempotentElem.eq, hpq, hqp]
      abel
    have h2 : (1 - p - q) * (v + star v) = 0 := by
      simp only [sub_mul, mul_add, one_mul, hpv, hqv, hps, hqs]
      abel
    have h3 : (v + star v) * (1 - p - q) = 0 := by
      simp only [add_mul, mul_sub, mul_one, hvp, hvq, hsp, hsq]
      abel
    have h4 : (v + star v) * (v + star v) = q + p := by
      simp only [add_mul, mul_add, hvv, hss]
      abel
    have hsq1 : (1 - p - q + v + star v) * (1 - p - q + v + star v) = 1 := by
      have hr : 1 - p - q + v + star v = (1 - p - q) + (v + star v) := by abel
      rw [hr, add_mul, mul_add (1 - p - q), mul_add (v + star v), h1, h2, h3, h4]
      abel
    rw [Unitary.mem_iff, hsa, hsq1]
    exact ⟨rfl, rfl⟩⟩

@[simp]
theorem coe_reflectionUnitary {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    (hv.reflectionUnitary hpq : A) = 1 - star v * v - v * star v + v + star v := (rfl)

theorem isSelfAdjoint_reflectionUnitary {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    IsSelfAdjoint (hv.reflectionUnitary hpq : A) := by
  have hp := hv.isStarProjection_star_mul_self
  have hq := hv.isStarProjection_mul_star_self
  rw [IsSelfAdjoint, coe_reflectionUnitary]
  simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    star_star]
  abel

theorem reflectionUnitary_conj {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    (hv.reflectionUnitary hpq : A) * (star v * v) * star (hv.reflectionUnitary hpq : A) =
      v * star v := by
  obtain ⟨hqp, hvv, -, -, hvq, -, hsp, hvp, -, -, -⟩ := orth_relations hv hpq
  have hp := hv.isStarProjection_star_mul_self
  rw [(hv.isSelfAdjoint_reflectionUnitary hpq).star_eq, coe_reflectionUnitary]
  have hleft : (1 - star v * v - v * star v + v + star v) * (star v * v) = v := by
    simp only [add_mul, sub_mul, one_mul, hp.isIdempotentElem.eq, hqp, hvp, hsp]
    abel
  rw [hleft]
  simp only [mul_add, mul_sub, mul_one, hvp, hvq, hvv]
  abel

/-- The rotation unitary `1 - p - q + v - star v` conjugating the initial projection
`p = star v * v` of a partial isometry `v` to its orthogonal final projection `q = v * star v`. -/
def rotationUnitary {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) : unitary A :=
  ⟨1 - star v * v - v * star v + v - star v, by
    obtain ⟨hqp, hvv, hss, hpv, hvq, hqs, hsp, hvp, hqv, hps, hsq⟩ := orth_relations hv hpq
    have hp := hv.isStarProjection_star_mul_self
    have hq := hv.isStarProjection_mul_star_self
    set p := star v * v
    set q := v * star v
    have hstar : star (1 - p - q + v - star v) = (1 - p - q) + (star v - v) := by
      simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
        star_star]
      abel
    have h1 : (1 - p - q) * (1 - p - q) = 1 - p - q := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hp.isIdempotentElem.eq,
        hq.isIdempotentElem.eq, hpq, hqp]
      abel
    have h2 : (1 - p - q) * (v - star v) = 0 := by
      simp only [sub_mul, mul_sub, one_mul, hpv, hqv, hps, hqs]
      abel
    have h2' : (1 - p - q) * (star v - v) = 0 := by
      simp only [sub_mul, mul_sub, one_mul, hpv, hqv, hps, hqs]
      abel
    have h3 : (v - star v) * (1 - p - q) = 0 := by
      simp only [sub_mul, mul_sub, mul_one, hvp, hvq, hsp, hsq]
      abel
    have h3' : (star v - v) * (1 - p - q) = 0 := by
      simp only [sub_mul, mul_sub, mul_one, hvp, hvq, hsp, hsq]
      abel
    rw [Unitary.mem_iff, hstar]
    have hval : 1 - p - q + v - star v = (1 - p - q) + (v - star v) := by abel
    rw [hval]
    constructor
    · rw [add_mul, mul_add (1 - p - q), mul_add (star v - v), h1, h2, h3']
      have h4 : (star v - v) * (v - star v) = p + q := by
        simp only [sub_mul, mul_sub, hvv, hss]; abel
      rw [h4]; abel
    · rw [add_mul, mul_add (1 - p - q), mul_add (v - star v), h1, h2', h3]
      have h4 : (v - star v) * (star v - v) = q + p := by
        simp only [sub_mul, mul_sub, hvv, hss]; abel
      rw [h4]; abel⟩

@[simp]
theorem coe_rotationUnitary {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    (hv.rotationUnitary hpq : A) = 1 - star v * v - v * star v + v - star v := (rfl)

theorem rotationUnitary_conj {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) :
    (hv.rotationUnitary hpq : A) * (star v * v) * star (hv.rotationUnitary hpq : A) =
      v * star v := by
  obtain ⟨hqp, hvv, -, -, hvq, -, hsp, hvp, -, -, -⟩ := orth_relations hv hpq
  have hp := hv.isStarProjection_star_mul_self
  have hq := hv.isStarProjection_mul_star_self
  rw [coe_rotationUnitary]
  have hleft : (1 - star v * v - v * star v + v - star v) * (star v * v) = v := by
    simp only [add_mul, sub_mul, one_mul, hp.isIdempotentElem.eq, hqp, hvp, hsp]
    abel
  have hstar : star (1 - star v * v - v * star v + v - star v) =
      1 - star v * v - v * star v + star v - v := by
    simp only [star_add, star_sub, star_one, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
      star_star]
  rw [hleft, hstar]
  simp only [mul_add, mul_sub, mul_one, hvp, hvq, hvv]
  abel

end TauCeti.IsPartialIsometry

end OrthogonalUnitaries
