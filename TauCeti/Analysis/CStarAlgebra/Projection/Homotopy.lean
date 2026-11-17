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

This file develops the homotopy and perturbation theory of projections in (possibly non-unital)
complex C⋆-algebras:

* `IsIdempotentElem.exp_smul` and `Unitary.selfAdjointExpPath`: closed-form exponential of a
  scaled idempotent and explicit path `t ↦ exp (i π t ((1 - w) / 2))` from `1` to a self-adjoint
  unitary `w`.
* `IsIdempotentElem.exists_isStarProjection_mul_eq`, `IsIdempotentElem.similarityUnit`, and
  `IsStarProjection.exists_isPartialIsometry_of_mul_eq`: similarity of idempotents to projections
  and upgrade of algebraic equivalence to Murray–von Neumann equivalence.
* `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one` and
  `IsStarProjection.exists_unitary_conj_of_continuous_path` (with non-unital variants and converse
  paths `Unitary.conjPath`, `Unitary.unitizationConjPath`): unitary conjugation in the identity
  component for nearby projections (`‖u - 1‖ ≤ √2 * ‖p - q‖`) and continuous projection paths.
* `TauCeti.IsPartialIsometry.reflectionUnitary` and `TauCeti.IsPartialIsometry.rotationUnitary`:
  explicit unitaries exchanging orthogonal Murray–von Neumann equivalent projections.

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
  have hpow : ∀ n : ℕ, (c • e) ^ (n + 1) = c ^ (n + 1) • e := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, smul_mul_smul_comm, he.eq, ← pow_succ]
  have hscalar : HasSum (fun n : ℕ => ((n + 1).factorial : 𝕜)⁻¹ • c ^ (n + 1))
      (NormedSpace.exp c - 1) := by
    have h0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) c
    rw [← hasSum_nat_add_iff' 1] at h0; simpa [Finset.sum_range_one] using h0
  have hfull : HasSum (fun n : ℕ => (n.factorial : 𝕜)⁻¹ • (c • e) ^ n)
      (1 + (NormedSpace.exp c - 1) • e) := by
    rw [← hasSum_nat_add_iff' 1]
    simpa [Finset.sum_range_one, add_sub_cancel_left, hpow, smul_smul] using hscalar.smul_const e
  exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (c • e)).unique hfull

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- For a star projection `p`, the exponential unitary `exp (i t p)` equals
`1 + (exp (i t) - 1) • p`. -/
theorem IsStarProjection.coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    (selfAdjoint.expUnitary (t • (⟨p, hp.isSelfAdjoint⟩ : selfAdjoint A)) : A) =
      1 + (Complex.exp (Complex.I * t) - 1) • p := by
  rw [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul, ← Complex.coe_smul t p, smul_smul,
    hp.isIdempotentElem.exp_smul, Complex.exp_eq_exp_ℂ]

/-- For a star projection `p`, the exponential unitary `exp (i π p)` equals `1 - 2 • p`. -/
theorem IsStarProjection.coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (selfAdjoint.expUnitary (Real.pi • (⟨p, hp.isSelfAdjoint⟩ : selfAdjoint A)) : A) =
      1 - (2 : ℂ) • p := by
  rw [hp.coe_expUnitary_smul, mul_comm, Complex.exp_pi_mul_I,
    show ((-1 : ℂ) - 1) = -(2 : ℂ) by norm_num, neg_smul, sub_eq_add_neg]

end IdempotentExp

section SelfAdjointUnitaryPath

namespace Unitary

/-- If `w` is a self-adjoint unitary, then `(1 - w) / 2` is a star projection. -/
theorem isStarProjection_half_one_sub {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
    (w : unitary A) (hw : IsSelfAdjoint (w : A)) :
    IsStarProjection ((2 : ℂ)⁻¹ • (1 - (w : A))) where
  isIdempotentElem := by
    have hww : (w : A) * (w : A) = 1 := by
      nth_rw 1 [← hw.star_eq]; exact Unitary.star_mul_self_of_mem w.property
    have hsq : (1 - (w : A)) * (1 - (w : A)) = (2 : ℂ) • (1 - (w : A)) := by
      simp only [mul_sub, sub_mul, one_mul, mul_one, hww, two_smul]; abel
    rw [IsIdempotentElem, smul_mul_smul_comm, hsq, smul_smul]; congr 1; norm_num
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_smul, star_sub, star_one, hw.star_eq]; congr 1; norm_num

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- Every self-adjoint unitary `w` is realized as `exp (i π ((1 - w) / 2))`. -/
theorem expUnitary_pi_smul_half_one_sub (w : unitary A) (hw : IsSelfAdjoint (w : A)) :
    selfAdjoint.expUnitary
        (Real.pi • (⟨(2 : ℂ)⁻¹ • (1 - (w : A)),
          (isStarProjection_half_one_sub w hw).isSelfAdjoint⟩ : selfAdjoint A)) = w := by
  ext
  rw [(isStarProjection_half_one_sub w hw).coe_expUnitary_pi_smul, smul_smul,
    show (2 : ℂ) * (2 : ℂ)⁻¹ = 1 by norm_num, one_smul, sub_sub_cancel]

/-- The explicit exponential path `t ↦ exp (i π t ((1 - w) / 2))` from `1` to a self-adjoint
unitary `w`. -/
noncomputable def selfAdjointExpPath (w : unitary A) (hw : IsSelfAdjoint (w : A)) :
    Path (1 : unitary A) w where
  toFun t := selfAdjoint.expUnitary (((t : ℝ) * Real.pi) •
    (⟨(2 : ℂ)⁻¹ • (1 - (w : A)),
      (isStarProjection_half_one_sub w hw).isSelfAdjoint⟩ : selfAdjoint A))
  continuous_toFun := selfAdjoint.continuous_expUnitary.comp
    ((continuous_subtype_val.mul continuous_const).smul continuous_const)
  source' := by simp
  target' := by simpa using expUnitary_pi_smul_half_one_sub w hw

@[simp] theorem coe_selfAdjointExpPath (w : unitary A) (hw : IsSelfAdjoint (w : A)) (t : I) :
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
      _ = (u : A) * p * star (u : A) := by
          rw [Unitary.star_mul_self_of_mem u.property, mul_one, mul_assoc (u : A), hp.1.eq]
  isSelfAdjoint := by
    rw [IsSelfAdjoint, star_mul, star_mul, star_star, hp.2.star_eq, mul_assoc]

section ConjPath
variable {A : Type*} [Monoid A] [StarMul A] [TopologicalSpace A] [ContinuousMul A]
  [ContinuousStar A]

/-- A path of unitaries starting at `1` induces a continuous path `t ↦ γ t * a * star (γ t)`
conjugating any element `a`. -/
def Unitary.conjPath (a : A) {u : unitary A} (γ : Path (1 : unitary A) u) :
    Path a ((u : A) * a * star (u : A)) where
  toFun t := (γ t : A) * a * star (γ t : A)
  continuous_toFun := ((continuous_subtype_val.comp γ.continuous).mul continuous_const).mul
    (continuous_star.comp (continuous_subtype_val.comp γ.continuous))
  source' := by simp
  target' := by simp

@[simp] theorem Unitary.conjPath_apply (a : A) {u : unitary A} (γ : Path (1 : unitary A) u)
    (t : I) : Unitary.conjPath a γ t = (γ t : A) * a * star (γ t : A) := (rfl)

theorem IsStarProjection.isStarProjection_conjPath {p : A} (hp : IsStarProjection p)
    {u : unitary A} (γ : Path (1 : unitary A) u) (t : I) :
    IsStarProjection (Unitary.conjPath p γ t) := hp.unitaryConj (γ t)

end ConjPath

section UnitizationConj
variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

/-- Conjugating an element `a : A` by a unitary `u : unitary (Unitization R A)` stays inside the
image of `Unitization.inr`. -/
theorem Unitary.inr_unitizationConj (a : A) (u : unitary (Unitization R A)) :
    ((((u : Unitization R A) * (a : Unitization R A) * star (u : Unitization R A)).snd : A) :
        Unitization R A) =
      (u : Unitization R A) * (a : Unitization R A) * star (u : Unitization R A) :=
  Unitization.ext (by simp [Unitization.fst_mul, Unitization.fst_inr]) rfl

/-- Conjugating a star projection `p : A` by a unitary `u : unitary (Unitization R A)` yields a
star projection in `A`. -/
theorem IsStarProjection.unitizationConj {p : A} (hp : IsStarProjection p)
    (u : unitary (Unitization R A)) :
    IsStarProjection
      (((u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A)).snd) := by
  have hp' : IsStarProjection (p : Unitization R A) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom R A)
  have hconj := hp'.unitaryConj u
  rw [← Unitary.inr_unitizationConj p u] at hconj
  exact ⟨Unitization.inr_injective (R := R) (by simpa [Unitization.inr_mul] using hconj.1.eq),
    Unitization.inr_injective (R := R) (by simpa [Unitization.inr_star] using hconj.2.star_eq)⟩

/-- If two star projections in a non-unital star algebra `A` are conjugate by a unitary in
`Unitization R A`, then they are Murray–von Neumann equivalent via a partial isometry in `A`. -/
theorem IsStarProjection.exists_isPartialIsometry_of_unitization_unitary_conj
    {p q : A} (hp : IsStarProjection p) {u : unitary (Unitization R A)}
    (hconj : (u : Unitization R A) * (p : Unitization R A) * star (u : Unitization R A) =
      (q : Unitization R A)) :
    ∃ v : A, TauCeti.IsPartialIsometry v ∧ star v * v = p ∧ v * star v = q := by
  let v' : Unitization R A := (u : Unitization R A) * (p : Unitization R A)
  have hv'_eq : (v'.snd : Unitization R A) = v' :=
    Unitization.ext (by simp [v', Unitization.fst_mul, Unitization.fst_inr]) rfl
  have hp' : IsStarProjection (p : Unitization R A) :=
    hp.map (Unitization.inrNonUnitalStarAlgHom R A)
  have hsv : star v'.snd * v'.snd = p := Unitization.inr_injective (R := R) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hv'_eq]
    dsimp only [v']
    rw [star_mul, hp'.2.star_eq, mul_assoc, ← mul_assoc (star (u : Unitization R A)),
      Unitary.star_mul_self_of_mem u.property, one_mul, hp'.1.eq]
  have hvs : v'.snd * star v'.snd = q := Unitization.inr_injective (R := R) <| by
    rw [Unitization.inr_mul, Unitization.inr_star, hv'_eq]
    dsimp only [v']
    rw [star_mul, hp'.2.star_eq, ← mul_assoc, mul_assoc (u : Unitization R A), hp'.1.eq, hconj]
  refine ⟨v'.snd, TauCeti.isPartialIsometry_iff.mpr <| Unitization.inr_injective (R := R) ?_,
    hsv, hvs⟩
  rw [Unitization.inr_mul, Unitization.inr_mul, Unitization.inr_star, mul_assoc,
    ← Unitization.inr_star, ← Unitization.inr_mul, hsv, hv'_eq]
  dsimp only [v']; rw [mul_assoc, hp'.1.eq]

end UnitizationConj

section UnitizationConjPath
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A path of unitaries in `A⁺¹` starting at `1` induces a norm-continuous path inside `A` via
`t ↦ ((γ t) * a * star (γ t)).snd`. -/
def Unitary.unitizationConjPath (a : A) {u : unitary A⁺¹} (γ : Path (1 : unitary A⁺¹) u) :
    Path a (((u : A⁺¹) * (a : A⁺¹) * star (u : A⁺¹)).snd) where
  toFun t := ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd
  continuous_toFun := by
    rw [(Unitization.isometry_inr (𝕜 := ℂ) (A := A)).isEmbedding.continuous_iff]
    rw [show Unitization.inr ∘ (fun t : I => ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd) =
        fun t : I => (γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹) from
      funext fun t => Unitary.inr_unitizationConj a (γ t)]
    exact ((continuous_subtype_val.comp γ.continuous).mul continuous_const).mul
      (continuous_star.comp (continuous_subtype_val.comp γ.continuous))
  source' := by simp
  target' := by simp

@[simp] theorem Unitary.unitizationConjPath_apply (a : A) {u : unitary A⁺¹}
    (γ : Path (1 : unitary A⁺¹) u) (t : I) :
    Unitary.unitizationConjPath a γ t =
      ((γ t : A⁺¹) * (a : A⁺¹) * star (γ t : A⁺¹)).snd := (rfl)

theorem IsStarProjection.isStarProjection_unitizationConjPath {p : A} (hp : IsStarProjection p)
    {u : unitary A⁺¹} (γ : Path (1 : unitary A⁺¹) u) (t : I) :
    IsStarProjection (Unitary.unitizationConjPath p γ t) := hp.unitizationConj (γ t)

end UnitizationConjPath

end UnitaryConjugation

section IdempotentToProjection

section SimilarityUnit
variable {A : Type*} [Ring A] {e p : A} (he : IsIdempotentElem e) (hp : IsIdempotentElem p)
  (hep : e * p = p) (hpe : p * e = e)

/-- If `e` and `p` are idempotents in a ring with `e * p = p` and `p * e = e`, then
`1 - (p - e)` is an invertible element with inverse `1 + (p - e)` conjugating `e` to `p`. -/
def IsIdempotentElem.similarityUnit : Aˣ where
  val := 1 - (p - e)
  inv := 1 + (p - e)
  val_inv := by
    simp only [mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq, he.eq, hep, hpe]; abel
  inv_val := by
    simp only [mul_sub, add_mul, sub_mul, one_mul, mul_one, hp.eq, he.eq, hep, hpe]; abel

@[simp] theorem IsIdempotentElem.coe_similarityUnit :
    (he.similarityUnit hp hep hpe : A) = 1 - (p - e) := (rfl)
@[simp] theorem IsIdempotentElem.coe_similarityUnit_inv :
    (↑(he.similarityUnit hp hep hpe)⁻¹ : A) = 1 + (p - e) := (rfl)

theorem IsIdempotentElem.similarityUnit_conj :
    (he.similarityUnit hp hep hpe : A) * e * (↑(he.similarityUnit hp hep hpe)⁻¹ : A) = p := by
  simp only [coe_similarityUnit, coe_similarityUnit_inv, sub_mul, one_mul, hpe, he.eq,
    sub_sub_cancel, mul_add, mul_one, mul_sub, hep]; abel

end SimilarityUnit

private theorem IsIdempotentElem.exists_isStarProjection_mul_eq_unital {A : Type*}
    [CStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let z : A := 1 + Star.star (e - Star.star e) * (e - Star.star e)
  obtain ⟨zu, hzu⟩ := CStarAlgebra.isUnit_of_le (1 : A)
    (le_add_of_nonneg_right (star_mul_self_nonneg (e - Star.star e)))
  let zinv : A := (zu⁻¹ : Aˣ)
  have hmul_right : z * zinv = 1 := by dsimp only [z]; rw [← hzu]; exact zu.mul_inv
  have hzinv_sa : IsSelfAdjoint zinv :=
    ((IsSelfAdjoint.one (R := A)).add (IsSelfAdjoint.star_mul_self _)).of_mul_eq_one hmul_right
  have hz_expand : z = 1 + Star.star e * e - Star.star e - e + e * Star.star e := by
    have hse : Star.star e * Star.star e = Star.star e := by rw [← star_mul, he.eq]
    dsimp only [z]; rw [star_sub, star_star, sub_mul, mul_sub, mul_sub, hse, he.eq]; abel
  have hez : e * z = e * Star.star e * e := by
    rw [hz_expand]; simp only [mul_add, mul_sub, mul_one, ← mul_assoc, he.eq]; abel
  have hze : z * e = e * Star.star e * e := by
    rw [hz_expand]; simp only [add_mul, sub_mul, one_mul, mul_assoc, he.eq]; abel
  have hcomm_e : Commute e zinv :=
    (show Commute e (zu : A) by rw [hzu, Commute, SemiconjBy, hez, hze]).units_inv_right
  have hcomm_se : Commute (Star.star e) zinv := by
    simpa [Commute, SemiconjBy, star_mul, hzinv_sa.star_eq] using
      (congr_arg Star.star hcomm_e.eq).symm
  have hpe : (e * Star.star e * zinv) * e = e := by
    rw [mul_assoc, ← hcomm_e.eq, ← mul_assoc, ← hez, mul_assoc, hmul_right, mul_one]
  refine ⟨e * Star.star e * zinv, ⟨?_, ?_⟩, by rw [← mul_assoc, ← mul_assoc, he.eq], hpe⟩
  · rw [IsIdempotentElem, ← mul_assoc _ (e * Star.star e), ← mul_assoc _ e, hpe]
  · rw [IsSelfAdjoint, star_mul, star_mul, star_star, hzinv_sa.star_eq,
      ← mul_assoc zinv e, ← hcomm_e.eq, mul_assoc, ← hcomm_se.eq, ← mul_assoc]

/-- Every idempotent in a (possibly non-unital) C⋆-algebra has an associated star projection `p`
with `e * p = p` and `p * e = e` (Blackadar, Proposition 4.6.2). When `A` is unital, `e` is
similar to `p` via `IsIdempotentElem.similarityUnit`. -/
theorem IsIdempotentElem.exists_isStarProjection_mul_eq {A : Type*}
    [NonUnitalCStarAlgebra A] {e : A} (he : IsIdempotentElem e) :
    ∃ p : A, IsStarProjection p ∧ e * p = p ∧ p * e = e := by
  obtain ⟨p', hp', hep', hp'e⟩ :=
    (show IsIdempotentElem (e : A⁺¹) by rw [IsIdempotentElem, ← Unitization.inr_mul, he.eq])
      |>.exists_isStarProjection_mul_eq_unital
  have hp'_eq : (p'.snd : A⁺¹) = p' := Unitization.ext (by
    simpa [Unitization.fst_mul, Unitization.fst_inr] using
      congr_arg (fun x : A⁺¹ => x.fst) hep') rfl
  exact ⟨p'.snd,
    ⟨Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hp'_eq]; exact hp'.1.eq),
     Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_star, hp'_eq]; exact hp'.2)⟩,
    Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hp'_eq, hep']),
    Unitization.inr_injective (R := ℂ) (by rw [Unitization.inr_mul, hp'_eq, hp'e])⟩

end IdempotentToProjection

section AlgebraicEquivalence

/-- Spectral inverse square root identities for a self-adjoint element with strictly positive
real spectrum. -/
private theorem cfc_inv_sqrt_spec {A : Type*} [CStarAlgebra A]
    {b : A} (hb : IsSelfAdjoint b) (hb_pos : ∀ t ∈ spectrum ℝ b, 0 < t) :
    let r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
    IsSelfAdjoint r ∧ b * (r * r) = 1 ∧ (r * r) * b = 1 ∧ b * r = cfc Real.sqrt b := by
  intro r
  have hf : ContinuousOn (fun t : ℝ => (Real.sqrt t)⁻¹) (spectrum ℝ b) :=
    ContinuousOn.inv₀ Real.continuous_sqrt.continuousOn fun t ht =>
      (Real.sqrt_pos.mpr (hb_pos t ht)).ne'
  have hrr : r * r = cfc (fun t : ℝ => t⁻¹) b := by
    rw [← cfc_mul (hf := hf) (hg := hf)]
    exact cfc_congr fun t ht => by rw [← mul_inv, Real.mul_self_sqrt (hb_pos t ht).le]
  have hb_rr : b * (r * r) = 1 := by
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (spectrum ℝ b) :=
      ContinuousOn.inv₀ continuousOn_id fun t ht => (hb_pos t ht).ne'
    nth_rw 1 [← cfc_id ℝ b]; rw [hrr, ← cfc_mul (hf := continuousOn_id) (hg := hinv)]
    exact (cfc_congr fun t ht => mul_inv_cancel₀ (hb_pos t ht).ne').trans
      (by rw [cfc_const (1 : ℝ) b, map_one])
  have hcomm : Commute r b := (Commute.refl b).cfc_real _
  refine ⟨cfc_predicate _ b, hb_rr, by rw [(hcomm.mul_left hcomm).eq, hb_rr], ?_⟩
  nth_rw 1 [← cfc_id ℝ b]; rw [← cfc_mul (hf := continuousOn_id) (hg := hf)]
  refine cfc_congr fun t ht => ?_
  nth_rw 1 [← Real.mul_self_sqrt (hb_pos t ht).le]
  rw [id_eq, mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hb_pos t ht)).ne', mul_one]

private theorem IsStarProjection.exists_mul_cfc_of_mul_eq_unital {A : Type*} [CStarAlgebra A]
    {p q x y : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hxy : x * y = p) (hyx : y * x = q)
    (hpx : p * x = x) (hqy : q * y = y) (hyp : y * p = y) :
    ∃ r : A, star (y * r) * (y * r) = p ∧ (y * r) * star (y * r) = q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  have _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hpsy : p * star y = star y := by
    simpa only [star_mul, hp.2.star_eq] using congr_arg star hyp
  let a : A := star y * y
  let b : A := a + (1 - p)
  have ha_nonneg : 0 ≤ a := star_mul_self_nonneg y
  have hb_sa : IsSelfAdjoint b := IsSelfAdjoint.of_nonneg (add_nonneg ha_nonneg hp.one_sub.nonneg)
  let M : ℝ := ‖star x * x‖ + 1
  have hM_pos : 0 < M := by positivity
  have hP_le_Ma : p ≤ M • a := by
    have hp_eq : p = star y * (star x * x) * y := by
      calc p = star (x * y) * (x * y) := by rw [hxy, hp.2.star_eq, hp.1.eq]
        _ = star y * (star x * x) * y := by simp only [star_mul, mul_assoc]
    exact hp_eq.le.trans <|
      (CStarAlgebra.star_left_conjugate_le_norm_smul y (star x * x) (.star_mul_self x)).trans
        (smul_le_smul_of_nonneg_right (by linarith) ha_nonneg)
  have hMinv_le_b : algebraMap ℝ A M⁻¹ ≤ b := by
    rw [Algebra.algebraMap_eq_smul_one, ← add_sub_cancel p 1, smul_add]
    refine add_le_add ?_ ?_
    · simpa only [inv_smul_smul₀ hM_pos.ne'] using
        smul_le_smul_of_nonneg_left hP_le_Ma (inv_pos.mpr hM_pos).le
    · simpa only [one_smul] using smul_le_smul_of_nonneg_right
        (inv_le_one_of_one_le₀ (le_add_of_nonneg_left (norm_nonneg _))) hp.one_sub.nonneg
  have hb_pos : ∀ t ∈ spectrum ℝ b, 0 < t := fun t ht =>
    (inv_pos.mpr hM_pos).trans_le ((algebraMap_le_iff_le_spectrum hb_sa).mp hMinv_le_b t ht)
  obtain ⟨hr_sa, hb_rr, hrr_b, -⟩ := cfc_inv_sqrt_spec hb_sa hb_pos
  set r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
  have hbp : b * p = a := by
    dsimp only [b, a]; rw [add_mul, mul_assoc, hyp, hp.one_sub_mul_self, add_zero]
  have hpb : p * b = a := by
    dsimp only [b, a]; rw [mul_add, ← mul_assoc, hpsy, hp.mul_one_sub_self, add_zero]
  have hcomm_rp : Commute r p := (show Commute b p by rw [Commute, SemiconjBy, hbp, hpb]).cfc_real _
  have hcomm_rb : Commute r b := (Commute.refl b).cfc_real _
  refine ⟨r, ?_, ?_⟩
  · calc star (y * r) * (y * r) = r * a * r := by simp only [a, star_mul, hr_sa.star_eq, mul_assoc]
      _ = (b * (r * r)) * p := by
          rw [← hbp, ← mul_assoc r b p, mul_assoc (r * b), ← hcomm_rp.eq, ← mul_assoc, hcomm_rb.eq]
          simp only [mul_assoc]
      _ = p := by rw [hb_rr, one_mul]
  · have h2 : ((y * r) * star (y * r)) * q = (y * r) * star (y * r) := by
      have h1 : q * ((y * r) * star (y * r)) = (y * r) * star (y * r) := by
        rw [← mul_assoc, ← mul_assoc, hqy]
      simpa only [star_mul, star_star, hq.2.star_eq] using congr_arg star h1
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
    calc p * x * q * (q * y * p) = p * x * (q * q) * y * p := by simp only [mul_assoc]
      _ = p * (x * y) * (x * y) * p := by rw [hq.1.eq, ← hyx]; simp only [mul_assoc]
      _ = p := by rw [hxy]; simp only [hp.1.eq]
  have hy'x' : y' * x' = q := by
    calc q * y * p * (p * x * q) = q * y * (p * p) * x * q := by simp only [mul_assoc]
      _ = q * (y * x) * (y * x) * q := by rw [hp.1.eq, ← hxy]; simp only [mul_assoc]
      _ = q := by rw [hyx]; simp only [hq.1.eq]
  have hP : IsStarProjection (p : A⁺¹) := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hQ : IsStarProjection (q : A⁺¹) := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨r, hsV_V, hV_sV⟩ := hP.exists_mul_cfc_of_mul_eq_unital hQ
    (by rw [← Unitization.inr_mul, hx'y']) (by rw [← Unitization.inr_mul, hy'x'])
    (by rw [← Unitization.inr_mul]; dsimp only [x']; rw [← mul_assoc, ← mul_assoc, hp.1.eq])
    (by rw [← Unitization.inr_mul]; dsimp only [y']; rw [← mul_assoc, ← mul_assoc, hq.1.eq])
    (by rw [← Unitization.inr_mul]; dsimp only [y']; rw [mul_assoc, hp.1.eq])
  let V : A⁺¹ := (y' : A⁺¹) * r
  have hv_eq : (V.snd : A⁺¹) = V := Unitization.ext (by simp [V]) rfl
  have hvp : star V.snd * V.snd = p := Unitization.inr_injective (R := ℂ)
    (by rw [Unitization.inr_mul, Unitization.inr_star, hv_eq, hsV_V])
  have hvq : V.snd * star V.snd = q := Unitization.inr_injective (R := ℂ)
    (by rw [Unitization.inr_mul, Unitization.inr_star, hv_eq, hV_sV])
  exact ⟨V.snd, TauCeti.isPartialIsometry_iff_isStarProjection_star_mul_self.mpr (hvp ▸ hp),
    hvp, hvq⟩

end AlgebraicEquivalence

section NearbyProjections

/-- Purely algebraic identities for `z = q * p + (1 - q) * (1 - p)` and `b = 1 - (p - q) ^ 2`. -/
private theorem nearby_proj_algebra {A : Type*} [Ring A] [StarRing A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    let z : A := q * p + (1 - q) * (1 - p)
    let b : A := 1 - (p - q) * (p - q)
    z * p = q * p ∧ q * z = q * p ∧ star z * z = b ∧ z * star z = b ∧
      z + star z = b + b ∧ Commute b z ∧ Commute b p := by
  intro z b
  have hzp : z * p = q * p := by
    dsimp only [z]
    rw [add_mul, mul_assoc, hp.1.eq, mul_assoc, hp.one_sub_mul_self, mul_zero, add_zero]
  have hqz : q * z = q * p := by
    dsimp only [z]
    rw [mul_add, ← mul_assoc, hq.1.eq, ← mul_assoc, hq.mul_one_sub_self, zero_mul, add_zero]
  have hsz : star z = p * q + (1 - p) * (1 - q) := by
    dsimp only [z]
    rw [star_add, star_mul, star_mul, star_sub, star_sub, star_one, hp.2.star_eq, hq.2.star_eq]
  have hmul : ∀ {r s : A}, IsStarProjection r → IsStarProjection s →
      (r * s + (1 - r) * (1 - s)) * (s * r + (1 - s) * (1 - r)) = 1 - (r - s) * (r - s) := by
    intro r s hr hs
    have hs2 : ∀ x, s * (s * x) = s * x := fun x => by rw [← mul_assoc, hs.1.eq]
    simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_assoc,
      hr.1.eq, hs.1.eq, hs2]; abel
  have hsz_z : star z * z = b := by rw [hsz]; exact hmul hp hq
  have hz_sz : z * star z = b := by
    rw [hsz]
    simpa only [b, show (q - p) * (q - p) = (p - q) * (p - q) by simp only [sub_mul, mul_sub]; abel]
      using hmul hq hp
  refine ⟨hzp, hqz, hsz_z, hz_sz,
    by rw [hsz]; dsimp only [z, b]; simp only [sub_mul, mul_sub, one_mul, mul_one,
        hp.1.eq, hq.1.eq]; abel,
    by rw [Commute, SemiconjBy]; calc b * z = z * star z * z := by rw [hz_sz]
        _ = z * b := by rw [mul_assoc, hsz_z],
    (Commute.one_left p).sub_left <| by
      rw [Commute, SemiconjBy]; simp only [sub_mul, mul_sub, ← mul_assoc, hp.1.eq, hq.1.eq]
      simp only [mul_assoc, hp.1.eq]; abel⟩

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
  have hsub_sa : IsSelfAdjoint (p - q) := hp.2.sub hq.2
  have hd_nonneg : 0 ≤ d := by simpa only [d, hsub_sa.star_eq] using star_mul_self_nonneg (p - q)
  have hb_sa : IsSelfAdjoint b := (IsSelfAdjoint.one (R := A)).sub (.of_nonneg hd_nonneg)
  have hd_norm : ‖d‖ = ‖p - q‖ ^ 2 := by
    rw [show d = star (p - q) * (p - q) by rw [hsub_sa.star_eq], CStarRing.norm_star_mul_self, sq]
  have hd_le : d ≤ algebraMap ℝ A (‖p - q‖ ^ 2) :=
    (le_algebraMap_iff_spectrum_le (.of_nonneg hd_nonneg)).mpr fun t ht => (le_abs_self t).trans <|
      by simpa [Real.norm_eq_abs, hd_norm] using spectrum.norm_le_norm_of_mem ht
  have hb_spec : ∀ s ∈ spectrum ℝ b, 1 - ‖p - q‖ ^ 2 ≤ s ∧ s ≤ 1 := fun s hs =>
    ⟨(algebraMap_le_iff_le_spectrum hb_sa).mp
        (by rw [map_sub, map_one]; exact sub_le_sub_left hd_le 1) s hs,
      (le_algebraMap_iff_spectrum_le hb_sa).mp
        (by rw [map_one]; exact sub_le_self 1 hd_nonneg) s hs⟩
  have hb_pos : ∀ s ∈ spectrum ℝ b, 0 < s := fun s hs => by
    nlinarith [norm_nonneg (p - q), (hb_spec s hs).1]
  obtain ⟨hr_sa, hb_rr, -, hb_r⟩ := cfc_inv_sqrt_spec hb_sa hb_pos
  set r : A := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) b
  have hcomm_rz : Commute r z := hcomm_bz.cfc_real _
  have hcomm_rp : Commute r p := hcomm_bp.cfc_real _
  have hcomm_rb : Commute r b := (Commute.refl b).cfc_real _
  have hcomm_rsz : Commute r (star z) := by
    simpa only [Commute, SemiconjBy, star_mul, hr_sa.star_eq] using
      (congr_arg star hcomm_rz.eq).symm
  let u : unitary A := ⟨z * r, Unitary.mem_iff.mpr ⟨by
    calc star (z * r) * (z * r) = r * b * r := by
          dsimp only [b, d, z]; rw [← hsz_z]; simp only [star_mul, hr_sa.star_eq, mul_assoc]
      _ = 1 := by rw [hcomm_rb.eq, mul_assoc, hb_rr], by
    calc (z * r) * star (z * r) = z * (r * r) * star z := by
          simp only [star_mul, hr_sa.star_eq, mul_assoc]
      _ = 1 := by
          rw [mul_assoc z (r * r), (hcomm_rsz.mul_left hcomm_rsz).eq, ← mul_assoc, hz_sz, hb_rr]⟩⟩
  have hu_conj : (u : A) * p * star (u : A) = q := by
    dsimp only [u]
    calc z * r * p * star (z * r) = (z * p) * ((r * r) * star z) := by
          rw [star_mul, hr_sa.star_eq, mul_assoc z r p, hcomm_rp.eq]; simp only [mul_assoc]
      _ = q * (b * (r * r)) := by
          rw [hzp, ← hqz, (hcomm_rsz.mul_left hcomm_rsz).eq]
          dsimp only [b, d, z]; rw [← hz_sz]; simp only [mul_assoc]
      _ = q := by rw [hb_rr, mul_one]
  have hu_sub_sq : star ((u : A) - 1) * ((u : A) - 1) =
      cfc (fun s : ℝ => 2 * (1 - Real.sqrt s)) b := by
    have hu_add : (u : A) + star (u : A) = (2 : ℝ) • cfc Real.sqrt b := by
      dsimp only [u]
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
      have hle_sqrt : s ≤ Real.sqrt s :=
        (Real.sqrt_sq hs0).symm.trans_le (Real.sqrt_le_sqrt (by nlinarith))
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
    nlinarith [norm_nonneg ((u : A) - 1), show 0 ≤ √2 * ‖p - q‖ by positivity]
  refine ⟨u, hu_conj, hnorm_bound, Unitary.joined 1 u ?_⟩
  rw [Submonoid.coe_one]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- Non-unital version of `IsStarProjection.exists_unitary_conj_of_norm_sub_lt_one` via `A⁺¹`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_norm_sub_lt_one {A : Type*}
    [NonUnitalCStarAlgebra A] {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hnorm : ‖p - q‖ < 1) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (p : A⁺¹) * star (u : A⁺¹) = (q : A⁺¹) ∧
      ‖(u : A⁺¹) - 1‖ ≤ √2 * ‖p - q‖ ∧ Joined (1 : unitary A⁺¹) u := by
  have hp' : IsStarProjection (p : A⁺¹) := hp.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hq' : IsStarProjection (q : A⁺¹) := hq.map (Unitization.inrNonUnitalStarAlgHom ℂ A)
  obtain ⟨u, hconj, hbd, hjoin⟩ := hp'.exists_unitary_conj_of_norm_sub_lt_one hq'
    (by rwa [← Unitization.inr_sub, Unitization.norm_inr])
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
  obtain ⟨δ, hδ, hdist⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hγ) 1 one_pos
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  let M : ℕ := N + 1
  let pt : ∀ k : ℕ, k ≤ M → I := fun k hk =>
    ⟨(k : ℝ) / (M : ℝ), by positivity, (div_le_one (by positivity)).mpr (by exact_mod_cast hk)⟩
  have hstep : ∀ k : ℕ, (hk : k ≤ M) →
      ∃ u : unitary A, (u : A) * γ 0 * star (u : A) = γ (pt k hk) ∧ Joined (1 : unitary A) u := by
    intro k; induction k with
    | zero =>
      intro hk; exact ⟨1, by simp [show pt 0 hk = 0 from Subtype.ext (by simp [pt])], Joined.refl 1⟩
    | succ k ih =>
      intro hk
      obtain ⟨u, hu_conj, hu_join⟩ := ih (Nat.le_of_succ_le hk)
      have hdiff_lt : ‖γ (pt k (Nat.le_of_succ_le hk)) - γ (pt (k + 1) hk)‖ < 1 := by
        rw [← dist_eq_norm]; apply hdist
        rw [Subtype.dist_eq, Real.dist_eq,
          show ((k : ℝ) / (M : ℝ)) - (((k + 1 : ℕ) : ℝ) / (M : ℝ)) = -(1 / (M : ℝ)) by
            push_cast; ring, abs_neg, abs_of_pos (by positivity)]
        simpa [M] using hN
      obtain ⟨v, hv_conj, -, hv_join⟩ :=
        (hproj _).exists_unitary_conj_of_norm_sub_lt_one (hproj _) hdiff_lt
      refine ⟨v * u, ?_, by simpa using hv_join.mul hu_join⟩
      rw [Submonoid.coe_mul, star_mul, mul_assoc (v : A), mul_assoc (v : A),
        ← mul_assoc ((u : A) * γ 0), hu_conj, ← mul_assoc, hv_conj]
  obtain ⟨u, hu_conj, hu_join⟩ := hstep M le_rfl
  exact ⟨u, (show pt M le_rfl = 1 from Subtype.ext (by simp [pt])) ▸ hu_conj, hu_join⟩

/-- Non-unital version of `IsStarProjection.exists_unitary_conj_of_continuous_path` via `A⁺¹`. -/
theorem IsStarProjection.exists_unitization_unitary_conj_of_continuous_path {A : Type*}
    [NonUnitalCStarAlgebra A] {γ : I → A} (hγ : Continuous γ)
    (hproj : ∀ t : I, IsStarProjection (γ t)) :
    ∃ u : unitary A⁺¹, (u : A⁺¹) * (γ 0 : A⁺¹) * star (u : A⁺¹) = (γ 1 : A⁺¹) ∧
      Joined (1 : unitary A⁺¹) u :=
  IsStarProjection.exists_unitary_conj_of_continuous_path (γ := fun t => (γ t : A⁺¹))
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

private theorem orth_unitary_spec {v : A} (hv : TauCeti.IsPartialIsometry v)
    (hpq : (star v * v) * (v * star v) = 0) (ε : ℤˣ) :
    let w : A := 1 - star v * v - v * star v + v + (ε : ℤ) • star v
    w ∈ unitary A ∧ w * (star v * v) * star w = v * star v := by
  intro w; set p := star v * v; set q := v * star v
  have hp : IsStarProjection p := hv.isStarProjection_star_mul_self
  have hq : IsStarProjection q := hv.isStarProjection_mul_star_self
  have hqp : q * p = 0 := by simpa [p, q, star_mul, mul_assoc] using congr_arg star hpq
  have hvp : v * p = v := by rw [← mul_assoc, hv.mul_star_mul_self]
  have hqv : q * v = v := hv.mul_star_mul_self
  have hps : p * star v = star v := by simpa [p, star_mul, mul_assoc] using congr_arg star hvp
  have hsq : star v * q = star v := by simpa [q, star_mul, mul_assoc] using congr_arg star hqv
  have hvv : v * v = 0 := by
    calc v * v = (v * p) * (q * v) := by rw [hvp, hqv]
      _ = v * (p * q) * v := by simp only [mul_assoc]
      _ = 0 := by rw [hpq, mul_zero, zero_mul]
  have hss : star v * star v = 0 := by simpa [star_mul] using congr_arg star hvv
  have hpv : p * v = 0 := by rw [mul_assoc, hvv, mul_zero]
  have hvq : v * q = 0 := by rw [← mul_assoc, hvv, zero_mul]
  have hqs : q * star v = 0 := by rw [mul_assoc, hss, mul_zero]
  have hsp : star v * p = 0 := by rw [← mul_assoc, hss, zero_mul]
  have hε : ∀ x : A, (ε : ℤ) • (ε : ℤ) • x = x := fun x => by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hstar : star w = 1 - p - q + star v + (ε : ℤ) • v := by
    simp only [w, star_add, star_sub, star_one, star_zsmul, hp.2.star_eq, hq.2.star_eq, star_star,
      p, q]
  refine ⟨Unitary.mem_iff.mpr ?_, ?_⟩
  · constructor <;>
    · rw [hstar]; dsimp only [w]
      simp only [add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, mul_smul_comm,
        smul_mul_assoc, hp.1.eq, hq.1.eq, hpq, hqp, hvp, hqv, hps, hsq, hvv, hss, hpv, hvq, hqs,
        hsp, smul_add, smul_sub, smul_zero, hε, p, q]; abel
  · have hwp : w * p = v := by
      simp only [w, add_mul, sub_mul, one_mul, smul_mul_assoc, hp.1.eq, hqp, hvp, hsp, smul_zero,
        p, q]; abel
    rw [hwp, hstar]
    simp only [mul_add, mul_sub, mul_one, mul_smul_comm, hvp, hvq, hvv, smul_zero, p, q]; abel

variable {v : A} (hv : TauCeti.IsPartialIsometry v) (hpq : (star v * v) * (v * star v) = 0)

/-- The self-adjoint reflection unitary `1 - p - q + v + star v` exchanging orthogonal initial
and final projections `p = star v * v` and `q = v * star v` of a partial isometry `v`. -/
def reflectionUnitary : unitary A :=
  ⟨1 - star v * v - v * star v + v + star v, by simpa using (orth_unitary_spec hv hpq 1).1⟩

@[simp] theorem coe_reflectionUnitary :
    (hv.reflectionUnitary hpq : A) = 1 - star v * v - v * star v + v + star v := (rfl)

theorem isSelfAdjoint_reflectionUnitary : IsSelfAdjoint (hv.reflectionUnitary hpq : A) := by
  rw [IsSelfAdjoint, coe_reflectionUnitary]
  simp only [star_add, star_sub, star_one, hv.isStarProjection_star_mul_self.2.star_eq,
    hv.isStarProjection_mul_star_self.2.star_eq, star_star]; abel

theorem reflectionUnitary_conj :
    (hv.reflectionUnitary hpq : A) * (star v * v) * star (hv.reflectionUnitary hpq : A) =
      v * star v := by simpa using (orth_unitary_spec hv hpq 1).2

/-- The rotation unitary `1 - p - q + v - star v` conjugating the initial projection
`p = star v * v` of a partial isometry `v` to its orthogonal final projection `q = v * star v`. -/
def rotationUnitary : unitary A :=
  ⟨1 - star v * v - v * star v + v - star v, by
    simpa [sub_eq_add_neg] using (orth_unitary_spec hv hpq (-1)).1⟩

@[simp] theorem coe_rotationUnitary :
    (hv.rotationUnitary hpq : A) = 1 - star v * v - v * star v + v - star v := (rfl)

theorem rotationUnitary_conj :
    (hv.rotationUnitary hpq : A) * (star v * v) * star (hv.rotationUnitary hpq : A) =
      v * star v := by simpa [sub_eq_add_neg] using (orth_unitary_spec hv hpq (-1)).2

end TauCeti.IsPartialIsometry

end OrthogonalUnitaries
