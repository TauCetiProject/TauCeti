/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star

/-!
# The sign isomorphism and positivity at negative loop parameters

Over every commutative ring `R`, the assignment `e i ↦ -e i` respects the Temperley–Lieb relations
when the loop value changes sign: `(-e i) * (-e i) = e i * e i`, so the quadratic relation
`e i * e i = δ • e i` at `δ` becomes the quadratic relation at `-δ`, while the zig-zag relation has
an odd number of factors on each side and the commutation relation an even number. This gives the
**sign isomorphism** `TL_n(δ) ≃ₐ[R] TL_n(-δ)`, `TauCeti.TemperleyLieb.signEquiv`, whose inverse is
the same construction in the other direction.

The sign isomorphism commutes with the strand inclusions and with the augmentation, and for a
self-adjoint loop value it preserves the analytic adjoint, since it sends each generator to a
self-adjoint element. It intertwines Markov traces up to the sign `(-1) ^ n`: if `tr` and `tr'`
are Markov traces at `δ` and `-δ`, then `tr' n (s x) = (-1) ^ n * tr n x`. Indeed the family
`x ↦ (-1) ^ n * tr' n (s x)` is again a Markov trace at `δ` (the sign `(-1) ^ n` compensates
`(-δ) ^ n = (-1) ^ n * δ ^ n` on the identity, the factor `-δ` under strand inclusion, and the sign
of the last generator in the Markov property), so it is `tr` by uniqueness of the Markov trace. In
particular the normalised traces `(δ ^ n)⁻¹ * tr n` correspond exactly, and the trace radicals and
their quotients correspond, compatibly with the strand maps.

Combined with Jones's positivity theorem at the positive loop value `-δ`, this classifies the
negative loop values with positive signed closure forms: for real `δ < 0`, the forms
`(-1) ^ n * tr n (x⋆ * x)` are real and nonnegative on every number of strands exactly when `-δ`
is an admissible loop parameter, `-δ = 2 cos (π / m)` for some `m ≥ 3` or `-δ ≥ 2`. The sign
`(-1) ^ n` cannot be dropped: on one strand the unsigned form is `tr 1 1 = δ < 0`.

## Main definitions

* `TauCeti.TemperleyLieb.signEquiv`: the sign isomorphism `TL_n(δ) ≃ₐ[R] TL_n(δ')` for
  `δ' = -δ`, sending `e i` to `-e i`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientSignEquiv`: the induced isomorphism of the
  quotients by the trace radicals.

## Main results

* `TauCeti.TemperleyLieb.strandIncl_signEquiv`: the sign isomorphism commutes with the strand
  inclusions.
* `TauCeti.TemperleyLieb.signEquiv_star`: for self-adjoint loop values it is a star isomorphism.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_signEquiv`,
  `TauCeti.TemperleyLieb.markovTrace_signEquiv`: the trace relation
  `tr' n (s x) = (-1) ^ n * tr n x`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.inv_pow_mul_map_signEquiv`: the normalised traces
  correspond.
* `TauCeti.TemperleyLieb.IsMarkovTrace.comap_traceRadical_signEquiv`: the trace radicals
  correspond.
* `TauCeti.TemperleyLieb.IsMarkovTrace.forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff`,
  `TauCeti.TemperleyLieb.markovTrace_neg_one_pow_nonneg_iff`: **positivity at negative loop
  parameters**.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Facts 4.4.14, for the signed
  closure forms at negative loop values.
* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {δ δ' : R} {n : ℕ}

/-- The algebra map sending each generator to its negative, from the loop value `δ` to the loop
value `δ' = -δ`. -/
private def signHom (h : δ' = -δ) : TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by rw [neg_mul_neg, e_mul_self, h, neg_smul, smul_neg])
    (fun hij ↦ by rw [neg_mul_neg, mul_neg, e_mul_e_mul_e hij])
    (fun hij ↦ by rw [neg_mul_neg, neg_mul_neg, (commute_e hij).eq])

private theorem signHom_e (h : δ' = -δ) (i : Fin (n - 1)) : signHom h (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

/-- The **sign isomorphism** between the Temperley–Lieb algebras at the loop values `δ` and
`δ' = -δ`, sending each generator `e i` to `-e i`. -/
def signEquiv (h : δ' = -δ) : TemperleyLieb R δ n ≃ₐ[R] TemperleyLieb R δ' n :=
  AlgEquiv.ofAlgHom (signHom h) (signHom (neg_eq_iff_eq_neg.1 h.symm))
    (hom_ext fun i ↦ by simp [signHom_e])
    (hom_ext fun i ↦ by simp [signHom_e])

/-- The sign isomorphism sends each generator to its negative. -/
@[simp]
theorem signEquiv_e (h : δ' = -δ) (i : Fin (n - 1)) : signEquiv h (e δ i) = -e δ' i :=
  signHom_e h i

/-- The inverse of the sign isomorphism is the sign isomorphism in the other direction. -/
@[simp]
theorem signEquiv_symm (h : δ' = -δ) :
    (signEquiv (n := n) h).symm = signEquiv (neg_eq_iff_eq_neg.1 h.symm) :=
  (rfl)

/-- The sign isomorphism commutes with the strand inclusions. -/
@[simp]
theorem strandIncl_signEquiv (h : δ' = -δ) (x : TemperleyLieb R δ (n + 1)) :
    strandIncl (signEquiv h x) = signEquiv h (strandIncl x) := by
  have key : strandIncl.comp (signEquiv (n := n + 1) h).toAlgHom =
      (signEquiv (n := n + 2) h).toAlgHom.comp strandIncl :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun key x

/-- The sign isomorphism commutes with the augmentations, which kill every generator. -/
@[simp]
theorem aug_signEquiv (h : δ' = -δ) (x : TemperleyLieb R δ n) : aug (signEquiv h x) = aug x := by
  have key : aug.comp (signEquiv (n := n) h).toAlgHom = aug :=
    hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun key x

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)] [Fact (IsSelfAdjoint δ')]

/-- For self-adjoint loop values, the sign isomorphism preserves the analytic adjoint. -/
@[simp]
theorem signEquiv_star (h : δ' = -δ) (x : TemperleyLieb R δ n) :
    signEquiv h (star x) = star (signEquiv h x) :=
  map_star_iff (F := (signEquiv h).toAlgHom).mpr
    (fun i ↦ by simpa using (isSelfAdjoint_e (δ := δ') i).neg) x

end Star

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R} {tr' : ∀ n : ℕ, TemperleyLieb R δ' n →ₗ[R] R}

/-- A Markov trace at `δ' = -δ`, pulled back along the sign isomorphism and multiplied by
`(-1) ^ n` on `n` strands, is a Markov trace at `δ`. -/
theorem comp_signEquiv (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) :
    IsMarkovTrace R δ fun n ↦ (-1 : R) ^ n • (tr' n ∘ₗ (signEquiv h).toLinearMap) := by
  subst h
  constructor
  · intro n
    simp [htr'.map_one, ← mul_pow]
  · intro n x y
    simp [htr'.map_mul_comm n (signEquiv _ x)]
  · intro n x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
      ← strandIncl_signEquiv, htr'.map_strandIncl, pow_succ]
    ring
  · intro n x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul,
      ← strandIncl_signEquiv, signEquiv_e, mul_neg, map_neg, htr'.map_strandIncl_mul_e_last,
      pow_succ]
    ring

/-- **The trace relation of the sign isomorphism.** For Markov traces `tr` at `δ` and `tr'` at
`δ' = -δ`, the sign isomorphism `s` satisfies `tr' n (s x) = (-1) ^ n * tr n x`. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (x : TemperleyLieb R δ n) :
    tr' n (signEquiv h x) = (-1) ^ n * tr n x := by
  have hx := LinearMap.congr_fun (congrFun (htr.unique (htr'.comp_signEquiv h)) n) x
  simp only [hx, LinearMap.smul_apply, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    smul_eq_mul, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- The sign isomorphism identifies the normalised traces `(δ ^ n)⁻¹ * tr n` at `δ` and `-δ`. -/
theorem inv_pow_mul_map_signEquiv {K : Type*} [Field K] {δ δ' : K}
    {tr : ∀ n : ℕ, TemperleyLieb K δ n →ₗ[K] K} {tr' : ∀ n : ℕ, TemperleyLieb K δ' n →ₗ[K] K}
    (htr : IsMarkovTrace K δ tr) (htr' : IsMarkovTrace K δ' tr') (h : δ' = -δ)
    (x : TemperleyLieb K δ n) :
    (δ' ^ n)⁻¹ * tr' n (signEquiv h x) = (δ ^ n)⁻¹ * tr n x := by
  have hs : ((-1 : K) ^ n)⁻¹ * (-1) ^ n = 1 := inv_mul_cancel₀ (pow_ne_zero n (by simp))
  rw [htr.map_signEquiv htr' h, h, neg_pow, mul_inv, mul_mul_mul_comm, hs, one_mul]

/-- The sign isomorphism identifies the trace radicals at `δ` and at `δ' = -δ`. -/
theorem comap_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) (n : ℕ) :
    Ideal.comap (signEquiv (n := n) h) ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  simp only [Ideal.mem_comap, LinearMap.mem_traceRadical]
  rw [(signEquiv h).surjective.forall]
  simp only [← map_mul, htr.map_signEquiv htr' h, ((isUnit_one.neg).pow n).mul_right_eq_zero]

/-- The sign isomorphism induces an isomorphism of the quotients by the trace radicals at `δ` and
at `δ' = -δ`. -/
def quotientSignEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) (n : ℕ) :
    (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) ≃ₐ[R]
      TemperleyLieb R δ' n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n) :=
  Ideal.quotientEquivAlg _ _ (signEquiv h) <| by
    rw [← htr.comap_traceRadical_signEquiv htr' h n]
    exact (Ideal.map_comap_of_surjective _ (signEquiv h).surjective _).symm

/-- The induced isomorphism of the trace-radical quotients is computed on representatives. -/
@[simp]
theorem quotientSignEquiv_mk (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R δ' tr')
    (h : δ' = -δ) {n : ℕ} (x : TemperleyLieb R δ n) :
    htr.quotientSignEquiv htr' h n
        (Ideal.Quotient.mk ((tr n).traceRadical (htr.map_mul_comm n)) x) =
      Ideal.Quotient.mk ((tr' n).traceRadical (htr'.map_mul_comm n)) (signEquiv h x) :=
  (rfl)

/-- The quotient traces satisfy the trace relation of the sign isomorphism. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) {n : ℕ}
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) (htr.quotientSignEquiv htr' h n x) =
      (-1) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientSignEquiv_mk, LinearMap.quotientTrace_mk, htr.map_signEquiv htr' h]

/-- The induced isomorphisms of the trace-radical quotients commute with the strand maps. -/
theorem quotientStrandIncl_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R δ' tr') (h : δ' = -δ) {n : ℕ}
    (x : TemperleyLieb R δ (n + 1) ⧸ (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr'.quotientStrandIncl n (htr.quotientSignEquiv htr' h (n + 1) x) =
      htr.quotientSignEquiv htr' h (n + 2) (htr.quotientStrandIncl n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [quotientSignEquiv_mk, quotientStrandIncl_mk, strandIncl_signEquiv]

end IsMarkovTrace

/-- **The trace relation for the spin-model traces.** If `δ = -(q + q⁻¹)` and
`δ' = -(q' + q'⁻¹) = -δ`, for instance `q' = -q`, then the sign isomorphism satisfies
`markovTrace q' (s x) = (-1) ^ n * markovTrace q x`. -/
theorem markovTrace_signEquiv (q : Rˣ) (hq : δ = -((q : R) + ((q⁻¹ : Rˣ) : R))) (q' : Rˣ)
    (hq' : δ' = -((q' : R) + ((q'⁻¹ : Rˣ) : R))) (h : δ' = -δ) (x : TemperleyLieb R δ n) :
    markovTrace q' hq' (signEquiv h x) = (-1) ^ n * markovTrace q hq x :=
  (isMarkovTrace_markovTrace q hq).map_signEquiv (isMarkovTrace_markovTrace q' hq') h x

open scoped ComplexOrder

namespace IsMarkovTrace

variable {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] {tr : ∀ n : ℕ, TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}

/-- **Positivity at negative loop parameters.** For `δ < 0`, the signed Hermitian forms
`(x, y) ↦ (-1) ^ n * tr n (x⋆ * y)` of a Markov trace are positive semidefinite on every number
`n` of strands exactly when `-δ` is an admissible loop parameter, `-δ = 2 cos (π / m)` for some
`m ≥ 3` or `-δ ≥ 2`. -/
theorem forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff (htr : IsMarkovTrace ℂ (δ : ℂ) tr)
    (hδ : δ < 0) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n), 0 ≤ (-1) ^ n * tr n (star x * x)) ↔
      -δ ∈ jonesLoopParameters := by
  have : Fact (IsSelfAdjoint ((-δ : ℝ) : ℂ)) := ⟨Complex.conj_ofReal _⟩
  have h : ((δ : ℝ) : ℂ) = -((-δ : ℝ) : ℂ) := by push_cast; ring
  rw [← (htr.comp_signEquiv h).forall_map_star_mul_self_nonneg_iff (neg_pos.2 hδ)]
  refine forall_congr' fun n ↦ ((signEquiv h).surjective.forall).trans (forall_congr' fun x ↦ ?_)
  simp [signEquiv_star]

end IsMarkovTrace

/-- **Positivity at negative loop parameters** for the spin-model trace. Let `δ < 0` and let `q` be
a unit with `δ = -(q + q⁻¹)`. Then the signed closure forms
`(-1) ^ n * TauCeti.TemperleyLieb.markovTrace q hq (x⋆ * x)` are real and nonnegative for every
number `n` of strands and every `x` exactly when `-δ` is an admissible loop parameter. -/
theorem markovTrace_neg_one_pow_nonneg_iff {δ : ℝ} [Fact (IsSelfAdjoint (δ : ℂ))] (hδ : δ < 0)
    (q : ℂˣ) (hq : (δ : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) :
    (∀ (n : ℕ) (x : TemperleyLieb ℂ (δ : ℂ) n),
        0 ≤ (-1) ^ n * markovTrace q hq (star x * x)) ↔
      -δ ∈ jonesLoopParameters :=
  (isMarkovTrace_markovTrace q hq).forall_neg_one_pow_mul_map_star_mul_self_nonneg_iff hδ

end TauCeti.TemperleyLieb
