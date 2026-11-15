/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Changing the sign of the Temperley–Lieb loop parameter

Negating every generator identifies the algebras at loop parameters `-δ` and `δ`, over
any commutative ring. The isomorphism `signEquiv` commutes with strand inclusions and
with the analytic adjoint for self-adjoint loop parameters. Taking the trivial star on
the coefficient ring also gives compatibility with the linear word reversal.

An unnormalized Markov trace changes by the factor `(-1) ^ n` on `n` strands.
`signTrace` is a linear equivalence transporting Markov families in both directions, and
`IsMarkovTrace.map_signEquiv` compares any two Markov families at opposite parameters by
uniqueness. In particular the sign isomorphism preserves and reflects the multiplication-pairing
trace radical and induces `IsMarkovTrace.quotientSignEquiv` on the trace quotients, even
at zero loop parameter and in characteristic two.

This is an isomorphism of towers of algebras, not an identification of signed cups
in a tensor category: the cup and its zigzag sign are separate data.

## References

* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*,
  Section 2.5, for signed cups and the Temperley–Lieb generators they determine.
-/

public section

namespace TauCeti.TemperleyLieb

variable {R : Type*} [CommRing R] {δ : R} {n : ℕ}

/-- Negating generators respects the presentation when the two loop values are opposites. -/
private def signHom (δ δ' : R) (h : δ = -δ') (n : ℕ) :
    TemperleyLieb R δ n →ₐ[R] TemperleyLieb R δ' n :=
  lift (fun i ↦ -e δ' i)
    (fun i ↦ by simp [h])
    (fun h ↦ by simpa using congrArg Neg.neg (e_mul_e_mul_e (δ := δ') h))
    (fun h ↦ by simpa using (commute_e (δ := δ') h).eq)

private theorem signHom_e (δ δ' : R) (h : δ = -δ') (i : Fin (n - 1)) :
    signHom δ δ' h n (e δ i) = -e δ' i :=
  lift_e _ _ _ _ i

/-- The sign isomorphism from loop parameter `-δ` to `δ`, sending `e i` to `-e i`.
It exists over every commutative ring, with no invertibility hypothesis on `δ`. -/
def signEquiv (δ : R) (n : ℕ) : TemperleyLieb R (-δ) n ≃ₐ[R] TemperleyLieb R δ n :=
  AlgEquiv.ofAlgHom (signHom (-δ) δ rfl n) (signHom δ (-δ) (neg_neg δ).symm n)
    (hom_ext fun i ↦ by simp [signHom_e])
    (hom_ext fun i ↦ by simp [signHom_e])

/-- The sign isomorphism negates each generator. -/
@[simp]
theorem signEquiv_e (i : Fin (n - 1)) : signEquiv δ n (e (-δ) i) = -e δ i :=
  signHom_e _ _ _ _

/-- The inverse sign isomorphism also negates each generator. -/
@[simp]
theorem signEquiv_symm_e (i : Fin (n - 1)) : (signEquiv δ n).symm (e δ i) = -e (-δ) i :=
  signHom_e _ _ _ _

/-- Changing the loop sign preserves the augmentation. -/
@[simp]
theorem aug_signEquiv (x : TemperleyLieb R (-δ) n) : aug (signEquiv δ n x) = aug x := by
  have h : aug.comp (signEquiv δ n).toAlgHom = aug := hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism preserves the augmentation. -/
@[simp]
theorem aug_signEquiv_symm (x : TemperleyLieb R δ n) :
    aug ((signEquiv δ n).symm x) = aug x := by
  simpa using (aug_signEquiv ((signEquiv δ n).symm x)).symm

/-- Changing the loop sign commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_strandIncl (x : TemperleyLieb R (-δ) (n + 1)) :
    signEquiv δ (n + 2) (strandIncl x) = strandIncl (signEquiv δ (n + 1) x) := by
  have h : (signEquiv δ (n + 2)).toAlgHom.comp strandIncl =
      strandIncl.comp (signEquiv δ (n + 1)).toAlgHom := hom_ext fun i ↦ by simp
  exact AlgHom.congr_fun h x

/-- The inverse sign isomorphism commutes with adding a straight strand. -/
@[simp]
theorem signEquiv_symm_strandIncl (x : TemperleyLieb R δ (n + 1)) :
    (signEquiv δ (n + 2)).symm (strandIncl x) =
      strandIncl ((signEquiv δ (n + 1)).symm x) := by
  apply (signEquiv δ (n + 2)).injective
  simp

section Star

variable [StarRing R] [Fact (IsSelfAdjoint δ)]

/-- The sign isomorphism preserves the analytic adjoint. For a trivial coefficient star,
this is compatibility with linear word reversal. -/
@[simp]
theorem signEquiv_star (x : TemperleyLieb R (-δ) n) :
    signEquiv δ n (star x) = star (signEquiv δ n x) :=
  (map_star_iff (F := (signEquiv δ n).toAlgHom)).mpr
    (fun i ↦ by simp [IsSelfAdjoint]) x

/-- The inverse sign isomorphism preserves the analytic adjoint. -/
@[simp]
theorem signEquiv_symm_star (x : TemperleyLieb R δ n) :
    (signEquiv δ n).symm (star x) = star ((signEquiv δ n).symm x) := by
  apply (signEquiv δ n).injective
  simp

end Star

/-- Linear equivalence transporting families of unnormalized traces from `-δ` to `δ`,
with the degree-dependent sign needed to retain the Markov normalization. -/
def signTrace : (∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R) ≃ₗ[R]
    (∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R) where
  toFun tr n := (-1 : R) ^ n • (tr n ∘ₗ (signEquiv δ n).symm.toLinearMap)
  invFun tr n := (-1 : R) ^ n • (tr n ∘ₗ (signEquiv δ n).toLinearMap)
  left_inv tr := by ext n x; simp [← mul_assoc, ← mul_pow]
  right_inv tr := by ext n x; simp [← mul_assoc, ← mul_pow]
  map_add' tr₁ tr₂ := by ext n x; simp [mul_add]
  map_smul' r tr := by ext n x; simp [mul_left_comm]

/-- Evaluation of the transported trace. -/
@[simp]
theorem signTrace_apply (tr : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R)
    (x : TemperleyLieb R δ n) :
    signTrace tr n x = (-1 : R) ^ n * tr n ((signEquiv δ n).symm x) := (rfl)

/-- Evaluation of the inverse signed transport. -/
@[simp]
theorem signTrace_symm_apply (tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R)
    (x : TemperleyLieb R (-δ) n) :
    signTrace.symm tr n x = (-1 : R) ^ n * tr n (signEquiv δ n x) := (rfl)

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb R δ n →ₗ[R] R}
  {tr' : ∀ n : ℕ, TemperleyLieb R (-δ) n →ₗ[R] R}

/-- The signed transport of a Markov family is again a Markov family, including at `δ = 0`. -/
theorem signTrace (htr' : IsMarkovTrace R (-δ) tr') :
    IsMarkovTrace R δ (TemperleyLieb.signTrace tr') where
  map_one n := by
    rw [signTrace_apply, _root_.map_one, htr'.map_one, ← mul_pow]
    simp
  map_mul_comm n x y := by simp only [signTrace_apply, map_mul, htr'.map_mul_comm]
  map_strandIncl n x := by
    simp only [signTrace_apply, signEquiv_symm_strandIncl, htr'.map_strandIncl]
    simp [pow_succ, mul_comm, mul_left_comm]
  map_strandIncl_mul_e_last n x := by
    simp only [signTrace_apply, map_mul, signEquiv_symm_strandIncl, signEquiv_symm_e,
      mul_neg, map_neg, htr'.map_strandIncl_mul_e_last]
    simp [pow_succ]

/-- Inverse signed transport preserves the Markov axioms. -/
theorem signTrace_symm (htr : IsMarkovTrace R δ tr) :
    IsMarkovTrace R (-δ) (TemperleyLieb.signTrace.symm tr) where
  map_one n := by
    rw [signTrace_symm_apply, _root_.map_one, htr.map_one, ← mul_pow]
    simp
  map_mul_comm n x y := by simp only [signTrace_symm_apply, map_mul, htr.map_mul_comm]
  map_strandIncl n x := by
    simp only [signTrace_symm_apply, signEquiv_strandIncl, htr.map_strandIncl]
    simp [pow_succ, mul_comm, mul_left_comm]
  map_strandIncl_mul_e_last n x := by
    simp only [signTrace_symm_apply, map_mul, signEquiv_strandIncl, signEquiv_e,
      mul_neg, map_neg, htr.map_strandIncl_mul_e_last]
    simp [pow_succ]

/-- At opposite loop parameters the unnormalized Markov traces differ by `(-1) ^ n`
under the sign isomorphism. No existence of either family is assumed implicitly. -/
theorem map_signEquiv (htr : IsMarkovTrace R δ tr) (htr' : IsMarkovTrace R (-δ) tr')
    (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    tr n (signEquiv δ n x) = (-1 : R) ^ n * tr' n x := by
  have h := congrFun (htr.unique htr'.signTrace) n
  simpa using LinearMap.congr_fun h (signEquiv δ n x)

/-- The inverse sign isomorphism changes an unnormalized Markov trace by `(-1) ^ n`. -/
theorem map_signEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    tr' n ((signEquiv δ n).symm x) = (-1 : R) ^ n * tr n x := by
  have h := congrFun (htr'.unique htr.signTrace_symm) n
  simpa using LinearMap.congr_fun h ((signEquiv δ n).symm x)

/-- The sign isomorphism carries the trace radical at `-δ` exactly onto the one at `δ`.
This holds over commutative rings, so in particular at every complex loop parameter. -/
theorem signEquiv_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    signEquiv δ n x ∈ (tr n).traceRadical (htr.map_mul_comm n) ↔
      x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) := by
  simp only [LinearMap.mem_traceRadical]
  rw [(signEquiv δ n).surjective.forall]
  simp only [← map_mul, htr.map_signEquiv htr', neg_one_pow_mul_eq_zero_iff]

/-- The inverse sign isomorphism also preserves and reflects trace-radical membership. -/
theorem signEquiv_symm_mem_traceRadical_iff (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    (signEquiv δ n).symm x ∈ (tr' n).traceRadical (htr'.map_mul_comm n) ↔
      x ∈ (tr n).traceRadical (htr.map_mul_comm n) := by
  simpa using (htr.signEquiv_mem_traceRadical_iff htr' n ((signEquiv δ n).symm x)).symm

/-- Pulling back the trace radical along the sign isomorphism gives the opposite radical. -/
theorem comap_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (signEquiv δ n).toRingHom ((tr n).traceRadical (htr.map_mul_comm n)) =
      (tr' n).traceRadical (htr'.map_mul_comm n) := by
  ext x
  exact htr.signEquiv_mem_traceRadical_iff htr' n x

/-- Pulling back along the inverse sign isomorphism gives the original trace radical. -/
theorem comap_traceRadical_signEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.comap (signEquiv δ n).symm.toRingHom ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) := by
  ext x
  exact htr.signEquiv_symm_mem_traceRadical_iff htr' n x

/-- The sign isomorphism maps the opposite trace radical onto the original one. -/
theorem map_traceRadical_signEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map (signEquiv δ n).toRingHom ((tr' n).traceRadical (htr'.map_mul_comm n)) =
      (tr n).traceRadical (htr.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquiv htr' n]
  exact Ideal.map_comap_of_surjective (signEquiv δ n).toRingHom
    (signEquiv δ n).surjective _

/-- The inverse sign isomorphism maps the original trace radical onto the opposite one. -/
theorem map_traceRadical_signEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    Ideal.map (signEquiv δ n).symm.toRingHom ((tr n).traceRadical (htr.map_mul_comm n)) =
      (tr' n).traceRadical (htr'.map_mul_comm n) := by
  rw [← htr.comap_traceRadical_signEquiv_symm htr' n]
  exact Ideal.map_comap_of_surjective (signEquiv δ n).symm.toRingHom
    (signEquiv δ n).symm.surjective _

/-- The sign isomorphism descends to the algebraic quotients by the Markov-trace radicals. -/
def quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) :
    (TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) ≃ₐ[R]
      (TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :=
  Ideal.quotientEquivAlg _ _ (signEquiv δ n) (htr.map_traceRadical_signEquiv htr' n).symm

/-- The quotient sign isomorphism is induced by the sign isomorphism on representatives. -/
@[simp]
theorem quotientSignEquiv_mk (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R (-δ) n) :
    htr.quotientSignEquiv htr' n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (signEquiv δ n x) :=
  Ideal.quotientEquivAlg_mk _ _ _ x

/-- The inverse quotient sign isomorphism acts on representatives by the inverse sign map. -/
@[simp]
theorem quotientSignEquiv_symm_mk (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ) (x : TemperleyLieb R δ n) :
    (htr.quotientSignEquiv htr' n).symm (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ ((signEquiv δ n).symm x) := by
  apply (htr.quotientSignEquiv htr' n).injective
  simp

/-- The quotient sign isomorphism retains the degree-dependent Markov-trace sign. -/
@[simp]
theorem quotientTrace_quotientSignEquiv (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R (-δ) n ⧸ (tr' n).traceRadical (htr'.map_mul_comm n)) :
    (tr n).quotientTrace (htr.map_mul_comm n) (htr.quotientSignEquiv htr' n x) =
      (-1 : R) ^ n * (tr' n).quotientTrace (htr'.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv htr']

/-- The inverse quotient sign isomorphism has the same degree-dependent trace sign. -/
@[simp]
theorem quotientTrace_quotientSignEquiv_symm (htr : IsMarkovTrace R δ tr)
    (htr' : IsMarkovTrace R (-δ) tr') (n : ℕ)
    (x : TemperleyLieb R δ n ⧸ (tr n).traceRadical (htr.map_mul_comm n)) :
    (tr' n).quotientTrace (htr'.map_mul_comm n) ((htr.quotientSignEquiv htr' n).symm x) =
      (-1 : R) ^ n * (tr n).quotientTrace (htr.map_mul_comm n) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [htr.map_signEquiv_symm htr']

end IsMarkovTrace

end TauCeti.TemperleyLieb
