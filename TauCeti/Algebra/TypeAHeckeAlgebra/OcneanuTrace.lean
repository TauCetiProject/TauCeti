/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.CosetBasis
public import TauCeti.Algebra.TypeAHeckeAlgebra.MarkovTrace

/-!
# Existence of the Ocneanu trace

For every commutative ring `R`, unit `q : Rˣ` and parameter `z : R`, this file constructs the
Ocneanu trace `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z` on the infinite type-A
Hecke algebra: the `R`-linear functional `τ` with `τ 1 = 1`, `τ (x * y) = τ (y * x)`, and the
Markov rule `τ (x * T n) = z * τ x` for `x` in the stage of the first `n + 1` strands. Together
with the uniqueness theorem `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.unique`, this is
Ocneanu's theorem: for every `z` there is exactly one Markov trace with parameter `z`
(`TauCeti.InfiniteTypeAHeckeAlgebra.existsUnique_isMarkovTrace`). No positivity is asserted.

The trace is built one strand at a time, following Jones. Write `Hₙ` for the stage of the first
`n` strands. By the coset basis theorem (`TauCeti.InfiniteTypeAHeckeAlgebra.cosetEquiv`), every
element of `Hₙ₊₂` is uniquely a sum `∑ m, a m * cosetRep q (n + 1) m` with coefficients in
`Hₙ₊₁`, where `cosetRep q (n + 1) m = T n * cosetRep q n m` for `m ≤ n` and the last
representative is `1`. A trace `φ` on `Hₙ₊₁` extends to `Hₙ₊₂` by sending this sum to
`φ (a (n + 1)) + z * ∑ (m ≤ n), φ (cosetRep q n m * a m)`, so that `a * T n * b ↦ z * φ (b * a)`
for `a`, `b` in `Hₙ₊₁`. That the extension is again a trace is checked on the decomposition
`Hₙ₊₂ = Hₙ₊₁ + Hₙ₊₁ Tₙ Hₙ₊₁` (`TauCeti.InfiniteTypeAHeckeAlgebra.toSubmodule_stage_add_two`),
using the same decomposition of `Hₙ₊₁` one level down, the quadratic relation and the braid
relation. The stage traces are compatible, so they glue to a functional on the union of the
stages.

## Main definitions

* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace`: the Ocneanu trace with parameter `z`.

## Main results

* `TauCeti.InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace`: the Ocneanu trace is a Markov
  trace with parameter `z`.
* `TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.eq_ocneanuTrace` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.existsUnique_isMarkovTrace`: **Ocneanu's theorem**, every
  Markov trace with parameter `z` is the Ocneanu trace, and there is exactly one.
* `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_eq_indexCharacter` and
  `TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_eq_signCharacter`: at `z = q` and `z = -q⁻¹`
  the Ocneanu trace is the corresponding character.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Section 5 (Theorem 5.1 and its proof).
* C. Kassel and V. Turaev, *Braid Groups*, Springer GTM 247 (2008), Chapter 4.
-/

public section

namespace TauCeti

namespace InfiniteTypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

section StageTrace

/-! ### Extending a trace from one stage to the next -/

variable (q) in
/-- The inclusion of the stage `n` into the stage `n + 1`. -/
private abbrev incl (n : ℕ) : stage R q n →ₐ[R] stage R q (n + 1) :=
  Subalgebra.inclusion (stage_mono n.le_succ)

variable (q) in
/-- The generator `T n`, which adds the last strand, as an element of the stage `n + 2`. -/
private abbrev lastT (n : ℕ) : stage R q (n + 2) :=
  ⟨T q n, T_mem_stage (by omega)⟩

variable (q) in
/-- The coset representative `cosetRep q n m` as an element of the stage `n + 1`. -/
private abbrev rep (n m : ℕ) : stage R q (n + 1) :=
  ⟨cosetRep q n m, cosetRep_mem_stage n m⟩

private theorem lastT_mul_lastT (n : ℕ) :
    lastT q n * lastT q n = ((q : R) - ↑q⁻¹) • lastT q n + 1 :=
  Subtype.ext (T_mul_self n)

private theorem lastT_mul_lastT_mul {n : ℕ} (y : stage R q (n + 2)) :
    lastT q n * (lastT q n * y) = ((q : R) - ↑q⁻¹) • (lastT q n * y) + y := by
  rw [← mul_assoc, lastT_mul_lastT, add_mul, smul_mul_assoc, one_mul]

/-- An element of the stage `n` commutes with the generator `T n`. -/
private theorem commute_lastT {n : ℕ} (c : stage R q n) :
    Commute (lastT q n) (incl q (n + 1) (incl q n c)) :=
  Subtype.ext (commute_T_of_mem_stage le_rfl c.2).eq

private theorem lastT_braid (n : ℕ) :
    lastT q (n + 1) * incl q (n + 2) (lastT q n) * lastT q (n + 1) =
      incl q (n + 2) (lastT q n) * lastT q (n + 1) * incl q (n + 2) (lastT q n) :=
  Subtype.ext (T_braid n).symm

private theorem lastT_braid_assoc (n : ℕ) (y : stage R q (n + 3)) :
    lastT q (n + 1) * (incl q (n + 2) (lastT q n) * (lastT q (n + 1) * y)) =
      incl q (n + 2) (lastT q n) * (lastT q (n + 1) * (incl q (n + 2) (lastT q n) * y)) := by
  simp only [← mul_assoc, lastT_braid]

private theorem lastT_mul_rep {n m : ℕ} (h : m ≤ n) :
    lastT q n * incl q (n + 1) (rep q n m) = rep q (n + 1) m :=
  Subtype.ext (cosetRep_succ h).symm

variable (z : R)

/-- The extension of a functional `φ` on the stage `n + 1` to the stage `n + 2`: in the coset
coordinates `x = ∑ m, a m * cosetRep q (n + 1) m`, it sends `x` to
`φ (a (n + 1)) + z * ∑ (m ≤ n), φ (cosetRep q n m * a m)`. -/
private noncomputable def extend {n : ℕ} (φ : stage R q (n + 1) →ₗ[R] R) :
    stage R q (n + 2) →ₗ[R] R :=
  LinearMap.lsum R (fun _ : Fin (n + 2) ↦ stage R q (n + 1)) R
      (Fin.lastCases (motive := fun _ ↦ stage R q (n + 1) →ₗ[R] R) φ
        fun m ↦ z • φ ∘ₗ LinearMap.mulLeft R (rep q n m)) ∘ₗ
    (cosetEquiv R q (n + 1)).symm.toLinearMap

variable {n : ℕ} (φ : stage R q (n + 1) →ₗ[R] R)

/-- The extension agrees with `φ` on the stage `n + 1`. -/
private theorem extend_incl (b : stage R q (n + 1)) : extend z φ (incl q (n + 1) b) = φ b := by
  simp [extend, -LinearMap.lsum_apply, LinearMap.lsum_piSingle]

private theorem extend_incl_mul_rep (m : Fin (n + 1)) (a : stage R q (n + 1)) :
    extend z φ (incl q (n + 1) a * rep q (n + 1) m) = z * φ (rep q n m * a) := by
  have h := cosetEquiv_symm_inclusion_mul_cosetRep m.castSucc a
  rw [Fin.val_castSucc] at h
  simp [extend, h, -LinearMap.lsum_apply, LinearMap.lsum_piSingle]

variable {φ}

/-- The defining property of the extension of a trace: `a * T n * b ↦ z * φ (b * a)`. -/
private theorem extend_incl_mul_lastT_mul_incl (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (a b : stage R q (n + 1)) :
    extend z φ (incl q (n + 1) a * lastT q n * incl q (n + 1) b) = z * φ (b * a) := by
  obtain ⟨c, rfl⟩ := (cosetEquiv R q n).surjective b
  simp only [cosetEquiv_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have hm : incl q (n + 1) a * lastT q n * incl q (n + 1) (incl q n (c m) * rep q n m) =
      incl q (n + 1) (a * incl q n (c m)) * rep q (n + 1) m := by
    rw [← lastT_mul_rep (Nat.lt_succ_iff.1 m.2), map_mul, map_mul, ← mul_assoc,
      mul_assoc _ (lastT q n), (commute_lastT (c m)).eq, ← mul_assoc, mul_assoc]
  rw [hm, extend_incl_mul_rep, ← mul_assoc, hφ]
  simp only [mul_assoc]

/-- `b * T n * T n ↦ ((q - q⁻¹) * z + 1) * φ b`. -/
private theorem extend_incl_mul_lastT_mul_lastT (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (b : stage R q (n + 1)) :
    extend z φ (incl q (n + 1) b * lastT q n * lastT q n) =
      (((q : R) - ↑q⁻¹) * z + 1) * φ b := by
  have h : incl q (n + 1) b * lastT q n * lastT q n =
      ((q : R) - ↑q⁻¹) • (incl q (n + 1) b * lastT q n * incl q (n + 1) 1) +
        incl q (n + 1) b := by
    rw [map_one, mul_one, mul_assoc, lastT_mul_lastT, mul_add, mul_smul_comm, mul_one]
  rw [h, map_add, map_smul, extend_incl_mul_lastT_mul_incl z hφ, extend_incl, one_mul,
    smul_eq_mul]
  ring

/-- The extension of a trace is tracial against the stage `n + 1`. -/
private theorem extend_incl_mul_comm (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (b : stage R q (n + 1)) (x : stage R q (n + 2)) :
    extend z φ (incl q (n + 1) b * x) = extend z φ (x * incl q (n + 1) b) := by
  have h := stage_linearMap_ext (f := extend z φ ∘ₗ LinearMap.mulLeft R (incl q (n + 1) b))
    (g := extend z φ ∘ₗ LinearMap.mulRight R (incl q (n + 1) b)) (fun c ↦ ?_) (fun a c ↦ ?_)
  · exact LinearMap.congr_fun h x
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [← map_mul, ← map_mul, extend_incl, extend_incl, hφ]
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_assoc _ _ (incl q (n + 1) b), ← map_mul,
      extend_incl_mul_lastT_mul_incl z hφ, extend_incl_mul_lastT_mul_incl z hφ, mul_assoc]

/-- `T n * T n * b ↦ ((q - q⁻¹) * z + 1) * φ b`. -/
private theorem extend_lastT_mul_lastT_mul_incl (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (b : stage R q (n + 1)) :
    extend z φ (lastT q n * (lastT q n * incl q (n + 1) b)) =
      (((q : R) - ↑q⁻¹) * z + 1) * φ b := by
  rw [← extend_incl_mul_lastT_mul_lastT z hφ, ← mul_assoc, ← extend_incl_mul_comm z hφ,
    mul_assoc]

/-! ### The extension of the extension of a trace is a trace -/

section Step

variable {m : ℕ} {φ : stage R q (m + 1) →ₗ[R] R}

/-- `T * w * T ↦ ((q - q⁻¹) * z + 1) * φ₁ w`, where `φ₁` is the extension of `φ` and `T` is the
generator adding the strand after it. -/
private theorem extend_extend_lastT_mul_incl_mul_lastT (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (hφ' : ∀ x y, extend z φ (x * y) = extend z φ (y * x)) (w : stage R q (m + 2)) :
    extend z (extend z φ) (lastT q (m + 1) * incl q (m + 2) w * lastT q (m + 1)) =
      (((q : R) - ↑q⁻¹) * z + 1) * extend z φ w := by
  have h := stage_linearMap_ext (n := m)
    (f := extend z (extend z φ) ∘ₗ LinearMap.mulRight R (lastT q (m + 1)) ∘ₗ
      LinearMap.mulLeft R (lastT q (m + 1)) ∘ₗ (incl q (m + 2)).toLinearMap)
    (g := (((q : R) - ↑q⁻¹) * z + 1) • extend z φ) (fun c ↦ ?_) (fun c d ↦ ?_)
  · exact LinearMap.congr_fun h w
  · simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [(commute_lastT c).eq, extend_incl_mul_lastT_mul_lastT z hφ']
  · simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, LinearMap.smul_apply, smul_eq_mul]
    -- `T * (c * T' * d) * T = (c * T') * T * (T' * d)`, by the braid relation.
    have h₁ : lastT q (m + 1) * incl q (m + 2) (incl q (m + 1) c * lastT q m * incl q (m + 1) d) *
        lastT q (m + 1) = incl q (m + 2) (incl q (m + 1) c * lastT q m) * lastT q (m + 1) *
          incl q (m + 2) (lastT q m * incl q (m + 1) d) := by
      simp only [map_mul, mul_assoc]
      rw [(commute_lastT c).left_comm, ← (commute_lastT d).eq, lastT_braid_assoc]
    have h₂ : lastT q m * incl q (m + 1) d * (incl q (m + 1) c * lastT q m) =
        lastT q m * incl q (m + 1) (d * c) * lastT q m := by
      simp only [map_mul, mul_assoc]
    rw [h₁, extend_incl_mul_lastT_mul_incl z hφ', h₂, hφ', extend_lastT_mul_lastT_mul_incl z hφ,
      extend_incl_mul_lastT_mul_incl z hφ]
    ring

/-- The value of `a * T * b * T` for `a = c' * T' * d'` and `b = c * T' * d`, where `T'` and `T`
are the last two generators. -/
private theorem extend_extend_mul_lastT_mul_mul_lastT
    (hφ' : ∀ x y, extend z φ (x * y) = extend z φ (y * x)) (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (c d c' d' : stage R q (m + 1)) :
    extend z (extend z φ) (incl q (m + 2) (incl q (m + 1) c' * lastT q m * incl q (m + 1) d') *
        lastT q (m + 1) * incl q (m + 2) (incl q (m + 1) c * lastT q m * incl q (m + 1) d) *
        lastT q (m + 1)) =
      z * (((q : R) - ↑q⁻¹) * extend z φ (lastT q m * (incl q (m + 1) (d * c') * lastT q m *
          incl q (m + 1) (d' * c))) + z * φ (d' * c * (d * c'))) := by
  have h₁ : incl q (m + 2) (incl q (m + 1) c' * lastT q m * incl q (m + 1) d') *
      lastT q (m + 1) * incl q (m + 2) (incl q (m + 1) c * lastT q m * incl q (m + 1) d) *
      lastT q (m + 1) =
      incl q (m + 2) (incl q (m + 1) c' * lastT q m * incl q (m + 1) (d' * c) * lastT q m) *
        lastT q (m + 1) * incl q (m + 2) (lastT q m * incl q (m + 1) d) := by
    simp only [map_mul, mul_assoc]
    rw [(commute_lastT c).left_comm, ← (commute_lastT d).eq, lastT_braid_assoc]
  have h₂ : lastT q m * incl q (m + 1) d *
      (incl q (m + 1) c' * lastT q m * incl q (m + 1) (d' * c) * lastT q m) =
      lastT q m * (incl q (m + 1) (d * c') * lastT q m * incl q (m + 1) (d' * c)) *
        lastT q m := by
    simp only [map_mul, mul_assoc]
  rw [h₁, extend_incl_mul_lastT_mul_incl z hφ', h₂, hφ', lastT_mul_lastT_mul, map_add, map_smul,
    extend_incl_mul_lastT_mul_incl z hφ, smul_eq_mul]

/-- The pairing `(a, b) ↦ ψ (a * T * b * T)` on the stage `m + 2`, where `ψ` is the second
extension of `φ` and `T` the last generator, is symmetric. -/
private theorem extend_extend_mul_lastT_mul_mul_lastT_comm (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (hφ' : ∀ x y, extend z φ (x * y) = extend z φ (y * x)) (a b : stage R q (m + 2)) :
    extend z (extend z φ)
        (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b * lastT q (m + 1)) =
      extend z (extend z φ)
        (incl q (m + 2) b * lastT q (m + 1) * incl q (m + 2) a * lastT q (m + 1)) := by
  set ψ := extend z (extend z φ)
  let G : stage R q (m + 2) →ₗ[R] stage R q (m + 2) →ₗ[R] R :=
    LinearMap.mk₂ R
      (fun a b ↦ ψ (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b * lastT q (m + 1)))
      (fun _ _ _ ↦ by simp only [map_add, add_mul])
      (fun _ _ _ ↦ by simp only [map_smul, smul_mul_assoc, smul_eq_mul])
      (fun _ _ _ ↦ by simp only [map_add, add_mul, mul_add])
      (fun _ _ _ ↦ by simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_eq_mul])
  have hG : ∀ a b, G a b =
      ψ (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b * lastT q (m + 1)) :=
    fun _ _ ↦ rfl
  -- The pairing is symmetric when one argument lies in the stage `m + 1`.
  have hA : ∀ a c, G a (incl q (m + 1) c) = G (incl q (m + 1) c) a := by
    intro a c
    rw [hG, hG]
    calc ψ (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) (incl q (m + 1) c) *
            lastT q (m + 1))
        = ψ (incl q (m + 2) (incl q (m + 1) c) *
            (incl q (m + 2) a * lastT q (m + 1) * lastT q (m + 1))) := by
          rw [mul_assoc _ (incl q (m + 2) (incl q (m + 1) c)), ← (commute_lastT c).eq,
            ← mul_assoc, extend_incl_mul_comm z hφ']
      _ = (((q : R) - ↑q⁻¹) * z + 1) * extend z φ (incl q (m + 1) c * a) := by
          rw [← mul_assoc, ← mul_assoc, ← map_mul, extend_incl_mul_lastT_mul_lastT z hφ']
      _ = ψ (lastT q (m + 1) * incl q (m + 2) (incl q (m + 1) c * a) * lastT q (m + 1)) :=
          (extend_extend_lastT_mul_incl_mul_lastT z hφ hφ' _).symm
      _ = ψ (incl q (m + 2) (incl q (m + 1) c) * lastT q (m + 1) * incl q (m + 2) a *
            lastT q (m + 1)) := by
          rw [map_mul (incl q (m + 2)), ← mul_assoc (lastT q (m + 1)), (commute_lastT c).eq]
  -- The pairing is symmetric on the products `c * T' * d`.
  have hB : ∀ c d c' d', G (incl q (m + 1) c' * lastT q m * incl q (m + 1) d')
      (incl q (m + 1) c * lastT q m * incl q (m + 1) d) =
      G (incl q (m + 1) c * lastT q m * incl q (m + 1) d)
        (incl q (m + 1) c' * lastT q m * incl q (m + 1) d') := by
    intro c d c' d'
    have e : ∀ x y : stage R q (m + 2),
        lastT q m * (x * lastT q m * y) = lastT q m * x * (lastT q m * y) :=
      fun _ _ ↦ by simp only [mul_assoc]
    rw [hG, hG, extend_extend_mul_lastT_mul_mul_lastT z hφ' hφ,
      extend_extend_mul_lastT_mul_mul_lastT z hφ' hφ, e, e, hφ', hφ (d' * c)]
  -- Hence it is symmetric, by the decomposition of the stage `m + 2` in both arguments.
  have hC : ∀ c d, G.flip (incl q (m + 1) c * lastT q m * incl q (m + 1) d) =
      G (incl q (m + 1) c * lastT q m * incl q (m + 1) d) := fun c d ↦
    stage_linearMap_ext (fun c' ↦ by rw [LinearMap.flip_apply, hA])
      (fun c' d' ↦ by rw [LinearMap.flip_apply, hB])
  have h := stage_linearMap_ext (f := G a) (g := G.flip a) (fun c ↦ by
    rw [LinearMap.flip_apply, hA]) (fun c d ↦ by
      rw [LinearMap.flip_apply, ← LinearMap.flip_apply (f := G), hC])
  simpa only [hG, LinearMap.flip_apply] using LinearMap.congr_fun h b

/-- The second extension of `φ` is tracial against the last generator. -/
private theorem extend_extend_lastT_mul_comm (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (hφ' : ∀ x y, extend z φ (x * y) = extend z φ (y * x)) (y : stage R q (m + 3)) :
    extend z (extend z φ) (lastT q (m + 1) * y) = extend z (extend z φ) (y * lastT q (m + 1)) := by
  have h := stage_linearMap_ext (n := m + 1)
    (f := extend z (extend z φ) ∘ₗ LinearMap.mulLeft R (lastT q (m + 1)))
    (g := extend z (extend z φ) ∘ₗ LinearMap.mulRight R (lastT q (m + 1)))
    (fun w ↦ ?_) (fun a b ↦ ?_)
  · exact LinearMap.congr_fun h y
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    have e₁ : lastT q (m + 1) * incl q (m + 2) w =
        incl q (m + 2) 1 * lastT q (m + 1) * incl q (m + 2) w := by
      rw [map_one, one_mul]
    have e₂ : incl q (m + 2) w * lastT q (m + 1) =
        incl q (m + 2) w * lastT q (m + 1) * incl q (m + 2) 1 := by
      rw [map_one, mul_one]
    rw [e₁, e₂, extend_incl_mul_lastT_mul_incl z hφ', extend_incl_mul_lastT_mul_incl z hφ',
      mul_one, one_mul]
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    rw [show lastT q (m + 1) * (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b) =
        lastT q (m + 1) * incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b by
      simp only [mul_assoc], ← extend_incl_mul_comm z hφ']
    simp only [← mul_assoc]
    exact extend_extend_mul_lastT_mul_mul_lastT_comm z hφ hφ' b a

/-- **The induction step.** If a functional `φ` on the stage `m + 1` and its extension to the
stage `m + 2` are traces, then so is the extension of the extension to the stage `m + 3`. -/
private theorem extend_extend_mul_comm (hφ : ∀ x y, φ (x * y) = φ (y * x))
    (hφ' : ∀ x y, extend z φ (x * y) = extend z φ (y * x)) (x y : stage R q (m + 3)) :
    extend z (extend z φ) (x * y) = extend z (extend z φ) (y * x) := by
  have h := stage_linearMap_ext (n := m + 1)
    (f := extend z (extend z φ) ∘ₗ LinearMap.mulLeft R x)
    (g := extend z (extend z φ) ∘ₗ LinearMap.mulRight R x) (fun b ↦ ?_) (fun a b ↦ ?_)
  · exact LinearMap.congr_fun h y
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    exact (extend_incl_mul_comm z hφ' b x).symm
  · simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    calc extend z (extend z φ) (x * (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b))
        = extend z (extend z φ) (incl q (m + 2) b * x * incl q (m + 2) a * lastT q (m + 1)) := by
          rw [show x * (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b) =
              x * incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b by
            simp only [mul_assoc], ← extend_incl_mul_comm z hφ']
          simp only [mul_assoc]
      _ = extend z (extend z φ) (lastT q (m + 1) * (incl q (m + 2) b * x * incl q (m + 2) a)) :=
          (extend_extend_lastT_mul_comm z hφ hφ' _).symm
      _ = extend z (extend z φ) (incl q (m + 2) a * lastT q (m + 1) * incl q (m + 2) b * x) := by
          rw [← mul_assoc, ← mul_assoc, ← extend_incl_mul_comm z hφ']
          simp only [mul_assoc]

end Step

/-! ### The traces on the stages -/

variable (q) in
/-- The trace on the stage `n + 1` with Markov parameter `z`, obtained from the scalars by
extending one strand at a time. -/
private noncomputable def stageTrace : (n : ℕ) → stage R q (n + 1) →ₗ[R] R
  | 0 => ((indexCharacter R q).comp (stage R q 1).val).toLinearMap
  | n + 1 => extend z (stageTrace n)

private theorem stageTrace_succ (n : ℕ) :
    stageTrace q z (n + 1) = extend z (stageTrace q z n) := rfl

private theorem stageTrace_mul_comm :
    ∀ (n : ℕ) (x y : stage R q (n + 1)), stageTrace q z n (x * y) = stageTrace q z n (y * x)
  | 0, x, y | 1, x, y => congrArg _ <| Subtype.ext
      (commute_of_mem_stage_two (stage_mono (by omega) x.2) (stage_mono (by omega) y.2)).eq
  | n + 2, x, y => by
    rw [stageTrace_succ, stageTrace_succ]
    exact extend_extend_mul_comm z (stageTrace_mul_comm n)
      (by rw [← stageTrace_succ]; exact stageTrace_mul_comm (n + 1)) x y

/-- The stage traces are compatible with the inclusions of the stages. -/
private theorem stageTrace_eq_of_le {m n : ℕ} (h : m ≤ n) {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (m + 1)) :
    stageTrace q z n ⟨x, stage_mono (by omega) hx⟩ = stageTrace q z m ⟨x, hx⟩ := by
  induction n, h using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [← ih, stageTrace_succ, ← extend_incl z (stageTrace q z n)]
    congr 1

end StageTrace

/-! ### The Ocneanu trace -/

variable (q) in
/-- The value of the stage traces at an element of the infinite algebra. -/
private noncomputable def traceFun (z : R) (x : InfiniteTypeAHeckeAlgebra R q) : R :=
  stageTrace q z (exists_mem_stage x).choose
    ⟨x, stage_mono (Nat.le_succ _) (exists_mem_stage x).choose_spec⟩

private theorem traceFun_eq (z : R) {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) : traceFun q z x = stageTrace q z n ⟨x, hx⟩ :=
  (stageTrace_eq_of_le z (le_max_left _ n) _).symm.trans
    (stageTrace_eq_of_le z (le_max_right _ n) hx)

variable (R q) in
/-- **The Ocneanu trace** with parameter `z`: the unique normalized trace on the infinite type-A
Hecke algebra satisfying the Markov rule `τ (x * T n) = z * τ x` for `x` in the stage of the
first `n + 1` strands (`TauCeti.InfiniteTypeAHeckeAlgebra.isMarkovTrace_ocneanuTrace` and
`TauCeti.InfiniteTypeAHeckeAlgebra.IsMarkovTrace.eq_ocneanuTrace`). -/
noncomputable def ocneanuTrace (z : R) : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R where
  toFun := traceFun q z
  map_add' x y := by
    obtain ⟨n, hx, hy⟩ := exists_mem_stage_and_mem_stage x y
    rw [traceFun_eq z (add_mem hx hy), traceFun_eq z hx, traceFun_eq z hy, ← map_add]
    rfl
  map_smul' r x := by
    obtain ⟨n, hx, -⟩ := exists_mem_stage_and_mem_stage x x
    rw [traceFun_eq z (Subalgebra.smul_mem _ hx r), traceFun_eq z hx, RingHom.id_apply,
      ← map_smul]
    rfl

private theorem ocneanuTrace_eq_stageTrace (z : R) {n : ℕ} {x : InfiniteTypeAHeckeAlgebra R q}
    (hx : x ∈ stage R q (n + 1)) : ocneanuTrace R q z x = stageTrace q z n ⟨x, hx⟩ :=
  traceFun_eq z hx

/-- **Existence of the Ocneanu trace.** The Ocneanu trace is a Markov trace with parameter
`z`. -/
theorem isMarkovTrace_ocneanuTrace (z : R) : IsMarkovTrace z (ocneanuTrace R q z) where
  map_one := by
    rw [ocneanuTrace_eq_stageTrace z (n := 0) (one_mem _)]
    exact map_one (indexCharacter R q)
  map_mul_comm x y := by
    obtain ⟨n, hx, hy⟩ := exists_mem_stage_and_mem_stage x y
    rw [ocneanuTrace_eq_stageTrace z (mul_mem hx hy), ocneanuTrace_eq_stageTrace z (mul_mem hy hx)]
    exact stageTrace_mul_comm z n ⟨x, hx⟩ ⟨y, hy⟩
  map_mul_T {n x} hx := by
    have hxT : x * T q n ∈ stage R q (n + 2) :=
      mul_mem (stage_mono n.succ.le_succ hx) (T_mem_stage (by omega))
    have e : (⟨x * T q n, hxT⟩ : stage R q (n + 2)) =
        incl q (n + 1) ⟨x, hx⟩ * lastT q n * incl q (n + 1) 1 := by
      ext
      simp [lastT]
    rw [ocneanuTrace_eq_stageTrace z hxT, ocneanuTrace_eq_stageTrace z hx, e, stageTrace_succ,
      extend_incl_mul_lastT_mul_incl z (stageTrace_mul_comm z n), one_mul]

/-- **Ocneanu's theorem.** Every Markov trace with parameter `z` is the Ocneanu trace. -/
theorem IsMarkovTrace.eq_ocneanuTrace {z : R} {τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R}
    (hτ : IsMarkovTrace z τ) : τ = ocneanuTrace R q z :=
  hτ.unique (isMarkovTrace_ocneanuTrace z)

/-- **Ocneanu's theorem.** For every parameter `z` there is exactly one Markov trace with
parameter `z`. -/
theorem existsUnique_isMarkovTrace (z : R) :
    ∃! τ : InfiniteTypeAHeckeAlgebra R q →ₗ[R] R, IsMarkovTrace z τ :=
  ⟨ocneanuTrace R q z, isMarkovTrace_ocneanuTrace z, fun _ hτ ↦ hτ.eq_ocneanuTrace⟩

/-- The Ocneanu trace is normalized. -/
@[simp]
theorem ocneanuTrace_one (z : R) : ocneanuTrace R q z 1 = 1 :=
  (isMarkovTrace_ocneanuTrace z).map_one

/-- Every generator has trace `z`. -/
@[simp]
theorem ocneanuTrace_T (z : R) (i : ℕ) : ocneanuTrace R q z (T q i) = z := by
  simpa using (isMarkovTrace_ocneanuTrace z).map_mul_T (one_mem (stage R q (i + 1)))

/-- At `z = q` the Ocneanu trace is the index character `T i ↦ q`. -/
theorem ocneanuTrace_eq_indexCharacter :
    ocneanuTrace R q q = (indexCharacter R q).toLinearMap :=
  isMarkovTrace_indexCharacter.eq_ocneanuTrace.symm

/-- At `z = -q⁻¹` the Ocneanu trace is the sign character `T i ↦ -q⁻¹`. -/
theorem ocneanuTrace_eq_signCharacter :
    ocneanuTrace R q (-↑q⁻¹) = (signCharacter R q).toLinearMap :=
  isMarkovTrace_signCharacter.eq_ocneanuTrace.symm

end InfiniteTypeAHeckeAlgebra

end TauCeti
