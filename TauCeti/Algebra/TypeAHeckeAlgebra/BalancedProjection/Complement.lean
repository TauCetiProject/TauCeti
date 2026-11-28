/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
import TauCeti.Algebra.Ring.Idempotent.Basic
import Mathlib.Tactic.Abel

/-!
# The complement automorphism of the balanced projection algebra

For idempotents `p` and `q`, replacing `p` and `q` by `1 - p` and `1 - q` negates the balanced
defect `(p * q * p - t • p) - (q * p * q - t • q)`. Sending `e i` to `1 - e i` therefore defines an
involutive `R`-algebra automorphism `TauCeti.BalancedProjectionAlgebra.complementEquiv` at the same
parameter `τ`. It preserves every finite stage and exchanges scalar characters `c ↔ 1 - c`.

## Main definitions and results

* `TauCeti.BalancedProjectionAlgebra.complementEquiv`, `stageComplementEquiv`: the involutive
  complement automorphism `e i ↦ 1 - e i` and its restriction to finite stages.
* `TauCeti.BalancedProjectionAlgebra.character_complementEquiv`: precomposing a scalar character
  with `complementEquiv` sends `c` to `1 - c`.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §§2–3.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §§5, 11.
-/

public section

namespace TauCeti.BalancedProjectionAlgebra

variable {R : Type*} [CommRing R]

section Complement

variable (τ : R)

private def complementHom : BalancedProjectionAlgebra R τ →ₐ[R] BalancedProjectionAlgebra R τ :=
  lift (fun i ↦ 1 - e τ i) (fun i ↦ (isIdempotentElem_e i).one_sub)
    (fun i ↦ (isIdempotentElem_e i).one_sub_mul_mul_sub_smul_eq
      (isIdempotentElem_e (i + 1)) (e_balanced i))
    (fun h ↦ by simp [sub_mul, mul_sub, (commute_e (Or.inl h)).eq]; abel)

/-- The involutive complement automorphism of the balanced projection algebra, sending each
generator `e i` to `1 - e i` at the same parameter `τ`. -/
def complementEquiv : BalancedProjectionAlgebra R τ ≃ₐ[R] BalancedProjectionAlgebra R τ :=
  AlgEquiv.ofAlgHom (complementHom τ) (complementHom τ)
    (hom_ext fun i ↦ by simp [complementHom]) (hom_ext fun i ↦ by simp [complementHom])

@[simp]
theorem complementEquiv_e (i : ℕ) : complementEquiv (R := R) τ (e τ i) = 1 - e τ i :=
  lift_e _ _ _ _ i

@[simp]
theorem complementEquiv_symm : (complementEquiv (R := R) τ).symm = complementEquiv τ :=
  AlgEquiv.ofAlgHom_symm _ _ _ _

@[simp]
theorem complementEquiv_complementEquiv (x : BalancedProjectionAlgebra R τ) :
    complementEquiv τ (complementEquiv τ x) = x := by
  simpa only [complementEquiv_symm] using (complementEquiv (R := R) τ).symm_apply_apply x

/-- Every finite stage of the balanced projection algebra is invariant under `complementEquiv`. -/
@[simp]
theorem complementEquiv_mem_stage_iff {n : ℕ} {x : BalancedProjectionAlgebra R τ} :
    complementEquiv τ x ∈ stage R τ n ↔ x ∈ stage R τ n := by
  have hle : stage R τ n ≤ (stage R τ n).comap (complementEquiv τ).toAlgHom :=
    stage_le_iff.2 fun i hi ↦ by simpa using sub_mem (Subalgebra.one_mem _) (e_mem_stage hi)
  exact ⟨fun hx ↦ by simpa using hle hx, fun hx ↦ hle hx⟩

/-- The complement automorphism restricted to `stage R τ n`. -/
def stageComplementEquiv (n : ℕ) : stage R τ n ≃ₐ[R] stage R τ n :=
  ((complementEquiv τ).subalgebraMap (stage R τ n)).trans
    (Subalgebra.equivOfEq _ _ <| Subalgebra.ext fun x ↦
      ⟨fun ⟨_, hy, h⟩ ↦ h ▸ (complementEquiv_mem_stage_iff τ).2 hy,
        fun hx ↦ ⟨complementEquiv τ x, (complementEquiv_mem_stage_iff τ).2 hx,
          complementEquiv_complementEquiv τ x⟩⟩)

@[simp]
theorem coe_stageComplementEquiv (n : ℕ) (x : stage R τ n) :
    (stageComplementEquiv (R := R) τ n x : BalancedProjectionAlgebra R τ) =
      complementEquiv τ x := (rfl)

@[simp]
theorem stageComplementEquiv_symm (n : ℕ) :
    (stageComplementEquiv (R := R) τ n).symm = stageComplementEquiv τ n :=
  AlgEquiv.ext fun x ↦ (stageComplementEquiv τ n).symm_apply_eq.mpr
    (Subtype.ext (complementEquiv_complementEquiv τ x).symm)

@[simp]
theorem stageComplementEquiv_stageComplementEquiv (n : ℕ) (x : stage R τ n) :
    stageComplementEquiv (R := R) τ n (stageComplementEquiv τ n x) = x :=
  Subtype.ext (complementEquiv_complementEquiv τ x)

variable {τ}

/-- Precomposing a scalar character `e i ↦ c` with `complementEquiv` yields the complementary
scalar character `e i ↦ 1 - c`. -/
@[simp]
theorem character_complementEquiv (c : R) (hc : IsIdempotentElem c)
    (x : BalancedProjectionAlgebra R τ) :
    character c hc (complementEquiv τ x) = character (1 - c) hc.one_sub x :=
  DFunLike.congr_fun
    (hom_ext (F := (character (τ := τ) c hc).comp (complementEquiv τ).toAlgHom)
      (G := character (1 - c) hc.one_sub) fun i ↦ by simp) x

end Complement

end TauCeti.BalancedProjectionAlgebra
