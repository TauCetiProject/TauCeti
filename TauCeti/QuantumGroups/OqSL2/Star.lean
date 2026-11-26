/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Star
public import TauCeti.Algebra.Star.ConjOpposite
public import TauCeti.QuantumGroups.OqSL2.Hopf
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# The compact real form `SU_q(2)` of `O_q(SL₂)`

For a real nonzero parameter `q`, the quantum coordinate algebra `OqSL2 q` carries the star
structure of the compact quantum group `SU_q(2)`: the conjugate-linear antimultiplicative
involution with

`a* = d`, `b* = -q c`, `c* = -q⁻¹ b`, `d* = a`.

In terms of `a` and `c` alone the fundamental matrix becomes `u = [[a, -q c*], [c, a*]]`, and the
defining relations of `OqSL2 q` become the five relations

`a* a + c* c = 1`, `a a* + q² c* c = 1`, `c* c = c c*`, `a c = q c a`, `a c* = q c* a`

of `SU_q(2)`. These five relations hold for two elements `α, γ` of a complex star algebra exactly
when the matrix `[[α, -q γ*], [γ, α*]]` is unitary (`TauCeti.OqSL2.isSUq2Pair_iff_mem_unitary`),
and star algebra maps out of `OqSL2 q` are exactly such pairs (`TauCeti.OqSL2.starLiftEquiv`): the
unitary-matrix presentation and the generator-relation presentation of `SU_q(2)` agree.

The coproduct is a star homomorphism, so `OqSL2 q` is a Hopf star algebra
(`TauCeti.OqSL2.instStarCoalgebra`). Its antipode is the matrix adjoint of the fundamental
matrix, `S(u_ij) = u_ji*` (`TauCeti.OqSL2.antipode_fundamentalMatrix`). In terms of `a` and `c`
the structure maps are `S(a) = a*`, `S(c*) = -q⁻¹ c*` (`TauCeti.OqSL2.antipode_a_eq_star`,
`TauCeti.OqSL2.antipode_star_c`), `S(c) = -q c` (`TauCeti.OqSL2.antipode_c`), and
`Δ(a) = a ⊗ a - q c* ⊗ c`, `Δ(c) = c ⊗ a + a* ⊗ c` (`TauCeti.OqSL2.comul_a_eq_star`,
`TauCeti.OqSL2.comul_c_eq_star`).

## Main definitions

* `TauCeti.OqSL2.instStarRing`: for real nonzero `q`, the star structure of `SU_q(2)`.
* `TauCeti.OqSL2.IsSUq2Pair`: the five relations of `SU_q(2)` for a pair of elements of a complex
  star algebra.
* `TauCeti.OqSL2.starLift`, `TauCeti.OqSL2.starLiftEquiv`: the universal property of `OqSL2 q`
  as a complex star algebra presented by `a` and `c`.

## Main results

* `TauCeti.OqSL2.isSUq2Pair_iff_mem_unitary`: the five relations hold exactly when
  `[[α, -q γ*], [γ, α*]]` is unitary.
* `TauCeti.OqSL2.fundamentalMatrix_mem_unitary`: the fundamental matrix is unitary.
* `TauCeti.OqSL2.instStarCoalgebra`: the coproduct is a star homomorphism.
* `TauCeti.OqSL2.antipode_fundamentalMatrix`: `S(u_ij) = u_ji*`.
* `TauCeti.OqSL2.comul_a_eq_star`, `TauCeti.OqSL2.comul_c_eq_star`: the coproduct of `a` and `c`
  in terms of `a`, `c` and their adjoints.

## Implementation notes

A conjugate-linear antimultiplicative map out of `OqSL2 q` is obtained from the universal property
of the presentation as a complex algebra map into the opposite algebra on which complex scalars
act through complex conjugation, `TauCeti.ConjOpposite`, as for `TauCeti.UqSl2.instStarRing`.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Sections 4.1.4 and 4.4, for the real form `O_q(SU(2))`.
* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Section 6.2, for the
  compact quantum group `SU_q(2)` and its five relations.
* S. L. Woronowicz, *Twisted SU(2) group. An example of a non-commutative differential calculus*,
  Publ. RIMS 23 (1987), for the unitary-matrix presentation.
-/

public section

open HopfAlgebra

namespace TauCeti.OqSL2

/-! ### The five relations of `SU_q(2)` -/

section Pair

variable {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]

/-- The five defining relations of `SU_q(2)` for a pair `α, γ` of elements of a complex star
algebra: `α* α + γ* γ = 1`, `α α* + q² γ* γ = 1`, `γ* γ = γ γ*`, `α γ = q γ α` and
`α γ* = q γ* α`. For real `q` they say that `[[α, -q γ*], [γ, α*]]` is unitary
(`TauCeti.OqSL2.isSUq2Pair_iff_mem_unitary`). -/
structure IsSUq2Pair (q : ℂ) (α γ : B) : Prop where
  /-- The first column of `[[α, -q γ*], [γ, α*]]` is a unit vector: `α* α + γ* γ = 1`. -/
  star_mul_self_add_star_mul_self : star α * α + star γ * γ = 1
  /-- The first row of `[[α, -q γ*], [γ, α*]]` is a unit vector: `α α* + q² γ* γ = 1`. -/
  mul_star_add_sq_smul_star_mul_self : α * star α + q ^ 2 • (star γ * γ) = 1
  /-- `γ` is normal: `γ* γ = γ γ*`. -/
  star_mul_self_eq_mul_star : star γ * γ = γ * star γ
  /-- `α γ = q γ α`. -/
  mul_eq_smul_mul : α * γ = q • (γ * α)
  /-- `α γ* = q γ* α`. -/
  mul_star_eq_smul_star_mul : α * star γ = q • (star γ * α)

/-- For real `q`, the star of the relation `α γ = q γ α` is `γ* α* = q α* γ*`. -/
theorem IsSUq2Pair.star_mul_star_eq_smul_star_mul_star [StarModule ℂ B] {q : ℂ} {α γ : B}
    (h : IsSUq2Pair q α γ) (hq : IsSelfAdjoint q) :
    star γ * star α = q • (star α * star γ) := by
  simpa [star_mul, hq.star_eq] using congrArg star h.mul_eq_smul_mul

/-- For real `q`, the star of the relation `α γ* = q γ* α` is `γ α* = q α* γ`. -/
theorem IsSUq2Pair.mul_star_eq_smul_star_mul' [StarModule ℂ B] {q : ℂ} {α γ : B}
    (h : IsSUq2Pair q α γ) (hq : IsSelfAdjoint q) : γ * star α = q • (star α * γ) := by
  simpa [star_mul, hq.star_eq] using congrArg star h.mul_star_eq_smul_star_mul

/-- The matrix `[[α, -q γ*], [γ, α*]]` is unitary exactly when `α` and `γ` satisfy the five
relations of `SU_q(2)`, for every real `q`. -/
theorem isSUq2Pair_iff_mem_unitary [StarModule ℂ B] {q : ℂ} (hq : IsSelfAdjoint q) (α γ : B) :
    IsSUq2Pair q α γ ↔ !![α, -q • star γ; γ, star α] ∈ unitary (Matrix (Fin 2) (Fin 2) B) := by
  have hq' : star q = q := hq.star_eq
  rw [Unitary.mem_iff, Matrix.star_eq_conjTranspose, Matrix.one_fin_two, ← Matrix.ext_iff,
    ← Matrix.ext_iff]
  simp only [Matrix.conjTranspose_apply, Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, star_star, star_smul, star_neg, hq', neg_smul,
    smul_neg, mul_neg, neg_mul, smul_mul_assoc, mul_smul_comm, neg_neg, smul_smul]
  constructor
  · intro h
    have h₄' := h.star_mul_star_eq_smul_star_mul_star hq
    have h₅' := h.mul_star_eq_smul_star_mul' hq
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    refine ⟨⟨⟨h₁, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h₄', neg_add_cancel]
    · rw [h₄, neg_add_cancel]
    · rw [← h₃, ← sq, add_comm]
      exact h₂
    · rw [← sq]
      exact h₂
    · rw [h₅, add_neg_cancel]
    · rw [h₅', add_neg_cancel]
    · rw [← h₃, add_comm]
      exact h₁
  · rintro ⟨⟨⟨h₁, -⟩, h₄, -⟩, ⟨h₂, h₅⟩, -, h₈⟩
    refine ⟨h₁, by rw [sq]; exact h₂, ?_, (neg_add_eq_zero.mp h₄).symm, add_neg_eq_zero.mp h₅⟩
    have h := h₁.trans h₈.symm
    rw [add_comm (γ * star γ)] at h
    exact add_left_cancel h

/-- The five relations of `SU_q(2)` are preserved by star algebra maps. -/
theorem IsSUq2Pair.map {C : Type*} [Ring C] [StarRing C] [Algebra ℂ C]
    {q : ℂ} {α γ : B} (h : IsSUq2Pair q α γ) (f : B →⋆ₐ[ℂ] C) : IsSUq2Pair q (f α) (f γ) where
  star_mul_self_add_star_mul_self := by
    simpa [map_star] using congrArg f h.star_mul_self_add_star_mul_self
  mul_star_add_sq_smul_star_mul_self := by
    simpa [map_star] using congrArg f h.mul_star_add_sq_smul_star_mul_self
  star_mul_self_eq_mul_star := by simpa [map_star] using congrArg f h.star_mul_self_eq_mul_star
  mul_eq_smul_mul := by simpa using congrArg f h.mul_eq_smul_mul
  mul_star_eq_smul_star_mul := by simpa [map_star] using congrArg f h.mul_star_eq_smul_star_mul

end Pair

variable (q : ℂ)

open ConjOpposite

/-! ### The star structure -/

variable [Fact (IsSelfAdjoint q)] [Fact (q ≠ 0)]

omit [Fact (q ≠ 0)] in
private theorem star_q : star q = q := (Fact.out : IsSelfAdjoint q).star_eq

/- Each relation check below brings every product of two generators into the order `b a`, `c a`,
`d b`, `d c`, `c b` with the defining relations (removing `a d` and `d a` through the quantum
determinant) and compares coefficients. -/
local macro "normalize_oqSL2" : tactic => `(tactic| (
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_neg, mul_one, one_mul,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul,
    a_mul_b, a_mul_c, b_mul_d, c_mul_d, b_mul_c, a_mul_d, d_mul_a] <;>
  match_scalars <;> (try field_simp [q_ne_zero]) <;> ring))

/-- The images of the generators under the star structure, as a generator tuple in the conjugate
opposite algebra. -/
private noncomputable def starTuple : GeneratorTuple q (ConjOpposite (OqSL2 q)) where
  a := toConj (d q)
  b := toConj (-q • c q)
  c := toConj (-q⁻¹ • b q)
  d := toConj (a q)
  a_mul_b := ofConj_injective (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_q]; normalize_oqSL2)
  a_mul_c := ofConj_injective (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_q]; normalize_oqSL2)
  b_mul_d := ofConj_injective (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_q]; normalize_oqSL2)
  c_mul_d := ofConj_injective (by
    simp only [ofConj_mul, ofConj_smul, ofConj_toConj, star_q]; normalize_oqSL2)
  b_mul_c := ofConj_injective (by
    simp only [ofConj_mul, ofConj_toConj]; normalize_oqSL2)
  a_mul_d_sub_d_mul_a := ofConj_injective (by
    simp only [ofConj_mul, ofConj_sub, ofConj_smul, ofConj_toConj, star_sub, star_inv₀, star_q]
    normalize_oqSL2)
  a_mul_d_sub_b_mul_c := ofConj_injective (by
    simp only [ofConj_mul, ofConj_sub, ofConj_smul, ofConj_toConj, ofConj_one, star_q]
    normalize_oqSL2)

/-- The conjugate-linear antimultiplicative map underlying the star structure. -/
private noncomputable def starFun (x : OqSL2 q) : OqSL2 q := ofConj (lift (starTuple q) x)

private theorem starFun_mul (x y : OqSL2 q) : starFun q (x * y) = starFun q y * starFun q x := by
  simp only [starFun, map_mul, ofConj_mul]

private theorem starFun_add (x y : OqSL2 q) : starFun q (x + y) = starFun q x + starFun q y := by
  simp only [starFun, map_add, ofConj_add]

private theorem starFun_neg (x : OqSL2 q) : starFun q (-x) = -starFun q x := by
  simp only [starFun, map_neg, ofConj_neg]

private theorem starFun_smul (r : ℂ) (x : OqSL2 q) : starFun q (r • x) = star r • starFun q x := by
  simp only [starFun, map_smul, ofConj_smul]

private theorem starFun_algebraMap (r : ℂ) :
    starFun q (algebraMap ℂ (OqSL2 q) r) = algebraMap ℂ (OqSL2 q) (star r) := by
  simp only [starFun, AlgHom.commutes, ofConj_algebraMap]

private theorem starFun_a : starFun q (a q) = d q := by
  simp [starFun, starTuple, ofConj_toConj]

private theorem starFun_b : starFun q (b q) = -q • c q := by
  simp [starFun, starTuple, ofConj_toConj]

private theorem starFun_c : starFun q (c q) = -q⁻¹ • b q := by
  simp [starFun, starTuple, ofConj_toConj]

private theorem starFun_d : starFun q (d q) = a q := by
  simp [starFun, starTuple, ofConj_toConj]

/-- For real nonzero `q`, the star structure of `SU_q(2)` on `OqSL2 q`: the conjugate-linear
antimultiplicative involution with `a* = d`, `b* = -q c`, `c* = -q⁻¹ b` and `d* = a`. -/
@[no_expose]
noncomputable instance instStarRing : StarRing (OqSL2 q) where
  star := starFun q
  star_involutive x := by
    induction x using OqSL2.induction with
    | generator g =>
      cases g <;>
        simp [starFun_a, starFun_b, starFun_c, starFun_d, starFun_neg, starFun_smul, star_q,
          star_inv₀, smul_smul, q_ne_zero]
    | algebraMap r => simp [starFun_algebraMap]
    | add x y hx hy => simp only [starFun_add, hx, hy]
    | mul x y hx hy => simp only [starFun_mul, hx, hy]
  star_mul := starFun_mul q
  star_add := starFun_add q

/-- The star structure of `SU_q(2)` is conjugate-linear. -/
instance instStarModule : StarModule ℂ (OqSL2 q) where
  star_smul := starFun_smul q

/-- The star structure is `starFun`, by definition of the instance. -/
private theorem star_eq_starFun (x : OqSL2 q) : star x = starFun q x := rfl

/-- `a* = d`. -/
@[simp] theorem star_a : star (a q) = d q := starFun_a q

/-- `b* = -q c`. -/
@[simp] theorem star_b : star (b q) = -q • c q := starFun_b q

/-- `c* = -q⁻¹ b`. -/
@[simp] theorem star_c : star (c q) = -q⁻¹ • b q := starFun_c q

/-- `d* = a`. -/
@[simp] theorem star_d : star (d q) = a q := starFun_d q

/-- The entry `b` is `-q c*`. -/
theorem b_eq_neg_smul_star_c : b q = -q • star (c q) := by
  simp [smul_smul, q_ne_zero]

/-- In terms of `a` and `c`, the fundamental matrix is `u = [[a, -q c*], [c, a*]]`. -/
theorem fundamentalMatrix_eq :
    fundamentalMatrix q = !![a q, -q • star (c q); c q, star (a q)] := by
  rw [← b_eq_neg_smul_star_c, star_a, fundamentalMatrix_def]

/-- The generators `a` and `c` satisfy the five relations of `SU_q(2)`. -/
theorem isSUq2Pair_a_c : IsSUq2Pair q (a q) (c q) where
  star_mul_self_add_star_mul_self := by simp only [star_a, star_c]; normalize_oqSL2
  mul_star_add_sq_smul_star_mul_self := by simp only [star_a, star_c]; normalize_oqSL2
  star_mul_self_eq_mul_star := by simp only [star_c]; normalize_oqSL2
  mul_eq_smul_mul := a_mul_c
  mul_star_eq_smul_star_mul := by simp only [star_c]; normalize_oqSL2

/-- The fundamental matrix `u = [[a, -q c*], [c, a*]]` of `SU_q(2)` is unitary. -/
theorem fundamentalMatrix_mem_unitary :
    fundamentalMatrix q ∈ unitary (Matrix (Fin 2) (Fin 2) (OqSL2 q)) := by
  rw [fundamentalMatrix_eq]
  exact (isSUq2Pair_iff_mem_unitary (Fact.out : IsSelfAdjoint q) _ _).1 (isSUq2Pair_a_c q)

/-! ### The universal property as a star algebra -/

section StarLift

variable {q} {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

/-- The generator tuple determined by a pair satisfying the five relations of `SU_q(2)`, with
`b = -q γ*` and `d = α*`. -/
private def pairTuple {α γ : B} (h : IsSUq2Pair q α γ) : GeneratorTuple q B where
  a := α
  b := -q • star γ
  c := γ
  d := star α
  a_mul_b := by
    rw [mul_smul_comm, h.mul_star_eq_smul_star_mul, smul_mul_assoc]; module
  a_mul_c := h.mul_eq_smul_mul
  b_mul_d := by
    rw [smul_mul_assoc, h.star_mul_star_eq_smul_star_mul_star Fact.out, mul_smul_comm]; module
  c_mul_d := h.mul_star_eq_smul_star_mul' Fact.out
  b_mul_c := by rw [smul_mul_assoc, mul_smul_comm, h.star_mul_self_eq_mul_star]
  a_mul_d_sub_d_mul_a := by
    have hq : (q - q⁻¹) * -q = 1 - q ^ 2 := by
      field_simp [q_ne_zero]
      ring
    rw [eq_sub_of_add_eq h.star_mul_self_add_star_mul_self,
      eq_sub_of_add_eq h.mul_star_add_sq_smul_star_mul_self, smul_mul_assoc, smul_smul, hq]
    module
  a_mul_d_sub_b_mul_c := by
    rw [smul_mul_assoc, smul_smul, ← h.mul_star_add_sq_smul_star_mul_self]; module

private theorem lift_pairTuple_star {α γ : B} (h : IsSUq2Pair q α γ) (x : OqSL2 q) :
    lift (pairTuple h) (star x) = star (lift (pairTuple h) x) := by
  induction x using OqSL2.induction with
  | generator g =>
    cases g <;> simp [pairTuple, star_q, smul_smul, q_ne_zero]
  | algebraMap r => simp [← algebraMap_star_comm]
  | add x y hx hy => simp only [star_add, map_add, hx, hy]
  | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

/-- The star algebra map out of `OqSL2 q` sending `a` and `c` to a pair `α, γ` satisfying the
five relations of `SU_q(2)`. -/
noncomputable def starLift {α γ : B} (h : IsSUq2Pair q α γ) : OqSL2 q →⋆ₐ[ℂ] B where
  toAlgHom := lift (pairTuple h)
  map_star' := lift_pairTuple_star h

/-- `starLift h` sends `a` to `α`. -/
@[simp] theorem starLift_a {α γ : B} (h : IsSUq2Pair q α γ) : starLift h (a q) = α := by
  simp [starLift, pairTuple]

/-- `starLift h` sends `b` to `-q γ*`. -/
@[simp] theorem starLift_b {α γ : B} (h : IsSUq2Pair q α γ) :
    starLift h (b q) = -q • star γ := by
  simp [starLift, pairTuple]

/-- `starLift h` sends `c` to `γ`. -/
@[simp] theorem starLift_c {α γ : B} (h : IsSUq2Pair q α γ) : starLift h (c q) = γ := by
  simp [starLift, pairTuple]

/-- `starLift h` sends `d` to `α*`. -/
@[simp] theorem starLift_d {α γ : B} (h : IsSUq2Pair q α γ) : starLift h (d q) = star α := by
  simp [starLift, pairTuple]

omit [StarModule ℂ B] in
/-- Two star algebra maps out of `OqSL2 q` agreeing on `a` and `c` are equal. -/
@[ext high]
theorem starAlgHom_ext {f g : OqSL2 q →⋆ₐ[ℂ] B} (ha : f (a q) = g (a q))
    (hc : f (c q) = g (c q)) : f = g := by
  have hb : f (b q) = g (b q) := by
    rw [b_eq_neg_smul_star_c, map_smul, map_smul, map_star, map_star, hc]
  have hd : f (d q) = g (d q) := by
    rw [← star_a, map_star, map_star, ha]
  have key : f.toAlgHom = g.toAlgHom := hom_ext ha hb hc hd
  exact StarAlgHom.ext fun x => DFunLike.congr_fun key x

/-- The universal property of `SU_q(2)`: star algebra maps out of `OqSL2 q` correspond to pairs
satisfying its five relations, through the images of `a` and `c`. -/
noncomputable def starLiftEquiv :
    {p : B × B // IsSUq2Pair q p.1 p.2} ≃ (OqSL2 q →⋆ₐ[ℂ] B) where
  toFun p := starLift p.property
  invFun f := ⟨(f (a q), f (c q)), (isSUq2Pair_a_c q).map f⟩
  left_inv p := by ext <;> simp
  right_inv f := by ext <;> simp

/-- The star algebra map attached to a pair is `starLift`. -/
@[simp]
theorem starLiftEquiv_apply (p : {p : B × B // IsSUq2Pair q p.1 p.2}) :
    starLiftEquiv p = starLift p.property := (rfl)

/-- The pair attached to a star algebra map records its values on `a` and `c`. -/
@[simp]
theorem starLiftEquiv_symm_apply (f : OqSL2 q →⋆ₐ[ℂ] B) :
    starLiftEquiv.symm f = ⟨(f (a q), f (c q)), (isSUq2Pair_a_c q).map f⟩ := (rfl)

end StarLift

/-! ### Compatibility with the Hopf structure -/

/-- For real nonzero `q`, the coproduct of `OqSL2 q` is a star homomorphism, so `SU_q(2)` is a
Hopf star algebra. -/
instance instStarCoalgebra : StarCoalgebra ℂ (OqSL2 q) where
  comul_star x := by
    induction x using OqSL2.induction with
    | generator g =>
      cases g <;>
        simp only [star_a, star_b, star_c, star_d, comul_a, comul_b, comul_c, comul_d, star_add,
          TensorProduct.star_tmul, map_smul, TensorProduct.tmul_smul,
          ← TensorProduct.smul_tmul'] <;>
        match_scalars <;> field_simp [q_ne_zero]
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y hx hy => simp only [star_mul, Bialgebra.comul_mul, hx, hy]

/-- The antipode of `SU_q(2)` is the matrix adjoint of its fundamental matrix:
`S(u_ij) = u_ji*`. -/
theorem antipode_fundamentalMatrix (i j : Fin 2) :
    antipode ℂ (fundamentalMatrix q i j) = star (fundamentalMatrix q j i) := by
  fin_cases i <;> fin_cases j <;> simp

/-- The antipode of `a` is `a*`. -/
theorem antipode_a_eq_star : antipode ℂ (a q) = star (a q) := by
  rw [antipode_a, star_a]

/-- The antipode of `c*` is `-q⁻¹ c*`. -/
theorem antipode_star_c : antipode ℂ (star (c q)) = -q⁻¹ • star (c q) := by
  rw [star_c, map_smul, antipode_b]

/-- In terms of `a` and `c`, the coproduct of `a` is `Δ(a) = a ⊗ a - q c* ⊗ c`. -/
theorem comul_a_eq_star :
    Coalgebra.comul (R := ℂ) (a q) = a q ⊗ₜ[ℂ] a q - (q • star (c q)) ⊗ₜ[ℂ] c q := by
  rw [comul_a, b_eq_neg_smul_star_c, neg_smul, TensorProduct.neg_tmul, sub_eq_add_neg]

/-- In terms of `a` and `c`, the coproduct of `c` is `Δ(c) = c ⊗ a + a* ⊗ c`. -/
theorem comul_c_eq_star :
    Coalgebra.comul (R := ℂ) (c q) = c q ⊗ₜ[ℂ] a q + star (a q) ⊗ₜ[ℂ] c q := by
  rw [comul_c, star_a]

end TauCeti.OqSL2
