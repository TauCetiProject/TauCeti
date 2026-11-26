/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.OqSL2.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# The Hopf algebra structure on `O_q(SL₂)`

For a nonzero parameter `q`, the quantum coordinate algebra `OqSL2 q` is a Hopf algebra with the
matrix coproduct and counit of its fundamental matrix `u = [[a, b], [c, d]]`,

`Δ(u_ij) = ∑_k u_ik ⊗ u_kj`,  `ε(u_ij) = δ_ij`,

and the antipode `S(a) = d`, `S(b) = -q⁻¹ b`, `S(c) = -q c`, `S(d) = a`, the quantum adjugate
of `u`. The coproduct and counit descend through the presentation's universal property because the
relations of `OqSL2 q` are those of a quantum matrix with quantum determinant one; the antipode
descends as an algebra map into the opposite algebra, and the antipode identities reduce to the
two forms `a d - q b c = 1` and `d a - q⁻¹ b c = 1` of the quantum determinant relation.

## Main definitions

* `TauCeti.OqSL2.instBialgebra`, `TauCeti.OqSL2.instHopfAlgebra`: the Hopf algebra structure.

## Main results

* `TauCeti.OqSL2.comul_fundamentalMatrix`: `Δ(u_ij) = ∑_k u_ik ⊗ u_kj`.
* `TauCeti.OqSL2.counit_fundamentalMatrix`: `ε(u_ij) = δ_ij`.
* `TauCeti.OqSL2.comul_a` and its companions, `counit_a`, `antipode_a` and their companions: the
  values of the structure maps on the generators.

## References

* A. Klimyk and K. Schmüdgen, *Quantum Groups and Their Representations*, Springer, 1997,
  Section 4.1.2, for the Hopf structure of `O_q(SL(2))`.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Sections IV.6 and IV.7.
-/

public section

open scoped TensorProduct

namespace TauCeti.OqSL2

variable (q : ℂ) [Fact (q ≠ 0)]

private theorem q_ne_zero : q ≠ 0 := Fact.out

/- Each relation check below expands products of generators, brings every product of two
generators into the order `b a`, `c a`, `d b`, `d c`, `c b` with the defining relations (removing
`a d` and `d a` through the quantum determinant), pulls the scalars out of the tensor factors,
and compares coefficients. -/
local macro "normalize_oqSL2" : tactic => `(tactic| (
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_neg, mul_one, one_mul,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def,
    TensorProduct.tmul_add, TensorProduct.add_tmul, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
    TensorProduct.tmul_neg, TensorProduct.neg_tmul, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_smul,
    MulOpposite.unop_sub, MulOpposite.unop_one, MulOpposite.unop_neg,
    a_mul_b, a_mul_c, b_mul_d, c_mul_d, b_mul_c, a_mul_d, d_mul_a] <;>
  match_scalars <;> (try field_simp [q_ne_zero]) <;> ring))

private def comulTuple : GeneratorTuple q (OqSL2 q ⊗[ℂ] OqSL2 q) where
  a := a q ⊗ₜ[ℂ] a q + b q ⊗ₜ[ℂ] c q
  b := a q ⊗ₜ[ℂ] b q + b q ⊗ₜ[ℂ] d q
  c := c q ⊗ₜ[ℂ] a q + d q ⊗ₜ[ℂ] c q
  d := c q ⊗ₜ[ℂ] b q + d q ⊗ₜ[ℂ] d q
  a_mul_b := by normalize_oqSL2
  a_mul_c := by normalize_oqSL2
  b_mul_d := by normalize_oqSL2
  c_mul_d := by normalize_oqSL2
  b_mul_c := by normalize_oqSL2
  a_mul_d_sub_d_mul_a := by normalize_oqSL2
  a_mul_d_sub_b_mul_c := by normalize_oqSL2

/-- The matrix coproduct `Δ(u_ij) = ∑_k u_ik ⊗ u_kj` of the fundamental matrix. -/
def comul : OqSL2 q →ₐ[ℂ] OqSL2 q ⊗[ℂ] OqSL2 q := lift (comulTuple q)

@[local simp] private theorem comul_aAux :
    comul q (a q) = a q ⊗ₜ[ℂ] a q + b q ⊗ₜ[ℂ] c q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_bAux :
    comul q (b q) = a q ⊗ₜ[ℂ] b q + b q ⊗ₜ[ℂ] d q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_cAux :
    comul q (c q) = c q ⊗ₜ[ℂ] a q + d q ⊗ₜ[ℂ] c q := by
  simp [comul, comulTuple]

@[local simp] private theorem comul_dAux :
    comul q (d q) = c q ⊗ₜ[ℂ] b q + d q ⊗ₜ[ℂ] d q := by
  simp [comul, comulTuple]

private def counitTuple (q : ℂ) : GeneratorTuple q ℂ where
  a := 1
  b := 0
  c := 0
  d := 1
  a_mul_b := by simp
  a_mul_c := by simp
  b_mul_d := by simp
  c_mul_d := by simp
  b_mul_c := by simp
  a_mul_d_sub_d_mul_a := by simp
  a_mul_d_sub_b_mul_c := by simp

/-- The counit `ε(u_ij) = δ_ij` of the fundamental matrix. -/
def counit (q : ℂ) : OqSL2 q →ₐ[ℂ] ℂ := lift (counitTuple q)

omit [Fact (q ≠ 0)] in
@[local simp] private theorem counit_aAux : counit q (a q) = 1 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
@[local simp] private theorem counit_bAux : counit q (b q) = 0 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
@[local simp] private theorem counit_cAux : counit q (c q) = 0 := by simp [counit, counitTuple]

omit [Fact (q ≠ 0)] in
@[local simp] private theorem counit_dAux : counit q (d q) = 1 := by simp [counit, counitTuple]

/-- The bialgebra structure of `O_q(SL₂)`, with the matrix coproduct and counit. -/
noncomputable instance instBialgebra : Bialgebra ℂ (OqSL2 q) :=
  Bialgebra.ofAlgHom (comul q) (counit q)
    (by
      apply hom_ext <;>
        simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, comul_aAux,
          comul_bAux, comul_cAux, comul_dAux, map_add, Algebra.TensorProduct.map_tmul,
          AlgHom.coe_id, id_eq, Algebra.TensorProduct.assoc_tmul, TensorProduct.add_tmul,
          TensorProduct.tmul_add] <;>
        abel)
    (by apply hom_ext <;> simp)
    (by apply hom_ext <;> simp)

private noncomputable def antipodeTuple : GeneratorTuple q (OqSL2 q)ᵐᵒᵖ where
  a := MulOpposite.op (d q)
  b := MulOpposite.op (-q⁻¹ • b q)
  c := MulOpposite.op (-q • c q)
  d := MulOpposite.op (a q)
  a_mul_b := MulOpposite.unop_injective (by normalize_oqSL2)
  a_mul_c := MulOpposite.unop_injective (by normalize_oqSL2)
  b_mul_d := MulOpposite.unop_injective (by normalize_oqSL2)
  c_mul_d := MulOpposite.unop_injective (by normalize_oqSL2)
  b_mul_c := MulOpposite.unop_injective (by normalize_oqSL2)
  a_mul_d_sub_d_mul_a := MulOpposite.unop_injective (by normalize_oqSL2)
  a_mul_d_sub_b_mul_c := MulOpposite.unop_injective (by normalize_oqSL2)

/-- The antipode, the quantum adjugate `S(u) = [[d, -q⁻¹ b], [-q c, a]]`, as an algebra map into
the opposite algebra. -/
noncomputable def antipodeOp : OqSL2 q →ₐ[ℂ] (OqSL2 q)ᵐᵒᵖ := lift (antipodeTuple q)

@[local simp] private theorem antipodeOp_aAux :
    antipodeOp q (a q) = MulOpposite.op (d q) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_bAux :
    antipodeOp q (b q) = MulOpposite.op (-q⁻¹ • b q) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_cAux :
    antipodeOp q (c q) = MulOpposite.op (-q • c q) := by
  simp [antipodeOp, antipodeTuple]

@[local simp] private theorem antipodeOp_dAux :
    antipodeOp q (d q) = MulOpposite.op (a q) := by
  simp [antipodeOp, antipodeTuple]

/-- The Hopf algebra structure of `O_q(SL₂)`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra ℂ (OqSL2 q) :=
  -- Mathlib's constructor extends the antipode identities from the generators.
  HopfAlgebra.ofAntipodeOfAdjoin (antipodeOp q) (adjoin_range_generator q)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp only [LinearMap.rTensor_tmul, CoalgebraStruct.comul, LinearMap.coe_ofClass, comul_aAux,
          comul_bAux, comul_cAux, comul_dAux, map_add, LinearMap.coe_comp, LinearEquiv.coe_coe,
          MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap, Function.comp_apply,
          antipodeOp_aAux, antipodeOp_bAux, antipodeOp_cAux, antipodeOp_dAux, MulOpposite.unop_op,
          neg_smul, MulOpposite.op_neg, MulOpposite.op_smul, MulOpposite.unop_neg,
          MulOpposite.unop_smul, LinearMap.mul'_apply, CoalgebraStruct.counit, counit_aAux,
          counit_bAux, counit_cAux, counit_dAux, Algebra.linearMap_apply, map_one, map_zero] <;>
        normalize_oqSL2)
    (by
      rintro _ ⟨g, rfl⟩
      cases g <;>
        simp only [LinearMap.lTensor_tmul, CoalgebraStruct.comul, LinearMap.coe_ofClass, comul_aAux,
          comul_bAux, comul_cAux, comul_dAux, map_add, LinearMap.coe_comp, LinearEquiv.coe_coe,
          MulOpposite.coe_opLinearEquiv_symm, AlgHom.coe_toLinearMap, Function.comp_apply,
          antipodeOp_aAux, antipodeOp_bAux, antipodeOp_cAux, antipodeOp_dAux, MulOpposite.unop_op,
          neg_smul, MulOpposite.op_neg, MulOpposite.op_smul, MulOpposite.unop_neg,
          MulOpposite.unop_smul, LinearMap.mul'_apply, CoalgebraStruct.counit, counit_aAux,
          counit_bAux, counit_cAux, counit_dAux, Algebra.linearMap_apply, map_one, map_zero] <;>
        normalize_oqSL2)

/-- The coproduct of `a`. -/
@[simp] theorem comul_a : Coalgebra.comul (R := ℂ) (a q) = a q ⊗ₜ[ℂ] a q + b q ⊗ₜ[ℂ] c q :=
  comul_aAux q

/-- The coproduct of `b`. -/
@[simp] theorem comul_b : Coalgebra.comul (R := ℂ) (b q) = a q ⊗ₜ[ℂ] b q + b q ⊗ₜ[ℂ] d q :=
  comul_bAux q

/-- The coproduct of `c`. -/
@[simp] theorem comul_c : Coalgebra.comul (R := ℂ) (c q) = c q ⊗ₜ[ℂ] a q + d q ⊗ₜ[ℂ] c q :=
  comul_cAux q

/-- The coproduct of `d`. -/
@[simp] theorem comul_d : Coalgebra.comul (R := ℂ) (d q) = c q ⊗ₜ[ℂ] b q + d q ⊗ₜ[ℂ] d q :=
  comul_dAux q

/-- The counit of `a` is one. -/
@[simp] theorem counit_a : Coalgebra.counit (R := ℂ) (a q) = 1 := counit_aAux q

/-- The counit of `b` is zero. -/
@[simp] theorem counit_b : Coalgebra.counit (R := ℂ) (b q) = 0 := counit_bAux q

/-- The counit of `c` is zero. -/
@[simp] theorem counit_c : Coalgebra.counit (R := ℂ) (c q) = 0 := counit_cAux q

/-- The counit of `d` is one. -/
@[simp] theorem counit_d : Coalgebra.counit (R := ℂ) (d q) = 1 := counit_dAux q

/-- The antipode of `a` is `d`. -/
@[simp] theorem antipode_a : HopfAlgebra.antipode ℂ (a q) = d q := by
  simp [HopfAlgebra.antipode]

/-- The antipode of `b` is `-q⁻¹ b`. -/
@[simp] theorem antipode_b : HopfAlgebra.antipode ℂ (b q) = -q⁻¹ • b q := by
  simp [HopfAlgebra.antipode]

/-- The antipode of `c` is `-q c`. -/
@[simp] theorem antipode_c : HopfAlgebra.antipode ℂ (c q) = -q • c q := by
  simp [HopfAlgebra.antipode]

/-- The antipode of `d` is `a`. -/
@[simp] theorem antipode_d : HopfAlgebra.antipode ℂ (d q) = a q := by
  simp [HopfAlgebra.antipode]

/-- The coproduct of the fundamental matrix is the matrix coproduct
`Δ(u_ij) = ∑_k u_ik ⊗ u_kj`. -/
theorem comul_fundamentalMatrix (i j : Fin 2) :
    Coalgebra.comul (R := ℂ) (fundamentalMatrix q i j) =
      ∑ k, fundamentalMatrix q i k ⊗ₜ[ℂ] fundamentalMatrix q k j := by
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

/-- The counit of the fundamental matrix is the identity matrix, `ε(u_ij) = δ_ij`. -/
theorem counit_fundamentalMatrix (i j : Fin 2) :
    Coalgebra.counit (R := ℂ) (fundamentalMatrix q i j) = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;> simp

/-- The constructed coproduct agrees with the native coalgebra operation. -/
@[simp] theorem comul_apply (x : OqSL2 q) : comul q x = Coalgebra.comul x := (rfl)

/-- The constructed counit agrees with the native coalgebra operation. -/
@[simp] theorem counit_apply (x : OqSL2 q) : counit q x = Coalgebra.counit x := (rfl)

/-- The opposite-valued antipode agrees with the native linear antipode. -/
@[simp] theorem antipodeOp_apply (x : OqSL2 q) :
    antipodeOp q x = MulOpposite.op (HopfAlgebra.antipode ℂ x) := (rfl)

end TauCeti.OqSL2
