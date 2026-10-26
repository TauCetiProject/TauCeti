/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.RepresentationTheory.Spin.HalfSpin.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.Fock
-- Private: the involution eigenspaces and the half-spin dimensions are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.RepresentationTheory.Spin.Dimension

/-!
# Chirality of the Fock module of an oriented four-space

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and `J` an
orthogonal complex structure on `V`. The `i`-eigenspace `W` of the complexified `J` polarizes
`Q.baseChange ℂ`, and the normalized Fock action
`c(v) = √2 (ε(v^(1,0)) - ι(v^(0,1)))` makes the exterior algebra `⋀ W` a complex Clifford module
of `(V, Q)` (`TauCeti.AlmostComplexStructure.realFockAction`). This is the native model of the
spinor module of `V`.

On the other hand, the orientation of `V` defines the chirality element
`Γ = -c(e₁) c(e₂) c(e₃) c(e₄)` (`CliffordAlgebra.chirality`), whose `±1` eigenspaces are the
half-spinors `W±` of the geometric model. This file compares the two when the orientation is the
one induced by `J`, that is, when some positively oriented orthonormal basis has the form
`(u₁, J u₁, u₂, J u₂)`: then **`Γ` acts on `⋀ W` by exterior parity**, the grade involution of
the exterior algebra. Consequently the positive half-spinors are the even forms
`⋀⁰ W ⊕ ⋀² W`, which contain the vacuum `1`, the negative half-spinors are the odd forms
`⋀¹ W`, and both have complex dimension two. Every orthogonal complex structure admits such an
adapted basis (`TauCeti.AlmostComplexStructure.exists_adapted_orthonormalBasis`), so one of the
two orientations of `V` is always of this kind.

## Main results

* `TauCeti.AlmostComplexStructure.realFockAction_chirality`: `Γ` acts on `⋀ W` by the grade
  involution `CliffordAlgebra.involute`.
* `TauCeti.AlmostComplexStructure.positiveHalfSpinors_realFockAction` and
  `TauCeti.AlmostComplexStructure.eigenspace_realFockAction_chirality_neg_one`: the `+1` and `-1`
  eigenspaces of `Γ` are the even and odd half-spin summands `TauCeti.spinPlus` and
  `TauCeti.spinMinus`.
* `TauCeti.AlmostComplexStructure.finrank_positiveHalfSpinors_realFockAction` and
  `TauCeti.AlmostComplexStructure.finrank_eigenspace_realFockAction_chirality_neg_one`: both
  half-spinor spaces have complex dimension two.

## Implementation notes

The vacuum is fixed by `Γ` because `c(u) c(J u) 1 = i Q(u)` for every real vector `u`. The
identity then propagates along exterior multiplication: a vector of `W` acts by `√2` times
exterior multiplication and anticommutes with `Γ`, as every complex vector does.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace TauCeti.AlmostComplexStructure

open CliffordAlgebra Module
open scoped RealInnerProductSpace TensorProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (J : AlmostComplexStructure V) (hQJ : ∀ v, Q (J v) = Q v) (hQnd : Q.Nondegenerate)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-! ### The chirality element -/

include hQ in
/-- `Γ` anticommutes with exterior multiplication by a vector of `W`. -/
private theorem realFockAction_chirality_ι_mul (x : (J.spinPolarizationData hQJ hQnd).W)
    (s : ExteriorAlgebra ℂ (J.spinPolarizationData hQJ hQnd).W) :
    J.realFockAction hQJ hQnd (chirality Q o) (ExteriorAlgebra.ι ℂ x * s) =
      -(ExteriorAlgebra.ι ℂ x * J.realFockAction hQJ hQnd (chirality Q o) s) := by
  have h := congr(J.fockAction hQJ hQnd $(ofBaseChangeAux_chirality_mul_ι o hQ ℂ (x : ℂ ⊗[ℝ] V)) s)
  simp only [map_mul, map_neg, Module.End.mul_apply, LinearMap.neg_apply,
    J.fockAction_ι_coe_W hQJ hQnd, ← realFockAction_apply, LinearMap.smul_apply,
    SpinPolarizationData.wedge_apply, map_smul, ← smul_neg] at h
  exact smul_right_injective _ (r := (Real.sqrt 2 : ℂ)) (by norm_num) h

variable {o}

include hQ in
/-- **Chirality is exterior parity on the Fock module.** If the orientation of `V` is induced by
`J`, in the sense that some positively oriented orthonormal basis has the form
`(u₁, J u₁, u₂, J u₂)`, then the chirality element `Γ` acts on `⋀ W` by the grade involution. -/
theorem realFockAction_chirality (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    J.realFockAction hQJ hQnd (chirality Q o) = involute.toLinearMap := by
  have hQb (i : Fin 4) : Q (b i) = -1 := by rw [hQ, b.orthonormal.1 i]; norm_num
  have hvac : J.realFockAction hQJ hQnd (chirality Q o) 1 = 1 := by
    rw [chirality_eq o hQ b hb, hb₁, hb₃, mul_assoc, map_neg, map_mul]
    simp only [LinearMap.neg_apply, Module.End.mul_apply, realFockAction_ι_mul_ι_apply_apply_one,
      map_smul, hQb]
    match_scalars
    norm_num
  refine LinearMap.ext fun s ↦ ?_
  induction s using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one, hvac]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | ι_mul x m hx => simp [J.realFockAction_chirality_ι_mul o hQ hQJ hQnd, hx]

include hQ in
/-- **The positive half-spinors of the Fock module are the even forms** `⋀⁰ W ⊕ ⋀² W`, for the
orientation induced by `J`. -/
theorem positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    positiveHalfSpinors o (J.realFockAction hQJ hQnd) =
      spinPlus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [mem_positiveHalfSpinors, J.realFockAction_chirality hQ hQJ hQnd b hb hb₁ hb₃,
    AlgHom.toLinearMap_apply, involute_eq_self_iff, mem_spinPlus]

include hQ in
/-- **The negative half-spinors of the Fock module are the odd forms** `⋀¹ W`, for the
orientation induced by `J`. -/
theorem eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1) =
      spinMinus (Q.baseChange ℂ) (J.spinPolarizationData hQJ hQnd) := by
  ext s
  rw [Module.End.mem_eigenspace_iff, J.realFockAction_chirality hQ hQJ hQnd b hb hb₁ hb₃,
    AlgHom.toLinearMap_apply, neg_one_smul, involute_eq_neg_iff, mem_spinMinus]

/-- The isotropic summand `W` of a complex structure on a four-space has complex dimension two. -/
private theorem finrank_spinPolarizationData_W :
    finrank ℂ (J.spinPolarizationData hQJ hQnd).W = 2 :=
  (J.spinPolarizationData hQJ hQnd).finrank_W_eq_of_finrank_eq_two_mul
    (by rw [finrank_baseChange, Fact.out (p := finrank ℝ V = 4)])

private theorem spinPolarizationData_W_ne_bot : (J.spinPolarizationData hQJ hQnd).W ≠ ⊥ := by
  intro h
  have h₂ := J.finrank_spinPolarizationData_W hQJ hQnd
  rw [h, finrank_bot] at h₂
  exact absurd h₂ (by norm_num)

include hQ in
/-- The positive half-spinors of the Fock module have complex dimension two. -/
theorem finrank_positiveHalfSpinors_realFockAction (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (positiveHalfSpinors o (J.realFockAction hQJ hQnd)) = 2 := by
  rw [J.positiveHalfSpinors_realFockAction hQ hQJ hQnd b hb hb₁ hb₃,
    finrank_spinPlus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd]
  norm_num

include hQ in
/-- The negative half-spinors of the Fock module have complex dimension two. -/
theorem finrank_eigenspace_realFockAction_chirality_neg_one (b : OrthonormalBasis (Fin 4) ℝ V)
    (hb : b.toBasis.orientation = o) (hb₁ : b 1 = J (b 0)) (hb₃ : b 3 = J (b 2)) :
    finrank ℂ (Module.End.eigenspace (J.realFockAction hQJ hQnd (chirality Q o)) (-1)) = 2 := by
  rw [J.eigenspace_realFockAction_chirality_neg_one hQ hQJ hQnd b hb hb₁ hb₃,
    finrank_spinMinus _ (J.spinPolarizationData_W_ne_bot hQJ hQnd),
    J.finrank_spinPolarizationData_W hQJ hQnd]
  norm_num

end TauCeti.AlmostComplexStructure
