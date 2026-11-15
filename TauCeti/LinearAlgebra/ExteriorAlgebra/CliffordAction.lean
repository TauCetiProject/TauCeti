/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.BaseChange
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorAlgebra.BaseChange
-- Private: the transport of the involution and the grading along `equivExterior`, the
-- comparison of the two base-change maps, and the computation of `LinearMap.tensorProductEnd`
-- are used only inside proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# The Clifford action on the exterior algebra

Let `Q` be a quadratic form on an `R`-module `M`, with `2` invertible in `R`. Mathlib's
`CliffordAlgebra.equivExterior` identifies `CliffordAlgebra Q` with `ExteriorAlgebra R M` as
modules. Transporting left multiplication along it makes the exterior algebra a module over the
Clifford algebra, `CliffordAlgebra.exteriorAction Q`, for which `equivExterior` is an isomorphism
from the regular module (`CliffordAlgebra.exteriorAction_apply_one`). A vector acts by exterior
multiplication minus contraction,

  `c(m) ω = m ∧ ω - ι(B m) ω`,  `B = QuadraticMap.associated (-Q)`,

(`CliffordAlgebra.exteriorAction_ι`). For a real inner product space and the geometric form
`Q v = -‖v‖²`, `B` is the inner product, so this is the action `c(v) = ε(v) - ι(v)` of the
Clifford algebra on differential forms at a point.

The action is graded for the exterior parity: the grade involution of the exterior algebra
intertwines `c(a)` with `c(involute a)`, and an element of parity `i` sends forms of parity `j` to
forms of parity `i + j`. In particular even elements preserve the even and odd forms and odd
elements, such as vectors, exchange them.

After extension of scalars to a commutative `R`-algebra `A`, the Clifford algebra
`CliffordAlgebra (Q.baseChange A)` acts `A`-linearly on `A ⊗[R] ExteriorAlgebra R M`
(`CliffordAlgebra.baseChangeExteriorAction`), through Mathlib's comparison
`CliffordAlgebra.toBaseChange` and the factorwise action on the tensor product. For `A = ℂ` this
is the Clifford action on complex-valued forms. When `2` is also invertible in `A`,
`ExteriorAlgebra.baseChangeEquiv` identifies the base-changed Chevalley map with
`CliffordAlgebra.equivExterior (Q.baseChange A)` and intertwines `baseChangeExteriorAction` with
`exteriorAction (Q.baseChange A)`.

## Main definitions

* `CliffordAlgebra.exteriorAction Q`: the action of `CliffordAlgebra Q` on `ExteriorAlgebra R M`.
* `CliffordAlgebra.baseChangeExteriorAction A Q`: the action of `CliffordAlgebra (Q.baseChange A)`
  on `A ⊗[R] ExteriorAlgebra R M`.

## Main results

* `CliffordAlgebra.exteriorAction_ι`: a vector acts by exterior multiplication minus contraction.
* `CliffordAlgebra.exteriorAction_apply_one`: acting on `1` is `CliffordAlgebra.equivExterior`.
* `CliffordAlgebra.exteriorAction_involute`: the action commutes with the grade involutions.
* `CliffordAlgebra.exteriorAction_mem_evenOdd`: the action is `ℤ/2`-graded.
* `CliffordAlgebra.baseChangeExteriorAction_ofBaseChangeAux_tmul` and
  `CliffordAlgebra.baseChangeExteriorAction_ι_tmul`: the extended action on pure tensors.
* `CliffordAlgebra.equivExterior_ofBaseChangeAux`, `CliffordAlgebra.equivExterior_baseChange`,
  `CliffordAlgebra.equivExterior_symm_baseChangeEquiv`, and
  `CliffordAlgebra.baseChangeEquiv_baseChangeExteriorAction`: compatibility of `equivExterior` and
  `exteriorAction` with `ExteriorAlgebra.baseChangeEquiv` when `2` is invertible in `A`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapters I and II.
-/

public section

noncomputable section

open scoped TensorProduct

namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]

section Action

variable (Q : QuadraticForm R M)

/-- The action of `CliffordAlgebra Q` on the exterior algebra: left multiplication transported
along `CliffordAlgebra.equivExterior`. A vector `m` acts by `ω ↦ m ∧ ω - ι(B m) ω` with
`B = QuadraticMap.associated (-Q)` (`CliffordAlgebra.exteriorAction_ι`). -/
def exteriorAction : CliffordAlgebra Q →ₐ[R] Module.End R (ExteriorAlgebra R M) :=
  ((equivExterior Q).conjAlgEquiv R).toAlgHom.comp (Algebra.lmul R (CliffordAlgebra Q))

/-- Unfolding lemma for `CliffordAlgebra.exteriorAction`. -/
theorem exteriorAction_apply (a : CliffordAlgebra Q) (x : ExteriorAlgebra R M) :
    exteriorAction Q a x = equivExterior Q (a * (equivExterior Q).symm x) :=
  (rfl)

/-- **`equivExterior` is a map of Clifford modules** from the regular module to the exterior
algebra.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to the underlying
`CliffordAlgebra.changeForm`, so the left-hand side is not in normal form. -/
theorem exteriorAction_equivExterior (a x : CliffordAlgebra Q) :
    exteriorAction Q a (equivExterior Q x) = equivExterior Q (a * x) := by
  rw [exteriorAction_apply, LinearEquiv.symm_apply_apply]

/-- **Acting on `1` is `CliffordAlgebra.equivExterior`**: the exterior algebra is a cyclic
Clifford module generated by `1`, isomorphic to the regular module. -/
@[simp]
theorem exteriorAction_apply_one (a : CliffordAlgebra Q) :
    exteriorAction Q a 1 = equivExterior Q a := by
  have h : equivExterior Q 1 = 1 := by simp
  rw [← h, exteriorAction_equivExterior, mul_one]

/-- **A vector acts by exterior multiplication minus contraction**:
`c(m) ω = m ∧ ω - ι(B m) ω` with `B = QuadraticMap.associated (-Q)`. -/
@[simp]
theorem exteriorAction_ι (m : M) (x : ExteriorAlgebra R M) :
    exteriorAction Q (ι Q m) x =
      ExteriorAlgebra.ι R m * x - contractLeft (QuadraticMap.associated (-Q) m) x := by
  rw [exteriorAction_apply, equivExterior_ι_mul, LinearEquiv.apply_symm_apply]

/-- **The action commutes with the grade involutions**:
`involute (c(a) ω) = c(involute a) (involute ω)`. -/
theorem exteriorAction_involute (a : CliffordAlgebra Q) (x : ExteriorAlgebra R M) :
    exteriorAction Q (involute a) (involute x) = involute (exteriorAction Q a x) := by
  obtain ⟨y, rfl⟩ := (equivExterior Q).surjective x
  rw [← equivExterior_involute, exteriorAction_equivExterior, exteriorAction_equivExterior,
    ← map_mul, equivExterior_involute]

/-- **The action is `ℤ/2`-graded**: an element of parity `i` sends forms of parity `j` to forms of
parity `i + j`. -/
theorem exteriorAction_mem_evenOdd {i j : ZMod 2} {a : CliffordAlgebra Q}
    (ha : a ∈ evenOdd Q i) {x : ExteriorAlgebra R M} (hx : x ∈ evenOdd (0 : QuadraticForm R M) j) :
    exteriorAction Q a x ∈ evenOdd (0 : QuadraticForm R M) (i + j) := by
  obtain ⟨y, rfl⟩ := (equivExterior Q).surjective x
  rw [equivExterior_mem_evenOdd_iff] at hx
  rw [exteriorAction_equivExterior, equivExterior_mem_evenOdd_iff]
  exact SetLike.GradedMul.mul_mem ha hx

end Action

/-! ### Extension of scalars -/

section BaseChange

variable (A : Type*) [CommRing A] [Algebra R A] (Q : QuadraticForm R M)

/-- The action of `CliffordAlgebra (Q.baseChange A)` on `A ⊗[R] ExteriorAlgebra R M`, for a
commutative `R`-algebra `A`: Mathlib's comparison `CliffordAlgebra.toBaseChange` to
`A ⊗[R] CliffordAlgebra Q`, followed by the action of `A` by scalars and of
`CliffordAlgebra Q` by `CliffordAlgebra.exteriorAction` on the second factor. -/
def baseChangeExteriorAction :
    CliffordAlgebra (Q.baseChange A) →ₐ[A] Module.End A (A ⊗[R] ExteriorAlgebra R M) :=
  ((LinearMap.tensorProductEnd R A (ExteriorAlgebra R M)).comp
    (Algebra.TensorProduct.map (AlgHom.id A A) (exteriorAction Q))).comp (toBaseChange A Q)

/-- An element whose image under `CliffordAlgebra.toBaseChange` is a pure tensor `w ⊗ c` acts on
pure tensors factorwise: `(w * z) ⊗ c(c) ω`. -/
private theorem baseChangeExteriorAction_tmul {a : CliffordAlgebra (Q.baseChange A)} {w : A}
    {c : CliffordAlgebra Q} (ha : toBaseChange A Q a = w ⊗ₜ c) (z : A) (x : ExteriorAlgebra R M) :
    baseChangeExteriorAction A Q a (z ⊗ₜ x) = (w * z) ⊗ₜ exteriorAction Q c x := by
  rw [baseChangeExteriorAction, AlgHom.comp_apply, ha, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.tensorProductEnd_tmul,
    LinearMap.smul_apply, LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

/-- The image of a real Clifford element acts on the second factor:
`c(a) (z ⊗ ω) = z ⊗ c(a) ω`. -/
@[simp]
theorem baseChangeExteriorAction_ofBaseChangeAux_tmul (a : CliffordAlgebra Q) (z : A)
    (x : ExteriorAlgebra R M) :
    baseChangeExteriorAction A Q (ofBaseChangeAux A Q a) (z ⊗ₜ x) =
      z ⊗ₜ exteriorAction Q a x := by
  rw [baseChangeExteriorAction_tmul A Q (toBaseChange_ofBaseChangeAux Q a), one_mul]

/-- A vector `w ⊗ m` acts on pure tensors by `c(w ⊗ m) (z ⊗ ω) = (w z) ⊗ c(m) ω`. -/
@[simp]
theorem baseChangeExteriorAction_ι_tmul (w : A) (m : M) (z : A) (x : ExteriorAlgebra R M) :
    baseChangeExteriorAction A Q (ι (Q.baseChange A) (w ⊗ₜ m)) (z ⊗ₜ x) =
      (w * z) ⊗ₜ exteriorAction Q (ι Q m) x :=
  baseChangeExteriorAction_tmul A Q (toBaseChange_ι A Q w m) z x

section InvertibleTwo

variable [Invertible (2 : A)]

/-- **Naturality of `equivExterior` under `ofBaseChangeAux`**: when `2` is invertible in both `R`
and `A`, the Chevalley map of `Q.baseChange A` agrees on `ofBaseChangeAux A Q c` with
`ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ equivExterior Q c)`. -/
theorem equivExterior_ofBaseChangeAux (c : CliffordAlgebra Q) :
    equivExterior (Q.baseChange A) (ofBaseChangeAux A Q c) =
      ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ[R] equivExterior Q c) := by
  let φ : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra A (A ⊗[R] M) :=
    ((ExteriorAlgebra.baseChangeEquiv R M A).toAlgHom.restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hφ_apply (y : ExteriorAlgebra R M) :
      ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ[R] y) = φ y := by
    simp [φ]
  have hφ_ι (m : M) : φ (ι 0 m) = ExteriorAlgebra.ι A (1 ⊗ₜ[R] m) :=
    ExteriorAlgebra.baseChangeEquiv_apply R M A 1 m
  have hinv2 : (⅟(2 : A) : A) = algebraMap R A (⅟(2 : R)) := by
    have h2 : (2 : A) * algebraMap R A (⅟(2 : R)) = 1 := by
      rw [← map_ofNat (algebraMap R A) 2, ← map_mul, mul_invOf_self, map_one]
    calc
      (⅟(2 : A) : A) = ⅟(2 : A) * ((2 : A) * algebraMap R A (⅟(2 : R))) := by rw [h2, mul_one]
      _ = (⅟(2 : A) * 2) * algebraMap R A (⅟(2 : R)) := (mul_assoc _ _ _).symm
      _ = algebraMap R A (⅟(2 : R)) := by rw [invOf_mul_self, one_mul]
  have hB (m m' : M) :
      QuadraticMap.associated (-(Q.baseChange A)) (1 ⊗ₜ[R] m) (1 ⊗ₜ[R] m') =
        algebraMap R A (QuadraticMap.associated (-Q) m m') := by
    rw [QuadraticMap.associated_apply, QuadraticMap.associated_apply, ← TensorProduct.tmul_add]
    simp [QuadraticForm.baseChange_tmul, smul_eq_mul, hinv2, ← Algebra.algebraMap_eq_smul_one]
  have hcontract (m : M) (y : ExteriorAlgebra R M) :
      contractLeft (QuadraticMap.associated (-(Q.baseChange A)) (1 ⊗ₜ[R] m)) (φ y) =
        φ (contractLeft (QuadraticMap.associated (-Q) m) y) := by
    induction y using CliffordAlgebra.left_induction with
    | algebraMap r =>
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A (ExteriorAlgebra A (A ⊗[R] M)),
        contractLeft_algebraMap, contractLeft_algebraMap, map_zero]
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    | ι_mul y' m' hy' =>
      rw [map_mul, hφ_ι, contractLeft_ι_mul, contractLeft_ι_mul, hy', hB,
        IsScalarTower.algebraMap_smul, map_sub, map_smul, map_mul, hφ_ι]
  rw [hφ_apply]
  induction c using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp [φ, ofBaseChangeAux, Algebra.algebraMap_eq_smul_one, ← Algebra.TensorProduct.one_def,
      equivExterior]
  | add x y hx hy => rw [map_add, map_add, hx, hy, ← map_add, ← map_add]
  | ι_mul x m hx =>
    rw [map_mul, ofBaseChangeAux_ι, equivExterior_ι_mul, equivExterior_ι_mul, hx, map_sub,
      map_mul, hφ_ι, hcontract]

/-- **Compatibility of `equivExterior` with `toBaseChange`** along
`ExteriorAlgebra.baseChangeEquiv`. -/
theorem equivExterior_baseChange (a : CliffordAlgebra (Q.baseChange A)) :
    equivExterior (Q.baseChange A) a =
      ExteriorAlgebra.baseChangeEquiv R M A
        ((equivExterior Q).baseChange R A _ _ (toBaseChange A Q a)) := by
  have key (t : A ⊗[R] CliffordAlgebra Q) :
      equivExterior (Q.baseChange A) (ofBaseChange A Q t) =
        ExteriorAlgebra.baseChangeEquiv R M A ((equivExterior Q).baseChange R A _ _ t) := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
    | tmul z c =>
      have hof : ofBaseChange A Q (z ⊗ₜ[R] c) = z • ofBaseChangeAux A Q c := by
        rw [← ofBaseChange_toBaseChange A Q (z • ofBaseChangeAux A Q c), map_smul,
          toBaseChange_ofBaseChangeAux, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have hz : z ⊗ₜ[R] equivExterior Q c = z • (1 ⊗ₜ[R] equivExterior Q c) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hof, LinearEquiv.baseChange_tmul, map_smul, hz, map_smul,
        equivExterior_ofBaseChangeAux]
  simpa only [ofBaseChange_toBaseChange] using key (toBaseChange A Q a)

/-- **Inverse Chevalley compatibility** along `ExteriorAlgebra.baseChangeEquiv`. -/
theorem equivExterior_symm_baseChangeEquiv (x : A ⊗[R] ExteriorAlgebra R M) :
    (equivExterior (Q.baseChange A)).symm (ExteriorAlgebra.baseChangeEquiv R M A x) =
      (equivBaseChange A Q).symm (((equivExterior Q).baseChange R A _ _).symm x) := by
  apply (equivExterior (Q.baseChange A)).injective
  rw [LinearEquiv.apply_symm_apply, equivExterior_baseChange A Q]
  have h : toBaseChange A Q ((equivBaseChange A Q).symm
      (((equivExterior Q).baseChange R A _ _).symm x)) =
      ((equivExterior Q).baseChange R A _ _).symm x :=
    (equivBaseChange A Q).apply_symm_apply _
  rw [h, LinearEquiv.apply_symm_apply]

/-- **`ExteriorAlgebra.baseChangeEquiv` intertwines `baseChangeExteriorAction` with
`exteriorAction (Q.baseChange A)`.** -/
theorem baseChangeEquiv_baseChangeExteriorAction
    (a : CliffordAlgebra (Q.baseChange A)) (x : A ⊗[R] ExteriorAlgebra R M) :
    ExteriorAlgebra.baseChangeEquiv R M A (baseChangeExteriorAction A Q a x) =
      exteriorAction (Q.baseChange A) a (ExteriorAlgebra.baseChangeEquiv R M A x) := by
  have key (t : A ⊗[R] CliffordAlgebra Q) (x : A ⊗[R] ExteriorAlgebra R M) :
      ExteriorAlgebra.baseChangeEquiv R M A
          (baseChangeExteriorAction A Q (ofBaseChange A Q t) x) =
        exteriorAction (Q.baseChange A) (ofBaseChange A Q t)
          (ExteriorAlgebra.baseChangeEquiv R M A x) := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ ht₁ ht₂ => simp only [map_add, LinearMap.add_apply, ht₁, ht₂]
    | tmul w c =>
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ hx₁ hx₂ => simp only [map_add, hx₁, hx₂]
      | tmul z y =>
        obtain ⟨d, rfl⟩ := (equivExterior Q).surjective y
        have hof : ofBaseChange A Q (w ⊗ₜ[R] c) = w • ofBaseChangeAux A Q c := by
          rw [← ofBaseChange_toBaseChange A Q (w • ofBaseChangeAux A Q c), map_smul,
            toBaseChange_ofBaseChangeAux, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have htc : toBaseChange A Q (ofBaseChange A Q (w ⊗ₜ[R] c)) = w ⊗ₜ[R] c :=
          toBaseChange_ofBaseChange A Q (w ⊗ₜ[R] c)
        have hzd : z ⊗ₜ[R] equivExterior Q d = z • (1 ⊗ₜ[R] equivExterior Q d) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have hwzd : (w * z) ⊗ₜ[R] equivExterior Q (c * d) =
            (w * z) • (1 ⊗ₜ[R] equivExterior Q (c * d)) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [baseChangeExteriorAction_tmul A Q htc, exteriorAction_equivExterior, hwzd, map_smul,
          ← equivExterior_ofBaseChangeAux A Q (c * d), hzd, map_smul,
          ← equivExterior_ofBaseChangeAux A Q d, hof, map_smul, exteriorAction_equivExterior,
          smul_mul_assoc, map_smul, ← map_mul, smul_smul, mul_comm z w]
  simpa only [ofBaseChange_toBaseChange] using key (toBaseChange A Q a) x

end InvertibleTwo

end BaseChange

end CliffordAlgebra
