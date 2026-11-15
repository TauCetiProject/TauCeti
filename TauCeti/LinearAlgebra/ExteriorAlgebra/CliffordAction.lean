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
`CliffordAlgebra.toBaseChange` and the factorwise action on the tensor product. When `2` is
invertible in `A`, `ExteriorAlgebra.baseChangeEquiv` intertwines this action with
`CliffordAlgebra.exteriorAction (Q.baseChange A)` and identifies the base-changed Chevalley map
with `CliffordAlgebra.equivExterior (Q.baseChange A)`. For `A = ℂ` this is the Clifford action on
complex-valued forms.

## Main definitions

* `CliffordAlgebra.exteriorAction Q`: the action of `CliffordAlgebra Q` on `ExteriorAlgebra R M`.
* `CliffordAlgebra.baseChangeExteriorAction A Q`: the action of `CliffordAlgebra (Q.baseChange A)`
  on `A ⊗[R] ExteriorAlgebra R M`.

## Main results

* `CliffordAlgebra.exteriorAction_ι`: a vector acts by exterior multiplication minus contraction.
* `CliffordAlgebra.exteriorAction_apply_one`: acting on `1` is `CliffordAlgebra.equivExterior`.
* `CliffordAlgebra.exteriorAction_involute`: the action commutes with the grade involutions.
* `CliffordAlgebra.exteriorAction_mem_evenOdd`: the action is `ℤ/2`-graded.
* `CliffordAlgebra.baseChangeExteriorAction_ofBaseChangeAux_tmul`,
  `CliffordAlgebra.baseChangeExteriorAction_ι_tmul`, and
  `CliffordAlgebra.baseChangeExteriorAction_apply_one`: the extended action on pure tensors and on
  `1`.
* `CliffordAlgebra.baseChangeEquiv_baseChangeExteriorAction`,
  `CliffordAlgebra.baseChangeEquiv_equivExterior`, and
  `CliffordAlgebra.equivExterior_symm_baseChangeEquiv`: compatibility with
  `ExteriorAlgebra.baseChangeEquiv`.

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

/-- **Acting on `1` is the base-changed Chevalley map** after `CliffordAlgebra.toBaseChange`. -/
@[simp]
theorem baseChangeExteriorAction_apply_one (a : CliffordAlgebra (Q.baseChange A)) :
    baseChangeExteriorAction A Q a 1 =
      (equivExterior Q).baseChange R A _ _ (toBaseChange A Q a) := by
  rw [baseChangeExteriorAction, AlgHom.comp_apply]
  induction toBaseChange A Q a using TensorProduct.inductionOn with
  | tmul w c =>
    rw [Algebra.TensorProduct.one_def, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, LinearMap.tensorProductEnd_tmul, LinearMap.smul_apply,
      LinearMap.baseChange_tmul, exteriorAction_apply_one, LinearEquiv.baseChange_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

section InvertibleTwo

variable [Invertible (2 : A)]

/-- **`ExteriorAlgebra.baseChangeEquiv` intertwines `baseChangeExteriorAction` with
`exteriorAction`** on the base-changed quadratic form. -/
@[simp]
theorem baseChangeEquiv_baseChangeExteriorAction (a : CliffordAlgebra (Q.baseChange A))
    (x : A ⊗[R] ExteriorAlgebra R M) :
    ExteriorAlgebra.baseChangeEquiv R M A (baseChangeExteriorAction A Q a x) =
      exteriorAction (Q.baseChange A) a (ExteriorAlgebra.baseChangeEquiv R M A x) := by
  induction a using CliffordAlgebra.induction generalizing x with
  | algebraMap z => simp [Algebra.algebraMap_eq_smul_one]
  | add a b ha hb => simp [ha, hb]
  | mul a b ha hb => simp [ha, hb]
  | ι u =>
    induction u using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
    | tmul w m =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul z y =>
        have h1mul (u v : ExteriorAlgebra R M) :
            ExteriorAlgebra.baseChangeEquiv R M A ((1 : A) ⊗ₜ[R] (u * v)) =
              ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ u) *
                ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ v) := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        have hwm : w ⊗ₜ[R] m = w • ((1 : A) ⊗ₜ[R] m) := by simp [TensorProduct.smul_tmul']
        rw [baseChangeExteriorAction_ι_tmul, ← mul_one (w * z), ← smul_eq_mul,
          ← TensorProduct.smul_tmul', map_smul,
          show z ⊗ₜ[R] y = z • ((1 : A) ⊗ₜ[R] y) by simp [TensorProduct.smul_tmul'],
          map_smul, map_smul, hwm, map_smul, map_smul, LinearMap.smul_apply, smul_smul,
          mul_comm z w]
        congr 1
        rw [exteriorAction_ι, exteriorAction_ι, TensorProduct.tmul_sub, map_sub, h1mul,
          ExteriorAlgebra.baseChangeEquiv_apply]
        congr 1
        -- Compare contractions on `y` along `y ↦ baseChangeEquiv (1 ⊗ y)`.
        set d : Module.Dual R M := QuadraticMap.associated (-Q) m
        set d' : Module.Dual A (A ⊗[R] M) := QuadraticMap.associated (-(Q.baseChange A)) (1 ⊗ₜ m)
        have hd (v : M) : d' (1 ⊗ₜ v) = algebraMap R A (d v) := by
          simp only [d, d', ← QuadraticForm.baseChange_neg, QuadraticForm.associated_baseChange,
            LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.algebraMap_eq_smul_one]
        induction y using CliffordAlgebra.left_induction with
        | algebraMap r =>
          rw [contractLeft_algebraMap, TensorProduct.tmul_zero, map_zero,
            Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
            ← Algebra.TensorProduct.one_def, ← algebraMap_smul A, map_smul, map_one,
            ← Algebra.algebraMap_eq_smul_one, contractLeft_algebraMap]
        | add u v hu hv => simp only [TensorProduct.tmul_add, map_add, hu, hv]
        | ι_mul u v hu =>
          change ExteriorAlgebra.baseChangeEquiv R M A
              (1 ⊗ₜ contractLeft d (ExteriorAlgebra.ι R v * u)) =
            contractLeft d'
              (ExteriorAlgebra.baseChangeEquiv R M A (1 ⊗ₜ (ExteriorAlgebra.ι R v * u)))
          rw [contractLeft_ι_mul, TensorProduct.tmul_sub, map_sub, TensorProduct.tmul_smul,
            h1mul, h1mul, ExteriorAlgebra.baseChangeEquiv_apply, contractLeft_ι_mul, hu,
            ← algebraMap_smul A, map_smul, ← hd v]

/-- **The Chevalley map commutes with scalar extension**: `CliffordAlgebra.equivExterior` on
`Q.baseChange A` agrees with the scalar extension of `equivExterior Q` along
`CliffordAlgebra.toBaseChange` and `ExteriorAlgebra.baseChangeEquiv`.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to `CliffordAlgebra.changeForm`,
so the left-hand side is not in normal form. -/
theorem baseChangeEquiv_equivExterior (a : CliffordAlgebra (Q.baseChange A)) :
    ExteriorAlgebra.baseChangeEquiv R M A
        ((equivExterior Q).baseChange R A _ _ (toBaseChange A Q a)) =
      equivExterior (Q.baseChange A) a := by
  rw [← baseChangeExteriorAction_apply_one, baseChangeEquiv_baseChangeExteriorAction, map_one,
    exteriorAction_apply_one]

/-- **The inverse Chevalley map commutes with scalar extension**: pulling back along
`ExteriorAlgebra.baseChangeEquiv` sends `(equivExterior (Q.baseChange A)).symm` to the scalar
extension of `(equivExterior Q).symm` followed by `CliffordAlgebra.ofBaseChange`.

Not a `simp` lemma: `simp` unfolds `CliffordAlgebra.equivExterior` to `CliffordAlgebra.changeForm`,
so the left-hand side is not in normal form. -/
theorem equivExterior_symm_baseChangeEquiv (x : A ⊗[R] ExteriorAlgebra R M) :
    (equivExterior (Q.baseChange A)).symm (ExteriorAlgebra.baseChangeEquiv R M A x) =
      ofBaseChange A Q (((equivExterior Q).baseChange R A _ _).symm x) := by
  apply (equivExterior (Q.baseChange A)).injective
  rw [LinearEquiv.apply_symm_apply, ← baseChangeEquiv_equivExterior, toBaseChange_ofBaseChange,
    LinearEquiv.apply_symm_apply]

end InvertibleTwo

end BaseChange

end CliffordAlgebra
