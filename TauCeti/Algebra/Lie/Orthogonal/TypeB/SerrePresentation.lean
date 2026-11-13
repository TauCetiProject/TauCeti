/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basis
public import TauCeti.Algebra.Lie.Presentation.Serre.Injective
import TauCeti.Algebra.Lie.Orthogonal.TypeB.Killing

/-!
# The Serre presentation of the split odd orthogonal Lie algebra

Over any characteristic-zero field, the standard numbered generators identify the Serre
presentation of the transposed type-B Cartan matrix with the split odd orthogonal Lie algebra.
The comparison and its inverse preserve Cartan, raising and lowering generators, including in
rank one. No validity condition on a Dynkin type is needed.

The construction specializes `LieAlgebra.Basis.serreLiftEquiv` to `TauCeti.typeBLieBasis`, using
`TauCeti.isKilling_typeB` and `TauCeti.isSerreSystem_typeBSimpleRootGenerator`.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4–6, Plate II.
* [J.P. Serre, *Complex Semisimple Lie Algebras*][serre1965], chapter VI, appendix.
-/

public section

open scoped Matrix

namespace TauCeti

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [CharZero K] (n : ℕ)

/-- The Serre presentation of the split odd orthogonal Lie algebra over a characteristic-zero
field, with the standard Bourbaki-numbered generators. This includes rank one. -/
def typeBSerreEquiv : Matrix.ToLieAlgebra K (CartanMatrix.B (n + 1))ᵀ ≃ₗ⁅K⁆
    LieAlgebra.Orthogonal.typeB (Fin (n + 1)) K :=
  (typeBLieBasis (K := K) n).serreLiftEquiv
    (by rw [typeBLieBasis_A])
    (by simpa only [funext (typeBLieBasis_h (K := K) n),
      funext (typeBLieBasis_e (K := K) n), funext (typeBLieBasis_f (K := K) n)] using
      isSerreSystem_typeBSimpleRootGenerator (K := K) (n := n))

/-- The type-B presentation isomorphism is the lift of the standard generators. -/
@[simp]
theorem coe_typeBSerreEquiv :
    ⇑(typeBSerreEquiv (K := K) n) = serreLift isSerreSystem_typeBSimpleRootGenerator := by
  simp only [typeBSerreEquiv, LieAlgebra.Basis.coe_serreLiftEquiv,
    funext (typeBLieBasis_h (K := K) n), funext (typeBLieBasis_e (K := K) n),
    funext (typeBLieBasis_f (K := K) n)]

/-- The Serre Cartan generator maps to the native simple coroot matrix. -/
@[simp]
theorem typeBSerreEquiv_serreH (i : Fin (n + 1)) :
    typeBSerreEquiv (K := K) n (serreH K (CartanMatrix.B (n + 1))ᵀ i) =
      typeBSimpleCorootGenerator i := by
  simp

/-- The Serre raising generator maps to the native positive simple-root matrix. -/
@[simp]
theorem typeBSerreEquiv_serreE (i : Fin (n + 1)) :
    typeBSerreEquiv (K := K) n (serreE K (CartanMatrix.B (n + 1))ᵀ i) =
      typeBSimpleRootGenerator i := by
  simp

/-- The Serre lowering generator maps to the native negative simple-root matrix. -/
@[simp]
theorem typeBSerreEquiv_serreF (i : Fin (n + 1)) :
    typeBSerreEquiv (K := K) n (serreF K (CartanMatrix.B (n + 1))ᵀ i) =
      typeBSimpleNegativeRootGenerator i := by
  simp

/-- The inverse presentation sends a simple coroot matrix to the Serre Cartan generator. -/
@[simp]
theorem typeBSerreEquiv_symm_typeBSimpleCorootGenerator (i : Fin (n + 1)) :
    (typeBSerreEquiv (K := K) n).symm (typeBSimpleCorootGenerator i) =
      serreH K (CartanMatrix.B (n + 1))ᵀ i := by
  rw [LieEquiv.symm_apply_eq, typeBSerreEquiv_serreH]

/-- The inverse presentation sends a positive simple-root matrix to the Serre raising generator. -/
@[simp]
theorem typeBSerreEquiv_symm_typeBSimpleRootGenerator (i : Fin (n + 1)) :
    (typeBSerreEquiv (K := K) n).symm (typeBSimpleRootGenerator i) =
      serreE K (CartanMatrix.B (n + 1))ᵀ i := by
  rw [LieEquiv.symm_apply_eq, typeBSerreEquiv_serreE]

/-- The inverse presentation sends a negative simple-root matrix to the Serre lowering generator. -/
@[simp]
theorem typeBSerreEquiv_symm_typeBSimpleNegativeRootGenerator (i : Fin (n + 1)) :
    (typeBSerreEquiv (K := K) n).symm (typeBSimpleNegativeRootGenerator i) =
      serreF K (CartanMatrix.B (n + 1))ᵀ i := by
  rw [LieEquiv.symm_apply_eq, typeBSerreEquiv_serreF]

end

end TauCeti
