/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.CliffordAlgebra.Dual
public import TauCeti.LinearAlgebra.ExteriorAlgebra.CliffordAction
-- Private: Chevalley grading and ordered-monomial identities are used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis

/-!
# Complexified forms as spinor endomorphisms and spinor tensors

A full complex Clifford representation identifies complexified real exterior forms with
endomorphisms of its spinor space: apply the inverse Chevalley map, the native Clifford
base-change equivalence, and the representation. Composing with Mathlib's
`dualTensorHomEquiv` gives the identification with `S ⊗ S*`. The dual here is the complex-linear
algebraic dual, not a Hermitian conjugate space.

Clifford multiplication on forms becomes left multiplication on endomorphisms, hence action
on the first spinor factor. In even negative-metric dimension, exterior parity instead becomes
conjugation by spinor chirality, hence the tensor product of chirality and its transpose.
The transpose is the induced dual parity; the chirality of the reverse-dual Clifford action
has the additional sign `(-1) ^ (dim V / 2)`. These comparisons include dimension zero and
both orientations. No Hermitian metric is needed for these algebraic identifications.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open scoped TensorProduct
open CliffordAlgebra Module

namespace AlgEquiv

variable {V S : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup S] [Module ℂ S] {Q : QuadraticForm ℝ V}

/-- The inverse Chevalley map followed by a full spinor representation, on the native
complexified real exterior carrier. -/
def cliffordFormsEquivEnd
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) :
    ℂ ⊗[ℝ] ExteriorAlgebra ℝ V ≃ₗ[ℂ] Module.End ℂ S :=
  ((equivExterior Q).baseChange ℝ ℂ _ _).symm.trans
    ((equivBaseChange ℂ Q).symm.toLinearEquiv.trans ρ.toLinearEquiv)

/-- On the inverse image of a Clifford element, the forms-to-endomorphisms map is the
specified representation.

Not a simp lemma: simplification unfolds `CliffordAlgebra.equivExterior`, so this left-hand
side is not in simp normal form. -/
theorem cliffordFormsEquivEnd_baseChange_equivExterior
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (a : CliffordAlgebra (Q.baseChange ℂ)) :
    ρ.cliffordFormsEquivEnd
        ((equivExterior Q).baseChange ℝ ℂ _ _ (toBaseChange ℂ Q a)) = ρ a := by
  simp [cliffordFormsEquivEnd, equivBaseChange]

/-- The inverse forms-to-endomorphisms map is the Chevalley map after native base change. -/
@[simp]
theorem cliffordFormsEquivEnd_symm_apply
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) (A : Module.End ℂ S) :
    ρ.cliffordFormsEquivEnd.symm A =
      (equivExterior Q).baseChange ℝ ℂ _ _ (toBaseChange ℂ Q (ρ.symm A)) := by
  apply ρ.cliffordFormsEquivEnd.injective
  rw [LinearEquiv.apply_symm_apply, cliffordFormsEquivEnd_baseChange_equivExterior,
    AlgEquiv.apply_symm_apply]

/-- Pure complexified forms are sent to the representation of their inverse Chevalley image. -/
@[simp]
theorem cliffordFormsEquivEnd_tmul
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (z : ℂ) (x : ExteriorAlgebra ℝ V) :
    ρ.cliffordFormsEquivEnd (z ⊗ₜ x) =
      z • ρ (ofBaseChangeAux ℂ Q ((equivExterior Q).symm x)) := by
  have h := ρ.cliffordFormsEquivEnd_baseChange_equivExterior
    (ofBaseChangeAux ℂ Q ((equivExterior Q).symm x))
  simp only [toBaseChange_ofBaseChangeAux, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply] at h
  rw [← h, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The increasing orthogonal wedge maps to the represented ordered Clifford monomial. -/
theorem cliffordFormsEquivEnd_basis
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    {I : Type*} [LinearOrder I] (b : Basis I ℝ V)
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (s : Finset I) :
    ρ.cliffordFormsEquivEnd (1 ⊗ₜ b.ExteriorAlgebra s) =
      ρ (ofBaseChangeAux ℂ Q (((s.sort (· ≤ ·)).map (ι Q ∘ b)).prod)) := by
  rw [← equivExterior_basis Q, cliffordFormsEquivEnd_tmul,
    LinearEquiv.symm_apply_apply, one_smul, basis_eq_prod_map_sort hb, List.map_map]

/-- The forms-to-endomorphisms map intertwines the native Clifford action with left
multiplication, not conjugation. -/
theorem cliffordFormsEquivEnd_action
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    ρ.cliffordFormsEquivEnd (baseChangeExteriorAction ℂ Q a x) =
      ρ a * ρ.cliffordFormsEquivEnd x := by
  induction a using CliffordAlgebra.induction generalizing x with
  | algebraMap z => simp [Algebra.algebraMap_eq_smul_one]
  | ι w =>
    induction w using TensorProduct.inductionOn with
    | add u v hu hv => simp [hu, hv, add_mul]
    | tmul z v =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy, mul_add]
      | tmul w y =>
        rw [baseChangeExteriorAction_ι_tmul, cliffordFormsEquivEnd_tmul,
          exteriorAction_apply, LinearEquiv.symm_apply_apply, map_mul, map_mul,
          cliffordFormsEquivEnd_tmul]
        have hι : ι (Q.baseChange ℂ) (z ⊗ₜ v) =
            z • ofBaseChangeAux ℂ Q (ι Q v) := by
          rw [ofBaseChangeAux_ι, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hι, map_smul, smul_mul_smul_comm, mul_smul]
  | add a b ha hb => simp [ha, hb, add_mul]
  | mul a b ha hb => simp [ha, hb, mul_assoc]

/-- Changing spinor coordinates conjugates the associated endomorphism; the form itself
is unchanged. -/
theorem cliffordFormsEquivEnd_conj
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    {T : Type*} [AddCommGroup T] [Module ℂ T] (e : S ≃ₗ[ℂ] T)
    (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (ρ.trans (e.conjAlgEquiv ℂ)).cliffordFormsEquivEnd x =
      (e.conjAlgEquiv ℂ) (ρ.cliffordFormsEquivEnd x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul z x => simp

variable [FiniteDimensional ℂ S]

/-- Complexified forms as `S ⊗ S*`, with evaluation `s ⊗ φ ↦ (t ↦ φ(t) s)`.
The endomorphism identification uses the specified full Clifford representation. -/
def cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) :
    ℂ ⊗[ℝ] ExteriorAlgebra ℝ V ≃ₗ[ℂ] S ⊗[ℂ] Dual ℂ S :=
  ρ.cliffordFormsEquivEnd.trans
    ((dualTensorHomEquiv ℂ S S).symm.trans (TensorProduct.comm ℂ (Dual ℂ S) S))

/-- Evaluation of the spinor tensor associated to a form recovers its spinor endomorphism. -/
@[simp]
theorem dualTensorHomEquiv_comm_cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    dualTensorHomEquiv ℂ S S (TensorProduct.comm ℂ S (Dual ℂ S)
      (ρ.cliffordFormsEquivTensor x)) = ρ.cliffordFormsEquivEnd x := by
  simp [cliffordFormsEquivTensor]

/-- The inverse tensor identification sends a pure spinor tensor to the inverse Chevalley
image of its rank-one endomorphism. -/
@[simp]
theorem cliffordFormsEquivTensor_symm_tmul
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (s : S) (φ : Dual ℂ S) :
    ρ.cliffordFormsEquivTensor.symm (s ⊗ₜ φ) =
      ρ.cliffordFormsEquivEnd.symm (dualTensorHom ℂ S S (φ ⊗ₜ s)) := by
  simp only [cliffordFormsEquivTensor, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    TensorProduct.comm_symm, TensorProduct.comm_tmul]
  congr 1

/-- Clifford multiplication acts on the first spinor factor and leaves the dual factor fixed. -/
theorem cliffordFormsEquivTensor_action
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (a : CliffordAlgebra (Q.baseChange ℂ)) (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    ρ.cliffordFormsEquivTensor (baseChangeExteriorAction ℂ Q a x) =
      TensorProduct.map (ρ a) LinearMap.id (ρ.cliffordFormsEquivTensor x) := by
  apply (TensorProduct.comm ℂ S (Dual ℂ S)).injective
  apply (dualTensorHomEquiv ℂ S S).injective
  rw [dualTensorHomEquiv_comm_cliffordFormsEquivTensor, cliffordFormsEquivEnd_action,
    ← TensorProduct.map_comm]
  rw [← ρ.dualTensorHomEquiv_comm_cliffordFormsEquivTensor x]
  exact (LinearMap.congr_fun (dualTensorHom_comp_lTensor (R := ℂ) (M := S) (ρ a)) _).symm

/-- The spinor tensor comparison is natural under changing spinor coordinates, covariantly
on the spinor factor and contravariantly on the dual factor. -/
theorem cliffordFormsEquivTensor_conj
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    {T : Type*} [AddCommGroup T] [Module ℂ T] [FiniteDimensional ℂ T]
    (e : S ≃ₗ[ℂ] T) (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    (ρ.trans (e.conjAlgEquiv ℂ)).cliffordFormsEquivTensor x =
      TensorProduct.map e.toLinearMap e.symm.toLinearMap.dualMap
        (ρ.cliffordFormsEquivTensor x) := by
  apply (TensorProduct.comm ℂ T (Dual ℂ T)).injective
  apply (dualTensorHomEquiv ℂ T T).injective
  rw [dualTensorHomEquiv_comm_cliffordFormsEquivTensor, cliffordFormsEquivEnd_conj,
    ← TensorProduct.map_comm, ← ρ.dualTensorHomEquiv_comm_cliffordFormsEquivTensor x]
  generalize ρ.cliffordFormsEquivTensor x = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp [hy, hz]
  | tmul s φ => ext t; simp

end AlgEquiv

namespace AlgEquiv

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup S] [Module ℂ S]
  {n : ℕ} [Fact (Module.finrank ℝ V = n)] {Q : QuadraticForm ℝ V}

/-- Exterior parity corresponds to conjugation by spinor chirality. This is different from
Clifford multiplication by the volume element, which acts only on the left. -/
theorem cliffordFormsEquivEnd_involute
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : Even n)
    (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    ρ.cliffordFormsEquivEnd (involute.toLinearMap.baseChange ℂ x) =
      ρ (complexVolume Q o) * ρ.cliffordFormsEquivEnd x * ρ (complexVolume Q o) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy, mul_add, add_mul]
  | tmul z x =>
    obtain ⟨a, rfl⟩ := (equivExterior Q).surjective x
    simp only [LinearMap.baseChange_tmul, AlgHom.toLinearMap_apply, ← equivExterior_involute,
      cliffordFormsEquivEnd_tmul, LinearEquiv.symm_apply_apply, ofBaseChangeAux_involute]
    rw [← complexVolume_mul_mul_complexVolume o hQ hn]
    simp

/-- On spinor tensors, exterior parity is `Γ ⊗ Γᵗ`. The dual operator is the transpose
of spinor chirality, not the chirality of the reverse-dual Clifford representation. -/
theorem cliffordFormsEquivTensor_involute [FiniteDimensional ℂ S]
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : Even n)
    (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    ρ.cliffordFormsEquivTensor (involute.toLinearMap.baseChange ℂ x) =
      TensorProduct.map (ρ (complexVolume Q o)) (ρ (complexVolume Q o)).dualMap
        (ρ.cliffordFormsEquivTensor x) := by
  apply (TensorProduct.comm ℂ S (Dual ℂ S)).injective
  apply (dualTensorHomEquiv ℂ S S).injective
  rw [dualTensorHomEquiv_comm_cliffordFormsEquivTensor,
    cliffordFormsEquivEnd_involute ρ o hQ hn, ← TensorProduct.map_comm,
    ← ρ.dualTensorHomEquiv_comm_cliffordFormsEquivTensor x]
  generalize ρ.cliffordFormsEquivTensor x = y
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp [hy, hz, mul_add, add_mul]
  | tmul s φ => ext t; simp

end AlgEquiv
