/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.ExteriorAlgebra.CliffordAction
-- Private: Chevalley grading and ordered-monomial identities are used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthogonalBasis

/-!
# Base-changed forms as spinor endomorphisms and spinor tensors

A full Clifford representation over a commutative `R`-algebra `A`, with `2` invertible in `R`,
identifies base-changed exterior forms with endomorphisms of its spinor module: apply the
inverse Chevalley map, the native Clifford base-change equivalence, and the representation.
For a finite projective spinor module, composing with Mathlib's `dualTensorHomEquiv` gives
the identification with `S ⊗ S*`. The dual here is the `A`-linear algebraic dual; in the
complex case it is not a Hermitian conjugate space.

Clifford multiplication on forms becomes left multiplication on endomorphisms, hence action
on the first spinor factor. In even negative-metric real dimension, after complexification,
exterior parity instead becomes conjugation by spinor chirality, hence the tensor product
of chirality and its transpose.
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

variable {R A V S : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Invertible (2 : R)] [AddCommGroup V] [Module R V]
  [AddCommGroup S] [Module A S] {Q : QuadraticForm R V}

/-- The inverse Chevalley map followed by a full spinor representation, on the native
base-changed exterior carrier. -/
def cliffordFormsEquivEnd
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S) :
    A ⊗[R] ExteriorAlgebra R V ≃ₗ[A] Module.End A S :=
  ((equivExterior Q).baseChange R A _ _).symm.trans
    ((equivBaseChange A Q).symm.toLinearEquiv.trans ρ.toLinearEquiv)

/-- On the inverse image of a Clifford element, the forms-to-endomorphisms map is the
specified representation.

Not a simp lemma: simplification unfolds `CliffordAlgebra.equivExterior`, so this left-hand
side is not in simp normal form. -/
theorem cliffordFormsEquivEnd_baseChange_equivExterior
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (a : CliffordAlgebra (Q.baseChange A)) :
    ρ.cliffordFormsEquivEnd
        ((equivExterior Q).baseChange R A _ _ (toBaseChange A Q a)) = ρ a := by
  simp [cliffordFormsEquivEnd, equivBaseChange]

/-- The inverse forms-to-endomorphisms map is the Chevalley map after native base change. -/
@[simp]
theorem cliffordFormsEquivEnd_symm_apply
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S) (a : Module.End A S) :
    ρ.cliffordFormsEquivEnd.symm a =
      (equivExterior Q).baseChange R A _ _ (toBaseChange A Q (ρ.symm a)) := by
  apply ρ.cliffordFormsEquivEnd.injective
  rw [LinearEquiv.apply_symm_apply, cliffordFormsEquivEnd_baseChange_equivExterior,
    AlgEquiv.apply_symm_apply]

/-- Pure base-changed forms are sent to the representation of their inverse Chevalley image. -/
@[simp]
theorem cliffordFormsEquivEnd_tmul
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (z : A) (x : ExteriorAlgebra R V) :
    ρ.cliffordFormsEquivEnd (z ⊗ₜ x) =
      z • ρ (ofBaseChangeAux A Q ((equivExterior Q).symm x)) := by
  have h := ρ.cliffordFormsEquivEnd_baseChange_equivExterior
    (ofBaseChangeAux A Q ((equivExterior Q).symm x))
  simp only [toBaseChange_ofBaseChangeAux, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply] at h
  rw [← h, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The increasing orthogonal wedge maps to the represented ordered Clifford monomial. -/
theorem cliffordFormsEquivEnd_one_tmul_exteriorAlgebra_eq_prod_map_sort
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    {I : Type*} [LinearOrder I] (b : Basis I R V)
    (hb : (QuadraticMap.associated Q).IsOrthoᵢ b) (s : Finset I) :
    ρ.cliffordFormsEquivEnd (1 ⊗ₜ b.ExteriorAlgebra s) =
      ρ (ofBaseChangeAux A Q (((s.sort (· ≤ ·)).map (ι Q ∘ b)).prod)) := by
  rw [← equivExterior_basis Q, cliffordFormsEquivEnd_tmul,
    LinearEquiv.symm_apply_apply, one_smul, basis_eq_prod_map_sort hb, List.map_map]

/-- The forms-to-endomorphisms map intertwines the native Clifford action with left
multiplication, not conjugation. -/
theorem cliffordFormsEquivEnd_action
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (a : CliffordAlgebra (Q.baseChange A)) (x : A ⊗[R] ExteriorAlgebra R V) :
    ρ.cliffordFormsEquivEnd (baseChangeExteriorAction A Q a x) =
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
        rw [ι_baseChange_tmul_eq_smul_ofBaseChangeAux, map_smul, smul_mul_smul_comm, mul_smul]
  | add a b ha hb => simp [ha, hb, add_mul]
  | mul a b ha hb => simp [ha, hb, mul_assoc]

/-- Changing spinor coordinates conjugates the associated endomorphism; the form itself
is unchanged. -/
theorem cliffordFormsEquivEnd_conj
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    {T : Type*} [AddCommGroup T] [Module A T] (e : S ≃ₗ[A] T)
    (x : A ⊗[R] ExteriorAlgebra R V) :
    (ρ.trans (e.conjAlgEquiv A)).cliffordFormsEquivEnd x =
      (e.conjAlgEquiv A) (ρ.cliffordFormsEquivEnd x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul z x => simp

variable [Module.Finite A S] [Module.Projective A S]

/-- Base-changed forms as `S ⊗ S*`, with evaluation `s ⊗ φ ↦ (t ↦ φ(t) s)`.
The endomorphism identification uses the specified full Clifford representation. -/
def cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S) :
    A ⊗[R] ExteriorAlgebra R V ≃ₗ[A] S ⊗[A] Dual A S :=
  ρ.cliffordFormsEquivEnd.trans
    ((dualTensorHomEquiv A S S).symm.trans (TensorProduct.comm A (Dual A S) S))

/-- Evaluation of the spinor tensor associated to a form recovers its spinor endomorphism. -/
@[simp]
theorem dualTensorHomEquiv_comm_cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (x : A ⊗[R] ExteriorAlgebra R V) :
    dualTensorHomEquiv A S S (TensorProduct.comm A S (Dual A S)
      (ρ.cliffordFormsEquivTensor x)) = ρ.cliffordFormsEquivEnd x := by
  simp [cliffordFormsEquivTensor]

/-- The inverse tensor identification sends a pure spinor tensor to the inverse Chevalley
image of its rank-one endomorphism. -/
@[simp]
theorem cliffordFormsEquivTensor_symm_tmul
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (s : S) (φ : Dual A S) :
    ρ.cliffordFormsEquivTensor.symm (s ⊗ₜ φ) =
      ρ.cliffordFormsEquivEnd.symm (dualTensorHom A S S (φ ⊗ₜ s)) := by
  simp only [cliffordFormsEquivTensor, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_symm, TensorProduct.comm_symm, TensorProduct.comm_tmul,
    ← LinearEquiv.coe_toLinearMap, toLinearMap_dualTensorHomEquiv]

/-- Transport by `f ⊗ gᵗ` on spinor tensors corresponds to `a ↦ f ∘ₗ a ∘ₗ g` on
endomorphisms, allowing different spinor coordinates and different forms on the two sides. -/
theorem cliffordFormsEquivTensor_eq_map_iff
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    {T : Type*} [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Projective A T]
    (σ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A T)
    (f : S →ₗ[A] T) (g : T →ₗ[A] S) (x y : A ⊗[R] ExteriorAlgebra R V) :
    σ.cliffordFormsEquivTensor y =
        TensorProduct.map f g.dualMap (ρ.cliffordFormsEquivTensor x) ↔
      σ.cliffordFormsEquivEnd y = f ∘ₗ ρ.cliffordFormsEquivEnd x ∘ₗ g := by
  have h (z : S ⊗[A] Dual A S) :
      dualTensorHomEquiv A T T
          (TensorProduct.comm A T (Dual A T) (TensorProduct.map f g.dualMap z)) =
        f ∘ₗ dualTensorHomEquiv A S S (TensorProduct.comm A S (Dual A S) z) ∘ₗ g := by
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw, LinearMap.comp_add, LinearMap.add_comp]
    | tmul s φ => ext t; simp
  rw [← (TensorProduct.comm A T (Dual A T)).injective.eq_iff,
    ← (dualTensorHomEquiv A T T).injective.eq_iff,
    dualTensorHomEquiv_comm_cliffordFormsEquivTensor, h,
    dualTensorHomEquiv_comm_cliffordFormsEquivTensor]

/-- Clifford multiplication acts on the first spinor factor and leaves the dual factor fixed. -/
theorem cliffordFormsEquivTensor_action
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    (a : CliffordAlgebra (Q.baseChange A)) (x : A ⊗[R] ExteriorAlgebra R V) :
    ρ.cliffordFormsEquivTensor (baseChangeExteriorAction A Q a x) =
      TensorProduct.map (ρ a) LinearMap.id (ρ.cliffordFormsEquivTensor x) := by
  simpa using (ρ.cliffordFormsEquivTensor_eq_map_iff ρ (ρ a) LinearMap.id x
    (baseChangeExteriorAction A Q a x)).mpr (ρ.cliffordFormsEquivEnd_action a x)

/-- The spinor tensor comparison is natural under changing spinor coordinates, covariantly
on the spinor factor and contravariantly on the dual factor. -/
theorem cliffordFormsEquivTensor_conj
    (ρ : CliffordAlgebra (Q.baseChange A) ≃ₐ[A] Module.End A S)
    {T : Type*} [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Projective A T]
    (e : S ≃ₗ[A] T) (x : A ⊗[R] ExteriorAlgebra R V) :
    (ρ.trans (e.conjAlgEquiv A)).cliffordFormsEquivTensor x =
      TensorProduct.map e.toLinearMap e.symm.toLinearMap.dualMap
        (ρ.cliffordFormsEquivTensor x) := by
  rw [ρ.cliffordFormsEquivTensor_eq_map_iff, cliffordFormsEquivEnd_conj,
    LinearEquiv.conjAlgEquiv_apply]

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
  rw [ρ.cliffordFormsEquivTensor_eq_map_iff]
  exact ρ.cliffordFormsEquivEnd_involute o hQ hn x

end AlgEquiv
