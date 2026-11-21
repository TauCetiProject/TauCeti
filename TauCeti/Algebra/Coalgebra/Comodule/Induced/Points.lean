/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Induced.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cochain.Points
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Pointwise equivariance of cotensor induction

For a coordinate bialgebra map `q : C →ₐc[R] D`, the cotensor equalizer defining induction
consists exactly of the regular functions satisfying `F(hg) = h F(g)` on points with values
in every commutative algebra. Evaluating at the universal pair of points already detects this
condition. In particular the criterion uses scheme-valued points, not just points over fields.

The cofree coaction gives right translation on these functions. For Hopf algebras,
applying the antipode to the coordinate factor gives Jantzen's convention `f(gh) = h⁻¹ f(g)`
by `Comodule.pointCochain_lTensor_antipode`, and the same action becomes left translation
`(a f)(g) = f(a⁻¹g)`. Evaluation at the identity agrees with the counit evaluation in
Frobenius reciprocity.

There is no finiteness or flatness assumption on the coefficient module, and the coordinate
map need not be surjective. Flatness of `C` is used only to form the induced comodule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups I*, SFB/MPI 85-9 (1985),
  §§3.3–3.7, pp. 52–58.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace BialgHom

open TauCeti TauCeti.Comodule

universe u v w x y

section Bialgebra

variable {R : Type u} [CommRing R]
  {C : Type v} [CommRing C] [Bialgebra R C]
  {D : Type w} [CommRing D] [Bialgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D)
  {A : Type y} [CommRing A] [Algebra R A]

attribute [local instance] cofree

private def conditionEval (h : D →ₐ[R] A) (g : C →ₐ[R] A) :
    (M ⊗[R] D) ⊗[R] C →ₗ[R] A ⊗[R] M :=
  (LinearMap.liftBaseChange A (pointCochain M h)).restrictScalars R ∘ₗ
    pointCochain (M ⊗[R] D) g

private theorem conditionEval_coact (h : D →ₐ[R] A) (g : C →ₐ[R] A)
    (t : M ⊗[R] C) :
    conditionEval h g ((coact (R := R) (C := D) (M := M)).rTensor C t) =
      endOfPoint M h (pointCochain M g t) := by
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul m c =>
    simp only [LinearMap.rTensor_tmul, conditionEval, LinearMap.comp_apply,
      pointCochain_tmul, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul,
      endOfPoint_tmul]
    rw [pointCochain_apply]

omit [Comodule R D M] in
private theorem conditionEval_comul (h : D →ₐ[R] A) (g : C →ₐ[R] A)
    (t : M ⊗[R] C) :
    conditionEval h g ((TensorProduct.assoc R M D C).symm
        (((q.toCoalgHom : C →ₗ[R] D).rTensor C ∘ₗ Coalgebra.comul).lTensor M t)) =
      pointCochain M (q.mapDomain (toConv h) * toConv g).ofConv t := by
  simp only [BialgHom.mapDomain_apply]
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [map_add, ht, hs]
  | tmul m c =>
    simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply, pointCochain_tmul,
      AlgHom.convMul_apply]
    induction Coalgebra.comul (R := R) c using TensorProduct.inductionOn with
    | add t s ht hs => simp only [map_add, tmul_add, add_tmul, ht, hs]
    | tmul c d => simp [conditionEval, smul_tmul', mul_comm, BialgHom.toCoalgHom_apply]

omit [Comodule R D M] in
private theorem conditionEval_universal (z : (M ⊗[R] D) ⊗[R] C) :
    conditionEval (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := C))
        Algebra.TensorProduct.includeRight z =
      TensorProduct.comm R M (D ⊗[R] C) (TensorProduct.assoc R M D C z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul md c =>
    induction md using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [add_tmul, map_add, hz, hz']
    | tmul m d => simp [conditionEval, smul_tmul']

variable [Module.Flat R C]

/-- The cotensor condition implies `F(hg) = h F(g)` on points over every value algebra. -/
theorem pointCochain_mul_of_mem_induced {t : M ⊗[R] C}
    (ht : t ∈ induced q.toCoalgHom M)
    (h : WithConv (D →ₐ[R] A)) (g : WithConv (C →ₐ[R] A)) :
    pointCochain M (q.mapDomain h * g).ofConv t =
      endOfPoint M h.ofConv (pointCochain M g.ofConv t) := by
  have heq := congrArg (conditionEval h.ofConv g.ofConv) ((mem_induced_iff q.toCoalgHom).mp ht)
  rw [conditionEval_coact, conditionEval_comul] at heq
  exact heq.symm

/-- Testing equivariance at the two tensor-factor points detects the cotensor equalizer. -/
theorem mem_induced_iff_pointCochain_mul_universal (t : M ⊗[R] C) :
    t ∈ induced q.toCoalgHom M ↔
      pointCochain M
          (q.mapDomain (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R)
            (A := D) (B := C))) *
            toConv Algebra.TensorProduct.includeRight).ofConv t =
        endOfPoint M (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := C))
          (pointCochain M Algebra.TensorProduct.includeRight t) := by
  refine ⟨fun ht ↦ pointCochain_mul_of_mem_induced q ht _ _, fun ht ↦ ?_⟩
  apply (mem_induced_iff q.toCoalgHom).mpr
  apply (TensorProduct.assoc R M D C).injective
  apply (TensorProduct.comm R M (D ⊗[R] C)).injective
  rw [← conditionEval_universal, ← conditionEval_universal,
    conditionEval_coact, conditionEval_comul]
  exact ht.symm

/-- A regular function belongs to cotensor induction exactly when `F(hg) = h F(g)` for
all points over all commutative value algebras. The value universe includes both coordinate
algebras, so it contains the universal tensor-factor test. -/
theorem mem_induced_iff_forall_pointCochain_mul (t : M ⊗[R] C) :
    t ∈ induced q.toCoalgHom M ↔
      ∀ (A : Type max v w) [CommRing A] [Algebra R A]
        (h : WithConv (D →ₐ[R] A)) (g : WithConv (C →ₐ[R] A)),
        pointCochain M (q.mapDomain h * g).ofConv t =
          endOfPoint M h.ofConv (pointCochain M g.ofConv t) := by
  refine ⟨fun ht A _ _ h g ↦ pointCochain_mul_of_mem_induced q ht h g, fun ht ↦ ?_⟩
  exact (mem_induced_iff_pointCochain_mul_universal q t).mpr
    (ht (D ⊗[R] C) (toConv (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := D) (B := C)))
      (toConv Algebra.TensorProduct.includeRight))

/-- Evaluation of a scalar-extended induced function at an algebra-valued point. This is
counit evaluation after the point acts, hence is linear over the value algebra. -/
def inducedPointEval (g : WithConv (C →ₐ[R] A)) :
    A ⊗[R] induced q.toCoalgHom M →ₗ[A] A ⊗[R] M :=
  let := Corestrict (M := induced q.toCoalgHom M) q.toCoalgHom
  (inducedEval q.toCoalgHom).toLinearMap.baseChange A ∘ₗ
    endOfPoint (induced q.toCoalgHom M) g.ofConv

/-- Evaluation is counit evaluation after applying the point action. -/
theorem inducedPointEval_def (g : WithConv (C →ₐ[R] A)) :
    let := Corestrict (M := induced q.toCoalgHom M) q.toCoalgHom
    inducedPointEval (M := M) q g =
      (inducedEval q.toCoalgHom).toLinearMap.baseChange A ∘ₗ
        endOfPoint (induced q.toCoalgHom M) g.ofConv := (rfl)

/-- On a pure tensor, evaluation pushes the coordinate factor through the point. -/
@[simp]
theorem inducedPointEval_tmul (g : WithConv (C →ₐ[R] A)) (a : A)
    (t : induced q.toCoalgHom M) :
    inducedPointEval q g (a ⊗ₜ[R] t) = a • pointCochain M g.ofConv (t : M ⊗[R] C) := by
  let := Corestrict (M := induced q.toCoalgHom M) q.toCoalgHom
  have h := rTensor_inducedEval_coact q.toCoalgHom t
  have naturality (z : induced q.toCoalgHom M ⊗[R] C) :
      (inducedEval q.toCoalgHom).toLinearMap.baseChange A
          (pointCochain (induced q.toCoalgHom M) g.ofConv z) =
        pointCochain M g.ofConv ((inducedEval q.toCoalgHom).toLinearMap.rTensor C z) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul t c => simp
  simp only [inducedPointEval, LinearMap.comp_apply, endOfPoint_tmul, map_smul]
  rw [← pointCochain_apply, naturality, h]

/-- Evaluation at the identity is the scalar extension of the counit evaluation in
Frobenius reciprocity. -/
@[simp]
theorem inducedPointEval_one :
    let := Corestrict (M := induced q.toCoalgHom M) q.toCoalgHom
    inducedPointEval (M := M) (A := A) q 1 =
      (inducedEval q.toCoalgHom).toLinearMap.baseChange A := by
  simp [inducedPointEval, endOfPoint_convOne]

/-- The point action on induction is right translation: `(a F)(g) = F(ga)`. -/
theorem inducedPointEval_endOfPoint (g a : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced q.toCoalgHom M) :
    inducedPointEval q g (endOfPoint (induced q.toCoalgHom M) a.ofConv z) =
      inducedPointEval q (g * a) z := by
  simp only [inducedPointEval, endOfPoint_convMul, LinearMap.comp_apply]

/-- Equivariance of induced functions also holds after extending the coefficient module. -/
theorem inducedPointEval_mapDomain_mul (h : WithConv (D →ₐ[R] A))
    (g : WithConv (C →ₐ[R] A)) (z : A ⊗[R] induced q.toCoalgHom M) :
    inducedPointEval q (q.mapDomain h * g) z =
      endOfPoint M h.ofConv (inducedPointEval q g z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a t =>
    rw [inducedPointEval_tmul, inducedPointEval_tmul,
      pointCochain_mul_of_mem_induced q t.property, map_smul]

/-- Evaluation commutes with extension of the value algebra. -/
theorem rTensor_inducedPointEval {B : Type*} [CommRing B] [Algebra R B]
    (φ : A →ₐ[R] B) (g : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced q.toCoalgHom M) :
    φ.toLinearMap.rTensor M (inducedPointEval q g z) =
      inducedPointEval q (AlgHom.mapValue φ g)
        (φ.toLinearMap.rTensor (induced q.toCoalgHom M) z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a t =>
    simp only [inducedPointEval_tmul, LinearMap.rTensor_tmul, AlgHom.mapValue_apply,
      AlgHom.rTensor_toLinearMap_apply_smul, rTensor_pointCochain, AlgHom.toLinearMap_apply]

/-- The lift in Frobenius reciprocity evaluates as `F(g) = u(g n)`, for a morphism
`u` from the corestricted source to the coefficient comodule. -/
theorem inducedPointEval_inducedLift {N : Type*} [AddCommMonoid N] [Module R N]
    [Comodule R C N] (f : letI := Corestrict (M := N) q.toCoalgHom; Hom R D N M)
    (g : WithConv (C →ₐ[R] A)) (z : A ⊗[R] N) :
    letI := Corestrict (M := N) q.toCoalgHom
    inducedPointEval q g ((inducedLift q.toCoalgHom f).toLinearMap.baseChange A z) =
      f.toLinearMap.baseChange A (endOfPoint N g.ofConv z) := by
  let := Corestrict (M := N) q.toCoalgHom
  let := Corestrict (M := induced q.toCoalgHom M) q.toCoalgHom
  have hf := (inducedEquiv q.toCoalgHom).apply_symm_apply f
  rw [inducedEquiv_symm_apply, inducedEquiv_apply] at hf
  have he := congrArg Hom.toLinearMap hf
  simp only [Hom.comp_toLinearMap, corestrictHom_toLinearMap] at he
  have hn := LinearMap.congr_fun
    (baseChange_comp_endOfPoint (inducedLift q.toCoalgHom f) g.ofConv) z
  simp only [LinearMap.comp_apply] at hn
  simp only [inducedPointEval_def, LinearMap.comp_apply]
  rw [← hn, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, he]

end Bialgebra

section Hopf

variable {R : Type u} [CommRing R]
  {C : Type v} [CommRing C] [HopfAlgebra R C]
  {D : Type w} [CommRing D] [HopfAlgebra R D]
  {M : Type x} [AddCommMonoid M] [Module R M] [Comodule R D M]
  (q : C →ₐc[R] D) [Module.Flat R C]
  {A : Type y} [CommRing A] [Algebra R A]

/-- Inverting the argument changes the cotensor convention to Jantzen's convention:
`f(gh) = h⁻¹ f(g)` for `f(g) = F(g⁻¹)`. -/
theorem pointCochain_mul_lTensor_antipode_of_mem_induced {t : M ⊗[R] C}
    (ht : t ∈ induced q.toCoalgHom M)
    (g : WithConv (C →ₐ[R] A)) (h : WithConv (D →ₐ[R] A)) :
    pointCochain M (g * q.mapDomain h).ofConv ((_root_.HopfAlgebraStruct.antipode R).lTensor M t) =
      endOfPoint M (h⁻¹).ofConv
        (pointCochain M g.ofConv ((_root_.HopfAlgebraStruct.antipode R).lTensor M t)) := by
  rw [pointCochain_lTensor_antipode, pointCochain_lTensor_antipode, mul_inv_rev, ← map_inv]
  exact pointCochain_mul_of_mem_induced q ht h⁻¹ g⁻¹

/-- After inverting the argument, the same induced action is left translation:
`(a f)(g) = f(a⁻¹g)`. -/
theorem inducedPointEval_inv_endOfPoint (g a : WithConv (C →ₐ[R] A))
    (z : A ⊗[R] induced q.toCoalgHom M) :
    inducedPointEval q g⁻¹ (endOfPoint (induced q.toCoalgHom M) a.ofConv z) =
      inducedPointEval q (a⁻¹ * g)⁻¹ z := by
  rw [inducedPointEval_endOfPoint, mul_inv_rev, inv_inv]

end Hopf

end BialgHom
