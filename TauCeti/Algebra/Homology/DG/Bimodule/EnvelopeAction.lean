/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Bimodule.Category
public import TauCeti.Algebra.Homology.DG.Bimodule.Hom.Complex
public import TauCeti.Algebra.Module.GradedModule.KoszulTwist.Algebra
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Koszul-twisted enveloping actions on DG bimodules

A DG `(A, B)`-bimodule `N` is a module over the enveloping algebra `A ⊗ Bᵐᵒᵖ`, the pure tensor
`a ⊗ b` acting by `m ↦ a m b`. A homogeneous `(A, B)`-bimodule cochain `f` of degree `p` commutes
with the left action of an element `a` of degree `r` only up to the Koszul sign `(-1)^(p r)`. So
`f` intertwines the action of `A ⊗ Bᵐᵒᵖ` on its source with the **twisted action**
`DGBimoduleCat.envelopeTwistAction`, in which `a ⊗ b` acts by `m ↦ (-1)^(p r) a m b`, through the
Koszul automorphism `TauCeti.InternalGrading.koszulTwistAlgEquiv` of `A`. In parameter zero this
is the untwisted action. Conversely, a linear map of degree `p` with this intertwining property is
a cochain (`TauCeti.dgBimoduleCochains.ofEnvelopeTwist`).

A bimodule cochain out of a cyclic bimodule `(A ⊗ Bᵐᵒᵖ) e`, for an idempotent `e` of degree zero,
is determined by its value at `e`, which lies in the **corner** `DGBimoduleCat.envelopeCorner`
of elements fixed by `e`. For a path algebra and `e = eⱼ ⊗ eᵢ` this is `eⱼ N eᵢ`.

## Main definitions

* `TauCeti.DGBimoduleCat.envelopeTwistAction`: the action of `A ⊗ Bᵐᵒᵖ` on `N` twisted by the
  Koszul automorphism of parameter `p` on `A`.
* `TauCeti.DGBimoduleCat.envelopeCorner`: the elements of a given degree fixed by the action of an
  element of `A ⊗ Bᵐᵒᵖ`.
* `TauCeti.dgBimoduleCochains.ofEnvelopeTwist`: the cochain given by a homogeneous linear map
  which intertwines the action of `A ⊗ Bᵐᵒᵖ` with the twisted action.

## Main results

* `TauCeti.DGBimoduleCat.envelopeTwistAction_mul`: the twisted action is an action.
* `TauCeti.DGBimoduleCat.envelopeTwistAction_mem`: it adds degrees, for the tensor-product
  grading of `A ⊗ Bᵐᵒᵖ`.
* `TauCeti.dgBimoduleCochains.map_envelopeTwistAction`: a degree-`p` cochain intertwines the
  action of `A ⊗ Bᵐᵒᵖ` with the twisted action of parameter `p`.

## References

* B. Keller, *Deriving DG categories*, Sections 1.1 and 6.1, for DG bimodules and the Koszul
  sign rule for their homogeneous morphisms.
-/

public section

open MulOpposite
open scoped TensorProduct

namespace TauCeti

variable {R : Type*} {A : Type*} {B : Type*}
  [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B]
  {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}

namespace DGBimoduleCat

variable (N : DGBimoduleCat hA hB)

/-- The action of the enveloping algebra `A ⊗ Bᵐᵒᵖ` on a DG bimodule `N`, twisted by the Koszul
automorphism of parameter `p` on the left factor: on homogeneous `a` of degree `r`, the pure tensor
`a ⊗ b` acts by `m ↦ (-1)^(p r) a m b`. -/
noncomputable def envelopeTwistAction (p : ℤ) : A ⊗[R] Bᵐᵒᵖ →ₗ[R] N →ₗ[R] N :=
  TensorProduct.Algebra.moduleAux ∘ₗ
    (Algebra.TensorProduct.map (InternalGrading.koszulTwistAlgEquiv 𝒜 p).toAlgHom
      (AlgHom.id R Bᵐᵒᵖ)).toLinearMap

@[simp]
theorem envelopeTwistAction_tmul (p : ℤ) (a : A) (b : Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction p (a ⊗ₜ[R] b) m = InternalGrading.koszulTwistAlgEquiv 𝒜 p a • b • m :=
  (rfl)

/-- In parameter zero the action is untwisted: `a ⊗ b` acts by `m ↦ a m b`. -/
theorem envelopeTwistAction_zero_tmul (a : A) (b : Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction 0 (a ⊗ₜ[R] b) m = a • b • m := by
  rw [envelopeTwistAction_tmul, InternalGrading.koszulTwistAlgEquiv_zero, AlgEquiv.coe_refl,
    id_eq]

/-- The twist does not affect the right action: `1 ⊗ b` acts by `m ↦ m b`. -/
theorem envelopeTwistAction_one_tmul (p : ℤ) (b : Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction p (1 ⊗ₜ[R] b) m = b • m := by
  rw [envelopeTwistAction_tmul, map_one, one_smul]

/-- `a ⊗ 1` acts by the left action of the Koszul twist of `a`. -/
theorem envelopeTwistAction_tmul_one (p : ℤ) (a : A) (m : N) :
    N.envelopeTwistAction p (a ⊗ₜ[R] 1) m = InternalGrading.koszulTwistAlgEquiv 𝒜 p a • m := by
  rw [envelopeTwistAction_tmul, one_smul]

/-- The unit of `A ⊗ Bᵐᵒᵖ` acts trivially. -/
@[simp]
theorem envelopeTwistAction_one (p : ℤ) (m : N) : N.envelopeTwistAction p 1 m = m := by
  rw [Algebra.TensorProduct.one_def, envelopeTwistAction_one_tmul, one_smul]

/-- The twisted action is an action of `A ⊗ Bᵐᵒᵖ`. -/
theorem envelopeTwistAction_mul (p : ℤ) (u v : A ⊗[R] Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction p (u * v) m =
      N.envelopeTwistAction p u (N.envelopeTwistAction p v m) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp [add_mul, hu, hu']
  | tmul a b =>
    induction v using TensorProduct.inductionOn with
    | add v v' hv hv' => simp [mul_add, hv, hv']
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, envelopeTwistAction_tmul, map_mul,
        mul_smul]
      rw [smul_comm (InternalGrading.koszulTwistAlgEquiv 𝒜 p a') b]

/-- On a pure tensor whose left factor has degree zero, the twist has no effect. -/
theorem envelopeTwistAction_tmul_of_mem_zero (p : ℤ) {a : A} (ha : a ∈ 𝒜 0) (b : Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction p (a ⊗ₜ[R] b) m = a • b • m := by
  rw [envelopeTwistAction_tmul, InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 p ha, mul_zero,
    Int.negOnePow_zero, one_smul]

variable {N} in
/-- **The twisted action adds degrees**, for the tensor-product grading of `A ⊗ Bᵐᵒᵖ`. -/
theorem envelopeTwistAction_mem (p : ℤ) {q r : ℤ} {u : A ⊗[R] Bᵐᵒᵖ}
    (hu : u ∈ ((InternalGrading.ofDecomposition 𝒜).tensorProduct
      (InternalGrading.ofDecomposition ℬ).opposite).piece q)
    {m : N} (hm : m ∈ N.grading r) : N.envelopeTwistAction p u m ∈ N.grading (q + r) := by
  refine (InternalGrading.ofDecomposition 𝒜).tensorProduct_piece_le _
    (C := (N.grading (q + r)).comap ((N.envelopeTwistAction p).flip m))
    (fun s x hx y hy ↦ ?_) hu
  rw [Submodule.mem_comap, LinearMap.flip_apply, envelopeTwistAction_tmul]
  rw [InternalGrading.ofDecomposition_piece] at hx
  have hτ := InternalGrading.koszulTwist_mem_ofDecomposition 𝒜 hx p
  have h := SetLike.GradedSMul.smul_mem hτ (SetLike.GradedSMul.smul_mem hy hm)
  simpa only [vadd_eq_add, InternalGrading.koszulTwistAlgEquiv_apply,
    show s + (q - s + r) = q + r by ring] using h

/-- The corner of a DG bimodule `N` cut out by an element `e` of `A ⊗ Bᵐᵒᵖ` in degree `q`: the
elements of degree `q` fixed by the untwisted action of `e`. -/
noncomputable def envelopeCorner (e : A ⊗[R] Bᵐᵒᵖ) (q : ℤ) : Submodule R N :=
  N.grading q ⊓ LinearMap.eqLocus (N.envelopeTwistAction 0 e) LinearMap.id

variable {N} in
theorem mem_envelopeCorner_iff {e : A ⊗[R] Bᵐᵒᵖ} {q : ℤ} {m : N} :
    m ∈ N.envelopeCorner e q ↔ m ∈ N.grading q ∧ N.envelopeTwistAction 0 e m = m := by
  rw [envelopeCorner, Submodule.mem_inf, LinearMap.mem_eqLocus, LinearMap.id_apply]

variable {N} in
/-- When the actions of `A` and `Bᵐᵒᵖ` on `N` are restricted from an action of `A ⊗ Bᵐᵒᵖ`, the
untwisted action is that action. The action of `A ⊗ Bᵐᵒᵖ` is a named argument, since it is
usually defined on a type which is only definitionally the carrier of `N`. -/
theorem envelopeTwistAction_zero_eq_smul [instE : Module (A ⊗[R] Bᵐᵒᵖ) N]
    (h : ∀ (a : A) (b : Bᵐᵒᵖ) (m : N), a • b • m = (a ⊗ₜ[R] b) • m) (u : A ⊗[R] Bᵐᵒᵖ) (m : N) :
    N.envelopeTwistAction 0 u m = u • m := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp [add_smul, hu, hu']
  | tmul a b => simp [h]

end DGBimoduleCat

namespace dgBimoduleCochains

open DGBimoduleCat

variable {M N : DGBimoduleCat hA hB}

/-- **Cochains intertwine the twisted actions.** A degree-`p` cochain intertwines the action of
`A ⊗ Bᵐᵒᵖ` on its source with the action on its target twisted by the Koszul automorphism of
parameter `p`. -/
theorem map_envelopeTwistAction {p : ℤ}
    (f : dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := M.grading) (𝒩 := N.grading) p)
    (u : A ⊗[R] Bᵐᵒᵖ) (x : M) :
    f.val.val (M.envelopeTwistAction 0 u x) = N.envelopeTwistAction p u (f.val.val x) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp [hu, hu']
  | tmul a b =>
    rw [envelopeTwistAction_zero_tmul, envelopeTwistAction_tmul,
      map_smul_left_eq_koszulTwistAlgEquiv_smul, map_smul]

/-- **Cochains from twisted-equivariant maps.** A linear map which raises degrees by `p` and
intertwines the action of `A ⊗ Bᵐᵒᵖ` on `M` with the action on `N` twisted by the Koszul
automorphism of parameter `p` is a degree-`p` bimodule cochain. -/
def ofEnvelopeTwist {p : ℤ} (g : M →ₗ[R] N) (hg : LinearMap.IsHomogeneous g M.grading N.grading p)
    (hgu : ∀ (u : A ⊗[R] Bᵐᵒᵖ) (x : M),
      g (M.envelopeTwistAction 0 u x) = N.envelopeTwistAction p u (g x)) :
    dgBimoduleCochains (B := B) (𝒜 := 𝒜) (ℳ := M.grading) (𝒩 := N.grading) p :=
  ⟨⟨{ toFun := g
      map_add' := g.map_add
      map_smul' := fun b x ↦ by
        simpa only [envelopeTwistAction_one_tmul, one_smul, RingHom.id_apply] using
          hgu (1 ⊗ₜ[R] b) x },
    dgRightModuleCochains.mem_iff.2 hg⟩, mem_iff.2 fun {r a} ha x ↦ by
      have h := hgu (a ⊗ₜ[R] 1) x
      rw [envelopeTwistAction_zero_tmul, one_smul, envelopeTwistAction_tmul_one,
        InternalGrading.koszulTwistAlgEquiv_apply_of_mem 𝒜 p ha, smul_assoc] at h
      simpa only [LinearMap.coe_mk, AddHom.coe_mk] using h⟩

@[simp]
theorem ofEnvelopeTwist_apply {p : ℤ} (g : M →ₗ[R] N)
    (hg : LinearMap.IsHomogeneous g M.grading N.grading p)
    (hgu : ∀ (u : A ⊗[R] Bᵐᵒᵖ) (x : M),
      g (M.envelopeTwistAction 0 u x) = N.envelopeTwistAction p u (g x)) (x : M) :
    (ofEnvelopeTwist g hg hgu).val.val x = g x :=
  (rfl)

end dgBimoduleCochains

end TauCeti
