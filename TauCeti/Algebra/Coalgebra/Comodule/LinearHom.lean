/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Evaluation
public import TauCeti.Algebra.Coalgebra.Comodule.Transport
public import TauCeti.Algebra.Coalgebra.Comodule.Fixed
public import TauCeti.LinearAlgebra.LinearMap.BaseChange

/-!
# Linear Hom comodules

For comodules `M` and `N` over a Hopf algebra, with `M` finite projective,
`Hom_R(M,N)` is a comodule by transport from the diagonal tensor comodule `M* ⊗ N`.
On algebra-valued points its action is `f ↦ g_N ∘ f ∘ g_M⁻¹`. In particular, taking
`N = M` gives the conjugation representation on endomorphisms, used to construct
representations with prescribed normal kernels. For a commutative Hopf algebra, the fixed
vectors are exactly the comodule morphisms.

The order `M* ⊗ N` is part of this construction. Over a noncommutative Hopf algebra,
swapping it to `N ⊗ M*` need not be colinear, and the identity endomorphism need not be
fixed in the former. The fixed-morphism characterization below therefore retains
commutative coefficients.

The construction uses `Comodule.dual`, `Comodule.tensor`, `Comodule.Transport` and Mathlib's
`dualTensorHomEquiv`; the point formula uses the existing inverse-point evaluation identity.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* J. S. Milne, *Algebraic Groups* (2017), §4.a and §5.c.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x y

variable {R : Type u} {H : Type v} {M : Type w} {N : Type x}
variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [Module.Finite R M] [Module.Projective R M]

noncomputable section

attribute [local instance] dual tensor

section Hom

variable [Semiring H] [HopfAlgebra R H] [Comodule R H M] [Comodule R H N]

/-- The comodule of linear maps from a finite projective comodule to an arbitrary comodule,
with the contragredient action on the source. This is an explicit structure, not a global
instance, so different coactions on the same linear Hom space can coexist. -/
@[implicit_reducible]
def linearHom : Comodule R H (M →ₗ[R] N) :=
  Transport (C := H) (dualTensorHomEquiv R M N)

attribute [local instance] linearHom

/-- The Hom coaction is transported from the tensor product of the dual and the target. -/
@[simp]
theorem linearHom_coact (f : M →ₗ[R] N) :
    coact (R := R) (C := H) f =
      TensorProduct.map (dualTensorHom R M N) LinearMap.id
        (coact (R := R) (C := H) ((dualTensorHomEquiv R M N).symm f)) := by
  simp only [transport_coact_apply, toLinearMap_dualTensorHomEquiv]

variable {A : Type y} [CommSemiring A] [Algebra R A]

/-- Under scalar extension of linear Hom, an algebra-valued point acts by conjugating
with its actions on the target and source. -/
@[simp↓]
theorem baseChangeTensorHom_endOfPoint_linearHom
    (g : WithConv (H →ₐ[R] A)) (f : A ⊗[R] (M →ₗ[R] N)) :
    LinearMap.baseChangeTensorHom R A M N
        (endOfPoint (M →ₗ[R] N) g.ofConv f) =
      endOfPoint N g.ofConv ∘ₗ LinearMap.baseChangeTensorHom R A M N f ∘ₗ
        endOfPoint M (g⁻¹).ofConv := by
  let e := dualTensorHomEquiv R M N
  let q := transportToHom (C := H) e
  have hsurj : Function.Surjective ((dualTensorHom R M N).baseChange A) := by
    simpa only [← LinearEquiv.coe_toLinearMap, LinearEquiv.coe_baseChange, e,
      toLinearMap_dualTensorHomEquiv] using
      (e.baseChange R A _ _).surjective
  obtain ⟨t, rfl⟩ := hsurj f
  have hn := baseChange_comp_endOfPoint q g.ofConv
  have hq : q.toLinearMap = dualTensorHom R M N :=
    (transportToHom_toLinearMap e).trans (toLinearMap_dualTensorHomEquiv ..)
  simp only [hq] at hn
  have hn' := LinearMap.congr_fun hn t
  simp only [LinearMap.comp_apply] at hn'
  rw [← hn']
  clear hn'
  induction t using TensorProduct.inductionOn with
  | add t t' h h' =>
      simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, h, h']
  | tmul a t =>
      induction t using TensorProduct.inductionOn with
      | add t t' h h' =>
          simp only [TensorProduct.tmul_add, map_add, LinearMap.comp_add,
            LinearMap.add_comp, h, h']
      | tmul φ n =>
          rw [← one_mul a, ← endOfPoint_tensor_tmul]
          simp only [one_mul]
          apply LinearMap.ext
          intro z
          rw [LinearMap.baseChangeTensorHom_distribBaseChange_symm_tmul]
          simp only [LinearMap.comp_apply, baseChangeEvaluation_dual_endOfPoint]
          rw [LinearMap.baseChange_tmul, LinearMap.baseChangeTensorHom_tmul,
            LinearMap.smul_apply]
          have heval := LinearMap.baseChangeTensorHom_distribBaseChange_symm_tmul
            (1 ⊗ₜ[R] φ) (a ⊗ₜ[R] n) (endOfPoint M (g⁻¹).ofConv z)
          simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
            one_mul, LinearMap.baseChange_tmul, LinearMap.baseChangeTensorHom_tmul,
            LinearMap.smul_apply] at heval
          rw [heval, map_smul]

/-- A scalar-extended linear map is fixed by a point in the Hom comodule exactly when it
intertwines the point actions on its source and target. -/
theorem endOfPoint_linearHom_one_tmul_eq_iff
    (g : WithConv (H →ₐ[R] A)) (f : M →ₗ[R] N) :
    endOfPoint (M →ₗ[R] N) g.ofConv (1 ⊗ₜ[R] f) = 1 ⊗ₜ[R] f ↔
      f.baseChange A ∘ₗ endOfPoint M g.ofConv =
        endOfPoint N g.ofConv ∘ₗ f.baseChange A := by
  have hpoint := baseChangeTensorHom_endOfPoint_linearHom g (1 ⊗ₜ[R] f)
  simp only [LinearMap.baseChangeTensorHom_tmul, one_smul] at hpoint
  constructor
  · intro hf
    rw [hf, LinearMap.baseChangeTensorHom_tmul, one_smul] at hpoint
    have h := congrArg (fun q ↦ q ∘ₗ endOfPoint M g.ofConv) hpoint
    simpa only [LinearMap.comp_assoc, endOfPoint_inv_comp, LinearMap.comp_id] using h
  · intro hf
    apply (LinearMap.baseChangeTensorHomEquiv
      (R := R) (A := A) (M := M) (N := N)).injective
    simp only [LinearMap.baseChangeTensorHomEquiv_apply,
      LinearMap.baseChangeTensorHom_tmul, one_smul]
    rw [hpoint, ← LinearMap.comp_assoc, ← hf, LinearMap.comp_assoc,
      endOfPoint_comp_inv, LinearMap.comp_id]

end Hom

section Fixed

attribute [local instance] linearHom

variable [CommSemiring H] [HopfAlgebra R H] [Comodule R H M] [Comodule R H N]

/-- The fixed vectors in the linear Hom comodule are exactly the colinear linear maps.
This criterion includes nonreduced Hopf algebras and needs no hypothesis on geometric points. -/
@[simp↓]
theorem mem_fixedSubcomodule_linearHom_iff (f : M →ₗ[R] N) :
    f ∈ fixedSubcomodule R H (M →ₗ[R] N) ↔
      TensorProduct.map f LinearMap.id ∘ₗ coact (R := R) (C := H) =
        coact (R := R) (C := H) ∘ₗ f := by
  -- The universal point detects coaction identities without reducedness assumptions.
  let g : WithConv (H →ₐ[R] H) := toConv (AlgHom.id R H)
  constructor
  · intro hf
    rw [mem_fixedSubcomodule] at hf
    have hfixed : endOfPoint (M →ₗ[R] N) g.ofConv (1 ⊗ₜ[R] f) = 1 ⊗ₜ[R] f := by
      simp only [endOfPoint_tmul, hf, one_smul, LinearMap.lTensor_tmul,
        AlgHom.toLinearMap_apply, g, AlgHom.id_apply, TensorProduct.comm_tmul]
    have hintertwine := (endOfPoint_linearHom_one_tmul_eq_iff g f).mp hfixed
    apply LinearMap.ext
    intro m
    apply (TensorProduct.comm R N H).injective
    have h := LinearMap.congr_fun hintertwine (1 ⊗ₜ[R] m)
    simp only [LinearMap.comp_apply, endOfPoint_tmul, one_smul, g,
      AlgHom.toLinearMap_id, LinearMap.lTensor_id, LinearMap.id_apply,
      LinearMap.baseChange_tmul] at h
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.lTensor_comm, LinearMap.rTensor_def] at h
    exact h
  · intro hf
    -- Naturality of a comodule morphism makes its conjugation action trivial.
    let q : Hom R H M N := ⟨f, hf⟩
    have hintertwine : f.baseChange H ∘ₗ endOfPoint M g.ofConv =
        endOfPoint N g.ofConv ∘ₗ f.baseChange H := baseChange_comp_endOfPoint q g.ofConv
    have hfixed := (endOfPoint_linearHom_one_tmul_eq_iff g f).mpr hintertwine
    rw [mem_fixedSubcomodule]
    apply (TensorProduct.comm R (M →ₗ[R] N) H).injective
    simpa only [endOfPoint_tmul, one_smul, g, AlgHom.toLinearMap_id,
      LinearMap.lTensor_id, LinearMap.id_apply, TensorProduct.comm_tmul] using hfixed

/-- Comodule morphisms are the fixed vectors of the linear Hom comodule. -/
def fixedLinearHomEquiv :
    fixedSubcomodule R H (M →ₗ[R] N) ≃ₗ[R] Hom R H M N where
  toFun f := ⟨f.1, (mem_fixedSubcomodule_linearHom_iff f.1).mp f.2⟩
  invFun f := ⟨f.toLinearMap, (mem_fixedSubcomodule_linearHom_iff f.toLinearMap).mpr
    f.map_coact⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fixed-Hom equivalence preserves the underlying linear map. -/
@[simp]
theorem fixedLinearHomEquiv_toLinearMap (f : fixedSubcomodule R H (M →ₗ[R] N)) :
    (fixedLinearHomEquiv f).toLinearMap = f.1 :=
  (rfl)

/-- The inverse fixed-Hom equivalence preserves the underlying linear map. -/
@[simp]
theorem fixedLinearHomEquiv_symm_coe (f : Hom R H M N) :
    ((fixedLinearHomEquiv (R := R) (H := H)).symm f : M →ₗ[R] N) = f.toLinearMap :=
  (rfl)

end Fixed

end

end TauCeti.Comodule
