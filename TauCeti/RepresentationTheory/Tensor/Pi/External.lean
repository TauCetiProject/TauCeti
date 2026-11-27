/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.RepresentationTheory.Irreducible
public import TauCeti.RepresentationTheory.Tensor.Pi.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import TauCeti.LinearAlgebra.PiTensorProduct.Dual
import TauCeti.LinearAlgebra.PiTensorProduct.Hom
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.Irreducible

/-!
# External tensor products over finite families

The product of monoids acts on the tensor product of a family of modules by acting in each
coordinate through its own representation. Over an algebraically closed field, the external
tensor product of a finite family of finite-dimensional irreducibles is irreducible. The proof
uses Burnside density on the factors and the canonical comparison of the tensor product of the
endomorphism spaces with the endomorphism space of the tensor product.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Springer GTM 129 (1991),
  Exercise 2.36 for the two-factor case.
* P. Etingof et al., *Introduction to Representation Theory*, AMS (2011),
  Theorem 3.10.2(i) for the density argument.
-/

public section

open scoped TensorProduct

namespace Representation

variable {ι : Type*} {G V : ι → Type*}

section Semiring

variable [∀ i, Monoid (G i)]
variable {R : Type*} [CommSemiring R] [∀ i, AddCommMonoid (V i)] [∀ i, Module R (V i)]

/-- The external tensor product of a family of representations of possibly different monoids.
A tuple of monoid elements acts on the tensor product by its action in each factor. -/
noncomputable def piExternalTensor (ρ : ∀ i, Representation R (G i) (V i)) :
    Representation R (∀ i, G i) (⨂[R] i, V i) :=
  piTensorProduct fun i ↦ (ρ i).comp (Pi.evalMonoidHom G i)

/-- The endomorphism associated to a tuple is the tensor of the component endomorphisms. -/
theorem piExternalTensor_apply (ρ : ∀ i, Representation R (G i) (V i)) (g : ∀ i, G i) :
    piExternalTensor ρ g = PiTensorProduct.map (fun i ↦ ρ i (g i)) := by
  simp [piExternalTensor, piTensorProduct_apply]

/-- The action of a tuple on a pure tensor is the tensor of the actions in its coordinates. -/
@[simp]
theorem piExternalTensor_apply_tprod (ρ : ∀ i, Representation R (G i) (V i))
    (g : ∀ i, G i) (v : ∀ i, V i) :
    piExternalTensor ρ g (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R fun i ↦ ρ i (g i) (v i) := by
  rw [piExternalTensor_apply, PiTensorProduct.map_tprod]

/-- In a tensor product basis the matrix entry of an external tensor product is the product of
the corresponding matrix entries in each factor. -/
theorem toMatrix_piExternalTensor [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (ρ : ∀ i, Representation R (G i) (V i)) (b : ∀ i, Module.Basis (κ i) R (V i))
    (g : ∀ i, G i) (p q : ∀ i, κ i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b)
        (piExternalTensor ρ g) p q =
      ∏ i, LinearMap.toMatrix (b i) (b i) (ρ i (g i)) (p i) (q i) := by
  classical
  simp [LinearMap.toMatrix_apply]

/-- Factorwise equivariant equivalences induce an equivalence of external tensor products. -/
noncomputable def Equiv.piExternalTensor {W : ι → Type*} [∀ i, AddCommMonoid (W i)]
    [∀ i, Module R (W i)] {ρ : ∀ i, Representation R (G i) (V i)}
    {σ : ∀ i, Representation R (G i) (W i)} (e : ∀ i, (ρ i).Equiv (σ i)) :
    (piExternalTensor ρ).Equiv (piExternalTensor σ) :=
  .mk (PiTensorProduct.congr fun i ↦ (e i).toLinearEquiv) fun g ↦
    PiTensorProduct.ext <| MultilinearMap.ext fun v ↦ by
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
        piExternalTensor_apply_tprod, PiTensorProduct.congr_tprod]
      exact congrArg (PiTensorProduct.tprod R)
        (funext fun i ↦ IntertwiningMap.isIntertwining (ρ i) (σ i)
          (e i).toIntertwiningMap (g i) (v i))

@[simp]
theorem Equiv.piExternalTensor_tprod {W : ι → Type*} [∀ i, AddCommMonoid (W i)]
    [∀ i, Module R (W i)] {ρ : ∀ i, Representation R (G i) (V i)}
    {σ : ∀ i, Representation R (G i) (W i)} (e : ∀ i, (ρ i).Equiv (σ i)) (v : ∀ i, V i) :
    Equiv.piExternalTensor e (PiTensorProduct.tprod R v) =
      PiTensorProduct.tprod R (fun i ↦ e i (v i)) :=
  PiTensorProduct.congr_tprod _ _

end Semiring

section Dual

variable {R : Type*} [CommRing R] [Finite ι] [∀ i, Group (G i)]
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
  [∀ i, Module.Finite R (V i)] [∀ i, Module.Free R (V i)]

/-- The external tensor product of the contragredients is the contragredient of the external
tensor product for a finite family of finite free representations. -/
noncomputable def piExternalTensorDualEquiv (ρ : ∀ i, Representation R (G i) (V i)) :
    (piExternalTensor fun i ↦ (ρ i).dual).Equiv (piExternalTensor ρ).dual :=
  .mk PiTensorProduct.dualDistribEquiv fun g ↦ by
    let _ := Fintype.ofFinite ι
    refine PiTensorProduct.ext <| MultilinearMap.ext fun f ↦ ?_
    refine PiTensorProduct.ext <| MultilinearMap.ext fun v ↦ ?_
    simp [PiTensorProduct.dualDistribEquiv, LinearMap.compMultilinearMap_apply,
      Representation.dual_apply, Module.Dual.transpose_apply, piExternalTensor_apply_tprod]

/-- The tensor of functionals acts on a pure tensor by multiplying their evaluations. -/
@[simp]
theorem piExternalTensorDualEquiv_tprod_apply [Fintype ι]
    (ρ : ∀ i, Representation R (G i) (V i)) (f : ∀ i, Module.Dual R (V i)) (v : ∀ i, V i) :
    piExternalTensorDualEquiv ρ (PiTensorProduct.tprod R f) (PiTensorProduct.tprod R v) =
      ∏ i, f i (v i) :=
  PiTensorProduct.dualDistrib_apply f v

end Dual

section Field

variable [∀ i, Monoid (G i)]
variable {k : Type*} [Field k] [Finite ι] [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, FiniteDimensional k (V i)]

/-- Over an algebraically closed field, the external tensor product of a finite family of
finite-dimensional irreducible representations is irreducible. -/
theorem isIrreducible_piExternalTensor [IsAlgClosed k]
    (ρ : ∀ i, Representation k (G i) (V i)) (hρ : ∀ i, (ρ i).IsIrreducible) :
    (piExternalTensor ρ).IsIrreducible := by
  classical
  have : ∀ i, Nontrivial (V i) := fun i ↦ (hρ i).nontrivial
  choose v hv using fun i ↦ exists_ne (0 : V i)
  have : Nontrivial (⨂[k] i, V i) := nontrivial_of_ne _ _ (PiTensorProduct.tprod_ne_zero hv)
  refine isIrreducible_of_asAlgebraHom_surjective _ ?_
  rw [← AlgHom.range_eq_top, ← Algebra.toSubmodule_eq_top, toSubmodule_range_asAlgebraHom]
  let e := PiTensorProduct.piTensorHomEquiv k V V
  have hspan := PiTensorProduct.submodule_span_eq_top
    (fun i ↦ span_range_eq_top_of_isIrreducible (hρ i))
  have himage : (Set.range (piExternalTensor ρ)) =
      e.toLinearMap '' Set.range (fun g : ∀ i, G i ↦
        PiTensorProduct.tprod k fun i ↦ ρ i (g i)) := by
    rw [← Set.range_comp]
    congr 1
    funext g
    rw [Function.comp_apply, LinearEquiv.coe_coe, piExternalTensor_apply]
    exact (PiTensorProduct.piTensorHomEquiv_tprod _).symm
  rw [himage, Submodule.span_image, hspan, Submodule.map_top, LinearMap.range_eq_top]
  exact e.surjective

end Field

end Representation
