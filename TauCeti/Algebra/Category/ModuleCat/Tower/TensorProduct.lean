/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Finite tensor products and compatible families

Tensoring a tower with a module gives a canonical map from the tensor product of its limit
to the limit of its tensor products. For a finite free coefficient module this map is an
isomorphism, without any hypothesis on the transitions. In particular, finite-dimensional
coefficient extension over a field commutes with compatible families of module quotients.
This is the inverse-limit step in extending coefficients of a left-ideal completion; it
makes no assertion that arbitrary tensor products commute with inverse limits.

`ModuleTower.lTensorLimEquiv` is independent of a basis: its forward map is the canonical
comparison `ModuleTower.lTensorLim`, characterized by its projections. A finite basis is used
only to prove bijectivity. Both the coefficient module and the tower can vary naturally.

The compatible-family carrier and projections are those of `ModuleTower.lim`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1.2, for completed enveloping
  algebras presented by inverse limits of module quotients.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Opposite TensorProduct

universe u v

variable {R : Type u} [CommRing R] (F : ModuleTower.{v} R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensor a tower levelwise with the fixed coefficient module `M` on the left. -/
-- The levelwise definition allows different ring and module universes, unlike the native
-- monoidal structure on ModuleCat, whose unit requires those universes to coincide.
abbrev lTensor : ModuleTower.{v} R where
  obj n := ModuleCat.of R (M ⊗[R] F.obj n)
  map f := ModuleCat.ofHom ((F.map f).hom.lTensor M)
  map_id n := by
    apply ModuleCat.hom_ext
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp [LinearMap.lTensor_comp]

/-- The transitions of a tensor tower are the tensor products of the original transitions. -/
@[simp]
theorem lTensor_transition (n : ℕ) :
    (F.lTensor M).transition n = (F.transition n).lTensor M := by
  rw [transition_def, transition_def]
  exact ModuleCat.hom_ofHom _

/-- The canonical comparison from a tensor product of compatible families to compatible
families of tensor products. No finiteness assumption is needed to define it. -/
def lTensorLim : M ⊗[R] F.lim →ₗ[R] (F.lTensor M).lim :=
  (F.lTensor M).limLift (fun n => (F.limπ n).lTensor M) fun n => by
    rw [lTensor_transition, ← LinearMap.lTensor_comp, F.transition_comp_limπ]

/-- Projection characterizes the tensor-limit comparison on every tensor, not only pure ones. -/
theorem limπ_lTensorLim (n : ℕ) (x : M ⊗[R] F.lim) :
    (F.lTensor M).limπ n (F.lTensorLim M x) = (F.limπ n).lTensor M x := by
  rw [lTensorLim, ← LinearMap.comp_apply, limπ_comp_limLift]

/-- The coordinates of the compatible family produced by the canonical comparison. -/
@[simp]
theorem coe_lTensorLim_apply (x : M ⊗[R] F.lim) (n : ℕ) :
    (F.lTensorLim M x : (F.lTensor M).Product) n = (F.limπ n).lTensor M x := by
  rw [← limπ_apply, F.limπ_lTensorLim M]

/-- The comparison is bijective whenever the coefficient module has a finite basis. -/
theorem lTensorLim_bijective_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι R M) :
    Function.Bijective (F.lTensorLim M) := by
  classical
  let := Fintype.ofFinite ι
  -- Tensor coordinates and their naturality come from TensorProduct.equivFinsuppOfBasisLeft
  -- and Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply.
  let c {N : Type v} [AddCommGroup N] [Module R N] :=
    TensorProduct.equivFinsuppOfBasisLeft (N := N) b
  have hc {N P : Type v} [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
      (g : N →ₗ[R] P) (x : M ⊗[R] N) (i : ι) :
      c (g.lTensor M x) i = g (c x i) :=
    b.equivFinsuppOfBasisLeft_lTensor_apply g x i
  refine ⟨?_, ?_⟩
  · intro x y h
    apply c.injective
    apply Finsupp.ext
    intro i
    apply F.lim_ext
    intro n
    have hn := congrArg (fun z => c ((F.lTensor M).limπ n z) i) h
    rw [F.limπ_lTensorLim M, F.limπ_lTensorLim M, hc, hc] at hn
    exact hn
  · intro y
    let z (i : ι) : F.lim :=
      ⟨fun n => c ((F.lTensor M).limπ n y) i, F.mem_lim.mpr fun n => by
        rw [← hc, ← lTensor_transition, ← LinearMap.comp_apply,
          (F.lTensor M).transition_comp_limπ]⟩
    let x : M ⊗[R] F.lim := c.symm (Finsupp.equivFunOnFinite.symm z)
    refine ⟨x, (F.lTensor M).lim_ext fun n => ?_⟩
    apply c.injective
    ext i
    rw [F.limπ_lTensorLim M, hc]
    simp only [x, LinearEquiv.apply_symm_apply, Finsupp.coe_equivFunOnFinite_symm]
    simp only [limπ_apply, z]

/-- Tensor a morphism of towers and a coefficient-module map levelwise. -/
def tensorMap {F G : ModuleTower.{v} R} {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : F ⟶ G) (f : M →ₗ[R] N) : F.lTensor M ⟶ G.lTensor N where
  app n := ModuleCat.ofHom (TensorProduct.map f (φ.app n).hom)
  naturality n k g := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.lTensor_tmul, TensorProduct.map_tmul]
    exact congrArg (fun y => f m ⊗ₜ y) (congr($(φ.naturality g).hom x))

@[simp]
theorem tensorMap_app_hom {F G : ModuleTower.{v} R} {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : F ⟶ G) (f : M →ₗ[R] N) (n : ℕᵒᵖ) :
    ((tensorMap φ f).app n).hom = TensorProduct.map f (φ.app n).hom :=
  (rfl)

@[simp]
theorem tensorMap_id : tensorMap (𝟙 F) (LinearMap.id : M →ₗ[R] M) = 𝟙 (F.lTensor M) := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m x
  simp [tensorMap]

/-- Tensor maps compose in both the coefficient module and the tower. -/
@[simp]
theorem tensorMap_comp {F G H : ModuleTower.{v} R} {M N P : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (φ : F ⟶ G) (ψ : G ⟶ H)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    tensorMap (φ ≫ ψ) (g ∘ₗ f) = tensorMap φ f ≫ tensorMap ψ g := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m x
  simp [tensorMap]

/-- The tensor-limit comparison is natural simultaneously in the tower and the coefficients. -/
theorem lTensorLim_naturality {G : ModuleTower.{v} R} {N : Type v}
    [AddCommGroup N] [Module R N] (φ : F ⟶ G) (f : M →ₗ[R] N) :
    limMap (tensorMap φ f) ∘ₗ F.lTensorLim M =
      G.lTensorLim N ∘ₗ TensorProduct.map f (limMap φ) := by
  apply TensorProduct.ext'
  intro m x
  apply (G.lTensor N).lim_ext
  intro n
  have hφ := LinearMap.congr_fun (limπ_comp_limMap φ n) x
  have h := LinearMap.congr_fun (limπ_comp_limMap (tensorMap φ f) n)
    (F.lTensorLim M (m ⊗ₜ x))
  simp only [LinearMap.comp_apply, F.limπ_lTensorLim M, LinearMap.lTensor_tmul,
    tensorMap_app_hom, TensorProduct.map_tmul] at h
  simpa only [LinearMap.comp_apply, TensorProduct.map_tmul, G.limπ_lTensorLim N,
    LinearMap.lTensor_tmul] using
    h.trans (congrArg (fun y => f m ⊗ₜ y) hφ.symm)

variable [Module.Free R M] [Module.Finite R M]

/-- Tensoring with a finite free coefficient module commutes with the limit of an arbitrary
module tower. Over a field this applies to every finite-dimensional coefficient algebra. -/
def lTensorLimEquiv : M ⊗[R] F.lim ≃ₗ[R] (F.lTensor M).lim :=
  LinearEquiv.ofBijective (F.lTensorLim M)
    (F.lTensorLim_bijective_of_basis M (Module.Free.chooseBasis R M))

@[simp]
theorem lTensorLimEquiv_apply (x : M ⊗[R] F.lim) :
    F.lTensorLimEquiv M x = F.lTensorLim M x :=
  (rfl)

/-- The inverse comparison is characterized by its coordinates in each tower term. -/
@[simp]
theorem lTensor_limπ_lTensorLimEquiv_symm (n : ℕ) (y : (F.lTensor M).lim) :
    (F.limπ n).lTensor M ((F.lTensorLimEquiv M).symm y) =
      (y : (F.lTensor M).Product) n := by
  rw [← limπ_lTensorLim, ← lTensorLimEquiv_apply, LinearEquiv.apply_symm_apply, limπ_apply]

end TauCeti.ModuleTower
