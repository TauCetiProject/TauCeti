/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Twisted subalgebras supported on monoid images

An injective homomorphism of monoids realizes its pullback twisted monoid algebra as the
subalgebra supported on its image. The scalar semiring need not be nontrivial, and the image
need not be a subgroup or a coordinate cone.
-/

public noncomputable section

namespace TauCeti.TwistedMonoidAlgebra

variable {R M G : Type*} [CommSemiring R] [Monoid M] [Monoid G]
  (α : G → G → Rˣ) [IsFactorSet α] (f : M →* G)

/-- The twisted subalgebra spanned by the basis indices in a monoid image. -/
def supported : Subalgebra R (twistedMonoidAlgebra R G α) :=
  Submodule.toSubalgebra (Submodule.span R (Set.range fun m ↦ (of (f m) :
    twistedMonoidAlgebra R G α))) (by
      rw [← of_one]
      exact Submodule.subset_span ⟨1, by simp only [map_one]⟩) (by
      refine fun x y hx hy ↦ Submodule.mul_le.1 ?_ x hx y hy
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      dsimp only
      rw [of_mul_of]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a * b, by dsimp only; rw [map_mul]⟩))

/-- The underlying module is the span of the monomials in the image. -/
@[simp]
theorem supported_toSubmodule :
    (supported α f).toSubmodule = Submodule.span R (Set.range fun m ↦
      (of (f m) : twistedMonoidAlgebra R G α)) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- Membership in the supported subalgebra is exactly support in the monoid image. -/
theorem mem_supported_iff (x : twistedMonoidAlgebra R G α) :
    x ∈ supported α f ↔ ↑((basis R G α).repr x).support ⊆ Set.range f := by
  rw [← Subalgebra.mem_toSubmodule, supported_toSubmodule]
  rw [show (Set.range fun m ↦ (of (f m) : twistedMonoidAlgebra R G α)) =
      (basis R G α) '' Set.range f by
    simp only [basis_apply]
    exact Set.range_comp' _ _]
  exact Module.Basis.mem_span_image _

private def supportedModuleEquiv :
    Submodule.span R (Set.range fun m ↦ (of (f m) : twistedMonoidAlgebra R G α)) ≃ₗ[R]
      supported α f :=
  (LinearEquiv.ofEq _ _ (supported_toSubmodule α f).symm).trans
    (supported α f).toSubmoduleEquiv

private theorem coe_supportedModuleEquiv (x) :
    (supportedModuleEquiv α f x : twistedMonoidAlgebra R G α) = x := by
  have h := LinearEquiv.coe_ofEq_apply
    (rfl : (supported α f).toSubmodule = (supported α f).toSubmodule)
    (LinearEquiv.ofEq _ _ (supported_toSubmodule α f).symm x)
  have h' : (supportedModuleEquiv α f x : twistedMonoidAlgebra R G α) =
      (LinearEquiv.ofEq _ _ (supported_toSubmodule α f).symm x :
        (supported α f).toSubmodule) := by
    simpa only [supportedModuleEquiv, LinearEquiv.trans_apply,
      Subalgebra.toSubmoduleEquiv] using h
  exact h'.trans (LinearEquiv.coe_ofEq_apply _ _)

/-- The image monomials form a basis of the supported subalgebra when the index map is injective. -/
def supportedBasis (hf : Function.Injective f) : Module.Basis M R (supported α f) :=
  by
    have hi : LinearIndependent R (fun m ↦ (of (f m) : twistedMonoidAlgebra R G α)) := by
      simpa only [Function.comp_def, basis_apply] using
        (basis R G α).linearIndependent.comp f hf
    exact (Module.Basis.span hi).map (supportedModuleEquiv α f)

/-- Supported basis vectors are the ambient basis monomials at the image indices. -/
@[simp]
theorem coe_supportedBasis_apply (hf : Function.Injective f) (m : M) :
    (supportedBasis α f hf m : twistedMonoidAlgebra R G α) = of (f m) := by
  simp only [supportedBasis, Module.Basis.map_apply, coe_supportedModuleEquiv,
    Module.Basis.coe_span_apply]

/-- Restricted coefficients are the original coefficients at image indices. -/
@[simp]
theorem supportedBasis_repr_apply (hf : Function.Injective f) (x : supported α f) (m : M) :
    (supportedBasis α f hf).repr x m =
      (basis R G α).repr (x : twistedMonoidAlgebra R G α) (f m) := by
  have h : ((Finsupp.lapply m).comp (supportedBasis α f hf).repr.toLinearMap :
      supported α f →ₗ[R] R) =
      (Finsupp.lapply (f m)).comp ((basis R G α).repr.toLinearMap.comp
        (supported α f).toSubmodule.subtype) := by
    apply (supportedBasis α f hf).ext
    intro n
    change ((supportedBasis α f hf).repr (supportedBasis α f hf n)) m =
      (basis R G α).repr (supportedBasis α f hf n : twistedMonoidAlgebra R G α) (f m)
    rw [Module.Basis.repr_self, coe_supportedBasis_apply, repr_of]
    classical
    simp only [Finsupp.single_apply, hf.eq_iff]
  exact LinearMap.congr_fun h x

local instance : IsFactorSet (fun a b : M ↦ α (f a) (f b)) := IsFactorSet.comp f α

/-- Pullback along an injective monoid map identifies the twisted algebra with its supported
ambient subalgebra. -/
def supportedEquiv (hf : Function.Injective f) :
    twistedMonoidAlgebra R M (fun a b ↦ α (f a) (f b)) ≃ₐ[R] supported α f := by
  let g := lift (α := fun a b ↦ α (f a) (f b))
    (fun m ↦ supportedBasis α f hf m) (by
      apply Subtype.ext
      simp only [coe_supportedBasis_apply, map_one, of_one, Subalgebra.coe_one]) (by
      intro a b
      apply Subtype.ext
      simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, coe_supportedBasis_apply,
        of_mul_of, map_mul])
  let e := (basis R M (fun a b ↦ α (f a) (f b))).equiv (supportedBasis α f hf) (Equiv.refl M)
  have he : g.toLinearMap = e.toLinearMap := by
    apply (basis R M (fun a b ↦ α (f a) (f b))).ext
    intro m
    simp only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
    rw [show e = (basis R M (fun a b ↦ α (f a) (f b))).equiv
      (supportedBasis α f hf) (Equiv.refl M) from rfl, Module.Basis.equiv_apply]
    simp only [basis_apply, g, lift_of, Equiv.refl_apply]
  apply AlgEquiv.ofBijective g
  have hb : Function.Bijective e := e.bijective
  have hfun : (g : _ → _) = e := by
    funext x
    have hx := LinearMap.congr_fun he x
    simpa only [AlgHom.toLinearMap_apply, LinearEquiv.coe_coe] using hx
  rwa [hfun]

/-- The supported equivalence sends each source basis element to the restricted basis vector. -/
@[simp]
theorem supportedEquiv_of (hf : Function.Injective f) (m : M) :
    supportedEquiv α f hf (of m) = supportedBasis α f hf m := by
  simp only [supportedEquiv, AlgEquiv.ofBijective_apply, lift_of]

end TauCeti.TwistedMonoidAlgebra
