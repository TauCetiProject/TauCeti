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

variable {R M G : Type*} [CommSemiring R] [MulOne M] [Monoid G]
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
theorem supported_toSubmodule :
    (supported α f).toSubmodule = Submodule.span R (Set.range fun m ↦
      (of (f m) : twistedMonoidAlgebra R G α)) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- Every monomial indexed by the image belongs to the supported algebra. -/
theorem of_mem_supported (m : M) :
    (of (f m) : twistedMonoidAlgebra R G α) ∈ supported α f := by
  rw [← Subalgebra.mem_toSubmodule, supported_toSubmodule]
  exact Submodule.subset_span ⟨m, rfl⟩

/-- Containment of a supported subalgebra is determined on its image monomials. -/
theorem supported_le_iff (A : Subalgebra R (twistedMonoidAlgebra R G α)) :
    supported α f ≤ A ↔ ∀ m, of (f m) ∈ A := by
  rw [← Subalgebra.toSubmodule.le_iff_le, supported_toSubmodule,
    Submodule.span_le, Set.range_subset_iff]
  exact forall_congr' fun _ ↦ Subalgebra.mem_toSubmodule A

/-- Membership in the supported subalgebra is exactly support in the monoid image. -/
theorem mem_supported_iff (x : twistedMonoidAlgebra R G α) :
    x ∈ supported α f ↔ ↑((basis R G α).repr x).support ⊆ Set.range f := by
  have hRange : (Set.range fun m ↦ (of (f m) : twistedMonoidAlgebra R G α)) =
      (basis R G α) '' Set.range f := by
    simp only [basis_apply]
    exact Set.range_comp' _ _
  rw [← Subalgebra.mem_toSubmodule, supported_toSubmodule, hRange]
  exact Module.Basis.mem_span_image _

/-- A scalar multiple of an ambient monomial lies in the supported algebra exactly when
the coefficient vanishes or the index belongs to the source image. -/
@[simp]
theorem smul_of_mem_supported_iff (r : R) (g : G) :
    r • (of g : twistedMonoidAlgebra R G α) ∈ supported α f ↔ r = 0 ∨ g ∈ Set.range f := by
  classical
  rw [mem_supported_iff]
  simp only [map_smul, repr_of, Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hr : r = 0 <;> simp [hr]

/-- An ambient monomial belongs to the supported algebra when its index belongs to the
source image or the scalar semiring is trivial. -/
@[simp]
theorem of_mem_supported_iff (g : G) :
    (of g : twistedMonoidAlgebra R G α) ∈ supported α f ↔ (1 : R) = 0 ∨ g ∈ Set.range f := by
  simpa only [one_smul] using smul_of_mem_supported_iff α f 1 g

private def supportedModuleEquiv :
    Submodule.span R (Set.range fun m ↦ (of (f m) : twistedMonoidAlgebra R G α)) ≃ₗ[R]
      supported α f :=
  LinearEquiv.ofEq _ _ (supported_toSubmodule α f).symm

private theorem coe_supportedModuleEquiv (x) :
    (supportedModuleEquiv α f x : twistedMonoidAlgebra R G α) = x :=
  LinearEquiv.coe_ofEq_apply (supported_toSubmodule α f).symm x

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

/-- The restricted basis at the identity index is the subalgebra unit. -/
@[simp]
theorem supportedBasis_one (hf : Function.Injective f) : supportedBasis α f hf 1 = 1 := by
  apply Subtype.ext
  simp only [coe_supportedBasis_apply, map_one, of_one, Subalgebra.coe_one]

/-- Multiplying supported basis vectors uses the ambient factor set and the source product. -/
@[simp]
theorem supportedBasis_mul (hf : Function.Injective f) (a b : M) :
    supportedBasis α f hf a * supportedBasis α f hf b =
      (α (f a) (f b) : R) • supportedBasis α f hf (a * b) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, coe_supportedBasis_apply, of_mul_of, map_mul]

/-- Restricted coefficients are the original coefficients at image indices. -/
@[simp]
theorem supportedBasis_repr_apply (hf : Function.Injective f) (x : supported α f) (m : M) :
    (supportedBasis α f hf).repr x m =
      (basis R G α).repr (x : twistedMonoidAlgebra R G α) (f m) := by
  let F := (Finsupp.lcomapDomain (R := R) f hf).comp
    ((basis R G α).repr.toLinearMap.comp (supported α f).val.toLinearMap)
  have h : (supportedBasis α f hf).repr.toLinearMap = F := by
    apply Module.Basis.repr_eq_iff.mpr
    intro n
    simp only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.val_apply,
      LinearEquiv.coe_coe, coe_supportedBasis_apply, repr_of, Finsupp.lcomapDomain_apply,
      Finsupp.comapDomain_single]
  simpa only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.val_apply,
    LinearEquiv.coe_coe, Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply] using
      congrArg (fun c : M →₀ R ↦ c m) (LinearMap.congr_fun h x)

/-- The factor set pulled back along a monoid homomorphism. -/
abbrev pullbackFactorSet (a b : M) : Rˣ := α (f a) (f b)

section Equiv

variable {N : Type*} [Monoid N] (g : N →* G)

instance : IsFactorSet (pullbackFactorSet α g) := IsFactorSet.comp g α

/-- Pullback along an injective monoid map identifies the twisted algebra with its supported
ambient subalgebra. -/
def supportedEquiv (hf : Function.Injective g) :
    twistedMonoidAlgebra R N (pullbackFactorSet α g) ≃ₐ[R] supported α g :=
  let F := lift (α := pullbackFactorSet α g) (supportedBasis α g hf)
    (supportedBasis_one α g hf) (supportedBasis_mul α g hf)
  let e := (basis R N (pullbackFactorSet α g)).equiv (supportedBasis α g hf) (Equiv.refl N)
  AlgEquiv.ofBijective F (by
    have he : F.toLinearMap = e.toLinearMap := by
      apply (basis R N (pullbackFactorSet α g)).ext
      intro m
      dsimp only [e, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
      rw [Module.Basis.equiv_apply]
      simp only [basis_apply, F, lift_of, Equiv.refl_apply]
    have hfun : (F : _ → _) = (e : _ → _) := congrArg DFunLike.coe he
    rw [hfun]
    exact e.bijective)

/-- The supported equivalence sends each source basis element to the restricted basis vector. -/
@[simp]
theorem supportedEquiv_of (hf : Function.Injective g) (m : N) :
    supportedEquiv α g hf (of m) = supportedBasis α g hf m := by
  simp only [supportedEquiv, AlgEquiv.ofBijective_apply, lift_of]

/-- The inverse supported equivalence sends each restricted basis vector to its source monomial. -/
@[simp]
theorem supportedEquiv_symm_basis (hf : Function.Injective g) (m : N) :
    (supportedEquiv α g hf).symm (supportedBasis α g hf m) = of m := by
  rw [← supportedEquiv_of α g hf m, AlgEquiv.symm_apply_apply]

end Equiv

end TauCeti.TwistedMonoidAlgebra
