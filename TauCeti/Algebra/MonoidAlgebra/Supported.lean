/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.Algebra.Algebra.Bilinear
import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Support submodules of additive monoid algebras

Mathlib's `AddMonoidAlgebra.supported` fixes the set of allowed exponents in a monoid algebra.
The supported characters form a basis, so extending scalars changes only their coefficients.
Convolution restricts to a bilinear map whenever addition of exponents lands in the target
support set. An additive submonoid acts on a support submodule when its exponents preserve
the support set, and a translate of the submonoid gives a free module of rank one.
-/

public section

open scoped Pointwise TensorProduct

namespace AddMonoidAlgebra

variable {M : Type*} {R S T : Type*}

section Basis

variable [Semiring R] (s : Set M)

/-- The monomial basis of the submodule supported on `s`, indexed by the elements of `s`. -/
noncomputable def basisSupported : Module.Basis s R (supported R R s) :=
  Module.Basis.ofRepr (supportedEquivFinsupp s)

/-- The coordinates in the supported monomial basis are the corresponding coefficients. -/
@[simp]
theorem basisSupported_repr_apply (f : supported R R s) (m : s) :
    (basisSupported s).repr f m = (f : R[M]).coeff m :=
  (rfl)

/-- A supported monomial basis vector is the monomial with coefficient one at its index. -/
@[simp]
theorem coe_basisSupported (m : s) :
    (basisSupported (R := R) s m : R[M]) = single (m : M) 1 := by
  classical
  simp [basisSupported, supportedEquivFinsupp]

end Basis

section Coefficients

variable [Semiring R] [Semiring S] [Semiring T] (s : Set M)

/-- Apply a ring homomorphism to the coefficients of a supported monoid-algebra element. -/
noncomputable def supportedMap (φ : R →+* S) :
    supported R R s →ₛₗ[φ] supported S S s :=
  (supportedEquivFinsupp s).symm.toLinearMap.comp <|
    (Finsupp.mapRange.linearMap φ.toSemilinearMap).comp (supportedEquivFinsupp s).toLinearMap

/-- Coefficient change applies the given map to each coefficient. -/
@[simp]
theorem coeff_supportedMap (φ : R →+* S) (f : supported R R s) (m : M) :
    (supportedMap s φ f : S[M]).coeff m = φ ((f : R[M]).coeff m) := by
  classical
  by_cases hm : m ∈ s
  · let j : s := ⟨m, hm⟩
    rw [← basisSupported_repr_apply s _ j, ← basisSupported_repr_apply s f j]
    simp [supportedMap, basisSupported]
  · rw [mem_supported'.1 (supportedMap s φ f).property m hm, mem_supported'.1 f.property m hm,
      map_zero]

/-- Coefficient change of a supported element agrees with coefficient change in the ambient
algebra. -/
theorem coe_supportedMap [AddMonoid M] (φ : R →+* S) (f : supported R R s) :
    (supportedMap s φ f : S[M]) = mapRingHom M φ f := by
  ext m
  simp

@[simp]
theorem supportedMap_id (f : supported R R s) : supportedMap s (RingHom.id R) f = f := by
  apply Subtype.ext
  ext m
  simp

@[simp]
theorem supportedMap_comp (φ : R →+* S) (ψ : S →+* T) (f : supported R R s) :
    supportedMap s ψ (supportedMap s φ f) = supportedMap s (ψ.comp φ) f := by
  apply Subtype.ext
  ext m
  simp

end Coefficients

section BaseChange

variable [CommSemiring R] [Semiring S] [Algebra R S] (s : Set M)

/-- The scalar extension of the supported submodule is the submodule with the same allowed
exponents over the new coefficient semiring. -/
noncomputable def supportedBaseChange :
    S ⊗[R] supported R R s ≃ₗ[S] supported S S s :=
  (Algebra.TensorProduct.basis S (basisSupported s)).repr.trans
    (supportedEquivFinsupp s).symm

/-- On pure tensors the scalar extension is coefficient change followed by scalar multiplication. -/
@[simp]
theorem supportedBaseChange_tmul (c : S) (f : supported R R s) :
    supportedBaseChange s (c ⊗ₜ[R] f) = c • supportedMap s (algebraMap R S) f := by
  apply (basisSupported s).repr.injective
  ext m
  simp [supportedBaseChange, basisSupported, supportedMap]

end BaseChange

section Multiplication

variable [Semiring R] [Add M] {s t u : Set M}

/-- The product of two elements with restricted supports is supported on any set containing all
sums of exponents of the two support sets. -/
theorem mul_mem_supported_of_add_subset (h : s + t ⊆ u) {f g : R[M]}
    (hf : f ∈ supported R R s) (hg : g ∈ supported R R t) :
    f * g ∈ supported R R u := by
  classical
  refine mem_supported.2 fun m hm ↦ h ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  exact Set.add_mem_add (mem_supported.1 hf ha) (mem_supported.1 hg hb)

end Multiplication

section Submonoid

variable [Semiring R] [AddMonoid M] (P : AddSubmonoid M) {s : Set M}

/-- The submonoid algebra has image equal to the submodule supported on the submonoid. -/
theorem mem_range_mapDomainRingHom_subtype {f : R[M]} :
    f ∈ Set.range (mapDomainRingHom R P.subtype) ↔ f ∈ supported R R (P : Set M) := by
  -- The application lemma for the bundled map does not rewrite under `Set.range`.
  change f ∈ Set.range (mapDomain (R := R) P.subtype) ↔ _
  simp only [mem_range_mapDomain_iff, ← AddMonoidHom.coe_mrange,
    AddSubmonoid.mrange_subtype, mem_supported, Set.subset_def, Finset.mem_coe]

/-- A submonoid algebra acts by convolution on a support set stable under adding exponents
from the submonoid on the left. -/
@[instance_reducible]
noncomputable def supportedModule (h : (P : Set M) + s ⊆ s) :
    Module (AddMonoidAlgebra R P) (supported R R s) := by
  let e := mapDomainRingHom R P.subtype
  letI := Module.compHom R[M] e
  letI : SMul (AddMonoidAlgebra R P) (supported R R s) :=
    ⟨fun g f ↦ ⟨e g * f.val, mul_mem_supported_of_add_subset h
      ((mem_range_mapDomainRingHom_subtype P).1 ⟨g, rfl⟩) f.property⟩⟩
  exact Function.Injective.module _ (supported R R s).subtype.toAddMonoidHom
    Subtype.val_injective (fun _ _ ↦ rfl)

/-- Scalar multiplication is convolution in the ambient monoid algebra. -/
@[simp]
theorem coe_smul_supportedModule (h : (P : Set M) + s ⊆ s)
    (g : AddMonoidAlgebra R P) (f : supported R R s) :
    letI := supportedModule (R := R) P h
    (↑(g • f) : R[M]) = mapDomainRingHom R P.subtype g * f.val :=
  (rfl)

end Submonoid

section Translate

variable [Semiring R] [AddCommGroup M] (P : AddSubmonoid M) {s : Set M} {m : M}

/-- A translate of an additive submonoid is stable under adding elements of the submonoid. -/
theorem _root_.AddSubmonoid.add_subset_of_eq_vadd (hs : s = m +ᵥ (P : Set M)) :
    (P : Set M) + s ⊆ s := by
  rw [hs]
  refine Set.add_subset_iff.2 fun p hp v hv ↦ ?_
  obtain ⟨q, hq, rfl⟩ := hv
  exact ⟨p + q, P.add_mem hp hq, by simp only [vadd_eq_add]; ac_rfl⟩

private theorem single_mul_single_neg {G : Type*} [AddGroup G] (g : G) :
    (single g (1 : R) : R[G]) * single (-g) 1 = 1 := by
  simp [single_mul_single, one_def]

/-- Multiplying by the monomial at `m` identifies the submonoid algebra with the module
supported on its translate by `m`. -/
noncomputable def supportedVAddEquiv (hs : s = m +ᵥ (P : Set M)) :
    letI := supportedModule (R := R) P (P.add_subset_of_eq_vadd hs)
    AddMonoidAlgebra R P ≃ₗ[AddMonoidAlgebra R P] supported R R s := by
  letI := supportedModule (R := R) P (P.add_subset_of_eq_vadd hs)
  have hm : m ∈ s := by rw [hs]; simpa using Set.vadd_mem_vadd_set (a := m) P.zero_mem
  refine LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ (basisSupported s ⟨m, hm⟩)) ?_
  refine ⟨?_, ?_⟩
  · intro g k hgk
    apply mapDomain_injective (R := R) (f := P.subtype) P.subtype_injective
    have hprod := congrArg (fun f : supported R R s ↦ f.val * single (-m) 1) hgk
    simpa only [LinearMap.toSpanSingleton_apply, coe_smul_supportedModule, coe_basisSupported,
      mul_assoc, single_mul_single_neg, mul_one, mapDomainRingHom_apply] using hprod
  · intro f
    have hsub : s + {-m} ⊆ (P : Set M) := by
      refine Set.add_subset_iff.2 fun v hv w hw ↦ ?_
      subst w
      rw [hs, Set.mem_vadd_set_iff_neg_vadd_mem] at hv
      simpa only [vadd_eq_add, add_comm] using hv
    have hsingle : single (-m) (1 : R) ∈ supported R R ({-m} : Set M) := by
      simpa only [mem_supported, coeff_single, Finsupp.mem_supported] using
        Finsupp.single_mem_supported R (1 : R) (Set.mem_singleton (-m))
    obtain ⟨g, hg⟩ := (mem_range_mapDomainRingHom_subtype P).2
      (mul_mem_supported_of_add_subset hsub f.property hsingle)
    have hinv : (single (-m) (1 : R) : R[M]) * single m 1 = 1 := by
      simpa only [neg_neg] using single_mul_single_neg (R := R) (-m)
    refine ⟨g, Subtype.ext ?_⟩
    rw [LinearMap.toSpanSingleton_apply, coe_smul_supportedModule, coe_basisSupported, hg,
      mul_assoc, hinv, mul_one]

/-- The translate frame sends a scalar to its product with the frame monomial. -/
@[simp]
theorem coe_supportedVAddEquiv (hs : s = m +ᵥ (P : Set M)) (g : AddMonoidAlgebra R P) :
    (supportedVAddEquiv P hs g : R[M]) = mapDomainRingHom R P.subtype g * single m 1 := by
  rw [supportedVAddEquiv]
  -- The defining map uses a local module instance. Matching the application lemma against it
  -- requires the higher transparency of `erw`.
  erw [LinearEquiv.ofBijective_apply]
  rw [LinearMap.toSpanSingleton_apply, coe_smul_supportedModule, coe_basisSupported]

/-- The inverse frame recovers the submonoid-algebra coordinate by multiplying by the
inverse monomial in the ambient algebra. -/
@[simp]
theorem mapDomain_supportedVAddEquiv_symm (hs : s = m +ᵥ (P : Set M))
    (f : supported R R s) :
    mapDomain Subtype.val ((supportedVAddEquiv P hs).symm f) = f.val * single (-m) 1 := by
  calc
    _ = (supportedVAddEquiv P hs ((supportedVAddEquiv P hs).symm f)).val * single (-m) 1 := by
      rw [coe_supportedVAddEquiv P hs, mul_assoc, single_mul_single_neg, mul_one,
        mapDomainRingHom_apply, AddSubmonoid.coe_subtype]
    _ = _ := by rw [LinearEquiv.apply_symm_apply]

end Translate

variable [CommSemiring R] [AddMonoid M] {s t u : Set M}

/-- Convolution on supported submodules, with the target support specified by addition of
exponents. -/
noncomputable def supportedMul (h : s + t ⊆ u) :
    supported R R s →ₗ[R] supported R R t →ₗ[R] supported R R u :=
  ((LinearMap.mul R R[M]).domRestrict₁₂ _ _).codRestrict₂
    (supported R R u).subtype (Submodule.subtype_injective _) fun f g ↦ by
      rw [LinearMap.domRestrict₁₂_apply, LinearMap.mul_apply', Submodule.range_subtype]
      exact mul_mem_supported_of_add_subset h f.property g.property

/-- The product in the supported submodule is ordinary convolution in the ambient algebra. -/
@[simp]
theorem coe_supportedMul (h : s + t ⊆ u) (f : supported R R s) (g : supported R R t) :
    (supportedMul h f g : R[M]) = (f : R[M]) * (g : R[M]) := by
  rw [← Submodule.subtype_apply, supportedMul, LinearMap.codRestrict₂_apply,
    LinearMap.domRestrict₁₂_apply, LinearMap.mul_apply']

/-- Coefficient change commutes with convolution on supported submodules. -/
@[simp]
theorem supportedMap_supportedMul [CommSemiring S] (φ : R →+* S) (h : s + t ⊆ u)
    (f : supported R R s) (g : supported R R t) :
    supportedMap u φ (supportedMul h f g) =
      supportedMul h (supportedMap s φ f) (supportedMap t φ g) := by
  apply Subtype.ext
  simp only [coe_supportedMap, coe_supportedMul, map_mul]

end AddMonoidAlgebra
