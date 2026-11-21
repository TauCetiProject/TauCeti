/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Algebra.MvPolynomial.Laurent.Partial

/-!
# Mixed quantum Laurent subalgebras

A mixed quantum Laurent algebra permits negative powers in a chosen set of coordinates,
while the other coordinates remain polynomial. It is the actual subalgebra of the based
quantum torus spanned by normalized monomials at the exponents `LaurentRing.nonnegOutside S`.
The permitted monomials form a basis, so membership is exactly the corresponding support
condition. No order, domain, finite-rank or generic-parameter hypothesis is needed.

The subalgebra at the ordinary parameter agrees with the corresponding ordinary partially
Laurent algebra under the normalized untwisting map. The coefficient semiring may be trivial;
monomial membership therefore records the alternative that its coefficient is zero.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4.
-/

public section

namespace TauCeti.QuantumTorus

variable {R I : Type*} [CommSemiring R] {u : Rˣ}
  {Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)} {S T : Set I}

/-- The mixed quantum Laurent subalgebra, allowing negative powers only in `S`. -/
noncomputable def partiallyLaurent (u : Rˣ) (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ))
    (S : Set I) : Subalgebra R (QuantumTorus R (I →₀ ℤ) u Λ) :=
  Submodule.toSubalgebra
    (Submodule.span R (monomial u Λ '' (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))))
    (by
      rw [← monomial_zero]
      exact Submodule.subset_span ⟨0, (LaurentRing.nonnegOutside S).zero_mem, rfl⟩)
    (by
      refine fun x y hx hy ↦ Submodule.mul_le.1 ?_ x hx y hy
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      dsimp only
      rw [monomial_mul_monomial]
      exact Submodule.smul_mem _ _ (Submodule.subset_span
        ⟨a + b, (LaurentRing.nonnegOutside S).add_mem ha hb, rfl⟩))

/-- The underlying module is the span of the permitted normalized monomials. -/
@[simp]
theorem partiallyLaurent_toSubmodule :
    (partiallyLaurent u Λ S).toSubmodule =
      Submodule.span R (monomial u Λ '' (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

/-- Mixed Laurent membership is support on exponents nonnegative outside the inverted set. -/
theorem mem_partiallyLaurent_iff (f : QuantumTorus R (I →₀ ℤ) u Λ) :
    f ∈ partiallyLaurent u Λ S ↔
      ∀ a ∈ ((basis u Λ).repr f).support, ∀ i ∉ S, 0 ≤ a i := by
  rw [← Subalgebra.mem_toSubmodule, partiallyLaurent_toSubmodule]
  have hm : monomial u Λ = (basis u Λ : (I →₀ ℤ) → QuantumTorus R (I →₀ ℤ) u Λ) :=
    (funext basis_apply).symm
  rw [hm, Module.Basis.mem_span_image]
  simp only [Set.subset_def, SetLike.mem_coe, LaurentRing.mem_nonnegOutside]

/-- A scalar monomial is permitted when its coefficient vanishes or its exponent is allowed. -/
@[simp]
theorem smul_monomial_mem_partiallyLaurent_iff (r : R) (a : I →₀ ℤ) :
    r • monomial u Λ a ∈ partiallyLaurent u Λ S ↔ r = 0 ∨ ∀ i ∉ S, 0 ≤ a i := by
  classical
  rw [mem_partiallyLaurent_iff]
  simp only [map_smul, basis_repr_monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hr : r = 0 <;> simp [hr]

/-- A normalized monomial is permitted if its exponent is allowed or its scalars are trivial. -/
@[simp]
theorem monomial_mem_partiallyLaurent_iff (a : I →₀ ℤ) :
    monomial u Λ a ∈ partiallyLaurent u Λ S ↔ (1 : R) = 0 ∨ ∀ i ∉ S, 0 ≤ a i := by
  simpa only [one_smul] using smul_monomial_mem_partiallyLaurent_iff (u := u) (Λ := Λ) 1 a

/-- Enlarging the inverted set enlarges the mixed quantum Laurent subalgebra. -/
theorem partiallyLaurent_mono (hST : S ⊆ T) :
    partiallyLaurent u Λ S ≤ partiallyLaurent u Λ T := by
  intro f hf
  exact (mem_partiallyLaurent_iff f).mpr fun a ha i hi ↦
    (mem_partiallyLaurent_iff f).mp hf a ha i (fun hs ↦ hi (hST hs))

/-- Inverting every coordinate recovers the full quantum torus. -/
@[simp]
theorem partiallyLaurent_univ : partiallyLaurent u Λ (Set.univ : Set I) = ⊤ := by
  ext f
  simp [mem_partiallyLaurent_iff]

/-- Permitted normalized monomials form a basis of the mixed quantum Laurent subalgebra. -/
noncomputable def partiallyLaurentBasis (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (S : Set I) :
    Module.Basis (LaurentRing.nonnegOutside S) R (partiallyLaurent u Λ S) :=
  (Module.Basis.span (show LinearIndependent R
      (fun a : LaurentRing.nonnegOutside S ↦ monomial u Λ (a : I →₀ ℤ)) from by
    simpa only [Function.comp_def, basis_apply] using
      (basis u Λ).linearIndependent.comp
        (fun a : LaurentRing.nonnegOutside S ↦ (a : I →₀ ℤ)) Subtype.val_injective)).map
      ((LinearEquiv.ofEq _ (partiallyLaurent u Λ S).toSubmodule (by
        rw [partiallyLaurent_toSubmodule]
        congr 1
        exact (Set.image_eq_range (monomial u Λ)
          (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))).symm)).trans
            (partiallyLaurent u Λ S).toSubmoduleEquiv)

/-- The restricted basis has the same ambient normalized monomials. -/
@[simp]
theorem coe_partiallyLaurentBasis_apply (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ S a : QuantumTorus R (I →₀ ℤ) u Λ) =
      monomial u Λ (a : I →₀ ℤ) := by
  unfold partiallyLaurentBasis
  rw [Module.Basis.map_apply]
  exact Module.Basis.coe_span_apply _ a

/-- Restricted basis coordinates are exactly the ambient quantum monomial coefficients. -/
@[simp]
theorem partiallyLaurentBasis_repr_apply (f : partiallyLaurent u Λ S)
    (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ S).repr f a =
      (basis u Λ).repr (f : QuantumTorus R (I →₀ ℤ) u Λ) (a : I →₀ ℤ) := by
  classical
  have he : (partiallyLaurentBasis u Λ S).coord a =
      ((basis u Λ).coord (a : I →₀ ℤ)).comp (partiallyLaurent u Λ S).val.toLinearMap := by
    apply (partiallyLaurentBasis u Λ S).ext
    intro b
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.comp_apply,
      AlgHom.toLinearMap_apply, Subalgebra.val_apply, coe_partiallyLaurentBasis_apply,
      basis_repr_monomial,
      Finsupp.single_apply, Subtype.ext_iff]
  exact LinearMap.congr_fun he f

/-- Untwisting carries the mixed quantum subalgebra to the ordinary partially Laurent algebra. -/
theorem map_partiallyLaurent_untwistedEquiv (h : ∀ a b, u ^ (Λ a b) = 1) :
    (partiallyLaurent u Λ S).map (untwistedEquiv u Λ h).toAlgHom =
      LaurentRing.partiallyLaurent R S := by
  apply Subalgebra.toSubmodule_injective
  rw [Subalgebra.map_toSubmodule, partiallyLaurent_toSubmodule,
    AlgEquiv.toAlgHom_toLinearMap, Submodule.map_span]
  have hm : (untwistedEquiv u Λ h).toLinearMap ∘ monomial u Λ =
      (fun a : I →₀ ℤ ↦ AddMonoidAlgebra.single a (1 : R)) := by
    funext a
    exact untwistedEquiv_monomial h a
  rw [← Set.image_comp, hm]
  ext f
  have hb : (AddMonoidAlgebra.basis (I →₀ ℤ) R : (I →₀ ℤ) → LaurentRing R I) =
      (fun a ↦ AddMonoidAlgebra.single a 1) := funext fun a ↦ AddMonoidAlgebra.basis_apply R a
  rw [← hb, Module.Basis.mem_span_image, Subalgebra.mem_toSubmodule,
    LaurentRing.mem_partiallyLaurent_iff]
  simp only [AddMonoidAlgebra.basis_repr, Set.subset_def,
    SetLike.mem_coe, LaurentRing.mem_nonnegOutside]

/-- When the twist is trivial, the mixed quantum subalgebra is the ordinary partial Laurent ring. -/
noncomputable def partiallyLaurentUntwistedEquiv (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ (I →₀ ℤ)) (h : ∀ a b, u ^ (Λ a b) = 1) (S : Set I) :
    partiallyLaurent u Λ S ≃ₐ[R] LaurentRing.partiallyLaurent R S :=
  ((untwistedEquiv u Λ h).subalgebraMap (partiallyLaurent u Λ S)).trans
    (Subalgebra.equivOfEq _ _ (map_partiallyLaurent_untwistedEquiv h))

/-- The ordinary comparison agrees with the ambient normalized untwisting map. -/
@[simp]
theorem coe_partiallyLaurentUntwistedEquiv_apply (h : ∀ a b, u ^ (Λ a b) = 1)
    (f : partiallyLaurent u Λ S) :
    (partiallyLaurentUntwistedEquiv u Λ h S f : LaurentRing R I) =
      untwistedEquiv u Λ h (f : QuantumTorus R (I →₀ ℤ) u Λ) := by
  simp only [partiallyLaurentUntwistedEquiv, AlgEquiv.trans_apply,
    Subalgebra.equivOfEq_apply]
  exact RingEquiv.subsemiringMap_apply_coe _ _ f

end TauCeti.QuantumTorus
