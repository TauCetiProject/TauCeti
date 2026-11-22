/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
public import TauCeti.Algebra.MonoidAlgebra.Twisted.Supported
public import TauCeti.Algebra.MvPolynomial.Laurent.Partial

/-!
# Mixed quantum Laurent subalgebras

A mixed quantum Laurent algebra permits negative powers in a chosen set of coordinates,
while the other coordinates remain polynomial. It is the actual subalgebra of the based
quantum torus with a chosen lattice basis. Permitted exponents pull back
`LaurentRing.nonnegOutside S` along the basis representation.
The permitted monomials form a basis, so membership is exactly the corresponding support
condition. No order, domain, finite-rank or generic-parameter hypothesis is needed.

The subalgebra at the ordinary parameter agrees with the corresponding ordinary partially
Laurent algebra under the normalized untwisting map. The coefficient semiring may be trivial;
monomial membership therefore records the alternative that its coefficient is zero.

The mixed membership, monotonicity and basis interfaces follow
`TauCeti.Algebra.MvPolynomial.Laurent.Partial`, in particular the ordinary
`LaurentRing.partiallyLaurent` and `LaurentRing.partiallyLaurentBasis` APIs.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4.
-/

public section

namespace TauCeti.QuantumTorus

variable {R L I : Type*} [CommSemiring R] [AddCommGroup L] {u : Rˣ}
  {Λ : LinearMap.BilinForm ℤ L} {b : Module.Basis I ℤ L} {S T : Set I}

private noncomputable def partiallyLaurentIndex (b : Module.Basis I ℤ L) (S : Set I) :
    Multiplicative (LaurentRing.nonnegOutside S) →* Multiplicative L :=
  AddMonoidHom.toMultiplicative
    (b.repr.symm.toLinearMap.toAddMonoidHom.comp (LaurentRing.nonnegOutside S).subtype)

private theorem partiallyLaurentIndex_injective :
    Function.Injective (partiallyLaurentIndex b S) := by
  intro a c h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply b.repr.symm.injective
  have he := congrArg Multiplicative.toAdd h
  simpa only [partiallyLaurentIndex, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_toLinearMap, AddSubmonoid.subtype_apply, toAdd_ofAdd] using he

/-- The mixed quantum Laurent subalgebra in a chosen lattice basis. Negative coordinates
are allowed only in `S`. It specializes support on an injective monoid image. -/
noncomputable def partiallyLaurent (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) : Subalgebra R (QuantumTorus R L u Λ) :=
  TwistedMonoidAlgebra.supported (factorSet u Λ) (partiallyLaurentIndex b S)

/-- The underlying module is the span of the permitted normalized monomials. -/
@[simp]
theorem partiallyLaurent_toSubmodule :
    (partiallyLaurent u Λ b S).toSubmodule =
      Submodule.span R ((fun a ↦ monomial u Λ (b.repr.symm a)) ''
        (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))) := by
  rw [partiallyLaurent, TwistedMonoidAlgebra.supported_toSubmodule]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.toAdd, a.toAdd.property, by
      simp only [partiallyLaurentIndex, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
        AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_toLinearMap, AddSubmonoid.subtype_apply, monomial_def]⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨Multiplicative.ofAdd ⟨a, ha⟩, by
      simp only [partiallyLaurentIndex, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
        AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_toLinearMap, AddSubmonoid.subtype_apply, toAdd_ofAdd, monomial_def]⟩

/-- Membership is support on lattice exponents with nonnegative coordinates outside `S`. -/
theorem mem_partiallyLaurent_iff (f : QuantumTorus R L u Λ) :
    f ∈ partiallyLaurent u Λ b S ↔
      ∀ a ∈ ((basis u Λ).repr f).support, ∀ i ∉ S, 0 ≤ b.repr a i := by
  rw [← Subalgebra.mem_toSubmodule, partiallyLaurent_toSubmodule]
  have hi : (fun a ↦ monomial u Λ (b.repr.symm a)) ''
      (LaurentRing.nonnegOutside S : Set (I →₀ ℤ)) =
        monomial u Λ '' (b.repr ⁻¹' (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))) := by
    simpa only [← Set.image_comp, Function.comp_def] using
      congrArg (fun t ↦ monomial u Λ '' t)
        (b.repr.image_symm_eq_preimage (LaurentRing.nonnegOutside S : Set (I →₀ ℤ)))
  have hm : monomial u Λ = (basis u Λ : L → QuantumTorus R L u Λ) :=
    (funext basis_apply).symm
  rw [hi, hm, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Set.mem_preimage, SetLike.mem_coe, LaurentRing.mem_nonnegOutside]

/-- A scalar monomial is permitted when its coefficient vanishes or its coordinates are allowed. -/
@[simp]
theorem smul_monomial_mem_partiallyLaurent_iff (r : R) (a : L) :
    r • monomial u Λ a ∈ partiallyLaurent u Λ b S ↔ r = 0 ∨ ∀ i ∉ S, 0 ≤ b.repr a i := by
  classical
  rw [mem_partiallyLaurent_iff]
  simp only [map_smul, basis_repr_monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
  by_cases hr : r = 0 <;> simp [hr]

/-- A normalized monomial is permitted if its coordinates are allowed or its scalars are trivial. -/
@[simp]
theorem monomial_mem_partiallyLaurent_iff (a : L) :
    monomial u Λ a ∈ partiallyLaurent u Λ b S ↔
      (1 : R) = 0 ∨ ∀ i ∉ S, 0 ≤ b.repr a i := by
  simpa only [one_smul] using smul_monomial_mem_partiallyLaurent_iff
    (u := u) (Λ := Λ) (b := b) 1 a

/-- A scalar monomial at a bundled permitted exponent has no remaining coordinate condition. -/
theorem smul_monomial_mem_partiallyLaurent (r : R) (a : LaurentRing.nonnegOutside S) :
    r • monomial u Λ (b.repr.symm (a : I →₀ ℤ)) ∈ partiallyLaurent u Λ b S := by
  apply (smul_monomial_mem_partiallyLaurent_iff r _).mpr
  right
  simpa only [LinearEquiv.apply_symm_apply] using
    (LaurentRing.mem_nonnegOutside.mp a.property)

/-- A normalized monomial at a bundled permitted exponent belongs to the mixed algebra. -/
theorem monomial_mem_partiallyLaurent (a : LaurentRing.nonnegOutside S) :
    monomial u Λ (b.repr.symm (a : I →₀ ℤ)) ∈ partiallyLaurent u Λ b S := by
  simpa only [one_smul] using
    (smul_monomial_mem_partiallyLaurent (u := u) (Λ := Λ) (b := b) 1 a)

/-- Enlarging the inverted set enlarges the mixed quantum Laurent subalgebra. -/
theorem partiallyLaurent_mono (hST : S ⊆ T) :
    partiallyLaurent u Λ b S ≤ partiallyLaurent u Λ b T := by
  intro f hf
  exact (mem_partiallyLaurent_iff f).mpr fun a ha i hi ↦
    (mem_partiallyLaurent_iff f).mp hf a ha i (fun hs ↦ hi (hST hs))

/-- Inverting every coordinate recovers the full quantum torus. -/
@[simp]
theorem partiallyLaurent_univ : partiallyLaurent u Λ b (Set.univ : Set I) = ⊤ := by
  ext f
  simp [mem_partiallyLaurent_iff]

/-- Containment of the mixed algebra can be tested on its permitted normalized monomials. -/
theorem partiallyLaurent_le_iff (A : Subalgebra R (QuantumTorus R L u Λ)) :
    partiallyLaurent u Λ b S ≤ A ↔ ∀ a : LaurentRing.nonnegOutside S,
      monomial u Λ (b.repr.symm (a : I →₀ ℤ)) ∈ A := by
  change (partiallyLaurent u Λ b S).toSubmodule ≤ A.toSubmodule ↔ _
  rw [partiallyLaurent_toSubmodule, Submodule.span_le, Set.image_eq_range, Set.range_subset_iff]
  rfl

/-- Permitted normalized monomials form a basis in the chosen lattice coordinates. -/
noncomputable def partiallyLaurentBasis (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) :
    Module.Basis (LaurentRing.nonnegOutside S) R (partiallyLaurent u Λ b S) :=
  (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective).reindex Multiplicative.toAdd

/-- The restricted basis has the same ambient normalized monomials. -/
@[simp]
theorem coe_partiallyLaurentBasis_apply (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ b S a : QuantumTorus R L u Λ) =
      monomial u Λ (b.repr.symm (a : I →₀ ℤ)) := by
  change ((TwistedMonoidAlgebra.supportedBasis (factorSet u Λ)
    (partiallyLaurentIndex b S) partiallyLaurentIndex_injective).reindex
      Multiplicative.toAdd a : QuantumTorus R L u Λ) = _
  rw [Module.Basis.reindex_apply, TwistedMonoidAlgebra.coe_supportedBasis_apply]
  simp only [Multiplicative.toAdd_symm_eq, partiallyLaurentIndex,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap, AddSubmonoid.subtype_apply,
    toAdd_ofAdd, monomial_def]

/-- Restricted basis coordinates are the ambient quantum coefficients in the chosen basis. -/
@[simp]
theorem partiallyLaurentBasis_repr_apply (f : partiallyLaurent u Λ b S)
    (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ b S).repr f a =
      (basis u Λ).repr (f : QuantumTorus R L u Λ) (b.repr.symm (a : I →₀ ℤ)) := by
  have h : ((Finsupp.lapply a).comp (partiallyLaurentBasis u Λ b S).repr.toLinearMap :
      partiallyLaurent u Λ b S →ₗ[R] R) =
      (Finsupp.lapply (b.repr.symm (a : I →₀ ℤ))).comp
        ((basis u Λ).repr.toLinearMap.comp (partiallyLaurent u Λ b S).toSubmodule.subtype) := by
    apply (partiallyLaurentBasis u Λ b S).ext
    intro c
    change ((partiallyLaurentBasis u Λ b S).repr (partiallyLaurentBasis u Λ b S c)) a =
      (basis u Λ).repr (partiallyLaurentBasis u Λ b S c : QuantumTorus R L u Λ)
        (b.repr.symm (a : I →₀ ℤ))
    rw [Module.Basis.repr_self, coe_partiallyLaurentBasis_apply, basis_repr_monomial]
    classical
    simp only [Finsupp.single_apply, b.repr.symm.injective.eq_iff, Subtype.coe_inj]
  exact LinearMap.congr_fun h f

/-- Increasing the inverted set preserves each permitted basis vector intrinsically. -/
@[simp]
theorem inclusion_partiallyLaurentBasis (hST : S ⊆ T) (a : LaurentRing.nonnegOutside S) :
    Subalgebra.inclusion (partiallyLaurent_mono (u := u) (Λ := Λ) (b := b) hST)
      (partiallyLaurentBasis u Λ b S a) =
        partiallyLaurentBasis u Λ b T ⟨a, LaurentRing.mem_nonnegOutside.mpr
          (fun i hi ↦ (LaurentRing.mem_nonnegOutside.mp a.property) i (fun h ↦ hi (hST h)))⟩ := by
  apply Subtype.ext
  simp only [Subalgebra.coe_inclusion, coe_partiallyLaurentBasis_apply]

/-- The zero coordinate of the restricted basis is the algebra unit. -/
@[simp]
theorem partiallyLaurentBasis_zero : partiallyLaurentBasis u Λ b S 0 = 1 := by
  apply Subtype.ext
  simp only [coe_partiallyLaurentBasis_apply, ZeroMemClass.coe_zero,
    map_zero, monomial_zero, Subalgebra.coe_one]

/-- Restricted basis multiplication retains the ambient twist and adds its coordinate indices. -/
@[simp]
theorem partiallyLaurentBasis_mul (a c : LaurentRing.nonnegOutside S) :
    partiallyLaurentBasis u Λ b S a * partiallyLaurentBasis u Λ b S c =
      (u ^ (Λ (b.repr.symm (a : I →₀ ℤ)) (b.repr.symm (c : I →₀ ℤ))) : Rˣ).val •
        partiallyLaurentBasis u Λ b S (a + c) := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_smul, coe_partiallyLaurentBasis_apply,
    monomial_mul_monomial, AddSubmonoid.coe_add, map_add]

/-- The original factor set restricted to the permitted coordinate monoid. -/
noncomputable def partiallyLaurentFactorSet (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I)
    (a c : Multiplicative (LaurentRing.nonnegOutside S)) : Rˣ :=
  factorSet u Λ (partiallyLaurentIndex b S a) (partiallyLaurentIndex b S c)

/-- The restricted factor set evaluates the form on the corresponding lattice vectors. -/
@[simp]
theorem partiallyLaurentFactorSet_apply (a c : Multiplicative (LaurentRing.nonnegOutside S)) :
    partiallyLaurentFactorSet u Λ b S a c =
      u ^ (Λ (b.repr.symm (a.toAdd : I →₀ ℤ)) (b.repr.symm (c.toAdd : I →₀ ℤ))) := by
  simp only [partiallyLaurentFactorSet, factorSet_apply, partiallyLaurentIndex,
    AddMonoidHom.coe_toMultiplicative, Function.comp_apply, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap,
    AddSubmonoid.subtype_apply, toAdd_ofAdd]

instance : IsFactorSet (partiallyLaurentFactorSet u Λ b S) :=
  IsFactorSet.comp (partiallyLaurentIndex b S) (factorSet u Λ)

/-- The mixed algebra is the twisted monoid algebra on its permitted coordinate indices. -/
noncomputable def partiallyLaurentEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) :
    twistedMonoidAlgebra R (Multiplicative (LaurentRing.nonnegOutside S))
      (partiallyLaurentFactorSet u Λ b S) ≃ₐ[R] partiallyLaurent u Λ b S :=
  TwistedMonoidAlgebra.supportedEquiv (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective

/-- The twisted realization preserves the normalized permitted basis. -/
@[simp]
theorem partiallyLaurentEquiv_of (a : Multiplicative (LaurentRing.nonnegOutside S)) :
    partiallyLaurentEquiv u Λ b S (TwistedMonoidAlgebra.of a) =
      partiallyLaurentBasis u Λ b S a.toAdd := by
  have h := TwistedMonoidAlgebra.supportedEquiv_of (factorSet u Λ)
    (partiallyLaurentIndex b S) partiallyLaurentIndex_injective a
  have hb : partiallyLaurentBasis u Λ b S a.toAdd =
      TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
        partiallyLaurentIndex_injective a := by
    change (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
      partiallyLaurentIndex_injective).reindex Multiplicative.toAdd a.toAdd = _
    rw [Module.Basis.reindex_apply]
    simp only [Multiplicative.toAdd_symm_eq, ofAdd_toAdd]
  exact h.trans hb.symm

/-- The inverse realization sends each permitted basis vector to its twisted basis element. -/
@[simp]
theorem partiallyLaurentEquiv_symm_basis (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentEquiv u Λ b S).symm (partiallyLaurentBasis u Λ b S a) =
      TwistedMonoidAlgebra.of (Multiplicative.ofAdd a) := by
  apply (partiallyLaurentEquiv u Λ b S).symm_apply_eq.mpr
  simpa only [toAdd_ofAdd] using (partiallyLaurentEquiv_of (u := u) (Λ := Λ) (b := b)
    (Multiplicative.ofAdd a)).symm

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Algebra maps from the mixed algebra are determined on the permitted monomials alone. -/
@[ext]
theorem partiallyLaurent_algHom_ext {f g : partiallyLaurent u Λ b S →ₐ[R] A}
    (h : ∀ a, f (partiallyLaurentBasis u Λ b S a) = g (partiallyLaurentBasis u Λ b S a)) :
    f = g :=
  AlgHom.toLinearMap_injective ((partiallyLaurentBasis u Λ b S).ext h)

/-- Extend a family on permitted exponents satisfying its restricted twisted product law.
No value or invertibility condition is required at forbidden exponents. -/
noncomputable def partiallyLaurentLift (g : LaurentRing.nonnegOutside S → A) (h0 : g 0 = 1)
    (hm : ∀ a c, g a * g c =
      (u ^ (Λ (b.repr.symm (a : I →₀ ℤ)) (b.repr.symm (c : I →₀ ℤ))) : Rˣ).val • g (a + c)) :
    partiallyLaurent u Λ b S →ₐ[R] A :=
  (TwistedMonoidAlgebra.lift (α := partiallyLaurentFactorSet u Λ b S)
    (fun a ↦ g a.toAdd) (by simpa using h0) (by
    intro a c
    simpa only [partiallyLaurentFactorSet_apply, toAdd_mul] using hm a.toAdd c.toAdd)).comp
      (partiallyLaurentEquiv u Λ b S).symm.toAlgHom

/-- The mixed lift takes the prescribed value at each permitted normalized monomial. -/
@[simp]
theorem partiallyLaurentLift_basis (g : LaurentRing.nonnegOutside S → A) (h0 : g 0 = 1)
    (hm : ∀ a c, g a * g c =
      (u ^ (Λ (b.repr.symm (a : I →₀ ℤ)) (b.repr.symm (c : I →₀ ℤ))) : Rˣ).val • g (a + c))
    (a : LaurentRing.nonnegOutside S) :
    partiallyLaurentLift g h0 hm (partiallyLaurentBasis u Λ b S a) = g a := by
  simp only [partiallyLaurentLift, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    partiallyLaurentEquiv_symm_basis, TwistedMonoidAlgebra.lift_of, toAdd_ofAdd]

end Lift

/-- Untwisting in the chosen lattice basis gives the ordinary partially Laurent algebra. -/
theorem map_partiallyLaurent_untwistedEquiv (h : ∀ a c, u ^ (Λ a c) = 1) :
    (partiallyLaurent u Λ b S).map
      ((untwistedEquiv u Λ h).trans
        (AddMonoidAlgebra.domCongr R R b.repr.toAddEquiv)).toAlgHom =
      LaurentRing.partiallyLaurent R S := by
  apply Subalgebra.toSubmodule_injective
  rw [Subalgebra.map_toSubmodule, partiallyLaurent_toSubmodule,
    AlgEquiv.toAlgHom_toLinearMap, Submodule.map_span]
  have hm : ((untwistedEquiv u Λ h).trans
      (AddMonoidAlgebra.domCongr R R b.repr.toAddEquiv)).toLinearEquiv.toLinearMap ∘
      (fun a ↦ monomial u Λ (b.repr.symm a)) =
      (fun a : I →₀ ℤ ↦ AddMonoidAlgebra.single a (1 : R)) := by
    funext a
    simp only [Function.comp_apply, LinearEquiv.coe_coe, AlgEquiv.coe_toLinearEquiv,
      AlgEquiv.trans_apply, untwistedEquiv_monomial, AddMonoidAlgebra.domCongr_single,
      LinearEquiv.coe_toAddEquiv, LinearEquiv.coe_addEquiv_apply,
      LinearEquiv.apply_symm_apply]
  rw [← Set.image_comp, hm]
  exact LaurentRing.partiallyLaurent_toSubmodule.symm

/-- Trivial twist identifies the mixed algebra with the ordinary partial Laurent ring in
its chosen lattice coordinates. -/
noncomputable def partiallyLaurentUntwistedEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (h : ∀ a c, u ^ (Λ a c) = 1) (S : Set I) :
    partiallyLaurent u Λ b S ≃ₐ[R] LaurentRing.partiallyLaurent R S :=
  (((untwistedEquiv u Λ h).trans
    (AddMonoidAlgebra.domCongr R R b.repr.toAddEquiv)).subalgebraMap
      (partiallyLaurent u Λ b S)).trans
    (Subalgebra.equivOfEq _ _ (map_partiallyLaurent_untwistedEquiv h))

/-- The restricted comparison agrees with untwisting followed by the chosen coordinate map. -/
@[simp]
theorem coe_partiallyLaurentUntwistedEquiv_apply (h : ∀ a c, u ^ (Λ a c) = 1)
    (f : partiallyLaurent u Λ b S) :
    (partiallyLaurentUntwistedEquiv u Λ b h S f : LaurentRing R I) =
      AddMonoidAlgebra.domCongr R R b.repr.toAddEquiv
        (untwistedEquiv u Λ h (f : QuantumTorus R L u Λ)) := by
  simp only [partiallyLaurentUntwistedEquiv, AlgEquiv.trans_apply,
    Subalgebra.equivOfEq_apply, AlgEquiv.subalgebraMap_apply_coe]

/-- Untwisting takes the mixed basis to the ordinary partially Laurent basis at the same index. -/
@[simp]
theorem partiallyLaurentUntwistedEquiv_basis (h : ∀ a c, u ^ (Λ a c) = 1)
    (a : LaurentRing.nonnegOutside S) :
    partiallyLaurentUntwistedEquiv u Λ b h S (partiallyLaurentBasis u Λ b S a) =
      LaurentRing.partiallyLaurentBasis R S a := by
  apply Subtype.ext
  simp only [coe_partiallyLaurentUntwistedEquiv_apply, coe_partiallyLaurentBasis_apply,
    untwistedEquiv_monomial, AddMonoidAlgebra.domCongr_single, LinearEquiv.coe_toAddEquiv,
    LinearEquiv.coe_addEquiv_apply, LinearEquiv.apply_symm_apply,
    LaurentRing.coe_partiallyLaurentBasis_apply]

end TauCeti.QuantumTorus
