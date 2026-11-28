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

/-- Map a permitted coordinate exponent to its multiplicatively tagged lattice vector. -/
noncomputable def partiallyLaurentIndex (b : Module.Basis I ℤ L) (S : Set I) :
    Multiplicative (LaurentRing.nonnegOutside S) →* Multiplicative L :=
  AddMonoidHom.toMultiplicative
    (b.repr.symm.toLinearMap.toAddMonoidHom.comp (LaurentRing.nonnegOutside S).subtype)

/-- Removing the multiplicative tag recovers the vector in the chosen lattice basis. -/
@[simp]
theorem partiallyLaurentIndex_toAdd (a : Multiplicative (LaurentRing.nonnegOutside S)) :
    (partiallyLaurentIndex b S a).toAdd = b.repr.symm (a.toAdd : I →₀ ℤ) := by
  simp only [partiallyLaurentIndex, AddMonoidHom.coe_toMultiplicative, Function.comp_apply,
    AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap,
    AddSubmonoid.subtype_apply, toAdd_ofAdd]

/-- Permitted coordinate exponents embed injectively in the ambient lattice. -/
theorem partiallyLaurentIndex_injective :
    Function.Injective (partiallyLaurentIndex b S) := by
  intro a c h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply b.repr.symm.injective
  simpa only [partiallyLaurentIndex_toAdd] using congrArg Multiplicative.toAdd h

/-- The coordinate index sends a permitted exponent to its ambient lattice vector. -/
@[simp]
theorem partiallyLaurentIndex_ofAdd (a : LaurentRing.nonnegOutside S) :
    partiallyLaurentIndex b S (Multiplicative.ofAdd a) =
      Multiplicative.ofAdd (b.repr.symm (a : I →₀ ℤ)) := by
  apply Multiplicative.toAdd.injective
  simp only [partiallyLaurentIndex_toAdd, toAdd_ofAdd]

/-- Supported ambient basis elements at coordinate indices are the normalized quantum monomials. -/
@[simp]
theorem of_partiallyLaurentIndex (a : Multiplicative (LaurentRing.nonnegOutside S)) :
    (TwistedMonoidAlgebra.of (partiallyLaurentIndex b S a) : QuantumTorus R L u Λ) =
      monomial u Λ (b.repr.symm (a.toAdd : I →₀ ℤ)) := by
  rw [monomial_def, ← partiallyLaurentIndex_toAdd, ofAdd_toAdd]

/-- The index image consists exactly of lattice vectors whose coordinates are nonnegative
outside the inverted set. -/
theorem mem_range_partiallyLaurentIndex_iff (a : Multiplicative L) :
    a ∈ Set.range (partiallyLaurentIndex b S) ↔ ∀ i ∉ S, 0 ≤ b.repr a.toAdd i := by
  constructor
  · rintro ⟨c, rfl⟩
    simpa only [partiallyLaurentIndex_toAdd, LinearEquiv.apply_symm_apply] using
      LaurentRing.mem_nonnegOutside.mp c.toAdd.property
  · intro h
    refine ⟨Multiplicative.ofAdd ⟨b.repr a.toAdd, LaurentRing.mem_nonnegOutside.mpr h⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    simp only [partiallyLaurentIndex_toAdd, toAdd_ofAdd, LinearEquiv.symm_apply_apply]

/-- The mixed quantum Laurent subalgebra in a chosen lattice basis. Negative coordinates
are allowed only in `S`. It specializes support on an injective monoid image. -/
noncomputable def partiallyLaurent (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) : Subalgebra R (QuantumTorus R L u Λ) :=
  TwistedMonoidAlgebra.supported (factorSet u Λ) (partiallyLaurentIndex b S)

/-- The mixed subalgebra is the supported subalgebra of its coordinate-index image. -/
theorem partiallyLaurent_eq_supported :
    partiallyLaurent u Λ b S =
      TwistedMonoidAlgebra.supported (factorSet u Λ) (partiallyLaurentIndex b S) := by
  ext f
  rw [partiallyLaurent]

/-- The underlying module is the span of the permitted normalized monomials. -/
theorem partiallyLaurent_toSubmodule :
    (partiallyLaurent u Λ b S).toSubmodule =
      Submodule.span R ((fun a ↦ monomial u Λ (b.repr.symm a)) ''
        (LaurentRing.nonnegOutside S : Set (I →₀ ℤ))) := by
  rw [partiallyLaurent, TwistedMonoidAlgebra.supported_toSubmodule]
  have hComp : (fun a : Multiplicative (LaurentRing.nonnegOutside S) ↦
      monomial u Λ (b.repr.symm (a.toAdd : I →₀ ℤ))) =
        (fun a : LaurentRing.nonnegOutside S ↦ monomial u Λ (b.repr.symm a)) ∘
          Multiplicative.toAdd := rfl
  simp only [of_partiallyLaurentIndex, hComp, Multiplicative.toAdd.surjective.range_comp,
    Set.image_eq_range]
  -- The carrier-set subtype is definitionally the additive-submonoid subtype.
  rfl

/-- Membership is support on lattice exponents with nonnegative coordinates outside `S`. -/
theorem mem_partiallyLaurent_iff (f : QuantumTorus R L u Λ) :
    f ∈ partiallyLaurent u Λ b S ↔
      ∀ a ∈ ((basis u Λ).repr f).support, ∀ i ∉ S, 0 ≤ b.repr a i := by
  rw [partiallyLaurent, TwistedMonoidAlgebra.mem_supported_iff, basis_eq_reindex]
  constructor
  · intro h a ha
    apply (mem_range_partiallyLaurentIndex_iff (a := Multiplicative.ofAdd a)).mp
    exact h (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff,
      Module.Basis.repr_reindex_apply, Multiplicative.toAdd_symm_eq] using ha)
  · intro h a ha
    apply (mem_range_partiallyLaurentIndex_iff (b := b) (S := S) a).mpr
    exact h a.toAdd (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff,
      Module.Basis.repr_reindex_apply, Multiplicative.toAdd_symm_eq, ofAdd_toAdd] using ha)

/-- A scalar monomial is permitted when its coefficient vanishes or its coordinates are allowed. -/
@[simp]
theorem smul_monomial_mem_partiallyLaurent_iff (r : R) (a : L) :
    r • monomial u Λ a ∈ partiallyLaurent u Λ b S ↔ r = 0 ∨ ∀ i ∉ S, 0 ≤ b.repr a i := by
  rw [partiallyLaurent, monomial_def, TwistedMonoidAlgebra.smul_of_mem_supported_iff,
    mem_range_partiallyLaurentIndex_iff]
  simp only [toAdd_ofAdd]

/-- A normalized monomial is permitted if its coordinates are allowed or its scalars are trivial. -/
@[simp]
theorem monomial_mem_partiallyLaurent_iff (a : L) :
    monomial u Λ a ∈ partiallyLaurent u Λ b S ↔
      (1 : R) = 0 ∨ ∀ i ∉ S, 0 ≤ b.repr a i := by
  simpa only [one_smul] using smul_monomial_mem_partiallyLaurent_iff
    (u := u) (Λ := Λ) (b := b) 1 a

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
  rw [partiallyLaurent, TwistedMonoidAlgebra.supported_le_iff]
  exact Multiplicative.toAdd.forall_congr' fun a ↦ by
    rw [of_partiallyLaurentIndex, Multiplicative.toAdd_symm_eq, toAdd_ofAdd]

/-- Permitted normalized monomials form a basis in the chosen lattice coordinates. -/
noncomputable def partiallyLaurentBasis (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) :
    Module.Basis (LaurentRing.nonnegOutside S) R (partiallyLaurent u Λ b S) :=
  (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective).reindex Multiplicative.toAdd

/-- Transport through the subalgebra identification sends the generic supported basis vector
back to the mixed basis vector at the same coordinate index. -/
theorem partiallyLaurentBasis_apply_eq_supportedBasis (a : LaurentRing.nonnegOutside S) :
    partiallyLaurentBasis u Λ b S a =
      Subalgebra.equivOfEq _ _
        (partiallyLaurent_eq_supported (u := u) (Λ := Λ) (b := b) (S := S)).symm
        (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
          partiallyLaurentIndex_injective (Multiplicative.ofAdd a)) := by
  apply Subtype.ext
  simp only [Subalgebra.equivOfEq_apply]
  have h := (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective).reindex_apply Multiplicative.toAdd a
  rw [Multiplicative.toAdd_symm_eq] at h
  exact congrArg Subtype.val h

/-- The restricted basis has the same ambient normalized monomials. -/
@[simp]
theorem coe_partiallyLaurentBasis_apply (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ b S a : QuantumTorus R L u Λ) =
      monomial u Λ (b.repr.symm (a : I →₀ ℤ)) := by
  simpa only [Subalgebra.equivOfEq_apply, TwistedMonoidAlgebra.coe_supportedBasis_apply,
    of_partiallyLaurentIndex, toAdd_ofAdd] using congrArg Subtype.val
      (partiallyLaurentBasis_apply_eq_supportedBasis (u := u) (Λ := Λ) (b := b) a)

/-- Restricted basis coordinates are the ambient quantum coefficients in the chosen basis. -/
@[simp]
theorem partiallyLaurentBasis_repr_apply (f : partiallyLaurent u Λ b S)
    (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentBasis u Λ b S).repr f a =
      (basis u Λ).repr (f : QuantumTorus R L u Λ) (b.repr.symm (a : I →₀ ℤ)) := by
  calc
    _ = (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
          partiallyLaurentIndex_injective).repr
        (f : TwistedMonoidAlgebra.supported (factorSet u Λ) (partiallyLaurentIndex b S))
        (Multiplicative.ofAdd a) :=
      (TwistedMonoidAlgebra.supportedBasis (factorSet u Λ) (partiallyLaurentIndex b S)
        partiallyLaurentIndex_injective).repr_reindex_apply f Multiplicative.toAdd a
    _ = (TwistedMonoidAlgebra.basis R (Multiplicative L) (factorSet u Λ)).repr
        (f : QuantumTorus R L u Λ) (partiallyLaurentIndex b S (Multiplicative.ofAdd a)) :=
      TwistedMonoidAlgebra.supportedBasis_repr_apply _ _ _ _ _
    _ = _ := by
      rw [basis_eq_reindex, Module.Basis.repr_reindex_apply]
      simp only [Multiplicative.toAdd_symm_eq, partiallyLaurentIndex_ofAdd]

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
  rw [partiallyLaurentBasis_apply_eq_supportedBasis]
  rw [ofAdd_zero, TwistedMonoidAlgebra.supportedBasis_one, map_one]

/-- Restricted basis multiplication retains the ambient twist and adds its coordinate indices. -/
@[simp]
theorem partiallyLaurentBasis_mul (a c : LaurentRing.nonnegOutside S) :
    partiallyLaurentBasis u Λ b S a * partiallyLaurentBasis u Λ b S c =
      (u ^ (Λ (b.repr.symm (a : I →₀ ℤ)) (b.repr.symm (c : I →₀ ℤ))) : Rˣ).val •
        partiallyLaurentBasis u Λ b S (a + c) := by
  rw [partiallyLaurentBasis_apply_eq_supportedBasis, partiallyLaurentBasis_apply_eq_supportedBasis,
    partiallyLaurentBasis_apply_eq_supportedBasis]
  have h := TwistedMonoidAlgebra.supportedBasis_mul (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective (Multiplicative.ofAdd a) (Multiplicative.ofAdd c)
  simp only [factorSet_apply, partiallyLaurentIndex_toAdd, toAdd_ofAdd, ← ofAdd_add] at h
  simpa only [map_mul, map_smul] using congrArg
    (Subalgebra.equivOfEq _ _
      (partiallyLaurent_eq_supported (u := u) (Λ := Λ) (b := b) (S := S)).symm) h

/-- The original factor set restricted to the permitted coordinate monoid. -/
noncomputable abbrev partiallyLaurentFactorSet (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) :=
  TwistedMonoidAlgebra.pullbackFactorSet (factorSet u Λ) (partiallyLaurentIndex b S)

/-- The restricted factor set evaluates the form on the corresponding lattice vectors. -/
theorem partiallyLaurentFactorSet_apply (a c : Multiplicative (LaurentRing.nonnegOutside S)) :
    partiallyLaurentFactorSet u Λ b S a c =
      u ^ (Λ (b.repr.symm (a.toAdd : I →₀ ℤ)) (b.repr.symm (c.toAdd : I →₀ ℤ))) := by
  simp only [partiallyLaurentFactorSet, TwistedMonoidAlgebra.pullbackFactorSet,
    factorSet_apply, partiallyLaurentIndex_toAdd]

/-- The mixed algebra is the twisted monoid algebra on its permitted coordinate indices. -/
noncomputable def partiallyLaurentEquiv (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L)
    (b : Module.Basis I ℤ L) (S : Set I) :
    twistedMonoidAlgebra R (Multiplicative (LaurentRing.nonnegOutside S))
      (partiallyLaurentFactorSet u Λ b S) ≃ₐ[R] partiallyLaurent u Λ b S :=
  (TwistedMonoidAlgebra.supportedEquiv (factorSet u Λ) (partiallyLaurentIndex b S)
    partiallyLaurentIndex_injective).trans
      (Subalgebra.equivOfEq _ _
        (partiallyLaurent_eq_supported (u := u) (Λ := Λ) (b := b) (S := S)).symm)

/-- The twisted realization preserves the normalized permitted basis. -/
@[simp]
theorem partiallyLaurentEquiv_of (a : Multiplicative (LaurentRing.nonnegOutside S)) :
    partiallyLaurentEquiv u Λ b S (TwistedMonoidAlgebra.of a) =
      partiallyLaurentBasis u Λ b S a.toAdd := by
  rw [partiallyLaurentEquiv, AlgEquiv.trans_apply,
    TwistedMonoidAlgebra.supportedEquiv_of,
    partiallyLaurentBasis_apply_eq_supportedBasis, ofAdd_toAdd]

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
    f = g := by
  apply AlgHom.toLinearMap_injective ((partiallyLaurentBasis u Λ b S).ext ?_)
  intro a
  simpa only [AlgHom.toLinearMap_apply] using h a

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

/-- The inverse untwisting comparison preserves the permitted coordinate index. -/
@[simp]
theorem partiallyLaurentUntwistedEquiv_symm_basis (h : ∀ a c, u ^ (Λ a c) = 1)
    (a : LaurentRing.nonnegOutside S) :
    (partiallyLaurentUntwistedEquiv u Λ b h S).symm (LaurentRing.partiallyLaurentBasis R S a) =
      partiallyLaurentBasis u Λ b S a := by
  rw [← partiallyLaurentUntwistedEquiv_basis h a, AlgEquiv.symm_apply_apply]

end TauCeti.QuantumTorus
