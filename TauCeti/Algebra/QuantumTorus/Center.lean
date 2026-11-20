/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuantumTorus.Basic
import TauCeti.Algebra.MonoidAlgebra.Twisted.Center
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The center of a based quantum torus

The center is determined by coefficients weighted by the opposite twist factors; without
scalar cancellation the two factors themselves need not be equal. When nonzero scalar
coefficients cancel, the center is spanned by normalized monomials on the central exponent
subgroup. These results specialize the arbitrary-factor-set twisted group algebra API.

The central exponent subgroup is defined by equality of opposite powers of the parameter,
using equalizers of additive homomorphisms. This definition makes sense for units in any
monoid, without constructing a torus. For alternating forms its condition is
`u ^ (2 * Λ a b) = 1` for every `b`, including finite-order parameters.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), Proposition 11.2.
-/

public section

namespace Units

variable {R L : Type*} [Monoid R] [AddCommGroup L]

/-- The exponents for which the opposite powers of a scalar unit agree against every test
exponent. When a based quantum torus exists, these are exactly its central monomials. -/
def quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) : AddSubgroup L :=
  ⨅ b : L, (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ.flip b).toAddMonoidHom).eqLocus
    (((zpowersHom Rˣ u).toAdditiveRight).comp (Λ b).toAddMonoidHom)

/-- Membership in the central exponent subgroup is equality of opposite powers. -/
@[simp]
theorem mem_quantumTorusCentralExponents (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (Λ a b) = u ^ (Λ b a) := by
  simp only [quantumTorusCentralExponents, AddSubgroup.mem_iInf]
  rfl

end Units

namespace TauCeti.QuantumTorus

section Monoid

variable {R L : Type*} [Monoid R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- For an alternating form, central exponents are detected by the commutation factors,
without an infinite-order hypothesis on the parameter. -/
theorem _root_.LinearMap.BilinForm.IsAlt.mem_quantumTorusCentralExponents_iff
    (hΛ : Λ.IsAlt) (a : L) :
    a ∈ u.quantumTorusCentralExponents Λ ↔ ∀ b, u ^ (2 * Λ a b) = 1 := by
  rw [Units.mem_quantumTorusCentralExponents]
  apply forall_congr'
  intro b
  have he : Λ a b - Λ b a = 2 * Λ a b := by
    have := hΛ.neg_eq a b
    omega
  rw [← he, zpow_sub, mul_inv_eq_one]

end Monoid

variable {R L : Type*} [CommSemiring R] [AddCommGroup L]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

/-- A torus element is central exactly when it commutes with every normalized monomial. -/
theorem mem_center_iff_commute_monomial (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ b, Commute f (monomial u Λ b) := by
  simpa only [Multiplicative.forall, monomial_def] using
    (TwistedMonoidAlgebra.mem_center_iff_commute_of (α := factorSet u Λ) f)

/-- Every coefficient multiplied by either opposite twist factor gives the same result.
Without scalar cancellation, the two twist factors themselves may differ. -/
theorem mem_center_iff_coeff (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔ ∀ a b,
      (basis u Λ).repr f a * (u ^ (Λ a b) : Rˣ) =
        (basis u Λ).repr f a * (u ^ (Λ b a) : Rˣ) := by
  simpa only [Multiplicative.forall, ← basis_repr_apply, factorSet_apply,
    toAdd_ofAdd] using
    (TwistedMonoidAlgebra.mem_center_iff_coeff (α := factorSet u Λ) f)

/-- A normalized monomial is central precisely at the central exponent subgroup.
No cancellation or nontriviality assumption is needed for its scalar coefficient one. -/
@[simp]
theorem monomial_mem_center_iff (a : L) :
    monomial u Λ a ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      a ∈ u.quantumTorusCentralExponents Λ := by
  simpa only [monomial_def, Multiplicative.forall, factorSet_apply,
    Units.mem_quantumTorusCentralExponents, toAdd_ofAdd] using
    (TwistedMonoidAlgebra.of_mem_center_iff (α := factorSet u Λ) (Multiplicative.ofAdd a))

/-- If nonzero scalar coefficients cancel, centrality is support on central exponents. -/
theorem mem_center_iff_support [IsCancelMulZero R] (f : QuantumTorus R L u Λ) :
    f ∈ Subalgebra.center R (QuantumTorus R L u Λ) ↔
      ∀ a ∈ ((basis u Λ).repr f).support, a ∈ u.quantumTorusCentralExponents Λ := by
  simpa only [Multiplicative.forall, Finsupp.mem_support_iff, ← basis_repr_apply,
    factorSet_apply, Units.mem_quantumTorusCentralExponents, toAdd_ofAdd] using
    (TwistedMonoidAlgebra.mem_center_iff_support (α := factorSet u Λ) f)

/-- The center is the span of its normalized central monomials when scalar coefficients cancel. -/
theorem center_toSubmodule_eq_span [IsCancelMulZero R] :
    (Subalgebra.center R (QuantumTorus R L u Λ)).toSubmodule =
      Submodule.span R (monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L)) := by
  have hi : (TwistedMonoidAlgebra.of (α := factorSet u Λ) ''
      {a : Multiplicative L | ∀ b, factorSet u Λ a b = factorSet u Λ b a}) =
      monomial u Λ '' (u.quantumTorusCentralExponents Λ : Set L) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.toAdd, ?_, ?_⟩
      · rw [SetLike.mem_coe, Units.mem_quantumTorusCentralExponents]
        intro b
        simpa only [factorSet_apply, toAdd_ofAdd] using ha (Multiplicative.ofAdd b)
      · simp only [monomial_def, ofAdd_toAdd]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Multiplicative.ofAdd a, ?_, (monomial_def a).symm⟩
      intro b
      simpa only [factorSet_apply, toAdd_ofAdd] using
        (Units.mem_quantumTorusCentralExponents u Λ a).mp ha b.toAdd
  rw [← hi]
  exact TwistedMonoidAlgebra.center_toSubmodule_eq_span

/-- The canonical map from the torus on central exponents to the center, with the
restricted bilinear form and its original normalized multiplication. -/
noncomputable def _root_.Units.quantumTorusCenterHom (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) →ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  lift u _
    (fun a ↦ ⟨monomial u Λ (a : L), (monomial_mem_center_iff _).mpr a.property⟩)
    (by apply Subtype.ext; simp)
    (by
      intro a b
      apply Subtype.ext
      simpa only [Subalgebra.coe_mul, Subalgebra.coe_smul, AddSubgroup.coe_add,
        LinearMap.compl₁₂_apply, AddMonoidHom.coe_toIntLinearMap,
        AddSubgroup.subtype_apply] using
        (monomial_mul_monomial (u := u) (Λ := Λ) (a : L) (b : L)))

/-- The canonical map preserves normalized monomials after inclusion in the ambient torus. -/
@[simp]
theorem _root_.Units.coe_quantumTorusCenterHom_monomial (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    ((u.quantumTorusCenterHom Λ) (monomial u _ a) : QuantumTorus R L u Λ) =
      monomial u Λ (a : L) := by
  simp only [Units.quantumTorusCenterHom, lift_monomial]

/-- The restricted central torus embeds without a scalar cancellation assumption. -/
theorem _root_.Units.quantumTorusCenterHom_injective (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Injective (u.quantumTorusCenterHom Λ) := by
  let S := u.quantumTorusCentralExponents Λ
  let ΛS := Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap
  let F := (Subalgebra.center R (QuantumTorus R L u Λ)).val.toLinearMap.comp
    (u.quantumTorusCenterHom Λ).toLinearMap
  have heq : F = (basis u ΛS).constr R (fun a : S ↦ monomial u Λ (a : L)) := by
    apply (basis u ΛS).ext
    intro a
    rw [Module.Basis.constr_basis]
    simp only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, basis_apply,
      Subalgebra.val_apply]
    exact Units.coe_quantumTorusCenterHom_monomial u Λ a
  have hli : LinearIndependent R (fun a : S ↦ monomial u Λ (a : L)) := by
    simpa only [Function.comp_def, basis_apply] using
      (basis u Λ).linearIndependent.comp (fun a : S ↦ (a : L)) Subtype.val_injective
  have hi : Function.Injective F := by
    rw [heq]
    exact (basis u ΛS).injective_constr_of_linearIndependent hli
  intro x y hxy
  apply hi
  simpa only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.val_apply] using
    congrArg (fun z : Subalgebra.center R (QuantumTorus R L u Λ) ↦
      (z : QuantumTorus R L u Λ)) hxy

/-- If nonzero scalar coefficients cancel, every central element has a preimage in the
restricted torus. -/
theorem _root_.Units.quantumTorusCenterHom_surjective [IsCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) : Function.Surjective (u.quantumTorusCenterHom Λ) := by
  let F := (Subalgebra.center R (QuantumTorus R L u Λ)).val.toLinearMap.comp
    (u.quantumTorusCenterHom Λ).toLinearMap
  have hle : Submodule.span R (monomial u Λ ''
      (u.quantumTorusCentralExponents Λ : Set L)) ≤ LinearMap.range F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨monomial u _ ⟨a, ha⟩, ?_⟩
    simpa only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.val_apply] using
      (Units.coe_quantumTorusCenterHom_monomial u Λ ⟨a, ha⟩)
  rintro ⟨f, hf⟩
  have hs : f ∈ Submodule.span R (monomial u Λ ''
      (u.quantumTorusCentralExponents Λ : Set L)) := by
    rw [← center_toSubmodule_eq_span]
    exact hf
  obtain ⟨g, hg⟩ := hle hs
  refine ⟨g, Subtype.ext ?_⟩
  simpa only [F, LinearMap.comp_apply, AlgHom.toLinearMap_apply, Subalgebra.val_apply] using hg

/-- The actual center has the restricted twisted multiplication on the central exponent
subgroup. No chosen basis or untwisting of its normalized monomials is imposed. -/
noncomputable def _root_.Units.quantumTorusCenterEquiv [IsCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) :
    let S := u.quantumTorusCentralExponents Λ
    QuantumTorus R S u (Λ.compl₁₂ S.subtype.toIntLinearMap S.subtype.toIntLinearMap) ≃ₐ[R]
      Subalgebra.center R (QuantumTorus R L u Λ) :=
  AlgEquiv.ofBijective (u.quantumTorusCenterHom Λ)
    ⟨u.quantumTorusCenterHom_injective Λ, u.quantumTorusCenterHom_surjective Λ⟩

/-- The center equivalence sends each normalized monomial to its ambient counterpart. -/
@[simp]
theorem _root_.Units.coe_quantumTorusCenterEquiv_monomial [IsCancelMulZero R] (u : Rˣ)
    (Λ : LinearMap.BilinForm ℤ L) (a : u.quantumTorusCentralExponents Λ) :
    ((u.quantumTorusCenterEquiv Λ) (monomial u _ a) : QuantumTorus R L u Λ) =
      monomial u Λ (a : L) := by
  -- The bijective algebra equivalence has the same forward map as the canonical homomorphism.
  change ((u.quantumTorusCenterHom Λ) (monomial u _ a) : QuantumTorus R L u Λ) = _
  exact Units.coe_quantumTorusCenterHom_monomial u Λ a

end TauCeti.QuantumTorus
