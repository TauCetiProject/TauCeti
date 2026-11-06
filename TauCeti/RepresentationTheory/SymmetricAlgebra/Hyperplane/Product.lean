/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ReflectingHyperplane
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Hyperplane.Character
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Jacobian
import Mathlib.Data.Fintype.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import TauCeti.LinearAlgebra.SymmetricAlgebra.UniqueFactorization

/-!
# The reflecting-hyperplane product divides the invariant Jacobian

For a faithful finite linear group, choose a nonzero form `ℓ_H` cutting out each distinct
reflecting hyperplane `H`. Write `e_H` for the order of its pointwise stabilizer, realized
as the inertia group of `(ℓ_H)` in `Sym(V*)`. The product `∏_H ℓ_H^(e_H - 1)` divides the
Jacobian of any system of invariant polynomial functions, provided the group order is
invertible in the field. The factors for different hyperplanes are relatively prime, so
the individual divisibilities combine without counting a hyperplane more than once.

We also count the pseudoreflections as `∑_H (e_H - 1)`. This count needs no restriction on
the characteristic: the nonidentity elements of each pointwise stabilizer have exactly
that fixed hyperplane. The divisor statement uses the primitive determinant character of
the cyclic stabilizer and is nonmodular. It gives lower bounds on multiplicities;
it does not exclude further factors.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), Chapter 3.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

open SymmetricAlgebra

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

/-- For a faithful representation, forgetting the reflecting hyperplane identifies the
nonidentity elements of its inertia groups with the pseudoreflections. -/
private noncomputable def sigmaInertiaNeOneEquivPseudoreflections
    (hρ : Function.Injective ρ)
    (ℓ : (H : ρ.reflectingHyperplanes) → Module.Dual K V)
    (hker : ∀ H, LinearMap.ker (ℓ H) = H.val) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    ((H : ρ.reflectingHyperplanes) ×
      {g : (Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G // g ≠ 1}) ≃
      {g : G // Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1} := by
  classical
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  let I (H : ρ.reflectingHyperplanes) :=
    (Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G
  let T := {g : G // Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1}
  let F := (H : ρ.reflectingHyperplanes) × {g : I H // g ≠ 1}
  -- The nonidentity part of each inertia group is one fiber of the fixed-hyperplane map.
  have hfix (H : ρ.reflectingHyperplanes) (g : I H) :
      H.val ≤ (ρ g).fixedSubmodule := by
    rw [← hker H]
    exact (ρ.mem_dual_inertia_span_singleton_ι_iff_le_fixedSubmodule).1 g.2
  have hneq (H : ρ.reflectingHyperplanes) (g : {g : I H // g ≠ 1}) : (g.val : G) ≠ 1 :=
    fun h ↦ g.2 (Subtype.ext h)
  have hfixed (H : ρ.reflectingHyperplanes) (g : {g : I H // g ≠ 1}) :
      (ρ g.val).fixedSubmodule = H.val :=
    ρ.fixedSubmodule_eq_of_mem_reflectingHyperplanes H.property
      (fun h ↦ hneq H g (hρ (h.trans (map_one ρ).symm))) (hfix H g.val)
  let f : F → T := fun x ↦ ⟨x.2.val, by
    rw [hfixed x.1 x.2]
    exact ρ.finrank_quotient_of_mem_reflectingHyperplanes x.1.property⟩
  -- Forgetting the hyperplane is bijective: it can be recovered as the fixed space.
  have hf : Function.Bijective f := by
    constructor
    · intro ⟨H, g⟩ ⟨H', g'⟩ h
      have hg : (g.val : G) = g'.val := congrArg Subtype.val h
      have hH : H = H' := Subtype.ext <| by
        rw [← hfixed H g, ← hfixed H' g', hg]
      subst H'
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Subtype.ext hg)))
    · intro g
      let H : ρ.reflectingHyperplanes := ⟨(ρ g).fixedSubmodule,
        ρ.fixedSubmodule_mem_reflectingHyperplanes g.property⟩
      have hg := ρ.ne_one_of_finrank_quotient_fixedSubmodule_eq_one g.property
      have hgI : g.val ∈ I H := by
        rw [ρ.mem_dual_inertia_span_singleton_ι_iff_le_fixedSubmodule, hker H]
      exact ⟨⟨H, ⟨⟨g.val, hgI⟩, fun h ↦ hg (congrArg Subtype.val h)⟩⟩, rfl⟩
  exact Equiv.ofBijective f hf

/-- Counting the nonidentity elements of hyperplane inertia groups counts each
pseudoreflection exactly once. This is valid even in modular characteristic. -/
theorem sum_card_dual_inertia_sub_one_eq_card_pseudoreflections
    (hρ : Function.Injective ρ)
    (ℓ : (H : ρ.reflectingHyperplanes) → Module.Dual K V)
    (hker : ∀ H, LinearMap.ker (ℓ H) = H.val) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    ∑ H : ρ.reflectingHyperplanes,
      (Nat.card ((Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G) - 1) =
      Nat.card {g : G // Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1} := by
  classical
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  let I (H : ρ.reflectingHyperplanes) :=
    (Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G
  -- Each fiber omits just the identity from its inertia group.
  rw [← Nat.card_congr (ρ.sigmaInertiaNeOneEquivPseudoreflections hρ ℓ hker), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro H _
  let := Fintype.ofFinite (I H)
  have hcard := Fintype.card_subtype_compl (fun g : I H ↦ g = 1)
  rw [Fintype.card_subtype_eq] at hcard
  simp only [← Nat.card_eq_fintype_card] at hcard
  exact hcard.symm

/-- For a faithful finite-dimensional representation with group order invertible in `K`,
the product over distinct reflecting hyperplanes of `ℓ_H^(e_H - 1)`, with `e_H` the order
of the inertia group of `(ℓ_H)`, divides the Jacobian of any family of invariants. -/
theorem prod_dual_inertia_sub_one_dvd_jacobian [FiniteDimensional K V]
    (hG : (Nat.card G : K) ≠ 0) (hρ : Function.Injective ρ)
    {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K (Module.Dual K V))
    (ℓ : (H : ρ.reflectingHyperplanes) → Module.Dual K V)
    (hker : ∀ H, LinearMap.ker (ℓ H) = H.val)
    {f : n → SymmetricAlgebra K (Module.Dual K V)}
    (hf : ∀ i, f i ∈ ρ.dual.symmetricAlgebraInvariants) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    (∏ H : ρ.reflectingHyperplanes,
      ι K (Module.Dual K V) (ℓ H) ^
        (Nat.card ((Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G) - 1)) ∣
      jacobian b f := by
  classical
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  have hℓ (H : ρ.reflectingHyperplanes) : ℓ H ≠ 0 := by
    intro hzero
    have hdim := ρ.finrank_quotient_of_mem_reflectingHyperplanes H.property
    rw [← hker H, hzero, LinearMap.ker_zero] at hdim
    simp only [Module.finrank_zero_of_subsingleton, zero_ne_one] at hdim
  apply Fintype.prod_dvd_of_isRelPrime
  · intro H H' hne
    apply (isRelPrime_ι_of_ker_ne (hℓ H) (hℓ H') ?_).pow
    rw [hker H, hker H']
    exact fun h ↦ hne (Subtype.ext h)
  · intro H
    obtain ⟨g, hg⟩ := ρ.exists_isPrimitiveRoot_det_dual_inertia_span_singleton_ι hG hρ (hℓ H)
    apply ρ.dual_ι_pow_sub_one_dvd_jacobian b _ Nat.card_pos hg hf
    exact (ρ.mem_dual_inertia_span_singleton_ι_iff_le_fixedSubmodule).1 g.property

end Representation
