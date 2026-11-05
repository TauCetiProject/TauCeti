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
the cyclic stabilizer and is nonmodular. It is a lower bound on multiplicities, not yet
the assertion that a basic invariant Jacobian has no other factors.

## References

* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), Chapter 3.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §18.
-/

public section

open SymmetricAlgebra

namespace Representation

variable {K G V : Type*} [Field K] [Group G] [Finite G] [AddCommGroup V] [Module K V]
  (ρ : Representation K G V)

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
  let T := {g : G // Module.finrank K (V ⧸ (ρ g).fixedSubmodule) = 1}
  let F := (H : ρ.reflectingHyperplanes) × {g : I H // g ≠ 1}
  -- The nonidentity part of each inertia group is one fiber of the fixed-hyperplane map.
  have hfix (H : ρ.reflectingHyperplanes) (g : I H) :
      H.val ≤ (ρ g).fixedSubmodule := by
    rw [← hker H, LinearMap.fixedSubmodule_eq_ker, ← Module.End.one_eq_id]
    exact dual_symmetricAlgebra_mem_inertia_span_singleton_ι_iff.1 g.2
  have hneq (H : ρ.reflectingHyperplanes) (g : {g : I H // g ≠ 1}) : (g.val : G) ≠ 1 :=
    fun h ↦ g.2 (Subtype.ext h)
  have hfixed (H : ρ.reflectingHyperplanes) (g : {g : I H // g ≠ 1}) :
      (ρ g.val).fixedSubmodule = H.val :=
    ρ.fixedSubmodule_eq_of_mem_reflectingHyperplanes hρ H.property (hneq H g) (hfix H g.val)
  let f : F → T := fun x ↦ ⟨x.2.val, by
    rw [hfixed x.1 x.2]
    exact ρ.finrank_quotient_of_mem_reflectingHyperplanes x.1.property⟩
  -- Forgetting the hyperplane is bijective: it can be recovered as the fixed space.
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hg : (x.2.val : G) = y.2.val := congrArg Subtype.val h
      have hH : x.1 = y.1 := Subtype.ext <| by
        rw [← hfixed x.1 x.2, ← hfixed y.1 y.2, hg]
      cases x with | mk H g =>
        cases y with | mk H' g' =>
          dsimp only at hH
          subst H'
          exact congrArg (Sigma.mk H) (Subtype.ext (Subtype.ext hg))
    · intro g
      let H : ρ.reflectingHyperplanes := ⟨(ρ g).fixedSubmodule,
        ρ.mem_reflectingHyperplanes.2 ⟨g, g.property, rfl⟩⟩
      have hg : g.val ≠ 1 := by
        intro h
        have hdim : Module.finrank K (V ⧸ (ρ (1 : G)).fixedSubmodule) = 1 := h ▸ g.property
        have htop : (ρ (1 : G)).fixedSubmodule = ⊤ :=
          LinearMap.fixedSubmodule_eq_top_iff.2 (map_one ρ)
        have hdim' : Module.finrank K (V ⧸ (⊤ : Submodule K V)) = 1 := htop ▸ hdim
        simp only [Module.finrank_zero_of_subsingleton, zero_ne_one] at hdim'
      have hgI : g.val ∈ I H := by
        rw [dual_symmetricAlgebra_mem_inertia_span_singleton_ι_iff, hker H,
          Module.End.one_eq_id, ← LinearMap.fixedSubmodule_eq_ker]
      exact ⟨⟨H, ⟨⟨g.val, hgI⟩, fun h ↦ hg (congrArg Subtype.val h)⟩⟩, rfl⟩
  -- Each fiber omits just the identity from its inertia group.
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro H _
  let := Fintype.ofFinite (I H)
  have hcard := Fintype.card_subtype_compl (fun g : I H ↦ g = 1)
  rw [Fintype.card_subtype_eq] at hcard
  simp only [← Nat.card_eq_fintype_card] at hcard
  exact hcard.symm

/-- The product of the reflecting forms with stabilizer multiplicities divides the Jacobian
of any invariant system. The hyperplanes are distinct, and the exponent is the stabilizer
order minus one, not the number of hyperplanes or an assumed order-two multiplicity. -/
theorem prod_dual_inertia_sub_one_dvd_jacobian [FiniteDimensional K V]
    (hG : (Nat.card G : K) ≠ 0) (hρ : Function.Injective ρ)
    {n : Type*} [Fintype n] [DecidableEq n] (b : Module.Basis n K (Module.Dual K V))
    (ℓ : (H : ρ.reflectingHyperplanes) → Module.Dual K V)
    (hℓ : ∀ H, ℓ H ≠ 0) (hker : ∀ H, LinearMap.ker (ℓ H) = H.val)
    {f : n → SymmetricAlgebra K (Module.Dual K V)}
    (hf : ∀ i, f i ∈ ρ.dual.symmetricAlgebraInvariants) :
    letI := ρ.dual.symmetricAlgebraMulSemiringAction
    (∏ H : ρ.reflectingHyperplanes,
      ι K (Module.Dual K V) (ℓ H) ^
        (Nat.card ((Ideal.span {ι K (Module.Dual K V) (ℓ H)}).inertia G) - 1)) ∣
      jacobian b f := by
  classical
  let := ρ.dual.symmetricAlgebraMulSemiringAction
  apply Fintype.prod_dvd_of_isRelPrime
  · intro H H' hne
    apply (isRelPrime_ι_of_ker_ne (hℓ H) (hℓ H') ?_).pow
    rw [hker H, hker H']
    exact fun h ↦ hne (Subtype.ext h)
  · intro H
    obtain ⟨g, hg⟩ := ρ.exists_isPrimitiveRoot_det_dual_inertia_span_singleton_ι hG hρ (hℓ H)
    apply ρ.dual_ι_pow_sub_one_dvd_jacobian b (hℓ H) _ Nat.card_pos hg hf
    simpa only [LinearMap.fixedSubmodule_eq_ker, Module.End.one_eq_id] using
      (dual_symmetricAlgebra_mem_inertia_span_singleton_ι_iff.1 g.property)

end Representation
