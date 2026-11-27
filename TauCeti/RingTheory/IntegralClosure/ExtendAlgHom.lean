/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Extending rational points along integral extensions

Let `S` be a commutative algebra over an algebraically closed field `k`, integral over a
`k`-algebra `R`, for instance a subalgebra `R ⊆ S` over which `S` is integral. Every `k`-algebra
homomorphism `R →ₐ[k] k` vanishing on the kernel of `R → S` extends to `S`. Geometrically, the
morphism `Spec S → Spec R` is surjective onto the `k`-points of the closed subscheme cut out by
that kernel; for injective `R → S`, it is surjective on `k`-points.

The proof is lying over. The kernel of `f : R →ₐ[k] k` is a maximal ideal of `R` containing the
kernel of `R → S`, and by lying over (`Ideal.exists_ideal_over_maximal_of_isIntegral`) it is the
contraction of a maximal ideal `Q` of `S`. The residue field `S ⧸ Q` is integral over
`R ⧸ ker f = k`, hence equal to `k`, and the quotient map `S → S ⧸ Q ≃ k` extends `f`.

This applies to the invariants of a finite group acting on a polynomial ring: every character of
the invariants is evaluation at a point.

## Main results

* `TauCeti.exists_algHom_comp_toAlgHom_eq`: a `k`-point of `R` vanishing on the kernel of `R → S`
  extends to `S`, when `S` is integral over `R`.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 5,
  Theorem 5.10 (lying over).
-/

public section

namespace TauCeti

variable {k S : Type*} [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]

/-- **Extension of rational points along an integral extension.** Let `S` be a commutative algebra
over an algebraically closed field `k`, integral over a `k`-algebra `R`. Every `k`-algebra
homomorphism `f : R →ₐ[k] k` vanishing on the kernel of `R → S` is the restriction of one on `S`.
The kernel condition holds when `R → S` is injective, for instance for a subalgebra `R` of `S`. -/
theorem exists_algHom_comp_toAlgHom_eq {R : Type*} [CommRing R] [Algebra k R] [Algebra R S]
    [IsScalarTower k R S] [Algebra.IsIntegral R S] (f : R →ₐ[k] k)
    (hf : RingHom.ker (algebraMap R S) ≤ RingHom.ker f) :
    ∃ g : S →ₐ[k] k, g.comp (IsScalarTower.toAlgHom k R S) = f := by
  -- The kernel of `f` is maximal, and lies under a maximal ideal `Q` of `S`.
  have hmax : (RingHom.ker f).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective f fun c ↦ ⟨algebraMap k R c, f.commutes c⟩
  obtain ⟨Q, hQ, hQf⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) _ hf
  -- Modulo `Q`, each `a ∈ R` is the scalar `f a`, since `a - f a` lies in the kernel of `f`.
  have hA (a : R) : Ideal.Quotient.mk Q (algebraMap R S a) = algebraMap k (S ⧸ Q) (f a) := by
    have ha : a - algebraMap k R (f a) ∈ RingHom.ker f := by
      simp [RingHom.mem_ker]
    rw [← hQf, Ideal.mem_comap, map_sub] at ha
    rw [← Ideal.Quotient.mk_algebraMap, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem,
      IsScalarTower.algebraMap_apply k R S]
    exact ha
  -- So `S ⧸ Q` is integral over `k`, hence equal to `k`.
  have : Algebra.IsIntegral k (S ⧸ Q) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hps⟩ := Algebra.IsIntegral.isIntegral (R := R) s
    refine ⟨p.map f.toRingHom, hp.map _, ?_⟩
    have hcomp : (algebraMap k (S ⧸ Q)).comp f.toRingHom =
        (Ideal.Quotient.mk Q).comp (algebraMap R S) :=
      RingHom.ext fun a ↦ (hA a).symm
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hps, map_zero]
  let e : k ≃ₐ[k] S ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k _)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q), AlgHom.ext fun a ↦ ?_⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom',
    Ideal.Quotient.mkₐ_eq_mk, hA, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_eq, ← e.commutes,
    Algebra.algebraMap_self_apply]

end TauCeti
