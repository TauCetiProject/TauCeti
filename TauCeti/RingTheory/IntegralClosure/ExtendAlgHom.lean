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

Let `S` be a commutative algebra over an algebraically closed field `k`, and let `A ⊆ S` be a
subalgebra over which `S` is integral. Every `k`-algebra homomorphism `A →ₐ[k] k`
extends to `S`. Geometrically, the morphism `Spec S → Spec A` is surjective on `k`-points.

The proof is lying over. The kernel of `f : A →ₐ[k] k` is a maximal ideal of `A`, and by lying
over (`Ideal.exists_ideal_over_maximal_of_isIntegral`) it is the contraction of a maximal ideal `Q`
of `S`. The residue field `S ⧸ Q` is integral over `A ⧸ ker f = k`, hence equal to `k`, and the
quotient map `S → S ⧸ Q ≃ k` extends `f`.

This applies to the invariants of a finite group acting on a polynomial ring: every character of
the invariants is evaluation at a point.

## Main results

* `TauCeti.exists_algHom_comp_val_eq`: a `k`-point of a subalgebra over which an algebra is
  integral extends to that algebra.
-/

public section

namespace TauCeti

variable {k S : Type*} [Field k] [IsAlgClosed k] [CommRing S] [Algebra k S]

/-- **Extension of rational points along an integral extension.** If a commutative algebra `S`
over an algebraically closed field `k` is integral over a subalgebra `A`, every `k`-algebra
homomorphism `A →ₐ[k] k` is the restriction of one on `S`. -/
theorem exists_algHom_comp_val_eq (A : Subalgebra k S) [Algebra.IsIntegral A S]
    (f : A →ₐ[k] k) : ∃ g : S →ₐ[k] k, g.comp A.val = f := by
  -- The kernel of `f` is maximal, and lies under a maximal ideal `Q` of `S`.
  have hmax : (RingHom.ker f).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective f fun c ↦ ⟨algebraMap k A c, f.commutes c⟩
  have hker : RingHom.ker (algebraMap A S) ≤ RingHom.ker f := by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]
    exact bot_le
  obtain ⟨Q, hQ, hQf⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) _ hker
  -- Modulo `Q`, each `a ∈ A` is the scalar `f a`, since `a - f a` lies in the kernel of `f`.
  have hA (a : A) : Ideal.Quotient.mk Q (a : S) = algebraMap k (S ⧸ Q) (f a) := by
    have ha : a - algebraMap k A (f a) ∈ RingHom.ker f := by
      simp [RingHom.mem_ker]
    rw [← hQf, Ideal.mem_comap] at ha
    have he : algebraMap k (S ⧸ Q) (f a) = Ideal.Quotient.mk Q (algebraMap k S (f a)) := rfl
    rw [he, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  -- So `S ⧸ Q` is integral over `k`, hence equal to `k`.
  have : Algebra.IsIntegral k (S ⧸ Q) := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hps⟩ := Algebra.IsIntegral.isIntegral (R := A) s
    refine ⟨p.map f.toRingHom, hp.map _, ?_⟩
    have hcomp : (algebraMap k (S ⧸ Q)).comp f.toRingHom =
        (Ideal.Quotient.mk Q).comp (algebraMap A S) :=
      RingHom.ext fun a ↦ (hA a).symm
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, hps, map_zero]
  let e : k ≃ₐ[k] S ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k _)
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q), AlgHom.ext fun a ↦ ?_⟩
  have hmk : Ideal.Quotient.mkₐ k Q (a : S) = e (f a) := hA a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Subalgebra.coe_val, hmk, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply]

end TauCeti
