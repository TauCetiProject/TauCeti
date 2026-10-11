/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.DotOrbit
import TauCeti.Algebra.Algebra.Pi
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Dot-invariant polynomials separate dot orbits

For two weights in distinct dot orbits, finite interpolation produces a polynomial taking
values zero and one on the respective orbits. Its product over Weyl pullbacks remains zero
and one on those orbits and is dot-invariant. Consequently two weights have identical
values on every dot-invariant polynomial exactly when they lie in one dot orbit.

This is the invariant-theoretic step of the Harish-Chandra central-character orbit theorem.
It is independent of surjectivity of the Harish-Chandra projection.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter VIII, §8, central characters.
-/

public section

namespace TauCeti

open LieAlgebra Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {b : (IsKilling.rootSystem H).Base}

/-- Two distinct dot orbits are separated by a dot-invariant polynomial with values zero
and one. The weights need not be integral or dominant. -/
theorem exists_mem_dotInvariants_lift_eq_zero_one {lam mu : Dual K H}
    (h : ¬ ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu) :
    ∃ p ∈ dotInvariants b, SymmetricAlgebra.lift lam p = 0 ∧
      SymmetricAlgebra.lift mu p = 1 := by
  classical
  let P := IsKilling.rootSystem H
  let := RootPairing.finite_weylGroup P
  let := Fintype.ofFinite P.weylGroup
  -- Interpolate on both entire orbits before taking a product of pullbacks.
  let s := Finset.univ.image (fun w : P.weylGroup ↦ dotAction P b w lam) ∪
    Finset.univ.image (fun w : P.weylGroup ↦ dotAction P b w mu)
  let values (f : Dual K H) : K := if ∃ w, dotAction P b w lam = f then 0 else 1
  obtain ⟨q, hq'⟩ := AlgHom.surjective_pi_of_injective
    (fun f : s ↦ SymmetricAlgebra.lift (f : Dual K H))
    (SymmetricAlgebra.lift.injective.comp Subtype.val_injective) (fun f : s ↦ values f)
  have hq (f : Dual K H) (hf : f ∈ s) : SymmetricAlgebra.lift f q = values f :=
    congrFun hq' ⟨f, hf⟩
  have hq_lam (w : P.weylGroup) : SymmetricAlgebra.lift (dotAction P b w lam) q = 0 := by
    rw [hq _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩))]
    exact ite_eq_left ⟨w, rfl⟩
  have hq_mu (w : P.weylGroup) : SymmetricAlgebra.lift (dotAction P b w mu) q = 1 := by
    rw [hq _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩))]
    simp only [values, ite_eq_right_iff, zero_ne_one, imp_false]
    rintro ⟨v, hv⟩
    apply h
    refine ⟨w⁻¹ * v, ?_⟩
    rw [dotAction_mul, hv, dotAction_inv_dotAction]
  -- The transpose map on the Cartan and the affine constant give polynomial pullbacks.
  let pull (w : P.weylGroup) : SymmetricAlgebra K H →ₐ[K] SymmetricAlgebra K H :=
    SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι K H).comp (w : P.Aut).toHom.coweightMap +
        (Algebra.linearMap K (SymmetricAlgebra K H)).comp (dotAction P b w 0))
  have hpull (w : P.weylGroup) (f : Dual K H) (p : SymmetricAlgebra K H) :
      SymmetricAlgebra.lift f (pull w p) =
        SymmetricAlgebra.lift (dotAction P b w f) p := by
    have heq : (SymmetricAlgebra.lift f).comp (pull w) =
        SymmetricAlgebra.lift (dotAction P b w f) := by
      ext x
      have ht := congrFun (congrArg DFunLike.coe
        ((w : P.Aut).toHom.weight_coweight_transpose_apply P P x)) f
      have ht' : (w • f) x = f ((w : P.Aut).toHom.coweightMap x) := by
        -- The Weyl action is the weight map of the underlying root-pairing automorphism.
        change ((w : P.Aut).toHom.weightMap f) x = _
        -- Express the perfect pairing as the bilinear evaluation map so its public
        -- root-system evaluation lemma applies.
        change P.toLinearMap ((w : P.Aut).toHom.weightMap f) x =
          P.toLinearMap f ((w : P.Aut).toHom.coweightMap x) at ht
        simpa only [P, IsKilling.rootSystem_toLinearMap_apply] using ht
      -- Normalize the composite coercion before using the generator evaluation lemma.
      change SymmetricAlgebra.lift f (pull w (SymmetricAlgebra.ι K H x)) =
        SymmetricAlgebra.lift (dotAction P b w f) (SymmetricAlgebra.ι K H x)
      simp only [pull, SymmetricAlgebra.lift_ι_apply,
        LinearMap.add_apply, LinearMap.comp_apply, map_add, Algebra.linearMap_apply,
        AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      rw [← ht']
      simp [dotAction_def, add_sub_assoc]
    exact DFunLike.congr_fun heq p
  -- Right multiplication permutes the factors, so the product is dot-invariant.
  let p := ∏ w : P.weylGroup, pull w q
  have heval (f : Dual K H) : SymmetricAlgebra.lift f p =
      ∏ w : P.weylGroup, SymmetricAlgebra.lift (dotAction P b w f) q := by
    simp only [p, map_prod, hpull]
  refine ⟨p, ?_, ?_, ?_⟩
  · rw [mem_dotInvariants_iff]
    intro v f
    rw [heval, heval]
    exact Fintype.prod_equiv (Equiv.mulRight v) _ _
      (fun w ↦ by simp only [P, Equiv.coe_mulRight, dotAction_mul])
  · rw [heval]
    simp [hq_lam]
  · rw [heval]
    simp [hq_mu]

/-- Equality of all dot-invariant polynomial values characterizes a dot orbit. -/
theorem forall_mem_dotInvariants_lift_eq_iff {lam mu : Dual K H} :
    (∀ p ∈ dotInvariants b, SymmetricAlgebra.lift lam p = SymmetricAlgebra.lift mu p) ↔
      ∃ w, dotAction (IsKilling.rootSystem H) b w lam = mu := by
  constructor
  · intro heq
    by_contra h
    obtain ⟨p, hp, hlam, hmu⟩ := exists_mem_dotInvariants_lift_eq_zero_one h
    simpa [hlam, hmu] using heq p hp
  · rintro ⟨w, rfl⟩ p hp
    exact ((mem_dotInvariants_iff.mp hp) w lam).symm

end TauCeti
