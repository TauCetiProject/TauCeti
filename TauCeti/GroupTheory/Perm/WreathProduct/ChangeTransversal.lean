/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
import Mathlib.Tactic.Group

/-!
# Changing the transversal in the monomial embedding

The monomial embedding of a group into the wreath product of a subgroup depends on a choice of
representatives for the left cosets. Two choices give conjugate embeddings. The conjugating
element belongs to the base group: at a coset `x` it is the difference between the two chosen
representatives at `x`.

This relation is the algebraic input for independence of the transversal in tensor induction and
in the Evens norm. It uses no topology or finite-index assumption. The coordinate identity is
`TauCeti.transversalDiff_mul_lWord`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3.
-/

public section

namespace Subgroup

open TauCeti

variable {G : Type*} [Group G] (U : Subgroup G)

/-- The base-group element comparing the monomial embeddings obtained from two left
transversals. Its coordinate at `x` is `r_s(x)⁻¹ r_t(x)` in `U`. -/
noncomputable def monomialChangeTransversal (s t : U.LeftTransversal) :
    WreathProduct U (G ⧸ U) :=
  SemidirectProduct.inl fun x ↦
    ⟨transversalDiff U (leftTransversalRep U s) (leftTransversalRep U t) x,
      transversalDiff_mem U _ _ (leftTransversalRep_mk U s)
        (leftTransversalRep_mk U t) x⟩

/-- The base coordinate of the change-of-transversal element is the difference of the two
chosen representatives. -/
@[simp] theorem monomialChangeTransversal_left (s t : U.LeftTransversal) (x : G ⧸ U) :
    (monomialChangeTransversal U s t).left x =
      ⟨transversalDiff U (leftTransversalRep U s) (leftTransversalRep U t) x,
        transversalDiff_mem U _ _ (leftTransversalRep_mk U s)
          (leftTransversalRep_mk U t) x⟩ :=
  by simp [monomialChangeTransversal]

/-- Changing a transversal does not alter the permutation coordinate of the comparing element. -/
@[simp] theorem monomialChangeTransversal_right (s t : U.LeftTransversal) :
    (monomialChangeTransversal U s t).right = 1 :=
  by simp [monomialChangeTransversal]

/-- Comparing a transversal with itself gives the identity element. -/
@[simp] theorem monomialChangeTransversal_self (s : U.LeftTransversal) :
    monomialChangeTransversal U s s = 1 := by
  apply SemidirectProduct.ext
  · funext x
    apply Subtype.ext
    simp
  · simp

/-- Changes of transversal compose in the same order as the chosen representatives. -/
theorem monomialChangeTransversal_mul (s t v : U.LeftTransversal) :
    monomialChangeTransversal U s t * monomialChangeTransversal U t v =
      monomialChangeTransversal U s v := by
  apply SemidirectProduct.ext
  · funext x
    apply Subtype.ext
    simp only [PermutationWreathProduct.mul_left, monomialChangeTransversal_left,
      monomialChangeTransversal_right, inv_one, one_smul, Subgroup.coe_mul, Subtype.coe_mk]
    simp only [transversalDiff_def]
    group
  · simp [SemidirectProduct.mul_right]

/-- The two monomial embeddings are intertwined by their base-group comparison element. -/
theorem monomialChangeTransversal_mul_monomialHom (s t : U.LeftTransversal) (g : G) :
    monomialChangeTransversal U s t * monomialHom U t g =
      monomialHom U s g * monomialChangeTransversal U s t := by
  apply SemidirectProduct.ext
  · funext x
    apply Subtype.ext
    simpa only [PermutationWreathProduct.mul_left, monomialChangeTransversal_left,
      monomialChangeTransversal_right, inv_one, one_smul, monomialHom_left,
      Equiv.Perm.smul_def, monomialHom_right_inv, Subgroup.coe_mul, Subtype.coe_mk] using
      transversalDiff_mul_lWord U (leftTransversalRep U s) (leftTransversalRep U t) x g
  · apply Equiv.ext
    intro x
    simp only [SemidirectProduct.mul_right, monomialChangeTransversal_right,
      one_mul, mul_one, monomialHom_right]

/-- The monomial embeddings for two transversals are conjugate by an element of the base group. -/
theorem monomialHom_changeTransversal (s t : U.LeftTransversal) (g : G) :
    monomialHom U t g =
      (monomialChangeTransversal U s t)⁻¹ * monomialHom U s g *
        monomialChangeTransversal U s t := by
  have h := monomialChangeTransversal_mul_monomialHom U s t g
  calc
    monomialHom U t g =
        (monomialChangeTransversal U s t)⁻¹ *
          (monomialChangeTransversal U s t * monomialHom U t g) := by group
    _ = (monomialChangeTransversal U s t)⁻¹ *
          (monomialHom U s g * monomialChangeTransversal U s t) := by rw [h]
    _ = _ := by group

/-- Relabeling the cosets by `Fin U.index` carries the same conjugacy to the finite-coordinate
monomial embeddings. -/
theorem monomialFinHom_changeTransversal (s t : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index) (g : G) :
    monomialFinHom U t e g =
      (WreathProduct.congr e (monomialChangeTransversal U s t))⁻¹ *
        monomialFinHom U s e g *
          WreathProduct.congr e (monomialChangeTransversal U s t) := by
  rw [monomialFinHom_apply, monomialFinHom_apply,
    monomialHom_changeTransversal (s := s) (t := t)]
  simp only [map_inv, map_mul]

end Subgroup
