/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.GroupTheory.TransversalWord

/-!
# The monomial homomorphism of a subgroup transversal

A transversal for `U ≤ G` embeds `G` in the permutation wreath product with base group `U`
and coordinates indexed by `G ⧸ U`. Its permutation part is left translation on cosets; its
coordinate at `x` is the transversal word `r(x)⁻¹ g r(g⁻¹ • x)`, where
`r = U.leftTransversalRep s` for `s : U.LeftTransversal`. Mathlib's bundled transversal supplies
the representatives and their section property; the monomial maps consume that same choice.
The cocycle law gives the homomorphism, and both the coset-indexed and finite-coordinate forms
are injective. The public maps live in the `Subgroup` namespace and are called as
`U.monomialHom s` and `U.monomialFinHom s e`, where `e` labels the cosets by `Fin U.index`.
Continuity for an open subgroup is proved in
`TauCeti.Topology.Algebra.Group.WreathProduct.Monomial`.

This is the monomial construction used in Evens' multiplicative transfer; see L. Evens,
"A generalization of the transfer map in the cohomology of groups", Trans. AMS 108 (1963),
§§2–3.
-/

public section

namespace Subgroup

open TauCeti

universe u v

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism associated to a bundled transversal `s` of `U`. Its permutation
part is left translation on `G ⧸ U`; the coordinate at `x` is the element
`r(x)⁻¹ g r(g⁻¹ • x)` of `U`, where `r = U.leftTransversalRep s`. -/
noncomputable def monomialHom (s : U.LeftTransversal) :
    G →* WreathProduct U (G ⧸ U) where
  toFun g := ⟨(fun x => ⟨lWord U (leftTransversalRep U s) x g,
    lWord_mem U (leftTransversalRep U s) (leftTransversalRep_mk U s) x g⟩),
    MulAction.toPermHom G (G ⧸ U) g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      simpa only [SemidirectProduct.one_left, Pi.one_apply, OneMemClass.coe_one] using
        lWord_one U (leftTransversalRep U s) x
    · exact map_one (MulAction.toPermHom G (G ⧸ U))
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      have hperm : ((MulAction.toPermHom G (G ⧸ U) g)⁻¹ x) = g⁻¹ • x := by
        rw [← map_inv, MulAction.toPermHom_apply, MulAction.toPerm_apply]
      simpa only [PermutationWreathProduct.mul_left, Equiv.Perm.smul_def, Subgroup.coe_mul,
        hperm] using
        (lWord_mul_lWord U (leftTransversalRep U s) x g h).symm
    · exact map_mul (MulAction.toPermHom G (G ⧸ U)) g h

/-- The coordinate of the monomial homomorphism is the transversal word as an element of `U`. -/
@[simp] theorem monomialHom_left (s : U.LeftTransversal)
    (g : G) (x : G ⧸ U) :
    (monomialHom U s g).left x = ⟨lWord U (leftTransversalRep U s) x g,
      lWord_mem U (leftTransversalRep U s) (leftTransversalRep_mk U s) x g⟩ := by
  rfl

/-- The permutation part of the monomial homomorphism translates left cosets. -/
@[simp] theorem monomialHom_right (s : U.LeftTransversal)
    (g : G) (x : G ⧸ U) :
    (monomialHom U s g).right x = g • x := by
  simp [monomialHom]

/-- The inverse permutation coordinate translates a coset by the inverse group element. -/
@[simp] theorem monomialHom_right_inv (s : U.LeftTransversal) (g : G) (x : G ⧸ U) :
    (monomialHom U s g).right⁻¹ x = g⁻¹ • x := by
  simpa only [map_inv, SemidirectProduct.inv_right] using monomialHom_right U s g⁻¹ x

/-- The monomial homomorphism associated to a subgroup transversal is injective. -/
theorem monomialHom_injective (s : U.LeftTransversal) :
    Function.Injective (monomialHom U s) := by
  intro g h heq
  let x : G ⧸ U := QuotientGroup.mk 1
  have hx : g • x = h • x := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => w.right x) heq
    simpa only [monomialHom_right] using this
  have hw : lWord U (leftTransversalRep U s) (g • x) g =
      lWord U (leftTransversalRep U s) (g • x) h := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => ((w.left (g • x) : U) : G)) heq
    simpa only [monomialHom_left, Subtype.coe_mk] using this
  have heq' : g * (leftTransversalRep U s) x = h * (leftTransversalRep U s) x := by
    calc
      g * (leftTransversalRep U s) x =
          (leftTransversalRep U s) (g • x) *
            lWord U (leftTransversalRep U s) (g • x) g :=
        (transversal_smul_mul_lWord U (leftTransversalRep U s) x g).symm
      _ = (leftTransversalRep U s) (h • x) *
          lWord U (leftTransversalRep U s) (h • x) h := by rw [← hx, hw]
      _ = h * (leftTransversalRep U s) x :=
        transversal_smul_mul_lWord U (leftTransversalRep U s) x h
  exact mul_right_cancel heq'

section FiniteCoordinates

/-- Relabel the cosets by `Fin (G : U)` using a chosen bijection `e`. The coordinate at `i`
is the transversal word at `e.symm i`. For a finite-index subgroup, one possible `e` is
`Finite.equivFinOfCardEq U.index_eq_card.symm`. -/
noncomputable def monomialFinHom (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index) :
    G →* WreathProduct U (Fin U.index) :=
  (WreathProduct.congr e).toMonoidHom.comp (monomialHom U s)

/-- The finite-coordinate homomorphism is the relabeling of the coset-indexed map. -/
-- A simp tag here makes the finite coordinate lemmas fail `simpNF`.
theorem monomialFinHom_apply (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index) (g : G) :
    monomialFinHom U s e g = WreathProduct.congr e (monomialHom U s g) := by
  rfl

/-- A finite coordinate is the transversal word at the corresponding coset, as an element of `U`. -/
@[simp] theorem monomialFinHom_left (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U s e g).left i =
      ⟨lWord U (leftTransversalRep U s) (e.symm i) g,
        lWord_mem U (leftTransversalRep U s) (leftTransversalRep_mk U s) _ g⟩ := by
  simp [monomialFinHom]

/-- The finite permutation coordinate translates the corresponding coset. -/
@[simp] theorem monomialFinHom_right (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U s e g).right i = e (g • e.symm i) := by
  simp [monomialFinHom]

/-- The inverse finite permutation coordinate translates the named coset by the inverse group
element. -/
@[simp] theorem monomialFinHom_right_inv (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index) (g : G) (i : Fin U.index) :
    (monomialFinHom U s e g).right⁻¹ i = e (g⁻¹ • e.symm i) := by
  simpa only [map_inv, SemidirectProduct.inv_right] using monomialFinHom_right U s e g⁻¹ i

/-- The finite-coordinate monomial homomorphism is injective. -/
theorem monomialFinHom_injective (s : U.LeftTransversal)
    (e : G ⧸ U ≃ Fin U.index) :
    Function.Injective (monomialFinHom U s e) :=
  (WreathProduct.congr e).injective.comp (monomialHom_injective U s)

end FiniteCoordinates

end Subgroup
