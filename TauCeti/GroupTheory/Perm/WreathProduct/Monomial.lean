/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.GroupTheory.TransversalWord
public import Mathlib.GroupTheory.Complement

/-!
# The monomial homomorphism of a subgroup transversal

A transversal for `U ≤ G` embeds `G` in the permutation wreath product with base group `U`
and coordinates indexed by `G ⧸ U`. Its permutation part is left translation on cosets; its
coordinate at `x` is the transversal word `r(x)⁻¹ g r(g⁻¹ • x)`, where
`r(x) = (t.2.leftQuotientEquiv x : G)`. Its cocycle law
gives the homomorphism, and both the coset-indexed and finite-coordinate forms are injective.
The input `t : U.LeftTransversal` bundles the transversal invariant. The section
`fun x => (t.2.leftQuotientEquiv x : G)` can be passed unchanged to cochain formulas taking a
representative map; `t.2.quotientGroupMk_leftQuotientEquiv` proves that it represents each coset.
Conversely, Mathlib's `Subgroup.isComplement_range_left` packages any representative map with
that property as a `U.LeftTransversal`; `Subgroup.IsComplement.leftQuotientEquiv_apply` proves
that its representative map recovers the original map pointwise.
The public maps are called as `TauCeti.monomialHom U t` and
`TauCeti.monomialFinHom U t`.
Continuity for an open subgroup is proved in
`TauCeti.Topology.Algebra.Group.WreathProduct.Monomial`.

This is the monomial construction used in Evens' multiplicative transfer; see L. Evens,
"A generalization of the transfer map in the cohomology of groups", Trans. AMS 108 (1963),
§§2–3.
-/

public section

namespace TauCeti

universe u v

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism associated to a transversal `t` of `U`. Its permutation part is
left translation on `G ⧸ U`; the coordinate at `x` is the element
`r(x)⁻¹ g r(g⁻¹ • x)` of `U`, where `r(x) = (t.2.leftQuotientEquiv x : G)`. -/
noncomputable def monomialHom (t : U.LeftTransversal) :
    G →* WreathProduct U (G ⧸ U) where
  toFun g := ⟨(fun x => ⟨lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g, lWord_mem U (fun x
      => (t.2.leftQuotientEquiv x : G)) (fun x => t.2.quotientGroupMk_leftQuotientEquiv x) x g⟩),
    MulAction.toPermHom G (G ⧸ U) g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      simpa only [SemidirectProduct.one_left, Pi.one_apply, OneMemClass.coe_one] using
        lWord_one U (fun x => (t.2.leftQuotientEquiv x : G)) x
    · exact map_one (MulAction.toPermHom G (G ⧸ U))
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      have hperm : ((MulAction.toPermHom G (G ⧸ U) g)⁻¹ x) = g⁻¹ • x := by
        rw [← map_inv, MulAction.toPermHom_apply, MulAction.toPerm_apply]
      simpa only [WreathProduct.mul_left, Subgroup.coe_mul, hperm] using
        (lWord_mul_lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g h).symm
    · exact map_mul (MulAction.toPermHom G (G ⧸ U)) g h

/-- The coordinate of the monomial homomorphism is the transversal word as an element of `U`. -/
@[simp] theorem monomialHom_left (t : U.LeftTransversal)
    (g : G) (x : G ⧸ U) :
    (monomialHom U t g).left x = ⟨lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g, lWord_mem U
        (fun x => (t.2.leftQuotientEquiv x : G)) (fun x => t.2.quotientGroupMk_leftQuotientEquiv x)
        x g⟩ := by
  rfl

/-- The coordinate of the monomial homomorphism coerces to the transversal word. -/
theorem coe_monomialHom_left (t : U.LeftTransversal)
    (g : G) (x : G ⧸ U) :
    ((monomialHom U t g).left x : G) = lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g := by
  simp only [monomialHom_left]

/-- The permutation part of the monomial homomorphism translates left cosets. -/
@[simp] theorem monomialHom_right (t : U.LeftTransversal)
    (g : G) (x : G ⧸ U) :
    (monomialHom U t g).right x = g • x := by
  simp [monomialHom]

/-- The monomial homomorphism associated to a subgroup transversal is injective. -/
theorem monomialHom_injective (t : U.LeftTransversal) :
    Function.Injective (monomialHom U t) := by
  intro g h heq
  let x : G ⧸ U := QuotientGroup.mk 1
  have hx : g • x = h • x := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => w.right x) heq
    simpa only [monomialHom_right] using this
  have hw : lWord U (fun x => (t.2.leftQuotientEquiv x : G)) (g • x) g = lWord U (fun x =>
      (t.2.leftQuotientEquiv x : G)) (g • x) h := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => ((w.left (g • x) : U) : G)) heq
    simpa only [coe_monomialHom_left] using this
  have heq' : g * (fun x => (t.2.leftQuotientEquiv x : G)) x = h * (fun x => (t.2.leftQuotientEquiv
      x : G)) x := by
    calc
      g * (fun x => (t.2.leftQuotientEquiv x : G)) x = (fun x => (t.2.leftQuotientEquiv x : G)) (g
          • x) * lWord U (fun x => (t.2.leftQuotientEquiv x : G)) (g • x) g :=
        (transversal_smul_mul_lWord U (fun x => (t.2.leftQuotientEquiv x : G)) x g).symm
      _ = (fun x => (t.2.leftQuotientEquiv x : G)) (h • x) * lWord U (fun x =>
          (t.2.leftQuotientEquiv x : G)) (h • x) h := by rw [← hx, hw]
      _ = h * (fun x => (t.2.leftQuotientEquiv x : G)) x := transversal_smul_mul_lWord U (fun x =>
          (t.2.leftQuotientEquiv x : G)) x h
  exact mul_right_cancel heq'

section FiniteIndex

variable [U.FiniteIndex]

/-- Relabel the cosets by `Fin (G : U)` using the choice-supplied bijection
`Finite.equivFinOfCardEq U.index_eq_card.symm`. The coordinate at `i` is the transversal word
at the coset named by this bijection; the coset-indexed map avoids this choice. -/
noncomputable def monomialFinHom (t : U.LeftTransversal) :
    G →* WreathProduct U (Fin U.index) :=
  (WreathProduct.congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)).toMonoidHom.comp (monomialHom U t)

/-- The finite-coordinate homomorphism is the relabeling of the coset-indexed map. -/
-- A simp tag here makes the finite coordinate lemmas fail `simpNF`.
theorem monomialFinHom_apply (t : U.LeftTransversal) (g : G) :
    monomialFinHom U t g =
      WreathProduct.congr (Finite.equivFinOfCardEq U.index_eq_card.symm)
        (monomialHom U t g) := by
  rfl

/-- A finite coordinate is the transversal word at the corresponding coset, as an element of `U`. -/
@[simp] theorem monomialFinHom_left (t : U.LeftTransversal)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U t g).left i =
      ⟨lWord U (fun x => (t.2.leftQuotientEquiv x : G)) ((Finite.equivFinOfCardEq
          U.index_eq_card.symm).symm i) g,
        lWord_mem U (fun x => (t.2.leftQuotientEquiv x : G)) (fun x =>
            t.2.quotientGroupMk_leftQuotientEquiv x) _ g⟩ := by
  simp [monomialFinHom]

/-- A finite coordinate coerces to the transversal word at the corresponding coset. -/
theorem coe_monomialFinHom_left (t : U.LeftTransversal)
    (g : G) (i : Fin U.index) :
    ((monomialFinHom U t g).left i : G) =
      lWord U (fun x => (t.2.leftQuotientEquiv x : G)) ((Finite.equivFinOfCardEq
          U.index_eq_card.symm).symm i) g := by
  simp only [monomialFinHom_left]

/-- The finite permutation coordinate translates the corresponding coset. -/
@[simp] theorem monomialFinHom_right (t : U.LeftTransversal)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U t g).right i =
      (Finite.equivFinOfCardEq U.index_eq_card.symm)
        (g • (Finite.equivFinOfCardEq U.index_eq_card.symm).symm i) := by
  simp [monomialFinHom]

/-- The finite-coordinate monomial homomorphism is injective. -/
theorem monomialFinHom_injective (t : U.LeftTransversal) :
    Function.Injective (monomialFinHom U t) :=
  (WreathProduct.congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)).injective.comp
      (monomialHom_injective U t)

end FiniteIndex

end TauCeti
