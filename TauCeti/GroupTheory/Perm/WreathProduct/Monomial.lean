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
coordinate at `x` is the transversal word `t(x)⁻¹ g t(g⁻¹ • x)`. A representative map
`t : G ⧸ U → G` and proof that it represents each coset are shared with the cochain formulas.
For `s : U.LeftTransversal`, Mathlib supplies such a map through `s.2.leftQuotientEquiv`, with its
section property given by `s.2.quotientGroupMk_leftQuotientEquiv`. Conversely, a section map
`r` with proof `hr` gives `⟨Set.range r, Subgroup.isComplement_range_left hr⟩ : U.LeftTransversal`,
whose representative map recovers `r` by `Subgroup.IsComplement.leftQuotientEquiv_apply`.
Thus `monomialHom U s.2.leftQuotientEquiv s.2.quotientGroupMk_leftQuotientEquiv` uses the
same bundled choice of representatives directly.
The cocycle law gives the homomorphism, and both the coset-indexed and finite-coordinate forms
are injective. The public maps are called as `TauCeti.monomialHom U t ht` and
`TauCeti.monomialFinHom U t ht e`, where `e` labels the cosets by `Fin U.index`.
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
`t(x)⁻¹ g t(g⁻¹ • x)` of `U`. A Mathlib `s : U.LeftTransversal` supplies `t` via
`s.2.leftQuotientEquiv` and `ht` via `s.2.quotientGroupMk_leftQuotientEquiv`. -/
noncomputable def monomialHom (t : G ⧸ U → G) (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →* WreathProduct U (G ⧸ U) where
  toFun g := ⟨(fun x => ⟨lWord U t x g, lWord_mem U t ht x g⟩),
    MulAction.toPermHom G (G ⧸ U) g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      simpa only [SemidirectProduct.one_left, Pi.one_apply, OneMemClass.coe_one] using
        lWord_one U t x
    · exact map_one (MulAction.toPermHom G (G ⧸ U))
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      have hperm : ((MulAction.toPermHom G (G ⧸ U) g)⁻¹ x) = g⁻¹ • x := by
        rw [← map_inv, MulAction.toPermHom_apply, MulAction.toPerm_apply]
      simpa only [WreathProduct.mul_left, Subgroup.coe_mul, hperm] using
        (lWord_mul_lWord U t x g h).symm
    · exact map_mul (MulAction.toPermHom G (G ⧸ U)) g h

/-- The coordinate of the monomial homomorphism is the transversal word as an element of `U`. -/
@[simp] theorem monomialHom_left (t : G ⧸ U → G) (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (g : G) (x : G ⧸ U) :
    (monomialHom U t ht g).left x = ⟨lWord U t x g, lWord_mem U t ht x g⟩ := by
  rfl

/-- The permutation part of the monomial homomorphism translates left cosets. -/
@[simp] theorem monomialHom_right (t : G ⧸ U → G) (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (g : G) (x : G ⧸ U) :
    (monomialHom U t ht g).right x = g • x := by
  simp [monomialHom]

/-- The inverse permutation coordinate translates a coset by the inverse group element. -/
@[simp] theorem monomialHom_right_inv (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) (x : G ⧸ U) :
    (monomialHom U t ht g).right⁻¹ x = g⁻¹ • x := by
  simpa only [map_inv, SemidirectProduct.inv_right] using monomialHom_right U t ht g⁻¹ x

/-- The monomial homomorphism associated to a subgroup transversal is injective. -/
theorem monomialHom_injective (t : G ⧸ U → G) (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Function.Injective (monomialHom U t ht) := by
  intro g h heq
  let x : G ⧸ U := QuotientGroup.mk 1
  have hx : g • x = h • x := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => w.right x) heq
    simpa only [monomialHom_right] using this
  have hw : lWord U t (g • x) g = lWord U t (g • x) h := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => ((w.left (g • x) : U) : G)) heq
    simpa only [monomialHom_left, Subtype.coe_mk] using this
  have heq' : g * t x = h * t x := by
    calc
      g * t x = t (g • x) * lWord U t (g • x) g :=
        (transversal_smul_mul_lWord U t x g).symm
      _ = t (h • x) * lWord U t (h • x) h := by rw [← hx, hw]
      _ = h * t x := transversal_smul_mul_lWord U t x h
  exact mul_right_cancel heq'

section FiniteCoordinates

/-- Relabel the cosets by `Fin (G : U)` using a chosen bijection `e`. The coordinate at `i`
is the transversal word at `e.symm i`. For a finite-index subgroup, one possible `e` is
`Finite.equivFinOfCardEq U.index_eq_card.symm`. -/
noncomputable def monomialFinHom (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index) :
    G →* WreathProduct U (Fin U.index) :=
  (WreathProduct.congr e).toMonoidHom.comp (monomialHom U t ht)

/-- The finite-coordinate homomorphism is the relabeling of the coset-indexed map. -/
-- A simp tag here makes the finite coordinate lemmas fail `simpNF`.
theorem monomialFinHom_apply (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index) (g : G) :
    monomialFinHom U t ht e g = WreathProduct.congr e (monomialHom U t ht g) := by
  rfl

/-- A finite coordinate is the transversal word at the corresponding coset, as an element of `U`. -/
@[simp] theorem monomialFinHom_left (t : G ⧸ U → G) (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U t ht e g).left i =
      ⟨lWord U t (e.symm i) g, lWord_mem U t ht _ g⟩ := by
  simp [monomialFinHom]

/-- The finite permutation coordinate translates the corresponding coset. -/
@[simp] theorem monomialFinHom_right (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index)
    (g : G) (i : Fin U.index) :
    (monomialFinHom U t ht e g).right i = e (g • e.symm i) := by
  simp [monomialFinHom]

/-- The inverse finite permutation coordinate translates the named coset by the inverse group
element. -/
@[simp] theorem monomialFinHom_right_inv (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index) (g : G) (i : Fin U.index) :
    (monomialFinHom U t ht e g).right⁻¹ i = e (g⁻¹ • e.symm i) := by
  simpa only [map_inv, SemidirectProduct.inv_right] using monomialFinHom_right U t ht e g⁻¹ i

/-- The finite-coordinate monomial homomorphism is injective. -/
theorem monomialFinHom_injective (t : G ⧸ U → G)
    (ht : ∀ x, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (e : G ⧸ U ≃ Fin U.index) :
    Function.Injective (monomialFinHom U t ht e) :=
  (WreathProduct.congr e).injective.comp (monomialHom_injective U t ht)

end FiniteCoordinates

end TauCeti
