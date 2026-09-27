/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.Topology.Algebra.Group.TransversalWord
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The monomial homomorphism of a subgroup transversal

A transversal for `U ≤ G` embeds `G` in the permutation wreath product with base group `U`
and coordinates indexed by `G ⧸ U`. Its permutation part is left translation on cosets; its
coordinate at `x` is the transversal word `t(x)⁻¹ g t(g⁻¹ • x)`. The cocycle law for that word
is exactly the multiplication law of the wreath product. For an open subgroup the map is
continuous in the coordinate topology, even though the transversal itself need not be continuous.

This is the monomial construction used in Evens' multiplicative transfer; see L. Evens,
"A generalization of the transfer map in the cohomology of groups", Trans. AMS 108 (1963),
§§2–3.
-/

public section

namespace TauCeti

universe u v

namespace WreathProduct

variable (D : Type u) (ι : Type v) [Group D]

/-- The coordinate topology on a permutation wreath product. The base coordinates have the
product topology, while the permutation has the topology of pointwise convergence. -/
instance instTopologicalSpace [TopologicalSpace D] [TopologicalSpace ι] :
    TopologicalSpace (WreathProduct D ι) :=
  TopologicalSpace.induced
    (fun w : WreathProduct D ι => (w.left, (w.right : ι → ι))) inferInstance

variable {D ι} {κ : Type*} [TopologicalSpace D] [TopologicalSpace ι]
  [TopologicalSpace κ]

/-- Relabeling a wreath product is continuous when the relabeling of its index type is
continuous. Both coordinates are checked in the coordinate topology. -/
theorem continuous_congr (e : ι ≃ κ) (he : Continuous e) :
    Continuous (congr (D := D) e) := by
  have hcoords : Continuous (fun w : WreathProduct D ι =>
      (w.left, (w.right : ι → ι))) := continuous_induced_dom
  apply continuous_induced_rng.mpr
  exact (continuous_pi fun i => by
    simpa only [congr_left, Function.comp_def] using
      (continuous_apply (e.symm i)).comp hcoords.fst).prodMk
      (continuous_pi fun i => by
        simpa only [congr_right, Equiv.permCongr_apply, Function.comp_def] using
          he.comp ((continuous_apply (e.symm i)).comp hcoords.snd))

end WreathProduct

variable {G : Type u} [Group G] (U : Subgroup G)

/-- The monomial homomorphism associated to a transversal `t` of `U`. Its permutation part is
left translation on `G ⧸ U`; the coordinate at `x` is the element
`t(x)⁻¹ g t(g⁻¹ • x)` of `U`. -/
def monomialHom (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →* WreathProduct U (G ⧸ U) where
  toFun g := ⟨(fun x => ⟨lWord U t x g, lWord_mem U t ht x g⟩),
    MulAction.toPermHom G (G ⧸ U) g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      exact lWord_one U t x
    · exact map_one (MulAction.toPermHom G (G ⧸ U))
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext x
      apply Subtype.ext
      exact (lWord_mul_lWord U t x g h).symm
    · exact map_mul (MulAction.toPermHom G (G ⧸ U)) g h

/-- The coordinate of the monomial homomorphism is the transversal word. -/
@[simp] theorem monomialHom_left (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (g : G) (x : G ⧸ U) :
    ((monomialHom U t ht g).left x : G) = lWord U t x g := by
  simp [monomialHom]

/-- The permutation part of the monomial homomorphism translates left cosets. -/
@[simp] theorem monomialHom_right (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x)
    (g : G) (x : G ⧸ U) :
    (monomialHom U t ht g).right x = g • x := by
  simp [monomialHom]

/-- A subgroup transversal gives a faithful monomial representation: the permutation part
locates the coset of `g`, and one coordinate recovers `g` from its transversal word. -/
theorem monomialHom_injective (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Function.Injective (monomialHom U t ht) := by
  intro g h heq
  let x : G ⧸ U := QuotientGroup.mk 1
  have hx : g • x = h • x := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => w.right x) heq
    simpa only [monomialHom_right] using this
  have hw : lWord U t (g • x) g = lWord U t (g • x) h := by
    have := congrArg (fun w : WreathProduct U (G ⧸ U) => ((w.left (g • x) : U) : G)) heq
    simpa only [monomialHom_left] using this
  have heq' : g * t x = h * t x := by
    calc
      g * t x = t (g • x) * lWord U t (g • x) g :=
        (transversal_smul_mul_lWord U t x g).symm
      _ = t (h • x) * lWord U t (h • x) h := by rw [← hx, hw]
      _ = h * t x := transversal_smul_mul_lWord U t x h
  exact mul_right_cancel heq'

/-- The monomial homomorphism is continuous when `U` is open. Continuity is coordinatewise:
the transversal word is locally continuous, and the coset permutation varies continuously at
each coset. -/
theorem continuous_monomialHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialHom U t ht) := by
  apply continuous_induced_rng.mpr
  exact (continuous_pi fun x =>
    (continuous_lWord U t hU x).subtype_mk _).prodMk
      (continuous_pi fun x => continuous_id.smul continuous_const)

/-- The continuous monomial homomorphism for an open subgroup and a chosen transversal. -/
def monomialContinuousHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (G ⧸ U) :=
  ⟨monomialHom U t ht, continuous_monomialHom U hU t ht⟩

/-- The continuous monomial homomorphism has the same underlying homomorphism. -/
@[simp] theorem monomialContinuousHom_apply [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialContinuousHom U hU t ht g = monomialHom U t ht g := by
  rfl

section FiniteIndex

variable [U.FiniteIndex]

/-- Relabel the cosets by `Fin (G : U)`, identifying the monomial representation with a
homomorphism to `U^(G : U) ⋊ Sym(G : U)`. The coset-indexed map above avoids this labeling. -/
noncomputable def monomialFinHom (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →* WreathProduct U (Fin U.index) :=
  (WreathProduct.congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)).toMonoidHom.comp (monomialHom U t ht)

/-- The finite-coordinate monomial homomorphism is injective. -/
theorem monomialFinHom_injective (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Function.Injective (monomialFinHom U t ht) :=
  (WreathProduct.congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)).injective.comp
      (monomialHom_injective U t ht)

/-- The finite-coordinate monomial homomorphism is continuous for an open subgroup. -/
theorem continuous_monomialFinHom [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
    (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    Continuous (monomialFinHom U t ht) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  exact (WreathProduct.continuous_congr
    (Finite.equivFinOfCardEq U.index_eq_card.symm)
    continuous_of_discreteTopology).comp (continuous_monomialHom U hU t ht)

/-- The finite-coordinate continuous monomial homomorphism for an open subgroup. -/
noncomputable def monomialFinContinuousHom [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G] (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) :
    G →ₜ* WreathProduct U (Fin U.index) :=
  ⟨monomialFinHom U t ht, continuous_monomialFinHom U hU t ht⟩

/-- The finite-coordinate continuous map has the finite-coordinate monomial homomorphism as
its underlying map. -/
@[simp] theorem monomialFinContinuousHom_apply [TopologicalSpace G] [ContinuousMul G]
    [ContinuousInv G] (hU : IsOpen (U : Set G)) (t : G ⧸ U → G)
    (ht : ∀ x : G ⧸ U, (QuotientGroup.mk (t x) : G ⧸ U) = x) (g : G) :
    monomialFinContinuousHom U hU t ht g = monomialFinHom U t ht g := by
  rfl

end FiniteIndex

end TauCeti
