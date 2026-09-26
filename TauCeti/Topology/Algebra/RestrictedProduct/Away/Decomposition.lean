/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Away.Basic
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Left
public import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng
public import TauCeti.Topology.Algebra.RestrictedProduct.Finite
public import TauCeti.Topology.Algebra.RestrictedProduct.Sum

/-!
# Decomposition of a restricted product along a finite set of indices

For a finite set `S` of indices, a restricted product `Πʳ i, [G i, U i]` is the product of the
plain product `Π i : S, G i` of the factors at `S` with the restricted product away from `S`: an
element is determined by its coordinates at `S`, which carry no integrality condition because
finitely many indices never affect restrictedness, and its restriction away from `S`. This is the
shape in which an adelic group is split into the local groups at a finite set of places times the
restricted product over the remaining places.

The decomposition `awayDecomposition S hS U` is the composite of three equivalences that are each
coordinatewise the identity: reindexing along `Equiv.sumCompl (· ∈ S)`
(`restrictedProductReindex`), the splitting of a restricted product over a sum of index types
(`restrictedProductSum`), and the collapse of the restricted product over the finite index type
`S` to the plain product (`restrictedProductOfFinite`). It is pinned by its coordinate formulas in
both directions, and its second component is the restriction `restrictAway S U`.

The decomposition is continuous for every reference family. Its inverse is continuous when the
reference subgroups **away from `S`** are open; the reference subgroups at `S` play no role, as
the finite factor carries no integrality condition. The openness hypothesis cannot be dropped: see
`not_continuous_awayDecomposition_symm`.

Everything here is also stated for additive groups (`addAwayDecomposition`, …), the form in which
the adeles of a global field split as the completions at a finite set of places times the adeles
away from it.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)]

/-- For a finite set `S` of indices, the decomposition of a restricted product as the plain
product of the factors at `S` times the restricted product away from `S`, coordinatewise the
identity in both directions: `x` goes to `((x i)_{i ∈ S}, (x i)_{i ∉ S})`, and `(y, z)` goes to
the element with coordinate `y ⟨i, _⟩` at `i ∈ S` and `z ⟨i, _⟩` at `i ∉ S`.

It is the composite of the reindexing along `Equiv.sumCompl (· ∈ S)`, the splitting over the sum
`S ⊕ {i // i ∉ S}`, and the collapse of the restricted product over the finite index type `S`. -/
@[to_additive addAwayDecomposition /-- For a finite set `S` of indices, the decomposition of a
restricted product of additive groups as the plain product of the factors at `S` times the
restricted product away from `S`, coordinatewise the identity in both directions: `x` goes to
`((x i)_{i ∈ S}, (x i)_{i ∉ S})`, and `(y, z)` goes to the element with coordinate `y ⟨i, _⟩` at
`i ∈ S` and `z ⟨i, _⟩` at `i ∉ S`.

It is the composite of the reindexing along `Equiv.sumCompl (· ∈ S)`, the splitting over the sum
`S ⊕ {i // i ∉ S}`, and the collapse of the restricted product over the finite index type `S`. -/]
noncomputable def awayDecomposition (S : Set ι) (hS : S.Finite) (U : ∀ i, Subgroup (G i)) :
    RestrictedProductGroup U ≃*
      RestrictedProductGroupWithFactor (∀ i : S, G i) fun j : {i // i ∉ S} ↦ U j.1 :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  haveI : Finite S := hS.to_subtype
  -- The reindexed restricted product over `S ⊕ {i // i ∉ S}`, split into its two summands.
  let c := (restrictedProductReindex U (Equiv.sumCompl (· ∈ S))).trans
    (restrictedProductSum fun k ↦ U (Equiv.sumCompl (· ∈ S) k))
  -- The collapse of the finite `S`-summand to the plain product.
  let f := restrictedProductOfFinite fun i : S ↦ U (Equiv.sumCompl (· ∈ S) (Sum.inl i))
  -- The composite equivalence, whose maps are spelled out below.
  let d := c.trans (f.prodCongr (MulEquiv.refl _))
  -- The factors of the two summands are `G (Equiv.sumCompl (· ∈ S) (Sum.inl i))` and
  -- `G (Equiv.sumCompl (· ∈ S) (Sum.inr j))`, which agree with `G i` and `G j` only after
  -- unfolding `Equiv.sumCompl`. Writing the maps of `d` out in terms of `c` and `f`, rather than
  -- ascribing `d` the target type, keeps every subterm well typed without that unfolding, so that
  -- the coordinate lemmas below follow from those of the three steps by rewriting.
  { toFun x := (f (c x).1, (c x).2)
    invFun y := c.symm (f.symm y.1, y.2)
    left_inv := d.left_inv
    right_inv := d.right_inv
    map_mul' := d.map_mul }

variable (S : Set ι) (hS : S.Finite) (U : ∀ i, Subgroup (G i))

/-- The first component of the decomposition records the coordinates at `S`. -/
@[to_additive (attr := simp) addAwayDecomposition_fst /-- The first component of the additive
away-`S` decomposition records the coordinates at `S`. -/]
theorem awayDecomposition_fst (x : RestrictedProductGroup U) (i : S) :
    (awayDecomposition S hS U x).1 i = x i := by
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  have h := restrictedProductSum_apply_inl (fun k ↦ U (Equiv.sumCompl (· ∈ S) k))
    (restrictedProductReindex U (Equiv.sumCompl (· ∈ S)) x) i
  rw [restrictedProductReindex_apply] at h
  simp only [awayDecomposition, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulEquiv.trans_apply,
    restrictedProductOfFinite_apply]
  -- `h` is the goal up to the computation rule `Equiv.sumCompl_apply_inl`, which holds by `rfl`.
  exact h

/-- The second component of the decomposition records the coordinates away from `S`.

Not a `simp` lemma: `simp` proves it from `awayDecomposition_snd_eq_restrictAway` and
`restrictAway_apply`. -/
@[to_additive addAwayDecomposition_snd /-- The second component of the additive away-`S`
decomposition records the coordinates away from `S`.

Not a `simp` lemma: `simp` proves it from `addAwayDecomposition_snd_eq_addRestrictAway` and
`addRestrictAway_apply`. -/]
theorem awayDecomposition_snd (x : RestrictedProductGroup U) (j : {i // i ∉ S}) :
    (awayDecomposition S hS U x).2 j = x j := by
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  have h := restrictedProductSum_apply_inr (fun k ↦ U (Equiv.sumCompl (· ∈ S) k))
    (restrictedProductReindex U (Equiv.sumCompl (· ∈ S)) x) j
  rw [restrictedProductReindex_apply] at h
  simp only [awayDecomposition, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulEquiv.trans_apply]
  -- `h` is the goal up to the computation rule `Equiv.sumCompl_apply_inr`, which holds by `rfl`.
  exact h

/-- The second component of the decomposition is the restriction away from `S`. -/
@[to_additive (attr := simp) addAwayDecomposition_snd_eq_addRestrictAway /-- The second component of
the additive away-`S` decomposition is the restriction away from `S`. -/]
theorem awayDecomposition_snd_eq_restrictAway (x : RestrictedProductGroup U) :
    (awayDecomposition S hS U x).2 = restrictAway S U x := by
  ext j
  simp [awayDecomposition_snd]

/-- At an index `i ∈ S`, the inverse of the decomposition reads its coordinate off the plain
product over `S`. -/
@[to_additive (attr := simp) addAwayDecomposition_symm_apply_of_mem /-- At an index `i ∈ S`, the
inverse of the additive away-`S` decomposition reads its coordinate off the plain product
over `S`. -/]
theorem awayDecomposition_symm_apply_of_mem
    (y : RestrictedProductGroupWithFactor (∀ i : S, G i) fun j : {i // i ∉ S} ↦ U j.1)
    (i : ι) (hi : i ∈ S) :
    (awayDecomposition S hS U).symm y i = y.1 ⟨i, hi⟩ := by
  have h := awayDecomposition_fst S hS U ((awayDecomposition S hS U).symm y) ⟨i, hi⟩
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- At an index `i ∉ S`, the inverse of the decomposition reads its coordinate off the restricted
product away from `S`. -/
@[to_additive (attr := simp) addAwayDecomposition_symm_apply_of_notMem /-- At an index `i ∉ S`, the
inverse of the additive away-`S` decomposition reads its coordinate off the restricted product away
from `S`. -/]
theorem awayDecomposition_symm_apply_of_notMem
    (y : RestrictedProductGroupWithFactor (∀ i : S, G i) fun j : {i // i ∉ S} ↦ U j.1)
    (i : ι) (hi : i ∉ S) :
    (awayDecomposition S hS U).symm y i = y.2 ⟨i, hi⟩ := by
  have h := awayDecomposition_snd S hS U ((awayDecomposition S hS U).symm y) ⟨i, hi⟩
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

variable [∀ i, TopologicalSpace (G i)]

/-- The decomposition is continuous for every reference family. -/
@[to_additive continuous_addAwayDecomposition /-- The additive away-`S` decomposition is continuous
for every reference family. -/]
theorem continuous_awayDecomposition : Continuous (awayDecomposition S hS U) := by
  let _ : DecidablePred (· ∈ S) := Classical.decPred _
  have : Finite S := hS.to_subtype
  -- Each of the three steps is a continuous map out of a single restricted product.
  have hc : Continuous ((restrictedProductReindex U (Equiv.sumCompl (· ∈ S))).trans
      (restrictedProductSum fun k ↦ U (Equiv.sumCompl (· ∈ S) k))) :=
    (continuous_restrictedProductSum _).comp (continuous_restrictedProductReindex U _)
  exact ((continuous_restrictedProductOfFinite _).comp (continuous_fst.comp hc)).prodMk
    (continuous_snd.comp hc)

/-- The inverse of the decomposition is continuous when the reference subgroups away from `S` are
open; the reference subgroups at `S` play no role, since the finite factor carries no integrality
condition. Together with `continuous_awayDecomposition` this makes the decomposition a
homeomorphism for such families. -/
@[to_additive continuous_addAwayDecomposition_symm /-- The inverse of the additive away-`S`
decomposition is continuous when the reference subgroups away from `S` are open; the reference
subgroups at `S` play no role, since the finite factor carries no integrality condition. Together
with `continuous_addAwayDecomposition` this makes the decomposition a homeomorphism for such
families. -/]
theorem continuous_awayDecomposition_symm (hU : ∀ i ∉ S, IsOpen (U i : Set (G i))) :
    Continuous (awayDecomposition S hS U).symm :=
  -- A map out of a product with a restricted-product factor, coordinatewise the identity.
  continuous_restrictedProduct_of_apply_eq_of_isOpen hS hU
    (fun y i ↦ awayDecomposition_symm_apply_of_mem S hS U y i.1 i.2)
    fun y j ↦ awayDecomposition_symm_apply_of_notMem S hS U y j.1 j.2

end TauCeti
