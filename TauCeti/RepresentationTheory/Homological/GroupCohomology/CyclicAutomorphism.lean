/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.RepresentationTheory.Cyclic.Affine
public import TauCeti.RepresentationTheory.Cyclic.Restriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.Abel
import TauCeti.LinearAlgebra.Exact

/-!
# Group cohomology of the cyclic representation of an automorphism of finite order

Let `T` be an additive commutative group, `m > 0`, and `A : T ≃+ T` an additive automorphism of
order dividing `m`, that is `A^[m] = id`. Then the cyclic group `C_m = Multiplicative (ZMod m)`
acts on `T` with its standard generator `ofAdd 1` acting by `A`; this is the integral
representation `AddEquiv.cyclicRep A hA : Rep ℤ C_m`. Its norm `N = ∑ g, ρ g` is the ordered sum
of powers `∑ j < m, A^j` (`AddEquiv.cyclicRepresentation_norm_apply`).

The group cohomology of `C_m` is computed by Mathlib's periodic resolution
(`Rep.FiniteCyclicGroup.groupCohomologyπOdd`, `Rep.FiniteCyclicGroup.groupCohomologyπEven`). For
the cyclic representation of `A` these quotient maps read as follows.

* In odd degree, and so in degree one, the classes are the elements `t` with
  `∑ j < m, A^j t = 0`, two of them having the same class exactly when they differ by
  `b - A b` for some `b : T` (`AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff`). The image of
  `A - 1` is that of `1 - A`, by negating the argument. These are the twists `t` for which the
  affine map `x ↦ A x + t` has order dividing `m`, up to conjugation by translations, which
  changes `t` to `t + (b - A b)`: two norm-zero twists have the same class exactly when their
  affine maps are conjugate by a translation
  (`AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff_exists_conj_affineEquiv`).
* In positive even degree, the classes are the fixed points of `A`, two of them having the same
  class exactly when they differ by a norm `∑ j < m, A^j y`
  (`AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`).

Every class arises in each case (`Rep.FiniteCyclicGroup.groupCohomologyπOdd_surjective`,
`Rep.FiniteCyclicGroup.groupCohomologyπEven_surjective`). For a homomorphism `χ : C_n → C_m`
sending the generator to its `d`-th power, an additive map
`f` intertwining `A^d` with `B` induces change-of-group maps on these classes. In degree one,
the class of `t` maps to the class of `f (partialNorm A d t)`; in degree two, the class of a
fixed point `v` maps to the class of `q • f v`, where `d * n = q * m`
(`AddMonoidHom.map_cyclicRepResHom_groupCohomologyπOdd_one`,
`AddMonoidHom.map_cyclicRepResHom_groupCohomologyπEven_two`). Coefficient maps are the case
`χ = id` and `d = q = 1`.

The representation itself is constructed in `TauCeti.RepresentationTheory.Cyclic.Automorphism`.

The second part of the file treats an exact sequence `0 → Λ → E → T → 0` of abelian groups whose
maps `i` and `p` intertwine automorphisms `AΛ`, `AE`, `AT` of order dividing `m`, for instance a
lattice `Λ` in a real vector space `E` with quotient torus `T`. It is a short exact sequence of
cyclic representations (`AddMonoidHom.shortExact_cyclicRepShortComplex`), and its connecting
homomorphism `δ : H¹(C_m, T) ⟶ H²(C_m, Λ)` is computed on classes: for `t` killed by the norm
and a lift `s : E` of `t`, the norm `∑ j < m, AE^j s` is the image of a fixed point `v` of `AΛ`
(`AddMonoidHom.exists_apply_eq_sum_range_iterate`), and `δ` sends the class of `t` to the class
of `v` (`TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one`). Changing `s` by the
image of `l : Λ` changes `v` by the norm of `l` (`AddMonoidHom.sum_range_iterate_add_apply`),
which does not change its class. In particular, when multiplication by `m` is injective on `E`
and `m • s = i v`, the class of the image of `s` is sent to the class of `v`, that is
`δ [v / m] = [v]`
(`TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one_of_nsmul_eq`). When multiplication
by `m` is bijective on `E`, as for a real vector space, the cohomology of `E` vanishes in positive
degrees and `δ` is an isomorphism (`TauCeti.cyclicConnectingEquiv`). The connecting homomorphism
is natural under arbitrary homomorphisms `χ : C_l → C_m`: maps between two such sequences
which intertwine the appropriate powers of the automorphisms and commute with the sequence
maps commute with `δ` (`TauCeti.map_δ_cyclicRepShortComplex`).

The construction is compatible with products. The cyclic representation of the product
automorphism `A × B` of `T × M` is the biproduct of those of `A` and `B`
(`AddEquiv.cyclicRepBinaryBiconeIsBilimit`), so the projections identify its cohomology with the
product of the two cohomologies
(`CategoryTheory.Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv`); in degrees one and two
this sends the class of `(t, u)` to the pair of classes of `t` and `u`
(`TauCeti.groupCohomologyProdEquiv_groupCohomologyπOdd_one`,
`TauCeti.groupCohomologyProdEquiv_groupCohomologyπEven_two`). The product of two equivariant exact
sequences is again one (`AddMonoidHom.shortExact_cyclicRepShortComplex_prodMap`), and under these
identifications its connecting homomorphism is the product of the two connecting homomorphisms
(`TauCeti.groupCohomologyProdEquiv_δ_cyclicRepShortComplex_prodMap`); in particular the connecting
isomorphism of a product of tori is the product of their connecting isomorphisms
(`TauCeti.groupCohomologyProdEquiv_cyclicConnectingEquiv`).

The last part of the file specializes to the trivial action, given by the identity automorphism.
Then the odd-degree cohomology of `C_m` is the `m`-torsion `T[m]`
(`TauCeti.groupCohomologyOddEquivTorsionBy`) and its positive even-degree cohomology is `T ⧸ m T`
(`TauCeti.groupCohomologyEvenEquivQuotSMulTop`). Through these identifications the connecting
homomorphism of `0 → Λ → E → T → 0` becomes the snake-lemma map `TauCeti.torsionByδ` of
multiplication by `m`, which sends `t` to the coset of `v` when `m • s = i v` for a lift `s` of
`t` (`TauCeti.groupCohomologyEvenEquivQuotSMulTop_δ`). When multiplication by `m` is bijective on
`E`, the snake-lemma isomorphism `T[m] ≃ Λ ⧸ m Λ` is therefore the connecting isomorphism
(`TauCeti.torsionByδEquiv_eq_trans_cyclicConnectingEquiv`). For a torus `E ⧸ Λ` this is the
description of its `m`-torsion points as `(1 / m) Λ ⧸ Λ ≃ Λ ⧸ m Λ`.

## Main definitions

* `AddMonoidHom.cyclicRepShortComplex`: the short complex `Λ ⟶ E ⟶ T` of cyclic
  representations.
* `TauCeti.cyclicConnectingEquiv`: the connecting isomorphism `H¹(C_m, T) ≃ H²(C_m, Λ)`
  when multiplication by `m` is bijective on `E`.
* `TauCeti.groupCohomologyOddEquivTorsionBy`: odd-degree cohomology of the trivial action is
  `T[m]`.
* `TauCeti.groupCohomologyEvenEquivQuotSMulTop`: positive even-degree cohomology of the trivial
  action is `T ⧸ m T`.

## Main results

* `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff`: odd-degree classes are norm-zero elements
  modulo the image of `1 - A`.
* `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff_exists_conj_affineEquiv`: two norm-zero twists
  have the same odd-degree class exactly when their affine maps are conjugate by a translation.
* `AddEquiv.groupCohomologyπEven_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`: positive even-degree classes are fixed points
  of `A` modulo the image of the norm.
* `AddMonoidHom.map_cyclicRepHom_groupCohomologyπOdd_one`,
  `AddMonoidHom.map_cyclicRepHom_groupCohomologyπEven_two`: an equivariant map acts on degree-`1`
  and degree-`2` classes by acting on their representatives.
* `AddMonoidHom.shortExact_cyclicRepShortComplex_iff`: a sequence of abelian groups with
  equivariant maps is exact exactly when it is a short exact sequence of cyclic representations.
* `AddMonoidHom.shortExact_cyclicRepShortComplex_prodMap`: the product of two such short exact
  sequences is short exact.

* `AddMonoidHom.map_cyclicRepResHom_groupCohomologyπOdd_one`,
  `AddMonoidHom.map_cyclicRepResHom_groupCohomologyπEven_two`: change-of-group maps act on
  degree-one twists by partial norms and on degree-two fixed points by the degree factor.
* `AddMonoidHom.shortExact_cyclicRepShortComplex`: an exact sequence of abelian groups with
  equivariant maps is a short exact sequence of cyclic representations.
* `TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one`,
  `TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one_of_nsmul_eq`: the connecting
  homomorphism sends the class of `t` to the class of the norm of a lift of `t`, and the class of
  `v / m` to the class of `v`.
* `TauCeti.map_δ_cyclicRepShortComplex`: naturality of the connecting homomorphism under maps of
  equivariant exact sequences.
* `TauCeti.groupCohomologyProdEquiv_groupCohomologyπOdd_one`,
  `TauCeti.groupCohomologyProdEquiv_groupCohomologyπEven_two`: the cohomology of a product of cyclic
  representations is the product of the cohomologies, computed on representatives.
* `TauCeti.groupCohomologyProdEquiv_δ_cyclicRepShortComplex_prodMap`,
  `TauCeti.groupCohomologyProdEquiv_cyclicConnectingEquiv`: the connecting homomorphism and the
  connecting isomorphism of a product of sequences are the products of those of the factors.

* `TauCeti.map_δ_cyclicRepShortComplex`: naturality of the connecting homomorphism under
  homomorphisms of cyclic groups and compatible maps of exact sequences.
* `TauCeti.groupCohomologyEvenEquivQuotSMulTop_δ`: for trivial actions, the connecting
  homomorphism is the snake-lemma map `T[m] → Λ ⧸ m Λ`.
* `TauCeti.torsionByδEquiv_eq_trans_cyclicConnectingEquiv`: for trivial actions and `m` bijective
  on `E`, the snake-lemma isomorphism `T[m] ≃ Λ ⧸ m Λ` is the connecting isomorphism.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §6 (the periodic resolution of a cyclic group).
* J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer (1979), Chapter VIII,
  §4 (the cohomology of cyclic groups).
-/

public section

open CategoryTheory Rep Rep.FiniteCyclicGroup
open Multiplicative (mem_zpowers_ofAdd_one)

namespace AddEquiv

variable {T : Type} [AddCommGroup T] {m : ℕ} [NeZero m] (A : T ≃+ T) (hA : (⇑A)^[m] = id)

/-- **Odd-degree classes of the cyclic representation.** A norm-zero element `x` has zero class
in odd degree exactly when `x = b - A b` for some `b : T`. -/
theorem groupCohomologyπOdd_cyclicRep_eq_zero_iff (i : ℕ) (hi : Odd i)
    (x : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap) :
    groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x = 0 ↔
      ∃ b, b - A b = (x : T) := by
  rw [groupCohomologyπOdd_eq_zero_iff, mem_range_cyclicRep_applyAsHom_sub_iff]

/-- **Odd-degree classes of the cyclic representation.** Two norm-zero elements `x` and `y`
have the same class in odd degree exactly when `y = x + (b - A b)` for some `b : T`. -/
theorem groupCohomologyπOdd_cyclicRep_eq_iff (i : ℕ) (hi : Odd i)
    (x y : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap) :
    groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x =
        groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi y ↔
      ∃ b, (y : T) = (x : T) + (b - A b) := by
  rw [eq_comm, groupCohomologyπOdd_eq_iff, mem_range_cyclicRep_applyAsHom_sub_iff]
  constructor <;> rintro ⟨b, hb⟩ <;> refine ⟨b, ?_⟩ <;> rw [hb] <;> abel

/-- **Translation conjugacy classes of affine maps.** Two norm-zero twists `x` and `y` have the
same class in odd degree, in particular in degree one, exactly when the affine maps
`z ↦ A z + x` and `z ↦ A z + y` are conjugate by a translation of `T`. -/
theorem groupCohomologyπOdd_cyclicRep_eq_iff_exists_conj_affineEquiv (i : ℕ) (hi : Odd i)
    (x y : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap) :
    groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x =
        groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi y ↔
      ∃ b, MulAut.conj (Equiv.addRight b) (A.affineEquiv x) = A.affineEquiv y := by
  rw [groupCohomologyπOdd_cyclicRep_eq_iff]
  simp_rw [conj_addRight_affineEquiv, affineEquiv_inj, true_and, eq_comm]

/-- **Even-degree classes of the cyclic representation.** A fixed point `x` of `A` has zero
class in positive even degree exactly when it is a norm `∑ j < m, A^j y`. -/
theorem groupCohomologyπEven_cyclicRep_eq_zero_iff (i : ℕ) [NeZero i] (hi : Even i)
    (x : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap) :
    groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x = 0 ↔
      ∃ y, ∑ j ∈ Finset.range m, (⇑A)^[j] y = (x : T) := by
  rw [groupCohomologyπEven_eq_zero_iff, mem_range_cyclicRep_norm_iff]

/-- **Even-degree classes of the cyclic representation.** Two fixed points `x` and `y` of `A`
have the same class in positive even degree exactly when `y = x + ∑ j < m, A^j z` for some
`z : T`. -/
theorem groupCohomologyπEven_cyclicRep_eq_iff (i : ℕ) [NeZero i] (hi : Even i)
    (x y : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap) :
    groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi x =
        groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one i hi y ↔
      ∃ z, (y : T) = (x : T) + ∑ j ∈ Finset.range m, (⇑A)^[j] z := by
  rw [eq_comm, groupCohomologyπEven_eq_iff, mem_range_cyclicRep_norm_iff]
  constructor <;> rintro ⟨z, hz⟩ <;> refine ⟨z, ?_⟩ <;> rw [hz] <;> abel

end AddEquiv

namespace AddMonoidHom

/-! ### Equivariant maps on the cohomology classes -/

section ChangeOfCyclicGroup

variable {T M : Type} [AddCommGroup T] [AddCommGroup M] {m n : ℕ} [NeZero m] [NeZero n]
  {A : T ≃+ T} {B : M ≃+ M} (f : T →+ M)
  (hA : (⇑A)^[m] = _root_.id) (hB : (⇑B)^[n] = _root_.id)
  (χ : Multiplicative (ZMod n) →* Multiplicative (ZMod m)) (d : ℕ)
  (hχ : χ (.ofAdd 1) = (.ofAdd 1) ^ d) (hf : ∀ x, f ((⇑A)^[d] x) = B (f x))

/-- Pulling back a degree-one class along a homomorphism sending the generator to its
`d`-th power replaces its twist `x` by `f (partialNorm A d x)`. -/
theorem map_cyclicRepResHom_groupCohomologyπOdd_one
    (x : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap)
    (y : LinearMap.ker (B.cyclicRep hB).norm.asHom.hom.toLinearMap)
    (hy : (y : M) = f (A.partialNorm d x)) :
    groupCohomology.map χ (f.cyclicRepResHom hA hB χ d hχ hf) 1
        (groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one x) =
      groupCohomologyπOdd (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one y := by
  have h := map_groupCohomologyπOdd_one (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one
    χ mem_zpowers_ofAdd_one d hχ (f.cyclicRepResHom hA hB χ d hχ hf) x y
  apply h
  rw [hy, AddEquiv.partialNorm_def]
  simp only [AddMonoidHom.coe_cyclicRepResHom_hom,
    AddEquiv.cyclicRepresentation_ofAdd_one_pow_apply]

/-- Pulling back a degree-two class multiplies its fixed-point representative by `q`,
where `d * n = q * m`. In particular, restriction along the standard inclusion of a cyclic
subgroup (`m = d * n`) preserves the representative. -/
theorem map_cyclicRepResHom_groupCohomologyπEven_two (q : ℕ) (hq : d * n = q * m)
    (x : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (y : LinearMap.ker (applyAsHom (B.cyclicRep hB) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (hy : (y : M) = q • f x) :
    groupCohomology.map χ (f.cyclicRepResHom hA hB χ d hχ hf) 2
        (groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two x) =
      groupCohomologyπEven (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two y := by
  have h := map_groupCohomologyπEven_two (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one
    χ mem_zpowers_ofAdd_one d hχ (f.cyclicRepResHom hA hB χ d hχ hf) q
    (by simpa [Nat.card_eq_fintype_card] using hq) x y
  exact h (by simpa only [AddMonoidHom.coe_cyclicRepResHom_hom] using hy)

end ChangeOfCyclicGroup

/-! ### The connecting class of an equivariant short exact sequence -/

variable {Λ E T : Type} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup T] {m : ℕ} [NeZero m]
  {AΛ : Λ ≃+ Λ} {AE : E ≃+ E} {AT : T ≃+ T} (i : Λ →+ E) (p : E →+ T)

/-- The short complex `Λ ⟶ E ⟶ T` of cyclic representations of `C_m` defined by additive maps
`i : Λ →+ E` and `p : E →+ T` intertwining automorphisms `AΛ`, `AE`, `AT` of order dividing `m`,
with `p ∘ i = 0`. Its body is exposed, so that its terms are the cyclic representations of `AΛ`,
`AE` and `AT` by definition and its connecting homomorphisms act on their cohomology. -/
@[expose]
noncomputable def cyclicRepShortComplex (hΛ : (⇑AΛ)^[m] = _root_.id)
    (hE : (⇑AE)^[m] = _root_.id) (hT : (⇑AT)^[m] = _root_.id) (hi : ∀ x, i (AΛ x) = AE (i x))
    (hp : ∀ x, p (AE x) = AT (p x)) (hpi : ∀ x, p (i x) = 0) :
    ShortComplex (Rep ℤ (Multiplicative (ZMod m))) where
  f := i.cyclicRepHom hΛ hE hi
  g := p.cyclicRepHom hE hT hp
  zero := by
    ext x
    simpa using hpi x

/-- The short complex `Λ ⟶ E ⟶ T` of cyclic representations is short exact when
`0 → Λ → E → T → 0` is an exact sequence of abelian groups. -/
theorem shortExact_cyclicRepShortComplex {hΛ : (⇑AΛ)^[m] = _root_.id}
    {hE : (⇑AE)^[m] = _root_.id} {hT : (⇑AT)^[m] = _root_.id} {hi : ∀ x, i (AΛ x) = AE (i x)}
    {hp : ∀ x, p (AE x) = AT (p x)} {hpi : ∀ x, p (i x) = 0} (hinj : Function.Injective i)
    (hexact : Function.Exact i p) (hsurj : Function.Surjective p) :
    (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).ShortExact :=
  -- The maps of the short complex are `i` and `p` on underlying groups.
  have hf := congrFun (coe_cyclicRepHom_hom i hΛ hE hi)
  have hg := congrFun (coe_cyclicRepHom_hom p hE hT hp)
  { exact := (forget₂ (Rep ℤ (Multiplicative (ZMod m))) (ModuleCat ℤ)).reflects_exact_of_faithful
      _ <| (ShortComplex.moduleCat_exact_iff _).2 fun x hx ↦
        ((hexact x).1 ((hg x).symm.trans hx)).imp fun y hy ↦ (hf y).trans hy
    mono_f := (Rep.mono_iff_injective _).2 fun x y h ↦ hinj ((hf x).symm.trans (h.trans (hf y)))
    epi_g := (Rep.epi_iff_surjective _).2 fun x ↦ (hsurj x).imp fun y hy ↦ (hg y).trans hy }

/-- The short complex `Λ ⟶ E ⟶ T` of cyclic representations is short exact exactly when
`0 → Λ → E → T → 0` is an exact sequence of abelian groups. -/
theorem shortExact_cyclicRepShortComplex_iff {hΛ : (⇑AΛ)^[m] = _root_.id}
    {hE : (⇑AE)^[m] = _root_.id} {hT : (⇑AT)^[m] = _root_.id} {hi : ∀ x, i (AΛ x) = AE (i x)}
    {hp : ∀ x, p (AE x) = AT (p x)} {hpi : ∀ x, p (i x) = 0} :
    (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).ShortExact ↔
      Function.Injective i ∧ Function.Exact i p ∧ Function.Surjective p := by
  refine ⟨fun hS ↦ ?_, fun h ↦ shortExact_cyclicRepShortComplex i p h.1 h.2.1 h.2.2⟩
  -- Read the sequence on underlying abelian groups, where its maps are `i` and `p`.
  have hF := hS.map_of_exact (forget₂ (Rep ℤ (Multiplicative (ZMod m))) (ModuleCat ℤ))
  have hf := congrFun (coe_cyclicRepHom_hom i hΛ hE hi)
  have hg := congrFun (coe_cyclicRepHom_hom p hE hT hp)
  refine ⟨fun x y h ↦ hF.moduleCat_injective_f ((hf x).trans (h.trans (hf y).symm)),
    fun x ↦ ⟨fun hx ↦ ?_, by rintro ⟨y, rfl⟩; exact hpi y⟩,
    fun x ↦ (hF.moduleCat_surjective_g x).imp fun y hy ↦ (hg y).symm.trans hy⟩
  exact ((ShortComplex.moduleCat_exact_iff _).1 hF.exact x ((hg x).trans hx)).imp
    fun y hy ↦ (hf y).symm.trans hy

variable {Λ' E' T' : Type} [AddCommGroup Λ'] [AddCommGroup E'] [AddCommGroup T']
  {AΛ' : Λ' ≃+ Λ'} {AE' : E' ≃+ E'} {AT' : T' ≃+ T'} {i' : Λ' →+ E'} {p' : E' →+ T'}

/-- The product of two short exact sequences of cyclic representations is short exact: for
equivariant exact sequences `0 → Λ → E → T → 0` and `0 → Λ' → E' → T' → 0`, the sequence
`0 → Λ × Λ' → E × E' → T × T' → 0` of cyclic representations of the product automorphisms is
short exact. -/
theorem shortExact_cyclicRepShortComplex_prodMap {hΛ : (⇑AΛ)^[m] = _root_.id}
    {hE : (⇑AE)^[m] = _root_.id} {hT : (⇑AT)^[m] = _root_.id} {hi : ∀ x, i (AΛ x) = AE (i x)}
    {hp : ∀ x, p (AE x) = AT (p x)} {hpi : ∀ x, p (i x) = 0} {hΛ' : (⇑AΛ')^[m] = _root_.id}
    {hE' : (⇑AE')^[m] = _root_.id} {hT' : (⇑AT')^[m] = _root_.id}
    {hi' : ∀ x, i' (AΛ' x) = AE' (i' x)} {hp' : ∀ x, p' (AE' x) = AT' (p' x)}
    {hpi' : ∀ x, p' (i' x) = 0} (hS : (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).ShortExact)
    (hS' : (i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi').ShortExact) :
    ((i.prodMap i').cyclicRepShortComplex (p.prodMap p') (AΛ.iterate_prodCongr_eq_id hΛ hΛ')
      (AE.iterate_prodCongr_eq_id hE hE') (AT.iterate_prodCongr_eq_id hT hT')
      (fun x ↦ Prod.ext (hi x.1) (hi' x.2)) (fun x ↦ Prod.ext (hp x.1) (hp' x.2))
      (fun x ↦ Prod.ext (hpi x.1) (hpi' x.2))).ShortExact := by
  obtain ⟨hinj, hexact, hsurj⟩ := (shortExact_cyclicRepShortComplex_iff i p).1 hS
  obtain ⟨hinj', hexact', hsurj'⟩ := (shortExact_cyclicRepShortComplex_iff i' p').1 hS'
  exact (shortExact_cyclicRepShortComplex_iff _ _).2 ⟨hinj.prodMap hinj',
    Function.Exact.prodMap (f₁ := i.toIntLinearMap) (g₁ := p.toIntLinearMap)
      (f₂ := i'.toIntLinearMap) (g₂ := p'.toIntLinearMap) hexact hexact',
    hsurj.prodMap hsurj'⟩

end AddMonoidHom

open groupCohomology

namespace TauCeti

variable {Λ E T : Type} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup T] {m : ℕ} [NeZero m]
  {AΛ : Λ ≃+ Λ} {AE : E ≃+ E} {AT : T ≃+ T} {i : Λ →+ E} {p : E →+ T}
  {hΛ : (⇑AΛ)^[m] = _root_.id} {hE : (⇑AE)^[m] = _root_.id}
  {hT : (⇑AT)^[m] = _root_.id} {hi : ∀ x, i (AΛ x) = AE (i x)} {hp : ∀ x, p (AE x) = AT (p x)}
  {hpi : ∀ x, p (i x) = 0} (hS : (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).ShortExact)

/-- **The integral connecting class.** For the short exact sequence `0 → Λ → E → T → 0` of
cyclic representations, let `t` be killed by the norm `∑ j < m, AT^j`, lift it to `s : E`, and
write the norm `∑ j < m, AE^j s` as the image of a fixed point `v` of `AΛ`. Then the connecting
homomorphism sends the degree-`1` class of `t` to the degree-`2` class of `v`. -/
theorem δ_cyclicRepShortComplex_groupCohomologyπOdd_one
    (t : LinearMap.ker (AT.cyclicRep hT).norm.asHom.hom.toLinearMap) (s : E) (hs : p s = t)
    (v : LinearMap.ker (applyAsHom (AΛ.cyclicRep hΛ) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (hv : i v = ∑ j ∈ Finset.range m, (⇑AE)^[j] s) :
    δ hS 1 2 rfl
        (groupCohomologyπOdd (AT.cyclicRep hT) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one t) =
      groupCohomologyπEven (AΛ.cyclicRep hΛ) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two v :=
  Rep.FiniteCyclicGroup.δ_groupCohomologyπOdd_one _ _ hS t s
    ((congrFun (AddMonoidHom.coe_cyclicRepHom_hom p hE hT hp) s).trans hs) v
    ((congrFun (AddMonoidHom.coe_cyclicRepHom_hom i hΛ hE hi) v).trans
      (hv.trans (AE.cyclicRepresentation_norm_apply hE s).symm))

/-- **The connecting class of `v / m`.** If multiplication by `m` is injective on `E` and
`m • s = i v` for a fixed point `v` of `AΛ`, then the connecting homomorphism sends the
degree-`1` class of the image `t` of `s` in `T` to the degree-`2` class of `v`. -/
theorem δ_cyclicRepShortComplex_groupCohomologyπOdd_one_of_nsmul_eq
    (hm : Function.Injective fun x : E ↦ m • x)
    (t : LinearMap.ker (AT.cyclicRep hT).norm.asHom.hom.toLinearMap) (s : E) (hs : p s = t)
    (v : LinearMap.ker (applyAsHom (AΛ.cyclicRep hΛ) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (hv : m • s = i v) :
    δ hS 1 2 rfl
        (groupCohomologyπOdd (AT.cyclicRep hT) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one t) =
      groupCohomologyπEven (AΛ.cyclicRep hΛ) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two v := by
  refine δ_cyclicRepShortComplex_groupCohomologyπOdd_one hS t s hs v ?_
  -- `s` is fixed by `AE`, since `m • AE s = AE (i v) = i (AΛ v) = i v = m • s`.
  have hfix : AE s = s := hm <| by
    simp only
    rw [← map_nsmul, hv, ← hi, (AΛ.mem_ker_cyclicRep_applyAsHom_sub_iff hΛ v.1).1 v.2]
  rw [Finset.sum_congr rfl fun j _ ↦ Function.iterate_fixed hfix j, Finset.sum_const,
    Finset.card_range, hv]

/-- **The connecting isomorphism `H¹(C_m, T) ≃ H²(C_m, Λ)`.** When multiplication by `m` is
bijective on `E`, for instance when `E` is a real vector space, the cohomology of `E` vanishes in
positive degrees and the connecting homomorphism of `0 → Λ → E → T → 0` is an isomorphism. -/
noncomputable def cyclicConnectingEquiv (hm : Function.Bijective fun x : E ↦ m • x) :
    groupCohomology (AT.cyclicRep hT) 1 ≃ₗ[ℤ] groupCohomology (AΛ.cyclicRep hΛ) 2 :=
  have : IsIso (δ hS 1 2 rfl) := isIso_δ_of_bijective_nsmul hS (n := 0) <| by
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  (asIso (δ hS 1 2 rfl)).toLinearEquiv

/-- The connecting isomorphism `H¹(C_m, T) ≃ H²(C_m, Λ)` is the connecting homomorphism. -/
@[simp]
theorem cyclicConnectingEquiv_apply (hm : Function.Bijective fun x : E ↦ m • x)
    (x : groupCohomology (AT.cyclicRep hT) 1) :
    cyclicConnectingEquiv hS hm x = δ hS 1 2 rfl x :=
  (rfl)

/-- **Naturality under homomorphisms of cyclic groups.** Suppose `χ : C_l → C_m` sends the
selected generator to its `d`-th power. Maps of exact sequences intertwining the `d`-th
iterates of the source automorphisms with the target automorphisms commute with the
connecting homomorphisms. This includes restriction, inflation, and coefficient maps. -/
theorem map_δ_cyclicRepShortComplex {l : ℕ} [NeZero l]
    {Λ' E' T' : Type} [AddCommGroup Λ'] [AddCommGroup E'] [AddCommGroup T']
    {AΛ' : Λ' ≃+ Λ'} {AE' : E' ≃+ E'} {AT' : T' ≃+ T'} {i' : Λ' →+ E'}
    {p' : E' →+ T'} {hΛ' : (⇑AΛ')^[l] = _root_.id} {hE' : (⇑AE')^[l] = _root_.id}
    {hT' : (⇑AT')^[l] = _root_.id} {hi' : ∀ x, i' (AΛ' x) = AE' (i' x)}
    {hp' : ∀ x, p' (AE' x) = AT' (p' x)} {hpi' : ∀ x, p' (i' x) = 0}
    (hS' : (i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi').ShortExact)
    (χ : Multiplicative (ZMod l) →* Multiplicative (ZMod m)) (d : ℕ)
    (hχ : χ (.ofAdd 1) = (.ofAdd 1) ^ d)
    (fΛ : Λ →+ Λ') (fE : E →+ E') (fT : T →+ T')
    (hfΛ : ∀ x, fΛ ((⇑AΛ)^[d] x) = AΛ' (fΛ x))
    (hfE : ∀ x, fE ((⇑AE)^[d] x) = AE' (fE x))
    (hfT : ∀ x, fT ((⇑AT)^[d] x) = AT' (fT x))
    (hfi : ∀ x, fE (i x) = i' (fΛ x)) (hfp : ∀ x, fT (p x) = p' (fE x))
    (n q : ℕ) (hnq : n + 1 = q) (x : groupCohomology (AT.cyclicRep hT) n) :
    map χ (fΛ.cyclicRepResHom hΛ hΛ' χ d hχ hfΛ) q (δ hS n q hnq x) =
      δ hS' n q hnq (map χ (fT.cyclicRepResHom hT hT' χ d hχ hfT) n x) := by
  let F : (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).map (resFunctor χ) ⟶
      i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi' :=
    { τ₁ := fΛ.cyclicRepResHom hΛ hΛ' χ d hχ hfΛ
      τ₂ := fE.cyclicRepResHom hE hE' χ d hχ hfE
      τ₃ := fT.cyclicRepResHom hT hT' χ d hχ hfT
      comm₁₂ := by
        ext x
        -- Extensionality exposes linear maps with restricted module instances. Express their
        -- evaluations as intertwining maps so that the characteristic evaluation lemmas match.
        change (i'.cyclicRepHom hΛ' hE' hi').hom
            ((fΛ.cyclicRepResHom hΛ hΛ' χ d hχ hfΛ).hom x) =
          (fE.cyclicRepResHom hE hE' χ d hχ hfE).hom ((i.cyclicRepHom hΛ hE hi).hom x)
        simpa only [AddMonoidHom.coe_cyclicRepResHom_hom,
          AddMonoidHom.coe_cyclicRepHom_hom] using (hfi x).symm
      comm₂₃ := by
        ext x
        -- As in the first square, use the underlying intertwining-map evaluations.
        change (p'.cyclicRepHom hE' hT' hp').hom
            ((fE.cyclicRepResHom hE hE' χ d hχ hfE).hom x) =
          (fT.cyclicRepResHom hT hT' χ d hχ hfT).hom ((p.cyclicRepHom hE hT hp).hom x)
        simpa only [AddMonoidHom.coe_cyclicRepResHom_hom,
          AddMonoidHom.coe_cyclicRepHom_hom] using (hfp x).symm }
  exact congr($(TauCeti.groupCohomology.δ_naturality χ hS hS' F n q hnq) x)

end TauCeti

/-! ### Products -/

namespace TauCeti

section Prod

variable {T M : Type} [AddCommGroup T] [AddCommGroup M] {m : ℕ} [NeZero m] {A : T ≃+ T}
  {B : M ≃+ M} (hA : (⇑A)^[m] = _root_.id) (hB : (⇑B)^[m] = _root_.id)

/-- **Degree-one classes of a product.** The identification of `H¹(C_m, T × M)` with
`H¹(C_m, T) × H¹(C_m, M)` by the projections sends the class of a norm-zero element `(t, u)` of
`T × M` to the pair of the classes of `t` and `u`. -/
theorem groupCohomologyProdEquiv_groupCohomologyπOdd_one
    (x : LinearMap.ker
      ((A.prodCongr B).cyclicRep (A.iterate_prodCongr_eq_id hA hB)).norm.asHom.hom.toLinearMap)
    (y : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap)
    (z : LinearMap.ker (B.cyclicRep hB).norm.asHom.hom.toLinearMap)
    (hy : (y : T) = (x : T × M).1) (hz : (z : M) = (x : T × M).2) :
    (AddEquiv.cyclicRepBinaryBiconeIsBilimit hA hB).groupCohomologyProdEquiv 1
        (groupCohomologyπOdd _ (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one x) =
      (groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one y,
        groupCohomologyπOdd (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one z) := by
  rw [Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply]
  apply Prod.ext
  · apply map_groupCohomologyπOdd_one (A.cyclicRep hA) (.ofAdd 1)
      mem_zpowers_ofAdd_one (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (by simp)
      (AddEquiv.cyclicRepBinaryBicone hA hB).fst x y
    simp only [Finset.sum_range_one, pow_zero, map_one,
      AddEquiv.cyclicRepBinaryBicone]
    erw [AddMonoidHom.coe_cyclicRepHom_hom]
    exact hy
  · apply map_groupCohomologyπOdd_one (B.cyclicRep hB) (.ofAdd 1)
      mem_zpowers_ofAdd_one (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (by simp)
      (AddEquiv.cyclicRepBinaryBicone hA hB).snd x z
    simp only [Finset.sum_range_one, pow_zero, map_one,
      AddEquiv.cyclicRepBinaryBicone]
    erw [AddMonoidHom.coe_cyclicRepHom_hom]
    exact hz

/-- **Degree-two classes of a product.** The identification of `H²(C_m, T × M)` with
`H²(C_m, T) × H²(C_m, M)` by the projections sends the class of a fixed point `(t, u)` of `A × B`
to the pair of the classes of `t` and `u`. -/
theorem groupCohomologyProdEquiv_groupCohomologyπEven_two
    (x : LinearMap.ker (applyAsHom ((A.prodCongr B).cyclicRep (A.iterate_prodCongr_eq_id hA hB))
      (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (y : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (z : LinearMap.ker (applyAsHom (B.cyclicRep hB) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (hy : (y : T) = (x : T × M).1) (hz : (z : M) = (x : T × M).2) :
    (AddEquiv.cyclicRepBinaryBiconeIsBilimit hA hB).groupCohomologyProdEquiv 2
        (groupCohomologyπEven _ (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two x) =
      (groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two y,
        groupCohomologyπEven (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two z) := by
  rw [Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply]
  apply Prod.ext
  · apply map_groupCohomologyπEven_two (A.cyclicRep hA) (.ofAdd 1)
      mem_zpowers_ofAdd_one (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (by simp)
      (AddEquiv.cyclicRepBinaryBicone hA hB).fst 1 (by simp) x y
    simp only [one_smul, AddEquiv.cyclicRepBinaryBicone]
    erw [AddMonoidHom.coe_cyclicRepHom_hom]
    exact hy
  · apply map_groupCohomologyπEven_two (B.cyclicRep hB) (.ofAdd 1)
      mem_zpowers_ofAdd_one (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (by simp)
      (AddEquiv.cyclicRepBinaryBicone hA hB).snd 1 (by simp) x z
    simp only [one_smul, AddEquiv.cyclicRepBinaryBicone]
    erw [AddMonoidHom.coe_cyclicRepHom_hom]
    exact hz

end Prod

section ProdShortComplex

variable {Λ E T Λ' E' T' : Type} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup T]
  [AddCommGroup Λ'] [AddCommGroup E'] [AddCommGroup T'] {m : ℕ} [NeZero m]
  {AΛ : Λ ≃+ Λ} {AE : E ≃+ E} {AT : T ≃+ T} {i : Λ →+ E} {p : E →+ T}
  {hΛ : (⇑AΛ)^[m] = _root_.id} {hE : (⇑AE)^[m] = _root_.id}
  {hT : (⇑AT)^[m] = _root_.id} {hi : ∀ x, i (AΛ x) = AE (i x)} {hp : ∀ x, p (AE x) = AT (p x)}
  {hpi : ∀ x, p (i x) = 0} (hS : (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi).ShortExact)
  {AΛ' : Λ' ≃+ Λ'} {AE' : E' ≃+ E'} {AT' : T' ≃+ T'} {i' : Λ' →+ E'} {p' : E' →+ T'}
  {hΛ' : (⇑AΛ')^[m] = _root_.id} {hE' : (⇑AE')^[m] = _root_.id}
  {hT' : (⇑AT')^[m] = _root_.id} {hi' : ∀ x, i' (AΛ' x) = AE' (i' x)}
  {hp' : ∀ x, p' (AE' x) = AT' (p' x)} {hpi' : ∀ x, p' (i' x) = 0}
  (hS' : (i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi').ShortExact)
  (hS₂ : ((i.prodMap i').cyclicRepShortComplex (p.prodMap p') (AΛ.iterate_prodCongr_eq_id hΛ hΛ')
    (AE.iterate_prodCongr_eq_id hE hE') (AT.iterate_prodCongr_eq_id hT hT')
    (fun x ↦ Prod.ext (hi x.1) (hi' x.2)) (fun x ↦ Prod.ext (hp x.1) (hp' x.2))
    (fun x ↦ Prod.ext (hpi x.1) (hpi' x.2))).ShortExact)

/-- Naturality of the connecting homomorphism of the product sequence along the first
projection. -/
private theorem map_fst_δ_cyclicRepShortComplex_prodMap (n q : ℕ) (hnq : n + 1 = q)
    (x : groupCohomology ((AT.prodCongr AT').cyclicRep (AT.iterate_prodCongr_eq_id hT hT')) n)
    (hi₂ : ∀ x, (i.prodMap i') ((AΛ.prodCongr AΛ') x) =
      (AE.prodCongr AE') ((i.prodMap i') x))
    (hp₂ : ∀ x, (p.prodMap p') ((AE.prodCongr AE') x) =
      (AT.prodCongr AT') ((p.prodMap p') x))
    (hpi₂ : ∀ x, (p.prodMap p') ((i.prodMap i') x) = 0) :
    map (MonoidHom.id _) (AddEquiv.cyclicRepBinaryBicone hΛ hΛ').fst q (δ hS₂ n q hnq x) =
      δ hS n q hnq (map (MonoidHom.id _) (AddEquiv.cyclicRepBinaryBicone hT hT').fst n x) := by
  let F : ((i.prodMap i').cyclicRepShortComplex (p.prodMap p')
    (AΛ.iterate_prodCongr_eq_id hΛ hΛ') (AE.iterate_prodCongr_eq_id hE hE')
    (AT.iterate_prodCongr_eq_id hT hT') hi₂ hp₂ hpi₂) ⟶
      (i.cyclicRepShortComplex p hΛ hE hT hi hp hpi) :=
    { τ₁ := (AddEquiv.cyclicRepBinaryBicone hΛ hΛ').fst
      τ₂ := (AddEquiv.cyclicRepBinaryBicone hE hE').fst
      τ₃ := (AddEquiv.cyclicRepBinaryBicone hT hT').fst
      comm₁₂ := by
        dsimp only [AddEquiv.cyclicRepBinaryBicone, AddMonoidHom.cyclicRepShortComplex]
        erw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
        rfl
      comm₂₃ := by
        dsimp only [AddEquiv.cyclicRepBinaryBicone, AddMonoidHom.cyclicRepShortComplex]
        erw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
        rfl }
  exact congr($(_root_.groupCohomology.δ_naturality hS₂ hS F n q hnq) x)

/-- Naturality of the connecting homomorphism of the product sequence along the second
projection. -/
private theorem map_snd_δ_cyclicRepShortComplex_prodMap (n q : ℕ) (hnq : n + 1 = q)
    (x : groupCohomology ((AT.prodCongr AT').cyclicRep (AT.iterate_prodCongr_eq_id hT hT')) n)
    (hi₂ : ∀ x, (i.prodMap i') ((AΛ.prodCongr AΛ') x) =
      (AE.prodCongr AE') ((i.prodMap i') x))
    (hp₂ : ∀ x, (p.prodMap p') ((AE.prodCongr AE') x) =
      (AT.prodCongr AT') ((p.prodMap p') x))
    (hpi₂ : ∀ x, (p.prodMap p') ((i.prodMap i') x) = 0) :
    map (MonoidHom.id _) (AddEquiv.cyclicRepBinaryBicone hΛ hΛ').snd q (δ hS₂ n q hnq x) =
      δ hS' n q hnq (map (MonoidHom.id _) (AddEquiv.cyclicRepBinaryBicone hT hT').snd n x) := by
  let F : ((i.prodMap i').cyclicRepShortComplex (p.prodMap p')
    (AΛ.iterate_prodCongr_eq_id hΛ hΛ') (AE.iterate_prodCongr_eq_id hE hE')
    (AT.iterate_prodCongr_eq_id hT hT') hi₂ hp₂ hpi₂) ⟶
      (i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi') :=
    { τ₁ := (AddEquiv.cyclicRepBinaryBicone hΛ hΛ').snd
      τ₂ := (AddEquiv.cyclicRepBinaryBicone hE hE').snd
      τ₃ := (AddEquiv.cyclicRepBinaryBicone hT hT').snd
      comm₁₂ := by
        dsimp only [AddEquiv.cyclicRepBinaryBicone, AddMonoidHom.cyclicRepShortComplex]
        erw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
        rfl
      comm₂₃ := by
        dsimp only [AddEquiv.cyclicRepBinaryBicone, AddMonoidHom.cyclicRepShortComplex]
        erw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
        rfl }
  exact congr($(_root_.groupCohomology.δ_naturality hS₂ hS' F n q hnq) x)

/-- **The connecting homomorphism of a product.** For equivariant exact sequences
`0 → Λ → E → T → 0` and `0 → Λ' → E' → T' → 0`, the connecting homomorphism
`Hⁿ(C_m, T × T') ⟶ H^q(C_m, Λ × Λ')` of the product sequence (short exact by
`AddMonoidHom.shortExact_cyclicRepShortComplex_prodMap`) is the product of the two connecting
homomorphisms, once the cohomology of each product is identified with the product of the
cohomologies by the projections. -/
theorem groupCohomologyProdEquiv_δ_cyclicRepShortComplex_prodMap (n q : ℕ) (hnq : n + 1 = q)
    (x : groupCohomology ((AT.prodCongr AT').cyclicRep (AT.iterate_prodCongr_eq_id hT hT')) n) :
    (AddEquiv.cyclicRepBinaryBiconeIsBilimit hΛ hΛ').groupCohomologyProdEquiv q
        (δ hS₂ n q hnq x) =
      Prod.map (δ hS n q hnq) (δ hS' n q hnq)
        ((AddEquiv.cyclicRepBinaryBiconeIsBilimit hT hT').groupCohomologyProdEquiv n x) := by
  have hi₂ : ∀ x, (i.prodMap i') ((AΛ.prodCongr AΛ') x) =
      (AE.prodCongr AE') ((i.prodMap i') x) := fun x ↦ Prod.ext (hi x.1) (hi' x.2)
  have hp₂ : ∀ x, (p.prodMap p') ((AE.prodCongr AE') x) =
      (AT.prodCongr AT') ((p.prodMap p') x) := fun x ↦ Prod.ext (hp x.1) (hp' x.2)
  have hpi₂ : ∀ x, (p.prodMap p') ((i.prodMap i') x) = 0 :=
    fun x ↦ Prod.ext (hpi x.1) (hpi' x.2)
  -- Each component is the naturality of the connecting homomorphism along a projection.
  have h₁ := map_fst_δ_cyclicRepShortComplex_prodMap (hΛ' := hΛ') (hE' := hE') (hT' := hT')
    (hi' := hi') (hp' := hp') (hpi' := hpi') hS hS₂ n q hnq x hi₂ hp₂ hpi₂
  have h₂ := map_snd_δ_cyclicRepShortComplex_prodMap (hΛ := hΛ) (hE := hE) (hT := hT)
    (hi := hi) (hp := hp) (hpi := hpi) hS' hS₂ n q hnq x hi₂ hp₂ hpi₂
  exact Prod.ext
    ((Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply_fst _ q _).trans <| h₁.trans <|
      congrArg (δ hS n q hnq) (Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply_fst
        (AddEquiv.cyclicRepBinaryBiconeIsBilimit hT hT') n x).symm)
    ((Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply_snd _ q _).trans <| h₂.trans <|
      congrArg (δ hS' n q hnq) (Limits.BinaryBicone.IsBilimit.groupCohomologyProdEquiv_apply_snd
        (AddEquiv.cyclicRepBinaryBiconeIsBilimit hT hT') n x).symm)

/-- **The connecting isomorphism of a product.** When multiplication by `m` is bijective on `E`
and on `E'`, the connecting isomorphism `H¹(C_m, T × T') ≃ H²(C_m, Λ × Λ')` of the product
sequence is the product of the connecting isomorphisms `H¹(C_m, T) ≃ H²(C_m, Λ)` and
`H¹(C_m, T') ≃ H²(C_m, Λ')`, once the cohomology of each product is identified with the product of
the cohomologies by the projections. -/
theorem groupCohomologyProdEquiv_cyclicConnectingEquiv (hm : Function.Bijective fun x : E ↦ m • x)
    (hm' : Function.Bijective fun x : E' ↦ m • x)
    (x : groupCohomology ((AT.prodCongr AT').cyclicRep (AT.iterate_prodCongr_eq_id hT hT')) 1) :
    (AddEquiv.cyclicRepBinaryBiconeIsBilimit hΛ hΛ').groupCohomologyProdEquiv 2
        (cyclicConnectingEquiv hS₂ (hm.prodMap hm') x) =
      Prod.map (cyclicConnectingEquiv hS hm) (cyclicConnectingEquiv hS' hm')
        ((AddEquiv.cyclicRepBinaryBiconeIsBilimit hT hT').groupCohomologyProdEquiv 1 x) := by
  rw [cyclicConnectingEquiv_apply,
    groupCohomologyProdEquiv_δ_cyclicRepShortComplex_prodMap hS hS' hS₂ 1 2 rfl x]
  exact Prod.ext (cyclicConnectingEquiv_apply hS hm _).symm
    (cyclicConnectingEquiv_apply hS' hm' _).symm

end ProdShortComplex

end TauCeti

/-! ### Trivial actions -/

namespace TauCeti

open scoped Pointwise

section Trivial

variable (T : Type) [AddCommGroup T] (m : ℕ) [NeZero m]

/-- **Odd-degree cohomology of the trivial action.** When `C_m` acts trivially on `T`, its
cohomology in odd degree is the `m`-torsion `T[m]`: the class of a norm-zero element `x`
corresponds to `x` itself. -/
noncomputable def groupCohomologyOddEquivTorsionBy (i : ℕ) (hi : Odd i) :
    groupCohomology ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) i ≃ₗ[ℤ]
      Submodule.torsionBy ℤ T m :=
  let ι := (Submodule.torsionBy ℤ T m).subtype.codRestrict _ fun x ↦
    (AddEquiv.mem_ker_cyclicRep_refl_norm_iff _).2 x.2
  (LinearEquiv.ofBijective ((groupCohomologyπOdd ((AddEquiv.refl T).cyclicRep
      (AddEquiv.iterate_refl m)) (.ofAdd 1) mem_zpowers_ofAdd_one i hi).hom ∘ₗ ι)
    ⟨fun x y h ↦ by
      simp only [LinearMap.comp_apply] at h
      rw [groupCohomologyπOdd_eq_iff, AddEquiv.mem_range_cyclicRep_refl_applyAsHom_sub_iff] at h
      simpa [ι, sub_eq_zero] using h,
    fun c ↦ by
      obtain ⟨x, rfl⟩ := groupCohomologyπOdd_surjective _ _ mem_zpowers_ofAdd_one i hi c
      -- `ι` sends `⟨x, _⟩` to `x`.
      exact ⟨⟨x, (AddEquiv.mem_ker_cyclicRep_refl_norm_iff _).1 x.2⟩, rfl⟩⟩).symm

/-- The odd-degree class corresponding to `x : T[m]` is the class of `x`. -/
theorem groupCohomologyOddEquivTorsionBy_symm_apply (i : ℕ) (hi : Odd i)
    (x : Submodule.torsionBy ℤ T m) :
    (groupCohomologyOddEquivTorsionBy T m i hi).symm x =
      groupCohomologyπOdd ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) (.ofAdd 1)
        mem_zpowers_ofAdd_one i hi ⟨x, (AddEquiv.mem_ker_cyclicRep_refl_norm_iff _).2 x.2⟩ :=
  (rfl)

/-- The odd-degree class of a norm-zero element `x` corresponds to `x` in `T[m]`. -/
theorem groupCohomologyOddEquivTorsionBy_groupCohomologyπOdd (i : ℕ) (hi : Odd i)
    (x : LinearMap.ker
      ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)).norm.asHom.hom.toLinearMap) :
    groupCohomologyOddEquivTorsionBy T m i hi
      (groupCohomologyπOdd ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) (.ofAdd 1)
        mem_zpowers_ofAdd_one i hi x) =
      ⟨x, (AddEquiv.mem_ker_cyclicRep_refl_norm_iff _).1 x.2⟩ := by
  rw [← LinearEquiv.eq_symm_apply, groupCohomologyOddEquivTorsionBy_symm_apply]

/-- **Even-degree cohomology of the trivial action.** When `C_m` acts trivially on `T`, its
cohomology in positive even degree is `T ⧸ m T`: the class of `x` corresponds to the coset of
`x`. -/
noncomputable def groupCohomologyEvenEquivQuotSMulTop (i : ℕ) [NeZero i] (hi : Even i) :
    groupCohomology ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) i ≃ₗ[ℤ]
      QuotSMulTop (m : ℤ) T :=
  let ι := (LinearMap.id : T →ₗ[ℤ] T).codRestrict _
    (AddEquiv.mem_ker_cyclicRep_refl_applyAsHom_sub (m := m))
  let φ := (groupCohomologyπEven ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m))
    (.ofAdd 1) mem_zpowers_ofAdd_one i hi).hom ∘ₗ ι
  have hφ : Function.Surjective φ := fun c ↦ by
    obtain ⟨x, rfl⟩ := groupCohomologyπEven_surjective _ _ mem_zpowers_ofAdd_one i hi c
    -- `ι` sends `x` to `⟨x, _⟩`.
    exact ⟨x, rfl⟩
  have hker : LinearMap.ker φ = (m : ℤ) • (⊤ : Submodule ℤ T) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.comp_apply, groupCohomologyπEven_eq_zero_iff,
      AddEquiv.mem_range_cyclicRep_refl_norm_iff]
    simp [ι, Submodule.mem_smul_pointwise_iff_exists]
  ((Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hφ)).symm

/-- The even-degree class corresponding to the coset of `x` is the class of `x`. -/
theorem groupCohomologyEvenEquivQuotSMulTop_symm_mk (i : ℕ) [NeZero i] (hi : Even i) (x : T) :
    (groupCohomologyEvenEquivQuotSMulTop T m i hi).symm (Submodule.Quotient.mk x) =
      groupCohomologyπEven ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) (.ofAdd 1)
        mem_zpowers_ofAdd_one i hi ⟨x, AddEquiv.mem_ker_cyclicRep_refl_applyAsHom_sub x⟩ :=
  -- Each step holds by `rfl` in Mathlib: `LinearEquiv.symm_symm`, `Submodule.quotEquivOfEq_mk`
  -- and `LinearMap.quotKerEquivOfSurjective_apply_mk`. Rewriting with them is not possible here:
  -- once the definition is unfolded, the goal is not type-correct at implicit transparency.
  (rfl)

/-- The even-degree class of `x` corresponds to the coset of `x` in `T ⧸ m T`. -/
theorem groupCohomologyEvenEquivQuotSMulTop_groupCohomologyπEven (i : ℕ) [NeZero i]
    (hi : Even i)
    (x : LinearMap.ker (applyAsHom ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m))
      (.ofAdd 1) - 𝟙 _).hom.toLinearMap) :
    groupCohomologyEvenEquivQuotSMulTop T m i hi
      (groupCohomologyπEven ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) (.ofAdd 1)
        mem_zpowers_ofAdd_one i hi x) = Submodule.Quotient.mk (x : T) := by
  have hx : (groupCohomologyEvenEquivQuotSMulTop T m i hi).symm (Submodule.Quotient.mk x) =
      groupCohomologyπEven ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) (.ofAdd 1)
        mem_zpowers_ofAdd_one i hi x := by
    rw [groupCohomologyEvenEquivQuotSMulTop_symm_mk]
  rw [← hx, LinearEquiv.apply_symm_apply]

end Trivial

section TrivialConnecting

variable {Λ E T : Type} [AddCommGroup Λ] [AddCommGroup E] [AddCommGroup T] {m : ℕ} [NeZero m]
  {i : Λ →ₗ[ℤ] E} {p : E →ₗ[ℤ] T}
  (hinj : Function.Injective i) (hexact : Function.Exact i p) (hsurj : Function.Surjective p)

/-- **The connecting map of trivial actions is the snake map.** For the trivial actions of `C_m`
on an exact sequence `0 → Λ → E → T → 0`, identify `H¹(C_m, T)` with `T[m]` and `H²(C_m, Λ)`
with `Λ ⧸ m Λ`. Then the connecting homomorphism `δ` becomes the snake-lemma connecting map
`TauCeti.torsionByδ`, which sends `t` to the coset of `v` when `m • s = i v` for a lift `s` of
`t`. -/
theorem groupCohomologyEvenEquivQuotSMulTop_δ
    (x : groupCohomology ((AddEquiv.refl T).cyclicRep (AddEquiv.iterate_refl m)) 1) :
    groupCohomologyEvenEquivQuotSMulTop Λ m 2 even_two
        (δ (i.toAddMonoidHom.shortExact_cyclicRepShortComplex p.toAddMonoidHom
          (hE := AddEquiv.iterate_refl m) (hi := by simp) (hp := by simp)
          (hpi := by simpa using hexact.apply_apply_eq_zero) hinj hexact hsurj) 1 2 rfl x) =
      torsionByδ (m : ℤ) hexact hinj hsurj (groupCohomologyOddEquivTorsionBy T m 1 odd_one x) := by
  -- Write `x` as the class of `t ∈ T[m]`, lift `t` to `s : E` and write `m • s = i v`.
  obtain ⟨t, rfl⟩ := (groupCohomologyOddEquivTorsionBy T m 1 odd_one).symm.surjective x
  obtain ⟨s, hs⟩ := hsurj t
  obtain ⟨v, hv⟩ := (hexact (m • s)).1 <| by
    rw [map_nsmul, hs, ← natCast_zsmul]
    exact (Submodule.mem_torsionBy_iff _ _).1 t.2
  -- `δ` sends the class of `t` to the class of `v`, and so does the snake map.
  have hδ := δ_cyclicRepShortComplex_groupCohomologyπOdd_one
    (i.toAddMonoidHom.shortExact_cyclicRepShortComplex p.toAddMonoidHom
      (hΛ := AddEquiv.iterate_refl m) (hE := AddEquiv.iterate_refl m)
      (hT := AddEquiv.iterate_refl m) (hi := by simp) (hp := by simp)
      (hpi := by simpa using hexact.apply_apply_eq_zero) hinj hexact hsurj)
    ⟨t, (AddEquiv.mem_ker_cyclicRep_refl_norm_iff _).2 t.2⟩ s (by simpa using hs)
    ⟨v, AddEquiv.mem_ker_cyclicRep_refl_applyAsHom_sub v⟩ (by simp [hv])
  rw [LinearEquiv.apply_symm_apply, groupCohomologyOddEquivTorsionBy_symm_apply, hδ,
    groupCohomologyEvenEquivQuotSMulTop_groupCohomologyπEven,
    torsionByδ_eq hexact hinj hsurj t hs (by rw [hv, natCast_zsmul])]

/-- **`T[m] ≃ Λ ⧸ m Λ` is the connecting isomorphism.** When multiplication by `m` is bijective on
`E`, the snake-lemma isomorphism `T[m] ≃ Λ ⧸ m Λ` is the connecting isomorphism
`H¹(C_m, T) ≃ H²(C_m, Λ)` of the trivial actions, read through `H¹(C_m, T) ≃ T[m]` and
`H²(C_m, Λ) ≃ Λ ⧸ m Λ`. -/
theorem torsionByδEquiv_eq_trans_cyclicConnectingEquiv
    (hm : Function.Bijective fun x : E ↦ m • x) :
    torsionByδEquiv (m : ℤ) hexact hinj hsurj (by simpa only [natCast_zsmul] using hm) =
      ((groupCohomologyOddEquivTorsionBy T m 1 odd_one).symm.trans
        (cyclicConnectingEquiv (i.toAddMonoidHom.shortExact_cyclicRepShortComplex
          p.toAddMonoidHom (hE := AddEquiv.iterate_refl m) (hi := by simp)
          (hp := by simp) (hpi := by simpa using hexact.apply_apply_eq_zero) hinj hexact hsurj)
          hm)).trans (groupCohomologyEvenEquivQuotSMulTop Λ m 2 even_two) :=
  LinearEquiv.ext fun t ↦ by
    simp [groupCohomologyEvenEquivQuotSMulTop_δ hinj hexact hsurj]

end TrivialConnecting

end TauCeti
