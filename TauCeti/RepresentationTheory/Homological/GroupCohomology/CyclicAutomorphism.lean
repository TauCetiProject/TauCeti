/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Cyclic.Automorphism
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.Corestriction
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.Tactic.Abel

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
  changes `t` to `t + (b - A b)`.
* In positive even degree, the classes are the fixed points of `A`, two of them having the same
  class exactly when they differ by a norm `∑ j < m, A^j y`
  (`AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`).

Every class arises in each case (`Rep.FiniteCyclicGroup.groupCohomologyπOdd_surjective`,
`Rep.FiniteCyclicGroup.groupCohomologyπEven_surjective`). An additive map `f` with
`f ∘ A = B ∘ f` acts on these classes through representatives: in degree one it sends the class
of `t` to the class of `f t`, and in degree two the class of a fixed point `v` to the class of
`f v` (`AddMonoidHom.map_cyclicRepHom_groupCohomologyπOdd_one`,
`AddMonoidHom.map_cyclicRepHom_groupCohomologyπEven_two`).

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
is natural: maps between two such sequences which intertwine the automorphisms and commute with
the maps of the sequences commute with `δ` (`TauCeti.map_δ_cyclicRepShortComplex`).

## Main definitions

* `AddMonoidHom.cyclicRepShortComplex`: the short complex `Λ ⟶ E ⟶ T` of cyclic
  representations.
* `TauCeti.cyclicConnectingEquiv`: the connecting isomorphism `H¹(C_m, T) ≃ H²(C_m, Λ)`
  when multiplication by `m` is bijective on `E`.

## Main results

* `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπOdd_cyclicRep_eq_iff`: odd-degree classes are norm-zero elements
  modulo the image of `1 - A`.
* `AddEquiv.groupCohomologyπEven_cyclicRep_eq_zero_iff`,
  `AddEquiv.groupCohomologyπEven_cyclicRep_eq_iff`: positive even-degree classes are fixed points
  of `A` modulo the image of the norm.
* `AddMonoidHom.map_cyclicRepHom_groupCohomologyπOdd_one`,
  `AddMonoidHom.map_cyclicRepHom_groupCohomologyπEven_two`: an equivariant map acts on degree-`1`
  and degree-`2` classes by acting on their representatives.
* `AddMonoidHom.shortExact_cyclicRepShortComplex`: an exact sequence of abelian groups with
  equivariant maps is a short exact sequence of cyclic representations.
* `TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one`,
  `TauCeti.δ_cyclicRepShortComplex_groupCohomologyπOdd_one_of_nsmul_eq`: the connecting
  homomorphism sends the class of `t` to the class of the norm of a lift of `t`, and the class of
  `v / m` to the class of `v`.
* `TauCeti.map_δ_cyclicRepShortComplex`: naturality of the connecting homomorphism under maps of
  equivariant exact sequences.

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

section CohomologyMap

variable {T M : Type} [AddCommGroup T] [AddCommGroup M] {m : ℕ} [NeZero m] {A : T ≃+ T}
  {B : M ≃+ M} (f : T →+ M) (hA : (⇑A)^[m] = _root_.id) (hB : (⇑B)^[m] = _root_.id)
  (hf : ∀ x, f (A x) = B (f x))

/-- An additive map `f` with `f ∘ A = B ∘ f` sends the degree-`1` class of a norm-zero element
`x` to the degree-`1` class of `f x`. -/
theorem map_cyclicRepHom_groupCohomologyπOdd_one
    (x : LinearMap.ker (A.cyclicRep hA).norm.asHom.hom.toLinearMap)
    (y : LinearMap.ker (B.cyclicRep hB).norm.asHom.hom.toLinearMap) (hy : (y : M) = f x) :
    groupCohomology.map (MonoidHom.id (Multiplicative (ZMod m))) (f.cyclicRepHom hA hB hf) 1
        (groupCohomologyπOdd (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one x) =
      groupCohomologyπOdd (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 1 odd_one y := by
  -- Specializing before unifying with the goal: unifying the general statement directly against
  -- the goal, where `res (MonoidHom.id _)` meets the cyclic representations, is very slow.
  have h := map_groupCohomologyπOdd_one (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one
    (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (pow_one _).symm (f.cyclicRepHom hA hB hf) x y
  refine h ?_
  rw [Finset.sum_range_one, pow_zero, map_one, Module.End.one_apply, hy]
  exact (congrFun (coe_cyclicRepHom_hom f hA hB hf) x.1).symm

/-- An additive map `f` with `f ∘ A = B ∘ f` sends the degree-`2` class of a fixed point `x` of
`A` to the degree-`2` class of the fixed point `f x` of `B`. -/
theorem map_cyclicRepHom_groupCohomologyπEven_two
    (x : LinearMap.ker (applyAsHom (A.cyclicRep hA) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (y : LinearMap.ker (applyAsHom (B.cyclicRep hB) (.ofAdd 1) - 𝟙 _).hom.toLinearMap)
    (hy : (y : M) = f x) :
    groupCohomology.map (MonoidHom.id (Multiplicative (ZMod m))) (f.cyclicRepHom hA hB hf) 2
        (groupCohomologyπEven (A.cyclicRep hA) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two x) =
      groupCohomologyπEven (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one 2 even_two y := by
  -- Specializing before unifying with the goal: unifying the general statement directly against
  -- the goal, where `res (MonoidHom.id _)` meets the cyclic representations, is very slow.
  have h := map_groupCohomologyπEven_two (B.cyclicRep hB) (.ofAdd 1) mem_zpowers_ofAdd_one
    (MonoidHom.id _) mem_zpowers_ofAdd_one 1 (pow_one _).symm (f.cyclicRepHom hA hB hf) 1 rfl x y
  refine h ?_
  rw [one_nsmul, hy]
  exact (congrFun (coe_cyclicRepHom_hom f hA hB hf) x.1).symm

end CohomologyMap

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

/-- **Naturality of the connecting homomorphism.** Let `fΛ`, `fE`, `fT` be additive maps from
an exact sequence `0 → Λ → E → T → 0` with automorphisms `AΛ`, `AE`, `AT` to another one
`0 → Λ' → E' → T' → 0` with automorphisms `AΛ'`, `AE'`, `AT'`, intertwining the automorphisms and
commuting with the maps of the two sequences. Then for `q = n + 1` the connecting homomorphisms
`Hⁿ(C_m, T) ⟶ H^q(C_m, Λ)` and `Hⁿ(C_m, T') ⟶ H^q(C_m, Λ')` commute with the maps induced by
`fT` and `fΛ`. -/
theorem map_δ_cyclicRepShortComplex {Λ' E' T' : Type} [AddCommGroup Λ'] [AddCommGroup E']
    [AddCommGroup T'] {AΛ' : Λ' ≃+ Λ'} {AE' : E' ≃+ E'} {AT' : T' ≃+ T'} {i' : Λ' →+ E'}
    {p' : E' →+ T'} {hΛ' : (⇑AΛ')^[m] = _root_.id} {hE' : (⇑AE')^[m] = _root_.id}
    {hT' : (⇑AT')^[m] = _root_.id} {hi' : ∀ x, i' (AΛ' x) = AE' (i' x)}
    {hp' : ∀ x, p' (AE' x) = AT' (p' x)} {hpi' : ∀ x, p' (i' x) = 0}
    (hS' : (i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi').ShortExact)
    (fΛ : Λ →+ Λ') (fE : E →+ E') (fT : T →+ T') (hfΛ : ∀ x, fΛ (AΛ x) = AΛ' (fΛ x))
    (hfE : ∀ x, fE (AE x) = AE' (fE x)) (hfT : ∀ x, fT (AT x) = AT' (fT x))
    (hfi : ∀ x, fE (i x) = i' (fΛ x)) (hfp : ∀ x, fT (p x) = p' (fE x))
    (n q : ℕ) (hnq : n + 1 = q) (x : groupCohomology (AT.cyclicRep hT) n) :
    map (MonoidHom.id (Multiplicative (ZMod m))) (fΛ.cyclicRepHom hΛ hΛ' hfΛ) q
        (δ hS n q hnq x) =
      δ hS' n q hnq
        (map (MonoidHom.id (Multiplicative (ZMod m))) (fT.cyclicRepHom hT hT' hfT) n x) := by
  -- The squares of the morphism of short complexes, since `i' ∘ fΛ = fE ∘ i` and
  -- `p' ∘ fE = fT ∘ p`.
  have h₁₂ : fΛ.cyclicRepHom hΛ hΛ' hfΛ ≫ i'.cyclicRepHom hΛ' hE' hi' =
      i.cyclicRepHom hΛ hE hi ≫ fE.cyclicRepHom hE hE' hfE := by
    rw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
    congr 1
    exact AddMonoidHom.ext fun x ↦ (hfi x).symm
  have h₂₃ : fE.cyclicRepHom hE hE' hfE ≫ p'.cyclicRepHom hE' hT' hp' =
      p.cyclicRepHom hE hT hp ≫ fT.cyclicRepHom hT hT' hfT := by
    rw [← AddMonoidHom.cyclicRepHom_comp, ← AddMonoidHom.cyclicRepHom_comp]
    congr 1
    exact AddMonoidHom.ext fun x ↦ (hfp x).symm
  let F : i.cyclicRepShortComplex p hΛ hE hT hi hp hpi ⟶
      i'.cyclicRepShortComplex p' hΛ' hE' hT' hi' hp' hpi' :=
    { τ₁ := fΛ.cyclicRepHom hΛ hΛ' hfΛ
      τ₂ := fE.cyclicRepHom hE hE' hfE
      τ₃ := fT.cyclicRepHom hT hT' hfT
      comm₁₂ := h₁₂
      comm₂₃ := h₂₃ }
  exact congr($(δ_naturality hS hS' F n q hnq) x)

end TauCeti
