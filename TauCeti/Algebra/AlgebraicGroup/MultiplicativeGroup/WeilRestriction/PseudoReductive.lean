/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Separable
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.FieldTheory.PurelyInseparable.BaseChange
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Connected
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.CharP
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.NoCharacters
import TauCeti.Algebra.AlgebraicGroup.Torus.Recognition
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Reductive.Basic
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The Weil restriction of `𝔾ₘ` along a field extension

For any finite field extension `K / k` in arbitrary characteristic, the Weil restriction
`Res_{K/k} 𝔾ₘ` is pseudo-reductive; when `K / k` is nontrivial and purely inseparable, it is the
standard example of a commutative pseudo-reductive group which is not reductive.

**Not reductive.** In characteristic `p > 0`, let `B` be a finite-dimensional commutative
`k`-algebra and `k'` an algebraic closure of `k`. The `k'`-points of `Res_{B/k} 𝔾ₘ` are the units of
`B ⊗[k] k'`. If this ring has a nonzero nilpotent element `n`, then `1 + n` is a nonidentity point
of `p`-power order, hence a nonidentity unipotent point. A commutative reductive group is a torus,
all of whose geometric points are semisimple, and a point which is both semisimple and unipotent is
the identity. Hence `Res_{B/k} 𝔾ₘ` is not reductive unless `B ⊗[k] k'` is reduced. For a nontrivial
finite purely inseparable extension `K / k` (which forces positive characteristic), `K ⊗[k] k'` is a
local ring with nonzero nilpotent maximal ideal
(`TauCeti.IsPurelyInseparable.not_isReduced_tensorProduct`).

**Pseudo-reductive.** For every finite field extension `K / k` in any characteristic, homomorphisms
from a smooth unipotent group `U` to `Res_{K/k} 𝔾ₘ` are trivial. By the defining adjunction of the
Weil restriction such a homomorphism is a group-like element `v` of `K ⊗[k] U`, a character of `U_K`
over `K`. Embedding `K` into an algebraic closure `k'` of `k`, every `k'`-point of `U_K` comes from
a geometric point of `U` and is therefore unipotent
(`TauCeti.HopfAlgebra.IsUnipotentPoint.baseChangePointsMulEquiv`), while `K ⊗[k] U` is reduced by
smoothness, so `v = 1` (`TauCeti.groupLike_eq_one_of_forall_isUnipotentPoint`). In particular the
unipotent radical of `Res_{K/k} 𝔾ₘ` over `k` is trivial, while smoothness and geometric
connectedness are `TauCeti.Algebra.WeilRestriction.instSmooth` and
`TauCeti.Algebra.WeilRestriction.geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup`.

Consequently, when `K / k` is nontrivial and purely inseparable, the geometric unipotent radical of
`Res_{K/k} 𝔾ₘ` over `AlgebraicClosure k` does not descend to `k`, and
`(Res_{K/k} 𝔾ₘ)_{AlgebraicClosure k}` is not pseudo-reductive, showing that separability cannot be
dropped from `TauCeti.pseudoReductiveCommHopfAlgProperty.baseChange`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.isReduced_tensorProduct_of_reductive_multiplicativeGroup`: in
  characteristic `p > 0`, if `Res_{B/k} 𝔾ₘ` is reductive then `B ⊗[k] AlgebraicClosure k` is
  reduced.
* `TauCeti.Algebra.WeilRestriction.not_reductive_multiplicativeGroup_of_isPurelyInseparable`: for
  a nontrivial finite purely inseparable extension `K / k`, `Res_{K/k} 𝔾ₘ` is not reductive.
* `TauCeti.Algebra.WeilRestriction.toConv_eq_one_of_geometricallyUnipotentPoints`: for any finite
  field extension `K / k`, every homomorphism from a smooth unipotent group to `Res_{K/k} 𝔾ₘ` is
  trivial.
* `TauCeti.Algebra.WeilRestriction.pseudoReductive_multiplicativeGroup`: in
  characteristic `p > 0`, `Res_{K/k} 𝔾ₘ` is pseudo-reductive for every finite field extension
  `K / k`.
* `WeilRestriction.not_pseudoReductive_baseChange_multiplicativeGroup_of_isPurelyInseparable`: for
  a nontrivial finite purely inseparable extension `K / k`, the geometric fibre of `Res_{K/k} 𝔾ₘ`
  over `AlgebraicClosure k` is not pseudo-reductive, showing that pseudo-reductivity need not
  survive inseparable field extensions.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Example 1.1.3 and
  Proposition 1.1.10.
* J. S. Milne, *Algebraic Groups* (2017), §§2.i, 6.47–6.48, and 19.b.
-/

public section

open WithConv
open scoped LaurentPolynomial TensorProduct

namespace TauCeti.Algebra.WeilRestriction

universe u

variable {k : Type u} [Field k]

/-- **A reductive Weil restriction of `𝔾ₘ` has reduced geometric fibre algebra.** Over a field `k`
of characteristic `p > 0`, if `Res_{B/k} 𝔾ₘ` is reductive for a finite-dimensional commutative
`k`-algebra `B`, then `B ⊗[k] AlgebraicClosure k` is reduced. -/
theorem isReduced_tensorProduct_of_reductive_multiplicativeGroup (p : ℕ) [Fact p.Prime]
    [CharP k p] {B : Type u} [CommRing B] [Algebra k B] [FiniteDimensional k B]
    (hB : reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (WeilRestriction k B B[T;T⁻¹]))) :
    IsReduced (B ⊗[k] AlgebraicClosure k) := by
  let k' := AlgebraicClosure k
  refine ⟨fun n hn ↦ by_contra fun hn0 ↦ ?_⟩
  -- The point `1 + n` of `Res_{B/k} 𝔾ₘ` has `p`-power order.
  let _ : Nontrivial (B ⊗[k] k') := ⟨⟨n, 0, hn0⟩⟩
  let _ : CharP (B ⊗[k] k') p := charP_of_injective_algebraMap (algebraMap k _).injective p
  obtain ⟨m, hm⟩ := id hn
  let u := hn.isUnit_one_add.unit
  have hu : u ^ p ^ m = 1 := Units.ext <| by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, add_pow_char_pow, one_pow,
      pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hm, add_zero,
      Units.val_one]
  let g := (multiplicativeGroupPoints k B k').symm u
  have hg : g ^ p ^ m = 1 :=
    (map_pow (multiplicativeGroupPoints k B k').symm u (p ^ m)).symm.trans (by rw [hu, map_one])
  have hg1 : g ≠ 1 := fun h ↦ hn0 <| by
    have := congrArg (fun g ↦ (multiplicativeGroupPoints k B k' g : B ⊗[k] k')) h
    simpa [g, u] using this
  -- A commutative reductive group is a torus, so its geometric points are semisimple.
  have htorus := hB.torus_of_geometricallySolvable
    (geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm k _)
  have hss := ((torusCommHopfAlgProperty_iff_isCocomm_and_geometricallySemisimplePoints _
    geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup).1 htorus).2
  rw [geometricallySemisimplePointsCommHopfAlgProperty_iff] at hss
  exact hg1 ((hss g).eq_one_of_isUnipotent
    (HopfAlgebra.isUnipotentPoint_of_pow_char_pow_eq_one p hg))

/-- **`Res_{K/k} 𝔾ₘ` is not reductive** for a nontrivial finite purely inseparable extension
`K / k`, over a field `k` of any characteristic. -/
theorem not_reductive_multiplicativeGroup_of_isPurelyInseparable {K : Type u} [Field K]
    [Algebra k K] [FiniteDimensional k K] [IsPurelyInseparable k K]
    (hK : 1 < Module.finrank k K) :
    ¬ reductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])) := by
  intro hred
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    have : Nonempty (K →ₐ[k] AlgebraicClosure k) := ⟨IsAlgClosed.lift⟩
    have hreduced := isReduced_tensorProduct_of_reductive_multiplicativeGroup p hred
    exact TauCeti.IsPurelyInseparable.not_isReduced_tensorProduct k K (AlgebraicClosure k) hK
      (isReduced_of_injective _ (Algebra.TensorProduct.comm k _ K).injective)
  · -- In characteristic zero a purely inseparable extension is trivial.
    have : CharZero k := CharP.charP_to_charZero k
    have hbij := IsPurelyInseparable.bijective_algebraMap_of_isSeparable k K
    have := (LinearEquiv.ofBijective (Algebra.linearMap k K) hbij).finrank_eq
    rw [Module.finrank_self] at this
    omega

/-- **Every homomorphism from a smooth unipotent group to `Res_{K/k} 𝔾ₘ` is trivial**, for every
finite field extension `K / k` in any characteristic. A bialgebra map from the coordinate Hopf
algebra of `Res_{K/k} 𝔾ₘ` to that of a smooth affine group `U` of finite type whose geometric
points are unipotent is the identity point `algebraMap k U ∘ counit` of `Res_{K/k} 𝔾ₘ` over `U`. -/
theorem toConv_eq_one_of_geometricallyUnipotentPoints
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K]
    {U : Type u} [CommRing U] [HopfAlgebra k U] [Algebra.FiniteType k U] [Algebra.Smooth k U]
    (hU : geometricallyUnipotentPointsCommHopfAlgProperty k (CommHopfAlgCat.of k U))
    (φ : WeilRestriction k K K[T;T⁻¹] →ₐc[k] U) :
    toConv (φ : WeilRestriction k K K[T;T⁻¹] →ₐ[k] U) = 1 := by
  let k' := AlgebraicClosure k
  let ι : K →ₐ[k] k' := IsAlgClosed.lift
  let _ : Algebra K k' := ι.toAlgebra
  have : IsScalarTower k K k' := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : IsReduced (K ⊗[k] U) := isReduced_of_smooth K _
  rw [geometricallyUnipotentPointsCommHopfAlgProperty_iff] at hU
  apply (multiplicativeGroupPoints k K U).injective
  rw [map_one]
  refine Units.ext ?_
  have hv := groupLike_eq_one_of_forall_isUnipotentPoint (k := K) (H := K ⊗[k] U) (K := k')
    (fun g ↦ (AlgHom.baseChangePointsMulEquiv (K := K)).apply_symm_apply g ▸
      (hU ((AlgHom.baseChangePointsMulEquiv (K := K)).symm g)).baseChangePointsMulEquiv)
    ⟨_, isGroupLikeElem_multiplicativeGroupPoints_toConv φ⟩
  exact congrArg GroupLike.val hv

/-- **`Res_{K/k} 𝔾ₘ` is pseudo-reductive** for every finite field extension `K / k` in any
characteristic: it is smooth and geometrically connected, and its unipotent radical over `k` is
trivial because it has no nontrivial homomorphism from a smooth unipotent group
(`TauCeti.Algebra.WeilRestriction.toConv_eq_one_of_geometricallyUnipotentPoints`). For a nontrivial
purely inseparable `K / k` it is not reductive
(`TauCeti.Algebra.WeilRestriction.not_reductive_multiplicativeGroup_of_isPurelyInseparable`). -/
theorem pseudoReductive_multiplicativeGroup
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] :
    pseudoReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])) := by
  let H := FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])
  refine (pseudoReductiveCommHopfAlgProperty_iff k H).2 ⟨inferInstance,
    geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup, ?_⟩
  rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  obtain ⟨_, hunip⟩ := (smoothUnipotentCommHopfAlgProperty_iff k _).1 hI.smoothUnipotent
  have h1 := toConv_eq_one_of_geometricallyUnipotentPoints
    ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).2 hunip)
    (FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H I))
  refine HopfIdeal.ext fun x ↦ ⟨fun hx ↦ (HopfIdeal.mem_augmentation k _).2
    (I.counit_eq_zero hx), fun hx ↦ ?_⟩
  rw [HopfIdeal.mem_augmentation] at hx
  rw [← FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff]
  have := congrArg (fun f ↦ f.ofConv x) h1
  simpa [AlgHom.convOne_apply, hx] using this

/-- **`Res_{K/k} 𝔾ₘ` ceases to be pseudo-reductive over `AlgebraicClosure k`** when `K / k` is a
nontrivial finite purely inseparable extension: although `Res_{K/k} 𝔾ₘ` is pseudo-reductive over `k`
in positive characteristic (`pseudoReductive_multiplicativeGroup`), its geometric fibre has
nontrivial unipotent radical. Thus pseudo-reductivity is not preserved by arbitrary inseparable
field extensions. -/
theorem not_pseudoReductive_baseChange_multiplicativeGroup_of_isPurelyInseparable {K : Type u}
    [Field K] [Algebra k K] [FiniteDimensional k K] [IsPurelyInseparable k K]
    (hK : 1 < Module.finrank k K) :
    ¬ pseudoReductiveCommHopfAlgProperty (AlgebraicClosure k)
      (FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k)
        (FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹]))) := by
  intro hpr
  apply not_reductive_multiplicativeGroup_of_isPurelyInseparable hK
  let H := FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])
  exact (reductiveCommHopfAlgProperty_iff_unipotentRadicalDefiningIdeal_baseChange_eq_augmentation
    k H).mpr ⟨inferInstance, geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup,
      hpr.unipotentRadicalDefiningIdeal_eq_augmentation⟩

end TauCeti.Algebra.WeilRestriction
