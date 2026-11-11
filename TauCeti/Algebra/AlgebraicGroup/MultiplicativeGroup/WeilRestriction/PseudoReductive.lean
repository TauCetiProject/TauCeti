/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Basic
public import TauCeti.Algebra.AlgebraicGroup.PseudoReductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Basic
public import TauCeti.FieldTheory.PurelyInseparable.BaseChange
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.WeilRestriction.Connected
import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.CharP
import TauCeti.Algebra.AlgebraicGroup.Torus.Recognition
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Construction
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Semisimple
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The Weil restriction of `𝔾ₘ` along a purely inseparable extension

For a nontrivial finite purely inseparable extension `K / k`, the Weil restriction `Res_{K/k} 𝔾ₘ`
is the standard example of a commutative pseudo-reductive group which is not reductive. This file
proves both properties, in characteristic `p > 0`; a nontrivial purely inseparable extension
forces this.

**Not reductive.** Let `B` be a finite-dimensional commutative `k`-algebra and `k'` an algebraic
closure of `k`. The `k'`-points of `Res_{B/k} 𝔾ₘ` are the units of `B ⊗[k] k'`. If this ring has a
nonzero nilpotent element `n`, then `1 + n` is a nonidentity point of `p`-power order, hence a
nonidentity unipotent point. A commutative reductive group is a torus, all of whose geometric
points are semisimple, and a point which is both semisimple and unipotent is the identity. Hence
`Res_{B/k} 𝔾ₘ` is not reductive unless `B ⊗[k] k'` is reduced. For `B = K` as above, `K ⊗[k] k'` is
a local ring with nonzero nilpotent maximal ideal
(`TauCeti.IsPurelyInseparable.not_isReduced_tensorProduct`).

**Pseudo-reductive.** For every finite field extension `K / k`, homomorphisms from a smooth
unipotent group `U` to `Res_{K/k} 𝔾ₘ` are trivial. By the defining adjunction of the Weil
restriction such a homomorphism is a unit `v` of `K ⊗[k] U`, a character of `U` over `K`. The
`K`-algebra `K ⊗[k] U` is reduced, so `v = 1` can be tested at its `K`-algebra maps to `k'`, for
`K` embedded in `k'`. Such a map is multiplication against a geometric point of `U`, which has
`p`-power order since it is unipotent; so it sends `v` to a `p`-power root of unity in `k'`, that
is, to one. In particular the unipotent radical of `Res_{K/k} 𝔾ₘ` over `k` is trivial, while
smoothness and geometric connectedness are `TauCeti.Algebra.WeilRestriction.instSmooth` and
`TauCeti.Algebra.WeilRestriction.geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.isReduced_tensorProduct_of_reductive_multiplicativeGroup`: in
  characteristic `p > 0`, if `Res_{B/k} 𝔾ₘ` is reductive then `B ⊗[k] AlgebraicClosure k` is
  reduced.
* `TauCeti.Algebra.WeilRestriction.not_reductive_multiplicativeGroup_of_isPurelyInseparable`: for
  a nontrivial finite purely inseparable extension `K / k`, `Res_{K/k} 𝔾ₘ` is not reductive.
* `TauCeti.Algebra.WeilRestriction.toConv_eq_one_of_geometricallyUnipotentPoints`: in
  characteristic `p > 0`, every homomorphism from a smooth unipotent group to `Res_{K/k} 𝔾ₘ` is
  trivial.
* `TauCeti.Algebra.WeilRestriction.pseudoReductive_multiplicativeGroup`: in
  characteristic `p > 0`, `Res_{K/k} 𝔾ₘ` is pseudo-reductive for every finite field extension
  `K / k`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Example 1.1.3 and
  Proposition 1.1.10.
* J. S. Milne, *Algebraic Groups* (2017), §§2.i and 19.b.
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

/-- **Every homomorphism from a smooth unipotent group to `Res_{K/k} 𝔾ₘ` is trivial**, for a
finite field extension `K / k` in characteristic `p > 0`. A bialgebra map from the coordinate Hopf
algebra of `Res_{K/k} 𝔾ₘ` to that of a smooth affine group `U` of finite type whose geometric
points are unipotent is the identity point `algebraMap k U ∘ counit` of `Res_{K/k} 𝔾ₘ` over `U`. -/
theorem toConv_eq_one_of_geometricallyUnipotentPoints (p : ℕ) [Fact p.Prime] [CharP k p]
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
  -- The unit `v` of `K ⊗[k] U` classifying `φ` is tested at the `K`-algebra maps to `k'`.
  refine Units.ext (eq_of_forall_algHom_apply_eq (k := K) (K := k') fun ψ ↦ ?_)
  -- The geometric point `y` of `U` underlying `ψ` has `p`-power order.
  let y : U →ₐ[k] k' := (ψ.restrictScalars k).comp Algebra.TensorProduct.includeRight
  obtain ⟨n, hn⟩ := (hU (toConv y)).exists_pow_char_pow_eq_one p
  have hz : BialgHom.mapDomain φ (toConv y) ^ p ^ n = 1 :=
    (map_pow (BialgHom.mapDomain φ) (toConv y) (p ^ n)).symm.trans (by rw [hn, map_one])
  -- Its image in `(K ⊗[k] k')ˣ` is the image of `v` under `K ⊗ y`.
  have hw := (map_pow (multiplicativeGroupPoints k K k') _ (p ^ n)).symm.trans
    (congrArg (multiplicativeGroupPoints k K k') hz)
  rw [map_one, BialgHom.mapDomain_apply, multiplicativeGroupPoints_naturality] at hw
  -- Multiplication `K ⊗[k] k' → k'` recovers `ψ` from `K ⊗ y`.
  let m : K ⊗[k] k' →ₐ[K] k' :=
    Algebra.TensorProduct.lift (Algebra.ofId K k') (AlgHom.id k k') fun _ _ ↦ .all _ _
  have hψ : m.comp (Algebra.TensorProduct.lTensor (S := K) K y) = ψ :=
    Algebra.TensorProduct.ext_ring (AlgHom.ext fun _ ↦ by simp [m, y])
  have hv := congrArg (fun w : (K ⊗[k] k')ˣ ↦ m w) hw
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one, map_pow, map_one] at hv
  replace hv : ψ (multiplicativeGroupPoints k K U (toConv φ)) ^ p ^ n = 1 := by
    simpa [← hψ] using hv
  rw [Units.val_one, map_one]
  exact iterateFrobenius_inj k' p n (by simpa [iterateFrobenius_def] using hv)

/-- **`Res_{K/k} 𝔾ₘ` is pseudo-reductive** for a finite field extension `K / k` in
characteristic `p > 0`: it is smooth and geometrically connected, and its unipotent radical over
`k` is trivial because it has no nontrivial homomorphism from a smooth unipotent group
(`TauCeti.Algebra.WeilRestriction.toConv_eq_one_of_geometricallyUnipotentPoints`). For a
nontrivial purely inseparable `K / k` it is not reductive
(`TauCeti.Algebra.WeilRestriction.not_reductive_multiplicativeGroup_of_isPurelyInseparable`). -/
theorem pseudoReductive_multiplicativeGroup (p : ℕ) [Fact p.Prime] [CharP k p]
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K] :
    pseudoReductiveCommHopfAlgProperty k
      (FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])) := by
  let H := FiniteTypeCommHopfAlgCat.of k (WeilRestriction k K K[T;T⁻¹])
  refine (pseudoReductiveCommHopfAlgProperty_iff k H).2 ⟨inferInstance,
    geometricallyConnectedCommHopfAlgProperty_multiplicativeGroup, ?_⟩
  rw [FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_eq_augmentation_iff]
  intro I hI
  obtain ⟨_, hunip⟩ := (smoothUnipotentCommHopfAlgProperty_iff k _).1 hI.smoothUnipotent
  have h1 := toConv_eq_one_of_geometricallyUnipotentPoints p
    ((geometricallyUnipotentPointsCommHopfAlgProperty_iff k _).2 hunip)
    (FiniteTypeCommHopfAlgCat.toBialgHom (FiniteTypeCommHopfAlgCat.mkQuotient H I))
  refine HopfIdeal.ext fun x ↦ ⟨fun hx ↦ (HopfIdeal.mem_augmentation k _).2
    (I.counit_eq_zero hx), fun hx ↦ ?_⟩
  rw [HopfIdeal.mem_augmentation] at hx
  rw [← FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff]
  have := congrArg (fun f ↦ f.ofConv x) h1
  simpa [AlgHom.convOne_apply, hx] using this

end TauCeti.Algebra.WeilRestriction
