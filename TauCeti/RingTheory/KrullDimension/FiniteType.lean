/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.KrullDimension.Integral
public import TauCeti.RingTheory.KrullDimension.Quotient
public import TauCeti.Topology.KrullDimension.Local
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.UFD
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Fiber
import TauCeti.Topology.KrullDimension.ClosedCover

/-!
# Krull dimension of finitely generated algebras over a field

Let `A` be a nontrivial finitely generated algebra over a field `k`. Noether normalization gives an
injective finite map `k[X₁, …, Xₛ] → A`, so `A` has Krull dimension `s`. Extending scalars along
any Noetherian `k`-algebra `K` keeps the map `K[X₁, …, Xₛ] → K ⊗[k] A` injective (every
`k`-module is flat) and finite, so `K ⊗[k] A` has the dimension of `K[X₁, …, Xₛ]`, namely
`dim K + s`. The tensor-product theorem handles the subsingleton case separately.

In particular the Krull dimension of a finitely generated algebra over a field does not change
under extension of the base field. This is the affine form of the invariance of the dimension of
a scheme locally of finite type over a field under field extension, which is what makes
fibrewise dimension bounds on morphisms stable under base change.

For a domain `A`, the same Noether normalization identifies `s` with the transcendence degree of
`A` over `k`: the variables form a transcendence basis because `A` is integral over them. The
transcendence degree only sees the fraction field, so an algebraic extension of finitely generated
domains, such as a localization `A[1/f]` with `f ≠ 0`, does not change the Krull dimension.

Every maximal ideal of a finitely generated algebra `A` with irreducible spectrum over `k` has
height `dim A`. For the polynomial ring `k[X₁, …, Xₛ]` this follows by induction on `s`: a maximal
ideal of `R[X]`, for `R`
a Jacobson ring, contracts to a maximal ideal of `R`, and its height is one more than the height of
that contraction. For a domain `A`, Noether normalization makes `A` integral over the normal domain
`k[X₁, …, Xₛ]`, so going down gives the lower height bound. The general case follows by quotienting
by the nilradical, which preserves dimension and prime heights. Geometrically, all closed points
of an irreducible variety have local dimension the dimension of the variety.

Geometrically, a nonempty open part of an irreducible closed subset of `Spec A` has the dimension
of the whole closed subset; this is what makes pure-dimensionality of schemes locally of finite
type over a field a local property.

The dimension formula `ht p + dim (A ⧸ p) = dim A` holds for every prime `p` of a finitely
generated algebra `A` with irreducible spectrum over `k`. The inequality `≤` holds in every ring.
For a domain `A`, the reverse inequality follows by induction on `dim A`. A nonzero prime `p`
contains a prime `P` of height one, minimal over a nonzero principal ideal. Over a Noether
normalization `k[X₁, …, Xₛ] ⊆ A` the prime `P` contracts to a height-one prime of the factorial
ring `k[X₁, …, Xₛ]`, which is principal, so `dim (A ⧸ P) = dim A - 1`; and the image of `p` in
`A ⧸ P` has height at most `ht p - 1`. The dimension of `A ⧸ p` is the transcendence degree of the
residue field `κ(p)`.

Consequently the local Krull dimension of `Spec A` at `p`, for any finitely generated `A`, is
`ht p + dim (A ⧸ p) = dim A_p + trdeg_k κ(p)`. Small open neighbourhoods of `p` meet only the
irreducible components `V(q)` through `p`, and each of these satisfies the dimension formula in
`A ⧸ q`; the height of `p` is attained on one of them.

## Main results

* `TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial`: an injective integral map
  `k[X₁, …, Xₛ] → A` forces `dim A = s`, the number of variables.
* `TauCeti.finiteRingKrullDim_of_finiteType`: a nontrivial finitely generated algebra over a field
  has finite Krull dimension.
* `TauCeti.ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType`:
  `dim (K ⊗[k] A) = dim K + dim A` for a Noetherian `k`-algebra `K`.
* `TauCeti.ringKrullDim_tensorProduct_field_of_finiteType`: `dim (K ⊗[k] A) = dim A` for a field
  extension `K / k`.
* `TauCeti.ringKrullDim_eq_toNat_trdeg`: a finitely generated domain over `k` has Krull dimension
  its transcendence degree over `k`.
* `TauCeti.ringKrullDim_eq_of_isAlgebraic`: an algebraic extension of finitely generated domains
  over `k` preserves the Krull dimension; `TauCeti.ringKrullDim_localization_away` is the case of
  `A[1/f]` with `f ≠ 0`.
* `MvPolynomial.height_eq_natCard_of_isMaximal`: every maximal ideal of `k[Xᵢ | i ∈ ι]`, for `ι`
  finite, has height the number of variables.
* `TauCeti.height_eq_ringKrullDim_of_isMaximal`: every maximal ideal of a finitely generated
  algebra `A` with irreducible spectrum over `k` has height `dim A`.
* `Ideal.isMaximal_under_of_finiteType`: along a homomorphism of `k`-algebras `A → B` with `B`
  finitely generated, maximal ideals of `B` contract to maximal ideals of `A`.
* `Ideal.height_eq_height_under_of_finite_of_finiteType`: a finite faithful extension of domains
  preserves prime heights when the base is a finitely generated algebra over a field.
* `TauCeti.topologicalKrullDim_inter_eq_of_finiteType`: in `Spec A`, a nonempty open part of an
  irreducible closed subset has the dimension of that subset.
* `Ideal.height_add_ringKrullDim_quotient_of_finiteType`: the dimension formula
  `ht p + dim (A ⧸ p) = dim A` for a finitely generated algebra `A` with irreducible spectrum.
* `Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField`: `dim (A ⧸ p) = trdeg_k κ(p)`.
* `TauCeti.topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient`,
  `TauCeti.topologicalKrullDimAt_eq_ringKrullDim_localization_add_trdeg`: the local Krull
  dimension of `Spec A` at `p` is `ht p + dim (A ⧸ p) = dim A_p + trdeg_k κ(p)`.

## References

* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW) (Noether normalization)
* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0) (dimension and
  transcendence degree)
* R. Hartshorne, *Algebraic Geometry* (1977), Chapter I, Theorem 1.8A (heights of
  primes in finitely generated domains over a field, and the dimension formula)
* [Stacks Project, Tags 00P0–00P4](https://stacks.math.columbia.edu/tag/00P4) (local dimension of
  `Spec A` for `A` of finite type over a field)
* The finite-extension height theorem is ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization), commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `Pcf.height_under_eq_of_finite_of_finiteType` in `lean/Pcf/Bounding/Divisors.lean`.
-/

public section

namespace TauCeti

open scoped TensorProduct
open Topology PrimeSpectrum

variable {k : Type*} [Field k]

/-- If a `k`-algebra `A` is integral over a polynomial ring `k[Xᵢ | i ∈ ι]` in finitely many
variables embedded in it, then `A` has Krull dimension the number of variables. -/
theorem ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial {ι A : Type*} [Finite ι]
    [CommRing A] [Algebra k A] (g : MvPolynomial ι k →ₐ[k] A) (hinj : Function.Injective g)
    (hint : g.IsIntegral) : ringKrullDim A = Nat.card ι := by
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial ι k) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := MvPolynomial ι k),
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
    zero_add]

variable (k) in
/-- A nontrivial finitely generated algebra over a field has finite Krull dimension. -/
theorem finiteRingKrullDim_of_finiteType (A : Type*) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  exact .of_ringKrullDim_eq_natCast
    (ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint)

variable (k) in
/-- A finite faithful extension of domains preserves prime heights when the base is a finitely
generated algebra over a field. -/
theorem _root_.Ideal.height_eq_height_under_of_finite_of_finiteType {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S] [Algebra k R]
    [Algebra.FiniteType k R] [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    (prime : Ideal S) [prime.IsPrime] : prime.height = (prime.under R).height := by
  have : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain (algebraMap R S)
  obtain ⟨numVars, embedding, hinj, hfinite⟩ := exists_finite_inj_algHom_of_fg k R
  let polynomial := MvPolynomial (Fin numVars) k
  let : Algebra polynomial R := embedding.toRingHom.toAlgebra
  have : Module.Finite polynomial R := hfinite
  have : FaithfulSMul polynomial R :=
    (faithfulSMul_iff_algebraMap_injective polynomial R).mpr hinj
  let : Algebra polynomial S := ((algebraMap R S).comp (algebraMap polynomial R)).toAlgebra
  have : IsScalarTower polynomial R S := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Finite polynomial S := Module.Finite.trans R S
  have : FaithfulSMul polynomial S :=
    (faithfulSMul_iff_algebraMap_injective polynomial S).mpr
      ((FaithfulSMul.algebraMap_injective R S).comp hinj)
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  calc
    prime.height = (prime.under polynomial).height :=
      Ideal.height_eq_height_under_of_quasiFinite prime
    _ = ((prime.under R).under polynomial).height := by rw [Ideal.under_under]
    _ = (prime.under R).height :=
      (Ideal.height_eq_height_under_of_quasiFinite (prime.under R)).symm

/-- The Krull dimension of `K ⊗[k] A`, for a Noetherian `k`-algebra `K` and a finitely generated
`k`-algebra `A`, is the sum of the Krull dimensions of `K` and `A`. -/
@[simp]
theorem ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType (K A : Type*) [CommRing K]
    [IsNoetherianRing K] [Algebra k K] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim K + ringKrullDim A := by
  cases subsingleton_or_nontrivial A with
  | inl hA => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
    -- Noether normalization `k[X₁, …, Xₛ] → A`, base-changed to `K[X₁, …, Xₛ] → K ⊗[k] A`,
    -- stays finite, and stays injective because `K` is flat over the field `k`.
    obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    let φ := Algebra.TensorProduct.map (AlgHom.id k K) g
    have hφinj : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K) g.toLinearMap hinj
    have hφfin : φ.toRingHom.Finite := RingHom.Finite.tensorProductMap (AlgHom.Finite.id k K) hfin
    algebraize [φ.toRingHom]
    have : FaithfulSMul (K ⊗[k] MvPolynomial (Fin s) k) (K ⊗[k] A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
    rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := K ⊗[k] MvPolynomial (Fin s) k),
      ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hfin.to_isIntegral]

/-- The Krull dimension of a finitely generated algebra over a field is unchanged by extending
the base field. -/
theorem ringKrullDim_tensorProduct_field_of_finiteType (K A : Type*) [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim A := by
  rw [ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType, ringKrullDim_eq_zero_of_field,
    zero_add]

variable (k) in
/-- A finitely generated domain over a field `k` has Krull dimension its transcendence degree over
`k`. The transcendence degree is finite by `Algebra.trdeg_lt_aleph0_of_finiteType`. -/
theorem ringKrullDim_eq_toNat_trdeg (A : Type*) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : ringKrullDim A = (Algebra.trdeg k A).toNat := by
  -- Noether normalization `k[X₁, …, Xₛ] → A` gives `dim A = s`, and the variables form a
  -- transcendence basis of `A` since `A` is integral, hence algebraic, over them.
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint]
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have h := lift_trdeg_add_eq k (MvPolynomial (Fin s) k) A
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := A)] at h
  rw [← Cardinal.toNat_lift, ← h]
  simp

variable (k) in
/-- An algebraic extension `B / A` of finitely generated domains over a field `k` does not change
the Krull dimension: both have the transcendence degree of `B` over `k`. -/
theorem ringKrullDim_eq_of_isAlgebraic (A B : Type*) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B]
    [Algebra.IsAlgebraic A B] [Algebra.FiniteType k A] [Algebra.FiniteType k B] :
    ringKrullDim A = ringKrullDim B := by
  have : IsDomain A := (FaithfulSMul.algebraMap_injective A B).isDomain (algebraMap A B)
  have h := lift_trdeg_add_eq k A B
  rw [trdeg_eq_zero (R := A) (A := B), Cardinal.lift_zero, add_zero] at h
  rw [ringKrullDim_eq_toNat_trdeg k, ringKrullDim_eq_toNat_trdeg k, ← Cardinal.toNat_lift, h,
    Cardinal.toNat_lift]

variable (k) in
/-- Inverting a nonzero element of a finitely generated domain over a field does not change its
Krull dimension. -/
theorem ringKrullDim_localization_away {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {f : A} (hf : f ≠ 0) :
    ringKrullDim (Localization.Away f) = ringKrullDim A := by
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : FaithfulSMul A (Localization.Away f) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsLocalization.injective _ hle)
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have := IsLocalization.isAlgebraic (Localization.Away f) (Submonoid.powers f)
  exact (ringKrullDim_eq_of_isAlgebraic k A _).symm

/-- Every maximal ideal of the polynomial ring `k[Xᵢ | i ∈ ι]` over a field `k` in finitely many
variables has height the number of variables. -/
@[simp]
theorem _root_.MvPolynomial.height_eq_natCard_of_isMaximal {ι : Type*} [Finite ι]
    (M : Ideal (MvPolynomial ι k)) [M.IsMaximal] : M.height = Nat.card ι := by
  revert M
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    intro M _
    have := H (M.comap (MvPolynomial.renameEquiv k e).toRingEquiv)
    rwa [RingEquiv.height_comap, Nat.card_congr e] at this
  | h_empty =>
    -- The polynomial ring in no variables has dimension `0`.
    intro M hM
    simpa using Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
  | h_option IH =>
    -- A maximal ideal of `R[X]`, with `R = k[Xᵢ | i ∈ α]` Jacobson, lies over a maximal ideal
    -- of `R` and has height one more than it.
    rename_i α _
    intro M _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let P := M.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have : (P.under (MvPolynomial α k)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    rw [← e.height_map M, Polynomial.height_eq_height_add_one (P.under (MvPolynomial α k)) P,
      IH, Finite.card_option, Nat.cast_add, Nat.cast_one]

variable (k) in
private theorem height_eq_ringKrullDim_of_isMaximal_of_isDomain {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (m : Ideal A) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  -- Noether normalization `k[X₁, …, Xₛ] → A` gives `dim A = s`; going down over the normal domain
  -- `k[X₁, …, Xₛ]` bounds the height of `m` below by that of its contraction, which is `s`.
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  refine le_antisymm (Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top') ?_
  rw [ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint]
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let p := m.under (MvPolynomial (Fin s) k)
  have : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m,
    MvPolynomial.height_eq_natCard_of_isMaximal p]
  exact_mod_cast le_self_add

variable (k) in
/-- Every maximal ideal of a finitely generated algebra with irreducible spectrum over a field
has height the Krull dimension of the algebra. -/
theorem height_eq_ringKrullDim_of_isMaximal {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)]
    (m : Ideal A) [m.IsMaximal] : (m.height : WithBot ℕ∞) = ringKrullDim A := by
  let I : Ideal A := nilradical A
  have hI : I.IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have : I.IsPrime := hI
  have : IsDomain (A ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr hI
  have : Algebra.FiniteType k (A ⧸ I) := .of_surjective (Ideal.Quotient.mkₐ k I)
    Ideal.Quotient.mk_surjective
  let q : Ideal (A ⧸ I) := m.map (Ideal.Quotient.mk I)
  have hIm : I ≤ m := nilradical_le_prime m
  have : q.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (by simpa [Ideal.mk_ker] using hIm)
  rw [← Ideal.height_map_quotientMk_nilradical m,
    ← ringKrullDim_quotient_nilradical A]
  exact height_eq_ringKrullDim_of_isMaximal_of_isDomain k q

variable (k) in
/-- Let `A → B` be a homomorphism of algebras over a field `k`, with `B` finitely generated over
`k`. Then every maximal ideal of `B` contracts to a maximal ideal of `A`. -/
theorem _root_.Ideal.isMaximal_under_of_finiteType {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B] [Algebra.FiniteType k B]
    (q : Ideal B) [q.IsMaximal] : (q.under A).IsMaximal := by
  -- `A ⧸ q ∩ A` is a domain embedded in the field `B ⧸ q`, which is finite over `k` by Zariski's
  -- lemma; so it is integral over `k`, hence a field.
  let := Ideal.Quotient.field q
  have : Module.Finite k (B ⧸ q) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ q)
  have : Module.Finite k (A ⧸ q.under A) :=
    .of_injective (Ideal.quotientMapₐ q (IsScalarTower.toAlgHom k A B) le_rfl).toLinearMap
      Ideal.quotientMap_injective
  exact Ideal.Quotient.maximal_of_isField _ (isField_of_isIntegral_of_isField' (Field.toIsField k))

variable (k) in
/-- In the spectrum of a finitely generated algebra over a field, a nonempty open part `Z ∩ U` of
an irreducible closed subset `Z` has the Krull dimension of `Z`. -/
theorem topologicalKrullDim_inter_eq_of_finiteType {A : Type*} [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] {Z U : Set (PrimeSpectrum A)} (hZ : IsIrreducible Z)
    (hZc : IsClosed Z) (hU : IsOpen U) (hZU : (Z ∩ U).Nonempty) :
    topologicalKrullDim ↥(Z ∩ U) = topologicalKrullDim Z := by
  refine le_antisymm (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le
    ?_
  -- `Z` is the zero locus of a prime `p`, so it is `Spec (A ⧸ p)`; and `Z ∩ U` contains the basic
  -- open set of some `g ∉ p`, which is `Spec (A ⧸ p)[1/g']` for the image `g'` of `g`.
  set p := vanishingIdeal Z
  have := isIrreducible_iff_vanishingIdeal_isPrime.mp hZ
  have hZp : zeroLocus p = Z := by rw [zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
  obtain ⟨x, hxZ, hxU⟩ := hZU
  obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU hU
  set g' := Ideal.Quotient.mk p g
  have hg : g' ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h ↦ hxg ((hZp ▸ hxZ : x ∈ zeroLocus p) h)
  let i := comap (Ideal.Quotient.mk p)
  have hi : IsClosedEmbedding i :=
    isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective
  have hrange : Set.range i = Z := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hZp]
  let j := comap (algebraMap (A ⧸ p) (Localization.Away g'))
  have hj : IsOpenEmbedding j := localization_away_isOpenEmbedding _ g'
  have hsub (y : PrimeSpectrum (Localization.Away g')) : i (j y) ∈ Z ∩ U := by
    refine ⟨hrange ▸ ⟨_, rfl⟩, hgU ?_⟩
    have hy : j y ∈ (basicOpen g' : Set (PrimeSpectrum (A ⧸ p))) :=
      localization_away_comap_range (Localization.Away g') g' ▸ ⟨y, rfl⟩
    rw [SetLike.mem_coe, mem_basicOpen] at hy ⊢
    simpa [i, comap_asIdeal] using hy
  calc topologicalKrullDim Z = topologicalKrullDim (PrimeSpectrum (A ⧸ p)) :=
        ((hi.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange)).symm.isHomeomorph
          |>.topologicalKrullDim_eq
    _ = topologicalKrullDim (PrimeSpectrum (Localization.Away g')) := by
        rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_localization_away k hg]
    _ ≤ topologicalKrullDim ↥(Z ∩ U) :=
        ((hi.isEmbedding.comp hj.isEmbedding).isInducing.codRestrict hsub).topologicalKrullDim_le


variable (k) in
/-- In a finitely generated domain over a field, quotienting by a prime of height one lowers the
Krull dimension by exactly one. -/
private theorem ringKrullDim_quotient_add_one_of_height_eq_one {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (P : Ideal A) [P.IsPrime]
    (hP : P.height = 1) : ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  -- Over a Noether normalization `R = k[X₁, …, Xₛ] ⊆ A`, `P` contracts to a height-one prime of
  -- the factorial ring `R`, which is principal; Krull's principal ideal theorem at a maximal ideal
  -- of `R`, of height `s`, then bounds the dimension of the quotient below.
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  set R := MvPolynomial (Fin s) k
  algebraize [g.toRingHom]
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.Finite R A := hfin
  set Q := P.under R
  have hQ : Q.height = 1 := Ideal.height_eq_height_under_of_finite_of_finiteType (R := R) k P ▸ hP
  obtain ⟨f, hf⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQ
  have hfQ : f ∈ Q := by
    rw [hf]
    exact Ideal.mem_span_singleton_self f
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact Q.ne_bot_of_height_eq_one hQ (by simpa using hf)
  -- `A ⧸ P` is integral over `R ⧸ Q = R ⧸ (f)`, and `A` is integral over `R`.
  rw [ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hfin.to_isIntegral,
    ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := R ⧸ Q) (S := A ⧸ P), hf,
    Ideal.submodule_span_eq]
  refine le_antisymm ?_ ?_
  · have := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf0)
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      zero_add] at this
  · obtain ⟨M, hM, hQM⟩ := Q.exists_le_maximal Ideal.IsPrime.ne_top'
    have := Ideal.height_le_ringKrullDim_quotient_add_one (hQM hfQ)
    rwa [MvPolynomial.height_eq_natCard_of_isMaximal] at this

variable (k) in
/-- The dimension formula `ht p + dim (A ⧸ p) = dim A` for a finitely generated domain `A` over a
field. -/
private theorem height_add_ringKrullDim_quotient_of_isDomain {A : Type*} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    p.height + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  refine le_antisymm (Ideal.height_add_ringKrullDim_quotient_le p) ?_
  -- Induct on `dim A`: below a nonzero prime `p` lies a prime `P` of height one, and passing to
  -- the domain `A ⧸ P` lowers `dim A` by one and the height of `p` by at least one.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim A = n := ⟨_, ringKrullDim_eq_toNat_trdeg k A⟩
  induction n generalizing A with
  | zero =>
    rw [hn]
    exact add_nonneg (by simp) ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    rcases eq_or_ne p ⊥ with rfl | hp
    · simp [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
    have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    obtain ⟨a, hap, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    obtain ⟨P, hP, hPp⟩ :=
      Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem p).mpr hap)
    have := hP.1.1
    have hP0 : P ≠ ⊥ := fun h ↦ ha (by simpa [h] using hP.1.2)
    have hP1 : P.height = 1 := le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
      (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hP0)))
    have hdimP : ringKrullDim (A ⧸ P) = n := by
      have hdim := ringKrullDim_quotient_add_one_of_height_eq_one k P hP1
      rw [hn, ringKrullDim_eq_toNat_trdeg k (A ⧸ P)] at hdim
      rw [ringKrullDim_eq_toNat_trdeg k (A ⧸ P),
        Nat.add_right_cancel (by exact_mod_cast hdim : (Algebra.trdeg k (A ⧸ P)).toNat + 1 = n + 1)]
    have : (p.map (Ideal.Quotient.mk P)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hPp
    have hIH := ih (p.map (Ideal.Quotient.mk P)) hdimP
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPp), hdimP] at hIH
    have hht := Ideal.height_map_quotientMk_add_one_le hPp fun m hm hle ↦ by
      rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hm
      exact hP0 (le_bot_iff.mp (hm ▸ hle))
    calc ringKrullDim A = n + 1 := by rw [hn]; push_cast; rfl
      _ ≤ (p.map (Ideal.Quotient.mk P)).height + ringKrullDim (A ⧸ p) + 1 := by gcongr
      _ = ((p.map (Ideal.Quotient.mk P)).height + 1 : ℕ∞) + ringKrullDim (A ⧸ p) := by
        push_cast
        exact add_right_comm _ _ _
      _ ≤ p.height + ringKrullDim (A ⧸ p) := by gcongr; exact_mod_cast hht

variable (k) in
/-- **The dimension formula.** In a finitely generated algebra `A` with irreducible spectrum over a
field, every prime `p` satisfies `ht p + dim (A ⧸ p) = dim A`. -/
theorem _root_.Ideal.height_add_ringKrullDim_quotient_of_finiteType {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] [IrreducibleSpace (PrimeSpectrum A)] (p : Ideal A)
    [p.IsPrime] : p.height + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  -- Pass to the domain `A ⧸ I`, for `I` the nilradical, which has the same primes.
  let I : Ideal A := nilradical A
  have : I.IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  have : IsDomain (A ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr this
  have hIp : I ≤ p := nilradical_le_prime p
  have : (p.map (Ideal.Quotient.mk I)).IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIp
  rw [← Ideal.height_map_quotientMk_nilradical p, ← ringKrullDim_quotient_nilradical A,
    ← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIp)]
  exact height_add_ringKrullDim_quotient_of_isDomain k _

variable (k) in
/-- For a prime `p` of a finitely generated algebra `A` over a field `k`, the Krull dimension of
`A ⧸ p` is the transcendence degree over `k` of the residue field `κ(p)`, the fraction field of
`A ⧸ p`. -/
theorem _root_.Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) = (Algebra.trdeg k p.ResidueField).toNat := by
  have : FaithfulSMul (A ⧸ p) p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective _ _)
  have := IsLocalization.isAlgebraic p.ResidueField (nonZeroDivisors (A ⧸ p))
  rw [ringKrullDim_eq_toNat_trdeg k (A ⧸ p), ← trdeg_add_eq k (A ⧸ p) (A := p.ResidueField),
    trdeg_eq_zero (R := A ⧸ p), add_zero]

variable (k) in
/-- **Local dimension of an affine scheme of finite type over a field.** For a finitely generated
algebra `A` over a field `k`, the local Krull dimension of `Spec A` at a prime `p` is
`ht p + dim (A ⧸ p)`. -/
theorem topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    topologicalKrullDimAt (PrimeSpectrum A) p =
      p.asIdeal.height + ringKrullDim (A ⧸ p.asIdeal) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  -- For a minimal prime `q ≤ p`, the dimension formula in the domain `A ⧸ q` reads
  -- `ht (p ⧸ q) + dim (A ⧸ p) = dim (A ⧸ q)`.
  have hq (q : Ideal A) (hq : q ∈ minimalPrimes A) (hqp : q ≤ p.asIdeal) :
      (p.asIdeal.map (Ideal.Quotient.mk q)).height + ringKrullDim (A ⧸ p.asIdeal) =
        ringKrullDim (A ⧸ q) := by
    have := hq.1.1
    have : (p.asIdeal.map (Ideal.Quotient.mk q)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hqp
    rw [← Ideal.height_add_ringKrullDim_quotient_of_finiteType k
        (p.asIdeal.map (Ideal.Quotient.mk q)),
      ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqp)]
  refine le_antisymm ?_ ((topologicalKrullDimAt_eq_iInf p).ge.trans' (le_iInf fun U ↦ ?_))
  · -- The open neighbourhood `U` of `p` avoiding the finitely many components `V(q)` not through
    -- `p` is covered by the components `V(q)` through `p`, each of dimension at most
    -- `ht (p ⧸ q) + dim (A ⧸ p) ≤ ht p + dim (A ⧸ p)`.
    let S := {q ∈ minimalPrimes A | ¬q ≤ p.asIdeal}
    have hS : S.Finite :=
      (minimalPrimes.finite_of_isNoetherianRing A).subset (Set.sep_subset _ _)
    let U : Set (PrimeSpectrum A) := (⋃ q ∈ S, zeroLocus (q : Set A))ᶜ
    have hU : IsOpen U := (hS.isClosed_biUnion fun _ _ ↦ isClosed_zeroLocus _).isOpen_compl
    have hpU : p ∈ U := by
      simp only [U, S, Set.mem_compl_iff, Set.mem_iUnion, mem_zeroLocus, SetLike.coe_subset_coe]
      exact fun ⟨q, ⟨_, h⟩, h'⟩ ↦ h h'
    let T := {q ∈ minimalPrimes A | q ≤ p.asIdeal}
    have : Finite T :=
      ((minimalPrimes.finite_of_isNoetherianRing A).subset (Set.sep_subset _ _)).to_subtype
    refine (topologicalKrullDimAt_le_of_isOpen hU hpU).trans ?_
    rw [topologicalKrullDim_eq_iSup_of_isClosed
      (fun q : T ↦ (Subtype.val ⁻¹' zeroLocus (q.1 : Set A) : Set U))
      (fun q ↦ (isClosed_zeroLocus _).preimage continuous_subtype_val) ?_]
    · refine iSup_le fun q ↦ ?_
      rw [IsEmbedding.subtypeVal.topologicalKrullDim_preimage, Subtype.range_coe]
      refine (IsEmbedding.inclusion Set.inter_subset_left).isInducing.topologicalKrullDim_le.trans
        ?_
      have := q.2.1.1
      rw [Ideal.topologicalKrullDim_zeroLocus, ← hq q q.2.1 q.2.2]
      gcongr
      exact_mod_cast Ideal.height_map_quotientMk_le q.2.2
    · intro x
      obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ x.1.asIdeal)
      refine ⟨⟨q, hq, ?_⟩, (mem_zeroLocus _ _).2 hqx⟩
      by_contra h
      exact x.2 (Set.mem_biUnion (x := q) ⟨hq, h⟩ ((mem_zeroLocus _ _).2 hqx))
  · -- Some component `V(q)` through `p` has `ht (p ⧸ q) = ht p`, and its nonempty open part
    -- `V(q) ∩ U` has the dimension `ht p + dim (A ⧸ p)` of `V(q)`.
    obtain ⟨q, hq', hqp, hht⟩ := p.asIdeal.exists_mem_minimalPrimes_height_map_quotientMk_eq
    have := hq'.1.1
    have hV : IsIrreducible (zeroLocus (q : Set A)) :=
      (isIrreducible_zeroLocus_iff q).2 (by rwa [this.radical])
    rw [← hht, hq q hq' hqp, ← Ideal.topologicalKrullDim_zeroLocus,
      ← topologicalKrullDim_inter_eq_of_finiteType k hV (isClosed_zeroLocus _) U.2.1
        ⟨p, (mem_zeroLocus _ _).2 hqp, U.2.2⟩]
    calc _ = topologicalKrullDim ↥((Subtype.val : U.1 → _) ⁻¹' zeroLocus (q : Set A)) := by
          rw [IsEmbedding.subtypeVal.topologicalKrullDim_preimage, Subtype.range_coe]
      _ ≤ _ := topologicalKrullDim_subspace_le _ _

variable (k) in
/-- **Local dimension of an affine scheme of finite type over a field, via the stalk.** For a
finitely generated algebra `A` over a field `k`, the local Krull dimension of `Spec A` at a prime
`p` is `dim A_p + trdeg_k κ(p)`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_localization_add_trdeg {A : Type*} [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    topologicalKrullDimAt (PrimeSpectrum A) p = ringKrullDim (Localization.AtPrime p.asIdeal) +
      (Algebra.trdeg k p.asIdeal.ResidueField).toNat := by
  rw [topologicalKrullDimAt_eq_height_add_ringKrullDim_quotient k,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
    Ideal.ringKrullDim_quotient_eq_toNat_trdeg_residueField k]

end TauCeti
