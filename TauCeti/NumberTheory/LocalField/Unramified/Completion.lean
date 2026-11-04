/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Topology.Algebra.ValuativeRel.Completion
public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal
public import TauCeti.NumberTheory.LocalField.Unramified.ZHat
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension
public import TauCeti.RingTheory.Valuation.ValuativeRel.Frobenius
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup
public import TauCeti.Topology.Algebra.UniformRing
public import TauCeti.Topology.Algebra.ValuativeRel.Completion
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.Extension
import TauCeti.RingTheory.AlgebraicIndependent.Automorphism
import TauCeti.RingTheory.AlgebraicIndependent.TranscendenceBasis
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# The completed maximal unramified extension `Breve E`

Let `E` be a nonarchimedean local field with residue field of cardinality `q`. This file
constructs the completion `Breve E` of the maximal unramified extension `E^{ur}` of `E`, together
with its arithmetic Frobenius `σ`, and establishes its valuation-theoretic, residue-field,
Frobenius-fixed-point, and transcendence properties.

The maximal unramified extension is taken inside the algebraic closure,
`TauCeti.MaxUnramifiedCompletion.Unramified E = TauCeti.maximalUnramifiedExtension E
(AlgebraicClosure E)`. As an algebraic extension of `E` it carries the spectral norm, the unique
absolute value extending the normalized absolute value of `E`, and the corresponding valuative
relation and topology (`TauCeti.algebraicExtensionNormedField`). These are installed here as
instances, so that `TauCeti.MaxUnramifiedCompletion.Breve E` is simply the uniform completion
`UniformSpace.Completion (Unramified E)`.

Every finite subextension of `E^{ur}/E` is unramified, so the value-group map from `E` to `E^{ur}`
— and hence to `Breve E` — is surjective. Consequently `Breve E` is a complete discretely valued
field of rank one whose valuation ring `𝒪[Breve E]` is a Henselian, `𝓂[Breve E]`-adically complete
discrete valuation ring in which every uniformizer of `E` remains a uniformizer, and `E` embeds into
`Breve E` as a closed subfield. Every monic polynomial over `𝓀[E^{ur}]` descends to some finite
unramified level and splits in a higher finite unramified level, so `𝓀[E^{ur}]` and `𝓀[Breve E]`
are algebraically closed.

Every automorphism of `E^{ur}/E` preserves the valuation, so it is uniformly continuous and
extends uniquely to a continuous valuation-preserving `E`-algebra automorphism of `Breve E`. This
gives the faithful action `TauCeti.MaxUnramifiedCompletion.galAction` of `Gal(E^{ur}/E)` on
`Breve E` and the arithmetic Frobenius `TauCeti.MaxUnramifiedCompletion.frobenius` (`σ`). On
`𝒪[Breve E]`, `σ(x) ≡ x^q (mod 𝓂[Breve E])`; uniformizer-adic approximation shows that the fixed
ring of `σ` on `𝒪[Breve E]` is `𝒪[E]`, the fixed field of `σ` on `Breve E` is `E`, and the fixed
field of `σ^n` (`n ≠ 0`) is the unramified extension of degree `n`. Hence the elements of `Breve E`
algebraic over `E` are precisely `E^{ur}`. Diagonalizing the powers of `σ` on `𝒪[Breve E]` produces
transcendental elements in every characteristic; when `CharZero E`, solving `σ(y_ℓ) = ℓ^{q-1} y_ℓ`
for primes `ℓ` larger than the residue characteristic yields an infinite algebraically independent
family over `E`.

## Main definitions

* `TauCeti.MaxUnramifiedCompletion.Unramified E`: the maximal unramified extension `E^{ur}` of `E`
  inside its algebraic closure.
* `TauCeti.MaxUnramifiedCompletion.unramifiedFrobenius E`: the arithmetic Frobenius of `E^{ur}/E`.
* `TauCeti.MaxUnramifiedCompletion.Breve E`: the completion of `E^{ur}`.
* `TauCeti.MaxUnramifiedCompletion.galAction`: the action of `Gal(E^{ur}/E)` on `Breve E` by
  continuous extension.
* `TauCeti.MaxUnramifiedCompletion.frobenius E`: the arithmetic Frobenius `σ` of `Breve E`.
* `TauCeti.MaxUnramifiedCompletion.integerFrobenius E`: the restriction of `σ` to an `𝒪[E]`-algebra
  automorphism of `𝒪[Breve E]`.

## Main results

* `TauCeti.MaxUnramifiedCompletion.mapValueGroupWithZero_surjective`,
  `TauCeti.MaxUnramifiedCompletion.breveIsDiscrete`,
  `TauCeti.MaxUnramifiedCompletion.breveIsDiscreteValuationRing`,
  `TauCeti.MaxUnramifiedCompletion.breveIsAdicComplete`,
  `TauCeti.MaxUnramifiedCompletion.breveHenselianLocalRing`: `Breve E` has the same value group as
  `E`, so its valuation is discrete of rank one and `𝒪[Breve E]` is adically complete and
  Henselian.
* `TauCeti.MaxUnramifiedCompletion.isUniformizer_algebraMap`,
  `TauCeti.MaxUnramifiedCompletion.isClosedEmbedding_algebraMap`: uniformizers of `E` remain
  uniformizers of `Breve E`, and `algebraMap E (Breve E)` is a closed embedding.
* `TauCeti.MaxUnramifiedCompletion.residueField_isAlgClosed`: `𝓀[Breve E]` is algebraically closed.
* `TauCeti.MaxUnramifiedCompletion.frobenius_congr`: `σ(x) ≡ x^q (mod 𝓂[Breve E])` for
  `x ∈ 𝒪[Breve E]`.
* `TauCeti.MaxUnramifiedCompletion.fixedPoints_frobenius`,
  `TauCeti.MaxUnramifiedCompletion.fixedPoints_integerFrobenius`,
  `TauCeti.MaxUnramifiedCompletion.fixedPoints_frobenius_pow`: the fixed field of `σ` is `E`, its
  integral fixed ring is `𝒪[E]`, and the fixed field of `σ^n` (`n ≠ 0`) is `E_n`.
* `TauCeti.MaxUnramifiedCompletion.isAlgebraic_iff_mem_range_coe`,
  `TauCeti.MaxUnramifiedCompletion.not_isAlgebraic`: the algebraic elements of `Breve E` over `E`
  are `E^{ur}`, and `Breve E` is not algebraic over `E` in any characteristic.
* `TauCeti.MaxUnramifiedCompletion.transcendenceDegree_infinite`: when `CharZero E`, `Breve E` has
  infinite transcendence degree over `E`.

## References

* M. Chen, *Composantes connexes géométriques d'espaces de modules de groupes `p`-divisibles*,
  Ann. Sci. Éc. Norm. Supér. (4) 47 (2014), 723–764, Proposition 2.0.3.
* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997),
  §1.1.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
-/

public section
noncomputable section

open scoped Polynomial
open ValuativeRel UniformSpace

namespace TauCeti.MaxUnramifiedCompletion

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-! ### The maximal unramified extension and its valuation -/

/-- **The maximal unramified extension** `E^{ur}` of a nonarchimedean local field `E`, taken
inside the algebraic closure of `E`: the union of the unramified extensions of all finite degrees,
generated by the roots of the polynomials `X^{q^n} − X`. -/
abbrev Unramified : IntermediateField E (AlgebraicClosure E) :=
  maximalUnramifiedExtension E (AlgebraicClosure E)

/-- The normed-field structure on `E^{ur}` given by the spectral norm, the unique absolute value
extending the normalized absolute value of `E`. -/
instance unramifiedNormedField : NormedField (Unramified E) :=
  algebraicExtensionNormedField E (Unramified E)

/-- The spectral norm of `E^{ur}` is ultrametric. -/
instance unramifiedIsUltrametricDist : IsUltrametricDist (Unramified E) :=
  algebraicExtensionNormedField_isUltrametricDist E (Unramified E)

/-- The valuative relation of `E^{ur}`, comparing spectral norms. By
`TauCeti.algebraicExtensionValuativeRel_eq` it is the only valuative relation on `E^{ur}`
extending that of `E`. -/
instance unramifiedValuativeRel : ValuativeRel (Unramified E) :=
  algebraicExtensionValuativeRel E (Unramified E)

/-- The valuative relation of `E^{ur}` extends that of `E`. -/
instance unramifiedValuativeExtension : ValuativeExtension E (Unramified E) :=
  algebraicExtension_valuativeExtension E (Unramified E)

/-- The topology of the spectral norm of `E^{ur}` is its valuative topology. -/
instance unramifiedIsValuativeTopology : IsValuativeTopology (Unramified E) :=
  algebraicExtension_isValuativeTopology E (Unramified E)

/-- Multiplication by a scalar of `E` is uniformly continuous on `E^{ur}`; this is what makes the
completion of `E^{ur}` an `E`-algebra. -/
instance unramifiedUniformContinuousConstSMul : UniformContinuousConstSMul E (Unramified E) :=
  haveI := IsScalarTower.continuousConstSMul E (Unramified E) (Unramified E)
  uniformContinuousConstSMul_of_continuousConstSMul E (Unramified E)

/-- **The arithmetic Frobenius of `E^{ur}/E`**: the automorphism raising every root of every
polynomial `X^{q^n} − X`, `n ≠ 0`, to the `q`-th power (see
`TauCeti.maximalUnramifiedFrobenius_apply_of_pow_natCard_pow_eq_self`). -/
abbrev unramifiedFrobenius : Gal(Unramified E/E) :=
  maximalUnramifiedFrobenius E (AlgebraicClosure E)

/-! ### The completion `Breve E` -/

/-- **The completed maximal unramified extension** `Breve E` of a nonarchimedean local field `E`:
the uniform completion of `E^{ur}` for its spectral norm. It is a complete valued field
(`UniformSpace.Completion.valuativeRel`, `UniformSpace.Completion.isValuativeTopology`) and an
algebra over `E` and over `E^{ur}`, the latter embedding densely
(`UniformSpace.Completion.denseRange_coe`). -/
abbrev Breve : Type _ :=
  Completion (Unramified E)

/-- The valuative relation of `Breve E` extends that of `E`. -/
instance breveValuativeExtension : ValuativeExtension E (Breve E) :=
  ValuativeExtension.trans E (Unramified E) (Breve E)

/-- The valuation of `Breve E` is nontrivial. -/
instance breveIsNontrivial : IsNontrivial (Breve E) :=
  .of_valuativeExtension E

/-! ### The Galois action on `Breve E` -/

variable {E}

/-- **The action of `Gal(E^{ur}/E)` on `Breve E`.** Every automorphism `τ` of `E^{ur}/E` preserves
the valuation, hence is uniformly continuous, and `galAction τ` is its unique extension to a
continuous `E`-algebra automorphism of the completion `Breve E` (`galAction_coe`,
`continuous_galAction`). -/
def galAction : Gal(Unramified E/E) →* (Breve E ≃ₐ[E] Breve E) where
  toFun τ := Completion.mapAlgEquiv τ τ.continuous_of_valuativeExtension
    τ.symm.continuous_of_valuativeExtension
  map_one' := Completion.mapAlgEquiv_refl
  map_mul' τ τ' := Completion.mapAlgEquiv_trans τ' τ _ _ _ _

/-- The action of `τ` on `Breve E` is the extension of `τ` to the completion. -/
theorem galAction_apply (τ : Gal(Unramified E/E)) :
    galAction τ = Completion.mapAlgEquiv τ τ.continuous_of_valuativeExtension
      τ.symm.continuous_of_valuativeExtension :=
  (rfl)

/-- The action of a Galois automorphism `τ` on `Breve E` extends `τ`. -/
@[simp]
theorem galAction_coe (τ : Gal(Unramified E/E)) (x : Unramified E) :
    galAction τ (x : Breve E) = (τ x : Breve E) := by
  rw [galAction_apply, Completion.mapAlgEquiv_coe]

/-- The action of a Galois automorphism on `Breve E` is continuous. -/
@[fun_prop, continuity]
theorem continuous_galAction (τ : Gal(Unramified E/E)) : Continuous (galAction τ) := by
  rw [galAction_apply]
  exact Completion.continuous_mapAlgEquiv _ _ _

/-- The inverse of the action of `τ` on `Breve E` is the action of `τ⁻¹`. This is not a simp
lemma: its right side `galAction τ⁻¹` is rewritten by `map_inv` to `(galAction τ)⁻¹`, which
simp leaves stuck, whereas `galAction_symm_coe` evaluates `(galAction τ).symm` on `E^{ur}`. -/
theorem galAction_symm (τ : Gal(Unramified E/E)) : (galAction τ).symm = galAction τ⁻¹ := by
  rw [map_inv, AlgEquiv.aut_inv]

/-- The inverse of the action of a Galois automorphism `τ` on `Breve E` extends `τ⁻¹`. -/
@[simp]
theorem galAction_symm_coe (τ : Gal(Unramified E/E)) (x : Unramified E) :
    (galAction τ).symm (x : Breve E) = (τ.symm x : Breve E) := by
  rw [galAction_symm, galAction_coe, AlgEquiv.aut_inv]

/-- **Uniqueness of the extension.** A continuous map `Breve E → Breve E` which agrees with a Galois
automorphism `τ` on `E^{ur}` is the action of `τ`. -/
theorem eq_galAction_of_continuous (τ : Gal(Unramified E/E)) {f : Breve E → Breve E}
    (hf : Continuous f) (h : ∀ x : Unramified E, f x = (τ x : Breve E)) : f = galAction τ :=
  Completion.ext hf (continuous_galAction τ) fun x ↦ by rw [h, galAction_coe]

/-- **The Galois action on `Breve E` is faithful.** -/
theorem galAction_injective : Function.Injective (galAction (E := E)) := by
  refine (injective_iff_map_eq_one _).2 fun τ hτ ↦ AlgEquiv.ext fun x ↦ ?_
  simpa using congr($hτ (x : Breve E))

/-! ### Frobenius -/

variable (E) in
/-- **The arithmetic Frobenius `σ` of `Breve E`**: the continuous extension to `Breve E` of the
arithmetic Frobenius of `E^{ur}/E`. It raises every root of every polynomial `X^{q^n} − X` to the
`q`-th power (`frobenius_coe_of_pow_natCard_pow_eq_self`). -/
def frobenius : Breve E ≃ₐ[E] Breve E :=
  galAction (unramifiedFrobenius E)

variable (E) in
/-- Frobenius on `Breve E` is the action of the arithmetic Frobenius of `E^{ur}`. -/
theorem frobenius_eq_galAction : frobenius E = galAction (unramifiedFrobenius E) :=
  (rfl)

/-- Frobenius on `Breve E` extends the arithmetic Frobenius of `E^{ur}`. -/
@[simp]
theorem frobenius_coe (x : Unramified E) :
    frobenius E (x : Breve E) = (unramifiedFrobenius E x : Breve E) :=
  galAction_coe _ x

/-- Frobenius on `Breve E` is continuous. -/
@[fun_prop, continuity]
theorem continuous_frobenius : Continuous (frobenius E) :=
  continuous_galAction _

/-- The inverse of Frobenius on `Breve E` extends the inverse of the arithmetic Frobenius of
`E^{ur}`. -/
@[simp]
theorem frobenius_symm_coe (x : Unramified E) :
    (frobenius E).symm (x : Breve E) = ((unramifiedFrobenius E).symm x : Breve E) :=
  galAction_symm_coe _ x

/-- **The equation of Frobenius on `Breve E`.** Frobenius raises every root `ζ ∈ E^{ur}` of
`X^{q^n} − X`, for `n ≠ 0`, to the `q`-th power, where `q` is the cardinality of the residue
field of `E`. This pins the arithmetic normalization: geometric Frobenius would send `ζ` to
`ζ^{q^{n-1}}` instead. -/
theorem frobenius_coe_of_pow_natCard_pow_eq_self {ζ : Unramified E} {n : ℕ} (hn : n ≠ 0)
    (hζ : ζ ^ Nat.card 𝓀[E] ^ n = ζ) :
    frobenius E (ζ : Breve E) = (ζ : Breve E) ^ Nat.card 𝓀[E] := by
  rw [frobenius_coe, maximalUnramifiedFrobenius_apply_of_pow_natCard_pow_eq_self hn hζ]
  -- `Completion.coeRingHom` is the coercion `E^{ur} → Breve E` bundled as a ring homomorphism.
  exact map_pow Completion.coeRingHom ζ _

/-- **The equation of inverse Frobenius on `Breve E`.** For every root `ζ ∈ E^{ur}` of
`X^{q^n} − X`, `n ≠ 0`, the inverse of Frobenius sends `ζ^q` back to `ζ`. -/
theorem frobenius_symm_coe_pow_natCard_of_pow_natCard_pow_eq_self {ζ : Unramified E} {n : ℕ}
    (hn : n ≠ 0) (hζ : ζ ^ Nat.card 𝓀[E] ^ n = ζ) :
    (frobenius E).symm ((ζ : Breve E) ^ Nat.card 𝓀[E]) = ζ := by
  rw [← frobenius_coe_of_pow_natCard_pow_eq_self hn hζ, AlgEquiv.symm_apply_apply]

variable (E) in
/-- **Frobenius on `Breve E` is not the identity**, since the arithmetic Frobenius of `E^{ur}` has
infinite order and the Galois action on `Breve E` is faithful. -/
theorem frobenius_ne_one : frobenius E ≠ 1 := by
  rw [frobenius_eq_galAction, ← map_one galAction, galAction_injective.ne_iff]
  exact fun h ↦ not_isOfFinOrder_maximalUnramifiedFrobenius E (AlgebraicClosure E)
    (h ▸ .one : IsOfFinOrder (unramifiedFrobenius E))

/-! ### Value group, discreteness, uniformizers, and closed embedding -/

variable (E) in
/-- Every finite subextension of `E^{ur}/E` is unramified, so the map of value groups with zero
from `E` to `E^{ur}` is surjective. -/
theorem mapValueGroupWithZero_unramified_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Unramified E)) := by
  refine ValuativeExtension.mapValueGroupWithZero_surjective_iff.2 fun y ↦ ?_
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, by simp⟩
  obtain ⟨f, hf, hyf⟩ := mem_maximalUnramifiedExtension_iff.1 y.2
  let L := unramifiedExtension E (AlgebraicClosure E) f
  let _ := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let _ := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension hf
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  have hϖL : Irreducible (algebraMap 𝒪[E] 𝒪[L] ϖ) := IsUnramified.irreducible_algebraMap hϖ
  let yL : L := ⟨y.1, hyf⟩
  have hyL0 : yL ≠ 0 :=
    fun h ↦ hy0 (Subtype.ext (congrArg (Subtype.val : L → AlgebraicClosure E) h))
  obtain ⟨n, hn⟩ := exists_eq_valuation_zpow_of_irreducible hϖL
    (Units.mk0 (valuation L yL) ((valuation L).ne_zero_iff.2 hyL0))
  have hveqL : algebraMap E L ((ϖ : E) ^ n) =ᵥ yL := by
    refine ((valuation L).veq_iff_eq).2 ?_
    rw [map_zpow₀, ← coe_algebraMap_integerRing]
    simpa using hn.symm
  let ι : L →ₐ[E] Unramified E := IntermediateField.inclusion
    (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) f)
  let _ := ι.toAlgebra
  have : ValuativeExtension L (Unramified E) := ι.valuativeExtension
  have hy_eq : algebraMap L (Unramified E) yL = y := Subtype.ext rfl
  refine ⟨(ϖ : E) ^ n, ?_⟩
  rw [← ι.commutes, ← hy_eq]
  exact ValuativeExtension.veq_iff_veq.2 hveqL

variable (E) in
/-- The valuation of `E^{ur}` is nontrivial. -/
instance unramifiedIsNontrivial : IsNontrivial (Unramified E) :=
  .of_valuativeExtension E

variable (E) in
/-- The valuation of `E^{ur}` is discrete. -/
instance unramifiedIsDiscrete : IsDiscrete (Unramified E) :=
  .of_mapValueGroupWithZero_surjective (mapValueGroupWithZero_unramified_surjective E)

variable (E) in
/-- The valuation of `E^{ur}` has rank at most one. -/
instance unramifiedIsRankLeOne : IsRankLeOne (Unramified E) :=
  .of_mapValueGroupWithZero_surjective (mapValueGroupWithZero_unramified_surjective E)

variable (E) in
/-- The valuation ring `𝒪[E^{ur}]` is a discrete valuation ring. -/
instance unramifiedIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[Unramified E] :=
  ValuativeExtension.isDiscreteValuationRing_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_unramified_surjective E)

variable (E) in
/-- The map of value groups with zero from `E` to `Breve E` is surjective. -/
theorem mapValueGroupWithZero_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Breve E)) := by
  rw [← ValuativeExtension.mapValueGroupWithZero_comp E (Unramified E) (Breve E),
    MonoidWithZeroHom.coe_comp]
  exact (Completion.mapValueGroupWithZero_surjective (Unramified E)).comp
    (mapValueGroupWithZero_unramified_surjective E)

variable (E) in
/-- The valuation of `Breve E` is discrete. -/
instance breveIsDiscrete : IsDiscrete (Breve E) :=
  Completion.isDiscrete (Unramified E)

variable (E) in
/-- The valuation of `Breve E` has rank at most one. -/
instance breveIsRankLeOne : IsRankLeOne (Breve E) :=
  Completion.isRankLeOne (Unramified E)

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is a discrete valuation ring. -/
theorem breveIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[Breve E] :=
  Completion.isDiscreteValuationRing_integer (Unramified E)

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is `𝓂[Breve E]`-adically complete. -/
theorem breveIsAdicComplete : IsAdicComplete 𝓂[Breve E] 𝒪[Breve E] :=
  Completion.isAdicComplete_maximalIdeal_integer (Unramified E)

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is a Henselian local ring. -/
theorem breveHenselianLocalRing : HenselianLocalRing 𝒪[Breve E] :=
  inferInstance

variable (E) in
/-- The maximal ideal of `𝒪[E]` generates the maximal ideal of `𝒪[Breve E]`. -/
@[simp]
theorem map_maximalIdeal_breve :
    𝓂[E].map (algebraMap 𝒪[E] 𝒪[Breve E]) = 𝓂[Breve E] :=
  ValuativeExtension.map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_surjective E)

/-- An element of `𝒪[E]` is irreducible if and only if its image in `𝒪[Breve E]` is irreducible. -/
@[simp]
theorem irreducible_algebraMap_iff {ϖ : 𝒪[E]} :
    Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] ϖ) ↔ Irreducible ϖ :=
  ValuativeExtension.irreducible_algebraMap_iff_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_surjective E)

/-- A unit `π : Eˣ` is a uniformizer of `E` if and only if its image in `Breve E` is a uniformizer
for the canonical valuation of `Breve E`. -/
theorem isUniformizer_algebraMap_iff {π : Eˣ} :
    (valuation (Breve E)).IsUniformizer (algebraMap E (Breve E) (π : E)) ↔ IsUniformizer E π := by
  refine ⟨fun hπ ↦ ?_, fun hπ ↦ ?_⟩
  · obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    have hϖ₀B : Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] ϖ₀) :=
      irreducible_algebraMap_iff.2 hϖ₀
    have hvπ : valuation (Breve E) (algebraMap E (Breve E) (π : E)) =
        (Valuation.IsRankOneDiscrete.generator (valuation (Breve E)) :
          ValueGroupWithZero (Breve E)) :=
      Valuation.IsUniformizer.iff.1 hπ
    have hvϖ₀ : valuation (Breve E) (algebraMap E (Breve E) (ϖ₀ : E)) =
        (Valuation.IsRankOneDiscrete.generator (valuation (Breve E)) :
          ValueGroupWithZero (Breve E)) := by
      have hu := hϖ₀B.isUniformizer_valuation
      rwa [coe_algebraMap_integerRing, Valuation.IsUniformizer.iff] at hu
    have heqB : valuation (Breve E) (algebraMap E (Breve E) (π : E)) =
        valuation (Breve E) (algebraMap E (Breve E) (ϖ₀ : E)) :=
      hvπ.trans hvϖ₀.symm
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
      ← ValuativeExtension.mapValueGroupWithZero_valuation] at heqB
    have heqE : valuation E (π : E) = valuation E (ϖ₀ : E) :=
      (ValuativeExtension.mapValueGroupWithZero_strictMono (A := E) (B := Breve E)).injective heqB
    have hπ1 : valuation E (π : E) ≤ 1 := heqE.trans_le ϖ₀.2
    exact (isUniformizer_iff_exists_irreducible E π).2
      ⟨⟨(π : E), hπ1⟩, irreducible_of_valuation_eq hϖ₀ heqE, rfl⟩
  · obtain ⟨ϖ, hϖ, hϖπ⟩ := (isUniformizer_iff_exists_irreducible E π).1 hπ
    have hu := (irreducible_algebraMap_iff.2 hϖ).isUniformizer_valuation
    rwa [coe_algebraMap_integerRing, hϖπ] at hu

/-- **Every uniformizer of `E` remains a uniformizer of `Breve E`.** -/
theorem isUniformizer_algebraMap {π : Eˣ} (hπ : IsUniformizer E π) :
    (valuation (Breve E)).IsUniformizer (algebraMap E (Breve E) (π : E)) :=
  isUniformizer_algebraMap_iff.2 hπ

/-- No uniformizer `ϖ` of `𝒪[E]` is a square in `Breve E`: `Breve E` has ramification index `1`
over `E`. -/
theorem not_isSquare_algebraMap_of_irreducible {ϖ : 𝒪[E]} (hϖ : Irreducible ϖ) :
    ¬ IsSquare (algebraMap E (Breve E) (ϖ : E)) := by
  rintro ⟨z, hz⟩
  have hz1 : valuation (Breve E) z ≤ 1 := by
    refine (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 ?_
    rw [← map_pow, sq, ← hz, ← coe_algebraMap_integerRing]
    exact (algebraMap 𝒪[E] 𝒪[Breve E] ϖ).2
  let z₀ : 𝒪[Breve E] := ⟨z, hz1⟩
  have hsq : algebraMap 𝒪[E] 𝒪[Breve E] ϖ = z₀ * z₀ := by
    ext
    simpa [z₀, coe_algebraMap_integerRing] using hz
  have hirr : Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] ϖ) := irreducible_algebraMap_iff.2 hϖ
  rcases hirr.isUnit_or_isUnit hsq with hu | hu <;>
    exact hirr.not_isUnit (hsq ▸ hu.mul hu)

variable (E) in
/-- The canonical map `E → E^{ur}` is a topological embedding. -/
theorem isEmbedding_algebraMap_unramified :
    Topology.IsEmbedding (algebraMap E (Unramified E)) :=
  isEmbedding_algebraMap_of_coinitial E (Unramified E) fun _ hy ↦
    ValuativeExtension.exists_ne_zero_vle_of_mapValueGroupWithZero_surjective
      (mapValueGroupWithZero_unramified_surjective E) hy

variable (E) in
/-- **The base local field `E` embeds into `Breve E` as a closed subfield.** -/
theorem isClosedEmbedding_algebraMap :
    Topology.IsClosedEmbedding (algebraMap E (Breve E)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact isClosedEmbedding_algebraMap_of_coinitial E (Breve E) fun _ hy ↦
    ValuativeExtension.exists_ne_zero_vle_of_mapValueGroupWithZero_surjective
      (mapValueGroupWithZero_surjective E) hy

/-! ### Algebraic closure of the residue field -/

variable (E) in
/-- **The residue field of `E^{ur}` is algebraically closed.** Every monic polynomial over
`𝓀[E^{ur}]` lifts to some finite unramified level `E_N` and splits in a finite unramified level
`E_M` above `E_N`. -/
instance unramifiedResidueField_isAlgClosed : IsAlgClosed 𝓀[Unramified E] := by
  refine IsAlgClosed.of_exists_root _ fun p hp_mon hp_irr ↦ ?_
  choose c hc using fun i : ℕ ↦ IsLocalRing.residue_surjective (p.coeff i)
  choose f hf0 hcf using fun i : ℕ ↦
    mem_maximalUnramifiedExtension_iff.1 (c i : Unramified E).2
  let N : ℕ := ∏ i ∈ Finset.range (p.natDegree + 1), f i
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hf0 i
  let L := unramifiedExtension E (AlgebraicClosure E) N
  let _ := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let _ := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension hN0
  let ιL : L →ₐ[E] Unramified E := IntermediateField.inclusion
    (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) N)
  let _ := ιL.toAlgebra
  have : ValuativeExtension L (Unramified E) := ιL.valuativeExtension
  have hlifts : p ∈ Polynomial.lifts (algebraMap 𝓀[L] 𝓀[Unramified E]) := by
    refine (Polynomial.lifts_iff_coeff_lifts _).2 fun i ↦ ?_
    by_cases hi : p.natDegree < i
    · exact ⟨0, by rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
    · have hi' : i ∈ Finset.range (p.natDegree + 1) :=
        Finset.mem_range_succ_iff.2 (not_lt.1 hi)
      have hdvd : f i ∣ N := Finset.dvd_prod_of_mem f hi'
      have hmemL : ((c i : Unramified E) : AlgebraicClosure E) ∈ L :=
        unramifiedExtension_le_of_dvd hN0 hdvd (hcf i)
      let y : L := ⟨((c i : Unramified E) : AlgebraicClosure E), hmemL⟩
      have hy_eq : algebraMap L (Unramified E) y = (c i : Unramified E) := Subtype.ext rfl
      have hy1 : valuation L y ≤ 1 := by
        have hc1 : (c i : Unramified E) ≤ᵥ 1 := by
          have hc' : valuation (Unramified E) (c i : Unramified E) ≤ 1 := (c i).2
          rwa [← map_one (valuation (Unramified E)), ← (valuation (Unramified E)).vle_iff_le] at hc'
        rw [← map_one (valuation L), ← (valuation L).vle_iff_le]
        refine (ValuativeExtension.vle_iff_vle (A := L) (B := Unramified E)).1 ?_
        rwa [hy_eq, (algebraMap L (Unramified E)).map_one]
      let y₀ : 𝒪[L] := ⟨y, hy1⟩
      have hy₀ : algebraMap 𝒪[L] 𝒪[Unramified E] y₀ = c i := Subtype.ext hy_eq
      exact ⟨IsLocalRing.residue 𝒪[L] y₀,
        by rw [ValuativeExtension.residueField_algebraMap_residue, hy₀, hc]⟩
  obtain ⟨q₀, hq₀_map, hq₀_deg, _⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp_mon
  have hq₀_pos : 0 < q₀.natDegree := hq₀_deg ▸ hp_irr.natDegree_pos
  obtain ⟨r, hr_irr, hr_dvd⟩ := Polynomial.exists_irreducible_of_natDegree_pos hq₀_pos
  have hr_X : r ∣ Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X :=
    hr_irr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp dvd_rfl
  let M : ℕ := N * r.natDegree
  have hM0 : M ≠ 0 := mul_ne_zero hN0 hr_irr.natDegree_pos.ne'
  let LM := unramifiedExtension E (AlgebraicClosure E) M
  let _ := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) LM
  let _ := finiteIntermediateFieldTopology E (AlgebraicClosure E) LM
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) LM
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) LM
  have : IsUnramified E LM := isUnramified_unramifiedExtension hM0
  let ιLM : LM →ₐ[E] Unramified E := IntermediateField.inclusion
    (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) M)
  let _ := ιLM.toAlgebra
  have : ValuativeExtension LM (Unramified E) := ιLM.valuativeExtension
  have hcard : Nat.card 𝓀[LM] = Nat.card 𝓀[L] ^ r.natDegree := by
    rw [natCard_residueField E LM, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hM0, natCard_residueField E L,
      IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hN0, pow_mul]
  let _ : Fintype 𝓀[LM] := Fintype.ofFinite 𝓀[LM]
  have hsplit_LM : (Polynomial.X ^ Nat.card 𝓀[LM] - Polynomial.X : 𝓀[LM][X]).Splits := by
    have : Polynomial.IsSplittingField 𝓀[LM] 𝓀[LM]
        (Polynomial.X ^ Fintype.card 𝓀[LM] - Polynomial.X) :=
      FiniteField.isSplittingField_sub 𝓀[LM] 𝓀[LM]
    have hs := Polynomial.IsSplittingField.splits 𝓀[LM]
      (Polynomial.X ^ Fintype.card 𝓀[LM] - Polynomial.X : 𝓀[LM][X])
    rwa [Algebra.algebraMap_self, Polynomial.map_id, Fintype.card_eq_nat_card] at hs
  have hsplit_ur : (Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X :
      𝓀[Unramified E][X]).Splits := by
    rw [← hcard]
    simpa using hsplit_LM.map (algebraMap 𝓀[LM] 𝓀[Unramified E])
  have hr_dvd_ur : r.map (algebraMap 𝓀[L] 𝓀[Unramified E]) ∣
      (Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X : 𝓀[Unramified E][X]) := by
    simpa using Polynomial.map_dvd (algebraMap 𝓀[L] 𝓀[Unramified E]) hr_X
  have hX_ne : (Polynomial.X ^ Nat.card 𝓀[L] ^ r.natDegree - Polynomial.X :
      𝓀[Unramified E][X]) ≠ 0 :=
    Polynomial.X_pow_sub_X_ne_zero (Nat.one_lt_pow hr_irr.natDegree_pos.ne' Finite.one_lt_card)
  have hr_split : (r.map (algebraMap 𝓀[L] 𝓀[Unramified E])).Splits :=
    hsplit_ur.of_dvd hX_ne hr_dvd_ur
  have hr_deg : (r.map (algebraMap 𝓀[L] 𝓀[Unramified E])).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap 𝓀[L] 𝓀[Unramified E]).injective]
    exact (Polynomial.degree_pos_of_irreducible hr_irr).ne'
  obtain ⟨z, hz⟩ := hr_split.exists_eval_eq_zero hr_deg
  have hr_dvd_p : r.map (algebraMap 𝓀[L] 𝓀[Unramified E]) ∣ p :=
    hq₀_map ▸ Polynomial.map_dvd (algebraMap 𝓀[L] 𝓀[Unramified E]) hr_dvd
  exact ⟨z, Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hr_dvd_p hz⟩

variable (E) in
/-- **The residue field of `Breve E` is algebraically closed.** -/
instance residueField_isAlgClosed : IsAlgClosed 𝓀[Breve E] :=
  IsAlgClosed.of_ringEquiv 𝓀[Unramified E] 𝓀[Breve E]
    (Completion.residueFieldRingEquiv (Unramified E))

/-! ### Galois invariance of the valuation and Frobenius congruence -/

/-- The continuous action of `Gal(E^{ur}/E)` on `Breve E` preserves the canonical valuation. -/
@[simp]
theorem galAction_valuation_eq (τ : Gal(Unramified E/E)) (x : Breve E) :
    valuation (Breve E) (galAction τ x) = valuation (Breve E) x :=
  Completion.valuation_eq_of_continuous (continuous_galAction τ) (fun _ ↦ map_eq_zero _)
    (galAction_coe τ) (fun r ↦ τ.valuation_eq (K := E) r) x

/-- Frobenius on `Breve E` preserves the canonical valuation. -/
@[simp]
theorem frobenius_valuation_eq (x : Breve E) :
    valuation (Breve E) (frobenius E x) = valuation (Breve E) x :=
  galAction_valuation_eq _ x

/-- The action of `Gal(E^{ur}/E)` preserves the valuation ring `𝒪[Breve E]`. -/
@[simp]
theorem galAction_mem_integer_iff (τ : Gal(Unramified E/E)) (x : Breve E) :
    galAction τ x ∈ 𝒪[Breve E] ↔ x ∈ 𝒪[Breve E] := by
  simp only [Valuation.mem_integer_iff, galAction_valuation_eq]

/-- Frobenius on `Breve E` preserves the valuation ring `𝒪[Breve E]`. -/
@[simp]
theorem frobenius_mem_integer_iff (x : Breve E) :
    frobenius E x ∈ 𝒪[Breve E] ↔ x ∈ 𝒪[Breve E] :=
  galAction_mem_integer_iff _ x

variable (E) in
/-- **The arithmetic Frobenius on the ring of integers `𝒪[Breve E]`** as an `𝒪[E]`-algebra
automorphism. -/
def integerFrobenius : 𝒪[Breve E] ≃ₐ[𝒪[E]] 𝒪[Breve E] :=
  ValuativeExtension.integerAlgEquivOfMemInteger (frobenius E) frobenius_mem_integer_iff

@[simp]
theorem coe_integerFrobenius_apply (x : 𝒪[Breve E]) :
    (integerFrobenius E x : Breve E) = frobenius E (x : Breve E) :=
  ValuativeExtension.coe_integerAlgEquivOfMemInteger_apply (frobenius E) frobenius_mem_integer_iff x

@[simp]
theorem coe_integerFrobenius_symm_apply (x : 𝒪[Breve E]) :
    ((integerFrobenius E).symm x : Breve E) = (frobenius E).symm (x : Breve E) :=
  ValuativeExtension.coe_integerAlgEquivOfMemInteger_symm_apply (frobenius E)
    frobenius_mem_integer_iff x

theorem coe_integerFrobenius_pow_apply (n : ℕ) (x : 𝒪[Breve E]) :
    ((integerFrobenius E ^ n) x : Breve E) = (frobenius E ^ n) (x : Breve E) :=
  ValuativeExtension.coe_integerAlgEquivOfMemInteger_pow_apply (frobenius E)
    frobenius_mem_integer_iff n x

/-- **Congruence of Frobenius on `𝒪[E^{ur}]`.** For every integer `x` of `E^{ur}`,
`σ(x) ≡ x^q` modulo the maximal ideal. -/
theorem unramifiedFrobenius_congr {x : Unramified E} (hx : x ∈ 𝒪[Unramified E]) :
    valuation (Unramified E) (unramifiedFrobenius E x - x ^ Nat.card 𝓀[E]) < 1 := by
  obtain ⟨f, hf, hxf⟩ := mem_maximalUnramifiedExtension_iff.1 x.2
  let L := unramifiedExtension E (AlgebraicClosure E) f
  let _ := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let _ := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension hf
  let ι : L →ₐ[E] Unramified E := IntermediateField.inclusion
    (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) f)
  let _ := ι.toAlgebra
  have : ValuativeExtension L (Unramified E) := ι.valuativeExtension
  let xL : L := ⟨x.1, hxf⟩
  have hxL_eq : algebraMap L (Unramified E) xL = x := Subtype.ext rfl
  have hxL1 : valuation L xL ≤ 1 := by
    have hx' : x ≤ᵥ 1 := by
      have h1 : valuation (Unramified E) x ≤ 1 := hx
      rwa [← map_one (valuation (Unramified E)), ← (valuation (Unramified E)).vle_iff_le] at h1
    rw [← map_one (valuation L), ← (valuation L).vle_iff_le]
    refine (ValuativeExtension.vle_iff_vle (A := L) (B := Unramified E)).1 ?_
    rwa [hxL_eq, (algebraMap L (Unramified E)).map_one]
  have hsub_eq : unramifiedFrobenius E x - x ^ Nat.card 𝓀[E] =
      algebraMap L (Unramified E)
        (frobeniusAlgEquiv (K := E) (L := L) xL - xL ^ Nat.card 𝓀[E]) := by
    refine Subtype.ext ?_
    have hcoe := coe_maximalUnramifiedFrobenius_apply_of_mem (K := E)
      (Ω := AlgebraicClosure E) (f := f) hxf
    have hx_pair : (⟨x.1, unramifiedExtension_le_maximalUnramifiedExtension E
        (AlgebraicClosure E) f hxf⟩ : Unramified E) = x := Subtype.ext rfl
    rw [hx_pair] at hcoe
    simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow]
    rw [hcoe]
    rfl
  have hvL : valuation L (frobeniusAlgEquiv (K := E) (L := L) xL - xL ^ Nat.card 𝓀[E]) < 1 :=
    valuation_frobeniusAlgEquiv_sub_pow (K := E) (L := L) ⟨xL, hxL1⟩
  rw [hsub_eq, ← map_one (valuation (Unramified E)), ← (valuation (Unramified E)).vlt_iff_lt,
    ← (algebraMap L (Unramified E)).map_one]
  refine ValuativeExtension.vlt_iff_vlt.2 ?_
  rwa [(valuation L).vlt_iff_lt, map_one]

/-- **Congruence of Frobenius on `𝒪[Breve E]`.** For every integer `x` of `Breve E`,
`σ(x) − x^q` has valuation strictly less than `1`, i.e., lies in `𝓂[Breve E]`. -/
theorem frobenius_congr {x : Breve E} (hx : x ∈ 𝒪[Breve E]) :
    valuation (Breve E) (frobenius E x - x ^ Nat.card 𝓀[E]) < 1 := by
  have hcont : Continuous fun z : 𝒪[Breve E] ↦ frobenius E z.1 - z.1 ^ Nat.card 𝓀[E] :=
    (continuous_frobenius.comp continuous_subtype_val).sub
      (continuous_subtype_val.pow (Nat.card 𝓀[E]))
  refine Completion.valuation_lt_one_of_continuous_integer (K := Unramified E) hcont
    (fun y ↦ ?_) ⟨x, hx⟩
  have hcoe : ((algebraMap 𝒪[Unramified E] 𝒪[Breve E] y : 𝒪[Breve E]) : Breve E) =
      ((y : Unramified E) : Breve E) := by
    rw [coe_algebraMap_integerRing, Completion.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply]
  rw [hcoe, frobenius_coe]
  have hcast : ((unramifiedFrobenius E (y : Unramified E) : Unramified E) : Breve E) -
      ((y : Unramified E) : Breve E) ^ Nat.card 𝓀[E] =
      ((unramifiedFrobenius E (y : Unramified E) - (y : Unramified E) ^ Nat.card 𝓀[E] :
        Unramified E) : Breve E) :=
    ((Completion.coe_sub _ _).trans
      (congrArg _ (map_pow Completion.coeRingHom (y : Unramified E) _))).symm
  rw [hcast, ← map_one (valuation (Breve E)), ← (valuation (Breve E)).vlt_iff_lt,
    ← Completion.coe_one, Completion.coe_vlt_coe_iff, (valuation (Unramified E)).vlt_iff_lt,
    map_one]
  exact unramifiedFrobenius_congr y.2

/-- On `𝒪[Breve E]`, `integerFrobenius E x - x ^ q` lies in the maximal ideal `𝓂[Breve E]`. -/
theorem integerFrobenius_sub_pow_mem_maximalIdeal (x : 𝒪[Breve E]) :
    integerFrobenius E x - x ^ Nat.card 𝓀[E] ∈ 𝓂[Breve E] :=
  ValuativeExtension.integerAlgEquivOfMemInteger_sub_pow_mem_maximalIdeal
    (frobenius E) frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) x

/-- Reduction modulo `𝓂[Breve E]` intertwines `integerFrobenius E` with the `q`-th power map on
`𝓀[Breve E]`. -/
@[simp]
theorem residue_integerFrobenius (x : 𝒪[Breve E]) :
    IsLocalRing.residue 𝒪[Breve E] (integerFrobenius E x) =
      IsLocalRing.residue 𝒪[Breve E] x ^ Nat.card 𝓀[E] :=
  ValuativeExtension.residue_integerAlgEquivOfMemInteger_of_valuation_sub_pow_lt_one
    (frobenius E) frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) x

/-- Reduction modulo `𝓂[Breve E]` intertwines the `n`-th power of `integerFrobenius E` with the
`q^n`-th power map on `𝓀[Breve E]`. -/
theorem residue_integerFrobenius_pow (n : ℕ) (x : 𝒪[Breve E]) :
    IsLocalRing.residue 𝒪[Breve E] ((integerFrobenius E ^ n) x) =
      IsLocalRing.residue 𝒪[Breve E] x ^ Nat.card 𝓀[E] ^ n :=
  ValuativeExtension.residue_integerAlgEquivOfMemInteger_pow_of_valuation_sub_pow_lt_one
    (frobenius E) frobenius_mem_integer_iff (fun _ hz ↦ frobenius_congr hz) n x

/-- For every `n : ℕ` and `x ∈ 𝒪[Breve E]`, `(σ ^ n)(x) ≡ x^{q^n} (mod 𝓂[Breve E])`. -/
theorem frobenius_pow_congr (n : ℕ) {x : Breve E} (hx : x ∈ 𝒪[Breve E]) :
    valuation (Breve E) ((frobenius E ^ n) x - x ^ Nat.card 𝓀[E] ^ n) < 1 :=
  ValuativeExtension.valuation_pow_sub_pow_lt_one_of_valuation_sub_pow_lt_one
    (frobenius E) Nat.card_pos.ne' (fun _ hz ↦ frobenius_congr hz) n hx

/-! ### Fixed points of Frobenius -/

/-- An element of `Breve E` is fixed by Frobenius if and only if it belongs to the image of `E`. -/
theorem frobenius_eq_self_iff {x : Breve E} :
    frobenius E x = x ↔ x ∈ Set.range (algebraMap E (Breve E)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one
    (mapValueGroupWithZero_surjective E) (frobenius E) (fun _ hz ↦ frobenius_congr hz) x

variable (E) in
/-- **The fixed field of Frobenius on `Breve E` is the base local field `E`.** -/
theorem fixedPoints_frobenius :
    {x : Breve E | frobenius E x = x} = Set.range (algebraMap E (Breve E)) :=
  Set.ext fun _ ↦ frobenius_eq_self_iff

variable (E) in
/-- **The fixed ring of Frobenius on `𝒪[Breve E]` is `𝒪[E]`.** -/
theorem fixedPoints_integerFrobenius :
    {x : 𝒪[Breve E] | integerFrobenius E x = x} = Set.range (algebraMap 𝒪[E] 𝒪[Breve E]) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · have hxB : frobenius E (x : Breve E) = (x : Breve E) :=
      (coe_integerFrobenius_apply x).symm.trans (congrArg Subtype.val hx)
    obtain ⟨c, hc⟩ := frobenius_eq_self_iff.1 hxB
    have hc1 : valuation E c ≤ 1 := by
      have hx' : (x : Breve E) ≤ᵥ 1 := by
        have h1 : valuation (Breve E) (x : Breve E) ≤ 1 := x.2
        rwa [← map_one (valuation (Breve E)), ← (valuation (Breve E)).vle_iff_le] at h1
      rw [← map_one (valuation E), ← (valuation E).vle_iff_le]
      refine (ValuativeExtension.vle_iff_vle (A := E) (B := Breve E)).1 ?_
      rwa [hc, (algebraMap E (Breve E)).map_one]
    exact ⟨⟨c, hc1⟩, Subtype.ext (by rw [coe_algebraMap_integerRing, hc])⟩
  · rintro ⟨c, rfl⟩
    exact (integerFrobenius E).commutes c

/-- The `n`-th power of Frobenius on `Breve E` extends the `n`-th power of the arithmetic
Frobenius of `E^{ur}`. -/
@[simp]
theorem frobenius_pow_coe (n : ℕ) (x : Unramified E) :
    (frobenius E ^ n) (x : Breve E) = ((unramifiedFrobenius E ^ n) x : Breve E) := by
  rw [frobenius_eq_galAction, ← map_pow, galAction_coe]

/-- **The fixed field of `σ^n` (`n ≠ 0`) on `Breve E` is the unramified extension `E_n` of degree
`n`.** -/
theorem fixedPoints_frobenius_pow {n : ℕ} (hn : n ≠ 0) :
    {x : Breve E | (frobenius E ^ n) x = x} =
      Set.range ((↑) ∘ IntermediateField.inclusion
        (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n)) := by
  let L := unramifiedExtension E (AlgebraicClosure E) n
  let _ := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let _ := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension hn
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  let ιU : L →ₐ[E] Unramified E := IntermediateField.inclusion
    (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) n)
  let _ : Algebra L (Unramified E) := ιU.toAlgebra
  have : IsScalarTower E L (Unramified E) := .of_algebraMap_eq fun r ↦ (ιU.commutes r).symm
  have : ValuativeExtension L (Unramified E) := ιU.valuativeExtension
  have : ContinuousConstSMul L (Unramified E) :=
    IsScalarTower.continuousConstSMul L (Unramified E) (Unramified E)
  have : UniformContinuousConstSMul L (Unramified E) :=
    uniformContinuousConstSMul_of_continuousConstSMul L (Unramified E)
  have : ValuativeExtension L (Breve E) := ValuativeExtension.trans L (Unramified E) (Breve E)
  have hsurjL : Function.Surjective (ValuativeExtension.mapValueGroupWithZero L (Breve E)) := by
    have hcomp : Function.Surjective
        ((ValuativeExtension.mapValueGroupWithZero L (Breve E)).comp
          (ValuativeExtension.mapValueGroupWithZero E L)) := by
      rw [ValuativeExtension.mapValueGroupWithZero_comp E L (Breve E)]
      exact mapValueGroupWithZero_surjective E
    rw [MonoidWithZeroHom.coe_comp] at hcomp
    exact hcomp.of_comp
  have hfixL : ∀ z : L,
      (frobenius E ^ n) (algebraMap L (Breve E) z) = algebraMap L (Breve E) z := by
    intro z
    have hord : orderOf (frobeniusAlgEquiv (K := E) (L := L)) = n := by
      rw [orderOf_frobeniusAlgEquiv, IsUnramified.inertiaDegree_eq_finrank,
        finrank_unramifiedExtension hn]
    have hpowL : (frobeniusAlgEquiv (K := E) (L := L) ^ n) z = z := by
      have h1 : frobeniusAlgEquiv (K := E) (L := L) ^
          orderOf (frobeniusAlgEquiv (K := E) (L := L)) = 1 :=
        pow_orderOf_eq_one _
      rw [hord] at h1
      exact congr($h1 z)
    have hcoe := coe_maximalUnramifiedFrobenius_zpow_apply_of_mem (K := E)
      (Ω := AlgebraicClosure E) (f := n) (n : ℤ) z.2
    rw [zpow_natCast, zpow_natCast, hpowL] at hcoe
    have hU : (unramifiedFrobenius E ^ n) (ιU z) = ιU z := Subtype.ext hcoe
    have hcoeB : algebraMap L (Breve E) z = (ιU z : Breve E) := rfl
    rw [hcoeB, frobenius_pow_coe, hU]
  let σL : Breve E ≃ₐ[L] Breve E :=
    { (frobenius E ^ n).toRingEquiv with commutes' := hfixL }
  have hcardL : Nat.card 𝓀[L] = Nat.card 𝓀[E] ^ n := by
    rw [natCard_residueField E L, IsUnramified.inertiaDegree_eq_finrank,
      finrank_unramifiedExtension hn]
  have hcongrL : ∀ z : Breve E, z ∈ 𝒪[Breve E] →
      valuation (Breve E) (σL z - z ^ Nat.card 𝓀[L]) < 1 := by
    intro z hz
    rw [hcardL]
    exact frobenius_pow_congr n hz
  ext x
  exact ValuativeExtension.eq_self_iff_mem_range_algebraMap_of_valuation_sub_pow_lt_one
    hsurjL σL hcongrL x

/-! ### Algebraic elements and transcendence of `Breve E` -/

/-- **An element of `Breve E` is algebraic over `E` if and only if it belongs to `E^{ur}`.** -/
theorem isAlgebraic_iff_mem_range_coe {x : Breve E} :
    IsAlgebraic E x ↔ x ∈ Set.range ((↑) : Unramified E → Breve E) := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨n, hn, hnx⟩ := hx.exists_pow_apply_eq_self_of_algEquiv (frobenius E)
    have hmem : x ∈ {z : Breve E | (frobenius E ^ n) z = z} := hnx
    rw [fixedPoints_frobenius_pow hn] at hmem
    obtain ⟨z, rfl⟩ := hmem
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp0, hpy⟩ := Algebra.IsAlgebraic.isAlgebraic (R := E) y
    refine ⟨p, hp0, ?_⟩
    have hcoe : (y : Breve E) = IsScalarTower.toAlgHom E (Unramified E) (Breve E) y := rfl
    rw [hcoe, Polynomial.aeval_algHom_apply, hpy, map_zero]

variable (E) in
/-- **`Breve E` contains elements transcendental over `E` in every characteristic.** -/
theorem exists_transcendental : ∃ x : Breve E, Transcendental E x :=
  ValuativeExtension.exists_transcendental_of_valuation_sub_pow_lt_one
    (mapValueGroupWithZero_surjective E) (frobenius E) Finite.one_lt_card
    (fun _ hz ↦ frobenius_congr hz)

variable (E) in
/-- **`Breve E` is not algebraic over `E` in any characteristic.** -/
theorem not_isAlgebraic : ¬ Algebra.IsAlgebraic E (Breve E) := by
  obtain ⟨x, hx⟩ := exists_transcendental E
  exact fun h ↦ hx (h.isAlgebraic x)

/-- For every principal unit `u ≡ 1 (mod 𝓂[E])`, the Frobenius eigenvector equation
`σ(y) = u y` admits a nonzero solution in `Breve E`. -/
theorem exists_frobenius_eq_mul_of_sub_one_mem {u : 𝒪[E]} (hu : u - 1 ∈ 𝓂[E]) :
    ∃ y : Breve E, y ≠ 0 ∧ frobenius E y = algebraMap E (Breve E) (u : E) * y :=
  ValuativeExtension.exists_apply_eq_mul_of_sub_one_mem_maximalIdeal
    (mapValueGroupWithZero_surjective E) (frobenius E) Finite.one_lt_card
    (fun _ hz ↦ frobenius_congr hz) hu

variable (E) in
/-- **In characteristic zero, `Breve E` has infinite transcendence degree over `E`.** Following
[Chen], Proposition 2.0.3, solving `σ(y_ℓ) = ℓ^{q-1} y_ℓ` for primes `ℓ` strictly exceeding the
residue characteristic yields an infinite family of nonzero `σ`-eigenvectors with multiplicatively
independent eigenvalues in `E`. -/
theorem transcendenceDegree_infinite [CharZero E] :
    Cardinal.aleph0 ≤ Algebra.trdeg E (Breve E) := by
  classical
  let p : ℕ := ringChar 𝓀[E]
  let _ : Fintype 𝓀[E] := Fintype.ofFinite 𝓀[E]
  let q : ℕ := Nat.card 𝓀[E]
  have hq1 : 1 < q := Finite.one_lt_card
  have hq_sub : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq1
  let ι := {ℓ : ℕ // Nat.Prime ℓ ∧ p < ℓ}
  have hinf : Infinite ι := by
    rw [← not_finite_iff_infinite]
    intro hfin
    let _ : Fintype ι := Fintype.ofFinite ι
    let B : ℕ := max p (Finset.univ.sup fun x : ι ↦ x.1) + 1
    obtain ⟨ℓ, hBℓ, hℓprime⟩ := Nat.exists_infinite_primes B
    have hpℓ : p < ℓ := (Nat.le_max_left _ _).trans_lt ((Nat.lt_succ_self _).trans_le hBℓ)
    have hle : ℓ ≤ Finset.univ.sup fun x : ι ↦ x.1 :=
      Finset.le_sup (f := fun x : ι ↦ x.1) (Finset.mem_univ (⟨ℓ, hℓprime, hpℓ⟩ : ι))
    have : B ≤ Finset.univ.sup fun x : ι ↦ x.1 := hBℓ.trans hle
    have : max p (Finset.univ.sup fun x : ι ↦ x.1) < Finset.univ.sup fun x : ι ↦ x.1 :=
      (Nat.lt_succ_self _).trans_le this
    exact (Nat.le_max_right p _).not_gt this
  let u₀ : ι → 𝒪[E] := fun ℓ ↦ (ℓ.1 : 𝒪[E]) ^ (q - 1)
  have hu₀_mem : ∀ ℓ : ι, u₀ ℓ - 1 ∈ 𝓂[E] := by
    intro ℓ
    let ψ := IsLocalRing.residue 𝒪[E]
    refine (IsLocalRing.residue_eq_zero_iff _).1 ?_
    have hp_prime : Nat.Prime p := CharP.char_is_prime 𝓀[E] p
    have hℓ_ne : (ℓ.1 : 𝓀[E]) ≠ 0 := by
      intro h0
      have hdvd : p ∣ ℓ.1 := (CharP.cast_eq_zero_iff 𝓀[E] p ℓ.1).1 h0
      rcases (Nat.dvd_prime ℓ.2.1).1 hdvd with hp1 | hp_eq
      · exact hp_prime.ne_one hp1
      · exact ℓ.2.2.ne hp_eq
    rw [ψ.map_sub, ψ.map_one, ψ.map_pow, map_natCast, sub_eq_zero]
    have hcard_eq : q = Fintype.card 𝓀[E] := Nat.card_eq_fintype_card
    rw [hcard_eq]
    exact FiniteField.pow_card_sub_one_eq_one (ℓ.1 : 𝓀[E]) hℓ_ne
  choose y hy0 hy_frob using fun ℓ : ι ↦ exists_frobenius_eq_mul_of_sub_one_mem (hu₀_mem ℓ)
  let u : ι → E := fun ℓ ↦ ((u₀ ℓ : 𝒪[E]) : E)
  have hσ_y : ∀ ℓ : ι, (frobenius E).toAlgHom (y ℓ) = algebraMap E (Breve E) (u ℓ) * y ℓ :=
    fun ℓ ↦ hy_frob ℓ
  have hu_inj : Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun ℓ k ↦ u ℓ ^ k := by
    intro d₁ d₂ hd
    dsimp only at hd
    have hcast : ∀ d : ι →₀ ℕ,
        (d.prod fun ℓ k ↦ u ℓ ^ k) =
          ((d.prod fun ℓ k ↦ ℓ.1 ^ ((q - 1) * k) : ℕ) : E) := by
      intro d
      have hhom := map_finsuppProd (Nat.castRingHom E) d fun ℓ k ↦ ℓ.1 ^ ((q - 1) * k)
      simp only [Nat.coe_castRingHom] at hhom
      refine (Finsupp.prod_congr fun ℓ _ ↦ ?_).trans hhom.symm
      simp only [u, u₀, pow_mul]
      push_cast
      rfl
    rw [hcast, hcast] at hd
    have hnat : (d₁.prod fun ℓ k ↦ ℓ.1 ^ ((q - 1) * k)) =
        d₂.prod fun ℓ k ↦ ℓ.1 ^ ((q - 1) * k) := Nat.cast_injective hd
    have hfact : ∀ (d : ι →₀ ℕ) (ℓ₀ : ι),
        (d.prod fun ℓ k ↦ ℓ.1 ^ ((q - 1) * k)).factorization ℓ₀.1 = (q - 1) * d ℓ₀ := by
      intro d ℓ₀
      rw [Finsupp.prod, Nat.factorization_prod_apply fun ℓ _ ↦ pow_ne_zero _ ℓ.2.1.ne_zero]
      have hsum : (∑ ℓ ∈ d.support, (ℓ.1 ^ ((q - 1) * d ℓ)).factorization ℓ₀.1) =
          ∑ ℓ ∈ d.support, if ℓ = ℓ₀ then (q - 1) * d ℓ else 0 := by
        refine Finset.sum_congr rfl fun ℓ _ ↦ ?_
        rw [ℓ.2.1.factorization_pow, Finsupp.single_apply]
        by_cases hℓ : ℓ = ℓ₀
        · subst hℓ
          simp
        · have hval : ℓ.1 ≠ ℓ₀.1 := fun hv ↦ hℓ (Subtype.ext hv)
          simp [hℓ, hval]
      rw [hsum, Finset.sum_ite_eq']
      by_cases hmem : ℓ₀ ∈ d.support
      · simp [hmem]
      · simp [hmem, Finsupp.notMem_support_iff.1 hmem]
    ext ℓ₀
    have heq : (q - 1) * d₁ ℓ₀ = (q - 1) * d₂ ℓ₀ := by
      rw [← hfact d₁ ℓ₀, ← hfact d₂ ℓ₀, hnat]
    exact mul_left_cancel₀ hq_sub heq
  have hind : AlgebraicIndependent E y :=
    algebraicIndependent_of_algHom_eigenvectors (frobenius E).toAlgHom hy0 hσ_y hu_inj
  have hle : Cardinal.lift.{_, 0} (Cardinal.mk ι) ≤ Algebra.trdeg E (Breve E) := by
    simpa only [Cardinal.lift_uzero] using hind.lift_cardinalMk_le_trdeg
  calc Cardinal.aleph0
      = Cardinal.lift.{_, 0} Cardinal.aleph0 := Cardinal.lift_aleph0.symm
    _ ≤ Cardinal.lift.{_, 0} (Cardinal.mk ι) := Cardinal.lift_le.2 (Cardinal.aleph0_le_mk ι)
    _ ≤ Algebra.trdeg E (Breve E) := hle

variable (E) in
/-- **In characteristic zero, `Breve E` has infinite transcendence degree over `E^{ur}`.** -/
theorem transcendenceDegree_unramified_infinite [CharZero E] :
    Cardinal.aleph0 ≤ Algebra.trdeg (Unramified E) (Breve E) := by
  rw [trdeg_eq_of_isAlgebraic_base (R := E) (S := Unramified E) (A := Breve E)]
  exact transcendenceDegree_infinite E

end TauCeti.MaxUnramifiedCompletion
