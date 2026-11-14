/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Completion
public import TauCeti.Algebra.Lie.Current.Derivation
public import TauCeti.Algebra.Lie.Derivation.Completion

/-!
# Vector-field derivations on completed current enveloping algebras

Every Laurent vector field `h d/dt` extends uniquely to a continuous derivation of the completed
level enveloping algebra, and continuous derivations of the completion are determined by their
values on the current mode generators `x ⊗ tᵐ`. Positive-order fields additionally preserve every
stage kernel. In particular the Witt vector field `t^{m+1} d/dt` sends `x_k` to `k x_{m+k}`, and
the degree derivation `t d/dt` acts on `x_n` by `n x_n`, also inside the completion. The extensions
commute with the completed level comparison, including at level zero.

The extension uses the complete topological algebra, not ring structures on the left-module
quotients. The degree derivation is the operator implemented by the Sugawara degree element
when that element exists; no such innerness is assumed here.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §4.3.9.
-/

public section

noncomputable section

open Topology Filter
open scoped LaurentSeries
open TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "U" => CentralQuotient R (centralElement c) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "i" => toCompletedEnveloping Φ hΦ hΦs a

-- Only the proof of extension uses a topology on the uncompleted algebra. Give it the
-- uniformity pulled back from the completion; injectivity of its canonical map is unnecessary.
private abbrev completionUniformSpace : UniformSpace U := UniformSpace.comap i inferInstance
attribute [local instance] completionUniformSpace

private instance : IsUniformAddGroup U := IsUniformAddGroup.comap i

private theorem uniformInducing_toCompleted : IsUniformInducing i :=
  isUniformInducing_iff_uniformSpace.mpr rfl

private theorem uniformContinuous_vectorField (h : R⸨X⸩) :
    UniformContinuous fun b : U ↦ i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h :
      Module.End R U) b) := by
  have hb := (hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).uniformity_of_nhds_zero
  have hs := hb.comap (fun p : U × U ↦ (i p.1, i p.2))
  obtain ⟨P, hP⟩ : ∃ P : ℤ, (P : WithTop ℤ) ≤ h.orderTop := by
    cases h.orderTop with
    | top => exact ⟨0, le_top⟩
    | coe P => exact ⟨P, le_rfl⟩
  refine (hs.tendsto_iff hb).mpr fun n _ ↦ ?_
  let m := (max (n : ℤ) (n + 1 - P)).toNat
  refine ⟨m, trivial, fun p hp ↦ ?_⟩
  have hp' : p.2 - p.1 ∈ orderLeftIdeal Φ hΦ hΦs a m := by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe, ← map_sub,
      toCompletedEnveloping_mem_completedOrderLeftIdeal_iff] using hp
  simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, ← map_sub,
    toCompletedEnveloping_mem_completedOrderLeftIdeal_iff] using
      orderLeftIdeal_antitone Φ hΦ hΦs a
        (by dsimp [m]; have := Int.self_le_toNat (max (n : ℤ) (n + 1 - P)); omega)
        (vectorFieldEnvelopingDerivation_mem_orderLeftIdeal_min Φ hΦ hΦs a hP hp')

/-- The continuous extension of the Laurent vector field `h d/dt` to the completed level
enveloping algebra. No order restriction on `h` is needed for continuity. -/
def vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩) :
    derivationLieAlgebra R Û :=
  derivationLieAlgebra.extend (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h) (i).toNonUnitalAlgHom
    (uniformInducing_toCompleted Φ hΦ hΦs a)
    (denseRange_toCompletedEnveloping Φ hΦ hΦs a)
    (uniformContinuous_vectorField Φ hΦ hΦs a h)

-- Record the bundled definition explicitly so extension lemmas need not unfold it.
private theorem coe_vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û) =
      (derivationLieAlgebra.extend (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h)
        (i).toNonUnitalAlgHom (uniformInducing_toCompleted Φ hΦ hΦs a)
        (denseRange_toCompletedEnveloping Φ hΦ hΦs a)
        (uniformContinuous_vectorField Φ hΦ hΦs a h) : Module.End R Û) := rfl

private theorem coe_toCompletedEnveloping_toNonUnitalAlgHom :
    ((i).toNonUnitalAlgHom : U → Û) = i := rfl

/-- The completed vector field extends the vector field on the uncompleted enveloping algebra.
The left side uses the simp normal form of the canonical map into the completion. -/
@[simp]
theorem vectorFieldCompletedEnvelopingDerivation_toLimQuotients (h : R⸨X⸩) (b : U) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û)
        (ModuleTower.toLimQuotients _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a) b) =
      i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R U) b) := by
  rw [← coe_toCompletedEnveloping, coe_vectorFieldCompletedEnvelopingDerivation]
  exact derivationLieAlgebra.extend_apply ..

/-- Completed vector fields are continuous for the current-order topology. -/
theorem continuous_vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩) :
    Continuous (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û) := by
  rw [coe_vectorFieldCompletedEnvelopingDerivation]
  exact derivationLieAlgebra.continuous_extend _ _ _ _ _

/-- Uniqueness of the continuous extension, even among maps not assumed to be derivations. -/
theorem eq_vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩) {f : Û → Û} (hf : Continuous f)
    (he : ∀ b : U, f (i b) =
      i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R U) b)) :
    f = (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û) := by
  rw [coe_vectorFieldCompletedEnvelopingDerivation]
  apply derivationLieAlgebra.eq_extend _ _ _ _ _ hf
  simpa only [coe_toCompletedEnveloping_toNonUnitalAlgHom] using he

/-- The degree derivation on completed current generators is `x_n ↦ n x_n`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_envelopingι_single_tmul
    (n : ℤ) (r : R) (x : L) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End R Û)
        (i (envelopingι c a (HahnSeries.single n r ⊗ₜ[R] x))) =
      n • i (envelopingι c a (HahnSeries.single n r ⊗ₜ[R] x)) := by
  simp only [coe_toCompletedEnveloping, vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
    vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul, map_zsmul]

/-- Completed vector fields of order at least one preserve every kernel of a current-order
stage projection. -/
theorem vectorFieldCompletedEnvelopingDerivation_mem_completedOrderLeftIdeal (h : R⸨X⸩)
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û) x ∈
      completedOrderLeftIdeal Φ hΦ hΦs a n := by
  let D := (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h : Module.End R Û)
  have hc : Continuous D := continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h
  have hd := denseRange_toCompletedEnveloping Φ hΦ hΦs a
  by_contra hbad
  obtain ⟨b, hb, hDb⟩ := hd.exists_mem_open
    ((isOpen_completedOrderLeftIdeal Φ hΦ hΦs a n).inter
      ((isClosed_completedOrderLeftIdeal Φ hΦ hΦs a n).isOpen_compl.preimage hc))
    ⟨x, hx, hbad⟩
  have hb' : b ∈ orderLeftIdeal Φ hΦ hΦs a n := by
    exact toCompletedEnveloping_mem_completedOrderLeftIdeal_iff.mp hb
  apply hDb
  simpa only [D, SetLike.mem_coe, coe_toCompletedEnveloping,
    vectorFieldCompletedEnvelopingDerivation_toLimQuotients] using
    (toCompletedEnveloping_mem_completedOrderLeftIdeal_iff.mpr
      (vectorFieldEnvelopingDerivation_mem_orderLeftIdeal Φ hΦ hΦs a hh hb'))

/-- Two continuous derivations of the completed level enveloping algebra agree as soon as they
agree on the current mode generators `x ⊗ tᵐ`. -/
theorem derivationLieAlgebra_ext_single {D E : derivationLieAlgebra R Û}
    (hD : Continuous (D : Module.End R Û)) (hE : Continuous (E : Module.End R Û))
    (h : ∀ (m : ℤ) (x : L),
      (D : Module.End R Û) (i (envelopingι c a (HahnSeries.single m (1 : R) ⊗ₜ[R] x))) =
        (E : Module.End R Û) (i (envelopingι c a (HahnSeries.single m (1 : R) ⊗ₜ[R] x)))) :
    D = E := by
  let S : Subalgebra R Û :=
    { carrier := {y | (D : Module.End R Û) y = (E : Module.End R Û) y}
      mul_mem' {x y} hx hy := by
        rw [Set.mem_ofPred_eq] at hx hy ⊢
        rw [derivationLieAlgebra.leibniz, derivationLieAlgebra.leibniz, hx, hy]
      one_mem' := by simp
      add_mem' {x y} hx hy := by
        rw [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_add, map_add, hx, hy]
      zero_mem' := by simp
      algebraMap_mem' r := by simp }
  have hpoly (p : LieAlgebra.loopAlgebra R ℤ L) :
      i (envelopingι c a (ofLoop R L p)) ∈ S := by
    obtain ⟨v, rfl⟩ := (LieAlgebra.LoopAlgebra.toFinsupp R ℤ L).symm.surjective p
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simpa only [map_add] using S.add_mem hv hw
    | single m x =>
      rw [LieAlgebra.LoopAlgebra.toFinsupp_symm_single, ofLoop_tmul,
        LaurentPolynomial.toLaurentSeries_single]
      exact h m x
  have hcur (u : currentAlgebra R L) : i (envelopingι c a u) ∈ S :=
    (isClosed_eq hD hE).mem_of_tendsto
      (tendsto_toCompletedEnveloping_envelopingι_ofLoop_trunc Φ hΦ hΦs a u)
      (Filter.Eventually.of_forall fun N ↦ hpoly _)
  have hU : (⊤ : Subalgebra R U) ≤ S.comap i := by
    rw [← LieAlgebra.ofTwoCocycle.adjoin_range_envelopingι c a, Algebra.adjoin_le_iff]
    rintro _ ⟨u, rfl⟩
    exact hcur u
  refine derivationLieAlgebra.ext fun x ↦ ?_
  induction x using (denseRange_toCompletedEnveloping Φ hΦ hΦs a).induction_on with
  | hp => exact isClosed_eq hD hE
  | ih b => exact hU Algebra.mem_top

/-- The completed vector field of `-h` is the negative of the completed vector field of `h`. -/
@[simp]
theorem vectorFieldCompletedEnvelopingDerivation_neg (h : R⸨X⸩) :
    vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (-h) =
      -vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h := by
  have hneg : Continuous ((-vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h :
      derivationLieAlgebra R Û) : Module.End R Û) := by
    rw [NegMemClass.coe_neg]
    exact (continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h).neg
  refine derivationLieAlgebra_ext_single Φ hΦ hΦs a
    (continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (-h)) hneg fun m x ↦ ?_
  simp only [NegMemClass.coe_neg, LinearMap.neg_apply, coe_toCompletedEnveloping,
    vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
    vectorFieldEnvelopingDerivation_envelopingι, vectorFieldDerivation_neg,
    LieDerivation.neg_apply, map_neg]

section WittMode

attribute [local instance 1100] HahnSeries.instAlgebra

/-- The Witt vector field `t^{m+1} d/dt` on completed current generators sends `x_k` to
`k x_{m+k}`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_add_one_envelopingι_single_tmul
    (m k : ℤ) (r : R) (x : L) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single (m + 1) 1) :
        Module.End R Û)
        (i (envelopingι c a (HahnSeries.single k r ⊗ₜ[R] x))) =
      k • i (envelopingι c a (HahnSeries.single (m + k) r ⊗ₜ[R] x)) := by
  have hcur : vectorFieldDerivation R L (HahnSeries.single (m + 1) 1)
      (HahnSeries.single k r ⊗ₜ[R] x) = k • (HahnSeries.single (m + k) r ⊗ₜ[R] x) := by
    rw [vectorFieldDerivation_tmul, LaurentSeries.derivative_apply,
      LaurentSeries.hasseDeriv_single, Ring.choose_one_right, Nat.cast_one,
      HahnSeries.single_mul_single, one_mul, show m + 1 + (k - 1) = m + k by ring,
      TensorProduct.smul_tmul']
    exact congrArg (· ⊗ₜ[R] x) (map_zsmul (HahnSeries.single.addMonoidHom (m + k)) k r)
  simp only [coe_toCompletedEnveloping, vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
    vectorFieldEnvelopingDerivation_envelopingι, hcur, map_zsmul]

end WittMode

end TauCeti.CurrentAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) {k : R}

/-- The completed level comparison intertwines the vector fields, for every level including
zero. In particular it intertwines the degree derivations. -/
theorem levelCompletedEnvelopingEquiv_vectorFieldCompletedEnvelopingDerivation
    (he : Ψ = k • Φ) (h : R⸨X⸩)
    (x : CompletedEnveloping Ψ hΨ hΨs 1) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he
        ((vectorFieldCompletedEnvelopingDerivation Ψ hΨ hΨs 1 h :
          Module.End R (CompletedEnveloping Ψ hΨ hΨs 1)) x) =
      (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs k h :
          Module.End R (CompletedEnveloping Φ hΦ hΦs k))
        (levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he x) := by
  have hc := continuous_levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he
  have hd := ModuleTower.denseRange_toLimQuotients _
    (orderLeftIdeal_natCast_antitone Ψ hΨ hΨs 1)
  induction x using hd.induction_on with
  | hp =>
    exact isClosed_eq
      (hc.comp (continuous_vectorFieldCompletedEnvelopingDerivation Ψ hΨ hΨs 1 h))
      ((continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs k h).comp hc)
  | ih b =>
    simp only [vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
      coe_toCompletedEnveloping, levelCompletedEnvelopingEquiv_toLimQuotients,
      levelEnvelopingEquiv_vectorFieldEnvelopingDerivation hΦ hΦs hΨ hΨs he]

end TauCeti.CurrentAlgebra

