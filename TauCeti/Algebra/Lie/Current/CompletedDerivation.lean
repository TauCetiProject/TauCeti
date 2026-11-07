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
level enveloping algebra. Positive-order fields additionally preserve every stage kernel.
In particular the degree derivation `t d/dt` acts on a current mode `x_n` by `n x_n`, also inside
the completion. The extensions commute with the completed level comparison, including at level zero.

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

