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
# The degree derivation on completed current enveloping algebras

Vector fields `h d/dt` with `h` of positive order preserve the current-order left ideals, so
their derivations extend uniquely to the completed level enveloping algebra. In particular the
degree derivation `t d/dt` acts on a current mode `x_n` by `n x_n`, also inside the completion.
The extended vector fields are continuous and preserve the kernels of the stage projections.
They commute with the completed level comparison, including at level zero.

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

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : R)

local notation "U" => CentralQuotient R (centralElement Φ hΦ hΦs) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "i" => toCompletedEnveloping Φ hΦ hΦs a

-- Only the proof of extension uses a topology on the uncompleted algebra. Give it the
-- uniformity pulled back from the completion; injectivity of its canonical map is unnecessary.
private abbrev completionUniformSpace : UniformSpace U := UniformSpace.comap i inferInstance
attribute [local instance] completionUniformSpace

private theorem uniformInducing_toCompleted : IsUniformInducing i :=
  isUniformInducing_iff_uniformSpace.mpr rfl

private theorem uniformContinuous_vectorField {h : R⸨X⸩} (hh : (1 : WithTop ℤ) ≤ h.orderTop) :
    UniformContinuous fun b : U ↦ i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h :
      Module.End R U) b) := by
  have hb := (hasBasis_nhds_zero_completedOrderLeftIdeal Φ hΦ hΦs a).uniformity_of_nhds_zero
  have hs := hb.comap (fun p : U × U ↦ (i p.1, i p.2))
  refine (hs.tendsto_iff hb).mpr fun n _ ↦ ⟨n, trivial, fun p hp ↦ ?_⟩
  have hp' : p.2 - p.1 ∈ orderLeftIdeal Φ hΦ hΦs a n := by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe, ← map_sub,
      coe_toCompletedEnveloping, mem_completedOrderLeftIdeal, ModuleTower.limπ_apply,
      ModuleTower.coe_toLimQuotients_apply, ModuleTower.quotientsπ_eq_zero_iff] using hp
  simpa only [Set.mem_ofPred_eq, SetLike.mem_coe, ← map_sub, coe_toCompletedEnveloping,
    mem_completedOrderLeftIdeal, ModuleTower.limπ_apply, ModuleTower.coe_toLimQuotients_apply,
    ModuleTower.quotientsπ_eq_zero_iff] using
      vectorFieldEnvelopingDerivation_mem_orderLeftIdeal Φ hΦ hΦs a hh hp'

/-- The continuous extension of `h d/dt` to the completed level enveloping algebra, for a
vector field preserving the maximal ideal of the power-series ring. -/
def vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩) (hh : (1 : WithTop ℤ) ≤ h.orderTop) :
    derivationLieAlgebra R Û :=
  derivationLieAlgebra.extend (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h) i
    (uniformInducing_toCompleted Φ hΦ hΦs a)
    (by simpa only [coe_toCompletedEnveloping] using
      (ModuleTower.denseRange_toLimQuotients _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a)))
    (uniformContinuous_vectorField Φ hΦ hΦs a hh)

/-- The completed vector field extends the vector field on the uncompleted enveloping algebra.
The left side uses the simp normal form of the canonical map into the completion. -/
@[simp]
theorem vectorFieldCompletedEnvelopingDerivation_toLimQuotients (h : R⸨X⸩)
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) (b : U) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh : Module.End R Û)
        (ModuleTower.toLimQuotients _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a) b) =
      i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R U) b) := by
  simpa only [vectorFieldCompletedEnvelopingDerivation, coe_toCompletedEnveloping] using
    derivationLieAlgebra.extend_apply (vectorFieldEnvelopingDerivation Φ hΦ hΦs a h) i
      (uniformInducing_toCompleted Φ hΦ hΦs a)
      (by simpa only [coe_toCompletedEnveloping] using
        (ModuleTower.denseRange_toLimQuotients _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a)))
      (uniformContinuous_vectorField Φ hΦ hΦs a hh) b

/-- Completed vector fields are continuous for the current-order topology. -/
theorem continuous_vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩)
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) :
    Continuous (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh : Module.End R Û) :=
  derivationLieAlgebra.continuous_extend _ _ _ _ _

/-- Uniqueness of the continuous extension, even among maps not assumed to be derivations. -/
theorem eq_vectorFieldCompletedEnvelopingDerivation (h : R⸨X⸩)
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) {f : Û → Û} (hf : Continuous f)
    (he : ∀ b : U, f (i b) =
      i ((vectorFieldEnvelopingDerivation Φ hΦ hΦs a h : Module.End R U) b)) :
    f = (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh : Module.End R Û) := by
  unfold vectorFieldCompletedEnvelopingDerivation
  exact derivationLieAlgebra.eq_extend _ _ _ _ _ hf he

/-- The degree derivation on completed current generators is `x_n ↦ n x_n`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_envelopingι_single_tmul
    (n : ℤ) (r : R) (x : L) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1)
        HahnSeries.orderTop_single_le : Module.End R Û)
        (i (envelopingι Φ hΦ hΦs a (HahnSeries.single n r ⊗ₜ[R] x))) =
      n • i (envelopingι Φ hΦ hΦs a (HahnSeries.single n r ⊗ₜ[R] x)) := by
  simp only [coe_toCompletedEnveloping, vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
    vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul, map_zsmul]

/-- Completed vector fields preserve every kernel of a current-order stage projection. -/
theorem vectorFieldCompletedEnvelopingDerivation_mem_completedOrderLeftIdeal (h : R⸨X⸩)
    (hh : (1 : WithTop ℤ) ≤ h.orderTop) {n : ℕ} {x : Û}
    (hx : x ∈ completedOrderLeftIdeal Φ hΦ hΦs a n) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh : Module.End R Û) x ∈
      completedOrderLeftIdeal Φ hΦ hΦs a n := by
  let D := (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh : Module.End R Û)
  have hc : Continuous D := continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a h hh
  have hset : (completedOrderLeftIdeal Φ hΦ hΦs a n : Set Û) =
      (LinearMap.ker ((orderQuotientTower Φ hΦ hΦs a).limπ n) : Set Û) :=
    Set.ext fun _ ↦ mem_completedOrderLeftIdeal
  have ho : IsOpen (completedOrderLeftIdeal Φ hΦ hΦs a n : Set Û) :=
    hset ▸ (orderQuotientTower Φ hΦ hΦs a).isOpen_ker_limπ n
  have hd := ModuleTower.denseRange_toLimQuotients _
    (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a)
  by_contra hbad
  obtain ⟨b, hb, hDb⟩ := hd.exists_mem_open
    (ho.inter ((isClosed_completedOrderLeftIdeal Φ hΦ hΦs a n).isOpen_compl.preimage hc))
    ⟨x, hx, hbad⟩
  have hb' : b ∈ orderLeftIdeal Φ hΦ hΦs a n := by
    simpa only [SetLike.mem_coe, mem_completedOrderLeftIdeal, ModuleTower.limπ_apply,
      ModuleTower.coe_toLimQuotients_apply, ModuleTower.quotientsπ_eq_zero_iff] using hb
  apply hDb
  simpa only [D, SetLike.mem_coe, vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
    coe_toCompletedEnveloping, mem_completedOrderLeftIdeal, ModuleTower.limπ_apply,
    ModuleTower.coe_toLimQuotients_apply, ModuleTower.quotientsπ_eq_zero_iff] using
    vectorFieldEnvelopingDerivation_mem_orderLeftIdeal Φ hΦ hΦs a hh hb'

end TauCeti.CurrentAlgebra

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ Ψ : LinearMap.BilinForm R L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
  (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm) {k : R}

/-- The completed level comparison intertwines the vector fields, for every level including
zero. In particular it intertwines the degree derivations. -/
theorem levelCompletedEnvelopingEquiv_vectorFieldCompletedEnvelopingDerivation
    (he : Ψ = k • Φ) (h : R⸨X⸩) (hh : (1 : WithTop ℤ) ≤ h.orderTop)
    (x : CompletedEnveloping Ψ hΨ hΨs 1) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he
        ((vectorFieldCompletedEnvelopingDerivation Ψ hΨ hΨs 1 h hh :
          Module.End R (CompletedEnveloping Ψ hΨ hΨs 1)) x) =
      (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs k h hh :
          Module.End R (CompletedEnveloping Φ hΦ hΦs k))
        (levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he x) := by
  have hc := continuous_levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs he
  have hd := ModuleTower.denseRange_toLimQuotients _
    (orderLeftIdeal_natCast_antitone Ψ hΨ hΨs 1)
  induction x using hd.induction_on with
  | hp =>
    exact isClosed_eq
      (hc.comp (continuous_vectorFieldCompletedEnvelopingDerivation Ψ hΨ hΨs 1 h hh))
      ((continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs k h hh).comp hc)
  | ih b =>
    simp only [vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
      coe_toCompletedEnveloping, levelCompletedEnvelopingEquiv_toLimQuotients,
      levelEnvelopingEquiv_vectorFieldEnvelopingDerivation hΦ hΦs hΨ hΨs he]

end TauCeti.CurrentAlgebra

