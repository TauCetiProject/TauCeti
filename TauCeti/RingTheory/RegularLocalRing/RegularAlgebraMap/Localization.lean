/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.RegularAlgebraMap.Basic

import Mathlib.RingTheory.TensorProduct.Finite
import TauCeti.RingTheory.LocalRing.ResidueField.Fiber
import TauCeti.RingTheory.Localization.LocalizationLocalization

/-!
# Locality of regular ring maps on the target

Localizing the target of a regular algebra map preserves regularity. Conversely, for a
Noetherian target, regularity can be tested on the local maps at its maximal ideals. The
contracted primes in the base need not be maximal.

## References

* The Stacks Project, [Lemma 15.42.2](https://stacks.math.columbia.edu/tag/07C0).
-/

public section

open TensorProduct
open Algebra.TensorProduct (includeRight)

namespace TauCeti.Excellence

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]

namespace RegularAlgebraMap

/-- Localizing the target of a regular ring map preserves regularity. -/
theorem localization_target (h : RegularAlgebraMap R B) (M : Submonoid B)
    [IsLocalization M C] : RegularAlgebraMap R C where
  flat :=
    have := h.flat
    have : Module.Flat B C := IsLocalization.flat C M
    Module.Flat.trans R B C
  geometricallyRegular_fiber p _ := by
    let f := Algebra.TensorProduct.lTensor (S := p.ResidueField) p.ResidueField
      (IsScalarTower.toAlgHom R B C)
    let : Algebra (p.Fiber B) (p.Fiber C) := f.toAlgebra
    have : IsScalarTower p.ResidueField (p.Fiber B) (p.Fiber C) :=
      .of_algebraMap_eq' f.comp_algebraMap.symm
    have := IsLocalization.tensorProduct_tensorProduct_right R p.ResidueField M C
      (by ext b; rfl)
    exact (h.geometricallyRegular_fiber p).localization
      (M.map (includeRight (R := R) (A := p.ResidueField)))

/-- A regular ring map induces a regular local ring map at every prime of the target. -/
theorem localization_atPrime (h : RegularAlgebraMap R B) (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    RegularAlgebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have : RegularAlgebraMap R (Localization.AtPrime q) := h.localization_target q.primeCompl
  exact localization_base (q.under R).primeCompl

private theorem geometricallyRegular_fiber_of_localization_maximal [IsNoetherianRing B]
    (h : ∀ (q : Ideal B) [q.IsMaximal],
      letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      RegularAlgebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))
    (p : Ideal R) [p.IsPrime] : GeometricallyRegular p.ResidueField (p.Fiber B) := by
  refine ⟨inferInstance, fun L _ _ _ _ ↦ ?_⟩
  let : Algebra R L := ((algebraMap p.ResidueField L).comp (algebraMap R _)).toAlgebra
  have : IsScalarTower R p.ResidueField L := .of_algebraMap_eq' rfl
  let eB := (Algebra.TensorProduct.cancelBaseChange R p.ResidueField L L B).toRingEquiv
  refine @IsRegularRing.of_ringEquiv _ _ _ _ eB.symm ?_
  have : IsNoetherianRing (p.Fiber B ⊗[p.ResidueField] L) :=
    IsNoetherianRing.of_finite (p.Fiber B) _
  have : IsNoetherianRing (L ⊗[R] B) := isNoetherianRing_of_ringEquiv _
    ((Algebra.TensorProduct.comm p.ResidueField (p.Fiber B) L).toRingEquiv.trans eB)
  -- A prime of the extended fibre survives in the localization at any maximal ideal above it.
  refine isRegularRing_iff.mpr fun P _ ↦ ?_
  let : Algebra B (L ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  obtain ⟨q, hq, hPq⟩ := Ideal.exists_le_maximal (P.under B) Ideal.IsPrime.ne_top'
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have hpq : p ≤ q.under R := by
    intro x hx
    apply hPq
    rw [Ideal.mem_under, Algebra.TensorProduct.right_algebraMap_apply,
      ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    simp [IsScalarTower.algebraMap_apply R p.ResidueField L,
      Ideal.algebraMap_residueField_eq_zero.mpr hx]
  let p' := p.map (algebraMap R (Localization.AtPrime (q.under R)))
  have : p'.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime (q.under R) hpq
  have := h q
  have hF : GeometricallyRegular p.ResidueField (p.Fiber (Localization.AtPrime q)) := by
    have hF := (p'.geometricallyRegular_fiber_iff_of_isLocalization (B := Localization.AtPrime q)
      (q.under R).primeCompl).mp inferInstance
    -- Use prime-spectrum equality to transport the fibre and its residue field together.
    have e : (⟨p'.under R, inferInstance⟩ : PrimeSpectrum R) = ⟨p, inferInstance⟩ :=
      PrimeSpectrum.ext (Ideal.under_map_of_isLocalizationAtPrime (q.under R) hpq)
    exact (congrArg (fun x : PrimeSpectrum R ↦ GeometricallyRegular x.asIdeal.ResidueField
      (x.asIdeal.Fiber (Localization.AtPrime q))) e).mp hF
  have : IsRegularRing (L ⊗[R] Localization.AtPrime q) := .of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField L L _).toRingEquiv
  let f := Algebra.TensorProduct.lTensor (S := L) L
    (IsScalarTower.toAlgHom R B (Localization.AtPrime q))
  let : Algebra (L ⊗[R] B) (L ⊗[R] Localization.AtPrime q) := f.toAlgebra
  have : IsScalarTower L (L ⊗[R] B) (L ⊗[R] Localization.AtPrime q) :=
    .of_algebraMap_eq' f.comp_algebraMap.symm
  let M := q.primeCompl.map (includeRight (R := R) (A := L))
  have : IsLocalization M (L ⊗[R] Localization.AtPrime q) :=
    IsLocalization.tensorProduct_tensorProduct_right R L q.primeCompl _ (by ext b; rfl)
  have hd : Disjoint (M : Set (L ⊗[R] B)) P := Set.disjoint_left.mpr <| by
    rintro _ ⟨b, hb, rfl⟩ hbP
    exact hb (hPq hbP)
  obtain ⟨Q, hQ, _, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime M
    (L ⊗[R] Localization.AtPrime q) P hd
  have hloc : IsRegularLocalRing (Localization.AtPrime Q) := inferInstance
  exact hloc.of_ringEquiv e.symm

variable (R B) in
/-- A ring map with Noetherian target `B` is regular if and only if the induced local ring map
at each maximal ideal of `B` is regular. The source is localized at the contracted prime. -/
theorem iff_localization_maximal [IsNoetherianRing B] :
    RegularAlgebraMap R B ↔ ∀ (q : Ideal B) [q.IsMaximal],
      letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      RegularAlgebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q) := by
  refine ⟨fun h q _ ↦ h.localization_atPrime q, fun h ↦
    ⟨?_, fun p _ ↦ geometricallyRegular_fiber_of_localization_maximal h p⟩⟩
  refine Module.flat_of_isLocalized_maximal B B (fun q _ ↦ Localization.AtPrime q)
    (fun q _ ↦ Algebra.linearMap B (Localization.AtPrime q)) fun q _ ↦ ?_
  let := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  have := h q
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.under R))
    (q.under R).primeCompl (Localization.AtPrime q)).mp inferInstance

end RegularAlgebraMap

/-! ### Boundary cases -/

/-- The maximal-local criterion for `ℤ → ℚ` uses a nonmaximal prime of `ℤ`. -/
example :
    let q : Ideal ℚ := ⊥
    letI : q.IsMaximal := Ideal.bot_isMaximal
    letI := Localization.AtPrime.algebraOfLiesOver (q.under ℤ) q
    RegularAlgebraMap (Localization.AtPrime (q.under ℤ)) (Localization.AtPrime q) ∧
      ¬ (q.under ℤ).IsMaximal := by
  let q : Ideal ℚ := ⊥
  have : q.IsMaximal := Ideal.bot_isMaximal
  refine ⟨(RegularAlgebraMap.iff_localization_maximal ℤ ℚ).mp
    (.of_isLocalization (nonZeroDivisors ℤ)) q, ?_⟩
  have hq : q.under ℤ = ⊥ := Ideal.comap_bot_of_injective (algebraMap ℤ ℚ)
    (FaithfulSMul.algebraMap_injective ℤ ℚ)
  exact fun h ↦ Int.not_isField (Ring.isField_iff_maximal_bot.mpr (hq ▸ h))

/-- The maximal-local test is vacuous for the zero algebra, and the structure map is regular. -/
example (R : Type*) [CommRing R] : RegularAlgebraMap R (R ⧸ (⊤ : Ideal R)) := by
  apply (RegularAlgebraMap.iff_localization_maximal R _).mpr
  intro q hq
  exact (hq.ne_top (Subsingleton.elim q ⊤)).elim

end TauCeti.Excellence
