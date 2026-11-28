/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.RingTheory.LocalRing.Herbrand
import Mathlib.FieldTheory.Galois.Profinite
import TauCeti.FieldTheory.Galois.GaloisClosure
import TauCeti.RingTheory.Valuation.RamificationGroup
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# Upper ramification of the absolute Galois group

`absoluteUpperRamificationGroup_def` gives the intersection of finite-level preimages.
`le_absoluteUpperRamificationGroup_iff` tests subgroup bounds via finite restrictions.
`absoluteUpperRamificationGroup_antitone` and `isClosed_absoluteUpperRamificationGroup`
give a decreasing filtration by closed subgroups, using
`TauCeti.IsLocalRing.upperRamificationGroup_antitone` and
`InfiniteGalois.restrictNormalHom_continuous`.

`absoluteUpperRamificationGroup_zero` identifies the term at zero with the image of inertia, using
`TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup` at finite levels and
`FiniteGaloisIntermediateField.exists_expChar_pow_mem` for descent.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section

open TauCeti.IsLocalRing

namespace ValuationSubring

variable {K : Type*} [Field K] (O : ValuationSubring (AlgebraicClosure K))

local notation "Oₘ" M => O.comap (algebraMap ↥M (AlgebraicClosure K))

/-- The upper ramification subgroup at index `u` relative to `O`, defined by the upper
ramification subgroups of the decomposition groups at all finite Galois levels. -/
noncomputable def absoluteUpperRamificationGroup (u : ℝ) : Subgroup (Field.absoluteGaloisGroup K) :=
  ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
    Subgroup.comap (G := Field.absoluteGaloisGroup K) (AlgEquiv.restrictNormalHom ↥M)
      ((upperRamificationGroup ((Oₘ M).decompositionSubgroup K) (Oₘ M) u).map
        ((Oₘ M).decompositionSubgroup K).subtype)

/-- The absolute upper ramification subgroup is the intersection of the finite-level preimages. -/
theorem absoluteUpperRamificationGroup_def (u : ℝ) :
    O.absoluteUpperRamificationGroup u = ⨅ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
      Subgroup.comap (G := Field.absoluteGaloisGroup K) (AlgEquiv.restrictNormalHom ↥M)
        ((upperRamificationGroup ((Oₘ M).decompositionSubgroup K) (Oₘ M) u).map
          ((Oₘ M).decompositionSubgroup K).subtype) := (rfl)

variable {O} in
/-- A subgroup lies in the filtration term iff its finite images lie in the finite upper groups. -/
@[simp]
theorem le_absoluteUpperRamificationGroup_iff {u : ℝ} {H : Subgroup (Field.absoluteGaloisGroup K)} :
    H ≤ O.absoluteUpperRamificationGroup u ↔
      ∀ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        H.map (AlgEquiv.restrictNormalHom ↥M) ≤
          (upperRamificationGroup ((Oₘ M).decompositionSubgroup K) (Oₘ M) u).map
            ((Oₘ M).decompositionSubgroup K).subtype := by
  rw [absoluteUpperRamificationGroup_def, le_iInf_iff]
  exact forall_congr' fun _ ↦ Subgroup.map_le_iff_le_comap.symm

variable {O} in
/-- Membership in the absolute upper ramification subgroup is tested on all finite Galois
restrictions. -/
@[simp]
theorem mem_absoluteUpperRamificationGroup_iff {u : ℝ} {σ : Field.absoluteGaloisGroup K} :
    σ ∈ O.absoluteUpperRamificationGroup u ↔
      ∀ M : FiniteGaloisIntermediateField K (AlgebraicClosure K),
        AlgEquiv.restrictNormalHom ↥M σ ∈
          (upperRamificationGroup ((Oₘ M).decompositionSubgroup K) (Oₘ M) u).map
            ((Oₘ M).decompositionSubgroup K).subtype := by
  rw [absoluteUpperRamificationGroup_def, Subgroup.mem_iInf]
  exact forall_congr' fun _ ↦ Subgroup.mem_comap

/-- The absolute upper ramification subgroups form a decreasing filtration. -/
theorem absoluteUpperRamificationGroup_antitone :
    Antitone (O.absoluteUpperRamificationGroup : ℝ → Subgroup (Field.absoluteGaloisGroup K)) := by
  intro u v huv
  simp only [absoluteUpperRamificationGroup_def]
  exact iInf_mono fun M ↦ Subgroup.comap_mono
    (Subgroup.map_mono (upperRamificationGroup_antitone _ _ huv))

/-- Each absolute upper ramification subgroup is closed in the Krull topology. -/
theorem isClosed_absoluteUpperRamificationGroup (u : ℝ) :
    IsClosed (O.absoluteUpperRamificationGroup u : Set (Field.absoluteGaloisGroup K)) := by
  rw [absoluteUpperRamificationGroup_def, Subgroup.coe_iInf]
  refine isClosed_iInter fun M ↦ ?_
  rw [@Subgroup.coe_comap (Field.absoluteGaloisGroup K) _ _ _ _ (AlgEquiv.restrictNormalHom ↥M)]
  -- The absolute Galois group carries the Krull topology of the algebraic closure.
  exact (isClosed_discrete _).preimage
    (InfiniteGalois.restrictNormalHom_continuous M.toIntermediateField)

/-- At zero the absolute upper ramification subgroup is inertia, viewed in the full absolute
Galois group. This holds for every valuation subring of the algebraic closure. -/
@[simp]
theorem absoluteUpperRamificationGroup_zero :
    O.absoluteUpperRamificationGroup 0 =
      (O.inertiaSubgroup K).map (O.decompositionSubgroup K).subtype := by
  refine Subgroup.ext fun (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ↦ ?_
  refine (mem_absoluteUpperRamificationGroup_iff (σ := σ)).trans
    (Iff.trans ?_ (mem_map_inertiaSubgroup_iff (σ := σ)).symm)
  have hzero (M : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
      ramificationGroupReal ((Oₘ M).decompositionSubgroup K) (Oₘ M) 0 =
        (Oₘ M).inertiaSubgroup K := by
    simpa only [Int.cast_zero, ramificationGroup_zero_eq_inertiaSubgroup] using
      ramificationGroupReal_intCast ((Oₘ M).decompositionSubgroup K) (Oₘ M) (0 : ℤ)
  simp_rw [upperRamificationGroup_of_le_zero _ _ le_rfl, hzero]
  simp only [mem_map_inertiaSubgroup_iff, mem_comap, mem_nonunits_comap, map_sub,
    IntermediateField.algebraMap_apply, AlgEquiv.restrictNormalHom_apply]
  constructor
  · intro h x hx
    -- A power of each element lies in a finite Galois subextension.
    obtain ⟨p, hp⟩ := ExpChar.exists K
    have : ExpChar (AlgebraicClosure K) p :=
      expChar_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
    obtain ⟨n, M, hxM⟩ := FiniteGaloisIntermediateField.exists_expChar_pow_mem K p x
    let z : M := ⟨x ^ p ^ n, hxM⟩
    have hz : (z : AlgebraicClosure K) = x ^ p ^ n := rfl
    have hpow := h M z (hz ▸ O.pow_mem hx _)
    rw [hz, map_pow, ← sub_pow_expChar_pow] at hpow
    exact (pow_mem_nonunits_iff (pow_ne_zero _ (expChar_ne_zero K p))).mp hpow
  · exact fun h M x hx ↦ h _ hx

end ValuationSubring
