/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Cohomology.Continuous
public import TauCeti.Algebra.Lie.Current.ResidueCocycle
public import TauCeti.Algebra.Lie.Current.Topology
public import TauCeti.Algebra.Lie.Loop.Cocycle

/-!
# Continuous cochains on formal currents

For formal currents `R⸨X⸩ ⊗[R] L` with their order topology, the continuity conditions of
`TauCeti.LieModule.Cohomology` take the concrete form of the joint-continuity criterion: writing
`a_N` for the currents of order at least `N`, a one-cochain is continuous when it vanishes on some
`a_N`, and an alternating two-cochain `c` is continuous when each `c u` vanishes on some `a_N` and
`c` vanishes on `a_N × a_N` for a single `N`. Since the bracket of currents is continuous,
coboundaries of continuous one-cochains with trivial coefficients are continuous two-cocycles.

The residue cocycle `(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` of an invariant symmetric form `Φ` is
continuous: every current pairs to zero with all currents of sufficiently high order, and the
pairing vanishes on the positive currents `a_0`. Its class in continuous second cohomology is
therefore defined, and over a characteristic-zero domain it is nonzero, and has no torsion, as soon
as `Φ` is nonzero. Indeed no multiple `t • c_Φ` with `t ≠ 0` is a coboundary of any one-cochain,
continuous or not, since its restriction to polynomial currents is not.

## Main results

* `TauCeti.CurrentAlgebra.mem_continuousTwoCochain_iff_orderSubmodule`: the joint-continuity
  criterion for two-cochains on formal currents.
* `TauCeti.CurrentAlgebra.d₁₂_mem_continuousTwoCocycle_of_isTrivial`: coboundaries of continuous
  one-cochains with trivial coefficients are continuous two-cocycles.
* `TauCeti.CurrentAlgebra.twoCochainOfBilinear_mem_continuousTwoCocycle`: the residue cocycle is
  continuous.
* `TauCeti.CurrentAlgebra.residueClass`: its class in continuous second cohomology.
* `TauCeti.CurrentAlgebra.smul_residueClass_eq_zero_iff`: a multiple of the residue class of a
  nonzero form vanishes only when the scalar does.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3, for the continuous cohomology of
  the formal loop algebra and its residue class.
-/

public section

noncomputable section

open Filter Topology
open scoped TensorProduct LaurentSeries

namespace TauCeti.CurrentAlgebra

open _root_.LieModule.Cohomology TauCeti.LieModule.Cohomology

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

/-- A one-cochain on formal currents is continuous exactly when it vanishes on all currents of
some order `N`. -/
theorem mem_continuousOneCochain_iff_orderSubmodule {f : oneCochain R (currentAlgebra R L) M} :
    f ∈ continuousOneCochain R (currentAlgebra R L) M ↔
      ∃ N : ℤ, ∀ u ∈ orderSubmodule R L N, f u = 0 := by
  simp [mem_continuousOneCochain_iff,
    (hasBasis_nhds_zero R L).eventually_iff]

/-- **The joint-continuity criterion on formal currents.** An alternating two-cochain `c` on
formal currents is continuous exactly when each partial map `c u` vanishes on the currents of some
order, and `c` vanishes on all pairs of currents of order at least a single `N`. -/
theorem mem_continuousTwoCochain_iff_orderSubmodule {c : twoCochain R (currentAlgebra R L) M} :
    c ∈ continuousTwoCochain R (currentAlgebra R L) M ↔
      (∀ u, ∃ N : ℤ, ∀ v ∈ orderSubmodule R L N, c u v = 0) ∧
        ∃ N : ℤ, ∀ u ∈ orderSubmodule R L N, ∀ v ∈ orderSubmodule R L N, c u v = 0 := by
  simp [mem_continuousTwoCochain_iff_of_hasBasis (hasBasis_nhds_zero R L)]

/-- Coboundaries of continuous one-cochains on formal currents with trivial coefficients are
continuous two-cocycles. -/
theorem d₁₂_mem_continuousTwoCocycle_of_isTrivial [LieRingModule (currentAlgebra R L) M]
    [LieModule R (currentAlgebra R L) M] [LieModule.IsTrivial (currentAlgebra R L) M]
    {f : oneCochain R (currentAlgebra R L) M}
    (hf : f ∈ continuousOneCochain R (currentAlgebra R L) M) :
    d₁₂ R (currentAlgebra R L) M f ∈ continuousTwoCocycle R (currentAlgebra R L) M :=
  d₁₂_mem_continuousTwoCocycle (continuous_lie R L)
    (fun m ↦ Eventually.of_forall fun u ↦ trivial_lie_zero _ M u m) hf

variable (R L)

/-- The residue 2-cochain of a symmetric form is continuous. -/
theorem twoCochainOfBilinear_mem_continuousTwoCochain (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.IsSymm) :
    twoCochainOfBilinear R L Φ hΦ ∈
      continuousTwoCochain R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) := by
  refine mem_continuousTwoCochain_iff_orderSubmodule.mpr ⟨fun u ↦ ?_, ⟨0, fun u hu v hv ↦ ?_⟩⟩
  · obtain ⟨N, hN⟩ := exists_orderSubmodule_le_ker_residuePairing R L Φ u
    exact ⟨N, fun v hv ↦ by simp [LinearMap.mem_ker.mp (hN hv)]⟩
  · simp [residuePairing_eq_zero_of_mem_orderSubmodule_zero R L Φ hu hv]

/-- The residue 2-cocycle of an invariant symmetric form is a continuous 2-cocycle. -/
theorem twoCochainOfBilinear_mem_continuousTwoCocycle (Φ : LinearMap.BilinForm R L)
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    twoCochainOfBilinear R L Φ hΦs ∈
      continuousTwoCocycle R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) :=
  mem_continuousTwoCocycle_iff.mpr ⟨twoCochainOfBilinear_mem_continuousTwoCochain R L Φ hΦs,
    twoCocycleOfBilinear_coe R L Φ hΦ hΦs ▸ (twoCocycleOfBilinear R L Φ hΦ hΦs).2⟩

/-- The residue class of an invariant symmetric form `Φ`: the class of the residue cocycle
`(f ⊗ x, g ⊗ y) ↦ Res(f dg) Φ(x, y)` in the continuous second cohomology of formal currents with
trivial coefficients. -/
def residueClass (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) :
    continuousSecondCohomology R (currentAlgebra R L) (TrivialLieModule R (currentAlgebra R L) R) :=
  continuousSecondCohomologyMk _ _ _
    ⟨twoCochainOfBilinear R L Φ hΦs, twoCochainOfBilinear_mem_continuousTwoCocycle R L Φ hΦ hΦs⟩

variable {R L}

/-- The residue class is represented by the residue cocycle. -/
theorem residueClass_eq_mk (Φ : LinearMap.BilinForm R L) (hΦ : Φ.lieInvariant L)
    (hΦs : Φ.IsSymm) :
    residueClass R L Φ hΦ hΦs = continuousSecondCohomologyMk _ _ _
      ⟨twoCochainOfBilinear R L Φ hΦs,
        twoCochainOfBilinear_mem_continuousTwoCocycle R L Φ hΦ hΦs⟩ :=
  (rfl)

/-- **The residue class of a nonzero form is torsion-free.** Over a characteristic-zero domain, a
multiple `t • [c_Φ]` of the residue class of a nonzero invariant symmetric form vanishes in
continuous second cohomology only for `t = 0`. -/
theorem smul_residueClass_eq_zero_iff [IsDomain R] [CharZero R] {Φ : LinearMap.BilinForm R L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0) (t : R) :
    t • residueClass R L Φ hΦ hΦs = 0 ↔ t = 0 := by
  refine ⟨fun h ↦ ?_, fun ht ↦ by simp [ht]⟩
  rw [residueClass_eq_mk, ← map_smul, continuousSecondCohomologyMk_eq_zero_iff] at h
  obtain ⟨f, -, hf⟩ := h
  let eC := TrivialLieModule.equiv R (currentAlgebra R L) R
  let eP := TrivialLieModule.equiv R (_root_.LieAlgebra.loopAlgebra R ℤ L) R
  -- Restricting the coboundary along the polynomial currents exhibits `t • c_Φ` as a coboundary
  -- on the loop algebra, which is impossible for `t ≠ 0`.
  refine (TauCeti.LieAlgebra.LoopAlgebra.smul_twoCochainOfBilinear_mem_range_d₁₂_iff hΦs hΦ0 t).mp
    ⟨(eP.symm.toLinearMap ∘ₗ eC.toLinearMap) ∘ₗ f ∘ₗ (ofLoop R L).toLinearMap, ?_⟩
  refine Subtype.ext (LinearMap.ext₂ fun u v ↦ eP.injective ?_)
  -- The differential of the restricted cochain is the restriction of `t • c_Φ`.
  have hd : eP (d₁₂ R _ _ ((eP.symm.toLinearMap ∘ₗ eC.toLinearMap) ∘ₗ f ∘ₗ
      (ofLoop R L).toLinearMap) u v) =
      t • eC (twoCochainOfBilinear R L Φ hΦs (ofLoop R L u) (ofLoop R L v)) := by
    rw [d₁₂_comp_lieHom_apply_apply_ofTrivial, hf]
    simp only [Submodule.coe_smul, smul_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, map_smul]
  -- On polynomial currents, `c_Φ` is the residue cocycle of the loop algebra.
  have hres : eC (twoCochainOfBilinear R L Φ hΦs (ofLoop R L u) (ofLoop R L v)) =
      eP (_root_.LieAlgebra.LoopAlgebra.twoCochainOfBilinear R ℤ L Φ hΦs u v) :=
    twoCochainOfBilinear_ofLoop R L Φ hΦs u v
  simpa only [twoCochain_val_apply, Submodule.coe_smul, LinearMap.smul_apply, map_smul, hres]
    using hd

/-- The residue class of a nonzero invariant symmetric form over a characteristic-zero domain is
nonzero. -/
theorem residueClass_ne_zero [IsDomain R] [CharZero R] {Φ : LinearMap.BilinForm R L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΦ0 : Φ ≠ 0) :
    residueClass R L Φ hΦ hΦs ≠ 0 := by
  simpa using (smul_residueClass_eq_zero_iff hΦ hΦs hΦ0 1).not.mpr one_ne_zero

end TauCeti.CurrentAlgebra
