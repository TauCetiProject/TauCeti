/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.ContinuousCohomology
public import TauCeti.Algebra.Lie.Current.Perfect
public import TauCeti.Algebra.Lie.Perfect

import TauCeti.Algebra.Lie.Killing.Basic
import TauCeti.Algebra.Lie.Killing.Perfect

/-!
# Universal maps from residue extensions

Fix a nonzero invariant form spanning the invariant forms of a finite-dimensional Killing
Lie algebra in characteristic zero. Every continuous two-cocycle on its formal currents,
with values in an arbitrary vector space with trivial action, receives a unique Lie algebra
map from the scalar residue extension over the identity on currents.

The existence theorem gives its full coordinate formula `(u, t) ↦ (u, t • z - f u)` with
`f` a continuous one-cochain. In particular it supplies the continuity estimate needed to
topologize this map: the correction vanishes on some high-order current subspace. The
coefficient space need not be finite-dimensional. Uniqueness holds among all Lie algebra
maps over currents, without prescribing their restriction to the central kernel.

These statements concern Mathlib's cocycle models `LieAlgebra.ofTwoCocycle`. They do not
equip arbitrary extensions with a topology or assert that an arbitrary extension has a
continuous splitting. The residue convention is `Res(f dg) Φ(x, y)`; the affine level form
`κ` corresponds to `Φ = -κ`.

The construction composes `LieAlgebra.ofTwoCocycle.map` with Mathlib's
`LieAlgebra.LieEquiv.ofCoboundary`, using its sign for the section change.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §1.3.
* V. G. Kac, *Infinite-Dimensional Lie Algebras*, Chapter 7.
-/

public section

noncomputable section

namespace TauCeti.CurrentAlgebra

open _root_.LieAlgebra _root_.LieModule.Cohomology TauCeti.LieModule.Cohomology

variable {K L Z : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] [AddCommGroup Z] [Module K Z]
  {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "C" => currentAlgebra K L
local notation "TK" => TrivialLieModule K C K
local notation "TZ" => TrivialLieModule K C Z
local notation "cΦ" => twoCocycleOfBilinear K L Φ hΦ hΦs

/-- A continuous cocycle extension with arbitrary trivial coefficients receives a map from
the scalar residue extension. Its central coordinate is `t • z - f u`, where `f` vanishes
on a high-order current subspace. -/
theorem exists_residueExtensionLift
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    (hne : ∃ x y z : L, Φ ⁅x, y⁆ z ≠ 0) (c : twoCocycle K C TZ)
    (hc : (c : twoCochain K C TZ) ∈ continuousTwoCocycle K C TZ) :
    ∃ z : Z, ∃ f : oneCochain K C TZ, ∃ N : ℤ,
      (∀ u ∈ orderSubmodule K L N, f u = 0) ∧
      ∃ F : ofTwoCocycle cΦ →ₗ⁅K⁆ ofTwoCocycle c,
        ∀ (u : C) (t : TK), F (ofProd cΦ (u, t)) =
          ofProd c (u, (TrivialLieModule.equiv K C Z).symm
            ((TrivialLieModule.equiv K C K t) • z) - f u) := by
  obtain ⟨z, f, hf, hcf⟩ :=
    exists_eq_twoCochainOfBilinearSMulRight_add_d₁₂ hΦ hΦs hspan hne hc
  obtain ⟨N, hN⟩ := mem_continuousOneCochain_iff_orderSubmodule.mp hf
  let d : twoCocycle K C TZ := ⟨twoCochainOfBilinearSMulRight K L Φ hΦs z,
    twoCochainOfBilinearSMulRight_mem_twoCocycle K L Φ hΦ hΦs z⟩
  let e : TK →ₗ[K] TZ := (TrivialLieModule.equiv K C Z).symm.toLinearMap ∘ₗ
    LinearMap.toSpanSingleton K Z z ∘ₗ (TrivialLieModule.equiv K C K).toLinearMap
  let F₀ := ofTwoCocycle.map cΦ LieHom.id e d (fun u v ↦ by simp [d, e])
  let F := (LieEquiv.ofCoboundary d c f hcf).toLieHom.comp F₀
  refine ⟨z, f, N, hN, F, fun u t ↦ ?_⟩
  simp [F, F₀, e, LieEquiv.ofCoboundary]

/-- The nonzero scalar residue extension is initial among extensions represented by
continuous two-cocycles with arbitrary trivial coefficients. The unique map lies over
the identity on currents; no condition on its map of kernels is imposed. -/
theorem existsUnique_residueExtensionLift
    (hspan : ∀ Ψ : LinearMap.BilinForm K L, Ψ.lieInvariant L → ∃ t : K, Ψ = t • Φ)
    (hne : ∃ x y z : L, Φ ⁅x, y⁆ z ≠ 0) (c : twoCocycle K C TZ)
    (hc : (c : twoCochain K C TZ) ∈ continuousTwoCocycle K C TZ) :
    ∃! F : ofTwoCocycle cΦ →ₗ⁅K⁆ ofTwoCocycle c,
      (ofTwoCocycle.proj c).comp F = ofTwoCocycle.proj cΦ := by
  obtain ⟨z, f, N, hN, F, hF⟩ := exists_residueExtensionLift hΦ hΦs hspan hne c hc
  have hproj : (ofTwoCocycle.proj c).comp F = ofTwoCocycle.proj cΦ := by
    apply LieHom.ext
    intro v
    obtain ⟨⟨u, t⟩, rfl⟩ := (ofProd cΦ).surjective v
    simp [hF]
  have hΦ0 : Φ ≠ 0 := by
    obtain ⟨x, y, z, h⟩ := hne
    intro hzero
    simp [hzero] at h
  have hperfect : derivedSeries K (ofTwoCocycle cΦ) 1 = ⊤ :=
    (derivedSeries_ofTwoCocycle_eq_top_iff L Φ hΦ hΦs
      (TauCeti.derivedSeries_one_eq_top_of_isKilling K L)).mpr hΦ0
  refine ⟨F, hproj, fun G hG ↦ ?_⟩
  apply G.eq_of_comp_eq_of_ker_le_center F (ofTwoCocycle.proj c) hperfect ?_
    (hG.trans hproj.symm)
  intro v hv
  have hv₁ := (ofTwoCocycle.mem_ker_proj c).mp hv
  apply (LieModule.mem_maxTrivSubmodule K _ _ _).mpr
  intro w
  simp only [bracket_ofTwoCocycle, hv₁, lie_zero, trivial_lie_zero, map_zero,
    sub_zero, add_zero]
  exact of_zero c

/-- For a simple Lie algebra over an algebraically closed field of characteristic zero,
the Killing residue extension has a unique map over currents into every continuous
cocycle extension with arbitrary trivial coefficients. More generally, irreducibility of
the adjoint module and nondegeneracy of the Killing form suffice. -/
theorem existsUnique_killingExtensionLift [IsAlgClosed K]
    [_root_.LieModule.IsIrreducible K L L] (c : twoCocycle K C TZ)
    (hc : (c : twoCochain K C TZ) ∈ continuousTwoCocycle K C TZ) :
    ∃! F : ofTwoCocycle (twoCocycleOfBilinear K L (killingForm K L)
        (_root_.LieModule.traceForm_lieInvariant K L L)
        (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L)))
        →ₗ⁅K⁆ ofTwoCocycle c,
      (ofTwoCocycle.proj c).comp F = ofTwoCocycle.proj _ := by
  have _i := _root_.LieModule.nontrivial_of_isIrreducible K L L
  exact existsUnique_residueExtensionLift
    (_root_.LieModule.traceForm_lieInvariant K L L)
    (LinearMap.BilinForm.isSymm_iff.mpr (_root_.LieModule.traceForm_isSymm K L L))
    (fun _ hΨ ↦ TauCeti.LieAlgebra.exists_eq_smul_killingForm hΨ)
    TauCeti.exists_killingForm_lie_ne_zero c hc

end TauCeti.CurrentAlgebra
