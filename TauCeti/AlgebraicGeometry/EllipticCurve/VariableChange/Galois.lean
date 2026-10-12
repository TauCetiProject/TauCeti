/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
public import TauCeti.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.Infinite

/-!
# Galois conjugation of changes of variables

An admissible change of variables with algebraic coefficients has a locally constant orbit
under the Krull topology. Over a Galois extension, it is defined over the base field exactly
when every automorphism fixes it. These two facts give continuity and descent for the
cocycles attached to pointed twists of Weierstrass curves.
-/

public section

namespace WeierstrassCurve.VariableChange

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Conjugation of a change of variables with integral coefficients is locally constant
for the Krull topology. No algebraicity assumption on the whole extension is needed. -/
theorem isLocallyConstant_map (C : VariableChange L)
    (hu : IsIntegral K (C.u : L)) (hr : IsIntegral K C.r)
    (hs : IsIntegral K C.s) (ht : IsIntegral K C.t) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ C.map (σ : L →+* L) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 hu.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 hr.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 hs.isLocallyConstant_apply σ₀,
    (IsLocallyConstant.iff_eventually_eq _).1 ht.isLocallyConstant_apply σ₀]
    with σ hu hr hs ht
  exact VariableChange.ext (Units.ext hu) hr hs ht

/-- Over a possibly infinite Galois extension, a change of variables descends precisely
when all its Galois conjugates agree with it. -/
theorem mem_range_baseChange_iff_fixed [IsGalois K L] (C : VariableChange L) :
    C ∈ Set.range (fun D : VariableChange K ↦ D.baseChange L) ↔
      ∀ σ : Gal(L/K), C.map (σ : L →+* L) = C := by
  constructor
  · rintro ⟨D, rfl⟩ σ
    ext <;> simp [VariableChange.baseChange, VariableChange.map, AlgEquiv.commutes]
  · intro h
    have fixed (f : VariableChange L → L)
        (hf : ∀ σ : Gal(L/K), f (C.map σ) = σ (f C)) :
        f C ∈ Set.range (algebraMap K L) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ ↦ by rw [← hf, h]
    obtain ⟨u, hu⟩ := fixed (fun D ↦ (D.u : L)) fun _ ↦ rfl
    obtain ⟨r, hr⟩ := fixed VariableChange.r fun _ ↦ rfl
    obtain ⟨s, hs⟩ := fixed VariableChange.s fun _ ↦ rfl
    obtain ⟨t, ht⟩ := fixed VariableChange.t fun _ ↦ rfl
    have hu₀ : u ≠ 0 := by
      rintro rfl
      exact C.u.ne_zero (hu.symm.trans (map_zero _))
    refine ⟨⟨Units.mk0 u hu₀, r, s, t⟩, ?_⟩
    exact VariableChange.ext (Units.ext hu) hr hs ht

end WeierstrassCurve.VariableChange
