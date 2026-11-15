/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Kaehler.Map
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.ZMod.Basic
public import TauCeti.Topology.Discrete

/-!
# Using change of rings for continuous differentials

These examples exercise the opaque cotangent presentation, semilinear change of rings,
and scalar extension with arbitrary caller algebra instances. A discrete polynomial example
reduces coefficients modulo four and carries `dX` to `dX`.
-/

public section

open TensorProduct TauCeti.Huber
open ContinuousKaehlerDifferential

section Generic

variable {A B A' B' A'' B'' : Type*}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
  [Algebra A B] [Algebra A' B'] [Algebra A'' B'']
  [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace A'] [IsTopologicalRing A']
  [TopologicalSpace A''] [IsTopologicalRing A'']
  [UniformSpace B] [IsUniformAddGroup B] [NonarchimedeanRing B] [CompleteSpace B] [T0Space B]
  [UniformSpace B'] [IsUniformAddGroup B'] [NonarchimedeanRing B'] [CompleteSpace B'] [T0Space B']
  [UniformSpace B''] [IsUniformAddGroup B''] [NonarchimedeanRing B'']
  [CompleteSpace B''] [T0Space B'']
  [IsAdicHom (algebraMap A B)] [IsAdicHom (algebraMap A' B')]
  [IsAdicHom (algebraMap A'' B'')]


variable (α : A →+* A') (φ : B →+* B')
  (h : φ.comp (algebraMap A B) = (algebraMap A' B').comp α) (hc : Continuous φ)

example (ω : ContinuousKaehlerDifferential A B) :
    (cotangentEquiv A B).symm (cotangentEquiv A B ω) = ω := by simp

example (ω : (ideal A B).Cotangent) :
    cotangentEquiv A B ((cotangentEquiv A B).symm ω) = ω := by simp

example (x : ideal A B) :
    cotangentEquiv A B (fromIdeal A B x) = (ideal A B).toCotangent x := by simp

example (x : ideal A B) :
    mapSemilinear α φ h hc (fromIdeal A B x) =
      fromIdeal A' B' ⟨CompletedTensor.map α φ φ h h hc hc x,
        ideal_le_comap_map α φ h hc x.2⟩ := by simp

example (b : B) : mapSemilinear α φ h hc (D A B b) = D A' B' (φ b) := by simp

variable [Algebra B B']
  (hB : (algebraMap B B').comp (algebraMap A B) = (algebraMap A' B').comp α)
  (hcB : Continuous (algebraMap B B'))

example (b' : B') (ω : ContinuousKaehlerDifferential A B) :
    map α hB hcB (b' ⊗ₜ[B] ω) =
      b' • mapSemilinear α (algebraMap B B') hB hcB ω := by simp

example (b' : B') (b : B) :
    map α hB hcB (b' ⊗ₜ[B] D A B b) = b' • D A' B' (algebraMap B B' b) := by simp

-- The construction also works in a context with independently selected compatible target actions.
example [Module B (ContinuousKaehlerDifferential A' B')]
    [IsScalarTower B B' (ContinuousKaehlerDifferential A' B')]
    (b' : B') (ω : ContinuousKaehlerDifferential A B) :
    map α hB hcB (b' ⊗ₜ[B] ω) =
      b' • mapSemilinear α (algebraMap B B') hB hcB ω := by simp

example (x : B ⊗[B] ContinuousKaehlerDifferential A B) :
    map (B := B) (B' := B) (RingHom.id A) rfl continuous_id x =
      TensorProduct.lid B (ContinuousKaehlerDifferential A B) x := by
  rw [ContinuousKaehlerDifferential.map_id]
  rfl

variable [Algebra B' B''] [Algebra B B''] [IsScalarTower B B' B'']
  (α' : A' →+* A'')
  (hB' : (algebraMap B' B'').comp (algebraMap A' B') = (algebraMap A'' B'').comp α')
  (hcB' : Continuous (algebraMap B' B''))

example (b'' : B'') (b' : B') (ω : ContinuousKaehlerDifferential A B) :
    map α' hB' hcB' (b'' ⊗ₜ[B'] map α hB hcB (b' ⊗ₜ[B] ω)) =
      map (α'.comp α)
        (by rw [IsScalarTower.algebraMap_eq B B' B'', RingHom.comp_assoc, hB,
          ← RingHom.comp_assoc, hB', RingHom.comp_assoc])
        (by rw [IsScalarTower.algebraMap_eq B B' B'']; exact hcB'.comp hcB)
        ((b'' * algebraMap B' B'' b') ⊗ₜ[B] ω) :=
  map_comp α hB hcB α' hB' hcB' b'' b' ω

end Generic

section Polynomial

/-- The integer polynomial ring has the discrete uniformity in this coefficient-change example. -/
local instance polynomialIntUniformSpace : UniformSpace (Polynomial ℤ) := ⊥
/-- The polynomial ring modulo four has the discrete uniformity. -/
local instance polynomialZModFourUniformSpace : UniformSpace (Polynomial (ZMod 4)) := ⊥
/-- The coefficient ring modulo four has the discrete uniformity. -/
local instance zModFourUniformSpace : UniformSpace (ZMod 4) := ⊥
local instance : DiscreteUniformity (Polynomial ℤ) := ⟨rfl⟩
local instance : DiscreteUniformity (Polynomial (ZMod 4)) := ⟨rfl⟩
local instance : DiscreteUniformity (ZMod 4) := ⟨rfl⟩
local instance : IsAdicHom (algebraMap ℤ (Polynomial ℤ)) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance
local instance : IsAdicHom (algebraMap (ZMod 4) (Polynomial (ZMod 4))) :=
  IsAdicHom.of_discrete_iff.mpr inferInstance

-- This square changes both the coefficient ring and the polynomial ring.
example : mapSemilinear (Int.castRingHom (ZMod 4))
    (Polynomial.mapRingHom (Int.castRingHom (ZMod 4)))
    (by ext; simp) continuous_of_discreteTopology (D ℤ (Polynomial ℤ) Polynomial.X) =
      D (ZMod 4) (Polynomial (ZMod 4)) Polynomial.X := by simp

end Polynomial
