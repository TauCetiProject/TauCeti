/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PerfectoidSpace.SpaTilt
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.NormedField
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Gauge
public import TauCeti.RingTheory.Perfectoid.UniformTilt.OfHom
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Valuation.Continuous.Valued
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Checks for the tilting map on adic spectra

We exercise `TauCeti.PerfectoidSpace.spaTilt` on `ℂ_p`, products `ℂ_p × ℂ_p`, perfect
characteristic-`p` rings, and the zero ring:

* On `ℂ_p`, every point of `Spa (ℂ_p, ℂ_p°)` tilts to the valuation comparing elements of `ℂ_p♭`
  by the norm of their zeroth coordinate, and no ring homomorphism `ℂ_p♭ →+* ℂ_p` exists that could
  realise `spaTilt` as a `comap`.
* On `ℂ_p × ℂ_p`, tilting commutes with the pullbacks along both projections, and the compatible
  idempotent `(1, 0)` remains separated by the supports of the tilted projection pullbacks.
* For a perfect ring of characteristic `p`, `spaTilt` agrees with pullback along
  `Pair.tiltPairHomOfCharP` (`uniformTilt.equivOfCharP`) and is mutually inverse to pullback along
  `Pair.tiltPairHomOfCharPSymm`, while over a zero ring both domain and codomain are empty.
-/

public section

open Filter Topology TauCeti.Huber TauCeti.Perfectoid TauCeti.PerfectoidSpace
  TauCeti.ValuationSpectrum

namespace TauCeti.Examples.SpaTilt

section PadicComplexAndProduct

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  (RingHom.id ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_id

section PadicComplex

/-- The canonical valuation of `ℂ_p` defines a point of `Spa (ℂ_p, ℂ_p°)`. -/
private noncomputable def padicComplexNormPoint : spa (Pair.powerBounded ℂ_[p]).plus :=
  ⟨ofValuation (Valued.v : Valuation ℂ_[p] NNReal), (mem_spa_iff _ _).mpr ⟨by
    rw [isContinuous_ofValuation_iff]
    exact Valued.isContinuous_v,
  fun a ha ↦ by
    rw [vle_ofValuation, ← NNReal.coe_le_coe, PadicComplex.valuation_coe,
      PadicComplex.valuation_coe, norm_one, ← isPowerBounded_iff_norm_le_one]
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at ha
    exact ha⟩⟩

-- On `ℂ_p`, `spaTilt` compares `f, g : ℂ_p♭` by `‖f♯‖ ≤ ‖g♯‖`.
example (x : spa (Pair.powerBounded ℂ_[p]).plus) (f g : uniformTilt p ℂ_[p]) :
    (spaTilt (p := p) (Pair.powerBounded ℂ_[p]) x).1.toValuativeRel.vle f g ↔
      ‖uniformTilt.coeff p ℂ_[p] 0 f‖ ≤ ‖uniformTilt.coeff p ℂ_[p] 0 g‖ := by
  rw [spaTilt_vle_iff, vle_iff_norm_le_of_mem_spa ((Pair.powerBounded_plus (A := ℂ_[p])) ▸ x.2)]

-- Uniqueness: `spaTilt` of the norm point equals any point comparing elements of `ℂ_p♭` by `‖·♯‖`.
example (y : spa ((Pair.powerBounded ℂ_[p]).tilt (p := p)).plus)
    (hy : ∀ f g, y.1.toValuativeRel.vle f g ↔
      ‖uniformTilt.coeff p ℂ_[p] 0 f‖ ≤ ‖uniformTilt.coeff p ℂ_[p] 0 g‖) :
    spaTilt (p := p) (Pair.powerBounded ℂ_[p]) (padicComplexNormPoint p) = y :=
  spaTilt_eq_of_vle_iff (Pair.powerBounded ℂ_[p]) fun f g ↦
    (hy f g).trans (vle_iff_norm_le_of_mem_spa
      ((Pair.powerBounded_plus (A := ℂ_[p])) ▸ (padicComplexNormPoint p).2) _ _).symm

-- Preimage of a rational subset `R(1 / ϖ♭)` on `ℂ_p` puts the compatible-root parameter `ϖ`
-- in the denominator.
open scoped Classical in
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    spaTilt (p := p) (Pair.powerBounded ℂ_[p]) ⁻¹'
        (Subtype.val ⁻¹'
          rationalSubset ((Pair.powerBounded ℂ_[p]).tilt (p := p)).plus {1} ϖ.toTilt) =
      Subtype.val ⁻¹' rationalSubset (Pair.powerBounded ℂ_[p]).plus {1} (ϖ.root 0) := by
  rw [spaTilt_preimage_rationalSubset, Finset.image_singleton, map_one,
    PseudoUniformizerRoots.coeff_toTilt]

-- Non-example: there is no ring homomorphism `ℂ_p♭ →+* ℂ_p`, so `spaTilt` is not a `comap`.
example : IsEmpty (uniformTilt p ℂ_[p] →+* ℂ_[p]) := by
  refine ⟨fun φ ↦ ?_⟩
  have hzero : (p : ℂ_[p]) = 0 := by
    rw [← map_natCast φ p, CharP.cast_eq_zero (uniformTilt p ℂ_[p]) p, map_zero]
  exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero hzero

end PadicComplex

section Product

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p] × ℂ_[p])) :=
  ⟨IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p⟩

local instance : IsTateRing (uniformTilt p (ℂ_[p] × ℂ_[p])) :=
  (RingHom.id (ℂ_[p] × ℂ_[p])).isTateRing_uniformTilt (p := p) continuous_id

/-- The first projection `ℂ_p × ℂ_p → ℂ_p` as a morphism of Huber pairs. -/
private noncomputable def fstPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.fst _ _
  continuous_toRingHom := continuous_fst
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).1

/-- The second projection `ℂ_p × ℂ_p → ℂ_p` as a morphism of Huber pairs. -/
private noncomputable def sndPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.snd _ _
  continuous_toRingHom := continuous_snd
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).2

-- Tilting commutes with pullback along both projections of `ℂ_p × ℂ_p`.
example (x : spa (Pair.powerBounded ℂ_[p]).plus) :
    spaTilt (p := p) (Pair.powerBounded (ℂ_[p] × ℂ_[p])) ((fstPair p).spaComap x) =
      ((fstPair p).tilt (p := p)).spaComap
        (spaTilt (p := p) (Pair.powerBounded ℂ_[p]) x) ∧
    spaTilt (p := p) (Pair.powerBounded (ℂ_[p] × ℂ_[p])) ((sndPair p).spaComap x) =
      ((sndPair p).tilt (p := p)).spaComap
        (spaTilt (p := p) (Pair.powerBounded ℂ_[p]) x) :=
  ⟨spaTilt_spaComap (fstPair p) x, spaTilt_spaComap (sndPair p) x⟩

-- The compatible idempotent `(1, 0)` distinguishes the two tilted projection pullbacks.
example (x : spa (Pair.powerBounded ℂ_[p]).plus) :
    let e : uniformTilt p (ℂ_[p] × ℂ_[p]) :=
      uniformTilt.mk (fun _ ↦ (1, 0)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])
    e ∉ (((fstPair p).tilt (p := p)).spaComap
        (spaTilt (p := p) (Pair.powerBounded ℂ_[p]) x)).1.supp ∧
      e ∈ (((sndPair p).tilt (p := p)).spaComap
        (spaTilt (p := p) (Pair.powerBounded ℂ_[p]) x)).1.supp := by
  intro e
  let := x.1.toValuativeRel
  simp [fstPair, sndPair, e]

end Product

end PadicComplexAndProduct

section CharP

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Fact (IsTopologicallyNilpotent (p : B))] [CharP B p] [PerfectRing B p]
  [IsTateRing (uniformTilt p B)]

-- For a perfect ring of characteristic `p`, `spaTilt` agrees with pullback along
-- `Pair.tiltPairHomOfCharP`, is mutually inverse to pullback along `Pair.tiltPairHomOfCharPSymm`,
-- and supports transform by `equivOfCharP`.
example (P : Pair B) (x : spa P.plus) (y : spa (P.tilt (p := p)).plus) (b : B) :
    spaTilt (p := p) P = (Pair.tiltPairHomOfCharP (p := p) P).spaComap ∧
      (Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap (spaTilt (p := p) P x) = x ∧
      spaTilt (p := p) P ((Pair.tiltPairHomOfCharPSymm (p := p) P).spaComap y) = y ∧
      ((uniformTilt.equivOfCharP p B).symm b ∈ (spaTilt (p := p) P x).1.supp ↔
        b ∈ x.1.supp) := by
  refine ⟨spaTilt_eq_spaComap_tiltPairHomOfCharP P, by simp, by simp, ?_⟩
  rw [mem_supp_spaTilt_iff, ← uniformTilt.equivOfCharP_apply, RingEquiv.apply_symm_apply]

end CharP

section Zero

variable {p : ℕ} [Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Subsingleton B] [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]

-- Over a zero ring, both `Spa(B, B⁺)` and `Spa(B♭, B♭⁺)` are empty.
example (P : Pair B) :
    IsEmpty (spa P.plus) ∧ IsEmpty (spa (P.tilt (p := p)).plus) :=
  ⟨inferInstance, inferInstance⟩

end Zero

end TauCeti.Examples.SpaTilt
