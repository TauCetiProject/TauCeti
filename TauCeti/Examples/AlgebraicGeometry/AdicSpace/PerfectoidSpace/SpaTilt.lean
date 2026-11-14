/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PerfectoidSpace.SpaTilt
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.NormedField
public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.RingTheory.Perfectoid.UniformTilt.OfHom
import TauCeti.Topology.Algebra.TopologicallyNilpotent.Basic

/-!
# Checks for the tilting map on adic spectra

We exercise `spaTilt` on concrete perfectoid Huber pairs:
1. On `(ℂ_p, ℂ_p°)` we exhibit an inhabited point `x₀`, verify that `spaTilt` compares elements of
   `ℂ_p♭` by the `p`-adic norm of their zeroth coordinates, and check `0 < |(x₀♭)(ϖ♭)| < 1` for a
   compatible-root parameter `ϖ`.
2. On `(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°)` we construct two distinct inhabited points `x₁, x₂` via the
   projections, separate their tilts using the compatible idempotent `(1, 0)`, and verify that the
   preimage under `spaTilt` of the rational subset `R({e, ψ}/ψ)` is a nonempty proper rational open
   subset containing `x₂` and excluding `x₁`.
3. On the characteristic-`p` perfectoid ring `ℂ_p♭` we check `spaTilt_eq_id_of_charP` and
   `spaTiltHomeomorphOfCharP` on an inhabited spectrum.
4. We verify the mixed-characteristic non-example that no ring homomorphism or Huber-pair morphism
   `(ℂ_p♭, ℂ_p♭°) → (ℂ_p, ℂ_p°)` exists, so `spaTilt` cannot arise as `Pair.Hom.spaComap`.
5. We test the uniqueness characterisation `spaTilt_eq_iff_forall_vle` and the zero-ring boundary
   case.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid TauCeti.PerfectoidSpace TauCeti.ValuationSpectrum

namespace TauCeti.Examples.PerfectoidSpaceSpaTilt

variable (p : ℕ) [Fact p.Prime]

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  IsPerfectoidTateRing.isTateRing_uniformTilt p ℂ_[p]

local instance : IsPerfectoidTateRing p (uniformTilt p ℂ_[p]) :=
  IsPerfectoidTateRing.isPerfectoidTateRing_uniformTilt p ℂ_[p]

/-- An inhabited point of `Spa(ℂ_p, ℂ_p°)`. -/
private noncomputable def padicComplexPoint : spa (Pair.powerBounded ℂ_[p]).plus :=
  (Set.nonempty_coe_sort.mpr <| Set.nonempty_iff_ne_empty.mpr fun h ↦
    not_subsingleton ℂ_[p]
      ((spa_eq_empty_iff_subsingleton (Pair.powerBounded ℂ_[p]).plus
        (Pair.powerBounded ℂ_[p]).isRingOfIntegralElements).mp h)).some

private theorem padicComplexPoint_mem :
    (padicComplexPoint p).1 ∈ spa (powerBoundedSubring ℂ_[p]) := by
  simpa only [Pair.powerBounded_plus] using (padicComplexPoint p).2

-- At the point of `Spa(ℂ_p, ℂ_p°)`, `spaTilt` compares elements of `ℂ_p♭` by the `p`-adic norms of
-- their zeroth coordinates.
example (f g : uniformTilt p ℂ_[p]) :
    (spaTilt p (Pair.powerBounded ℂ_[p]) (padicComplexPoint p)).1.toValuativeRel.vle f g ↔
      ‖uniformTilt.coeff p ℂ_[p] 0 f‖ ≤ ‖uniformTilt.coeff p ℂ_[p] 0 g‖ := by
  rw [spaTilt_vle_iff]
  exact vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p) _ _

-- A tilted compatible-root parameter satisfies `0 < |(x₀♭)(ϖ♭)| < 1` at `padicComplexPoint`.
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    (spaTilt p (Pair.powerBounded ℂ_[p]) (padicComplexPoint p)).1.toValuativeRel.vlt 0 ϖ.toTilt ∧
      (spaTilt p (Pair.powerBounded ℂ_[p]) (padicComplexPoint p)).1.toValuativeRel.vlt
        ϖ.toTilt 1 := by
  obtain ⟨hne, hlt1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  rw [spaTilt_vlt_iff, spaTilt_vlt_iff, ← valuation_lt_iff, ← valuation_lt_iff, ← not_le, ← not_le,
    valuation_le_iff, valuation_le_iff, vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p),
    vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p)]
  simp only [uniformTilt.coeff_zero, PseudoUniformizerRoots.coeff_toTilt, map_one, norm_zero,
    norm_one, not_le]
  exact ⟨norm_pos_iff.mpr hne, hlt1⟩

-- At `padicComplexPoint`, the tilted point has trivial support (`ℂ_p♭` is an integral domain),
-- `spaTilt` is spectral, and rational subsets of `Spa(ℂ_p♭, ℂ_p♭°)` admit normalised integral
-- presentations with `ϖ.toTilt ^ N`.
open scoped Classical in
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) (s₀ : uniformTilt p ℂ_[p]) :
    let P := Pair.powerBounded ℂ_[p]
    (spaTilt p P (padicComplexPoint p)).1.supp = ⊥ ∧
      IsSpectralMap (spaTilt p P) ∧
      ∃ (T : Finset (uniformTilt p ℂ_[p])) (s : uniformTilt p ℂ_[p]) (N : ℕ),
        0 < N ∧
        ((insert (ϖ.toTilt ^ N) T : Finset (uniformTilt p ℂ_[p])) : Set (uniformTilt p ℂ_[p])) ⊆
          (P.tilt (p := p)).plus ∧
        s ∈ (P.tilt (p := p)).plus ∧
        rationalSubset (P.tilt (p := p)).plus (insert (ϖ.toTilt ^ N) T) s =
          rationalSubset (P.tilt (p := p)).plus {1} s₀ := by
  intro P
  refine ⟨Ideal.ext fun f ↦ ?_, isSpectralMap_spaTilt p P,
    TauCeti.PerfectoidSpace.exists_rationalSubset_eq_insert_pseudoUniformizer_pow P ϖ
      (by simp) s₀⟩
  rw [mem_supp_spaTilt_iff, Ideal.mem_bot, ValuationSpectrum.mem_supp_iff,
    vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p), norm_zero, norm_le_zero_iff,
    uniformTilt.coeff_zero_eq_zero_iff]

section TwoPointProduct

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p] × ℂ_[p])) :=
  ⟨Prod.isTopologicallyNilpotent_iff.mpr
    ⟨IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p,
      IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p⟩⟩

local instance : IsTateRing (uniformTilt p (ℂ_[p] × ℂ_[p])) :=
  (RingHom.id (ℂ_[p] × ℂ_[p])).isTateRing_uniformTilt (p := p) continuous_id

private noncomputable def fstPair :
    Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p])) (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.fst _ _
  continuous_toRingHom := continuous_fst
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).1

private noncomputable def sndPair :
    Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p])) (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.snd _ _
  continuous_toRingHom := continuous_snd
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).2

private noncomputable def prodPointFst : spa (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus :=
  (fstPair p).spaComap (padicComplexPoint p)

private noncomputable def prodPointSnd : spa (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus :=
  (sndPair p).spaComap (padicComplexPoint p)

private noncomputable def idempotentTilt : uniformTilt p (ℂ_[p] × ℂ_[p]) :=
  uniformTilt.mk (fun _ ↦ (1, 0)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])

private noncomputable def diagParamTilt (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    uniformTilt p (ℂ_[p] × ℂ_[p]) :=
  uniformTilt.mk (fun n ↦ (ϖ.root n, ϖ.root n))
    (fun n ↦ Prod.ext (ϖ.root_succ_pow n) (ϖ.root_succ_pow n))

-- Naturality separates the tilted images of `prodPointFst` and `prodPointSnd`, and the rational
-- preimage `spaTilt ⁻¹' R({e, ψ}/ψ)` is a nonempty proper rational open containing `prodPointSnd`
-- and excluding `prodPointFst`.
open scoped Classical in
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    let P := Pair.powerBounded (ℂ_[p] × ℂ_[p])
    let U : Set (spa (P.tilt (p := p)).plus) :=
      Subtype.val ⁻¹' rationalSubset (P.tilt (p := p)).plus
        {idempotentTilt p, diagParamTilt p ϖ} (diagParamTilt p ϖ)
    spaTilt p P ⁻¹' U ∈ spaRationalFamily P.plus ∧
      prodPointSnd p ∈ spaTilt p P ⁻¹' U ∧
      prodPointFst p ∉ spaTilt p P ⁻¹' U ∧
      spaTilt p P (prodPointFst p) ≠ spaTilt p P (prodPointSnd p) ∧
      spaTilt p P (prodPointFst p) =
        ((fstPair p).tilt (p := p)).spaComap
          (spaTilt p (Pair.powerBounded ℂ_[p]) (padicComplexPoint p)) := by
  intro P U
  have hψ : IsUnit (diagParamTilt p ϖ) := by
    rw [uniformTilt.isUnit_iff_coeff_zero, diagParamTilt, uniformTilt.coeff_mk]
    exact Prod.isUnit_iff.mpr
      ⟨ϖ.isPseudoUniformizer_root_zero.isUnit, ϖ.isPseudoUniformizer_root_zero.isUnit⟩
  have hrat : spaTilt p P ⁻¹' U ∈ spaRationalFamily P.plus :=
    spaTilt_preimage_rationalSubset_mem_spaRationalFamily_of_exists_isUnit P
      ⟨diagParamTilt p ϖ, by simp, hψ⟩ (diagParamTilt p ϖ)
  obtain ⟨hne, hlt1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  have hmem₂ : prodPointSnd p ∈ spaTilt p P ⁻¹' U := by
    change (spaTilt p P (prodPointSnd p)).1 ∈ rationalSubset (P.tilt (p := p)).plus
      {idempotentTilt p, diagParamTilt p ϖ} (diagParamTilt p ϖ)
    rw [mem_rationalSubset_iff]
    refine ⟨(spaTilt p P (prodPointSnd p)).2, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · rw [spaTilt_vle_iff, prodPointSnd, Pair.Hom.spaComap_val, comap_vle]
        simp only [sndPair, idempotentTilt, diagParamTilt, uniformTilt.coeff_mk, RingHom.coe_snd]
        rw [vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p), norm_zero]
        exact norm_nonneg _
      · rw [Finset.mem_singleton.mp hf]
        exact (spaTilt p P (prodPointSnd p)).1.toValuativeRel.vle_refl _
    · rw [spaTilt_vle_iff, uniformTilt.coeff_zero, prodPointSnd, Pair.Hom.spaComap_val, comap_vle]
      simp only [sndPair, diagParamTilt, uniformTilt.coeff_mk, map_zero, RingHom.coe_snd]
      rw [vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p), norm_zero, not_le]
      exact norm_pos_iff.mpr hne
  have hnmem₁ : prodPointFst p ∉ spaTilt p P ⁻¹' U := by
    intro hmem
    have hle := ((mem_rationalSubset_iff _ _ _ _).mp hmem).2.1
      (idempotentTilt p) (Finset.mem_insert_self _ _)
    rw [spaTilt_vle_iff, prodPointFst, Pair.Hom.spaComap_val, comap_vle] at hle
    simp only [fstPair, idempotentTilt, diagParamTilt, uniformTilt.coeff_mk,
      RingHom.coe_fst] at hle
    rw [vle_iff_norm_le_of_mem_spa (padicComplexPoint_mem p), norm_one] at hle
    exact hlt1.not_ge hle
  refine ⟨hrat, hmem₂, hnmem₁, fun heq ↦ hnmem₁ ?_, spaTilt_spaComap (fstPair p) _⟩
  change spaTilt p P (prodPointFst p) ∈ U
  rw [heq]
  exact hmem₂

end TwoPointProduct

section CharacteristicP

local instance : IsUniform (uniformTilt p ℂ_[p]) :=
  IsPerfectoidTateRing.isUniform p

local instance : Fact (IsTopologicallyNilpotent (p : uniformTilt p ℂ_[p])) :=
  ⟨IsPerfectoidTateRing.isTopologicallyNilpotent_natCast p⟩

local instance : IsTateRing (uniformTilt p (uniformTilt p ℂ_[p])) :=
  IsPerfectoidTateRing.isTateRing_uniformTilt p (uniformTilt p ℂ_[p])

-- On the concrete characteristic-`p` perfectoid ring `ℂ_p♭`, `spaTilt` is the identity up to the
-- canonical Huber-pair isomorphism `tiltEquivSymmHom`, and `spaTiltHomeomorphOfCharP` is a
-- homeomorphism on an inhabited spectrum.
example :
    let P := Pair.powerBounded (uniformTilt p ℂ_[p])
    Nonempty (spa P.plus) ∧
      (P.tiltEquivSymmHom (p := p)).spaComap ∘ spaTilt p P = _root_.id ∧
      IsHomeomorph (spaTilt p P) := by
  intro P
  have hne : Nonempty (spa P.plus) :=
    Set.nonempty_coe_sort.mpr <| Set.nonempty_iff_ne_empty.mpr fun h ↦
      not_subsingleton (uniformTilt p ℂ_[p])
        ((spa_eq_empty_iff_subsingleton P.plus P.isRingOfIntegralElements).mp h)
  exact ⟨hne, spaTilt_eq_id_of_charP P, isHomeomorph_spaTilt_of_charP P⟩

end CharacteristicP

-- Non-example: in mixed characteristic there is no ring homomorphism `ℂ_p♭ →+* ℂ_p`, hence no
-- morphism of Huber pairs `(ℂ_p, ℂ_p°).tilt → (ℂ_p, ℂ_p°)` whose `spaComap` could produce
-- `spaTilt`.
example :
    IsEmpty (uniformTilt p ℂ_[p] →+* ℂ_[p]) ∧
      IsEmpty (Pair.Hom ((Pair.powerBounded ℂ_[p]).tilt (p := p)) (Pair.powerBounded ℂ_[p])) := by
  have hno : IsEmpty (uniformTilt p ℂ_[p] →+* ℂ_[p]) := ⟨fun φ ↦ by
    have hp0 : (p : uniformTilt p ℂ_[p]) = 0 := CharP.cast_eq_zero _ p
    have hp_im : φ (p : uniformTilt p ℂ_[p]) = (p : ℂ_[p]) := map_natCast φ p
    rw [hp0, map_zero] at hp_im
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp_im.symm⟩
  exact ⟨hno, ⟨fun f ↦ hno.false f.toRingHom⟩⟩

-- Uniqueness characterisation: `spaTilt p P x` is uniquely determined in `Spa(P.tilt)` by its
-- sharp comparisons.
example (y : spa ((Pair.powerBounded ℂ_[p]).tilt (p := p)).plus)
    (h : ∀ f g : uniformTilt p ℂ_[p],
      y.1.toValuativeRel.vle f g ↔
        (padicComplexPoint p).1.toValuativeRel.vle
          (uniformTilt.coeff p ℂ_[p] 0 f) (uniformTilt.coeff p ℂ_[p] 0 g)) :
    y = spaTilt p (Pair.powerBounded ℂ_[p]) (padicComplexPoint p) :=
  (spaTilt_eq_iff_forall_vle (p := p) _ _ _).mpr h

section ZeroRing

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
  [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B]
  [Subsingleton B] [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]

-- `spaTilt` typechecks on the zero ring (where `CharP B p` would be false), and both spectra are
-- empty.
example (P : Pair B) :
    IsEmpty (spa P.plus) ∧ IsEmpty (spa (P.tilt (p := p)).plus) ∧
      Continuous (spaTilt p P) := by
  have hemp₁ : spa P.plus = ∅ :=
    (spa_eq_empty_iff_subsingleton P.plus P.isRingOfIntegralElements).mpr inferInstance
  have : Subsingleton (uniformTilt p B) :=
    ⟨fun x y ↦ uniformTilt.ext fun _ ↦ Subsingleton.elim _ _⟩
  have hemp₂ : spa (P.tilt (p := p)).plus = ∅ :=
    (spa_eq_empty_iff_subsingleton _ (P.tilt (p := p)).isRingOfIntegralElements).mpr inferInstance
  exact ⟨Set.isEmpty_coe_sort.mpr hemp₁, Set.isEmpty_coe_sort.mpr hemp₂, continuous_spaTilt p P⟩

end ZeroRing

end TauCeti.Examples.PerfectoidSpaceSpaTilt
