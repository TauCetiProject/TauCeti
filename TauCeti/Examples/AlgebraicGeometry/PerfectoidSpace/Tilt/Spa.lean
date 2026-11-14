/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PerfectoidSpace.Tilt.Spa
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.NormedField
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Field
public import TauCeti.RingTheory.Perfectoid.UniformTilt.OfHom
public import TauCeti.RingTheory.Perfectoid.Padic
public import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# Concrete checks for the tilting map on adic spectra

We exercise the tilting map `spaTilt` across five families of concrete examples and non-examples:

1. **Inhabitedness and norm comparison on `Spa(ℂ_p, ℂ_p°)`**: both `Spa(ℂ_p, ℂ_p°)` and its tilted
   target `Spa(ℂ_p♭, ℂ_p♭°)` are nonempty, every tilted point compares elements of `ℂ_p♭` by the
   `ℂ_p`-norm of their zeroth coordinates (`‖x♯‖ ≤ ‖y♯‖`), strictly separates powers of a
   compatible-root pseudouniformiser (`v(ϖ♭²) < v(ϖ♭) < 1`), and has trivial support.
2. **Functoriality and point separation on `Spa(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°)`**: pulling back an
   inhabited point of `Spa(ℂ_p, ℂ_p°)` along the two coordinate projections produces two points
   whose images under `Pair.spaTilt` remain distinct on `Spa((ℂ_p × ℂ_p)♭, (ℂ_p × ℂ_p)♭°)`,
   separated by the compatible idempotent `(1, 0)`.
3. **Rational-subset preimages on `ℂ_p`**: a concrete rational subset `R({f, ϖ♭} / ϖ♭)` pulls back
   to `R({f♯, ϖ} / ϖ)` inside `spaRationalFamily`, and every rational subset of `Spa(ℂ_p♭, ℂ_p♭°)`
   pulls back to `spaRationalFamily` of `Spa(ℂ_p, ℂ_p°)`.
4. **Characteristic `p` and the zero ring**: on the characteristic-`p` perfectoid field
   `tiltField p ℂ_p`, `spaTilt` composes with `spaComap` of `(equivOfCharP).symm` to the identity
   and is a homeomorphism; on any trivial ring `B`, both adic spectra are empty and `Pair.spaTilt`
   is bijective without requiring the inconsistent hypothesis `CharP B p`.
5. **Non-example in mixed characteristic**: `IsEmpty (uniformTilt p ℂ_p →+* ℂ_p)` and hence
   `IsEmpty (Pair.Hom ((Pair.powerBounded ℂ_p).tilt) (Pair.powerBounded ℂ_p))`, showing that the
   continuous map `Pair.spaTilt` on `Spa(ℂ_p, ℂ_p°)` cannot arise as `Pair.Hom.spaComap` of any
   morphism of Huber pairs.
-/

public section

open TauCeti.Huber TauCeti.Perfectoid TauCeti.PerfectoidSpace TauCeti.ValuationSpectrum

namespace TauCeti.Examples.PerfectoidSpaceTiltSpa

variable (p : ℕ) [Fact p.Prime]

/-! ### 1. Inhabitedness and norm comparison on `Spa(ℂ_p, ℂ_p°)` -/

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p])) :=
  ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one (PadicComplex.norm_p_lt_one p)⟩

local instance : IsTateRing (uniformTilt p ℂ_[p]) :=
  (RingHom.id ℂ_[p]).isTateRing_uniformTilt (p := p) continuous_id

/-- `Spa(ℂ_p, ℂ_p°)` is genuinely inhabited, since `ℂ_p` is Hausdorff and nontrivial. -/
theorem nonempty_spa_padicComplex :
    Nonempty (spa (Pair.powerBounded ℂ_[p]).plus) := by
  rw [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, Ne,
    spa_eq_empty_iff_subsingleton _ (Pair.powerBounded ℂ_[p]).isRingOfIntegralElements]
  exact not_subsingleton ℂ_[p]

/-- Consequently `Spa(ℂ_p♭, ℂ_p♭°)` is inhabited via `Pair.spaTilt`. -/
theorem nonempty_spa_tilt_padicComplex :
    Nonempty (spa ((Pair.powerBounded ℂ_[p]).tilt (p := p)).plus) :=
  (nonempty_spa_padicComplex p).map ((Pair.powerBounded ℂ_[p]).spaTilt p)

/-- At any point of `Spa(ℂ_p, ℂ_p°)`, the tilted valuation compares elements of `ℂ_p♭` by the
`ℂ_p`-norm of their zeroth coordinates. -/
example (x : spa (Pair.powerBounded ℂ_[p]).plus) (f g : uniformTilt p ℂ_[p]) :
    ((Pair.powerBounded ℂ_[p]).spaTilt p x).1.toValuativeRel.vle f g ↔
      ‖uniformTilt.coeff p ℂ_[p] 0 f‖ ≤ ‖uniformTilt.coeff p ℂ_[p] 0 g‖ := by
  have hx : x.1 ∈ spa (powerBoundedSubring ℂ_[p]) := by
    simpa only [Pair.powerBounded_plus] using x.2
  rw [Pair.spaTilt_val, spaTilt_vle_iff, vle_iff_norm_le_of_mem_spa hx]

/-- Powers of a compatible-root pseudouniformiser `w` are strictly ordered at an inhabited tilted
point of `Spa(ℂ_p♭, ℂ_p♭°)`: `v(w²) < v(w) < 1`. -/
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) :
    ∃ x : spa (Pair.powerBounded ℂ_[p]).plus,
      let w := uniformTilt.mk ϖ.root ϖ.root_succ_pow
      let y := ((Pair.powerBounded ℂ_[p]).spaTilt p x).1
      y.toValuativeRel.vlt (w ^ 2) w ∧ y.toValuativeRel.vlt w 1 := by
  obtain ⟨x⟩ := nonempty_spa_padicComplex p
  have hx : x.1 ∈ spa (powerBoundedSubring ℂ_[p]) := by
    simpa only [Pair.powerBounded_plus] using x.2
  obtain ⟨h0, h1⟩ := isPseudoUniformizer_iff_norm_lt_one.mp ϖ.isPseudoUniformizer_root_zero
  refine ⟨x, ?_, ?_⟩
  · change ¬ ((Pair.powerBounded ℂ_[p]).spaTilt p x).1.toValuativeRel.vle
      (uniformTilt.mk ϖ.root ϖ.root_succ_pow) (uniformTilt.mk ϖ.root ϖ.root_succ_pow ^ 2)
    rw [Pair.spaTilt_val, spaTilt_vle_iff, vle_iff_norm_le_of_mem_spa hx, map_pow,
      uniformTilt.coeff_mk, norm_pow, not_le]
    exact pow_lt_self_of_lt_one₀ (norm_pos_iff.mpr h0) h1 (by decide)
  · change ¬ ((Pair.powerBounded ℂ_[p]).spaTilt p x).1.toValuativeRel.vle
      1 (uniformTilt.mk ϖ.root ϖ.root_succ_pow)
    rw [Pair.spaTilt_val, spaTilt_vle_iff, vle_iff_norm_le_of_mem_spa hx, map_one,
      uniformTilt.coeff_mk, norm_one, not_le]
    exact h1

/-- Every tilted point of `Spa(ℂ_p, ℂ_p°)` has trivial prime support in `ℂ_p♭`. -/
example (x : spa (Pair.powerBounded ℂ_[p]).plus) :
    ((Pair.powerBounded ℂ_[p]).spaTilt p x).1.supp = ⊥ := by
  have hx : x.1 ∈ spa (powerBoundedSubring ℂ_[p]) := by
    simpa only [Pair.powerBounded_plus] using x.2
  ext f
  rw [Pair.spaTilt_val, ValuationSpectrum.mem_supp_iff, spaTilt_vle_iff, uniformTilt.coeff_zero,
    vle_iff_norm_le_of_mem_spa hx, norm_zero, norm_le_zero_iff, uniformTilt.coeff_zero_eq_zero_iff,
    Ideal.mem_bot]

/-! ### 2. Functoriality and point separation on `Spa(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°)` -/

local instance : Fact (IsTopologicallyNilpotent (p : ℂ_[p] × ℂ_[p])) :=
  ⟨Prod.isTopologicallyNilpotent_iff.mpr (by
    simpa using And.intro (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p]))
      (Fact.out : IsTopologicallyNilpotent (p : ℂ_[p])))⟩

local instance : IsTateRing (uniformTilt p (ℂ_[p] × ℂ_[p])) :=
  (RingHom.id (ℂ_[p] × ℂ_[p])).isTateRing_uniformTilt (p := p) continuous_id

/-- First projection `(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°) → (ℂ_p, ℂ_p°)` as a Huber-pair morphism. -/
private noncomputable def fstPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.fst _ _
  continuous_toRingHom := continuous_fst
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).1

/-- Second projection `(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°) → (ℂ_p, ℂ_p°)` as a Huber-pair morphism. -/
private noncomputable def sndPair : Pair.Hom (Pair.powerBounded (ℂ_[p] × ℂ_[p]))
    (Pair.powerBounded ℂ_[p]) where
  toRingHom := RingHom.snd _ _
  continuous_toRingHom := continuous_snd
  map_mem_plus _ hx := by
    rw [Pair.powerBounded_plus, mem_powerBoundedSubring] at hx ⊢
    exact (isPowerBounded_prod_iff.mp hx).2

/-- Two inhabited points of `Spa(ℂ_p × ℂ_p, (ℂ_p × ℂ_p)°)` pulled back from `Spa(ℂ_p, ℂ_p°)` along
the two projections remain distinct after applying `Pair.spaTilt`. -/
example :
    ∃ x₁ x₂ : spa (Pair.powerBounded (ℂ_[p] × ℂ_[p])).plus,
      (Pair.powerBounded (ℂ_[p] × ℂ_[p])).spaTilt p x₁ ≠
        (Pair.powerBounded (ℂ_[p] × ℂ_[p])).spaTilt p x₂ := by
  obtain ⟨x₀⟩ := nonempty_spa_padicComplex p
  have hx₀ : x₀.1 ∈ spa (powerBoundedSubring ℂ_[p]) := by
    simpa only [Pair.powerBounded_plus] using x₀.2
  refine ⟨(fstPair p).spaComap x₀, (sndPair p).spaComap x₀, ?_⟩
  rw [(fstPair p).spaTilt_spaComap, (sndPair p).spaTilt_spaComap]
  intro h
  let e : uniformTilt p (ℂ_[p] × ℂ_[p]) :=
    uniformTilt.mk (fun _ ↦ (1, 0)) (fun _ ↦ by simp [(Fact.out : p.Prime).ne_zero])
  have he :
      (((fstPair p).tilt (p := p)).spaComap
          ((Pair.powerBounded ℂ_[p]).spaTilt p x₀)).1.toValuativeRel.vle e 0 ↔
        (((sndPair p).tilt (p := p)).spaComap
          ((Pair.powerBounded ℂ_[p]).spaTilt p x₀)).1.toValuativeRel.vle e 0 := by
    rw [h]
  rw [Pair.Hom.spaComap_val, comap_vle, Pair.Hom.spaComap_val, comap_vle, map_zero, map_zero,
    Pair.spaTilt_val, spaTilt_vle_iff, spaTilt_vle_iff, uniformTilt.coeff_zero,
    vle_iff_norm_le_of_mem_spa hx₀, vle_iff_norm_le_of_mem_spa hx₀, norm_zero,
    Pair.Hom.toRingHom_tilt, Pair.Hom.toRingHom_tilt, uniformTilt.coeff_map,
    uniformTilt.coeff_map] at he
  simp only [fstPair, sndPair, e, uniformTilt.coeff_mk, RingHom.coe_fst, RingHom.coe_snd,
    norm_one, norm_zero] at he
  exact absurd (he.mpr le_rfl) (by norm_num)

/-! ### 3. Rational-subset preimages on `ℂ_p` -/

open scoped Classical in
/-- A concrete rational subset `R({f, w} / w)` on `Spa(ℂ_p♭, ℂ_p♭°)` pulls back along `spaTilt`
to `R({f♯, ϖ} / ϖ)` and belongs to `spaRationalFamily` of `Spa(ℂ_p, ℂ_p°)`. -/
example (ϖ : PseudoUniformizerRoots p ℂ_[p]) (f : uniformTilt p ℂ_[p]) :
    let P := Pair.powerBounded ℂ_[p]
    let w := uniformTilt.mk ϖ.root ϖ.root_succ_pow
    let U := (Subtype.val : spa (P.tilt (p := p)).plus → _) ⁻¹'
      rationalSubset (P.tilt (p := p)).plus ({f, w} : Finset (uniformTilt p ℂ_[p])) w
    P.spaTilt p ⁻¹' U =
      (Subtype.val : spa P.plus → _) ⁻¹'
        rationalSubset P.plus {uniformTilt.coeff p ℂ_[p] 0 f, ϖ.root 0} (ϖ.root 0) ∧
    P.spaTilt p ⁻¹' U ∈ spaRationalFamily P.plus := by
  dsimp only
  constructor
  · rw [(Pair.powerBounded ℂ_[p]).spaTilt_preimage_rationalSubset]
    simp
  · refine (Pair.powerBounded ℂ_[p]).spaTilt_preimage_mem_spaRationalFamily (p := p)
      (mem_spaRationalFamily_iff.mpr ⟨{f, uniformTilt.mk ϖ.root ϖ.root_succ_pow},
        uniformTilt.mk ϖ.root ϖ.root_succ_pow, ?_, rfl⟩)
    have hu : IsUnit (uniformTilt.mk ϖ.root ϖ.root_succ_pow) :=
      uniformTilt.isUnit_iff_coeff_zero.mpr
        (by simpa only [uniformTilt.coeff_mk] using ϖ.isPseudoUniformizer_root_zero.isUnit)
    rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hu]
    simp [isOpen_univ]

/-! ### 4. Characteristic `p` and the zero ring -/

section CharacteristicP

local instance : Fact (IsTopologicallyNilpotent (p : tiltField p ℂ_[p])) :=
  ⟨by rw [CharP.cast_eq_zero]; exact IsTopologicallyNilpotent.zero⟩

/-- On the characteristic-`p` perfectoid field `tiltField p ℂ_p`, `spaTilt` is a homeomorphism and
composes with `spaComap` of `(equivOfCharP).symm` to the identity. -/
example :
    let hplus := isRingOfIntegralElements_powerBoundedSubring (tiltField p ℂ_[p])
    IsHomeomorph (spaTilt p hplus) ∧
      (ValuationSpectrum.spaComap
        ((uniformTilt.equivOfCharP p (tiltField p ℂ_[p])).symm :
          tiltField p ℂ_[p] →+* uniformTilt p (tiltField p ℂ_[p]))
        (uniformTilt.continuous_equivOfCharP_symm p (tiltField p ℂ_[p]))
        (powerBoundedSubring (tiltField p ℂ_[p])) (uniformTilt.plusSubring p hplus)
        (fun b hb ↦ by simp [hb]) ∘ spaTilt p hplus) = _root_.id :=
  ⟨isHomeomorph_spaTilt_of_charP _, spaTilt_eq_id_of_charP _⟩

end CharacteristicP

section ZeroRing

variable {B : Type*} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
  [IsTateRing B] [CompleteSpace B] [T2Space B] [IsUniform B] [Subsingleton B]
  [Fact (IsTopologicallyNilpotent (p : B))] [IsTateRing (uniformTilt p B)]

/-- On the zero ring (where `CharP B p` fails for prime `p`), both `Spa(B, B⁺)` and its tilted
target are empty and `Pair.spaTilt` is bijective. -/
example (P : Pair B) :
    IsEmpty (spa P.plus) ∧ IsEmpty (spa (P.tilt (p := p)).plus) ∧
      Function.Bijective (P.spaTilt p) := by
  have h₁ : IsEmpty (spa P.plus) := by
    rw [Set.isEmpty_coe_sort, spa_eq_empty_iff_subsingleton _ P.isRingOfIntegralElements]
    infer_instance
  have h₂ : IsEmpty (spa (P.tilt (p := p)).plus) := by
    rw [Set.isEmpty_coe_sort,
      spa_eq_empty_iff_subsingleton _ (P.tilt (p := p)).isRingOfIntegralElements]
    infer_instance
  exact ⟨h₁, h₂, ⟨fun x ↦ isEmptyElim x, fun y ↦ isEmptyElim y⟩⟩

end ZeroRing

/-! ### 5. Non-example: `spaTilt` does not come from a morphism of Huber pairs -/

/-- No ring homomorphism exists from `ℂ_p♭` (characteristic `p`) to `ℂ_p` (characteristic `0`). -/
theorem isEmpty_ringHom_uniformTilt_padicComplex :
    IsEmpty (uniformTilt p ℂ_[p] →+* ℂ_[p]) := by
  refine ⟨fun φ ↦ ?_⟩
  have hp0 : (p : uniformTilt p ℂ_[p]) = 0 := CharP.cast_eq_zero _ p
  have hφ : φ (p : uniformTilt p ℂ_[p]) = (p : ℂ_[p]) := map_natCast φ p
  rw [hp0, map_zero] at hφ
  exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero hφ.symm

/-- Consequently there is no morphism of Huber pairs `(ℂ_p♭, ℂ_p♭°) → (ℂ_p, ℂ_p°)`: the continuous
tilting map `Pair.spaTilt : Spa(ℂ_p, ℂ_p°) → Spa(ℂ_p♭, ℂ_p♭°)` cannot arise as `Pair.Hom.spaComap`
of any Huber-pair morphism. -/
theorem isEmpty_pairHom_tilt_padicComplex :
    IsEmpty (Pair.Hom ((Pair.powerBounded ℂ_[p]).tilt (p := p)) (Pair.powerBounded ℂ_[p])) :=
  ⟨fun φ ↦ (isEmpty_ringHom_uniformTilt_padicComplex p).false φ.toRingHom⟩

end TauCeti.Examples.PerfectoidSpaceTiltSpa

end
