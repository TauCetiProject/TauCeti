/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.ChainComplex
public import TauCeti.Geometry.Manifold.Morse.Boundary.Diffeomorph
public import TauCeti.Geometry.Manifold.Morse.Boundary.IndexOne
public import TauCeti.Geometry.Manifold.Morse.Boundary.SignedChainComplex
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Projectivization
public import TauCeti.Geometry.Manifold.Projectivization.Signs
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# The Morse complex of the real projective plane

On the real projective plane `ℝℙ² = ℙ ℝ (Fin 3 → ℝ)`, the moment function
`[v] ↦ (∑ i, w i * v i ^ 2) / ∑ i, v i ^ 2` with three distinct weights `w` is a Morse function
(`TauCeti.isMorse_projectiveMomentFunction`) with one critical point of each index `0`, `1` and
`2` (`TauCeti.criticalCount_projectiveMomentFunction_real`): a minimum, a saddle and a maximum.
This file computes the trajectories between them, the mod-two Morse complex and the integral Morse
boundary, for pseudo-gradients `X` adapted to this function.

* `X` is Morse–Smale, whatever its choice. The saddle is the only critical point whose index is
  neither `0` nor `2`, so `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.of_subsingleton` applies.
* There are exactly two trajectories from the maximum to the saddle and exactly two from the
  saddle to the minimum. The stable manifold of the saddle is a line, whose two halves both come
  from the only critical point of index `2`; its unstable manifold is a line, whose two halves both
  go to the only critical point of index `0`.
* So the mod-two Morse boundary vanishes, and the mod-two Morse complex is `𝔽₂ → 𝔽₂ → 𝔽₂` with
  zero differentials. Its homology is `𝔽₂` in degrees `0`, `1` and `2` and zero above, the
  mod-two homology of `ℝℙ²`.

Over `ℤ` the same two pairs of trajectories give the differentials `±2` from the maximum to the
saddle and `0` from the saddle to the minimum, recovering `H₁(ℝℙ²; ℤ) = ℤ/2`: the two trajectories
into the saddle carry the same sign and the two out of it opposite signs. Those signs come from
orientations of the unstable manifolds, which the mod-two complex does not see.

* The differential `d₁` from the saddle to the minimum vanishes, for every adapted pseudo-gradient
  and every choice of orientations
  (`signedMorseBoundary_single_eq_zero_projectiveMomentFunction_real`), since the minimum is the
  only critical point of index `0`.
* The differential `d₂` from the maximum to the saddle is `±2` for every adapted pseudo-gradient
  commuting with the sign changes of the homogeneous coordinates, such as the one of
  `TauCeti.exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul`, and every choice
  of orientations (`signedMorseBoundary_single_eq_two_or_eq_neg_two_projectiveMomentFunction_real`).
  Let `[e_a]` be the maximum and `[e_b]` the saddle. The reflection `σ` negating the `b`-th
  homogeneous coordinate fixes both and exchanges the two trajectories between them: its fixed
  points other than `[e_b]` form the line `v b = 0`, invariant under the flow, so no trajectory
  into `[e_b]` meets them. In the affine charts, `σ` acts on the tangent space at the saddle by `-1`
  and at the maximum by a reflection, so it reverses the orientations of both unstable manifolds,
  and by `TauCeti.IsAdaptedPseudoGradient.trajectorySign_apply_eq_mul_mul_trajectorySign` the two
  trajectories have the same sign.

So a multiple `n` of the saddle is a boundary exactly when `n` is even
(`single_mem_range_signedMorseBoundary_iff_even_projectiveMomentFunction_real`): this is the
computation `H₁(ℝℙ²; ℤ) = ℤ/2` on the level of the integral Morse boundary.

Since the minimum is unique and `ℝℙ²` has dimension two, the integral Morse boundary squares to
zero (`signedMorseBoundary_comp_signedMorseBoundary_projectiveMomentFunction_real`), so the
integral Morse chain complex `TauCeti.IsAdaptedPseudoGradient.signedMorseComplex` is defined, and
its homology is that of `ℝℙ²`:

* `H₀ = R` with coefficients in any ring `R`, for every adapted pseudo-gradient;
* `H₁ = ℤ/2` and `H₂ = 0` over `ℤ`, for the adapted pseudo-gradients commuting with the sign
  changes of the homogeneous coordinates: the differential `d₂`, which sends the maximum to `±2`
  times the saddle, is injective and its image consists of the chains with even coefficient at the
  saddle (`injective_signedMorseBoundaryAt_one_projectiveMomentFunction_real`,
  `mem_range_signedMorseBoundaryAt_one_iff_projectiveMomentFunction_real`). Modulo two all three
  homology groups are instead `ZMod 2`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isMorseSmale_projectiveMomentFunction_real`: every pseudo-gradient adapted to the moment
  function on `ℝℙ²` is Morse–Smale.
* `ncard_morseTrajectorySlice_projectiveMomentFunction_real`: between critical points whose indices
  differ by one there are exactly two trajectories.
* `IsMorseSmale.morseBoundary_projectiveMomentFunction_real`: the mod-two Morse boundary is zero.
* `IsMorseSmale.finrank_homology_morseComplex_projectiveMomentFunction_real`: the mod-two Morse
  homology has dimension `1` in degrees `0`, `1` and `2` and dimension `0` above.
* `signedMorseBoundary_single_eq_zero_projectiveMomentFunction_real`: the integral Morse boundary
  of the saddle is zero.
* `signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real`,
  `signedMorseBoundary_single_eq_two_or_eq_neg_two_projectiveMomentFunction_real`: for a
  pseudo-gradient commuting with the sign changes, the integral Morse boundary of the maximum is
  `±2` times the saddle.
* `single_mem_range_signedMorseBoundary_iff_even_projectiveMomentFunction_real`: a multiple `n` of
  the saddle is an integral Morse boundary exactly when `n` is even.
* `exists_isAdaptedPseudoGradient_signedMorseBoundary_single_projectiveMomentFunction_real`: some
  adapted pseudo-gradient has `d₂ = ±2` for all orientations.
* `signedMorseBoundary_comp_signedMorseBoundary_projectiveMomentFunction_real`: the integral Morse
  boundary squares to zero.
* `nonempty_linearEquiv_homology_zero_signedMorseComplex_projectiveMomentFunction_real`,
  `nonempty_linearEquiv_homology_one_signedMorseComplex_projectiveMomentFunction_real`,
  `isZero_homology_two_signedMorseComplex_projectiveMomentFunction_real`: the integral Morse
  homology in degree `0` is `R` over any ring; over `ℤ`, for pseudo-gradients commuting with the
  sign changes, it is `ℤ/2` in degree `1` and `0` in degree `2`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex, and its computation for the real projective plane).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2 (the Morse complex of `ℝℙ²`).
-/

public section

open Function Module
open scoped ContDiff LinearAlgebra.Projectivization Manifold

namespace TauCeti

variable {w : Fin 3 → ℝ}

namespace IsAdaptedPseudoGradient

variable {X : (x : ℙ ℝ (Fin 3 → ℝ)) → TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x}

/-- **The moment function on `ℝℙ²` is Morse–Smale for every pseudo-gradient.** For distinct
weights, every pseudo-gradient adapted to the moment function on the real projective plane
satisfies the Morse–Smale condition: its saddle is its only critical point of index neither `0`
nor `2`. -/
theorem isMorseSmale_projectiveMomentFunction_real (hw : Injective w)
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X) : hX.IsMorseSmale := by
  refine IsMorseSmale.of_subsingleton (isMorse_projectiveMomentFunction hw)
    ((subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 1).anti ?_)
  rintro x ⟨hx, hx0, hx2⟩
  have hle : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) x ≤ 2 :=
    manifoldMorseIndex_le_finrank.trans_eq (Module.finrank_fin_fun ℝ)
  rw [Module.finrank_fin_fun] at hx2
  exact ⟨hx, by omega⟩

/-- **Two trajectories between consecutive indices on `ℝℙ²`.** For distinct weights and every
pseudo-gradient adapted to the moment function on the real projective plane, there are exactly two
trajectories from a critical point `p` to a critical point `q` of index one less: from the maximum
to the saddle, and from the saddle to the minimum. -/
theorem ncard_morseTrajectorySlice_projectiveMomentFunction_real (hw : Injective w)
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X) {p q : ℙ ℝ (Fin 3 → ℝ)}
    (hp : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) (projectiveMomentFunction ℝ w) p = 0)
    (hq : mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ) (projectiveMomentFunction ℝ w) q = 0)
    (hpq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p =
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q + 1) :
    (hX.morseTrajectorySlice p q).ncard = 2 := by
  have h := hX.isMorseSmale_projectiveMomentFunction_real hw
  have hf := isMorse_projectiveMomentFunction (𝕜 := ℝ) hw
  have hsub := subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw
  have hle : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p ≤ 2 :=
    manifoldMorseIndex_le_finrank.trans_eq (Module.finrank_fin_fun ℝ)
  -- Either `p` is the maximum and `q` the saddle, or `q` is the minimum and `p` the saddle.
  obtain hp2 | hq0 : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2 ∨
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 0 := by omega
  · refine h.ncard_morseTrajectorySlice_eq_two_of_unique_index_finrank hf hq
      (by rw [Module.finrank_fin_fun]; omega) fun y hy hy2 ↦ hsub 2 ⟨hy, ?_⟩ ⟨hp, hp2⟩
    rwa [Module.finrank_fin_fun] at hy2
  · exact h.ncard_morseTrajectorySlice_eq_two_of_unique_index_zero hf hp (by omega)
      fun y hy hy0 ↦ hsub 0 ⟨hy, hy0⟩ ⟨hq, hq0⟩

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X} (h : hX.IsMorseSmale)
  (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))

/-- **The mod-two Morse boundary of `ℝℙ²` is zero.** For every pseudo-gradient adapted to the
moment function on the real projective plane, the mod-two Morse complex is the free
`ZMod 2`-module on the minimum, the saddle and the maximum, with zero differential. -/
@[simp]
theorem morseBoundary_projectiveMomentFunction_real : h.morseBoundary hf = 0 := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  exact h.morseBoundary_eq_zero_of_finrank_eq_two hf (Module.finrank_fin_fun ℝ)
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 2)
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0)

/-- **The mod-two Morse homology of `ℝℙ²`.** For distinct weights, so that the moment function on
the real projective plane is Morse, and every pseudo-gradient adapted to it, the mod-two Morse
homology has dimension `1` in degrees `0`, `1` and `2`, and dimension `0` in higher degrees. -/
theorem finrank_homology_morseComplex_projectiveMomentFunction_real (n : ℕ) :
    finrank (ZMod 2) ((h.morseComplex hf).homology n) = if n ≤ 2 then 1 else 0 := by
  rw [h.finrank_homology_morseComplex_of_morseBoundary_eq_zero hf
      (h.morseBoundary_projectiveMomentFunction_real hf),
    criticalCount_projectiveMomentFunction_real (isMorse_projectiveMomentFunction_iff.1 hf)]
  split_ifs <;> simp

end IsMorseSmale

/-- **The integral Morse boundary of the saddle of `ℝℙ²` is zero.** For every pseudo-gradient
adapted to the moment function on the real projective plane and every choice of orientations of
the unstable manifolds, the two trajectories from the saddle to the minimum carry opposite signs,
so the Morse boundary of the saddle vanishes, with coefficients in any ring. -/
theorem signedMorseBoundary_single_eq_zero_projectiveMomentFunction_real
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X)
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)) {R : Type*} [Ring R]
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hp : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 1) (a : R) :
    hX.signedMorseBoundary 𝔬 hf R (Finsupp.single p a) = 0 :=
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  IsMorseSmale.signedMorseBoundary_single_eq_zero_of_unique_index_zero
    (hX.isMorseSmale_projectiveMomentFunction_real hw) hf 𝔬 hp
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0) a

/-- **`∂² = 0` on `ℝℙ²`.** For every pseudo-gradient adapted to the moment function on the real
projective plane and every choice of orientations of the unstable manifolds, the integral Morse
boundary squares to zero, with coefficients in any ring. So the integral Morse chain complex
`TauCeti.IsAdaptedPseudoGradient.signedMorseComplex` of `ℝℙ²` is defined. -/
theorem signedMorseBoundary_comp_signedMorseBoundary_projectiveMomentFunction_real
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X)
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X) (R : Type*) [Ring R] :
    hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0 :=
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  IsMorseSmale.signedMorseBoundary_comp_signedMorseBoundary_eq_zero_of_finrank_le_two
    (hX.isMorseSmale_projectiveMomentFunction_real hw) (Module.finrank_fin_fun ℝ).le
    (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0)

/-- For distinct weights, the moment function on `ℝℙ²` has exactly one critical point of each index
`k ≤ 2`. -/
private theorem exists_forall_eq_projectiveMomentFunction_real (hw : Injective w) {k : ℕ}
    (hk : k ≤ 2) :
    ∃ p : {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
        manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = k}, ∀ q, q = p :=
  Nat.card_eq_one_iff_exists.1 <| by
    rw [natCard_criticalPoints_manifoldMorseIndex_eq_toNat_criticalCount,
      criticalCount_projectiveMomentFunction_real hw, ite_eq_left_iff.2 fun h ↦ absurd hk h,
      ENat.toNat_one]

/-- A chain supported on critical points of index `k`, when `p` is the only one, is a multiple of
`p`. -/
private theorem eq_single_of_forall_eq_projectiveMomentFunction_real {k : ℕ}
    {p : {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = k}}
    (hp : ∀ q, q = p) {R : Type*} [Zero R]
    (c : {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = k} →₀ R) :
    c = Finsupp.single p (c p) :=
  letI : Unique _ := ⟨⟨p⟩, hp⟩
  Finsupp.unique_single c

/-- **`H₀(ℝℙ²) = R`.** For every pseudo-gradient adapted to the moment function on the real
projective plane and every choice of orientations, the integral Morse homology in degree `0`, with
coefficients in any ring `R`, is `R`, since the minimum is the only critical point of index `0`. -/
theorem nonempty_linearEquiv_homology_zero_signedMorseComplex_projectiveMomentFunction_real
    (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X)
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X) {R : Type*} [Ring R]
    (hsq : hX.signedMorseBoundary 𝔬 hf R ∘ₗ hX.signedMorseBoundary 𝔬 hf R = 0) :
    Nonempty ((hX.signedMorseComplex 𝔬 hf R hsq).homology 0 ≃ₗ[R] R) := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  obtain ⟨p, hp⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 0) (by norm_num)
  exact nonempty_linearEquiv_homology_zero_signedMorseComplex hsq
    (IsMorseSmale.signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero hf
      (hX.isMorseSmale_projectiveMomentFunction_real hw)
      (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0)) p hp

/-! ### The integral boundary of the maximum -/

section Maximum

variable {X : (x : ℙ ℝ (Fin 3 → ℝ)) → TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x}
  (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X)
  (hXε : ∀ (ε : Fin 3 → ℤˣ) x,
    mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (ε • ·) x (X x) = X (ε • x))

/-- The reflection negating the `b`-th homogeneous coordinate, as a diffeomorphism of `ℝℙ²`. -/
private noncomputable abbrev reflection (b : Fin 3) :
    ℙ ℝ (Fin 3 → ℝ) ≃ₘ^∞⟮𝓘(ℝ, Fin 2 → ℝ), 𝓘(ℝ, Fin 2 → ℝ)⟯ ℙ ℝ (Fin 3 → ℝ) :=
  Diffeomorph.constSmul 𝓘(ℝ, Fin 2 → ℝ) ∞ (Pi.mulSingle b (-1) : Fin 3 → ℤˣ)

private theorem comp_reflection (b : Fin 3) :
    projectiveMomentFunction ℝ w ∘ reflection b = projectiveMomentFunction ℝ w :=
  funext fun x ↦ by
    rw [Function.comp_apply, Diffeomorph.constSmul_apply, projectiveMomentFunction_smul]

include hXε in
private theorem mfderiv_reflection (b : Fin 3) (y : ℙ ℝ (Fin 3 → ℝ)) :
    mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (reflection b) y (X y) = X (reflection b y) := by
  rw [Diffeomorph.coe_constSmul]
  exact hXε _ y

include hXε in
/-- **The reflection moves every point of a trajectory into a coordinate point.** On a trajectory
of `X` from another point to the coordinate point `[e_b]`, the reflection negating the `b`-th
coordinate fixes no point: its fixed points other than `[e_b]` lie on the line `v b = 0`, which is
invariant under the flow and closed, so a trajectory through one of them cannot tend to `[e_b]`. -/
private theorem reflection_ne_of_mem_morseTrajectorySlice {p : ℙ ℝ (Fin 3 → ℝ)} {b : Fin 3}
    (hpb : p ≠ Projectivization.mk ℝ (Pi.single b 1 : Fin 3 → ℝ) (by simp)) {y : ℙ ℝ (Fin 3 → ℝ)}
    (hy : y ∈ hX.morseTrajectorySlice p
      (Projectivization.mk ℝ (Pi.single b 1 : Fin 3 → ℝ) (by simp))) :
    reflection b y ≠ y := by
  intro hfix
  obtain ⟨-, hys, hyv⟩ := hX.mem_morseTrajectorySlice.1 hy
  have hlt := hX.value_lt_of_mem_morseTrajectorySlice hpb hy
  have hq0 := mem_criticalPoints_iff_mfderiv_eq_zero.1
    (mk_single_mem_criticalPoints_projectiveMomentFunction (𝕜 := ℝ) w b)
  -- The flow commutes with the reflection, so it carries `y` through fixed points of it, none of
  -- which is the rest point `[e_b]`, below the level of `y`.
  have hout (t : ℝ) : hX.flow t y ∈ (Projectivization.affineOpen b)ᶜ := fun hmem ↦ by
    have hσt : reflection b (hX.flow t y) = hX.flow t y := by
      rw [← flow_apply_diffeomorph hX hX (mfderiv_reflection hXε b), hfix]
    rw [Diffeomorph.constSmul_apply] at hσt
    have hq := eq_mk_single_of_mulSingle_neg_one_smul_eq hσt hmem
    have hyq : y = Projectivization.mk ℝ (Pi.single b 1 : Fin 3 → ℝ) (by simp) := by
      rw [← hX.flow_apply_of_mfderiv_eq_zero hq0 (-t), ← hq, ← Flow.map_add, neg_add_cancel,
        Flow.map_zero_apply]
    rw [hyq] at hyv
    linarith
  -- So the limit `[e_b]` of the flow lies in the closed complement of the affine open at `b`.
  exact (Projectivization.isOpen_affineOpen b).isClosed_compl.mem_of_tendsto
    (Flow.mem_stableSet.1 hys) (Filter.Eventually.of_forall hout) (by simp)

/-- In the affine chart at `a`, the reflection negating another coordinate `b` changes the sign of
exactly one affine coordinate, so as a linear map of `ℝ²` it has negative determinant. -/
private theorem det_chartSigns_mulSingle_neg_one_neg {a b : Fin 3} (hab : a ≠ b) :
    LinearMap.det (DistribMulAction.toLinearEquiv ℝ (Fin 2 → ℝ)
      (chartSigns (Pi.mulSingle b (-1) : Fin 3 → ℤˣ) a) : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) < 0 := by
  set c := chartSigns (Pi.mulSingle b (-1) : Fin 3 → ℤˣ) a
  -- The change of signs is diagonal, with exactly one entry `-1` since `a ≠ b`.
  have hS : LinearMap.toMatrix' (DistribMulAction.toLinearEquiv ℝ (Fin 2 → ℝ) c :
      (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) = Matrix.diagonal fun j ↦ ((c j : ℤ) : ℝ) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [LinearMap.toMatrix'_apply, Units.smul_def]
    · simp [LinearMap.toMatrix'_apply, hij]
  rw [← LinearMap.det_toMatrix', hS, Matrix.det_diagonal]
  have := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (prod_chartSigns_mulSingle_neg_one_of_ne hab)
  push_cast at this
  rw [this]
  norm_num

include hX in
/-- At the maximum `[e_a]`, the reflection negating another coordinate `b` acts on the unstable
frame of the orientation data by a linear map reversing their orientation: its derivative is
conjugate to the change of signs of the affine coordinates at `a`, which has a single sign `-1`. -/
private theorem exists_mfderiv_reflection_unstableFrame_of_eq_two
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hp : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2) {a b : Fin 3}
    (ha : Projectivization.mk ℝ (Pi.single a 1 : Fin 3 → ℝ) (by simp) = p) (hab : a ≠ b) :
    ∃ L : ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart p).weight i < 0} → ℝ),
      (∀ v, mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (reflection b) p
          (hX.unstableFrame (𝔬.chart p) p v) = hX.unstableFrame (𝔬.chart p) p (L v)) ∧
        Orientation.map _ L (𝔬.orientation p) =
          Units.map (Int.castRingHom ℝ).toMonoidHom (-1) • 𝔬.orientation p := by
  set ε : Fin 3 → ℤˣ := Pi.mulSingle b (-1)
  -- At `p` the unstable frame is an isomorphism `F` onto the tangent space, since `ind p = 2`.
  have hmem : (p : ℙ ℝ (Fin 3 → ℝ)) ∈ hX.flow.unstableSet p :=
    (hX.mem_unstableSet_inter_stableSet_self
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property)).1
  have hinj := hX.injective_unstableFrame_of_mem (𝔬.coord_mfderiv_chart p) hf hmem
  have hdim : finrank ℝ ({i // (𝔬.chart p).weight i < 0} → ℝ) =
      finrank ℝ (TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (p : ℙ ℝ (Fin 3 → ℝ))) := by
    rw [(𝔬.chart p).finrank_negativeWeight_fun, hp]
    exact (finrank_fin_fun ℝ).symm
  set F := LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) p).toLinearMap
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩
  -- The derivative `A` of the affine chart at `a` is an isomorphism, and it turns the derivative
  -- of the reflection at `p` into the change of signs `S` of the affine coordinates.
  have hpa : (p : ℙ ℝ (Fin 3 → ℝ)) ∈ Projectivization.affineOpen a := by
    rw [← ha]
    simp
  obtain ⟨A, hA⟩ := isInvertible_mfderiv_chart
    (Projectivization.affineOpenPartialHomeomorph_mem_maximalAtlas (𝕜' := ℝ) a)
    (y := (p : ℙ ℝ (Fin 3 → ℝ))) (by simpa using hpa)
  set S := DistribMulAction.toLinearEquiv ℝ (Fin 2 → ℝ) (chartSigns ε a)
  set G : ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) := F.trans A.toLinearEquiv
  refine ⟨G.trans (S.trans G.symm), fun v ↦ A.injective ?_, ?_⟩
  · have hfix : ε • (p : ℙ ℝ (Fin 3 → ℝ)) = p := by
      rw [← ha, signs_smul_mk_single]
    have h := mvfderiv_affineChart_mfderiv_signs_smul ε a hpa (F v)
    rw [hfix, ← Projectivization.coe_affineOpenPartialHomeomorph] at h
    have hAz (z : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (p : ℙ ℝ (Fin 3 → ℝ))) :
        A z = mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ)
          (Projectivization.affineOpenPartialHomeomorph (K := ℝ) a) (p : ℙ ℝ (Fin 3 → ℝ)) z :=
      DFunLike.congr_fun hA z
    rw [Diffeomorph.coe_constSmul]
    -- `mvfderiv` is `mfderiv` with values read in the model space, and `G v = A (F v)`.
    have hGv : mvfderiv 𝓘(ℝ, Fin 2 → ℝ) (Projectivization.affineOpenPartialHomeomorph (K := ℝ) a)
        (p : ℙ ℝ (Fin 3 → ℝ)) (F v) = G v := (hAz (F v)).symm
    refine (hAz _).trans (h.trans ?_)
    rw [hGv]
    -- The right side is `A (F (G⁻¹ (S (G v)))) = G (G⁻¹ (S (G v)))`, and `S` changes the signs.
    exact (G.apply_symm_apply (S (G v))).symm
  · rw [Orientation.intCast_units_smul_eq_ite, ite_eq_right (by decide),
      Orientation.map_eq_neg_iff_det_neg _ _
        (by rw [Fintype.card_fin, (𝔬.chart p).finrank_negativeWeight_fun])]
    -- The map is the conjugate of `S` by `G`, by unfolding the compositions.
    have hconj : ((G.trans (S.trans G.symm) :
          ({i // (𝔬.chart p).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart p).weight i < 0} → ℝ)) :
          ({i // (𝔬.chart p).weight i < 0} → ℝ) →ₗ[ℝ] ({i // (𝔬.chart p).weight i < 0} → ℝ)) =
        (G.symm : (Fin 2 → ℝ) →ₗ[ℝ] _) ∘ₗ (S : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) ∘ₗ
          (G.symm.symm : _ →ₗ[ℝ] Fin 2 → ℝ) := rfl
    rw [hconj, LinearMap.det_conj]
    exact det_chartSigns_mulSingle_neg_one_neg hab

include hX in
/-- At the saddle `[e_b]`, the reflection negating the coordinate `b` acts on the tangent space by
`-1`, hence on the one-dimensional unstable frame by `-1`, reversing the orientation. -/
private theorem exists_mfderiv_reflection_unstableFrame_of_eq_one
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1) {b : Fin 3}
    (hb : Projectivization.mk ℝ (Pi.single b 1 : Fin 3 → ℝ) (by simp) = q) :
    ∃ L : ({i // (𝔬.chart q).weight i < 0} → ℝ) ≃ₗ[ℝ] ({i // (𝔬.chart q).weight i < 0} → ℝ),
      (∀ v, mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (reflection b) q
          (hX.unstableFrame (𝔬.chart q) q v) = hX.unstableFrame (𝔬.chart q) q (L v)) ∧
        Orientation.map _ L (𝔬.orientation q) =
          Units.map (Int.castRingHom ℝ).toMonoidHom (-1) • 𝔬.orientation q := by
  have hd (u : TangentSpace 𝓘(ℝ, Fin 2 → ℝ) (q : ℙ ℝ (Fin 3 → ℝ))) :
      mfderiv 𝓘(ℝ, Fin 2 → ℝ) 𝓘(ℝ, Fin 2 → ℝ) (reflection b) q u = -u := by
    revert u
    rw [← hb, Diffeomorph.coe_constSmul]
    exact mfderiv_mulSingle_neg_one_smul_mk_single b
  refine ⟨LinearEquiv.neg ℝ, fun v ↦ by rw [hd, LinearEquiv.neg_apply, map_neg], ?_⟩
  have hdim : Module.finrank ℝ ({i // (𝔬.chart q).weight i < 0} → ℝ) = 1 := by
    rw [(𝔬.chart q).finrank_negativeWeight_fun, hq]
  rw [Orientation.intCast_units_smul_eq_ite, ite_eq_right (by decide),
    Orientation.map_eq_neg_iff_det_neg _ _ (by rw [Fintype.card_fin, hdim, hq])]
  have hneg : ((LinearEquiv.neg ℝ : ({i // (𝔬.chart q).weight i < 0} → ℝ) ≃ₗ[ℝ] _) :
      ({i // (𝔬.chart q).weight i < 0} → ℝ) →ₗ[ℝ] _) = (-1 : ℝ) • LinearMap.id := by
    ext
    simp
  rw [hneg, LinearMap.det_smul, LinearMap.det_id, hdim]
  norm_num

include hX hXε in
/-- **The integral boundary coefficient of the maximum of `ℝℙ²` at the saddle is `±2`.** For an
adapted pseudo-gradient of the moment function on the real projective plane which commutes with
the sign changes of the homogeneous coordinates, and for every choice of orientations of the
unstable manifolds, the two trajectories from the maximum `p` to the saddle `q` carry the same
sign, so the coefficient of `q` in the integral Morse boundary of `p` is `2` or `-2`. -/
theorem signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {p q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hp : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2)
    (hq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1) :
    hX.signedMorseBoundaryCoeff 𝔬 p q = 2 ∨ hX.signedMorseBoundaryCoeff 𝔬 p q = -2 := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  have hpq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p =
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q + 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a, Projectivization.mk ℝ (Pi.single a 1 : Fin 3 → ℝ) (by simp) = p := by
    simpa [criticalPoints_projectiveMomentFunction hw] using p.property
  obtain ⟨b, hb⟩ : ∃ b, Projectivization.mk ℝ (Pi.single b 1 : Fin 3 → ℝ) (by simp) = q := by
    simpa [criticalPoints_projectiveMomentFunction hw] using q.property
  have hpb : (p : ℙ ℝ (Fin 3 → ℝ)) ≠ q := fun h ↦ by
    rw [Subtype.ext h] at hp
    omega
  have hab : a ≠ b := by
    rintro rfl
    exact hpb (ha.symm.trans hb)
  -- The reflection negating the coordinate of the saddle fixes both critical points and preserves
  -- the signs of the trajectories between them.
  have hσp : reflection b p = p := by
    rw [← ha, Diffeomorph.constSmul_apply, signs_smul_mk_single]
  have hσq : reflection b q = q := by
    rw [← hb, Diffeomorph.constSmul_apply, signs_smul_mk_single]
  obtain ⟨Lp, hLp, hup⟩ := exists_mfderiv_reflection_unstableFrame_of_eq_two hX hf 𝔬 hp ha hab
  obtain ⟨Lq, hLq, huq⟩ := exists_mfderiv_reflection_unstableFrame_of_eq_one hX 𝔬 hq hb
  have hsign {y : ℙ ℝ (Fin 3 → ℝ)} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
      hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq
          (reflection b y) =
        hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq y := by
    rw [trajectorySign_apply_eq_mul_mul_trajectorySign hX hf (reflection b) (comp_reflection b)
      (mfderiv_reflection hXε b) 𝔬 hσp hσq Lp Lq hLp hLq hup huq hpq hy]
    simp
  -- There are two trajectories, exchanged by the reflection.
  have hcard := hX.ncard_morseTrajectorySlice_projectiveMomentFunction_real hw
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.property)
    (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property) hpq
  obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := hX.morseTrajectorySlice p q) (by omega)
  have hσy : reflection b y ∈ hX.morseTrajectorySlice p q := by
    rw [← hσp, ← hσq, ← image_morseTrajectorySlice_diffeomorph (comp_reflection b) hX hX
      (mfderiv_reflection hXε b)]
    exact Set.mem_image_of_mem _ hy
  have hne : y ≠ reflection b y := fun h ↦ reflection_ne_of_mem_morseTrajectorySlice hX hXε
    (hb ▸ hpb) (hb ▸ hy) h.symm
  have hslice : hX.morseTrajectorySlice p q = {y, reflection b y} :=
    (Set.eq_of_subset_of_ncard_le (Set.pair_subset hy hσy) (by rw [hcard, Set.ncard_pair hne])
      (Set.finite_of_ncard_ne_zero (by omega))).symm
  have hmem := hX.mem_morseTrajectorySlice.1 hy
  rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def, hslice,
    finsum_mem_pair hne, hsign ⟨hmem.1, hmem.2.1⟩]
  rcases trajectorySign_eq_one_or_eq_neg_one (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q)
    (hX.isMorseSmale_projectiveMomentFunction_real hw) hf ⟨hmem.1, hmem.2.1⟩ with h | h <;>
    rw [h] <;> norm_num

include hX hXε in
/-- **The differential `d₂ = ±2` of `ℝℙ²`.** For an adapted pseudo-gradient of the moment function
on the real projective plane which commutes with the sign changes of the homogeneous coordinates,
and for every choice of orientations of the unstable manifolds, the integral Morse boundary of the
maximum `p` is twice the saddle `q`, up to sign. -/
theorem signedMorseBoundary_single_eq_two_or_eq_neg_two_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {p q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hp : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2)
    (hq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1) :
    hX.signedMorseBoundary 𝔬 hf ℤ (Finsupp.single p 1) = Finsupp.single q 2 ∨
      hX.signedMorseBoundary 𝔬 hf ℤ (Finsupp.single p 1) = Finsupp.single q (-2) := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  -- The saddle is the only critical point of index one, so the boundary of `p` lives on it.
  have hoff (r : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)) (hr : r ≠ q) :
      hX.signedMorseBoundaryCoeff 𝔬 p r = 0 := by
    refine signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one fun h ↦ hr (Subtype.ext ?_)
    exact subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 1
      ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 r.property, by omega⟩
      ⟨mem_criticalPoints_iff_mfderiv_eq_zero.1 q.property, hq⟩
  rcases signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε hf 𝔬
    hp hq with h | h
  · refine Or.inl (Finsupp.ext fun r ↦ ?_)
    rcases eq_or_ne r q with rfl | hr
    · simp [h]
    · simp [hoff r hr, hr.symm]
  · refine Or.inr (Finsupp.ext fun r ↦ ?_)
    rcases eq_or_ne r q with rfl | hr
    · simp [h]
    · simp [hoff r hr, hr.symm]

include hX hXε in
/-- **The boundaries on the saddle of `ℝℙ²`.** For an adapted pseudo-gradient of the moment function
on the real projective plane which commutes with the sign changes of the homogeneous coordinates,
and for every choice of orientations, the multiple `n • q` of the saddle `q` is the integral Morse
boundary of a chain exactly when `n` is even. The chains of index one are the multiples of `q`, and
they are cycles (`signedMorseBoundary_single_eq_zero_projectiveMomentFunction_real`), so modulo
boundaries they form `ℤ / 2`, the first homology of `ℝℙ²`. -/
theorem single_mem_range_signedMorseBoundary_iff_even_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    {q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)}
    (hq : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1) (n : ℤ) :
    Finsupp.single q n ∈ LinearMap.range (hX.signedMorseBoundary 𝔬 hf ℤ) ↔ Even n := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  constructor
  · -- Every boundary coefficient at the saddle is `0` or `±2`.
    rintro ⟨c, hc⟩
    have hn := congrArg (· q) hc
    simp only [signedMorseBoundary_apply, Finsupp.single_eq_same] at hn
    rw [← hn, Finsupp.sum]
    refine Finset.even_sum _ fun r _ ↦ Even.mul_left ?_ _
    by_cases hr : manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) r = 2
    · rcases signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε hf
        𝔬 hr hq with h | h <;> simp [h]
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega)]
      exact Even.zero
  · -- The maximum has boundary `±2 q`.
    rintro ⟨k, rfl⟩
    have h2 := criticalCount_projectiveMomentFunction_real hw 2
    rw [criticalCount_def, ite_eq_left (by norm_num)] at h2
    obtain ⟨p, hp, hp2⟩ := Set.nonempty_of_encard_ne_zero (by rw [h2]; norm_num)
    rcases signedMorseBoundary_single_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε hf
      𝔬 (p := ⟨p, hp⟩) hp2 hq with h | h
    · refine ⟨Finsupp.single ⟨p, hp⟩ k, ?_⟩
      rw [← mul_one k, ← smul_eq_mul, ← Finsupp.smul_single, map_smul, h, Finsupp.smul_single]
      congr 1
      ring
    · refine ⟨Finsupp.single ⟨p, hp⟩ (-k), ?_⟩
      rw [← mul_one (-k), ← smul_eq_mul, ← Finsupp.smul_single, map_smul, h, Finsupp.smul_single]
      congr 1
      ring

/-- **An adapted pseudo-gradient of `ℝℙ²` with `d₂ = ±2`.** For distinct weights, the moment
function on the real projective plane has an adapted pseudo-gradient for which, whatever the
orientations of the unstable manifolds, the integral Morse boundary of the maximum is twice the
saddle, up to sign. -/
theorem exists_isAdaptedPseudoGradient_signedMorseBoundary_single_projectiveMomentFunction_real
    (hw : Injective w) :
    ∃ (X : (x : ℙ ℝ (Fin 3 → ℝ)) → TangentSpace 𝓘(ℝ, Fin 2 → ℝ) x)
      (hX : IsAdaptedPseudoGradient (projectiveMomentFunction ℝ w) X),
      ∀ (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
        {p q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w)},
        manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 2 →
        manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1 →
        hX.signedMorseBoundary 𝔬 (isMorse_projectiveMomentFunction hw) ℤ (Finsupp.single p 1) =
            Finsupp.single q 2 ∨
          hX.signedMorseBoundary 𝔬 (isMorse_projectiveMomentFunction hw) ℤ
            (Finsupp.single p 1) = Finsupp.single q (-2) := by
  obtain ⟨X, hX, hXε⟩ := exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul hw
  exact ⟨X, hX, fun 𝔬 _ _ hp hq ↦
    signedMorseBoundary_single_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε
      (isMorse_projectiveMomentFunction hw) 𝔬 hp hq⟩

/-! ### The integral Morse homology of `ℝℙ²` -/

include hX hXε in
/-- **The boundaries in degree one of `ℝℙ²`.** For an adapted pseudo-gradient of the moment
function on the real projective plane which commutes with the sign changes of the homogeneous
coordinates, and every choice of orientations, a graded chain `c` of index one is an integral
Morse boundary exactly when its coefficient at the saddle `q` is even. -/
theorem mem_range_signedMorseBoundaryAt_one_iff_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    (q : {q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1})
    (c : {q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1} →₀ ℤ) :
    c ∈ LinearMap.range (hX.signedMorseBoundaryAt 𝔬 hf ℤ 1) ↔ 2 ∣ c q := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  have hcoeff (p : {p : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) p = 1 + 1}) :=
    signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε hf 𝔬
      p.property q.property
  constructor
  · -- Every coefficient of the boundary at the saddle is `±2`.
    rintro ⟨y, rfl⟩
    rw [signedMorseBoundaryAt_apply, Finsupp.sum]
    refine Finset.dvd_sum fun p _ ↦ Dvd.dvd.mul_left ?_ _
    rcases hcoeff p with h | h <;> simp [h]
  · -- The maximum has boundary `±2 q`, and the chains of index one are the multiples of `q`.
    rintro ⟨k, hk⟩
    obtain ⟨p, -⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 2) le_rfl
    obtain ⟨q', hq'⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 1) (by norm_num)
    have hq (r) : r = q := (hq' r).trans (hq' q).symm
    rw [eq_single_of_forall_eq_projectiveMomentFunction_real hq c, hk]
    rcases hcoeff p with h | h <;>
      [refine ⟨Finsupp.single p k, ?_⟩; refine ⟨Finsupp.single p (-k), ?_⟩] <;>
    · ext r
      rw [hq r, signedMorseBoundaryAt_single_apply, h, Finsupp.single_eq_same]
      push_cast
      ring

include hX hXε in
/-- **The differential `d₂` of `ℝℙ²` is injective over `ℤ`.** For an adapted pseudo-gradient of the
moment function on the real projective plane which commutes with the sign changes of the
homogeneous coordinates, and every choice of orientations, the graded integral Morse boundary from
index two to index one, which sends the maximum to `±2` times the saddle, is injective. -/
theorem injective_signedMorseBoundaryAt_one_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X) :
    Injective (hX.signedMorseBoundaryAt 𝔬 hf ℤ 1) := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  obtain ⟨p, hp⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 2) le_rfl
  obtain ⟨q, -⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 1) (by norm_num)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc0
  have h0 := congrArg (· q) hc0
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h0
  rw [eq_single_of_forall_eq_projectiveMomentFunction_real hp c, signedMorseBoundaryAt_single_apply,
    Int.cast_id] at h0
  rw [eq_single_of_forall_eq_projectiveMomentFunction_real hp c,
    mul_eq_zero.1 h0 |>.resolve_right ?_, Finsupp.single_zero]
  rcases signedMorseBoundaryCoeff_eq_two_or_eq_neg_two_projectiveMomentFunction_real hX hXε hf 𝔬
    p.property q.property with h | h <;> simp [h]

include hX hXε in
/-- **`H₁(ℝℙ²; ℤ) = ℤ/2`.** For an adapted pseudo-gradient of the moment function on the real
projective plane which commutes with the sign changes of the homogeneous coordinates, such as the
one of `TauCeti.exists_isAdaptedPseudoGradient_projectiveMomentFunction_mfderiv_smul`, and every
choice of orientations, the integral Morse homology in degree `1` is `ℤ/2`: every chain of index
one is a cycle, and it is a boundary exactly when its coefficient at the saddle is even. -/
theorem nonempty_linearEquiv_homology_one_signedMorseComplex_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) :
    Nonempty ((hX.signedMorseComplex 𝔬 hf ℤ hsq).homology 1 ≃ₗ[ℤ] ZMod 2) := by
  have hw := isMorse_projectiveMomentFunction_iff.1 hf
  obtain ⟨q, -⟩ := exists_forall_eq_projectiveMomentFunction_real hw (k := 1) (by norm_num)
  set K := hX.signedMorseComplex 𝔬 hf ℤ hsq
  have hm : (ComplexShape.down ℕ).next 1 = 0 := ChainComplex.next_nat_succ 0
  -- Every chain of index one is a cycle, since the minimum is unique, so the homology in degree
  -- one is the quotient of the chains by the boundaries.
  have hd0 : K.d 1 0 = 0 := signedMorseComplex_d_eq_zero_of_signedMorseBoundaryAt_eq_zero hsq 0
    (IsMorseSmale.signedMorseBoundaryAt_zero_eq_zero_of_unique_index_zero hf
      (hX.isMorseSmale_projectiveMomentFunction_real hw)
      (subsingleton_setOf_manifoldMorseIndex_projectiveMomentFunction_real hw 0))
  -- The coefficient at the saddle modulo two vanishes exactly on the boundaries.
  let ψ : ({q : criticalPoints 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) //
      manifoldMorseIndex 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w) q = 1} →₀ ℤ) →ₗ[ℤ]
      ZMod 2 :=
    (Int.castAddHom (ZMod 2)).toIntLinearMap ∘ₗ Finsupp.lapply q
  have hψ_apply (c) : ψ c = (c q : ZMod 2) := by simp [ψ]
  have hψ : Surjective ψ := fun a ↦ ⟨Finsupp.single q (a.cast : ℤ), by
    rw [hψ_apply, Finsupp.single_eq_same, ZMod.intCast_zmod_cast]⟩
  have hexact : Function.Exact (hX.signedMorseBoundaryAt 𝔬 hf ℤ 1) ψ := fun c ↦ by
    rw [hψ_apply, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_ofNat,
      ← mem_range_signedMorseBoundaryAt_one_iff_projectiveMomentFunction_real hX hXε hf 𝔬 q c,
      LinearMap.mem_range, Set.mem_range]
  -- The differential of `K` into degree one is the graded integral Morse boundary, and the terms
  -- of `K` are the chain modules by definition (`signedMorseComplex_X`).
  have hd : (K.d (1 + 1) 1).hom = hX.signedMorseBoundaryAt 𝔬 hf ℤ 1 :=
    LinearMap.ext (signedMorseComplex_d_apply hsq 1)
  rw [← hd, ← ChainComplex.prev ℕ 1] at hexact
  exact ⟨((K.isoHomologyι 1 0 hm hd0) ≪≫ (K.sc 1).moduleCatOpcyclesIso).toLinearEquiv.trans
    (hexact.linearEquivOfSurjective hψ)⟩

include hX hXε in
/-- **`H₂(ℝℙ²; ℤ) = 0`.** For an adapted pseudo-gradient of the moment function on the real
projective plane which commutes with the sign changes of the homogeneous coordinates, and every
choice of orientations, the integral Morse homology in degree `2` vanishes: the differential `d₂`
sends the maximum to `±2` times the saddle, so it has no nonzero cycles. Over `ZMod 2` this
homology is instead `ZMod 2`
(`IsMorseSmale.finrank_homology_morseComplex_projectiveMomentFunction_real`). -/
theorem isZero_homology_two_signedMorseComplex_projectiveMomentFunction_real
    (hf : IsMorse 𝓘(ℝ, Fin 2 → ℝ) (projectiveMomentFunction ℝ w))
    (𝔬 : MorseOrientation (projectiveMomentFunction ℝ w) X)
    (hsq : hX.signedMorseBoundary 𝔬 hf ℤ ∘ₗ hX.signedMorseBoundary 𝔬 hf ℤ = 0) :
    CategoryTheory.Limits.IsZero ((hX.signedMorseComplex 𝔬 hf ℤ hsq).homology 2) := by
  -- The differential out of degree two is injective, so there are no nonzero cycles.
  refine (hX.signedMorseComplex 𝔬 hf ℤ hsq).isZero_homology_of_injective_d
    (ChainComplex.next_nat_succ 1) fun a b hab ↦ ?_
  exact injective_signedMorseBoundaryAt_one_projectiveMomentFunction_real hX hXε hf 𝔬 <|
    (signedMorseComplex_d_apply hsq 1 a).symm.trans (hab.trans (signedMorseComplex_d_apply hsq 1 b))

end Maximum

end IsAdaptedPseudoGradient

end TauCeti
