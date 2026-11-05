/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.Connectivity
public import TauCeti.Geometry.Manifold.RegularValue.Polynomial
public import TauCeti.LinearAlgebra.Projectivization.ZeroLocus
public import TauCeti.Topology.Algebra.Projectivization

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import TauCeti.Geometry.Manifold.Complex.ReciprocalExhaustion
import TauCeti.Geometry.Manifold.Complex.SquaredDistance
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars
import TauCeti.Geometry.Manifold.Morse.SquaredDistance
import TauCeti.Topology.Algebra.Projectivization.AffineDistance
import TauCeti.Topology.Algebra.Projectivization.ZeroLocus

/-!
# Lefschetz hyperplane theorems in homotopy and homology

Let `X ⊆ ℂℙⁿ` be a closed subset and `H = {x_i = 0}` a coordinate hyperplane, with complement the
standard affine chart `U_i = Projectivization.affineOpen i ≅ ℂⁿ`. Suppose that the affine part
`Z = affineChart i '' (X ∩ U_i) ⊆ ℂⁿ` carries a complex manifold structure of complex dimension
`d` for which the inclusion `Z → ℂⁿ` is a smooth holomorphic immersion; nothing is assumed about
`X` along the hyperplane section `X ∩ H`, where `X` may be singular.

For almost every centre `c ∈ ℂⁿ`, the squared Euclidean distance `ρ(z) = ‖z - c‖²` on `Z` is a
Morse function (`TauCeti.ae_isMorse_norm_sq_sub_comp`). Because `Z → ℂⁿ` is a holomorphic
immersion, `ρ` is strictly plurisubharmonic, so its reciprocal transform `(1 + ρ)⁻¹` is a Morse
function on `Z` whose critical points all have real Morse index at least `d`
(`TauCeti.IsManifoldStrictlyPlurisubharmonicAt.le_manifoldMorseIndex_inv_one_add`). Read on `X`,
this reciprocal transform extends by `0` across `X ∩ H` to the continuous function
`F = Projectivization.affineChartInvOneAddDistSq i c`, which takes values in `[0, 1]` and is
strictly positive outside `X ∩ H`.

Consequently, whenever `X ∩ H` admits a neighbourhood `W` in `X` whose inclusion `(X ∩ H) ↪ W` is
a weak homotopy equivalence (for example when `W` deformation retracts onto `X ∩ H`), compactness
of `X` places a positive sublevel `{F ≤ δ}` inside `W`, and reversed handle attachments of `F` of
index at least `d` yield Milnor's relative homotopy Lefschetz theorem (Theorem 7.4):

* the relative homotopy sets `π_j(X, X ∩ H, a₀)` vanish for `1 ≤ j < d`
  (`TauCeti.subsingleton_relHomotopyGroup_notMem_affineOpen`);
* the inclusion `X ∩ H ↪ X` induces surjections `π_j(X ∩ H, a₀) → π_j(X, a₀)` for `j < d` and
  bijections for `j + 1 < d` (`TauCeti.surjective_homotopyGroupMap_notMem_affineOpen`,
  `TauCeti.bijective_homotopyGroupMap_notMem_affineOpen`).

Directly from the cellular homology of the same high-index cell attachments — without passing
through Hurewicz or homotopy groups — if `(X ∩ H) ↪ W` induces isomorphisms on singular homology
in the relevant degrees with coefficients in an object `R` of an abelian category with small
coproducts, then:

* the relative singular homology `H_j(X, X ∩ H; R)` vanishes for `j < d`
  (`TauCeti.isZero_singularHomology_notMem_affineOpen`);
* the inclusion `X ∩ H ↪ X` induces epimorphisms on `H_j(·; R)` for `j < d` and isomorphisms for
  `j + 1 < d` (`TauCeti.epi_homologyMap_notMem_affineOpen`,
  `TauCeti.isIso_homologyMap_notMem_affineOpen`).

Specializing to `X = complexProjectiveZeroLocus p` for a finite family `p` of homogeneous
polynomials whose dehomogenizations in chart `i` have surjective Jacobian at every common zero
yields the corresponding relative homotopy and homology Lefschetz theorems in degrees below the
affine complete-intersection dimension `n - |ι|`.

## Main results

* `TauCeti.subsingleton_relHomotopyGroup_notMem_affineOpen`,
  `TauCeti.surjective_homotopyGroupMap_notMem_affineOpen`,
  `TauCeti.bijective_homotopyGroupMap_notMem_affineOpen`: Milnor's Theorem 7.4 on relative
  homotopy and homotopy-group maps of `(X, X ∩ H)`.
* `TauCeti.isZero_singularHomology_notMem_affineOpen`,
  `TauCeti.epi_homologyMap_notMem_affineOpen`,
  `TauCeti.isIso_homologyMap_notMem_affineOpen`: direct cellular/Morse proof of the homological
  weak Lefschetz theorem for `(X, X ∩ H)` with arbitrary abelian-category coefficients.
* `TauCeti.subsingleton_relHomotopyGroup_complexProjectiveZeroLocus_notMem_affineOpen`,
  `TauCeti.surjective_homotopyGroupMap_complexProjectiveZeroLocus_notMem_affineOpen`,
  `TauCeti.bijective_homotopyGroupMap_complexProjectiveZeroLocus_notMem_affineOpen`,
  `TauCeti.isZero_singularHomology_complexProjectiveZeroLocus_notMem_affineOpen`,
  `TauCeti.epi_homologyMap_complexProjectiveZeroLocus_notMem_affineOpen`,
  `TauCeti.isIso_homologyMap_complexProjectiveZeroLocus_notMem_affineOpen`: specializations to
  projective zero loci with smooth complete-intersection affine complement.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Section 7, Theorem 7.4.
* A. Andreotti and T. Frankel, *The Lefschetz theorem on hyperplane sections*, Annals of
  Mathematics (2) 69 (1959), 713–717.
-/

public section

noncomputable section

open CategoryTheory Limits Function MvPolynomial Set Topology
open scoped ContDiff LinearAlgebra.Projectivization Manifold Topology.Homotopy

universe v w

namespace TauCeti

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}

/-- Given a closed `X ⊆ ℂℙⁿ` whose affine part `Z ⊆ ℂⁿ` in chart `i` is a holomorphically immersed
complex manifold, construct the open embedding `j : Z → X` onto `X \ H_i` and choose a generic
centre `c ∈ ℂⁿ` so that `F = affineChartInvOneAddDistSq i c` on `X` pulls back along `j` to a
Morse function whose critical points all have Morse index at least `dim_ℂ E`. -/
private theorem exists_openEmbedding_isMorse_affineChartInvOneAddDistSq
    {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z)) :
    have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
    ∃ (j : Z → X) (F : X → ℝ),
      IsOpenEmbedding j ∧ Continuous F ∧ IsMorse 𝓘(ℝ, E) (F ∘ j) ∧ BddAbove (range F) ∧
      (∀ x ∉ range j, F x ≤ 0) ∧
      (∀ x ∈ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, F x ≤ 0) ∧
      (∀ x ∉ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, 0 < F x) ∧
      (∀ a b, 0 < a → a ≤ b → IsCompact (F ⁻¹' Icc a b)) ∧
      (∀ p ∈ criticalPoints 𝓘(ℝ, E) (F ∘ j),
        Module.finrank ℂ E ≤ manifoldMorseIndex 𝓘(ℝ, E) (F ∘ j) p) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  have : IsManifold 𝓘(ℝ, E) 2 Z := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold 𝓘(ℂ, E) 2 Z := IsManifold.of_le (n := ∞) (by simp)
  -- Step 1: restrict `(affineChart i).symm` to an open embedding `j : Z → X` onto `X \ H_i`.
  let j : Z → X := Projectivization.affineChartSymmRestrict i hZ
  have hj : IsOpenEmbedding j := Projectivization.isOpenEmbedding_affineChartSymmRestrict i hZ
  -- Step 2: compose `Z → Fin n → ℂ` with the linear equivalence onto `EuclideanSpace ℂ (Fin n)`
  -- and restrict scalars from `ℂ` to `ℝ`, preserving derivative injectivity.
  let eL := (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n ↦ ℂ).symm
  let ι : Z → EuclideanSpace ℂ (Fin n) := eL ∘ Subtype.val
  have hιC : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ ι :=
    eL.contDiff.contMDiff.comp hZval
  have hιR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ ι := by
    simpa using hιC.restrictScalars ℝ
  have hinj_mvC (z : Z) : Injective (mvfderiv 𝓘(ℂ, E) ι z) := by
    intro v w hvw
    have hmd : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z :=
      (hZval z).mdifferentiableAt (by simp)
    simp only [ι, mvfderiv_comp_apply_of_differentiableAt eL.differentiableAt hmd,
      eL.fderiv, mvfderiv_apply_eq_mfderiv_apply] at hvw
    exact hinj z (eL.injective hvw)
  have hinj_mfC (z : Z) : Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ι z) :=
    fun v w hvw ↦ hinj_mvC z
      ((mvfderiv_apply_eq_mfderiv_apply ι z v).trans
        (hvw.trans (mvfderiv_apply_eq_mfderiv_apply ι z w).symm))
  have hinj_mfR (z : Z) : Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ι z) :=
    ((hιC z).mdifferentiableAt (by simp)).injective_mfderiv_restrictScalars ℝ (hinj_mfC z)
  -- Step 3: choose a generic centre `c` so `ρ(z) = ‖ι z - c‖²` is Morse on `Z`, and identify the
  -- pullback `F ∘ j` of `affineChartInvOneAddDistSq i c` with `(1 + ρ)⁻¹`.
  let _ : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin n)) := InnerProductSpace.rclikeToReal ℂ _
  obtain ⟨c, hc_morse⟩ :=
    (ae_isMorse_norm_sq_sub_comp
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin n)))
      hιR hinj_mfR).exists
  let ρ : Z → ℝ := fun z ↦ ‖ι z - c‖ ^ 2
  let F : X → ℝ := fun x ↦ Projectivization.affineChartInvOneAddDistSq i c x.1
  have hF_cont : Continuous F :=
    (Projectivization.continuous_affineChartInvOneAddDistSq i c).comp continuous_subtype_val
  have hFj : F ∘ j = fun z : Z ↦ (1 + ρ z)⁻¹ := by
    ext z
    dsimp only [Function.comp_apply, F, j, ι, ρ, eL]
    rw [Projectivization.coe_affineChartSymmRestrict,
      Projectivization.affineChartInvOneAddDistSq_affineChart_symm, dist_eq_norm,
      PiLp.coe_symm_continuousLinearEquiv]
  have hρ_denom (z : Z) : 1 + ρ z ≠ 0 := by dsimp only [ρ]; positivity
  have hf_morse : IsMorse 𝓘(ℝ, E) (F ∘ j) := hFj ▸ hc_morse.inv_one_add hρ_denom
  -- Step 4: verify the sign, compactness, and plurisubharmonic Morse-index lower bound of `F`.
  refine ⟨j, F, hj, hF_cont, hf_morse,
    ⟨1, forall_mem_range.2 fun x ↦ Projectivization.affineChartInvOneAddDistSq_le_one i c x.1⟩,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x hx ↦ ?_,
    fun _ _ _ _ ↦ (isClosed_Icc.preimage hF_cont).isCompact, fun p hp ↦ ?_⟩
  · rw [Projectivization.range_affineChartSymmRestrict] at hx
    exact (Projectivization.affineChartInvOneAddDistSq_of_notMem hx).le
  · exact (Projectivization.affineChartInvOneAddDistSq_of_notMem hx).le
  · simp only [mem_ofPred_eq, not_not] at hx
    exact (Projectivization.affineChartInvOneAddDistSq_pos_iff i c).2 hx
  · have hφ' : deriv (fun t : ℝ ↦ (1 + t)⁻¹) (ρ p) ≠ 0 := by
      rw [deriv_fun_inv'' (differentiableAt_id.const_add 1) (hρ_denom p)]
      simp [hρ_denom p]
    have hp_ρ : p ∈ criticalPoints 𝓘(ℝ, E) ρ := by
      rw [hFj] at hp
      exact (mem_criticalPoints_scalar_comp_iff (f := ρ) (φ := fun t ↦ (1 + t)⁻¹)
        ((hc_morse.contMDiff p).mdifferentiableAt (by simp)) hφ').1 hp
    have hpsh : IsManifoldStrictlyPlurisubharmonicAt E ρ p :=
      (isManifoldStrictlyPlurisubharmonicAt_norm_sq_sub_comp_iff ((hιC p).of_le (by simp))).2
        (hinj_mvC p)
    simpa only [hFj] using hpsh.le_manifoldMorseIndex_inv_one_add
      (hc_morse.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints hp_ρ) (hρ_denom p)

/-- **Path-component surjectivity of a hyperplane section.** If `X ⊆ ℂℙⁿ` is closed, `X \ H_i` is a
holomorphically immersed complex manifold of positive dimension, and `X ∩ H_i` admits a
neighbourhood `W` in `X` whose inclusion `(X ∩ H_i) ↪ W` is a weak homotopy equivalence, then
every point of `X` can be joined by a path in `X` to a point of `X ∩ H_i`. -/
theorem exists_joined_notMem_affineOpen {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X)
    (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hd : 0 < Module.finrank ℂ E) (x : X) :
    ∃ a : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i},
      Joined (a : X) x := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.exists_joined_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex hW
    (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hd x

/-- **Path-component injectivity of a hyperplane section.** When the affine complement has complex
dimension at least `2`, two points of `X ∩ H_i` are joined by a path in `X` if and only if they are
joined by a path in `X ∩ H_i`. -/
theorem joined_notMem_affineOpen_iff {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X)
    (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hd : 1 < Module.finrank ℂ E)
    {a₀ a₁ : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}} :
    Joined (a₀ : X) (a₁ : X) ↔ Joined a₀ a₁ := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.joined_subtypeVal_iff_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex hW
    (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hd

/-- **Lefschetz hyperplane surjectivity on homotopy groups (Milnor, Theorem 7.4).** The inclusion
`X ∩ H_i ↪ X` induces a surjection `π_k(X ∩ H_i, a₀) → π_k(X, a₀)` for `k < dim_ℂ Z`. -/
theorem surjective_homotopyGroupMap_notMem_affineOpen {J : Type v} [Finite J]
    {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J < Module.finrank ℂ E)
    (a₀ : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Surjective (HomotopyGroup.map (N := J) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X))) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.surjective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex
    hW (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hJ a₀

/-- **Lefschetz hyperplane bijectivity on homotopy groups (Milnor, Theorem 7.4).** The inclusion
`X ∩ H_i ↪ X` induces a bijection `π_k(X ∩ H_i, a₀) → π_k(X, a₀)` for `k + 1 < dim_ℂ Z`. -/
theorem bijective_homotopyGroupMap_notMem_affineOpen {J : Type v} [Finite J]
    {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J + 1 < Module.finrank ℂ E)
    (a₀ : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Bijective (HomotopyGroup.map (N := J) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩ (rfl : (a₀ : X) = (a₀ : X))) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.bijective_homotopyGroupMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex
    hW (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hJ a₀

/-- **Relative homotopy Lefschetz theorem (Milnor, Theorem 7.4).** Let `X ⊆ ℂℙⁿ` be closed, with
affine part `X \ H_i ≅ Z` a holomorphically immersed complex manifold of complex dimension `d`, and
let `W` be a neighbourhood of `X ∩ H_i` in `X` whose inclusion `(X ∩ H_i) ↪ W` is a weak homotopy
equivalence. Then `π_{k+1}(X, X ∩ H_i, a₀) = 0` whenever `k + 1 < d`. No smoothness of `X` is
assumed along `X ∩ H_i`. -/
theorem subsingleton_relHomotopyGroup_notMem_affineOpen {J : Type v} [Finite J]
    {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J + 1 < Module.finrank ℂ E)
    (a₀ : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Subsingleton (RelHomotopyGroup J
      ⟨TopPair.ofSubset (X := TopCat.of X)
        {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, a₀⟩) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.subsingleton_relHomotopyGroup_ofSubset_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex
    hW (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hJ a₀

section Homology

variable {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{0} A_cat]

/-- **Homological Lefschetz epimorphism.** If `(X ∩ H_i) ↪ W` induces a singular homology
isomorphism in degree `k` on a neighbourhood `W` of `X ∩ H_i` in `X`, then `(X ∩ H_i) ↪ X` induces
an epimorphism `H_k(X ∩ H_i; R) ⟶ H_k(X; R)` for `k < dim_ℂ Z`. -/
theorem epi_homologyMap_notMem_affineOpen {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X)
    (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    (R : A_cat) {k : ℕ} {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k < Module.finrank ℂ E) :
    Epi (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C({x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, X)))) R k) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.epi_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex R hW
    (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hk

/-- **Homological Lefschetz isomorphism.** If `(X ∩ H_i) ↪ W` induces a singular homology
isomorphism in degree `k` on a neighbourhood `W` of `X ∩ H_i` in `X`, then `(X ∩ H_i) ↪ X` induces
an isomorphism `H_k(X ∩ H_i; R) ≅ H_k(X; R)` for `k + 1 < dim_ℂ Z`. -/
theorem isIso_homologyMap_notMem_affineOpen {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))} (hX : IsClosed X)
    (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    (R : A_cat) {k : ℕ} {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k + 1 < Module.finrank ℂ E) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C({x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, X)))) R k) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.isIso_homologyMap_subtypeVal_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex R hW
    (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hk

/-- **Homological weak Lefschetz theorem.** If `(X ∩ H_i) ↪ W` induces singular homology
isomorphisms in degree `k` and (when `k > 0`) degree `k - 1` on a neighbourhood `W` of `X ∩ H_i` in
`X`, then the relative singular homology `H_k(X, X ∩ H_i; R)` vanishes for `k < dim_ℂ Z`, proved
directly from high-index Morse cell attachments on `X \ H_i`. -/
theorem isZero_singularHomology_notMem_affineOpen {X : Set (ℙ ℂ (Fin (n + 1) → ℂ))}
    (hX : IsClosed X) (i : Fin (n + 1)) {Z : Set (Fin n → ℂ)}
    (hZ : Projectivization.affineChart i '' (X ∩ Projectivization.affineOpen i) = Z)
    [ChartedSpace E Z] [IsManifold 𝓘(ℂ, E) ∞ Z]
    (hZval : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) ∞ (Subtype.val : Z → Fin n → ℂ))
    (hinj : ∀ z : Z, Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin n → ℂ) Subtype.val z))
    (R : A_cat) {k : ℕ} {W : Set X}
    {hAW : {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : ∀ m, m = k ∨ m + 1 = k → IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R m))
    (hW_nhds : W ∈ 𝓝ˢ {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k < Module.finrank ℂ E) :
    IsZero ((TopPair.ofSubset (X := TopCat.of X)
      {x : X | (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}).singularHomology
      R k) := by
  have : CompactSpace X := isCompact_iff_compactSpace.1 hX.isCompact
  have : IsManifold 𝓘(ℝ, E) ∞ Z := (inferInstance : IsManifold 𝓘(ℂ, E) ∞ Z).restrictScalars ℝ
  obtain ⟨j, F, hj, hF, hf, hbdd, hA, hAF, hpos, hcpt, hindex⟩ :=
    exists_openEmbedding_isMorse_affineChartInvOneAddDistSq hX i hZ hZval hinj
  exact hf.isZero_singularHomology_ofSubset_of_isOpenEmbedding hj hF hbdd hA hAF hcpt hindex R hW
    (exists_pos_sublevel_subset_of_mem_nhdsSet hF hpos hW_nhds) hk

end Homology

end General

section ZeroLocus

variable {n : ℕ} {ι : Type*} [Fintype ι] {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}

/-- **Path-component surjectivity for a hyperplane section of a projective zero locus.** -/
theorem exists_joined_complexProjectiveZeroLocus_notMem_affineOpen
    (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hd : 0 < n - Fintype.card ι) (x : complexProjectiveZeroLocus p) :
    ∃ a : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i},
      Joined (a : complexProjectiveZeroLocus p) x := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact exists_joined_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    hW hW_nhds (by simpa [Module.finrank_fin_fun] using hd) x

/-- **Path-component injectivity for a hyperplane section of a projective zero locus.** -/
theorem joined_complexProjectiveZeroLocus_notMem_affineOpen_iff
    (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hd : 1 < n - Fintype.card ι)
    {a₀ a₁ : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}} :
    Joined (a₀ : complexProjectiveZeroLocus p) (a₁ : complexProjectiveZeroLocus p) ↔
      Joined a₀ a₁ := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact joined_notMem_affineOpen_iff (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    hW hW_nhds (by simpa [Module.finrank_fin_fun] using hd)

/-- **Relative homotopy Lefschetz theorem for a projective zero locus.** Let `X` be the zero locus
in `ℂℙⁿ` of a finite family of homogeneous polynomials whose dehomogenizations in chart `i` have
surjective Jacobian at every common zero, so `X \ H_i` is a smooth affine complete intersection of
dimension `n - |ι|`. If `W` is a neighbourhood of `X ∩ H_i` in `X` whose inclusion `(X ∩ H_i) ↪ W`
is a weak homotopy equivalence, then `π_{k+1}(X, X ∩ H_i, a₀) = 0` for `k + 1 < n - |ι|`. -/
theorem subsingleton_relHomotopyGroup_complexProjectiveZeroLocus_notMem_affineOpen
    {J : Type v} [Finite J] (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J + 1 < n - Fintype.card ι)
    (a₀ : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Subsingleton (RelHomotopyGroup J
      ⟨TopPair.ofSubset (X := TopCat.of (complexProjectiveZeroLocus p))
        {x : complexProjectiveZeroLocus p |
          (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}, a₀⟩) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact subsingleton_relHomotopyGroup_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    hW hW_nhds (by simpa [Module.finrank_fin_fun] using hJ) a₀

/-- **Homotopy-group surjectivity for a hyperplane section of a projective zero locus.** Under the
same hypotheses, `(X ∩ H_i) ↪ X` induces a surjection `π_k(X ∩ H_i, a₀) → π_k(X, a₀)` for
`k < n - |ι|`. -/
theorem surjective_homotopyGroupMap_complexProjectiveZeroLocus_notMem_affineOpen
    {J : Type v} [Finite J] (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J < n - Fintype.card ι)
    (a₀ : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Surjective (HomotopyGroup.map (N := J) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩
      (rfl : (a₀ : complexProjectiveZeroLocus p) = (a₀ : complexProjectiveZeroLocus p))) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact surjective_homotopyGroupMap_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    hW hW_nhds (by simpa [Module.finrank_fin_fun] using hJ) a₀

/-- **Homotopy-group bijectivity for a hyperplane section of a projective zero locus.** Under the
same hypotheses, `(X ∩ H_i) ↪ X` induces a bijection `π_k(X ∩ H_i, a₀) → π_k(X, a₀)` for
`k + 1 < n - |ι|`. -/
theorem bijective_homotopyGroupMap_complexProjectiveZeroLocus_notMem_affineOpen
    {J : Type v} [Finite J] (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : (ContinuousMap.inclusion hAW).IsWeakHomotopyEquivalence)
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hJ : Nat.card J + 1 < n - Fintype.card ι)
    (a₀ : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}) :
    Bijective (HomotopyGroup.map (N := J) (x := a₀)
      ⟨Subtype.val, continuous_subtype_val⟩
      (rfl : (a₀ : complexProjectiveZeroLocus p) = (a₀ : complexProjectiveZeroLocus p))) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact bijective_homotopyGroupMap_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    hW hW_nhds (by simpa [Module.finrank_fin_fun] using hJ) a₀

section ZeroLocusHomology

variable {A_cat : Type v} [Category.{w} A_cat] [Abelian A_cat] [HasCoproducts.{0} A_cat]

/-- **Homological Lefschetz epimorphism for a projective zero locus.** -/
theorem epi_homologyMap_complexProjectiveZeroLocus_notMem_affineOpen
    (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    (R : A_cat) {k : ℕ} {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k < n - Fintype.card ι) :
    Epi (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C({x : complexProjectiveZeroLocus p |
          (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i},
          complexProjectiveZeroLocus p)))) R k) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact epi_homologyMap_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    R hW hW_nhds (by simpa [Module.finrank_fin_fun] using hk)

/-- **Homological Lefschetz isomorphism for a projective zero locus.** -/
theorem isIso_homologyMap_complexProjectiveZeroLocus_notMem_affineOpen
    (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    (R : A_cat) {k : ℕ} {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R k))
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k + 1 < n - Fintype.card ι) :
    IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
        C({x : complexProjectiveZeroLocus p |
          (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i},
          complexProjectiveZeroLocus p)))) R k) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact isIso_homologyMap_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    R hW hW_nhds (by simpa [Module.finrank_fin_fun] using hk)

/-- **Homological weak Lefschetz theorem for a projective zero locus.** -/
theorem isZero_singularHomology_complexProjectiveZeroLocus_notMem_affineOpen
    (hp : ∀ m, (p m).IsHomogeneous (d m)) (i : Fin (n + 1))
    (hrank : ∀ z ∈ affineZeroLocus fun m ↦ dehomogenize i (p m),
      Surjective (jacobiMatrixAt (fun m ↦ dehomogenize i (p m)) z).mulVec)
    (R : A_cat) {k : ℕ} {W : Set (complexProjectiveZeroLocus p)}
    {hAW : {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i} ⊆ W}
    (hW : ∀ m, m = k ∨ m + 1 = k → IsIso (SSet.homologyMap (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.inclusion hAW))) R m))
    (hW_nhds : W ∈ 𝓝ˢ {x : complexProjectiveZeroLocus p |
      (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i})
    (hk : k < n - Fintype.card ι) :
    IsZero ((TopPair.ofSubset (X := TopCat.of (complexProjectiveZeroLocus p))
      {x : complexProjectiveZeroLocus p |
        (x : ℙ ℂ (Fin (n + 1) → ℂ)) ∉ Projectivization.affineOpen i}).singularHomology R k) := by
  let _ := affineZeroLocusChartedSpace hrank
  have := isManifold_affineZeroLocus hrank ∞
  exact isZero_singularHomology_notMem_affineOpen (isClosed_complexProjectiveZeroLocus p) i
    (image_affineChart_complexProjectiveZeroLocus_inter_affineOpen hp i)
    (contMDiff_coe_affineZeroLocus hrank ∞) (injective_mfderiv_coe_affineZeroLocus hrank)
    R hW hW_nhds (by simpa [Module.finrank_fin_fun] using hk)

end ZeroLocusHomology

end ZeroLocus

end TauCeti
