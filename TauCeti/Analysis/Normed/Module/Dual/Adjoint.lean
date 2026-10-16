/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.Analysis.Normed.Operator.Banach

/-!
# Kernels and ranges of adjoints, and the closed-range theorem

The adjoint of a continuous linear map `T : E →L[𝕜] F` between normed spaces is precomposition
`ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E`. Annihilators are
Mathlib's `Submodule.orthogonalBilin` for the canonical pairing `topDualPairing`: for `S ≤ E`,
`S.orthogonalBilin (topDualPairing 𝕜 E).flip` is the annihilator of `S` in the dual, and for
`G ≤ StrongDual 𝕜 E`, `G.orthogonalBilin (topDualPairing 𝕜 E)` is the preannihilator of `G`
in `E`.

This file proves the unconditional identities `ker T* = (range T)ᗮ`,
`range T* ≤ (ker T)ᗮ` and, when functionals separate points of `F`, `ker T = (range T*)_⊥`.
For a bounded operator between Banach spaces it then proves the **closed-range theorem**:
`range T` is closed iff `range T*` is closed, in which case `range T* = (ker T)ᗮ`.

The reverse implication only needs the domain to be complete. It goes through the criterion
that a map whose adjoint is bounded below is surjective: geometric Hahn–Banach shows that the
closure of the image of a ball contains a ball, and Banach's lemma
`ContinuousLinearMap.exists_preimage_norm_le_of_mem_closure` upgrades this to surjectivity.
Completeness of the domain cannot be dropped: the inclusion of finitely supported sequences
into `ℓ²` has dense proper range, while its adjoint is surjective.

## Main declarations

* `ContinuousLinearMap.ker_precomp_eq_orthogonalBilin_range`: `ker T* = (range T)ᗮ`.
* `ContinuousLinearMap.ker_eq_orthogonalBilin_range_precomp`: `ker T = (range T*)_⊥`.
* `ContinuousLinearMap.range_precomp_eq_orthogonalBilin_ker`: if `range T` is closed, then
  `range T* = (ker T)ᗮ`.
* `ContinuousLinearMap.surjective_of_norm_le_norm_comp`: a map whose adjoint is bounded below
  is surjective.
* `ContinuousLinearMap.isClosed_range_precomp_iff`: the closed-range theorem.

## References

* W. Rudin, *Functional Analysis*, 2nd ed., Theorems 4.12, 4.14 and 4.15.
-/

public section

open Function Metric Set Topology
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*}

section Algebraic

variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The kernel of the adjoint is the annihilator of the range. -/
theorem ker_precomp_eq_orthogonalBilin_range (T : E →L[𝕜] F) :
    (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).ker =
      T.range.orthogonalBilin (topDualPairing 𝕜 F).flip := by
  ext g
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonalBilin, LinearMap.mem_range,
    LinearMap.flip_apply, topDualPairing_apply, forall_exists_index,
    forall_apply_eq_imp_iff, coe_coe, ContinuousLinearMap.ext_iff, precomp_apply, comp_apply,
    zero_apply]

/-- The range of the adjoint annihilates the kernel. -/
theorem range_precomp_le_orthogonalBilin_ker (T : E →L[𝕜] F) :
    (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range ≤
      T.ker.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  rintro _ ⟨g, rfl⟩ x hx
  simp_all

/-- When continuous functionals separate the points of `F`, the kernel of a map is the
preannihilator of the range of its adjoint. -/
theorem ker_eq_orthogonalBilin_range_precomp [SeparatingDual 𝕜 F] (T : E →L[𝕜] F) :
    T.ker = (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range.orthogonalBilin
      (topDualPairing 𝕜 E) := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_orthogonalBilin, LinearMap.mem_range,
    topDualPairing_apply, forall_exists_index, forall_apply_eq_imp_iff,
    precomp_apply, comp_apply, coe_coe]
  exact SeparatingDual.eq_zero_iff_forall_dual_eq_zero (T x)

end Algebraic

section HahnBanach

variable [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Closed-range theorem, range of the adjoint.** If a bounded operator between Banach
spaces has closed range, then the range of its adjoint is exactly the annihilator of its
kernel. -/
theorem range_precomp_eq_orthogonalBilin_ker (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range =
      T.ker.orthogonalBilin (topDualPairing 𝕜 E).flip := by
  refine le_antisymm T.range_precomp_le_orthogonalBilin_ker fun f hf ↦ ?_
  -- `f` is constant on the fibres of `T`.
  have hf' : ∀ x x', T x = T x' → f x = f x' := by
    intro x x' h
    have hx : x - x' ∈ T.ker := by simp [h]
    simpa [sub_eq_zero] using Submodule.mem_orthogonalBilin.mp hf _ hx
  -- By the open mapping theorem, every point of the range has a preimage of controlled norm.
  have : CompleteSpace T.range := hT.completeSpace_coe
  obtain ⟨C, -, hC⟩ := T.rangeRestrict.exists_preimage_norm_le fun y ↦ by
    obtain ⟨_, x, rfl⟩ := y
    exact ⟨x, rfl⟩
  choose pre hpre hnorm using hC
  have hTpre : ∀ y : T.range, T (pre y) = y := fun y ↦ by simpa using congrArg Subtype.val (hpre y)
  -- Hence `f` descends to a bounded functional on the range, which extends to `F`.
  let g : T.range →ₗ[𝕜] 𝕜 :=
    { toFun y := f (pre y)
      map_add' a b := by
        rw [← map_add]
        exact hf' _ _ (by simp [hTpre])
      map_smul' c a := by
        rw [RingHom.id_apply, smul_eq_mul, ← smul_eq_mul, ← map_smul]
        exact hf' _ _ (by simp [hTpre]) }
  let g' : StrongDual 𝕜 T.range := g.mkContinuous (‖f‖ * C) fun y ↦
    calc ‖f (pre y)‖ ≤ ‖f‖ * ‖pre y‖ := f.le_opNorm _
      _ ≤ ‖f‖ * (C * ‖y‖) := by gcongr; exact hnorm y
      _ = ‖f‖ * C * ‖y‖ := by ring
  obtain ⟨G, hG, -⟩ := exists_extension_norm_eq T.range g'
  refine ⟨G, ext fun x ↦ ?_⟩
  have hx := hG ⟨T x, x, rfl⟩
  simp only [coe_coe, precomp_apply, comp_apply]
  rw [hx, LinearMap.mkContinuous_apply]
  exact hf' _ _ (hTpre _)

/-- If a bounded operator between Banach spaces has closed range, then so does its adjoint. -/
theorem isClosed_range_precomp_of_isClosed_range (T : E →L[𝕜] F)
    (hT : IsClosed (T.range : Set F)) :
    IsClosed ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range :
      Set (StrongDual 𝕜 E)) := by
  have h := ker_precomp_eq_orthogonalBilin_range (𝕜 := 𝕜) T.ker.subtypeL
  rw [Submodule.toLinearMap_subtypeL, Submodule.range_subtype] at h
  rw [T.range_precomp_eq_orthogonalBilin_ker hT, ← h]
  exact isClosed_ker _

end HahnBanach

section RCLike

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If the adjoint of `S` is bounded below with constant `K`, then every `y` lies in the closure
of the image of the closed ball of radius `K * ‖y‖`. -/
theorem mem_closure_image_closedBall_of_norm_le_norm_comp (S : E →L[𝕜] F) {K : ℝ≥0}
    (hK : ∀ g : StrongDual 𝕜 F, ‖g‖ ≤ K * ‖g.comp S‖) (y : F) :
    y ∈ closure (S '' closedBall 0 (K * ‖y‖)) := by
  set r : ℝ := K * ‖y‖ with hr_def
  have hr : 0 ≤ r := by positivity
  by_contra hy
  -- Separate `y` from the closed real-convex hull of the image of the ball.
  obtain ⟨f, u, hfK, hfy⟩ : ∃ (f : StrongDual 𝕜 F) (u : ℝ),
      (∀ a ∈ closure (S '' closedBall (0 : E) r), RCLike.re (f a) < u) ∧
        u < RCLike.re (f y) := by
    let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
    let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
    have : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
    have : IsScalarTower ℝ 𝕜 F := .restrictScalars ℝ 𝕜 F
    have hconv : Convex ℝ (S '' closedBall (0 : E) r) :=
      (convex_closedBall 0 r).linear_image ((S : E →ₗ[𝕜] F).restrictScalars ℝ)
    exact RCLike.geometric_hahn_banach_closed_point hconv.closure isClosed_closure hy
  -- The separated set is balanced, so the real-part bound is a bound on the modulus.
  have hball : ∀ x ∈ closedBall (0 : E) r, ‖f (S x)‖ ≤ u := by
    intro x hx
    have hre : ∀ c : 𝕜, ‖c‖ = 1 → RCLike.re (c * f (S x)) ≤ u := fun c hc ↦ by
      have hcx : c • x ∈ closedBall (0 : E) r := by simpa [norm_smul, hc] using hx
      simpa using (hfK _ (subset_closure ⟨c • x, hcx, rfl⟩)).le
    obtain ⟨c, hc, heq⟩ := RCLike.exists_norm_eq_mul_self (f (S x))
    simpa only [← heq, RCLike.ofReal_re] using hre c hc
  have hu : 0 ≤ u := by simpa using hball 0 (by simpa using hr)
  have hfS : ‖f.comp S‖ * r ≤ u := by
    rcases hr.eq_or_lt with h | h
    · rw [← h, mul_zero]
      exact hu
    · refine (le_div_iff₀ h).mp (opNorm_le_of_unit_norm (div_nonneg hu h.le) fun x hx ↦ ?_)
      have hmem : (r : 𝕜) • x ∈ closedBall (0 : E) r := by
        simp [norm_smul, hx, abs_of_pos h]
      have hrx := hball _ hmem
      rw [map_smul, map_smul, norm_smul, RCLike.norm_ofReal, abs_of_pos h] at hrx
      rw [le_div_iff₀ h, comp_apply, mul_comm]
      exact hrx
  have hfy' := (RCLike.re_le_norm (f y)).trans (f.le_opNorm y)
  have : ‖f‖ * ‖y‖ ≤ ‖f.comp S‖ * r :=
    calc ‖f‖ * ‖y‖ ≤ K * ‖f.comp S‖ * ‖y‖ := by gcongr; exact hK f
      _ = ‖f.comp S‖ * r := by rw [hr_def]; ring
  linarith

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- A bounded operator on a Banach space whose adjoint is bounded below is surjective. -/
theorem surjective_of_norm_le_norm_comp (S : E →L[𝕜] F) {K : ℝ≥0}
    (hK : ∀ g : StrongDual 𝕜 F, ‖g‖ ≤ K * ‖g.comp S‖) : Surjective S := fun y ↦
  let ⟨x, hx, _⟩ := S.exists_preimage_norm_le_of_mem_closure
    (S.mem_closure_image_closedBall_of_norm_le_norm_comp hK) y
  ⟨x, hx⟩

/-- **Closed-range theorem, reverse implication.** If the adjoint of a bounded operator on a
Banach space has closed range, then the operator has closed range. The codomain need not be
complete. -/
theorem isClosed_range_of_isClosed_range_precomp (T : E →L[𝕜] F)
    (h : IsClosed ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range :
      Set (StrongDual 𝕜 E))) :
    IsClosed (T.range : Set F) := by
  -- Corestrict `T` to the closure `Z` of its range; it suffices to show this is surjective.
  set Z := T.range.topologicalClosure
  have hmem : ∀ x, T x ∈ Z := fun x ↦ T.range.le_topologicalClosure ⟨x, rfl⟩
  let T₀ : E →L[𝕜] Z := T.codRestrict Z hmem
  have hT₀ : Z.subtypeL ∘ T₀ = T := funext (T.coe_codRestrict_apply Z hmem)
  have hdense : DenseRange T₀ := by
    refine Z.isEmbedding_subtypeL.isInducing.dense_iff.2 fun z ↦ ?_
    have hz : (z : F) ∈ closure (T.range : Set F) := by
      rw [← Submodule.topologicalClosure_coe]
      exact z.2
    rwa [← Set.range_comp, hT₀, ← coe_coe, ← LinearMap.coe_range]
  -- The adjoint of `T₀` is injective, and by Hahn–Banach it has the same range as that of `T`.
  let A : StrongDual 𝕜 Z →L[𝕜] StrongDual 𝕜 E := precomp 𝕜 T₀
  have hinj : Injective A := fun ψ₁ ψ₂ hψ ↦ DFunLike.coe_injective <|
    hdense.equalizer ψ₁.continuous ψ₂.continuous (funext fun x ↦ DFunLike.congr_fun hψ x)
  have hrange : Set.range A =
      ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range : Set (StrongDual 𝕜 E)) := by
    ext φ
    constructor
    · rintro ⟨ψ, rfl⟩
      obtain ⟨g, hg, -⟩ := exists_extension_norm_eq Z ψ
      exact ⟨g, ext fun x ↦ by simpa [A, T₀] using hg (T₀ x)⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.comp Z.subtypeL, ext fun x ↦ by simp [A, T₀]⟩
  -- So the adjoint of `T₀` is bounded below, and `T₀` is surjective.
  obtain ⟨K, hK⟩ := A.antilipschitz_of_injective_of_isClosed_range hinj (hrange ▸ h)
  have hsurj : Surjective T₀ :=
    T₀.surjective_of_norm_le_norm_comp fun ψ ↦ by simpa [A] using A.bound_of_antilipschitz hK ψ
  have hZ : (T.range : Set F) = Z := by
    refine subset_antisymm T.range.le_topologicalClosure fun z hz ↦ ?_
    obtain ⟨x, hx⟩ := hsurj ⟨z, hz⟩
    exact ⟨x, by simpa [T₀] using congrArg Subtype.val hx⟩
  rw [hZ]
  exact T.range.isClosed_topologicalClosure

/-- **Closed-range theorem.** A bounded operator between Banach spaces has closed range if and
only if its adjoint has closed range. -/
theorem isClosed_range_precomp_iff [CompleteSpace F] (T : E →L[𝕜] F) :
    IsClosed ((precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E).range :
      Set (StrongDual 𝕜 E)) ↔ IsClosed (T.range : Set F) :=
  ⟨T.isClosed_range_of_isClosed_range_precomp, T.isClosed_range_precomp_of_isClosed_range⟩

end Complete

end RCLike

end ContinuousLinearMap
