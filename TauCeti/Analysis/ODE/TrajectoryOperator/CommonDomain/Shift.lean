/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SpectralFlow
public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.Conjugation
public import TauCeti.Analysis.Fredholm.Spectral.CommonDomain.Conjugation
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Normed.Operator.LinearPMap.CommonDomain.Spectrum
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The index of the trajectory operator along a path of shifts crossing one eigenvalue

Let `ι : D →L[ℝ] H` be a compact operator from a Banach space into a Hilbert space, and let
`B : D →L[ℝ] H` be `ι`-symmetric, `⟪B x, ι y⟫ = ⟪ι x, B y⟫`, with some invertible shift
`B - c ι`. For injective `ι` such a pair is a self-adjoint operator on `H` with domain `range ι`
and compact resolvent, such as the asymptotic operator `J₀ ∂ₜ + S` of the Floer equation with
`D = H¹` and `H = L²`.
Its eigenvalues are the real `μ` with `B x = μ ι x` for some `x ≠ 0`.

This file computes the index of the trajectory operator `D_A u = (ι ∘ u)' + A u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` for the paths of shifts `A s = B - f(s) ι`, where
`f : ℝ → ℝ` is continuous with limits `c₋` and `c₊` at `±∞` that are not eigenvalues, and every
shift `B - f(s) ι` is invertible except where `f(s)` equals one eigenvalue `μ`. For every `a` far
enough to the left and every `b` far enough to the right, the index of `D_A` is the spectral flow
`TauCeti.domainSpectralFlow ι A a b`
(`eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow` in the namespace
`TauCeti.WeakDerivStep`).

A path of shifts crossing a single eigenvalue is the elementary step of the index formula: since
there are only finitely many eigenvalues in a bounded set
(`ContinuousLinearMap.finite_inter_setOf_not_isInvertible_smul_sub`), a change of the limits of a
path by a shift can be broken into steps crossing one eigenvalue each.

## Proof

The path preserves the splitting of `B` along its eigenspace at `μ`, and the block theorem
`eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow` of
`TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain.SpectralFlow` applies after a change of
trivialization.

* **The eigenspace.** The kernel `E` of `μ ι - B` is finite-dimensional, since `μ ι - B` is a
  compact perturbation of an invertible shift, and `ι` is injective on it. Its image
  `F = ι(E) ⊆ H` is finite-dimensional, and `B` acts on it as `μ`.
* **The complement.** By the symmetry of `B`, the subspace `D'` of the `x : D` with
  `ι x ⊥ F` is mapped into `Fᗮ` by `ι` and `B`. On `D'` the shift `μ ι - B` is injective, and every
  other shift `c ι - B` invertible on `D` stays invertible as a map `D' → Fᗮ`: its inverse maps
  `Fᗮ` into `D'`, since `(c - μ) ⟪ι x, ι k⟫ = ⟪(c ι - B) x, ι k⟫` for `k ∈ E`. By the Fredholm
  alternative for shifts (`ContinuousLinearMap.isInvertible_smul_sub_iff_injective`), every shift
  `B - f(s) ι` is invertible as a map `D' → Fᗮ`.
* **The change of trivialization.** The map `(v, x') ↦ ι⁻¹ v + x'` from `F × D'` to `D` is
  bijective, hence an isomorphism by the open mapping theorem, and the orthogonal decomposition
  identifies `H` isometrically with `F × Fᗮ`. They intertwine `ι` with `1 ⊕ ι|_{D'}` and the path
  `A` with the block path `(μ - f(s)) ⊕ (B - f(s) ι)|_{D'}`, whose second block is invertible at
  every time. Changes of trivialization preserve both the index
  (`TauCeti.WeakDerivStep.index_familyDomainTrajectoryOperator_comp_comp_symm`) and the spectral
  flow (`TauCeti.domainSpectralFlow_comp_comp_symm`).

## Main results

In the namespace `TauCeti.WeakDerivStep`:

* `eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow`: the index of
  `∂ₛ + B - f(s) ι` is the spectral flow of the path of shifts, when the shifts cross at most one
  eigenvalue.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, §4.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {ι B : D →L[ℝ] H} {μ c : ℝ}

/-! ### The eigenspace at `μ` and its complement -/

/-- The image under `ι` of the eigenspace of `B` at `μ`, the kernel of `μ ι - B`. -/
private abbrev eigenImage (ι B : D →L[ℝ] H) (μ : ℝ) : Submodule ℝ H :=
  ((μ • ι - B).ker).map (ι : D →ₗ[ℝ] H)

/-- The vectors of `D` whose image under `ι` is orthogonal to the eigenspace of `B` at `μ`. -/
private abbrev eigenCompl (ι B : D →L[ℝ] H) (μ : ℝ) : Submodule ℝ D :=
  (eigenImage ι B μ)ᗮ.comap (ι : D →ₗ[ℝ] H)

private theorem apply_eq_smul_of_mem_ker {k : D} (hk : k ∈ (μ • ι - B).ker) :
    B k = μ • ι k := by
  have h := LinearMap.mem_ker.1 hk
  simp only [ContinuousLinearMap.coe_coe, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
    Pi.smul_apply, sub_eq_zero] at h
  exact h.symm

/-- `ι` is injective on the eigenspace, when some shift is invertible. -/
private theorem eq_zero_of_mem_ker_of_apply_eq_zero (h₀ : (c • ι - B).IsInvertible) {k : D}
    (hk : k ∈ (μ • ι - B).ker) (hιk : ι k = 0) : k = 0 :=
  h₀.injective <| by simp [apply_eq_smul_of_mem_ker hk, hιk]

/-- For `k` in the eigenspace, `⟪ι k, (c ι - B) x⟫ = (c - μ) ⟪ι k, ι x⟫`. -/
private theorem inner_apply_smul_sub_apply (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {k : D}
    (hk : k ∈ (μ • ι - B).ker) (x : D) :
    ⟪ι k, (c • ι - B) x⟫_ℝ = (c - μ) * ⟪ι k, ι x⟫_ℝ := by
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
    Pi.smul_apply, inner_sub_right, real_inner_smul_right]
  rw [real_inner_comm (B x) (ι k), hsymm, apply_eq_smul_of_mem_ker hk, real_inner_smul_right,
    real_inner_comm (ι k) (ι x)]
  ring

private theorem mem_eigenCompl_iff {x : D} :
    x ∈ eigenCompl ι B μ ↔ ∀ k ∈ (μ • ι - B).ker, ⟪ι k, ι x⟫_ℝ = 0 := by
  simp only [Submodule.mem_comap, Submodule.mem_orthogonal, Submodule.mem_map,
    forall_exists_index, and_imp]
  exact ⟨fun h k hk ↦ h _ k hk rfl, fun h _ k hk hku ↦ hku ▸ h k hk⟩

/-- Every shift maps the complement into the orthogonal complement of the eigenspace. -/
private theorem smul_sub_apply_mem_orthogonal (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (c : ℝ) {x : D} (hx : x ∈ eigenCompl ι B μ) : (c • ι - B) x ∈ (eigenImage ι B μ)ᗮ := by
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨k, hk, rfl⟩
  rw [ContinuousLinearMap.coe_coe, inner_apply_smul_sub_apply hsymm hk,
    mem_eigenCompl_iff.1 hx k hk, mul_zero]

/-- The inverse of an invertible shift maps the orthogonal complement of the eigenspace into the
complement. -/
private theorem inverse_apply_mem_eigenCompl (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (h₀ : (c • ι - B).IsInvertible) {y : H} (hy : y ∈ (eigenImage ι B μ)ᗮ) :
    (c • ι - B).inverse y ∈ eigenCompl ι B μ := by
  refine mem_eigenCompl_iff.2 fun k hk ↦ ?_
  rcases eq_or_ne c μ with rfl | hcμ
  · have hk0 : (c • ι - B) k = (c • ι - B) 0 := by rw [map_zero]; exact LinearMap.mem_ker.1 hk
    rw [h₀.injective hk0, map_zero, inner_zero_left]
  · have h := inner_apply_smul_sub_apply (c := c) hsymm hk ((c • ι - B).inverse y)
    have hmem : ι k ∈ eigenImage ι B μ := Submodule.mem_map_of_mem hk
    rw [h₀.self_apply_inverse, Submodule.inner_right_of_mem_orthogonal hmem hy] at h
    exact (mul_eq_zero.1 h.symm).resolve_left (sub_ne_zero.2 hcμ)

/-! ### The operators on the complement -/

/-- An operator `D → H` mapping the complement into the orthogonal complement of the eigenspace,
as an operator between them. -/
private abbrev compl (T : D →L[ℝ] H) (hT : ∀ x ∈ eigenCompl ι B μ, T x ∈ (eigenImage ι B μ)ᗮ) :
    eigenCompl ι B μ →L[ℝ] (eigenImage ι B μ)ᗮ :=
  (T ∘L (eigenCompl ι B μ).subtypeL).codRestrict _ fun x ↦ hT x x.property

/-- `ι` on the complement. -/
private abbrev complι (ι B : D →L[ℝ] H) (μ : ℝ) :
    eigenCompl ι B μ →L[ℝ] (eigenImage ι B μ)ᗮ :=
  compl (B := B) (μ := μ) ι fun _ hx ↦ hx

/-- `B` on the complement. -/
private abbrev complB (ι B : D →L[ℝ] H) (μ : ℝ) (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) :
    eigenCompl ι B μ →L[ℝ] (eigenImage ι B μ)ᗮ :=
  compl B fun _ hx ↦ by simpa using smul_sub_apply_mem_orthogonal hsymm 0 hx

private theorem coe_smul_complι_sub_complB_apply (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (c : ℝ) (x : eigenCompl ι B μ) :
    ((c • complι ι B μ - complB ι B μ hsymm) x : H) = (c • ι - B) x :=
  rfl

private theorem coe_complι_apply (x : eigenCompl ι B μ) : (complι ι B μ x : H) = ι x :=
  rfl

private theorem coe_complB_sub_smul_complι_apply (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (c : ℝ) (x : eigenCompl ι B μ) :
    ((complB ι B μ hsymm - c • complι ι B μ) x : H) = (B - c • ι) x :=
  rfl

private theorem isCompactOperator_complι (hι : IsCompactOperator ι) :
    IsCompactOperator (complι ι B μ) :=
  (hι.comp_clm _).codRestrict _ (Submodule.isClosed_orthogonal _)

variable [CompleteSpace D] [CompleteSpace H]

private instance : CompleteSpace (eigenCompl ι B μ) :=
  ((Submodule.isClosed_orthogonal _).preimage ι.continuous).completeSpace_coe

omit [CompleteSpace D] [CompleteSpace H] in
/-- The shifts `B - c ι` on the complement are symmetric through `ι`. -/
private theorem inner_complB_sub_smul_complι_apply (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (c : ℝ) (x y : eigenCompl ι B μ) :
    ⟪(complB ι B μ hsymm - c • complι ι B μ) x, complι ι B μ y⟫_ℝ =
      ⟪complι ι B μ x, (complB ι B μ hsymm - c • complι ι B μ) y⟫_ℝ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_complB_sub_smul_complι_apply,
    coe_complB_sub_smul_complι_apply]
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right, coe_complι_apply, hsymm]

/-- A shift invertible on `D` stays invertible on the complement. -/
private theorem isInvertible_smul_complι_sub_complB
    (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (h₀ : (c • ι - B).IsInvertible) :
    (c • complι ι B μ - complB ι B μ hsymm).IsInvertible := by
  refine ContinuousLinearMap.isInvertible_iff_bijective.2 ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have := congrArg Subtype.val hxy
    rw [coe_smul_complι_sub_complB_apply, coe_smul_complι_sub_complB_apply] at this
    exact Subtype.ext (h₀.injective this)
  · refine ⟨⟨_, inverse_apply_mem_eigenCompl hsymm h₀ y.property⟩, Subtype.ext ?_⟩
    rw [coe_smul_complι_sub_complB_apply, h₀.self_apply_inverse]

omit [CompleteSpace D] [CompleteSpace H] in
/-- The shift at the eigenvalue is injective on the complement. -/
private theorem injective_smul_complι_sub_complB (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (h₀ : (c • ι - B).IsInvertible) :
    Function.Injective (μ • complι ι B μ - complB ι B μ hsymm) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
  have hker : (x : D) ∈ (μ • ι - B).ker := by
    have := congrArg Subtype.val hx
    rw [coe_smul_complι_sub_complB_apply] at this
    exact LinearMap.mem_ker.2 this
  refine eq_zero_of_mem_ker_of_apply_eq_zero h₀ hker ?_
  exact inner_self_eq_zero.1 (mem_eigenCompl_iff.1 x.property _ hker)

/-! ### The eigenspace block -/

omit [CompleteSpace D] [CompleteSpace H] in
/-- The scalar block `(μ - c) • 1` on the eigenspace is invertible when the shift `c ι - B` is:
either `c ≠ μ`, or the eigenspace is trivial. -/
private theorem isInvertible_smul_one [FiniteDimensional ℝ (eigenImage ι B μ)]
    (h₀ : (c • ι - B).IsInvertible) :
    ((μ - c) • (1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ)).IsInvertible := by
  rcases eq_or_ne μ c with rfl | hμc
  · -- The eigenspace is trivial.
    have hF : ∀ v : eigenImage ι B μ, v = 0 := by
      rintro ⟨_, k, hk, rfl⟩
      simp [h₀.injective (by simpa using hk : (μ • ι - B) k = (μ • ι - B) 0)]
    exact ContinuousLinearMap.isInvertible_iff_bijective.2
      ⟨fun v w _ ↦ (hF v).trans (hF w).symm, fun w ↦ ⟨0, (by simp [hF w])⟩⟩
  · exact (ContinuousLinearMap.isInvertible_smul_iff (sub_ne_zero.2 hμc)).2
      ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩

/-! ### The change of trivialization -/

omit [CompleteSpace D] [CompleteSpace H] in
/-- A continuous right inverse of `ι` from the image of the eigenspace into the eigenspace. -/
private theorem exists_rightInverse [FiniteDimensional ℝ (eigenImage ι B μ)]
    (h₀ : (c • ι - B).IsInvertible) :
    ∃ J : eigenImage ι B μ →L[ℝ] D, ∀ v, J v ∈ (μ • ι - B).ker ∧ ι (J v) = v := by
  set E := (μ • ι - B).ker
  have hinj : Function.Injective ((ι : D →ₗ[ℝ] H).submoduleMap E) := by
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ Subtype.ext ?_
    exact eq_zero_of_mem_ker_of_apply_eq_zero h₀ x.property (congrArg Subtype.val hx)
  let e := LinearEquiv.ofBijective _ ⟨hinj, LinearMap.submoduleMap_surjective _ E⟩
  refine ⟨E.subtypeL ∘L LinearMap.toContinuousLinearMap (e.symm : eigenImage ι B μ →ₗ[ℝ] E),
    fun v ↦ ⟨(e.symm v).property, ?_⟩⟩
  exact congrArg Subtype.val (e.apply_symm_apply v)

omit [CompleteSpace H] in
/-- The map `(v, x') ↦ ι⁻¹ v + x'` from `F × D'` to `D`, for the image `F` of the eigenspace and
its complement `D'`, is an isomorphism. -/
private theorem exists_equiv [FiniteDimensional ℝ (eigenImage ι B μ)]
    (h₀ : (c • ι - B).IsInvertible) :
    ∃ (J : eigenImage ι B μ →L[ℝ] D) (W : WithLp 2 (eigenImage ι B μ × eigenCompl ι B μ) ≃L[ℝ] D),
      (∀ v, J v ∈ (μ • ι - B).ker ∧ ι (J v) = v) ∧ ∀ z, W z = J z.fst + z.snd := by
  set F := eigenImage ι B μ
  obtain ⟨J, hJ⟩ := exists_rightInverse (μ := μ) h₀
  set W₀ : WithLp 2 (F × eigenCompl ι B μ) →L[ℝ] D :=
    J ∘L WithLp.fstL 2 ℝ F (eigenCompl ι B μ) +
      (eigenCompl ι B μ).subtypeL ∘L WithLp.sndL 2 ℝ F (eigenCompl ι B μ)
  have hW₀ (z) : W₀ z = J z.fst + z.snd := rfl
  obtain ⟨W, hW⟩ : W₀.IsInvertible := by
    refine ContinuousLinearMap.isInvertible_iff_bijective.2
      ⟨(injective_iff_map_eq_zero _).2 fun z hz ↦ ?_, fun x ↦ ?_⟩
    · -- `ι (W₀ z) = z.fst + ι z.snd` with `z.fst ∈ F` and `ι z.snd ∈ Fᗮ`, so both vanish.
      have h : (z.fst : H) = -ι z.snd := by
        rw [eq_neg_iff_add_eq_zero, ← (hJ z.fst).2, ← map_add, ← hW₀, hz, map_zero]
      have hfst : z.fst = 0 := by
        have hmem : ι z.snd ∈ Fᗮ := z.snd.property
        have h0 : ⟪(z.fst : H), ι z.snd⟫_ℝ = 0 :=
          Submodule.inner_right_of_mem_orthogonal z.fst.property hmem
        rw [← neg_eq_iff_eq_neg.2 h, inner_neg_right, neg_eq_zero, inner_self_eq_zero] at h0
        exact_mod_cast h0
      have hsnd : z.snd = 0 := by
        rw [hW₀, hfst, map_zero, zero_add] at hz
        exact Subtype.ext hz
      exact WithLp.ofLp_injective 2 (Prod.ext hfst hsnd)
    · set v : F := F.orthogonalProjectionOnto (ι x)
      have hx' : x - J v ∈ eigenCompl ι B μ := by
        rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, map_sub, (hJ v).2]
        exact F.sub_starProjection_mem_orthogonal (ι x)
      exact ⟨WithLp.toLp 2 (v, ⟨_, hx'⟩), by simp [hW₀]⟩
  exact ⟨J, W, hJ, fun z ↦ by rw [← hW₀, ← hW, ContinuousLinearEquiv.coe_coe]⟩

omit [CompleteSpace H] in
/-- The orthogonal decomposition `U : H ≃ F × Fᗮ` along the image `F` of the eigenspace and an
isomorphism `V : D ≃ F × D'` intertwine `ι` with `1 ⊕ ι|_{D'}` and every shift `B - a ι` with
`(μ - a) ⊕ (B - a ι)|_{D'}`. -/
private theorem exists_conj [FiniteDimensional ℝ (eigenImage ι B μ)]
    (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (h₀ : (c • ι - B).IsInvertible) :
    ∃ V : D ≃L[ℝ] WithLp 2 (eigenImage ι B μ × eigenCompl ι B μ),
      ((1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ).withLpProdMap 2 (complι ι B μ)) ∘L
          (V : D →L[ℝ] _) =
        ((eigenImage ι B μ).orthogonalDecomposition : H →L[ℝ] _) ∘L ι ∧
      ∀ a : ℝ, ((eigenImage ι B μ).orthogonalDecomposition : H →L[ℝ] _) ∘L (B - a • ι) ∘L
          (V.symm : _ →L[ℝ] D) =
        ((μ - a) • (1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ)).withLpProdMap 2
          (complB ι B μ hsymm - a • complι ι B μ) := by
  set F := eigenImage ι B μ
  set U := F.orthogonalDecomposition
  obtain ⟨J, W, hJ, hW⟩ := exists_equiv (μ := μ) h₀
  -- `U (v + w) = (v, w)` for `v ∈ F` and `w ∈ Fᗮ`.
  have hU (v : F) (w : Fᗮ) : U (v + w) = WithLp.toLp 2 (v, w) := by
    rw [← U.apply_symm_apply (WithLp.toLp 2 (v, w))]
    simp [U]
  refine ⟨W.symm, ?_, fun a ↦ ?_⟩
  · -- `1 ⊕ ι|_{D'} = U ∘ ι ∘ W`, then compose with `W⁻¹`.
    have h : (1 : F →L[ℝ] F).withLpProdMap 2 (complι ι B μ) =
        (U : H →L[ℝ] _) ∘L ι ∘L (W : _ →L[ℝ] D) := by
      ext1 z
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv]
      rw [hW, map_add, (hJ z.fst).2, ContinuousLinearMap.withLpProdMap_apply]
      -- `ι z.snd` is the coercion of the element `⟨ι z.snd, _⟩` of `Fᗮ`.
      exact (hU z.fst ⟨ι z.snd, z.snd.property⟩).symm
    rw [h]
    ext1 x
    simp
  · ext1 z
    have hB : (B - a • ι) (W z) = (((μ - a) • z.fst : F) : H) +
        (((complB ι B μ hsymm - a • complι ι B μ) z.snd : Fᗮ) : H) := by
      rw [hW, map_add]
      congr 1
      rw [FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply,
        apply_eq_smul_of_mem_ker (hJ z.fst).1, (hJ z.fst).2, Submodule.coe_smul, sub_smul]
    simp only [ContinuousLinearEquiv.symm_symm, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [hB, hU, ContinuousLinearMap.withLpProdMap_apply]
    simp

/-- Every shift `B - f(s) ι` is invertible on the complement, when the shifts on `D` are invertible
away from the eigenvalue `μ`. -/
private theorem isInvertible_complB_sub_smul_complι (hι : IsCompactOperator ι)
    (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) (h₀ : (c • ι - B).IsInvertible) {a : ℝ}
    (ha : a ≠ μ → (B - a • ι).IsInvertible) :
    (complB ι B μ hsymm - a • complι ι B μ).IsInvertible := by
  rw [ContinuousLinearMap.isInvertible_sub_comm]
  rcases eq_or_ne a μ with haμ | haμ
  · rw [haμ]
    exact (ContinuousLinearMap.isInvertible_smul_sub_iff_injective (𝕜 := ℝ)
      (ι := complι ι B μ) (A := complB ι B μ hsymm) (c₀ := c) (c := μ)
      (isCompactOperator_complι hι) (isInvertible_smul_complι_sub_complB hsymm h₀)).2
      (injective_smul_complι_sub_complB hsymm h₀)
  · exact isInvertible_smul_complι_sub_complB hsymm
      (ContinuousLinearMap.isInvertible_sub_comm.1 (ha haμ))

omit [CompleteSpace D] [CompleteSpace H] in
/-- A path `s ↦ P - f(s) Q` with `f` continuous and bounded has an `L∞` class. -/
private theorem memLp_sub_smul {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (P Q : X)
    {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) :
    MemLp (fun s ↦ P - f s • Q) ∞ μ₀ :=
  memLp_top_of_bound (continuous_const.sub (hf.smul continuous_const)).aestronglyMeasurable
    (‖P‖ + M * ‖Q‖) (.of_forall fun s ↦ (norm_sub_le _ _).trans (by
      rw [norm_smul]
      gcongr
      exact hM s))

omit [CompleteSpace D] [CompleteSpace H] in
/-- On bounded windows the path of shifts on the complement differs from its limit by multiples
of `ι`. -/
private theorem exists_norm_sub_apply_le (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    {f : ℝ → ℝ} {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M) (ctop T : ℝ) :
    ∃ C, ∀ᵐ s ∂volume, s ∈ Ioo (-T) T → ∀ x,
      ‖((complB ι B μ hsymm - f s • complι ι B μ) -
          (complB ι B μ hsymm - ctop • complι ι B μ)) x‖ ≤ C * ‖complι ι B μ x‖ := by
  refine ⟨‖ctop‖ + M, .of_forall fun s _ x ↦ ?_⟩
  simp only [sub_sub_sub_cancel_left, FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply,
    Pi.smul_apply]
  rw [← sub_smul, norm_smul]
  gcongr
  exact (norm_sub_le _ _).trans (by gcongr; exact hM s)

omit [CompleteSpace D] [CompleteSpace H] in
/-- The path of shifts, conjugated by the change of trivialization, has an `L∞` class: the
conjugated path `s ↦ Ψ B - f(s) Ψ ι` is affine in the bounded function `f`. -/
private theorem exists_lp_conj [FiniteDimensional ℝ (eigenImage ι B μ)]
    (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {f : ℝ → ℝ} {M : ℝ} (hM : ∀ s, ‖f s‖ ≤ M)
    (hf : Continuous f) (V : D ≃L[ℝ] WithLp 2 (eigenImage ι B μ × eigenCompl ι B μ))
    (hA' : ∀ a : ℝ, ((eigenImage ι B μ).orthogonalDecomposition : H →L[ℝ] _) ∘L (B - a • ι) ∘L
          (V.symm : _ →L[ℝ] D) =
        ((μ - a) • (1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ)).withLpProdMap 2
          (complB ι B μ hsymm - a • complι ι B μ))
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (hAL : AL =ᵐ[μ₀] fun s ↦ B - f s • ι) :
    ∃ AL' : Lp (WithLp 2 (eigenImage ι B μ × eigenCompl ι B μ) →L[ℝ]
        WithLp 2 (eigenImage ι B μ × (eigenImage ι B μ)ᗮ)) ∞ μ₀,
      (∀ᵐ s ∂μ₀, AL' s =
        ((eigenImage ι B μ).orthogonalDecomposition.toContinuousLinearEquiv : H →L[ℝ] _).comp
          ((AL s).comp (V.symm : _ →L[ℝ] D))) ∧
      AL' =ᵐ[μ₀] fun s ↦
        ((μ - f s) • (1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ)).withLpProdMap 2
          (complB ι B μ hsymm - f s • complι ι B μ) := by
  set U := ((eigenImage ι B μ).orthogonalDecomposition :
    H →L[ℝ] WithLp 2 (eigenImage ι B μ × (eigenImage ι B μ)ᗮ))
  set W := (V.symm : WithLp 2 (eigenImage ι B μ × eigenCompl ι B μ) →L[ℝ] D)
  have hΨ (a : ℝ) : U ∘L (B - a • ι) ∘L W = U ∘L B ∘L W - a • U ∘L ι ∘L W := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul]
  have hm := memLp_sub_smul (U ∘L B ∘L W) (U ∘L ι ∘L W) hf hM
  refine ⟨hm.toLp _, ?_, ?_⟩
  · filter_upwards [hm.coeFn_toLp, hAL] with s hs hs'
    rw [hs, ← hΨ, hs']
  · filter_upwards [hm.coeFn_toLp] with s hs
    rw [hs, ← hΨ]
    exact hA' (f s)

/-! ### The index along a path of shifts -/

/-- **The index is the spectral flow along a path of shifts crossing one eigenvalue.** Let
`ι : D → H` be a compact operator from a Banach space into a Hilbert space, and `B : D → H` an
operator symmetric through `ι`. Let `f : ℝ → ℝ` be continuous with limits `c₋` at `-∞` and `c₊`
at `∞` at which the shifts `B - c± ι` are invertible, and suppose that every shift `B - f(s) ι` is
invertible except where `f(s)` is a given `μ`. Then for every `a` far enough to the left and every
`b` far enough to the right, the index of `u ↦ (ι ∘ u)' + (B - f(s) ι) u` from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` to `L²(ℝ, H)` is the spectral flow of the path `s ↦ B - f(s) ι` from
`a` to `b`. -/
theorem eventually_index_familyDomainTrajectoryOperator_sub_smul_eq_domainSpectralFlow
    (hι : IsCompactOperator ι) (hsymm : ∀ x y, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) {cbot ctop : ℝ} (hbot : Tendsto f atBot (𝓝 cbot))
    (htop : Tendsto f atTop (𝓝 ctop)) (hcbot : (B - cbot • ι).IsInvertible)
    (hctop : (B - ctop • ι).IsInvertible) (hμ : ∀ s, f s ≠ μ → (B - f s • ι).IsInvertible)
    (AL : Lp (D →L[ℝ] H) ∞ μ₀) (hAL : AL =ᵐ[μ₀] fun s ↦ B - f s • ι) :
    ∀ᶠ ab in atBot ×ˢ atTop,
      (familyDomainTrajectoryOperator (p := 2) ι AL).index =
        domainSpectralFlow ι (fun s ↦ B - f s • ι) ab.1 ab.2 := by
  have h₀ := ContinuousLinearMap.isInvertible_sub_comm.1 hctop
  have := ContinuousLinearMap.finiteDimensional_ker_smul_sub hι h₀ μ
  obtain ⟨V, hι', hA'⟩ := exists_conj (μ := μ) hsymm h₀
  obtain ⟨M, hM⟩ := exists_forall_norm_le_of_tendsto hf hbot htop
  -- The conjugated path is affine in `f(s)`, so it has an `L∞` class.
  obtain ⟨AL', hconj, hAL'⟩ := exists_lp_conj (μ := μ) hsymm hM hf V hA' AL hAL
  -- The block theorem applies to the conjugated path.
  have hblock :=
    eventually_index_familyDomainTrajectoryOperator_withLpProdMap_eq_domainSpectralFlow
      (isCompactOperator_complι (μ := μ) hι)
      (A₁ := fun s ↦ (μ - f s) • (1 : eigenImage ι B μ →L[ℝ] eigenImage ι B μ))
      (A₂ := fun s ↦ complB ι B μ hsymm - f s • complι ι B μ)
      ((continuous_const.sub hf).smul continuous_const)
      (continuous_const.sub (hf.smul continuous_const))
      (fun s x y ↦ by simp [real_inner_smul_left, real_inner_smul_right])
      (fun s ↦ inner_complB_sub_smul_complι_apply hsymm (f s))
      (fun s ↦ isInvertible_complB_sub_smul_complι hι hsymm h₀ (hμ s))
      (isInvertible_smul_one (ContinuousLinearMap.isInvertible_sub_comm.1 hcbot))
      (isInvertible_smul_one h₀)
      (isInvertible_complB_sub_smul_complι hι hsymm h₀ fun _ ↦ hcbot)
      (isInvertible_complB_sub_smul_complι hι hsymm h₀ fun _ ↦ hctop)
      ((tendsto_const_nhds.sub hbot).smul_const _) ((tendsto_const_nhds.sub htop).smul_const _)
      (tendsto_const_nhds.sub (hbot.smul_const _)) (tendsto_const_nhds.sub (htop.smul_const _))
      (exists_norm_sub_apply_le hsymm hM ctop) AL' hAL'
  -- The change of trivialization preserves the index and the spectral flow.
  have hind := index_familyDomainTrajectoryOperator_comp_comp_symm (p := 2) V
    (eigenImage ι B μ).orthogonalDecomposition.toContinuousLinearEquiv hι' hconj
  have hsf (a b : ℝ) := domainSpectralFlow_comp_comp_symm (a := a) (b := b)
    (A := fun s ↦ B - f s • ι) (fun _ ↦ (eigenImage ι B μ).orthogonalDecomposition)
    (fun _ ↦ V) (fun _ _ ↦ hι')
  filter_upwards [hblock] with ⟨a, b⟩ h
  rw [← hind, h, ← hsf]
  congr 1
  funext s
  rw [hA' (f s)]

end TauCeti.WeakDerivStep
