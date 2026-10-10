/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Projection geometry for finite orthonormal families

Reusable projection and Parseval identities for spans of finite orthonormal
subfamilies.  These results are independent of Davis--Kahan perturbation theory.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Pythagoras across an orthogonal projection**:
`‖P_K x‖² + ‖x − P_K x‖² = ‖x‖²`.

`x` splits into its projection and the complementary component, which are orthogonal, so the
norms add in square. Stated for any submodule carrying an orthogonal projection. -/
theorem norm_sq_starProjection_add_norm_sq_sub (K : Submodule 𝕜 F)
    [K.HasOrthogonalProjection] (x : F) :
    ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
  have horth : ⟪K.starProjection x, x - K.starProjection x⟫_𝕜 = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem x)
      (K.sub_starProjection_mem_orthogonal x)
  have hx : K.starProjection x + (x - K.starProjection x) = x := by abel
  calc ‖K.starProjection x‖ ^ 2 + ‖x - K.starProjection x‖ ^ 2
      = ‖K.starProjection x + (x - K.starProjection x)‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := 𝕜), horth, map_zero]; ring
    _ = ‖x‖ ^ 2 := by rw [hx]

/-! The three bridge lemmas hold for an orthonormal family in *any* inner product
space: the span of a finite subfamily is finite-dimensional, so it always carries
an orthogonal projection (the `HasOrthogonalProjection` instance is automatic when
the ambient space is finite-dimensional, as in the spectral-subspace application
below, and is requested explicitly otherwise).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.ProjectionGeometry`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `f44d966`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5, Claude Opus 4.8; Copyright (c) 2026
  Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

/--
**Projection onto the span of an orthonormal subfamily.** For an orthonormal
family `w` and a finite index set `s`, the orthogonal projection onto
`span 𝕜 (w '' s)` acts as `x ↦ ∑ i ∈ s, ⟪w i, x⟫ • w i`.
-/
@[simp]
theorem Orthonormal.starProjection_span_image_apply {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection x = ∑ i ∈ s, ⟪w i, x⟫_𝕜 • w i := by
  classical
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.sum_smul_mem _ _ fun i hi =>
      Submodule.subset_span (Set.mem_image_of_mem w (by exact_mod_cast hi))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      have hj' : j ∈ s := by exact_mod_cast hj
      rw [inner_sub_left, sum_inner, Finset.sum_congr rfl (fun i _ => by
        rw [inner_smul_left, orthonormal_iff_ite.mp hw i j, mul_ite, mul_one, mul_zero])]
      rw [Finset.sum_ite_eq' s j fun i => (starRingEnd 𝕜) ⟪w i, x⟫_𝕜, ite_eq_left hj',
        inner_conj_symm, sub_self]
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

/--
On a member `w k` of the orthonormal family, the projection onto
`span 𝕜 (w '' s)` keeps it iff `k ∈ s`.
-/
theorem Orthonormal.starProjection_span_image_apply_self {ι : Type*} [DecidableEq ι]
    {w : ι → F} (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (k : ι) :
    (Submodule.span 𝕜 (w '' ↑s)).starProjection (w k) = if k ∈ s then w k else 0 := by
  rw [Orthonormal.starProjection_span_image_apply hw s (w k),
    Finset.sum_congr rfl (fun i _ => by
      rw [orthonormal_iff_ite.mp hw i k, ite_smul, one_smul, zero_smul]),
    Finset.sum_ite_eq' s k fun i => w i]

/--
Parseval for the projection onto the span of an orthonormal subfamily:
`‖P x‖² = ∑ i ∈ s, ‖⟪w i, x⟫‖²`.
-/
theorem Orthonormal.norm_sq_starProjection_span_image {ι : Type*} {w : ι → F}
    (hw : Orthonormal 𝕜 w) (s : Finset ι)
    [(Submodule.span 𝕜 (w '' ↑s)).HasOrthogonalProjection] (x : F) :
    ‖(Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ ^ 2 = ∑ i ∈ s, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  have hcast : ((‖(Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ : ℝ) : 𝕜) ^ 2
      = ((∑ i ∈ s, ‖⟪w i, x⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜),
      Orthonormal.starProjection_span_image_apply hw s x, _root_.Orthonormal.inner_sum hw]
    rw [Finset.sum_congr rfl fun i _ => RCLike.conj_mul ⟪w i, x⟫_𝕜]
    push_cast
    rfl
  exact_mod_cast hcast

variable [FiniteDimensional 𝕜 F] {m : ℕ}

/-- **Complementary Parseval for a projection residual.** For a subfamily of an orthonormal
*basis* `w`, the residual of the projection onto its span carries the complementary Parseval
sum: `‖x − P x‖² = ∑_{i ∉ s} ‖⟪w i, x⟫‖²`.  Companion to
`Orthonormal.norm_sq_starProjection_span_image` (`‖P x‖² = ∑_{i ∈ s}`); together they split
Parseval `‖x‖² = ∑_i ‖⟪w i, x⟫‖²` across `s` and its complement. -/
theorem OrthonormalBasis.norm_sq_sub_starProjection_span_image
    (w : OrthonormalBasis (Fin m) 𝕜 F) (s : Finset (Fin m)) (x : F) :
    ‖x - (Submodule.span 𝕜 (w '' ↑s)).starProjection x‖ ^ 2
      = ∑ i ∈ sᶜ, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  -- `x − P x = Pᗮ x`, and `‖x‖² = ‖P x‖² + ‖Pᗮ x‖²`; subtract off `‖P x‖² = ∑_s` from
  -- Parseval `‖x‖² = ∑_i` to leave the complement sum.
  have hres : x - (Submodule.span 𝕜 (w '' ↑s)).starProjection x
      = (Submodule.span 𝕜 (w '' ↑s))ᗮ.starProjection x :=
    (Submodule.starProjection_orthogonal_val x).symm
  have hdecomp := Submodule.norm_sq_eq_add_norm_sq_starProjection x (Submodule.span 𝕜 (w '' ↑s))
  rw [Orthonormal.norm_sq_starProjection_span_image w.orthonormal s x] at hdecomp
  rw [hres]
  linarith [w.sum_sq_norm_inner_right x,
    Finset.sum_add_sum_compl s fun i => ‖⟪w i, x⟫_𝕜‖ ^ 2, hdecomp]

omit [FiniteDimensional 𝕜 F] in
/-- Symmetric block-counting identity for two orthonormal bases `u`, `v` and an
index set `s`: the squared overlaps summed over the `(sᶜ, s)` block equal those
summed over the `(s, sᶜ)` block.  Both equal `s.card` minus the leading–leading
overlap sum, by Parseval (each row of overlaps sums to `1`). -/
private theorem sum_inner_sq_compl_block_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  rw [Finset.sum_comm]
  -- For a unit vector `w` and orthonormal basis `b`, the overlaps split as
  -- `∑_{sᶜ} = 1 − ∑_s` by Parseval.
  have key : ∀ (b : OrthonormalBasis (Fin m) 𝕜 F) (w : F), ‖w‖ = 1 →
      ∑ k ∈ sᶜ, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 - ∑ k ∈ s, ‖⟪w, b k⟫_𝕜‖ ^ 2 := by
    intro b w hw
    have hpar : ∑ k, ‖⟪w, b k⟫_𝕜‖ ^ 2 = 1 := by
      rw [Finset.sum_congr rfl fun k _ => by rw [norm_inner_symm],
        b.sum_sq_norm_inner_right w, hw, one_pow]
    linarith [Finset.sum_add_sum_compl s fun k => ‖⟪w, b k⟫_𝕜‖ ^ 2]
  rw [Finset.sum_congr rfl fun j (_ : j ∈ s) => key u (v j) (v.orthonormal.1 j),
    Finset.sum_congr rfl fun i (_ : i ∈ s) => key v (u i) (u.orthonormal.1 i),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by rw [norm_inner_symm])

/--
**Projector form of the Davis–Kahan identity.** For two orthonormal bases `u`,
`v` of a finite-dimensional inner product space over `𝕜 = ℝ, ℂ` and an index set
`s`, the squared Frobenius distance (computed in the basis `u`) between the
orthogonal projections onto `span (v '' s)` and `span (u '' s)` is twice the
cross overlap sum:
`∑ₖ ‖(P_v − P_u) uₖ‖² = 2 ∑_{i ∈ s} ∑_{j ∉ s} ‖⟪uᵢ, vⱼ⟫‖²`.
-/
theorem sum_norm_sub_starProjection_span_sq_eq (u v : OrthonormalBasis (Fin m) 𝕜 F)
    (s : Finset (Fin m)) :
    ∑ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := by
  -- Per-`k` reduction: the `k`-th term is a single cross-overlap row.
  have hQnorm : ∀ k, ‖(Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)‖ ^ 2
      = ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 :=
    fun k => Orthonormal.norm_sq_starProjection_span_image v.orthonormal s (u k)
  have hterm : ∀ k, ‖((Submodule.span 𝕜 (v '' ↑s)).starProjection
        - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k)‖ ^ 2
      = if k ∈ s then ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2 else ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2 := by
    intro k
    rw [show (((Submodule.span 𝕜 (v '' ↑s)).starProjection
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection) (u k))
        = (Submodule.span 𝕜 (v '' ↑s)).starProjection (u k)
          - (Submodule.span 𝕜 (u '' ↑s)).starProjection (u k) from rfl,
      Orthonormal.starProjection_span_image_apply_self u.orthonormal s k]
    split <;> rename_i hk
    · -- `k ∈ s`: `P_u` keeps `uₖ`, so the term is the residual of `uₖ` against the `v`-span,
      -- which is the complementary Parseval sum.
      rw [norm_sub_rev]
      exact OrthonormalBasis.norm_sq_sub_starProjection_span_image v s (u k)
    · -- `k ∉ s`: the `u`-projection vanishes; the term is the `v`-projection norm.
      rw [sub_zero, hQnorm k]
  -- Sum the per-`k` formula and swap the two cross blocks into each other.
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_add_sum_compl s]
  rw [Finset.sum_congr rfl fun k (hk : k ∈ s) => ite_eq_left hk,
    Finset.sum_congr rfl fun k (hk : k ∈ sᶜ) => ite_eq_right (Finset.mem_compl.mp hk)]
  -- First block is the target cross sum (after swapping the inner-product slots).
  have hswap : ∀ (i j : Fin m), ‖⟪v j, u i⟫_𝕜‖ = ‖⟪u i, v j⟫_𝕜‖ := fun i j =>
    norm_inner_symm (v j) (u i)
  have hA : ∑ k ∈ s, ∑ j ∈ sᶜ, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hswap i j]
  -- Second block equals the first by the symmetric block-counting identity.
  have hB : ∑ k ∈ sᶜ, ∑ j ∈ s, ‖⟪v j, u k⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ∑ j ∈ sᶜ, ‖⟪u i, v j⟫_𝕜‖ ^ 2 := sum_inner_sq_compl_block_eq u v s
  rw [hA, hB]
  ring

end TauCeti
