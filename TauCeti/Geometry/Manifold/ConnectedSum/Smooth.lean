/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ConnectedSum.Basic

import Mathlib.Geometry.Euclidean.Inversion.Calculus
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.Instances.Quotient
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sum
import TauCeti.Geometry.Manifold.MFDeriv.Sum

/-!
# The connected sum of two manifolds

Let `M` and `N` be `C^n` manifolds modelled on `I : ModelWithCorners ℝ E H`, with `E` a real inner
product space, and let `e₁ : E → M` and `e₂ : E → N` be open embeddings which are `C^n` local
diffeomorphisms, the coordinate balls of the connected sum `TauCeti.ConnectedSum e₁ e₂`. The
punctured summands are open subsets of `M` and `N`, so their disjoint union is a `C^n` manifold, and
the quotient map onto the connected sum is a local homeomorphism
(`TauCeti.ConnectedSum.isLocalHomeomorph_mk`, in `TauCeti.Geometry.Manifold.ConnectedSum.Basic`).
Pushing the charts forward along it gives the connected sum a charted-space structure
(`TauCeti.ConnectedSum.chartedSpace`).

These charts form a `C^n` manifold (`TauCeti.ConnectedSum.isManifold`): two points of the punctured
summands with the same image are glued by the inversion `v ↦ v / ‖v‖²` of `E`, read through the
balls, and near such a point this transition `e₂ ∘ inversion 0 1 ∘ e₁⁻¹` is a composite of `C^n`
maps, since the inversion is smooth away from the centre. This is the local deck-transformation
criterion `IsLocalHomeomorph.isManifold_chartedSpaceOfRightInverse`. The quotient map is then a
`C^n` local diffeomorphism (`TauCeti.ConnectedSum.isLocalDiffeomorph_mk`).

The charts are not instances, as they depend on the hypotheses on the balls; consumers use them with
`letI`, as for other spaces glued from charts.

## Main definitions

* `TauCeti.ConnectedSum.chartedSpace`: the charts of the connected sum, pushed forward from the
  punctured summands.

## Main results

* `TauCeti.ConnectedSum.isManifold`: the connected sum of two `C^n` manifolds is a `C^n` manifold.
* `TauCeti.ConnectedSum.isLocalDiffeomorph_mk`: its quotient map is a `C^n` local diffeomorphism.
* `TauCeti.ConnectedSum.isLocalDiffeomorph_inl`, `TauCeti.ConnectedSum.isLocalDiffeomorph_inr`:
  so are the inclusions of the punctured summands.
* `TauCeti.ConnectedSum.isLocalDiffeomorph_punctureBall`,
  `TauCeti.ConnectedSum.isLocalDiffeomorph_inlBall`,
  `TauCeti.ConnectedSum.isLocalDiffeomorph_inrBall`: a ball of a summand avoiding the centre of
  the ball of the connected sum which is a `C^n` local diffeomorphism stays one as a ball of the
  punctured summand and of the connected sum.
* `TauCeti.ConnectedSum.isLocalDiffeomorph_punctureMap`: the restriction of a `C^n` local
  diffeomorphism to the punctured summands is a `C^n` local diffeomorphism.
* `TauCeti.ConnectedSum.mfderiv_inl_apply`, `TauCeti.ConnectedSum.mfderiv_inr_apply`: the
  differentials of the inclusions of the punctured summands are those of the quotient map.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
-/

public section

noncomputable section

open Set Filter Function Topology TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti.ConnectedSum

/-- A ball avoiding the centre of the ball `e` which is a `C^n` local diffeomorphism is one as a
ball of the punctured summand `M ∖ {e 0}`. -/
theorem isLocalDiffeomorph_punctureBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
    {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M] {e f : E → M}
    (h : e 0 ∉ range f) (df : IsLocalDiffeomorph 𝓘(ℝ, E) I n f) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I n (punctureBall e f h) := fun w ↦
  IsLocalDiffeomorphAt.of_comp_left ((subtypeVal_comp_punctureBall h).symm ▸ df w)
    (isLocalDiffeomorph_subtype_val _)
    (continuous_induced_rng.2
      ((subtypeVal_comp_punctureBall h).symm ▸ df.contMDiff.continuous)).continuousAt

/-- The restriction of a `C^n` local diffeomorphism to the punctured summands is a `C^n` local
diffeomorphism. -/
theorem isLocalDiffeomorph_punctureMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
    {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M]
    {M' : Type*} [TopologicalSpace M'] [T1Space M'] [ChartedSpace H M']
    {e : E → M} {e' : E → M'} {φ : M → M'} (hφ : Injective φ) (h0 : φ (e 0) = e' 0)
    (dφ : IsLocalDiffeomorph I I n φ) :
    IsLocalDiffeomorph I I n (punctureMap φ hφ h0) :=
  fun x ↦ IsLocalDiffeomorphAt.of_comp_left
    (subtypeVal_comp_punctureMap hφ h0 ▸ (isLocalDiffeomorph_subtype_val x).comp (hg := dφ x))
    (isLocalDiffeomorph_subtype_val _)
    (continuous_punctureMap hφ h0 dφ.contMDiff.continuous).continuousAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace H N]
  {e₁ : E → M} {e₂ : E → N}

/-- The **charts of the connected sum**, pushed forward from the punctured summands along the
quotient map. -/
@[instance_reducible]
def chartedSpace (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂) :
    ChartedSpace H (ConnectedSum e₁ e₂) :=
  (isLocalHomeomorph_mk h₁ h₂).chartedSpace (mk_surjective e₁ e₂)

variable {n : ℕ∞}

/-- **The transition map of the connected sum.** Near a point `x = f v` of the punctured ball `f`,
with `v ≠ 0`, the points of the punctured summand are glued by a map to the other punctured summand
which is `C^n` at `x`, given near `x` by `g ∘ inversion 0 1 ∘ f⁻¹`. -/
private theorem exists_transition {X Y : Type*} [TopologicalSpace X] [T1Space X] [ChartedSpace H X]
    [TopologicalSpace Y] [T1Space Y] [ChartedSpace H Y]
    {f : E → X} {g : E → Y} (df : IsLocalDiffeomorph 𝓘(ℝ, E) I n f)
    (dg : IsLocalDiffeomorph 𝓘(ℝ, E) I n g) {v : E} (hv : v ≠ 0) {x : puncture f}
    (hx : f v = x) {y : puncture g} (hy : g (inversion 0 1 v) = y) :
    ∃ τ : puncture f → puncture g, ContMDiffAt I I n τ x ∧ τ x = y ∧
      ∀ᶠ x' : puncture f in 𝓝 x, ∃ v' ≠ 0, f v' = (x' : X) ∧ g (inversion 0 1 v') = (τ x' : Y) := by
  set L := (df v).localInverse
  set τ₀ : X → Y := g ∘ inversion 0 1 ∘ L
  have hLx : L x = v := hx ▸ (df v).localInverse_left_inv (df v).localInverse_mem_target
  have hτ₀x : τ₀ x = y := by simp only [τ₀, comp_apply, hLx, hy]
  -- `τ₀` is `C^n` at `x`: the inversion is smooth away from the centre.
  have hinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) n (inversion (0 : E) 1) (L x) :=
    (contDiffAt_const.inversion contDiffAt_const contDiffAt_id (hLx ▸ hv)).contMDiffAt
  have hL : ContMDiffAt I 𝓘(ℝ, E) n L x := hx ▸ (df v).contMDiffAt_localInverse
  have hτ₀ : ContMDiffAt I I n τ₀ x := dg.contMDiff.contMDiffAt.comp _ (hinv.comp _ hL)
  -- Near `x`, the point `L x'` is a nonzero preimage of `x'` whose image under `τ₀` is not the
  -- removed centre of `Y`.
  have hLc : ContinuousAt L x := by rw [← hx]; exact (df v).continuousAt_localInverse
  have hfL : ∀ᶠ x' in 𝓝 (x : X), f (L x') = x' := by
    rw [← hx]
    exact eventually_of_mem ((df v).localInverse.open_source.mem_nhds
      (df v).localInverse_mem_source) fun x' hx' ↦ (df v).localInverse_right_inv hx'
  have hev : ∀ᶠ x' in 𝓝 (x : X), L x' ≠ 0 ∧ f (L x') = x' ∧ τ₀ x' ≠ g 0 :=
    (hLc.eventually_ne (by rwa [hLx])).and (hfL.and
      (hτ₀.continuousAt.eventually_ne (by rw [hτ₀x]; exact mem_puncture.1 y.2)))
  have hev' := continuous_subtype_val.continuousAt.eventually hev
  classical
  let τ : puncture f → puncture g := fun x' ↦
    if h : τ₀ x' = g 0 then y else ⟨τ₀ x', mem_puncture.2 h⟩
  have hτ : ∀ᶠ x' in 𝓝 x, ((τ x' : puncture g) : Y) = τ₀ x' :=
    hev'.mono fun x' h ↦ by simp [τ, h.2.2]
  refine ⟨τ, ?_, Subtype.ext ?_, hev'.and hτ |>.mono fun x' h ↦ ⟨L x', h.1.1, h.1.2.1, h.2.symm⟩⟩
  · -- A map into the open punctured summand is `C^n` when it is after the inclusion, which holds
    -- as it agrees with `τ₀` near `x`.
    have hcomp : ContMDiffAt I I n (Subtype.val ∘ τ) x :=
      (hτ₀.comp x contMDiff_subtype_val.contMDiffAt).congr_of_eventuallyEq hτ
    exact (TauCeti.ContMDiffAt.subtypeVal_comp_iff (puncture g) τ x).mp hcomp
  · rw [hτ.self_of_nhds, hτ₀x]

/-- The local deck transformations of the quotient map of the connected sum are `C^n`: two points
with the same image are exchanged near the first by a `C^n` map commuting with the quotient
map. -/
private theorem exists_contMDiffAt_deck (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂)
    (z w : puncture e₁ ⊕ puncture e₂) (hzw : mk e₁ e₂ z = mk e₁ e₂ w) :
    ∃ φ : puncture e₁ ⊕ puncture e₂ → puncture e₁ ⊕ puncture e₂,
      ContMDiffAt I I n φ z ∧ φ z = w ∧ mk e₁ e₂ ∘ φ =ᶠ[𝓝 z] mk e₁ e₂ := by
  obtain rfl | h | h := (mk_eq_mk_iff h₁.injective h₂.injective).1 hzw
  · exact ⟨id, contMDiffAt_id, rfl, .rfl⟩
  · -- `z = e₁ v` is glued to `w = e₂ (inversion 0 1 v)`.
    rcases z with x | x <;> rcases w with y | y <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at h
    obtain ⟨v, hv, hx, hy⟩ := h
    obtain ⟨τ, hτ, hτx, hev⟩ := exists_transition d₁ d₂ hv hx hy
    refine ⟨Sum.inr ∘ τ ∘ Sum.elim id fun _ ↦ x, ContMDiff.inr.contMDiffAt.comp _
      (hτ.comp _ (contMDiff_id.sumElim contMDiff_const).contMDiffAt), by simp [hτx], ?_⟩
    rw [← IsOpenEmbedding.inl.map_nhds_eq, EventuallyEq, eventually_map]
    filter_upwards [hev] with x' ⟨v', hv', hx', hy'⟩
    simp only [comp_apply, Sum.elim_inl, id_eq, mk_inl, mk_inr]
    exact ((inl_eq_inr_iff h₁.injective h₂.injective).2 ⟨v', hv', hx', hy'⟩).symm
  · -- `z = e₂ w'` is glued to `w = e₁ (inversion 0 1 w')`, as the inversion is an involution.
    rcases z with x | x <;> rcases w with y | y <;>
      simp only [rel_inl_inr, not_rel_inl_inl, not_rel_inr_inl, not_rel_inr_inr] at h
    obtain ⟨v, hv, hy, hx⟩ := h
    have hv' : inversion (0 : E) 1 v ≠ 0 := by
      simpa [inversion_eq_center one_ne_zero] using hv
    obtain ⟨τ, hτ, hτx, hev⟩ := exists_transition d₂ d₁ hv' hx
      (by rw [inversion_inversion (0 : E) one_ne_zero, hy])
    refine ⟨Sum.inl ∘ τ ∘ Sum.elim (fun _ ↦ x) id, ContMDiff.inl.contMDiffAt.comp _
      (hτ.comp _ (contMDiff_const.sumElim contMDiff_id).contMDiffAt), by simp [hτx], ?_⟩
    rw [← IsOpenEmbedding.inr.map_nhds_eq, EventuallyEq, eventually_map]
    filter_upwards [hev] with x' ⟨v', hv', hx', hy'⟩
    simp only [comp_apply, Sum.elim_inr, id_eq, mk_inl, mk_inr]
    refine (inl_eq_inr_iff h₁.injective h₂.injective).2 ⟨inversion 0 1 v',
      by simpa [inversion_eq_center one_ne_zero] using hv', hy', ?_⟩
    rw [inversion_inversion (0 : E) one_ne_zero, hx']

variable [IsManifold I n M] [IsManifold I n N]

/-- **The connected sum of two `C^n` manifolds is a `C^n` manifold**, for coordinate balls which
are open embeddings and `C^n` local diffeomorphisms. -/
theorem isManifold (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    IsManifold I n (ConnectedSum e₁ e₂) :=
  (isLocalHomeomorph_mk h₁ h₂).isManifold_chartedSpaceOfRightInverse
    (mk_surjective e₁ e₂).hasRightInverse.choose_spec
    (exists_contMDiffAt_deck h₁ h₂ d₁ d₂)

/-- The quotient map from the disjoint union of the punctured summands onto the connected sum is a
`C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_mk (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph I I n (mk e₁ e₂) :=
  (isLocalHomeomorph_mk h₁ h₂).isLocalDiffeomorph_chartedSpaceOfRightInverse
    (mk_surjective e₁ e₂).hasRightInverse.choose_spec
    (exists_contMDiffAt_deck h₁ h₂ d₁ d₂)

/-- The first punctured summand is a `C^n` local diffeomorphism into the connected sum. -/
theorem isLocalDiffeomorph_inl (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph I I n (inl e₁ e₂) := by
  let := chartedSpace (H := H) h₁ h₂
  rw [← mk_comp_inl]
  exact fun x ↦ (isLocalDiffeomorph_sumInl x).comp (hg := isLocalDiffeomorph_mk h₁ h₂ d₁ d₂ _)

/-- The second punctured summand is a `C^n` local diffeomorphism into the connected sum. -/
theorem isLocalDiffeomorph_inr (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph I I n (inr e₁ e₂) := by
  let := chartedSpace (H := H) h₁ h₂
  rw [← mk_comp_inr]
  exact fun y ↦ (isLocalDiffeomorph_sumInr y).comp (hg := isLocalDiffeomorph_mk h₁ h₂ d₁ d₂ _)

section Ball

variable {f : E → M} {g : E → N} (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂)

include d₁ d₂ in
/-- A ball of the first summand which is a `C^n` local diffeomorphism is one as a ball of the
connected sum. -/
theorem isLocalDiffeomorph_inlBall (h : e₁ 0 ∉ range f)
    (df : IsLocalDiffeomorph 𝓘(ℝ, E) I n f) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph 𝓘(ℝ, E) I n (inlBall e₁ e₂ f h) := fun w ↦
  letI := chartedSpace (H := H) h₁ h₂
  inl_comp_punctureBall e₁ e₂ h ▸ (isLocalDiffeomorph_punctureBall h df w).comp
    (hg := isLocalDiffeomorph_inl h₁ h₂ d₁ d₂ _)

include d₁ d₂ in
/-- A ball of the second summand which is a `C^n` local diffeomorphism is one as a ball of the
connected sum. -/
theorem isLocalDiffeomorph_inrBall (h : e₂ 0 ∉ range g)
    (dg : IsLocalDiffeomorph 𝓘(ℝ, E) I n g) :
    letI := chartedSpace (H := H) h₁ h₂
    IsLocalDiffeomorph 𝓘(ℝ, E) I n (inrBall e₁ e₂ g h) := fun w ↦
  letI := chartedSpace (H := H) h₁ h₂
  inr_comp_punctureBall e₁ e₂ h ▸ (isLocalDiffeomorph_punctureBall h dg w).comp
    (hg := isLocalDiffeomorph_inr h₁ h₂ d₁ d₂ _)

end Ball

/-- The differential of the inclusion of the first punctured summand into the connected sum is that
of the quotient map at the corresponding point of the disjoint union. -/
theorem mfderiv_inl_apply (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) (hn : n ≠ 0)
    (x : puncture e₁) (u : TangentSpace I x) :
    letI := chartedSpace (H := H) h₁ h₂
    mfderiv I I (inl e₁ e₂) x u = mfderiv I I (mk e₁ e₂) (Sum.inl x) u := by
  let := chartedSpace (H := H) h₁ h₂
  rw [← mk_comp_inl]
  exact TauCeti.mfderiv_comp_sumInl_apply
    ((isLocalDiffeomorph_mk h₁ h₂ d₁ d₂ (Sum.inl x)).mdifferentiableAt (by exact_mod_cast hn)) u

/-- The differential of the inclusion of the second punctured summand into the connected sum is
that of the quotient map at the corresponding point of the disjoint union. -/
theorem mfderiv_inr_apply (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂) (hn : n ≠ 0)
    (y : puncture e₂) (u : TangentSpace I y) :
    letI := chartedSpace (H := H) h₁ h₂
    mfderiv I I (inr e₁ e₂) y u = mfderiv I I (mk e₁ e₂) (Sum.inr y) u := by
  let := chartedSpace (H := H) h₁ h₂
  rw [← mk_comp_inr]
  exact TauCeti.mfderiv_comp_sumInr_apply
    ((isLocalDiffeomorph_mk h₁ h₂ d₁ d₂ (Sum.inr y)).mdifferentiableAt (by exact_mod_cast hn)) u

end TauCeti.ConnectedSum
