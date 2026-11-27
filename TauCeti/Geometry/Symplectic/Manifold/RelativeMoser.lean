/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
import TauCeti.Geometry.Manifold.Flow.TimeDependent.Related
import TauCeti.Geometry.Manifold.Flow.TimeDependent.RestPoint
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The relative Moser theorem

Let `σ₀`, `σ₁` be closed two-forms on a boundaryless Hausdorff second-countable manifold `M` which
agree, as bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded
submanifold `f : Q → M`, with `σ₀` nondegenerate along `f(Q)`. The **relative Moser theorem**
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`) gives a
diffeomorphism `Φ` of `M` which fixes every point of `f(Q)`, moves only the points of a compact
set, and pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. Restricted to such a neighbourhood
`U`, it is a diffeomorphism from `U` onto the open set `Φ(U)` which fixes `f(Q)` pointwise and
carries `σ₀` on `U` to `σ₁` on `Φ(U)`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`). Both diffeomorphisms fix `f(Q)` to
first order: their differential at every point of `f(Q)` is the identity of the full ambient
tangent space. This first-order statement needs the agreement of the full ambient forms along
`f(Q)`; agreement of their pullbacks to `Q` is a weaker condition.

Agreement of the pullbacks still suffices for the rest, provided the affine path
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate at every point of `f(Q)`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq`).
The resulting diffeomorphism fixes `f(Q)` pointwise and has identity differential exactly at the
points where the two forms agree on the full ambient tangent space. Along a coisotropic
submanifold, for instance, two symplectic forms with the same pullback need not agree on the
ambient tangent space, while their path can still be nondegenerate there.

The proof is Moser's argument relative to a compact set
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`).
Suppose `σ₁ - σ₀ = dβ` for a smooth one-form `β` which vanishes on a compact set `K`, and the path
`σ_s = σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate along `K`. Since nondegeneracy is an open
condition and `[0, 1] × K` is compact, the path stays nondegenerate on a neighbourhood `N` of `K`.
Reparametrize the path by the smooth step function `c = Real.smoothTransition`, which is `0` for
`t ≤ 0` and `1` for `t ≥ 1`, and cut the Moser field off by a smooth function `ρ` which equals `1`
near `K` and has compact support in `N`:

`X_t = ρ (σ_{c(t)}♭)⁻¹ (-c'(t) β)`.

This time-dependent field is smooth and compactly supported, so its flow `φ_{0,t}` is defined for
all times; it vanishes on `K`, which the flow therefore fixes. Where `ρ = 1`, Cartan's formula gives
Moser's equation `∂_t σ_{c(t)} + L_{X_t} σ_{c(t)} = c'(t) dβ - c'(t) dβ = 0`. Trajectories starting
near `K` stay in this region up to time `1`, and along them the pullbacks `φ_{0,t}^* σ_{c(t)}` are
constant (`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc`).
So `Φ = φ_{0,1}` pulls `σ₁` back to `σ₀` near `K`.

If moreover `β` has zero first jet at a point `x` of `K`, so has every `X_t`: in the chart at `x`,
`ι_{X_t} σ_{c(t)} = -ρ c'(t) β` expresses the coordinate field as the image of the coordinate
expression of `β` under the inverse flat map of the slice, which stays bounded near `x`. At a
common rest point of a field with zero first jet the linearized flow is constant
(`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`), so the differential of `Φ` at `x`
is the identity.

The construction is natural. With the cut-off `ρ` given rather than chosen
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff`), it only needs
`dβ = σ₁ - σ₀` on the support of `ρ`, and `Φ` commutes with every diffeomorphism `g` which
preserves `σ₀`, `σ₁`, `β` and `ρ`: such a `g` carries the Moser field to itself, so it commutes with
its flow (`MDifferentiable.apply_timeDependentFlowOf`). This is the input of the equivariant
relative Moser theorem, in `TauCeti.Geometry.Symplectic.Manifold.RelativeMoser.Equivariant`.

For the submanifold version, the relative Poincaré lemma
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`) writes `σ₁ - σ₀`, whose
pullback along `f` vanishes, as `dβ` on a tubular neighbourhood `W` of `f(Q)`, with `β` vanishing
along `f(Q)`. At the points where `σ₁ - σ₀` itself vanishes as a full ambient tensor, `β` has zero
first jet (`TauCeti.SmoothTwoForm.exists_relative_primitive_sub_of_mpullback_eq`, shared with the
equivariant version). Moser's argument on the open submanifold `W` gives a compactly supported
diffeomorphism of `W`, which extends by the identity to `M`.

## Main results

* `TauCeti.SmoothTwoForm.exists_isOpen_forall_nondegenerate`: a path of two-forms nondegenerate
  along a compact set stays nondegenerate on a neighbourhood of it.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff`: Moser's theorem
  with a given primitive and cut-off, commuting with the diffeomorphisms preserving these data.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`:
  Moser's theorem relative to a compact set along which a given primitive of `σ₁ - σ₀` vanishes,
  with identity differential wherever the primitive has zero first jet.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq`:
  the relative Moser theorem for closed two-forms with equal pullbacks to a compact embedded
  submanifold, joined by a path nondegenerate along it.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`: the relative
  Moser theorem for closed two-forms agreeing along a compact embedded submanifold, with identity
  differential along it.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`: the same theorem as a
  diffeomorphism between open neighbourhoods of the submanifold.

## References

* J. Moser, *On the volume elements on a manifold*, Trans. Amer. Math. Soc. 120 (1965), 286–294.
* A. Weinstein, *Symplectic manifolds and their Lagrangian submanifolds*, Advances in Mathematics
  6 (1971), 329–346.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Theorem 7.4 (the relative Moser theorem) and Proposition 6.8.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 3.2.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Moser family and the cut-off Moser field -/

/-- The smooth path `σ₀ + c(t) (σ₁ - σ₀)` of two-forms, as a form on `ℝ × M`, where `c` is the
smooth step function `Real.smoothTransition`. -/
private def moserFamily (σ₀ σ₁ : SmoothTwoForm I M) :
    SmoothForm (𝓘(ℝ, ℝ).prod I) (ℝ × M) ℝ 2 :=
  SmoothForm.lineMapFamily σ₀ σ₁ (Real.smoothTransition.contDiff (n := ⊤))

/-- The slices of the Moser family, as rough forms. -/
private theorem mpullback_prodMk_moserFamily_coe (σ₀ σ₁ : SmoothTwoForm I M) (t : ℝ) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (moserFamily σ₀ σ₁).val =
      (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val :=
  (SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (SmoothForm.mpullback_prodMk_lineMapFamily σ₀ σ₁ _ t))

/-- Where `σ₁` agrees with `σ₀`, every point of the path `σ₀ + s (σ₁ - σ₀)` has the bilinear form of
`σ₀`. -/
theorem bilinFormAt_add_smul_sub_of_eq {σ₀ σ₁ : SmoothTwoForm I M} {x : M}
    (h : σ₁.val x = σ₀.val x) (s : ℝ) :
    (σ₀ + s • (σ₁ - σ₀)).bilinFormAt x = σ₀.bilinFormAt x := by
  have h : (σ₁ - σ₀).val x = 0 := by rw [AddSubgroupClass.coe_sub, Pi.sub_apply, h, sub_self]
  ext v w
  simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply, h, smul_zero,
    add_zero]

/-- The Moser vector field of the path `σ₀ + c(t) (σ₁ - σ₀)` and the primitive `β`, cut off by
`ρ`: `X_t = ρ (σ_t♭)⁻¹ (-c'(t) β)`. -/
private def moserField (σ₀ σ₁ : SmoothTwoForm I M) (β : SmoothForm I M ℝ 1) (ρ : M → ℝ)
    (t : ℝ) (x : M) : TangentSpace I x :=
  ρ x • ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).inverse
    (-deriv Real.smoothTransition t • SmoothForm.degreeOneEquiv β x)

/-- The Moser field vanishes where the primitive does. -/
private theorem moserField_eq_zero {σ₀ σ₁ : SmoothTwoForm I M} {β : SmoothForm I M ℝ 1}
    (ρ : M → ℝ) {x : M} (hx : β.val x = 0) (t : ℝ) : moserField σ₀ σ₁ β ρ t x = 0 := by
  have h : SmoothForm.degreeOneEquiv β x = 0 := ContinuousLinearMap.ext fun v ↦ by
    rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hx, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply, zero_apply]
  simp [moserField, h]

/-- Where the slice is nondegenerate, the Moser field satisfies `ι_{X_t} σ_t = -ρ c'(t) β`. -/
private theorem interior_moserField {σ₀ σ₁ : SmoothTwoForm I M} (β : SmoothForm I M ℝ 1)
    (ρ : M → ℝ) {t : ℝ} {x : M}
    (hx : ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible) :
    RoughForm.interior (moserField σ₀ σ₁ β ρ t) (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val x =
      (ρ x * -deriv Real.smoothTransition t) • β.val x := by
  rw [interior_apply_eq_ofSubsingleton_flat, moserField, map_smul, hx.self_apply_inverse]
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv]
  simp [mul_assoc]

/-- When the slices are nondegenerate on the support of `ρ`, the Moser field satisfies
`ι_{X_t} σ_t = -ρ c'(t) β` everywhere: off the support of `ρ` both sides vanish. -/
private theorem interior_moserField_eq {σ₀ σ₁ : SmoothTwoForm I M} (β : SmoothForm I M ℝ 1)
    {ρ : M → ℝ}
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible) (t : ℝ) :
    RoughForm.interior (moserField σ₀ σ₁ β ρ t) (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val =
      fun y ↦ (ρ y * -deriv Real.smoothTransition t) • β.val y := by
  funext y
  by_cases hy : y ∈ tsupport ρ
  · exact interior_moserField β ρ (hinv t y hy)
  · have hρy : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hX : moserField σ₀ σ₁ β ρ t y = 0 := by simp only [moserField, hρy, zero_smul]
    rw [interior_apply_eq_ofSubsingleton_flat, hX, map_zero, hρy, zero_mul, zero_smul]
    ext v
    simp

/-- **The Moser field is natural.** A diffeomorphism which preserves `σ₀`, `σ₁`, the primitive
`β` and the cut-off `ρ` carries the Moser field to itself: `dg (X_t x) = X_t (g x)`. -/
private theorem mfderiv_moserField {σ₀ σ₁ : SmoothTwoForm I M} {β : SmoothForm I M ℝ 1}
    {ρ : M → ℝ}
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    (g : M ≃ₘ⟮I, I⟯ M) (hg₀ : mpullback I I g σ₀.val = σ₀.val)
    (hg₁ : mpullback I I g σ₁.val = σ₁.val) (hgβ : mpullback I I g β.val = β.val)
    (hgρ : ∀ x, ρ (g x) = ρ x) (t : ℝ) (x : M) :
    mfderiv I I g x (moserField σ₀ σ₁ β ρ t x) = moserField σ₀ σ₁ β ρ t (g x) := by
  set σ := σ₀ + Real.smoothTransition t • (σ₁ - σ₀)
  by_cases hx : ρ x = 0
  · simp [moserField, hx, hgρ]
  have hA := hinv t x (subset_tsupport _ hx)
  have hB := hinv t (g x) (subset_tsupport _ (by rwa [Function.mem_support, hgρ]))
  have hL : (mfderiv I I g x).IsInvertible := g.isInvertible_mfderiv (by simp)
  -- `g` preserves the slice `σ`, so `σ_(g x) (dg v, dg w) = σ_x (v, w)`.
  have hgσ : mpullback I I g σ.val = σ.val := by
    simp only [σ, AddSubgroupClass.coe_sub, Submodule.coe_add, Submodule.coe_smul,
      mpullback_add, mpullback_smul, mpullback_sub, hg₀, hg₁]
  have key (v w : TangentSpace I x) :
      σ.flat (g x) (mfderiv I I g x v) (mfderiv I I g x w) = σ.flat x v w := by
    rw [flat_apply, flat_apply, SmoothBundleForm.eval₂_apply, SmoothBundleForm.eval₂_apply,
      ← mpullback_apply_pair, hgσ]
  -- Both sides solve `σ♭_(g x) v = β_(g x)`, tested on the vectors `dg w`.
  have hv : mfderiv I I g x ((σ.flat x).inverse (SmoothForm.degreeOneEquiv β x)) =
      (σ.flat (g x)).inverse (SmoothForm.degreeOneEquiv β (g x)) := by
    refine (hB.inverse_apply_self _).symm.trans (congrArg _ (ContinuousLinearMap.ext fun w' ↦ ?_))
    obtain ⟨w, rfl⟩ := hL.surjective w'
    rw [key, hA.self_apply_inverse, SmoothForm.degreeOneEquiv_apply_apply_vec,
      SmoothForm.degreeOneEquiv_apply_apply_vec, ← mpullback_apply_one, hgβ]
  simp only [moserField, hgρ, map_smul]
  rw [hv]

/-- In the chart at `x`, the identity `ι_{X_t} σ_t = -ρ c'(t) β` of the Moser field gives the norm
of the flat map of the coordinate expression `σ'_t` applied to the coordinate expression `X'_t`:
`‖σ'_t♭(z) (X'_t(z))‖ = ‖ρ c'(t)‖ ‖β'(z)‖` at every point `z` of the chart target. -/
private theorem norm_flatL_inChartAt_mpullbackWithin_moserField [IsManifold I 1 M]
    {σ₀ σ₁ : SmoothTwoForm I M} (β : SmoothForm I M ℝ 1) {ρ : M → ℝ}
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    {x : M} {z : E} (hz : z ∈ (extChartAt I x).target) (t : ℝ) :
    ‖ContinuousAlternatingMap.flatL ℝ E ℝ
        (RoughForm.inChartAt (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val x z)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (moserField σ₀ σ₁ β ρ t) (range I) z : E)‖ =
      ‖ρ ((extChartAt I x).symm z) * -deriv Real.smoothTransition t‖ *
        ‖RoughForm.inChartAt β.val x z‖ := by
  have h := RoughForm.inChartAt_interior (moserField σ₀ σ₁ β ρ t)
    (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val hz
  rw [interior_moserField_eq β hinv t, RoughForm.inChartAt_fun_smul] at h
  refine (ContinuousAlternatingMap.norm_ofSubsingleton (ι := Fin 1) 0 _).symm.trans ?_
  exact (congrArg norm (ContinuousAlternatingMap.ofSubsingleton_flatL_apply _ _)).trans
    ((congrArg norm h.symm).trans (norm_smul _ _))

/-- The flat maps of the slices of the Moser family form a smooth section along the projection
`ℝ × M → M`. -/
private theorem contMDiff_flat_moserFamily (σ₀ σ₁ : SmoothTwoForm I M) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((σ₀ + Real.smoothTransition p.1 • (σ₁ - σ₀)).flat p.2)) := by
  intro p
  have hσ := SmoothForm.contMDiff_mpullback_prodMk (moserFamily σ₀ σ₁) p
  simp only [moserFamily, SmoothForm.mpullback_prodMk_lineMapFamily] at hσ
  simpa only [← flat_def] using contMDiffAt_sectionAlong_flatL (b := Prod.snd) hσ

variable [FiniteDimensional ℝ E]

/-- The Moser field `(t, x) ↦ X_t(x)` is jointly smooth when the slices are nondegenerate on the
support of `ρ`: near that support it is built from smooth sections by fibrewise inversion and
evaluation, and away from it it vanishes. -/
private theorem contMDiff_moserField {σ₀ σ₁ : SmoothTwoForm I M} (β : SmoothForm I M ℝ 1)
    {ρ : M → ℝ} (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, moserField σ₀ σ₁ β ρ p.1 p.2⟩ : TangentBundle I M)) := by
  rintro ⟨t₀, x₀⟩
  by_cases hx₀ : x₀ ∈ tsupport ρ
  · have hc : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M ↦ -deriv Real.smoothTransition p.1) (t₀, x₀) := by
      have hd : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
        (contDiff_infty_iff_deriv.1 (Real.smoothTransition.contDiff (n := ⊤))).2
      exact (hd.neg.contMDiff.comp contMDiff_fst).contMDiffAt
    have hβ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
        (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] ℝ)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) p.2
          (SmoothForm.degreeOneEquiv β p.2)) (t₀, x₀) :=
      SmoothForm.contMDiffAt_sectionAlong_degreeOneEquiv_iff (α := fun _ ↦ β).2
        ((β.contMDiff.comp contMDiff_snd).contMDiffAt)
    have h := (ContMDiffAt.clm_bundle_inverse (x := (t₀, x₀)) (b := Prod.snd)
      (ϕ := fun p : ℝ × M ↦ (σ₀ + Real.smoothTransition p.1 • (σ₁ - σ₀)).flat p.2)
      (contMDiff_flat_moserFamily σ₀ σ₁ _)
      (hinv t₀ x₀ hx₀)).clm_bundle_apply (hc.smul_totalSpace hβ)
    exact (hρ.comp contMDiff_snd).contMDiffAt.smul_totalSpace h
  · -- Away from the support of `ρ` the field vanishes identically.
    refine ((contMDiff_zeroSection ℝ (TangentSpace I)).comp contMDiff_snd).contMDiffAt
      |>.congr_of_eventuallyEq ?_
    filter_upwards [(continuous_snd.tendsto (t₀, x₀)).eventually
      (notMem_tsupport_iff_eventuallyEq.1 hx₀)] with p hp
    simp only [moserField, hp, Pi.zero_apply, zero_smul]
    -- The zero section at `p.2` is the pair `⟨p.2, 0⟩` by definition.
    rfl

/-- If the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate along a compact set `K`, it is
nondegenerate on a whole open neighbourhood of `K`, and so are all the slices of the Moser family
there. -/
private theorem exists_isOpen_isInvertible_flat {σ₀ σ₁ : SmoothTwoForm I M} {K : Set M}
    (hK : IsCompact K)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧ ∀ t, ∀ x ∈ N,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible := by
  set O := {p : ℝ × M | ((σ₀ + Real.smoothTransition p.1 • (σ₁ - σ₀)).flat p.2).IsInvertible}
  -- The bundles and the base map are given explicitly: unification would otherwise read the
  -- section along the identity of `M`.
  have hO : IsOpen O := Continuous.isOpen_setOf_clm_bundle_isInvertible (𝕜 := ℝ) (F₁ := E)
    (F₂ := E →L[ℝ] ℝ) (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    (b := Prod.snd) (ϕ := fun p : ℝ × M ↦ (σ₀ + Real.smoothTransition p.1 • (σ₁ - σ₀)).flat p.2)
    (contMDiff_flat_moserFamily σ₀ σ₁).continuous
  have hsub : Icc (0 : ℝ) 1 ×ˢ K ⊆ O := fun p hp ↦ isInvertible_flat_iff.2
    (hnd p.2 hp.2 _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  obtain ⟨u, N, -, hN, hu, hKN, huN⟩ := generalized_tube_lemma isCompact_Icc hK hO hsub
  -- The step function takes the same value at `t` and at its projection to `[0, 1]`.
  refine ⟨N, hN, hKN, fun t x hx ↦ ?_⟩
  have h := huN (mk_mem_prod (hu (projIcc (0 : ℝ) 1 zero_le_one t).property) hx)
  simpa only [O, mem_ofPred_eq, Real.smoothTransition.projIcc] using h

/-- If the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is nondegenerate along a compact set `K`, it
stays nondegenerate on an open neighbourhood of `K`. -/
theorem exists_isOpen_forall_nondegenerate {σ₀ σ₁ : SmoothTwoForm I M} {K : Set M}
    (hK : IsCompact K)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ N, IsOpen N ∧ K ⊆ N ∧
      ∀ x ∈ N, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate := by
  obtain ⟨N, hN, hKN, hinvN⟩ := exists_isOpen_isInvertible_flat hK hnd
  refine ⟨N, hN, hKN, fun x hx s hs ↦ ?_⟩
  obtain ⟨t, -, rfl⟩ := Real.smoothTransition.surjOn_Icc hs
  exact isInvertible_flat_iff.1 (hinvN t x hx)

/-! ### Moser's equation and the relative Moser theorems -/

variable [I.Boundaryless]

/-- **The Moser field inherits a zero first jet from the primitive.** If `β` vanishes at `x`,
its coordinate expression in the chart at `x` has zero derivative there, and the slice `σ_t` is
nondegenerate at `x`, then the coordinate expression of the Moser field `X_t` in the chart at `x`
also has zero derivative at the chart point of `x`.

Write `σ'_t`, `X'_t` and `β'` for the coordinate expressions in the chart at `x`. There
`ι_{X_t} σ_t = -ρ c'(t) β` reads `σ'_t♭(z) (X'_t(z)) = -ρ c'(t) β'(z)`, and the inverse of
`σ'_t♭(z)` stays bounded near the chart point `z₀` of `x`, so `X'_t = O(β') = o(z - z₀)`. -/
private theorem hasFDerivAt_mpullbackWithin_moserField
    {σ₀ σ₁ : SmoothTwoForm I M} {β : SmoothForm I M ℝ 1} {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    {x : M} (hx : x ∈ tsupport ρ) (hβx : β.val x = 0)
    (hβ : HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (extChartAt I x x)) (t : ℝ) :
    HasFDerivAt (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (moserField σ₀ σ₁ β ρ t) (range I)) (0 : E →L[ℝ] E) (extChartAt I x x) := by
  set z₀ := extChartAt I x x
  set σt := σ₀ + Real.smoothTransition t • (σ₁ - σ₀)
  set V : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
    (moserField σ₀ σ₁ β ρ t) (range I)
  -- The flat maps of the coordinate expression of the slice, and the coefficient `-ρ c'(t)`.
  set F : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦ ContinuousAlternatingMap.flatL ℝ E ℝ
    (RoughForm.inChartAt σt.val x z)
  set κ : E → ℝ := fun z ↦ ρ ((extChartAt I x).symm z) * -deriv Real.smoothTransition t
  have hFc : ContinuousAt F z₀ := by
    have h := (σt.isSmoothForm.contDiffWithinAt_inChartAt_self x).continuousWithinAt
    rw [I.range_eq_univ, continuousWithinAt_univ] at h
    exact (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.continuousAt.comp h
  have hF₀ : (F z₀).IsInvertible := by
    simp only [F, z₀, RoughForm.inChartAt_extChartAt_self, ← flat_def]
    exact hinv t x hx
  have hκc : ContinuousAt κ z₀ :=
    ((hρ.continuous.continuousAt).comp (continuousAt_extChartAt_symm x)).mul continuousAt_const
  -- In the chart, `σ'_t♭(z) (X'_t(z)) = -ρ c'(t) β'(z)`.
  have hkey : ∀ᶠ z in 𝓝 z₀, ‖F z (V z)‖ = ‖κ z‖ * ‖RoughForm.inChartAt β.val x z‖ :=
    Filter.eventually_of_mem (extChartAt_target_mem_nhds x) fun z hz ↦
      norm_flatL_inChartAt_mpullbackWithin_moserField β hinv hz t
  -- The inverses of `σ'_t♭(z)` are bounded near `z₀`, so `X'_t = O(β')`.
  set G : E → (E →L[ℝ] ℝ) →L[ℝ] E := fun z ↦ (F z).inverse
  -- Name the operator norm instance: inferring it through the dual space times out.
  let : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  have hGc : ContinuousAt G z₀ :=
    (hF₀.contDiffAt_map_inverse (n := 0)).continuousAt.comp hFc
  have hbig : V =O[𝓝 z₀] RoughForm.inChartAt β.val x := by
    refine Asymptotics.IsBigO.of_bound ((‖G z₀‖ + 1) * (‖κ z₀‖ + 1)) ?_
    filter_upwards [hFc.eventually hF₀.eventually_nhds, hkey,
      hGc.norm.eventually (gt_mem_nhds (lt_add_one ‖G z₀‖)),
      hκc.norm.eventually (gt_mem_nhds (lt_add_one ‖κ z₀‖))] with z hzF hzk hzG hzκ
    calc ‖V z‖ = ‖G z (F z (V z))‖ := by rw [hzF.inverse_apply_self]
      _ ≤ ‖G z‖ * ‖F z (V z)‖ := (G z).le_opNorm _
      _ = ‖G z‖ * (‖κ z‖ * ‖RoughForm.inChartAt β.val x z‖) := by rw [hzk]
      _ ≤ (‖G z₀‖ + 1) * ((‖κ z₀‖ + 1) * ‖RoughForm.inChartAt β.val x z‖) := by
        gcongr
      _ = _ := by ring
  -- The primitive vanishes to first order at `z₀`, hence so does `X'_t`.
  have hβ₀ : RoughForm.inChartAt β.val x z₀ = 0 := (RoughForm.inChartAt_extChartAt_self _ x).trans
      hβx
  have hV₀ : V z₀ = 0 := by
    have h : moserField σ₀ σ₁ β ρ t ((extChartAt I x).symm z₀) = 0 :=
      moserField_eq_zero ρ (by rw [extChartAt_to_inv]; exact hβx) t
    simp only [V]
    rw [VectorField.mpullbackWithin_apply, h, map_zero]
    -- The zero of the tangent space of the model space is the zero of `E`.
    rfl
  have hβo := hβ.isLittleO
  simp only [hβ₀, sub_zero, zero_apply] at hβo
  exact .of_isLittleO (by simpa only [hV₀, sub_zero, zero_apply] using hbig.trans_isLittleO hβo)

/-- **Moser's equation for the cut-off Moser field.** Near a point around which `ρ = 1`, the rate
`∂_t σ_t + L_{X_t} σ_t` of the Moser family vanishes: `∂_t σ_t = c'(t) dβ`, while Cartan's formula
gives `L_{X_t} σ_t = d (ι_{X_t} σ_t) = -c'(t) dβ`. -/
private theorem moserRate_eq_zero {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) {β : SmoothForm I M ℝ 1} {ρ : M → ℝ}
    (hβ : ∀ x ∈ tsupport ρ, mextDeriv β.val x = (σ₁ - σ₀).val x)
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    (t : ℝ) {y : M} (hy : ∀ᶠ z in 𝓝 y, ρ z = 1) :
    (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) (moserFamily σ₀ σ₁).val) +
      mlieDerivForm (moserField σ₀ σ₁ β ρ t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (moserFamily σ₀ σ₁).val)) y = 0 := by
  -- The slices `σ₀ + c(u) (σ₁ - σ₀)` have velocity `c'(t) (σ₁ - σ₀)`.
  have hvel : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) (moserFamily σ₀ σ₁).val) y =
      deriv Real.smoothTransition t • (σ₁ - σ₀).val y := by
    simpa only [moserFamily, SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv, Submodule.coe_smul,
      Pi.smul_apply] using
      congrArg (fun β ↦ β.val y) (SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily σ₀ σ₁
        (Real.smoothTransition.contDiff (n := ⊤)) t)
  -- The slice at time `t` is closed, since `σ₀` and `σ₁` are.
  have hclosed : (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).IsClosed :=
    h₀.add ((h₁.sub h₀).smul _)
  have hXt : MDifferentiableAt I I.tangent
      (fun z ↦ (⟨z, moserField σ₀ σ₁ β ρ t z⟩ : TangentBundle I M)) y :=
    ((contMDiff_moserField β hρ hinv).comp (contMDiff_const.prodMk contMDiff_id)
      |>.mdifferentiableAt (by simp))
  -- Near `y` the contraction `ι_{X_t} σ_t` is `-c'(t) β`, whose exterior derivative is
  -- `-c'(t) (σ₁ - σ₀)`.
  have hL : mlieDerivForm (moserField σ₀ σ₁ β ρ t)
      (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val y =
        -deriv Real.smoothTransition t • (σ₁ - σ₀).val y := by
    rw [mlieDerivForm_eq_mextDeriv_interior_apply (SmoothForm.mdifferentiableAt _ y) hXt
      (congrFun ((SmoothForm.isClosed_def _).1 hclosed) y)]
    have hev : ∀ᶠ z in 𝓝 y, RoughForm.interior (moserField σ₀ σ₁ β ρ t)
        (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).val z =
          (-deriv Real.smoothTransition t • β.val) z := by
      filter_upwards [hy] with z hz
      have hz' : z ∈ tsupport ρ := subset_tsupport _ (by simp [hz])
      rw [interior_moserField β ρ (hinv t z hz'), hz, one_mul, Pi.smul_apply]
    rw [mextDeriv_congr_of_eventuallyEq hev, mextDeriv_smul, Pi.smul_apply,
      hβ y (subset_tsupport _ (by simp [hy.self_of_nhds]))]
  rw [Pi.add_apply, hvel, mpullback_prodMk_moserFamily_coe, hL, neg_smul, add_neg_cancel]

variable [T2Space M]

/-- The flow of the Moser field fixes to first order every point of the support of `ρ` at which
`β` vanishes with zero first jet: its differential there is the identity. -/
private theorem mfderiv_timeDependentFlowOf_moserField_eq_id {σ₀ σ₁ : SmoothTwoForm I M}
    {β : SmoothForm I M ℝ 1} {ρ : M → ℝ} (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    {x : M} (hx : x ∈ tsupport ρ) (hβx : β.val x = 0)
    (hβ : HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (extChartAt I x x)) (s t : ℝ) :
    mfderiv I I (timeDependentFlowOf (moserField σ₀ σ₁ β ρ) s t) x =
      ContinuousLinearMap.id ℝ (TangentSpace I x) :=
  mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero
    ((contMDiff_moserField β hρ hinv).of_le (by simp)) (moserField_eq_zero ρ hβx) fun u _ ↦
      (hasFDerivAt_mpullbackWithin_moserField hρ hinv hx hβx hβ u).fderiv

/-- **Moser's theorem relative to a compact set, with a given primitive and cut-off.** Let `σ₀`,
`σ₁` be closed two-forms on a boundaryless manifold, let `ρ` be a smooth compactly supported
function, equal to `1` near a compact set `K`, and let `β` be a smooth one-form with `dβ = σ₁ - σ₀`
on the support of `ρ`, vanishing along `K`. Suppose the path `σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, is
nondegenerate on the support of `ρ`. Then there is a diffeomorphism `Φ` of the manifold which fixes
every point of `K` and every point off the support of `ρ`, and pulls `σ₁` back to `σ₀` on a
neighbourhood of `K`. It fixes to first order every point of `K` at which `β` has zero first jet.

The diffeomorphism is natural: it commutes with every diffeomorphism `g` which preserves `σ₀`,
`σ₁`, `β` and `ρ`. This is how the equivariant relative Moser theorem is obtained, from invariant
primitives and cut-offs. -/
theorem exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff {σ₀ σ₁ : SmoothTwoForm I M}
    (h₀ : σ₀.IsClosed) (h₁ : σ₁.IsClosed) {β : SmoothForm I M ℝ 1} {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρc : HasCompactSupport ρ)
    (hβ : ∀ x ∈ tsupport ρ, mextDeriv β.val x = (σ₁ - σ₀).val x)
    (hnd : ∀ x ∈ tsupport ρ, ∀ s ∈ Icc (0 : ℝ) 1,
      ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ x ∈ K, β.val x = 0) (hρ1 : ∀ᶠ x in 𝓝ˢ K, ρ x = 1) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∀ x ∉ tsupport ρ, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ K, (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      (∀ x ∈ K, HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
        (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      ∀ g : M ≃ₘ⟮I, I⟯ M, mpullback I I g σ₀.val = σ₀.val → mpullback I I g σ₁.val = σ₁.val →
        mpullback I I g β.val = β.val → (∀ x, ρ (g x) = ρ x) → ∀ x, Φ (g x) = g (Φ x) := by
  have hinv (t : ℝ) (x : M) (hx : x ∈ tsupport ρ) :
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible :=
    isInvertible_flat_iff.2
      (hnd x hx _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩)
  have hX := contMDiff_moserField β hρ hinv
  have hX₁ := hX.of_le (m := 1) (by simp)
  have hzero (x : M) (hx : ∀ u, moserField σ₀ σ₁ β ρ u x = 0) (s t : ℝ) :
      timeDependentFlowOf (moserField σ₀ σ₁ β ρ) s t x = x :=
    timeDependentFlowOf_eq_self_of_forall_eq_zero hX₁ hx s t
  have hXρ (u : ℝ) (y : M) (hy : y ∉ tsupport ρ) : moserField σ₀ σ₁ β ρ u y = 0 := by
    simp [moserField, image_eq_zero_of_notMem_tsupport hy]
  have hc := isCompleteVectorField_timeDependentSuspensionField hX₁ hρc hXρ
  let Φ := timeDependentFlowDiffeomorph hc le_top hX 0 1
  have hΦ : ⇑Φ = timeDependentFlowOf (moserField σ₀ σ₁ β ρ) 0 1 :=
    funext (timeDependentFlowDiffeomorph_apply hc le_top hX 0 1)
  have hKρ : K ⊆ tsupport ρ := fun x hx ↦ subset_tsupport _
    (by simp [(eventually_nhdsSet_iff_forall.1 hρ1 x hx).self_of_nhds])
  refine ⟨Φ, fun x hx ↦ ?_, fun x hx ↦ ?_, ?_, fun x hx hjet ↦ hΦ ▸
    mfderiv_timeDependentFlowOf_moserField_eq_id hρ hinv (hKρ hx) (hβK x hx) hjet 0 1,
    fun g hg₀ hg₁ hgβ hgρ x ↦ ?_⟩
  · rw [hΦ]
    exact hzero x (moserField_eq_zero ρ (hβK x hx)) 0 1
  · rw [hΦ]
    exact hzero x (fun u ↦ hXρ u x hx) 0 1
  rotate_left
  · -- The flow of a natural field commutes with the symmetry.
    rw [hΦ]
    exact ((g.mdifferentiable (by simp)).apply_timeDependentFlowOf hX₁ hX₁
      (mfderiv_moserField hinv g hg₀ hg₁ hgβ hgρ)
      ((timeDependentFlowDomain_eq_univ hc).symm ▸ mem_univ _)).symm
  -- The trajectories starting near `K` stay, up to time `1`, where `ρ = 1` near each point.
  set V := {y : M | ∀ᶠ z in 𝓝 y, ρ z = 1}
  have hKV : K ⊆ V := fun x hx ↦ (eventually_nhdsSet_iff_forall.1 hρ1) x hx
  have hφ : Continuous fun p : ℝ × M ↦ timeDependentFlowOf (moserField σ₀ σ₁ β ρ) 0 p.1 p.2 :=
    ((contMDiff_timeDependentFlowOf hc le_top hX).comp
      ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)).continuous
  have hS : IsOpen {p : ℝ × M | timeDependentFlowOf (moserField σ₀ σ₁ β ρ) 0 p.1 p.2 ∈ V} :=
    isOpen_setOfPred_eventually_nhds.preimage hφ
  obtain ⟨u, W, -, hW, hu, hKW, huW⟩ := generalized_tube_lemma isCompact_Icc hK hS
    fun p hp ↦ by
      rw [mem_ofPred_eq, hzero p.2 (moserField_eq_zero ρ (hβK p.2 hp.2))]
      exact hKV hp.2
  filter_upwards [hW.mem_nhdsSet.2 hKW] with x hx
  -- Along these trajectories Moser's equation holds, so the flow carries `σ₁` back to `σ₀`.
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_uIcc
    (hX.of_le (by simp)) hc (fun _ _ ↦ ((moserFamily σ₀ σ₁).contMDiff.of_le (by simp)).contMDiffAt)
    fun t ht ↦ moserRate_eq_zero h₀ h₁ hβ hρ hinv t
      (huW (mk_mem_prod (hu ((uIcc_of_le (zero_le_one' ℝ)).subset ht)) hx))
  rw [mpullback_prodMk_moserFamily_coe, mpullback_prodMk_moserFamily_coe,
    Real.smoothTransition.one, Real.smoothTransition.zero, one_smul, zero_smul,
    add_zero, add_sub_cancel] at h
  rw [SmoothForm.coe_mpullback, hΦ]
  exact h

/-- **Moser's theorem relative to a compact set, with a given primitive.** Let `σ₀`, `σ₁` be
two-forms on a boundaryless manifold, with `σ₀` closed and `σ₁ - σ₀ = dβ` for a smooth one-form
`β`. Let `K` be a compact set along which `β` vanishes and along which the path
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, stays nondegenerate. Then there is a diffeomorphism `Φ` of the
manifold which fixes every point of `K`, moves only the points of a compact set, and pulls `σ₁`
back to `σ₀` on a neighbourhood of `K`. Moreover `Φ` fixes to first order every point of `K` at
which `β` has zero first jet: where the coordinate expression of `β` in the chart at `x` has zero
derivative at the chart point of `x`, the differential of `Φ` at `x` is the identity. -/
theorem exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.val = (σ₁ - σ₀).val)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ x ∈ K, β.val x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ K, (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      ∀ x ∈ K, HasFDerivAt (RoughForm.inChartAt β.val x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
        (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  -- `σ₁ = σ₀ + dβ` is closed.
  have h₁ : σ₁.IsClosed := by
    have h : (σ₁ - σ₀).IsClosed := by
      rw [SmoothForm.isClosed_def, ← hβ]
      exact SmoothForm.mextDeriv_mextDeriv β
    simpa using h₀.add h
  -- Cut the Moser field off outside a neighbourhood of `K` on which the path stays nondegenerate.
  obtain ⟨N, hN, hKN, hndN⟩ := exists_isOpen_forall_nondegenerate hK hnd
  obtain ⟨ρ, hρ, hρ1, hρc, hρN, -⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I hN hKN
  obtain ⟨Φ, hΦK, hΦρ, hΦ, hΦ1, -⟩ := exists_diffeomorph_fix_eventually_mpullback_eq_of_cutoff
    h₀ h₁ hρ hρc (fun x _ ↦ congrFun hβ x) (fun x hx ↦ hndN x (hρN hx)) hK hβK hρ1
  exact ⟨Φ, hΦK, ⟨tsupport ρ, hρc, hΦρ⟩, hΦ, hΦ1⟩

/-- **A primitive of `σ₁ - σ₀` near a submanifold along which the pullbacks agree.** Let `σ₀`,
`σ₁` be closed two-forms on a boundaryless second-countable Hausdorff manifold `M` whose pullbacks
along an embedded submanifold `f : Q → M` agree. Then on an open neighbourhood `W` of `f(Q)` the
restriction of `σ₁ - σ₀` has a smooth primitive `β` which vanishes along `f(Q)` and has zero first
jet at every point `f q` where `σ₁ - σ₀` vanishes. -/
theorem exists_relative_primitive_sub_of_mpullback_eq [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀) :
    ∃ (W : TopologicalSpace.Opens M) (hfW : range f ⊆ W) (β : RoughForm I W ℝ 1),
      IsSmoothForm I ∞ β ∧ mextDeriv β = mpullback I I (Subtype.val : W → M) (σ₁ - σ₀).val ∧
      (∀ q, β ⟨f q, hfW (mem_range_self q)⟩ = 0) ∧
      ∀ q, (σ₁ - σ₀).val (f q) = 0 →
        HasFDerivAt (RoughForm.inChartAt β ⟨f q, hfW (mem_range_self q)⟩)
          (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
          (extChartAt I (⟨f q, hfW (mem_range_self q)⟩ : W) ⟨f q, hfW (mem_range_self q)⟩) := by
  have hpull : mpullback J I f (σ₁ - σ₀).val = 0 := by
    have h := congrArg Subtype.val hf
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback] at h
    rw [AddSubgroupClass.coe_sub, mpullback_sub, h, sub_self]
  -- This is the relative Poincaré lemma on a tubular neighbourhood of `f(Q)`.
  obtain ⟨W, -, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := ℝ) isOpen_univ
    (subset_univ _)
  exact ⟨W, hfW, hprim (k := 1) (r := ⊤) le_top (σ₁ - σ₀).isSmoothForm
    ((SmoothForm.isClosed_def _).1 (h₁.sub h₀)) hpull⟩

/-- **The relative Moser theorem for forms with equal pullbacks.** Let `σ₀`, `σ₁` be closed
two-forms on a boundaryless second-countable Hausdorff manifold `M` whose pullbacks along a compact
embedded submanifold `f : Q → M` agree, and suppose that the path `σ₀ + s (σ₁ - σ₀)`,
`s ∈ [0, 1]`, is nondegenerate at every point of `f(Q)`. Then there is a diffeomorphism `Φ` of `M`
which fixes every point of `f(Q)`, moves only the points of a compact set, and pulls `σ₁` back to
`σ₀` on a neighbourhood of `f(Q)`. Moreover `Φ` fixes to first order every point `f q` at which
`σ₁` and `σ₀` agree as bilinear forms on the full ambient tangent space: its differential there is
the identity. -/
theorem exists_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq
    [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed)
    (hf : SmoothForm.mpullback f f.contMDiff σ₁ = SmoothForm.mpullback f f.contMDiff σ₀)
    (hnd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q)).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      ∀ q, σ₁.val (f q) = σ₀.val (f q) →
        mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q)) := by
  -- A primitive of `σ₁ - σ₀` on a neighbourhood `W` of `f(Q)`, vanishing along `f(Q)`, with zero
  -- first jet wherever `σ₁ - σ₀` vanishes.
  obtain ⟨W, hfW, βW, hβW, hdβW, hβW0, hβW1⟩ :=
    exists_relative_primitive_sub_of_mpullback_eq f h₀ h₁ hf
  -- Moser's argument runs on the open submanifold `W`, with the restricted forms.
  let res := SmoothForm.mpullback (I := I) (I' := I) (F := ℝ) (k := 2) (Subtype.val : W → M)
    contMDiff_subtypeVal
  let g : Q → W := fun q ↦ ⟨f q, hfW (mem_range_self q)⟩
  have hgK : IsCompact (range g) :=
    isCompact_range (f.contMDiff.continuous.subtype_mk fun q ↦ hfW (mem_range_self q))
  obtain ⟨Ψ, hΨK, ⟨C, hC, hΨC⟩, hΨ, hΨ1⟩ :=
    exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub (σ₀ := res σ₀)
      (σ₁ := res σ₁) (h₀.mpullback _ _) (β := ⟨βW, hβW.mem_smoothBundleForms⟩)
    (by rw [hdβW, ← map_sub]; exact (SmoothForm.coe_mpullback _ _ _).symm) hgK
    (by rintro _ ⟨q, rfl⟩; exact hβW0 q)
    (by
      rintro _ ⟨q, rfl⟩ s hs
      rw [← map_sub, ← map_smul, ← map_add]
      exact (nondegenerate_bilinFormAt_mpullback_subtype_val_iff (g q)).2 (hnd q s hs))
  -- Extend the compactly supported diffeomorphism of `W` by the identity.
  obtain ⟨Φ, hΦW, hΦC⟩ := Ψ.exists_extend_of_isCompact hC hΨC
  have hcomp : ⇑Φ ∘ (Subtype.val : W → M) = Subtype.val ∘ ⇑Ψ := funext hΦW
  -- On `W`, the differential of `Φ` at `f q` is that of `Ψ` at `g q`.
  have hΦ1 (q : Q) (hq : σ₁.val (f q) = σ₀.val (f q)) :
      mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q)) := by
    have hη : (σ₁ - σ₀).val (f q) = 0 := by
      rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hq, sub_self]
    exact (Manifold.mfderiv_eq_id_iff_of_comp_subtype_val hcomp.symm).1
      (hΨ1 (g q) (mem_range_self q) (hβW1 q hη))
  have hrange : Subtype.val '' range g = range f := (range_comp _ _).symm
  exact ⟨Φ, fun q ↦ (hΦW (g q)).trans (congrArg Subtype.val (hΨK _ (mem_range_self q))),
    ⟨Subtype.val '' C, hC.image continuous_subtypeVal, hΦC⟩,
    hrange ▸ SmoothForm.eventually_mpullback_eq_of_subtype_val_comp_eq Φ.contMDiff Ψ.contMDiff
      hcomp hΨ, hΦ1⟩

/-- **The relative Moser theorem.** Let `σ₀`, `σ₁` be closed two-forms on a boundaryless
second-countable Hausdorff manifold `M` which agree, as bilinear forms on the full tangent spaces of
`M`, at every point of a compact embedded submanifold `f : Q → M`, and let `σ₀` be nondegenerate
along it. Then there is a diffeomorphism `Φ` of `M` which fixes every point of `f(Q)`, moves only
the points of a compact set, and pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. Moreover
`Φ` fixes `f(Q)` to first order: its differential at every point of `f(Q)` is the identity of the
full ambient tangent space. -/
theorem exists_diffeomorph_fix_embedding_eventually_mpullback_eq [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      (∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).val x = σ₀.val x) ∧
      ∀ q, mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q)) := by
  -- The forms agree along `f(Q)`, so do their pullbacks, and the path is constantly `σ₀` there.
  obtain ⟨Φ, hΦf, hΦC, hΦ, hΦ1⟩ :=
    exists_diffeomorph_fix_embedding_eventually_mpullback_eq_of_mpullback_eq f h₀ h₁
      (SmoothForm.mpullback_eq_of_forall_apply_eq f.contMDiff heq)
      fun q s _ ↦ bilinFormAt_add_smul_sub_of_eq (heq q) s ▸ hnd q
  exact ⟨Φ, hΦf, hΦC, hΦ, fun q ↦ hΦ1 q (heq q)⟩

open TopologicalSpace in
/-- **The relative Moser theorem between neighbourhoods** (Cannas da Silva, Theorem 7.4). Let `σ₀`,
`σ₁` be closed two-forms on a boundaryless second-countable Hausdorff manifold `M` which agree, as
bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded submanifold
`f : Q → M`, and let `σ₀` be nondegenerate along it. Then there are open neighbourhoods `U₀`, `U₁`
of `f(Q)` and a diffeomorphism `φ : U₀ → U₁` which fixes every point of `f(Q)` and pulls the
restriction of `σ₁` to `U₁` back to the restriction of `σ₀` to `U₀`. Its differential at every
point of `f(Q)` is the identity of the full ambient tangent space. -/
theorem exists_diffeomorph_opens_of_eq_along [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.val (f q) = σ₀.val (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtypeVal σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtypeVal σ₀ := by
  obtain ⟨Φ, hΦf, -, hΦ, hΦ1⟩ :=
    exists_diffeomorph_fix_embedding_eventually_mpullback_eq f h₀ h₁ hnd heq
  -- Restrict `Φ` to an open neighbourhood `U` of `f(Q)` on which it pulls `σ₁` back to `σ₀`, and
  -- to its image `Φ(U)`, the preimage of `U` under `Φ⁻¹`.
  obtain ⟨U, ⟨hU, hfU⟩, hUΦ⟩ := (hasBasis_nhdsSet (range f)).mem_iff.1 hΦ
  let U₀ : Opens M := ⟨U, hU⟩
  let U₁ : Opens M := ⟨Φ.symm ⁻¹' U, hU.preimage Φ.symm.continuous⟩
  have hU₀₁ (x : M) : x ∈ U₀ ↔ Φ x ∈ U₁ := by
    simp [U₀, U₁]
  refine ⟨U₀, U₁, Φ.subtype hU₀₁, fun q ↦
    ⟨hfU (mem_range_self q), (Φ.subtype_apply_coe hU₀₁ _).trans (hΦf q), ?_⟩, ?_⟩
  · -- The restriction `φ` has the differential of `Φ`, read through the inclusions.
    exact ContinuousLinearMap.ext fun v ↦
      (Manifold.mfderiv_apply_of_subtype_val_comp_eq (I' := I)
        (funext fun x ↦ Φ.subtype_apply_coe hU₀₁ x) v).trans (DFunLike.congr_fun (hΦ1 q) v)
  apply Subtype.ext
  funext z
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtypeVal Φ.contMDiff
    (funext (Φ.subtype_apply_coe hU₀₁)), SmoothForm.coe_mpullback_subtype_val_apply,
    SmoothForm.coe_mpullback_subtype_val_apply]
  exact hUΦ z.property

end TauCeti.SmoothTwoForm
