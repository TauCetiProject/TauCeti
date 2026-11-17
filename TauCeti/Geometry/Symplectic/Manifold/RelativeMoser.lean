/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.Flow.TimeDependent.RestPoint
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The relative Moser theorem

Let `σ₀`, `σ₁` be closed two-forms on a boundaryless Hausdorff second-countable manifold `M` which
agree, as bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded
submanifold `f : Q → M`, with `σ₀` nondegenerate along `f(Q)`. The **relative Moser theorem**
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`) gives a
diffeomorphism `Φ` of `M` which fixes every point of `f(Q)`, moves only the points of a compact
set, and pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. It fixes `f(Q)` to first order:
its differential at every point of `f(Q)` is the identity of the full ambient tangent space.
Restricted to such a neighbourhood `U`, it is a diffeomorphism from `U` onto the open set `Φ(U)`
which fixes `f(Q)` pointwise, with differential the identity there, and carries `σ₀` on `U` to
`σ₁` on `Φ(U)`
(`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`). Only the agreement of the full
ambient forms along `f(Q)` is used; agreement of their pullbacks to `Q` is a weaker condition.

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

If moreover `β` has zero first jet at a point `x` of `K`, then so does `X_t`: in the preferred
chart at `x`, the coordinate expressions satisfy `σ_{c(t)} (X_t, ·) = -c'(t) β` near the chart
point, and the flat map of `σ_{c(t)}` is uniformly invertible there, so `X_t` is bounded by a
multiple of `β`. The variational equation of the flow at the common rest point `x`
(`TauCeti.mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero`) then makes the differential of
`Φ` at `x` the identity.

For the submanifold version, the relative Poincaré lemma
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`) writes `σ₁ - σ₀`, whose
pullback along `f` vanishes, as `dβ` on a tubular neighbourhood `W` of `f(Q)`, with `β` vanishing
along `f(Q)`. Since `σ₁ - σ₀` vanishes along `f(Q)` as a full ambient tensor, `β` has moreover zero
first jet there. Moser's argument on the open submanifold `W` gives a compactly supported
diffeomorphism of `W` whose differential is the identity along `f(Q)`, and which extends by the
identity to `M`. This first-order identity requires the full ambient agreement of the forms: it is
what lets a prescribed differential along `f(Q)` survive the Moser correction.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub`:
  Moser's theorem relative to a compact set along which a given primitive of `σ₁ - σ₀` vanishes,
  with identity differential wherever the primitive has zero first jet.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`: the relative
  Moser theorem for closed two-forms agreeing along a compact embedded submanifold, by a
  diffeomorphism with identity differential along it.
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
  SmoothForm.mpullback Prod.snd contMDiff_snd σ₀ +
    SmoothForm.funSMulₗ ⟨fun p ↦ Real.smoothTransition p.1, by
      exact (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_fst⟩
      (SmoothForm.mpullback Prod.snd contMDiff_snd (σ₁ - σ₀))

/-- The slices of the Moser family are the forms `σ₀ + c(t) (σ₁ - σ₀)`. -/
private theorem mpullback_prodMk_moserFamily (σ₀ σ₁ : SmoothTwoForm I M) (t : ℝ) :
    SmoothForm.mpullback (Prod.mk t) (contMDiff_const.prodMk contMDiff_id)
        (moserFamily σ₀ σ₁) = σ₀ + Real.smoothTransition t • (σ₁ - σ₀) := by
  apply Subtype.ext
  -- `Prod.snd ∘ Prod.mk t` is the identity of `M`.
  have hcomp (τ : SmoothTwoForm I M) : TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (TauCeti.mpullback (𝓘(ℝ, ℝ).prod I) I Prod.snd τ.1) = τ.1 := by
    simpa only [SmoothForm.coe_mpullback, LinearMap.id_apply] using
      congrArg Subtype.val ((SmoothForm.mpullback_mpullback (Prod.mk t) Prod.snd
        (I' := 𝓘(ℝ, ℝ).prod I) (contMDiff_const.prodMk contMDiff_id) contMDiff_snd τ).trans
          (LinearMap.congr_fun SmoothForm.mpullback_id τ))
  simp only [moserFamily, map_add, SmoothForm.coe_mpullback, SmoothForm.add_toRoughForm, hcomp]
  -- `erw`: the coercion of `funSMulₗ` carries the `IsManifold _ 1` instance derived from the
  -- product, which differs syntactically from the one in the goal.
  erw [SmoothForm.coe_funSMulₗ, mpullback_fun_smul, SmoothForm.coe_mpullback, hcomp]
  -- The bundled cut-off function evaluates at `(t, x)` to `Real.smoothTransition t` by definition,
  -- and the scalar multiple of a smooth form is computed pointwise.
  rfl

/-- The slices of the Moser family, as rough forms. -/
private theorem mpullback_prodMk_moserFamily_coe (σ₀ σ₁ : SmoothTwoForm I M) (t : ℝ) :
    mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (moserFamily σ₀ σ₁).1 =
      (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).1 :=
  (SmoothForm.coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_prodMk_moserFamily σ₀ σ₁ t))

/-- The Moser vector field of the path `σ₀ + c(t) (σ₁ - σ₀)` and the primitive `β`, cut off by
`ρ`: `X_t = ρ (σ_t♭)⁻¹ (-c'(t) β)`. -/
private def moserField (σ₀ σ₁ : SmoothTwoForm I M) (β : SmoothForm I M ℝ 1) (ρ : M → ℝ)
    (t : ℝ) (x : M) : TangentSpace I x :=
  ρ x • ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).inverse
    (-deriv Real.smoothTransition t • SmoothForm.degreeOneEquiv β x)

/-- The Moser field vanishes where the primitive does. -/
private theorem moserField_eq_zero {σ₀ σ₁ : SmoothTwoForm I M} {β : SmoothForm I M ℝ 1}
    (ρ : M → ℝ) {x : M} (hx : β.1 x = 0) (t : ℝ) : moserField σ₀ σ₁ β ρ t x = 0 := by
  have h : SmoothForm.degreeOneEquiv β x = 0 := ContinuousLinearMap.ext fun v ↦ by
    rw [SmoothForm.degreeOneEquiv_apply_apply_vec, hx, ContinuousAlternatingMap.coe_zero,
      Pi.zero_apply, zero_apply]
  simp [moserField, h]

/-- Where the slice is nondegenerate, the Moser field satisfies `ι_{X_t} σ_t = -ρ c'(t) β`. -/
private theorem interior_moserField {σ₀ σ₁ : SmoothTwoForm I M} (β : SmoothForm I M ℝ 1)
    (ρ : M → ℝ) {t : ℝ} {x : M}
    (hx : ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible) :
    RoughForm.interior (moserField σ₀ σ₁ β ρ t) (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).1 x =
      (ρ x * -deriv Real.smoothTransition t) • β.1 x := by
  rw [interior_apply_eq_ofSubsingleton_flat, moserField, map_smul, hx.self_apply_inverse]
  ext v
  have hv : v = ![v 0] := funext fun i ↦ by fin_cases i; rfl
  rw [hv]
  simp [mul_assoc]

/-- The flat maps of the slices of the Moser family form a smooth section along the projection
`ℝ × M → M`. -/
private theorem contMDiff_flat_moserFamily (σ₀ σ₁ : SmoothTwoForm I M) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((σ₀ + Real.smoothTransition p.1 • (σ₁ - σ₀)).flat p.2)) := by
  intro p
  have hσ := SmoothForm.contMDiff_mpullback_prodMk (moserFamily σ₀ σ₁) p
  simp only [mpullback_prodMk_moserFamily] at hσ
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
  have h := huN (mk_mem_prod (hu (projIcc (0 : ℝ) 1 zero_le_one t).2) hx)
  simpa only [O, mem_ofPred_eq, Real.smoothTransition.projIcc] using h

/-! ### Moser's equation and the relative Moser theorems -/

variable [I.Boundaryless]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **Moser's contraction identity in coordinates.** In the preferred chart at `x`, at a chart
coordinate `z` over which `ρ = 1`, the coordinate expressions of the slice `σ_t` and of the Moser
field `X_t` satisfy `σ_t (X_t, w) = -c'(t) β(w)`. -/
private theorem inChartAt_apply_mpullbackWithin_moserField {σ₀ σ₁ : SmoothTwoForm I M}
    {β : SmoothForm I M ℝ 1} {ρ : M → ℝ}
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    (t : ℝ) {x : M} {z : E} (hz : z ∈ (extChartAt I x).target)
    (hρz : ρ ((extChartAt I x).symm z) = 1) (w : E) :
    RoughForm.inChartAt (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).1 x z
        ![VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
          (moserField σ₀ σ₁ β ρ t) (range I) z, w] =
      -deriv Real.smoothTransition t * RoughForm.inChartAt β.1 x z ![w] := by
  set A := mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) z with hA
  -- The tangent spaces of the model space are the model space itself.
  set V : E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
    (moserField σ₀ σ₁ β ρ t) (range I) z
  have hAV : A V = moserField σ₀ σ₁ β ρ t ((extChartAt I x).symm z) :=
    (isInvertible_mfderivWithin_extChartAt_symm hz).self_apply_inverse _
  -- Off the chart, `ι_{X_t} σ_t = -c'(t) β` where `ρ = 1`.
  have hι := interior_moserField β ρ (hinv t _ (subset_tsupport ρ
    (show (extChartAt I x).symm z ∈ Function.support ρ by
      rw [Function.mem_support, hρz]; exact one_ne_zero)))
  rw [hρz, one_mul, interior_apply_eq_ofSubsingleton_flat] at hι
  have h := congrArg (fun φ ↦ φ ![A w]) hι
  simp only [ContinuousAlternatingMap.ofSubsingleton_apply_apply, Matrix.cons_val_fin_one,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  -- In the chart, both forms are evaluated on the images of the vectors under `A`.
  rw [RoughForm.inChartAt_apply, RoughForm.inChartAt_apply, ← hA]
  have hl : (fun i ↦ A (![V, w] i)) = ![A V, A w] := by
    funext i
    fin_cases i <;> rfl
  have hr : (fun i ↦ A (![w] i)) = ![A w] := by
    funext i
    fin_cases i
    rfl
  rw [hl, hr, hAV, ← h, flat_apply, SmoothBundleForm.eval₂_apply]

omit [FiniteDimensional ℝ E] in
/-- **The Moser field has zero first jet where the primitive does.** Let `x` be a point near which
`ρ = 1`, at which `β` vanishes and its coordinate expression in the preferred chart has zero
derivative. Then the Moser field `X_t`, read in the preferred chart at `x`, has zero derivative at
the chart point. Indeed, near the chart point the coordinate expressions satisfy
`σ_t (X_t, ·) = -c'(t) β`, and the flat map of `σ_t` has a bounded inverse there, so `X_t` is
bounded by a multiple of `β`, which vanishes to first order. -/
private theorem fderiv_mpullbackWithin_moserField_eq_zero {σ₀ σ₁ : SmoothTwoForm I M}
    {β : SmoothForm I M ℝ 1} {ρ : M → ℝ}
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    (t : ℝ) {x : M} (hρ : ∀ᶠ y in 𝓝 x, ρ y = 1) (hβ : β.1 x = 0)
    (hβ' : HasFDerivAt (RoughForm.inChartAt β.1 x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
      (extChartAt I x x)) :
    fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
      (moserField σ₀ σ₁ β ρ t) (range I)) (extChartAt I x x) = 0 := by
  set σ := σ₀ + Real.smoothTransition t • (σ₁ - σ₀)
  set c := -deriv Real.smoothTransition t
  set z₀ := extChartAt I x x
  -- The tangent spaces of the model space are the model space itself.
  set V' : E → E := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm
    (moserField σ₀ σ₁ β ρ t) (range I)
  set B : E → E →L[ℝ] E →L[ℝ] ℝ := fun z ↦
    ContinuousAlternatingMap.flatL ℝ E ℝ (RoughForm.inChartAt σ.1 x z)
  -- In coordinates, the flat map of `σ_t` is continuous, and invertible at the chart point.
  have hBc : ContinuousAt B z₀ := by
    have h := σ.isSmoothForm.contDiffWithinAt_inChartAt_self x
    rw [I.range_eq_univ, contDiffWithinAt_univ] at h
    exact (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.continuousAt.comp h.continuousAt
  obtain ⟨e, he⟩ := hinv t x (subset_tsupport _ (by simp [hρ.self_of_nhds]))
  -- The tangent space at `x` is the model space `E`.
  let e' : E ≃L[ℝ] (E →L[ℝ] ℝ) := e
  have hB₀ : B z₀ = e' := by
    rw [show (e' : E →L[ℝ] E →L[ℝ] ℝ) = σ.flat x from he]
    simp only [B, z₀, RoughForm.inChartAt_extChartAt_self, flat_def]
  -- So near the chart point `‖v‖ ≤ C ‖B z v‖`.
  have hlower := hBc.eventually_forall_norm_le_mul_norm_apply e' hB₀
  -- Near the chart point, `σ_t (V' z, w) = c β(w)` in coordinates, by Moser's equation.
  have hsym : Tendsto (extChartAt I x).symm (𝓝 z₀) (𝓝 x) := by
    simpa only [z₀, extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  have hkey : ∀ᶠ z in 𝓝 z₀, ∀ w, B z (V' z) w = c * RoughForm.inChartAt β.1 x z ![w] := by
    filter_upwards [extChartAt_target_mem_nhds (I := I) x, hsym.eventually hρ] with z hz hρz w
    rw [ContinuousAlternatingMap.flatL_apply_apply]
    exact inChartAt_apply_mpullbackWithin_moserField hinv t hz hρz w
  -- Hence `‖X_t‖ ≤ C |c| ‖β‖` near the chart point, in coordinates.
  have hfun : ∀ᶠ z in 𝓝 z₀, ‖B z (V' z)‖ ≤ |c| * ‖RoughForm.inChartAt β.1 x z‖ := by
    filter_upwards [hkey] with z hz
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [hz w, norm_mul, Real.norm_eq_abs, mul_assoc]
    gcongr
    simpa using (RoughForm.inChartAt β.1 x z).le_opNorm ![w]
  have hb₀ : RoughForm.inChartAt β.1 x z₀ = 0 := by
    rw [RoughForm.inChartAt_extChartAt_self, hβ]
    rfl
  refine (Asymptotics.IsBigO.hasFDerivAt_zero ?_ hβ' hb₀).fderiv
  refine Asymptotics.IsBigO.of_bound (2 * ‖(e'.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * |c|) ?_
  filter_upwards [hlower, hfun] with z h1 h2
  calc ‖V' z‖ ≤ 2 * ‖(e'.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * ‖B z (V' z)‖ := h1 _
    _ ≤ 2 * ‖(e'.symm : (E →L[ℝ] ℝ) →L[ℝ] E)‖ * (|c| * ‖RoughForm.inChartAt β.1 x z‖) := by
      gcongr
    _ = _ := by ring

/-- **Moser's equation for the cut-off Moser field.** Near a point around which `ρ = 1`, the rate
`∂_t σ_t + L_{X_t} σ_t` of the Moser family vanishes: `∂_t σ_t = c'(t) dβ`, while Cartan's formula
gives `L_{X_t} σ_t = d (ι_{X_t} σ_t) = -c'(t) dβ`. -/
private theorem moserRate_eq_zero {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    {β : SmoothForm I M ℝ 1} (hβ : mextDeriv β.1 = (σ₁ - σ₀).1) {ρ : M → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ)
    (hinv : ∀ t, ∀ x ∈ tsupport ρ,
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible)
    (t : ℝ) {y : M} (hy : ∀ᶠ z in 𝓝 y, ρ z = 1) :
    (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
        (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) (moserFamily σ₀ σ₁).1) +
      mlieDerivForm (moserField σ₀ σ₁ β ρ t)
        (mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (moserFamily σ₀ σ₁).1)) y = 0 := by
  -- The slices `σ₀ + c(u) (σ₁ - σ₀)` have velocity `c'(t) (σ₁ - σ₀)`.
  have hvel : mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (mlieDerivForm (fun _ ↦ ((1 : ℝ), (0 : E))) (moserFamily σ₀ σ₁).1) y =
      deriv Real.smoothTransition t • (σ₁ - σ₀).1 y := by
    have h := (moserFamily σ₀ σ₁).hasDerivAt_mpullback_prodMk_timeDeriv t y
    simp only [mpullback_prodMk_moserFamily, SmoothForm.coe_mpullback,
      SmoothForm.coe_timeDeriv] at h
    refine h.unique ?_
    have hc : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition t) t :=
      ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero t).hasDerivAt
    -- The values of the slices are read in the model fibre `E [⋀^Fin 2]→L[ℝ] ℝ`.
    have h2 : HasDerivAt (F := E [⋀^Fin 2]→L[ℝ] ℝ)
        (fun u ↦ (σ₀.1 y : E [⋀^Fin 2]→L[ℝ] ℝ) +
          Real.smoothTransition u • ((σ₁ - σ₀).1 y : E [⋀^Fin 2]→L[ℝ] ℝ))
        (deriv Real.smoothTransition t • ((σ₁ - σ₀).1 y : E [⋀^Fin 2]→L[ℝ] ℝ)) t :=
      (hc.smul_const _).const_add _
    exact h2
  -- The slice at time `t` is closed, since `σ₁ - σ₀ = dβ` is exact.
  have hclosed : (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).IsClosed := by
    refine h₀.add (SmoothForm.IsClosed.smul _ ?_)
    rw [SmoothForm.isClosed_def, ← hβ]
    exact SmoothForm.mextDeriv_mextDeriv β
  have hXt : MDifferentiableAt I I.tangent
      (fun z ↦ (⟨z, moserField σ₀ σ₁ β ρ t z⟩ : TangentBundle I M)) y :=
    ((contMDiff_moserField β hρ hinv).comp (contMDiff_const.prodMk contMDiff_id)
      |>.mdifferentiableAt (by simp))
  -- Near `y` the contraction `ι_{X_t} σ_t` is `-c'(t) β`, whose exterior derivative is
  -- `-c'(t) (σ₁ - σ₀)`.
  have hL : mlieDerivForm (moserField σ₀ σ₁ β ρ t)
      (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).1 y =
        -deriv Real.smoothTransition t • (σ₁ - σ₀).1 y := by
    rw [mlieDerivForm_eq_mextDeriv_interior_apply (SmoothForm.mdifferentiableAt _ y) hXt
      (congrFun ((SmoothForm.isClosed_def _).1 hclosed) y)]
    have hev : ∀ᶠ z in 𝓝 y, RoughForm.interior (moserField σ₀ σ₁ β ρ t)
        (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).1 z =
          (-deriv Real.smoothTransition t • β.1) z := by
      filter_upwards [hy] with z hz
      have hz' : z ∈ tsupport ρ := subset_tsupport _ (by simp [hz])
      rw [interior_moserField β ρ (hinv t z hz'), hz, one_mul, Pi.smul_apply]
    rw [mextDeriv_congr_of_eventuallyEq hev, mextDeriv_smul, hβ, Pi.smul_apply]
  rw [Pi.add_apply, hvel, mpullback_prodMk_moserFamily_coe, hL, neg_smul, add_neg_cancel]

variable [T2Space M]

/-- **Moser's theorem relative to a compact set, with a given primitive.** Let `σ₀`, `σ₁` be
two-forms on a boundaryless manifold, with `σ₀` closed and `σ₁ - σ₀ = dβ` for a smooth one-form
`β`. Let `K` be a compact set along which `β` vanishes and along which the path
`σ₀ + s (σ₁ - σ₀)`, `s ∈ [0, 1]`, stays nondegenerate. Then there is a diffeomorphism `Φ` of the
manifold which fixes every point of `K`, moves only the points of a compact set, and pulls `σ₁`
back to `σ₀` on a neighbourhood of `K`. At every point `x` of `K` at which `β` has zero first jet,
in the sense that its coordinate expression in the preferred chart at `x` has zero derivative at
the chart point, the differential of `Φ` is the identity. -/
theorem exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub
    {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1}
    (hβ : mextDeriv β.1 = (σ₁ - σ₀).1)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ x ∈ K, β.1 x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧
      (∀ x ∈ K, HasFDerivAt (RoughForm.inChartAt β.1 x) (0 : E →L[ℝ] E [⋀^Fin 1]→L[ℝ] ℝ)
        (extChartAt I x x) → mfderiv I I Φ x = ContinuousLinearMap.id ℝ (TangentSpace I x)) ∧
      (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      ∀ᶠ x in 𝓝ˢ K, (SmoothForm.mpullback Φ Φ.contMDiff σ₁).1 x = σ₀.1 x := by
  -- Cut the Moser field off outside a neighbourhood of `K` on which the path stays nondegenerate.
  obtain ⟨N, hN, hKN, hinvN⟩ := exists_isOpen_isInvertible_flat hK hnd
  obtain ⟨ρ, hρ, hρ1, hρc, hρN, -⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I hN hKN
  have hinv (t : ℝ) (x : M) (hx : x ∈ tsupport ρ) :
      ((σ₀ + Real.smoothTransition t • (σ₁ - σ₀)).flat x).IsInvertible :=
    hinvN t x (hρN hx)
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
  set V := {y : M | ∀ᶠ z in 𝓝 y, ρ z = 1}
  have hKV : K ⊆ V := fun x hx ↦ (eventually_nhdsSet_iff_forall.1 hρ1) x hx
  refine ⟨Φ, fun x hx ↦ ?_, fun x hx hβx ↦ ?_, ⟨tsupport ρ, hρc, fun x hx ↦ ?_⟩, ?_⟩
  · rw [hΦ]
    exact hzero x (moserField_eq_zero ρ (hβK x hx)) 0 1
  · -- The Moser field has zero first jet at `x`, so its flow fixes `x` to first order.
    rw [hΦ]
    exact mfderiv_timeDependentFlowOf_eq_id_of_forall_eq_zero (hX.of_le (by simp))
      (moserField_eq_zero ρ (hβK x hx))
      fun u _ ↦ fderiv_mpullbackWithin_moserField_eq_zero hinv u (hKV hx) (hβK x hx) hβx
  · rw [hΦ]
    exact hzero x (fun u ↦ hXρ u x hx) 0 1
  -- The trajectories starting near `K` stay, up to time `1`, where `ρ = 1` near each point.
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
    fun t ht ↦ moserRate_eq_zero h₀ hβ hρ hinv t
      (huW (mk_mem_prod (hu ((uIcc_of_le (zero_le_one' ℝ)).subset ht)) hx))
  rw [mpullback_prodMk_moserFamily_coe, mpullback_prodMk_moserFamily_coe,
    Real.smoothTransition.one, Real.smoothTransition.zero, one_smul, zero_smul,
    add_zero, add_sub_cancel] at h
  rw [SmoothForm.coe_mpullback, hΦ]
  exact h

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- At a point where `σ₁` and `σ₀` agree, every form `σ₀ + s (σ₁ - σ₀)` of the linear path
between them is `σ₀`. -/
private theorem bilinFormAt_add_smul_sub_of_eq {σ₀ σ₁ : SmoothTwoForm I M} (s : ℝ) {x : M}
    (h : σ₁.1 x = σ₀.1 x) : (σ₀ + s • (σ₁ - σ₀)).bilinFormAt x = σ₀.bilinFormAt x := by
  ext v w
  simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
    SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply,
    AddSubgroupClass.coe_sub, Pi.sub_apply, h, sub_self, smul_zero, add_zero]

/-- **The relative Moser theorem.** Let `σ₀`, `σ₁` be closed two-forms on a boundaryless
second-countable Hausdorff manifold `M` which agree, as bilinear forms on the full tangent spaces of
`M`, at every point of a compact embedded submanifold `f : Q → M`, and let `σ₀` be nondegenerate
along it. Then there is a diffeomorphism `Φ` of `M` which fixes every point of `f(Q)`, has
differential the identity at every point of `f(Q)`, moves only the points of a compact set, and
pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. -/
theorem exists_diffeomorph_fix_embedding_eventually_mpullback_eq [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.1 (f q) = σ₀.1 (f q)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧
      (∀ q, mfderiv I I Φ (f q) = ContinuousLinearMap.id ℝ (TangentSpace I (f q))) ∧
      (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      ∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).1 x = σ₀.1 x := by
  have hη (q : Q) : (σ₁ - σ₀).1 (f q) = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, heq q, sub_self]
  -- The relative Poincaré lemma gives a primitive of `σ₁ - σ₀` on a tubular neighbourhood `W` of
  -- `f(Q)`, vanishing along `f(Q)` with zero first jet, since `σ₁ - σ₀` vanishes there.
  obtain ⟨W, -, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := ℝ) isOpen_univ
    (subset_univ _)
  obtain ⟨βW, hβW, hdβW, hβW0, hβW1⟩ := hprim (k := 1) (r := ⊤) le_top (σ₁ - σ₀).isSmoothForm
    ((SmoothForm.isClosed_def _).1 (h₁.sub h₀)) (funext fun q ↦ by
      ext v
      simp only [mpullback_apply, hη q, ContinuousAlternatingMap.coe_zero, Pi.zero_apply])
  -- Moser's argument runs on the open submanifold `W`, with the restricted forms.
  let res := SmoothForm.mpullback (I := I) (I' := I) (F := ℝ) (k := 2) (Subtype.val : W → M)
    contMDiff_subtype_val
  let g : Q → W := fun q ↦ ⟨f q, hfW (mem_range_self q)⟩
  have hgK : IsCompact (range g) :=
    isCompact_range (f.contMDiff.continuous.subtype_mk fun q ↦ hfW (mem_range_self q))
  obtain ⟨Ψ, hΨK, hΨ1, ⟨C, hC, hΨC⟩, hΨ⟩ :=
    exists_diffeomorph_fix_eventually_mpullback_eq_of_mextDeriv_eq_sub (σ₀ := res σ₀)
      (σ₁ := res σ₁) (h₀.mpullback _ _) (β := ⟨βW, hβW.mem_smoothBundleForms⟩)
    (by rw [hdβW, ← map_sub]; exact (SmoothForm.coe_mpullback _ _ _).symm) hgK
    (by rintro _ ⟨q, rfl⟩; exact hβW0 q)
    (by
      rintro _ ⟨q, rfl⟩ s -
      rw [← map_sub, ← map_smul, ← map_add]
      exact (nondegenerate_bilinFormAt_mpullback_subtype_val_iff (g q)).2
        (bilinFormAt_add_smul_sub_of_eq s (heq q) ▸ hnd q))
  -- Extend the compactly supported diffeomorphism of `W` by the identity.
  obtain ⟨Φ, hΦW, hΦC⟩ := Ψ.exists_extend_of_isCompact hC hΨC
  have hcomp : ⇑Φ ∘ (Subtype.val : W → M) = Subtype.val ∘ ⇑Ψ := funext hΦW
  refine ⟨Φ, fun q ↦ ?_, fun q ↦ ?_, ⟨Subtype.val '' C, hC.image continuous_subtype_val, hΦC⟩,
    ?_⟩
  · -- The point `g q` of `W` lies over `f q`.
    exact (hΦW (g q)).trans (congrArg Subtype.val (hΨK _ (mem_range_self q)))
  · -- On `W`, `Φ` is `Ψ`, whose differential at `g q` is the identity.
    exact ContinuousLinearMap.ext fun v ↦
      (Manifold.mfderiv_apply_of_comp_subtype_val_eq hcomp (g q) v).symm.trans
        (DFunLike.congr_fun (hΨ1 (g q) (mem_range_self q) (hβW1 q (hη q))) v)
  -- On `W`, the pullback by `Φ` is the pullback by `Ψ` of the restricted forms.
  obtain ⟨U, ⟨hU, hKU⟩, hUΨ⟩ := (hasBasis_nhdsSet (range g)).mem_iff.1 hΨ
  refine mem_of_superset ((W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU).mem_nhdsSet.2 ?_)
    ?_
  · rintro _ ⟨q, rfl⟩
    exact ⟨g q, hKU (mem_range_self q), rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_ofPred_eq, ← SmoothForm.coe_mpullback_subtype_val_apply,
      SmoothForm.mpullback_mpullback_of_comp_eq _ _ Ψ.contMDiff contMDiff_subtype_val hcomp]
    exact (hUΨ hz).trans (SmoothForm.coe_mpullback_subtype_val_apply σ₀ z)

open TopologicalSpace in
/-- **The relative Moser theorem between neighbourhoods** (Cannas da Silva, Theorem 7.4). Let `σ₀`,
`σ₁` be closed two-forms on a boundaryless second-countable Hausdorff manifold `M` which agree, as
bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded submanifold
`f : Q → M`, and let `σ₀` be nondegenerate along it. Then there are open neighbourhoods `U₀`, `U₁`
of `f(Q)` and a diffeomorphism `φ : U₀ → U₁` which fixes every point of `f(Q)`, with differential
the identity there, and pulls the restriction of `σ₁` to `U₁` back to the restriction of `σ₀` to
`U₀`. -/
theorem exists_diffeomorph_opens_of_eq_along [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.1 (f q) = σ₀.1 (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q ∧
        mfderiv I I φ ⟨f q, h⟩ = ContinuousLinearMap.id ℝ (TangentSpace I (⟨f q, h⟩ : U₀))) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtype_val σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtype_val σ₀ := by
  obtain ⟨Φ, hΦf, hΦ1, -, hΦ⟩ :=
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
  · -- The restriction `φ` of `Φ` has the differential of `Φ`, the identity along `f(Q)`.
    ext v
    exact (Manifold.mfderiv_apply_of_comp_subtype_val_eq
      (funext fun x ↦ (Φ.subtype_apply_coe hU₀₁ x).symm) _ v).trans
        (DFunLike.congr_fun (hΦ1 q) v)
  apply Subtype.ext
  funext z
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtype_val Φ.contMDiff
    (funext (Φ.subtype_apply_coe hU₀₁)), SmoothForm.coe_mpullback_subtype_val_apply,
    SmoothForm.coe_mpullback_subtype_val_apply]
  exact hUΦ z.2

end TauCeti.SmoothTwoForm
