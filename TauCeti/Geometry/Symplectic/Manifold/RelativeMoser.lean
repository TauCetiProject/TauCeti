/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Manifold.Flat
public import TauCeti.Geometry.Manifold.TubularNeighborhood.RelativePoincare
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.Family
import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.Diffeomorph.Extend
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Symplectic.Manifold.Opens

/-!
# The relative Moser theorem

Let `σ₀`, `σ₁` be closed two-forms on a boundaryless Hausdorff second-countable manifold `M` which
agree, as bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded
submanifold `f : Q → M`, with `σ₀` nondegenerate along `f(Q)`. The **relative Moser theorem**
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_mpullback_eq`) gives a diffeomorphism `Φ`
of `M` which fixes every point of `f(Q)`, moves only the points of a compact set, and pulls `σ₁`
back to `σ₀` on a neighbourhood of `f(Q)`. Restricted to such a neighbourhood `U`, it is a
diffeomorphism from `U` onto the open set `Φ(U)` which fixes `f(Q)` pointwise and carries `σ₀` on
`U` to `σ₁` on `Φ(U)` (`TauCeti.SmoothTwoForm.exists_diffeomorph_opens_of_eq_along`). Only the
agreement of the full ambient forms along `f(Q)` is used; agreement of their pullbacks to `Q` is a
weaker condition.

The proof is Moser's argument relative to a compact set
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_mpullback_eq_of_mextDeriv_eq_sub`). Suppose
`σ₁ - σ₀ = dβ` for a smooth one-form `β` which vanishes on a compact set `K`, and the path
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
constant (`TauCeti.mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_Icc`).
So `Φ = φ_{0,1}` pulls `σ₁` back to `σ₀` near `K`.

For the submanifold version, the relative Poincaré lemma
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`) writes `σ₁ - σ₀`, whose
pullback along `f` vanishes, as `dβ` on a tubular neighbourhood `W` of `f(Q)`, with `β` vanishing
along `f(Q)`. Moser's argument on the open submanifold `W` gives a compactly supported
diffeomorphism of `W`, which extends by the identity to `M`.

## Main results

* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_mpullback_eq_of_mextDeriv_eq_sub`: Moser's theorem
  relative to a compact set along which a given primitive of `σ₁ - σ₀` vanishes.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_mpullback_eq`: the relative Moser theorem
  for closed two-forms agreeing along a compact embedded submanifold.
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
  have hι : MDifferentiable I (𝓘(ℝ, ℝ).prod I) (Prod.mk t : M → ℝ × M) :=
    (contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ _).mdifferentiable
      (by simp)
  have hsnd : MDifferentiable (𝓘(ℝ, ℝ).prod I) I (Prod.snd : ℝ × M → M) :=
    contMDiff_snd.mdifferentiable (n := ∞) (by simp)
  have hcomp (τ : SmoothTwoForm I M) : TauCeti.mpullback I (𝓘(ℝ, ℝ).prod I) (Prod.mk t)
      (TauCeti.mpullback (𝓘(ℝ, ℝ).prod I) I Prod.snd τ.1) = τ.1 := by
    rw [← mpullback_comp hι hsnd]
    exact mpullback_id τ.1
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

/-- Restricting a smooth form to an open subset does not change its values. -/
private theorem coe_mpullback_subtype_val_apply {k : ℕ} {U : TopologicalSpace.Opens M}
    (σ : SmoothForm I M ℝ k) (z : U) :
    (SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val σ).1 z = σ.1 z :=
  (congrFun (SmoothForm.coe_mpullback _ _ σ) z).trans (mpullback_subtype_val_apply σ.1 z)

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
back to `σ₀` on a neighbourhood of `K`. -/
theorem exists_diffeomorph_fix_mpullback_eq_of_mextDeriv_eq_sub {σ₀ σ₁ : SmoothTwoForm I M}
    (h₀ : σ₀.IsClosed) {β : SmoothForm I M ℝ 1} (hβ : mextDeriv β.1 = (σ₁ - σ₀).1)
    {K : Set M} (hK : IsCompact K) (hβK : ∀ x ∈ K, β.1 x = 0)
    (hnd : ∀ x ∈ K, ∀ s ∈ Icc (0 : ℝ) 1, ((σ₀ + s • (σ₁ - σ₀)).bilinFormAt x).Nondegenerate) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ x ∈ K, Φ x = x) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
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
  refine ⟨Φ, fun x hx ↦ ?_, ⟨tsupport ρ, hρc, fun x hx ↦ ?_⟩, ?_⟩
  · rw [hΦ]
    exact hzero x (moserField_eq_zero ρ (hβK x hx)) 0 1
  · rw [hΦ]
    exact hzero x (fun u ↦ hXρ u x hx) 0 1
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
  have h := mpullback_timeDependentFlowOf_mpullback_prodMk_apply_eq_of_forall_mem_Icc
    (hX.of_le (by simp)) hc ((moserFamily σ₀ σ₁).contMDiff.of_le (by simp)) zero_le_one x
    fun t ht ↦ moserRate_eq_zero h₀ hβ hρ hinv t (huW (mk_mem_prod (hu ht) hx))
  rw [mpullback_prodMk_moserFamily_coe, mpullback_prodMk_moserFamily_coe,
    Real.smoothTransition.one, Real.smoothTransition.zero, one_smul, zero_smul,
    add_zero, add_sub_cancel] at h
  rw [SmoothForm.coe_mpullback, hΦ]
  exact h

/-- **The relative Moser theorem.** Let `σ₀`, `σ₁` be closed two-forms on a boundaryless
second-countable Hausdorff manifold `M` which agree, as bilinear forms on the full tangent spaces of
`M`, at every point of a compact embedded submanifold `f : Q → M`, and let `σ₀` be nondegenerate
along it. Then there is a diffeomorphism `Φ` of `M` which fixes every point of `f(Q)`, moves only
the points of a compact set, and pulls `σ₁` back to `σ₀` on a neighbourhood of `f(Q)`. -/
theorem exists_diffeomorph_fix_embedding_mpullback_eq [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.1 (f q) = σ₀.1 (f q)) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, (∀ q, Φ (f q) = f q) ∧ (∃ C, IsCompact C ∧ ∀ x ∉ C, Φ x = x) ∧
      ∀ᶠ x in 𝓝ˢ (range f), (SmoothForm.mpullback Φ Φ.contMDiff σ₁).1 x = σ₀.1 x := by
  have hη (q : Q) : (σ₁ - σ₀).1 (f q) = 0 := by
    rw [AddSubgroupClass.coe_sub, Pi.sub_apply, heq q, sub_self]
  -- The relative Poincaré lemma gives a primitive of `σ₁ - σ₀` on a tubular neighbourhood `W` of
  -- `f(Q)`, vanishing along `f(Q)`.
  obtain ⟨W, -, hfW, hprim⟩ := f.exists_isSmoothForm_relative_primitive (F := ℝ) isOpen_univ
    (subset_univ _)
  obtain ⟨βW, hβW, hdβW, hβW0⟩ := hprim (k := 1) (r := ⊤) le_top (σ₁ - σ₀).isSmoothForm
    ((SmoothForm.isClosed_def _).1 (h₁.sub h₀)) (funext fun q ↦ by
      ext v
      simp only [mpullback_apply, hη q, ContinuousAlternatingMap.coe_zero, Pi.zero_apply])
  -- Moser's argument runs on the open submanifold `W`, with the restricted forms.
  let res := SmoothForm.mpullback (I := I) (I' := I) (F := ℝ) (k := 2) (Subtype.val : W → M)
    contMDiff_subtype_val
  let g : Q → W := fun q ↦ ⟨f q, hfW (mem_range_self q)⟩
  have hgK : IsCompact (range g) :=
    isCompact_range (f.contMDiff.continuous.subtype_mk fun q ↦ hfW (mem_range_self q))
  obtain ⟨Ψ, hΨK, ⟨C, hC, hΨC⟩, hΨ⟩ := exists_diffeomorph_fix_mpullback_eq_of_mextDeriv_eq_sub
    (σ₀ := res σ₀) (σ₁ := res σ₁) (h₀.mpullback _ _) (β := ⟨βW, hβW.mem_smoothBundleForms⟩)
    (by rw [hdβW, ← map_sub]; exact (SmoothForm.coe_mpullback _ _ _).symm) hgK
    (by rintro _ ⟨q, rfl⟩; exact hβW0 q)
    (by
      rintro _ ⟨q, rfl⟩ s -
      rw [← map_sub, ← map_smul, ← map_add]
      refine (nondegenerate_bilinFormAt_mpullback_subtype_val_iff (g q)).2 ?_
      -- Along `f(Q)` the path is constantly `σ₀`.
      have hb : (σ₀ + s • (σ₁ - σ₀)).bilinFormAt (f q) = σ₀.bilinFormAt (f q) := by
        ext v w
        simp only [SmoothForm.bilinFormAt_apply, SmoothBundleForm.eval₂_apply,
          SmoothForm.add_toRoughForm, Pi.add_apply, SetLike.val_smul, Pi.smul_apply, hη q,
          smul_zero, add_zero]
      exact hb ▸ hnd q)
  -- Extend the compactly supported diffeomorphism of `W` by the identity.
  obtain ⟨Φ, hΦW, hΦC⟩ := isLocalDiffeomorph_subtype_val.exists_diffeomorph_extend_of_isCompact
    W.isOpen.isOpenEmbedding_subtypeVal Ψ hC hΨC
  have hcomp : ⇑Φ ∘ (Subtype.val : W → M) = Subtype.val ∘ ⇑Ψ := funext hΦW
  refine ⟨Φ, fun q ↦ ?_, ⟨Subtype.val '' C, hC.image continuous_subtype_val, hΦC⟩, ?_⟩
  · rw [show f q = (g q : M) from rfl, hΦW, hΨK _ (mem_range_self q)]
  -- On `W`, the pullback by `Φ` is the pullback by `Ψ` of the restricted forms.
  obtain ⟨U, ⟨hU, hKU⟩, hUΨ⟩ := (hasBasis_nhdsSet (range g)).mem_iff.1 hΨ
  refine mem_of_superset ((W.isOpen.isOpenEmbedding_subtypeVal.isOpenMap U hU).mem_nhdsSet.2 ?_)
    ?_
  · rintro _ ⟨q, rfl⟩
    exact ⟨g q, hKU (mem_range_self q), rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [mem_ofPred_eq, ← coe_mpullback_subtype_val_apply,
      SmoothForm.mpullback_mpullback_of_comp_eq _ _ Ψ.contMDiff contMDiff_subtype_val hcomp]
    exact (hUΨ hz).trans (coe_mpullback_subtype_val_apply σ₀ z)

open TopologicalSpace in
/-- **The relative Moser theorem between neighbourhoods** (Cannas da Silva, Theorem 7.4). Let `σ₀`,
`σ₁` be closed two-forms on a boundaryless second-countable Hausdorff manifold `M` which agree, as
bilinear forms on the full tangent spaces of `M`, at every point of a compact embedded submanifold
`f : Q → M`, and let `σ₀` be nondegenerate along it. Then there are open neighbourhoods `U₀`, `U₁`
of `f(Q)` and a diffeomorphism `φ : U₀ → U₁` which fixes every point of `f(Q)` and pulls the
restriction of `σ₁` to `U₁` back to the restriction of `σ₀` to `U₀`. -/
theorem exists_diffeomorph_opens_of_eq_along [SecondCountableTopology M]
    {E' H' Q : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
    [TopologicalSpace Q] [ChartedSpace H' Q] [IsManifold J ∞ Q] [CompactSpace Q]
    (f : SmoothEmbedding J I ∞ Q M) {σ₀ σ₁ : SmoothTwoForm I M} (h₀ : σ₀.IsClosed)
    (h₁ : σ₁.IsClosed) (hnd : ∀ q, (σ₀.bilinFormAt (f q)).Nondegenerate)
    (heq : ∀ q, σ₁.1 (f q) = σ₀.1 (f q)) :
    ∃ (U₀ U₁ : Opens M) (φ : U₀ ≃ₘ⟮I, I⟯ U₁),
      (∀ q, ∃ h : f q ∈ U₀, (φ ⟨f q, h⟩ : M) = f q) ∧
      SmoothForm.mpullback φ φ.contMDiff
          (SmoothForm.mpullback (Subtype.val : U₁ → M) contMDiff_subtype_val σ₁) =
        SmoothForm.mpullback (Subtype.val : U₀ → M) contMDiff_subtype_val σ₀ := by
  obtain ⟨Φ, hΦf, -, hΦ⟩ := exists_diffeomorph_fix_embedding_mpullback_eq f h₀ h₁ hnd heq
  -- Restrict `Φ` to an open neighbourhood `U` of `f(Q)` on which it pulls `σ₁` back to `σ₀`, and
  -- to its image `Φ(U)`, the preimage of `U` under `Φ⁻¹`.
  obtain ⟨U, ⟨hU, hfU⟩, hUΦ⟩ := (hasBasis_nhdsSet (range f)).mem_iff.1 hΦ
  let U₀ : Opens M := ⟨U, hU⟩
  let U₁ : Opens M := ⟨Φ.symm ⁻¹' U, hU.preimage Φ.symm.continuous⟩
  have hU₀₁ (x : M) : x ∈ U₀ ↔ Φ x ∈ U₁ := by
    simp [U₀, U₁]
  refine ⟨U₀, U₁, Φ.subtype hU₀₁, fun q ↦
    ⟨hfU (mem_range_self q), (Φ.subtype_apply_coe hU₀₁ _).trans (hΦf q)⟩, ?_⟩
  apply Subtype.ext
  funext z
  rw [SmoothForm.mpullback_mpullback_of_comp_eq _ _ contMDiff_subtype_val Φ.contMDiff
    (funext (Φ.subtype_apply_coe hU₀₁)), coe_mpullback_subtype_val_apply,
    coe_mpullback_subtype_val_apply]
  exact hUΦ z.2

end TauCeti.SmoothTwoForm
