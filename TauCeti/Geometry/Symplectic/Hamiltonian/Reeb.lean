/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Pullback
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.Transform
import TauCeti.Geometry.Contact.Flat
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Reparam
import TauCeti.Topology.VectorBundle.Smul

/-!
# Reeb fields of energy hypersurfaces

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M`, let `θ` be a one-form
with `dθ = -σ`, and let `ι : S → M` be a hypersurface on which a function `K` is constant, in the
sense that the tangent image of `ι` at `s` is exactly the kernel of `dK`. If the restriction
`ι^* θ` is a contact form, then its Reeb vector field is a rescaling of the Hamiltonian vector
field `X_K` of `K`:

`dι (R_(ι^* θ)) = θ(X_K)⁻¹ • X_K`

(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`); the contact
condition forces `θ(X_K)` not to vanish
(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_ne_zero`). Indeed `X_K` is
tangent to the level, since `dK(X_K) = σ(X_K, X_K) = 0`, and for every vector `w` tangent to the
level, `dθ(X_K, w) = -σ(X_K, w) = -dK(w) = 0`. So the lift of `X_K / θ(X_K)` satisfies the two
Reeb equations, which determine the Reeb vector field.

This is how Reeb flows on hypersurfaces of contact type are reparametrized Hamiltonian flows: on
the unit cosphere bundle of a Riemannian manifold, with `θ` the Liouville form and `K` the kinetic
energy, the factor `θ(X_K)` is identically `1`, and the Reeb flow is the cogeodesic flow.

Conversely, on a compact hypersurface every closed characteristic is a closed Reeb orbit. If `S`
is compact and `ι` is injective, every periodic integral curve `δ` of `X_K` starting on the image
of `ι` is `ι ∘ γ ∘ ψ` for a periodic integral curve `γ` of the Reeb field and a homeomorphism `ψ`
of `ℝ` fixing `0`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_isMIntegralCurve_reebVectorField_comp_eq`). The
Reeb orbit `γ` through the starting point, run with the time change `ψ' = θ(X_K) ∘ ι ∘ γ ∘ ψ`,
whose factor has a constant sign along `γ` and is bounded on the compact `S`, is carried by `ι`
to an integral curve of `X_K`; uniqueness of integral curves identifies it with `δ`, and since `δ`
closes up and `ι` is injective, so does `γ`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_ne_zero`: on a hypersurface
  of contact type, `θ(X_K)` does not vanish.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`: the Reeb field of
  `ι^* θ` is carried to `X_K / θ(X_K)`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.exists_isMIntegralCurve_reebVectorField_comp_eq`: the
  closed characteristics of a compact hypersurface of contact type are its closed Reeb orbits, up
  to a change of time.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.4 (Reeb vector fields).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {σ : SmoothTwoForm I M}

section EnergyHypersurface

variable [IsManifold J 2 S]

/-- Exterior-derivative identity: if `dθ = -σ` at `x`, then
`dθ(a • X_K, u) = -σ(a • X_K, u) = -a dK(u)`. -/
private theorem mextDeriv_smul_hamiltonianVectorField (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {K : M → ℝ} {x : M} (hdθ : mextDeriv θ.val x = -σ.val x) (a : ℝ)
    (u : TangentSpace I x) :
    mextDeriv θ.val x ![a • σ.hamiltonianVectorField K x, u] = -(a * mvfderiv I K x u) := by
  rw [hdθ, ContinuousAlternatingMap.neg_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothBundleForm.eval₂_smul_left, hσ.eval₂_hamiltonianVectorField, smul_eq_mul]

omit [IsManifold J 2 S] in
/-- The Hamiltonian vector field is tangent to the level, since `dK(X_K) = σ(X_K, X_K) = 0`. -/
private theorem smul_hamiltonianVectorField_mem_range (hσ : σ.IsNondegenerate) {ι : S → M}
    {K : M → ℝ} {s : S} (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) (a : ℝ) :
    a • σ.hamiltonianVectorField K (ι s) ∈ (mfderiv J I ι s).range := by
  rw [hK, LinearMap.mem_ker, map_smul, ContinuousLinearMap.coe_coe,
    (hσ.isHamiltonianVectorField_hamiltonianVectorField K).mvfderiv_apply_self (ι s), smul_zero]

/-- **On a hypersurface of contact type, `θ(X_K)` does not vanish.** Let `σ` be a nondegenerate
two-form and `θ` a one-form with `dθ = -σ` at `ι s`, and suppose that the tangent image of
`ι : S → M` at `s` is the kernel of `dK`. If the restriction `ι^* θ` is a contact form, then
`θ(X_K) ≠ 0` at `ι s`. -/
theorem IsNondegenerate.apply_hamiltonianVectorField_ne_zero (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ} {s : S}
    (hdθ : mextDeriv θ.val (ι s) = -σ.val (ι s))
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    θ.val (ι s) ![σ.hamiltonianVectorField K (ι s)] ≠ 0 := by
  have := SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα s
  have hdK (w : TangentSpace J s) : mvfderiv I K (ι s) (mfderiv J I ι s w) = 0 :=
    (LinearMap.exact_iff.2 hK.symm).apply_apply_eq_zero w
  -- Suppose `θ(X_K) = 0`. A lift `v` of `X_K` lies in `ker α` and is `dα`-orthogonal to
  -- everything, so `v = 0`.
  intro hc
  obtain ⟨v, hv⟩ := smul_hamiltonianVectorField_mem_range hσ hK 1
  rw [one_smul, ContinuousLinearMap.coe_coe] at hv
  have hv0 : v = 0 := by
    refine (SmoothForm.isContactForm_iff.1 hα s).2 v ?_ fun w _ ↦ ?_
    · rw [SmoothForm.mpullback_apply_one, hv, hc]
    · rw [SmoothForm.mextDeriv_mpullback_apply_two, hv,
        ← one_smul ℝ (σ.hamiltonianVectorField K (ι s)),
        mextDeriv_smul_hamiltonianVectorField hσ hdθ, hdK, mul_zero, neg_zero]
  -- Hence `X_K = 0` and `dK = 0`, so `dι` is surjective.
  have hX0 : σ.hamiltonianVectorField K (ι s) = 0 := by rw [← hv, hv0, map_zero]
  have hdK0 : mvfderiv I K (ι s) = 0 := (hσ.hamiltonianVectorField_eq_zero_iff).1 hX0
  have hsurj (u : TangentSpace I (ι s)) : ∃ w, mfderiv J I ι s w = u := by
    have : u ∈ (mfderiv J I ι s).range := by
      rw [hK, hdK0]
      simp
    exact this
  -- Then `dι (R)` is `σ`-orthogonal to everything, so vanishes, contradicting `α(R) = 1`.
  set R := (SmoothForm.mpullback ι hι θ).reebVectorField s
  have hR : mfderiv J I ι s R = 0 := by
    refine (hσ.isInvertible_flat (ι s)).injective ?_
    ext u
    obtain ⟨w, rfl⟩ := hsurj u
    have h2 := hα.mextDeriv_reebVectorField_left s w
    rw [SmoothForm.mextDeriv_mpullback_apply_two, hdθ, ContinuousAlternatingMap.neg_apply,
      ← SmoothBundleForm.eval₂_apply, neg_eq_zero] at h2
    rw [SmoothTwoForm.flat_apply]
    simpa using h2
  have h1 := hα.apply_reebVectorField s
  rw [SmoothForm.mpullback_apply_one, hR, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero] at h1
  exact zero_ne_one h1

/-- **The Reeb field of an energy hypersurface is a rescaled Hamiltonian field.** Let `σ` be a
nondegenerate two-form and `θ` a one-form with `dθ = -σ` at `ι s`, and suppose that the tangent
image of `ι : S → M` at `s` is the kernel of `dK`. If the restriction `ι^* θ` is a contact form,
then `θ(X_K)` does not vanish at `ι s` (`IsNondegenerate.apply_hamiltonianVectorField_ne_zero`),
and the differential of `ι` sends the Reeb vector field of `ι^* θ` to `X_K / θ(X_K)`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback (hσ : σ.IsNondegenerate)
    {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ} {s : S}
    (hdθ : mextDeriv θ.val (ι s) = -σ.val (ι s))
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι θ).reebVectorField s) =
      (θ.val (ι s) ![σ.hamiltonianVectorField K (ι s)])⁻¹ •
        σ.hamiltonianVectorField K (ι s) := by
  have := SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα s
  have hθK := hσ.apply_hamiltonianVectorField_ne_zero hι hα hdθ hK
  have hdK (w : TangentSpace J s) : mvfderiv I K (ι s) (mfderiv J I ι s w) = 0 :=
    (LinearMap.exact_iff.2 hK.symm).apply_apply_eq_zero w
  -- Express `X_K / θ(X_K)` through a lift `v`.
  obtain ⟨v, hv⟩ := smul_hamiltonianVectorField_mem_range hσ hK
    (θ.val (ι s) ![σ.hamiltonianVectorField K (ι s)])⁻¹
  rw [ContinuousLinearMap.coe_coe] at hv
  set X := σ.hamiltonianVectorField K (ι s)
  set c := θ.val (ι s) ![X]
  -- Scalar normalization: `θ(X_K / θ(X_K)) = 1`.
  have hθv : θ.val (ι s) ![c⁻¹ • X] = 1 := by
    rw [← SmoothForm.degreeOneEquiv_coe_apply, map_smul, SmoothForm.degreeOneEquiv_coe_apply,
      smul_eq_mul, inv_mul_cancel₀ hθK]
  -- The lift `v` of `X_K / θ(X_K)` satisfies the two Reeb equations.
  have hR : (SmoothForm.mpullback ι hι θ).reebVectorField s = v :=
    ((hα.eq_reebVectorField_iff).2 ⟨by rw [SmoothForm.mpullback_apply_one, hv, hθv], fun w ↦ by
      rw [SmoothForm.mextDeriv_mpullback_apply_two, hv,
        mextDeriv_smul_hamiltonianVectorField hσ hdθ, hdK, mul_zero, neg_zero]⟩).symm
  rw [hR, hv]

end EnergyHypersurface

/-! ### Closed characteristics of a compact hypersurface of contact type -/

section ClosedOrbit

variable [IsManifold J ∞ S]

/-- Along a hypersurface of contact type, `θ(X_K)` is continuous: its inverse is the factor
relating the continuous sections `dι ∘ R` and `X_K ∘ ι`
(`IsNondegenerate.mfderiv_reebVectorField_mpullback`). -/
private theorem IsNondegenerate.continuous_apply_hamiltonianVectorField [FiniteDimensional ℝ E']
    (hσ : σ.IsNondegenerate) {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι θ).IsContactForm) {K : M → ℝ}
    (hKs : ContMDiff I 𝓘(ℝ) 2 K) (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s))
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    Continuous fun s ↦ θ.val (ι s) ![σ.hamiltonianVectorField K (ι s)] := by
  set X := σ.hamiltonianVectorField K
  set c : S → ℝ := fun s ↦ θ.val (ι s) ![X (ι s)]
  have hc0 (s : S) : c s ≠ 0 := hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ s) (hK s)
  have hXs : ContMDiff I I.tangent 1 (T% X) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by rwa [one_add_one_eq_two])
  have hinv : Continuous fun s ↦ (c s)⁻¹ := continuous_iff_continuousAt.2 fun s ↦
    TauCeti.VectorBundle.continuousAt_of_eventually_eq_smul (φ := fun s ↦ T% X (ι s))
      (ψ := fun s ↦ tangentMap J I ι ⟨s, (SmoothForm.mpullback ι hι θ).reebVectorField s⟩)
      ((hXs.continuous.comp hι.continuous).continuousAt)
      (((hι.continuous_tangentMap (by simp)).comp
        hα.contMDiff_reebVectorField.continuous).continuousAt)
      (Filter.Eventually.of_forall fun s ↦ by
        simp [tangentMap, hσ.mfderiv_reebVectorField_mpullback hι hα (hdθ s) (hK s), X, c])
      fun h ↦ hc0 s <| by
        simp only [c]
        rw [show X (ι s) = 0 from h, ← SmoothForm.degreeOneEquiv_coe_apply, map_zero]
  exact (hinv.inv₀ fun s ↦ inv_ne_zero (hc0 s)).congr fun s ↦ inv_inv (c s)

variable [BoundarylessManifold I M] [T2Space M] [BoundarylessManifold J S] [CompactSpace S]

/-- **Closed characteristics of a compact hypersurface of contact type are closed Reeb orbits.**
Let `σ` be a nondegenerate two-form, `θ` a one-form with `dθ = -σ` along `ι`, and `ι : S → M` an
injective smooth map from a compact manifold whose tangent images are the kernels of `dK`, for a
`C²` function `K`, and along which `ι^* θ` is a contact form. Then every periodic integral curve
`δ` of `X_K`, of nonzero period, starting on the image of `ι` is a closed Reeb orbit of `ι^* θ`
run at another speed: `δ = ι ∘ γ ∘ ψ` for a periodic integral curve `γ` of the Reeb field, of
nonzero period, and a homeomorphism `ψ` of `ℝ` fixing `0`. -/
theorem IsNondegenerate.exists_isMIntegralCurve_reebVectorField_comp_eq
    (hσ : σ.IsNondegenerate) {θ : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hιi : Function.Injective ι) (hα : (SmoothForm.mpullback ι hι θ).IsContactForm)
    {K : M → ℝ} (hKs : ContMDiff I 𝓘(ℝ) 2 K) (hdθ : ∀ s, mextDeriv θ.val (ι s) = -σ.val (ι s))
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) {δ : ℝ → M}
    (hδ : IsMIntegralCurve δ (σ.hamiltonianVectorField K)) (hδ₀ : δ 0 ∈ Set.range ι) {T : ℝ}
    (hT : T ≠ 0) (hper : Function.Periodic δ T) :
    ∃ γ : ℝ → S, IsMIntegralCurve γ (SmoothForm.mpullback ι hι θ).reebVectorField ∧
      (∃ τ, τ ≠ 0 ∧ Function.Periodic γ τ) ∧ ∃ ψ : ℝ ≃ₜ ℝ, ψ 0 = 0 ∧ δ = ι ∘ γ ∘ ψ := by
  have : T2Space S := T2Space.of_injective_continuous hιi hι.continuous
  obtain ⟨s₀, hs₀⟩ := hδ₀
  have := SmoothForm.finiteDimensional_of_isContactForm_mpullback hι hα s₀
  set R := (SmoothForm.mpullback ι hι θ).reebVectorField
  set X := σ.hamiltonianVectorField K
  -- `dι (R s) = c(s)⁻¹ • X_K (ι s)` with `c(s) = θ(X_K)` at `ι s`, continuous and nonvanishing.
  set c : S → ℝ := fun s ↦ θ.val (ι s) ![X (ι s)]
  have hc0 (s : S) : c s ≠ 0 := hσ.apply_hamiltonianVectorField_ne_zero hι hα (hdθ s) (hK s)
  have hcc : Continuous c := hσ.continuous_apply_hamiltonianVectorField hι hα hKs hdθ hK
  have hRs : ContMDiff J J.tangent 1 (T% R) := hα.contMDiff_reebVectorField.of_le (by simp)
  have hXs : ContMDiff I I.tangent 1 (T% X) :=
    hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by rwa [one_add_one_eq_two])
  -- Change the time of the Reeb orbit through `s₀` by `ψ' = c ∘ γ ∘ ψ`, with `|c|` bounded on the
  -- compact `S`: this gives an integral curve of `c • R`, which `ι` carries to `X_K`.
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcc.continuousOn
  obtain ⟨γ, hγ0, hγ⟩ := (isCompleteVectorField_of_compactSpace hRs).exists_isMIntegralCurve hRs s₀
  obtain ⟨ψ, hψ0, hγψ⟩ := hγ.exists_homeomorph_isMIntegralCurve_comp_of_abs_le
    (Y := fun s ↦ c s • R s) (hcc.comp hγ.continuous) (fun t ↦ hc0 _)
    (fun t ↦ by simpa using hC (γ t) trivial) fun t ↦ rfl
  have hιγψ : IsMIntegralCurve (ι ∘ γ ∘ ψ) X := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγψ ⊢
    exact hγψ.map_of_mfderiv_eq (fun t _ ↦ (hι _).mdifferentiableAt (by simp)) fun t _ ↦ by
      rw [map_smul, hσ.mfderiv_reebVectorField_mpullback hι hα (hdθ _) (hK _), smul_smul,
        mul_inv_cancel₀ (hc0 _), one_smul]
  -- By uniqueness of integral curves, it is `δ`.
  have hδeq : δ = ι ∘ γ ∘ ψ := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hXs hδ
    hιγψ (by simp [hψ0, hγ0, hs₀])
  -- Since `δ` closes up and `ι` is injective, so does `γ`.
  have hclose : γ (ψ T) = γ (ψ 0) := hιi <| by
    simpa [hδeq] using hper 0
  refine ⟨γ, hγ, ⟨ψ T - ψ 0, sub_ne_zero.2 fun h ↦ hT (by simpa using ψ.injective h),
    hγ.periodic_of_eq hRs hclose⟩, ψ, hψ0, hδeq⟩

end ClosedOrbit

end SmoothTwoForm

end TauCeti
