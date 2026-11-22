/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap
public import TauCeti.Analysis.Calculus.NormalExtension.Chart

/-!
# Charts adapted to a pseudoholomorphic curve

Let `u : V → W` be a curve in a normed space `W` carrying a field `J` of endomorphisms with
`J² = -1` along `u`, and let `u` be `J`-holomorphic for a fixed structure `j` on `V`:
`Du (j v) = J (u a) (Du v)`. Unlike a totally real submanifold, the image of `u` is invariant
under `J`, so the adapted extension of `TauCeti.adaptedNormalExtension` degenerates along it
(`TauCeti.not_isInvertible_fderiv_adaptedNormalExtension_complexLine`, in
`TauCeti.Analysis.Calculus.AdaptedChart`). Instead, choose a
*complex normal frame* `Z a : N →L W`, for a real model `N` of the normal directions, such that
`Du a`, `Z a` and `J (u a) ∘ Z a` together span `W` freely. The **complex normal extension**

`Φ (a, x, y) = u a + Z a x + J (u a) (Z a y)` (`TauCeti.complexNormalExtension`)

is the normal extension of `u` by the doubled frame `(Z, J Z)`. On the zero section its
derivative is `(v, x, y) ↦ Du v + Z x + J (Z y)`, which intertwines the standard structure
`(v, x, y) ↦ (j v, -y, x)` with `J` (`TauCeti.fderiv_complexNormalExtension_intertwines`). So
when this derivative is invertible, `Φ` is a local diffeomorphism
(`TauCeti.exists_complexNormalChart`) which straightens the curve to the zero section `V × {0}`
and pulls `J` back to the standard structure along it
(`OpenPartialHomeomorph.pullbackEnd_of_coe_eq_complexNormalExtension`). These are the local
coordinates of McDuff–Salamon Lemma 2.4.2.

**Transverse control.** The chart is only as regular as `u`, `Z` and `J ∘ u`: for `C¹` data it
is a `C¹` chart, and the pulled-back structure `Φ^* J = DΦ⁻¹ ∘ (J ∘ Φ) ∘ DΦ` is in general only
continuous. It is nevertheless Lipschitz in the normal directions: near the base point,

`‖Φ^* J (a, w) - Φ^* J (a, 0)‖ ≤ C ‖w‖`

(`OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`,
in `TauCeti.Analysis.Calculus.NormalExtension.Chart`). This holds for any chart given by a normal
extension `γ x + A x w` with `C¹` data and a field `J` that is Lipschitz near the base point,
because such a chart is affine in the normal variable:
`Φ (a, w) - Φ (a, 0) = A a w`, and `DΦ (a, w) - DΦ (a, 0)` is `(v, w') ↦ (DA v) w`, both linear
in `w`. No derivative of `Φ^* J` in the curve direction enters. For the complex normal chart it
gives `‖Φ^* J (a, w) - J_std‖ ≤ C ‖w‖`
(`OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_le_of_coe_eq_complexNormalExtension`). This is
the coefficient bound behind the estimate `|∂_s b + J_std ∂_t b| ≤ C |b| |d(a, b)|` for the
normal component `b` of a second `Φ^* J`-holomorphic curve `(a, b)`, through which unique
continuation compares two holomorphic curves; that estimate itself is not stated here.

## Main declarations

* `TauCeti.complexNormalExtension`: the extension `u a + Z a x + J (u a) (Z a y)`.
* `TauCeti.fderiv_complexNormalExtension_zero`: its derivative on the zero section.
* `TauCeti.fderiv_complexNormalExtension_intertwines`: that derivative is complex linear.
* `TauCeti.exists_complexNormalChart`: the inverse function theorem for the extension, a case of
  `TauCeti.exists_normalExtensionChart`.
* `OpenPartialHomeomorph.pullbackEnd_of_coe_eq_complexNormalExtension`: the pulled-back
  structure is standard on the zero section.
* `OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_le_of_coe_eq_complexNormalExtension`: the
  pulled-back structure differs from the standard one by `O(‖w‖)`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Lemma 2.4.2 and its proof (coordinates along an embedded holomorphic disc).
-/

public noncomputable section

open Set Filter
open scoped Topology ContDiff NNReal

namespace TauCeti

section Extension

variable {𝕜 V N W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {u : V → W} {J : W → W →L[𝕜] W} {Z : V → N →L[𝕜] W}

/-- The **complex normal extension** `(a, x, y) ↦ u a + Z a x + J (u a) (Z a y)` of a curve `u`
by a frame `Z` of normal directions and its image `J Z`. -/
def complexNormalExtension (u : V → W) (J : W → W →L[𝕜] W) (Z : V → N →L[𝕜] W) :
    V × (N × N) → W :=
  normalExtension u fun a ↦ (Z a).coprod ((J (u a)).comp (Z a))

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Express the complex normal extension through its doubled normal frame. -/
theorem complexNormalExtension_eq_normalExtension (u : V → W) (J : W → W →L[𝕜] W)
    (Z : V → N →L[𝕜] W) :
    complexNormalExtension u J Z =
      normalExtension u fun a ↦ (Z a).coprod ((J (u a)).comp (Z a)) := by
  rfl

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Evaluate a complex normal extension. -/
@[simp]
theorem complexNormalExtension_apply (p : V × (N × N)) :
    complexNormalExtension u J Z p = u p.1 + Z p.1 p.2.1 + J (u p.1) (Z p.1 p.2.2) := by
  simp [complexNormalExtension_eq_normalExtension, ContinuousLinearMap.coprod_apply, add_assoc]

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- The complex normal extension agrees with the curve on the zero section. -/
theorem complexNormalExtension_zero (a : V) : complexNormalExtension u J Z (a, 0) = u a := by
  simp

/-- The complex normal extension has the common regularity of the curve, the frame and `J`. -/
theorem contDiffAt_complexNormalExtension {n : ℕ∞ω} {a : V} {y : N × N}
    (hu : ContDiffAt 𝕜 n u a) (hZ : ContDiffAt 𝕜 n Z a) (hJ : ContDiffAt 𝕜 n J (u a)) :
    ContDiffAt 𝕜 n (complexNormalExtension u J Z) (a, y) := by
  rw [complexNormalExtension_eq_normalExtension]
  exact contDiffAt_normalExtension hu (hZ.continuousLinearMapCoprod ((hJ.comp a hu).clm_comp hZ))

/-- If `u` and `Z` are `C^n` on a set `U` and `u` maps `U` into a set `Ω` on which `J` is
`C^n`, the complex normal extension is `C^n` on `U ×ˢ univ`. -/
theorem contDiffOn_complexNormalExtension {n : ℕ∞ω} {U : Set V} {Ω : Set W}
    (hu : ContDiffOn 𝕜 n u U) (hZ : ContDiffOn 𝕜 n Z U) (hJ : ContDiffOn 𝕜 n J Ω)
    (huΩ : MapsTo u U Ω) :
    ContDiffOn 𝕜 n (complexNormalExtension u J Z) (U ×ˢ univ) := by
  rw [complexNormalExtension_eq_normalExtension]
  exact contDiffOn_normalExtension hu
    (hZ.continuousLinearMapCoprod ((hJ.comp hu huΩ).clm_comp hZ))

/-- On the zero section the derivative of the complex normal extension is the frame
`(v, x, y) ↦ Du v + Z x + J (Z y)`. It needs only a continuous frame and a continuous `J`. -/
theorem hasFDerivAt_complexNormalExtension_zero {a : V} {D : V →L[𝕜] W}
    (hu : HasFDerivAt u D a) (hZ : ContinuousAt Z a) (hJ : ContinuousAt J (u a)) :
    HasFDerivAt (complexNormalExtension u J Z)
      (D.coprod ((Z a).coprod ((J (u a)).comp (Z a)))) (a, 0) := by
  rw [complexNormalExtension_eq_normalExtension]
  exact hasFDerivAt_normalExtension_zero hu
    (hZ.continuousLinearMapCoprod ((hJ.comp hu.continuousAt).clm_comp hZ))

/-- The derivative of the complex normal extension on the zero section. -/
theorem fderiv_complexNormalExtension_zero {a : V} (hu : DifferentiableAt 𝕜 u a)
    (hZ : ContinuousAt Z a) (hJ : ContinuousAt J (u a)) :
    fderiv 𝕜 (complexNormalExtension u J Z) (a, 0) =
      (fderiv 𝕜 u a).coprod ((Z a).coprod ((J (u a)).comp (Z a))) :=
  (hasFDerivAt_complexNormalExtension_zero hu.hasFDerivAt hZ hJ).fderiv

/-- **The first jet is complex linear.** If `u` is `J`-holomorphic at `a` for the structure `j`
on `V` and `J (u a)² = -1`, the derivative of the complex normal extension at `(a, 0)` carries
the standard structure `(v, x, y) ↦ (j v, -y, x)` to `J (u a)`. -/
theorem fderiv_complexNormalExtension_intertwines {j : V →L[𝕜] V} {a : V}
    (hu : DifferentiableAt 𝕜 u a) (hZ : ContinuousAt Z a) (hJ : ContinuousAt J (u a))
    (hhol : ∀ v, fderiv 𝕜 u a (j v) = J (u a) (fderiv 𝕜 u a v))
    (hsq : ∀ w, J (u a) (J (u a) w) = -w) (v : V) (x y : N) :
    fderiv 𝕜 (complexNormalExtension u J Z) (a, 0) (j v, (-y, x)) =
      J (u a) (fderiv 𝕜 (complexNormalExtension u J Z) (a, 0) (v, (x, y))) := by
  rw [fderiv_complexNormalExtension_zero hu hZ hJ]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply, map_neg, map_add,
    hhol, hsq]
  abel

/-- **The flat complex slice.** For the slice `V × {0}` of `V × (N × N)` with the standard
structure and the frame `x ↦ (0, (x, 0))`, the complex normal extension is the identity. -/
@[simp]
theorem complexNormalExtension_inl (j : V →L[𝕜] V) :
    complexNormalExtension (ContinuousLinearMap.inl 𝕜 V (N × N))
      (fun _ ↦ j.prodMap ((-ContinuousLinearMap.snd 𝕜 N N).prod (ContinuousLinearMap.fst 𝕜 N N)))
      (fun _ ↦ (ContinuousLinearMap.inr 𝕜 V (N × N)).comp (ContinuousLinearMap.inl 𝕜 N N)) =
      id := by
  funext p
  ext <;> simp

end Extension

section Chart

variable {𝕜 V N W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {u : V → W} {J : W → W →L[𝕜] W} {Z : V → N →L[𝕜] W}

/-- **Complex normal charts exist.** Let `u` and the frame `Z` be `C^ℓ` on an open `U`, and `J`
be `C^ℓ` on an open `Ω` containing `u (U)`, with `1 ≤ ℓ`. If at `a₀ ∈ U` the frame
`(v, x, y) ↦ Du v + Z x + J (Z y)` is invertible, the complex normal extension restricts to a
partial homeomorphism around `(a₀, 0)` with source in `U × N × N`, target in `Ω`, and which is
`C^ℓ` with `C^ℓ` inverse. -/
theorem exists_complexNormalChart [CompleteSpace V] [CompleteSpace N] {U : Set V} {Ω : Set W}
    {a₀ : V} {ℓ : ℕ∞ω} (hU : IsOpen U) (hΩ : IsOpen Ω) (ha₀ : a₀ ∈ U) (hℓ : 1 ≤ ℓ)
    (hu : ContDiffOn 𝕜 ℓ u U) (hZ : ContDiffOn 𝕜 ℓ Z U) (hJ : ContDiffOn 𝕜 ℓ J Ω)
    (huΩ : MapsTo u U Ω)
    (hframe : ((fderiv 𝕜 u a₀).coprod ((Z a₀).coprod ((J (u a₀)).comp (Z a₀)))).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (V × (N × N)) W, ⇑e = complexNormalExtension u J Z ∧
      (a₀, 0) ∈ e.source ∧ e.source ⊆ U ×ˢ univ ∧ e.target ⊆ Ω ∧
      ContDiffOn 𝕜 ℓ e e.source ∧ ContDiffOn 𝕜 ℓ e.symm e.target := by
  rw [complexNormalExtension_eq_normalExtension]
  exact exists_normalExtensionChart hU hΩ ha₀ hℓ hu
    (hZ.continuousLinearMapCoprod ((hJ.comp hu huΩ).clm_comp hZ)) huΩ hframe

end Chart

end TauCeti

namespace OpenPartialHomeomorph

section ComplexNormal

variable {𝕜 V N W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {u : V → W} {J : W → W →L[𝕜] W} {Z : V → N →L[𝕜] W}
  {e : OpenPartialHomeomorph (V × (N × N)) W}

/-- **The chart straightens `J` along the curve.** At a point `(a, 0)` of the source where `u` is
`J`-holomorphic for `j`, `J (u a)² = -1` and the inverse chart is differentiable, the
pulled-back structure is the standard structure `(v, x, y) ↦ (j v, -y, x)`. -/
theorem pullbackEnd_of_coe_eq_complexNormalExtension {j : V →L[𝕜] V}
    (he : ⇑e = TauCeti.complexNormalExtension u J Z) {a : V} (ha : (a, 0) ∈ e.source)
    (hu : DifferentiableAt 𝕜 u a) (hZ : ContinuousAt Z a) (hJ : ContinuousAt J (u a))
    (hhol : ∀ v, fderiv 𝕜 u a (j v) = J (u a) (fderiv 𝕜 u a v))
    (hsq : ∀ w, J (u a) (J (u a) w) = -w) (hs : DifferentiableAt 𝕜 e.symm (u a)) :
    e.pullbackEnd J (a, 0) =
      j.prodMap ((-ContinuousLinearMap.snd 𝕜 N N).prod (ContinuousLinearMap.fst 𝕜 N N)) := by
  have hea : e (a, 0) = u a := by rw [he, TauCeti.complexNormalExtension_zero]
  have hd : DifferentiableAt 𝕜 e (a, 0) := by
    rw [he]
    exact (TauCeti.hasFDerivAt_complexNormalExtension_zero hu.hasFDerivAt hZ hJ).differentiableAt
  refine ContinuousLinearMap.ext fun ⟨v, x, y⟩ ↦ ?_
  have hint := TauCeti.fderiv_complexNormalExtension_intertwines hu hZ hJ hhol hsq v x y
  rw [← he] at hint
  rw [pullbackEnd_apply, hea, ← hint, ← hea,
    e.fderiv_symm_apply_fderiv_apply_of_mem_source ha hd (by rwa [hea])]
  simp

end ComplexNormal

section ComplexNormalLipschitz

variable {𝕜 V N W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {u : V → W} {J : W → W →L[𝕜] W} {Z : V → N →L[𝕜] W}
  {e : OpenPartialHomeomorph (V × (N × N)) W}

/-- **McDuff–Salamon Lemma 2.4.2: transverse control in a complex normal chart.** Let `u` be
`J`-holomorphic for `j` near `a₀`, with `J² = -1` along `u` near `a₀`, and let `e` be a chart
whose underlying map is the complex normal extension, with `u` and the frame `Z` of class `C¹` at
`a₀`, `J` of class `C¹` at `u a₀` and a `C¹` inverse at `u a₀`. Then near `(a₀, 0)` the pulled-back
structure differs from the standard structure `(v, x, y) ↦ (j v, -y, x)` by at most a constant
times the size of the normal coordinate. -/
theorem exists_norm_pullbackEnd_sub_le_of_coe_eq_complexNormalExtension {j : V →L[𝕜] V}
    (he : ⇑e = TauCeti.complexNormalExtension u J Z) {a₀ : V} (ha₀ : (a₀, 0) ∈ e.source)
    (hu : ContDiffAt 𝕜 1 u a₀) (hZ : ContDiffAt 𝕜 1 Z a₀) (hJ : ContDiffAt 𝕜 1 J (u a₀))
    (hes : ContDiffAt 𝕜 1 e.symm (u a₀))
    (hhol : ∀ᶠ a in 𝓝 a₀, ∀ v, fderiv 𝕜 u a (j v) = J (u a) (fderiv 𝕜 u a v))
    (hsq : ∀ᶠ a in 𝓝 a₀, ∀ w, J (u a) (J (u a) w) = -w) :
    ∃ C, ∀ᶠ p in 𝓝 (a₀, (0 : N × N)),
      ‖e.pullbackEnd J p -
        j.prodMap ((-ContinuousLinearMap.snd 𝕜 N N).prod (ContinuousLinearMap.fst 𝕜 N N))‖ ≤
        C * ‖p.2‖ := by
  have hA : ContDiffAt 𝕜 1 (fun a ↦ (Z a).coprod ((J (u a)).comp (Z a))) a₀ :=
    hZ.continuousLinearMapCoprod ((hJ.comp a₀ hu).clm_comp hZ)
  obtain ⟨K, t, ht, hK⟩ := hJ.exists_lipschitzOnWith
  obtain ⟨C, hC⟩ :=
    exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension
      (he.trans (TauCeti.complexNormalExtension_eq_normalExtension u J Z)) ha₀ hu hA ht hK hes
  refine ⟨C, ?_⟩
  -- Near `a₀`, the structure is standard at the foot `(a, 0)` of each point `(a, w)`.
  have hJu : ∀ᶠ a in 𝓝 a₀, ContinuousAt J (u a) :=
    hu.continuousAt.eventually ((hJ.eventually (by simp)).mono fun _ h ↦ h.continuousAt)
  have hsymm : ∀ᶠ a in 𝓝 a₀, DifferentiableAt 𝕜 e.symm (u a) :=
    hu.continuousAt.eventually
      ((hes.eventually (by simp)).mono fun _ h ↦ h.differentiableAt one_ne_zero)
  have hsrc : ∀ᶠ a in 𝓝 a₀, (a, (0 : N × N)) ∈ e.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds ha₀)
  have hfoot : ∀ᶠ a in 𝓝 a₀, e.pullbackEnd J (a, 0) =
      j.prodMap ((-ContinuousLinearMap.snd 𝕜 N N).prod (ContinuousLinearMap.fst 𝕜 N N)) := by
    filter_upwards [hsrc, hu.eventually (by simp), hZ.eventually (by simp), hJu, hhol, hsq,
      hsymm] with a h₁ h₂ h₃ h₄ h₅ h₆ h₇
    exact pullbackEnd_of_coe_eq_complexNormalExtension he h₁ (h₂.differentiableAt one_ne_zero)
      h₃.continuousAt h₄ h₅ h₆ h₇
  filter_upwards [hC, continuousAt_fst.eventually hfoot] with p hp hp'
  rwa [← hp']

end ComplexNormalLipschitz

end OpenPartialHomeomorph
