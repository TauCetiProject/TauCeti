/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import TauCeti.Analysis.Calculus.AdaptedChart
public import TauCeti.Analysis.Calculus.ContDiff.ContinuousLinearMap

/-!
# Charts adapted to a pseudoholomorphic curve

Let `u : V → W` be a curve in a normed space `W` carrying a field `J` of endomorphisms with
`J² = -1` along `u`, and let `u` be `J`-holomorphic for a fixed structure `j` on `V`:
`Du (j v) = J (u a) (Du v)`. Unlike a totally real submanifold, the image of `u` is invariant
under `J`, so the adapted extension of `TauCeti.adaptedNormalExtension` degenerates along it
(`TauCeti.not_isInvertible_fderiv_adaptedNormalExtension_complexLine`). Instead, choose a
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

(`OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`).
This holds for any chart given by a normal extension `γ x + A x w` with `C¹` data and a field `J`
that is Lipschitz near the base point, because such a chart is affine in the normal variable:
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
* `TauCeti.exists_complexNormalChart`: the inverse function theorem for the extension.
* `OpenPartialHomeomorph.pullbackEnd_of_coe_eq_complexNormalExtension`: the pulled-back
  structure is standard on the zero section.
* `OpenPartialHomeomorph.exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`:
  transverse Lipschitz control of the structure pulled back along any normal-extension chart.
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
    ContDiffAt 𝕜 n (complexNormalExtension u J Z) (a, y) :=
  contDiffAt_normalExtension hu (hZ.continuousLinearMapCoprod ((hJ.comp a hu).clm_comp hZ))

/-- If `u` and `Z` are `C^n` on an open `U` and `u` maps `U` into a set `Ω` on which `J` is
`C^n`, the complex normal extension is `C^n` on `U ×ˢ univ`. -/
theorem contDiffOn_complexNormalExtension {n : ℕ∞ω} {U : Set V} {Ω : Set W}
    (hu : ContDiffOn 𝕜 n u U) (hZ : ContDiffOn 𝕜 n Z U) (hJ : ContDiffOn 𝕜 n J Ω)
    (huΩ : MapsTo u U Ω) :
    ContDiffOn 𝕜 n (complexNormalExtension u J Z) (U ×ˢ univ) := by
  have hA : ContDiffOn 𝕜 n (fun a ↦ (Z a).coprod ((J (u a)).comp (Z a))) U := by
    simp_rw [← ContinuousLinearMap.comp_fst_add_comp_snd]
    exact (hZ.clm_comp contDiffOn_const).add
      (((hJ.comp hu huΩ).clm_comp hZ).clm_comp contDiffOn_const)
  have hfst : MapsTo (Prod.fst : V × (N × N) → V) (U ×ˢ univ) U := fun _ hp ↦ hp.1
  exact ((hu.comp contDiffOn_fst hfst).add
    ((hA.comp contDiffOn_fst hfst).clm_apply contDiffOn_snd)).congr fun p _ ↦ by
      simp [ContinuousLinearMap.coprod_apply, add_assoc]

/-- On the zero section the derivative of the complex normal extension is the frame
`(v, x, y) ↦ Du v + Z x + J (Z y)`. It needs only a continuous frame and a continuous `J`. -/
theorem hasFDerivAt_complexNormalExtension_zero {a : V} {D : V →L[𝕜] W}
    (hu : HasFDerivAt u D a) (hZ : ContinuousAt Z a) (hJ : ContinuousAt J (u a)) :
    HasFDerivAt (complexNormalExtension u J Z)
      (D.coprod ((Z a).coprod ((J (u a)).comp (Z a)))) (a, 0) :=
  hasFDerivAt_normalExtension_zero hu
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
  have hΦ : ContDiffOn 𝕜 ℓ (complexNormalExtension u J Z) (U ×ˢ univ) :=
    contDiffOn_complexNormalExtension hu hZ hJ huΩ
  have hs : IsOpen ((U ×ˢ univ) ∩ complexNormalExtension u J Z ⁻¹' Ω) :=
    hΦ.continuousOn.isOpen_inter_preimage (hU.prod isOpen_univ) hΩ
  have hmem : (a₀, (0 : N × N)) ∈ (U ×ˢ univ) ∩ complexNormalExtension u J Z ⁻¹' Ω :=
    ⟨⟨ha₀, mem_univ _⟩, by simpa only [mem_preimage, complexNormalExtension_zero] using huΩ ha₀⟩
  have hu₁ : ContDiffAt 𝕜 1 u a₀ := (hu.contDiffAt (hU.mem_nhds ha₀)).of_le hℓ
  have hZc : ContinuousAt Z a₀ := hZ.continuousOn.continuousAt (hU.mem_nhds ha₀)
  have hJc : ContinuousAt J (u a₀) := hJ.continuousOn.continuousAt (hΩ.mem_nhds (huΩ ha₀))
  obtain ⟨E, hE⟩ := hframe
  rw [← fderiv_complexNormalExtension_zero (hu₁.differentiableAt one_ne_zero) hZc hJc] at hE
  obtain ⟨e, he, hx, hsub, hsymm⟩ :=
    TauCeti.ContDiffOn.exists_openPartialHomeomorph (hΦ.mono inter_subset_left) hs hmem hℓ hE
  refine ⟨e, he, hx, fun p hp ↦ (hsub hp).1, fun y hy ↦ ?_, ?_, hsymm⟩
  · rw [← e.right_inv hy, he]
    exact (hsub (e.map_target hy)).2
  · rw [he]
    exact hΦ.mono fun p hp ↦ (hsub hp).1

end Chart

end TauCeti

namespace OpenPartialHomeomorph

section Lipschitz

variable {𝕜 V E W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The conjugates `G ∘ K ∘ M` and `G' ∘ K' ∘ M'`, with `G` a left inverse of `M` and `G'` a
right inverse of `M'`, differ by at most the differences of `K, K'` and of `M, M'`. -/
private theorem norm_comp_comp_sub_comp_comp_le {G G' : W →L[𝕜] V} {K K' : W →L[𝕜] W}
    {M M' : V →L[𝕜] W} (hGM : G.comp M = ContinuousLinearMap.id 𝕜 V)
    (hMG : M'.comp G' = ContinuousLinearMap.id 𝕜 W) :
    ‖G.comp (K.comp M) - G'.comp (K'.comp M')‖ ≤
      ‖G‖ * ‖M - M'‖ * ‖G'‖ * ‖K‖ * ‖M‖ + ‖G'‖ * ‖K - K'‖ * ‖M‖ +
        ‖G'‖ * ‖K'‖ * ‖M - M'‖ := by
  -- `G - G' = G ∘ (M' - M) ∘ G'`, since `G ∘ M = id` and `M' ∘ G' = id`.
  have hG : G - G' = G.comp ((M' - M).comp G') := by
    rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, hMG,
      ← ContinuousLinearMap.comp_assoc, hGM, ContinuousLinearMap.comp_id,
      ContinuousLinearMap.id_comp]
  have hsplit : G.comp (K.comp M) - G'.comp (K'.comp M') =
      (G - G').comp (K.comp M) + G'.comp ((K - K').comp M) + G'.comp (K'.comp (M - M')) := by
    ext v
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  have h₁ : ‖(G - G').comp (K.comp M)‖ ≤ ‖G‖ * ‖M - M'‖ * ‖G'‖ * ‖K‖ * ‖M‖ := by
    calc ‖(G - G').comp (K.comp M)‖ ≤ ‖G - G'‖ * (‖K‖ * ‖M‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ ‖G‖ * (‖M' - M‖ * ‖G'‖) * (‖K‖ * ‖M‖) := by
          rw [hG]
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ = ‖G‖ * ‖M - M'‖ * ‖G'‖ * ‖K‖ * ‖M‖ := by rw [norm_sub_rev]; ring
  have h₂ : ‖G'.comp ((K - K').comp M)‖ ≤ ‖G'‖ * ‖K - K'‖ * ‖M‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
  have h₃ : ‖G'.comp (K'.comp (M - M'))‖ ≤ ‖G'‖ * ‖K'‖ * ‖M - M'‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans <| by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
  rw [hsplit]
  exact (norm_add₃_le).trans (add_le_add (add_le_add h₁ h₂) h₃)

/-- The derivatives of a normal extension at `(x, w)` and at `(x, 0)` differ by `(DA ·) w`. -/
private theorem norm_fderiv_normalExtension_sub_le {γ : V → W} {A : V → E →L[𝕜] W} {x : V}
    {w : E} (hγ : DifferentiableAt 𝕜 γ x) (hA : DifferentiableAt 𝕜 A x) :
    ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x, w) -
        fderiv 𝕜 (TauCeti.normalExtension γ A) (x, 0)‖ ≤ ‖fderiv 𝕜 A x‖ * ‖w‖ := by
  rw [(TauCeti.hasFDerivAt_normalExtension hγ.hasFDerivAt hA.hasFDerivAt (y := w)).fderiv,
    (TauCeti.hasFDerivAt_normalExtension hγ.hasFDerivAt hA.hasFDerivAt (y := 0)).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p ↦ ?_
  simp only [sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_zero,
    zero_apply, add_zero, add_sub_cancel_left, ContinuousLinearMap.coe_fst']
  calc ‖fderiv 𝕜 A x p.1 w‖ ≤ ‖fderiv 𝕜 A x‖ * ‖p.1‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ ≤ ‖fderiv 𝕜 A x‖ * ‖w‖ * ‖p‖ := by
        rw [mul_right_comm]
        gcongr
        exact norm_fst_le p

/-- The pointwise estimate behind
`exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension`: at `(x, w)` and `(x, 0)`,
given bounds on the derivatives of the chart and its inverse, on `J` and on the frame, and a
Lipschitz constant of `J` on a set containing both images. -/
private theorem norm_pullbackEnd_sub_pullbackEnd_le {γ : V → W} {A : V → E →L[𝕜] W}
    {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W} {K : ℝ≥0} {t : Set W}
    {BA BD BM BG BJ : ℝ} (he : ⇑e = TauCeti.normalExtension γ A) (hK : LipschitzOnWith K J t)
    {x : V} {w : E} (hps : (x, w) ∈ e.source) (hqs : (x, 0) ∈ e.source)
    (hγ : DifferentiableAt 𝕜 γ x) (hA : DifferentiableAt 𝕜 A x)
    (hpes : DifferentiableAt 𝕜 e.symm (e (x, w))) (hqes : DifferentiableAt 𝕜 e.symm (e (x, 0)))
    (hpt : e (x, w) ∈ t) (hqt : e (x, 0) ∈ t) (hBA : ‖A x‖ ≤ BA) (hBD : ‖fderiv 𝕜 A x‖ ≤ BD)
    (hBM : ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x, w)‖ ≤ BM)
    (hpG : ‖fderiv 𝕜 e.symm (e (x, w))‖ ≤ BG) (hqG : ‖fderiv 𝕜 e.symm (e (x, 0))‖ ≤ BG)
    (hpJ : ‖J (e (x, w))‖ ≤ BJ) (hBJ : ‖J (e (x, 0))‖ ≤ BJ) :
    ‖e.pullbackEnd J (x, w) - e.pullbackEnd J (x, 0)‖ ≤
      (BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD) * ‖w‖ := by
  have hd {y : E} : DifferentiableAt 𝕜 e (x, y) := by
    rw [he]
    exact (TauCeti.hasFDerivAt_normalExtension hγ.hasFDerivAt hA.hasFDerivAt).differentiableAt
  -- The chart moves by `A x w` in the normal direction, and its derivative by `(DA ·) w`.
  have hM : ‖fderiv 𝕜 e (x, w) - fderiv 𝕜 e (x, 0)‖ ≤ BD * ‖w‖ := by
    rw [he]
    exact (norm_fderiv_normalExtension_sub_le hγ hA).trans (by gcongr)
  have hJ : ‖J (e (x, w)) - J (e (x, 0))‖ ≤ K * BA * ‖w‖ := by
    calc ‖J (e (x, w)) - J (e (x, 0))‖ ≤ K * ‖e (x, w) - e (x, 0)‖ := hK.norm_sub_le hpt hqt
      _ ≤ K * (BA * ‖w‖) := by
          rw [he]
          simp only [TauCeti.normalExtension_apply, add_sub_add_left_eq_sub, map_zero, sub_zero]
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
      _ = K * BA * ‖w‖ := by ring
  have hMp : ‖fderiv 𝕜 e (x, w)‖ ≤ BM := by rwa [he]
  have hBG : 0 ≤ BG := (norm_nonneg _).trans hpG
  have hBD' : 0 ≤ BD := (ContinuousLinearMap.opNorm_nonneg _).trans hBD
  have hBJ' : 0 ≤ BJ := (norm_nonneg _).trans hBJ
  have hBA' : 0 ≤ BA := (ContinuousLinearMap.opNorm_nonneg _).trans hBA
  rw [pullbackEnd_def, pullbackEnd_def]
  calc _ ≤ _ := norm_comp_comp_sub_comp_comp_le (K := J (e (x, w))) (K' := J (e (x, 0)))
        (e.fderiv_symm_comp_fderiv_of_mem_source hps hd hpes)
        (e.fderiv_comp_fderiv_symm_of_mem_source hqs hd hqes)
    _ ≤ BG * (BD * ‖w‖) * BG * BJ * BM + BG * (K * BA * ‖w‖) * BM + BG * BJ * (BD * ‖w‖) := by
        gcongr
    _ = (BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD) * ‖w‖ := by ring

/-- Near `(x₀, 0)`, the hypotheses of `norm_pullbackEnd_sub_pullbackEnd_le` hold with bounds
given by the values at `(x₀, 0)` plus one. -/
private theorem eventually_normalExtension_chart_bounds {γ : V → W} {A : V → E →L[𝕜] W}
    {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W} {x₀ : V} {K : ℝ≥0} {t : Set W}
    (he : ⇑e = TauCeti.normalExtension γ A) (hx₀ : (x₀, 0) ∈ e.source)
    (hγ : ContDiffAt 𝕜 1 γ x₀) (hA : ContDiffAt 𝕜 1 A x₀) (ht : t ∈ 𝓝 (γ x₀))
    (hJ : LipschitzOnWith K J t) (hes : ContDiffAt 𝕜 1 e.symm (γ x₀)) :
    ∀ᶠ q in 𝓝 (x₀, (0 : E)), q ∈ e.source ∧ (DifferentiableAt 𝕜 γ q.1 ∧
      DifferentiableAt 𝕜 A q.1) ∧ DifferentiableAt 𝕜 e.symm (e q) ∧ e q ∈ t ∧
      ‖A q.1‖ ≤ ‖A x₀‖ + 1 ∧ ‖fderiv 𝕜 A q.1‖ ≤ ‖fderiv 𝕜 A x₀‖ + 1 ∧
      ‖fderiv 𝕜 (TauCeti.normalExtension γ A) q‖ ≤
        ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x₀, 0)‖ + 1 ∧
      ‖fderiv 𝕜 e.symm (e q)‖ ≤ ‖fderiv 𝕜 e.symm (γ x₀)‖ + 1 ∧
      ‖J (e q)‖ ≤ ‖J (γ x₀)‖ + 1 := by
  have hep₀ : e (x₀, 0) = γ x₀ := by rw [he, TauCeti.normalExtension_zero]
  have hec : ContinuousAt e (x₀, 0) := e.continuousAt hx₀
  have hb {f : V × E → ℝ} {c : ℝ} (hf : Tendsto f (𝓝 (x₀, 0)) (𝓝 c)) :
      ∀ᶠ q in 𝓝 (x₀, (0 : E)), f q ≤ c + 1 :=
    hf.eventually (eventually_le_nhds (lt_add_one _))
  have hfst : Tendsto (Prod.fst : V × E → V) (𝓝 (x₀, 0)) (𝓝 x₀) := continuousAt_fst
  have hdiff : ∀ᶠ x in 𝓝 x₀, DifferentiableAt 𝕜 γ x ∧ DifferentiableAt 𝕜 A x :=
    ((hγ.eventually (by simp)).and (hA.eventually (by simp))).mono fun x hx ↦
      ⟨hx.1.differentiableAt one_ne_zero, hx.2.differentiableAt one_ne_zero⟩
  have hsymm : ∀ᶠ y in 𝓝 (e (x₀, 0)), DifferentiableAt 𝕜 e.symm y := by
    rw [hep₀]
    exact (hes.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt one_ne_zero
  have hG : Tendsto (fun q ↦ ‖fderiv 𝕜 e.symm (e q)‖) (𝓝 (x₀, 0))
      (𝓝 ‖fderiv 𝕜 e.symm (γ x₀)‖) :=
    ((hes.continuousAt_fderiv one_ne_zero).norm.tendsto.comp (hep₀ ▸ hec.tendsto))
  have hJt : Tendsto (fun q ↦ ‖J (e q)‖) (𝓝 (x₀, 0)) (𝓝 ‖J (γ x₀)‖) :=
    ((hJ.continuousOn.continuousAt ht).norm.tendsto.comp (hep₀ ▸ hec.tendsto))
  exact (e.open_source.eventually_mem hx₀).and <| (hfst.eventually hdiff).and <|
    (hec.eventually hsymm).and <| (hec.eventually_mem (by rwa [hep₀])).and <|
    (hb (hA.continuousAt.norm.tendsto.comp hfst)).and <|
    (hb ((continuous_norm.continuousAt.comp
      (hA.continuousAt_fderiv one_ne_zero)).tendsto.comp hfst)).and <|
    (hb ((TauCeti.contDiffAt_normalExtension hγ hA).continuousAt_fderiv
      one_ne_zero).norm.tendsto).and <| (hb hG).and (hb hJt)

/-- **Transverse Lipschitz control along a normal-extension chart.** Let `e` be a chart whose
underlying map is the normal extension `(x, w) ↦ γ x + A x w`, with `γ` and `A` of class `C¹`
at `x₀` and a `C¹` inverse at `γ x₀`, and let `J` be Lipschitz on a neighbourhood of `γ x₀`.
Then the pulled-back field `e^* J` is Lipschitz in the normal variable near `(x₀, 0)`:
`‖e^* J (x, w) - e^* J (x, 0)‖ ≤ C ‖w‖`. No regularity of `e^* J` in `x` is claimed. -/
theorem exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension
    {γ : V → W} {A : V → E →L[𝕜] W} {J : W → W →L[𝕜] W} {e : OpenPartialHomeomorph (V × E) W}
    {x₀ : V} {K : ℝ≥0} {t : Set W} (he : ⇑e = TauCeti.normalExtension γ A)
    (hx₀ : (x₀, 0) ∈ e.source) (hγ : ContDiffAt 𝕜 1 γ x₀) (hA : ContDiffAt 𝕜 1 A x₀)
    (ht : t ∈ 𝓝 (γ x₀)) (hJ : LipschitzOnWith K J t) (hes : ContDiffAt 𝕜 1 e.symm (γ x₀)) :
    ∃ C, ∀ᶠ p in 𝓝 (x₀, (0 : E)),
      ‖e.pullbackEnd J p - e.pullbackEnd J (p.1, 0)‖ ≤ C * ‖p.2‖ := by
  have hgood := eventually_normalExtension_chart_bounds he hx₀ hγ hA ht hJ hes
  -- Each point `(x, w)` near `(x₀, 0)` is compared with its foot `(x, 0)`, also near `(x₀, 0)`.
  have hzero : Tendsto (fun p : V × E ↦ (p.1, (0 : E))) (𝓝 (x₀, 0)) (𝓝 (x₀, 0)) :=
    (continuous_fst.prodMk continuous_const).tendsto' _ _ rfl
  set BA := ‖A x₀‖ + 1
  set BD := ‖fderiv 𝕜 A x₀‖ + 1
  set BM := ‖fderiv 𝕜 (TauCeti.normalExtension γ A) (x₀, 0)‖ + 1
  set BG := ‖fderiv 𝕜 e.symm (γ x₀)‖ + 1
  set BJ := ‖J (γ x₀)‖ + 1
  refine ⟨BG * BD * BG * BJ * BM + BG * (K * BA) * BM + BG * BJ * BD, ?_⟩
  filter_upwards [hgood, hzero.eventually hgood] with p
    ⟨hps, ⟨hpγ, hpA⟩, hpes, hpt, hpA', hpDA, hpM, hpG, hpJ⟩ ⟨hqs, _, hqes, hqt, _, _, _, hqG, hqJ⟩
  exact norm_pullbackEnd_sub_pullbackEnd_le he hJ hps hqs hpγ hpA hpes hqes hpt hqt hpA' hpDA hpM
    hpG hqG hpJ hqJ

end Lipschitz

section ComplexNormal

variable {𝕜 V N W : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup N] [NormedSpace 𝕜 N] [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  {u : V → W} {J : W → W →L[𝕜] W} {Z : V → N →L[𝕜] W}
  {e : OpenPartialHomeomorph (V × (N × N)) W}

omit [NormedSpace 𝕜 V] in
/-- A complex normal chart inverts the curve on the zero section of its source. -/
theorem symm_apply_of_coe_eq_complexNormalExtension (he : ⇑e = TauCeti.complexNormalExtension u J Z)
    {a : V} (ha : (a, 0) ∈ e.source) : e.symm (u a) = (a, 0) := by
  rw [← TauCeti.complexNormalExtension_zero (u := u) (J := J) (Z := Z) a, ← he, e.left_inv ha]

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
    exists_norm_pullbackEnd_sub_pullbackEnd_le_of_coe_eq_normalExtension he ha₀ hu hA ht hK hes
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
