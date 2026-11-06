/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Asymptotics.Prod

/-!
# Normal extensions for adapted coordinates

The map `normalExtension γ A (x, y) = γ x + A x y` extends a parametrization by prescribed
normal directions. Its derivative on the zero section requires only continuity of the normal
frame, rather than differentiability of that frame.

The adapted extension uses `A x = J (γ x) ∘ Dγ x`. If `γ` is `C^(n+1)` and `J` is `C^n`, this
extension is `C^n`, including finite orders. The ambient almost complex field is given by its
continuous-linear endomorphisms in coordinates. These extensions are candidate charts for
coordinates adapted to a totally real submanifold.

## Main declarations

* `normalExtension`: a parametrization extended by a prescribed normal frame.
* `hasFDerivAt_normalExtension_zero`: its first jet for merely continuous normal frames.
* `adaptedNormalExtension`: the frame obtained by applying `J` to the tangential derivative.
* `contDiffOn_adaptedNormalExtension`: finite regularity on open coordinate domains.
* `fderiv_adaptedNormalExtension_intertwines`: complex linearity of the adapted first jet.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public noncomputable section

open Filter Asymptotics
open scoped Topology ContDiff

namespace TauCeti

variable {𝕜 V W E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Extend a parametrization by a prescribed family of normal directions. -/
def normalExtension (γ : V → W) (A : V → E →L[𝕜] W) (p : V × E) : W :=
  γ p.1 + A p.1 p.2

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Evaluate a normal extension at an arbitrary point. -/
@[simp]
theorem normalExtension_apply (γ : V → W) (A : V → E →L[𝕜] W) (p : V × E) :
    normalExtension γ A p = γ p.1 + A p.1 p.2 := by rfl

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- The extension agrees with its parametrization on the zero section. -/
theorem normalExtension_zero (γ : V → W) (A : V → E →L[𝕜] W) (x : V) :
    normalExtension γ A (x, 0) = γ x := by simp [normalExtension]

/-- The normal extension has the common regularity of its parametrization and its frame. -/
theorem contDiff_normalExtension {γ : V → W} {A : V → E →L[𝕜] W} {n : ℕ∞ω}
    (hγ : ContDiff 𝕜 n γ) (hA : ContDiff 𝕜 n A) :
    ContDiff 𝕜 n (normalExtension γ A) :=
  (hγ.comp contDiff_fst).add ((hA.comp contDiff_fst).clm_apply contDiff_snd)

/-- Regularity of the extension is local in its tangential variable. -/
theorem contDiffAt_normalExtension {γ : V → W} {A : V → E →L[𝕜] W} {n : ℕ∞ω}
    {x : V} {y : E} (hγ : ContDiffAt 𝕜 n γ x) (hA : ContDiffAt 𝕜 n A x) :
    ContDiffAt 𝕜 n (normalExtension γ A) (x, y) :=
  (hγ.comp (x, y) contDiffAt_fst).add
    ((hA.comp (x, y) contDiffAt_fst).clm_apply contDiffAt_snd)

/-- On the zero section, continuity of the normal frame suffices for the first-jet formula.
No derivative of that frame is required. -/
theorem hasFDerivAt_normalExtension_zero {γ : V → W} {A : V → E →L[𝕜] W} {x : V}
    {D : V →L[𝕜] W} (hγ : HasFDerivAt γ D x) (hA : ContinuousAt A x) :
    HasFDerivAt (normalExtension γ A) (D.coprod (A x)) (x, 0) := by
  have hγr : (fun h : V × E ↦ γ (x + h.1) - γ x - D h.1) =o[𝓝 0] fun h ↦ h :=
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hγ).comp_tendsto
      (continuous_fst.tendsto 0)).trans_isBigO isBigO_fst_prod'
  have hAc : ContinuousAt (fun h : V × E ↦ A (x + h.1)) 0 := by
    apply ContinuousAt.comp
    · simpa only [Prod.fst_zero, add_zero] using hA
    · fun_prop
  have hAr : (fun h : V × E ↦ A (x + h.1) - A x) =o[𝓝 0] fun _ ↦ (1 : ℝ) := by
    simpa only [Prod.fst_zero, add_zero] using (hAc.isLittleO (F := ℝ))
  have hnr : (fun h : V × E ↦ (A (x + h.1) - A x) h.2) =o[𝓝 0] fun h ↦ h := by
    have hr := hAr.norm_left.mul_isBigO
      (isBigO_snd_prod' (f' := fun h : V × E ↦ h) (l := 𝓝 0)).norm_norm
    have hb := (isBoundedBilinearMap_apply :
      IsBoundedBilinearMap 𝕜 (fun p : (E →L[𝕜] W) × E ↦ p.1 p.2)).isBigO_comp
        (g := fun h : V × E ↦ A (x + h.1) - A x) (h := fun h ↦ h.2) (l := 𝓝 0)
    apply IsLittleO.of_norm_right
    simpa only [one_mul] using hb.trans_isLittleO hr
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  convert hγr.add hnr using 1
  ext h
  simp only [normalExtension, Prod.fst_add, Prod.snd_add,
    add_zero, zero_add, map_zero, ContinuousLinearMap.coprod_apply,
    sub_apply]
  abel

/-- The derivative of a normal extension along the zero section is its doubled frame. -/
theorem fderiv_normalExtension_zero {γ : V → W} {A : V → E →L[𝕜] W} {x : V}
    (hγ : DifferentiableAt 𝕜 γ x) (hA : ContinuousAt A x) :
    fderiv 𝕜 (normalExtension γ A) (x, 0) = (fderiv 𝕜 γ x).coprod (A x) :=
  (hasFDerivAt_normalExtension_zero hγ.hasFDerivAt hA).fderiv

/-- The normal extension used to build coordinates adapted to a totally real submanifold. -/
def adaptedNormalExtension (γ : V → W) (J : W → W →L[𝕜] W) : V × V → W :=
  normalExtension γ (fun x ↦ (J (γ x)).comp (fderiv 𝕜 γ x))

/-- Express the adapted extension through its prescribed normal frame. -/
theorem adaptedNormalExtension_eq_normalExtension (γ : V → W) (J : W → W →L[𝕜] W) :
    adaptedNormalExtension γ J =
      normalExtension γ (fun x ↦ (J (γ x)).comp (fderiv 𝕜 γ x)) := by rfl

/-- Evaluate an adapted normal extension at an arbitrary point. -/
@[simp]
theorem adaptedNormalExtension_apply (γ : V → W) (J : W → W →L[𝕜] W) (p : V × V) :
    adaptedNormalExtension γ J p = γ p.1 + J (γ p.1) (fderiv 𝕜 γ p.1 p.2) := by rfl

/-- The adapted extension agrees with the parametrized submanifold. -/
theorem adaptedNormalExtension_zero (γ : V → W) (J : W → W →L[𝕜] W) (x : V) :
    adaptedNormalExtension γ J (x, 0) = γ x := by
  simp [adaptedNormalExtension]

/-- The adapted extension is `C^n` for a `C^(n+1)` parametrization and `C^n` structure.
In particular a smooth parametrization costs no derivative of the almost complex field. -/
theorem contDiff_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    (hγ : ContDiff 𝕜 (n + 1) γ) (hJ : ContDiff 𝕜 n J) :
    ContDiff 𝕜 n (adaptedNormalExtension γ J) := by
  have hγn := hγ.of_le (le_self_add : n ≤ n + 1)
  exact contDiff_normalExtension hγn ((hJ.comp hγn).clm_comp (hγ.fderiv_right le_rfl))

/-- The local regularity statement, suitable for coordinate domains. -/
theorem contDiffAt_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    {x y : V} (hγ : ContDiffAt 𝕜 (n + 1) γ x) (hJ : ContDiffAt 𝕜 n J (γ x)) :
    ContDiffAt 𝕜 n (adaptedNormalExtension γ J) (x, y) := by
  have hγn := hγ.of_le (le_self_add : n ≤ n + 1)
  exact contDiffAt_normalExtension hγn
    ((hJ.comp x hγn).clm_comp (hγ.fderiv_right le_rfl))

/-- If `γ` is `C^(n+1)` on an open `U` and maps it into an open `Ω` on which `J` is `C^n`,
the adapted extension is `C^n` on `U ×ˢ univ`. -/
theorem contDiffOn_adaptedNormalExtension {γ : V → W} {J : W → W →L[𝕜] W} {n : ℕ∞ω}
    {U : Set V} {Ω : Set W} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hγ : ContDiffOn 𝕜 (n + 1) γ U) (hJ : ContDiffOn 𝕜 n J Ω)
    (hγΩ : Set.MapsTo γ U Ω) :
    ContDiffOn 𝕜 n (adaptedNormalExtension γ J) (U ×ˢ Set.univ) := by
  intro p hp
  exact (contDiffAt_adaptedNormalExtension (hγ.contDiffAt (hU.mem_nhds hp.1))
    (hJ.contDiffAt (hΩ.mem_nhds (hγΩ hp.1)))).contDiffWithinAt

/-- The adapted first jet requires only a `C^1` parametrization and a continuous structure
at the base point. In particular it does not consume a derivative of `J`. -/
theorem hasFDerivAt_adaptedNormalExtension_zero {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x)) :
    HasFDerivAt (adaptedNormalExtension γ J)
      ((fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x))) (x, 0) :=
  hasFDerivAt_normalExtension_zero (hγ.differentiableAt one_ne_zero).hasFDerivAt
    ((hJ.comp hγ.continuousAt).clm_comp (hγ.continuousAt_fderiv one_ne_zero))

/-- Along the zero section, the tangential derivatives are `Dγ` and the normal derivatives
are `J ∘ Dγ`. -/
theorem fderiv_adaptedNormalExtension_zero {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x)) :
    fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) =
      (fderiv 𝕜 γ x).coprod ((J (γ x)).comp (fderiv 𝕜 γ x)) :=
  (hasFDerivAt_adaptedNormalExtension_zero hγ hJ).fderiv

/-- The adapted derivative intertwines the standard product structure with the ambient
almost complex structure. Only its square identity at the base point is needed. -/
theorem fderiv_adaptedNormalExtension_intertwines {γ : V → W} {J : W → W →L[𝕜] W} {x : V}
    (hγ : ContDiffAt 𝕜 1 γ x) (hJ : ContinuousAt J (γ x))
    (hsq : ∀ v, J (γ x) (J (γ x) v) = -v) (v w : V) :
    fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) (-w, v) =
      J (γ x) (fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) (v, w)) := by
  rw [fderiv_adaptedNormalExtension_zero hγ hJ]
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply, map_neg,
    map_add, hsq]
  abel

/-- For a linear parametrization, the extension evaluates without a derivative operator. -/
theorem adaptedNormalExtension_continuousLinearMap (L : V →L[𝕜] W)
    (J : W → W →L[𝕜] W) (p : V × V) :
    adaptedNormalExtension L J p = L p.1 + J (L p.1) (L p.2) := by
  simp [adaptedNormalExtension, normalExtension, ContinuousLinearMap.fderiv]

/-- The standard real locus in a product has the identity as its adapted extension. -/
@[simp]
theorem adaptedNormalExtension_inl :
    adaptedNormalExtension (ContinuousLinearMap.inl 𝕜 V V)
      (fun _ ↦ (-ContinuousLinearMap.snd 𝕜 V V).prod (ContinuousLinearMap.fst 𝕜 V V)) = id := by
  funext p
  rw [adaptedNormalExtension_continuousLinearMap]
  ext <;> simp

/-- The extension depends on the structure only along the parametrized submanifold. -/
theorem adaptedNormalExtension_congr {γ : V → W} {J K : W → W →L[𝕜] W}
    (h : ∀ x, J (γ x) = K (γ x)) :
    adaptedNormalExtension γ J = adaptedNormalExtension γ K := by
  funext p
  simp only [adaptedNormalExtension, normalExtension, h]

omit [NormedAddCommGroup V] [NormedSpace 𝕜 V] in
/-- Changing the normal frame changes the extension by its action on the normal coordinate. -/
theorem normalExtension_sub_normalExtension (γ : V → W) (A B : V → E →L[𝕜] W) (p : V × E) :
    normalExtension γ A p - normalExtension γ B p = (A p.1 - B p.1) p.2 := by
  simp [normalExtension]

/-- Perturbations of the ambient structure are amplified only by the tangential derivative
and the size of the normal coordinate. -/
theorem norm_adaptedNormalExtension_sub_le (γ : V → W) (J K : W → W →L[𝕜] W)
    (p : V × V) :
    ‖adaptedNormalExtension γ J p - adaptedNormalExtension γ K p‖ ≤
      ‖J (γ p.1) - K (γ p.1)‖ * ‖fderiv 𝕜 γ p.1‖ * ‖p.2‖ := by
  rw [adaptedNormalExtension_eq_normalExtension, adaptedNormalExtension_eq_normalExtension,
    normalExtension_sub_normalExtension, ← ContinuousLinearMap.sub_comp]
  exact ContinuousLinearMap.le_of_opNorm_le _ (ContinuousLinearMap.opNorm_comp_le _ _) _

/-- The first jet is Lipschitz in the value of the ambient structure along the submanifold.
This is a quantitative comparison of actual derivatives, with no derivative assumption on `J`. -/
theorem norm_fderiv_adaptedNormalExtension_sub_le {γ : V → W}
    {J K : W → W →L[𝕜] W} {x : V} (hγ : ContDiffAt 𝕜 1 γ x)
    (hJ : ContinuousAt J (γ x)) (hK : ContinuousAt K (γ x)) :
    ‖fderiv 𝕜 (adaptedNormalExtension γ J) (x, 0) -
        fderiv 𝕜 (adaptedNormalExtension γ K) (x, 0)‖ ≤
      ‖J (γ x) - K (γ x)‖ * ‖fderiv 𝕜 γ x‖ := by
  rw [fderiv_adaptedNormalExtension_zero hγ hJ,
    fderiv_adaptedNormalExtension_zero hγ hK]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro p
  simp only [sub_apply, ContinuousLinearMap.coprod_apply, add_sub_add_left_eq_sub]
  rw [← sub_apply, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.le_of_opNorm_le _
    (ContinuousLinearMap.opNorm_comp_le _ _) _).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le p)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end TauCeti
