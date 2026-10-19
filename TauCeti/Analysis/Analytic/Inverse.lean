/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem

/-!
# The analytic inverse and implicit function theorems

Let `f : E → F` be analytic at `a`, with `E` complete, and suppose its derivative at `a` is a
continuous linear equivalence. Then `f` restricts to an `OpenPartialHomeomorph` around `a` which
is analytic on its source and whose inverse is analytic on its whole target
(`AnalyticAt.exists_openPartialHomeomorph`). Mathlib's `OpenPartialHomeomorph.analyticAt_symm`
gives analyticity of an inverse at one point where the derivative is known to be invertible.
Invertibility at the base point alone suffices here because it persists throughout the source of
the inverse function theorem's homeomorphism
(`HasStrictFDerivAt.isInvertible_of_mem_toOpenPartialHomeomorph_source`).

Applying the inverse function theorem to `(w, z) ↦ (f (w, z), w)` gives the analytic implicit
function theorem: the implicit functions of Mathlib's `ImplicitFunctionData` and
`HasStrictFDerivAt.implicitFunctionOfProdDomain` are analytic when the defining equation is. For
a scalar equation `f (w, z) = 0` with `∂f/∂z ≠ 0` this is the implicit root theorem: near a
simple zero, the zeros of `f` form the graph of an analytic function of `w`
(`AnalyticAt.exists_analyticAt_eventually_eq_zero_iff`).

Everything holds over an arbitrary nontrivially normed field `𝕜`, in particular over `ℝ` and
`ℂ`; the implicit root theorem asks `𝕜` to be complete.

## Main results

* `HasStrictFDerivAt.analyticOnNhd_toOpenPartialHomeomorph_symm`: the local inverse built by the
  inverse function theorem is analytic on its target wherever `f` is analytic on its source.
* `HasStrictFDerivAt.analyticAt_localInverse`: the local inverse is analytic at `f a`.
* `AnalyticAt.exists_openPartialHomeomorph`: the **analytic inverse function theorem**.
* `ImplicitFunctionData.analyticAt_implicitFunction` and
  `HasStrictFDerivAt.analyticAt_implicitFunctionOfProdDomain`: the **analytic implicit function
  theorem**.
* `AnalyticAt.exists_analyticAt_eventually_eq_zero_iff`: the **analytic implicit root theorem**.

## References

* S. G. Krantz, H. R. Parks, *A Primer of Real Analytic Functions*, second edition, Birkhäuser
  (2002), Chapter 2 (the real analytic inverse and implicit function theorems).
* R. C. Gunning, H. Rossi, *Analytic Functions of Several Complex Variables*, Prentice-Hall
  (1965), Chapter I (the holomorphic inverse and implicit function theorems).
-/

public section

open Filter Set
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace HasStrictFDerivAt

variable {f : E → F} {L : E ≃L[𝕜] F} {a : E}

/-- The local inverse built by the inverse function theorem is analytic at every point `y` of its
target at whose preimage `f` is analytic. Invertibility of the derivative is assumed only at the
base point `a`. -/
theorem analyticAt_toOpenPartialHomeomorph_symm (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    {y : F} (hy : y ∈ (hf.toOpenPartialHomeomorph f).target)
    (hfy : AnalyticAt 𝕜 f ((hf.toOpenPartialHomeomorph f).symm y)) :
    AnalyticAt 𝕜 (hf.toOpenPartialHomeomorph f).symm y := by
  set Θ := hf.toOpenPartialHomeomorph f
  have hΘ : ⇑Θ = f := hf.toOpenPartialHomeomorph_coe
  obtain ⟨A, hA⟩ := hf.isInvertible_of_mem_toOpenPartialHomeomorph_source (Θ.map_target hy)
    hfy.differentiableAt.hasFDerivAt
  rw [← hΘ] at hfy hA
  exact Θ.analyticAt_symm hy hfy hA.symm

/-- If `f` is analytic on the source of the homeomorphism built by the inverse function theorem,
then its inverse is analytic on the whole target. -/
theorem analyticOnNhd_toOpenPartialHomeomorph_symm (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    (hfs : AnalyticOnNhd 𝕜 f (hf.toOpenPartialHomeomorph f).source) :
    AnalyticOnNhd 𝕜 (hf.toOpenPartialHomeomorph f).symm (hf.toOpenPartialHomeomorph f).target :=
  fun _ hy ↦ hf.analyticAt_toOpenPartialHomeomorph_symm hy
    (hfs _ ((hf.toOpenPartialHomeomorph f).map_target hy))

/-- The local inverse of a map analytic at `a`, with invertible derivative there, is analytic at
`f a`. This is the several-variable form of Mathlib's `AnalyticAt.analyticAt_localInverse`. -/
theorem analyticAt_localInverse (hf : HasStrictFDerivAt f (L : E →L[𝕜] F) a)
    (ha : AnalyticAt 𝕜 f a) : AnalyticAt 𝕜 (hf.localInverse f L a) (f a) := by
  rw [localInverse_def]
  set Θ := hf.toOpenPartialHomeomorph f
  have hΘ : ⇑Θ = f := hf.toOpenPartialHomeomorph_coe
  have hL : fderiv 𝕜 Θ a = L := hΘ ▸ hf.hasFDerivAt.fderiv
  rw [← hΘ] at ha ⊢
  exact Θ.analyticAt_symm' hf.mem_toOpenPartialHomeomorph_source ha hL

end HasStrictFDerivAt

/-- **The analytic inverse function theorem.** A map analytic at `a`, whose derivative at `a` is a
continuous linear equivalence, coincides with an `OpenPartialHomeomorph` whose source is a
neighbourhood of `a` inside any prescribed neighbourhood `s`, which is analytic on its source, and
whose inverse is analytic on its target. -/
theorem AnalyticAt.exists_openPartialHomeomorph {f : E → F} {a : E} (hf : AnalyticAt 𝕜 f a)
    {L : E ≃L[𝕜] F} (hL : fderiv 𝕜 f a = L) {s : Set E} (hs : s ∈ 𝓝 a) :
    ∃ Θ : OpenPartialHomeomorph E F, ⇑Θ = f ∧ a ∈ Θ.source ∧ Θ.source ⊆ s ∧
      AnalyticOnNhd 𝕜 f Θ.source ∧ AnalyticOnNhd 𝕜 Θ.symm Θ.target := by
  have hstrict : HasStrictFDerivAt f (L : E →L[𝕜] F) a := hL ▸ hf.hasStrictFDerivAt
  -- `F` is complete, being isomorphic to `E`
  have : CompleteSpace F :=
    (completeSpace_congr (e := L.symm.toLinearEquiv.toEquiv) L.symm.isUniformEmbedding).2 ‹_›
  -- restrict to the open set of points of `interior s` at which `f` is analytic
  have ht : IsOpen (interior s ∩ {x | AnalyticAt 𝕜 f x}) :=
    isOpen_interior.inter (isOpen_analyticAt 𝕜 f)
  set Θ := (hstrict.toOpenPartialHomeomorph f).restrOpen _ ht
  have hsource : Θ.source ⊆ interior s ∩ {x | AnalyticAt 𝕜 f x} := inter_subset_right
  refine ⟨Θ, rfl,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, mem_interior_iff_mem_nhds.2 hs, hf⟩,
    hsource.trans (inter_subset_left.trans interior_subset), fun x hx ↦ (hsource hx).2,
    fun y hy ↦ hstrict.analyticAt_toOpenPartialHomeomorph_symm hy.1 (hsource (Θ.map_target hy)).2⟩

namespace ImplicitFunctionData

variable [CompleteSpace F] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- **The analytic implicit function theorem**, general form: the implicit function defined by
analytic `leftFun` and `rightFun` is analytic. -/
theorem analyticAt_implicitFunction {φ : ImplicitFunctionData 𝕜 E F G}
    (hl : AnalyticAt 𝕜 φ.leftFun φ.pt) (hr : AnalyticAt 𝕜 φ.rightFun φ.pt) :
    AnalyticAt 𝕜 φ.implicitFunction.uncurry (φ.prodFun φ.pt) := by
  rw [implicitFunction_def, Function.uncurry_curry, ← HasStrictFDerivAt.localInverse_def]
  exact φ.hasStrictFDerivAt.analyticAt_localInverse
    ((hl.prod hr).congr (.of_forall fun x ↦ (φ.prodFun_apply x).symm))

end ImplicitFunctionData

namespace HasStrictFDerivAt

variable [CompleteSpace F] {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [CompleteSpace E₁] {f : E₁ × E → F} {f'u : E₁ × E →L[𝕜] F} {u : E₁ × E}

/-- **The analytic implicit function theorem.** If `f : E₁ × E → F` is analytic at `u` and its
partial derivative in the second variable is invertible there, the implicit function `ψ` with
`f (x, ψ x) = f u` near `u.1` is analytic at `u.1`. -/
theorem analyticAt_implicitFunctionOfProdDomain (dfu : HasStrictFDerivAt f f'u u)
    (if₂u : (f'u ∘L .inr 𝕜 E₁ E).IsInvertible) (hf : AnalyticAt 𝕜 f u) :
    AnalyticAt 𝕜 (dfu.implicitFunctionOfProdDomain if₂u) u.1 := by
  rw [implicitFunctionOfProdDomain_def]
  set φ := dfu.implicitFunctionDataOfProdDomain if₂u
  have hφ : AnalyticAt 𝕜 φ.implicitFunction.uncurry (f u, u.1) := by
    simpa [φ] using φ.analyticAt_implicitFunction (by simpa [φ] using hf)
      (by simpa [φ] using analyticAt_fst)
  exact analyticAt_snd.comp (hφ.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl)

end HasStrictFDerivAt

/-- **The analytic implicit root theorem.** Let `f (w, z)` be analytic at `u = (w₀, z₀)`, with
`f u = 0` and `∂f/∂z ≠ 0` at `u`. Then there is a function `g`, analytic at `w₀` with
`g w₀ = z₀`, such that near `u` the zeros of `f` are exactly the points `(w, g w)`; in particular
`f (w, g w) = 0` for all `w` near `w₀`. -/
theorem AnalyticAt.exists_analyticAt_eventually_eq_zero_iff [CompleteSpace 𝕜] {f : E × 𝕜 → 𝕜}
    {u : E × 𝕜} (hf : AnalyticAt 𝕜 f u) (hu : f u = 0)
    (h : deriv (fun z ↦ f (u.1, z)) u.2 ≠ 0) :
    ∃ g : E → 𝕜, AnalyticAt 𝕜 g u.1 ∧ g u.1 = u.2 ∧ (∀ᶠ w in 𝓝 u.1, f (w, g w) = 0) ∧
      ∀ᶠ v in 𝓝 u, f v = 0 ↔ g v.1 = v.2 := by
  have dfu := hf.hasStrictFDerivAt
  -- the partial derivative in `z` is multiplication by `deriv (fun z ↦ f (u.1, z)) u.2`
  have hpartial : fderiv 𝕜 f u ∘L .inr 𝕜 E 𝕜 =
      ContinuousLinearEquiv.unitsEquivAut 𝕜 (.mk0 _ h) := by
    have hd : HasFDerivAt (fun z ↦ f (u.1, z)) (fderiv 𝕜 f u ∘L .inr 𝕜 E 𝕜) u.2 :=
      hf.differentiableAt.hasFDerivAt.comp u.2 (hasFDerivAt_prodMk_right u.1 u.2)
    ext
    simp [hd.hasDerivAt.deriv]
  have if₂u : (fderiv 𝕜 f u ∘L .inr 𝕜 E 𝕜).IsInvertible := ⟨_, hpartial.symm⟩
  refine ⟨dfu.implicitFunctionOfProdDomain if₂u,
    dfu.analyticAt_implicitFunctionOfProdDomain if₂u hf,
    eq_of_tendsto_nhds (dfu.tendsto_implicitFunctionOfProdDomain if₂u), ?_, ?_⟩
  · simpa [hu] using dfu.eventually_apply_implicitFunctionOfProdDomain if₂u
  · simpa [hu, eq_comm] using dfu.eventually_apply_eq_iff_implicitFunctionOfProdDomain if₂u
