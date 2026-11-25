/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.SpatialDerivative
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Bilinear
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CompLeft
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Differentiation
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.Inclusion
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.OfDeriv
import TauCeti.Analysis.Holder.CompLinear
import TauCeti.Analysis.Holder.Inclusion
import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.DirectionalDerivative

/-!
# Higher regularity for the parabolic Cauchy problem

On `ℝⁿ = EuclideanSpace ℝ ι` and a time slab `ℝⁿ × [0, T]`, let

`P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u`

have coefficients in `C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic, and let `u` be the
solution in `C_b^{2+α,1+α/2}` of the Cauchy problem `P u = f`, `u(·, 0) = g`
(`TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE`). This file proves that the solution is
as regular as the data allow, at every order `k`: if the coefficients and the forcing lie in the
parabolic Hölder space `C_{par,b}^{k+α}` (`TauCeti.ParabolicCkHolderSpace`) and the initial datum
lies in `C_b^{k+2,α}`, then `u` lies in `C_{par,b}^{k+2+α}`
(`TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply`). This is the
regularity half of the Schauder theory of the Cauchy problem in every order; no compatibility
condition is needed on the whole space.

## The argument

The proof is by induction on `k`, the case `k = 0` being the base theory. For the step from `k` to
`k + 1`, the induction hypothesis puts `u` in `C_{par,b}^{k+2+α}`. Fix a coordinate direction `e`.
By `TauCeti.ParabolicC2HolderSpace.euclideanInitialDataCLE_symm_apply_eq_spatialFDerivL_apply`, the
derivative `∂ₑu` solves the Cauchy problem for the same operator with forcing
`∂ₑf + (∂ₑaⁱʲ) ∂ᵢ∂ⱼu + (∂ₑbⁱ) ∂ᵢu + (∂ₑc) u` and initial datum `∂ₑg`. The new forcing lies in
`C_{par,b}^{k+α}`, since the derivatives of the data lose one order, `D_x²u` loses two from `u`, and
the spaces are closed under products (`ContinuousLinearMap.compParabolicCkHolder₂`), and `∂ₑg` lies
in `C_b^{k+2,α}`. So the induction hypothesis puts each `∂ₑu`, hence the gradient `D_x u`, in
`C_{par,b}^{k+2+α}`. The equation `∂ₜu = f + aⁱʲ ∂ᵢ∂ⱼu + bⁱ ∂ᵢu + c u` then puts `∂ₜu` in
`C_{par,b}^{k+1+α}`, and a map whose spatial and time derivatives lie in these two spaces lies in
`C_{par,b}^{k+3+α}` (`TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 4.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti.ParabolicC2HolderSpace

open Set ParabolicSpaceTime
open scoped NNReal

variable {α : ℝ≥0}

/-! ### Lowering the order -/

section Lower

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- A map with the values of a parabolic Hölder map of order `k + 1` has those of one of order
`k`. -/
private theorem exists_coe_eq_of_exists_succ (hα : α ≤ 1) {k : ℕ} {X : slab (E := E) a b → F}
    (hX : ∃ A : ParabolicCkHolderSpace (k + 1) α E F hab, ⇑A = X) :
    ∃ A : ParabolicCkHolderSpace k α E F hab, ⇑A = X :=
  hX.elim fun A hA ↦
    (ParabolicCkHolderSpace.exists_coe_eq_of_le hα k.le_succ A).imp fun _ h ↦ h.trans hA

end Lower

/-! ### Identifying the derivatives -/

section Derivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {a b : ℝ} {hab : a < b}

/-- The directional derivative of a coefficient of order `k + 1` along `e` is a coefficient of
order `k`. -/
private theorem exists_hasLineDerivAt (hα : α ≤ 1) {k : ℕ}
    {X : HolderSpace α (slab (E := E) a b) F}
    {A : ParabolicCkHolderSpace (k + 1) α E F hab} (hA : ⇑A = ⇑X)
    (e : E) :
    ∃ X' : HolderSpace α (slab (E := E) a b) F,
      (∃ A' : ParabolicCkHolderSpace k α E F hab, ⇑A' = ⇑X') ∧
        ∀ (t : Icc a b) x,
          HasLineDerivAt ℝ (fun y ↦ X (slabMk y t)) (X' (slabMk x t)) x e := by
  set A' := ParabolicCkHolderSpace.spatialLineDerivL e A
  obtain ⟨X', hX'⟩ := ParabolicCkHolderSpace.exists_holderSpace_coe_eq hα A'
  refine ⟨X', ⟨A', hX'.symm⟩, fun t x ↦ ?_⟩
  have hd := ParabolicCkHolderSpace.hasSpatialLineDerivAt e A t x
  rwa [hA, ← hX'] at hd

/-- The directional derivative of an initial datum of order `k + 3` along `e` is an initial
datum of order `k + 2`. -/
private theorem exists_fderiv_apply_eq (hα : α ≤ 1) {k : ℕ}
    {g : CkHolderSpace 2 α E F}
    {G : CkHolderSpace (k + 3) α E F} (hG : ⇑G = ⇑g) (e : E) :
    ∃ g' : CkHolderSpace 2 α E F,
      (∃ G' : CkHolderSpace (k + 2) α E F, ⇑G' = ⇑g') ∧
        ∀ x, fderiv ℝ g x e = g' x := by
  set G' := CkHolderSpace.compLeftL (ContinuousLinearMap.apply ℝ F e)
    (CkHolderSpace.fderivL (k + 2) α E F G)
  obtain ⟨g', hg'⟩ := CkHolderSpace.exists_coe_eq_of_le hα (by omega : 2 ≤ k + 2) G'
  refine ⟨g', ⟨G', hg'.symm⟩, fun x ↦ ?_⟩
  rw [hg', CkHolderSpace.compLeftL_apply, ContinuousLinearMap.apply_apply,
    CkHolderSpace.fderivL_apply, hG]

end Derivatives

/-! ### The Euclidean data -/

section Euclidean

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0} {hT : (0 : ℝ) < T}

/-- The forcing `F₀ + aⁱʲ (D_x W)(eᵢ, eⱼ) + bⁱ W(eᵢ) + c W₀` assembled from maps of order `j` and a
gradient field `W` of order `j + 1` has order `j`. -/
private theorem exists_apply_eq_add_sum (hα : α ≤ 1) {j : ℕ}
    (A : ι → ι → ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT)
    (B : ι → ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT)
    (C F₀ W₀ : ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT)
    (W : ParabolicCkHolderSpace (j + 1) α (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι →L[ℝ] ℝ) hT) :
    ∃ Z : ParabolicCkHolderSpace j α (EuclideanSpace ℝ ι) ℝ hT, ∀ p, Z p = F₀ p +
      (∑ i, ∑ l, A i l p * ParabolicCkHolderSpace.spatialFDerivL j α (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι →L[ℝ] ℝ) hT W p
          (EuclideanSpace.single i 1) (EuclideanSpace.single l 1) +
        ∑ i, B i p * W p (EuclideanSpace.single i 1) + C p * W₀ p) := by
  set mulL := (ContinuousLinearMap.mul ℝ ℝ).compParabolicCkHolder₂ (k := j)
    (E := EuclideanSpace ℝ ι) (hab := hT) hα
  refine ⟨F₀ + (∑ i, ∑ l, mulL (A i l) (ParabolicCkHolderSpace.compLeftL
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single l 1)).comp
        (ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single i 1)))
      (ParabolicCkHolderSpace.spatialFDerivL j α (EuclideanSpace ℝ ι)
      (EuclideanSpace ℝ ι →L[ℝ] ℝ) hT W)) +
    ∑ i, mulL (B i) (ParabolicCkHolderSpace.compLeftL
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))
      (ParabolicCkHolderSpace.inclusionL hα W)) + mulL C W₀), fun p ↦ ?_⟩
  simp [mulL, Finset.sum_apply]

variable {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- **The induction step for one direction.** If the solutions of the Cauchy problems with data of
order `k` have order `k + 2`, the coefficients and forcing have order `k + 1` and the initial datum
order `k + 3`, then every directional derivative `∂ₑu` of the solution has order `k + 2`. -/
private theorem exists_apply_eq_spatialFDerivL_apply (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℕ}
    (ih : ∀ (f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ),
      (∃ F : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑F = ⇑f') →
      (∃ G : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ, ⇑G = ⇑g') →
      ∃ U : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
        ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f', g')))
    (hak : ∀ i j, ∃ A : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑A = ⇑(a i j))
    (hbk : ∀ i, ∃ B : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑B = ⇑(b i))
    (hck : ∃ C : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑C = ⇑c)
    {f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (hfk : ∃ F : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑F = ⇑f)
    {g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hgk : ∃ G : CkHolderSpace (k + 3) α (EuclideanSpace ℝ ι) ℝ, ⇑G = ⇑g)
    {U : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT}
    (hU : ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)))
    (e : EuclideanSpace ℝ ι) :
    ∃ V : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT, ∀ p,
      V p = spatialFDerivL ((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) p e := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)
  choose A hA using hak
  choose B hB using hbk
  obtain ⟨C, hC⟩ := hck
  obtain ⟨F, hF⟩ := hfk
  obtain ⟨G, hG⟩ := hgk
  -- The derivatives of the data along `e` have one order less.
  choose a' ha'k ha' using fun i j ↦ exists_hasLineDerivAt hα₁.le (hA i j) e
  choose b' hb'k hb' using fun i ↦ exists_hasLineDerivAt hα₁.le (hB i) e
  obtain ⟨c', hc'k, hc'⟩ := exists_hasLineDerivAt hα₁.le hC e
  obtain ⟨f', hf'k, hf'⟩ := exists_hasLineDerivAt hα₁.le hF e
  obtain ⟨g', hg'k, hg'⟩ := exists_fderiv_apply_eq hα₁.le hG e
  have hg'u (x : EuclideanSpace ℝ ι) :
      spatialFDerivL u (slabMk x ⟨0, left_mem_Icc.2 hT.le⟩) e = g' x := by
    rw [← hg', ← fderiv_eq]
    congr 2
    funext y
    exact euclideanInitialDataCLE_symm_apply_slabMk_zero _ y
  -- `∂ₑu` solves the differentiated Cauchy problem, whose forcing has order `k`.
  have hsol := euclideanInitialDataCLE_symm_apply_eq_spatialFDerivL_apply hα₀ hα₁ hT ha ha' hb'
    hc' hf' (euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply _) hg'u
  choose A' hA' using ha'k
  choose B' hB' using hb'k
  obtain ⟨C', hC'⟩ := hc'k
  obtain ⟨F', hF'⟩ := hf'k
  obtain ⟨U₀, hU₀⟩ := ParabolicCkHolderSpace.exists_coe_eq_of_le hα₁.le (by omega : k ≤ k + 2) U
  have hW₁ := ParabolicCkHolderSpace.spatialFDerivL_eq_of_coe_eq hU
  obtain ⟨Z, hZ⟩ := exists_apply_eq_add_sum hα₁.le A' B' C' F' U₀
    (ParabolicCkHolderSpace.spatialFDerivL (k + 1) α _ ℝ hT U)
  have hZf : ⇑Z = ⇑(f' + spatialOperatorL hα₁.le (euclideanSecondOrderCoeff a')
      (euclideanFirstOrderCoeff b') (euclideanZerothOrderCoeff c') u) := funext fun p ↦ by
    rw [hZ, hW₁, ParabolicCkHolderSpace.spatialFDerivL_eq_spatialSecondFDerivL hW₁, congrFun hU₀,
      congrFun hU]
    simp [hA', hB', hC', hF']
  obtain ⟨V, hV⟩ := ih _ g' ⟨Z, hZf⟩ hg'k
  exact ⟨V, fun p ↦ (congrFun hV p).trans (hsol p)⟩

/-- **The induction step.** If the solutions of the Cauchy problems with data of order `k` have
order `k + 2`, the coefficients and forcing have order `k + 1` and the initial datum order `k + 3`,
then the solution has order `k + 3`. -/
private theorem exists_coe_eq_succ (hα₀ : 0 < α) (hα₁ : α < 1) {k : ℕ}
    (ih : ∀ (f' : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ)
      (g' : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ),
      (∃ F : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑F = ⇑f') →
      (∃ G : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ, ⇑G = ⇑g') →
      ∃ U : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
        ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f', g')))
    (hak : ∀ i j, ∃ A : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑A = ⇑(a i j))
    (hbk : ∀ i, ∃ B : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑B = ⇑(b i))
    (hck : ∃ C : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑C = ⇑c)
    {f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (hfk : ∃ F : ParabolicCkHolderSpace (k + 1) α (EuclideanSpace ℝ ι) ℝ hT, ⇑F = ⇑f)
    {g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hgk : ∃ G : CkHolderSpace (k + 3) α (EuclideanSpace ℝ ι) ℝ, ⇑G = ⇑g) :
    ∃ U : ParabolicCkHolderSpace (k + 3) α (EuclideanSpace ℝ ι) ℝ hT,
      ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  set u := (euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)
  -- By the induction hypothesis `u` has order `k + 2`.
  obtain ⟨G₀, hG₀⟩ := hgk
  obtain ⟨G₁, hG₁⟩ := CkHolderSpace.exists_coe_eq_of_le hα₁.le (by omega : k + 2 ≤ k + 3) G₀
  obtain ⟨U, hU⟩ := ih f g (exists_coe_eq_of_exists_succ hα₁.le hfk) ⟨G₁, hG₁.trans hG₀⟩
  -- Its gradient has order `k + 2`, assembled from the directional derivatives.
  choose V hV using fun l ↦ exists_apply_eq_spatialFDerivL_apply hα₀ hα₁ ih hak hbk hck hfk
    ⟨G₀, hG₀⟩ hU (EuclideanSpace.single l 1)
  set Gr := ∑ l, ParabolicCkHolderSpace.compLeftL
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.proj (𝕜 := ℝ) l)) (V l)
  have hGr (p : slab (E := EuclideanSpace ℝ ι) 0 T) : Gr p = spatialFDerivL u p := by
    have hcoord (l : ι) : (EuclideanSpace.basisFun ι ℝ).toBasis.coord l =
        (EuclideanSpace.proj l : EuclideanSpace ℝ ι →L[ℝ] ℝ) :=
      LinearMap.ext fun v ↦ by simp [Module.Basis.coord_apply]
    refine ContinuousLinearMap.coe_injective ?_
    simpa [Gr, Finset.sum_apply, hV, EuclideanSpace.basisFun_apply, hcoord] using
      (EuclideanSpace.basisFun ι ℝ).toBasis.sum_dual_apply_smul_coord
        (spatialFDerivL u p : Module.Dual ℝ (EuclideanSpace ℝ ι))
  -- By the equation, its time derivative has order `k + 1`.
  choose A hA using hak
  choose B hB using hbk
  obtain ⟨C, hC⟩ := hck
  obtain ⟨F, hF⟩ := hfk
  obtain ⟨H, hH⟩ := exists_apply_eq_add_sum hα₁.le A B C F
    (ParabolicCkHolderSpace.inclusionL hα₁.le U) Gr
  have hHu (p : slab (E := EuclideanSpace ℝ ι) 0 T) : H p = timeDerivL u p := by
    have hP := congrArg (fun w ↦ w p)
      (euclideanParabolicOperatorL_euclideanInitialDataCLE_symm_apply (hα₀ := hα₀)
        (hα₁ := hα₁) (hT := hT) (a := a) (b := b) (c := c) (ha := ha) (f, g))
    simp only [euclideanParabolicOperatorL_apply] at hP
    rw [hH, ParabolicCkHolderSpace.inclusionL_apply, hGr,
      ParabolicCkHolderSpace.spatialFDerivL_eq_spatialSecondFDerivL hGr, congrFun hU]
    simp only [hA, hB, hC, hF]
    linarith
  have hval : ⇑(valueL u) = ⇑u := funext (valueL_apply u)
  refine ⟨ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv (k := k + 1) (valueL u) Gr H
    (fun t x ↦ ?_) (fun x t ↦ ?_), funext fun p ↦ ?_⟩
  · rw [hval, hGr]
    exact u.hasSpatialFDerivAt t x
  · rw [hval, hHu]
    exact u.hasTimeDerivWithinAt x t
  · rw [ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv_apply, valueL_apply]

/-- **Higher regularity for the parabolic Cauchy problem.** Let `0 < α < 1`, let `aⁱʲ`, `bⁱ`, `c`
be coefficients in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, and let `u` be the
solution in `C_b^{2+α,1+α/2}` of `∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u = f`, `u(·, 0) = g`. If the
coefficients and the forcing lie in the parabolic Hölder space `C_{par,b}^{k+α}` and the initial
datum lies in `C_b^{k+2,α}`, then `u` lies in `C_{par,b}^{k+2+α}`. -/
theorem exists_coe_eq_euclideanInitialDataCLE_symm_apply (hα₀ : 0 < α) (hα₁ : α < 1) (k : ℕ)
    (hak : ∀ i j, ∃ A : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑A = ⇑(a i j))
    (hbk : ∀ i, ∃ B : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑B = ⇑(b i))
    (hck : ∃ C : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑C = ⇑c)
    {f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (hfk : ∃ F : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑F = ⇑f)
    {g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hgk : ∃ G : CkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ, ⇑G = ⇑g) :
    ∃ U : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  induction k generalizing f g with
  | zero =>
    exact ⟨ParabolicCkHolderSpace.equivParabolicC2HolderSpace.symm _,
      ParabolicCkHolderSpace.coe_equivParabolicC2HolderSpace_symm _⟩
  | succ k ih =>
    exact exists_coe_eq_succ hα₀ hα₁
      (fun f' g' hf' hg' ↦ ih (fun i j ↦ exists_coe_eq_of_exists_succ hα₁.le (hak i j))
        (fun i ↦ exists_coe_eq_of_exists_succ hα₁.le (hbk i))
        (exists_coe_eq_of_exists_succ hα₁.le hck) hf' hg')
      hak hbk hck hfk hgk

end Euclidean

end TauCeti.ParabolicC2HolderSpace
