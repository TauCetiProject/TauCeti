/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Integrals of two-forms over rectangles and their homotopy invariance

The integral of a two-form `φ` on a manifold `M` over a map `u : ℝ × ℝ → M` on the rectangle with
opposite corners `a` and `b` is

`∫_u φ = ∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds`,

the iterated integral of the pullback `u^* φ` against the coordinate orientation of the plane
(`TauCeti.rectangleIntegral`). For a symplectic form this is the symplectic area of `u`. When
`u(s, ·)` is a loop for every `s`, so that `u` is a cylinder between the loops `u(a.1, ·)` and
`u(b.1, ·)`, it is the area term `∫ ū^* ω` of the Hamiltonian action functional on the free loop
space, in which `ū` joins a loop to a reference loop; and when one of these loops is constant,
`u` is a cap of the other.

The basic property of these integrals is **Stokes' formula for a homotopy**. Let `φ` be closed and
let `Φ : (ℝ × ℝ) × ℝ → M` be a `C²` family of maps `Φ(·, c)` of the plane. The integral of the
closed form `Φ^* φ` over the boundary of the cube `[a, b] × [0, 1]` vanishes, so the difference of
the integrals over the top face `Φ(·, 1)` and the bottom face `Φ(·, 0)` is a signed sum of the
integrals over the four side faces, swept out by the four edges of the rectangle during the
homotopy (`TauCeti.rectangleIntegral_sub_rectangleIntegral_eq_sides`). A side face contributes
nothing when it is degenerate: when its edge stays fixed during the homotopy, or remains a
constant path. Indeed the integral over any map that only depends on one of the two coordinates
vanishes (`TauCeti.rectangleIntegral_comp_fst`, `TauCeti.rectangleIntegral_comp_snd`). Hence the
integral over a cylinder is invariant under homotopies through cylinders whose boundary loops are
each either fixed or constant (`TauCeti.rectangleIntegral_eq_of_homotopy`). This covers homotopies
of cylinders relative to their boundary loops, homotopies of caps relative to the capped loop, and
homotopies of spheres presented as cylinders between constant loops. It is the analytic input for
showing that the Hamiltonian action of a loop does not depend on the choice of cylinder or cap
within a homotopy class.

This is the two-dimensional analogue of the line integral `TauCeti.pathIntegral`: it integrates
along an arbitrary map of the plane, without the integrability conditions of the integral of a top
form over the rectangle manifold.

The proof pulls `φ` back to the flat form `ψ = Φ^* φ` on `(ℝ × ℝ) × ℝ`, which is closed because
pullback commutes with the exterior derivative, and expresses the integral over each face of the
cube as an iterated integral of `ψ` by the chain rule. The flat statement is Stokes' formula on the
boundary of a cube (`TauCeti.integral2_slice_sub_eq_sides`), proved with the cylinder homotopy
operator and Stokes' formula on a rectangle; no Stokes theorem on a manifold with corners is used.

## Main definitions

* `TauCeti.rectangleIntegral φ u a b`: the integral of the two-form `φ` over the map `u` on the
  rectangle with opposite corners `a` and `b`.

## Main results

* `TauCeti.rectangleIntegral_mpullback`: naturality under pullback of forms.
* `TauCeti.rectangleIntegral_comp_fst`, `TauCeti.rectangleIntegral_comp_snd`: the integral over a
  map depending on only one coordinate vanishes.
* `TauCeti.rectangleIntegral_sub_rectangleIntegral_eq_sides`: Stokes' formula for a homotopy of
  maps of a rectangle, for a closed form.
* `TauCeti.rectangleIntegral_eq_of_homotopy`: homotopy invariance of the integral of a closed form
  over a cylinder whose boundary loops stay fixed or constant.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, Springer, 1982, §4
  (the homotopy operator and homotopy invariance).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS, 2012,
  the chapter on Floer homology (the symplectic action and its dependence on the cylinder).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1 (the action functional on contractible loops).
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold Interval ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The integral of a two-form `φ` over a map `u : ℝ × ℝ → M` on the rectangle with opposite
corners `a` and `b`, oriented by the coordinates `(s, t)` of the plane: the iterated integral
`∫_{a.1}^{b.1} ∫_{a.2}^{b.2} φ_{u(s, t)}(∂_s u, ∂_t u) dt ds` of the pullback `u^* φ` evaluated on
the coordinate vectors. Exchanging the two corners in one coordinate changes its sign. -/
def rectangleIntegral (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) : F :=
  ∫ s in a.1..b.1, ∫ t in a.2..b.2, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)]

/-- The defining formula of `TauCeti.rectangleIntegral`. -/
theorem rectangleIntegral_def (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ u a b =
      ∫ s in a.1..b.1, ∫ t in a.2..b.2, mpullback 𝓘(ℝ, ℝ × ℝ) I u φ (s, t) ![(1, 0), (0, 1)] :=
  (rfl)

/-- The integral over a map `u` is the iterated integral of `φ` on the partial derivatives
of `u`. -/
theorem rectangleIntegral_eq (φ : RoughForm I M F 2) (u : ℝ × ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ u a b = ∫ s in a.1..b.1, ∫ t in a.2..b.2,
      φ (u (s, t)) ![mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (1, 0),
        mfderiv 𝓘(ℝ, ℝ × ℝ) I u (s, t) (0, 1)] := by
  refine intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [mpullback_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The integral is natural under pullback of forms. -/
theorem rectangleIntegral_mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] {f : M → M'} (φ : RoughForm I' M' F 2) {u : ℝ × ℝ → M} {a b : ℝ × ℝ}
    (hf : ∀ z ∈ [[a.1, b.1]] ×ˢ [[a.2, b.2]], MDifferentiableAt I I' f (u z))
    (hu : ∀ z ∈ [[a.1, b.1]] ×ˢ [[a.2, b.2]], MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z) :
    rectangleIntegral (mpullback I I' f φ) u a b = rectangleIntegral φ (f ∘ u) a b := by
  refine intervalIntegral.integral_congr fun s hs ↦ intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [mpullback_comp_at (hu _ ⟨hs, ht⟩) (hf _ ⟨hs, ht⟩)]

/-- The pullback of a form along `γ ∘ P`, for a continuous linear map `P : ℝ × ℝ → ℝ` with an
affine section `j`, vanishes on every family of vectors one of which lies in the kernel of `P`.
Where `γ` is differentiable this is the chain rule; where it is not, neither is `γ ∘ P`, since
`γ = (γ ∘ P) ∘ j`, and the pullback is zero. -/
private theorem mpullback_comp_clm_apply_eq_zero {k : ℕ} (φ : RoughForm I M F k) (γ : ℝ → M)
    (P : ℝ × ℝ →L[ℝ] ℝ) {j : ℝ → ℝ × ℝ} (hj : Differentiable ℝ j) (hjP : ∀ t, P (j t) = t)
    {z : ℝ × ℝ} (hjz : j (P z) = z) {v : Fin k → ℝ × ℝ} {i : Fin k} (hv : P (v i) = 0) :
    mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ P) φ z v = 0 := by
  by_cases hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (P z)
  · rw [mpullback_comp_apply_of_hasFDerivAt P.hasFDerivAt hγ]
    exact (mpullback 𝓘(ℝ, ℝ) I γ φ (P z)).map_coord_zero i hv
  · have hnd : ¬ MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (γ ∘ P) z := by
      intro h
      refine hγ ?_
      have hγ' : γ = (γ ∘ P) ∘ j := funext fun t ↦ by simp [hjP]
      rw [hγ']
      exact (hjz ▸ h).comp (P z) (hj (P z)).mdifferentiableAt
    have h0 : mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ P) φ z = 0 := by
      ext w
      rw [mpullback_apply, mfderiv_zero_of_not_mdifferentiableAt hnd,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
      exact (φ _).map_coord_zero i (zero_apply _)
    -- The zero alternating map evaluates to zero.
    rw [h0]
    rfl

/-- The integral of a two-form over a map that only depends on the second coordinate vanishes. -/
@[simp]
theorem rectangleIntegral_comp_snd (φ : RoughForm I M F 2) (γ : ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ (γ ∘ Prod.snd) a b = 0 := by
  have h (z : ℝ × ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ Prod.snd) φ z ![(1, 0), (0, 1)] = 0 :=
    mpullback_comp_clm_apply_eq_zero φ γ (.snd ℝ ℝ ℝ) (j := fun t ↦ (z.1, t)) (by fun_prop)
      (fun _ ↦ rfl) rfl (i := 0) rfl
  simp [rectangleIntegral_def, h]

/-- The integral of a two-form over a map that only depends on the first coordinate vanishes. -/
@[simp]
theorem rectangleIntegral_comp_fst (φ : RoughForm I M F 2) (γ : ℝ → M) (a b : ℝ × ℝ) :
    rectangleIntegral φ (γ ∘ Prod.fst) a b = 0 := by
  have h (z : ℝ × ℝ) :
      mpullback 𝓘(ℝ, ℝ × ℝ) I (γ ∘ Prod.fst) φ z ![(1, 0), (0, 1)] = 0 :=
    mpullback_comp_clm_apply_eq_zero φ γ (.fst ℝ ℝ ℝ) (j := fun s ↦ (s, z.2)) (by fun_prop)
      (fun _ ↦ rfl) rfl (i := 1) rfl
  simp [rectangleIntegral_def, h]

/-- A side face of a homotopy has zero integral when its edge stays fixed, or remains a constant
path, during the homotopy. -/
private theorem rectangleIntegral_side_eq_zero (φ : RoughForm I M F 2) {Φ : (ℝ × ℝ) × ℝ → M}
    {x y : ℝ} (h : (∀ t c, Φ ((x, t), c) = Φ ((x, t), 0)) ∨ ∀ t c, Φ ((x, t), c) = Φ ((x, y), c))
    (a b : ℝ × ℝ) : rectangleIntegral φ (fun p ↦ Φ ((x, p.1), p.2)) a b = 0 := by
  rcases h with h | h
  · rw [show (fun p : ℝ × ℝ ↦ Φ ((x, p.1), p.2)) = (fun t ↦ Φ ((x, t), 0)) ∘ Prod.fst from
      funext fun p ↦ h p.1 p.2]
    exact rectangleIntegral_comp_fst φ _ a b
  · rw [show (fun p : ℝ × ℝ ↦ Φ ((x, p.1), p.2)) = (fun c ↦ Φ ((x, y), c)) ∘ Prod.snd from
      funext fun p ↦ h p.1 p.2]
    exact rectangleIntegral_comp_snd φ _ a b

variable [CompleteSpace F] [IsManifold I 2 M]

/-- **Stokes' formula for a homotopy of maps of a rectangle.** Let `φ` be a closed `C¹` two-form
and `Φ : (ℝ × ℝ) × ℝ → M` a `C²` homotopy from `Φ(·, 0)` to `Φ(·, 1)`. The integral of `Φ^* φ`
over the boundary of the cube `[a, b] × [0, 1]` vanishes: the change of the integral over the
rectangle `[a, b]` from `Φ(·, 0)` to `Φ(·, 1)` is the signed sum of the integrals over the side
faces `(t, c) ↦ Φ((a.1, t), c)`, `(t, c) ↦ Φ((b.1, t), c)`, `(s, c) ↦ Φ((s, a.2), c)` and
`(s, c) ↦ Φ((s, b.2), c)` swept out by the edges of the rectangle. -/
theorem rectangleIntegral_sub_rectangleIntegral_eq_sides {φ : RoughForm I M F 2}
    (hφ : IsSmoothForm I 1 φ) (hdφ : mextDeriv φ = 0) {Φ : (ℝ × ℝ) × ℝ → M}
    (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ) (a b : ℝ × ℝ) :
    rectangleIntegral φ (fun z ↦ Φ (z, 1)) a b - rectangleIntegral φ (fun z ↦ Φ (z, 0)) a b =
      (rectangleIntegral φ (fun p ↦ Φ ((a.1, p.1), p.2)) (a.2, 0) (b.2, 1) -
        rectangleIntegral φ (fun p ↦ Φ ((b.1, p.1), p.2)) (a.2, 0) (b.2, 1)) -
      (rectangleIntegral φ (fun p ↦ Φ ((p.1, a.2), p.2)) (a.1, 0) (b.1, 1) -
        rectangleIntegral φ (fun p ↦ Φ ((p.1, b.2), p.2)) (a.1, 0) (b.1, 1)) := by
  -- The flat closed form `ψ = Φ^* φ` on `(ℝ × ℝ) × ℝ` and its cylinder homotopy `β = h ψ`.
  let ψ : (ℝ × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) [⋀^Fin 2]→L[ℝ] F := mpullback 𝓘(ℝ, (ℝ × ℝ) × ℝ) I Φ φ
  have hΦd : MDifferentiable 𝓘(ℝ, (ℝ × ℝ) × ℝ) I Φ := hΦ.mdifferentiable two_ne_zero
  have hψ : ContDiff ℝ 1 ψ := by
    have h := hφ.mpullback (f := Φ) (by simpa [one_add_one_eq_two] using hΦ)
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    exact (RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace
      (((isSmoothForm_def _ _).mp h x).contMDiffWithinAt (s := univ))).contDiffAt Filter.univ_mem
  have hdψ : extDeriv ψ = 0 := by
    funext x
    rw [← mextDeriv_eq_extDeriv,
      ← mpullback_mextDeriv hΦ ((isSmoothBundleForm_def _ _).mpr hφ.contMDiff), hdφ,
      mpullback_zero]
    -- Both sides are the zero form at `x`, as a manifold form and as a flat form.
    rfl
  -- Every face is a composite `Φ ∘ L` with `L` affine, and its integral is the iterated integral
  -- of `ψ` on the images under `dL` of the coordinate vectors.
  have hface {L : ℝ × ℝ → (ℝ × ℝ) × ℝ} {A : ℝ × ℝ →L[ℝ] (ℝ × ℝ) × ℝ}
      (hL : ∀ p, HasFDerivAt L A p) (a' b' : ℝ × ℝ) :
      rectangleIntegral φ (Φ ∘ L) a' b' =
        ∫ s in a'.1..b'.1, ∫ t in a'.2..b'.2, ψ (L (s, t)) ![A (1, 0), A (0, 1)] := by
    refine intervalIntegral.integral_congr fun s _ ↦ intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [mpullback_comp_apply_of_hasFDerivAt (hL _) (hΦd _)]
    refine (ContinuousAlternatingMap.compContinuousLinearMap_apply _ _ _).trans (congrArg _ ?_)
    funext i
    fin_cases i <;> rfl
  have hs (x : ℝ) := hface (L := fun p ↦ ((x, p.1), p.2))
    (fun p ↦ ((hasFDerivAt_const x p).prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd) (a.2, 0)
    (b.2, 1)
  have ht (y : ℝ) := hface (L := fun p ↦ ((p.1, y), p.2))
    (fun p ↦ (hasFDerivAt_fst.prodMk (hasFDerivAt_const y p)).prodMk hasFDerivAt_snd) (a.1, 0)
    (b.1, 1)
  have hc (c : ℝ) := hface (L := fun z ↦ (z, c)) (fun p ↦ hasFDerivAt_prodMk_left p c) a b
  simp only [Function.comp_def, ContinuousLinearMap.prod_apply, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', zero_apply]
    at hs ht hc
  rw [hc, hc, hs, hs, ht, ht]
  exact integral2_slice_sub_eq_sides hψ hdψ a b

/-- **Homotopy invariance of the integral over a cylinder.** Let `φ` be a closed `C¹` two-form and
`Φ : (ℝ × ℝ) × ℝ → M` a `C²` homotopy through cylinders `Φ(·, c)` on the rectangle `[a, b]`: the
edges `t = a.2` and `t = b.2` of each rectangle are mapped alike, so that `t ↦ Φ((s, t), c)` is a
loop on `[a.2, b.2]` for every `s`. Suppose that each of the two boundary loops `s = a.1` and
`s = b.1` either stays fixed or remains a constant loop during the homotopy. Then the integrals of
`φ` over `Φ(·, 0)` and `Φ(·, 1)` agree. -/
theorem rectangleIntegral_eq_of_homotopy {φ : RoughForm I M F 2} (hφ : IsSmoothForm I 1 φ)
    (hdφ : mextDeriv φ = 0) {Φ : (ℝ × ℝ) × ℝ → M} (hΦ : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) I 2 Φ)
    {a b : ℝ × ℝ}
    (ha : (∀ t c, Φ ((a.1, t), c) = Φ ((a.1, t), 0)) ∨
      ∀ t c, Φ ((a.1, t), c) = Φ ((a.1, a.2), c))
    (hb : (∀ t c, Φ ((b.1, t), c) = Φ ((b.1, t), 0)) ∨
      ∀ t c, Φ ((b.1, t), c) = Φ ((b.1, b.2), c))
    (hper : ∀ s c, Φ ((s, b.2), c) = Φ ((s, a.2), c)) :
    rectangleIntegral φ (fun z ↦ Φ (z, 1)) a b = rectangleIntegral φ (fun z ↦ Φ (z, 0)) a b := by
  have h := rectangleIntegral_sub_rectangleIntegral_eq_sides hφ hdφ hΦ a b
  rw [rectangleIntegral_side_eq_zero φ ha, rectangleIntegral_side_eq_zero φ hb,
    show (fun p : ℝ × ℝ ↦ Φ ((p.1, b.2), p.2)) = fun p ↦ Φ ((p.1, a.2), p.2) from
      funext fun p ↦ hper p.1 p.2] at h
  simpa [sub_eq_zero] using h

end TauCeti
