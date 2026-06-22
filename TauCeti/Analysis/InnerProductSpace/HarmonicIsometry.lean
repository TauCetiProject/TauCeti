/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Geometric invariance of the Laplacian and of harmonic functions

Mathlib's `Mathlib/Analysis/InnerProductSpace/Laplacian.lean` records that the Laplacian `Δ`
commutes with *left* composition by a continuous linear map or equivalence acting on the
*values* of a function (`ContDiffAt.laplacian_CLM_comp_left`, `laplacian_CLE_comp_left`).
This file supplies the complementary *right* composition, acting on the *domain* variable: the
geometric invariance of `Δ` under the rigid motions of a Euclidean space — affine isometry
equivalences, with orthogonal changes of variable (linear isometry equivalences) and translations
as special cases.

For an affine isometry equivalence `e : E ≃ᵃⁱ[ℝ] E'` and any `f : E' → F`,

`Δ (f ∘ e) = (Δ f) ∘ e`.

In particular, for a linear isometry equivalence `l : E ≃ₗᵢ[ℝ] E'`,

`Δ (f ∘ l) = (Δ f) ∘ l`,

and for a translation by `a : E`,

`Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`.

Both identities hold with *no* differentiability hypothesis on `f`, because the underlying
`iteratedFDeriv` composition laws are unconditional (the iterated derivative is junk-valued off
the smooth locus, yet still transforms correctly under a linear change of variable). Smoothness
re-enters only in the harmonic-function corollaries, where the `ContDiffAt` half of
`InnerProductSpace.HarmonicAt` is transported across the equivalence: harmonicity is invariant
under the full isometry group, the symmetry that underlies the mean-value property and the
construction of radial harmonic functions (PDE roadmap, Lane C, item 12).

## Main declarations

* `TauCeti.laplacian_comp_affineIsometryEquiv`: `Δ (f ∘ e) = (Δ f) ∘ e` for an affine
  isometry equivalence `e`.
* `TauCeti.laplacian_comp_linearIsometryEquiv`: `Δ (f ∘ l) = (Δ f) ∘ l` for an isometry `l`.
* `TauCeti.laplacian_comp_add_right`: translation invariance of `Δ`.
* `TauCeti.harmonicAt_comp_affineIsometryEquiv_iff`,
  `TauCeti.harmonicOnNhd_comp_affineIsometryEquiv_iff`: harmonicity is invariant under
  affine isometry equivalences.
* `TauCeti.harmonicAt_comp_linearIsometryEquiv_iff`,
  `TauCeti.harmonicOnNhd_comp_linearIsometryEquiv_iff`: harmonicity is invariant under
  linear isometric changes of variable.
* `TauCeti.harmonicAt_comp_add_right_iff`, `TauCeti.harmonicOnNhd_comp_add_right_iff`:
  harmonicity is invariant under translation.
-/

namespace TauCeti

open InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. This is the unconditional engine behind the
geometric invariance of the Laplacian. -/
private theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Geometric invariance of the Laplacian under isometries.** For a linear isometry
equivalence `l`, the Laplacian commutes with right composition by `l`:
`Δ (f ∘ l) = (Δ f) ∘ l`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_linearIsometryEquiv (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- **Translation invariance of the Laplacian.** Shifting the argument by a constant `a`
commutes with the Laplacian: `Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a)`. No
differentiability hypothesis is needed. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- **Geometric invariance of the Laplacian under affine isometries.** For an affine isometry
equivalence `e`, the Laplacian commutes with right composition by `e`:
`Δ (f ∘ e) = (Δ f) ∘ e`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_affineIsometryEquiv (e : E ≃ᵃⁱ[ℝ] E') (f : E' → F) :
    Δ (f ∘ e) = (Δ f) ∘ e := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext x
    have hx : e x = e.linearIsometryEquiv x + e 0 := by
      simpa using e.map_vadd (0 : E) x
    simp [Function.comp_apply, hx]
  rw [hcomp, laplacian_comp_linearIsometryEquiv e.linearIsometryEquiv (fun y ↦ f (y + e 0)),
    laplacian_comp_add_right f (e 0)]
  ext x
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  simp [Function.comp_apply, hx]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NormedSpace ℝ F] in
/-- Precomposition by a homeomorphism transports vanishing in a neighbourhood: `g ∘ h` vanishes
near `x` iff `g` vanishes near `h x`. -/
private theorem eventuallyEq_zero_comp_homeomorph_iff (h : E ≃ₜ E') (g : E' → F) (x : E) :
    (g ∘ h =ᶠ[𝓝 x] 0) ↔ (g =ᶠ[𝓝 (h x)] 0) := by
  rw [← h.map_nhds_eq x]
  constructor
  · intro hyp
    refine Filter.eventually_map.mpr ?_
    filter_upwards [hyp] with y hy
    simpa using hy
  · intro hyp
    have hyp' := Filter.eventually_map.mp hyp
    filter_upwards [hyp'] with y hy
    simpa using hy

/-- **Harmonicity is invariant under isometric changes of variable.** For a linear isometry
equivalence `l`, the function `f ∘ l` is harmonic at `x` iff `f` is harmonic at `l x`. -/
theorem harmonicAt_comp_linearIsometryEquiv_iff (l : E ≃ₗᵢ[ℝ] E') {f : E' → F} {x : E} :
    HarmonicAt (f ∘ l) x ↔ HarmonicAt f (l x) := by
  have hcd : ContDiffAt ℝ 2 (f ∘ l) x ↔ ContDiffAt ℝ 2 f (l x) := by
    have := l.toContinuousLinearEquiv.contDiffAt_comp_iff (f := f) (n := 2) (x := l x)
    simpa using this
  have hlap : (Δ (f ∘ l) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (l x)] 0) := by
    rw [laplacian_comp_linearIsometryEquiv l f]
    have := eventuallyEq_zero_comp_homeomorph_iff l.toHomeomorph (Δ f) x
    rwa [LinearIsometryEquiv.coe_toHomeomorph] at this
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩, fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- **Harmonicity is invariant under translation.** The function `y ↦ f (y + a)` is harmonic
at `x` iff `f` is harmonic at `x + a`. -/
theorem harmonicAt_comp_add_right_iff {f : E → F} {x a : E} :
    HarmonicAt (fun y ↦ f (y + a)) x ↔ HarmonicAt f (x + a) := by
  have hcd : ContDiffAt ℝ 2 (fun y ↦ f (y + a)) x ↔ ContDiffAt ℝ 2 f (x + a) := by
    constructor
    · intro h
      have hφ : ContDiffAt ℝ 2 (fun z : E ↦ z - a) (x + a) := by fun_prop
      have h' : ContDiffAt ℝ 2 (fun y ↦ f (y + a)) ((fun z : E ↦ z - a) (x + a)) := by
        simpa using h
      have hc := h'.comp (x + a) hφ
      have hgf : (fun y ↦ f (y + a)) ∘ (fun z : E ↦ z - a) = f := by funext w; simp
      rwa [hgf] at hc
    · intro h
      have hψ : ContDiffAt ℝ 2 (fun y : E ↦ y + a) x := by fun_prop
      exact h.comp x hψ
  have hlap : (Δ (fun y ↦ f (y + a)) =ᶠ[𝓝 x] 0) ↔ (Δ f =ᶠ[𝓝 (x + a)] 0) := by
    rw [laplacian_comp_add_right f a]
    have := eventuallyEq_zero_comp_homeomorph_iff (Homeomorph.addRight a) (Δ f) x
    simpa [Function.comp_def] using this
  exact ⟨fun hf ↦ ⟨hcd.1 hf.1, hlap.1 hf.2⟩, fun hf ↦ ⟨hcd.2 hf.1, hlap.2 hf.2⟩⟩

/-- **Harmonicity is invariant under affine isometries.** For an affine isometry equivalence
`e`, the function `f ∘ e` is harmonic at `x` iff `f` is harmonic at `e x`. -/
theorem harmonicAt_comp_affineIsometryEquiv_iff (e : E ≃ᵃⁱ[ℝ] E') {f : E' → F} {x : E} :
    HarmonicAt (f ∘ e) x ↔ HarmonicAt f (e x) := by
  have hcomp : f ∘ e = (fun y ↦ f (y + e 0)) ∘ e.linearIsometryEquiv := by
    funext y
    have hy : e y = e.linearIsometryEquiv y + e 0 := by
      simpa using e.map_vadd (0 : E) y
    simp [Function.comp_apply, hy]
  rw [hcomp, harmonicAt_comp_linearIsometryEquiv_iff e.linearIsometryEquiv]
  have hx : e x = e.linearIsometryEquiv x + e 0 := by
    simpa using e.map_vadd (0 : E) x
  simpa [hx] using harmonicAt_comp_add_right_iff (f := f) (x := e.linearIsometryEquiv x)
    (a := e 0)

/-- Harmonicity on a neighbourhood of a set is invariant under an affine isometry equivalence. -/
theorem harmonicOnNhd_comp_affineIsometryEquiv_iff (e : E ≃ᵃⁱ[ℝ] E') {f : E' → F}
    {s : Set E'} : HarmonicOnNhd (f ∘ e) (e ⁻¹' s) ↔ HarmonicOnNhd f s := by
  constructor
  · intro hf y hy
    have hpre : e (e.symm y) ∈ s := by simpa using hy
    have h := hf (e.symm y) hpre
    simpa using (harmonicAt_comp_affineIsometryEquiv_iff e).1 h
  · intro hf x hx
    exact (harmonicAt_comp_affineIsometryEquiv_iff e).2 (hf (e x) hx)

/-- Harmonicity on a neighbourhood of a set is invariant under a linear isometric change of
variable. -/
theorem harmonicOnNhd_comp_linearIsometryEquiv_iff (l : E ≃ₗᵢ[ℝ] E') {f : E' → F}
    {s : Set E'} : HarmonicOnNhd (f ∘ l) (l ⁻¹' s) ↔ HarmonicOnNhd f s := by
  rw [← LinearIsometryEquiv.coe_toAffineIsometryEquiv l]
  exact harmonicOnNhd_comp_affineIsometryEquiv_iff l.toAffineIsometryEquiv

/-- Harmonicity on a neighbourhood of a set is invariant under translation. -/
theorem harmonicOnNhd_comp_add_right_iff {f : E → F} {s : Set E} (a : E) :
    HarmonicOnNhd (fun y ↦ f (y + a)) ((fun y ↦ y + a) ⁻¹' s) ↔ HarmonicOnNhd f s := by
  let e : E ≃ᵃⁱ[ℝ] E := AffineIsometryEquiv.constVAdd ℝ E a
  have hfun : (fun y ↦ f (y + a)) = f ∘ e := by
    funext y
    simp [e, Function.comp_apply, add_comm]
  have hset : ((fun y ↦ y + a) ⁻¹' s) = e ⁻¹' s := by
    ext y
    simp [e, add_comm]
  rw [hfun, hset]
  exact harmonicOnNhd_comp_affineIsometryEquiv_iff e

/-- Harmonicity on a neighbourhood of a set is preserved by an isometric change of variable. -/
theorem HarmonicOnNhd.comp_linearIsometryEquiv {f : E' → F} {s : Set E'} (l : E ≃ₗᵢ[ℝ] E')
    (hf : HarmonicOnNhd f s) : HarmonicOnNhd (f ∘ l) (l ⁻¹' s) :=
  (harmonicOnNhd_comp_linearIsometryEquiv_iff l).2 hf

/-- Harmonicity on a neighbourhood of a set is preserved by translation. -/
theorem HarmonicOnNhd.comp_add_right {f : E → F} {s : Set E} (a : E)
    (hf : HarmonicOnNhd f s) : HarmonicOnNhd (fun y ↦ f (y + a)) ((fun y ↦ y + a) ⁻¹' s) :=
  (harmonicOnNhd_comp_add_right_iff a).2 hf

end TauCeti
