/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Orthonormal local frames and metric trivializations

Let `V → M` be a vector bundle whose fibres carry inner products.

* `IsLocalFrameOn.coeff_eq_inner`: the coefficient functionals of an orthonormal local frame are
  its metric duals. This lets local-frame connection and curvature coefficients be read as inner
  products.
* `IsLocalFrameOn.of_orthonormal`: a `C^n` family of `finrank 𝕜 F` pointwise orthonormal sections
  of a finite-rank bundle on `u` forms a `C^n` local frame on `u`.
* `IsLocalFrameOn.toOrthonormalBasisAt`: at each point `x ∈ u`, an orthonormal local frame gives
  an `OrthonormalBasis ι 𝕜 (V x)`.
* `IsLocalFrameOn.diffeomorphOfOrthonormal`: any global `C^k` orthonormal frame of a `C^k`
  Riemannian vector bundle trivializes `TotalSpace F V` by a fibrewise isometric `C^k`
  diffeomorphism `TotalSpace F V ≃ₘ^k M × EuclideanSpace ℝ ι` sending `⟨x, w⟩` to
  `(x, i ↦ ⟪s i x, w⟫)` and `(x, c)` back to `⟨x, ∑ i, c i • s i x⟩`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 10.
* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press (1974), §§3 and 5.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

namespace IsLocalFrameOn

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace 𝕜 (V x)]
  [FiberBundle F V]
  {ι : Type*} {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}

/-- The coefficients of an orthonormal local frame are its metric duals. Only orthonormality
at the point is needed. -/
theorem coeff_eq_inner [Finite ι] (hs : IsLocalFrameOn I F n s u) {x : M} (hx : x ∈ u)
    (ho : Orthonormal 𝕜 (fun i ↦ s i x)) (i : ι) (v : V x) :
    hs.coeff i x v = inner 𝕜 (s i x) v := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hexp : v = ∑ j, hs.coeff j x v • s j x := by
    simpa only [FiberBundle.extend_apply_self] using
      hs.coeff_sum_eq (FiberBundle.extend F v) hx
  have h := ho.inner_right_fintype (fun j ↦ hs.coeff j x v) i
  rw [← hexp] at h
  exact h.symm

/-- A `C^n` family of `finrank 𝕜 F` pointwise orthonormal sections on `u` forms a `C^n` local
frame on `u`. -/
theorem of_orthonormal [VectorBundle 𝕜 F V] [FiniteDimensional 𝕜 F] [Fintype ι]
    (hcard : Fintype.card ι = Module.finrank 𝕜 F)
    (ho : ∀ x ∈ u, Orthonormal 𝕜 fun i ↦ s i x)
    (hs : ∀ i, CMDiff[u] n (T% (s i))) :
    IsLocalFrameOn I F n s u :=
  of_linearIndependent hcard (fun x hx ↦ (ho x hx).linearIndependent) hs

/-- Given an orthonormal local frame `{s i}` on `u ∋ x`, returns the orthonormal basis
`{s i x}` of the fibre `V x`. -/
noncomputable def toOrthonormalBasisAt [Fintype ι] (hs : IsLocalFrameOn I F n s u) {x : M}
    (hx : x ∈ u) (ho : Orthonormal 𝕜 fun i ↦ s i x) :
    OrthonormalBasis ι 𝕜 (V x) :=
  OrthonormalBasis.mk ho (hs.generating hx)

@[simp]
theorem coe_toOrthonormalBasisAt [Fintype ι] (hs : IsLocalFrameOn I F n s u) {x : M}
    (hx : x ∈ u) (ho : Orthonormal 𝕜 fun i ↦ s i x) :
    ⇑(hs.toOrthonormalBasisAt hx ho) = fun i ↦ s i x :=
  OrthonormalBasis.coe_mk ho (hs.generating hx)

end RCLike

section Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {k : ℕ∞ω} [IsContMDiffRiemannianBundle I k F V]
  {ι : Type*} [Fintype ι] {s : ι → Π x, V x}

/-- **Global bundle trivialization by inner-product coordinates.** Any global `C^k` orthonormal
frame `s` of a `C^k` Riemannian vector bundle `V → M` trivializes `TotalSpace F V` by a global
`C^k` diffeomorphism sending `⟨x, w⟩` to `(x, i ↦ ⟪s i x, w⟫)` and `(x, c)` back to
`⟨x, ∑ i, c i • s i x⟩`. -/
noncomputable def diffeomorphOfOrthonormal (hs : IsLocalFrameOn I F k s univ)
    (ho : ∀ x, Orthonormal ℝ fun i ↦ s i x) :
    TotalSpace F V ≃ₘ^k⟮I.prod 𝓘(ℝ, F), I.prod 𝓘(ℝ, EuclideanSpace ℝ ι)⟯
      (M × EuclideanSpace ℝ ι) where
  toFun p := (p.proj, WithLp.toLp 2 fun i ↦ inner ℝ (s i p.proj) p.2)
  invFun q := ⟨q.1, ∑ i, q.2.ofLp i • s i q.1⟩
  left_inv p := by
    refine TotalSpace.ext rfl (heq_of_eq ?_)
    have hb := (hs.toOrthonormalBasisAt (mem_univ p.proj) (ho p.proj)).sum_repr' p.2
    simpa only [WithLp.ofLp_toLp, coe_toOrthonormalBasisAt] using hb
  right_inv := by
    rintro ⟨x, c⟩
    refine Prod.ext rfl (PiLp.ext fun i ↦ ?_)
    simpa only [WithLp.ofLp_toLp] using (ho x).inner_right_fintype c.ofLp i
  contMDiff_toFun := by
    have hcoord : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, ι → ℝ) k
        (fun p : TotalSpace F V ↦ fun i : ι ↦ inner ℝ (s i p.proj) p.2) :=
      contMDiff_pi_module_iff.mpr fun i ↦
        ((contMDiffOn_univ.mp (hs.contMDiffOn i)).comp
          (Bundle.contMDiff_proj V)).inner_bundle contMDiff_id
    have htoLp : ContDiff ℝ k (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toContinuousLinearEquiv.contDiff
    exact (Bundle.contMDiff_proj V).prodMk (htoLp.contMDiff.comp hcoord)
  contMDiff_invFun :=
    ContMDiff.sum_sectionAlong Finset.univ
      (fun i (q : M × EuclideanSpace ℝ ι) ↦ q.2.ofLp i • s i q.1)
      contMDiff_fst fun i _ ↦
        ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : ι ↦ ℝ) i).contDiff.contMDiff.comp
          contMDiff_snd).smul_totalSpace
          ((contMDiffOn_univ.mp (hs.contMDiffOn i)).comp contMDiff_fst)

@[simp]
theorem diffeomorphOfOrthonormal_apply_fst (hs : IsLocalFrameOn I F k s univ)
    (ho : ∀ x, Orthonormal ℝ fun i ↦ s i x) (p : TotalSpace F V) :
    (hs.diffeomorphOfOrthonormal ho p).1 = p.proj :=
  (rfl)

@[simp]
theorem diffeomorphOfOrthonormal_apply_snd (hs : IsLocalFrameOn I F k s univ)
    (ho : ∀ x, Orthonormal ℝ fun i ↦ s i x) (p : TotalSpace F V) (i : ι) :
    ((hs.diffeomorphOfOrthonormal ho p).2).ofLp i = inner ℝ (s i p.proj) p.2 :=
  (rfl)

@[simp]
theorem diffeomorphOfOrthonormal_symm_apply (hs : IsLocalFrameOn I F k s univ)
    (ho : ∀ x, Orthonormal ℝ fun i ↦ s i x) (q : M × EuclideanSpace ℝ ι) :
    (hs.diffeomorphOfOrthonormal ho).symm q = ⟨q.1, ∑ i, q.2.ofLp i • s i q.1⟩ :=
  (rfl)

/-- The inner-product coordinate trivialization preserves fibre norms. -/
@[simp]
theorem norm_diffeomorphOfOrthonormal_snd (hs : IsLocalFrameOn I F k s univ)
    (ho : ∀ x, Orthonormal ℝ fun i ↦ s i x) (p : TotalSpace F V) :
    ‖(hs.diffeomorphOfOrthonormal ho p).2‖ = ‖p.2‖ := by
  have hrepr : (hs.diffeomorphOfOrthonormal ho p).2 =
      (hs.toOrthonormalBasisAt (mem_univ p.proj) (ho p.proj)).repr p.2 :=
    PiLp.ext fun i ↦ by
      rw [diffeomorphOfOrthonormal_apply_snd, OrthonormalBasis.repr_apply_apply,
        coe_toOrthonormalBasisAt]
  rw [hrepr, LinearIsometryEquiv.norm_map]

end Riemannian

end IsLocalFrameOn
