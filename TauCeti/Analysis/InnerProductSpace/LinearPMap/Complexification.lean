/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import TauCeti.Analysis.InnerProductSpace.Complexification

/-!
# Complexification of partially defined operators

A real partially defined operator `T` extends to `T.complexifyL2` on the Hilbert
complexifications, with domain consisting exactly of vectors whose real and imaginary
parts lie in `T.domain`. No boundedness of `T` is required. Complexification preserves
and reflects density of the domain and closedness of the graph, and commutes with
the adjoint, including its domain (also for Mathlib's non-dense zero-value convention).
In particular it preserves and reflects self-adjointness.

The carrier is the existing `WithLp 2 (TauCeti.Complexification E)`, not the Taylor-norm
complexification. These comparisons allow real unbounded operators to be treated by
complex Hilbert-space spectral theory.

## References

* J. Weidmann, *Linear Operators in Hilbert Spaces*, Chapters 2 and 5.
-/

public section

noncomputable section

open TauCeti WithLp
open scoped InnerProductSpace

namespace LinearPMap

section NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The complex-linear extension of a real partially defined operator on the Hilbert
complexification. Both coordinates must belong to its original domain. -/
def complexifyL2 (T : E →ₗ.[ℝ] F) :
    WithLp 2 (Complexification E) →ₗ.[ℂ] WithLp 2 (Complexification F) where
  domain := T.domain.complexifyL2
  toFun :=
    { toFun := fun z ↦ toLp 2
        ⟨T ⟨z.val.ofLp.re, ((T.domain.mem_complexifyL2 _).1 z.property).1⟩,
          T ⟨z.val.ofLp.im, ((T.domain.mem_complexifyL2 _).1 z.property).2⟩⟩
      map_add' z w := by
        apply ofLp_injective 2
        ext <;> simp [← map_add]
      map_smul' c z := by
        apply ofLp_injective 2
        ext <;> simp [Complexification.smul_re, Complexification.smul_im,
          ← map_smul, ← map_sub, ← map_add]; rfl }

@[simp]
theorem complexifyL2_domain (T : E →ₗ.[ℝ] F) :
    T.complexifyL2.domain = T.domain.complexifyL2 := (rfl)

/-- The coordinate criterion for membership in the complexified operator domain.
The simplifier obtains this from `complexifyL2_domain` and `Submodule.mem_complexifyL2`. -/
theorem mem_complexifyL2_domain (T : E →ₗ.[ℝ] F) (z : WithLp 2 (Complexification E)) :
    z ∈ T.complexifyL2.domain ↔ z.ofLp.re ∈ T.domain ∧ z.ofLp.im ∈ T.domain := by
  rw [complexifyL2_domain, Submodule.mem_complexifyL2]

@[simp]
theorem complexifyL2_apply_re (T : E →ₗ.[ℝ] F) (z : T.complexifyL2.domain) :
    (T.complexifyL2 z).ofLp.re =
      T ⟨z.val.ofLp.re, ((T.mem_complexifyL2_domain _).1 z.property).1⟩ := (rfl)

@[simp]
theorem complexifyL2_apply_im (T : E →ₗ.[ℝ] F) (z : T.complexifyL2.domain) :
    (T.complexifyL2 z).ofLp.im =
      T ⟨z.val.ofLp.im, ((T.mem_complexifyL2_domain _).1 z.property).2⟩ := (rfl)

/-- The complexified operator agrees with the original operator on real vectors. -/
@[simp]
theorem complexifyL2_ofReal (T : E →ₗ.[ℝ] F) (x : T.domain) :
    T.complexifyL2 ⟨toLp 2 (Complexification.ofReal (x : E)),
      by simp [x.property]⟩ = toLp 2 (Complexification.ofReal (T x)) := by
  apply ofLp_injective 2
  ext
  · simp
  · simp only [complexifyL2_apply_im, Complexification.ofReal_im]
    convert T.map_zero using 2

/-- A partially defined operator is densely defined exactly when its complexification is. -/
theorem dense_domain_complexifyL2_iff (T : E →ₗ.[ℝ] F) :
    Dense (T.complexifyL2.domain : Set (WithLp 2 (Complexification E))) ↔
      Dense (T.domain : Set E) :=
  T.domain.dense_complexifyL2_iff

/-- Membership in the complexified graph is membership in the real graph in both
coordinates. -/
theorem mem_graph_complexifyL2_iff (T : E →ₗ.[ℝ] F)
    (z : WithLp 2 (Complexification E)) (w : WithLp 2 (Complexification F)) :
    (z, w) ∈ T.complexifyL2.graph ↔
      (z.ofLp.re, w.ofLp.re) ∈ T.graph ∧ (z.ofLp.im, w.ofLp.im) ∈ T.graph := by
  constructor
  · intro h
    obtain ⟨x, rfl, rfl⟩ := T.complexifyL2.mem_graph_iff.mp h
    exact ⟨T.mem_graph ⟨_, ((T.mem_complexifyL2_domain _).1 x.property).1⟩,
      T.mem_graph ⟨_, ((T.mem_complexifyL2_domain _).1 x.property).2⟩⟩
  · rintro ⟨hr, hi⟩
    obtain ⟨xr, hxr, hyr⟩ := T.mem_graph_iff.mp hr
    obtain ⟨xi, hxi, hyi⟩ := T.mem_graph_iff.mp hi
    dsimp only at hxr hxi hyr hyi
    refine T.complexifyL2.mem_graph_iff.mpr
      ⟨⟨z, (T.mem_complexifyL2_domain _).2
        ⟨by rw [← hxr]; exact xr.property, by rw [← hxi]; exact xi.property⟩⟩, rfl, ?_⟩
    apply ofLp_injective 2
    apply Complexification.ext
    · simpa only [complexifyL2_apply_re, ← hxr] using hyr
    · simpa only [complexifyL2_apply_im, ← hxi] using hyi

/-- Complexification preserves and reflects closedness, for operators between arbitrary
real normed spaces. -/
@[simp]
theorem isClosed_complexifyL2_iff (T : E →ₗ.[ℝ] F) :
    T.complexifyL2.IsClosed ↔ T.IsClosed := by
  let eE := (complexificationEquivProd E).toHomeomorph.trans
    (prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph
  let eF := (complexificationEquivProd F).toHomeomorph.trans
    (prodContinuousLinearEquiv 2 ℝ F F).toHomeomorph
  let q := (eE.prodCongr eF).trans (Homeomorph.prodProdProdComm E E F F)
  have hg : (T.complexifyL2.graph : Set _) =
      q ⁻¹' ((T.graph : Set (E × F)) ×ˢ (T.graph : Set (E × F))) := by
    ext ⟨z, w⟩
    have hq : q (z, w) = ((z.ofLp.re, w.ofLp.re), (z.ofLp.im, w.ofLp.im)) := by
      simp [q, eE, eF, Homeomorph.prodProdProdComm, complexificationEquivProd_apply]
    simp only [SetLike.mem_coe, mem_graph_complexifyL2_iff, Set.mem_preimage, hq,
      Set.mem_prod]
  simp only [IsClosed]
  rw [hg, q.isClosed_preimage]
  constructor
  · intro h
    have h' := h.preimage (continuous_id.prodMk (continuous_const (y := (0 : E × F))))
    have hs : (fun p : E × F ↦ (p, (0 : E × F))) ⁻¹'
        ((T.graph : Set (E × F)) ×ˢ (T.graph : Set (E × F))) = T.graph := by
      ext p
      simp only [Set.mem_preimage, Set.mem_prod, SetLike.mem_coe, Submodule.zero_mem,
        and_true]
    exact hs ▸ h'
  · intro h
    exact h.prod h

/-- Complexification of partially defined operators is injective. -/
theorem complexifyL2_injective :
    Function.Injective (complexifyL2 : (E →ₗ.[ℝ] F) → _) := by
  intro T S h
  apply eq_of_eq_graph
  ext p
  have hp := congrArg (fun A ↦
    (toLp 2 (Complexification.ofReal p.1), toLp 2 (Complexification.ofReal p.2)) ∈ A.graph) h
  simpa only [mem_graph_complexifyL2_iff, ofLp_toLp, Complexification.ofReal_re,
    Complexification.ofReal_im, Prod.mk_zero_zero, Submodule.zero_mem, and_true,
    Prod.mk.eta] using (iff_of_eq hp)

end NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Complexification preserves formal adjoint pairs without any density assumption. -/
theorem IsFormalAdjoint.complexifyL2 {T : E →ₗ.[ℝ] F} {S : F →ₗ.[ℝ] E}
    (h : T.IsFormalAdjoint S) : T.complexifyL2.IsFormalAdjoint S.complexifyL2 := by
  intro z w
  let zr : T.domain := ⟨z.val.ofLp.re, ((T.mem_complexifyL2_domain _).1 z.property).1⟩
  let zi : T.domain := ⟨z.val.ofLp.im, ((T.mem_complexifyL2_domain _).1 z.property).2⟩
  let wr : S.domain := ⟨w.val.ofLp.re, ((S.mem_complexifyL2_domain _).1 w.property).1⟩
  let wi : S.domain := ⟨w.val.ofLp.im, ((S.mem_complexifyL2_domain _).1 w.property).2⟩
  apply Complex.ext <;> simp only [complexification_re_inner, complexification_im_inner,
    complexifyL2_apply_re, complexifyL2_apply_im]
  · exact congrArg₂ (· + ·) (h zr wr) (h zi wi)
  · exact congrArg₂ (· - ·) (h zr wi) (h zi wr)

variable [CompleteSpace E]

/-- The adjoint domain of a complexification is exactly the complexification of the real
adjoint domain, without any density assumption. -/
theorem mem_adjoint_complexifyL2_domain_iff (T : E →ₗ.[ℝ] F)
    (z : WithLp 2 (Complexification F)) :
    z ∈ T.complexifyL2†.domain ↔ z.ofLp.re ∈ T†.domain ∧ z.ofLp.im ∈ T†.domain := by
  let e := (complexificationEquivProd E).toHomeomorph.trans
    (prodContinuousLinearEquiv 2 ℝ E E).toHomeomorph
  let j (x : T.domain) : T.complexifyL2.domain :=
    ⟨toLp 2 (Complexification.ofReal (x : E)), by simp [x.property]⟩
  have hj : Continuous j := by
    apply Continuous.subtype_mk
    convert e.symm.continuous.comp
      (continuous_subtype_val.prodMk (continuous_const (y := (0 : E)))) using 1
    ext x
    apply ofLp_injective 2
    apply Complexification.ext <;> simp [e]
  let r (x : T.complexifyL2.domain) : T.domain :=
    ⟨x.val.ofLp.re, ((T.mem_complexifyL2_domain _).1 x.property).1⟩
  let i (x : T.complexifyL2.domain) : T.domain :=
    ⟨x.val.ofLp.im, ((T.mem_complexifyL2_domain _).1 x.property).2⟩
  have hr : Continuous r := by
    apply Continuous.subtype_mk
    simpa [e] using (e.continuous.comp continuous_subtype_val).fst
  have hi : Continuous i := by
    apply Continuous.subtype_mk
    simpa [e] using (e.continuous.comp continuous_subtype_val).snd
  simp only [mem_adjoint_domain_iff]
  constructor
  · intro h
    have h' := h.comp hj
    constructor
    · simpa [j, Function.comp_def] using Complex.continuous_re.comp h'
    · simpa [j, Function.comp_def] using (Complex.continuous_im.comp h').neg
  · rintro ⟨hre, him⟩
    have hreal := (hre.comp hr).add (him.comp hi)
    have himag := (hre.comp hi).sub (him.comp hr)
    convert (Complex.continuous_ofReal.comp hreal).add
      ((Complex.continuous_ofReal.comp himag).mul (continuous_const (y := Complex.I))) using 1
    ext x
    apply Complex.ext <;> simp [r, i, Function.comp_def]

/-- Adjoint and Hilbert complexification commute, including Mathlib's zero-value convention
for operators with non-dense domain. -/
theorem adjoint_complexifyL2 (T : E →ₗ.[ℝ] F) :
    T.complexifyL2† = T†.complexifyL2 := by
  classical
  apply LinearPMap.ext
  · ext z
    simpa only [mem_complexifyL2_domain] using T.mem_adjoint_complexifyL2_domain_iff z
  · intro z hz hz'
    by_cases hT : Dense (T.domain : Set E)
    · apply adjoint_apply_eq ((T.dense_domain_complexifyL2_iff).2 hT)
      exact (adjoint_isFormalAdjoint hT).complexifyL2 ⟨z, hz'⟩
    · rw [adjoint_apply_of_not_dense (T.dense_domain_complexifyL2_iff.not.mpr hT)]
      apply ofLp_injective 2
      ext <;> simp [adjoint_apply_of_not_dense hT]

/-- A real operator on a Hilbert space is self-adjoint exactly when its Hilbert
complexification is self-adjoint. No closedness or density hypothesis is assumed. -/
@[simp]
theorem isSelfAdjoint_complexifyL2_iff (T : E →ₗ.[ℝ] E) :
    IsSelfAdjoint T.complexifyL2 ↔ IsSelfAdjoint T := by
  constructor
  · intro h
    rw [isSelfAdjoint_def] at h ⊢
    apply complexifyL2_injective
    rw [← T.adjoint_complexifyL2]
    exact h
  · intro h
    rw [isSelfAdjoint_def, T.adjoint_complexifyL2]
    exact congrArg complexifyL2 h

end LinearPMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Complexification of a bounded operator restricted to a real subspace is its bounded
complexification restricted to the complexified subspace. -/
theorem toPMap_complexifyL2 (T : E →L[ℝ] F) (S : Submodule ℝ E) :
    (T.toPMap S).complexifyL2 = T.complexifyL2.toPMap S.complexifyL2 := by
  apply LinearPMap.ext
  · simp
  · intro z hz hz'
    apply ofLp_injective 2
    ext <;> simp

end ContinuousLinearMap
