/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Nondegenerate critical submanifolds and the normal Hessian

A function `f` on a manifold `M` is *Morse–Bott* when its critical locus is a union of
submanifolds along each of which the Hessian is nondegenerate in the normal directions. This file
sets up the pointwise linear algebra along one embedded critical submanifold `i : S → M`.

Along a family of critical points, every tangent vector of the family lies in the kernel of the
critical Hessian (`TauCeti.criticalHessian_mfderiv_eq_zero`). Hence the critical Hessian
`criticalHessian I f (i s)` descends to a quadratic form, the *normal Hessian*, on the intrinsic
normal space `T_{i s} M ⧸ di(T_s S)` of the embedding. The embedding is a *nondegenerate critical
submanifold* in the sense of Bott when the kernel of the critical Hessian is exactly the tangent
space of the submanifold, equivalently when every normal Hessian is nondegenerate. Its index is the
Morse index of `f` at the point, and the indices of `f` and `-f` add up to the codimension of the
submanifold.

The normal spaces are the fibres of the intrinsic normal bundle of the embedding, so the normal
Hessians form the fibrewise quadratic form from which the positive and negative normal bundles of
a Morse–Bott function are built.

## Main definitions

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`: an embedding consisting of critical points of
  `f`, along which `f` is `C²`.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`: the quadratic form induced by the
  critical Hessian on a normal space of a critical submanifold.
* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`: Bott's nondegeneracy condition,
  that the kernel of the critical Hessian is the tangent space of the submanifold.

## Main results

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.nondegenerate_normalHessian_iff` and
  `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isNondegenerateCriticalSubmanifold_iff`:
  nondegeneracy of the critical submanifold is nondegeneracy of all its normal Hessians.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.sigNeg_normalHessian` and
  `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.sigPos_normalHessian`: the indices of inertia of
  the normal Hessian are the Morse indices of `f` and `-f`.
* `IsNondegenerateCriticalSubmanifold.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank`:
  along a nondegenerate critical submanifold the indices of `f` and `-f` add up to the
  dimension of the normal space.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton`: a
  zero-dimensional nondegenerate critical submanifold is a family of nondegenerate critical
  points.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_prodMkLeft`: Bott's local model,
  the slice `S × {c}` through a nondegenerate critical point `c` of `g` is a nondegenerate
  critical submanifold of `g ∘ Prod.snd`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Ann. of Math. 60 (1954), 248–261.
* A. Banyaga and D. Hurtubise, *A proof of the Morse–Bott lemma*, Expo. Math. 22 (2004),
  365–373.
* L. Nicolaescu, *An Invitation to Morse Theory*, 2nd ed., Springer Universitext, 2011, §2.6.
-/

public section

open Filter Function Set Topology QuadraticForm
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {F G S : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace S] [ChartedSpace G S]
  {n : ℕ∞ω} (i : SmoothEmbedding J I n S M) (f : M → ℝ)

/-- An embedding `i` is a **critical submanifold** of a real function `f` when `f` is `C²` at
every point of `i` and every point of `i` is a critical point of `f`. -/
structure IsCriticalSubmanifold : Prop where
  /-- The function is `C²` at every point of the submanifold. -/
  contMDiffAt (s : S) : ContMDiffAt I 𝓘(ℝ) 2 f (i s)
  /-- Every point of the submanifold is a critical point. -/
  mem_criticalPoints (s : S) : i s ∈ criticalPoints I f

/-- An embedding `i` is a **nondegenerate critical submanifold** of `f` in the sense of Bott when
it is a critical submanifold and, at each of its points, the kernel of the critical Hessian is
exactly the tangent space of the submanifold. A function is Morse–Bott when its critical locus
is covered by such submanifolds. -/
structure IsNondegenerateCriticalSubmanifold : Prop extends IsCriticalSubmanifold i f where
  /-- The kernel of the critical Hessian is the tangent space of the submanifold. -/
  ker_criticalHessian (s : S) : (criticalHessian I f (i s)).ker = (mfderiv J I i s).range

variable {i f}

/-- The negation of a function has the same critical submanifolds. -/
theorem IsCriticalSubmanifold.neg (h : i.IsCriticalSubmanifold f) : i.IsCriticalSubmanifold (-f) :=
  ⟨fun s ↦ contDiff_neg.contMDiff.contMDiffAt.comp _ (h.contMDiffAt s),
    fun s ↦ criticalPoints_neg (I := I) (f := f) ▸ h.mem_criticalPoints s⟩

@[simp]
theorem isCriticalSubmanifold_neg_iff : i.IsCriticalSubmanifold (-f) ↔ i.IsCriticalSubmanifold f :=
  ⟨fun h ↦ neg_neg f ▸ h.neg, IsCriticalSubmanifold.neg⟩

/-- The negation of a function has the same nondegenerate critical submanifolds. -/
theorem IsNondegenerateCriticalSubmanifold.neg (h : i.IsNondegenerateCriticalSubmanifold f) :
    i.IsNondegenerateCriticalSubmanifold (-f) where
  toIsCriticalSubmanifold := h.toIsCriticalSubmanifold.neg
  ker_criticalHessian s := by
    rw [criticalHessian_neg, ← h.ker_criticalHessian s]
    ext v
    simp

@[simp]
theorem isNondegenerateCriticalSubmanifold_neg_iff :
    i.IsNondegenerateCriticalSubmanifold (-f) ↔ i.IsNondegenerateCriticalSubmanifold f :=
  ⟨fun h ↦ neg_neg f ▸ h.neg, IsNondegenerateCriticalSubmanifold.neg⟩

section Boundaryless

variable [I.Boundaryless]

/-- A **zero-dimensional** nondegenerate critical submanifold is a family of nondegenerate critical
points: when the model of `S` is trivial, Bott's condition says that the critical Hessian is
injective. -/
theorem isNondegenerateCriticalSubmanifold_iff_of_subsingleton [FiniteDimensional ℝ E]
    [Subsingleton F] :
    i.IsNondegenerateCriticalSubmanifold f ↔
      ∀ s, IsManifoldNondegenerateCriticalPoint I f (i s) := by
  have hrange (s : S) : (mfderiv J I i s).range = ⊥ := by
    -- The tangent spaces of `S` are the trivial model space `F`.
    have : Subsingleton (TangentSpace J s) := inferInstanceAs (Subsingleton F)
    rw [Subsingleton.elim (mfderiv J I i s) 0]
    exact LinearMap.range_zero
  simp only [isManifoldNondegenerateCriticalPoint_iff_criticalHessian, ← mem_criticalPoints]
  refine ⟨fun h s ↦ ⟨h.contMDiffAt s, h.mem_criticalPoints s,
    criticalHessian_isInvertible_of_injective ?_⟩, fun h ↦ ⟨⟨fun s ↦ (h s).1, fun s ↦ (h s).2.1⟩,
    fun s ↦ ?_⟩⟩
  · have hker : (criticalHessian I f (i s)).ker = ⊥ := by rw [h.ker_criticalHessian s, hrange s]
    exact LinearMap.ker_eq_bot.1 hker
  · rw [hrange s]
    exact LinearMap.ker_eq_bot.2 (h s).2.2.injective

variable [IsManifold I 1 M]

namespace IsCriticalSubmanifold

variable (h : i.IsCriticalSubmanifold f) (s : S) (hn : n ≠ 0)
include h

/-- The tangent space of a critical submanifold lies in the radical of the critical Hessian. -/
theorem tangentRange_le_radical :
    i.tangentRange s hn ≤ (criticalHessian I f (i s)).toBilinForm.toQuadraticMap.radical :=
  range_mfderiv_le_radical_criticalHessian (h.contMDiffAt s)
    ((i.contMDiff s).mdifferentiableAt hn) (Eventually.of_forall h.mem_criticalPoints)

/-- The **normal Hessian** of a critical submanifold: the quadratic form which the critical Hessian
of `f` induces on the normal space at `s`, the quotient of the ambient tangent space by the tangent
space of the submanifold. -/
def normalHessian : QuadraticForm ℝ (i.NormalSpace s hn) :=
  (criticalHessian I f (i s)).toBilinForm.toQuadraticMap.lift (i.tangentRange s hn)
    (h.tangentRange_le_radical s hn)

/-- The normal Hessian evaluates the critical Hessian on any representative of a normal class. -/
@[simp]
theorem normalHessian_normalClass (v : TangentSpace I (i s)) :
    h.normalHessian s hn (i.normalClass s hn v) = criticalHessian I f (i s) v v := by
  rw [normalClass_def, ← ContinuousLinearMap.toBilinForm_apply,
    ← LinearMap.BilinMap.toQuadraticMap_apply]
  -- The normal space is the quotient by the tangent range, and the normal class is its projection.
  exact QuadraticMap.lift_mk (h.tangentRange_le_radical s hn) v

/-- The radical of the normal Hessian is the image of the kernel of the critical Hessian. -/
theorem radical_normalHessian :
    (h.normalHessian s hn).radical = (criticalHessian I f (i s)).ker.map (i.normalClass s hn) := by
  have hrad := QuadraticMap.radical_lift _ (h.tangentRange_le_radical s hn)
  rw [radical_toQuadraticMap_toBilinForm_criticalHessian (h.contMDiffAt s)] at hrad
  rw [normalClass_def]
  exact hrad

/-- The normal Hessian at `s` is nondegenerate exactly when the kernel of the critical Hessian is
the tangent space of the submanifold. -/
theorem nondegenerate_normalHessian_iff :
    (h.normalHessian s hn).Nondegenerate ↔
      (criticalHessian I f (i s)).ker = (mfderiv J I i s).range := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  have hle := h.tangentRange_le_radical s hn
  rw [radical_toQuadraticMap_toBilinForm_criticalHessian (h.contMDiffAt s)] at hle
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, radical_normalHessian, eq_bot_iff,
    Submodule.map_le_iff_le_comap, Submodule.comap_bot, normalClass_ker]
  exact ⟨fun hker ↦ le_antisymm hker hle, fun hker ↦ hker.le⟩

/-- A critical submanifold is nondegenerate exactly when all of its normal Hessians are
nondegenerate. -/
theorem isNondegenerateCriticalSubmanifold_iff :
    i.IsNondegenerateCriticalSubmanifold f ↔ ∀ s, (h.normalHessian s hn).Nondegenerate := by
  exact ⟨fun h' s ↦ (h.nondegenerate_normalHessian_iff s hn).2 (h'.ker_criticalHessian s),
    fun hnd ↦ ⟨h, fun s ↦ (h.nondegenerate_normalHessian_iff s hn).1 (hnd s)⟩⟩

variable [FiniteDimensional ℝ E]

/-- The negative index of inertia of the normal Hessian is the Morse index of `f`. -/
theorem sigNeg_normalHessian : sigNeg (h.normalHessian s hn) = manifoldMorseIndex I f (i s) :=
  (sigNeg_lift _ _ _).trans manifoldMorseIndex_eq_sigNeg_criticalHessian.symm

/-- The positive index of inertia of the normal Hessian is the Morse index of `-f`. -/
theorem sigPos_normalHessian :
    sigPos (h.normalHessian s hn) = manifoldMorseIndex I (-f) (i s) :=
  (sigPos_lift _ _ _).trans manifoldMorseIndex_neg_eq_sigPos_criticalHessian.symm

end IsCriticalSubmanifold

/-- Along a nondegenerate critical submanifold, the Morse indices of `f` and `-f` add up to the
dimension of the normal space: the normal space splits into a positive and a negative definite
part for the normal Hessian. -/
theorem IsNondegenerateCriticalSubmanifold.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    [FiniteDimensional ℝ E] (h : i.IsNondegenerateCriticalSubmanifold f) (s : S) (hn : n ≠ 0) :
    manifoldMorseIndex I (-f) (i s) + manifoldMorseIndex I f (i s) =
      Module.finrank ℝ (i.NormalSpace s hn) := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  -- The normal space is a quotient of the finite-dimensional tangent space.
  have : FiniteDimensional ℝ (i.NormalSpace s hn) :=
    inferInstanceAs (FiniteDimensional ℝ (TangentSpace I (i s) ⧸ i.tangentRange s hn))
  have hc := h.toIsCriticalSubmanifold
  rw [← hc.sigPos_normalHessian s hn, ← hc.sigNeg_normalHessian s hn]
  exact sigPos_add_sigNeg_of_nondegenerate _
    ((hc.nondegenerate_normalHessian_iff s hn).2 (h.ker_criticalHessian s))

end Boundaryless

section Product

variable [I.Boundaryless] [IsManifold J n S] [IsManifold I n M]

/-- **Bott's local model.** If `c` is a nondegenerate critical point of `g` and the preferred chart
of `M` at `c` is centred at `c`, then the slice `S × {c}` is a nondegenerate critical submanifold
of `g ∘ Prod.snd` on `S × M`: the critical Hessian there is the Hessian of `g` in the `M`-direction
and vanishes in the `S`-direction. -/
theorem isNondegenerateCriticalSubmanifold_prodMkLeft {g : M → ℝ} {c : M}
    (hc : extChartAt I c c = 0) (hg : IsManifoldNondegenerateCriticalPoint I g c) :
    IsNondegenerateCriticalSubmanifold
      (ofIsSmoothEmbedding (fun s : S ↦ (s, c))
        (isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero (I := J) (n := n) hc))
      (g ∘ Prod.snd) := by
  obtain ⟨hg2, hg0, hinv⟩ := isManifoldNondegenerateCriticalPoint_iff_criticalHessian.1 hg
  have hmg : mfderiv I 𝓘(ℝ) g c = 0 :=
    mem_criticalPoints_iff_mfderiv_eq_zero.1 (mem_criticalPoints.2 hg0)
  -- `g ∘ Prod.snd` is the separated sum of zero and `g`, so its critical Hessian at `(s, c)` is
  -- the critical Hessian of `g` at `c` applied to the `M`-components.
  have hsum : g ∘ Prod.snd = (fun _ : S ↦ (0 : ℝ)) ∘ Prod.fst + g ∘ Prod.snd := by
    funext p
    simp
  have h0 (s : S) : criticalHessian J (fun _ : S ↦ (0 : ℝ)) s = 0 := by
    rw [criticalHessian_def, Function.comp_def]
    simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply]
    -- The two sides differ only in reading the model space `F` as `TangentSpace J s`.
    rfl
  have hH (s : S) (v w : F × E) :
      criticalHessian (J.prod I) (g ∘ Prod.snd) (s, c) v w = criticalHessian I g c v.2 w.2 := by
    rw [hsum, criticalHessian_comp_fst_add_comp_snd_apply contDiffAt_const
      hg2.contDiffAt_comp_extChartAt_symm, h0]
    -- The zero form applied to the `S`-components, read in the model space `F`, is zero.
    exact zero_add _
  refine ⟨⟨fun s ↦ ?_, fun s ↦ ?_⟩, fun s ↦ ?_⟩
  · rw [ofIsSmoothEmbedding_apply]
    exact hg2.comp _ contMDiffAt_snd
  · rw [ofIsSmoothEmbedding_apply, mem_criticalPoints_iff_mfderiv_eq_zero,
      mfderiv_comp (s, c) (hg2.mdifferentiableAt two_ne_zero) mdifferentiableAt_snd, hmg,
      ContinuousLinearMap.zero_comp]
  · -- The kernel of the critical Hessian and the tangent space of the slice are both `F × {0}`.
    have hmem (x : F × E) :
        criticalHessian (J.prod I) (g ∘ Prod.snd) (s, c) x = 0 ↔ x.2 = 0 := by
      refine ⟨fun hx ↦ ?_, fun h2 ↦ ?_⟩
      · -- Pairing `x` with the vectors `(0, z)` shows that `x.2` is in the kernel of the
        -- invertible Hessian of `g`.
        have hw : criticalHessian I g c x.2 = 0 := ContinuousLinearMap.ext fun z ↦
          (hH s x (0, z)).symm.trans (congr($hx (0, z)).trans (zero_apply _))
        exact hinv.injective (hw.trans (map_zero _).symm)
      · ext z
        rw [hH s x z, h2, zero_apply]
        exact congr($(map_zero (criticalHessian I g c)) _).trans (zero_apply _)
    rw [ofIsSmoothEmbedding_apply, coe_ofIsSmoothEmbedding, mfderiv_prod_left,
      ContinuousLinearMap.coe_inl]
    ext x
    exact LinearMap.mem_ker.trans ((hmem x).trans
      (SetLike.ext_iff.1 (LinearMap.range_inl ℝ F E) x).symm)

end Product

end TauCeti.SmoothEmbedding
