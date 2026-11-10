/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Signature
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Morse–Bott critical submanifolds and the normal Hessian

A function `f` on a manifold `M` is Morse–Bott when its critical set is a union of submanifolds
along which the critical Hessian is as nondegenerate as possible. This file sets up the pointwise
theory of one such submanifold, given as a bundled smooth embedding `i : S → M`.

Along a submanifold of critical points the critical Hessian always vanishes in the tangent
directions: if `γ` is a differentiable map whose values near `s` are critical points of a `C²`
function `f`, then `Hess f (γ s) (dγ u, w) = 0` for all `u` and `w`
(`TauCeti.criticalHessian_mfderiv_apply_eq_zero`). For a smooth embedding `i` whose image consists
of critical points (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold`), the tangent space of the
image therefore lies in the kernel of the critical Hessian, and the Hessian descends to a symmetric
bilinear form on the intrinsic normal space `TangentSpace I (i s) ⧸ range (di)`, the **normal
Hessian** (`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`).

The submanifold is **nondegenerate**, or Morse–Bott, when the kernel of the critical Hessian is
exactly the tangent space of the image
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`); equivalently, the normal Hessian
is nondegenerate at every point. Then the normal Hessian carries all of the inertia of the critical
Hessian: its negative index is the Morse index of `f` at the point, its positive index is the Morse
index of `-f`, and the two add up to the codimension of the submanifold. For a zero-dimensional
submanifold the condition says exactly that each point is a nondegenerate critical point, and
conversely a nondegenerate critical point lies on no critical submanifold of positive dimension.

## Main declarations

* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold`: a smooth embedding into the critical set of a
  function which is `C²` along it.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isLocallyConstant_comp`: a function is locally
  constant along each of its critical submanifolds.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.normalHessian`: the normal Hessian.
* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`: Morse–Bott critical submanifolds.
* `TauCeti.SmoothEmbedding.IsCriticalSubmanifold.isNondegenerateCriticalSubmanifold_iff`:
  nondegeneracy of the submanifold is nondegeneracy of the normal Hessian.
* `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.sigNeg_normalHessian`: the Morse
  index is the negative index of inertia of the normal Hessian.
* `IsNondegenerateCriticalSubmanifold.manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank`:
  index plus coindex is the codimension.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_iff_of_subsingleton`: in dimension
  zero, Morse–Bott means Morse.
* `TauCeti.SmoothEmbedding.isNondegenerateCriticalSubmanifold_comp_snd`: the model example, the
  slice `M × {0}` for `(x, v) ↦ q v` with `q` nondegenerate at `0`.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* A. Banyaga and D. E. Hurtubise, *A proof of the Morse–Bott lemma*, Expositiones Mathematicae 22
  (2004), 365–373.
-/

public section

open Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {f : M → ℝ}

namespace SmoothEmbedding

variable {n : ℕ∞ω}

/-- A smooth embedding `i : S → M` is a **critical submanifold** of `f` when every point of its
image is a critical point of `f` and `f` is `C²` at each of these points. No condition is put on
the Hessian; see `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold` for the Morse–Bott
condition. -/
structure IsCriticalSubmanifold (i : SmoothEmbedding J I n S M) (f : M → ℝ) : Prop where
  /-- The function is `C²` at every point of the submanifold. -/
  contMDiffAt (s : S) : ContMDiffAt I 𝓘(ℝ) 2 f (i s)
  /-- Every point of the submanifold is a critical point. -/
  mem_criticalPoints (s : S) : i s ∈ criticalPoints I f

/-- A smooth embedding `i : S → M` is a **nondegenerate critical submanifold**, or **Morse–Bott
critical submanifold**, of `f` when it is a critical submanifold and the kernel of the critical
Hessian at each point `i s` is contained in the tangent space `range (mfderiv J I i s)` of the
image. On a boundaryless manifold the reverse inclusion always holds
(`TauCeti.SmoothEmbedding.IsCriticalSubmanifold.tangentRange_le_ker_criticalHessian`), so the
condition says that the kernel of the Hessian is exactly the tangent space of the critical
submanifold. -/
structure IsNondegenerateCriticalSubmanifold (i : SmoothEmbedding J I n S M) (f : M → ℝ) : Prop
    extends i.IsCriticalSubmanifold f where
  /-- The kernel of the critical Hessian lies in the tangent space of the submanifold. -/
  ker_criticalHessian_le (s : S) :
    (criticalHessian I f (i s)).ker ≤ (mfderiv J I i s).toLinearMap.range

variable {i : SmoothEmbedding J I n S M} (hn : n ≠ 0)

include hn in
/-- **A function is locally constant along a critical submanifold.** The differential of `f ∘ i`
is `df ∘ di`, which vanishes because every point of the submanifold is critical. In particular `f`
takes a single value, the critical value, on each connected component of `S`. -/
theorem IsCriticalSubmanifold.isLocallyConstant_comp [IsManifold J 1 S]
    (h : i.IsCriticalSubmanifold f) : IsLocallyConstant (f ∘ i) := by
  have hf (s : S) : MDifferentiableAt I 𝓘(ℝ) f (i s) :=
    (h.contMDiffAt s).mdifferentiableAt two_ne_zero
  have hi (s : S) : MDifferentiableAt J I i s := (i.contMDiff s).mdifferentiableAt hn
  refine MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero (fun s ↦ (hf s).comp s (hi s))
    fun s ↦ ?_
  rw [mfderiv_comp s (hf s) (hi s),
    mem_criticalPoints_iff_mfderiv_eq_zero.1 (h.mem_criticalPoints s),
    ContinuousLinearMap.zero_comp]

namespace IsCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f)
include h

/-- Along a critical submanifold, the tangent space of the submanifold lies in the kernel of the
critical Hessian. -/
theorem tangentRange_le_ker_criticalHessian (s : S) :
    i.tangentRange s hn ≤ (criticalHessian I f (i s)).ker := by
  rintro _ ⟨u, rfl⟩
  ext w
  exact criticalHessian_mfderiv_apply_eq_zero (h.contMDiffAt s)
    ((i.contMDiff s).mdifferentiableAt hn) (Eventually.of_forall h.mem_criticalPoints) u w

/-- The tangent space of a critical submanifold lies in the kernel of the bilinear form of the
critical Hessian. -/
private theorem tangentRange_le_ker_toBilinForm (s : S) :
    i.tangentRange s hn ≤ LinearMap.ker (criticalHessian I f (i s)).toBilinForm := by
  rw [ContinuousLinearMap.ker_toBilinForm]
  exact h.tangentRange_le_ker_criticalHessian hn s

omit h in
/-- The **normal Hessian** of a critical submanifold `i` of `f` at `s`: the critical Hessian of
`f` at `i s`, which vanishes on the tangent space of the submanifold, descended to a bilinear form
on the normal space `TangentSpace I (i s) ⧸ range (mfderiv J I i s)`. -/
def normalHessian (h : i.IsCriticalSubmanifold f) (s : S) :
    LinearMap.BilinForm ℝ (i.NormalSpace s hn) :=
  -- `NormalSpace` is by definition the quotient by `tangentRange`, with its quotient structure.
  (LinearMap.IsRefl.liftQ₂ (criticalHessian I f (i s)).toBilinForm (i.tangentRange s hn)
    (isSymm_toBilinForm_criticalHessian (h.contMDiffAt s)).isRefl
    (h.tangentRange_le_ker_toBilinForm hn s) :
    LinearMap.BilinForm ℝ (TangentSpace I (i s) ⧸ i.tangentRange s hn))

/-- The normal Hessian evaluates on normal classes as the critical Hessian. -/
@[simp]
theorem normalHessian_normalClass (s : S) (v w : TangentSpace I (i s)) :
    h.normalHessian hn s (i.normalClass s hn v) (i.normalClass s hn w) =
      criticalHessian I f (i s) v w := by
  rw [normalClass_def]
  exact LinearMap.liftQ₂_mk (h.tangentRange_le_ker_toBilinForm hn s)
    ((isSymm_toBilinForm_criticalHessian (h.contMDiffAt s)).isRefl.ker_flip ▸
      h.tangentRange_le_ker_toBilinForm hn s) v w

/-- The normal Hessian is symmetric. -/
theorem isSymm_normalHessian (s : S) : (h.normalHessian hn s).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun p q ↦ ?_
  obtain ⟨v, rfl⟩ := i.normalClass_surjective s hn p
  obtain ⟨w, rfl⟩ := i.normalClass_surjective s hn q
  simp only [normalHessian_normalClass]
  exact criticalHessian_apply_swap (h.contMDiffAt s) v w

/-- The kernel of the normal Hessian is the image of the kernel of the critical Hessian in the
normal space. -/
theorem ker_normalHessian (s : S) :
    LinearMap.ker (h.normalHessian hn s) =
      (criticalHessian I f (i s)).ker.map (i.normalClass s hn) := by
  ext p
  obtain ⟨v, rfl⟩ := i.normalClass_surjective s hn p
  simp only [LinearMap.mem_ker, Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨v, ?_, rfl⟩
    ext w
    simpa using LinearMap.congr_fun hv (i.normalClass s hn w)
  · rintro ⟨v', hv', hvv'⟩
    refine LinearMap.ext fun q ↦ ?_
    obtain ⟨w, rfl⟩ := i.normalClass_surjective s hn q
    have hv'' : criticalHessian I f (i s) v' = 0 := hv'
    rw [← hvv', normalHessian_normalClass, hv'', zero_apply, LinearMap.zero_apply]

/-- The normal Hessian has trivial kernel exactly when the kernel of the critical Hessian lies in
the tangent space of the submanifold. -/
theorem ker_normalHessian_eq_bot_iff (s : S) :
    LinearMap.ker (h.normalHessian hn s) = ⊥ ↔
      (criticalHessian I f (i s)).ker ≤ i.tangentRange s hn := by
  rw [h.ker_normalHessian, ← LinearMap.le_ker_iff_map, normalClass_ker]

end IsCriticalSubmanifold

namespace IsNondegenerateCriticalSubmanifold

variable [I.Boundaryless] [IsManifold I 2 M] (h : i.IsNondegenerateCriticalSubmanifold f)
include h

/-- At each point of a nondegenerate critical submanifold, the kernel of the critical Hessian is
the tangent space of the submanifold. -/
theorem ker_criticalHessian (s : S) :
    (criticalHessian I f (i s)).ker = i.tangentRange s hn :=
  le_antisymm (h.ker_criticalHessian_le s) (h.tangentRange_le_ker_criticalHessian hn s)

/-- At each point of a nondegenerate critical submanifold, the radical of the quadratic form of
the critical Hessian is the tangent space of the submanifold. -/
theorem radical_criticalHessian (s : S) :
    (criticalHessian I f (i s)).toBilinForm.toQuadraticMap.radical = i.tangentRange s hn := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [LinearMap.BilinForm.radical_toQuadraticMap _
      (isSymm_toBilinForm_criticalHessian (h.contMDiffAt s)),
    ContinuousLinearMap.ker_toBilinForm, h.ker_criticalHessian hn s]

/-- The normal Hessian of a nondegenerate critical submanifold has trivial kernel. -/
theorem ker_normalHessian (s : S) : LinearMap.ker (h.normalHessian hn s) = ⊥ :=
  (h.toIsCriticalSubmanifold.ker_normalHessian_eq_bot_iff hn s).mpr (h.ker_criticalHessian_le s)

/-- The quadratic form of the normal Hessian is the quadratic form of the critical Hessian
descended to the quotient by its radical, the tangent space of the submanifold. -/
private theorem toQuadraticMap_normalHessian (s : S) :
    (h.normalHessian hn s).toQuadraticMap =
      (criticalHessian I f (i s)).toBilinForm.toQuadraticMap.lift (i.tangentRange s hn)
        (h.radical_criticalHessian hn s).ge := by
  ext p
  obtain ⟨v, rfl⟩ := i.normalClass_surjective s hn p
  rw [LinearMap.BilinMap.toQuadraticMap_apply, IsCriticalSubmanifold.normalHessian_normalClass,
    normalClass_def]
  exact (QuadraticMap.lift_mk (h.radical_criticalHessian hn s).ge v).symm

variable [FiniteDimensional ℝ E]

/-- **The Morse index of a Morse–Bott critical submanifold** is the negative index of inertia of
its normal Hessian. -/
theorem sigNeg_normalHessian (s : S) :
    sigNeg (h.normalHessian hn s).toQuadraticMap = manifoldMorseIndex I f (i s) := by
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, h.toQuadraticMap_normalHessian hn s]
  exact QuadraticForm.sigNeg_lift _ _ (h.radical_criticalHessian hn s).ge

/-- The positive index of inertia of the normal Hessian of a Morse–Bott critical submanifold is the
Morse index of `-f`. -/
theorem sigPos_normalHessian (s : S) :
    sigPos (h.normalHessian hn s).toQuadraticMap = manifoldMorseIndex I (-f) (i s) := by
  rw [manifoldMorseIndex_neg_eq_sigPos_criticalHessian, h.toQuadraticMap_normalHessian hn s]
  exact QuadraticForm.sigPos_lift _ _ (h.radical_criticalHessian hn s).ge

include hn in
/-- **Index plus coindex is the codimension.** At each point of a Morse–Bott critical
submanifold modelled on `E'`, the Morse indices of `f` and `-f` and the dimension of the
submanifold add up to the dimension of `M`. -/
theorem manifoldMorseIndex_add_manifoldMorseIndex_neg_add_finrank (s : S) :
    manifoldMorseIndex I f (i s) + manifoldMorseIndex I (-f) (i s) + Module.finrank ℝ E' =
      Module.finrank ℝ E := by
  have hsig := QuadraticForm.sigPos_add_sigNeg_add_radical
    (Q := (criticalHessian I f (i s)).toBilinForm.toQuadraticMap)
  have hrank : Module.finrank ℝ (i.tangentRange s hn) = Module.finrank ℝ E' :=
    LinearMap.finrank_range_of_inj (i.isImmersion.mfderiv_injective hn s)
  rw [h.radical_criticalHessian hn s, hrank, ← manifoldMorseIndex_eq_sigNeg_criticalHessian,
    ← manifoldMorseIndex_neg_eq_sigPos_criticalHessian] at hsig
  -- `TangentSpace I (i s)` is by definition the model space `E`.
  have hE : Module.finrank ℝ (TangentSpace I (i s)) = Module.finrank ℝ E := rfl
  omega

end IsNondegenerateCriticalSubmanifold

/-- **Morse–Bott is nondegeneracy of the normal Hessian.** A critical submanifold is
nondegenerate exactly when its normal Hessian has trivial kernel at every point. -/
theorem IsCriticalSubmanifold.isNondegenerateCriticalSubmanifold_iff [I.Boundaryless]
    [IsManifold I 2 M] (h : i.IsCriticalSubmanifold f) :
    i.IsNondegenerateCriticalSubmanifold f ↔ ∀ s, LinearMap.ker (h.normalHessian hn s) = ⊥ :=
  ⟨fun h' s ↦ h'.ker_normalHessian hn s,
    fun hker ↦ ⟨h, fun s ↦ (h.ker_normalHessian_eq_bot_iff hn s).mp (hker s)⟩⟩

/-- A critical submanifold of `f` is a critical submanifold of `-f`. -/
theorem IsCriticalSubmanifold.neg (h : i.IsCriticalSubmanifold f) :
    i.IsCriticalSubmanifold (-f) where
  contMDiffAt s := contDiff_neg.contMDiff.contMDiffAt.comp (i s) (h.contMDiffAt s)
  mem_criticalPoints s := by
    rw [criticalPoints_neg]
    exact h.mem_criticalPoints s

/-- A smooth embedding is a critical submanifold of `f` exactly when it is one of `-f`. -/
@[simp]
theorem isCriticalSubmanifold_neg_iff :
    i.IsCriticalSubmanifold (-f) ↔ i.IsCriticalSubmanifold f :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, IsCriticalSubmanifold.neg⟩

/-- A Morse–Bott critical submanifold of `f` is a Morse–Bott critical submanifold of `-f`. -/
theorem IsNondegenerateCriticalSubmanifold.neg (h : i.IsNondegenerateCriticalSubmanifold f) :
    i.IsNondegenerateCriticalSubmanifold (-f) where
  toIsCriticalSubmanifold := h.toIsCriticalSubmanifold.neg
  ker_criticalHessian_le s v hv := by
    rw [criticalHessian_neg] at hv
    exact h.ker_criticalHessian_le s (neg_eq_zero.mp hv)

/-- A function is Morse–Bott along `i` exactly when its negation is. -/
@[simp]
theorem isNondegenerateCriticalSubmanifold_neg_iff :
    i.IsNondegenerateCriticalSubmanifold (-f) ↔ i.IsNondegenerateCriticalSubmanifold f :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, IsNondegenerateCriticalSubmanifold.neg⟩

section Boundaryless

variable [I.Boundaryless] [IsManifold I 2 M]

include hn in
/-- **A nondegenerate critical point lies on no critical submanifold of positive dimension.** If
some point of a critical submanifold modelled on `E'` is a nondegenerate critical point, then `E'`
is trivial. -/
theorem IsCriticalSubmanifold.subsingleton_of_isManifoldNondegenerateCriticalPoint
    (h : i.IsCriticalSubmanifold f) {s : S}
    (hs : IsManifoldNondegenerateCriticalPoint I f (i s)) : Subsingleton E' := by
  refine ⟨fun u u' ↦ i.isImmersion.mfderiv_injective hn s ?_⟩
  -- Tangent vectors of the submanifold lie in the kernel of the injective critical Hessian.
  have hinj := hs.isInvertible_criticalHessian.injective
  have hker (u : TangentSpace J s) : mfderiv J I i s u = 0 :=
    hinj ((h.tangentRange_le_ker_criticalHessian hn s ⟨u, rfl⟩).trans (map_zero _).symm)
  rw [hker u, hker u']

omit [IsManifold I 2 M] in
/-- **In dimension zero, Morse–Bott means Morse.** A smooth embedding of a manifold modelled on a
trivial space is a Morse–Bott critical submanifold of `f` exactly when each of its points is a
nondegenerate critical point of `f`. -/
theorem isNondegenerateCriticalSubmanifold_iff_of_subsingleton [FiniteDimensional ℝ E]
    [Subsingleton E'] :
    i.IsNondegenerateCriticalSubmanifold f ↔
      ∀ s, IsManifoldNondegenerateCriticalPoint I f (i s) := by
  simp only [isManifoldNondegenerateCriticalPoint_iff_criticalHessian, ← mem_criticalPoints]
  refine ⟨fun h s ↦ ⟨h.contMDiffAt s, h.mem_criticalPoints s,
    criticalHessian_isInvertible_of_injective ?_⟩, fun h ↦ ⟨⟨fun s ↦ (h s).1, fun s ↦ (h s).2.1⟩,
      fun s v hv ↦ ?_⟩⟩
  · -- The kernel of the Hessian lies in the range of a map out of the trivial space.
    refine (injective_iff_map_eq_zero (criticalHessian I f (i s))).mpr fun v hv ↦ ?_
    obtain ⟨u, rfl⟩ := h.ker_criticalHessian_le s hv
    -- `TangentSpace J s` is by definition the trivial model space `E'`.
    have hu : u = 0 := Subsingleton.elim (α := E') u 0
    rw [hu, LinearMap.map_zero]
  · rw [(h s).2.2.injective (hv.trans (map_zero _).symm)]
    exact zero_mem _

end Boundaryless

/-- **The constant function is Morse–Bott along the whole manifold.** For a constant function
every point is critical and the critical Hessian vanishes, so its kernel is the whole tangent
space, which is the tangent space of the identity embedding. -/
theorem isNondegenerateCriticalSubmanifold_id_const [IsManifold I n M] (c : ℝ) :
    (SmoothEmbedding.id (I := I) (n := n) (M := M)).IsNondegenerateCriticalSubmanifold
      (fun _ ↦ c) where
  contMDiffAt _ := contMDiffAt_const
  mem_criticalPoints _ := mem_criticalPoints.mpr (mvfderiv_const c)
  ker_criticalHessian_le x v _ := ⟨v, by rw [coe_id, mfderiv_id]; rfl⟩

section Prod

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A tangent vector at `(x, 0)` in the kernel of the critical Hessian of `q ∘ Prod.snd` has
vanishing second component when `0` is a nondegenerate critical point of `q`. -/
private theorem snd_eq_zero_of_criticalHessian_comp_snd_apply_eq_zero {q : V → ℝ}
    (hq : IsNondegenerateCriticalPoint q 0) (x : M)
    (v : TangentSpace (I.prod 𝓘(ℝ, V)) (x, (0 : V)))
    (hv : criticalHessian (I.prod 𝓘(ℝ, V)) (q ∘ Prod.snd) (x, 0) v = 0) : v.2 = 0 := by
  have hD₂ : fderiv ℝ (fderiv ℝ q) 0 v.2 = 0 := ContinuousLinearMap.ext fun w ↦ by
    have hw := congrArg (fun L ↦ L ((0 : E), w)) hv
    exact (criticalHessian_comp_snd_apply hq.contDiffAt x v (0, w)).symm.trans
      hw
  exact hq.isInvertible.injective (hD₂.trans (map_zero _).symm)

/-- **The model Morse–Bott function.** If `q` has a nondegenerate critical point at `0`, then the
slice `M × {0}` of `M × V` is a Morse–Bott critical submanifold of `(x, v) ↦ q v`. The slice is a
smooth embedding for instance by `TauCeti.isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero`. -/
theorem isNondegenerateCriticalSubmanifold_comp_snd {q : V → ℝ}
    (hq : IsNondegenerateCriticalPoint q 0)
    (h : Manifold.IsSmoothEmbedding I (I.prod 𝓘(ℝ, V)) n (fun x : M ↦ (x, (0 : V)))) :
    (ofIsSmoothEmbedding _ h).IsNondegenerateCriticalSubmanifold (q ∘ Prod.snd) where
  contMDiffAt x := by
    rw [ofIsSmoothEmbedding_apply]
    exact hq.contDiffAt.contMDiffAt.comp (x, 0) contMDiffAt_snd
  mem_criticalPoints x := by
    rw [ofIsSmoothEmbedding_apply, mem_criticalPoints,
      mvfderiv_comp (x, 0) (hq.contDiffAt.differentiableAt two_ne_zero).mdifferentiableAt
        mdifferentiableAt_snd, mvfderiv_eq_fderiv, hq.fderiv_eq_zero,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.zero_comp]
  ker_criticalHessian_le x v hv := by
    rw [ofIsSmoothEmbedding_apply] at hv
    have hv₂ : v.2 = 0 := snd_eq_zero_of_criticalHessian_comp_snd_apply_eq_zero hq x v hv
    have hD : mfderiv I (I.prod 𝓘(ℝ, V)) (fun y : M ↦ (y, (0 : V))) x =
        (ContinuousLinearMap.id ℝ _).prod 0 :=
      ((hasMFDerivAt_id x).prodMk (hasMFDerivAt_const (0 : V) x)).mfderiv
    refine ⟨v.1, ?_⟩
    rw [coe_ofIsSmoothEmbedding, hD]
    exact Prod.ext rfl hv₂.symm

end Prod

end SmoothEmbedding

end TauCeti
