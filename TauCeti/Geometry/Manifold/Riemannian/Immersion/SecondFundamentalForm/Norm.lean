/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Bilinear
public import TauCeti.Geometry.Manifold.Riemannian.Immersion.SecondFundamentalForm.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Topology.VectorBundle.Riemannian.Hermitian

/-!
# Squared norm of the second fundamental form

The second fundamental form of a `C²` map is tensorial in both tangent
arguments. Its squared Hilbert–Schmidt norm is the sum of the squares of its coefficients in
any orthonormal tangent frame. Along an immersion that is `C^{k+2}`, the second fundamental
form of a `C^k` field and a `C^{k+1}` field is a `C^k` field along the map, and for a `C²`
immersion the squared norm is continuous, including at boundary and corner points of the
source.

The squared norm uses Otis Chodosh's intrinsic two-slot Hilbert–Schmidt construction,
`TauCeti.bilinearHilbertSchmidtEnergy`, from
`TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Bilinear`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7–8.
-/

public section

open Bundle ContinuousLinearMap CovariantDerivative Filter Manifold
open TauCeti.Manifold
open scoped ContDiff InnerProductSpace Manifold Topology

namespace TauCeti

variable
  {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

section Pointwise

variable [IsManifold J 2 N]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} {f : M → N} {x : M}

omit [FiniteDimensional ℝ E] in
private theorem tensorialAt_immersionSecondFundamentalForm_left (Y : Π y : M, TangentSpace I y) :
    TensorialAt I E (fun X ↦ immersionSecondFundamentalForm cov f X Y x) x where
  smul := fun {_ _} _ _ ↦ immersionSecondFundamentalForm_smul_left _ _ _ _
  add := fun {_ _} _ _ ↦ immersionSecondFundamentalForm_add_left _ _ _ _

omit [FiniteDimensional ℝ E] in
private theorem tensorialAt_immersionSecondFundamentalForm_right
    (hf : ContMDiffAt I J 2 f x) (X : Π y : M, TangentSpace I y) :
    TensorialAt I E (fun Y ↦ immersionSecondFundamentalForm cov f X Y x) x := by
  have coord {W : Π y : M, TangentSpace I y} (hW : MDiffAt (T% W) x) :
      MDifferentiableAt I 𝓘(ℝ, F)
        (sectionCoord ℝ (F := F) f (fun y ↦ mfderiv I J f y (W y)) (f x)) x := by
    have h := hf.contMDiffAt_tangentMap (X := (W x : TangentBundle I M)) (m := 1) (by norm_num)
    exact mdifferentiableAt_sectionCoord f _ ((h.mdifferentiableAt one_ne_zero).comp
      x hW) (FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f x))
  exact ⟨fun {g Y} hg hY ↦ immersionSecondFundamentalForm_smul_right X Y g hg (coord hY),
    fun {Y Z} hY hZ ↦ immersionSecondFundamentalForm_add_right X Y Z (coord hY) (coord hZ)⟩

variable (cov f x) in
open Classical in
/-- The pointwise bilinear form induced by `immersionSecondFundamentalForm` at points where the
map is `C²`. It is zero at other points. -/
noncomputable def immersionSecondFundamentalFormAt :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace J (f x) :=
  if hf : ContMDiffAt I J 2 f x then
    TensorialAt.mkHom₂ (fun X Y ↦ immersionSecondFundamentalForm cov f X Y x) x
      (fun Y _ ↦ tensorialAt_immersionSecondFundamentalForm_left Y)
      (fun X _ ↦ tensorialAt_immersionSecondFundamentalForm_right hf X)
  else 0

/-- The pointwise second fundamental form vanishes outside the `C²` locus. -/
@[simp]
theorem immersionSecondFundamentalFormAt_of_not_contMDiffAt
    (hf : ¬ ContMDiffAt I J 2 f x) : immersionSecondFundamentalFormAt (I := I) cov f x = 0 := by
  rw [immersionSecondFundamentalFormAt, dite_eq_right hf]

/-- Evaluating the pointwise form on differentiable vector fields recovers the covariant
definition of the second fundamental form. -/
theorem immersionSecondFundamentalFormAt_apply (hf : ContMDiffAt I J 2 f x)
    {X Y : Π y : M, TangentSpace I y} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    immersionSecondFundamentalFormAt cov f x (X x) (Y x) =
      immersionSecondFundamentalForm cov f X Y x := by
  rw [immersionSecondFundamentalFormAt, dite_eq_left hf, TensorialAt.mkHom₂_apply _ _ hX hY]

/-- Values of the pointwise second fundamental form lie in the normal space. -/
theorem immersionSecondFundamentalFormAt_mem (v w : TangentSpace I x) :
    immersionSecondFundamentalFormAt cov f x v w ∈ orthogonalNormalSpace I J f x := by
  by_cases hf : ContMDiffAt I J 2 f x
  · rw [immersionSecondFundamentalFormAt, dite_eq_left hf,
      TensorialAt.mkHom₂_apply_eq_extend]
    exact immersionSecondFundamentalForm_mem _ _ x
  · simp [immersionSecondFundamentalFormAt_of_not_contMDiffAt hf]

/-- The pointwise second fundamental form of a torsion-free connection is symmetric. -/
theorem immersionSecondFundamentalFormAt_comm (ht : cov.IsTorsionFree)
    (v w : TangentSpace I x) :
    immersionSecondFundamentalFormAt cov f x v w =
      immersionSecondFundamentalFormAt cov f x w v := by
  by_cases hf : ContMDiffAt I J 2 f x
  · simp only [immersionSecondFundamentalFormAt, dite_eq_left hf,
      TensorialAt.mkHom₂_apply_eq_extend]
    exact immersionSecondFundamentalForm_comm ht hf
      (FiberBundle.mdifferentiableAt_extend ..) (FiberBundle.mdifferentiableAt_extend ..)
  · simp [immersionSecondFundamentalFormAt_of_not_contMDiffAt hf]

section Norm

variable [RiemannianBundle (fun y : M ↦ TangentSpace I y)]

/-- The squared Hilbert–Schmidt norm of the second fundamental form. -/
noncomputable def immersionSecondFundamentalFormNormSq
    (cov : CovariantDerivative J F (TangentSpace J : N → Type _)) (f : M → N) (x : M) : ℝ :=
  bilinearHilbertSchmidtEnergy (𝕜 := ℝ) (E := TangentSpace I x) (E₂ := TangentSpace I x)
    (F := TangentSpace J (f x)) (immersionSecondFundamentalFormAt (I := I) cov f x)

/-- The squared norm is the intrinsic two-slot Hilbert–Schmidt energy of the pointwise form. -/
theorem immersionSecondFundamentalFormNormSq_def :
    immersionSecondFundamentalFormNormSq (I := I) cov f x =
      bilinearHilbertSchmidtEnergy (immersionSecondFundamentalFormAt (I := I) cov f x) := (rfl)

/-- The squared norm of the second fundamental form is nonnegative. -/
theorem immersionSecondFundamentalFormNormSq_nonneg :
    0 ≤ immersionSecondFundamentalFormNormSq (I := I) cov f x := by
  rw [immersionSecondFundamentalFormNormSq_def]
  exact bilinearHilbertSchmidtEnergy_nonneg _

/-- The squared norm vanishes exactly when the pointwise second fundamental form vanishes. -/
@[simp]
theorem immersionSecondFundamentalFormNormSq_eq_zero_iff :
    immersionSecondFundamentalFormNormSq (I := I) cov f x = 0 ↔
      immersionSecondFundamentalFormAt (I := I) cov f x = 0 := by
  rw [immersionSecondFundamentalFormNormSq_def, bilinearHilbertSchmidtEnergy_eq_zero_iff]

/-- The squared norm is the sum of the squared norms of all coefficients in an orthonormal
tangent basis. -/
theorem immersionSecondFundamentalFormNormSq_eq_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    immersionSecondFundamentalFormNormSq (I := I) cov f x =
      ∑ i, ∑ j, ‖immersionSecondFundamentalFormAt cov f x (b i) (b j)‖ ^ 2 :=
  bilinearHilbertSchmidtEnergy_eq_sum b b (immersionSecondFundamentalFormAt (I := I) cov f x)

end Norm

end Pointwise

section Regularity

variable [IsManifold J ∞ N] [T2Space N] {k : ℕ∞ω} [ENat.LEInfty k]
  [IsContMDiffRiemannianBundle J k F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} [ContMDiffCovariantDerivative cov k]
  {f : M → N} {x : M}

/-- **The second fundamental form is `C^k`**: at a point where `f` is `C^{k+2}` with injective
differential, `B(X, Y)` is a `C^k` field along `f` for a `C^k` field `X` and a `C^{k+1}` field `Y`,
a `C^k` covariant derivative and a `C^k` metric on `N`. This includes boundary and corner points
of the source. -/
theorem contMDiffAt_immersionSecondFundamentalForm (hf : ContMDiffAt I J (k + 1 + 1) f x)
    (hinj : Function.Injective (mfderiv I J f x)) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiffAt k (T% X) x) (hY : CMDiffAt (k + 1) (T% Y) x) :
    ContMDiffAt I J.tangent k
      (fun y ↦ TotalSpace.mk' F (f y) (immersionSecondFundamentalForm cov f X Y y)) x := by
  have hdf : ContMDiffAt I J.tangent (k + 1)
      (fun y ↦ TotalSpace.mk' F (f y) (mfderiv I J f y (Y y))) x := by
    simpa only [id_eq] using hf.mfderiv_apply_sectionAlong (b := id) hY le_rfl
  simpa only [immersionSecondFundamentalForm_def, orthogonalNormalSpace_def] using
    hf.starProjection_orthogonal_range_mfderiv_apply le_self_add hinj
      (cov.contMDiffAt_alongMap_apply hdf hX)

end Regularity

section Continuity

variable [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle I 1 E (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle J 0 F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} {f : M → N} {x : M}
  [ContMDiffCovariantDerivative cov 0]

/-- The squared norm of the second fundamental form of a `C²` immersion is continuous at source
points with injective differential, including boundary and corner points. -/
theorem continuousAt_immersionSecondFundamentalFormNormSq
    (hf : ContMDiffAt I J 2 f x) (hinj : Function.Injective (mfderiv I J f x)) :
    ContinuousAt (immersionSecondFundamentalFormNormSq (I := I) cov f) x := by
  obtain ⟨s, hs, hx, X, hX, ho⟩ := exists_isLocalFrameOn_orthonormal
    (I := I) (n := 1) (F := E) (V := TangentSpace I) x
  have hval (i j : Fin (Module.finrank ℝ E)) :
      ContMDiffAt I J.tangent 0
        (fun y ↦ TotalSpace.mk' F (f y) (immersionSecondFundamentalForm cov f (X i) (X j) y))
        x :=
    contMDiffAt_immersionSecondFundamentalForm (k := 0) (hf.of_le (by norm_num)) hinj
      ((hX.contMDiffAt hs hx i).of_le zero_le) (by simpa using hX.contMDiffAt hs hx j)
  have : IsContinuousRiemannianBundle F (TangentSpace J : N → Type _) :=
    IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := J) (n := 0)
  have hn : Continuous (fun z : TangentBundle J N ↦ ‖z.snd‖) :=
    ContinuousFiberNorm.continuous_norm (F := F) (E := TangentSpace J)
  have hsq (i j : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun y ↦ ‖immersionSecondFundamentalForm cov f (X i) (X j) y‖ ^ 2) x :=
    (hn.continuousAt.comp (hval i j).continuousAt).pow 2
  have hsum : ContinuousAt (fun y ↦ ∑ i, ∑ j,
      ‖immersionSecondFundamentalForm cov f (X i) (X j) y‖ ^ 2) x :=
    tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦ hsq i j
  apply hsum.congr_of_eventuallyEq
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 hf
  filter_upwards [hs.mem_nhds hx, hfn] with y hy hyf
  let b := OrthonormalBasis.mk (ho y hy) (hX.generating hy).ge
  rw [immersionSecondFundamentalFormNormSq_eq_sum b]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simpa only [b, OrthonormalBasis.coe_mk] using congrArg (fun z ↦ ‖z‖ ^ 2)
    (immersionSecondFundamentalFormAt_apply (cov := cov) hyf
      ((hX.contMDiffAt hs hy i).mdifferentiableAt one_ne_zero)
      ((hX.contMDiffAt hs hy j).mdifferentiableAt one_ne_zero))

/-- The squared norm of the second fundamental form of a `C²` immersion is continuous on the
entire source. -/
theorem continuous_immersionSecondFundamentalFormNormSq
    (hf : ContMDiff I J 2 f) (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    Continuous (immersionSecondFundamentalFormNormSq (I := I) cov f) :=
  continuous_iff_continuousAt.2 fun y ↦
    continuousAt_immersionSecondFundamentalFormNormSq (hf y) (hinj y)

end Continuity

end TauCeti
