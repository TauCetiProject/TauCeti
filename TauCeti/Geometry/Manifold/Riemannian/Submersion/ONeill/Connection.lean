/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Integrability
public import TauCeti.Geometry.Manifold.Riemannian.Submersion.Connection
import TauCeti.Geometry.Manifold.Distribution.Kernel
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Prod

/-!
# Levi-Civita connection decomposition for a Riemannian submersion

For a Riemannian submersion `f : M → N` with horizontal lift `IsRiemannianSubmersion.horizontalLift`
and O'Neill tensors `A` and `T` (`IsRiemannianSubmersion.oneillA` and
`IsRiemannianSubmersion.oneillT`), the Levi-Civita derivative of a basic horizontal vector field
`X y = h.horizontalLift y (B (f y))` splits completely into base differentiation and O'Neill's
tensors:

* Along a horizontal vector `u ∈ (mfderiv I J f x).kerᗮ`,
  `∇_u X = h.horizontalLift x (∇^N_(df u) B) + A_u (X x)`.
* Along a vertical vector `w ∈ (mfderiv I J f x).ker`,
  `∇_w X = A_(X x) w + T_w (X x)`.
* Along an arbitrary tangent vector `u`, summing the two components expresses `∇_u X` in terms of
  `∇^N_(df u) B`, `A`, and `T`.
* For a vertical field `V`, the Lie bracket with `X` is vertical and satisfies
  `[X, V] x = v (∇_(X x) V) - T_(V x) (X x)`.

For the first projection of a Riemannian product `M × N → M`, both fundamental tensors vanish
identically (`TauCeti.oneillA_fst` and `TauCeti.oneillT_fst`).

## Main results

* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker`:
  `∇_u X` for a basic horizontal field `X` and horizontal `u`.
* `starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker` and
  `leviCivitaConnection_horizontalLift_of_mem_ker`: `h (∇_w X)` and `∇_w X` for a basic horizontal
  field `X` and vertical `w`.
* `TauCeti.IsRiemannianSubmersion.leviCivitaConnection_horizontalLift`:
  `∇_u X` for a basic horizontal field `X` and arbitrary tangent vector `u`.
* `TauCeti.IsRiemannianSubmersion.mlieBracket_horizontalLift_of_eventually_mem_ker`:
  `[X, V] = v (∇_X V) - T_V X` for basic horizontal `X` and vertical `V`.
* `TauCeti.oneillA_fst` and `TauCeti.oneillT_fst`: both O'Neill tensors vanish for a Riemannian
  product projection.

## References

* B. O'Neill, *The fundamental equations of a submersion*, Michigan Math. J. 13 (1966),
  459–469, Lemmas 1 and 2.
* A. L. Besse, *Einstein Manifolds*, Springer, 1987, Chapter 9, §C (equations 9.24).
-/

public section

open Bundle Filter Manifold VectorField
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti.IsRiemannianSubmersion

section Preliminaries

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

variable (I J) in
private theorem starProjection_orthogonal_ker_add_starProjection_ker
    (f : M → N) {x : M} (v : TangentSpace I x) :
    (mfderiv I J f x).kerᗮ.starProjection v + (mfderiv I J f x).ker.starProjection v = v := by
  simp [Submodule.starProjection_orthogonal]

end Preliminaries

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} (h : IsRiemannianSubmersion I J f)

-- These regularity indices are propositionally, but not definitionally, equal to two.
local instance : IsManifold I (minSmoothness ℝ 2) M := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

local instance : IsManifold J (minSmoothness ℝ 2) N := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact .of_le (by norm_cast)

section BasicFields

variable {B : Π y : N, TangentSpace J y} {x : M}
include h

private theorem mdifferentiableAt_horizontalLift_of_contMDiffAt_one
    (hB : CMDiffAt 1 (T% B) (f x)) :
    MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x := by
  let : IsManifold I ((1 : ℕ∞ω) + 1) M := by
    rw [one_add_one_eq_two]
    exact .of_le (by norm_cast)
  exact (h.contMDiffAt_horizontalLift hB (by norm_num)).mdifferentiableAt one_ne_zero

/-- The horizontal component of the Levi-Civita derivative of a basic horizontal field along a
horizontal tangent vector `u` is the horizontal lift of the base Levi-Civita derivative along
`df u`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (B (f y))) x u) =
      h.horizontalLift x
        (CovariantDerivative.leviCivitaConnection J N B (f x) (mfderiv I J f x u)) := by
  conv_lhs => rw [← h.horizontalLift_mfderiv_of_mem x hu]
  exact h.starProjection_covariantDerivative_horizontalLift
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (I := I) (M := M))
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection (I := J) (M := N))
    hB (mfderiv I J f x u)

/-- **O'Neill's horizontal connection formula.** Differentiating a basic horizontal field
`y ↦ h.horizontalLift y (B (f y))` along a horizontal tangent vector `u` gives the lifted base
derivative plus O'Neill's `A`-tensor. -/
theorem leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {u : TangentSpace I x}
    (hu : u ∈ (mfderiv I J f x).kerᗮ) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N B (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  rw [← starProjection_orthogonal_ker_add_starProjection_ker I J f
      (CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u),
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker
      hB hu,
    h.oneillA_apply_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) u,
    Submodule.starProjection_eq_self_iff.mpr hu]

/-- **O'Neill's Lemma 2 (horizontal part).** For a basic horizontal field `X` and a vertical
tangent vector `w`, the horizontal part of `∇_w X` is `A_(X x) w`. -/
theorem starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).ker) :
    (mfderiv I J f x).kerᗮ.starProjection
        (CovariantDerivative.leviCivitaConnection I M
          (fun y ↦ h.horizontalLift y (B (f y))) x w) =
      h.oneillA x (h.horizontalLift x (B (f x))) w := by
  let : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set X : Π y : M, TangentSpace I y := fun y ↦ h.horizontalLift y (B (f y))
  have hXd : MDiffAt (T% X) x := h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  set V : Π y : M, TangentSpace I y :=
    fun y ↦ (mfderiv I J f y).ker.starProjection (FiberBundle.extend E w y)
  have hVd : MDiffAt (T% V) x :=
    ((h.contMDiff_starProjection_ker (n := ∞) (by simp)).mdifferentiableAt
      (by simp)).clm_bundle_apply (FiberBundle.mdifferentiableAt_extend I E w)
  have hVx : V x = w := by simp [V, Submodule.starProjection_eq_self_iff.mpr hw]
  have hVv (y : M) : V y ∈ (mfderiv I J f y).ker := Submodule.starProjection_apply_mem _ _
  have htor := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hbr_mem : mlieBracket I X V x ∈ (mfderiv I J f x).ker :=
    (h.isSubmersion.contMDiff x).mlieBracket_mem_ker_mfderiv_of_eventually_related
      (by simp [minSmoothness_of_isRCLikeNormedField]) hXd hVd (hB.mdifferentiableAt one_ne_zero)
      (.of_forall fun y ↦ h.mfderiv_horizontalLift y _) (.of_forall hVv)
  have hbr : (mfderiv I J f x).kerᗮ.starProjection (mlieBracket I X V x) = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr
      (by rwa [Submodule.orthogonal_orthogonal])
  have hAV := h.oneillA_apply_of_eventually_mem_ker hVd (.of_forall hVv) (X x)
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hAV
  have hproj := congrArg (mfderiv I J f x).kerᗮ.starProjection htor
  rw [map_sub, hbr, sub_eq_zero] at hproj
  rw [← hVx, ← hproj, ← hAV, hVx]

/-- **O'Neill's vertical-horizontal connection formula.** Differentiating a basic horizontal field
`X` along a vertical vector `w` gives `A_(X x) w + T_w (X x)`. -/
theorem leviCivitaConnection_horizontalLift_of_mem_ker
    (hB : CMDiffAt 1 (T% B) (f x)) {w : TangentSpace I x}
    (hw : w ∈ (mfderiv I J f x).ker) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x w =
      h.oneillA x (h.horizontalLift x (B (f x))) w +
        h.oneillT x w (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  rw [← starProjection_orthogonal_ker_add_starProjection_ker I J f
      (CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x w),
    h.starProjection_orthogonal_ker_leviCivitaConnection_horizontalLift_of_mem_ker hB hw,
    h.oneillT_apply_of_eventually_mem_orthogonal_ker hXd
      (.of_forall fun y ↦ h.horizontalLift_mem_orthogonal_ker y _) w,
    Submodule.starProjection_eq_self_iff.mpr hw]

/-- **O'Neill's full connection formula on basic horizontal fields.** For any tangent vector `u`,
the Levi-Civita derivative of `X y = h.horizontalLift y (B (f y))` along `u` decomposes into the
lifted base derivative along `df u` together with the three `A` and `T` terms. -/
theorem leviCivitaConnection_horizontalLift (hB : CMDiffAt 1 (T% B) (f x))
    (u : TangentSpace I x) :
    CovariantDerivative.leviCivitaConnection I M (fun y ↦ h.horizontalLift y (B (f y))) x u =
      h.horizontalLift x
          (CovariantDerivative.leviCivitaConnection J N B (f x) (mfderiv I J f x u)) +
        h.oneillA x u (h.horizontalLift x (B (f x))) +
        h.oneillA x (h.horizontalLift x (B (f x))) ((mfderiv I J f x).ker.starProjection u) +
        h.oneillT x u (h.horizontalLift x (B (f x))) := by
  have huh : (mfderiv I J f x).kerᗮ.starProjection u ∈ (mfderiv I J f x).kerᗮ :=
    Submodule.starProjection_apply_mem _ _
  have huv : (mfderiv I J f x).ker.starProjection u ∈ (mfderiv I J f x).ker :=
    Submodule.starProjection_apply_mem _ _
  have huv0 : mfderiv I J f x ((mfderiv I J f x).ker.starProjection u) = 0 :=
    LinearMap.mem_ker.mp huv
  have hdf : mfderiv I J f x ((mfderiv I J f x).kerᗮ.starProjection u) = mfderiv I J f x u := by
    have := congrArg (mfderiv I J f x)
      (starProjection_orthogonal_ker_add_starProjection_ker I J f u)
    rwa [map_add, huv0, add_zero] at this
  conv_lhs => rw [← starProjection_orthogonal_ker_add_starProjection_ker I J f u]
  rw [map_add,
    h.leviCivitaConnection_horizontalLift_of_mem_orthogonal_ker hB huh,
    h.leviCivitaConnection_horizontalLift_of_mem_ker hB huv,
    hdf, h.oneillA_starProjection_orthogonal_ker, h.oneillT_starProjection_ker]
  abel

/-- The Lie bracket of a basic horizontal field `X` with a field `V` which is vertical near `x` is
vertical and equals `v (∇_(X x) V) - T_(V x) (X x)`. -/
theorem mlieBracket_horizontalLift_of_eventually_mem_ker (hB : CMDiffAt 1 (T% B) (f x))
    {V : Π y : M, TangentSpace I y} (hVd : MDiffAt (T% V) x)
    (hVv : ∀ᶠ y in 𝓝 x, V y ∈ (mfderiv I J f y).ker) :
    mlieBracket I (fun y ↦ h.horizontalLift y (B (f y))) V x =
      (mfderiv I J f x).ker.starProjection
          (CovariantDerivative.leviCivitaConnection I M V x (h.horizontalLift x (B (f x)))) -
        h.oneillT x (V x) (h.horizontalLift x (B (f x))) := by
  have hXd : MDiffAt (T% (fun y ↦ h.horizontalLift y (B (f y)))) x :=
    h.mdifferentiableAt_horizontalLift_of_contMDiffAt_one hB
  have htor := ((CovariantDerivative.torsion_eq_zero_iff _).mp
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hXd hVd
  have hAV := h.oneillA_apply_of_eventually_mem_ker hVd hVv (h.horizontalLift x (B (f x)))
  rw [Submodule.starProjection_eq_self_iff.mpr (h.horizontalLift_mem_orthogonal_ker x _)] at hAV
  have hdecompV := (starProjection_orthogonal_ker_add_starProjection_ker I J f
    (CovariantDerivative.leviCivitaConnection I M V x (h.horizontalLift x (B (f x))))).symm
  rw [← hAV] at hdecompV
  have hVX := h.leviCivitaConnection_horizontalLift_of_mem_ker hB hVv.self_of_nhds
  conv_lhs => rw [← htor, hdecompV, hVX]
  abel

end BasicFields

end TauCeti.IsRiemannianSubmersion

section Product

open Bundle Manifold
open scoped ContDiff Manifold TauCeti

namespace TauCeti

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

private theorem starProjection_orthogonal_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm ((Manifold.tangentSpaceProdEquiv p v).1, 0) := by
  rw [← (isRiemannianSubmersion_fst (I := I) (J := J)).horizontalLift_mfderiv, horizontalLift_fst]
  congr 1
  simp only [mfderiv_fst, Manifold.tangentSpaceProdEquiv_apply]
  rfl

private theorem starProjection_ker_fst (p : M × N) (v : TangentSpace (I.prod J) p) :
    (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection v =
      (Manifold.tangentSpaceProdEquiv p).symm (0, (Manifold.tangentSpaceProdEquiv p v).2) := by
  have hv : (mfderiv (I.prod J) I (@Prod.fst M N) p).ker.starProjection v =
      v - (mfderiv (I.prod J) I (@Prod.fst M N) p).kerᗮ.starProjection v := by
    simp [Submodule.starProjection_orthogonal]
  rw [hv, starProjection_orthogonal_ker_fst]
  apply (Manifold.tangentSpaceProdEquiv p).injective
  rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rcases Manifold.tangentSpaceProdEquiv p v with ⟨v₁, v₂⟩
  simp

private theorem prodVectorField_extend_projections (p : M × N) (v : TangentSpace (I.prod J) p) :
    let Y₁ := FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1
    let Y₂ := FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2
    Manifold.prodVectorField Y₁ Y₂ p = v ∧
      (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).kerᗮ.starProjection
        (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField Y₁ 0 ∧
      (fun q ↦ (mfderiv (I.prod J) I (@Prod.fst M N) q).ker.starProjection
        (Manifold.prodVectorField Y₁ Y₂ q)) = Manifold.prodVectorField 0 Y₂ := by
  refine ⟨?_, funext fun q ↦ ?_, funext fun q ↦ ?_⟩
  · apply (Manifold.tangentSpaceProdEquiv p).injective
    rw [Manifold.tangentSpaceProdEquiv_prodVectorField, FiberBundle.extend_apply_self,
      FiberBundle.extend_apply_self, Prod.mk.eta]
  · rw [starProjection_orthogonal_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]
  · rw [starProjection_ker_fst]
    apply (Manifold.tangentSpaceProdEquiv q).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, Manifold.tangentSpaceProdEquiv_prodVectorField,
      Manifold.tangentSpaceProdEquiv_prodVectorField, Pi.zero_apply]

variable
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J ∞ F (fun y : N ↦ TangentSpace J y)]

/-- O'Neill's horizontal tensor `A` vanishes identically for the first projection of a Riemannian
product. -/
@[simp]
theorem oneillA_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillA p = 0 := by
  ext u v
  have ⟨hYp, hH, hV⟩ := prodVectorField_extend_projections p v
  have hY₁ : MDiffAt (T% (FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1)) p.1 :=
    FiberBundle.mdifferentiableAt_extend I E _
  have hY₂ : MDiffAt (T% (FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2)) p.2 :=
    FiberBundle.mdifferentiableAt_extend J F _
  have h0M : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace I)
  have h0N : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace J)
  conv_lhs => rw [← hYp]
  rw [(isRiemannianSubmersion_fst (I := I) (J := J)).oneillA_apply
      (Manifold.mdifferentiableAt_prodVectorField hY₁ hY₂) u,
    hH, hV, starProjection_ker_fst, starProjection_orthogonal_ker_fst,
    starProjection_orthogonal_ker_fst]
  apply (Manifold.tangentSpaceProdEquiv p).injective
  simp only [zero_apply, map_add, map_zero, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0N,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0M hY₂,
    (CovariantDerivative.leviCivitaConnection I M).zero,
    (CovariantDerivative.leviCivitaConnection J N).zero, Pi.zero_apply]
  ext <;> simp

/-- O'Neill's vertical tensor `T` vanishes identically for the first projection of a Riemannian
product. -/
@[simp]
theorem oneillT_fst (p : M × N) :
    (isRiemannianSubmersion_fst (I := I) (J := J)).oneillT p = 0 := by
  ext u v
  have ⟨hYp, hH, hV⟩ := prodVectorField_extend_projections p v
  have hY₁ : MDiffAt (T% (FiberBundle.extend E (Manifold.tangentSpaceProdEquiv p v).1)) p.1 :=
    FiberBundle.mdifferentiableAt_extend I E _
  have hY₂ : MDiffAt (T% (FiberBundle.extend F (Manifold.tangentSpaceProdEquiv p v).2)) p.2 :=
    FiberBundle.mdifferentiableAt_extend J F _
  have h0M : MDiffAt (T% (0 : Π x : M, TangentSpace I x)) p.1 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace I)
  have h0N : MDiffAt (T% (0 : Π y : N, TangentSpace J y)) p.2 :=
    mdifferentiableAt_zeroSection ℝ (TangentSpace J)
  conv_lhs => rw [← hYp]
  rw [(isRiemannianSubmersion_fst (I := I) (J := J)).oneillT_apply
      (Manifold.mdifferentiableAt_prodVectorField hY₁ hY₂) u,
    hH, hV, starProjection_orthogonal_ker_fst, starProjection_ker_fst, starProjection_ker_fst]
  apply (Manifold.tangentSpaceProdEquiv p).injective
  simp only [zero_apply, map_add, map_zero, ContinuousLinearEquiv.apply_symm_apply,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ h0N,
    Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField h0M hY₂,
    (CovariantDerivative.leviCivitaConnection I M).zero,
    (CovariantDerivative.leviCivitaConnection J N).zero, Pi.zero_apply]
  ext <;> simp

end TauCeti

end Product
