/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Correspondence
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Mixed
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Generating families on manifolds

Let `M` and `N` be manifolds and `A` a normed space of *auxiliary variables*. A real function
`S((q, Q), a)` on `(M × N) × A` is a **generating family** of a cotangent relation between `T*M`
and `T*N`. For each fixed `a` the function `S(·, a)` on `M × N` generates the relation

`p = d_q S((q, Q), a)`, `P = -d_Q S((q, Q), a)`

(`TauCeti.CotangentBundle.generatingCorrespondence`), and the family relation is the union of
these relations over the points where `S` is stationary in `a`. Its parametrization is

`G : ((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S)) ∈ T*M × T*N`

(`TauCeti.CotangentBundle.familyCorrespondence`), restricted to the *fibre-critical set*
`Σ_S = {z | ∂_a S z = 0}` of the *fibre derivative* `∂_a S`
(`TauCeti.CotangentBundle.familyFiberDeriv`).

When `S` is smooth and the derivative of `∂_a S` is surjective at every point of `Σ_S`, the family
is *transverse* and `Σ_S` is a regular level of `∂_a S`. With the atlas of
`TauCeti.regularLevelChartedSpace` (`TauCeti.CotangentBundle.familyCriticalSetChartedSpace`) it is
then a smooth manifold of dimension `dim M + dim N`
(`TauCeti.CotangentBundle.isManifold_familyCriticalSet`), and this file proves that `G` restricted
to `Σ_S` is a Lagrangian correspondence in the immersed sense, for the twisted product
`pr₁^*ω_M - pr₂^*ω_N`:

* **Exactness.** `G` pulls the primitive `pr₁^*λ_M - pr₂^*λ_N` of the twisted product back to
  `dS - ∂_a S(da)` (`TauCeti.CotangentBundle.mpullback_familyCorrespondence_liouvilleForm_apply`),
  so along `Σ_S` it pulls it back to the differential of the restriction of `S`
  (`TauCeti.CotangentBundle.mpullback_familyCorrespondence_comp_coe_liouvilleForm`).
* **Injectivity.** At a transverse point, the differential of `G` is injective on the kernel of
  the differential of `∂_a S` (`TauCeti.CotangentBundle.injOn_mfderiv_familyCorrespondence_ker`).
  A vector `(v, b)` killed by `dG` has `v = 0`, since `G` lies over `(q, Q)`; then the covectors
  `d_q S` and `d_Q S` do not move in the direction `b`, and by the symmetry of mixed derivatives
  (`TauCeti.Manifold.fderiv_mvfderiv_apply`) neither does `∂_a S(·)(b)` in any direction of
  `M × N`. Together with `(0, b) ∈ ker d(∂_a S)` and the symmetry of the second derivative in `a`,
  every covector in the range of `d(∂_a S)` vanishes on `b`, so `b = 0` by surjectivity.
* Hence `G ∘ Subtype.val` is an exact Lagrangian map with primitive the restriction of `S`
  (`TauCeti.CotangentBundle.isExactLagrangianMap_familyCorrespondence_comp_coe`) and a Lagrangian
  immersion (`TauCeti.CotangentBundle.isLagrangianImmersion_familyCorrespondence_comp_coe`): an
  immersed Lagrangian correspondence `T*M ⇝ T*N`.

This is the manifold counterpart of the generating families on normed spaces of
`TauCeti.Geometry.Symplectic.Cotangent.GeneratingFunction.Family.Basic`, stated for
correspondences as `TauCeti.CotangentBundle.generatingCorrespondence` is for a single generating
function. The image of `G` on `Σ_S` need not be embedded: distinct critical points may have the
same image. The auxiliary variables range over a normed space, as for the phase functions of
Hörmander; no compactness is assumed.

## References

* L. Hörmander, *Fourier integral operators. I*, Acta Math. 127 (1971), 79–183, Section 3.1, for
  the Lagrangian defined by a nondegenerate phase function.
* A. Weinstein, *Lectures on Symplectic Manifolds*, CBMS Regional Conference Series in
  Mathematics 29, AMS, 1977, for generating families (Morse families).
-/

public section

noncomputable section

open Bundle Function Manifold Module
open scoped Manifold ContDiff Topology

namespace TauCeti.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F H' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] {S : (M × N) × A → ℝ}

/-! ### The fibre derivative and the family relation -/

/-- The **fibre derivative** `∂_a S(x, a)` of a family `S : X × A → ℝ` of functions on `X`
parametrized by a normed space `A` of auxiliary variables: the derivative of `a ↦ S(x, a)`. -/
def familyFiberDeriv {X : Type*} (S : X × A → ℝ) (z : X × A) : StrongDual ℝ A :=
  fderiv ℝ (fun a ↦ S (z.1, a)) z.2

/-- The fibre derivative evaluated on a vector `b` of auxiliary variables. -/
theorem familyFiberDeriv_apply {X : Type*} (S : X × A → ℝ) (z : X × A) (b : A) :
    familyFiberDeriv S z b = fderiv ℝ (fun a ↦ S (z.1, a)) z.2 b :=
  (rfl)

variable (I J) in
/-- The **cotangent relation generated by a family** `S((q, Q), a)` on `(M × N) × A`, parametrized
by `((q, Q), a)` as `((q, d_q S), (Q, -d_Q S)) ∈ T*M × T*N`: at a parameter `a` it is the
relation generated by `S(·, a)`. Restricted to the points where `S` is stationary in `a`, it is a
Lagrangian immersion for a smooth transverse family
(`TauCeti.CotangentBundle.isLagrangianImmersion_familyCorrespondence_comp_coe`). -/
def familyCorrespondence (S : (M × N) × A → ℝ) (z : (M × N) × A) :
    CotangentBundle I M × CotangentBundle J N :=
  generatingCorrespondence I J (fun x ↦ S (x, z.2)) z.1

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- At a parameter `a`, the family relation is the relation generated by `S(·, a)`. -/
@[simp]
theorem familyCorrespondence_apply (x : M × N) (a : A) :
    familyCorrespondence I J S (x, a) = generatingCorrespondence I J (fun x' ↦ S (x', a)) x :=
  (rfl)

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- The family relation lies over the pair of base points. -/
@[simp]
theorem map_proj_familyCorrespondence (z : (M × N) × A) :
    Prod.map TotalSpace.proj TotalSpace.proj (familyCorrespondence I J S z) = z.1 := by
  simp [familyCorrespondence]

omit [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace N] in
/-- The source projection of a generated relation, as a covector at the first base point. -/
private theorem generatingSource_eq_mk {T : M × N → ℝ} (x : M × N) :
    generatingSource I T x =
      TotalSpace.mk' (E →L[ℝ] ℝ) x.1 (mvfderiv I (fun q ↦ T (q, x.2)) x.1) :=
  CotangentBundle.ext (proj_generatingSource x) fun v ↦
    DFunLike.congr_fun (generatingSource_snd x) v

omit [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace M] in
/-- The target projection of a generated relation, as a covector at the second base point. -/
private theorem generatingTarget_eq_mk {T : M × N → ℝ} (x : M × N) :
    generatingTarget J T x =
      TotalSpace.mk' (F →L[ℝ] ℝ) x.2 (-mvfderiv J (fun Q ↦ T (x.1, Q)) x.2) :=
  CotangentBundle.ext (proj_generatingTarget x) fun v ↦
    DFunLike.congr_fun (generatingTarget_snd x) v

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
/-- The family relation at `z`, written out: the covectors `d_q S` at `q` and `-d_Q S` at `Q`. -/
theorem familyCorrespondence_eq_mk (z : (M × N) × A) :
    familyCorrespondence I J S z =
      (TotalSpace.mk' (E →L[ℝ] ℝ) z.1.1 (mvfderiv I (fun q ↦ S ((q, z.1.2), z.2)) z.1.1),
        TotalSpace.mk' (F →L[ℝ] ℝ) z.1.2 (-mvfderiv J (fun Q ↦ S ((z.1.1, Q), z.2)) z.1.2)) := by
  simp only [familyCorrespondence, generatingCorrespondence_apply, generatingSource_eq_mk,
    generatingTarget_eq_mk]

/-! ### Smoothness -/

section Smooth

variable [IsManifold I 2 M] [IsManifold J 2 N]

/-- The source component `((q, Q), a) ↦ (q, d_q S)` of the family relation of a smooth family is
smooth. -/
theorem contMDiff_familyCorrespondence_fst
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun z ↦ (familyCorrespondence I J S z).1) := by
  -- Reassociated, this is the source projection of the relation generated by `S` on
  -- `M × (N × A)`.
  refine ((contMDiff_generatingSource (I := I) (J := J.prod 𝓘(ℝ, A))
    (S := fun p : M × (N × A) ↦ S ((p.1, p.2.1), p.2.2))
    (hS.comp ((contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd)).prodMk
      (contMDiff_snd.comp contMDiff_snd)))).comp ((contMDiff_fst.comp contMDiff_fst).prodMk
        ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd))).congr fun z ↦ ?_
  simp only [familyCorrespondence, generatingCorrespondence_apply, comp_apply,
    generatingSource_eq_mk]

/-- The target component `((q, Q), a) ↦ (Q, -d_Q S)` of the family relation of a smooth family is
smooth. -/
theorem contMDiff_familyCorrespondence_snd
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞
      (fun z ↦ (familyCorrespondence I J S z).2) := by
  -- Reassociated, this is the target projection of the relation generated by `S` on
  -- `(M × A) × N`.
  refine ((contMDiff_generatingTarget (I := I.prod 𝓘(ℝ, A)) (J := J)
    (S := fun p : (M × A) × N ↦ S ((p.1.1, p.2), p.1.2))
    (hS.comp (((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)))).comp (((contMDiff_fst.comp contMDiff_fst).prodMk
        contMDiff_snd).prodMk (contMDiff_snd.comp contMDiff_fst))).congr fun z ↦ ?_
  simp only [familyCorrespondence, generatingCorrespondence_apply, comp_apply,
    generatingTarget_eq_mk]

/-- The family relation of a smooth family is smooth. -/
theorem contMDiff_familyCorrespondence (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A))
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))) ∞
      (familyCorrespondence I J S) :=
  (contMDiff_familyCorrespondence_fst hS).prodMk (contMDiff_familyCorrespondence_snd hS)

/-- The fibre derivative of a smooth family is smooth. -/
theorem contMDiff_familyFiberDeriv (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) :
    ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) ∞ (familyFiberDeriv S) :=
  fun z ↦ ContMDiffAt.fderiv_right (g := fun x a ↦ S (x, a)) (hS z) le_rfl

end Smooth

/-! ### Exactness -/

section Differential

variable [IsManifold I ∞ M] [IsManifold J ∞ N]

/-- The Liouville primitive `pr₁^*λ_M - pr₂^*λ_N` of `T*M × T*N`, pulled back along a pair of smooth
maps `ψ₁, ψ₂` into the two cotangent bundles, pairs a tangent vector `v` with the covectors of
`ψ₁` and `ψ₂` on the derivatives of their base points. -/
private theorem mpullback_prodMk_liouvilleForm_apply
    {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {K : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X] [IsManifold K 1 X]
    {ψ₁ : X → CotangentBundle I M} {ψ₂ : X → CotangentBundle J N} {g₁ : X → M} {g₂ : X → N}
    (h₁ : ContMDiff K (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ ψ₁)
    (h₂ : ContMDiff K (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ ψ₂) (hg₁ : ∀ x, (ψ₁ x).proj = g₁ x)
    (hg₂ : ∀ x, (ψ₂ x).proj = g₂ x) (x : X) (v : Fin 1 → TangentSpace K x) :
    mpullback (F := ℝ) (k := 1) K ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (fun x ↦ (ψ₁ x, ψ₂ x))
        (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm I M) -
          SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm J N)).1 x v =
      (ψ₁ x).2 (mfderiv K I g₁ x (v 0)) - (ψ₂ x).2 (mfderiv K J g₂ x (v 0)) := by
  rw [← SmoothForm.coe_mpullback _ (h₁.prodMk h₂), map_sub, SmoothForm.mpullback_mpullback,
    SmoothForm.mpullback_mpullback, Submodule.coe_sub, Pi.sub_apply,
    ContinuousAlternatingMap.sub_apply, SmoothForm.coe_mpullback, SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq (ψ := Prod.fst ∘ fun x ↦ (ψ₁ x, ψ₂ x)) hg₁
      ((h₁ x).mdifferentiableAt (by simp)),
    mpullback_liouvilleForm_apply_of_proj_comp_eq (ψ := Prod.snd ∘ fun x ↦ (ψ₁ x, ψ₂ x)) hg₂
      ((h₂ x).mdifferentiableAt (by simp))]
  rfl

/-- **The family relation pulls the Liouville primitive back to `dS - ∂_a S (da)`.** At every
point `z = (x, a)`, the pullback of the one-form `pr₁^*λ_M - pr₂^*λ_N` on `T*M × T*N` along the
family relation takes the value `dS(u) - ∂_a S(z)(u.2)` on a tangent vector `u = (u.1, u.2)`. -/
theorem mpullback_familyCorrespondence_liouvilleForm_apply
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) (z : (M × N) × A)
    (v : Fin 1 → TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) :
    mpullback (F := ℝ) (k := 1) ((I.prod J).prod 𝓘(ℝ, A))
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S)
        (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm I M) -
          SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm J N)).1 z v =
      mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) S z (v 0) - familyFiberDeriv S z (v 0).2 := by
  have hq : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) I (fun z : (M × N) × A ↦ z.1.1) z (v 0) =
      ((v 0).1.1 : E) :=
    DFunLike.congr_fun ((hasMFDerivAt_fst (I := I) (I' := J) z.1).comp z
      (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)).mfderiv (v 0)
  have hQ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) J (fun z : (M × N) × A ↦ z.1.2) z (v 0) =
      ((v 0).1.2 : F) :=
    DFunLike.congr_fun ((hasMFDerivAt_snd (I := I) (I' := J) z.1).comp z
      (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)).mfderiv (v 0)
  have hSz : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) S z :=
    (hS z).mdifferentiableAt (by simp)
  have hSx : MDifferentiableAt (I.prod J) 𝓘(ℝ) (fun x ↦ S (x, z.2)) z.1 :=
    ((hS.comp (contMDiff_id.prodMk contMDiff_const)) z.1).mdifferentiableAt (by simp)
  rw [mpullback_prodMk_liouvilleForm_apply (contMDiff_familyCorrespondence_fst hS)
      (contMDiff_familyCorrespondence_snd hS) (g₁ := fun z ↦ z.1.1) (g₂ := fun z ↦ z.1.2)
      (fun _ ↦ by simp [familyCorrespondence]) (fun _ ↦ by simp [familyCorrespondence]) z v,
    hq, hQ, familyCorrespondence_eq_mk]
  -- The two covectors of `G` are the partial differentials of `S(·, a)`, and `dS` is their sum
  -- plus the fibre derivative.
  have h₁ := hSz.mvfderiv_prod_eq_add_apply (v 0)
  have h₂ := hSx.mvfderiv_prod_eq_add_apply (v 0).1
  have h₃ : mvfderiv 𝓘(ℝ, A) (fun a ↦ S (z.1, a)) z.2 (v 0).2 = familyFiberDeriv S z (v 0).2 :=
    mvfderiv_eq_fderiv_apply _ _ _
  have h₄ : (-mvfderiv J (fun Q ↦ S ((z.1.1, Q), z.2)) z.1.2) (v 0).1.2 =
      -mvfderiv J (fun Q ↦ S ((z.1.1, Q), z.2)) z.1.2 (v 0).1.2 :=
    rfl
  simp only at h₂ ⊢
  linear_combination -h₁ - h₂ - h₃ - h₄

/-! ### Injectivity at a transverse point -/

omit [IsManifold J ∞ N] in
/-- A curve `γ` in `T*M` through covectors `c a` at a fixed point `q` moves only in its covector:
if `γ` has zero derivative in a direction `b`, so does `c`. -/
private theorem fderiv_eq_zero_of_mfderiv_eq_zero {q : M} {γ : A → CotangentBundle I M}
    {c : A → E →L[ℝ] ℝ} (hγ : ∀ a, γ a = TotalSpace.mk' (E →L[ℝ] ℝ) q (c a)) {a b : A}
    (hd : MDifferentiableAt 𝓘(ℝ, A) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) γ a)
    (h : mfderiv 𝓘(ℝ, A) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) γ a b = 0) :
    DifferentiableAt ℝ c a ∧ fderiv ℝ c a b = 0 := by
  -- The fibre coordinate in the trivialization at `q` recovers `c`.
  set Ψ : CotangentBundle I M → E →L[ℝ] ℝ := fun p ↦
    (trivializationAt (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) q p).2
  have hΨ : MDifferentiableAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ, E →L[ℝ] ℝ) Ψ (γ a) := by
    rw [hγ]
    exact (Bundle.TotalSpace.contMDiffAt_trivializationAt_snd (n := 1)
      (TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) q (c a))
      ).mdifferentiableAt one_ne_zero
  have hc : c = Ψ ∘ γ := by
    funext a'
    rw [comp_apply, hγ]
    exact ((continuousLinearMapAt_trivializationAt_self q (c a')).symm.trans
      ((trivializationAt (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) q
        ).continuousLinearMapAt_apply_of_mem ℝ
          (FiberBundle.mem_baseSet_trivializationAt _ _ q) (c a')))
  have hH := hΨ.hasMFDerivAt.comp a hd.hasMFDerivAt
  rw [← hc] at hH
  refine ⟨hH.hasFDerivAt.differentiableAt, ?_⟩
  have h0 : mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E →L[ℝ] ℝ) c a b = 0 := by
    rw [hH.mfderiv]
    exact (congrArg (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ, E →L[ℝ] ℝ) Ψ _) h).trans (map_zero _)
  rw [mfderiv_eq_fderiv] at h0
  -- The identifications of the tangent spaces of normed spaces with the spaces are identities.
  exact h0

/-- The family relation lies over the pair of base points, so the derivatives of its two components
determine the `M × N` component of a tangent vector. -/
private theorem fst_eq_zero_of_mfderiv_familyCorrespondence_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    {u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z}
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z u = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z u = 0) :
    (u.1 : E × F) = 0 := by
  have hπ₁ := mfderiv_comp_apply z
    ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
      (familyCorrespondence I J S z).1).mdifferentiableAt (n := 1) one_ne_zero)
    ((contMDiff_familyCorrespondence_fst hS z).mdifferentiableAt (by simp)) u
  have hπ₂ := mfderiv_comp_apply z
    ((Bundle.contMDiff_proj (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ)
      (familyCorrespondence I J S z).2).mdifferentiableAt (n := 1) one_ne_zero)
    ((contMDiff_familyCorrespondence_snd hS z).mdifferentiableAt (by simp)) u
  rw [h₁, map_zero] at hπ₁
  rw [h₂, map_zero] at hπ₂
  -- The base points of the two components are `q` and `Q`.
  rw [show (π (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∘
      fun z ↦ (familyCorrespondence I J S z).1) = Prod.fst ∘ Prod.fst from
    funext fun _ ↦ by simp [familyCorrespondence],
    ((hasMFDerivAt_fst (I := I) (I' := J) z.1).comp z
      (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)).mfderiv] at hπ₁
  rw [show (π (F →L[ℝ] ℝ) (fun y : N ↦ TangentSpace J y →L[ℝ] ℝ) ∘
      fun z ↦ (familyCorrespondence I J S z).2) = Prod.snd ∘ Prod.fst from
    funext fun _ ↦ by simp [familyCorrespondence],
    ((hasMFDerivAt_snd (I := I) (I' := J) z.1).comp z
      (hasMFDerivAt_fst (I := I.prod J) (I' := 𝓘(ℝ, A)) z)).mfderiv] at hπ₂
  exact Prod.ext hπ₁ hπ₂

/-- If neither covector of the family relation moves in the direction `(0, b)`, then the fibre
derivative `∂_a S(·)(b)` does not move on `M × N` either: by the symmetry of mixed derivatives its
differential is the derivative of `d_x S` in the direction `b`. -/
private theorem mvfderiv_familyFiberDeriv_apply_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A} {b : A}
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z ((0, b) : (E × F) × A) = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z ((0, b) : (E × F) × A) = 0) (w : E × F) :
    mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) b) z.1 w = 0 := by
  have hι : MDifferentiableAt 𝓘(ℝ, A) ((I.prod J).prod 𝓘(ℝ, A)) (fun a ↦ (z.1, a)) z.2 :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  -- Along the curve `a ↦ (z.1, a)` the components of `G` are the covectors `d_q S` and `-d_Q S`
  -- at the fixed points `q` and `Q`, so these do not move in the direction `b`.
  have hG₁ : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) (z.1, z.2) :=
    (contMDiff_familyCorrespondence_fst hS _).mdifferentiableAt (by simp)
  have hG₂ : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) (z.1, z.2) :=
    (contMDiff_familyCorrespondence_snd hS _).mdifferentiableAt (by simp)
  set c₁ : A → E →L[ℝ] ℝ := fun a ↦ mvfderiv I (fun q ↦ S ((q, z.1.2), a)) z.1.1
  set c₂ : A → F →L[ℝ] ℝ := fun a ↦ -mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2
  obtain ⟨hd₁, hc₁⟩ := fderiv_eq_zero_of_mfderiv_eq_zero
    (γ := (fun z ↦ (familyCorrespondence I J S z).1) ∘ fun a ↦ (z.1, a))
    (q := z.1.1) (c := c₁) (b := b)
    (fun a ↦ by simp [c₁, familyCorrespondence_eq_mk]) (hG₁.comp z.2 hι)
    ((mfderiv_comp_apply z.2 hG₁ hι b).trans (by rw [mfderiv_prod_right]; exact h₁))
  obtain ⟨hd₂, hc₂⟩ := fderiv_eq_zero_of_mfderiv_eq_zero (I := J)
    (γ := (fun z ↦ (familyCorrespondence I J S z).2) ∘ fun a ↦ (z.1, a))
    (q := z.1.2) (c := c₂) (b := b)
    (fun a ↦ by simp [c₂, familyCorrespondence_eq_mk]) (hG₂.comp z.2 hι)
    ((mfderiv_comp_apply z.2 hG₂ hι b).trans (by rw [mfderiv_prod_right]; exact h₂))
  -- The differential of `S(·, a)` at `x` is the sum of the two covectors.
  have hfun : (fun a ↦ mvfderiv (I.prod J) (fun x ↦ S (x, a)) z.1 w) =
      fun a ↦ c₁ a w.1 - c₂ a w.2 := by
    funext a
    have hSa : MDifferentiableAt (I.prod J) 𝓘(ℝ) (fun x ↦ S (x, a)) z.1 :=
      ((hS.comp (contMDiff_id.prodMk contMDiff_const)) z.1).mdifferentiableAt (by simp)
    have h := hSa.mvfderiv_prod_eq_add_apply w
    have hneg : c₂ a w.2 = -mvfderiv J (fun Q ↦ S ((z.1.1, Q), a)) z.1.2 w.2 := rfl
    linear_combination h + hneg
  have hD := (hd₁.hasFDerivAt.clm_apply (hasFDerivAt_const w.1 z.2)).sub
    (hd₂.hasFDerivAt.clm_apply (hasFDerivAt_const w.2 z.2))
  have hmix := TauCeti.Manifold.fderiv_mvfderiv_apply (F := fun a x ↦ S (x, a)) (a := z.2)
    (x := z.1) (((hS.comp (contMDiff_snd.prodMk contMDiff_fst)) _).of_le (by simp)) w b
  simp only [familyFiberDeriv_apply]
  rw [← hmix, hfun, show (fun a ↦ c₁ a w.1 - c₂ a w.2) = (fun a ↦ c₁ a w.1) - fun a ↦ c₂ a w.2
    from rfl, hD.fderiv]
  simp [hc₁, hc₂]

/-- The differential of the fibre derivative, evaluated on `b`: its `M × N` part is the
differential of `∂_a S(·)(b)` and its `A` part is the second derivative of `S(x, ·)`. -/
private theorem mfderiv_familyFiberDeriv_apply_apply
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) (z : (M × N) × A)
    (u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) (b : A) :
    mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z u b =
      mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) b) z.1 u.1 +
        fderiv ℝ (fderiv ℝ fun a ↦ S (z.1, a)) z.2 u.2 b := by
  have hD : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A)
      (familyFiberDeriv S) z :=
    (contMDiff_familyFiberDeriv hS z).mdifferentiableAt (by simp)
  have hb : MDifferentiableAt ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ)
      (fun z' ↦ familyFiberDeriv S z' b) z :=
    (ContinuousLinearMap.apply ℝ ℝ b).mdifferentiableAt.comp z hD
  have hSx : ContDiff ℝ ∞ fun a ↦ S (z.1, a) :=
    contMDiff_iff_contDiff.mp (hS.comp (contMDiff_const.prodMk contMDiff_id))
  have hA : HasFDerivAt (fun a ↦ fderiv ℝ (fun a ↦ S (z.1, a)) a b)
      ((fderiv ℝ (fderiv ℝ fun a ↦ S (z.1, a)) z.2).flip b) z.2 := by
    simpa using ((hSx.fderiv_right (m := 1) (by simp)).differentiable (by simp)
      z.2).hasFDerivAt.clm_apply (hasFDerivAt_const b z.2)
  rw [← ContinuousLinearMap.apply_apply b,
    ← (ContinuousLinearMap.apply ℝ ℝ b).mvfderiv_comp_apply hD u]
  rw [show (ContinuousLinearMap.apply ℝ ℝ b ∘ familyFiberDeriv S) =
    fun z' ↦ familyFiberDeriv S z' b from rfl, hb.mvfderiv_prod_eq_add_apply u]
  -- In the `A` direction, `∂_a S(x, ·)(b)` is the derivative of `a ↦ dS(x, ·)_a (b)`.
  exact congrArg (_ + ·) ((mvfderiv_eq_fderiv_apply _ _ _).trans
    (DFunLike.congr_fun hA.fderiv u.2))

/-- At a transverse point, a tangent vector in the kernel of the differential of the fibre
derivative which both components of the differential of the family relation kill is zero. -/
private theorem eq_zero_of_mfderiv_familyCorrespondence_eq_zero
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    (hsurj : Surjective
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z))
    {u : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z}
    (hu : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z u = 0)
    (h₁ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).1) z u = 0)
    (h₂ : mfderiv ((I.prod J).prod 𝓘(ℝ, A)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ))
      (fun z ↦ (familyCorrespondence I J S z).2) z u = 0) : u = 0 := by
  have hu₁ := fst_eq_zero_of_mfderiv_familyCorrespondence_eq_zero hS h₁ h₂
  obtain ⟨b, rfl⟩ : ∃ b : A, u = ((0, b) : (E × F) × A) := ⟨u.2, Prod.ext hu₁ rfl⟩
  -- The fibre derivative `∂_a S(·)(b)` does not move on `M × N`.
  have hmix := mvfderiv_familyFiberDeriv_apply_eq_zero hS h₁ h₂
  have hsymm : IsSymmSndFDerivAt ℝ (fun a ↦ S (z.1, a)) z.2 :=
    (contMDiff_iff_contDiff.mp (hS.comp (contMDiff_const.prodMk contMDiff_id))).contDiffAt
      |>.isSymmSndFDerivAt (by simp)
  -- Hence every covector in the range of `d(∂_a S)` vanishes on `b`: its value is the second
  -- derivative of `S(x, ·)` at `(·, b)`, which is symmetric and vanishes since `(0, b)` lies in
  -- the kernel.
  have hD (w : TangentSpace ((I.prod J).prod 𝓘(ℝ, A)) z) :
      mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z w b = 0 := by
    have h₀ := mfderiv_familyFiberDeriv_apply_apply hS z ((0, b) : (E × F) × A) w.2
    have hw := mfderiv_familyFiberDeriv_apply_apply hS z w b
    have hz : mvfderiv (I.prod J) (fun x ↦ familyFiberDeriv S (x, z.2) w.2) z.1 (0 : E × F) = 0 :=
      map_zero _
    have hb : mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z
        ((0, b) : (E × F) × A) w.2 = 0 := by
      have hu' : mvfderiv ((I.prod J).prod 𝓘(ℝ, A)) (familyFiberDeriv S) z
          ((0, b) : (E × F) × A) = (0 : StrongDual ℝ A) :=
        (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans hu
      exact (congrArg (fun φ : StrongDual ℝ A ↦ φ w.2) hu').trans (by simp)
    linear_combination hw + hmix w.1 - hsymm b w.2 - h₀ + hb - hz
  refine Prod.ext rfl (SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun β ↦ ?_)
  obtain ⟨w, rfl⟩ := hsurj β
  rw [← mvfderiv_apply_eq_mfderiv_apply]
  exact hD w

/-- **Injectivity at a transverse point.** If the differential of the fibre derivative `∂_a S` of a
smooth family is surjective at `z`, the differential of the family relation is injective on its
kernel. -/
theorem injOn_mfderiv_familyCorrespondence_ker
    (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S) {z : (M × N) × A}
    (hsurj : Surjective
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z)) :
    Set.InjOn
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A))
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S) z)
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z).ker := by
  have hprod := mfderiv_prodMk
    ((contMDiff_familyCorrespondence_fst hS z).mdifferentiableAt (by simp))
    ((contMDiff_familyCorrespondence_snd hS z).mdifferentiableAt (by simp))
  intro u hu u' hu' h
  rw [← sub_eq_zero]
  have h' := Prod.mk.inj (hprod ▸ h)
  simp only [ContinuousLinearMap.coe_coe] at h'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hu hu'
  refine eq_zero_of_mfderiv_familyCorrespondence_eq_zero hS hsurj ?_ ?_ ?_
  · rw [map_sub, hu, hu', sub_zero]
  · rw [map_sub, h'.1, sub_self]
  · rw [map_sub, h'.2, sub_self]

end Differential

/-! ### The fibre-critical set -/

section CriticalSet

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [FiniteDimensional ℝ A]
  (hS : ContMDiff ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ) ∞ S)
  (hreg : IsRegularValue ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) 0)

omit [TopologicalSpace H] [TopologicalSpace H'] in
/-- The fibre-critical set has codimension `dim A` in `(M × N) × A`. -/
private theorem finrank_sub_finrank_strongDual :
    finrank ℝ ((E × F) × A) - finrank ℝ (StrongDual ℝ A) = finrank ℝ E + finrank ℝ F := by
  rw [finrank_prod, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  omega

/-- The **fibre-critical set** `{z | ∂_a S z = 0}` of a smooth transverse family, as a charted space
modelled on `Fin (dim M + dim N) → ℝ`: it is a regular level of the fibre derivative, with the
atlas of `TauCeti.regularLevelChartedSpace`. -/
@[instance_reducible]
def familyCriticalSetChartedSpace :
    ChartedSpace (Fin (finrank ℝ E + finrank ℝ F) → ℝ)
      {z : (M × N) × A // familyFiberDeriv S z = 0} :=
  regularLevelChartedSpace (fun z _ ↦ (contMDiff_familyFiberDeriv hS z).of_le (by simp)) hreg
    finrank_sub_finrank_strongDual

/-- The fibre-critical set of a smooth transverse family is a smooth manifold of dimension
`dim M + dim N`. -/
theorem isManifold_familyCriticalSet :
    letI := familyCriticalSetChartedSpace hS hreg
    IsManifold 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ) ∞
      {z : (M × N) × A // familyFiberDeriv S z = 0} :=
  isManifold_regularLevel (by simp) (fun z _ ↦ contMDiff_familyFiberDeriv hS z) hreg
    finrank_sub_finrank_strongDual

/-- The inclusion of the fibre-critical set of a smooth transverse family is a smooth
embedding. -/
theorem isSmoothEmbedding_coe_familyCriticalSet :
    letI := familyCriticalSetChartedSpace hS hreg
    IsSmoothEmbedding 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ) ((I.prod J).prod 𝓘(ℝ, A)) ∞
      (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A) :=
  isSmoothEmbedding_coe_regularLevel (by simp) (fun z _ ↦ contMDiff_familyFiberDeriv hS z) hreg
    finrank_sub_finrank_strongDual

/-- The tangent space of the fibre-critical set at `z` is the kernel of the differential of the
fibre derivative there. -/
theorem range_mfderiv_coe_familyCriticalSet (z : {z : (M × N) × A // familyFiberDeriv S z = 0}) :
    letI := familyCriticalSetChartedSpace hS hreg
    (mfderiv 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ) ((I.prod J).prod 𝓘(ℝ, A))
      (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A) z).range =
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z).ker :=
  range_mfderiv_coe_regularLevel _ hreg _ z

/-- **The family relation is exact on the fibre-critical set.** Along the fibre-critical set of a
smooth transverse family, the family relation pulls the primitive `pr₁^*λ_M - pr₂^*λ_N` of the
twisted product back to the differential of the restriction of `S`. -/
theorem mpullback_familyCorrespondence_comp_coe_liouvilleForm :
    letI := familyCriticalSetChartedSpace hS hreg
    mpullback (F := ℝ) (k := 1) 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ)
        ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
        (familyCorrespondence I J S ∘ Subtype.val)
        (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm I M) -
          SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
            (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
            (liouvilleForm J N)).1 =
      mextDeriv (RoughForm.ofFunction 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ)
        (S ∘ (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A))) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hcoe := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).contMDiff.mdifferentiable
    (by simp)
  rw [mpullback_comp hcoe ((contMDiff_familyCorrespondence hS).mdifferentiable (by simp))]
  funext z
  ext v
  rw [TauCeti.mpullback_apply, mpullback_familyCorrespondence_liouvilleForm_apply hS, z.2,
    mextDeriv_ofFunction, ContinuousAlternatingMap.ofSubsingleton_apply_apply,
    mvfderiv_comp_apply z ((hS z).mdifferentiableAt (by simp)) (hcoe z)]
  simp only [mvfderiv_apply_eq_mfderiv_apply]
  -- The fibre derivative vanishes at `z`, so its value on `(dz v).2` is `0`.
  exact sub_zero _

/-- **The differential of the family relation is injective on the fibre-critical set.** -/
theorem injective_mfderiv_familyCorrespondence_comp_coe
    (z : {z : (M × N) × A // familyFiberDeriv S z = 0}) :
    letI := familyCriticalSetChartedSpace hS hreg
    Injective (mfderiv 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ)
      ((I.prod 𝓘(ℝ, E →L[ℝ] ℝ)).prod (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
      (familyCorrespondence I J S ∘ Subtype.val) z) := by
  let := familyCriticalSetChartedSpace hS hreg
  have hemb := isSmoothEmbedding_coe_familyCriticalSet hS hreg
  have hcoe := (hemb.isImmersion.contMDiff z).mdifferentiableAt (by simp)
  have hG := (contMDiff_familyCorrespondence hS z.1).mdifferentiableAt (by simp)
  -- The inclusion is injective with tangent image the kernel of `d(∂_a S)`, on which the
  -- differential of the family relation is injective.
  have hmem (v) : mfderiv 𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ) ((I.prod J).prod 𝓘(ℝ, A))
      Subtype.val z v ∈
      (mfderiv ((I.prod J).prod 𝓘(ℝ, A)) 𝓘(ℝ, StrongDual ℝ A) (familyFiberDeriv S) z).ker := by
    rw [← range_mfderiv_coe_familyCriticalSet hS hreg z]
    exact ⟨v, rfl⟩
  intro v w hvw
  rw [mfderiv_comp_apply z hG hcoe, mfderiv_comp_apply z hG hcoe] at hvw
  exact hemb.isImmersion.mfderiv_injective (by simp) z
    (injOn_mfderiv_familyCorrespondence_ker hS (isRegularPoint_iff.mp (hreg.isRegularPoint z.2))
      (hmem v) (hmem w) hvw)

/-- **A transverse generating family defines an exact Lagrangian map.** On finite-dimensional
boundaryless manifolds `M` and `N`, the family relation `((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S))`
of a smooth transverse family `S` on `(M × N) × A`, restricted to its fibre-critical set, is an
exact Lagrangian map into `T*M × T*N` for the twisted product `pr₁^*ω_M - pr₂^*ω_N` and its
primitive `pr₁^*λ_M - pr₂^*λ_N`, with primitive the restriction of `S`. -/
theorem isExactLagrangianMap_familyCorrespondence_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    ((isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.twistedProd
        (isSymplectic_symplecticForm (I := J) (M := N)).isNondegenerate).IsExactLagrangianMap
      𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ)
      (SmoothForm.mpullback (Prod.fst : CotangentBundle I M × CotangentBundle J N → _)
          (contMDiff_fst (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (liouvilleForm I M) -
        SmoothForm.mpullback (Prod.snd : CotangentBundle I M × CotangentBundle J N → _)
          (contMDiff_snd (I := I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (J := J.prod 𝓘(ℝ, F →L[ℝ] ℝ)))
          (liouvilleForm J N))
      (familyCorrespondence I J S ∘ Subtype.val)
      (S ∘ (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A)) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hcoe := (isSmoothEmbedding_coe_familyCriticalSet hS hreg).isImmersion.contMDiff
  refine (SmoothTwoForm.IsNondegenerate.isExactLagrangianMap_iff_of_finrank
    (twistedProd_symplecticForm I M J N) ((contMDiff_familyCorrespondence hS).comp hcoe)
    (injective_mfderiv_familyCorrespondence_comp_coe hS hreg) ?_).mpr
      ⟨hS.comp hcoe, mpullback_familyCorrespondence_comp_coe_liouvilleForm hS hreg⟩
  simp only [finrank_fin_fun, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  ring

/-- **A transverse generating family defines a Lagrangian immersion.** On finite-dimensional
boundaryless manifolds `M` and `N`, the family relation `((q, Q), a) ↦ ((q, d_q S), (Q, -d_Q S))`
of a smooth transverse family `S` on `(M × N) × A`, restricted to its fibre-critical set, is a
Lagrangian immersion into `T*M × T*N` for the twisted product `pr₁^*ω_M - pr₂^*ω_N`: an immersed
Lagrangian correspondence `T*M ⇝ T*N`. -/
theorem isLagrangianImmersion_familyCorrespondence_comp_coe :
    letI := familyCriticalSetChartedSpace hS hreg
    ((isSymplectic_symplecticForm (I := I) (M := M)).isNondegenerate.twistedProd
        (isSymplectic_symplecticForm (I := J) (M := N)).isNondegenerate).IsLagrangianImmersion
      𝓘(ℝ, Fin (finrank ℝ E + finrank ℝ F) → ℝ) (familyCorrespondence I J S ∘
        (Subtype.val : {z : (M × N) × A // familyFiberDeriv S z = 0} → (M × N) × A)) := by
  let := familyCriticalSetChartedSpace hS hreg
  have := isManifold_familyCriticalSet hS hreg
  have hL := isExactLagrangianMap_familyCorrespondence_comp_coe hS hreg
  refine ⟨((contMDiff_familyCorrespondence hS).comp
      (isSmoothEmbedding_coe_familyCriticalSet hS hreg).isImmersion.contMDiff
      ).isImmersion_of_injective_mfderiv (by simp)
      (injective_mfderiv_familyCorrespondence_comp_coe hS hreg),
    hL.isLagrangianMap.isIsotropicMap, ?_⟩
  simp only [finrank_fin_fun, finrank_prod, ContinuousLinearMap.dual_finrank_eq]
  ring

end CriticalSet

end TauCeti.CotangentBundle
