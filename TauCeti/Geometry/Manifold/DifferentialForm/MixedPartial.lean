/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.ModelChart
import TauCeti.Geometry.Manifold.VectorField.Prod
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# Mixed partial derivatives of closed two-forms over a parameter space

Let `η` be a smooth two-form on the product `P × M` of a real Banach space `P` of parameters with
a manifold `M`. For a parameter direction `a ∈ P`, contracting `η` with the constant field
`∂_a = (a, 0)` and reading the result on vertical tangent vectors `(0, v)` gives a family of
one-forms on `M` indexed by the parameter,

`β_a(p)ₓ(v) = η_(p, x)((a, 0), (0, v))`,

and evaluating `η` on two constant fields gives a family of functions on `M`,
`f_(a, b)(p)(x) = η_(p, x)((a, 0), (b, 0))`. The exterior derivative of `η` on the corresponding
three vectors is

`dη((a, 0), (b, 0), (0, v)) = ∂_a β_b(v) - ∂_b β_a(v) + d_M f_(a, b)(v)`

(`TauCeti.SmoothForm.mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv`), where `∂_a` and `∂_b`
differentiate in the parameter and `d_M` differentiates along `M`. It is the invariant formula for
the exterior derivative (`TauCeti.mextDeriv_apply_vectorField_of_mlieBracket_eq_zero`) on the three
pairwise commuting fields `∂_a`, `∂_b` and a vertical extension of `v`. Hence, if `η` is closed at
`(p, x)`, the families satisfy the mixed-partial identity

`∂_b β_a - ∂_a β_b = d_M f_(a, b)`

(`TauCeti.SmoothForm.fderiv_apply_sub_fderiv_apply_eq_mvfderiv_apply`). The parameter derivatives
exist: the coefficients of a smooth form along a slice `q ↦ (q, x)` are differentiable in `q`
(`TauCeti.SmoothForm.differentiableAt_apply_prodMk`).

For a two-parameter family of maps `φ_(t, u)` of `M` and a closed two-form `σ` on `M`, applied to
the pullback of `σ` along `((t, u), x) ↦ φ_(t, u) x`, the mixed-partial identity is the
two-parameter identity of flux forms in `TauCeti.Geometry.Symplectic.Flux.TwoParameter`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.32 (the invariant
  formula for the exterior derivative).
-/

public section

noncomputable section

open Bundle VectorField
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The coefficients of a smooth form on `P × M` along the slice `q ↦ (q, x)`, against fixed
tangent vectors of `P × M`, are differentiable in the parameter. -/
theorem differentiableAt_apply_prodMk [IsManifold I 1 M] {k : ℕ}
    (η : SmoothForm (𝓘(ℝ, P).prod I) (P × M) F k) (p : P) (x : M) (w : Fin k → P × E) :
    DifferentiableAt ℝ (fun q ↦ η.val (q, x) w) p := by
  -- Extend each `w i` to a product field: constant in `P`, an extension of `(w i).2` along `M`.
  let W : Fin k → (z : P × M) → TangentSpace (𝓘(ℝ, P).prod I) z := fun i ↦
    Manifold.prodVectorField (fun _ ↦ (w i).1)
      (FiberBundle.extend (x := x) E ((w i).2 : TangentSpace I x))
  have hW (i : Fin k) : MDifferentiableAt (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod I).tangent
      (fun z ↦ (W i z : TangentBundle (𝓘(ℝ, P).prod I) (P × M))) (p, x) := by
    refine Manifold.mdifferentiableAt_prodVectorField (p := (p, x))
      ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero) ?_
    exact FiberBundle.mdifferentiableAt_extend (V := TangentSpace I) (x := x) I E (w i).2
  have h := (η.mdifferentiableAt_apply_vectorField hW).comp p
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  -- Along the slice through `x` the fields take the values `w i`.
  have hval (q : P) : (fun i ↦ W i (q, x)) = w := funext fun i ↦
    Prod.ext (Manifold.prodVectorField_fst _ _ _)
      ((Manifold.prodVectorField_snd _ _ _).trans (FiberBundle.extend_apply_self _ _))
  simpa only [Function.comp_def, id_eq, hval] using h.differentiableAt

/-! ### The coordinate frame of a parameter product -/

/-- The frame of `P × M` on which exterior derivatives are evaluated: the constant fields
`(a, 0)` and `(b, 0)` and the vertical field `(0, W)`. -/
private def paramFrame (a b : P) (W : (y : M) → TangentSpace I y) :
    Fin 3 → (q : P × M) → TangentSpace (𝓘(ℝ, P).prod I) q :=
  fun i ↦ Manifold.prodVectorField (fun _ ↦ ![a, b, 0] i) (![0, 0, W] i)

variable {a b : P} {W : (y : M) → TangentSpace I y}

private theorem paramFrame_fst (i : Fin 3) (q : P × M) :
    (paramFrame a b W i q).1 = ![a, b, 0] i :=
  Manifold.prodVectorField_fst _ _ q

private theorem paramFrame_snd (i : Fin 3) (q : P × M) :
    (paramFrame a b W i q).2 = ![0, 0, W] i q.2 :=
  Manifold.prodVectorField_snd _ _ q

private theorem paramFrame_zero (q : P × M) :
    paramFrame a b W 0 q = ((a, 0) : TangentSpace (𝓘(ℝ, P).prod I) q) :=
  Prod.ext (paramFrame_fst 0 q) (paramFrame_snd 0 q)

private theorem paramFrame_one (q : P × M) :
    paramFrame a b W 1 q = ((b, 0) : TangentSpace (𝓘(ℝ, P).prod I) q) :=
  Prod.ext (paramFrame_fst 1 q) (paramFrame_snd 1 q)

private theorem paramFrame_two (q : P × M) :
    paramFrame a b W 2 q = ((0, W q.2) : TangentSpace (𝓘(ℝ, P).prod I) q) :=
  Prod.ext (paramFrame_fst 2 q) (paramFrame_snd 2 q)

/-- The values of the frame at a point. -/
private theorem paramFrame_apply (q : P × M) :
    (paramFrame a b W · q) =
      ![((a, 0) : TangentSpace (𝓘(ℝ, P).prod I) q), (b, 0), (0, W q.2)] := by
  funext l
  fin_cases l
  exacts [paramFrame_zero q, paramFrame_one q, paramFrame_two q]

variable {p : P} {x : M}

section

variable [IsManifold I 1 M]

private theorem removeNth_paramFrame (η : SmoothForm (𝓘(ℝ, P).prod I) (P × M) F 2)
    (i j l : Fin 3) (hjl : ∀ m, i.succAbove m = ![j, l] m) :
    (fun q ↦ η.val q (Fin.removeNth i (paramFrame a b W · q))) =
      fun q ↦ η.val q ![paramFrame a b W j q, paramFrame a b W l q] := by
  funext q
  congr 1
  funext m
  fin_cases m <;> simp [Fin.removeNth, hjl]

/-- The vertical components `0`, `0` and `W` of the frame are differentiable where `W` is. -/
private theorem mdifferentiableAt_vertical
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) (i : Fin 3) :
    MDifferentiableAt I I.tangent (fun y ↦ (![0, 0, W] i y : TangentBundle I M)) x := by
  fin_cases i
  · exact (contMDiff_zeroSection ℝ (TangentSpace I)).mdifferentiableAt one_ne_zero
  · exact (contMDiff_zeroSection ℝ (TangentSpace I)).mdifferentiableAt one_ne_zero
  · exact hW

private theorem mdifferentiableAt_paramFrame
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) (i : Fin 3) :
    MDifferentiableAt (𝓘(ℝ, P).prod I) (𝓘(ℝ, P).prod I).tangent
      (fun q ↦ (paramFrame a b W i q : TangentBundle (𝓘(ℝ, P).prod I) (P × M))) (p, x) :=
  Manifold.mdifferentiableAt_prodVectorField (p := (p, x))
    ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_vertical hW i)

/-- Evaluating a smooth two-form on two fields of the frame and differentiating along a third
splits into a parameter derivative and a derivative along `M`. -/
private theorem mvfderiv_apply_paramFrame (η : SmoothForm (𝓘(ℝ, P).prod I) (P × M) F 2)
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) (i j k : Fin 3) :
    mvfderiv (𝓘(ℝ, P).prod I) (fun q ↦ η.val q ![paramFrame a b W j q, paramFrame a b W k q])
        (p, x) (paramFrame a b W i (p, x)) =
      fderiv ℝ (fun q ↦ η.val (q, x) ![paramFrame a b W j (q, x), paramFrame a b W k (q, x)]) p
          (![a, b, 0] i) +
        mvfderiv I (fun y ↦ η.val (p, y) ![paramFrame a b W j (p, y), paramFrame a b W k (p, y)])
          x (![0, 0, W] i x) := by
  have hd := η.mdifferentiableAt_apply_vectorField (x := (p, x))
    (V := ![paramFrame a b W j, paramFrame a b W k])
    (fun l ↦ by fin_cases l; exacts [mdifferentiableAt_paramFrame (p := p) hW j,
      mdifferentiableAt_paramFrame (p := p) hW k])
  have hev (q : P × M) : (fun l ↦ ![paramFrame a b W j, paramFrame a b W k] l q) =
      ![paramFrame a b W j q, paramFrame a b W k q] := by
    funext l
    fin_cases l <;> simp
  simp only [hev] at hd
  rw [hd.mvfderiv_prod_eq_add_apply, paramFrame_fst, paramFrame_snd]
  -- The parameter summand is `mvfderiv_eq_fderiv_apply` once `(p, x).1` and `(p, x).2` reduce.
  exact congrArg (· + _) (mvfderiv_eq_fderiv_apply _ p _)

end

variable [CompleteSpace E] [CompleteSpace P] [IsManifold I 2 M]

private theorem mlieBracket_paramFrame
    (hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x) (i j : Fin 3) :
    mlieBracket (𝓘(ℝ, P).prod I) (paramFrame a b W i) (paramFrame a b W j) (p, x) = 0 := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  rw [paramFrame, paramFrame, Manifold.mlieBracket_prodVectorField (p := (p, x))
    ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero)
    ((contMDiff_tangentBundle_mk_const _).mdifferentiableAt one_ne_zero)
    (mdifferentiableAt_vertical hW i) (mdifferentiableAt_vertical hW j)]
  -- The zero of the tangent space of `P × M` is the zero of `P × E` only definitionally.
  refine Prod.ext ?_ ?_
  · simp only [Manifold.prodVectorField_fst, mlieBracket_const_model_space]
    rfl
  · simp only [Manifold.prodVectorField_snd]
    fin_cases i <;> fin_cases j <;> simp <;> rfl

/-! ### The exterior derivative in product coordinates -/

/-- **The exterior derivative of a two-form on a parameter product.** For a smooth two-form `η`
on `P × M`, parameter directions `a, b ∈ P` and `v ∈ T_x M`,
`dη((a, 0), (b, 0), (0, v))` is the parameter derivative along `a` of `η((b, 0), (0, v))`, minus
the parameter derivative along `b` of `η((a, 0), (0, v))`, plus the derivative along `v` of
`y ↦ η_(p, y)((a, 0), (b, 0))`. -/
theorem mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv
    (η : SmoothForm (𝓘(ℝ, P).prod I) (P × M) F 2) (p : P) (x : M) (a b : P)
    (v : TangentSpace I x) :
    mextDeriv η.val (p, x) ![(a, 0), (b, 0), (0, v)] =
      fderiv ℝ (fun q ↦ η.val (q, x) ![(b, 0), (0, v)]) p a -
        fderiv ℝ (fun q ↦ η.val (q, x) ![(a, 0), (0, v)]) p b +
        mvfderiv I (fun y ↦ η.val (p, y) ![(a, 0), (b, 0)]) x v := by
  -- Evaluate on the frame `(a, 0)`, `(b, 0)`, `(0, W)` for a vertical extension `W` of `v`.
  set W : (y : M) → TangentSpace I y := FiberBundle.extend E v
  have hW : MDifferentiableAt I I.tangent (fun y ↦ (W y : TangentBundle I M)) x :=
    FiberBundle.mdifferentiableAt_extend I E v
  have hW0 : W x = v := FiberBundle.extend_apply_self _ v
  have h := mextDeriv_apply_vectorField_of_mlieBracket_eq_zero (η.mdifferentiableAt (p, x))
    (mdifferentiableAt_paramFrame (a := a) (b := b) (p := p) hW) (mlieBracket_paramFrame hW)
  have hpt : (paramFrame a b W · (p, x)) = ![(a, 0), (b, 0), (0, v)] := by
    rw [paramFrame_apply, hW0]
    -- The right side elaborates as a vector in `P × E`, the frame's values as a vector in the
    -- tangent space of `P × M`; the two types agree only by unfolding `TangentSpace`.
    rfl
  rw [Fin.sum_univ_three] at h
  rw [removeNth_paramFrame η 0 1 2 (by decide), removeNth_paramFrame η 1 0 2 (by decide),
    removeNth_paramFrame η 2 0 1 (by decide), mvfderiv_apply_paramFrame η hW,
    mvfderiv_apply_paramFrame η hW, mvfderiv_apply_paramFrame η hW] at h
  -- Along the slices through `(p, x)`, the fields take their values at `(p, x)`.
  have hf₀ : (fun q ↦ η.val (q, x) ![paramFrame a b W 1 (q, x), paramFrame a b W 2 (q, x)]) =
      fun q ↦ η.val (q, x) ![(b, 0), (0, v)] := by
    simp only [paramFrame_one, paramFrame_two, hW0]
  have hf₁ : (fun q ↦ η.val (q, x) ![paramFrame a b W 0 (q, x), paramFrame a b W 2 (q, x)]) =
      fun q ↦ η.val (q, x) ![(a, 0), (0, v)] := by
    simp only [paramFrame_zero, paramFrame_two, hW0]
  have hf₂ : (fun y ↦ η.val (p, y) ![paramFrame a b W 0 (p, y), paramFrame a b W 1 (p, y)]) =
      fun y ↦ η.val (p, y) ![(a, 0), (b, 0)] := by
    simp only [paramFrame_zero, paramFrame_one]
  refine (congrArg (mextDeriv η.val (p, x)) hpt.symm).trans ?_
  rw [h, hf₀, hf₁, hf₂]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Pi.zero_apply, map_zero, hW0, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_one_pow]
  abel

/-- **Mixed partial derivatives of a closed two-form over a parameter space.** Let `η` be a
smooth two-form on `P × M`, closed at `(p, x)`. For parameter directions `a, b ∈ P` and
`v ∈ T_x M`, the parameter derivative in the direction `b` of `η((a, 0), (0, v))`, minus that in
the direction `a` of `η((b, 0), (0, v))`, is the derivative along `v` of the function
`y ↦ η_(p, y)((a, 0), (b, 0))`. -/
theorem fderiv_apply_sub_fderiv_apply_eq_mvfderiv_apply
    (η : SmoothForm (𝓘(ℝ, P).prod I) (P × M) F 2) {p : P} {x : M}
    (hη : mextDeriv η.val (p, x) = 0) (a b : P) (v : TangentSpace I x) :
    fderiv ℝ (fun q ↦ η.val (q, x) ![(a, 0), (0, v)]) p b -
        fderiv ℝ (fun q ↦ η.val (q, x) ![(b, 0), (0, v)]) p a =
      mvfderiv I (fun y ↦ η.val (p, y) ![(a, 0), (b, 0)]) x v := by
  have h := mextDeriv_apply_eq_fderiv_sub_fderiv_add_mvfderiv η p x a b v
  rw [hη, ContinuousAlternatingMap.coe_zero, Pi.zero_apply] at h
  rw [← sub_eq_zero, ← neg_eq_zero]
  convert h.symm using 1
  abel

end TauCeti.SmoothForm
