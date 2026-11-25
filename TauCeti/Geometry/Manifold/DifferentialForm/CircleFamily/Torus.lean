/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.CircleFamily.Pullback
public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Instances.CircleFamily.Torus

/-!
# The angle forms and the time forms of a smooth family of tori

For finitely many positive period functions `p i : B → ℝ_{>0}` on a smooth manifold `B`, the
family `TauCeti.TorusFamily p` has the torus `∀ i, AddCircle (p i b)` as its fiber over `b`. This
file puts on it, for each factor `i`, the two one-forms that extend the coordinate time forms
`dt_i` of the individual tori (`TauCeti.torusTimeForm`) across the family. Each is the pullback,
along the `i`-th coordinate `(b, x) ↦ (b, x i)` to the family of circles of `p i`
(`TauCeti.TorusFamily.coord`), of the corresponding form of that family of circles.

* The **angle form** `β_i` (`TauCeti.TorusFamily.angleForm`) is the pullback of the angle form
  of the family of circles of `p i`, the differential of the `i`-th normalized angle. It is
  defined and closed for all period functions, smooth or not, and restricts on the torus over `b`
  to `(p i b)⁻¹ • dt_i`.
* The **time form** `η_i = p_i • β_i` (`TauCeti.TorusFamily.timeForm`), for a smooth period
  function `p i`, is the pullback of the time form of the family of circles of `p i`. It restricts
  on the torus over `b` to its coordinate time form `dt_i`, and its exterior derivative is
  `d(p_i ∘ base) ∧ β_i`. It is not closed in general.

Both forms are natural. Base change along a smooth map `f : B' → B` pulls back the forms of `p` to
those of the periods `p i ∘ f`; in particular, along the inclusion of an open subset, the forms of
`p` restrict to those of the family over that subset. The fiberwise rescaling from the periods `p`
to the periods `q` keeps the normalized angles, so it pulls the angle form `β_i` of `q` back to that
of `p`, and the time form `η_i` of `q` back to `(q i / p i)` times the time form `η_i` of `p`.

For smooth period functions, the forms are computed on the real cover
`Q(b, t) = (b, ([t j]_(p j b))ⱼ)` of the family (`TauCeti.TorusFamily.representative`), the
covering map from `B × (ι → ℝ)`: `Q^* β_i = d(t_i / p_i)` and
`Q^* η_i = dt_i - (t_i / p_i) • dp_i`, where `p_i` stands for `(b, t) ↦ p i b`. Every form pulled
back along `Q` is invariant under the deck translations `t ↦ t + (k j * p j b)ⱼ`; for `Q^* η_i`
the term `k_i dp_i` coming from the translated coordinate is cancelled by the change of `t_i / p_i`.

## Main definitions

* `TauCeti.TorusFamily.angleForm p IB i`: the angle form `β_i`.
* `TauCeti.TorusFamily.timeForm p IB i hp`: the time form `η_i = p_i • β_i`.

## Main results

* `TauCeti.TorusFamily.angleForm_apply`: the angle form is the differential of the `i`-th
  normalized angle.
* `TauCeti.TorusFamily.isClosed_angleForm`, `TauCeti.TorusFamily.mpullback_mk_angleForm`: the
  angle form is closed and restricts to `(p i b)⁻¹ • dt_i` on the torus over `b`.
* `TauCeti.TorusFamily.timeForm_apply`, `TauCeti.TorusFamily.mpullback_mk_timeForm`: the time form
  is the angle form rescaled by the `i`-th period, and restricts to `dt_i` on the torus over `b`.
* `TauCeti.TorusFamily.mextDeriv_timeForm`: `dη_i = d(p_i ∘ base) ∧ β_i`.
* `TauCeti.TorusFamily.mpullback_comap_angleForm`, `TauCeti.TorusFamily.mpullback_comap_timeForm`:
  compatibility with base change.
* `TauCeti.TorusFamily.mpullback_rescale_angleForm`,
  `TauCeti.TorusFamily.mpullback_rescale_timeForm`: compatibility with the fiberwise rescalings.
* `TauCeti.TorusFamily.mpullback_representative_angleForm`,
  `TauCeti.TorusFamily.mpullback_representative_timeForm`: on the real cover,
  `Q^* β_i = d(t_i / p_i)` and `Q^* η_i = dt_i - (t_i / p_i) • dp_i`.
* `TauCeti.TorusFamily.mpullback_deck_mpullback_representative`: forms pulled back to the real
  cover are invariant under the deck translations.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (the angle variables of a family of invariant tori).
-/

public section

noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

namespace TorusFamily

variable {B ι : Type*} [Fintype ι] (p : ι → B → PositivePeriod) {EB HB : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB)
  [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]

/-- Pull a form on the family of circles of `p i` back to the torus over `b`, through the `i`-th
coordinate, as the pullback along the `i`-th factor of its restriction to the circle over `b`. -/
private theorem mpullback_mk_mpullback_coord (i : ι) (b : B)
    (φ : SmoothForm (IB.prod 𝓘(ℝ)) (CircleFamily.Pullback (p i)) ℝ 1) :
    SmoothForm.mpullback (mk b) (contMDiff_mk p IB ∞ b)
        (SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i) φ) =
      SmoothForm.mpullback (fun x ↦ x i) contMDiff_apply
        (SmoothForm.mpullback (CircleFamily.Pullback.mk b)
          (CircleFamily.Pullback.contMDiff_mk (p i) IB ∞ b) φ) :=
  -- On the torus over `b`, the `i`-th coordinate is the `i`-th factor followed by the inclusion
  -- of the circle over `b`.
  SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext (coord_mk p i b)) φ

/-! ### The angle forms -/

/-- The angle form `β_i` of the family of tori: the pullback along the `i`-th coordinate of the
angle form of the family of circles of `p i`, the differential of the `i`-th normalized angle. -/
def angleForm (i : ι) :
    SmoothForm (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) (TorusFamily p) ℝ 1 :=
  SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i)
    (CircleFamily.Pullback.angleForm (p i) IB)

/-- The angle form `β_i` is the pullback along the `i`-th coordinate of the angle form of the
family of circles of `p i`. -/
@[simp]
theorem mpullback_coord_angleForm (i : ι) :
    SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i)
      (CircleFamily.Pullback.angleForm (p i) IB) = angleForm p IB i :=
  (rfl)

/-- The angle form `β_i` is the differential of the `i`-th normalized angle, read in the real
tangent lines of the unit-period circle. -/
@[simp]
theorem angleForm_apply (i : ι) (z : TorusFamily p)
    (v : Fin 1 → TangentSpace (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) z) :
    (angleForm p IB i).val z v =
      mfderiv (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) 𝓘(ℝ)
        (fun z ↦ (normalization p IB ∞ z).2 i) z (v 0) := by
  have hg := ((contMDiff_snd.comp (CircleFamily.Pullback.normalization (p i) IB ∞).contMDiff)
    (coord p i z)).mdifferentiableAt (by simp)
  have hc := (contMDiff_coord p IB ∞ i z).mdifferentiableAt (by simp)
  have h : (Prod.snd ∘ CircleFamily.Pullback.normalization (p i) IB ∞) ∘ coord p i =
      fun z ↦ (normalization p IB ∞ z).2 i :=
    funext fun z ↦ by simp
  rw [angleForm, SmoothForm.mpullback_apply, CircleFamily.Pullback.angleForm_apply, ← h]
  exact (mfderiv_comp_apply z hg hc (v 0)).symm

/-- The angle forms are closed. -/
theorem isClosed_angleForm (i : ι) : (angleForm p IB i).IsClosed :=
  (CircleFamily.Pullback.isClosed_angleForm (p i) IB).mpullback _ _

/-- On the torus over `b`, the angle form `β_i` restricts to `(p i b)⁻¹ • dt_i`. -/
@[simp]
theorem mpullback_mk_angleForm (i : ι) (b : B) :
    SmoothForm.mpullback (mk b) (contMDiff_mk p IB ∞ b) (angleForm p IB i) =
      (p i b : ℝ)⁻¹ • torusTimeForm (fun j ↦ (p j b : ℝ)) i := by
  rw [angleForm, mpullback_mk_mpullback_coord, CircleFamily.Pullback.mpullback_mk_angleForm,
    map_smul, torusTimeForm_def]

/-! ### The time forms -/

/-- The time form `η_i = p_i • β_i` of the family of tori, for a smooth period function `p i`: the
pullback along the `i`-th coordinate of the time form of the family of circles of `p i`. It
restricts to the coordinate time form `dt_i` on the torus over each `b`. -/
def timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) :
    SmoothForm (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) (TorusFamily p) ℝ 1 :=
  SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i)
    (CircleFamily.Pullback.timeForm (p i) IB hp)

/-- The time form `η_i` is the pullback along the `i`-th coordinate of the time form of the family
of circles of `p i`. -/
@[simp]
theorem mpullback_coord_timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) :
    SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i)
      (CircleFamily.Pullback.timeForm (p i) IB hp) = timeForm p IB i hp :=
  (rfl)

/-- The time form `η_i` is the angle form `β_i` rescaled by the `i`-th period at the base point. -/
@[simp]
theorem timeForm_apply (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) (z : TorusFamily p)
    (v : Fin 1 → TangentSpace (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) z) :
    (timeForm p IB i hp).val z v = p i z.base * (angleForm p IB i).val z v := by
  rw [timeForm, angleForm, SmoothForm.mpullback_apply, SmoothForm.mpullback_apply,
    CircleFamily.Pullback.timeForm_apply, base_coord]

/-- On the torus over `b`, the time form `η_i` restricts to the coordinate time form `dt_i`. -/
@[simp]
theorem mpullback_mk_timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) (b : B) :
    SmoothForm.mpullback (mk b) (contMDiff_mk p IB ∞ b) (timeForm p IB i hp) =
      torusTimeForm (fun j ↦ (p j b : ℝ)) i := by
  rw [timeForm, mpullback_mk_mpullback_coord, CircleFamily.Pullback.mpullback_mk_timeForm,
    torusTimeForm_def]

/-- The exterior derivative of the time form `η_i` is `d(p_i ∘ base) ∧ β_i`. -/
theorem mextDeriv_timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i)) :
    mextDeriv (timeForm p IB i hp).val =
      RoughForm.wedge
        (mextDeriv (RoughForm.ofFunction (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
          fun z : TorusFamily p ↦ (p i z.base : ℝ)))
        (angleForm p IB i).val := by
  have hc := contMDiff_coord p IB ∞ i
  have hg : ContMDiff (IB.prod 𝓘(ℝ)) 𝓘(ℝ, ℝ) ∞
      fun z : CircleFamily.Pullback (p i) ↦ (p i z.base : ℝ) :=
    (contMDiff_subtypeVal.comp hp).comp (CircleFamily.Pullback.contMDiff_base (p i) IB ∞)
  have hcomp : (fun z : CircleFamily.Pullback (p i) ↦ (p i z.base : ℝ)) ∘ coord p i =
      fun z ↦ (p i z.base : ℝ) :=
    funext fun z ↦ by simp
  rw [timeForm, ← mextDerivₗ_apply, SmoothForm.mextDerivₗ_mpullback, SmoothForm.coe_mpullback,
    mextDerivₗ_apply, CircleFamily.Pullback.mextDeriv_timeForm, mpullback_wedge,
    mpullback_mextDeriv_ofFunction (hc.mdifferentiable (by simp)) (hg.mdifferentiable (by simp)),
    hcomp, ← SmoothForm.coe_mpullback _ hc, mpullback_coord_angleForm]

/-! ### Base change -/

section BaseChange

variable {B' : Type*} (f : B' → B) {EB' HB' : Type*} [NormedAddCommGroup EB']
  [NormedSpace ℝ EB'] [TopologicalSpace HB'] {IB' : ModelWithCorners ℝ EB' HB'}
  [TopologicalSpace B'] [ChartedSpace HB' B'] [IsManifold IB' ∞ B']

/-- Pull a form on the family of circles of `p i` back through the `i`-th coordinate and then
along base change, as the pullback through the `i`-th coordinate of its base change. -/
private theorem mpullback_comap_mpullback_coord (hf : ContMDiff IB' IB ∞ f) (i : ι)
    (φ : SmoothForm (IB.prod 𝓘(ℝ)) (CircleFamily.Pullback (p i)) ℝ 1) :
    SmoothForm.mpullback (comap p f) (contMDiff_comap p f IB hf)
        (SmoothForm.mpullback (coord p i) (contMDiff_coord p IB ∞ i) φ) =
      SmoothForm.mpullback (coord (fun i ↦ p i ∘ f) i) (contMDiff_coord _ IB' ∞ i)
        (SmoothForm.mpullback (CircleFamily.Pullback.comap (p i) f)
          (CircleFamily.Pullback.contMDiff_comap (p i) f IB hf) φ) :=
  SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _ (funext (coord_comap p f i)) φ

/-- Base change along a smooth map `f` pulls the angle form `β_i` of the family of `p` back to the
angle form `β_i` of the family of the periods `p i ∘ f`. -/
@[simp]
theorem mpullback_comap_angleForm (hf : ContMDiff IB' IB ∞ f) (i : ι) :
    SmoothForm.mpullback (comap p f) (contMDiff_comap p f IB hf) (angleForm p IB i) =
      angleForm (fun i ↦ p i ∘ f) IB' i := by
  rw [angleForm, mpullback_comap_mpullback_coord p IB f hf,
    CircleFamily.Pullback.mpullback_comap_angleForm (p i) IB f hf, angleForm]

/-- Base change along a smooth map `f` pulls the time form `η_i` of the family of `p` back to the
time form `η_i` of the family of the periods `p i ∘ f`. -/
@[simp]
theorem mpullback_comap_timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i))
    (hf : ContMDiff IB' IB ∞ f) :
    SmoothForm.mpullback (comap p f) (contMDiff_comap p f IB hf) (timeForm p IB i hp) =
      timeForm (fun i ↦ p i ∘ f) IB' i (hp.comp hf) := by
  rw [timeForm, mpullback_comap_mpullback_coord p IB f hf,
    CircleFamily.Pullback.mpullback_comap_timeForm (p i) IB f hp hf, timeForm]

end BaseChange

/-! ### Fiberwise rescaling -/

variable (q : ι → B → PositivePeriod)

/-- The fiberwise rescaling from the periods `p` to the periods `q` keeps the normalized angles, so
it pulls the angle form `β_i` of `q` back to the angle form `β_i` of `p`. -/
@[simp]
theorem mpullback_rescale_angleForm (i : ι) :
    SmoothForm.mpullback (rescale p IB q ∞) (rescale p IB q ∞).contMDiff (angleForm q IB i) =
      angleForm p IB i := by
  rw [angleForm, angleForm, SmoothForm.mpullback_mpullback_of_comp_eq (rescale p IB q ∞).contMDiff
    (contMDiff_coord q IB ∞ i) (contMDiff_coord p IB ∞ i)
    (CircleFamily.Pullback.rescale (p i) IB (q i) ∞).contMDiff
    (funext (coord_rescale p IB q ∞ i)), CircleFamily.Pullback.mpullback_rescale_angleForm]

/-- The fiberwise rescaling from the periods `p` to the periods `q` pulls the time form `η_i` of
`q` back to `(q i / p i)` times the time form `η_i` of `p`. -/
theorem mpullback_rescale_timeForm (i : ι) (hp : ContMDiff IB 𝓘(ℝ) ∞ (p i))
    (hq : ContMDiff IB 𝓘(ℝ) ∞ (q i)) :
    (SmoothForm.mpullback (rescale p IB q ∞) (rescale p IB q ∞).contMDiff
        (timeForm q IB i hq)).val =
      fun z ↦ ((q i z.base : ℝ) / p i z.base) • (timeForm p IB i hp).val z := by
  refine funext fun z ↦ ContinuousAlternatingMap.ext fun v ↦ ?_
  have h := DFunLike.congr_fun
    (congrFun (congrArg Subtype.val (mpullback_rescale_angleForm p IB q i)) z) v
  rw [SmoothForm.mpullback_apply] at h
  rw [SmoothForm.mpullback_apply, timeForm_apply, base_rescale, h,
    ContinuousAlternatingMap.smul_apply, timeForm_apply, smul_eq_mul]
  field_simp [(p i z.base).property.ne']

/-! ### The real cover -/

section RealCover

variable {p IB} (hp : ∀ j, ContMDiff IB 𝓘(ℝ) ∞ (p j))

omit [IsManifold IB ∞ B] in
include hp in
/-- The normalized time `t i / p i b` of a real point `(b, t)` is smooth: it is the `i`-th time
coordinate of the real normalization. -/
private theorem contMDiff_normalizedTime (i : ι) :
    ContMDiff (IB.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ, ℝ) ∞ fun z : B × (ι → ℝ) ↦ z.2 i / (p i z.1 : ℝ) := by
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).contMDiff.comp
    contMDiff_snd).comp (realNormalization p IB hp).contMDiff
  simpa only [Function.comp_def, realNormalization_apply, ContinuousLinearMap.proj_apply] using h

include hp in
/-- On the real cover `Q(b, t) = (b, ([t j]_(p j b))ⱼ)`, the angle form `β_i` is the differential
of the normalized time `t i / p i b`. -/
theorem mpullback_representative_angleForm (i : ι) :
    mpullback (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
        (representative p) (angleForm p IB i).val =
      mextDeriv (RoughForm.ofFunction (IB.prod 𝓘(ℝ, ι → ℝ))
        fun z : B × (ι → ℝ) ↦ z.2 i / (p i z.1 : ℝ)) := by
  have hcomp : (fun z ↦ (normalization p IB ∞ z).2 i) ∘ representative p =
      ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ fun z : B × (ι → ℝ) ↦ z.2 i / (p i z.1 : ℝ) :=
    funext fun z ↦ by simp only [Function.comp_apply, normalization_representative]
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hQ := (contMDiff_representative p IB hp z).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) 𝓘(ℝ)
      (fun z ↦ (normalization p IB ∞ z).2 i) (representative p z) :=
    (((contMDiff_apply (i := i)).comp contMDiff_snd).comp (normalization p IB ∞).contMDiff
      _).mdifferentiableAt (by simp)
  have hh := (contMDiff_normalizedTime hp i z).mdifferentiableAt (by simp)
  have hc := ((AddCircle.contMDiff_coe 1 ∞) (z.2 i / (p i z.1 : ℝ))).mdifferentiableAt (by simp)
  rw [mpullback_apply, angleForm_apply, ← mfderiv_comp_apply z hg hQ, hcomp,
    mfderiv_comp_apply z hc hh, AddCircle.mfderiv_coe, mextDeriv_ofFunction,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, mvfderiv_apply_eq_mfderiv_apply]
  -- The derivative of `ℝ → AddCircle 1` is the identity of `ℝ`, whose source is the tangent space
  -- of the circle only up to definitional unfolding, so `ContinuousLinearMap.id_apply` does not
  -- rewrite here.
  rfl

include hp in
/-- On the real cover `Q(b, t) = (b, ([t j]_(p j b))ⱼ)`, the time form `η_i` is
`dt_i - (t i / p i b) • d(p i ∘ pr₁)`: the product rule for `t i = p i b * (t i / p i b)`. -/
theorem mpullback_representative_timeForm (i : ι) :
    mpullback (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
        (representative p) (timeForm p IB i (hp i)).val =
      mextDeriv (RoughForm.ofFunction (IB.prod 𝓘(ℝ, ι → ℝ)) fun z : B × (ι → ℝ) ↦ z.2 i) -
        fun z ↦ (z.2 i / (p i z.1 : ℝ)) •
          mextDeriv (RoughForm.ofFunction (IB.prod 𝓘(ℝ, ι → ℝ))
            fun z : B × (ι → ℝ) ↦ (p i z.1 : ℝ)) z := by
  have hper : ContMDiff (IB.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ, ℝ) ∞ fun z : B × (ι → ℝ) ↦ (p i z.1 : ℝ) :=
    (contMDiff_subtypeVal.comp (hp i)).comp contMDiff_fst
  have ht : (fun z : B × (ι → ℝ) ↦ (p i z.1 : ℝ)) * (fun z ↦ z.2 i / (p i z.1 : ℝ)) =
      fun z ↦ z.2 i :=
    funext fun z ↦ by simp [mul_div_cancel₀ _ (p i z.1).property.ne']
  funext z
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  have hv := DFunLike.congr_fun (congrFun (mpullback_representative_angleForm hp i) z) v
  rw [mpullback_apply] at hv
  rw [mpullback_apply, timeForm_apply, hv, base_representative, Pi.sub_apply, ← ht,
    mextDeriv_ofFunction_mul ((hper z).mdifferentiableAt (by simp))
      ((contMDiff_normalizedTime hp i z).mdifferentiableAt (by simp))]
  simp

omit [IsManifold IB ∞ B] in
include hp in
/-- Every form pulled back to the real cover `Q(b, t) = (b, ([t j]_(p j b))ⱼ)` is invariant under
the deck translations `(b, t) ↦ (b, t + (k j * p j b)ⱼ)`, which fix `Q`. For the time forms this is
the invariance of `Q^* η_i = dt_i - (t i / p i b) • d(p i ∘ pr₁)`. -/
theorem mpullback_deck_mpullback_representative {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {l : ℕ} (k : ι → ℤ)
    (φ : RoughForm (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) (TorusFamily p) F l) :
    mpullback (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod 𝓘(ℝ, ι → ℝ))
        (fun z : B × (ι → ℝ) ↦ (z.1, z.2 + fun j ↦ k j * (p j z.1 : ℝ)))
        (mpullback (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
          (representative p) φ) =
      mpullback (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
        (representative p) φ := by
  have hdeck : ContMDiff (IB.prod 𝓘(ℝ, ι → ℝ)) (IB.prod 𝓘(ℝ, ι → ℝ)) ∞
      fun z : B × (ι → ℝ) ↦ (z.1, z.2 + fun j ↦ k j * (p j z.1 : ℝ)) :=
    contMDiff_fst.prodMk (contMDiff_snd.add (contMDiff_pi_module_iff.2 fun j ↦
      contMDiff_const.mul ((contMDiff_subtypeVal.comp (hp j)).comp contMDiff_fst)))
  have hcomp : representative p ∘
      (fun z : B × (ι → ℝ) ↦ (z.1, z.2 + fun j ↦ k j * (p j z.1 : ℝ))) = representative p :=
    funext fun z ↦ representative_add_intCast_mul p z.1 z.2 k
  rw [← mpullback_comp (hdeck.mdifferentiable (by simp))
    ((contMDiff_representative p IB hp).mdifferentiable (by simp)), hcomp]

end RealCover

end TorusFamily

end TauCeti
