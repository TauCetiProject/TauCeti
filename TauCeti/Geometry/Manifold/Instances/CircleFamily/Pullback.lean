/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.CircleFamily

/-!
# Smooth families of circles with varying positive period

For a positive period function `p : B → ℝ_{>0}` on a manifold `B`, the family
`TauCeti.CircleFamily.Pullback p` has the circle `AddCircle (p b)` as its fiber over `b`. It is the
pullback of the total family `TauCeti.CircleFamily` of positive-period circles along `p`.

As for the total family, the topology and smooth structure are transported through an explicit
normalization `N_p (b, x) = (b, D_(p b, 1) x)` to the product `B × AddCircle 1`, where
`D_(p, q) : AddCircle p ≃ AddCircle q` is the rescaling `[t]_p ↦ [(q / p) t]_q`. The construction
needs no regularity of `p`. Each fixed circle `AddCircle (p b)` embeds smoothly with its own smooth
structure, as the fiber of the smooth base projection, and has a smooth retraction from the family.

The family is compatible with the total family: the map `(b, x) ↦ (p b, x)` to
`TauCeti.CircleFamily` is `C^n` when `p` is, and for continuous `p` it identifies the family with
the fiber product of `p` and the period projection
(`TauCeti.CircleFamily.Pullback.fiberProductHomeomorph`). Over the positive periods themselves,
with `p` the identity, it is the total family.

Base change along `f : B' → B` is the map `(b', x) ↦ (f b', x)` from the family of `p ∘ f`; in
normalized coordinates it is `f × id`. So it is smooth, a local diffeomorphism or an open embedding
when `f` is, and it is functorial. Base change along the inclusion of an open subset restricts the
family to the part over that subset.

For two period functions `p` and `q`, the fiberwise rescaling `(b, x) ↦ (b, D_(p b, q b) x)` is a
smooth diffeomorphism of families preserving the normalized angle, with the identity, inverse and
composition laws of the rescalings of single circles, and commutes with base change.

The real representative map `(b, t) ↦ (b, [t]_(p b))` from `B × ℝ` is a covering map when `p` is
continuous, and a `C^n` local diffeomorphism when `p` is `C^n`. Its normalized angle is
`[t / p b]_1`, and it is invariant under the deck translations `t ↦ t + k p b`.

## Main definitions

* `TauCeti.CircleFamily.Pullback p`: the family of the circles `AddCircle (p b)` over `B`.
* `TauCeti.CircleFamily.Pullback.normalization p IB n`: the normalization
  `(b, x) ↦ (b, D_(p b, 1) x)`, a `C^n` diffeomorphism onto `B × AddCircle 1`.
* `TauCeti.CircleFamily.Pullback.toCircleFamily p`: the map `(b, x) ↦ (p b, x)` to the total family.
* `TauCeti.CircleFamily.Pullback.comap p f`: base change along `f`.
* `TauCeti.CircleFamily.Pullback.rescale p q IB n`: the fiberwise rescaling from the periods `p`
  to the periods `q`.
* `TauCeti.CircleFamily.Pullback.representative p`: the real representative map
  `(b, t) ↦ (b, [t]_(p b))`.

## Main results

* `TauCeti.CircleFamily.Pullback.contMDiff_mk`,
  `TauCeti.CircleFamily.Pullback.contMDiff_retraction`,
  `TauCeti.CircleFamily.Pullback.fiberHomeomorph`: each fixed circle is a smooth fiber of the
  family, with a smooth retraction.
* `TauCeti.CircleFamily.Pullback.contMDiff_toCircleFamily`,
  `TauCeti.CircleFamily.Pullback.fiberProductHomeomorph`: comparison with the total family.
* `TauCeti.CircleFamily.Pullback.contMDiff_comap`,
  `TauCeti.CircleFamily.Pullback.isLocalDiffeomorph_comap`,
  `TauCeti.CircleFamily.Pullback.isOpenEmbedding_comap`,
  `TauCeti.CircleFamily.Pullback.range_comap`: regularity and image of base change.
* `TauCeti.CircleFamily.Pullback.rescale_mk`, `TauCeti.CircleFamily.Pullback.rescale_self`,
  `TauCeti.CircleFamily.Pullback.rescale_symm`, `TauCeti.CircleFamily.Pullback.rescale_trans`:
  the fiberwise rescalings.
* `TauCeti.CircleFamily.Pullback.isLocalDiffeomorph_representative`,
  `TauCeti.CircleFamily.Pullback.isCoveringMap_representative`: the real representative map is a
  local diffeomorphism and a covering.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (the angle variables of a family of invariant tori,
  whose periods vary with the action variables).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The family of the circles `AddCircle (p b)` over a base `B`, for a positive period function
`p : B → ℝ_{>0}`: the pullback of the total family `TauCeti.CircleFamily` along `p`. -/
@[ext]
structure CircleFamily.Pullback {B : Type*} (p : B → PositivePeriod) where
  /-- The base point. -/
  base : B
  /-- A point of the circle whose period is the period at the base point. -/
  point : AddCircle (p base : ℝ)

namespace CircleFamily.Pullback

variable {B : Type*} (p : B → PositivePeriod)

/-- Normalize the circle over each base point to the unit-period circle. -/
def normalizationEquiv : Pullback p ≃ B × AddCircle (1 : ℝ) where
  toFun z := (z.base, AddCircle.diffeomorphAddCircle (p z.base : ℝ) 1 ⊤ z.point)
  invFun z := ⟨z.1, (AddCircle.diffeomorphAddCircle (p z.1 : ℝ) 1 ⊤).symm z.2⟩
  left_inv z := by
    rcases z with ⟨b, x⟩
    exact congrArg (mk b) ((AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).symm_apply_apply x)
  right_inv z :=
    Prod.ext rfl ((AddCircle.diffeomorphAddCircle (p z.1 : ℝ) 1 ⊤).apply_symm_apply _)

/-- Normalization keeps the base point and rescales the circle point to period one. -/
@[simp]
theorem normalizationEquiv_apply (z : Pullback p) :
    normalizationEquiv p z =
      (z.base, AddCircle.diffeomorphAddCircle (p z.base : ℝ) 1 ⊤ z.point) := (rfl)

/-- The inverse normalization rescales the unit-period circle back to the period at the base. -/
@[simp]
theorem normalizationEquiv_symm_apply (z : B × AddCircle (1 : ℝ)) :
    (normalizationEquiv p).symm z =
      ⟨z.1, (AddCircle.diffeomorphAddCircle (p z.1 : ℝ) 1 ⊤).symm z.2⟩ := (rfl)

/-- The normalization of a point of the circle over `b` is its rescaling to period one. -/
private theorem normalizationEquiv_mk (b : B) (x : AddCircle (p b : ℝ)) :
    normalizationEquiv p (mk b x) = (b, AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤ x) := (rfl)

/-! ### Fixed fibers -/

/-- Retract the family onto the circle over a fixed base point by keeping the normalized angle. -/
def retraction (b : B) (z : Pullback p) : AddCircle (p b : ℝ) :=
  (AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).symm (normalizationEquiv p z).2

/-- The retraction to the circle over `b` is a left inverse of the inclusion of that circle. -/
@[simp]
theorem retraction_mk (b : B) (x : AddCircle (p b : ℝ)) : retraction p b (mk b x) = x :=
  (AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).symm_apply_apply x

/-- On the fiber over `b`, the inclusion of the circle over `b` is a right inverse of the
retraction. -/
theorem mk_retraction {b : B} {z : Pullback p} (h : z.base = b) : mk b (retraction p b z) = z := by
  subst b
  rcases z with ⟨b, x⟩
  exact congrArg (mk b) (retraction_mk p b x)

/-! ### The total family -/

/-- The map `(b, x) ↦ (p b, x)` from the family of `p` to the total family of positive-period
circles. -/
def toCircleFamily (z : Pullback p) : CircleFamily := ⟨p z.base, z.point⟩

/-- The map to the total family sends the circle over `b` to the circle of period `p b`. -/
@[simp]
theorem toCircleFamily_mk (b : B) (x : AddCircle (p b : ℝ)) :
    toCircleFamily p (mk b x) = CircleFamily.mk (p b) x := (rfl)

/-- The map to the total family covers `p`. -/
@[simp]
theorem period_toCircleFamily (z : Pullback p) : (toCircleFamily p z).period = p z.base := (rfl)

/-- The map to the total family keeps the normalized angle. -/
@[simp]
theorem normalization_toCircleFamily (n : ℕ∞ω) (z : Pullback p) :
    CircleFamily.normalization n (toCircleFamily p z) =
      (p z.base, AddCircle.diffeomorphAddCircle (p z.base : ℝ) 1 ⊤ z.point) :=
  CircleFamily.normalization_mk n (p z.base) z.point

/-- In normalized coordinates, the map to the total family is `p × id`. -/
private theorem toCircleFamily_eq (n : ℕ∞ω) :
    toCircleFamily p =
      (CircleFamily.normalization n).symm ∘ Prod.map p id ∘ normalizationEquiv p := by
  funext z
  rw [Function.comp_apply, Function.comp_apply,
    ← (CircleFamily.normalization n).symm_apply_apply (toCircleFamily p z),
    normalization_toCircleFamily]
  rfl

/-! ### The real representative map -/

/-- The real representative map `(b, t) ↦ (b, [t]_(p b))` of the family. -/
def representative (z : B × ℝ) : Pullback p := ⟨z.1, (z.2 : AddCircle (p z.1 : ℝ))⟩

/-- The real representative map covers the projection to the base. -/
@[simp]
theorem base_representative (z : B × ℝ) : (representative p z).base = z.1 := (rfl)

/-- Every point of the family has a real representative. -/
theorem representative_surjective : Function.Surjective (representative p) := by
  rintro ⟨b, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨(b, t), rfl⟩

/-- The real representative map is invariant under the deck translations `t ↦ t + k p b`. -/
@[simp]
theorem representative_add_intCast_mul (b : B) (t : ℝ) (k : ℤ) :
    representative p (b, t + k * (p b : ℝ)) = representative p (b, t) := by
  simp [representative, ← zsmul_eq_mul]

/-- In normalized coordinates, the representative of `(b, t)` has angle the class of `t / p b` in
the unit circle. -/
private theorem normalizationEquiv_representative (z : B × ℝ) :
    normalizationEquiv p (representative p z) =
      (z.1, ((z.2 / (p z.1 : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  rw [representative, normalizationEquiv_mk, AddCircle.diffeomorphAddCircle_apply_mk]
  simp [div_eq_mul_inv]

/-! ### Base change -/

variable {B' : Type*} (f : B' → B)

/-- **Base change** along `f : B' → B`: the point `x` of the circle over `b'` in the family of
`p ∘ f` is sent to the same point of the same circle, over `f b'`, in the family of `p`. -/
def comap (z : Pullback (p ∘ f)) : Pullback p := ⟨f z.base, z.point⟩

/-- Base change sends the circle over `b'` to the circle over `f b'`. -/
@[simp]
theorem comap_mk (b' : B') (x : AddCircle (p (f b') : ℝ)) :
    comap p f (mk b' x) = mk (f b') x := (rfl)

/-- Base change covers `f`. -/
@[simp]
theorem base_comap (z : Pullback (p ∘ f)) : (comap p f z).base = f z.base := (rfl)

/-- Base change along the identity is the identity. -/
@[simp]
theorem comap_id : comap p (id : B → B) = id := (rfl)

/-- Base change is functorial: base change along `f ∘ g` is base change along `g`, then along
`f`. -/
theorem comap_comp {B'' : Type*} (g : B'' → B') :
    comap p (f ∘ g) = comap p f ∘ comap (p ∘ f) g := (rfl)

/-- In normalized coordinates, base change along `f` is `f × id`. -/
private theorem normalizationEquiv_comap (z : Pullback (p ∘ f)) :
    normalizationEquiv p (comap p f z) = Prod.map f id (normalizationEquiv (p ∘ f) z) := (rfl)

/-- The image of base change is the part of the family over the image of `f`. -/
theorem range_comap : range (comap p f) = base ⁻¹' range f := by
  ext z
  refine ⟨?_, fun ⟨b', hb'⟩ ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w.base, rfl⟩
  · rcases z with ⟨b, x⟩
    subst hb'
    exact ⟨mk b' x, rfl⟩

section Topology

variable [TopologicalSpace B]

instance : TopologicalSpace (Pullback p) :=
  TopologicalSpace.induced (normalizationEquiv p) inferInstance

/-- The topology of the family is the one for which normalization is a homeomorphism. -/
def normalizationHomeomorph : Pullback p ≃ₜ B × AddCircle (1 : ℝ) :=
  (normalizationEquiv p).toHomeomorphOfIsInducing ⟨rfl⟩

instance [T2Space B] : T2Space (Pullback p) := (normalizationHomeomorph p).symm.t2Space

instance [SecondCountableTopology B] : SecondCountableTopology (Pullback p) :=
  (normalizationHomeomorph p).secondCountableTopology

/-- The normalization homeomorphism is the normalization of the circles. -/
private theorem coe_normalizationHomeomorph :
    ⇑(normalizationHomeomorph p) = normalizationEquiv p := (rfl)

/-- The normalization homeomorphism keeps the base point and rescales the circle point to period
one. -/
@[simp]
theorem normalizationHomeomorph_apply (z : Pullback p) :
    normalizationHomeomorph p z =
      (z.base, AddCircle.diffeomorphAddCircle (p z.base : ℝ) 1 ⊤ z.point) := (rfl)

/-- The inverse normalization homeomorphism rescales the unit-period circle back to the period at
the base. -/
@[simp]
theorem normalizationHomeomorph_symm_apply (z : B × AddCircle (1 : ℝ)) :
    (normalizationHomeomorph p).symm z =
      ⟨z.1, (AddCircle.diffeomorphAddCircle (p z.1 : ℝ) 1 ⊤).symm z.2⟩ := (rfl)

/-- A map into the family is continuous when its normalization is. -/
private theorem continuous_of_normalizationEquiv_comp {X : Type*} [TopologicalSpace X]
    {g : X → Pullback p} (hg : Continuous (normalizationEquiv p ∘ g)) : Continuous g := by
  rw [← coe_normalizationHomeomorph] at hg
  exact (normalizationHomeomorph p).comp_continuous_iff.mp hg

/-- The base projection of the family is continuous. -/
theorem continuous_base : Continuous (base : Pullback p → B) :=
  continuous_fst.comp (normalizationHomeomorph p).continuous

/-- The inclusion of the circle over a base point is continuous. -/
theorem continuous_mk (b : B) : Continuous (mk (p := p) b) :=
  continuous_of_normalizationEquiv_comp p
    (continuous_const.prodMk (AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).continuous)

/-- The retraction to the circle over a base point is continuous. -/
theorem continuous_retraction (b : B) : Continuous (retraction p b) :=
  (AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).symm.continuous.comp
    (continuous_snd.comp (normalizationHomeomorph p).continuous)

/-- The circle over a base point is homeomorphic to the subspace fiber of the base projection. -/
def fiberHomeomorph (b : B) : AddCircle (p b : ℝ) ≃ₜ {z : Pullback p // z.base = b} where
  toFun x := ⟨mk b x, rfl⟩
  invFun z := retraction p b z.1
  left_inv := retraction_mk p b
  right_inv z := Subtype.ext (mk_retraction p z.2)
  continuous_toFun := (continuous_mk p b).subtype_mk _
  continuous_invFun := (continuous_retraction p b).comp continuous_subtype_val

/-- The fiber homeomorphism is the inclusion of the circle. -/
@[simp]
theorem coe_fiberHomeomorph (b : B) (x : AddCircle (p b : ℝ)) :
    (fiberHomeomorph p b x).1 = mk b x := (rfl)

/-- The inverse fiber homeomorphism is the retraction restricted to the fiber. -/
@[simp]
theorem fiberHomeomorph_symm_apply (b : B) (z : {z : Pullback p // z.base = b}) :
    (fiberHomeomorph p b).symm z = retraction p b z.1 := (rfl)

/-- The map to the total family is continuous when `p` is. -/
theorem continuous_toCircleFamily (hp : Continuous p) : Continuous (toCircleFamily p) := by
  rw [toCircleFamily_eq p 0, ← coe_normalizationHomeomorph]
  exact (CircleFamily.normalization 0).symm.continuous.comp
    ((hp.prodMap continuous_id).comp (normalizationHomeomorph p).continuous)

/-- **The family of `p` is the fiber product of `p` and the period projection.** For continuous
`p`, the map `z ↦ (z.base, (p z.base, z.point))` is a homeomorphism onto the pairs `(b, w)` of a
base point and a point of the total family whose period is `p b`. -/
def fiberProductHomeomorph (hp : Continuous p) :
    Pullback p ≃ₜ {w : B × CircleFamily // p w.1 = w.2.period} where
  toFun z := ⟨(z.base, toCircleFamily p z), rfl⟩
  invFun w := ⟨w.1.1, CircleFamily.retraction (p w.1.1) w.1.2⟩
  left_inv z := by
    rcases z with ⟨b, x⟩
    exact congrArg (mk b) (CircleFamily.retraction_mk (p b) x)
  right_inv w := Subtype.ext (Prod.ext rfl (CircleFamily.mk_retraction w.2.symm))
  continuous_toFun := ((continuous_base p).prodMk (continuous_toCircleFamily p hp)).subtype_mk _
  continuous_invFun := by
    refine continuous_of_normalizationEquiv_comp p ?_
    -- In normalized coordinates the inverse keeps the base point and the normalized angle of the
    -- point of the total family, which lies on the circle of period `p b`.
    have h : normalizationEquiv p ∘
        (fun w : {w : B × CircleFamily // p w.1 = w.2.period} ↦
          (⟨w.1.1, CircleFamily.retraction (p w.1.1) w.1.2⟩ : Pullback p)) =
        fun w ↦ (w.1.1, (CircleFamily.normalization ⊤ w.1.2).2) := by
      funext w
      refine Prod.ext rfl ?_
      conv_rhs => rw [← CircleFamily.mk_retraction w.2.symm, CircleFamily.normalization_mk]
      rfl
    rw [h]
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp ((CircleFamily.normalization ⊤).continuous.comp
        (continuous_snd.comp continuous_subtype_val)))

/-- The fiber-product homeomorphism records the base point and the image in the total family. -/
@[simp]
theorem coe_fiberProductHomeomorph (hp : Continuous p) (z : Pullback p) :
    (fiberProductHomeomorph p hp z).1 = (z.base, toCircleFamily p z) := (rfl)

/-- For continuous periods, the real representative map is a covering map. In normalized
coordinates it is the quotient map of the unit circle after dividing the time by the period. -/
theorem isCoveringMap_representative (hp : Continuous p) : IsCoveringMap (representative p) := by
  have hpos : ∀ b, (p b : ℝ) ≠ 0 := fun b ↦ (p b).property.ne'
  let g : B × ℝ ≃ₜ B × ℝ :=
    { toFun z := (z.1, z.2 / (p z.1 : ℝ))
      invFun z := (z.1, z.2 * (p z.1 : ℝ))
      left_inv z := by simp [hpos]
      right_inv z := by simp [hpos]
      continuous_toFun := continuous_fst.prodMk
        (continuous_snd.div ((continuous_subtype_val.comp hp).comp continuous_fst)
          fun z ↦ hpos z.1)
      continuous_invFun := continuous_fst.prodMk
        (continuous_snd.mul ((continuous_subtype_val.comp hp).comp continuous_fst)) }
  have h : representative p =
      (normalizationHomeomorph p).symm ∘ Prod.map id ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ g := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, eq_comm, Homeomorph.symm_apply_eq,
      coe_normalizationHomeomorph, normalizationEquiv_representative]
    rfl
  rw [h]
  exact ((IsCoveringMap.id.prodMap (AddCircle.isCoveringMap_coe 1)).comp_homeomorph
    g).homeomorph_comp (normalizationHomeomorph p).symm

/-! ### Continuity of base change -/

variable [TopologicalSpace B']

/-- Base change is continuous along a continuous map. -/
theorem continuous_comap (hf : Continuous f) : Continuous (comap p f) :=
  continuous_of_normalizationEquiv_comp p ((hf.prodMap continuous_id).comp
    (normalizationHomeomorph (p ∘ f)).continuous)

/-- Base change along an open embedding is an open embedding. -/
theorem isOpenEmbedding_comap (hf : IsOpenEmbedding f) : IsOpenEmbedding (comap p f) := by
  have h : comap p f = (normalizationHomeomorph p).symm ∘ Prod.map f id ∘
      normalizationHomeomorph (p ∘ f) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, eq_comm, Homeomorph.symm_apply_eq,
      coe_normalizationHomeomorph, coe_normalizationHomeomorph, normalizationEquiv_comap]
  rw [h]
  exact (normalizationHomeomorph p).symm.isOpenEmbedding.comp
    ((hf.prodMap IsOpenEmbedding.id).comp (normalizationHomeomorph (p ∘ f)).isOpenEmbedding)

/-- **Open restriction.** Over an open subset `U` of the base, base change along the inclusion
identifies the family of `p` restricted to `U` with the open part of the family over `U`. -/
def opensHomeomorph (U : TopologicalSpace.Opens B) :
    Pullback (p ∘ ((↑) : U → B)) ≃ₜ (base ⁻¹' (U : Set B) : Set (Pullback p)) :=
  (isOpenEmbedding_comap p _ U.isOpenEmbedding').isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_comap, Subtype.range_coe]))

/-- The open-restriction homeomorphism is base change along the inclusion. -/
@[simp]
theorem coe_opensHomeomorph (U : TopologicalSpace.Opens B) (z : Pullback (p ∘ ((↑) : U → B))) :
    (opensHomeomorph p U z : Pullback p) = comap p ((↑) : U → B) z := (rfl)

end Topology

section Manifold

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  (IB : ModelWithCorners ℝ EB HB) [TopologicalSpace B] [ChartedSpace HB B]

instance : ChartedSpace (ModelProd HB ℝ) (Pullback p) :=
  (normalizationHomeomorph p).pullbackChartedSpace

instance {n : ℕ∞ω} [IsManifold IB n B] : IsManifold (IB.prod 𝓘(ℝ)) n (Pullback p) :=
  (normalizationHomeomorph p).pullback_isManifold _ n

/-- The normalization `(b, x) ↦ (b, D_(p b, 1) x)` of the family, as a `C^n` diffeomorphism onto
`B × AddCircle 1`. -/
def normalization (n : ℕ∞ω) :
    Pullback p ≃ₘ^n⟮IB.prod 𝓘(ℝ), IB.prod 𝓘(ℝ)⟯ B × AddCircle (1 : ℝ) :=
  { normalizationEquiv p with
    contMDiff_toFun := by
      have h := ((normalizationHomeomorph p).pullbackDiffeomorph (IB.prod 𝓘(ℝ)) n).contMDiff
      rwa [Homeomorph.coe_pullbackDiffeomorph] at h
    contMDiff_invFun := by
      have h := ((normalizationHomeomorph p).pullbackDiffeomorph (IB.prod 𝓘(ℝ)) n).symm.contMDiff
      rwa [Homeomorph.coe_pullbackDiffeomorph_symm] at h }

/-- The normalization diffeomorphism is the normalization of the circles. -/
private theorem coe_normalization (n : ℕ∞ω) :
    ⇑(normalization p IB n) = normalizationEquiv p := by
  unfold normalization
  rfl

/-- Normalization retains the base point. -/
@[simp]
theorem normalization_fst (n : ℕ∞ω) (z : Pullback p) : (normalization p IB n z).1 = z.base := by
  rw [coe_normalization]
  rfl

/-- Normalization rescales the circle point to period one. -/
@[simp]
theorem normalization_snd (n : ℕ∞ω) (z : Pullback p) :
    (normalization p IB n z).2 = AddCircle.diffeomorphAddCircle (p z.base : ℝ) 1 ⊤ z.point := by
  rw [coe_normalization]
  rfl

/-- The inverse normalization rescales the unit-period circle back to the period at the base. -/
@[simp]
theorem normalization_symm_apply (n : ℕ∞ω) (z : B × AddCircle (1 : ℝ)) :
    (normalization p IB n).symm z =
      ⟨z.1, (AddCircle.diffeomorphAddCircle (p z.1 : ℝ) 1 ⊤).symm z.2⟩ := by
  unfold normalization
  rfl

/-- In normalized coordinates, a point of the circle over `b` keeps its base point and is rescaled
to period one. -/
theorem normalization_mk (n : ℕ∞ω) (b : B) (x : AddCircle (p b : ℝ)) :
    normalization p IB n (mk b x) = (b, AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤ x) := by
  rw [coe_normalization, normalizationEquiv_mk]

/-- The base projection of the family is `C^n`. -/
theorem contMDiff_base (n : ℕ∞ω) : ContMDiff (IB.prod 𝓘(ℝ)) IB n (base : Pullback p → B) := by
  simpa only [Function.comp_def, normalization_fst] using
    contMDiff_fst.comp (normalization p IB n).contMDiff

/-- The inclusion of the circle over a base point, with its own smooth structure, is `C^n`. -/
theorem contMDiff_mk (n : ℕ∞ω) (b : B) : ContMDiff 𝓘(ℝ) (IB.prod 𝓘(ℝ)) n (mk (p := p) b) := by
  have h := (normalization p IB n).symm.contMDiff.comp
    ((contMDiff_const (c := b)).prodMk
      ((AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).contMDiff.of_le le_top))
  convert h using 1
  funext x
  simp only [Function.comp_apply, normalization_symm_apply, Diffeomorph.symm_apply_apply]

/-- The retraction to the circle over a base point is `C^n`. -/
theorem contMDiff_retraction (n : ℕ∞ω) (b : B) :
    ContMDiff (IB.prod 𝓘(ℝ)) 𝓘(ℝ) n (retraction p b) := by
  have h := ((AddCircle.diffeomorphAddCircle (p b : ℝ) 1 ⊤).symm.contMDiff.of_le le_top).comp
    (contMDiff_snd.comp (normalization p IB n).contMDiff)
  rwa [coe_normalization] at h

/-- The map to the total family is `C^n` when `p` is. -/
theorem contMDiff_toCircleFamily {n : ℕ∞ω} (hp : ContMDiff IB 𝓘(ℝ) n p) :
    ContMDiff (IB.prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) n (toCircleFamily p) := by
  rw [toCircleFamily_eq p n, ← coe_normalization p IB n]
  exact (CircleFamily.normalization n).symm.contMDiff.comp
    ((hp.prodMap contMDiff_id).comp (normalization p IB n).contMDiff)

/-- Over the positive periods themselves, the family of the identity is the total family: the map
`(p, x) ↦ (p, x)` is a `C^n` diffeomorphism. -/
def diffeomorphCircleFamily (n : ℕ∞ω) :
    Pullback (id : PositivePeriod → PositivePeriod) ≃ₘ^n⟮𝓘(ℝ).prod 𝓘(ℝ), 𝓘(ℝ).prod 𝓘(ℝ)⟯
      CircleFamily :=
  (normalization id 𝓘(ℝ) n).trans (CircleFamily.normalization n).symm

/-- The identification with the total family is the map to the total family. -/
@[simp]
theorem coe_diffeomorphCircleFamily (n : ℕ∞ω) :
    ⇑(diffeomorphCircleFamily n) = toCircleFamily id := by
  rw [toCircleFamily_eq id n, diffeomorphCircleFamily, Diffeomorph.coe_trans, coe_normalization,
    Prod.map_id, Function.id_comp]

/-! ### Smooth base change -/

variable {EB' HB' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B'] {n : ℕ∞ω}

/-- In normalized coordinates, base change along `f` is `f × id`. -/
private theorem comap_eq :
    comap p f = (normalization p IB n).symm ∘ Prod.map f id ∘ normalization (p ∘ f) IB' n := by
  funext z
  rw [Function.comp_apply, Function.comp_apply,
    ← (normalization p IB n).symm_apply_apply (comap p f z), coe_normalization, coe_normalization,
    normalizationEquiv_comap]

/-- Base change along a `C^n` map is `C^n`. -/
theorem contMDiff_comap (hf : ContMDiff IB' IB n f) :
    ContMDiff (IB'.prod 𝓘(ℝ)) (IB.prod 𝓘(ℝ)) n (comap p f) := by
  rw [comap_eq p f IB (IB' := IB') (n := n)]
  exact (normalization p IB n).symm.contMDiff.comp
    ((hf.prodMap contMDiff_id).comp (normalization (p ∘ f) IB' n).contMDiff)

/-- Base change along a `C^n` local diffeomorphism is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_comap (hf : IsLocalDiffeomorph IB' IB n f) :
    IsLocalDiffeomorph (IB'.prod 𝓘(ℝ)) (IB.prod 𝓘(ℝ)) n (comap p f) := by
  rw [comap_eq p f IB (IB' := IB') (n := n)]
  intro z
  have h := hf.prodMap (Diffeomorph.refl 𝓘(ℝ) (AddCircle (1 : ℝ)) n).isLocalDiffeomorph
  exact ((normalization (p ∘ f) IB' n).isLocalDiffeomorph z).comp _ _
    ((h _).comp _ _ ((normalization p IB n).symm.isLocalDiffeomorph _))

/-! ### Fiberwise rescaling -/

/-- The fiberwise rescaling `(b, x) ↦ (b, D_(p b, q b) x)` from the family of the periods `p` to the
family of the periods `q`. It keeps the normalized angle, so it is the normalization of `p`
followed by the inverse normalization of `q`, a `C^n` diffeomorphism. -/
def rescale (q : B → PositivePeriod) (n : ℕ∞ω) :
    Pullback p ≃ₘ^n⟮IB.prod 𝓘(ℝ), IB.prod 𝓘(ℝ)⟯ Pullback q :=
  (normalization p IB n).trans (normalization q IB n).symm

variable (q r : B → PositivePeriod)

/-- The fiberwise rescaling keeps the normalized angle. -/
@[simp]
theorem normalization_rescale (n : ℕ∞ω) (z : Pullback p) :
    normalization q IB n (rescale p IB q n z) = normalization p IB n z := by
  rw [rescale, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply]

/-- The fiberwise rescaling rescales the circle over each base point from period `p b` to period
`q b`. -/
@[simp]
theorem rescale_mk (n : ℕ∞ω) (b : B) (x : AddCircle (p b : ℝ)) :
    rescale p IB q n (mk b x) =
      mk b (AddCircle.diffeomorphAddCircle (p b : ℝ) (q b : ℝ) ⊤ x) := by
  rw [rescale, Diffeomorph.coe_trans, Function.comp_apply, normalization_mk,
    normalization_symm_apply, AddCircle.diffeomorphAddCircle_symm]
  exact congrArg (mk b)
    (DFunLike.congr_fun (AddCircle.diffeomorphAddCircle_trans (p b : ℝ) 1 (q b : ℝ) ⊤) x)

/-- The fiberwise rescaling covers the identity of the base. -/
@[simp]
theorem base_rescale (n : ℕ∞ω) (z : Pullback p) : (rescale p IB q n z).base = z.base := by
  rcases z with ⟨b, x⟩
  rw [rescale_mk]

/-- Rescaling to the same periods is the identity. -/
@[simp]
theorem rescale_self (n : ℕ∞ω) : rescale p IB p n = Diffeomorph.refl (IB.prod 𝓘(ℝ)) _ n :=
  Diffeomorph.self_trans_symm _

/-- The inverse of the rescaling from `p` to `q` is the rescaling from `q` to `p`. -/
@[simp]
theorem rescale_symm (n : ℕ∞ω) : (rescale p IB q n).symm = rescale q IB p n :=
  Diffeomorph.ext fun _ ↦ (rfl)

/-- Rescaling from `p` to `q` and then to `r` is the rescaling from `p` to `r`. -/
@[simp]
theorem rescale_trans (n : ℕ∞ω) :
    (rescale p IB q n).trans (rescale q IB r n) = rescale p IB r n :=
  Diffeomorph.ext fun z ↦ by
    simp only [rescale, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply]

/-- The fiberwise rescaling commutes with base change. -/
theorem comap_rescale (n : ℕ∞ω) (z : Pullback (p ∘ f)) :
    comap q f (rescale (p ∘ f) IB' (q ∘ f) n z) = rescale p IB q n (comap p f z) := by
  rcases z with ⟨b', x⟩
  rw [rescale_mk, comap_mk, comap_mk, rescale_mk]
  rfl

/-! ### Smoothness of the real representative map -/

/-- The normalized angle of the representative of `(b, t)` is the class of `t / p b` in the unit
circle. -/
@[simp]
theorem normalization_representative (n : ℕ∞ω) (z : B × ℝ) :
    normalization p IB n (representative p z) =
      (z.1, ((z.2 / (p z.1 : ℝ) : ℝ) : AddCircle (1 : ℝ))) := by
  rw [coe_normalization, normalizationEquiv_representative]

/-- Normalize real representatives by dividing the time coordinate by the period at the base
point. For `C^n` periods this is a `C^n` diffeomorphism of `B × ℝ`. -/
def realNormalization (hp : ContMDiff IB 𝓘(ℝ) n p) :
    (B × ℝ) ≃ₘ^n⟮IB.prod 𝓘(ℝ), IB.prod 𝓘(ℝ)⟯ B × ℝ where
  toFun z := (z.1, z.2 / (p z.1 : ℝ))
  invFun z := (z.1, z.2 * (p z.1 : ℝ))
  left_inv z := by simp [(p z.1).property.ne']
  right_inv z := by simp [(p z.1).property.ne']
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.div₀
    ((contMDiff_subtype_val.comp hp).comp contMDiff_fst) fun z ↦ (p z.1).property.ne')
  contMDiff_invFun := contMDiff_fst.prodMk
    (contMDiff_snd.mul ((contMDiff_subtype_val.comp hp).comp contMDiff_fst))

/-- Real normalization divides the time coordinate by the period. -/
@[simp]
theorem realNormalization_apply (hp : ContMDiff IB 𝓘(ℝ) n p) (z : B × ℝ) :
    realNormalization p IB hp z = (z.1, z.2 / (p z.1 : ℝ)) := (rfl)

/-- Inverse real normalization multiplies the normalized time by the period. -/
@[simp]
theorem realNormalization_symm_apply (hp : ContMDiff IB 𝓘(ℝ) n p) (z : B × ℝ) :
    (realNormalization p IB hp).symm z = (z.1, z.2 * (p z.1 : ℝ)) := (rfl)

/-- In normalized coordinates, the representative map is the quotient map of the unit circle in
the time coordinate. -/
private theorem representative_eq (hp : ContMDiff IB 𝓘(ℝ) n p) :
    representative p = (normalization p IB n).symm ∘
      Prod.map id ((↑) : ℝ → AddCircle (1 : ℝ)) ∘ realNormalization p IB hp := by
  funext z
  rw [Function.comp_apply, Function.comp_apply,
    ← (normalization p IB n).symm_apply_apply (representative p z), normalization_representative]
  rfl

/-- For `C^n` periods, the real representative map is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_representative (hp : ContMDiff IB 𝓘(ℝ) n p) :
    IsLocalDiffeomorph (IB.prod 𝓘(ℝ)) (IB.prod 𝓘(ℝ)) n (representative p) := by
  rw [representative_eq p IB hp]
  intro z
  have h := (Diffeomorph.refl IB B n).isLocalDiffeomorph.prodMap
    (AddCircle.isLocalDiffeomorph_coe 1 n)
  exact ((realNormalization p IB hp).isLocalDiffeomorph z).comp _ _
    ((h _).comp _ _ ((normalization p IB n).symm.isLocalDiffeomorph _))

/-- For `C^n` periods, the real representative map is `C^n`. -/
theorem contMDiff_representative (hp : ContMDiff IB 𝓘(ℝ) n p) :
    ContMDiff (IB.prod 𝓘(ℝ)) (IB.prod 𝓘(ℝ)) n (representative p) :=
  (isLocalDiffeomorph_representative p IB hp).contMDiff

end Manifold

end CircleFamily.Pullback

end TauCeti
