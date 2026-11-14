/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.CircleFamily.Pullback
public import TauCeti.Geometry.Manifold.ContMDiff.Pi
public import TauCeti.Geometry.Manifold.IsManifold.Pi

/-!
# Smooth families of tori with finitely many varying positive periods

For a finite index type `ι` and positive period functions `p i : B → ℝ_{>0}` on a manifold `B`,
the family `TauCeti.TorusFamily p` has the torus `∀ i, AddCircle (p i b)` as its fiber over `b`.
For a single period function this is the family of circles `TauCeti.CircleFamily.Pullback`; here
the periods of the different factors vary independently.

As for families of circles, the topology and smooth structure are transported through an explicit
normalization `N_p (b, x) = (b, (D_(p i b, 1) (x i))ᵢ)` to the product `B × (ι → AddCircle 1)`,
where `D_(p, q) : AddCircle p ≃ AddCircle q` is the rescaling `[t]_p ↦ [(q / p) t]_q`. The
construction needs no regularity of the period functions. The smooth structure is modelled on
`IB.prod (ModelWithCorners.pi fun _ ↦ 𝓘(ℝ))`, the model of `B` times the product model of the unit
torus. The inclusion of each fixed torus `∀ i, AddCircle (p i b)`, with its product smooth
structure, is smooth, identifies that torus with the fiber of the smooth base projection, and has a
smooth retraction from the family.

The `i`-th coordinate `(b, x) ↦ (b, x i)` (`TauCeti.TorusFamily.coord`) is a smooth map to the
family of circles of `p i`. The family is the fiber product of these circle families over `B`: a
map into it is continuous, or `C^n`, exactly when its base and all its coordinates are
(`TauCeti.TorusFamily.continuous_iff`, `TauCeti.TorusFamily.contMDiff_iff`), and for nonempty `ι`
a point is determined by its coordinates.

Base change along `f : B' → B` is the map `(b', x) ↦ (f b', x)` from the family of the periods
`p i ∘ f`; in normalized coordinates it is `f × id`, so it is smooth, a local diffeomorphism or an
open embedding when `f` is. Base change along the inclusion of an open subset restricts the family
to the part over that subset. For two families of period functions `p` and `q`, the fiberwise
rescaling `(b, x) ↦ (b, (D_(p i b, q i b) (x i))ᵢ)` is a smooth diffeomorphism of families
preserving the normalized angles, with the identity, inverse and composition laws, compatible with
the coordinates and with base change.

## Main definitions

* `TauCeti.TorusFamily p`: the family of the tori `∀ i, AddCircle (p i b)` over `B`.
* `TauCeti.TorusFamily.normalization p IB n`: the normalization
  `(b, x) ↦ (b, (D_(p i b, 1) (x i))ᵢ)`, a `C^n` diffeomorphism onto `B × (ι → AddCircle 1)`.
* `TauCeti.TorusFamily.coord p i`: the `i`-th coordinate, a map to the family of circles of `p i`.
* `TauCeti.TorusFamily.retraction p b`: the retraction onto the torus over `b`.
* `TauCeti.TorusFamily.comap p f`: base change along `f`.
* `TauCeti.TorusFamily.rescale p IB q n`: the fiberwise rescaling from the periods `p` to the
  periods `q`.

## Main results

* `TauCeti.TorusFamily.contMDiff_base`, `TauCeti.TorusFamily.contMDiff_mk`,
  `TauCeti.TorusFamily.contMDiff_retraction`: the base projection, the inclusion of a fixed torus
  and the retraction onto it are smooth.
* `TauCeti.TorusFamily.fiberHomeomorph`: the torus over `b` is homeomorphic to the subspace fiber
  of the base projection.
* `TauCeti.TorusFamily.contMDiff_coord`, `TauCeti.TorusFamily.contMDiffWithinAt_iff`: the
  coordinates are smooth, and a map into the family is `C^n` within a set at a point exactly when
  its base and its coordinates are.
* `TauCeti.TorusFamily.contMDiffWithinAt_comap`, `TauCeti.TorusFamily.isLocalDiffeomorphAt_comap`,
  `TauCeti.TorusFamily.opensHomeomorph`: smooth base change and open restriction.
* `TauCeti.TorusFamily.rescale_mk`, `TauCeti.TorusFamily.rescale_trans`,
  `TauCeti.TorusFamily.coord_rescale`: the fiberwise rescalings.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (families of invariant tori whose periods vary with
  the action variables).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

/-- The family of the tori `∀ i, AddCircle (p i b)` over a base `B`, for finitely many positive
period functions `p i : B → ℝ_{>0}`. -/
@[ext]
structure TorusFamily {B ι : Type*} (p : ι → B → PositivePeriod) where
  /-- The base point. -/
  base : B
  /-- A point of the torus whose periods are the periods at the base point. -/
  point : ∀ i, AddCircle (p i base : ℝ)

namespace TorusFamily

variable {B ι : Type*} (p : ι → B → PositivePeriod)

/-- Normalize the torus over each base point to the unit torus, factor by factor. -/
def normalizationEquiv : TorusFamily p ≃ B × (ι → AddCircle (1 : ℝ)) where
  toFun z := (z.base, fun i ↦ AddCircle.diffeomorphAddCircle (p i z.base : ℝ) 1 ⊤ (z.point i))
  invFun z := ⟨z.1, fun i ↦ (AddCircle.diffeomorphAddCircle (p i z.1 : ℝ) 1 ⊤).symm (z.2 i)⟩
  left_inv z := by
    rcases z with ⟨b, x⟩
    exact congrArg (mk b) (funext fun i ↦
      (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).symm_apply_apply (x i))
  right_inv z := Prod.ext rfl (funext fun i ↦
    (AddCircle.diffeomorphAddCircle (p i z.1 : ℝ) 1 ⊤).apply_symm_apply (z.2 i))

/-- Normalization keeps the base point and rescales each factor to period one. -/
@[simp]
theorem normalizationEquiv_apply (z : TorusFamily p) :
    normalizationEquiv p z =
      (z.base, fun i ↦ AddCircle.diffeomorphAddCircle (p i z.base : ℝ) 1 ⊤ (z.point i)) := (rfl)

/-- The inverse normalization rescales each unit-period factor back to its period at the base. -/
@[simp]
theorem normalizationEquiv_symm_apply (z : B × (ι → AddCircle (1 : ℝ))) :
    (normalizationEquiv p).symm z =
      ⟨z.1, fun i ↦ (AddCircle.diffeomorphAddCircle (p i z.1 : ℝ) 1 ⊤).symm (z.2 i)⟩ := (rfl)

/-! ### Fixed fibers -/

/-- Retract the family onto the torus over a fixed base point by keeping the normalized angles. -/
def retraction (b : B) (z : TorusFamily p) : ∀ i, AddCircle (p i b : ℝ) :=
  fun i ↦ (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).symm ((normalizationEquiv p z).2 i)

/-- The retraction to the torus over `b` is a left inverse of the inclusion of that torus. -/
@[simp]
theorem retraction_mk (b : B) (x : ∀ i, AddCircle (p i b : ℝ)) : retraction p b (mk b x) = x :=
  funext fun i ↦ (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).symm_apply_apply (x i)

/-- On the fiber over `b`, the inclusion of the torus over `b` is a right inverse of the
retraction. -/
theorem mk_retraction {b : B} {z : TorusFamily p} (h : z.base = b) :
    mk b (retraction p b z) = z := by
  subst b
  rcases z with ⟨b, x⟩
  exact congrArg (mk b) (retraction_mk p b x)

/-- The retraction to the torus over `b` rescales each factor from its period at the base point to
its period at `b`. -/
@[simp]
theorem retraction_apply (b : B) (z : TorusFamily p) (i : ι) :
    retraction p b z i =
      AddCircle.diffeomorphAddCircle (p i z.base : ℝ) (p i b : ℝ) ⊤ (z.point i) := by
  rw [retraction, normalizationEquiv_apply, AddCircle.diffeomorphAddCircle_symm]
  exact DFunLike.congr_fun
    (AddCircle.diffeomorphAddCircle_trans (p i z.base : ℝ) 1 (p i b : ℝ) ⊤) (z.point i)

/-! ### Coordinates -/

/-- The `i`-th coordinate `(b, x) ↦ (b, x i)`, from the family of tori to the family of circles of
the `i`-th period function. -/
@[expose] def coord (i : ι) (z : TorusFamily p) : CircleFamily.Pullback (p i) :=
  ⟨z.base, z.point i⟩

/-- The `i`-th coordinate of a point of the torus over `b` is its `i`-th factor, over `b`. -/
@[simp]
theorem coord_mk (i : ι) (b : B) (x : ∀ i, AddCircle (p i b : ℝ)) :
    coord p i (mk b x) = CircleFamily.Pullback.mk b (x i) := (rfl)

/-- The coordinates cover the identity of the base. -/
@[simp]
theorem base_coord (i : ι) (z : TorusFamily p) : (coord p i z).base = z.base := (rfl)

/-- The point of the `i`-th coordinate is the `i`-th factor of the point. -/
@[simp]
theorem point_coord (i : ι) (z : TorusFamily p) : (coord p i z).point = z.point i := (rfl)

/-- For nonempty `ι`, a point of the family is determined by its coordinates. -/
theorem coord_injective [Nonempty ι] :
    Function.Injective fun z : TorusFamily p ↦ (coord p · z) := by
  intro z w h
  have hb : z.base = w.base :=
    congrArg CircleFamily.Pullback.base (congrFun h (Classical.arbitrary ι))
  rcases z with ⟨b, x⟩
  rcases w with ⟨b', y⟩
  subst hb
  refine congrArg (mk b) (funext fun i ↦ ?_)
  have hi := congrFun h i
  simp only [coord_mk, CircleFamily.Pullback.mk.injEq, heq_eq_eq, true_and] at hi
  exact hi

/-! ### Base change -/

variable {B' : Type*} (f : B' → B)

/-- **Base change** along `f : B' → B`: the point `x` of the torus over `b'` in the family of the
periods `p i ∘ f` is sent to the same point of the same torus, over `f b'`, in the family of
`p`. -/
def comap (z : TorusFamily fun i ↦ p i ∘ f) : TorusFamily p := ⟨f z.base, z.point⟩

/-- Base change sends the torus over `b'` to the torus over `f b'`. -/
@[simp]
theorem comap_mk (b' : B') (x : ∀ i, AddCircle (p i (f b') : ℝ)) :
    comap p f (mk b' x) = mk (f b') x := (rfl)

/-- Base change covers `f`. -/
@[simp]
theorem base_comap (z : TorusFamily fun i ↦ p i ∘ f) : (comap p f z).base = f z.base := (rfl)

/-- Base change along the identity is the identity. -/
@[simp]
theorem comap_id : comap p (id : B → B) = id := (rfl)

/-- Base change is functorial: base change along `f ∘ g` is base change along `g`, then along
`f`. -/
theorem comap_comp {B'' : Type*} (g : B'' → B') :
    comap p (f ∘ g) = comap p f ∘ comap (fun i ↦ p i ∘ f) g := (rfl)

/-- Base change commutes with the coordinates. -/
@[simp]
theorem coord_comap (i : ι) (z : TorusFamily fun i ↦ p i ∘ f) :
    coord p i (comap p f z) = CircleFamily.Pullback.comap (p i) f (coord _ i z) := by
  rcases z with ⟨b', x⟩
  exact (CircleFamily.Pullback.comap_mk (p i) f b' (x i)).symm

/-- In normalized coordinates, base change along `f` is `f × id`. -/
private theorem normalizationEquiv_comap (z : TorusFamily fun i ↦ p i ∘ f) :
    normalizationEquiv p (comap p f z) = Prod.map f id (normalizationEquiv _ z) := (rfl)

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

instance : TopologicalSpace (TorusFamily p) :=
  TopologicalSpace.induced (normalizationEquiv p) inferInstance

/-- The topology of the family is the one for which normalization is a homeomorphism. -/
def normalizationHomeomorph : TorusFamily p ≃ₜ B × (ι → AddCircle (1 : ℝ)) :=
  (normalizationEquiv p).toHomeomorphOfIsInducing ⟨rfl⟩

instance [T2Space B] : T2Space (TorusFamily p) := (normalizationHomeomorph p).symm.t2Space

instance [SecondCountableTopology B] [Countable ι] : SecondCountableTopology (TorusFamily p) :=
  (normalizationHomeomorph p).secondCountableTopology

/-- The normalization homeomorphism is the normalization of the tori. -/
private theorem coe_normalizationHomeomorph :
    ⇑(normalizationHomeomorph p) = normalizationEquiv p := (rfl)

/-- The normalization homeomorphism keeps the base point and rescales each factor to period
one. -/
@[simp]
theorem normalizationHomeomorph_apply (z : TorusFamily p) :
    normalizationHomeomorph p z =
      (z.base, fun i ↦ AddCircle.diffeomorphAddCircle (p i z.base : ℝ) 1 ⊤ (z.point i)) := (rfl)

/-- The inverse normalization homeomorphism rescales each unit-period factor back to its period at
the base. -/
@[simp]
theorem normalizationHomeomorph_symm_apply (z : B × (ι → AddCircle (1 : ℝ))) :
    (normalizationHomeomorph p).symm z =
      ⟨z.1, fun i ↦ (AddCircle.diffeomorphAddCircle (p i z.1 : ℝ) 1 ⊤).symm (z.2 i)⟩ := (rfl)

/-- A map into the family is continuous when its normalization is. -/
private theorem continuous_of_normalizationEquiv_comp {X : Type*} [TopologicalSpace X]
    {g : X → TorusFamily p} (hg : Continuous (normalizationEquiv p ∘ g)) : Continuous g := by
  rw [← coe_normalizationHomeomorph] at hg
  exact (normalizationHomeomorph p).comp_continuous_iff.mp hg

/-- The base projection of the family is continuous. -/
theorem continuous_base : Continuous (base : TorusFamily p → B) :=
  continuous_fst.comp (normalizationHomeomorph p).continuous

/-- The inclusion of the torus over a base point is continuous. -/
theorem continuous_mk (b : B) : Continuous (mk (p := p) b) :=
  continuous_of_normalizationEquiv_comp p (continuous_const.prodMk (continuous_pi fun i ↦
    (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).continuous.comp (continuous_apply i)))

/-- The retraction to the torus over a base point is continuous. -/
theorem continuous_retraction (b : B) : Continuous (retraction p b) :=
  continuous_pi fun i ↦ (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).symm.continuous.comp
    ((continuous_apply i).comp (continuous_snd.comp (normalizationHomeomorph p).continuous))

/-- The torus over a base point is homeomorphic to the subspace fiber of the base projection. -/
def fiberHomeomorph (b : B) :
    (∀ i, AddCircle (p i b : ℝ)) ≃ₜ {z : TorusFamily p // z.base = b} where
  toFun x := ⟨mk b x, rfl⟩
  invFun z := retraction p b z.1
  left_inv := retraction_mk p b
  right_inv z := Subtype.ext (mk_retraction p z.2)
  continuous_toFun := (continuous_mk p b).subtype_mk _
  continuous_invFun := (continuous_retraction p b).comp continuous_subtype_val

/-- The fiber homeomorphism is the inclusion of the torus. -/
@[simp]
theorem coe_fiberHomeomorph (b : B) (x : ∀ i, AddCircle (p i b : ℝ)) :
    (fiberHomeomorph p b x).1 = mk b x := (rfl)

/-- The inverse fiber homeomorphism is the retraction restricted to the fiber. -/
@[simp]
theorem fiberHomeomorph_symm_apply (b : B) (z : {z : TorusFamily p // z.base = b}) :
    (fiberHomeomorph p b).symm z = retraction p b z.1 := (rfl)

/-- In normalized coordinates, the `i`-th coordinate keeps the base point and the `i`-th
normalized angle. -/
private theorem normalizationHomeomorph_comp_coord (i : ι) :
    CircleFamily.Pullback.normalizationHomeomorph (p i) ∘ coord p i =
      (fun w ↦ (w.1, w.2 i)) ∘ normalizationHomeomorph p :=
  funext fun z ↦ by simp [coord]

/-- The coordinates of the family are continuous. -/
theorem continuous_coord (i : ι) : Continuous (coord p i) := by
  refine (CircleFamily.Pullback.normalizationHomeomorph (p i)).comp_continuous_iff.mp ?_
  rw [normalizationHomeomorph_comp_coord]
  exact (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)).comp
    (normalizationHomeomorph p).continuous

section ContinuousIff

variable {X : Type*} [TopologicalSpace X] {g : X → TorusFamily p} {s : Set X} {x : X}

/-- A map into the family is continuous within a set at a point exactly when its base and all its
coordinates are: the family is the fiber product of the families of circles of its period
functions. -/
theorem continuousWithinAt_iff :
    ContinuousWithinAt g s x ↔
      ContinuousWithinAt (base ∘ g) s x ∧ ∀ i, ContinuousWithinAt (coord p i ∘ g) s x := by
  refine ⟨fun hg ↦ ⟨(continuous_base p).continuousAt.comp_continuousWithinAt hg,
    fun i ↦ (continuous_coord p i).continuousAt.comp_continuousWithinAt hg⟩, fun ⟨hb, hc⟩ ↦ ?_⟩
  have h : normalizationHomeomorph p ∘ g = fun x ↦ ((base ∘ g) x,
      fun i ↦ (CircleFamily.Pullback.normalizationHomeomorph (p i) ((coord p i ∘ g) x)).2) :=
    funext fun x ↦ by simp [coord]
  rw [(normalizationHomeomorph p).comp_continuousWithinAt_iff, h]
  exact hb.prodMk (continuousWithinAt_pi.2 fun i ↦
    ((continuous_snd.comp (CircleFamily.Pullback.normalizationHomeomorph (p i)).continuous).tendsto
      _).comp (hc i))

/-- A map into the family is continuous at a point exactly when its base and all its coordinates
are. -/
theorem continuousAt_iff :
    ContinuousAt g x ↔ ContinuousAt (base ∘ g) x ∧ ∀ i, ContinuousAt (coord p i ∘ g) x := by
  simp only [← continuousWithinAt_univ, TorusFamily.continuousWithinAt_iff]

/-- A map into the family is continuous on a set exactly when its base and all its coordinates
are. -/
theorem continuousOn_iff :
    ContinuousOn g s ↔ ContinuousOn (base ∘ g) s ∧ ∀ i, ContinuousOn (coord p i ∘ g) s := by
  simp only [ContinuousOn, TorusFamily.continuousWithinAt_iff]
  exact ⟨fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun i x hx ↦ (h x hx).2 i⟩,
    fun h x hx ↦ ⟨h.1 x hx, fun i ↦ h.2 i x hx⟩⟩

/-- A map into the family is continuous exactly when its base and all its coordinates are: the
family is the fiber product of the families of circles of its period functions. -/
theorem continuous_iff :
    Continuous g ↔ Continuous (base ∘ g) ∧ ∀ i, Continuous (coord p i ∘ g) := by
  simp only [← continuousOn_univ, TorusFamily.continuousOn_iff]

end ContinuousIff

/-! ### Continuity of base change -/

variable [TopologicalSpace B']

/-- Base change is continuous within the part of the family over `s` at a point over which `f` is
continuous within `s`. -/
theorem continuousWithinAt_comap {s : Set B'} {z : TorusFamily fun i ↦ p i ∘ f}
    (hf : ContinuousWithinAt f s z.base) : ContinuousWithinAt (comap p f) (base ⁻¹' s) z := by
  have h : normalizationHomeomorph p ∘ comap p f =
      fun w ↦ (f w.base, (normalizationHomeomorph _ w).2) := (rfl)
  rw [(normalizationHomeomorph p).comp_continuousWithinAt_iff, h]
  exact (hf.comp (continuous_base _).continuousWithinAt (mapsTo_preimage _ _)).prodMk
    (continuous_snd.comp (normalizationHomeomorph _).continuous).continuousWithinAt

/-- Base change is continuous at a point over which `f` is continuous. -/
theorem continuousAt_comap {z : TorusFamily fun i ↦ p i ∘ f} (hf : ContinuousAt f z.base) :
    ContinuousAt (comap p f) z := by
  rw [← continuousWithinAt_univ] at hf ⊢
  simpa only [preimage_univ] using continuousWithinAt_comap p f hf

/-- Base change is continuous on the part of the family over a set on which `f` is continuous. -/
theorem continuousOn_comap {s : Set B'} (hf : ContinuousOn f s) :
    ContinuousOn (comap p f) (base ⁻¹' s) :=
  fun _ hz ↦ continuousWithinAt_comap p f (hf _ hz)

/-- Base change is continuous along a continuous map. -/
theorem continuous_comap (hf : Continuous f) : Continuous (comap p f) :=
  continuous_iff_continuousAt.2 fun _ ↦ continuousAt_comap p f hf.continuousAt

/-- Base change along an open embedding is an open embedding. -/
theorem isOpenEmbedding_comap (hf : IsOpenEmbedding f) : IsOpenEmbedding (comap p f) := by
  have h : comap p f = (normalizationHomeomorph p).symm ∘ Prod.map f id ∘
      normalizationHomeomorph (fun i ↦ p i ∘ f) := by
    funext z
    rw [Function.comp_apply, Function.comp_apply, eq_comm, Homeomorph.symm_apply_eq,
      coe_normalizationHomeomorph, coe_normalizationHomeomorph, normalizationEquiv_comap]
  rw [h]
  exact (normalizationHomeomorph p).symm.isOpenEmbedding.comp
    ((hf.prodMap IsOpenEmbedding.id).comp (normalizationHomeomorph _).isOpenEmbedding)

/-- **Open restriction.** Over an open subset `U` of the base, base change along the inclusion
identifies the family of `p` restricted to `U` with the open part of the family over `U`. -/
def opensHomeomorph (U : TopologicalSpace.Opens B) :
    TorusFamily (fun i ↦ p i ∘ ((↑) : U → B)) ≃ₜ (base ⁻¹' (U : Set B) : Set (TorusFamily p)) :=
  (isOpenEmbedding_comap p _ U.isOpenEmbedding').isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_comap, Subtype.range_coe]))

/-- The open-restriction homeomorphism is base change along the inclusion. -/
@[simp]
theorem coe_opensHomeomorph (U : TopologicalSpace.Opens B)
    (z : TorusFamily fun i ↦ p i ∘ ((↑) : U → B)) :
    (opensHomeomorph p U z : TorusFamily p) = comap p ((↑) : U → B) z := (rfl)

end Topology

section Manifold

variable [Fintype ι] {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] (IB : ModelWithCorners ℝ EB HB) [TopologicalSpace B] [ChartedSpace HB B]

instance : ChartedSpace (ModelProd HB (ModelPi fun _ : ι ↦ ℝ)) (TorusFamily p) :=
  (normalizationHomeomorph p).pullbackChartedSpace

instance {n : ℕ∞ω} [IsManifold IB n B] :
    IsManifold (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (TorusFamily p) :=
  (normalizationHomeomorph p).pullback_isManifold _ n

/-- The normalization `(b, x) ↦ (b, (D_(p i b, 1) (x i))ᵢ)` of the family, as a `C^n`
diffeomorphism onto `B × (ι → AddCircle 1)`. -/
def normalization (n : ℕ∞ω) :
    TorusFamily p ≃ₘ^n⟮IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)),
      IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))⟯ B × (ι → AddCircle (1 : ℝ)) :=
  { normalizationEquiv p with
    contMDiff_toFun := by
      have h := ((normalizationHomeomorph p).pullbackDiffeomorph
        (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n).contMDiff
      rwa [Homeomorph.coe_pullbackDiffeomorph] at h
    contMDiff_invFun := by
      have h := ((normalizationHomeomorph p).pullbackDiffeomorph
        (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n).symm.contMDiff
      rwa [Homeomorph.coe_pullbackDiffeomorph_symm] at h }

/-- The normalization diffeomorphism is the normalization of the tori. -/
private theorem coe_normalization (n : ℕ∞ω) :
    ⇑(normalization p IB n) = normalizationEquiv p := by
  unfold normalization
  rfl

/-- Normalization retains the base point. -/
@[simp]
theorem normalization_fst (n : ℕ∞ω) (z : TorusFamily p) :
    (normalization p IB n z).1 = z.base := by
  rw [coe_normalization]
  rfl

/-- Normalization rescales each factor to period one. -/
@[simp]
theorem normalization_snd (n : ℕ∞ω) (z : TorusFamily p) :
    (normalization p IB n z).2 =
      fun i ↦ AddCircle.diffeomorphAddCircle (p i z.base : ℝ) 1 ⊤ (z.point i) := by
  rw [coe_normalization]
  rfl

/-- The inverse normalization rescales each unit-period factor back to its period at the base. -/
@[simp]
theorem normalization_symm_apply (n : ℕ∞ω) (z : B × (ι → AddCircle (1 : ℝ))) :
    (normalization p IB n).symm z =
      ⟨z.1, fun i ↦ (AddCircle.diffeomorphAddCircle (p i z.1 : ℝ) 1 ⊤).symm (z.2 i)⟩ := by
  unfold normalization
  rfl

/-- In normalized coordinates, a point of the torus over `b` keeps its base point and each factor
is rescaled to period one. -/
@[simp]
theorem normalization_mk (n : ℕ∞ω) (b : B) (x : ∀ i, AddCircle (p i b : ℝ)) :
    normalization p IB n (mk b x) =
      (b, fun i ↦ AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤ (x i)) := by
  rw [coe_normalization, normalizationEquiv_apply]

omit [Fintype ι] in
/-- In normalized coordinates, the `i`-th coordinate of a point keeps its base point and its
`i`-th factor, rescaled to period one. -/
@[simp]
theorem normalization_coord (n : ℕ∞ω) (i : ι) (z : TorusFamily p) :
    CircleFamily.Pullback.normalization (p i) IB n (coord p i z) =
      (z.base, AddCircle.diffeomorphAddCircle (p i z.base : ℝ) 1 ⊤ (z.point i)) :=
  CircleFamily.Pullback.normalization_mk (p i) IB n z.base (z.point i)

/-- In normalized coordinates, the base change of a point lies over the image of its base point,
with the same factors rescaled to period one. -/
@[simp]
theorem normalization_comap (n : ℕ∞ω) (z : TorusFamily fun i ↦ p i ∘ f) :
    normalization p IB n (comap p f z) =
      (f z.base, fun i ↦ AddCircle.diffeomorphAddCircle (p i (f z.base) : ℝ) 1 ⊤ (z.point i)) := by
  rw [coe_normalization]
  rfl

/-- The base projection of the family is `C^n`. -/
theorem contMDiff_base (n : ℕ∞ω) :
    ContMDiff (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) IB n
      (base : TorusFamily p → B) := by
  simpa only [Function.comp_def, normalization_fst] using
    contMDiff_fst.comp (normalization p IB n).contMDiff

/-- The inclusion of the torus over a base point, with its own product smooth structure, is
`C^n`. -/
theorem contMDiff_mk (n : ℕ∞ω) (b : B) :
    ContMDiff (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (mk (p := p) b) := by
  have h := (normalization p IB n).symm.contMDiff.comp ((contMDiff_const (c := b)).prodMk
    (ContMDiff.piMap fun i ↦
      (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).contMDiff.of_le le_top))
  convert h using 1
  funext x
  simp only [Function.comp_apply, normalization_symm_apply, Pi.map_apply,
    Diffeomorph.symm_apply_apply]

/-- The retraction to the torus over a base point is `C^n`. -/
theorem contMDiff_retraction (n : ℕ∞ω) (b : B) :
    ContMDiff (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) n (retraction p b) := by
  have h := (ContMDiff.piMap fun i ↦
      (AddCircle.diffeomorphAddCircle (p i b : ℝ) 1 ⊤).symm.contMDiff.of_le le_top).comp
    (contMDiff_snd.comp (normalization p IB n).contMDiff)
  rwa [coe_normalization] at h

/-- In normalized coordinates, the `i`-th coordinate keeps the base point and the `i`-th
normalized angle. -/
private theorem coord_eq (n : ℕ∞ω) (i : ι) :
    coord p i = (CircleFamily.Pullback.normalization (p i) IB n).symm ∘
      Prod.map id (fun x : ι → AddCircle (1 : ℝ) ↦ x i) ∘ normalization p IB n := by
  funext z
  rcases z with ⟨b, x⟩
  rw [Function.comp_apply, Function.comp_apply,
    ← (CircleFamily.Pullback.normalization (p i) IB n).symm_apply_apply (coord p i (mk b x))]
  congr 1
  ext
  · simp
  · simp [CircleFamily.Pullback.normalization_mk, normalization_mk]

/-- The coordinates of the family are `C^n`. -/
theorem contMDiff_coord (n : ℕ∞ω) (i : ι) :
    ContMDiff (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) (IB.prod 𝓘(ℝ)) n (coord p i) := by
  rw [coord_eq p IB n i]
  exact (CircleFamily.Pullback.normalization (p i) IB n).symm.contMDiff.comp
    ((contMDiff_id.prodMap contMDiff_apply).comp (normalization p IB n).contMDiff)

section ContMDiffIff

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X] {n : ℕ∞ω}
  {g : X → TorusFamily p} {s : Set X} {x : X}

/-- A map into the family is `C^n` within a set at a point exactly when its base and all its
coordinates are: the family is the fiber product of the families of circles of its period
functions. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt IX (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n g s x ↔
      ContMDiffWithinAt IX IB n (base ∘ g) s x ∧
        ∀ i, ContMDiffWithinAt IX (IB.prod 𝓘(ℝ)) n (coord p i ∘ g) s x := by
  refine ⟨fun hg ↦ ⟨(contMDiff_base p IB n).contMDiffAt.comp_contMDiffWithinAt x hg,
    fun i ↦ (contMDiff_coord p IB n i).contMDiffAt.comp_contMDiffWithinAt x hg⟩,
    fun ⟨hb, hc⟩ ↦ ?_⟩
  have h : normalization p IB n ∘ g = fun x ↦ ((base ∘ g) x,
      fun i ↦ (CircleFamily.Pullback.normalization (p i) IB n ((coord p i ∘ g) x)).2) := by
    funext x
    ext <;> simp
  rw [← (normalization p IB n).contMDiffWithinAt_diffeomorph_comp_iff le_rfl, h]
  exact hb.prodMk (contMDiffWithinAt_pi_iff.2 fun i ↦ contMDiffAt_snd.comp_contMDiffWithinAt x
    ((CircleFamily.Pullback.normalization (p i) IB n).contMDiffAt.comp_contMDiffWithinAt x
      (hc i)))

/-- A map into the family is `C^n` at a point exactly when its base and all its coordinates
are. -/
theorem contMDiffAt_iff :
    ContMDiffAt IX (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n g x ↔
      ContMDiffAt IX IB n (base ∘ g) x ∧
        ∀ i, ContMDiffAt IX (IB.prod 𝓘(ℝ)) n (coord p i ∘ g) x := by
  simp only [← contMDiffWithinAt_univ, TorusFamily.contMDiffWithinAt_iff]

/-- A map into the family is `C^n` on a set exactly when its base and all its coordinates are. -/
theorem contMDiffOn_iff :
    ContMDiffOn IX (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n g s ↔
      ContMDiffOn IX IB n (base ∘ g) s ∧
        ∀ i, ContMDiffOn IX (IB.prod 𝓘(ℝ)) n (coord p i ∘ g) s := by
  simp only [ContMDiffOn, TorusFamily.contMDiffWithinAt_iff]
  exact ⟨fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun i x hx ↦ (h x hx).2 i⟩,
    fun h x hx ↦ ⟨h.1 x hx, fun i ↦ h.2 i x hx⟩⟩

/-- A map into the family is `C^n` exactly when its base and all its coordinates are: the family is
the fiber product of the families of circles of its period functions. -/
theorem contMDiff_iff :
    ContMDiff IX (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n g ↔
      ContMDiff IX IB n (base ∘ g) ∧ ∀ i, ContMDiff IX (IB.prod 𝓘(ℝ)) n (coord p i ∘ g) := by
  simp only [← contMDiffOn_univ, TorusFamily.contMDiffOn_iff]

end ContMDiffIff

/-! ### Smooth base change -/

variable {EB' HB' : Type*} [NormedAddCommGroup EB'] [NormedSpace ℝ EB'] [TopologicalSpace HB']
  {IB' : ModelWithCorners ℝ EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B'] {n : ℕ∞ω}

/-- In normalized coordinates, base change along `f` is `f × id`. -/
private theorem comap_eq :
    comap p f = (normalization p IB n).symm ∘ Prod.map f id ∘
      normalization (fun i ↦ p i ∘ f) IB' n := by
  funext z
  rw [Function.comp_apply, Function.comp_apply,
    ← (normalization p IB n).symm_apply_apply (comap p f z), coe_normalization, coe_normalization,
    normalizationEquiv_comap]

/-- Base change is `C^n` within the part of the family over `s` at a point over which `f` is `C^n`
within `s`. -/
theorem contMDiffWithinAt_comap {s : Set B'} {z : TorusFamily fun i ↦ p i ∘ f}
    (hf : ContMDiffWithinAt IB' IB n f s z.base) :
    ContMDiffWithinAt (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) (base ⁻¹' s) z := by
  have h : normalization p IB n ∘ comap p f =
      fun w ↦ (f w.base, (normalization _ IB' n w).2) := by
    funext w
    simp
  rw [← (normalization p IB n).contMDiffWithinAt_diffeomorph_comp_iff le_rfl, h]
  exact (hf.comp z (contMDiff_base _ IB' n z).contMDiffWithinAt (mapsTo_preimage _ _)).prodMk
    (contMDiff_snd.comp (normalization _ IB' n).contMDiff z).contMDiffWithinAt

/-- Base change is `C^n` at a point over which `f` is `C^n`. -/
theorem contMDiffAt_comap {z : TorusFamily fun i ↦ p i ∘ f} (hf : ContMDiffAt IB' IB n f z.base) :
    ContMDiffAt (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) z := by
  rw [← contMDiffWithinAt_univ] at hf ⊢
  simpa only [preimage_univ] using contMDiffWithinAt_comap p f IB hf

/-- Base change is `C^n` on the part of the family over a set on which `f` is `C^n`. -/
theorem contMDiffOn_comap {s : Set B'} (hf : ContMDiffOn IB' IB n f s) :
    ContMDiffOn (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) (base ⁻¹' s) :=
  fun _ hz ↦ contMDiffWithinAt_comap p f IB (hf _ hz)

/-- Base change along a `C^n` map is `C^n`. -/
theorem contMDiff_comap (hf : ContMDiff IB' IB n f) :
    ContMDiff (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) :=
  fun _ ↦ contMDiffAt_comap p f IB (hf _)

/-- Base change is a `C^n` local diffeomorphism at a point over which `f` is one. -/
theorem isLocalDiffeomorphAt_comap {z : TorusFamily fun i ↦ p i ∘ f}
    (hf : IsLocalDiffeomorphAt IB' IB n f z.base) :
    IsLocalDiffeomorphAt (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) z := by
  rw [comap_eq p f IB (IB' := IB') (n := n)]
  have h := hf.prodMap ((Diffeomorph.refl (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))
    (ι → AddCircle (1 : ℝ)) n).isLocalDiffeomorph (normalization _ IB' n z).2)
  rw [← normalization_fst _ IB' n z] at h
  exact ((normalization _ IB' n).isLocalDiffeomorph z).comp _ _
    (h.comp _ _ ((normalization p IB n).symm.isLocalDiffeomorph _))

/-- Base change is a `C^n` local diffeomorphism on the part of the family over a set on which `f`
is one. -/
theorem isLocalDiffeomorphOn_comap {s : Set B'} (hf : IsLocalDiffeomorphOn IB' IB n f s) :
    IsLocalDiffeomorphOn (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) (base ⁻¹' s) :=
  fun z ↦ isLocalDiffeomorphAt_comap p f IB (hf ⟨z.1.base, z.2⟩)

/-- Base change along a `C^n` local diffeomorphism is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_comap (hf : IsLocalDiffeomorph IB' IB n f) :
    IsLocalDiffeomorph (IB'.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)))
      (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) n (comap p f) :=
  fun z ↦ isLocalDiffeomorphAt_comap p f IB (hf z.base)

/-! ### Fiberwise rescaling -/

/-- The fiberwise rescaling `(b, x) ↦ (b, (D_(p i b, q i b) (x i))ᵢ)` from the family of the periods
`p` to the family of the periods `q`. It keeps the normalized angles, so it is the normalization of
`p` followed by the inverse normalization of `q`, a `C^n` diffeomorphism. -/
def rescale (q : ι → B → PositivePeriod) (n : ℕ∞ω) :
    TorusFamily p ≃ₘ^n⟮IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)),
      IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))⟯ TorusFamily q :=
  (normalization p IB n).trans (normalization q IB n).symm

variable (q r : ι → B → PositivePeriod)

/-- The fiberwise rescaling keeps the normalized angles. -/
@[simp]
theorem normalization_rescale (n : ℕ∞ω) (z : TorusFamily p) :
    normalization q IB n (rescale p IB q n z) = normalization p IB n z := by
  rw [rescale, Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.apply_symm_apply]

/-- The fiberwise rescaling rescales the `i`-th factor of the torus over each base point from
period `p i b` to period `q i b`. -/
@[simp]
theorem rescale_mk (n : ℕ∞ω) (b : B) (x : ∀ i, AddCircle (p i b : ℝ)) :
    rescale p IB q n (mk b x) =
      mk b fun i ↦ AddCircle.diffeomorphAddCircle (p i b : ℝ) (q i b : ℝ) ⊤ (x i) := by
  rw [rescale, Diffeomorph.coe_trans, Function.comp_apply, normalization_mk,
    normalization_symm_apply]
  refine congrArg (mk b) (funext fun i ↦ ?_)
  rw [AddCircle.diffeomorphAddCircle_symm]
  exact DFunLike.congr_fun (AddCircle.diffeomorphAddCircle_trans (p i b : ℝ) 1 (q i b : ℝ) ⊤) (x i)

/-- The fiberwise rescaling covers the identity of the base. -/
@[simp]
theorem base_rescale (n : ℕ∞ω) (z : TorusFamily p) : (rescale p IB q n z).base = z.base := by
  rcases z with ⟨b, x⟩
  rw [rescale_mk]

/-- The fiberwise rescaling acts on each coordinate as the rescaling of the family of circles. -/
@[simp]
theorem coord_rescale (n : ℕ∞ω) (i : ι) (z : TorusFamily p) :
    coord q i (rescale p IB q n z) =
      CircleFamily.Pullback.rescale (p i) IB (q i) n (coord p i z) := by
  rcases z with ⟨b, x⟩
  rw [rescale_mk, coord_mk, coord_mk, CircleFamily.Pullback.rescale_mk]

/-- Rescaling to the same periods is the identity. -/
@[simp]
theorem rescale_self (n : ℕ∞ω) :
    rescale p IB p n = Diffeomorph.refl (IB.prod (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ))) _ n :=
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
theorem comap_rescale (n : ℕ∞ω) (z : TorusFamily fun i ↦ p i ∘ f) :
    comap q f (rescale (fun i ↦ p i ∘ f) IB' (fun i ↦ q i ∘ f) n z) =
      rescale p IB q n (comap p f z) := by
  rcases z with ⟨b', x⟩
  rw [rescale_mk, comap_mk, comap_mk, rescale_mk]
  rfl

end Manifold

end TorusFamily

end TauCeti
