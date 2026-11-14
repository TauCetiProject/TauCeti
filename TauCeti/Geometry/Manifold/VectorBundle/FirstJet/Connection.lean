/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# A connection splits the first-jet sequence

Let `V → M` be a `C^1` vector bundle of finite rank. Its first jets fit into the exact sequence

`0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0`

of `TauCeti.FirstJetBundle.ofDeriv` and `TauCeti.FirstJetBundle.value`, which has no canonical
splitting. A covariant derivative `∇` on `V` gives one: the value `∇s(x)` of `∇` on a section `s`
differentiable at `x` depends only on the first jet `j¹s(x)`, so `∇` is a linear map
`J¹Vₓ → Hom(TₓM, Vₓ)`, and this map is a left inverse of `ofDeriv`.

In the chart and the trivialization of `V` at `x`, a first jet is a pair `(v, A)` of a value and a
chart derivative, and the flat derivative of the trivialization sends the jet of `s` to the
derivative coordinate of `j¹s(x)`. The covariant derivative `∇` differs from this flat derivative
by its Christoffel form `Γₓ`, a tensor, so `∇` is `(v, A) ↦ A + Γₓ v` read through the
trivialization.

## Main definitions and results

* `TauCeti.FirstJetBundle.covariantDerivative`: the linear map `J¹Vₓ → Hom(TₓM, Vₓ)` induced by a
  covariant derivative over a set containing `x`, with
  `TauCeti.FirstJetBundle.covariantDerivative_jet`: it sends `j¹s(x)` to `∇s(x)`. Consequently
  `∇s(x)` depends only on the first jet of `s` at `x`
  (`TauCeti.FirstJetBundle.covariantDerivative_eq_of_jet_eq`). Since every first jet is the first
  jet of such a section, this property characterizes it
  (`TauCeti.FirstJetBundle.eq_covariantDerivative_iff`). In coordinates it sends `(w, A)` to `A`
  plus the covariant derivative of the section with constant coordinates `w`
  (`TauCeti.FirstJetBundle.covariantDerivative_apply`).
* `TauCeti.FirstJetBundle.covariantDerivative_comp_ofDeriv`: it is a left inverse of the inclusion
  `Hom(TₓM, Vₓ) → J¹Vₓ`, so it splits the first-jet sequence.
* `TauCeti.FirstJetBundle.horizontalLift`: the corresponding right inverse `Vₓ → J¹Vₓ` of the
  projection, whose image is the kernel of the covariant derivative, and
  `TauCeti.FirstJetBundle.connectionEquiv`: the resulting isomorphism
  `J¹Vₓ ≃ Vₓ × Hom(TₓM, Vₓ)`, `j ↦ (value j, ∇ j)`, which sends `j¹s(x)` to `(s x, ∇s(x))`
  (`TauCeti.FirstJetBundle.connectionEquiv_jet`). A first jet is a horizontal lift exactly when
  its covariant derivative vanishes (`TauCeti.FirstJetBundle.eq_horizontalLift_iff`,
  `TauCeti.FirstJetBundle.jet_eq_horizontalLift_iff`), and
  `TauCeti.FirstJetBundle.horizontalLift_apply` gives the horizontal lift in coordinates.
* `TauCeti.FirstJetBundle.covariantDerivative_add_one_form` and
  `TauCeti.FirstJetBundle.covariantDerivative_sub_covariantDerivative`: changing the covariant
  derivative by an endomorphism-valued one-form `A` changes the derivative coordinate of the
  splitting by `A` applied to the value coordinate; in particular two covariant derivatives give
  splittings that differ by their difference tensor applied to the value. Correspondingly
  `TauCeti.FirstJetBundle.horizontalLift_add_one_form` and
  `TauCeti.FirstJetBundle.horizontalLift_sub_horizontalLift` change the horizontal lift of `v` by
  minus the jet of `A x v`, respectively of the difference tensor applied to `v`.
* `TauCeti.FirstJetBundle.connectionEquiv_trivial_jet` and
  `TauCeti.FirstJetBundle.connectionEquiv_add_one_form_trivial_jet`: on a trivial bundle, the
  canonical flat connection `d` and the connection `d + A` decompose the first jet of a section
  `σ` as `(σ x, dσ(x))` and `(σ x, dσ(x) + A (σ x))`.

For instance, on the trivial line bundle over `ℝ` the jet of the constant section `1` is sent to
`0` by the flat derivative `d` and to `a` by `d + a dt`, while its value stays `1`
(`TauCeti.FirstJetBundle.connectionEquiv_trivial_jet_const` and
`TauCeti.FirstJetBundle.connectionEquiv_add_one_form_trivial_jet_const`).

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*, §17
  (connections and first jets).
* D. J. Saunders, *The Geometry of Jet Bundles*, London Math. Soc. Lecture Note Series 142,
  Chapter 4.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4 (locality of
  covariant derivatives and connections on trivial bundles).
-/

public section

noncomputable section

open Bundle FiberBundle Set Filter
open scoped Manifold Topology

namespace TauCeti

namespace FirstJetBundle

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle 1 F V I]
  {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)} {U : Set M} {x : M}

/-! ### The flat derivative of the trivialization at a point -/

/-- The flat covariant derivative of the trivialization at `x` sends a section differentiable at
`x` to the derivative coordinate of its first jet at `x`, read back through the trivialization. -/
private theorem frameCovariantDerivative_eq_symmL_comp_jet_snd {s : Π x : M, V x}
    (hs : MDiffAt (T% s) x) :
    Manifold.frameCovariantDerivative I (Module.finBasis 𝕜 F) (trivializationAt F V x) s x =
      ((trivializationAt F V x).symmL 𝕜 x).comp (jet I F s x).2 := by
  set e := trivializationAt F V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  -- The section read in the trivialization at `x` has the jet's derivative coordinate as its
  -- manifold derivative at `x`: its expression in the chart at `x` is the local representative.
  have hg : MDiffAt (fun y ↦ (e ⟨y, s y⟩).2) x := (e.mdifferentiableAt_section_iff I s hx).1 hs
  have hrep : writtenInExtChartAt I 𝓘(𝕜, F) x (fun y ↦ (e ⟨y, s y⟩).2) = localRep I F s x := by
    funext z
    simp [writtenInExtChartAt, localRep_apply, e]
  have hA : HasMFDerivAt I 𝓘(𝕜, F) (fun y ↦ (e ⟨y, s y⟩).2) x (jet I F s x).2 := by
    -- The tangent spaces of `M` at `x` and of the model space `F` are `E` and `F` themselves, so
    -- the manifold derivative is the chart derivative, by `MDifferentiableAt.mfderiv_abuse`.
    have h := hg.hasMFDerivAt
    rwa [hg.mfderiv_abuse, hrep, ← jet_snd] at h
  refine Manifold.frameCovariantDerivative_eq_symmL_comp _ hA (fun i ↦ ?_) hx
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  rw [e.localFrameCoeff_eq_coeff (I := I) (b := Module.finBasis 𝕜 F) hy, Module.Basis.coord_apply]

/-- The Christoffel form at `x` of a covariant derivative over `U`, relative to the flat covariant
derivative of the trivialization at `x`. -/
private def christoffelAt (hcov : IsCovariantDerivativeOn F cov U) (x : M) :
    V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  (hcov.mono (inter_subset_left (t := (trivializationAt F V x).baseSet))).difference
    ((Manifold.isCovariantDerivativeOn_frameCovariantDerivative (I := I) (Module.finBasis 𝕜 F)
      (e := trivializationAt F V x)).mono inter_subset_right) x

omit [IsManifold I 1 M] in
/-- On the value of a section differentiable at `x`, the Christoffel form at `x` is the covariant
derivative of the section minus its flat derivative in the trivialization at `x`. -/
private theorem christoffelAt_apply (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    christoffelAt hcov x (σ x) = cov σ x -
      Manifold.frameCovariantDerivative I (Module.finBasis 𝕜 F) (trivializationAt F V x) σ x :=
  IsCovariantDerivativeOn.difference_apply _ _ (mem_inter hx (mem_baseSet_trivializationAt F V x))
    hσ

/-! ### The covariant derivative of a first jet -/

/-- **The covariant derivative of a first jet.** A covariant derivative `∇` over a set `U` gives,
at each point `x`, the continuous linear map `J¹Vₓ → Hom(TₓM, Vₓ)` that sends the first jet
`j¹s(x)` of a section differentiable at `x` to `∇s(x)` when `x ∈ U`
(`TauCeti.FirstJetBundle.covariantDerivative_jet`). It is a left inverse of
`TauCeti.FirstJetBundle.ofDeriv`, so it splits the first-jet sequence. For `x ∉ U` it is the
flat derivative of the trivialization `trivializationAt F V x`: it depends on that choice and
carries no information about `∇`. -/
def covariantDerivative (hcov : IsCovariantDerivativeOn F cov U) (x : M) :
    FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  -- A jet is a pair `(v, A)` in `F × (E →L[𝕜] F)` and `TangentSpace I x` is `E`, as in
  -- `TauCeti.FirstJetBundle.ofDeriv`; the first summand reads `A` back through the trivialization.
  (ContinuousLinearMap.postcomp (TangentSpace I x) ((trivializationAt F V x).symmL 𝕜 x) ∘L
      ContinuousLinearMap.snd 𝕜 F (E →L[𝕜] F) :
        FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x) +
    christoffelAt hcov x ∘L value I F x

/-- The covariant derivative of a jet: its derivative coordinate read through the trivialization
at `x`, plus the Christoffel form at `x` applied to its value. -/
private theorem covariantDerivative_eq_add_christoffelAt
    (hcov : IsCovariantDerivativeOn F cov U) (j : FirstJetBundle I F V x) :
    covariantDerivative hcov x j =
      (((trivializationAt F V x).symmL 𝕜 x).comp j.2 : TangentSpace I x →L[𝕜] V x) +
        christoffelAt hcov x (value I F x j) :=
  (rfl)

/-- **A covariant derivative only depends on first jets**: at a point `x` of `U`, the covariant
derivative of the first jet `j¹s(x)` of a section differentiable at `x` is `∇s(x)`. -/
@[simp]
theorem covariantDerivative_jet (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {s : Π x : M, V x} (hs : MDiffAt (T% s) x) :
    covariantDerivative hcov x (jet I F s x) = cov s x := by
  rw [covariantDerivative_eq_add_christoffelAt, value_jet, christoffelAt_apply hcov hx hs,
    frameCovariantDerivative_eq_symmL_comp_jet_snd hs]
  -- The two copies of the flat derivative are typed by `E →L[𝕜] V x` and its synonym
  -- `TangentSpace I x →L[𝕜] V x`, so `rw [add_sub_cancel]` does not see the pattern.
  exact add_sub_cancel _ _

/-- Two sections differentiable at a point `x` of `U` with the same first jet at `x` have the same
covariant derivative at `x`. -/
theorem covariantDerivative_eq_of_jet_eq (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {s t : Π x : M, V x} (hs : MDiffAt (T% s) x) (ht : MDiffAt (T% t) x)
    (h : jet I F s x = jet I F t x) : cov s x = cov t x := by
  rw [← covariantDerivative_jet hcov hx hs, h, covariantDerivative_jet hcov hx ht]

/-- The covariant derivative of the jet with value zero and derivative `L` is `L`. -/
theorem covariantDerivative_ofDeriv (hcov : IsCovariantDerivativeOn F cov U)
    (L : TangentSpace I x →L[𝕜] V x) : covariantDerivative hcov x (ofDeriv I F x L) = L := by
  rw [covariantDerivative_eq_add_christoffelAt, value_ofDeriv, map_zero, add_zero, ofDeriv_apply]
  ext v
  exact (trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜)
    (mem_baseSet_trivializationAt F V x) (L v)

/-- **A covariant derivative splits the first-jet sequence**: the covariant derivative of jets is
a left inverse of the inclusion `Hom(TₓM, Vₓ) → J¹Vₓ`. -/
@[simp]
theorem covariantDerivative_comp_ofDeriv (hcov : IsCovariantDerivativeOn F cov U) :
    covariantDerivative hcov x ∘L ofDeriv I F x = ContinuousLinearMap.id 𝕜 _ :=
  ContinuousLinearMap.ext (covariantDerivative_ofDeriv hcov)

omit [IsManifold I 1 M] in
/-- The flat derivative of the trivialization at `x` vanishes on a section with constant
coordinates in that trivialization. -/
private theorem frameCovariantDerivative_symm_eq_zero (w : F) :
    Manifold.frameCovariantDerivative I (Module.finBasis 𝕜 F) (trivializationAt F V x)
      (fun y ↦ (trivializationAt F V x).symm y w) x = 0 := by
  set e := trivializationAt F V x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  -- The coefficients of the section in the frame are the constant coordinates of `w`.
  have hcoeff (i : Fin (Module.finrank 𝕜 F)) :
      (fun y ↦ e.localFrameCoeff I (Module.finBasis 𝕜 F) i y (e.symm y w)) =ᶠ[𝓝 x]
        fun _ ↦ (Module.finBasis 𝕜 F).coord i w :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦
      (e.localFrameCoeff_eq_coeff (I := I) (b := Module.finBasis 𝕜 F)
        (s := fun y ↦ e.symm y w) hy).trans (by simp [e.apply_mk_symm hy])
  have hconst : HasMFDerivAt (M' := F) I 𝓘(𝕜, F) (fun _ : M ↦ w) x
      (0 : TangentSpace I x →L[𝕜] F) := hasMFDerivAt_const _ _
  rw [Manifold.frameCovariantDerivative_eq_symmL_comp _ hconst hcoeff hx,
    ContinuousLinearMap.comp_zero]

/-- **The covariant derivative of a first jet in coordinates.** At a point `x` of `U`, in the
chart and trivialization `e` at `x`, a first jet `(w, A)` is sent to `A` read back in `Vₓ` plus
the covariant derivative at `x` of the section `y ↦ e.symm y w` with constant coordinates `w`. -/
theorem covariantDerivative_apply (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    (j : FirstJetBundle I F V x) :
    covariantDerivative hcov x j =
      (((trivializationAt F V x).symmL 𝕜 x).comp j.2 : TangentSpace I x →L[𝕜] V x) +
        cov (fun y ↦ (trivializationAt F V x).symm y j.1) x := by
  have hσ : MDiffAt (T% (fun y ↦ (trivializationAt F V x).symm y j.1)) x :=
    ((Manifold.contMDiffOn_symm_baseSet (I := I) j.1).mdifferentiableOn
      one_ne_zero).mdifferentiableAt
        ((trivializationAt F V x).open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V x))
  rw [covariantDerivative_eq_add_christoffelAt, value_apply, christoffelAt_apply hcov hx hσ,
    frameCovariantDerivative_symm_eq_zero, sub_zero]

/-- **Characterization of the covariant derivative of first jets.** At a point `x` of `U`, a
continuous linear map `J¹Vₓ → Hom(TₓM, Vₓ)` is `TauCeti.FirstJetBundle.covariantDerivative`
exactly when it sends the first jet of every section `s` differentiable at `x` to `∇s(x)`: every
first jet is the first jet of such a section. -/
theorem eq_covariantDerivative_iff (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {K : FirstJetBundle I F V x →L[𝕜] TangentSpace I x →L[𝕜] V x} :
    K = covariantDerivative hcov x ↔
      ∀ s : Π x : M, V x, MDiffAt (T% s) x → K (jet I F s x) = cov s x := by
  refine ⟨by rintro rfl s hs; exact covariantDerivative_jet hcov hx hs, fun h ↦ ?_⟩
  refine ContinuousLinearMap.ext fun j ↦ ?_
  obtain ⟨s, hs, rfl⟩ := exists_contMDiffAt_jet_eq I F (n := 1) x j
  rw [h s (hs.mdifferentiableAt one_ne_zero),
    covariantDerivative_jet hcov hx (hs.mdifferentiableAt one_ne_zero)]

/-! ### Changing the covariant derivative -/

omit [IsManifold I 1 M] in
/-- The Christoffel form at `x` is affine in the covariant derivative: adding an
endomorphism-valued one-form `A` adds `A x`. -/
private theorem christoffelAt_add_one_form (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (v : V x) :
    christoffelAt (hcov.add_one_form A) x v = christoffelAt hcov x v + A x v := by
  have hσ := mdifferentiableAt_extend I F v
  rw [← FiberBundle.extend_apply_self F v, christoffelAt_apply _ hx hσ,
    christoffelAt_apply hcov hx hσ]
  abel

/-- **Changing the splitting by a one-form**: adding an endomorphism-valued one-form `A` to the
covariant derivative adds `A x` applied to the value of the jet. -/
theorem covariantDerivative_add_one_form (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (j : FirstJetBundle I F V x) :
    covariantDerivative (hcov.add_one_form A) x j =
      covariantDerivative hcov x j + A x (value I F x j) := by
  rw [covariantDerivative_eq_add_christoffelAt, covariantDerivative_eq_add_christoffelAt,
    christoffelAt_add_one_form hcov hx]
  abel

/-- **The splittings of two covariant derivatives differ by their difference tensor** applied to
the value of the jet. -/
theorem covariantDerivative_sub_covariantDerivative {cov' : (Π x : M, V x) →
    (Π x : M, TangentSpace I x →L[𝕜] V x)} (hcov : IsCovariantDerivativeOn F cov U)
    (hcov' : IsCovariantDerivativeOn F cov' U) (hx : x ∈ U) (j : FirstJetBundle I F V x) :
    covariantDerivative hcov x j - covariantDerivative hcov' x j =
      hcov.difference hcov' x (value I F x j) := by
  have hσ := mdifferentiableAt_extend I F (value I F x j)
  rw [covariantDerivative_eq_add_christoffelAt, covariantDerivative_eq_add_christoffelAt,
    add_sub_add_left_eq_sub, ← FiberBundle.extend_apply_self F (value I F x j),
    christoffelAt_apply hcov hx hσ, christoffelAt_apply hcov' hx hσ,
    IsCovariantDerivativeOn.difference_apply _ _ hx hσ]
  abel

/-! ### The horizontal lift and the splitting isomorphism -/

variable (I F) in
/-- The jet with value `v` and derivative coordinate zero in the chart and trivialization at `x`;
it depends on these choices, and the horizontal lift corrects it. -/
private def flatLift (x : M) : V x →L[𝕜] FirstJetBundle I F V x :=
  ContinuousLinearMap.inl 𝕜 F (E →L[𝕜] F) ∘L (trivializationAt F V x).continuousLinearMapAt 𝕜 x

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] in
private theorem flatLift_apply (v : V x) :
    flatLift I F x v =
      (((trivializationAt F V x).continuousLinearMapAt 𝕜 x v, 0) : FirstJetBundle I F V x) :=
  (rfl)

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] in
private theorem value_flatLift (v : V x) : value I F x (flatLift I F x v) = v := by
  have hx := mem_baseSet_trivializationAt F V x
  rw [flatLift_apply, (trivializationAt F V x).continuousLinearMapAt_apply_of_mem (R := 𝕜) hx]
  exact (value_apply I F x _).trans (Trivialization.symm_apply_apply_mk _ hx v)

/-- The **horizontal lift** `Vₓ → J¹Vₓ` of a covariant derivative over a set: the jet with value
`v` and covariant derivative zero. It is the right inverse of the projection `J¹Vₓ → Vₓ` that
corresponds to the splitting `TauCeti.FirstJetBundle.covariantDerivative`; like that splitting, it
only reflects `∇` when `x ∈ U`. -/
def horizontalLift (hcov : IsCovariantDerivativeOn F cov U) (x : M) :
    V x →L[𝕜] FirstJetBundle I F V x :=
  flatLift I F x - ofDeriv I F x ∘L covariantDerivative hcov x ∘L flatLift I F x

private theorem horizontalLift_eq_flatLift_sub (hcov : IsCovariantDerivativeOn F cov U) (v : V x) :
    horizontalLift hcov x v =
      flatLift I F x v - ofDeriv I F x (covariantDerivative hcov x (flatLift I F x v)) :=
  (rfl)

/-- The horizontal lift of `v` has value `v`. -/
@[simp]
theorem value_horizontalLift (hcov : IsCovariantDerivativeOn F cov U) (v : V x) :
    value I F x (horizontalLift hcov x v) = v := by
  rw [horizontalLift_eq_flatLift_sub, map_sub, value_ofDeriv, sub_zero, value_flatLift]

/-- The horizontal lift is a right inverse of the projection `J¹Vₓ → Vₓ`. -/
theorem value_comp_horizontalLift (hcov : IsCovariantDerivativeOn F cov U) :
    value I F x ∘L horizontalLift hcov x = ContinuousLinearMap.id 𝕜 (V x) :=
  ContinuousLinearMap.ext (value_horizontalLift hcov)

/-- The horizontal lift of `v` has covariant derivative zero. -/
@[simp]
theorem covariantDerivative_horizontalLift (hcov : IsCovariantDerivativeOn F cov U) (v : V x) :
    covariantDerivative hcov x (horizontalLift hcov x v) = 0 := by
  rw [horizontalLift_eq_flatLift_sub, map_sub, covariantDerivative_ofDeriv, sub_self]

/-- **The splitting decomposition of a first jet**: every first jet is the horizontal lift of its
value plus the jet of its covariant derivative. -/
theorem horizontalLift_value_add_ofDeriv_covariantDerivative
    (hcov : IsCovariantDerivativeOn F cov U) (j : FirstJetBundle I F V x) :
    horizontalLift hcov x (value I F x j) + ofDeriv I F x (covariantDerivative hcov x j) = j := by
  -- The difference `j - horizontalLift (value j)` has value zero, so it is the jet of some `L`,
  -- and taking covariant derivatives identifies `L` with the covariant derivative of `j`.
  obtain ⟨L, hL⟩ : j - horizontalLift hcov x (value I F x j) ∈
      LinearMap.range (ofDeriv I F (V := V) x).toLinearMap := by
    rw [range_ofDeriv, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
      value_horizontalLift, sub_self]
  have hcd : covariantDerivative hcov x j = L := by
    have h := congrArg (covariantDerivative hcov x) hL
    rwa [ContinuousLinearMap.coe_coe, covariantDerivative_ofDeriv, map_sub,
      covariantDerivative_horizontalLift, sub_zero, eq_comm] at h
  rw [hcd, ← ContinuousLinearMap.coe_coe (ofDeriv I F x), hL, add_sub_cancel]

/-- The horizontal lift composed with the covariant derivative of jets is zero. -/
theorem covariantDerivative_comp_horizontalLift (hcov : IsCovariantDerivativeOn F cov U) :
    covariantDerivative hcov x ∘L horizontalLift hcov x = 0 :=
  ContinuousLinearMap.ext (covariantDerivative_horizontalLift hcov)

/-- A first jet is the horizontal lift of `v` exactly when it has value `v` and covariant
derivative zero. -/
theorem eq_horizontalLift_iff (hcov : IsCovariantDerivativeOn F cov U)
    {j : FirstJetBundle I F V x} {v : V x} :
    j = horizontalLift hcov x v ↔ value I F x j = v ∧ covariantDerivative hcov x j = 0 := by
  refine ⟨by rintro rfl; simp, fun ⟨hv, hK⟩ ↦ ?_⟩
  rw [← horizontalLift_value_add_ofDeriv_covariantDerivative hcov j, hv, hK, map_zero, add_zero]

/-- The value coordinate of the horizontal lift of `v` in the trivialization `e` at `x` is
`e v`. -/
@[simp]
theorem horizontalLift_fst (hcov : IsCovariantDerivativeOn F cov U) (v : V x) :
    (horizontalLift hcov x v).1 = (trivializationAt F V x).continuousLinearMapAt 𝕜 x v := by
  rw [horizontalLift_eq_flatLift_sub]
  change (flatLift I F x v).1 - (ofDeriv I F x _).1 = _
  rw [ofDeriv_fst, sub_zero, flatLift_apply]

/-- **The horizontal lift in coordinates.** At a point `x` of `U`, in the trivialization `e` at
`x`, the horizontal lift of `v` has value coordinate `e v`, and its derivative coordinate is minus
the covariant derivative at `x`, read in `e`, of the section `y ↦ e.symm y (e v)` with constant
coordinates `e v`. -/
theorem horizontalLift_apply (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U) (v : V x) :
    horizontalLift hcov x v =
      (((trivializationAt F V x).continuousLinearMapAt 𝕜 x v,
        -((trivializationAt F V x).continuousLinearMapAt 𝕜 x).comp
          (cov (fun y ↦ (trivializationAt F V x).symm y
            ((trivializationAt F V x).continuousLinearMapAt 𝕜 x v)) x)) :
        FirstJetBundle I F V x) := by
  have hxe := mem_baseSet_trivializationAt F V x
  refine ((eq_horizontalLift_iff hcov).2 ⟨?_, ?_⟩).symm
  · exact (value_apply I F x _).trans <|
      ((trivializationAt F V x).symmL_apply (R := 𝕜) hxe _).symm.trans
        ((trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hxe v)
  · refine (covariantDerivative_apply hcov hx _).trans ?_
    ext w
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      neg_apply, map_neg, zero_apply]
    rw [(trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hxe, neg_add_cancel]

/-- At a point `x` of `U`, the derivative coordinate of the horizontal lift of `v` in the
trivialization `e` at `x` is minus the covariant derivative at `x`, read in `e`, of the section
with constant coordinates `e v`. -/
theorem horizontalLift_snd (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U) (v : V x) :
    (horizontalLift hcov x v).2 =
      -((trivializationAt F V x).continuousLinearMapAt 𝕜 x).comp
        (cov (fun y ↦ (trivializationAt F V x).symm y
          ((trivializationAt F V x).continuousLinearMapAt 𝕜 x v)) x) :=
  congrArg Prod.snd (horizontalLift_apply hcov hx v)

/-- **Changing the horizontal lift by a one-form**: adding an endomorphism-valued one-form `A` to
the covariant derivative subtracts the jet of `A x v` from the horizontal lift of `v`. -/
theorem horizontalLift_add_one_form (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (v : V x) :
    horizontalLift (hcov.add_one_form A) x v = horizontalLift hcov x v - ofDeriv I F x (A x v) := by
  refine ((eq_horizontalLift_iff (hcov.add_one_form A)).2 ⟨?_, ?_⟩).symm
  · rw [map_sub, value_horizontalLift, value_ofDeriv, sub_zero]
  · rw [covariantDerivative_add_one_form hcov hx, map_sub, map_sub, value_horizontalLift,
      value_ofDeriv, sub_zero, covariantDerivative_horizontalLift, covariantDerivative_ofDeriv,
      zero_sub, neg_add_cancel]

/-- **The horizontal lifts of two covariant derivatives differ by their difference tensor**: the
difference of the horizontal lifts of `v` is minus the jet of the difference tensor applied to
`v`. -/
theorem horizontalLift_sub_horizontalLift {cov' : (Π x : M, V x) →
    (Π x : M, TangentSpace I x →L[𝕜] V x)} (hcov : IsCovariantDerivativeOn F cov U)
    (hcov' : IsCovariantDerivativeOn F cov' U) (hx : x ∈ U) (v : V x) :
    horizontalLift hcov x v - horizontalLift hcov' x v =
      -ofDeriv I F x (hcov.difference hcov' x v) := by
  have h := horizontalLift_value_add_ofDeriv_covariantDerivative hcov' (horizontalLift hcov x v)
  have hK := covariantDerivative_sub_covariantDerivative hcov hcov' hx (horizontalLift hcov x v)
  rw [value_horizontalLift] at h hK
  rw [covariantDerivative_horizontalLift, zero_sub] at hK
  rw [← hK, map_neg, neg_neg, sub_eq_iff_eq_add']
  exact h.symm

/-- The kernel of the covariant derivative of jets is the image of the horizontal lift: the
splitting `J¹Vₓ = Vₓ ⊕ Hom(TₓM, Vₓ)` has these two summands. -/
theorem ker_covariantDerivative (hcov : IsCovariantDerivativeOn F cov U) :
    LinearMap.ker (covariantDerivative hcov x).toLinearMap =
      LinearMap.range (horizontalLift hcov x).toLinearMap := by
  ext j
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨fun h ↦ ⟨value I F x j, ?_⟩, ?_⟩
  · have hj := horizontalLift_value_add_ofDeriv_covariantDerivative hcov j
    rwa [h, map_zero, add_zero] at hj
  · rintro ⟨v, rfl⟩
    exact covariantDerivative_horizontalLift hcov v

/-- **The splitting isomorphism of a covariant derivative**: a first jet is determined by its
value and its covariant derivative, and every pair of a value and a homomorphism occurs, so
`J¹Vₓ ≃ Vₓ × Hom(TₓM, Vₓ)`. As for `TauCeti.FirstJetBundle.covariantDerivative`, it only reflects
`∇` when `x ∈ U`. -/
def connectionEquiv (hcov : IsCovariantDerivativeOn F cov U) (x : M) :
    FirstJetBundle I F V x ≃L[𝕜] V x × (TangentSpace I x →L[𝕜] V x) :=
  ContinuousLinearEquiv.equivOfInverse ((value I F x).prod (covariantDerivative hcov x))
    ((horizontalLift hcov x).coprod (ofDeriv I F x))
    (horizontalLift_value_add_ofDeriv_covariantDerivative hcov)
    fun p ↦ by
      rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.coprod_apply, map_add, map_add,
        value_horizontalLift, value_ofDeriv, add_zero, covariantDerivative_horizontalLift,
        covariantDerivative_ofDeriv, zero_add]

/-- The splitting isomorphism sends a jet to its value and its covariant derivative. -/
@[simp]
theorem connectionEquiv_apply (hcov : IsCovariantDerivativeOn F cov U)
    (j : FirstJetBundle I F V x) :
    connectionEquiv hcov x j = (value I F x j, covariantDerivative hcov x j) :=
  (rfl)

/-- The inverse of the splitting isomorphism sends a value and a homomorphism to the sum of the
horizontal lift of the value and the jet of the homomorphism. -/
@[simp]
theorem connectionEquiv_symm_apply (hcov : IsCovariantDerivativeOn F cov U)
    (p : V x × (TangentSpace I x →L[𝕜] V x)) :
    (connectionEquiv hcov x).symm p = horizontalLift hcov x p.1 + ofDeriv I F x p.2 :=
  (rfl)

/-- The splitting isomorphism sends the first jet of a section differentiable at a point `x` of
`U` to its value and its covariant derivative at `x`. -/
theorem connectionEquiv_jet (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {s : Π x : M, V x} (hs : MDiffAt (T% s) x) :
    connectionEquiv hcov x (jet I F s x) = (s x, cov s x) := by
  rw [connectionEquiv_apply, value_jet, covariantDerivative_jet hcov hx hs]

/-- At a point `x` of `U`, a section differentiable at `x` has first jet the horizontal lift of
its value exactly when its covariant derivative at `x` vanishes. -/
theorem jet_eq_horizontalLift_iff (hcov : IsCovariantDerivativeOn F cov U) (hx : x ∈ U)
    {s : Π x : M, V x} (hs : MDiffAt (T% s) x) :
    jet I F s x = horizontalLift hcov x (s x) ↔ cov s x = 0 := by
  rw [eq_horizontalLift_iff, value_jet, covariantDerivative_jet hcov hx hs]
  exact and_iff_right rfl

end

/-! ### Trivial bundles -/

section Trivial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {U : Set M} {x : M}

/-- On a trivial bundle, the covariant derivative of first jets induced by the canonical flat
connection sends a first jet to its derivative coordinate. -/
theorem covariantDerivative_trivial
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U) (j : FirstJetBundle I F (Bundle.Trivial M F) x) :
    covariantDerivative hcov x j = j.2 := by
  rw [covariantDerivative_apply hcov hx, CovariantDerivative.trivial_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_symm_apply,
    mvfderiv_const, add_zero]
  ext w
  exact (Trivialization.symmL_apply (R := 𝕜) _ (mem_univ x) (j.2 w)).trans
    (Trivial.trivialization_symm_apply M F x (j.2 w))

/-- On a trivial bundle, the horizontal lift of the canonical flat connection sends `v` to the
first jet with value `v` and derivative zero. -/
theorem horizontalLift_trivial
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U) (v : Bundle.Trivial M F x) :
    horizontalLift hcov x v = ((v, 0) : FirstJetBundle I F (Bundle.Trivial M F) x) := by
  refine ((eq_horizontalLift_iff hcov).2 ⟨?_, ?_⟩).symm
  · refine (value_apply I F x _).trans ?_
    simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_symm_apply]
  · exact covariantDerivative_trivial hcov hx _

/-- On a trivial bundle, the splitting isomorphism of the canonical flat connection is the
identity on the coordinates of a first jet. -/
theorem connectionEquiv_trivial_apply
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U) (j : FirstJetBundle I F (Bundle.Trivial M F) x) :
    connectionEquiv hcov x j = (j.1, j.2) := by
  rw [connectionEquiv_apply, covariantDerivative_trivial hcov hx, value_apply]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_symm_apply]
  rfl

/-- On a trivial bundle, the splitting isomorphism of the canonical flat connection decomposes the
first jet of a section `σ` as its value and its derivative. -/
theorem connectionEquiv_trivial_jet
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U) (σ : M → F) :
    connectionEquiv hcov x (jet I F (σ : Π y, Bundle.Trivial M F y) x) = (σ x, mvfderiv I σ x) := by
  rw [connectionEquiv_apply, value_jet, covariantDerivative_trivial hcov hx,
    jet_trivial_snd_eq_mvfderiv]

/-- On a trivial bundle, the splitting isomorphism of the connection `d + A` decomposes the first
jet of a section `σ` as its value and `dσ + A σ`. -/
theorem connectionEquiv_add_one_form_trivial_jet
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U)
    (A : Π x : M, Bundle.Trivial M F x →L[𝕜] TangentSpace I x →L[𝕜] Bundle.Trivial M F x)
    (σ : M → F) :
    connectionEquiv (hcov.add_one_form A) x (jet I F (σ : Π y, Bundle.Trivial M F y) x) =
      (σ x, mvfderiv I σ x + A x (σ x)) := by
  rw [connectionEquiv_apply, covariantDerivative_add_one_form hcov hx, value_jet,
    covariantDerivative_trivial hcov hx, jet_trivial_snd_eq_mvfderiv]

/-- On a trivial bundle, the splitting isomorphism of the canonical flat connection decomposes the
first jet of a constant section `v` as `(v, 0)`. -/
theorem connectionEquiv_trivial_jet_const
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U) (v : F) :
    connectionEquiv hcov x (jet I F (fun _ ↦ v : Π y, Bundle.Trivial M F y) x) = (v, 0) := by
  rw [connectionEquiv_trivial_jet hcov hx, mvfderiv_const]

/-- On a trivial bundle, the splitting isomorphism of the connection `d + A` decomposes the first
jet of a constant section `v` as `(v, A v)`. -/
theorem connectionEquiv_add_one_form_trivial_jet_const
    (hcov : IsCovariantDerivativeOn F (CovariantDerivative.trivial (I := I) (M := M) F) U)
    (hx : x ∈ U)
    (A : Π x : M, Bundle.Trivial M F x →L[𝕜] TangentSpace I x →L[𝕜] Bundle.Trivial M F x)
    (v : F) :
    connectionEquiv (hcov.add_one_form A) x (jet I F (fun _ ↦ v : Π y, Bundle.Trivial M F y) x) =
      (v, A x v) := by
  rw [connectionEquiv_add_one_form_trivial_jet hcov hx, mvfderiv_const, zero_add]

end Trivial

end FirstJetBundle

end TauCeti
