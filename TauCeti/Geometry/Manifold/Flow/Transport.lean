/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.VectorField.Transverse
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Section
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# The transport equation near a transverse hypersurface

Let `Z` be a smooth vector field and `g` a smooth function on a finite-dimensional boundaryless
manifold `N`, and let `ι : S → N` be a smooth embedding of a boundaryless manifold of one dimension
less, to which `Z` is transverse: `Z (ι s)` never lies in the image of the differential of `ι`. The
**transport equation** `Z h = g`, that is `dh (Z) = g`, has a smooth solution `h` on an open
neighbourhood of the image of `ι` which vanishes on that image
(`TauCeti.exists_contMDiffOn_mvfderiv_eq_of_isTransverseAlong`). Neither `Z` nor `S` need be
complete or compact. When `N` is σ-compact and the image of `ι` is closed, the solution extends
to a smooth function on all of `N`, still solving the equation near the image of `ι`
(`TauCeti.exists_contMDiff_mvfderiv_eq_of_isTransverseAlong`).

The solution is given by the method of characteristics: along the trajectory `φ_t (ι s)` of `Z`,
`h (φ_t (ι s)) = ∫₀ᵗ g (φ_u (ι s)) du`. Rather than integrating, the proof adjoins this integral as
a coordinate. On `ℝ × N`, the trajectories of the vector field `(y, x) ↦ (g x, Z x)` starting at
`(0, ι s)` follow the trajectories of `Z` in the second component, while their first component is
the integral of `g` along them. Write `F (t, s)` for the point at time `t` on the trajectory
through `(0, ι s)`. Its spatial part `(t, s) ↦ (F (t, s)).2` has differential
`(a, w) ↦ a Z (ι s) + dι w` at `(0, s)`, which is invertible by transversality, and it restricts to
`ι` on `{0} × S`. Since `ι` is an embedding, the spatial part is therefore a diffeomorphism `Ψ`
from an open neighbourhood of `{0} × S` onto an open neighbourhood `U` of the image of `ι`
(`IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section`), and `h = (F ∘ Ψ⁻¹).1` solves the
equation on `U`.

The equation is the Reeb-direction equation `R_α h = β (R_α)` of the strict contact-Moser method,
in which `Z` is a Reeb vector field.

## Main results

* `TauCeti.isOpen_setOf_notMem_range_mfderiv_of_finrank_add_one_eq`: the points of an immersed
  hypersurface at which a smooth vector field is transverse to it form an open set.
* `TauCeti.exists_contMDiffOn_mvfderiv_eq_of_isTransverseAlong`: a smooth solution of `Z h = g`
  on an open neighbourhood of a transverse embedded hypersurface, vanishing on the hypersurface.
* `TauCeti.exists_contMDiff_mvfderiv_eq_of_isTransverseAlong`: for a closed hypersurface in a
  σ-compact manifold, a solution which is smooth on the whole manifold.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 9 (flowouts, and the method of characteristics for first-order
  partial differential equations).
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N] [BoundarylessManifold I N]
  {Z : (x : N) → TangentSpace I x} {g : N → ℝ}

/-- The vector field `(y, x) ↦ (g x, Z x)` on `ℝ × N`. Its trajectories follow those of `Z` in the
second component, while the first component integrates `g` along them. -/
private def integralField (Z : (x : N) → TangentSpace I x) (g : N → ℝ) :
    (p : ℝ × N) → TangentSpace (𝓘(ℝ).prod I) p :=
  fun p ↦ (g p.2, Z p.2)

variable (hZ : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Z x⟩ : TangentBundle I N)))
  (hg : ContMDiff I 𝓘(ℝ) ∞ g)
include hZ hg

omit [FiniteDimensional ℝ E] [T2Space N] [BoundarylessManifold I N] in
private theorem contMDiff_integralField :
    ContMDiff (𝓘(ℝ).prod I) (𝓘(ℝ).prod I).tangent ∞
      (fun p : ℝ × N ↦ (⟨p, integralField Z g p⟩ : TangentBundle (𝓘(ℝ).prod I) (ℝ × N))) := by
  have hpair : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ).tangent ∞ (fun p : ℝ × N ↦ (p.1, g p.2)) :=
    contMDiff_fst.prodMk (hg.comp contMDiff_snd)
  -- `𝓘(ℝ).tangent` is the model of `ℝ × ℝ`, charted over itself.
  rw [chartedSpaceSelf_prod] at hpair
  have h1 : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ).tangent ∞
      (fun p : ℝ × N ↦ (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm (p.1, g p.2)) :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm.comp hpair
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ)) (M := ℝ) (I' := I) (M' := N)).comp
    (h1.prodMk (hZ.comp contMDiff_snd))

omit [FiniteDimensional ℝ E] in
/-- If `h` read along the trajectory of `(g, Z)` through `p` agrees, near the time `t`, with the
first component of that trajectory, then `Z h = g` at the trajectory's point at time `t`. -/
private theorem mvfderiv_apply_eq_of_eventuallyEq_flowOf {p : ℝ × N} {t : ℝ}
    (ht : (t, p) ∈ flowDomain (integralField Z g)) {h : N → ℝ}
    (hh : MDifferentiableAt I 𝓘(ℝ) h (flowOf (integralField Z g) t p).2)
    (heq : (fun u ↦ h (flowOf (integralField Z g) u p).2) =ᶠ[𝓝 t]
      fun u ↦ (flowOf (integralField Z g) u p).1) :
    mvfderiv I h (flowOf (integralField Z g) t p).2 (Z (flowOf (integralField Z g) t p).2) =
      g (flowOf (integralField Z g) t p).2 := by
  have hZg := (contMDiff_integralField hZ hg).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  -- Both functions of `u` have a derivative at `t`, computed along the field `(g, Z)`.
  have H1 := hasDerivAt_comp_flowOf hZg ht (g := Prod.fst) mdifferentiableAt_fst
  have H2 := (hasDerivAt_comp_flowOf hZg ht (g := h ∘ Prod.snd)
    (hh.comp _ mdifferentiableAt_snd)).congr_of_eventuallyEq heq.symm
  have H := H2.unique H1
  rw [mvfderiv_comp_snd_apply, show (Prod.fst : ℝ × N → ℝ) = id ∘ Prod.fst from rfl,
    mvfderiv_comp_fst_apply] at H
  have hid (y : ℝ) (v : TangentSpace 𝓘(ℝ) y) : mvfderiv 𝓘(ℝ) id y v = v := by
    rw [mvfderiv_eq_fderiv_apply, fderiv_id]
    rfl
  -- The components of `integralField Z g` at a point `(y, x)` are `g x` and `Z x` by definition.
  exact H.trans (hid _ _)

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S] {ι : S → N}
  (hι : ContMDiff J I ∞ ι)
include hι

/-- The trajectories of `(g, Z)` through the points `(0, ι s)` depend smoothly on time and on `s`
wherever they are defined. -/
private theorem contMDiffOn_flowOf_integralField :
    ContMDiffOn (𝓘(ℝ).prod J) (𝓘(ℝ).prod I) ∞
      (fun q : ℝ × S ↦ flowOf (integralField Z g) q.1 ((0 : ℝ), ι q.2))
      {q | (q.1, ((0 : ℝ), ι q.2)) ∈ flowDomain (integralField Z g)} := fun _ hq ↦
  (contMDiffAt_flowOf_comp le_top (contMDiff_integralField hZ hg)
    (f := fun q : ℝ × S ↦ ((0 : ℝ), ι q.2)) contMDiffAt_fst
    (contMDiffAt_const.prodMk (hι.contMDiffAt.comp _ contMDiffAt_snd)) hq).contMDiffWithinAt

/-- The parameters `(t, s)` for which the trajectory of `(g, Z)` through `(0, ι s)` is defined at
time `t` form an open set. -/
private theorem isOpen_setOf_mem_flowDomain_integralField :
    IsOpen {q : ℝ × S | (q.1, ((0 : ℝ), ι q.2)) ∈ flowDomain (integralField Z g)} :=
  isOpen_setOf_mem_flowDomain ((contMDiff_integralField hZ hg).of_le (by simp)) continuous_fst
    (continuous_const.prodMk (hι.continuous.comp continuous_snd))

/-- At time zero, the spatial part of the trajectories of `(g, Z)` through the points `(0, ι s)` has
differential `v ↦ v.1 Z (ι s) + dι v.2`. -/
private theorem mfderiv_snd_flowOf_integralField_zero_apply (s : S)
    (v : TangentSpace (𝓘(ℝ).prod J) ((0 : ℝ), s)) :
    mfderiv (𝓘(ℝ).prod J) I (fun q : ℝ × S ↦ (flowOf (integralField Z g) q.1 (0, ι q.2)).2)
        (0, s) v = v.1 • Z (ι s) + mfderiv J I ι s v.2 := by
  have hZg := (contMDiff_integralField hZ hg).of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)
  have hf : ContMDiffAt J (𝓘(ℝ).prod I) 1 (fun y : S ↦ ((0 : ℝ), ι y)) s :=
    contMDiffAt_const.prodMk (hι.contMDiffAt.of_le (by simp))
  have h0 : ((0 : ℝ), ((0 : ℝ), ι s)) ∈ flowDomain (integralField Z g) :=
    mem_flowDomain_zero hZg _
  have hF : MDifferentiableAt (𝓘(ℝ).prod J) (𝓘(ℝ).prod I)
      (fun q : ℝ × S ↦ flowOf (integralField Z g) q.1 ((0 : ℝ), ι q.2)) ((0 : ℝ), s) :=
    ((contMDiffOn_flowOf_integralField hZ hg hι).contMDiffAt
      ((isOpen_setOf_mem_flowDomain_integralField hZ hg hι).mem_nhds h0)).mdifferentiableAt
        (by simp)
  have h := mfderiv_flowOf_comp_apply hZg (p := ((0 : ℝ), s)) hf h0 v
  rw [show flowOf (integralField Z g) 0 = id from funext (flowOf_zero _), mfderiv_id,
    mfderiv_prodMk mdifferentiableAt_const (hι.mdifferentiableAt (by simp))] at h
  have hcomp := mfderiv_comp_apply ((0 : ℝ), s) mdifferentiableAt_snd hF v
  rw [mfderiv_snd] at hcomp
  refine hcomp.trans ((congrArg Prod.snd h).trans ?_)
  simp only [integralField, id]
  -- The second components of `v.1 • (g (ι s), Z (ι s))` and of `(0, dι v.2)` are `v.1 • Z (ι s)`
  -- and `dι v.2`, by the definitions of the operations on `ℝ × E`.
  rfl

variable [BoundarylessManifold J S]

/-- If `Z` is transverse to the immersion `ι` at `s`, and `S` has one dimension less than `N`,
the spatial part of the trajectories of `(g, Z)` through the points `(0, ι s)` is a local
diffeomorphism at `(0, s)`. -/
private theorem isLocalDiffeomorphAt_snd_flowOf_integralField [IsManifold J ∞ S] {s : S}
    (himm : Injective (mfderiv J I ι s)) (htr : Z (ι s) ∉ (mfderiv J I ι s).range)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    IsLocalDiffeomorphAt (𝓘(ℝ).prod J) I ∞
      (fun q : ℝ × S ↦ (flowOf (integralField Z g) q.1 ((0 : ℝ), ι q.2)).2) ((0 : ℝ), s) := by
  have : FiniteDimensional ℝ E' := by
    have : FiniteDimensional ℝ (TangentSpace I (ι s)) := inferInstanceAs (FiniteDimensional ℝ E)
    exact FiniteDimensional.of_injective (mfderiv J I ι s).toLinearMap himm
  -- Transversality makes the differential `(a, w) ↦ a Z (ι s) + dι w` injective.
  have hinj : Injective (mfderiv (𝓘(ℝ).prod J) I
      (fun q : ℝ × S ↦ (flowOf (integralField Z g) q.1 ((0 : ℝ), ι q.2)).2) ((0 : ℝ), s)) :=
    fun v v' hv ↦ (injective_smul_add_mfderiv_iff_notMem_range himm).2 htr
      ((mfderiv_snd_flowOf_integralField_zero_apply hZ hg hι s v).symm.trans
        (hv.trans (mfderiv_snd_flowOf_integralField_zero_apply hZ hg hι s v')))
  exact isLocalDiffeomorphAt_of_injective_mfderiv
    ((contMDiff_snd.contMDiffOn (s := univ)).comp (contMDiffOn_flowOf_integralField hZ hg hι)
      fun _ _ ↦ mem_univ _)
    (isOpen_setOf_mem_flowDomain_integralField hZ hg hι)
    (mem_flowDomain_zero ((contMDiff_integralField hZ hg).of_le (by simp)) _)
    BoundarylessManifold.isInteriorPoint (by simp) hinj
    (by rw [Module.finrank_prod, finrank_self, ← hdim, add_comm])

omit hg in
/-- **Transversality to a hypersurface is an open condition.** Let `Z` be a smooth vector field on
a finite-dimensional boundaryless manifold `N`, and let `ι : S → N` be a smooth immersion of a
boundaryless manifold of one dimension less. Then the points `s` at which `Z (ι s)` is transverse
to `ι`, that is, not in the range of `dι_s`, form an open subset of `S`.

This is the codimension-one case, read off from the flow-out of `Z` along `ι`: at a transverse
point the flow-out is a local diffeomorphism, hence so it is nearby. -/
theorem isOpen_setOf_notMem_range_mfderiv_of_finrank_add_one_eq [IsManifold J ∞ S]
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    IsOpen {s | Z (ι s) ∉ (mfderiv J I ι s).range} := by
  have hg : ContMDiff I 𝓘(ℝ) ∞ (0 : N → ℝ) := contMDiff_const
  refine isOpen_iff_mem_nhds.2 fun s hs ↦ ?_
  -- The flow-out of `(0, Z)` is a local diffeomorphism at `(0, s)`, hence at `(0, s')` for `s'`
  -- near `s`, and there its differential `(a, w) ↦ a Z (ι s') + dι w` is injective.
  have hev := ((continuous_const.prodMk continuous_id).tendsto s).eventually
    (isLocalDiffeomorphAt_snd_flowOf_integralField hZ hg hι (himm s) hs hdim).eventually
  filter_upwards [hev] with s' hs'
  exact (injective_smul_add_mfderiv_iff_notMem_range (himm s')).1 fun v v' hv ↦
    (hs'.isInvertible_mfderiv (by simp)).injective
      ((mfderiv_snd_flowOf_integralField_zero_apply hZ hg hι s' v).trans
        (hv.trans (mfderiv_snd_flowOf_integralField_zero_apply hZ hg hι s' v').symm))

variable [IsManifold J ∞ S] [TopologicalSpace.PseudoMetrizableSpace N]
  [TopologicalSpace.PseudoMetrizableSpace S]

omit [FiniteDimensional ℝ E] in
/-- **The transport equation near a transverse hypersurface.** Let `Z` be a smooth vector field and
`g` a smooth function on a finite-dimensional boundaryless manifold `N`, and let `ι : S → N` be a
smooth embedding of a boundaryless manifold of one dimension less, to which `Z` is transverse. Then
there are an open neighbourhood `U` of the image of `ι` and a function `h`, smooth on `U` and
vanishing on the image of `ι`, with `Z h = g` on `U`. No completeness of `Z` and no compactness of
`S` is needed; `S` and `N` are pseudometrizable, as second countable Hausdorff manifolds are. -/
theorem exists_contMDiffOn_mvfderiv_eq_of_isTransverseAlong
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hind : Topology.IsInducing ι)
    (htr : IsTransverseAlong J Z ι) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    ∃ U : Set N, IsOpen U ∧ range ι ⊆ U ∧ ∃ h : N → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ h U ∧
      (∀ s, h (ι s) = 0) ∧ ∀ x ∈ U, mvfderiv I h x (Z x) = g x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨∅, isOpen_empty, by simp [range_eq_empty], 0, contMDiffOn_empty, isEmptyElim,
      by simp⟩
  set F := fun q : ℝ × S ↦ flowOf (integralField Z g) q.1 ((0 : ℝ), ι q.2)
  have hF0 (y : S) : F (0, y) = (0, ι y) := flowOf_zero _ _
  -- The spatial part of `F` is a local diffeomorphism near `{0} × S`, where it restricts to the
  -- embedding `ι`; so it is a diffeomorphism `Ψ` from a neighbourhood of `{0} × S` onto an open
  -- neighbourhood of the image of `ι`.
  obtain ⟨Ψ, hsΨ, hΨD, -, hΨ⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_near_section
    (f := fun q ↦ (F q).2) (O := {q | (q.1, ((0 : ℝ), ι q.2)) ∈ flowDomain (integralField Z g)} ∩
      {q | IsLocalDiffeomorphAt (𝓘(ℝ).prod J) I ∞ (fun q ↦ (F q).2) q}) (fun q ↦ q.property.2)
    ((isOpen_setOf_mem_flowDomain_integralField hZ hg hι).inter
      (isOpen_iff_mem_nhds.2 fun _ hq ↦ IsLocalDiffeomorphAt.eventually hq))
    (s := fun y : S ↦ ((0 : ℝ), y))
    (by
      rintro _ ⟨y, rfl⟩
      exact ⟨mem_flowDomain_zero ((contMDiff_integralField hZ hg).of_le (by simp)) _,
        isLocalDiffeomorphAt_snd_flowOf_integralField hZ hg hι (himm y)
          (isTransverseAlong_iff.1 htr y) hdim⟩)
    (continuous_const.prodMk continuous_id) Prod.snd continuous_snd (fun _ ↦ rfl)
    (by simpa only [Function.comp_def, hF0] using hind)
  -- The solution is the integral of `g`, the first component of `F`, read through `Ψ⁻¹`.
  set h : N → ℝ := fun x ↦ (F (Ψ.toPartialEquiv.symm x)).1
  have hΨF (q : ℝ × S) : Ψ q = (F q).2 := congrFun hΨ q
  have hhF (q : ℝ × S) (hq : q ∈ Ψ.source) : h (F q).2 = (F q).1 := by
    simp only [h, ← hΨF, Ψ.toPartialEquiv.left_inv hq]
  have hh : ContMDiffOn I 𝓘(ℝ) ∞ h Ψ.target :=
    ((contMDiff_fst.contMDiffOn (s := univ)).comp (contMDiffOn_flowOf_integralField hZ hg hι)
      fun _ _ ↦ mem_univ _).comp Ψ.symm.contMDiffOn fun x hx ↦ (hΨD (Ψ.map_target hx)).1
  refine ⟨Ψ.target, Ψ.open_target, ?_, h, hh, fun y ↦ ?_, fun x hx ↦ ?_⟩
  · rintro _ ⟨y, rfl⟩
    have h0 : Ψ (0, y) = ι y := by rw [hΨF, hF0]
    exact h0 ▸ Ψ.map_source (hsΨ ⟨y, rfl⟩)
  · simpa [hF0] using hhF (0, y) (hsΨ ⟨y, rfl⟩)
  -- Write `x = (F q).2` with `q ∈ Ψ.source`; near the time `q.1`, the trajectory through
  -- `(0, ι q.2)` stays in `Ψ.source`, where `h` of its spatial part is its first component.
  set q := Ψ.toPartialEquiv.symm x
  have hq : q ∈ Ψ.source := Ψ.map_target hx
  have hxq : (F q).2 = x := (hΨF q).symm.trans (Ψ.right_inv hx)
  have hmd : MDifferentiableAt I 𝓘(ℝ) h (F q).2 :=
    (hh.contMDiffAt (Ψ.open_target.mem_nhds (hxq ▸ hx))).mdifferentiableAt (by simp)
  have heq : (fun u ↦ h (flowOf (integralField Z g) u ((0 : ℝ), ι q.2)).2) =ᶠ[𝓝 q.1]
      fun u ↦ (flowOf (integralField Z g) u ((0 : ℝ), ι q.2)).1 := by
    filter_upwards [(Ψ.open_source.preimage (continuous_id.prodMk continuous_const)).mem_nhds
      (show (q.1, q.2) ∈ Ψ.source from hq)] with u hu
    exact hhF (u, q.2) hu
  have := mvfderiv_apply_eq_of_eventuallyEq_flowOf hZ hg (hΨD hq).1 hmd heq
  rwa [← hxq]

omit [FiniteDimensional ℝ E] in
/-- **The transport equation near a closed transverse hypersurface.** Let `Z` be a smooth vector
field and `g` a smooth function on a finite-dimensional boundaryless σ-compact manifold `N`, and
let `ι : S → N` be a smooth embedding with closed image of a boundaryless manifold of one dimension
less, to which `Z` is transverse. Then there is a smooth function `h` on `N`, vanishing on the image
of `ι`, with `Z h = g` on an open neighbourhood of that image. -/
theorem exists_contMDiff_mvfderiv_eq_of_isTransverseAlong [SigmaCompactSpace N]
    (himm : ∀ s, Injective (mfderiv J I ι s)) (hind : Topology.IsInducing ι)
    (hclosed : IsClosed (range ι)) (htr : IsTransverseAlong J Z ι)
    (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    ∃ U : Set N, IsOpen U ∧ range ι ⊆ U ∧ ∃ h : N → ℝ, ContMDiff I 𝓘(ℝ) ∞ h ∧
      (∀ s, h (ι s) = 0) ∧ ∀ x ∈ U, mvfderiv I h x (Z x) = g x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨U, hU, hιU, h, hh, h0, hZh⟩ :=
    exists_contMDiffOn_mvfderiv_eq_of_isTransverseAlong hZ hg hι himm hind htr hdim
  -- Cut `h` off by a smooth function `χ` supported in `U` and equal to `1` near the image of `ι`.
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric N
  obtain ⟨W, hW, hιW, hWU⟩ := normal_exists_closure_subset hclosed hU hιU
  obtain ⟨χ, hχ, -, hsupp, hone⟩ :=
    isClosed_closure.exists_contMDiff_tsupport_subset_eq_one_iff (I := I) hU hWU
  refine ⟨W, hW, hιW, fun x ↦ χ x * h x, contMDiff_of_tsupport fun x hx ↦ ?_,
    fun s ↦ by simp [h0], fun x hx ↦ ?_⟩
  · exact hχ.contMDiffAt.mul (hh.contMDiffAt (hU.mem_nhds (hsupp (tsupport_mul_subset_left hx))))
  · have heq : (fun y ↦ χ y * h y) =ᶠ[𝓝 x] h := by
      filter_upwards [hW.mem_nhds hx] with y hy
      rw [(hone y).1 (subset_closure hy), one_mul]
    rw [heq.mvfderiv_eq]
    exact hZh x (hWU (subset_closure hx))

end TauCeti
