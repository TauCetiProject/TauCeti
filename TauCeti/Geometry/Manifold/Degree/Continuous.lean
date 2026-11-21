/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.Degree.Basic
-- Private: global degree invariance, Whitney smooth approximation, `[0, 1]` manifold charts,
-- and homotopy/path-connectedness bridges are used only inside definitions and proofs.
import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Topology.Homotopy.Homotopic.With
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# The mapping degree of a continuous map

Let `M` be a compact Hausdorff smooth manifold and `N` a Hausdorff smooth manifold without
boundary. Every continuous map `f : C(M, N)` has relatively compact image in `N`, so by Whitney's
approximation theorem (`ContinuousMap.exists_contMDiff_homotopic_of_isCompact_closure_range`) it is
homotopic to a smooth map `g : C(M, N)`. For orientations `o` of `M` and `o'` of `N`, we define the
*continuous mapping degree* `TauCeti.continuousDegree o o' f` to be the smooth mapping degree
`TauCeti.degree o o' g` of such a smooth approximation.

When `M` is boundaryless and `N` is σ-compact and connected of the same dimension `k`, any
continuous homotopy between smooth maps `M → N` can be smoothed to a smooth homotopy
(`ContinuousMap.Homotopy.exists_contMDiff_homotopy_of_isCompact_closure_range`), along which
`TauCeti.degree` is invariant (`TauCeti.degree_eq_of_homotopy`). Consequently:

* two continuously homotopic smooth maps `M → N` have the same `TauCeti.degree`
  (`TauCeti.degree_eq_of_homotopic`);
* `TauCeti.continuousDegree o o' f` equals `TauCeti.degree o o' g` for *every* smooth map `g`
  homotopic to `f` (`TauCeti.continuousDegree_eq_degree_of_homotopic`), so it agrees with
  `TauCeti.degree` on smooth maps (`TauCeti.continuousDegree_eq_degree`) and is invariant under
  continuous homotopies (`TauCeti.continuousDegree_eq_of_homotopic`);
* the continuous degree is `1` on the identity (`TauCeti.continuousDegree_id`), `0` on constant
  maps into positive-dimensional targets (`TauCeti.continuousDegree_const`), and multiplicative
  under composition (`TauCeti.continuousDegree_comp`), so homotopy equivalences and homeomorphisms
  have degree `±1` (`TauCeti.natAbs_continuousDegree_of_homotopyEquiv`,
  `TauCeti.natAbs_continuousDegree_of_homeomorph`);
* a continuous map missing a point `y ∈ N` can be smoothed inside the open punctured manifold
  `N \ {y}`, where any smooth representative fails to be surjective and hence has degree `0`;
  therefore every continuous map of nonzero degree is surjective
  (`TauCeti.surjective_of_continuousDegree_ne_zero`).

## Main definitions

* `TauCeti.continuousDegree o o' f`: the mapping degree of a continuous map `f : C(M, N)`, defined
  as `TauCeti.degree o o' g` for a smooth map `g` homotopic to `f`.

## Main results

* `TauCeti.degree_eq_of_homotopic`: continuously homotopic smooth maps have the same smooth degree.
* `TauCeti.continuousDegree_eq_degree_of_homotopic`: `continuousDegree o o' f = degree o o' g`
  for every smooth map `g` homotopic to `f`.
* `TauCeti.continuousDegree_eq_degree`, `TauCeti.continuousDegree_eq_degreeAtRegularValue`:
  compatibility with `TauCeti.degree` and `TauCeti.degreeAtRegularValue` on smooth maps.
* `TauCeti.continuousDegree_eq_of_homotopic`, `TauCeti.continuousDegree_eq_of_homotopy`,
  `TauCeti.continuousDegree_eq_of_joined`: homotopy invariance of the continuous degree.
* `TauCeti.continuousDegree_id`, `TauCeti.continuousDegree_const`: degree of the identity and of
  constant maps.
* `TauCeti.continuousDegree_eq_zero_of_notMem_range`,
  `TauCeti.surjective_of_continuousDegree_ne_zero`,
  `TauCeti.continuousDegree_eq_zero_of_not_compactSpace`: surjectivity of maps of nonzero degree.
* `TauCeti.continuousDegree_comp`: multiplicativity `deg(g ∘ f) = deg g · deg f`.
* `TauCeti.isUnit_continuousDegree_of_homotopyEquiv`,
  `TauCeti.natAbs_continuousDegree_of_homotopyEquiv`,
  `TauCeti.natAbs_continuousDegree_of_homeomorph`: homotopy equivalences and homeomorphisms have
  degree `±1`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 6 (Theorems 6.26 and 6.29) and Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open ContinuousMap Function Set
open scoped Manifold ContDiff Topology

namespace TauCeti

section Definition

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {ι : Type*} [Fintype ι]

/-- The **mapping degree of a continuous map** `f : C(M, N)` from a compact Hausdorff manifold `M`
to a Hausdorff boundaryless manifold `N`, with respect to orientations `o` of `M` and `o'` of `N`:
the smooth mapping degree `TauCeti.degree o o' g` of a smooth map `g` homotopic to `f`, chosen by
Whitney approximation. When `M` is boundaryless and `N` is σ-compact and connected of the same
dimension `Fin k`, this does not depend on the smooth representative
(`TauCeti.continuousDegree_eq_degree_of_homotopic`). -/
def continuousDegree (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    (f : C(M, N)) : ℤ :=
  degree o o'
    (f.exists_contMDiff_homotopic_of_isCompact_closure_range (I := I) (J := J) ⊤
      ((isCompact_range f.continuous).closure_of_subset Subset.rfl)).choose

/-- Every continuous map `f : C(M, N)` is homotopic to a smooth map whose smooth degree equals
`continuousDegree o o' f`. -/
theorem exists_contMDiff_homotopic_and_continuousDegree_eq_degree
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι) (f : C(M, N)) :
    ∃ g : C(M, N), ContMDiff I J ∞ g ∧ f.Homotopic g ∧
      continuousDegree o o' f = degree o o' g := by
  let h := f.exists_contMDiff_homotopic_of_isCompact_closure_range (I := I) (J := J) ⊤
    ((isCompact_range f.continuous).closure_of_subset Subset.rfl)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩

/-- Reversing the orientation of the source negates the continuous degree. -/
@[simp]
theorem continuousDegree_neg_left (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (f : C(M, N)) :
    continuousDegree (-o) o' f = -continuousDegree o o' f :=
  degree_neg_left

/-- Reversing the orientation of the target negates the continuous degree. -/
@[simp]
theorem continuousDegree_neg_right (o : Manifold.Orientation I M ι)
    (o' : Manifold.Orientation J N ι) (f : C(M, N)) :
    continuousDegree o (-o') f = -continuousDegree o o' f :=
  degree_neg_right

end Definition

section Global

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N] {k : ℕ}

/-- **Continuous homotopy invariance of the smooth degree.** Two smooth maps `f, g : M → N` that
are joined by a continuous homotopy have the same smooth mapping degree. -/
theorem degree_eq_of_homotopic (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f g : M → N} (hf : ContMDiff I J ∞ f)
    (hg : ContMDiff I J ∞ g)
    (h : ContinuousMap.Homotopic ⟨f, hf.continuous⟩ ⟨g, hg.continuous⟩) :
    degree o o' f = degree o o' g := by
  obtain ⟨H⟩ := h
  obtain ⟨K, hK, hK₀, hK₁⟩ := H.exists_contMDiff_homotopy_of_isCompact_closure_range
    ((isCompact_range H.continuous).closure_of_subset Subset.rfl) ⊤ hf hg
  -- Restrict `K : M × ℝ → N` to the parameter interval `[0, 1]`.
  have hF : ContMDiff (I.prod (𝓡∂ 1)) J ∞ fun p : M × Icc (0 : ℝ) 1 ↦ K (p.1, p.2) :=
    hK.comp (contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  exact degree_eq_of_homotopy o o' hf hg hF (fun x ↦ hK₀ x) (fun x ↦ hK₁ x)

/-- **Characterization by smooth approximations.** For every smooth map `g : M → N` continuously
homotopic to `f`, `continuousDegree o o' f` equals `degree o o' g`. -/
theorem continuousDegree_eq_degree_of_homotopic (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : C(M, N)} {g : M → N} (hg : ContMDiff I J ∞ g)
    (h : f.Homotopic ⟨g, hg.continuous⟩) :
    continuousDegree o o' f = degree o o' g := by
  obtain ⟨f₀, hf₀, hff₀, hdeg⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o o' f
  exact hdeg.trans (degree_eq_of_homotopic o o' hf₀ hg (hff₀.symm.trans h))

/-- On a smooth bundled map `f : C(M, N)`, `continuousDegree` agrees with `degree`. -/
theorem continuousDegree_eq_degree (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : C(M, N)} (hf : ContMDiff I J ∞ f) :
    continuousDegree o o' f = degree o o' f :=
  continuousDegree_eq_degree_of_homotopic o o' hf (.refl f)

/-- For a smooth map `f : C(M, N)` and any regular value `y` of `f`, `continuousDegree o o' f` is
the signed count of the fibre over `y`. -/
theorem continuousDegree_eq_degreeAtRegularValue (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : C(M, N)} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) :
    continuousDegree o o' f = degreeAtRegularValue o o' f y :=
  (continuousDegree_eq_degree o o' hf).trans
    (degree_eq_degreeAtRegularValue o o' hf hf.continuous.isProperMap hy)

/-- **Homotopy invariance of the continuous degree.** Continuously homotopic maps `f, g : C(M, N)`
have the same mapping degree. -/
theorem continuousDegree_eq_of_homotopic (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f g : C(M, N)} (h : f.Homotopic g) :
    continuousDegree o o' f = continuousDegree o o' g := by
  obtain ⟨g₀, hg₀, hgg₀, hdeg⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o o' g
  exact (continuousDegree_eq_degree_of_homotopic o o' hg₀ (h.trans hgg₀)).trans hdeg.symm

/-- A homotopy `H : f.Homotopy g` witnesses that `f` and `g` have the same continuous degree. -/
theorem continuousDegree_eq_of_homotopy (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f g : C(M, N)} (H : f.Homotopy g) :
    continuousDegree o o' f = continuousDegree o o' g :=
  continuousDegree_eq_of_homotopic o o' ⟨H⟩

/-- Maps in the same path component of `C(M, N)` have the same continuous degree. -/
theorem continuousDegree_eq_of_joined (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f g : C(M, N)} (h : Joined f g) :
    continuousDegree o o' f = continuousDegree o o' g :=
  continuousDegree_eq_of_homotopic o o' (ContinuousMap.homotopic_iff_joined.2 h)

omit [BoundarylessManifold I M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N] in
/-- The identity map of a compact connected oriented boundaryless manifold has continuous degree
`1`. -/
@[simp]
theorem continuousDegree_id [I.Boundaryless] [ConnectedSpace M]
    (o : Manifold.Orientation I M (Fin k)) :
    continuousDegree o o (ContinuousMap.id M) = 1 :=
  (continuousDegree_eq_degree o o contMDiff_id).trans (degree_id o)

/-- A constant map into a connected manifold of positive dimension has continuous degree `0`. -/
@[simp]
theorem continuousDegree_const [NeZero k]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) (y₀ : N) :
    continuousDegree o o' (ContinuousMap.const M y₀) = 0 := by
  have hpos : 0 < Module.finrank ℝ E' := by
    rw [← o'.card_eq, Fintype.card_fin]
    exact NeZero.pos k
  exact (continuousDegree_eq_degree o o' contMDiff_const).trans (degree_const hpos y₀)

/-- A continuous map `f : C(M, N)` missing a point `y ∈ N` has continuous degree `0`. -/
theorem continuousDegree_eq_zero_of_notMem_range (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : C(M, N)} {y : N} (hy : y ∉ range f) :
    continuousDegree o o' f = 0 := by
  -- Factor `f` through the open punctured manifold `W = N \ {y}` and smooth it inside `W`.
  let W : TopologicalSpace.Opens N := ⟨{y}ᶜ, isClosed_singleton.isOpen_compl⟩
  let f' : C(M, W) := ⟨_, f.continuous.subtype_mk fun x hxy ↦ hy ⟨x, hxy⟩⟩
  obtain ⟨g', hg', hfg'⟩ := f'.exists_contMDiff_homotopic_of_isCompact_closure_range
    (I := I) (J := J) ⊤ ((isCompact_range f'.continuous).closure_of_subset Subset.rfl)
  let ι : C(W, N) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hιg' : ContMDiff I J ∞ (ι.comp g') := contMDiff_subtypeVal.comp hg'
  have hhom : f.Homotopic (ι.comp g') := by
    have hfι : ι.comp f' = f := ContinuousMap.ext fun _ ↦ rfl
    exact hfι ▸ ContinuousMap.Homotopic.comp (.refl ι) hfg'
  rw [continuousDegree_eq_degree_of_homotopic o o' hιg' hhom]
  by_contra hne
  obtain ⟨x, hx⟩ := surjective_of_degree_ne_zero o o' hιg' hιg'.continuous.isProperMap hne y
  exact (g' x).property hx

/-- **Surjectivity from nonzero continuous degree.** Every continuous map `f : C(M, N)` of nonzero
mapping degree from a compact oriented boundaryless manifold to a connected oriented boundaryless
manifold of the same dimension is surjective. -/
theorem surjective_of_continuousDegree_ne_zero (o : Manifold.Orientation I M (Fin k))
    (o' : Manifold.Orientation J N (Fin k)) {f : C(M, N)} (h : continuousDegree o o' f ≠ 0) :
    Surjective f := fun _ ↦
  by_contra fun hy ↦ h (continuousDegree_eq_zero_of_notMem_range o o' hy)

/-- Any continuous map from a compact oriented boundaryless manifold to a non-compact connected
oriented boundaryless manifold of the same dimension has continuous degree `0`. -/
theorem continuousDegree_eq_zero_of_not_compactSpace (hN : ¬ CompactSpace N)
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) (f : C(M, N)) :
    continuousDegree o o' f = 0 := by
  by_contra hne
  have hsurj := surjective_of_continuousDegree_ne_zero o o' hne
  exact hN ⟨by rw [← range_eq_univ.2 hsurj]; exact isCompact_range f.continuous⟩

omit [SigmaCompactSpace N] in
/-- **Multiplicativity of the continuous degree.** For continuous maps `f : C(M, N)` and
`g : C(N, P)` between compact connected oriented boundaryless manifolds of the same dimension,
`deg(g ∘ f) = deg g · deg f`. -/
theorem continuousDegree_comp {E'' H'' P : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [FiniteDimensional ℝ E''] [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
    [K.Boundaryless] [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]
    [T2Space P] [SigmaCompactSpace P] [ConnectedSpace P] [CompactSpace N]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k))
    (o'' : Manifold.Orientation K P (Fin k)) (f : C(M, N)) (g : C(N, P)) :
    continuousDegree o o'' (g.comp f) = continuousDegree o' o'' g * continuousDegree o o' f := by
  obtain ⟨f₀, hf₀, hff₀, hdf⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o o' f
  obtain ⟨g₀, hg₀, hgg₀, hdg⟩ :=
    exists_contMDiff_homotopic_and_continuousDegree_eq_degree o' o'' g
  rw [hdf, hdg, continuousDegree_eq_degree_of_homotopic o o'' (hg₀.comp hf₀) (hgg₀.comp hff₀)]
  exact degree_comp o o' o'' hf₀ hg₀ hf₀.continuous.isProperMap hg₀.continuous.isProperMap

omit [BoundarylessManifold I M] [SigmaCompactSpace N] in
/-- If `g.comp f` is homotopic to the identity of `M`, then the product of the continuous degrees
of `g` and `f` is `1`. -/
theorem continuousDegree_mul_eq_one_of_homotopic_id [I.Boundaryless] [CompactSpace N]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k))
    {f : C(M, N)} {g : C(N, M)} (h : (g.comp f).Homotopic (ContinuousMap.id M)) :
    continuousDegree o' o g * continuousDegree o o' f = 1 := by
  have := h.connectedSpace_of_comp_homotopic_id
  rw [← continuousDegree_comp o o' o f g, continuousDegree_eq_of_homotopic o o h,
    continuousDegree_id]

omit [BoundarylessManifold I M] [SigmaCompactSpace N] in
/-- A homotopy equivalence between compact connected oriented boundaryless manifolds of the same
dimension has invertible continuous degree (`±1`). -/
theorem isUnit_continuousDegree_of_homotopyEquiv [I.Boundaryless] [CompactSpace N]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) (e : M ≃ₕ N) :
    IsUnit (continuousDegree o o' e.toFun) :=
  IsUnit.of_mul_eq_one_right _ (continuousDegree_mul_eq_one_of_homotopic_id o o' e.left_inv)

omit [BoundarylessManifold I M] [SigmaCompactSpace N] in
/-- A homotopy equivalence between compact connected oriented boundaryless manifolds of the same
dimension has continuous degree of absolute value `1`. -/
@[simp]
theorem natAbs_continuousDegree_of_homotopyEquiv [I.Boundaryless] [CompactSpace N]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) (e : M ≃ₕ N) :
    (continuousDegree o o' e.toFun).natAbs = 1 :=
  Int.isUnit_iff_natAbs_eq.1 (isUnit_continuousDegree_of_homotopyEquiv o o' e)

omit [BoundarylessManifold I M] [SigmaCompactSpace N] in
/-- A homeomorphism between compact connected oriented boundaryless manifolds of the same dimension
has continuous degree of absolute value `1`. -/
@[simp]
theorem natAbs_continuousDegree_of_homeomorph [I.Boundaryless]
    (o : Manifold.Orientation I M (Fin k)) (o' : Manifold.Orientation J N (Fin k)) (e : M ≃ₜ N) :
    (continuousDegree o o' (e : C(M, N))).natAbs = 1 := by
  have := e.compactSpace
  exact natAbs_continuousDegree_of_homotopyEquiv o o' e.toHomotopyEquiv

end Global

end TauCeti
