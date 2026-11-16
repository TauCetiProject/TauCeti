/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.Paracompact
public import TauCeti.AlgebraicTopology.ThinRealization.Basic
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.LocallyFinite
import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
import TauCeti.Geometry.Convex.ConvexSpace.Defs
import TauCeti.Geometry.Convex.ConvexSpace.Topology
import TauCeti.Topology.Category.TopCat.ClosedEmbedding
import TauCeti.Topology.Category.TopCat.Compact
import TauCeti.Topology.Category.TopCat.Paracompact
import TauCeti.Topology.Compactness.CompactlyGeneratedSpace
import TauCeti.Topology.Compactness.Lindelof

/-!
# The skeletal filtration and point-set topology of thin geometric realization

Let `X : SimplicialObject TopCat` be a simplicial space. Its `k`-skeleton
`TauCeti.thinRealization.skeleton X k` is the quotient of `Σ (m : Fin (k + 1)), Xₘ × Δᵐ` by all
simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` between simplices of degree at most `k`. The
`0`-skeleton is homeomorphic to `X₀` (`TauCeti.thinRealization.skeletonZeroHomeomorph`), and the
thin realization `|X|` is the sequential colimit in `TopCat` of the skeletal diagram
(`TauCeti.thinRealization.isColimitSkeletonCocone`).

When every degeneracy `X.σ i` has closed range in `X_{n+1}`, the latching locus
`L_{n+1} X = ⋃ i, range (X.σ i)` (`TauCeti.thinRealization.latchingSet`) is closed, so the
attaching subspace `A_{n+1} = (L_{n+1} X × Δ^{n+1}) ∪ (X_{n+1} × ∂Δ^{n+1})`
(`TauCeti.thinRealization.attachSubspace`) is a closed subspace of `X_{n+1} × Δ^{n+1}`. The
canonical attaching map `A_{n+1} ⟶ sk_n |X|` (`TauCeti.thinRealization.attachMap`) is well-defined
(using `Convexity.StdSimplex.exists_map_succAbove_of_map_succAbove_eq` on face overlaps and
`CategoryTheory.SimplicialObject.isEmbedding_σ` on degeneracy overlaps) and continuous by pasting on
the finite closed cover by degeneracy and face pieces, and the resulting square expresses
`sk_{n+1} |X|` as the pushout of `sk_n |X|` and `X_{n+1} × Δ^{n+1}` along `A_{n+1}`
(`TauCeti.thinRealization.isPushout_skeleton`).

From this closed-attachment filtration and the `TopCat` closed-embedding, normality, compactness,
and paracompactness theorems (`TauCeti.TopCat.isClosedEmbedding_of_isPushout`,
`TauCeti.TopCat.normalSpace_of_isPushout`, `TauCeti.TopCat.exists_subset_range_ι_of_isCompact`,
`TauCeti.TopCat.paracompactSpace_of_isColimit`), we deduce the point-set topology of the thin
realization in its raw weak (final) topology:

* `TauCeti.thinRealization.isClosedEmbedding_skeletonStep` and
  `TauCeti.thinRealization.isClosedEmbedding_skeletonIncl`: every skeletal transition map and every
  map `sk_k |X| ⟶ |X|` is a closed embedding.
* `TauCeti.thinRealization.uCompactlyGeneratedSpace` and `TauCeti.thinRealization.lindelofSpace`:
  `|X|` is compactly generated (respectively Lindelöf) whenever every `Xₙ` is, with no closedness
  condition on degeneracies.
* `TauCeti.thinRealization.t1Space`,
  `TauCeti.thinRealization.exists_subset_range_skeletonIncl_of_isCompact`, and
  `TauCeti.thinRealization.exists_lift_of_compactSpace`: when the degeneracies have closed range
  and every `Xₙ` is `T1`, `|X|` is `T1` and every compact subset (and every continuous map from a
  compact space) lies in a finite skeleton.
* `TauCeti.thinRealization.normalSpace`, `TauCeti.thinRealization.t4Space`,
  `TauCeti.thinRealization.t2Space`, and `TauCeti.thinRealization.paracompactSpace`: when the
  degeneracies have closed range and every `Xₙ` is `T3` and Lindelöf (for example, regular
  second-countable or compact Hausdorff), `|X|` is normal, `T4`, Hausdorff, Lindelöf, and
  paracompact.

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* P. Gabriel and M. Zisman, *Calculus of Fractions and Homotopy Theory*, Springer, 1967,
  Chapter III.
* A. Hatcher, *Algebraic Topology*, Appendix, Propositions A.1–A.3.
-/

public noncomputable section

open CategoryTheory Limits Opposite Set Topology Convexity

open scoped Simplicial

universe v u

namespace TauCeti.thinRealization

open SimplexCategory (toTop δ σ)

private local instance (n : SimplexCategory) : CompactSpace (toTop.{u}.obj n) :=
  inferInstanceAs (CompactSpace (ULift.{u} (StdSimplex ℝ (Fin (n.len + 1)))))

private local instance (n : SimplexCategory) : T2Space (toTop.{u}.obj n) :=
  inferInstanceAs (T2Space (ULift.{u} (StdSimplex ℝ (Fin (n.len + 1)))))

section BoundaryAndLatching

/-- The boundary `∂Δ^{n+1}` of the topological `(n + 1)`-simplex: the union of the images of its
`n + 2` face inclusions. -/
def toTopBoundary (n : ℕ) : Set (toTop.{u}.obj ⦋n + 1⦌) :=
  ⋃ i : Fin (n + 2), range (toTop.{u}.map (δ i))

/-- Each face inclusion `Δⁿ ⟶ Δ^{n+1}` is a closed embedding. -/
theorem isClosedEmbedding_toTop_map_δ {n : ℕ} (i : Fin (n + 2)) :
    IsClosedEmbedding (toTop.{u}.map (δ i)) := by
  refine (toTop.{u}.map (δ i)).hom.continuous.isClosedEmbedding fun s₁ s₂ h ↦ ?_
  exact ULift.ext (StdSimplex.map_injective Fin.succAbove_right_injective (congrArg ULift.down h))

/-- A point of the topological `(n + 1)`-simplex lies in the `i`-th face exactly when its `i`-th
barycentric weight vanishes. -/
theorem mem_range_toTop_map_δ_iff {n : ℕ} (i : Fin (n + 2)) (t : toTop.{u}.obj ⦋n + 1⦌) :
    t ∈ range (toTop.{u}.map (δ i)) ↔ t.down.weights i = 0 := by
  rw [← StdSimplex.mem_range_map_succAbove_iff i t.down]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.down, rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨ULift.up s, ULift.ext hs⟩

/-- A point of the topological `(n + 1)`-simplex lies in its boundary `∂Δ^{n+1}` exactly when some
barycentric weight vanishes. -/
theorem mem_toTopBoundary_iff {n : ℕ} (t : toTop.{u}.obj ⦋n + 1⦌) :
    t ∈ toTopBoundary.{u} n ↔ ∃ i : Fin (n + 2), t.down.weights i = 0 := by
  simp only [toTopBoundary, mem_iUnion, mem_range_toTop_map_δ_iff]

/-- The boundary `∂Δ^{n+1}` is a closed subset of the topological `(n + 1)`-simplex. -/
theorem isClosed_toTopBoundary (n : ℕ) : IsClosed (toTopBoundary.{u} n) :=
  isClosed_iUnion_of_finite fun i ↦ (isClosedEmbedding_toTop_map_δ i).isClosed_range

variable (X : SimplicialObject TopCat.{u})

/-- The latching locus `L_{n+1} X` in degree `n + 1`: the union of the images of the `n + 1`
degeneracy maps `Xₙ ⟶ X_{n+1}`. -/
def latchingSet (n : ℕ) : Set (X.obj (op ⦋n + 1⦌)) :=
  ⋃ i : Fin (n + 1), range (X.σ i)

/-- The latching locus in degree `n + 1` is precisely the set of degenerate `(n + 1)`-simplices of
the underlying simplicial set. -/
theorem latchingSet_eq_degenerate (n : ℕ) :
    latchingSet X n = SSet.degenerate (X ⋙ forget TopCat) (n + 1) :=
  (SSet.degenerate_eq_iUnion_range_σ (X ⋙ forget TopCat) (n := n)).symm

/-- If every degeneracy in degree `n + 1` has closed image, the latching locus `L_{n+1} X` is
closed. -/
theorem isClosed_latchingSet {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    IsClosed (latchingSet X n) :=
  isClosed_iUnion_of_finite hσ

end BoundaryAndLatching

section Skeleton

variable (X : SimplicialObject TopCat.{u})

/-- The simplicial identifications `(X(f) x, t) ∼ (x, f_* t)` restricted to degrees `≤ k`. -/
private inductive SkeletonRel (k : ℕ) :
    (Σ m : Fin (k + 1), X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌) →
      (Σ m : Fin (k + 1), X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌) → Prop
  | mk {m r : Fin (k + 1)} (f : ⦋m.val⦌ ⟶ ⦋r.val⦌) (x : X.obj (op ⦋r.val⦌))
      (t : toTop.{u}.obj ⦋m.val⦌) :
      SkeletonRel k ⟨m, X.map f.op x, t⟩ ⟨r, x, toTop.map f t⟩

/-- The `k`-skeleton `sk_k |X|` of the thin geometric realization of `X`: the quotient of
`Σ (m : Fin (k + 1)), Xₘ × Δᵐ` by all simplicial identifications between simplices of degree at
most `k`, with the quotient topology. -/
def skeleton (k : ℕ) : TopCat.{u} :=
  TopCat.of (Quot (SkeletonRel X k))

namespace skeleton

/-- The characteristic map `Xₘ × Δᵐ → sk_k |X|` for `m ≤ k`. -/
def ι (k : ℕ) (m : Fin (k + 1)) :
    C(X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌, skeleton X k) :=
  ⟨fun p ↦ Quot.mk (SkeletonRel X k) ⟨m, p⟩, continuous_quot_mk.comp continuous_sigmaMk⟩

/-- The skeletal characteristic maps satisfy all simplicial identifications in degrees `≤ k`. -/
@[simp]
theorem ι_map (k : ℕ) {m r : Fin (k + 1)} (f : ⦋m.val⦌ ⟶ ⦋r.val⦌) (x : X.obj (op ⦋r.val⦌))
    (t : toTop.{u}.obj ⦋m.val⦌) :
    ι X k m (X.map f.op x, t) = ι X k r (x, toTop.map f t) :=
  Quot.sound (SkeletonRel.mk f x t)

/-- Every point of `sk_k |X|` lies in the image of a characteristic map of degree `≤ k`. -/
theorem ι_jointly_surjective (k : ℕ) (p : skeleton X k) :
    ∃ (m : Fin (k + 1)) (x : X.obj (op ⦋m.val⦌)) (t : toTop.{u}.obj ⦋m.val⦌),
      ι X k m (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1, p.2.1, p.2.2, rfl⟩

/-- The `k`-skeleton carries the quotient topology of `Σ (m : Fin (k + 1)), Xₘ × Δᵐ`. -/
theorem isQuotientMap_sigma (k : ℕ) :
    IsQuotientMap fun p : Σ m : Fin (k + 1), X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌ ↦
      ι X k p.1 p.2 :=
  isQuotientMap_quot_mk

/-- A set in `sk_k |X|` is open exactly when its preimage under every characteristic map of degree
`≤ k` is open. -/
theorem isOpen_iff {k : ℕ} {s : Set (skeleton X k)} :
    IsOpen s ↔ ∀ m : Fin (k + 1), IsOpen (ι X k m ⁻¹' s) := by
  rw [← (isQuotientMap_sigma X k).isOpen_preimage, isOpen_sigma_iff]
  rfl

/-- A set in `sk_k |X|` is closed exactly when its preimage under every characteristic map of
degree `≤ k` is closed. -/
theorem isClosed_iff {k : ℕ} {s : Set (skeleton X k)} :
    IsClosed s ↔ ∀ m : Fin (k + 1), IsClosed (ι X k m ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_iff, preimage_compl]

/-- A map out of `sk_k |X|` is continuous exactly when its composite with every characteristic map
of degree `≤ k` is continuous. -/
theorem continuous_iff {k : ℕ} {Z : Type*} [TopologicalSpace Z] {g : skeleton X k → Z} :
    Continuous g ↔ ∀ m : Fin (k + 1), Continuous (g ∘ ι X k m) := by
  rw [(isQuotientMap_sigma X k).continuous_iff, continuous_sigma_iff]
  rfl

/-- Two continuous maps out of `sk_k |X|` agree as soon as they agree on every characteristic
map of degree `≤ k`. -/
@[ext]
theorem hom_ext {k : ℕ} {Z : TopCat} {g h : skeleton X k ⟶ Z}
    (H : ∀ (m : Fin (k + 1)) x t, g (ι X k m (x, t)) = h (ι X k m (x, t))) : g = h := by
  ext p
  obtain ⟨m, x, t, rfl⟩ := ι_jointly_surjective X k p
  exact H m x t

/-- The universal property of the `k`-skeleton: continuous maps `Xₘ × Δᵐ → Z` for `m ≤ k`
compatible with simplicial operators in degrees `≤ k` descend to a continuous map
`sk_k |X| → Z`. -/
def desc {X : SimplicialObject TopCat.{u}} {k : ℕ} {Z : Type*} [TopologicalSpace Z]
    (g : ∀ m : Fin (k + 1), C(X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌, Z))
    (hg : ∀ ⦃m r : Fin (k + 1)⦄ (f : ⦋m.val⦌ ⟶ ⦋r.val⦌) (x : X.obj (op ⦋r.val⦌))
      (t : toTop.{u}.obj ⦋m.val⦌), g m (X.map f.op x, t) = g r (x, toTop.map f t)) :
    C(skeleton X k, Z) where
  toFun := Quot.lift (fun p ↦ g p.1 p.2) (by rintro _ _ ⟨f, x, t⟩; exact hg f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun m ↦ (g m).continuous)

@[simp]
theorem desc_ι {X : SimplicialObject TopCat.{u}} {k : ℕ} {Z : Type*} [TopologicalSpace Z]
    (g : ∀ m : Fin (k + 1), C(X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌, Z))
    (hg : ∀ ⦃m r : Fin (k + 1)⦄ (f : ⦋m.val⦌ ⟶ ⦋r.val⦌) (x : X.obj (op ⦋r.val⦌))
      (t : toTop.{u}.obj ⦋m.val⦌), g m (X.map f.op x, t) = g r (x, toTop.map f t))
    (m : Fin (k + 1)) (p : X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌) :
    desc g hg (ι X k m p) = g m p :=
  (rfl)

end skeleton

/-- The `0`-skeleton of `|X|` is homeomorphic to the space `X₀` of `0`-simplices. -/
def skeletonZeroHomeomorph : skeleton X 0 ≃ₜ X.obj (op ⦋0⦌) where
  toFun := skeleton.desc (X := X) (k := 0) (fun m ↦ by
    obtain rfl : m = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    exact ContinuousMap.fst) fun {m r} f x t ↦ by
    obtain rfl : m = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    obtain rfl : r = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    have hf : f = 𝟙 ⦋0⦌ := by
      refine SimplexCategory.Hom.ext f (𝟙 ⦋0⦌) (OrderHom.ext _ _ (funext fun i ↦ Fin.ext ?_))
      have h1 := (f.toOrderHom i).isLt
      have h2 := ((𝟙 ⦋0⦌ : ⦋0⦌ ⟶ ⦋0⦌).toOrderHom i).isLt
      simp only [SimplexCategory.len_mk] at h1 h2
      omega
    simp [hf]
  invFun x := skeleton.ι X 0 0 (x, (default : toTop.{u}.obj ⦋0⦌))
  left_inv p := by
    obtain ⟨m, x, t, rfl⟩ := skeleton.ι_jointly_surjective X 0 p
    obtain rfl : m = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    rw [Subsingleton.elim t default]
    rfl
  right_inv _ := rfl
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun :=
    (skeleton.ι X 0 0).continuous.comp (continuous_id.prodMk continuous_const)

/-- On a `0`-simplex `(x, t)` in `sk_0 |X|`, `skeletonZeroHomeomorph X` recovers `x`. This is not
a `simp` lemma: `simp` rewrites `(0 : Fin 1).val` inside the dependent domain of `skeleton.ι`. -/
theorem skeletonZeroHomeomorph_apply_ι (x : X.obj (op ⦋0⦌)) (t : toTop.{u}.obj ⦋0⦌) :
    skeletonZeroHomeomorph X (skeleton.ι X 0 0 (x, t)) = x :=
  (rfl)

/-- The inverse of `skeletonZeroHomeomorph X` sends `x : X₀` to the `0`-simplex `(x, default)`. -/
@[simp]
theorem skeletonZeroHomeomorph_symm_apply (x : X.obj (op ⦋0⦌)) :
    (skeletonZeroHomeomorph X).symm x = skeleton.ι X 0 0 (x, (default : toTop.{u}.obj ⦋0⦌)) :=
  (rfl)

/-- The canonical transition map `sk_k |X| ⟶ sk_l |X|` for `k ≤ l`. -/
def skeletonMap {k l : ℕ} (hkl : k ≤ l) : skeleton X k ⟶ skeleton X l :=
  TopCat.ofHom <| skeleton.desc (X := X) (k := k)
    (fun m ↦ skeleton.ι X l (m.castLE (Nat.succ_le_succ hkl))) fun {m r} f x t ↦
    skeleton.ι_map X l (m := m.castLE (Nat.succ_le_succ hkl))
      (r := r.castLE (Nat.succ_le_succ hkl)) f x t

@[simp]
theorem skeletonMap_ι {k l : ℕ} (hkl : k ≤ l) (m : Fin (k + 1))
    (x : X.obj (op ⦋m.val⦌)) (t : toTop.{u}.obj ⦋m.val⦌) :
    skeletonMap X hkl (skeleton.ι X k m (x, t)) =
      skeleton.ι X l (m.castLE (Nat.succ_le_succ hkl)) (x, t) :=
  (rfl)

@[simp]
theorem skeletonMap_refl (k : ℕ) : skeletonMap X (le_refl k) = 𝟙 (skeleton X k) := by
  ext m x t
  simp

@[simp]
theorem skeletonMap_comp {j k l : ℕ} (hjk : j ≤ k) (hkl : k ≤ l) :
    skeletonMap X hjk ≫ skeletonMap X hkl = skeletonMap X (hjk.trans hkl) := by
  ext m x t
  simp only [ConcreteCategory.comp_apply, skeletonMap_ι]
  rfl

/-- The canonical map `sk_k |X| ⟶ |X|` from the `k`-skeleton to the thin realization. -/
def skeletonIncl (k : ℕ) : skeleton X k ⟶ thinRealization X :=
  TopCat.ofHom <| skeleton.desc (X := X) (k := k) (fun m ↦ ι X ⦋m.val⦌) fun _ _ f x t ↦
    ι_map X f x t

@[simp]
theorem skeletonIncl_ι (k : ℕ) (m : Fin (k + 1)) (x : X.obj (op ⦋m.val⦌))
    (t : toTop.{u}.obj ⦋m.val⦌) :
    skeletonIncl X k (skeleton.ι X k m (x, t)) = ι X ⦋m.val⦌ (x, t) :=
  (rfl)

@[reassoc (attr := simp)]
theorem skeletonMap_comp_skeletonIncl {k l : ℕ} (hkl : k ≤ l) :
    skeletonMap X hkl ≫ skeletonIncl X l = skeletonIncl X k := by
  ext m x t
  simp

/-- The skeletal filtration of `|X|` as a sequential diagram `ℕ ⥤ TopCat`. -/
@[expose, simps]
def skeletonDiagram : ℕ ⥤ TopCat.{u} where
  obj := skeleton X
  map f := skeletonMap X (leOfHom f)

/-- The thin realization `|X|` as a cocone over its skeletal diagram. -/
@[expose, simps]
def skeletonCocone : Cocone (skeletonDiagram X) where
  pt := thinRealization X
  ι :=
    { app := skeletonIncl X
      naturality := fun _ _ f ↦
        (skeletonMap_comp_skeletonIncl X (leOfHom f)).trans (Category.comp_id _).symm }

/-- **Sequential colimit of skeleta.** The thin geometric realization `|X|` is the colimit in
`TopCat` of its skeletal diagram `k ↦ sk_k |X|`. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc s := TopCat.ofHom <| desc (X := X) (Z := s.pt)
    (fun n ↦ (s.ι.app n.len).hom.comp (skeleton.ι X n.len (Fin.last n.len))) fun {m n} f x t ↦ by
      let N := max m.len n.len
      have hm : m.len ≤ N := le_max_left m.len n.len
      have hn : n.len ≤ N := le_max_right m.len n.len
      have h1 : s.ι.app N (skeleton.ι X N ((Fin.last m.len).castLE (Nat.succ_le_succ hm))
            (X.map f.op x, t)) =
          s.ι.app m.len (skeleton.ι X m.len (Fin.last m.len) (X.map f.op x, t)) :=
        ConcreteCategory.congr_hom (s.w (homOfLE hm))
          (skeleton.ι X m.len (Fin.last m.len) (X.map f.op x, t))
      have h2 : s.ι.app N (skeleton.ι X N ((Fin.last n.len).castLE (Nat.succ_le_succ hn))
            (x, toTop.map f t)) =
          s.ι.app n.len (skeleton.ι X n.len (Fin.last n.len) (x, toTop.map f t)) :=
        ConcreteCategory.congr_hom (s.w (homOfLE hn))
          (skeleton.ι X n.len (Fin.last n.len) (x, toTop.map f t))
      exact h1.symm.trans ((congrArg (s.ι.app N) (skeleton.ι_map X N
        (m := (Fin.last m.len).castLE (Nat.succ_le_succ hm))
        (r := (Fin.last n.len).castLE (Nat.succ_le_succ hn)) f x t)).trans h2)
  fac s k := skeleton.hom_ext X fun m x t ↦
    (desc_ι _ _ ⦋m.val⦌ (x, t)).trans
      (ConcreteCategory.congr_hom (s.w (homOfLE (Nat.le_of_lt_succ m.isLt)))
        (skeleton.ι X m.val (Fin.last m.val) (x, t))).symm
  uniq s g hg := by
    refine hom_ext X fun n x t ↦ ?_
    rw [TopCat.ofHom_apply, desc_ι]
    exact ConcreteCategory.congr_hom (hg n.len) (skeleton.ι X n.len (Fin.last n.len) (x, t))

end Skeleton

section Pushout

variable (X : SimplicialObject TopCat.{u})

/-- The attaching subspace `A_{n+1} = (L_{n+1} X × Δ^{n+1}) ∪ (X_{n+1} × ∂Δ^{n+1})` inside
`X_{n+1} × Δ^{n+1}` along which the `(n + 1)`-simplices are attached to `sk_n |X|`. -/
def attachSubspace (n : ℕ) : Set (X.obj (op ⦋n + 1⦌) × toTop.{u}.obj ⦋n + 1⦌) :=
  (latchingSet X n ×ˢ univ) ∪ (univ ×ˢ toTopBoundary.{u} n)

/-- When every degeneracy in degree `n + 1` has closed image, the attaching subspace `A_{n+1}` is
closed in `X_{n+1} × Δ^{n+1}`. -/
theorem isClosed_attachSubspace {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    IsClosed (attachSubspace X n) :=
  ((isClosed_latchingSet X hσ).prod isClosed_univ).union
    (isClosed_univ.prod (isClosed_toTopBoundary n))

/-- The inclusion of the attaching subspace `A_{n+1}` into `X_{n+1} × Δ^{n+1}`. -/
def attachIncl (n : ℕ) :
    TopCat.of (attachSubspace X n) ⟶ TopCat.of (X.obj (op ⦋n + 1⦌) × toTop.{u}.obj ⦋n + 1⦌) :=
  TopCat.ofHom (ContinuousMap.subtypeVal _)

@[simp]
theorem attachIncl_apply (n : ℕ) (p : attachSubspace X n) : attachIncl X n p = p.1 := (rfl)

/-- When every degeneracy in degree `n + 1` has closed image, `A_{n+1} ⟶ X_{n+1} × Δ^{n+1}` is a
closed embedding. -/
theorem isClosedEmbedding_attachIncl {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    IsClosedEmbedding (attachIncl X n) :=
  (isClosed_attachSubspace X hσ).isClosedEmbedding_subtypeVal

/-- Overlap compatibility between two degeneracies on `sk_n |X|`. -/
private theorem skeleton_ι_σ_eq_σ {n : ℕ} {i k : Fin (n + 1)} {y z : X.obj (op ⦋n⦌)}
    (h : X.σ i y = X.σ k z) (t : toTop.{u}.obj ⦋n + 1⦌) :
    skeleton.ι X n (Fin.last n) (y, toTop.map (σ i) t) =
      skeleton.ι X n (Fin.last n) (z, toTop.map (σ k) t) := by
  wlog hik : i ≤ k generalizing i k y z
  · exact (this h.symm (le_of_not_ge hik)).symm
  rcases hik.eq_or_lt with rfl | hlt
  · rw [(SimplicialObject.isEmbedding_σ X i).injective h]
  -- For `i < k`, both `y` and `z` are degeneracies of `w = X.δ i z`, and
  -- `σ i ≫ σ k' = σ k ≫ σ i'`.
  cases n with
  | zero => exact absurd hlt (by omega)
  | succ m =>
    let i' : Fin (m + 1) := i.castPred (Fin.ne_last_of_lt hlt)
    let k' : Fin (m + 1) := k.pred (Fin.ne_zero_of_lt hlt)
    have hi' : i'.castSucc = i := Fin.castSucc_castPred i _
    have hk' : k'.succ = k := Fin.succ_pred k _
    have hi'k' : i' ≤ k' := Nat.le_sub_one_of_lt hlt
    let w : X.obj (op ⦋m⦌) := X.δ i z
    have hy : y = X.σ k' w := by
      have h1 := congrArg (X.δ i.castSucc) h
      have h2 : X.δ i.castSucc (X.σ i y) = y := by
        rw [← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
          ConcreteCategory.id_apply]
      have h3 : X.δ i.castSucc (X.σ k z) = X.σ k' (X.δ i z) := by
        rw [← hk', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
        exact ConcreteCategory.congr_hom
          (SimplicialObject.δ_comp_σ_of_le (X := X) (i := i) (j := k')
            (by rw [← hi']; exact Fin.castSucc_le_castSucc_iff.2 hi'k')) z
      exact h2.symm.trans (h1.trans h3)
    have hz : z = X.σ i' w := by
      have h1 := congrArg (X.δ k.succ) h.symm
      have h2 : X.δ k.succ (X.σ k z) = z := by
        rw [← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_succ,
          ConcreteCategory.id_apply]
      have h3 : X.δ k.succ (X.σ i y) = X.σ i' (X.δ k y) := by
        rw [← hi', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply]
        exact ConcreteCategory.congr_hom
          (SimplicialObject.δ_comp_σ_of_gt (X := X) (i := k) (j := i') (by rwa [hi'])) y
      have h4 : X.δ k y = w := by
        rw [hy, ← hk', ← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_succ,
          ConcreteCategory.id_apply]
      exact h2.symm.trans (h1.trans (h3.trans (congrArg (X.σ i') h4)))
    have hσ : σ i ≫ σ k' = σ k ≫ σ i' := by
      rw [← hi', ← hk']
      exact SimplexCategory.σ_comp_σ hi'k'
    calc
      skeleton.ι X (m + 1) (Fin.last (m + 1)) (y, toTop.map (σ i) t)
          = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (w, toTop.map (σ k') (toTop.map (σ i) t)) := by
            rw [hy]
            exact skeleton.ι_map X (m + 1) (m := Fin.last (m + 1))
              (r := (Fin.last m).castSucc) (σ k') w (toTop.map (σ i) t)
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc (w, toTop.map (σ i ≫ σ k') t) := by
            rw [Functor.map_comp, ConcreteCategory.comp_apply]
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc (w, toTop.map (σ k ≫ σ i') t) := by
            rw [hσ]
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (w, toTop.map (σ i') (toTop.map (σ k) t)) := by
            rw [Functor.map_comp, ConcreteCategory.comp_apply]
      _ = skeleton.ι X (m + 1) (Fin.last (m + 1)) (z, toTop.map (σ k) t) := by
            rw [hz]
            exact (skeleton.ι_map X (m + 1) (m := Fin.last (m + 1))
              (r := (Fin.last m).castSucc) (σ i') w (toTop.map (σ k) t)).symm

/-- Overlap compatibility between two faces on `sk_n |X|`. -/
private theorem skeleton_ι_δ_eq_δ {n : ℕ} {j k : Fin (n + 2)} {s s' : toTop.{u}.obj ⦋n⦌}
    (h : toTop.map (δ j) s = toTop.map (δ k) s') (x : X.obj (op ⦋n + 1⦌)) :
    skeleton.ι X n (Fin.last n) (X.δ j x, s) = skeleton.ι X n (Fin.last n) (X.δ k x, s') := by
  wlog hjk : j ≤ k generalizing j k s s'
  · exact (this h.symm (le_of_not_ge hjk)).symm
  rcases hjk.eq_or_lt with rfl | hlt
  · rw [(isClosedEmbedding_toTop_map_δ j).injective h]
  -- Distinct faces of `Δ¹` are disjoint; in higher degrees `s` and `s'` share a codimension-2 face.
  cases n with
  | zero =>
    have hj0 : (toTop.map (δ j) s).down.weights j = 0 :=
      (mem_range_toTop_map_δ_iff j _).1 ⟨s, rfl⟩
    have hk0 : (toTop.map (δ j) s).down.weights k = 0 :=
      (mem_range_toTop_map_δ_iff k _).1 ⟨s', h.symm⟩
    have hj : j = 0 := by fin_cases j <;> fin_cases k <;> simp_all
    have hk : k = 1 := by fin_cases j <;> fin_cases k <;> simp_all
    subst hj hk
    have hsum : ∑ i : Fin 2, (toTop.map (δ (0 : Fin 2)) s).down.weights i = 1 :=
      (toTop.map (δ (0 : Fin 2)) s).down.total_of_fintype
    rw [Fin.sum_univ_two, hj0, hk0, add_zero] at hsum
    exact absurd hsum zero_ne_one
  | succ m =>
    obtain ⟨w, hs, hs'⟩ := StdSimplex.exists_map_succAbove_of_map_succAbove_eq hlt
      (congrArg ULift.down h)
    let j' : Fin (m + 2) := j.castPred (Fin.ne_last_of_lt hlt)
    let k' : Fin (m + 2) := k.pred (Fin.ne_zero_of_lt hlt)
    have hj' : j'.castSucc = j := Fin.castSucc_castPred j _
    have hk' : k'.succ = k := Fin.succ_pred k _
    have hj'k' : j' ≤ k' := Nat.le_sub_one_of_lt hlt
    have hs_eq : s = toTop.map (δ k') (ULift.up w) := ULift.ext hs
    have hs'_eq : s' = toTop.map (δ j') (ULift.up w) := ULift.ext hs'
    have hδ : δ j' ≫ δ k = δ k' ≫ δ j := by
      rw [← hj', ← hk']
      exact SimplexCategory.δ_comp_δ hj'k'
    calc
      skeleton.ι X (m + 1) (Fin.last (m + 1)) (X.δ j x, s)
          = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (X.map (δ k').op (X.δ j x), ULift.up w) := by
            rw [hs_eq]
            exact (skeleton.ι_map X (m + 1) (m := (Fin.last m).castSucc)
              (r := Fin.last (m + 1)) (δ k') (X.δ j x) (ULift.up w)).symm
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (X.map (δ k' ≫ δ j).op x, ULift.up w) := by
            rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
            rfl
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (X.map (δ j' ≫ δ k).op x, ULift.up w) := by
            rw [hδ]
      _ = skeleton.ι X (m + 1) (Fin.last m).castSucc
              (X.map (δ j').op (X.δ k x), ULift.up w) := by
            rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
            rfl
      _ = skeleton.ι X (m + 1) (Fin.last (m + 1)) (X.δ k x, s') := by
            rw [hs'_eq]
            exact skeleton.ι_map X (m + 1) (m := (Fin.last m).castSucc)
              (r := Fin.last (m + 1)) (δ j') (X.δ k x) (ULift.up w)

open scoped Classical in
/-- Underlying function of the attaching map `A_{n+1} → sk_n |X|`. -/
private def attachFun (n : ℕ) (p : attachSubspace X n) : skeleton X n :=
  if hx : ∃ i : Fin (n + 1), p.1.1 ∈ range (X.σ i) then
    skeleton.ι X n (Fin.last n) (X.δ hx.choose.castSucc p.1.1, toTop.map (σ hx.choose) p.1.2)
  else
    have ht : ∃ j : Fin (n + 2), p.1.2 ∈ range (toTop.{u}.map (δ j)) := by
      rcases p.2 with ⟨hx', _⟩ | ⟨_, ht'⟩
      · exact absurd (mem_iUnion.1 hx') hx
      · exact mem_iUnion.1 ht'
    skeleton.ι X n (Fin.last n) (X.δ ht.choose p.1.1, ht.choose_spec.choose)

private theorem attachFun_σ {n : ℕ} (i : Fin (n + 1)) (y : X.obj (op ⦋n⦌))
    (t : toTop.{u}.obj ⦋n + 1⦌) (hp : (X.σ i y, t) ∈ attachSubspace X n) :
    attachFun X n ⟨(X.σ i y, t), hp⟩ = skeleton.ι X n (Fin.last n) (y, toTop.map (σ i) t) := by
  classical
  have hx : ∃ k : Fin (n + 1), X.σ i y ∈ range (X.σ k) := ⟨i, y, rfl⟩
  simp only [attachFun, hx, ↓reduceDIte]
  obtain ⟨z, hz⟩ := hx.choose_spec
  have hδ : X.δ hx.choose.castSucc (X.σ i y) = z := by
    calc
      X.δ hx.choose.castSucc (X.σ i y) = X.δ hx.choose.castSucc (X.σ hx.choose z) :=
        congrArg _ hz.symm
      _ = z := by
        rw [← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
          ConcreteCategory.id_apply]
  rw [hδ]
  exact skeleton_ι_σ_eq_σ X hz t

private theorem attachFun_δ {n : ℕ} (j : Fin (n + 2)) (x : X.obj (op ⦋n + 1⦌))
    (s : toTop.{u}.obj ⦋n⦌) (hp : (x, toTop.map (δ j) s) ∈ attachSubspace X n) :
    attachFun X n ⟨(x, toTop.map (δ j) s), hp⟩ = skeleton.ι X n (Fin.last n) (X.δ j x, s) := by
  classical
  by_cases hx : ∃ i : Fin (n + 1), x ∈ range (X.σ i)
  · obtain ⟨i, y, rfl⟩ := hx
    rw [attachFun_σ X i y (toTop.map (δ j) s) hp, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← skeleton.ι_map X n (m := Fin.last n) (r := Fin.last n) (δ j ≫ σ i) y s,
      op_comp, X.map_comp, ConcreteCategory.comp_apply]
    rfl
  · simp only [attachFun, hx, ↓reduceDIte]
    have ht : ∃ k : Fin (n + 2), toTop.{u}.map (δ j) s ∈ range (toTop.{u}.map (δ k)) :=
      ⟨j, s, rfl⟩
    exact skeleton_ι_δ_eq_δ X ht.choose_spec.choose_spec x

private theorem continuousOn_attachFun_σ {n : ℕ} (i : Fin (n + 1)) :
    ContinuousOn (attachFun X n) (Subtype.val ⁻¹' (range (X.σ i) ×ˢ univ)) := by
  have hcont : Continuous fun p : attachSubspace X n ↦
      skeleton.ι X n (Fin.last n) (X.δ i.castSucc p.1.1, toTop.map (σ i) p.1.2) :=
    (skeleton.ι X n (Fin.last n)).continuous.comp <|
      ((X.δ i.castSucc).hom.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        ((toTop.map (σ i)).hom.continuous.comp (continuous_snd.comp continuous_subtype_val))
  refine hcont.continuousOn.congr fun p hp ↦ ?_
  obtain ⟨y, hy⟩ := hp.1
  have hp' : p = ⟨(X.σ i y, p.1.2), by rw [hy]; exact p.2⟩ := Subtype.ext (Prod.ext hy.symm rfl)
  have hδ : X.δ i.castSucc p.1.1 = y := by
    rw [← hy, ← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
      ConcreteCategory.id_apply]
  dsimp only
  conv_lhs => rw [hp']
  rw [attachFun_σ, hδ]

private theorem continuousOn_attachFun_δ {n : ℕ} (j : Fin (n + 2)) :
    ContinuousOn (attachFun X n) (Subtype.val ⁻¹' (univ ×ˢ range (toTop.{u}.map (δ j)))) := by
  let e : X.obj (op ⦋n + 1⦌) × toTop.{u}.obj ⦋n⦌ → attachSubspace X n := fun p ↦
    ⟨(p.1, toTop.map (δ j) p.2), Or.inr ⟨trivial, mem_iUnion.2 ⟨j, p.2, rfl⟩⟩⟩
  have he_emb : IsEmbedding e := by
    have hcomp : Subtype.val ∘ e = Prod.map id (toTop.map (δ j)) := rfl
    exact IsEmbedding.of_comp (f := e) (g := Subtype.val)
      ((continuous_fst.prodMk ((toTop.map (δ j)).hom.continuous.comp continuous_snd)).subtype_mk
        _) continuous_subtype_val (hcomp ▸ IsEmbedding.id.prodMap
          (isClosedEmbedding_toTop_map_δ j).isEmbedding)
  have he_range : range e = Subtype.val ⁻¹' (univ ×ˢ range (toTop.{u}.map (δ j))) := by
    ext p
    constructor
    · rintro ⟨⟨x, s⟩, rfl⟩
      exact ⟨trivial, s, rfl⟩
    · rintro ⟨_, s, hs⟩
      exact ⟨(p.1.1, s), Subtype.ext (Prod.ext rfl hs)⟩
  rw [← he_range, ← image_univ, he_emb.isInducing.continuousOn_image_iff]
  have hcomp : attachFun X n ∘ e = fun p ↦ skeleton.ι X n (Fin.last n) (X.δ j p.1, p.2) :=
    funext fun ⟨x, s⟩ ↦ attachFun_δ X j x s _
  rw [hcomp]
  exact ((skeleton.ι X n (Fin.last n)).continuous.comp
    (((X.δ j).hom.continuous.comp continuous_fst).prodMk continuous_snd)).continuousOn

private theorem continuous_attachFun {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    Continuous (attachFun X n) := by
  let D : Fin (n + 1) → Set (attachSubspace X n) := fun i ↦
    Subtype.val ⁻¹' (range (X.σ i) ×ˢ univ)
  let F : Fin (n + 2) → Set (attachSubspace X n) := fun j ↦
    Subtype.val ⁻¹' (univ ×ˢ range (toTop.{u}.map (δ j)))
  have hDclosed (i : Fin (n + 1)) : IsClosed (D i) :=
    ((hσ i).prod isClosed_univ).preimage continuous_subtype_val
  have hFclosed (j : Fin (n + 2)) : IsClosed (F j) :=
    (isClosed_univ.prod (isClosedEmbedding_toTop_map_δ j).isClosed_range).preimage
      continuous_subtype_val
  have hcover : (⋃ i, D i) ∪ (⋃ j, F j) = univ := by
    refine eq_univ_of_forall fun p ↦ ?_
    rcases p.2 with ⟨hx, _⟩ | ⟨_, ht⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      exact Or.inl (mem_iUnion.2 ⟨i, hi, trivial⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.1 ht
      exact Or.inr (mem_iUnion.2 ⟨j, trivial, hj⟩)
  rw [← continuousOn_univ, ← hcover]
  exact ((locallyFinite_of_finite _).continuousOn_iUnion hDclosed
      (continuousOn_attachFun_σ X)).union_of_isClosed
    ((locallyFinite_of_finite _).continuousOn_iUnion hFclosed (continuousOn_attachFun_δ X))
    (isClosed_iUnion_of_finite hDclosed) (isClosed_iUnion_of_finite hFclosed)

/-- The attaching map `A_{n+1} ⟶ sk_n |X|` sending `(X.σ i y, t)` to `[y, (σ i)_* t]` and
`(x, (δ j)_* s)` to `[X.δ j x, s]`. -/
def attachMap (n : ℕ) (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    TopCat.of (attachSubspace X n) ⟶ skeleton X n :=
  TopCat.ofHom ⟨attachFun X n, continuous_attachFun X hσ⟩

/-- On a degenerate simplex `(X.σ i y, t)`, the attaching map evaluates to `[y, (σ i)_* t]`. -/
theorem attachMap_σ {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i)))
    (i : Fin (n + 1)) (y : X.obj (op ⦋n⦌)) (t : toTop.{u}.obj ⦋n + 1⦌)
    (hp : (X.σ i y, t) ∈ attachSubspace X n) :
    attachMap X n hσ ⟨(X.σ i y, t), hp⟩ = skeleton.ι X n (Fin.last n) (y, toTop.map (σ i) t) :=
  attachFun_σ X i y t hp

/-- On a boundary point `(x, (δ j)_* s)`, the attaching map evaluates to `[X.δ j x, s]`. -/
theorem attachMap_δ {n : ℕ} (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i)))
    (j : Fin (n + 2)) (x : X.obj (op ⦋n + 1⦌)) (s : toTop.{u}.obj ⦋n⦌)
    (hp : (x, toTop.map (δ j) s) ∈ attachSubspace X n) :
    attachMap X n hσ ⟨(x, toTop.map (δ j) s), hp⟩ = skeleton.ι X n (Fin.last n) (X.δ j x, s) :=
  attachFun_δ X j x s hp

/-- Commutativity of the skeletal attaching square. -/
@[reassoc]
theorem attachMap_comp_skeletonMap (n : ℕ) (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    attachMap X n hσ ≫ skeletonMap X n.le_succ =
      attachIncl X n ≫ TopCat.ofHom (skeleton.ι X (n + 1) (Fin.last (n + 1))) := by
  ext p
  rcases p.2 with ⟨hx, _⟩ | ⟨_, ht⟩
  · obtain ⟨i, y, hy⟩ := mem_iUnion.1 hx
    have hp' : p = ⟨(X.σ i y, p.1.2), by rw [hy]; exact p.2⟩ :=
      Subtype.ext (Prod.ext hy.symm rfl)
    rw [hp', ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, attachMap_σ, skeletonMap_ι,
      attachIncl_apply]
    exact (skeleton.ι_map X (n + 1) (m := Fin.last (n + 1)) (r := (Fin.last n).castSucc)
      (σ i) y p.1.2).symm
  · obtain ⟨j, s, hs⟩ := mem_iUnion.1 ht
    have hp' : p = ⟨(p.1.1, toTop.map (δ j) s), by rw [hs]; exact p.2⟩ :=
      Subtype.ext (Prod.ext rfl hs.symm)
    rw [hp', ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, attachMap_δ, skeletonMap_ι,
      attachIncl_apply]
    exact skeleton.ι_map X (n + 1) (m := (Fin.last n).castSucc) (r := Fin.last (n + 1))
      (δ j) p.1.1 s

private theorem pushout_compat_last_last {n : ℕ}
    {hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))}
    {c : PushoutCocone (attachMap X n hσ) (attachIncl X n)}
    (hc : ∀ p : attachSubspace X n, c.inl (attachMap X n hσ p) = c.inr p.1)
    (f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌) (x : X.obj (op ⦋n + 1⦌)) (t : toTop.{u}.obj ⦋n + 1⦌) :
    c.inr (X.map f.op x, t) = c.inr (x, toTop.map f t) := by
  by_cases hinj : Function.Injective f.toOrderHom
  · have : Mono f := SimplexCategory.mono_iff_injective.2 hinj
    rw [SimplexCategory.eq_id_of_mono f, op_id, X.map_id, toTop.map_id,
      ConcreteCategory.id_apply, ConcreteCategory.id_apply]
  · -- Any non-injective endomorphism of `⦋n + 1⦌` factors as `σ i ≫ β ≫ δ j`.
    obtain ⟨i, α, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hinj
    have hnotSurj : ¬ Function.Surjective α.toOrderHom := fun hsurj ↦ by
      have := Fintype.card_le_of_surjective _ hsurj
      simp only [Fintype.card_fin, SimplexCategory.len_mk] at this
      omega
    obtain ⟨j, β, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective α hnotSurj
    have hX : X.map (σ i ≫ β ≫ δ j).op x = X.σ i (X.map β.op (X.δ j x)) := by
      rw [op_comp, op_comp, X.map_comp, X.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply]
      rfl
    have hT : toTop.map (σ i ≫ β ≫ δ j) t =
        toTop.map (δ j) (toTop.map β (toTop.map (σ i) t)) := by
      rw [Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply]
    have hL : (X.map (σ i ≫ β ≫ δ j).op x, t) ∈ attachSubspace X n :=
      Or.inl ⟨mem_iUnion.2 ⟨i, X.map β.op (X.δ j x), hX.symm⟩, trivial⟩
    have hR : (x, toTop.map (σ i ≫ β ≫ δ j) t) ∈ attachSubspace X n :=
      Or.inr ⟨trivial, mem_iUnion.2 ⟨j, toTop.map β (toTop.map (σ i) t), hT.symm⟩⟩
    rw [← hc ⟨_, hL⟩, ← hc ⟨_, hR⟩]
    have hpL : (⟨(X.map (σ i ≫ β ≫ δ j).op x, t), hL⟩ : attachSubspace X n) =
        ⟨(X.σ i (X.map β.op (X.δ j x)), t), by rwa [← hX]⟩ := Subtype.ext (Prod.ext hX rfl)
    have hpR : (⟨(x, toTop.map (σ i ≫ β ≫ δ j) t), hR⟩ : attachSubspace X n) =
        ⟨(x, toTop.map (δ j) (toTop.map β (toTop.map (σ i) t))), by rwa [← hT]⟩ :=
      Subtype.ext (Prod.ext rfl hT)
    rw [hpL, hpR, attachMap_σ X hσ i _ t _, attachMap_δ X hσ j x _ _]
    exact congrArg c.inl (skeleton.ι_map X n (m := Fin.last n) (r := Fin.last n) β
      (X.δ j x) (toTop.map (σ i) t))

private theorem pushout_compat_last_cast {n : ℕ}
    {hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))}
    {c : PushoutCocone (attachMap X n hσ) (attachIncl X n)}
    (hc : ∀ p : attachSubspace X n, c.inl (attachMap X n hσ p) = c.inr p.1)
    {r' : Fin (n + 1)} (f : ⦋n + 1⦌ ⟶ ⦋r'.val⦌) (x : X.obj (op ⦋r'.val⦌))
    (t : toTop.{u}.obj ⦋n + 1⦌) :
    c.inr (X.map f.op x, t) = c.inl (skeleton.ι X n r' (x, toTop.map f t)) := by
  have hnotInj : ¬ Function.Injective f.toOrderHom := fun hinj ↦ by
    have := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, SimplexCategory.len_mk] at this
    omega
  obtain ⟨i, ψ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hnotInj
  have hX : X.map (σ i ≫ ψ).op x = X.σ i (X.map ψ.op x) := by
    rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
    rfl
  have hL : (X.map (σ i ≫ ψ).op x, t) ∈ attachSubspace X n :=
    Or.inl ⟨mem_iUnion.2 ⟨i, X.map ψ.op x, hX.symm⟩, trivial⟩
  rw [← hc ⟨_, hL⟩]
  have hp : (⟨(X.map (σ i ≫ ψ).op x, t), hL⟩ : attachSubspace X n) =
      ⟨(X.σ i (X.map ψ.op x), t), by rwa [← hX]⟩ := Subtype.ext (Prod.ext hX rfl)
  rw [hp, attachMap_σ X hσ i _ t _]
  refine congrArg c.inl ?_
  rw [Functor.map_comp, ConcreteCategory.comp_apply]
  exact skeleton.ι_map X n (m := Fin.last n) (r := r') ψ x (toTop.map (σ i) t)

private theorem pushout_compat_cast_last {n : ℕ}
    {hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))}
    {c : PushoutCocone (attachMap X n hσ) (attachIncl X n)}
    (hc : ∀ p : attachSubspace X n, c.inl (attachMap X n hσ p) = c.inr p.1)
    {m' : Fin (n + 1)} (f : ⦋m'.val⦌ ⟶ ⦋n + 1⦌) (x : X.obj (op ⦋n + 1⦌))
    (t : toTop.{u}.obj ⦋m'.val⦌) :
    c.inl (skeleton.ι X n m' (X.map f.op x, t)) = c.inr (x, toTop.map f t) := by
  have hnotSurj : ¬ Function.Surjective f.toOrderHom := fun hsurj ↦ by
    have := Fintype.card_le_of_surjective _ hsurj
    simp only [Fintype.card_fin, SimplexCategory.len_mk] at this
    omega
  obtain ⟨j, ψ, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f hnotSurj
  have hT : toTop.map (ψ ≫ δ j) t = toTop.map (δ j) (toTop.map ψ t) := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
  have hR : (x, toTop.map (ψ ≫ δ j) t) ∈ attachSubspace X n :=
    Or.inr ⟨trivial, mem_iUnion.2 ⟨j, toTop.map ψ t, hT.symm⟩⟩
  rw [← hc ⟨_, hR⟩]
  have hp : (⟨(x, toTop.map (ψ ≫ δ j) t), hR⟩ : attachSubspace X n) =
      ⟨(x, toTop.map (δ j) (toTop.map ψ t)), by rwa [← hT]⟩ := Subtype.ext (Prod.ext rfl hT)
  rw [hp, attachMap_δ X hσ j x _ _]
  refine congrArg c.inl ?_
  have hX : X.map (ψ ≫ δ j).op x = X.map ψ.op (X.δ j x) := by
    rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [hX]
  exact skeleton.ι_map X n (m := m') (r := Fin.last n) ψ (X.δ j x) t

/-- **Skeletal pushout square.** When every degeneracy in degree `n + 1` has closed image, the
`(n + 1)`-skeleton `sk_{n+1} |X|` is the pushout in `TopCat` of `sk_n |X|` and
`X_{n+1} × Δ^{n+1}` along the closed attaching subspace
`A_{n+1} = (L_{n+1} X × Δ^{n+1}) ∪ (X_{n+1} × ∂Δ^{n+1})`. -/
theorem isPushout_skeleton (n : ℕ) (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    IsPushout (attachMap X n hσ) (attachIncl X n) (skeletonMap X n.le_succ)
      (TopCat.ofHom (skeleton.ι X (n + 1) (Fin.last (n + 1)))) := by
  have hw := attachMap_comp_skeletonMap X n hσ
  let descFn (c : PushoutCocone (attachMap X n hσ) (attachIncl X n)) (m : Fin (n + 2)) :
      C(X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌, c.pt) :=
    m.lastCases c.inr.hom (fun m' ↦ c.inl.hom.comp (skeleton.ι X n m'))
  have descCompat (c : PushoutCocone (attachMap X n hσ) (attachIncl X n)) :
      ∀ ⦃m r : Fin (n + 2)⦄ (f : ⦋m.val⦌ ⟶ ⦋r.val⦌) (x : X.obj (op ⦋r.val⦌))
        (t : toTop.{u}.obj ⦋m.val⦌),
        descFn c m (X.map f.op x, t) = descFn c r (x, toTop.map f t) := fun {m r} f x t ↦ by
    dsimp only [descFn]
    have hc (p : attachSubspace X n) : c.inl (attachMap X n hσ p) = c.inr p.1 := by
      have h := ConcreteCategory.congr_hom c.condition p
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, attachIncl_apply] at h
      exact h
    induction m using Fin.lastCases with
    | last =>
      induction r using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        exact pushout_compat_last_last X hc f x t
      | cast r' =>
        simp only [Fin.lastCases_last, Fin.lastCases_castSucc, ContinuousMap.comp_apply]
        exact pushout_compat_last_cast X hc f x t
    | cast m' =>
      induction r using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_castSucc, Fin.lastCases_last, ContinuousMap.comp_apply]
        exact pushout_compat_cast_last X hc f x t
      | cast r' =>
        simp only [Fin.lastCases_castSucc, ContinuousMap.comp_apply]
        exact congrArg c.inl (skeleton.ι_map X n (m := m') (r := r') f x t)
  let descMap (c : PushoutCocone (attachMap X n hσ) (attachIncl X n)) : skeleton X (n + 1) ⟶ c.pt :=
    TopCat.ofHom <| skeleton.desc (X := X) (k := n + 1) (descFn c) (descCompat c)
  have hdesc_cast (c : PushoutCocone (attachMap X n hσ) (attachIncl X n)) (m' : Fin (n + 1))
      (x : X.obj (op ⦋m'.val⦌)) (t : toTop.{u}.obj ⦋m'.val⦌) :
      descMap c (skeleton.ι X (n + 1) m'.castSucc (x, t)) = c.inl (skeleton.ι X n m' (x, t)) :=
    (skeleton.desc_ι (descFn c) (descCompat c) m'.castSucc (x, t)).trans
      (by simp only [descFn, Fin.lastCases_castSucc, ContinuousMap.comp_apply])
  have hdesc_last (c : PushoutCocone (attachMap X n hσ) (attachIncl X n))
      (x : X.obj (op ⦋n + 1⦌)) (t : toTop.{u}.obj ⦋n + 1⦌) :
      descMap c (skeleton.ι X (n + 1) (Fin.last (n + 1)) (x, t)) = c.inr (x, t) :=
    (skeleton.desc_ι (descFn c) (descCompat c) (Fin.last (n + 1)) (x, t)).trans
      (by simp only [descFn, Fin.lastCases_last])
  refine IsPushout.of_isColimit' ⟨hw⟩ (PushoutCocone.IsColimit.mk hw descMap
    (fun c ↦ skeleton.hom_ext X fun m x t ↦ hdesc_cast c m x t)
    (fun c ↦ TopCat.ext fun ⟨x, t⟩ ↦ hdesc_last c x t)
    fun c g h1 h2 ↦ skeleton.hom_ext X fun m x t ↦ by
      induction m using Fin.lastCases with
      | last => exact (ConcreteCategory.congr_hom h2 (x, t)).trans (hdesc_last c x t).symm
      | cast m' =>
        exact (ConcreteCategory.congr_hom h1 (skeleton.ι X n m' (x, t))).trans
          (hdesc_cast c m' x t).symm)

/-- Each skeletal step `sk_n |X| ⟶ sk_{n+1} |X|` is a closed embedding when the degeneracies in
degree `n + 1` have closed image. -/
theorem isClosedEmbedding_skeletonStep {n : ℕ}
    (hσ : ∀ i : Fin (n + 1), IsClosed (range (X.σ i))) :
    IsClosedEmbedding (skeletonMap X n.le_succ) :=
  TopCat.isClosedEmbedding_of_isPushout (isPushout_skeleton X n hσ)
    (isClosedEmbedding_attachIncl X hσ)

/-- Every skeletal transition map `sk_k |X| ⟶ sk_l |X|` (`k ≤ l`) is a closed embedding when all
degeneracies have closed image. -/
theorem isClosedEmbedding_skeletonMap
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i))) {k l : ℕ} (hkl : k ≤ l) :
    IsClosedEmbedding (skeletonMap X hkl) :=
  TopCat.isClosedEmbedding_map_of_isWellOrderContinuous (skeletonDiagram X)
    (fun n _ ↦ isClosedEmbedding_skeletonStep X (hσ n)) hkl

/-- Every map `sk_k |X| ⟶ |X|` from a skeleton to the thin realization is a closed embedding when
all degeneracies have closed image. -/
theorem isClosedEmbedding_skeletonIncl
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i))) (k : ℕ) :
    IsClosedEmbedding (skeletonIncl X k) :=
  TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (fun n ↦ isClosedEmbedding_skeletonStep X (hσ n)) (isColimitSkeletonCocone X) k

end Pushout

section Topology

/-- The product of a compactly generated space with a topological simplex is compactly generated
for every test-space universe `v`. -/
private theorem uCompactlyGeneratedSpace_prod_toTop {Y : Type*} [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{v} Y] (n : SimplexCategory) :
    UCompactlyGeneratedSpace.{v} (Y × toTop.{u}.obj n) := by
  let e : Y × ULift.{v} (StdSimplex ℝ (Fin (n.len + 1))) ≃ₜ Y × toTop.{u}.obj n :=
    Homeomorph.prodCongr (.refl Y) (Homeomorph.ulift.trans Homeomorph.ulift.symm)
  have : UCompactlyGeneratedSpace.{v} (Y × ULift.{v} (StdSimplex ℝ (Fin (n.len + 1)))) :=
    TauCeti.uCompactlyGeneratedSpace_prod_of_compactSpace
  exact uCompactlyGeneratedSpace_of_coinduced e.continuous e.isQuotientMap.eq_coinduced

variable (X : SimplicialObject TopCat.{u})

/-- Each skeleton `sk_k |X|` is compactly generated whenever every `Xₙ` is. -/
theorem uCompactlyGeneratedSpace_skeleton [∀ n, UCompactlyGeneratedSpace.{v} (X.obj n)] (k : ℕ) :
    UCompactlyGeneratedSpace.{v} (skeleton X k) := by
  have : ∀ m : Fin (k + 1), UCompactlyGeneratedSpace.{v}
      (X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌) :=
    fun m ↦ uCompactlyGeneratedSpace_prod_toTop ⦋m.val⦌
  exact uCompactlyGeneratedSpace_of_coinduced (skeleton.isQuotientMap_sigma X k).continuous
    (skeleton.isQuotientMap_sigma X k).eq_coinduced

/-- The thin geometric realization `|X|` is compactly generated in its raw weak topology whenever
every `Xₙ` is compactly generated. No closedness condition on degeneracies is needed. -/
theorem uCompactlyGeneratedSpace [∀ n, UCompactlyGeneratedSpace.{v} (X.obj n)] :
    UCompactlyGeneratedSpace.{v} (thinRealization X) := by
  have : ∀ n : SimplexCategory, UCompactlyGeneratedSpace.{v} (X.obj (op n) × toTop.{u}.obj n) :=
    fun n ↦ uCompactlyGeneratedSpace_prod_toTop n
  exact uCompactlyGeneratedSpace_of_coinduced (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).eq_coinduced

/-- Each skeleton `sk_k |X|` is Lindelöf whenever every `Xₙ` is Lindelöf. -/
theorem lindelofSpace_skeleton [∀ n, LindelofSpace (X.obj n)] (k : ℕ) :
    LindelofSpace (skeleton X k) := by
  have : ∀ m : Fin (k + 1), LindelofSpace (X.obj (op ⦋m.val⦌) × toTop.{u}.obj ⦋m.val⦌) :=
    fun m ↦ TauCeti.lindelofSpace_prod_of_compactSpace
  exact LindelofSpace.of_continuous_surjective (skeleton.isQuotientMap_sigma X k).continuous
    (skeleton.isQuotientMap_sigma X k).surjective

/-- The thin geometric realization `|X|` is Lindelöf whenever every `Xₙ` is Lindelöf. No
closedness condition on degeneracies is needed. -/
theorem lindelofSpace [∀ n, LindelofSpace (X.obj n)] : LindelofSpace (thinRealization X) := by
  have : Countable SimplexCategory :=
    Function.Injective.countable (f := SimplexCategory.len) fun ⟨_⟩ ⟨_⟩ h ↦ by cases h; rfl
  have : ∀ n : SimplexCategory, LindelofSpace (X.obj (op n) × toTop.{u}.obj n) :=
    fun n ↦ TauCeti.lindelofSpace_prod_of_compactSpace
  exact LindelofSpace.of_continuous_surjective (isQuotientMap_sigma X).continuous
    (isQuotientMap_sigma X).surjective

/-- Each skeleton `sk_k |X|` is `T1` when all degeneracies have closed image and every `Xₙ` is
`T1`. -/
theorem t1Space_skeleton (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, T1Space (X.obj n)] : ∀ k, T1Space (skeleton X k)
  | 0 => (skeletonZeroHomeomorph X).symm.t1Space
  | k + 1 =>
    have := t1Space_skeleton hσ k
    TopCat.t1Space_of_isPushout (isPushout_skeleton X k (hσ k))
      (isClosedEmbedding_attachIncl X (hσ k))

/-- The thin geometric realization `|X|` is `T1` when all degeneracies have closed image and every
`Xₙ` is `T1`. -/
theorem t1Space (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, T1Space (X.obj n)] : T1Space (thinRealization X) :=
  have : ∀ j, T1Space ((skeletonDiagram X).obj j) := t1Space_skeleton X hσ
  TopCat.t1Space_of_isColimit
    (fun _ _ hij ↦ (isClosedEmbedding_skeletonMap X hσ hij).injective) (isColimitSkeletonCocone X)

/-- Every compact subset of `|X|` lies in a finite skeleton when all degeneracies have closed image
and every `Xₙ` is `T1`. -/
theorem exists_subset_range_skeletonIncl_of_isCompact
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i))) [∀ n, T1Space (X.obj n)]
    {K : Set (thinRealization X)} (hK : IsCompact K) :
    ∃ k, K ⊆ range (skeletonIncl X k) :=
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton X hσ
  TopCat.exists_subset_range_ι_of_isCompact
    (fun _ _ hij ↦ (isClosedEmbedding_skeletonMap X hσ hij).injective)
    (isColimitSkeletonCocone X) hK

/-- Every continuous map from a compact space into `|X|` factors continuously through a finite
skeleton when all degeneracies have closed image and every `Xₙ` is `T1`. -/
theorem exists_lift_of_compactSpace
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i))) [∀ n, T1Space (X.obj n)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinRealization X)) :
    ∃ k, ∃ g' : C(K, skeleton X k), (skeletonIncl X k).hom.comp g' = g :=
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton X hσ
  TopCat.exists_lift_of_compactSpace (isColimitSkeletonCocone X)
    (fun k ↦ (isClosedEmbedding_skeletonIncl X hσ k).isEmbedding) g

/-- Each skeleton `sk_k |X|` is normal when all degeneracies have closed image and every level
product `Xₙ × Δⁿ` is normal. -/
theorem normalSpace_skeleton_of_prod
    (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n : ℕ, NormalSpace (X.obj (op ⦋n⦌) × toTop.{u}.obj ⦋n⦌)] :
    ∀ k, NormalSpace (skeleton X k)
  | 0 =>
    let e : X.obj (op ⦋0⦌) × toTop.{u}.obj ⦋0⦌ ≃ₜ skeleton X 0 :=
      (Homeomorph.prodUnique _ _).trans (skeletonZeroHomeomorph X).symm
    e.normalSpace
  | k + 1 =>
    have := normalSpace_skeleton_of_prod hσ k
    TopCat.normalSpace_of_isPushout (isPushout_skeleton X k (hσ k))
      (isClosedEmbedding_attachIncl X (hσ k))

/-- The thin geometric realization `|X|` is normal when all degeneracies have closed image and
every level product `Xₙ × Δⁿ` is normal. -/
theorem normalSpace_of_prod (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n : ℕ, NormalSpace (X.obj (op ⦋n⦌) × toTop.{u}.obj ⦋n⦌)] :
    NormalSpace (thinRealization X) :=
  have : ∀ n, NormalSpace ((skeletonDiagram X).obj n) := normalSpace_skeleton_of_prod X hσ
  TopCat.normalSpace_of_isColimit (fun n ↦ isClosedEmbedding_skeletonStep X (hσ n))
    (isColimitSkeletonCocone X)

/-- Each skeleton `sk_k |X|` is normal when all degeneracies have closed image and every `Xₙ` is
regular and Lindelöf. -/
theorem normalSpace_skeleton (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, RegularSpace (X.obj n)] [∀ n, LindelofSpace (X.obj n)] (k : ℕ) :
    NormalSpace (skeleton X k) := by
  have : ∀ n : ℕ, LindelofSpace (X.obj (op ⦋n⦌) × toTop.{u}.obj ⦋n⦌) :=
    fun _ ↦ TauCeti.lindelofSpace_prod_of_compactSpace
  exact normalSpace_skeleton_of_prod X hσ k

/-- The thin geometric realization `|X|` is normal when all degeneracies have closed image and
every `Xₙ` is regular and Lindelöf. -/
theorem normalSpace (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, RegularSpace (X.obj n)] [∀ n, LindelofSpace (X.obj n)] :
    NormalSpace (thinRealization X) := by
  have : ∀ n : ℕ, LindelofSpace (X.obj (op ⦋n⦌) × toTop.{u}.obj ⦋n⦌) :=
    fun _ ↦ TauCeti.lindelofSpace_prod_of_compactSpace
  exact normalSpace_of_prod X hσ

/-- **Normal Hausdorff thin realization.** When all degeneracies have closed image and every `Xₙ`
is `T3` and Lindelöf, the thin realization `|X|` is `T4` (normal and `T1`, hence Hausdorff). -/
theorem t4Space (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, T3Space (X.obj n)] [∀ n, LindelofSpace (X.obj n)] :
    T4Space (thinRealization X) :=
  have := t1Space X hσ
  have := normalSpace X hσ
  {}

/-- When all degeneracies have closed image and every `Xₙ` is `T3` and Lindelöf, the thin
realization `|X|` is Hausdorff. -/
theorem t2Space (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, T3Space (X.obj n)] [∀ n, LindelofSpace (X.obj n)] :
    T2Space (thinRealization X) :=
  have := t4Space X hσ
  inferInstance

/-- **Paracompact thin realization.** When all degeneracies have closed image and every `Xₙ` is
`T3` and Lindelöf, the thin realization `|X|` is paracompact in its raw weak topology. -/
theorem paracompactSpace (hσ : ∀ (n : ℕ) (i : Fin (n + 1)), IsClosed (range (X.σ i)))
    [∀ n, T3Space (X.obj n)] [∀ n, LindelofSpace (X.obj n)] :
    ParacompactSpace (thinRealization X) :=
  have : ∀ n, NormalSpace ((skeletonDiagram X).obj n) := normalSpace_skeleton X hσ
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton X hσ
  have : ∀ n, LindelofSpace ((skeletonDiagram X).obj n) := lindelofSpace_skeleton X
  TopCat.paracompactSpace_of_isColimit (fun n ↦ isClosedEmbedding_skeletonStep X (hσ n))
    (isColimitSkeletonCocone X)

end Topology

end TauCeti.thinRealization
