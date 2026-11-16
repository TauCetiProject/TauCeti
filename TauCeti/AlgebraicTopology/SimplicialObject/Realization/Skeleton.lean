/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialObject.Realization.Basic
public import TauCeti.AlgebraicTopology.SimplicialObject.TopCat
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding
public import TauCeti.Topology.Category.TopCat.Compact
public import TauCeti.Topology.Category.TopCat.Paracompact

/-!
# Skeletal filtration and point-set topology of thin realization

For a simplicial space `X : SimplicialObject TopCat`, the `n`-skeleton
`TauCeti.thinRealization.skeleton X n` is the quotient of `Σ (k ≤ n), Xₖ × Δᵏ` by the simplicial
identifications `(X(f) x, t) ∼ (x, f_* t)` along morphisms `f : ⦋j⦌ ⟶ ⦋k⦌` with `j, k ≤ n`.
These stages form a sequence `TauCeti.thinRealization.skeletonDiagram X : ℕ ⥤ TopCat` whose
colimit is `TauCeti.thinRealization X` (`TauCeti.thinRealization.isColimitSkeletonCocone`), with
`0`-skeleton homeomorphic to `X _⦋0⦌` (`TauCeti.thinRealization.skeletonZeroHomeomorph`).

Whenever each degeneracy `X.σ j` has closed image in `X _⦋n + 1⦌` (automatic whenever `X _⦋n + 1⦌`
is Hausdorff by `CategoryTheory.SimplicialObject.isClosedEmbedding_σ`), the attaching subspace
`A_{n+1} = (⋃ j, range (X.σ j)) × Δ^{n+1} ∪ X_{n+1} × ∂Δ^{n+1}` is closed in `X_{n+1} × Δ^{n+1}`
(`TauCeti.thinRealization.isClosed_attachingSet`), the attaching map `A_{n+1} → skₙ |X|` is
continuous (`TauCeti.thinRealization.attachMap`), and `sk_{n+1} |X|` is the pushout of `skₙ |X|`
and `X_{n+1} × Δ^{n+1}` along `A_{n+1}` (`TauCeti.thinRealization.isPushout_skeleton`).

Applying the pushout and sequential-colimit stability theorems of `TauCeti.Topology.Category.TopCat`
yields:

* Every skeletal inclusion `skₙ |X| ⟶ sk_{n+1} |X|` and `skₙ |X| ⟶ |X|` is a closed embedding.
* If every level `Xₙ` is `T1` (resp. every `Xₙ × Δⁿ` is normal), every stage and `|X|` are `T1`
  (resp. normal); combining them yields `T4Space` (in particular Hausdorffness) and, when every
  level is Lindelöf, `ParacompactSpace`.
* Every compact subset of `|X|` lies in a single finite stage `skₙ |X|`, and every continuous map
  from a compact space into `|X|` factors continuously through one stage.
* In particular, if every level `Xₙ` is regular, `T1`, and Lindelöf (covering both
  second-countable regular `T1` spaces such as Hausdorff manifolds and compact Hausdorff spaces),
  then `|X|` is `T4` (Hausdorff) and paracompact
  (`TauCeti.thinRealization.t4Space_of_regularSpace_lindelofSpace`,
  `TauCeti.thinRealization.paracompactSpace_of_regularSpace_lindelofSpace`). If every level is
  first-countable (resp. weakly locally compact Hausdorff), `|X|` is compactly generated
  (`TauCeti.thinRealization.uCompactlyGeneratedSpace_of_firstCountable`,
  `TauCeti.thinRealization.compactlyGeneratedSpace_of_weaklyLocallyCompact`).

## References

* G. Segal, *Categories and cohomology theories*, Topology **13** (1974), 293–312, Appendix A.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Propositions A.1 and A.3.
-/

public noncomputable section

open CategoryTheory Limits Opposite Set Topology Convexity

open scoped Simplicial

universe u v

namespace SimplexCategory

/-- Each coface map of topological simplices is a closed embedding. -/
theorem isClosedEmbedding_toTop_map_δ {n : ℕ} (i : Fin (n + 2)) :
    IsClosedEmbedding (toTop.{u}.map (δ i)) := by
  have : CompactSpace (toTop.{u}.obj ⦋n⦌) :=
    inferInstanceAs (CompactSpace (ULift (StdSimplex ℝ (Fin (n + 1)))))
  have : T2Space (toTop.{u}.obj ⦋n + 1⦌) :=
    inferInstanceAs (T2Space (ULift (StdSimplex ℝ (Fin (n + 2)))))
  refine (toTop.{u}.map (δ i)).hom.continuous.isClosedEmbedding fun a b hab ↦ ULift.ext ?_
  exact StdSimplex.map_injective Fin.succAbove_right_injective (congrArg ULift.down hab)

/-- Every topological simplex is second-countable. -/
theorem secondCountableTopology_toTop (n : SimplexCategory) :
    SecondCountableTopology (toTop.{u}.obj n) := by
  have : SecondCountableTopology (StdSimplex ℝ (Fin (n.len + 1))) :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).secondCountableTopology
  exact (Homeomorph.ulift (X := StdSimplex ℝ (Fin (n.len + 1)))).isEmbedding.secondCountableTopology

end SimplexCategory

namespace TauCeti.thinRealization

variable (X : SimplicialObject TopCat.{u})

/-! ### Skeletal filtration -/

/-- The simplicial identifications truncated at degree `n`. -/
private inductive SkeletonRel (n : ℕ) :
    (Σ k : {k : SimplexCategory // k.len ≤ n},
      X.obj (op k.1) × SimplexCategory.toTop.{u}.obj k.1) →
    (Σ k : {k : SimplexCategory // k.len ≤ n},
      X.obj (op k.1) × SimplexCategory.toTop.{u}.obj k.1) → Prop
  | mk {j k : {k : SimplexCategory // k.len ≤ n}} (f : j.1 ⟶ k.1) (x : X.obj (op k.1))
      (t : SimplexCategory.toTop.{u}.obj j.1) :
      SkeletonRel n ⟨j, X.map f.op x, t⟩ ⟨k, x, SimplexCategory.toTop.map f t⟩

/-- The `n`-skeleton `skₙ |X|` of the thin realization: the quotient of
`Σ (k ≤ n), Xₖ × Δᵏ` by all simplicial identifications among degrees at most `n`. -/
def skeleton (n : ℕ) : TopCat.{u} :=
  TopCat.of (Quot (SkeletonRel X n))

namespace skeleton

/-- The characteristic map `Xₖ × Δᵏ → skₙ |X|` for a degree `k ≤ n`. -/
def ι (n : ℕ) (k : SimplexCategory) (hk : k.len ≤ n) :
    C(X.obj (op k) × SimplexCategory.toTop.{u}.obj k, skeleton X n) :=
  ⟨fun p ↦ Quot.mk (SkeletonRel X n) ⟨⟨k, hk⟩, p⟩,
    continuous_quot_mk.comp (continuous_sigmaMk (σ := fun j : {k : SimplexCategory // k.len ≤ n} ↦
      X.obj (op j.1) × SimplexCategory.toTop.{u}.obj j.1))⟩

/-- Characteristic maps into the `n`-skeleton respect all simplicial operators between degrees
at most `n`. -/
@[simp]
theorem ι_map (n : ℕ) {j k : SimplexCategory} (f : j ⟶ k) (hj : j.len ≤ n) (hk : k.len ≤ n)
    (x : X.obj (op k)) (t : SimplexCategory.toTop.{u}.obj j) :
    ι X n j hj (X.map f.op x, t) = ι X n k hk (x, SimplexCategory.toTop.map f t) :=
  Quot.sound (SkeletonRel.mk (j := ⟨j, hj⟩) (k := ⟨k, hk⟩) f x t)

/-- Every point of `skₙ |X|` lies in the image of a characteristic map of degree at most `n`. -/
theorem ι_jointly_surjective (n : ℕ) (p : skeleton X n) :
    ∃ (k : SimplexCategory) (hk : k.len ≤ n) (x : X.obj (op k))
      (t : SimplexCategory.toTop.{u}.obj k), ι X n k hk (x, t) = p := by
  induction p using Quot.ind with
  | mk p => exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩

/-- Two morphisms out of `skₙ |X|` agree once they agree on all simplices of degree at most `n`. -/
@[ext]
theorem hom_ext {n : ℕ} {Z : TopCat.{u}} {g h : skeleton X n ⟶ Z}
    (H : ∀ (k : SimplexCategory) (hk : k.len ≤ n) (x : X.obj (op k))
      (t : SimplexCategory.toTop.{u}.obj k),
      g (ι X n k hk (x, t)) = h (ι X n k hk (x, t))) : g = h := by
  ext p
  obtain ⟨k, hk, x, t, rfl⟩ := ι_jointly_surjective X n p
  exact H k hk x t

/-- The universal property of `skₙ |X|`. -/
def desc {X : SimplicialObject TopCat.{u}} {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    (g : ∀ (k : SimplexCategory), k.len ≤ n → C(X.obj (op k) × SimplexCategory.toTop.{u}.obj k, Z))
    (hg : ∀ ⦃j k : SimplexCategory⦄ (hj : j.len ≤ n) (hk : k.len ≤ n) (f : j ⟶ k)
      (x : X.obj (op k)) (t : SimplexCategory.toTop.{u}.obj j),
      g j hj (X.map f.op x, t) = g k hk (x, SimplexCategory.toTop.map f t)) :
    C(skeleton X n, Z) where
  toFun := Quot.lift (fun p ↦ g p.1.1 p.1.2 p.2)
    (by rintro _ _ ⟨f, x, t⟩; exact hg _ _ f x t)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma fun k ↦ (g k.1 k.2).continuous)

@[simp]
theorem desc_ι {X : SimplicialObject TopCat.{u}} {n : ℕ} {Z : Type*} [TopologicalSpace Z]
    (g : ∀ (k : SimplexCategory), k.len ≤ n → C(X.obj (op k) × SimplexCategory.toTop.{u}.obj k, Z))
    (hg : ∀ ⦃j k : SimplexCategory⦄ (hj : j.len ≤ n) (hk : k.len ≤ n) (f : j ⟶ k)
      (x : X.obj (op k)) (t : SimplexCategory.toTop.{u}.obj j),
      g j hj (X.map f.op x, t) = g k hk (x, SimplexCategory.toTop.map f t))
    (k : SimplexCategory) (hk : k.len ≤ n)
    (p : X.obj (op k) × SimplexCategory.toTop.{u}.obj k) :
    desc g hg (ι X n k hk p) = g k hk p :=
  (rfl)

/-- The canonical transition map `skₘ |X| ⟶ skₙ |X|` for `m ≤ n`. -/
def mapLE {m n : ℕ} (hmn : m ≤ n) : skeleton X m ⟶ skeleton X n :=
  TopCat.ofHom <| desc (fun k hk ↦ ι X n k (hk.trans hmn)) fun _ _ _ _ f x t ↦
    ι_map X n f _ _ x t

@[simp]
theorem mapLE_ι {m n : ℕ} (hmn : m ≤ n) (k : SimplexCategory) (hk : k.len ≤ m)
    (p : X.obj (op k) × SimplexCategory.toTop.{u}.obj k) :
    mapLE X hmn (ι X m k hk p) = ι X n k (hk.trans hmn) p :=
  (rfl)

/-- The canonical morphism `skₙ |X| ⟶ |X|` from the `n`-skeleton to the thin realization. -/
def toRealization (n : ℕ) : skeleton X n ⟶ thinRealization X :=
  TopCat.ofHom <| desc (fun k _ ↦ thinRealization.ι X k) fun _ _ _ _ f x t ↦
    thinRealization.ι_map X f x t

@[simp]
theorem toRealization_ι (n : ℕ) (k : SimplexCategory) (hk : k.len ≤ n)
    (p : X.obj (op k) × SimplexCategory.toTop.{u}.obj k) :
    toRealization X n (ι X n k hk p) = thinRealization.ι X k p :=
  (rfl)

end skeleton

/-- The skeletal filtration of `|X|` as a sequence `ℕ ⥤ TopCat`. -/
@[expose, simps obj map]
def skeletonDiagram : ℕ ⥤ TopCat.{u} where
  obj := skeleton X
  map f := skeleton.mapLE X (leOfHom f)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- The canonical cocone from the skeletal filtration to `|X|`. -/
@[expose]
def skeletonCocone : Cocone (skeletonDiagram X) where
  pt := thinRealization X
  ι :=
    { app := skeleton.toRealization X
      naturality m n f := skeleton.hom_ext X fun k hk x t ↦ by
        change skeleton.toRealization X n (skeleton.mapLE X (leOfHom f)
            (skeleton.ι X m k hk (x, t))) =
          skeleton.toRealization X m (skeleton.ι X m k hk (x, t))
        rw [skeleton.mapLE_ι, skeleton.toRealization_ι, skeleton.toRealization_ι] }

/-- The `n`-th leg of the skeletal cocone agrees with the characteristic map `ι X k` on each
degree `k ≤ n`. -/
theorem skeletonCocone_ι_app_apply (n : ℕ) (k : SimplexCategory) (hk : k.len ≤ n)
    (p : X.obj (op k) × SimplexCategory.toTop.{u}.obj k) :
    (skeletonCocone X).ι.app n (skeleton.ι X n k hk p) = ι X k p :=
  (rfl)

/-- The thin realization `|X|` is the sequential colimit in `TopCat` of its skeletal filtration. -/
def isColimitSkeletonCocone : IsColimit (skeletonCocone X) where
  desc s := TopCat.ofHom <|
    desc (fun k ↦ (s.ι.app k.len).hom.comp (skeleton.ι X k.len k le_rfl)) fun j k f x t ↦ by
      let N := max j.len k.len
      have hj : j.len ≤ N := le_max_left _ _
      have hk : k.len ≤ N := le_max_right _ _
      have h1 : s.ι.app j.len (skeleton.ι X j.len j le_rfl (X.map f.op x, t)) =
          s.ι.app N (skeleton.ι X N j hj (X.map f.op x, t)) := by
        have hw := ConcreteCategory.congr_hom (s.w (homOfLE hj))
          (skeleton.ι X j.len j le_rfl (X.map f.op x, t))
        change s.ι.app N (skeleton.mapLE X hj (skeleton.ι X j.len j le_rfl (X.map f.op x, t))) =
          _ at hw
        rw [skeleton.mapLE_ι] at hw
        exact hw.symm
      have h2 : s.ι.app k.len (skeleton.ι X k.len k le_rfl (x, SimplexCategory.toTop.map f t)) =
          s.ι.app N (skeleton.ι X N k hk (x, SimplexCategory.toTop.map f t)) := by
        have hw := ConcreteCategory.congr_hom (s.w (homOfLE hk))
          (skeleton.ι X k.len k le_rfl (x, SimplexCategory.toTop.map f t))
        change s.ι.app N (skeleton.mapLE X hk
          (skeleton.ι X k.len k le_rfl (x, SimplexCategory.toTop.map f t))) = _ at hw
        rw [skeleton.mapLE_ι] at hw
        exact hw.symm
      change s.ι.app j.len (skeleton.ι X j.len j le_rfl (X.map f.op x, t)) =
        s.ι.app k.len (skeleton.ι X k.len k le_rfl (x, SimplexCategory.toTop.map f t))
      rw [h1, h2, skeleton.ι_map]
  fac s n := skeleton.hom_ext X fun k hk x t ↦ by
    have hw := ConcreteCategory.congr_hom (s.w (homOfLE hk))
      (skeleton.ι X k.len k le_rfl (x, t))
    change s.ι.app n (skeleton.mapLE X hk (skeleton.ι X k.len k le_rfl (x, t))) =
      s.ι.app k.len (skeleton.ι X k.len k le_rfl (x, t)) at hw
    rw [skeleton.mapLE_ι] at hw
    change (desc (fun k ↦ (s.ι.app k.len).hom.comp (skeleton.ι X k.len k le_rfl)) _)
        ((skeletonCocone X).ι.app n (skeleton.ι X n k hk (x, t))) =
      s.ι.app n (skeleton.ι X n k hk (x, t))
    rw [skeletonCocone_ι_app_apply, desc_ι]
    exact hw.symm
  uniq s m hm := hom_ext X fun k x t ↦ by
    have h := ConcreteCategory.congr_hom (hm k.len) (skeleton.ι X k.len k le_rfl (x, t))
    change m ((skeletonCocone X).ι.app k.len (skeleton.ι X k.len k le_rfl (x, t))) =
      s.ι.app k.len (skeleton.ι X k.len k le_rfl (x, t)) at h
    rw [skeletonCocone_ι_app_apply] at h
    change m (ι X k (x, t)) =
      (desc (fun k ↦ (s.ι.app k.len).hom.comp (skeleton.ι X k.len k le_rfl)) _) (ι X k (x, t))
    rw [desc_ι]
    exact h

/-- The `0`-skeleton of `|X|` is homeomorphic to `X _⦋0⦌`. -/
def skeletonZeroHomeomorph : skeleton X 0 ≃ₜ X _⦋0⦌ where
  toFun := skeleton.desc (X := X) (n := 0)
    (fun k hk ↦ match k, hk with
      | ⟨0⟩, _ => ContinuousMap.fst
      | ⟨m + 1⟩, hk => absurd hk (Nat.not_succ_le_zero m))
    (fun j k hj hk f x t ↦ by
      cases j with
      | mk a =>
        cases k with
        | mk b =>
          cases a with
          | zero =>
            cases b with
            | zero =>
              have hf : f = 𝟙 ⦋0⦌ := by
                ext i
                simp [Fin.eq_zero]
              subst hf
              simp
            | succ b => exact absurd hk (Nat.not_succ_le_zero b)
          | succ a => exact absurd hj (Nat.not_succ_le_zero a))
  invFun x := skeleton.ι X 0 ⦋0⦌ le_rfl (x, default)
  left_inv p := by
    obtain ⟨⟨m⟩, hm, x, t, rfl⟩ := skeleton.ι_jointly_surjective X 0 p
    cases m with
    | zero =>
      simp only [skeleton.desc_ι, ContinuousMap.fst_apply]
      rw [Subsingleton.elim t default]
    | succ m => exact absurd hm (Nat.not_succ_le_zero m)
  right_inv _ := rfl
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun := (skeleton.ι X 0 ⦋0⦌ le_rfl).continuous.comp
    (continuous_id.prodMk continuous_const)

/-! ### Skeletal pushout squares -/

/-- The attaching subspace `A_{n+1} = (L_{n+1} X × Δ^{n+1}) ∪ (X_{n+1} × ∂Δ^{n+1})` inside
`X_{n+1} × Δ^{n+1}`. -/
def attachingSet (n : ℕ) : Set (X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) :=
  (⋃ j : Fin (n + 1), range (X.σ j)) ×ˢ univ ∪
    univ ×ˢ (⋃ i : Fin (n + 2), range (SimplexCategory.toTop.{u}.map (SimplexCategory.δ i)))

/-- If every degeneracy `X.σ j` has closed image, then the attaching subspace `A_{n+1}` is closed
in `X_{n+1} × Δ^{n+1}`. -/
theorem isClosed_attachingSet {n : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j))) :
    IsClosed (attachingSet X n) :=
  ((isClosed_iUnion_of_finite hσ).prod isClosed_univ).union
    (isClosed_univ.prod <| isClosed_iUnion_of_finite fun i ↦
      (SimplexCategory.isClosedEmbedding_toTop_map_δ i).isClosed_range)

/-- Overlap compatibility between two degeneracy loci in `skₙ |X|`. -/
private theorem skeleton_ι_σ_eq_σ {n : ℕ} {j k : Fin (n + 1)} {y z : X _⦋n⦌}
    (h : X.σ j y = X.σ k z) (t : SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) :
    skeleton.ι X n ⦋n⦌ le_rfl (y, SimplexCategory.toTop.map (SimplexCategory.σ j) t) =
      skeleton.ι X n ⦋n⦌ le_rfl (z, SimplexCategory.toTop.map (SimplexCategory.σ k) t) := by
  suffices aux : ∀ {j k : Fin (n + 1)} {y z : X _⦋n⦌}, j < k → X.σ j y = X.σ k z →
      skeleton.ι X n ⦋n⦌ le_rfl (y, SimplexCategory.toTop.map (SimplexCategory.σ j) t) =
        skeleton.ι X n ⦋n⦌ le_rfl (z, SimplexCategory.toTop.map (SimplexCategory.σ k) t) by
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact aux hjk h
    · rw [(SimplicialObject.isEmbedding_σ X j).injective h]
    · exact (aux hkj h.symm).symm
  intro j k y z hjk h
  cases n with
  | zero => exact absurd hjk (not_lt_of_ge (le_of_eq ((Fin.eq_zero k).trans (Fin.eq_zero j).symm)))
  | succ m =>
    let a : Fin (m + 1) := j.castPred (Fin.ne_last_of_lt hjk)
    let b : Fin (m + 1) := k.pred (Fin.ne_zero_of_lt hjk)
    have ha : a.castSucc = j := Fin.castSucc_castPred j _
    have hb : b.succ = k := Fin.succ_pred k _
    have hab : a ≤ b := by
      rw [← Fin.castSucc_lt_succ_iff, ha, hb]
      exact hjk
    have hab' : a.castSucc ≤ b.castSucc := Fin.castSucc_le_castSucc_iff.2 hab
    -- Extract the common `(m)`-simplex `w = X.δ a.castSucc z` with `y = X.σ b w` and `z = X.σ a w`.
    let w : X _⦋m⦌ := X.δ a.castSucc z
    have hy : y = X.σ b w := by
      have h1 : X.δ j.castSucc (X.σ j y) = y := by
        rw [← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
          ConcreteCategory.id_apply]
      have h2 : X.δ a.castSucc.castSucc (X.σ b.succ z) = X.σ b (X.δ a.castSucc z) := by
        have hid := congrArg (fun f ↦ X.map f.op z) (SimplexCategory.δ_comp_σ_of_le hab')
        simpa [SimplicialObject.δ, SimplicialObject.σ] using hid
      rw [← h1, h, ← ha, ← hb, h2]
    have hz : z = X.σ a w := by
      apply (SimplicialObject.isEmbedding_σ X k).injective
      have hid := congrArg (fun f ↦ X.map f.op w) (SimplexCategory.σ_comp_σ hab)
      have hid' : X.σ a.castSucc (X.σ b w) = X.σ b.succ (X.σ a w) := by
        simpa [SimplicialObject.σ] using hid
      rw [← h, hy, ← ha, ← hb, hid']
    rw [hy, hz]
    calc
      skeleton.ι X (m + 1) ⦋m + 1⦌ le_rfl
          (X.σ b w, SimplexCategory.toTop.map (SimplexCategory.σ j) t)
        = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ
            (w, SimplexCategory.toTop.map (SimplexCategory.σ b)
              (SimplexCategory.toTop.map (SimplexCategory.σ j) t)) :=
          skeleton.ι_map X (m + 1) (SimplexCategory.σ b) le_rfl m.le_succ w _
      _ = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ
            (w, SimplexCategory.toTop.map
              (SimplexCategory.σ a.castSucc ≫ SimplexCategory.σ b) t) := by
          rw [← ha, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ
            (w, SimplexCategory.toTop.map (SimplexCategory.σ b.succ ≫ SimplexCategory.σ a) t) := by
          rw [SimplexCategory.σ_comp_σ hab]
      _ = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ
            (w, SimplexCategory.toTop.map (SimplexCategory.σ a)
              (SimplexCategory.toTop.map (SimplexCategory.σ k) t)) := by
          rw [← hb, Functor.map_comp, ConcreteCategory.comp_apply]
      _ = skeleton.ι X (m + 1) ⦋m + 1⦌ le_rfl
            (X.σ a w, SimplexCategory.toTop.map (SimplexCategory.σ k) t) :=
          (skeleton.ι_map X (m + 1) (SimplexCategory.σ a) le_rfl m.le_succ w _).symm

/-- Overlap compatibility between two boundary faces in `skₙ |X|`. -/
private theorem skeleton_ι_δ_eq_δ {n : ℕ} {i l : Fin (n + 2)}
    {u v : SimplexCategory.toTop.{u}.obj ⦋n⦌}
    (h : SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u =
      SimplexCategory.toTop.{u}.map (SimplexCategory.δ l) v)
    (x : X _⦋n + 1⦌) :
    skeleton.ι X n ⦋n⦌ le_rfl (X.δ i x, u) = skeleton.ι X n ⦋n⦌ le_rfl (X.δ l x, v) := by
  suffices aux : ∀ {i l : Fin (n + 2)} {u v : SimplexCategory.toTop.{u}.obj ⦋n⦌}, i < l →
      SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u =
        SimplexCategory.toTop.{u}.map (SimplexCategory.δ l) v →
      skeleton.ι X n ⦋n⦌ le_rfl (X.δ i x, u) = skeleton.ι X n ⦋n⦌ le_rfl (X.δ l x, v) by
    rcases lt_trichotomy i l with hil | rfl | hli
    · exact aux hil h
    · rw [(SimplexCategory.isClosedEmbedding_toTop_map_δ i).injective h]
    · exact (aux hli h.symm).symm
  intro i l u v hil h
  cases n with
  | zero =>
    have hlt : i.val < l.val := hil
    have hi : i = 0 := Fin.ext (show i.val = 0 by omega)
    have hl : l = 1 := Fin.ext (show l.val = 1 by omega)
    subst hi hl
    have hw0 : (u.down.map (0 : Fin 2).succAbove).weights 0 = 0 :=
      StdSimplex.weights_map_succAbove_self 0 u.down
    have hw1 : (u.down.map (0 : Fin 2).succAbove).weights 1 = 0 := by
      have hdown : u.down.map (0 : Fin 2).succAbove = v.down.map (1 : Fin 2).succAbove :=
        congrArg ULift.down h
      rw [hdown]
      exact StdSimplex.weights_map_succAbove_self 1 v.down
    have htot := StdSimplex.total_fin_two (u.down.map (0 : Fin 2).succAbove)
    linarith
  | succ m =>
    obtain ⟨w, hu, hv⟩ := StdSimplex.exists_map_succAbove_of_map_succAbove_eq hil
      (congrArg ULift.down h)
    let i' : Fin (m + 2) := i.castPred (Fin.ne_last_of_lt hil)
    let l' : Fin (m + 2) := l.pred (Fin.ne_zero_of_lt hil)
    have hi' : i'.castSucc = i := Fin.castSucc_castPred i _
    have hl' : l'.succ = l := Fin.succ_pred l _
    have hil' : i' ≤ l' := by
      rw [← Fin.castSucc_lt_succ_iff, hi', hl']
      exact hil
    have hu' : u = SimplexCategory.toTop.{u}.map (SimplexCategory.δ l') ⟨w⟩ := ULift.ext hu
    have hv' : v = SimplexCategory.toTop.{u}.map (SimplexCategory.δ i') ⟨w⟩ := ULift.ext hv
    have hid : X.δ l' (X.δ i x) = X.δ i' (X.δ l x) := by
      have hid0 := congrArg (fun f ↦ X.map f.op x) (SimplexCategory.δ_comp_δ hil')
      simpa [SimplicialObject.δ, hi', hl'] using hid0.symm
    rw [hu', hv']
    calc
      skeleton.ι X (m + 1) ⦋m + 1⦌ le_rfl
          (X.δ i x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ l') ⟨w⟩)
        = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ (X.δ l' (X.δ i x), ⟨w⟩) :=
          (skeleton.ι_map X (m + 1) (SimplexCategory.δ l') m.le_succ le_rfl _ _).symm
      _ = skeleton.ι X (m + 1) ⦋m⦌ m.le_succ (X.δ i' (X.δ l x), ⟨w⟩) := by rw [hid]
      _ = skeleton.ι X (m + 1) ⦋m + 1⦌ le_rfl
            (X.δ l x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i') ⟨w⟩) :=
          skeleton.ι_map X (m + 1) (SimplexCategory.δ i') m.le_succ le_rfl _ _

/-- Overlap compatibility between a degeneracy locus and a boundary face in `skₙ |X|`. -/
private theorem skeleton_ι_σ_eq_δ {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 2))
    (y : X _⦋n⦌) (u : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    skeleton.ι X n ⦋n⦌ le_rfl
        (y, SimplexCategory.toTop.map (SimplexCategory.σ j)
          (SimplexCategory.toTop.map (SimplexCategory.δ i) u)) =
      skeleton.ι X n ⦋n⦌ le_rfl (X.δ i (X.σ j y), u) := by
  have h1 : X.δ i (X.σ j y) = X.map (SimplexCategory.δ i ≫ SimplexCategory.σ j).op y := by
    simp [SimplicialObject.δ, SimplicialObject.σ]
  have h2 : SimplexCategory.toTop.{u}.map (SimplexCategory.σ j)
      (SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u) =
      SimplexCategory.toTop.{u}.map (SimplexCategory.δ i ≫ SimplexCategory.σ j) u := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
  rw [h1, h2]
  exact (skeleton.ι_map X n (SimplexCategory.δ i ≫ SimplexCategory.σ j) le_rfl le_rfl y u).symm

/-- Underlying function of the attaching map `A_{n+1} → skₙ |X|`. -/
private def attachMapFun (n : ℕ) (p : attachingSet X n) : skeleton X n :=
  open Classical in
  if h : ∃ j : Fin (n + 1), p.1.1 ∈ range (X.σ j) then
    skeleton.ι X n ⦋n⦌ le_rfl
      (X.δ h.choose.castSucc p.1.1,
        SimplexCategory.toTop.map (SimplexCategory.σ h.choose) p.1.2)
  else
    have hδ : ∃ i : Fin (n + 2),
        p.1.2 ∈ range (SimplexCategory.toTop.{u}.map (SimplexCategory.δ i)) := by
      rcases p.2 with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd (mem_iUnion.1 h1) h
      · exact mem_iUnion.1 h2
    skeleton.ι X n ⦋n⦌ le_rfl (X.δ hδ.choose p.1.1, hδ.choose_spec.choose)

private theorem attachMapFun_of_mem_range_σ {n : ℕ} (j : Fin (n + 1)) (y : X _⦋n⦌)
    (t : SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) (hp : (X.σ j y, t) ∈ attachingSet X n) :
    attachMapFun X n ⟨(X.σ j y, t), hp⟩ =
      skeleton.ι X n ⦋n⦌ le_rfl (y, SimplexCategory.toTop.map (SimplexCategory.σ j) t) := by
  classical
  have hex : ∃ k : Fin (n + 1), X.σ j y ∈ range (X.σ k) := ⟨j, y, rfl⟩
  simp only [attachMapFun, hex, ↓reduceDIte]
  obtain ⟨z, hz⟩ := hex.choose_spec
  have hz' : X.δ hex.choose.castSucc (X.σ j y) = z := by
    have hret := ConcreteCategory.congr_hom
      (SimplicialObject.δ_comp_σ_self (X := X) (i := hex.choose)) z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.id_apply, hz] at hret
    exact hret
  rw [hz']
  exact skeleton_ι_σ_eq_σ X hz t

private theorem attachMapFun_of_mem_range_δ {n : ℕ} (i : Fin (n + 2)) (x : X _⦋n + 1⦌)
    (u : SimplexCategory.toTop.{u}.obj ⦋n⦌)
    (hp : (x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u) ∈ attachingSet X n) :
    attachMapFun X n ⟨(x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u), hp⟩ =
      skeleton.ι X n ⦋n⦌ le_rfl (X.δ i x, u) := by
  classical
  by_cases h : ∃ j : Fin (n + 1), x ∈ range (X.σ j)
  · obtain ⟨j, y, rfl⟩ := h
    rw [attachMapFun_of_mem_range_σ X j y _ hp]
    exact skeleton_ι_σ_eq_δ X j i y u
  · simp only [attachMapFun, h, ↓reduceDIte]
    have hδ : ∃ l : Fin (n + 2),
        SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u ∈
          range (SimplexCategory.toTop.{u}.map (SimplexCategory.δ l)) := ⟨i, u, rfl⟩
    exact skeleton_ι_δ_eq_δ X hδ.choose_spec.choose_spec x

private theorem continuous_attachMapFun {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j))) :
    Continuous (attachMapFun X n) := by
  -- Cover `attachingSet X n` by the finitely many closed degeneracy pieces and boundary faces.
  let D (j : Fin (n + 1)) : Set (attachingSet X n) :=
    Subtype.val ⁻¹' (range (X.σ j) ×ˢ univ)
  let e (i : Fin (n + 2)) :
      X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌ → attachingSet X n :=
    fun q ↦ ⟨(q.1, SimplexCategory.toTop.map (SimplexCategory.δ i) q.2),
      Or.inr ⟨mem_univ _, mem_iUnion.2 ⟨i, q.2, rfl⟩⟩⟩
  have hDclosed (j : Fin (n + 1)) : IsClosed (D j) :=
    ((hσ j).prod isClosed_univ).preimage continuous_subtype_val
  have he (i : Fin (n + 2)) : IsClosedEmbedding (e i) := by
    have hprod : IsClosedEmbedding (Prod.map (id : X _⦋n + 1⦌ → X _⦋n + 1⦌)
        (SimplexCategory.toTop.{u}.map (SimplexCategory.δ i))) :=
      IsClosedEmbedding.id.prodMap (SimplexCategory.isClosedEmbedding_toTop_map_δ i)
    exact (IsClosedEmbedding.of_comp_iff
      (isClosed_attachingSet X hσ).isClosedEmbedding_subtypeVal).1 hprod
  have hcover : (⋃ j, D j) ∪ (⋃ i, range (e i)) = univ := by
    ext ⟨⟨x, t⟩, hp⟩
    simp only [mem_union, mem_iUnion, mem_preimage, mem_prod, mem_univ, and_true, mem_range,
      iff_true, D, e]
    rcases hp with ⟨hx, -⟩ | ⟨-, ht⟩
    · exact Or.inl (mem_iUnion.1 hx)
    · obtain ⟨i, u, rfl⟩ := mem_iUnion.1 ht
      exact Or.inr ⟨i, (x, u), rfl⟩
  have hDcont : ContinuousOn (attachMapFun X n) (⋃ j, D j) :=
    (locallyFinite_of_finite _).continuousOn_iUnion hDclosed fun j ↦ by
      have hg : Continuous fun p : attachingSet X n ↦
          skeleton.ι X n ⦋n⦌ le_rfl (X.δ j.castSucc p.1.1,
            SimplexCategory.toTop.map (SimplexCategory.σ j) p.1.2) :=
        (skeleton.ι X n ⦋n⦌ le_rfl).continuous.comp <|
          ((X.δ j.castSucc).hom.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
            ((SimplexCategory.toTop.map (SimplexCategory.σ j)).hom.continuous.comp
              (continuous_snd.comp continuous_subtype_val))
      refine hg.continuousOn.congr fun p hp ↦ ?_
      obtain ⟨y, hy⟩ := hp.1
      have h1 : X.δ j.castSucc p.1.1 = y := by
        rw [← hy, ← ConcreteCategory.comp_apply, SimplicialObject.δ_comp_σ_self,
          ConcreteCategory.id_apply]
      rcases p with ⟨⟨x, t⟩, hpmem⟩
      dsimp only at hy h1 ⊢
      subst hy
      rw [h1, attachMapFun_of_mem_range_σ X j y t hpmem]
  have hFcont : ContinuousOn (attachMapFun X n) (⋃ i, range (e i)) :=
    (locallyFinite_of_finite _).continuousOn_iUnion (fun i ↦ (he i).isClosed_range) fun i ↦ by
      rw [← image_univ, (he i).isInducing.continuousOn_image_iff]
      have hg : Continuous fun q : X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌ ↦
          skeleton.ι X n ⦋n⦌ le_rfl (X.δ i q.1, q.2) :=
        (skeleton.ι X n ⦋n⦌ le_rfl).continuous.comp <|
          ((X.δ i).hom.continuous.comp continuous_fst).prodMk continuous_snd
      exact (hg.congr fun ⟨x, u⟩ ↦ (attachMapFun_of_mem_range_δ X i x u _).symm).continuousOn
  rw [← continuousOn_univ, ← hcover]
  exact hDcont.union_of_isClosed hFcont (isClosed_iUnion_of_finite hDclosed)
    (isClosed_iUnion_of_finite fun i ↦ (he i).isClosed_range)

/-- The attaching map `A_{n+1} ⟶ skₙ |X|` from the closed attaching subspace of
`X_{n+1} × Δ^{n+1}` to the `n`-skeleton. -/
def attachMap {n : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j))) :
    TopCat.of (attachingSet X n) ⟶ skeleton X n :=
  TopCat.ofHom ⟨attachMapFun X n, continuous_attachMapFun X hσ⟩

/-- On the image of the `j`-th degeneracy, the attaching map collapses the simplex along `σ j`. -/
theorem attachMap_of_mem_range_σ {n : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j)))
    (j : Fin (n + 1)) (y : X _⦋n⦌) (t : SimplexCategory.toTop.{u}.obj ⦋n + 1⦌)
    (hp : (X.σ j y, t) ∈ attachingSet X n) :
    attachMap X hσ ⟨(X.σ j y, t), hp⟩ =
      skeleton.ι X n ⦋n⦌ le_rfl (y, SimplexCategory.toTop.map (SimplexCategory.σ j) t) :=
  attachMapFun_of_mem_range_σ X j y t hp

/-- On the `i`-th boundary face of `Δ^{n+1}`, the attaching map applies `X.δ i`. -/
theorem attachMap_of_mem_range_δ {n : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j)))
    (i : Fin (n + 2)) (x : X _⦋n + 1⦌) (u : SimplexCategory.toTop.{u}.obj ⦋n⦌)
    (hp : (x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u) ∈ attachingSet X n) :
    attachMap X hσ ⟨(x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u), hp⟩ =
      skeleton.ι X n ⦋n⦌ le_rfl (X.δ i x, u) :=
  attachMapFun_of_mem_range_δ X i x u hp

/-- **Skeletal pushout square.** When every degeneracy `X.σ j` has closed image in `X_{n+1}`, the
`(n + 1)`-skeleton `sk_{n+1} |X|` is the pushout in `TopCat` of `skₙ |X|` and `X_{n+1} × Δ^{n+1}`
along the closed attaching subspace `A_{n+1}`. -/
theorem isPushout_skeleton {n : ℕ} (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j))) :
    IsPushout (attachMap X hσ)
      (TopCat.ofHom (Y := TopCat.of (X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n + 1⦌))
        ⟨Subtype.val, continuous_subtype_val⟩)
      ((skeletonDiagram X).map (homOfLE n.le_succ))
      (TopCat.ofHom (skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl)) := by
  have hcomm :
      attachMap X hσ ≫ (skeletonDiagram X).map (homOfLE n.le_succ) =
        TopCat.ofHom (Y := TopCat.of (X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n + 1⦌))
          ⟨Subtype.val, continuous_subtype_val⟩ ≫
          TopCat.ofHom (skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl) := by
    ext ⟨⟨x, t⟩, hp⟩
    rcases hp with h | h
    · obtain ⟨j, y, rfl⟩ := mem_iUnion.1 h.1
      change skeleton.mapLE X n.le_succ (attachMap X hσ ⟨(X.σ j y, t), Or.inl h⟩) =
        skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl (X.σ j y, t)
      rw [attachMap_of_mem_range_σ X hσ j y t (Or.inl h), skeleton.mapLE_ι]
      exact (skeleton.ι_map X (n + 1) (SimplexCategory.σ j) le_rfl n.le_succ y t).symm
    · obtain ⟨i, u, rfl⟩ := mem_iUnion.1 h.2
      change skeleton.mapLE X n.le_succ
          (attachMap X hσ ⟨(x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u), Or.inr h⟩) =
        skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl
          (x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i) u)
      rw [attachMap_of_mem_range_δ X hσ i x u (Or.inr h), skeleton.mapLE_ι]
      exact skeleton.ι_map X (n + 1) (SimplexCategory.δ i) n.le_succ le_rfl x u
  let g (s : PushoutCocone (attachMap X hσ)
      (TopCat.ofHom (Y := TopCat.of (X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n + 1⦌))
        ⟨Subtype.val, continuous_subtype_val⟩)) :
      ∀ (k : SimplexCategory), k.len ≤ n + 1 →
        C(X.obj (op k) × SimplexCategory.toTop.{u}.obj k, s.pt) :=
    fun k hk ↦
      if hle : k.len ≤ n then
        s.inl.hom.comp (skeleton.ι X n k hle)
      else
        have heq : k = ⦋n + 1⦌ := SimplexCategory.ext (show k.len = n + 1 by omega)
        heq ▸ s.inr.hom
  have hg_le (s) (k : SimplexCategory) (hle : k.len ≤ n) (p) :
      g s k (hle.trans n.le_succ) p = s.inl (skeleton.ι X n k hle p) := by
    simp [g, hle]
  have hg_top (s) (p) : g s ⦋n + 1⦌ le_rfl p = s.inr p := by
    simp [g]
  have hg (s) : ∀ ⦃j k : SimplexCategory⦄ (hj : j.len ≤ n + 1) (hk : k.len ≤ n + 1)
      (f : j ⟶ k) (x : X.obj (op k)) (t : SimplexCategory.toTop.{u}.obj j),
      g s j hj (X.map f.op x, t) = g s k hk (x, SimplexCategory.toTop.map f t) := by
    have hcase_lt_top (a : SimplexCategory) (ha : a.len ≤ n) (f : a ⟶ ⦋n + 1⦌)
        (x : X _⦋n + 1⦌) (t : SimplexCategory.toTop.{u}.obj a) :
        s.inl (skeleton.ι X n a ha (X.map f.op x, t)) =
          s.inr (x, SimplexCategory.toTop.map f t) := by
      have hnsurj : ¬Function.Surjective f.toOrderHom := fun hsurj ↦ by
        have hcard := Fintype.card_le_of_surjective f.toOrderHom hsurj
        simp only [Fintype.card_fin] at hcard
        omega
      obtain ⟨i, f', rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f hnsurj
      have hmem : (x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i)
          (SimplexCategory.toTop.{u}.map f' t)) ∈ attachingSet X n :=
        Or.inr ⟨mem_univ _, mem_iUnion.2 ⟨i, _, rfl⟩⟩
      have hcond := ConcreteCategory.congr_hom s.condition ⟨_, hmem⟩
      change s.inl (attachMap X hσ ⟨_, hmem⟩) =
        s.inr (x, SimplexCategory.toTop.{u}.map (SimplexCategory.δ i)
          (SimplexCategory.toTop.{u}.map f' t)) at hcond
      rw [attachMap_of_mem_range_δ X hσ i x _ hmem] at hcond
      rw [Functor.map_comp, ConcreteCategory.comp_apply, ← hcond]
      congr 1
      have hmap : X.map (f' ≫ SimplexCategory.δ i).op x = X.map f'.op (X.δ i x) := by
        simp [SimplicialObject.δ]
      rw [hmap]
      exact skeleton.ι_map X n f' ha le_rfl (X.δ i x) t
    have hcase_top_lt (b : SimplexCategory) (hb : b.len ≤ n) (f : ⦋n + 1⦌ ⟶ b)
        (x : X.obj (op b)) (t : SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) :
        s.inr (X.map f.op x, t) =
          s.inl (skeleton.ι X n b hb (x, SimplexCategory.toTop.map f t)) := by
      have hninj : ¬Function.Injective f.toOrderHom := fun hinj ↦ by
        have hcard := Fintype.card_le_of_injective f.toOrderHom hinj
        simp only [Fintype.card_fin] at hcard
        omega
      obtain ⟨j, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hninj
      have hmap : X.map (SimplexCategory.σ j ≫ f').op x = X.σ j (X.map f'.op x) := by
        simp [SimplicialObject.σ]
      have hmem : (X.σ j (X.map f'.op x), t) ∈ attachingSet X n :=
        Or.inl ⟨mem_iUnion.2 ⟨j, _, rfl⟩, mem_univ _⟩
      have hcond := ConcreteCategory.congr_hom s.condition ⟨_, hmem⟩
      change s.inl (attachMap X hσ ⟨_, hmem⟩) = s.inr (X.σ j (X.map f'.op x), t) at hcond
      rw [attachMap_of_mem_range_σ X hσ j _ t hmem] at hcond
      rw [hmap, ← hcond, Functor.map_comp, ConcreteCategory.comp_apply]
      congr 1
      exact skeleton.ι_map X n f' le_rfl hb x _
    intro j k hj hk f x t
    by_cases hj' : j.len ≤ n <;> by_cases hk' : k.len ≤ n
    · rw [hg_le s j hj', hg_le s k hk', skeleton.ι_map]
    · obtain rfl : k = ⦋n + 1⦌ := SimplexCategory.ext (show k.len = n + 1 by omega)
      rw [hg_le s j hj', hg_top s]
      exact hcase_lt_top j hj' f x t
    · obtain rfl : j = ⦋n + 1⦌ := SimplexCategory.ext (show j.len = n + 1 by omega)
      rw [hg_top s, hg_le s k hk']
      exact hcase_top_lt k hk' f x t
    · obtain rfl : j = ⦋n + 1⦌ := SimplexCategory.ext (show j.len = n + 1 by omega)
      obtain rfl : k = ⦋n + 1⦌ := SimplexCategory.ext (show k.len = n + 1 by omega)
      rw [hg_top s, hg_top s]
      by_cases hfid : f = 𝟙 ⦋n + 1⦌
      · subst hfid
        rw [op_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
        rfl
      · have hninj : ¬Function.Injective f.toOrderHom := fun hinj ↦ by
          have : Mono f := SimplexCategory.mono_iff_injective.2 hinj
          exact hfid (SimplexCategory.eq_id_of_mono f)
        obtain ⟨j, f', rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f hninj
        have h1 := hcase_top_lt ⦋n⦌ le_rfl (SimplexCategory.σ j) (X.map f'.op x) t
        have h2 := hcase_lt_top ⦋n⦌ le_rfl f' x
          (SimplexCategory.toTop.{u}.map (SimplexCategory.σ j) t)
        have hmap : X.map (SimplexCategory.σ j ≫ f').op x =
            X.map (SimplexCategory.σ j).op (X.map f'.op x) := by simp
        rw [hmap, h1, h2, Functor.map_comp, ConcreteCategory.comp_apply]
  let pushoutDesc s := TopCat.ofHom (skeleton.desc (g s) (hg s))
  have hdesc_le (s) (k : SimplexCategory) (hk : k.len ≤ n) (p) :
      pushoutDesc s (skeleton.ι X (n + 1) k (hk.trans n.le_succ) p) =
        s.inl (skeleton.ι X n k hk p) :=
    (skeleton.desc_ι (g s) (hg s) k (hk.trans n.le_succ) p).trans (hg_le s k hk p)
  have hdesc_top (s) (p) :
      pushoutDesc s (skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl p) = s.inr p :=
    (skeleton.desc_ι (g s) (hg s) ⦋n + 1⦌ le_rfl p).trans (hg_top s p)
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hcomm) <|
    PushoutCocone.IsColimit.mk hcomm pushoutDesc (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
  · refine skeleton.hom_ext X fun k hk x t ↦ ?_
    change pushoutDesc s (skeleton.mapLE X n.le_succ (skeleton.ι X n k hk (x, t))) = _
    rw [skeleton.mapLE_ι, hdesc_le]
  · ext ⟨x, t⟩
    exact hdesc_top s (x, t)
  · refine skeleton.hom_ext X fun k hk x t ↦ ?_
    by_cases hle : k.len ≤ n
    · have h1 := ConcreteCategory.congr_hom hm₁ (skeleton.ι X n k hle (x, t))
      change m (skeleton.mapLE X n.le_succ (skeleton.ι X n k hle (x, t))) = _ at h1
      rw [skeleton.mapLE_ι] at h1
      exact h1.trans (hdesc_le s k hle (x, t)).symm
    · have hk' : k.len = n + 1 := by
        change k.len ≤ n + 1 at hk
        omega
      obtain rfl : k = ⦋n + 1⦌ := SimplexCategory.ext hk'
      have h2 := ConcreteCategory.congr_hom hm₂ (x, t)
      change m (skeleton.ι X (n + 1) ⦋n + 1⦌ le_rfl (x, t)) = s.inr (x, t) at h2
      exact h2.trans (hdesc_top s (x, t)).symm

/-! ### Topological properties from the skeletal filtration -/

section ClosedDegeneracy

variable {X}

/-- Every successor map `skₙ |X| ⟶ sk_{n+1} |X|` is a closed embedding when degeneracies into
level `n + 1` have closed image. -/
theorem isClosedEmbedding_skeletonDiagram_map_succ {n : ℕ}
    (hσ : ∀ j : Fin (n + 1), IsClosed (range (X.σ j))) :
    IsClosedEmbedding ((skeletonDiagram X).map (homOfLE n.le_succ)) :=
  TauCeti.TopCat.isClosedEmbedding_of_isPushout (isPushout_skeleton X hσ)
    (isClosed_attachingSet X hσ).isClosedEmbedding_subtypeVal

variable (hσ : ∀ (n : ℕ) (j : Fin (n + 1)), IsClosed (range (X.σ j)))
include hσ

/-- The inclusion of each skeleton `skₙ |X| ⟶ |X|` is a closed embedding when all degeneracies
have closed image. -/
theorem isClosedEmbedding_skeletonCocone_ι (n : ℕ) :
    IsClosedEmbedding ((skeletonCocone X).ι.app n) :=
  TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit_of_succ
    (fun k ↦ isClosedEmbedding_skeletonDiagram_map_succ (hσ k))
    (isColimitSkeletonCocone X) n

/-- Every skeleton `skₙ |X|` is `T1` when all degeneracies have closed image and every level is
`T1`. -/
theorem t1Space_skeleton [hX : ∀ n : ℕ, T1Space (X _⦋n⦌)] (n : ℕ) : T1Space (skeleton X n) := by
  induction n with
  | zero => exact (skeletonZeroHomeomorph X).symm.t1Space
  | succ n ih =>
    have : T1Space (X _⦋n + 1⦌) := hX (n + 1)
    have : T2Space (SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) :=
      inferInstanceAs (T2Space (ULift (StdSimplex ℝ (Fin (n + 2)))))
    exact TauCeti.TopCat.t1Space_of_isPushout (isPushout_skeleton X (hσ n))
      (isClosed_attachingSet X (hσ n)).isClosedEmbedding_subtypeVal

/-- The thin realization `|X|` is `T1` when all degeneracies have closed image and every level is
`T1`. -/
theorem t1Space [∀ n : ℕ, T1Space (X _⦋n⦌)] : T1Space (thinRealization X) := by
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton hσ
  exact TauCeti.TopCat.t1Space_of_isColimit
    (fun _ _ hij ↦ (TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous
      (skeletonDiagram X)
      (fun n _ ↦ isClosedEmbedding_skeletonDiagram_map_succ (hσ n)) hij).injective)
    (isColimitSkeletonCocone X)

/-- Every skeleton `skₙ |X|` is normal when all degeneracies have closed image and every product
`Xₙ × Δⁿ` is normal. -/
theorem normalSpace_skeleton
    [hX : ∀ n : ℕ, NormalSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] (n : ℕ) :
    NormalSpace (skeleton X n) := by
  induction n with
  | zero =>
    have : NormalSpace (X _⦋0⦌ × SimplexCategory.toTop.{u}.obj ⦋0⦌) := hX 0
    let e : skeleton X 0 ≃ₜ X _⦋0⦌ × SimplexCategory.toTop.{u}.obj ⦋0⦌ :=
      (skeletonZeroHomeomorph X).trans (Homeomorph.prodUnique _ _).symm
    exact e.isClosedEmbedding.normalSpace
  | succ n ih =>
    have : NormalSpace (X _⦋n + 1⦌ × SimplexCategory.toTop.{u}.obj ⦋n + 1⦌) := hX (n + 1)
    exact TauCeti.TopCat.normalSpace_of_isPushout (isPushout_skeleton X (hσ n))
      (isClosed_attachingSet X (hσ n)).isClosedEmbedding_subtypeVal

/-- The thin realization `|X|` is normal when all degeneracies have closed image and every product
`Xₙ × Δⁿ` is normal. -/
theorem normalSpace
    [∀ n : ℕ, NormalSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] :
    NormalSpace (thinRealization X) := by
  have : ∀ n, NormalSpace ((skeletonDiagram X).obj n) := normalSpace_skeleton hσ
  exact TauCeti.TopCat.normalSpace_of_isColimit
    (fun n ↦ isClosedEmbedding_skeletonDiagram_map_succ (hσ n)) (isColimitSkeletonCocone X)

/-- The thin realization `|X|` is `T4` (normal and `T1`, hence Hausdorff) when all degeneracies
have closed image, every level is `T1`, and every product `Xₙ × Δⁿ` is normal. -/
theorem t4Space [∀ n : ℕ, T1Space (X _⦋n⦌)]
    [∀ n : ℕ, NormalSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] :
    T4Space (thinRealization X) :=
  have := t1Space hσ
  have := normalSpace hσ
  {}

/-- The thin realization `|X|` is paracompact when all degeneracies have closed image, every level
is `T1` and Lindelöf, and every product `Xₙ × Δⁿ` is normal. -/
theorem paracompactSpace [∀ n : ℕ, T1Space (X _⦋n⦌)] [∀ n : ℕ, LindelofSpace (X _⦋n⦌)]
    [∀ n : ℕ, NormalSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌)] :
    ParacompactSpace (thinRealization X) :=
  have := t4Space hσ
  have := lindelofSpace X
  inferInstance

/-- Every compact subset of `|X|` lies in the image of a single finite skeleton `skₙ |X|`, when
all degeneracies have closed image and every level is `T1`. -/
theorem exists_subset_range_skeleton_of_isCompact [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Set (thinRealization X)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ range ((skeletonCocone X).ι.app n) := by
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton hσ
  exact TauCeti.TopCat.exists_subset_range_ι_of_isCompact
    (fun _ _ hij ↦ (TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous
      (skeletonDiagram X)
      (fun n _ ↦ isClosedEmbedding_skeletonDiagram_map_succ (hσ n)) hij).injective)
    (isColimitSkeletonCocone X) hK

/-- Every continuous map from a compact space into `|X|` factors continuously through a single
finite skeleton `skₙ |X|`, when all degeneracies have closed image and every level is `T1`. -/
theorem exists_lift_skeleton_of_compactSpace [∀ n : ℕ, T1Space (X _⦋n⦌)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinRealization X)) :
    ∃ (n : ℕ) (g' : C(K, skeleton X n)), ((skeletonCocone X).ι.app n).hom.comp g' = g := by
  have : ∀ n, T1Space ((skeletonDiagram X).obj n) := t1Space_skeleton hσ
  exact TauCeti.TopCat.exists_lift_of_compactSpace (isColimitSkeletonCocone X)
    (fun n ↦ (isClosedEmbedding_skeletonCocone_ι hσ n).isEmbedding) g

end ClosedDegeneracy

/-! ### High-level corollaries for regular Lindelöf and compactly generated levels -/

section Corollaries

/-- If every level `Xₙ` is regular, `T1`, and Lindelöf (in particular, if every level is a
second-countable regular `T1` space or a compact Hausdorff space), then `|X|` is `T4` (hence
Hausdorff). -/
theorem t4Space_of_regularSpace_lindelofSpace
    [hR : ∀ n : ℕ, RegularSpace (X _⦋n⦌)] [hT : ∀ n : ℕ, T1Space (X _⦋n⦌)]
    [hL : ∀ n : ℕ, LindelofSpace (X _⦋n⦌)] : T4Space (thinRealization X) := by
  have hσ (n : ℕ) (j : Fin (n + 1)) : IsClosed (range (X.σ j)) := by
    have : RegularSpace (X _⦋n + 1⦌) := hR (n + 1)
    have : T1Space (X _⦋n + 1⦌) := hT (n + 1)
    exact (SimplicialObject.isClosedEmbedding_σ X j).isClosed_range
  have hN (n : ℕ) : NormalSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌) := by
    have : RegularSpace (X _⦋n⦌) := hR n
    have : LindelofSpace (X _⦋n⦌) := hL n
    have : CompactSpace (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
      inferInstanceAs (CompactSpace (ULift (StdSimplex ℝ (Fin (n + 1)))))
    have : T2Space (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
      inferInstanceAs (T2Space (ULift (StdSimplex ℝ (Fin (n + 1)))))
    have : LindelofSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
      lindelofSpace_prod_of_compactSpace_right
    exact NormalSpace.of_regularSpace_lindelofSpace
  exact t4Space hσ

/-- If every level `Xₙ` is regular, `T1`, and Lindelöf (covering both second-countable regular `T1`
spaces and compact Hausdorff spaces), then `|X|` is paracompact. -/
theorem paracompactSpace_of_regularSpace_lindelofSpace
    [∀ n : ℕ, RegularSpace (X _⦋n⦌)] [∀ n : ℕ, T1Space (X _⦋n⦌)]
    [∀ n : ℕ, LindelofSpace (X _⦋n⦌)] : ParacompactSpace (thinRealization X) :=
  have := t4Space_of_regularSpace_lindelofSpace X
  have := lindelofSpace X
  inferInstance

/-- If every level `Xₙ` is first-countable (in particular, second-countable), then `|X|` is
compactly generated in every universe `v`. -/
theorem uCompactlyGeneratedSpace_of_firstCountable
    [hF : ∀ n : ℕ, FirstCountableTopology (X _⦋n⦌)] :
    UCompactlyGeneratedSpace.{v} (thinRealization X) := by
  have : ∀ n : ℕ, UCompactlyGeneratedSpace.{v} (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
    fun n ↦ by
      have : FirstCountableTopology (X _⦋n⦌) := hF n
      have : SecondCountableTopology (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
        SimplexCategory.secondCountableTopology_toTop ⦋n⦌
      infer_instance
  exact uCompactlyGeneratedSpace X

/-- If every level `Xₙ` is weakly locally compact and Hausdorff (in particular, compact Hausdorff
or a locally compact Hausdorff manifold), then `|X|` is compactly generated. -/
theorem compactlyGeneratedSpace_of_weaklyLocallyCompact
    [hL : ∀ n : ℕ, WeaklyLocallyCompactSpace (X _⦋n⦌)] [hT : ∀ n : ℕ, T2Space (X _⦋n⦌)] :
    CompactlyGeneratedSpace (thinRealization X) := by
  have : ∀ n : ℕ, CompactlyGeneratedSpace (X _⦋n⦌ × SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
    fun n ↦ by
      have : WeaklyLocallyCompactSpace (X _⦋n⦌) := hL n
      have : T2Space (X _⦋n⦌) := hT n
      have : CompactSpace (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
        inferInstanceAs (CompactSpace (ULift (StdSimplex ℝ (Fin (n + 1)))))
      have : T2Space (SimplexCategory.toTop.{u}.obj ⦋n⦌) :=
        inferInstanceAs (T2Space (ULift (StdSimplex ℝ (Fin (n + 1)))))
      infer_instance
  exact uCompactlyGeneratedSpace X

/-- If every level `Xₙ` is Hausdorff, every compact subset of `|X|` lies in a single finite
skeleton `skₙ |X|`. -/
theorem exists_subset_range_skeleton_of_isCompact_of_t2Space [hT : ∀ n : ℕ, T2Space (X _⦋n⦌)]
    {K : Set (thinRealization X)} (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ range ((skeletonCocone X).ι.app n) :=
  have : ∀ n : ℕ, T1Space (X _⦋n⦌) := fun n ↦ have := hT n; inferInstance
  exists_subset_range_skeleton_of_isCompact
    (fun n j ↦ have := hT (n + 1); (SimplicialObject.isClosedEmbedding_σ X j).isClosed_range) hK

/-- If every level `Xₙ` is Hausdorff, every continuous map from a compact space into `|X|` factors
continuously through a single finite skeleton `skₙ |X|`. -/
theorem exists_lift_skeleton_of_compactSpace_of_t2Space [hT : ∀ n : ℕ, T2Space (X _⦋n⦌)]
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (g : C(K, thinRealization X)) :
    ∃ (n : ℕ) (g' : C(K, skeleton X n)), ((skeletonCocone X).ι.app n).hom.comp g' = g :=
  have : ∀ n : ℕ, T1Space (X _⦋n⦌) := fun n ↦ have := hT n; inferInstance
  exists_lift_skeleton_of_compactSpace
    (fun n j ↦ have := hT (n + 1); (SimplicialObject.isClosedEmbedding_σ X j).isClosed_range) g

end Corollaries

end TauCeti.thinRealization
