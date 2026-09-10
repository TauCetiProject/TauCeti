/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothCircle

/-!
# Smooth link presentations

A labeled oriented smooth link with `n` components in a manifold is a family of `n` smooth
circle embeddings whose images are pairwise disjoint.  The parametrization of each circle gives
that component its orientation; the `Fin n` index records a component labeling.  This file bundles
exactly those data and develops their basic transformations.

Component relabeling changes only the `Fin n` labels.  Orientation reversal is performed on every
component, while an ambient diffeomorphism transports all components at once.  All three operations
preserve the underlying subset of the ambient manifold in the expected way.  The zero-component
link and the one-component link show that this presentation includes the empty link and recovers
`SmoothCircleEmbedding` exactly.

Framings are not part of this presentation: a smooth framing is additional normal-bundle data and
will be carried by a separate type once tubular neighbourhoods are available.

## Main definitions

* `TauCeti.SmoothLinkEmbedding`: labeled oriented smooth links with a prescribed number of
  components.
* `TauCeti.SmoothLinkEmbedding.relabel`: transport the component labels along a permutation.
* `TauCeti.SmoothLinkEmbedding.reverse`: reverse every component orientation.
* `TauCeti.SmoothLinkEmbedding.transDiffeomorph`: transport a link by an ambient diffeomorphism.
* `TauCeti.SmoothLinkEmbedding.singletonEquiv`: the identification of one-component links with
  smooth circle embeddings.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

noncomputable section

namespace TauCeti

open Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ}

/-- A labeled oriented smooth link with `n` components in a manifold.

The components are smooth embeddings of the standard oriented circle, and distinct components
have disjoint images.  The index `Fin n` is part of the presentation and labels the components. -/
structure SmoothLinkEmbedding (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (n : ℕ) where
  /-- The smooth circle embedding presenting each labeled component. -/
  component : Fin n → SmoothCircleEmbedding I M
  /-- Distinct link components have disjoint images. -/
  pairwiseDisjoint_range :
    Pairwise (Function.onFun Disjoint fun i ↦ Set.range (component i))

namespace SmoothLinkEmbedding

variable {L K : SmoothLinkEmbedding I M n}

instance instFunLike : FunLike (SmoothLinkEmbedding I M n) (Fin n) (SmoothCircleEmbedding I M) where
  coe L := L.component
  coe_injective L K h := by
    cases L
    cases K
    cases h
    rfl

/-- The component family determines a smooth link presentation. -/
@[ext]
theorem ext (h : ∀ i, L i = K i) : L = K :=
  DFunLike.ext L K h

/-- The images of two differently labeled components of a smooth link are disjoint. -/
theorem disjoint_range (L : SmoothLinkEmbedding I M n) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (L i)) (Set.range (L j)) :=
  L.pairwiseDisjoint_range hij

/-- The subset of the ambient manifold occupied by a smooth link. -/
def range (L : SmoothLinkEmbedding I M n) : Set M :=
  ⋃ i, Set.range (L i)

/-- A point lies in a smooth link exactly when it lies on one of its components. -/
theorem mem_range_iff (L : SmoothLinkEmbedding I M n) (x : M) :
    x ∈ L.range ↔ ∃ i y, L i y = x := by
  simp only [range, Set.mem_iUnion, Set.mem_range]

/-- The range of a component is contained in the range of the whole link. -/
theorem component_range_subset (L : SmoothLinkEmbedding I M n) (i : Fin n) :
    Set.range (L i) ⊆ L.range :=
  Set.subset_iUnion (fun j ↦ Set.range (L j)) i

/-- A point of a link lies on a unique labeled component. -/
theorem existsUnique_component_of_mem_range (L : SmoothLinkEmbedding I M n) {x : M}
    (hx : x ∈ L.range) : ∃! i, x ∈ Set.range (L i) := by
  rw [mem_range_iff] at hx
  obtain ⟨i, y, rfl⟩ := hx
  refine ⟨i, Set.mem_range_self y, ?_⟩
  intro j hj
  by_contra hij
  exact Set.disjoint_left.1 (L.disjoint_range hij) hj (Set.mem_range_self y)

/-! ### Empty and one-component links -/

/-- The smooth link with no components. -/
def empty : SmoothLinkEmbedding I M 0 where
  component := Fin.elim0
  pairwiseDisjoint_range i := Fin.elim0 i

/-- The empty smooth link occupies the empty subset. -/
@[simp]
theorem range_empty : (empty (I := I) (M := M)).range = ∅ := by
  simp [range]

/-- Regard a smooth circle embedding as a one-component smooth link. -/
def singleton (f : SmoothCircleEmbedding I M) : SmoothLinkEmbedding I M 1 where
  component := fun _ ↦ f
  pairwiseDisjoint_range i j hij := (hij (Subsingleton.elim i j)).elim

/-- The only component of a singleton link is the original circle embedding. -/
@[simp]
theorem singleton_apply (f : SmoothCircleEmbedding I M) (i : Fin 1) :
    singleton f i = f := by
  rw [singleton.eq_def]
  rfl

/-- A singleton link occupies precisely the image of its circle embedding. -/
@[simp]
theorem range_singleton (f : SmoothCircleEmbedding I M) :
    (singleton f).range = Set.range f := by
  ext x
  simp [range]

/-- One-component smooth links are exactly smooth circle embeddings. -/
def singletonEquiv : SmoothCircleEmbedding I M ≃ SmoothLinkEmbedding I M 1 where
  toFun := singleton
  invFun L := L 0
  left_inv f := rfl
  right_inv L := by
    apply SmoothLinkEmbedding.ext
    intro i
    exact congrArg L (Subsingleton.elim 0 i)

/-! ### Component relabeling -/

/-- Relabel the components of a smooth link along a permutation.  If `e` sends an old label to a
new label, then the component at the new label `i` is the old component at `e.symm i`. -/
def relabel (L : SmoothLinkEmbedding I M n) (e : Equiv.Perm (Fin n)) :
    SmoothLinkEmbedding I M n where
  component i := L (e.symm i)
  pairwiseDisjoint_range _ _ hij :=
    L.disjoint_range fun h ↦ hij (e.symm.injective h)

/-- Relabeling reads the component at the inverse old label. -/
@[simp]
theorem relabel_apply (L : SmoothLinkEmbedding I M n) (e : Equiv.Perm (Fin n)) (i : Fin n) :
    L.relabel e i = L (e.symm i) := by
  rw [relabel.eq_def]
  rfl

/-- Relabeling by the identity permutation changes nothing. -/
@[simp]
theorem relabel_refl (L : SmoothLinkEmbedding I M n) : L.relabel (Equiv.refl _) = L := by
  apply SmoothLinkEmbedding.ext
  intro i
  rfl

/-- Successive relabelings compose in the order in which old labels are sent to new labels. -/
@[simp]
theorem relabel_relabel (L : SmoothLinkEmbedding I M n) (e f : Equiv.Perm (Fin n)) :
    (L.relabel e).relabel f = L.relabel (e.trans f) := by
  apply SmoothLinkEmbedding.ext
  intro i
  rfl

/-- Component relabeling does not change the subset occupied by a link. -/
@[simp]
theorem range_relabel (L : SmoothLinkEmbedding I M n) (e : Equiv.Perm (Fin n)) :
    (L.relabel e).range = L.range := by
  ext x
  constructor
  · rw [mem_range_iff, mem_range_iff]
    rintro ⟨i, y, hiy⟩
    exact ⟨e.symm i, y, hiy⟩
  · rw [mem_range_iff, mem_range_iff]
    rintro ⟨i, y, hiy⟩
    exact ⟨e i, y, by simpa using hiy⟩

/-- Component permutations act on smooth links by relabeling. -/
instance instMulActionPerm : MulAction (Equiv.Perm (Fin n)) (SmoothLinkEmbedding I M n) where
  smul e L := L.relabel e
  one_smul L := L.relabel_refl
  mul_smul e f L := (L.relabel_relabel f e).symm

/-- The component-permutation action is relabeling. -/
@[simp]
theorem perm_smul_def (e : Equiv.Perm (Fin n)) (L : SmoothLinkEmbedding I M n) :
    e • L = L.relabel e :=
  rfl

/-! ### Orientation reversal -/

/-- Reverse the orientation of every component of a smooth link. -/
def reverse (L : SmoothLinkEmbedding I M n) : SmoothLinkEmbedding I M n where
  component i := (L i).reverse
  pairwiseDisjoint_range i j hij := by
    simpa only [SmoothCircleEmbedding.range_reverse] using L.disjoint_range hij

/-- Reversing a smooth link reverses each of its components. -/
@[simp]
theorem reverse_apply (L : SmoothLinkEmbedding I M n) (i : Fin n) :
    L.reverse i = (L i).reverse := by
  rw [reverse.eq_def]
  rfl

/-- Reversing every component twice gives the original smooth link. -/
@[simp]
theorem reverse_reverse (L : SmoothLinkEmbedding I M n) : L.reverse.reverse = L := by
  apply SmoothLinkEmbedding.ext
  intro i
  simp

/-- Reversing component orientations does not change the subset occupied by a link. -/
@[simp]
theorem range_reverse (L : SmoothLinkEmbedding I M n) : L.reverse.range = L.range := by
  simp only [range, reverse_apply, SmoothCircleEmbedding.range_reverse]

/-- Relabeling commutes with reversing every component orientation. -/
@[simp]
theorem reverse_relabel (L : SmoothLinkEmbedding I M n) (e : Equiv.Perm (Fin n)) :
    (L.relabel e).reverse = L.reverse.relabel e := by
  apply SmoothLinkEmbedding.ext
  intro i
  rfl

/-! ### Ambient transport -/

section Ambient

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]

/-- Transport every component of a smooth link by an ambient diffeomorphism. -/
def transDiffeomorph (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P) :
    SmoothLinkEmbedding I P n where
  component i := SmoothEmbedding.transDiffeomorph (L i) e
  pairwiseDisjoint_range i j hij := by
    simp only [Function.onFun, SmoothEmbedding.range_transDiffeomorph]
    exact Set.disjoint_image_of_injective e.injective (L.disjoint_range hij)

/-- Ambient transport acts on every component by the same diffeomorphism. -/
@[simp]
theorem transDiffeomorph_apply (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P) (i : Fin n) :
    L.transDiffeomorph e i = SmoothEmbedding.transDiffeomorph (L i) e := by
  rw [transDiffeomorph.eq_def]
  rfl

/-- Transporting by the identity ambient diffeomorphism changes nothing. -/
@[simp]
theorem transDiffeomorph_refl [IsManifold I ∞ M] (L : SmoothLinkEmbedding I M n) :
    L.transDiffeomorph (_root_.Diffeomorph.refl I M ∞) = L := by
  apply SmoothLinkEmbedding.ext
  intro i
  simp

/-- Successive ambient transports compose. -/
@[simp]
theorem transDiffeomorph_transDiffeomorph
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P) (f : P ≃ₘ⟮I, I⟯ Q) :
    (L.transDiffeomorph e).transDiffeomorph f = L.transDiffeomorph (e.trans f) := by
  apply SmoothLinkEmbedding.ext
  intro i
  simp

/-- Ambient transport carries the range of a smooth link to its image under the
diffeomorphism. -/
@[simp]
theorem range_transDiffeomorph (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P) :
    (L.transDiffeomorph e).range = e '' L.range := by
  ext x
  constructor
  · rw [mem_range_iff]
    rintro ⟨i, y, rfl⟩
    exact ⟨L i y, component_range_subset L i (Set.mem_range_self y),
      by
        symm
        rw [transDiffeomorph_apply, SmoothEmbedding.transDiffeomorph_apply]⟩
  · rintro ⟨z, hz, rfl⟩
    rw [mem_range_iff] at hz ⊢
    obtain ⟨i, y, rfl⟩ := hz
    exact ⟨i, y, by rw [transDiffeomorph_apply, SmoothEmbedding.transDiffeomorph_apply]⟩

/-- Ambient transport commutes with component relabeling. -/
@[simp]
theorem transDiffeomorph_relabel (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P)
    (σ : Equiv.Perm (Fin n)) :
    (L.relabel σ).transDiffeomorph e = (L.transDiffeomorph e).relabel σ := by
  apply SmoothLinkEmbedding.ext
  intro i
  simp

/-- Ambient transport commutes with reversing all component orientations. -/
@[simp]
theorem reverse_transDiffeomorph (L : SmoothLinkEmbedding I M n) (e : M ≃ₘ⟮I, I⟯ P) :
    (L.transDiffeomorph e).reverse = L.reverse.transDiffeomorph e := by
  apply SmoothLinkEmbedding.ext
  intro i
  rw [reverse_apply, transDiffeomorph_apply, transDiffeomorph_apply, reverse_apply]
  apply SmoothEmbedding.ext
  intro x
  simp

end Ambient

section AmbientAction

variable [IsManifold I ∞ M]

/-- Ambient self-diffeomorphisms act on smooth links by transport. -/
instance instMulActionDiff : MulAction (Diff I M ∞) (SmoothLinkEmbedding I M n) where
  smul e L := L.transDiffeomorph e
  one_smul L := L.transDiffeomorph_refl
  mul_smul e f L := (L.transDiffeomorph_transDiffeomorph f e).symm

/-- The ambient diffeomorphism action is transport of the whole smooth link. -/
@[simp]
theorem smul_def (e : Diff I M ∞) (L : SmoothLinkEmbedding I M n) :
    e • L = L.transDiffeomorph e :=
  rfl

/-- Ambient transport commutes with component relabeling. -/
instance instSMulCommClassPerm :
    SMulCommClass (Diff I M ∞) (Equiv.Perm (Fin n)) (SmoothLinkEmbedding I M n) where
  smul_comm e σ L := by
    rw [smul_def, perm_smul_def, smul_def, perm_smul_def]
    exact (L.transDiffeomorph_relabel e σ).symm

end AmbientAction

end SmoothLinkEmbedding

end TauCeti
