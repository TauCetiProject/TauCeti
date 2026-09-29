/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.Chains

/-!
# Cellular maps and the cellular chain complex

A continuous map between relative CW complexes is cellular when it carries each stage of the
skeletal filtration into the corresponding stage. Such a map induces maps on the relative
homology of consecutive skeleta. Naturality of the connecting morphism of a pair and of the
map from skeletal homology to relative homology shows that these maps commute with the cellular
differential.
Thus a cellular map induces a map of cellular chain complexes, respecting identities and
composition. No choice of characteristic maps or cellular representatives is involved.
The predicate is used as `TauCeti.IsCellular f`, and its induced chain map as
`TauCeti.cellularChainComplexMap R f hf`. The skeletal restrictions are
`TauCeti.skeletonMap f hf n` and `TauCeti.skeletonPairMap f hf n`.

This is the map-level form of the cellular differential in Hatcher, *Algebraic Topology*,
Section 2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w₁ w₂ w₃ w v u

namespace TauCeti

section Cellularity

variable {X : Type w₁} {Y : Type w₂} {Z : Type w₃}
  [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  {D : Set X} {D' : Set Y} {D'' : Set Z}
  {C : Set X} [RelCWComplex C D] {C' : Set Y} [RelCWComplex C' D']
  {C'' : Set Z} [RelCWComplex C'' D'']

/-- A continuous map between relative CW complexes is cellular if it preserves every stage of
their skeletal filtrations. The degree-zero condition includes preservation of the base
subspaces. -/
def IsCellular (f : ContinuousMap C C') : Prop :=
  ∀ (n : ℕ) (x : C), (x : X) ∈ skeletonLT C (n : ℕ∞) →
    ((f x : C') : Y) ∈ skeletonLT C' (n : ℕ∞)

/-- Cellularity means preserving every stage of the skeletal filtration. -/
theorem isCellular_iff {f : ContinuousMap C C'} :
    IsCellular f ↔ ∀ (n : ℕ) (x : C), (x : X) ∈ skeletonLT C (n : ℕ∞) →
      ((f x : C') : Y) ∈ skeletonLT C' (n : ℕ∞) := Iff.rfl

/-- The identity map of a relative CW complex is cellular. -/
lemma isCellular_id : IsCellular (C := C) (C' := C) (ContinuousMap.id C) := by
  intro n x hx
  exact hx

/-- Cellular maps are closed under composition. -/
lemma IsCellular.comp {f : ContinuousMap C C'} {g : ContinuousMap C' C''}
    (hg : IsCellular g) (hf : IsCellular f) : IsCellular (g.comp f) := by
  intro n x hx
  exact hg n (f x) (hf n x hx)

end Cellularity

variable {X Y Z : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z] [T2Space Z]
  {D : Set X} {D' : Set Y} {D'' : Set Z}
  {C : Set X} [RelCWComplex C D] {C' : Set Y} [RelCWComplex C' D']
  {C'' : Set Z} [RelCWComplex C'' D'']

/-- A cellular map restricted to the `n`-th stage of the skeletal filtration. -/
def skeletonMap (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    skeletonObj C n ⟶ skeletonObj C' n :=
  TopCat.ofHom ⟨fun x ↦
    ⟨f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩,
      hf n ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩ x.2⟩,
    by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (f.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val (fun x ↦
          (skeletonLT C (n : ℕ∞)).subset_complex x.2)))⟩

/-- On points, the skeletal map is the restriction of the original map. -/
-- The subtype coercion on the left simplifies before this lemma can apply, so it is not a
-- simp lemma (Mathlib's simpNF linter rejects the attribute).
lemma skeletonMap_apply (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ)
    (x : skeletonObj C n) :
    (((skeletonMap f hf n) x : skeletonObj C' n) : Y) =
      ((f ⟨x.1, (skeletonLT C (n : ℕ∞)).subset_complex x.2⟩ : C') : Y) := by
  unfold skeletonMap
  rfl

/-- The skeletal restriction of the identity is the identity. -/
@[simp]
lemma skeletonMap_id (n : ℕ) :
    skeletonMap (C := C) (C' := C) (ContinuousMap.id C) isCellular_id n =
      𝟙 (skeletonObj C n) := by
  ext x
  rfl

/-- Restricting a composite of cellular maps to a skeleton agrees with composing the
restrictions. -/
@[simp, reassoc]
lemma skeletonMap_comp {f : ContinuousMap C C'} {g : ContinuousMap C' C''}
    (hg : IsCellular g) (hf : IsCellular f) (n : ℕ) :
    skeletonMap (g.comp f) (hg.comp hf) n =
      skeletonMap f hf n ≫ skeletonMap g hg n := by
  ext x
  rfl

/-- A cellular map induces a map between pairs of consecutive skeleta. -/
def skeletonPairMap (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    skeletonPair C n ⟶ skeletonPair C' n :=
  TopPair.ofHom (skeletonMap f hf (n + 1)) (skeletonMap f hf n) (by
    ext x
    rfl)

/-- The map on ambient spaces of a skeletal pair map is the restriction to the upper
skeleton. -/
@[simp]
lemma skeletonPairMap_fst (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    TopPair.Hom.fst (skeletonPairMap f hf n) = skeletonMap f hf (n + 1) := by
  unfold skeletonPairMap
  rfl

/-- The map on subspaces of a skeletal pair map is the restriction to the lower
skeleton. -/
@[simp]
lemma skeletonPairMap_snd (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    TopPair.Hom.snd (skeletonPairMap f hf n) = skeletonMap f hf n := by
  unfold skeletonPairMap
  rfl

/-- The map of skeletal pairs induced by the identity is the identity map of pairs. -/
@[simp]
lemma skeletonPairMap_id (n : ℕ) :
    skeletonPairMap (C := C) (C' := C) (ContinuousMap.id C) isCellular_id n =
      𝟙 (skeletonPair C n) := by
  ext : 2 <;> simp

/-- The map of skeletal pairs induced by a composite is the composite of the maps of pairs. -/
@[simp, reassoc]
lemma skeletonPairMap_comp {f : ContinuousMap C C'} {g : ContinuousMap C' C''}
    (hg : IsCellular g) (hf : IsCellular f) (n : ℕ) :
    skeletonPairMap (g.comp f) (hg.comp hf) n =
      skeletonPairMap f hf n ≫ skeletonPairMap g hg n := by
  ext : 2 <;> rfl

/-- A cellular map induces a map between triples of consecutive skeleta. -/
def skeletonTripleMap (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    skeletonTriple C n ⟶ skeletonTriple C' n :=
  ⟨ComposableArrows.homMk₂ (skeletonMap f hf n) (skeletonMap f hf (n + 1))
    (skeletonMap f hf (n + 2)) (by ext x; rfl) (by ext x; rfl)⟩

/-- The inner pair of a skeletal triple map is the map of the lower skeletal pairs. -/
lemma skeletonTripleMap_innerPair (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    TopTriple.innerPair.map (skeletonTripleMap f hf n) = skeletonPairMap f hf n := by
  ext : 2 <;> rfl

/-- The outer pair of a skeletal triple map is the map of the upper skeletal pairs. -/
lemma skeletonTripleMap_outerPair (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    TopTriple.outerPair.map (skeletonTripleMap f hf n) =
      skeletonPairMap f hf (n + 1) := by
  ext : 2 <;> rfl

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

/-- The map induced by a cellular map on the cellular chain group in degree `n`. -/
abbrev cellularChainGroupMap (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    cellularChainGroup C R n ⟶ cellularChainGroup C' R n :=
  TopPair.singularHomologyMap (skeletonPairMap f hf n) R n

/-- The identity cellular map induces the identity on each cellular chain group. -/
@[simp]
lemma cellularChainGroupMap_id (n : ℕ) :
    cellularChainGroupMap R (ContinuousMap.id C) isCellular_id n =
      𝟙 (cellularChainGroup C R n) := by
  simp [cellularChainGroupMap, skeletonPairMap_id, TopPair.singularHomologyMap.eq_def]

/-- Composition of cellular maps induces composition on each cellular chain group. -/
@[simp, reassoc]
lemma cellularChainGroupMap_comp {f : ContinuousMap C C'} {g : ContinuousMap C' C''}
    (hg : IsCellular g) (hf : IsCellular f) (n : ℕ) :
    cellularChainGroupMap R (g.comp f) (hg.comp hf) n =
      cellularChainGroupMap R f hf n ≫ cellularChainGroupMap R g hg n := by
  unfold cellularChainGroupMap
  rw [skeletonPairMap_comp hg hf n]
  simp only [TopPair.singularHomologyMap.eq_def, Functor.map_comp,
    SSetPair.homologyMap_comp]

/-- The maps induced on consecutive skeletal relative homology groups commute with the
cellular differential. -/
@[reassoc]
lemma cellularDifferential_naturality (f : ContinuousMap C C')
    (hf : IsCellular f) (n : ℕ) :
    cellularChainGroupMap R f hf (n + 1) ≫ cellularDifferential C' R n =
      cellularDifferential C R n ≫ cellularChainGroupMap R f hf n := by
  have h := (skeletonTriple C n).singularHomologyδ_naturality
    (skeletonTripleMap f hf n) R (n + 1) n
  rw [skeletonTripleMap_innerPair, skeletonTripleMap_outerPair] at h
  simp only [cellularDifferential_eq_singularHomologyδ, cellularChainGroupMap]
  convert h.symm using 1 <;> rfl

/-- The chain map on cellular chains induced by a cellular map. -/
def cellularChainComplexMap (f : ContinuousMap C C') (hf : IsCellular f) :
    cellularChainComplex C R ⟶ cellularChainComplex C' R :=
  ChainComplex.ofHom (fun n ↦
    eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap R f hf n ≫
      eqToHom (cellularChainComplex_X C' R n).symm) (by
    intro n
    simp only [cellularChainComplex_d, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (cellularChainGroupMap R f hf (n + 1)),
      ← Category.assoc (cellularDifferential C R n),
      cellularDifferential_naturality R f hf n])

/-- The degree-`n` component of the cellular chain map is the relative-homology map,
transported along the object equalities of the cellular chain complexes. -/
@[simp]
lemma cellularChainComplexMap_f (f : ContinuousMap C C') (hf : IsCellular f) (n : ℕ) :
    (cellularChainComplexMap R f hf).f n =
      eqToHom (cellularChainComplex_X C R n) ≫ cellularChainGroupMap R f hf n ≫
        eqToHom (cellularChainComplex_X C' R n).symm := by
  unfold cellularChainComplexMap
  rfl

/-- The identity cellular map induces the identity chain map. -/
@[simp]
lemma cellularChainComplexMap_id :
    cellularChainComplexMap R (ContinuousMap.id C) isCellular_id =
      𝟙 (cellularChainComplex C R) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cellularChainComplexMap_f, cellularChainGroupMap_id, HomologicalComplex.id_f]
  simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- Composition of cellular maps induces composition of their cellular chain maps. -/
@[simp, reassoc]
lemma cellularChainComplexMap_comp {f : ContinuousMap C C'} {g : ContinuousMap C' C''}
    (hg : IsCellular g) (hf : IsCellular f) :
    cellularChainComplexMap R (g.comp f) (hg.comp hf) =
      cellularChainComplexMap R f hf ≫ cellularChainComplexMap R g hg := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [cellularChainComplexMap_f, HomologicalComplex.comp_f,
    cellularChainComplexMap_f, cellularChainComplexMap_f,
    cellularChainGroupMap_comp R hg hf n]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end TauCeti
