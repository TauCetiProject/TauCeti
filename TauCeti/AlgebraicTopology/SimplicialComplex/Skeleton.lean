/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps
public import Mathlib.Data.Finset.Card

/-!
# Skeleta of abstract simplicial complexes

The `n`-skeleton retains the faces with at most `n + 1` vertices. Skeleta form an increasing,
exhaustive filtration, and a simplicial map restricts to a map between corresponding skeleta,
even when it identifies vertices. This is the combinatorial filtration underlying the cellular
structure of a geometric realization.

The construction is first given for precomplexes, so it also applies to subcomplexes with unused
vertices and to the void complex. An abstract complex retains all its vertices in every skeleton.

## References

* A. Hatcher, *Algebraic Topology*, Chapter 0 (simplicial complexes and their skeleta).
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι κ : Type*} {K L : PreAbstractSimplicialComplex ι} {σ : Finset ι} {m n : ℕ}

/-- The `n`-skeleton consists of the faces with at most `n + 1` vertices. -/
def skeleton (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    PreAbstractSimplicialComplex ι where
  faces := {σ | σ ∈ K ∧ σ.card ≤ n + 1}
  isRelLowerSet_faces := fun {_} hσ => ⟨(K.isRelLowerSet_faces hσ.1).1,
    fun {_} hτσ hτ => ⟨K.isRelLowerSet_faces.mem_of_le hσ.1 hτσ hτ,
      (Finset.card_le_card hτσ).trans hσ.2⟩⟩

@[simp]
theorem mem_skeleton : σ ∈ K.skeleton n ↔ σ ∈ K ∧ σ.card ≤ n + 1 := Iff.rfl

/-- Every skeleton is a subcomplex of the original complex. -/
theorem skeleton_le (K : PreAbstractSimplicialComplex ι) (n : ℕ) : K.skeleton n ≤ K :=
  fun _ hσ => (mem_skeleton.mp hσ).1

/-- Skeleta are monotone in the complex and the dimension bound. -/
theorem skeleton_mono (hKL : K ≤ L) (hmn : m ≤ n) : K.skeleton m ≤ L.skeleton n := by
  intro σ hσ
  obtain ⟨hσK, hcard⟩ := mem_skeleton.mp hσ
  exact mem_skeleton.mpr ⟨hKL hσK, hcard.trans (Nat.add_le_add_right hmn 1)⟩

/-- Taking successive skeleta keeps the smaller dimension bound. -/
@[simp]
theorem skeleton_skeleton (K : PreAbstractSimplicialComplex ι) (m n : ℕ) :
    (K.skeleton m).skeleton n = K.skeleton (min m n) := by
  apply SetLike.ext
  intro σ
  simp only [mem_skeleton]
  constructor
  · rintro ⟨⟨hK, hm⟩, hn⟩
    exact ⟨hK, by omega⟩
  · rintro ⟨hK, hmn⟩
    exact ⟨⟨hK, by omega⟩, by omega⟩

/-- A complex equals its `n`-skeleton exactly when every face has at most `n + 1` vertices. -/
theorem skeleton_eq_self_iff : K.skeleton n = K ↔ ∀ σ ∈ K, σ.card ≤ n + 1 := by
  constructor
  · intro h σ hσ
    exact (mem_skeleton.mp (h.symm ▸ hσ)).2
  · intro h
    exact le_antisymm (skeleton_le K n) (fun σ hσ => mem_skeleton.mpr ⟨hσ, h σ hσ⟩)

/-- Every face occurs in some skeleton, without a finite-dimensionality assumption. -/
theorem iSup_skeleton (K : PreAbstractSimplicialComplex ι) : ⨆ n, K.skeleton n = K := by
  apply le_antisymm (iSup_le fun n => skeleton_le K n)
  intro σ hσ
  exact le_iSup (fun n => K.skeleton n) σ.card
    (mem_skeleton.mpr ⟨hσ, Nat.le_succ _⟩)

namespace SimplicialMap

variable [DecidableEq κ] {L : PreAbstractSimplicialComplex κ}

/-- A simplicial map restricts to corresponding skeleta; vertex identifications may lower the
dimension of a face. -/
def skeleton (f : SimplicialMap K L) (n : ℕ) :
    SimplicialMap (K.skeleton n) (L.skeleton n) where
  toFun := f
  map_face' := by
    intro σ hσ
    obtain ⟨hσK, hcard⟩ := mem_skeleton.mp hσ
    exact mem_skeleton.mpr ⟨f.map_face hσK, Finset.card_image_le.trans hcard⟩

@[simp]
theorem skeleton_apply (f : SimplicialMap K L) (n : ℕ) (v : ι) : f.skeleton n v = f v :=
  (rfl)

/-- Restriction to skeleta preserves composition. -/
@[simp]
theorem skeleton_comp {μ : Type*} [DecidableEq μ] {P : PreAbstractSimplicialComplex μ}
    (g : SimplicialMap L P) (f : SimplicialMap K L) (n : ℕ) :
    (g.comp f).skeleton n = (g.skeleton n).comp (f.skeleton n) := by
  apply DFunLike.ext
  intro v
  simp

/-- Restriction of an identity map is the identity on the skeleton. -/
@[simp]
theorem skeleton_id [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (n : ℕ) :
    (id K).skeleton n = id (K.skeleton n) := by
  apply DFunLike.ext
  intro v
  simp

end SimplicialMap

end PreAbstractSimplicialComplex

namespace AbstractSimplicialComplex

variable {ι : Type*} {K L : AbstractSimplicialComplex ι} {σ : Finset ι} {m n : ℕ}

/-- The `n`-skeleton of an abstract complex, retaining all its vertices. This reducible lift
allows simplicial maps between precomplex skeleta to be used on abstract skeleta as well. -/
abbrev skeleton (K : AbstractSimplicialComplex ι) (n : ℕ) : AbstractSimplicialComplex ι where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.skeleton n
  singleton_mem v := PreAbstractSimplicialComplex.mem_skeleton.mpr
    ⟨K.singleton_mem v, by simp⟩

@[simp]
theorem skeleton_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex ι) (n : ℕ) :
    (K.skeleton n).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex.skeleton n := (rfl)

@[simp]
theorem mem_skeleton : σ ∈ K.skeleton n ↔ σ ∈ K ∧ σ.card ≤ n + 1 := Iff.rfl

/-- The inclusion used to realize a skeleton as a subspace of the original polyhedron. -/
theorem skeleton_le (K : AbstractSimplicialComplex ι) (n : ℕ) : K.skeleton n ≤ K :=
  fun _ hσ => (mem_skeleton.mp hσ).1

/-- Skeleta are monotone in the complex and the dimension bound. -/
theorem skeleton_mono (hKL : K ≤ L) (hmn : m ≤ n) : K.skeleton m ≤ L.skeleton n :=
  toPreAbstractSimplicialComplex_le_iff.mp
    (PreAbstractSimplicialComplex.skeleton_mono
      (toPreAbstractSimplicialComplex_le_iff.mpr hKL) hmn)

/-- Taking successive skeleta keeps the smaller dimension bound. -/
@[simp]
theorem skeleton_skeleton (K : AbstractSimplicialComplex ι) (m n : ℕ) :
    (K.skeleton m).skeleton n = K.skeleton (min m n) := by
  apply toPreAbstractSimplicialComplex_injective
  simp

/-- A complex equals its `n`-skeleton exactly when all face dimensions are at most `n`. -/
theorem skeleton_eq_self_iff : K.skeleton n = K ↔ ∀ σ ∈ K, σ.card ≤ n + 1 := by
  rw [← toPreAbstractSimplicialComplex_injective.eq_iff,
    skeleton_toPreAbstractSimplicialComplex, PreAbstractSimplicialComplex.skeleton_eq_self_iff]
  simp

/-- The increasing family of skeleta exhausts the complex. -/
theorem iSup_skeleton (K : AbstractSimplicialComplex ι) : ⨆ n, K.skeleton n = K := by
  apply le_antisymm (iSup_le fun n => skeleton_le K n)
  intro σ hσ
  exact le_iSup (fun n => K.skeleton n) σ.card
    (mem_skeleton.mpr ⟨hσ, Nat.le_succ _⟩)

end AbstractSimplicialComplex
