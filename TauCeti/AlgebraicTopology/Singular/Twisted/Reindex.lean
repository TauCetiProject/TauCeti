/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Basic

/-!
# Reindexing twisted chains on totally disconnected spaces

A surjective reindexing of singular simplices induces an epimorphism on twisted chains,
because coefficient transport is invertible. On a totally disconnected space every singular
simplex is constant. Consequently parallel simplicial structure maps on twisted chains agree,
even for nonconstant local coefficient systems. These identities allow the usual degeneracies
to contract positive-degree chains without moving their supports.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
-/

public section

open CategoryTheory Limits SimplexCategory

open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)
  {m n : SimplexCategoryᵒᵖ}

/-- A surjective map on singular simplices gives an epimorphism on twisted chains. -/
theorem epi_twistedChains_map_of_surjective (α : m ⟶ n)
    (hα : Function.Surjective ((TopCat.toSSet.obj X).map α)) :
    Epi ((twistedChains L).map α) := by
  constructor
  intro M f g h
  apply twistedChains_hom_ext L
  intro τ
  obtain ⟨σ, rfl⟩ := hα τ
  have hσ := congrArg (ιTwistedChains L σ ≫ ·) h
  exact (cancel_epi (L.map (vertexTransport α σ))).1 (by
    simpa only [ιTwistedChains_map_assoc] using hσ)

/-- Parallel simplicial structure maps on twisted chains agree when the space is totally
disconnected. No trivialization of the local coefficient system is needed. -/
theorem twistedChains_map_eq_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X]
    (α β : m ⟶ n) : (twistedChains L).map α = (twistedChains L).map β := by
  let γ := (SimplexCategory.const m.unop ⦋0⦌ 0).op
  have hsurj : Function.Surjective ((TopCat.toSSet.obj X).map γ) := by
    let e := TopCat.toSSetIsoConst X
    intro σ
    refine ⟨e.inv.app (Opposite.op ⦋0⦌) (e.hom.app m σ), ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app _)).1
    simp
  have := epi_twistedChains_map_of_surjective L γ hsurj
  apply (cancel_epi ((twistedChains L).map γ)).1
  rw [← Functor.map_comp, ← Functor.map_comp]
  -- Both composites are opposite to the unique morphism into the zero simplex.
  congr 1

/-! The following maps give simplicial reindexing its chain-degree types explicitly. This avoids
requiring consumers of the locally finite extension machinery to unfold the alternating face
map complex when elaborating a simplicial structure map as a map between chain terms. -/

variable {a b c : ℕ}

/-- Simplicial reindexing, read as a map between the terms of the twisted chain complex. -/
noncomputable def twistedChainReindex (α : ⦋a⦌ ⟶ ⦋b⦌) :
    (twistedChainComplex L).X b ⟶ (twistedChainComplex L).X a :=
  eqToHom (twistedChainComplex_X_eq_twistedChains_obj L b) ≫
    (twistedChains L).map α.op ≫
      eqToHom (twistedChainComplex_X_eq_twistedChains_obj L a).symm

/-- Reindexing transports a coefficient to the initial vertex of the reindexed simplex. -/
@[reassoc (attr := simp)]
theorem ιTwistedChainComplex_reindex (α : ⦋a⦌ ⟶ ⦋b⦌)
    (σ : (TopCat.toSSet.obj X) _⦋b⦌) :
    ιTwistedChainComplex L b σ ≫ twistedChainReindex L α =
      L.map (vertexTransport α.op σ) ≫
        ιTwistedChainComplex L a ((TopCat.toSSet.obj X).map α.op σ) := by
  simp only [twistedChainReindex, ιTwistedChainComplex_eqToHom_twistedChains_assoc,
    ιTwistedChains_map_assoc]
  simp only [← ιTwistedChainComplex_eqToHom_twistedChains, Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Identity reindexing acts identically on a chain term. -/
@[simp]
theorem twistedChainReindex_id : twistedChainReindex L (𝟙 ⦋a⦌) = 𝟙 _ := by
  simp [twistedChainReindex]

/-- Simplicial reindexing of chain terms is contravariant. -/
theorem twistedChainReindex_comp (α : ⦋a⦌ ⟶ ⦋b⦌) (β : ⦋b⦌ ⟶ ⦋c⦌) :
    twistedChainReindex L (α ≫ β) = twistedChainReindex L β ≫ twistedChainReindex L α := by
  simp [twistedChainReindex, Functor.map_comp]

/-- Parallel reindexings of chain terms agree on a totally disconnected space. -/
theorem twistedChainReindex_eq_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X]
    (α β : ⦋a⦌ ⟶ ⦋b⦌) : twistedChainReindex L α = twistedChainReindex L β := by
  simp only [twistedChainReindex,
    twistedChains_map_eq_of_totallyDisconnectedSpace L α.op β.op]

/-- The zeroth degeneracies contract the twisted chain complex in positive degrees on a
totally disconnected space. They preserve the image of each singular simplex. -/
theorem d_comp_twistedChainReindex_add_twistedChainReindex_comp_d
    [TotallyDisconnectedSpace X] (k : ℕ) :
    (twistedChainComplex L).d (k + 1) k ≫ twistedChainReindex L (σ (0 : Fin (k + 1))) +
      twistedChainReindex L (σ (0 : Fin (k + 2))) ≫
        (twistedChainComplex L).d (k + 2) (k + 1) = 𝟙 _ := by
  -- Read the native alternating-face differential in its chain-term types.
  have hd (j : ℕ) : (twistedChainComplex L).d (j + 1) j =
      ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • twistedChainReindex L (δ i) := by
    simp only [twistedChainComplex_d_eq_objD,
      AlgebraicTopology.AlternatingFaceMapComplex.objD, SimplicialObject.δ,
      Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.comp_zsmul,
      Preadditive.zsmul_comp, twistedChainReindex]
  have hcomp {a b : ℕ} (α : ⦋a⦌ ⟶ ⦋b⦌) (β : ⦋b⦌ ⟶ ⦋a⦌) :
      twistedChainReindex L β ≫ twistedChainReindex L α = 𝟙 _ := by
    rw [← twistedChainReindex_comp,
      twistedChainReindex_eq_of_totallyDisconnectedSpace L (α ≫ β) (𝟙 _),
      twistedChainReindex_id]
  have hsum : (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ)) +
      (∑ i : Fin (k + 3), (-1 : ℤ) ^ (i : ℕ)) = 1 := by
    by_cases h : Even (k + 2) <;>
      simp [Fin.sum_neg_one_pow, Nat.even_add_one, h]
  rw [hd, hd]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum,
    Preadditive.zsmul_comp, Preadditive.comp_zsmul, hcomp,
    ← Finset.sum_smul, ← add_smul, hsum, one_smul]

end TauCeti.LocalCoefficientSystem
