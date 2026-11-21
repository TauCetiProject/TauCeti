/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.McKay.Matrix
import TauCeti.LinearAlgebra.Matrix.Connected
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Recognition
import TauCeti.RepresentationTheory.CharacterTable.TensorGeneration

/-!
# The McKay correspondence

Let `G` be a nontrivial finite group and `V` a faithful two-dimensional complex representation of
`G` with `det (V.ρ g) = 1` for every `g : G`. John McKay observed in 1980 that the tensor-product
multiplicities `dim_ℂ Hom_G(X, V ⊗ Y)` on `SimpleFDRepClasses ℂ G` form `2I - C` for the
generalized Cartan matrix `C` of a valid affine simply-laced Dynkin diagram (`Aₙ` for `n ≥ 1`,
`Dₙ` for `n ≥ 4`, or `E₆`, `E₇`, `E₈`), with the irreducible dimensions as marks and the trivial
representation at an affine node.

Following Steinberg (1985), `TauCeti.exists_isMcKayLabelling` proves this directly without a prior
classification of the finite subgroups of `SL₂(ℂ)` by combining symmetry, loop-freeness, the
dimension null vector, and tensor-power connectedness from
`TauCeti.RepresentationTheory.McKay.Matrix` with Burnside–Brauer faithful tensor generation
(`FDRep.exists_pos_finrank_hom_tensorPower`) and matrix affine-diagram recognition
(`TauCeti.exists_affineDynkinType_of_symm_loopFree_nullVector`).

## Main definitions and results

* `TauCeti.IsMcKayLabelling`: an affine ADE labelling of `SimpleFDRepClasses ℂ G` relative to `V`,
  characterized by `TauCeti.isMcKayLabelling_iff` and `TauCeti.isMcKayLabelling_iff_mckayMatrix`.
* `TauCeti.exists_isMcKayLabelling`: **the McKay correspondence**, and
  `TauCeti.IsMcKayLabelling.eq_of_valid`: uniqueness of the valid affine diagram `t`.

## References

* J. McKay, *Graphs, singularities, and finite groups*, Proc. Symp. Pure Math. **37** (1980),
  183–186.
* R. Steinberg, *Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*, Pacific J.
  Math. **118** (1985), 587–598.
-/

public section

open CategoryTheory MonoidalCategory Finset

universe u

namespace TauCeti

/-- A **McKay labelling** of the simple complex representations of `G` by an affine simply-laced
diagram `t`, relative to `V`: a bijection `e` from `SimpleFDRepClasses ℂ G` to `Fin t.nodes` such
that `dim_ℂ Hom_G(X, V ⊗ Y) = 2 δ_{e [X], e [Y]} - C_{e [X], e [Y]}`, `dim_ℂ X = t.marks (e [X])`,
and any simple trivial representation sits at `t.affineNode`. -/
def IsMcKayLabelling {G : Type u} [Group G] (V : FDRep ℂ G) (t : TauCeti.AffineDynkinType)
    (e : TauCeti.SimpleFDRepClasses ℂ G ≃ Fin t.nodes) : Prop :=
  (∀ (X Y : FDRep ℂ G) [Simple X] [Simple Y],
      (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
        2 * (if e (TauCeti.SimpleFDRepClasses.mk X) = e (TauCeti.SimpleFDRepClasses.mk Y)
          then 1 else 0) -
          t.cartanMatrix (e (TauCeti.SimpleFDRepClasses.mk X))
            (e (TauCeti.SimpleFDRepClasses.mk Y))) ∧
    (∀ (X : FDRep ℂ G) [Simple X],
      (Module.finrank ℂ X : ℤ) = t.marks (e (TauCeti.SimpleFDRepClasses.mk X))) ∧
    ∀ (X : FDRep ℂ G) [Simple X], (∀ g : G, X.ρ g = 1) →
      e (TauCeti.SimpleFDRepClasses.mk X) = t.affineNode

/-- Defining characterization of `TauCeti.IsMcKayLabelling` on simple objects of `FDRep ℂ G`. -/
theorem isMcKayLabelling_iff {G : Type u} [Group G] (V : FDRep ℂ G)
    (t : AffineDynkinType) (e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes) :
    IsMcKayLabelling V t e ↔
      (∀ (X Y : FDRep ℂ G) [Simple X] [Simple Y],
          (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
            2 * (if e (SimpleFDRepClasses.mk X) = e (SimpleFDRepClasses.mk Y) then 1 else 0) -
              t.cartanMatrix (e (SimpleFDRepClasses.mk X)) (e (SimpleFDRepClasses.mk Y))) ∧
        (∀ (X : FDRep ℂ G) [Simple X],
          (Module.finrank ℂ X : ℤ) = t.marks (e (SimpleFDRepClasses.mk X))) ∧
        ∀ (X : FDRep ℂ G) [Simple X], (∀ g : G, X.ρ g = 1) →
          e (SimpleFDRepClasses.mk X) = t.affineNode :=
  Iff.rfl

namespace IsMcKayLabelling

variable {G : Type u} [Group G] {V : FDRep ℂ G} {t : AffineDynkinType}
  {e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes}

/-- Object-level multiplicity identity under a McKay labelling. -/
theorem finrank_hom_tensor (h : IsMcKayLabelling V t e) (X Y : FDRep ℂ G) [Simple X] [Simple Y] :
    (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
      2 * (if e (SimpleFDRepClasses.mk X) = e (SimpleFDRepClasses.mk Y) then 1 else 0) -
        t.cartanMatrix (e (SimpleFDRepClasses.mk X)) (e (SimpleFDRepClasses.mk Y)) :=
  h.1 X Y

/-- Object-level mark identity under a McKay labelling. -/
theorem finrank_eq_marks_mk (h : IsMcKayLabelling V t e) (X : FDRep ℂ G) [Simple X] :
    (Module.finrank ℂ X : ℤ) = t.marks (e (SimpleFDRepClasses.mk X)) :=
  h.2.1 X

/-- Object-level affine-node normalization under a McKay labelling. -/
theorem apply_mk_of_trivial (h : IsMcKayLabelling V t e) (X : FDRep ℂ G) [Simple X]
    (htriv : ∀ g : G, X.ρ g = 1) : e (SimpleFDRepClasses.mk X) = t.affineNode :=
  h.2.2 X htriv

/-- Under a McKay labelling, `(mckayMatrix V c₁ c₂ : ℤ) = 2 δ_{e c₁, e c₂} - C_{e c₁, e c₂}`. -/
theorem mckayMatrix_apply (h : IsMcKayLabelling V t e) (c₁ c₂ : SimpleFDRepClasses ℂ G) :
    (mckayMatrix V c₁ c₂ : ℤ) =
      2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂) := by
  induction c₁ using SimpleFDRepClasses.ind with | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with | h Y hY =>
    rw [mckayMatrix_mk_mk]; exact h.1 X Y

/-- Under a McKay labelling, `(c.finrank : ℤ) = t.marks (e c)` for every simple class `c`. -/
theorem finrank_eq_marks (h : IsMcKayLabelling V t e) (c : SimpleFDRepClasses ℂ G) :
    (c.finrank : ℤ) = t.marks (e c) := by
  induction c using SimpleFDRepClasses.ind with
  | h X hX => rw [SimpleFDRepClasses.finrank_mk]; exact h.2.1 X

/-- Under a McKay labelling, `SimpleFDRepClasses.trivial ℂ G` maps to `t.affineNode`. -/
theorem apply_trivial (h : IsMcKayLabelling V t e) :
    e (SimpleFDRepClasses.trivial ℂ G) = t.affineNode := by
  rw [SimpleFDRepClasses.trivial_def]
  exact h.2.2 _ fun g ↦ LinearMap.ext fun v ↦ by
    rw [FDRep.of_ρ', _root_.Representation.trivial_apply, one_apply_eq_self]

/-- **Uniqueness of the affine Dynkin type in a McKay labelling.** Any two valid affine
simply-laced diagrams admitting McKay labellings for the same representation `V` are equal. -/
theorem eq_of_valid {t₁ t₂ : AffineDynkinType} {e₁ : SimpleFDRepClasses ℂ G ≃ Fin t₁.nodes}
    {e₂ : SimpleFDRepClasses ℂ G ≃ Fin t₂.nodes} (ht₁ : t₁.Valid) (ht₂ : t₂.Valid)
    (h₁ : IsMcKayLabelling V t₁ e₁) (h₂ : IsMcKayLabelling V t₂ e₂) :
    t₁ = t₂ := by
  let σ : Fin t₁.nodes ≃ Fin t₂.nodes := e₁.symm.trans e₂
  have hC : t₂.cartanMatrix.submatrix σ σ = t₁.cartanMatrix := by
    ext i j
    have eq1 := h₁.mckayMatrix_apply (e₁.symm i) (e₁.symm j)
    have eq2 := h₂.mckayMatrix_apply (e₁.symm i) (e₁.symm j)
    simp only [Equiv.apply_symm_apply] at eq1
    have hiff : (e₂ (e₁.symm i) = e₂ (e₁.symm j)) ↔ (i = j) := by
      rw [e₂.injective.eq_iff, e₁.symm.injective.eq_iff]
    simp only [Matrix.submatrix_apply, σ, Equiv.trans_apply, hiff] at eq2 ⊢
    omega
  have hgraph : t₁.graph = t₂.graph.comap σ := by
    rw [AffineDynkinType.graph_eq_diagramGraph_cartanMatrix t₁,
      AffineDynkinType.graph_eq_diagramGraph_cartanMatrix t₂, ← hC,
      diagramGraph_submatrix σ.injective]
  exact AffineDynkinType.eq_of_graph_iso ht₁ ht₂ ⟨σ, fun {i j} ↦ by simp [hgraph]⟩

end IsMcKayLabelling

/-- `TauCeti.IsMcKayLabelling V t e` is equivalent to the three isomorphism-class identities on
`mckayMatrix V`, `SimpleFDRepClasses.finrank`, and `SimpleFDRepClasses.trivial ℂ G`. -/
theorem isMcKayLabelling_iff_mckayMatrix {G : Type u} [Group G] (V : FDRep ℂ G)
    (t : AffineDynkinType) (e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes) :
    IsMcKayLabelling V t e ↔
      (∀ c₁ c₂ : SimpleFDRepClasses ℂ G,
          (mckayMatrix V c₁ c₂ : ℤ) =
            2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂)) ∧
        (∀ c : SimpleFDRepClasses ℂ G, (c.finrank : ℤ) = t.marks (e c)) ∧
        e (SimpleFDRepClasses.trivial ℂ G) = t.affineNode := by
  refine ⟨fun h ↦ ⟨h.mckayMatrix_apply, h.finrank_eq_marks, h.apply_trivial⟩, ?_⟩
  rintro ⟨hM, hδ, hAff⟩
  refine ⟨fun X Y _ _ ↦ ?_, fun X _ ↦ ?_, fun X _ htriv ↦ ?_⟩
  · simpa [mckayMatrix_mk_mk] using hM (SimpleFDRepClasses.mk X) (SimpleFDRepClasses.mk Y)
  · simpa [SimpleFDRepClasses.finrank_mk] using hδ (SimpleFDRepClasses.mk X)
  · rwa [(SimpleFDRepClasses.mk_eq_trivial_iff X).mpr htriv]

/-- Transport a McKay labelling along an isomorphism `V₁ ≅ V₂` in `FDRep ℂ G`. -/
theorem IsMcKayLabelling.of_iso {G : Type u} [Group G] {V₁ V₂ : FDRep ℂ G} (iso : V₁ ≅ V₂)
    {t : AffineDynkinType} {e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes}
    (h : IsMcKayLabelling V₁ t e) : IsMcKayLabelling V₂ t e := by
  rw [isMcKayLabelling_iff_mckayMatrix, ← mckayMatrix_congr iso]
  exact (isMcKayLabelling_iff_mckayMatrix V₁ t e).mp h

/-- Isomorphic complex representations admit the same McKay labellings. -/
theorem isMcKayLabelling_congr {G : Type u} [Group G] {V₁ V₂ : FDRep ℂ G} (iso : V₁ ≅ V₂)
    (t : AffineDynkinType) (e : SimpleFDRepClasses ℂ G ≃ Fin t.nodes) :
    IsMcKayLabelling V₁ t e ↔ IsMcKayLabelling V₂ t e :=
  ⟨fun h ↦ h.of_iso iso, fun h ↦ h.of_iso iso.symm⟩

/-- **The McKay correspondence** (McKay 1980; Steinberg 1985). For a nontrivial finite group `G`
and a faithful two-dimensional complex representation `V` of determinant `1`, the McKay matrix of
`V` is `2I - C` for the generalized Cartan matrix `C` of a valid affine simply-laced Dynkin
diagram, with the dimensions of the simples as its marks and the trivial representation at its
affine node. -/
theorem exists_isMcKayLabelling {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (V : FDRep ℂ G) (hdim : Module.finrank ℂ V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    ∃ (t : TauCeti.AffineDynkinType) (e : TauCeti.SimpleFDRepClasses ℂ G ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling V t e := by
  classical
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ := Fintype.ofFinite (SimpleFDRepClasses ℂ G)
  have hConn (c : SimpleFDRepClasses ℂ G) :
      Relation.ReflTransGen (fun x y ↦ x ≠ y ∧ 0 < mckayMatrix V x y)
        c (SimpleFDRepClasses.trivial ℂ G) := by
    obtain ⟨n, -, hn⟩ : ∃ n < V.characterValueCount, 0 < c.multiplicity (V.tensorPower n) := by
      induction c using SimpleFDRepClasses.ind with
      | h X hX =>
        simp_rw [SimpleFDRepClasses.multiplicity_mk]
        exact FDRep.exists_pos_finrank_hom_tensorPower V X hfaithful
          (FDRep.isIrreducible_of_simple X).finrank_pos
    rw [← mckayMatrix_pow_apply_trivial V n c] at hn
    exact Matrix.reflTransGen_ne_and_pos_of_pow_pos (mckayMatrix V) hn
  obtain ⟨t, e, ht, hLab⟩ :=
    exists_affineDynkinType_of_symm_loopFree_nullVector (mckayMatrix V)
      (isSymm_mckayMatrix_of_finrank_eq_two hdim hdet)
      (mckayMatrix_apply_self_eq_zero hdim hfaithful hdet)
      (SimpleFDRepClasses.trivial ℂ G) hConn SimpleFDRepClasses.finrank
      SimpleFDRepClasses.finrank_pos SimpleFDRepClasses.finrank_trivial
      fun c ↦ by simpa [hdim] using sum_mckayMatrix_mul_finrank V c
  exact ⟨t, e, ht, (isMcKayLabelling_iff_mckayMatrix V t e).mpr hLab⟩

end TauCeti
