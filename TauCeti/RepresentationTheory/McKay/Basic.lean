/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.McKay.Matrix
import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Recognition
import TauCeti.RepresentationTheory.CharacterTable.IrreducibleClassification

/-!
# The McKay correspondence

Let `G` be a nontrivial finite group and `V` a faithful two-dimensional complex representation of
`G` with `det (V.ρ g) = 1` for every `g : G`. John McKay observed in 1980 that the tensor-product
multiplicities `dim_ℂ Hom_G(X, V ⊗ Y)` on `SimpleClasses (FDRep ℂ G)` form `2I - C` for the
generalized Cartan matrix `C` of a valid affine simply-laced Dynkin diagram (`Aₙ` for `n ≥ 1`,
`Dₙ` for `n ≥ 4`, or `E₆`, `E₇`, `E₈`), with the irreducible dimensions as marks and the trivial
representation at an affine node.

Following Steinberg (1985), `TauCeti.exists_isMcKayLabelling` proves this directly without a prior
classification of the finite subgroups of `SL₂(ℂ)` by combining symmetry, loop-freeness, the
dimension eigenvector equation `M *ᵥ δ = 2 • δ` (null vector of `2I - M`), and reachability to the
trivial class from `TauCeti.RepresentationTheory.McKay.Matrix` with matrix affine-diagram
recognition (`Matrix.exists_affineDynkinType_of_isSymm_of_diag_eq_zero_of_mulVec_eq_two_smul`).

## Main definitions and results

* `TauCeti.IsMcKayLabelling`: an affine ADE labelling of `SimpleClasses (FDRep ℂ G)` relative to
  `V`, characterized by `TauCeti.isMcKayLabelling_iff` and
  `TauCeti.isMcKayLabelling_iff_mckayMatrix`, with transport along representations and group
  isomorphisms (`TauCeti.IsMcKayLabelling.of_iso`, `TauCeti.isMcKayLabelling_res_iff`,
  `TauCeti.IsMcKayLabelling.res`, `TauCeti.IsMcKayLabelling.of_mulEquiv`).
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

universe u v

namespace TauCeti

/-- A **McKay labelling** of the simple complex representations of `G` by an affine simply-laced
diagram `t`, relative to `V`: a bijection `e` from `SimpleClasses (FDRep ℂ G)` to `Fin t.nodes`
such that `dim_ℂ Hom_G(X, V ⊗ Y) = 2 δ_{e [X], e [Y]} - C_{e [X], e [Y]}`,
`dim_ℂ X = t.marks (e [X])`, and any simple trivial representation sits at `t.affineNode`. -/
def IsMcKayLabelling {G : Type u} [Group G] (V : FDRep ℂ G) (t : TauCeti.AffineDynkinType)
    (e : TauCeti.SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes) : Prop :=
  (∀ (X Y : FDRep ℂ G) [Simple X] [Simple Y],
      (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
        2 * (if e (SimpleClasses.classOf X) = e (SimpleClasses.classOf Y) then 1 else 0) -
          t.cartanMatrix (e (SimpleClasses.classOf X)) (e (SimpleClasses.classOf Y))) ∧
    (∀ (X : FDRep ℂ G) [Simple X],
      (Module.finrank ℂ X : ℤ) = t.marks (e (SimpleClasses.classOf X))) ∧
    ∀ (X : FDRep ℂ G) [Simple X], (∀ g : G, X.ρ g = 1) →
      e (SimpleClasses.classOf X) = t.affineNode

/-- Defining characterization of `TauCeti.IsMcKayLabelling` on simple objects of `FDRep ℂ G`. -/
theorem isMcKayLabelling_iff {G : Type u} [Group G] (V : FDRep ℂ G)
    (t : AffineDynkinType) (e : SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes) :
    IsMcKayLabelling V t e ↔
      (∀ (X Y : FDRep ℂ G) [Simple X] [Simple Y],
          (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
            2 * (if e (SimpleClasses.classOf X) = e (SimpleClasses.classOf Y) then 1 else 0) -
              t.cartanMatrix (e (SimpleClasses.classOf X)) (e (SimpleClasses.classOf Y))) ∧
        (∀ (X : FDRep ℂ G) [Simple X],
          (Module.finrank ℂ X : ℤ) = t.marks (e (SimpleClasses.classOf X))) ∧
        ∀ (X : FDRep ℂ G) [Simple X], (∀ g : G, X.ρ g = 1) →
          e (SimpleClasses.classOf X) = t.affineNode :=
  Iff.rfl

namespace IsMcKayLabelling

variable {G : Type u} [Group G] {V : FDRep ℂ G} {t : AffineDynkinType}
  {e : SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes}

/-- Object-level Hom-dimension identity under a McKay labelling (the multiplicity identity when `G`
is finite). -/
theorem finrank_hom_tensor (h : IsMcKayLabelling V t e) (X Y : FDRep ℂ G) [Simple X] [Simple Y] :
    (Module.finrank ℂ (X ⟶ V ⊗ Y) : ℤ) =
      2 * (if e (SimpleClasses.classOf X) = e (SimpleClasses.classOf Y) then 1 else 0) -
        t.cartanMatrix (e (SimpleClasses.classOf X)) (e (SimpleClasses.classOf Y)) :=
  h.1 X Y

/-- Object-level mark identity under a McKay labelling. -/
theorem finrank_eq_marks_classOf (h : IsMcKayLabelling V t e) (X : FDRep ℂ G) [Simple X] :
    (Module.finrank ℂ X : ℤ) = t.marks (e (SimpleClasses.classOf X)) :=
  h.2.1 X

/-- Object-level affine-node normalization under a McKay labelling. -/
theorem apply_classOf_of_trivial (h : IsMcKayLabelling V t e) (X : FDRep ℂ G) [Simple X]
    (htriv : ∀ g : G, X.ρ g = 1) : e (SimpleClasses.classOf X) = t.affineNode :=
  h.2.2 X htriv

/-- Under a McKay labelling, `(V.mckayMatrix c₁ c₂ : ℤ) = 2 δ_{e c₁, e c₂} - C_{e c₁, e c₂}`. -/
theorem mckayMatrix_apply (h : IsMcKayLabelling V t e) (c₁ c₂ : SimpleClasses (FDRep ℂ G)) :
    (V.mckayMatrix c₁ c₂ : ℤ) =
      2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂) := by
  induction c₁ using SimpleClasses.ind with | h X =>
  induction c₂ using SimpleClasses.ind with | h Y =>
    rw [FDRep.mckayMatrix_classOf_classOf]; exact h.1 X Y

/-- Under a McKay labelling, reindexing the integer-cast McKay matrix along `e` gives
`2 • 1 - t.cartanMatrix`. -/
theorem reindex_mckayMatrix (h : IsMcKayLabelling V t e) :
    Matrix.reindex e e (V.mckayMatrix.map (Nat.cast : ℕ → ℤ)) = 2 • 1 - t.cartanMatrix := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply,
    h.mckayMatrix_apply, Equiv.apply_symm_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply]
  split_ifs <;> ring

/-- Under a McKay labelling, `(c.finrank : ℤ) = t.marks (e c)` for every simple class `c`. -/
theorem finrank_eq_marks (h : IsMcKayLabelling V t e) (c : SimpleClasses (FDRep ℂ G)) :
    (c.finrank : ℤ) = t.marks (e c) := by
  induction c using SimpleClasses.ind with
  | h X => rw [SimpleClasses.finrank_classOf]; exact h.2.1 X

/-- Under a McKay labelling, `SimpleClasses.trivial ℂ G` maps to `t.affineNode`. -/
theorem apply_trivial (h : IsMcKayLabelling V t e) :
    e (SimpleClasses.trivial ℂ G) = t.affineNode := by
  rw [SimpleClasses.trivial_def]
  exact h.2.2 _ fun _ ↦ LinearMap.ext fun _ ↦ rfl

/-- **Uniqueness of the affine Dynkin type in a McKay labelling.** Any two valid affine
simply-laced diagrams admitting McKay labellings for the same representation `V` are equal. -/
theorem eq_of_valid {t₁ t₂ : AffineDynkinType}
    {e₁ : SimpleClasses (FDRep ℂ G) ≃ Fin t₁.nodes}
    {e₂ : SimpleClasses (FDRep ℂ G) ≃ Fin t₂.nodes} (ht₁ : t₁.Valid) (ht₂ : t₂.Valid)
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
`V.mckayMatrix`, `SimpleClasses.finrank`, and `SimpleClasses.trivial ℂ G`. -/
theorem isMcKayLabelling_iff_mckayMatrix {G : Type u} [Group G] (V : FDRep ℂ G)
    (t : AffineDynkinType) (e : SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes) :
    IsMcKayLabelling V t e ↔
      (∀ c₁ c₂ : SimpleClasses (FDRep ℂ G),
          (V.mckayMatrix c₁ c₂ : ℤ) =
            2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂)) ∧
        (∀ c : SimpleClasses (FDRep ℂ G), (c.finrank : ℤ) = t.marks (e c)) ∧
        e (SimpleClasses.trivial ℂ G) = t.affineNode := by
  refine ⟨fun h ↦ ⟨h.mckayMatrix_apply, h.finrank_eq_marks, h.apply_trivial⟩, ?_⟩
  rintro ⟨hM, hδ, hAff⟩
  refine ⟨fun X Y _ _ ↦ ?_, fun X _ ↦ ?_, fun X _ htriv ↦ ?_⟩
  · simpa [FDRep.mckayMatrix_classOf_classOf] using
      hM (SimpleClasses.classOf X) (SimpleClasses.classOf Y)
  · simpa [SimpleClasses.finrank_classOf] using hδ (SimpleClasses.classOf X)
  · rwa [(SimpleClasses.classOf_eq_trivial_iff X).mpr htriv]

/-- Transport a McKay labelling along an isomorphism `V₁ ≅ V₂` in `FDRep ℂ G`. -/
theorem IsMcKayLabelling.of_iso {G : Type u} [Group G] {V₁ V₂ : FDRep ℂ G} (iso : V₁ ≅ V₂)
    {t : AffineDynkinType} {e : SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes}
    (h : IsMcKayLabelling V₁ t e) : IsMcKayLabelling V₂ t e := by
  rw [isMcKayLabelling_iff_mckayMatrix, ← FDRep.mckayMatrix_congr iso]
  exact (isMcKayLabelling_iff_mckayMatrix V₁ t e).mp h

/-- Isomorphic complex representations admit the same McKay labellings. -/
theorem isMcKayLabelling_congr {G : Type u} [Group G] {V₁ V₂ : FDRep ℂ G} (iso : V₁ ≅ V₂)
    (t : AffineDynkinType) (e : SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes) :
    IsMcKayLabelling V₁ t e ↔ IsMcKayLabelling V₂ t e :=
  ⟨fun h ↦ h.of_iso iso, fun h ↦ h.of_iso iso.symm⟩

/-- Restricting along a group isomorphism `φ : G₁ ≃* G₂` preserves McKay labellings via
`SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)`. -/
theorem isMcKayLabelling_res_iff {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    (φ : G₁ ≃* G₂) (V : FDRep ℂ G₂) (t : AffineDynkinType)
    (e : SimpleClasses (FDRep ℂ G₂) ≃ Fin t.nodes) :
    IsMcKayLabelling ((Action.res (FGModuleCat ℂ) (φ : G₁ →* G₂)).obj V) t
        ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).symm.trans e) ↔
      IsMcKayLabelling V t e := by
  rw [isMcKayLabelling_iff_mckayMatrix, isMcKayLabelling_iff_mckayMatrix]
  refine and_congr ?_ (and_congr ?_ ?_)
  · refine ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).forall_congr fun c₁ ↦
      (SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).forall_congr fun c₂ ↦ ?_).symm
    simp only [FDRep.mckayMatrix_res_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  · refine ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).forall_congr
      fun c ↦ ?_).symm
    simp only [SimpleClasses.finrank_equiv_actionResEquiv, Equiv.trans_apply,
      Equiv.symm_apply_apply]
  · rw [Equiv.trans_apply, ← SimpleClasses.equiv_actionResEquiv_trivial (k := ℂ) φ,
      Equiv.symm_apply_apply]

/-- Transport a McKay labelling of `V : FDRep ℂ G₂` along a group isomorphism `φ : G₁ ≃* G₂` to
the restricted representation `(Action.res (FGModuleCat ℂ) (φ : G₁ →* G₂)).obj V`. -/
theorem IsMcKayLabelling.res {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    (φ : G₁ ≃* G₂) {V : FDRep ℂ G₂} {t : AffineDynkinType}
    {e : SimpleClasses (FDRep ℂ G₂) ≃ Fin t.nodes} (h : IsMcKayLabelling V t e) :
    IsMcKayLabelling ((Action.res (FGModuleCat ℂ) (φ : G₁ →* G₂)).obj V) t
      ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).symm.trans e) :=
  (isMcKayLabelling_res_iff φ V t e).mpr h

/-- Transport a McKay labelling along a group isomorphism `φ : G₁ ≃* G₂` and an intertwiner
`(Action.res (FGModuleCat ℂ) (φ : G₁ →* G₂)).obj V₂ ≅ V₁`. -/
theorem IsMcKayLabelling.of_mulEquiv {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
    (φ : G₁ ≃* G₂) {V₁ : FDRep ℂ G₁} {V₂ : FDRep ℂ G₂}
    (iso : (Action.res (FGModuleCat ℂ) (φ : G₁ →* G₂)).obj V₂ ≅ V₁)
    {t : AffineDynkinType} {e : SimpleClasses (FDRep ℂ G₂) ≃ Fin t.nodes}
    (h : IsMcKayLabelling V₂ t e) :
    IsMcKayLabelling V₁ t
      ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ) φ)).symm.trans e) :=
  (h.res φ).of_iso iso

/-- **The McKay correspondence** (McKay 1980; Steinberg 1985). For a nontrivial finite group `G`
and a faithful two-dimensional complex representation `V` of determinant `1`, the McKay matrix of
`V` is `2I - C` for the generalized Cartan matrix `C` of a valid affine simply-laced Dynkin
diagram, with the dimensions of the simples as its marks and the trivial representation at its
affine node. -/
theorem exists_isMcKayLabelling {G : Type u} [Group G] [Finite G] [Nontrivial G]
    (V : FDRep ℂ G) (hdim : Module.finrank ℂ V = 2) (hfaithful : Function.Injective V.ρ)
    (hdet : ∀ g : G, LinearMap.det (V.ρ g) = 1) :
    ∃ (t : TauCeti.AffineDynkinType) (e : TauCeti.SimpleClasses (FDRep ℂ G) ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling V t e := by
  classical
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let _ := Fintype.ofFinite (SimpleClasses (FDRep ℂ G))
  obtain ⟨t, e, ht, hLab⟩ :=
    Matrix.exists_affineDynkinType_of_isSymm_of_diag_eq_zero_of_mulVec_eq_two_smul V.mckayMatrix
      (FDRep.isSymm_mckayMatrix_of_finrank_eq_two_of_det_eq_one hdim hdet)
      (FDRep.mckayMatrix_apply_self_eq_zero hdim hfaithful hdet)
      (SimpleClasses.trivial ℂ G) (FDRep.reflTransGen_mckayMatrix_trivial V hfaithful)
      SimpleClasses.finrank SimpleClasses.finrank_pos SimpleClasses.finrank_trivial
      (hdim ▸ FDRep.mckayMatrix_mulVec_finrank V)
  exact ⟨t, e, ht, (isMcKayLabelling_iff_mckayMatrix V t e).mpr hLab⟩

end TauCeti
