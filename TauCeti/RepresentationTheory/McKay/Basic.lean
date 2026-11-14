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
multiplicities `dim_ℂ Hom_G(X, V ⊗ Y)` on the isomorphism classes of simple complex representations
of `G` form `2I - C` for the generalized Cartan matrix `C` of a valid affine simply-laced Dynkin
diagram (`Aₙ` for `n ≥ 1`, `Dₙ` for `n ≥ 4`, or `E₆`, `E₇`, `E₈`), with the dimensions of the
simples as the marks and the trivial representation at an affine node.

Following Steinberg (*Finite subgroups of `SU₂`, Dynkin diagrams and affine Coxeter elements*,
1985), the classification is proved directly from representation theory
(`TauCeti.RepresentationTheory.McKay.Matrix`) and the recognition of affine simply-laced diagrams
(`TauCeti.exists_affineDynkinType_of_symm_loopFree_nullVector`), without using a prior
classification of the finite subgroups of `SL₂(ℂ)`:

1. **Symmetry** (`TauCeti.isSymm_mckayMatrix`): the `Fin 2` determinant form on `V` is unimodular
   and `G`-invariant (`Representation.equivDualOfFinrankEqTwo`), so `V` is self-dual and Frobenius
   reciprocity makes `mckayMatrix V` symmetric.
2. **Null vector** (`TauCeti.sum_mckayMatrix_mul_finrank`): decomposing `V ⊗ Y` into simples and
   passing through `ᘁV` shows that the vector `δ` of irreducible dimensions satisfies
   `M δ = (dim V) δ = 2 δ`, with `δ > 0` and `δ = 1` at the trivial class.
3. **Connectedness** (`Matrix.reflTransGen_ne_and_pos_of_pow_pos`):
   `(mckayMatrix V ^ n) c trivial` equals the multiplicity of `c` in `V^⊗n`
   (`TauCeti.mckayMatrix_pow_apply_trivial`), which is positive for some `n` by Burnside–Brauer
   faithful tensor generation (`FDRep.exists_pos_finrank_hom_tensorPower`).
4. **Loop-freeness** (`FDRep.finrank_hom_tensor_self_eq_zero`,
   `TauCeti.mckayMatrix_apply_self_eq_zero`): when `G` is nontrivial, no simple `X` occurs in
   `V ⊗ X`.
5. **Affine ADE recognition** (`TauCeti.exists_affineDynkinType_of_symm_loopFree_nullVector`): if
   some off-diagonal entry is at least `2`, additive balance forces the graph to have two vertices
   of mark `1` joined by a double edge, giving `Ã₁`. Otherwise all entries are `0` or `1`, so Kac's
   additive-function recognition theorem
   (`SimpleGraph.Connected.exists_sum_eq_two_mul_iff_existsUnique_affineDynkinType_iso`) and
   transitivity of diagram automorphisms on special nodes
   (`TauCeti.AffineDynkinType.exists_graph_iso_apply_eq_affineNode`) produce a valid affine diagram
   with the trivial representation at `affineNode`.

Both hypotheses `Nontrivial G` and `∀ g, det (V.ρ g) = 1` are sharp: for the trivial group the
`1 × 1` McKay matrix `(2)` has a self-loop and is no affine diagram, while the standard
`2`-dimensional reflection representation of `S₃` is faithful and self-dual with determinant `±1`
and has a self-loop at its `2`-dimensional simple constituent.

For the specialization to finite nontrivial subgroups of `SU(2)`, see
`TauCeti.RepresentationTheory.McKay.SU2`.

## Main definitions

* `TauCeti.IsMcKayLabelling`: an affine ADE labelling of `SimpleFDRepClasses ℂ G` relative to `V`.

## Main results

* `TauCeti.isMcKayLabelling_def`, `TauCeti.isMcKayLabelling_iff_mckayMatrix`, and
  `TauCeti.isMcKayLabelling_congr`: object-level and `mckayMatrix` characterizations of
  `IsMcKayLabelling`, and invariance under isomorphism of `V`.
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
diagram `t`, relative to `V`: a bijection `e` from `SimpleFDRepClasses ℂ G` to the nodes of `t`
such that

* the multiplicity `dim_ℂ Hom_G(X, V ⊗ Y)` of a simple `X` in `V ⊗ Y` equals `2 δ_{i,j} - C_{i,j}`
  at the nodes `i = e [X]` and `j = e [Y]`, for the generalized Cartan matrix `C` of `t`;
* the dimension of each simple equals the mark of its node;
* any one-dimensional trivial representation sits at `t.affineNode`. -/
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

/-- Unfolded characterization of `TauCeti.IsMcKayLabelling` on simple objects of `FDRep ℂ G`. -/
theorem isMcKayLabelling_def {G : Type u} [Group G] (V : FDRep ℂ G)
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

/-- Under a McKay labelling, `(mckayMatrix V c₁ c₂ : ℤ) = 2 δ_{e c₁, e c₂} - C_{e c₁, e c₂}`. -/
theorem mckayMatrix_apply (h : IsMcKayLabelling V t e) (c₁ c₂ : SimpleFDRepClasses ℂ G) :
    (mckayMatrix V c₁ c₂ : ℤ) =
      2 * (if e c₁ = e c₂ then 1 else 0) - t.cartanMatrix (e c₁) (e c₂) := by
  induction c₁ using SimpleFDRepClasses.ind with
  | h X hX =>
  induction c₂ using SimpleFDRepClasses.ind with
  | h Y hY =>
    rw [mckayMatrix_mk_mk]
    exact h.1 X Y

/-- Under a McKay labelling, `(c.finrank : ℤ) = t.marks (e c)` for every simple class `c`. -/
theorem finrank_eq_marks (h : IsMcKayLabelling V t e) (c : SimpleFDRepClasses ℂ G) :
    (c.finrank : ℤ) = t.marks (e c) := by
  induction c using SimpleFDRepClasses.ind with
  | h X hX =>
    rw [SimpleFDRepClasses.finrank_mk]
    exact h.2.1 X

/-- Under a McKay labelling, `SimpleFDRepClasses.trivial ℂ G` maps to `t.affineNode`. -/
theorem apply_trivial (h : IsMcKayLabelling V t e) :
    e (SimpleFDRepClasses.trivial ℂ G) = t.affineNode := by
  rw [SimpleFDRepClasses.trivial_def]
  refine h.2.2 _ fun g ↦ LinearMap.ext fun v ↦ ?_
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
  refine AffineDynkinType.eq_of_graph_iso ht₁ ht₂ ⟨σ, fun {i j} ↦ ?_⟩
  simp [hgraph]

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
  let _ : Fintype (SimpleFDRepClasses ℂ G) :=
    Fintype.ofEquiv _ (SimpleFDRepClasses.equivFinCardConjClasses ℂ G).symm
  have hSymm : (mckayMatrix V).IsSymm := isSymm_mckayMatrix hdim hdet
  have hLoop (c : SimpleFDRepClasses ℂ G) : mckayMatrix V c c = 0 :=
    mckayMatrix_apply_self_eq_zero hdim hfaithful hdet c
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
  have hSum (c : SimpleFDRepClasses ℂ G) :
      ∑ c₂, mckayMatrix V c c₂ * c₂.finrank = 2 * c.finrank := by
    simpa [hdim] using sum_mckayMatrix_mul_finrank V c
  obtain ⟨t, e, ht, hLab⟩ :=
    exists_affineDynkinType_of_symm_loopFree_nullVector (mckayMatrix V) hSymm hLoop
      (SimpleFDRepClasses.trivial ℂ G) hConn SimpleFDRepClasses.finrank
      SimpleFDRepClasses.finrank_pos SimpleFDRepClasses.finrank_trivial hSum
  exact ⟨t, e, ht, (isMcKayLabelling_iff_mckayMatrix V t e).mpr hLab⟩

end TauCeti
