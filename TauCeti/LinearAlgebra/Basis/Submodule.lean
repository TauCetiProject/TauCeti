/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import TauCeti.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import TauCeti.LinearAlgebra.LinearIndependent.Fin

/-!
# Bases adapted to a subspace

A subspace of a finite-dimensional vector space over a division ring is spanned by a subset of
a finite basis of the ambient space. The cardinality of that subset is the dimension of the
subspace. This is useful when constructions on coordinate summands must be applied to arbitrary
subspaces. The basis is assembled from bases of the subspace and of a complement.

Two subspaces admit bases sharing an initial basis of their intersection, whose
combined complementary parts complete a basis of their sum. This gives compatible
coordinates for comparing determinants of the four subspaces.

The image of a subspace under a linear map has the same span as the images of any of its
bases, including when that span is taken over a larger scalar ring.
-/

public section

open Submodule TauCeti

namespace Submodule

section

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- A subspace of a finite-dimensional vector space is a coordinate summand for a finite basis. -/
theorem exists_basis_span_image_eq (W : Submodule k V) :
    ∃ (b : Module.Basis (Fin (Module.finrank k V)) k V)
      (s : Finset (Fin (Module.finrank k V))),
      span k (b '' (s : Set (Fin (Module.finrank k V)))) = W ∧
        s.card = Module.finrank k W := by
  obtain ⟨W', hW'⟩ := W.exists_isCompl
  let bW := Module.finBasis k W
  let c := (bW.prod (Module.finBasis k W')).map (W.prodEquivOfIsCompl W' hW')
  let e := Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis c).symm
  let s := Finset.univ.map (Function.Embedding.inl.trans e.toEmbedding)
  refine ⟨c.reindex e, s, ?_, by simp [s]⟩
  have himage : c.reindex e '' (s : Set _) = W.subtype '' Set.range bW := by
    ext x
    simp [s, c, Module.Basis.prod_apply]
  rw [himage, ← Submodule.map_span, bW.span_eq, Submodule.map_top, Submodule.range_subtype]

end

variable {k V : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]

/-- Two finite-dimensional subspaces admit bases with a common initial basis for their intersection.
The concatenation of the common part and the two complementary parts is a basis
of their sum. Empty parts, nested subspaces and the zero space are allowed. -/
theorem exists_linearIndependent_span_inf_sup (U W : Submodule k V)
    [Module.Finite k U] [Module.Finite k W] :
    ∃ (p q r : ℕ) (x : Fin p → V) (y : Fin q → V) (z : Fin r → V),
      LinearIndependent k (Fin.append x (Fin.append y z)) ∧
      span k (Set.range x) = U ⊓ W ∧
      span k (Set.range (Fin.append x y)) = U ∧
      span k (Set.range (Fin.append x z)) = W ∧
      span k (Set.range (Fin.append x (Fin.append y z))) = U ⊔ W := by
  classical
  -- Choose complements of the intersection inside each subspace.
  obtain ⟨Y, hIY, hU⟩ := IsModularLattice.exists_disjoint_and_sup_eq
    (show U ⊓ W ≤ U from inf_le_left)
  obtain ⟨Z, hIZ, hW⟩ := IsModularLattice.exists_disjoint_and_sup_eq
    (show U ⊓ W ≤ W from inf_le_right)
  have hZW : Z ≤ W := hW ▸ le_sup_right
  have : Module.Finite k Y := finiteDimensional_of_le (hU ▸ le_sup_right : Y ≤ U)
  have : Module.Finite k Z := finiteDimensional_of_le hZW
  have hUZ : Disjoint U Z := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro v hv
    exact (disjoint_def.mp hIZ) v ⟨hv.1, hZW hv.2⟩ hv.2
  let bX := Module.finBasis k ↥(U ⊓ W)
  let bY := Module.finBasis k Y
  let bZ := Module.finBasis k Z
  have hbas (P : Submodule k V) [Module.Finite k P] :
      span k (Set.range fun i ↦ (Module.finBasis k P i : V)) = P :=
    (Submodule.span_range_subtype_eq_top_iff P fun i ↦ (Module.finBasis k P i).2).1
      (Module.finBasis k P).span_eq
  refine ⟨_, _, _, (fun i ↦ (bX i : V)), (fun i ↦ (bY i : V)), (fun i ↦ (bZ i : V)),
    ?_, hbas _, ?_, ?_, ?_⟩
  · have hxy := linearIndependent_fin_append.mpr
        ⟨bX.linearIndependent_coe_basis, bY.linearIndependent_coe_basis,
          by simpa only [bX, bY, hbas] using hIY⟩
    have hxyz := linearIndependent_fin_append.mpr ⟨hxy, bZ.linearIndependent_coe_basis,
        by simpa only [span_range_fin_append, bX, bY, bZ, hbas, hU] using hUZ⟩
    rw [Fin.append_assoc] at hxyz
    exact (linearIndependent_equiv (finCongr (Nat.add_assoc _ _ _))).mp hxyz
  · rw [span_range_fin_append, hbas, hbas, hU]
  · rw [span_range_fin_append, hbas, hbas, hW]
  · rw [span_range_fin_append, span_range_fin_append, hbas, hbas, hbas, ← sup_assoc, hU]
    calc U ⊔ Z = U ⊔ ((U ⊓ W) ⊔ Z) := by
           rw [← sup_assoc, sup_eq_left.mpr (inf_le_left : U ⊓ W ≤ U)]
         _ = U ⊔ W := by rw [hW]

end Submodule

namespace Module.Basis

variable {R S M N α : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N]
  [SMul R S] [IsScalarTower R S N] {U : Submodule R M}

/-- The span of the image of a submodule is generated by the images of any basis, even when
the span is taken over a larger scalar ring. -/
theorem span_image (b : Basis α R U) (f : M →ₗ[R] N) :
    Submodule.span S (f '' (U : Set M)) = Submodule.span S (Set.range fun i ↦ f (b i)) := by
  -- The basis vectors, viewed in `M`, span `U` over `R`.
  have hU : Submodule.span R (Set.range (U.subtype ∘ b)) = U := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  -- Hence their images under `f` span the image of `U` over `R`.
  have hfU : Submodule.span R (Set.range (f ∘ U.subtype ∘ b)) = U.map f := by
    rw [Set.range_comp, Submodule.span_image, hU]
  -- Taking `S`-spans of both sides gives the claim.
  rw [← Submodule.map_coe, ← hfU, Submodule.span_span_of_tower]
  simp only [Function.comp_def, Submodule.subtype_apply]

end Module.Basis
