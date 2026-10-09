/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.InvariantForm
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
import TauCeti.Algebra.Coalgebra.Subcomodule.Comap
import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Invariant Lagrangians for connected solvable groups

A finite-dimensional symplectic representation of a reduced connected solvable affine
group over an algebraically closed field has an invariant Lagrangian, in every
characteristic. More generally, an invariant alternating form, even a degenerate one,
admits a subrepresentation equal to its orthogonal complement.

Choose a maximal invariant isotropic subspace `W`. Its orthogonal complement is invariant.
If `W` is smaller than `Wᗮ`, Lie--Kolchin gives an eigenline in `Wᗮ/W`; its inverse image
is a larger invariant isotropic subspace, a contradiction. For a nondegenerate form the
resulting subspace has half the dimension of the representation.

An invariant Lagrangian allows ordinary Lie--Kolchin triangularization inside it. This
is the isotropic-subspace step in constructing complete invariant isotropic flags and
conjugating solvable subgroups of symplectic groups into flag stabilizers.

## References

* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §10.5 and §11.
* J. S. Milne, *Algebraic Groups* (2017), §16 and §24.6.
-/

public section

open TauCeti
open scoped TensorProduct

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {k H M : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [FiniteDimensional k M]

private theorem exists_isotropic_extension {B : BilinForm k M} (hB : B.IsAlt)
    (hinv : TauCeti.Representation.IsInvariantForm
      (Comodule.basePointsRepresentation (H := H) M) B)
    (N : Subcomodule k H M) (hN : N.toSubmodule ≤ B.orthogonal N.toSubmodule)
    (heq : N.toSubmodule ≠ B.orthogonal N.toSubmodule) :
    ∃ U : Subcomodule k H M, N.toSubmodule < U.toSubmodule ∧
      U.toSubmodule ≤ B.orthogonal U.toSubmodule := by
  classical
  -- Form the nonzero orthogonal subquotient on which Lie--Kolchin supplies an eigenline.
  let O := N.orthogonal B hinv
  have hO : O.toSubmodule = B.orthogonal N.toSubmodule :=
    Subcomodule.orthogonal_toSubmodule N B hinv
  let _ : AddCommGroup O := Module.addCommMonoidToAddCommGroup k
  have : Module.Finite k O := O.finite
  let K := N.comap O.subtype
  let Q := O ⧸ K.toSubmodule
  have hK : K.toSubmodule ≠ ⊤ := by
    intro htop
    apply heq
    apply le_antisymm hN
    intro m hm
    have hmO : m ∈ O := by
      rwa [← Subcomodule.mem_toSubmodule, Subcomodule.orthogonal_toSubmodule]
    have : (⟨m, hmO⟩ : O) ∈ K.toSubmodule := htop ▸ Submodule.mem_top
    simpa only [K, Subcomodule.mem_toSubmodule, Subcomodule.mem_comap,
      Subcomodule.subtype_apply] using this
  have : Nontrivial Q := Submodule.Quotient.nontrivial_iff.mpr hK
  -- Pull the eigenline back, then include it in the original representation.
  obtain ⟨q, c, hq, -, hcoact⟩ :=
    (Comodule.hasNonzeroWeightVector_iff (k := k) (C := H)).mp
      (Comodule.hasNonzeroWeightVector_of_isSolvable (k := k) (H := H) (M := Q))
  obtain ⟨v, hv⟩ := K.mkQ_surjective q
  let L : Subcomodule k H Q := Subcomodule.ofSubmodule (k ∙ q) fun x hx ↦ by
    rw [Comodule.coact_eq_tmul_of_mem_span hcoact hx]
    exact ⟨⟨x, hx⟩ ⊗ₜ[k] c, by simp⟩
  let U := (L.comap K.mkQ).map O.subtype
  have hU : U.toSubmodule = N.toSubmodule ⊔ k ∙ (v : M) := by
    rw [Subcomodule.map_toSubmodule, Subcomodule.comap_toSubmodule,
      Subcomodule.mkQ_toLinearMap]
    -- The weight line is the image of the span of the chosen lift.
    have hv' : K.toSubmodule.mkQ v = q := by
      simpa only [Subcomodule.mkQ_apply, Submodule.mkQ_apply] using hv
    have hL : L.toSubmodule = (k ∙ v).map K.toSubmodule.mkQ := by
      rw [Submodule.map_span, Set.image_singleton, hv']
      rfl
    have hrange : LinearMap.range O.subtype.toLinearMap = O.toSubmodule := by
      ext m
      simp only [LinearMap.mem_range, Comodule.Hom.coe_toLinearMap, Subcomodule.subtype_apply,
        Subcomodule.mem_toSubmodule, Subtype.exists, exists_prop, exists_eq_right]
    rw [hL, Submodule.comap_map_mkQ, Submodule.map_sup,
      Subcomodule.comap_toSubmodule, Submodule.map_comap_eq, hrange,
      inf_comm, inf_eq_left.mpr (hO.symm ▸ hN),
      Submodule.map_span, Set.image_singleton, Comodule.Hom.coe_toLinearMap,
      Subcomodule.subtype_apply]
  have hiso : U.toSubmodule ≤ B.orthogonal U.toSubmodule := by
    rw [hU]
    apply hB.sup_span_singleton_le_orthogonal hN
    simpa only [← Subcomodule.mem_toSubmodule, hO] using v.property
  have hle : N.toSubmodule ≤ U.toSubmodule := by rw [hU]; exact le_sup_left
  -- The lifted vector cannot lie in N, since its class is nonzero.
  refine ⟨U, lt_of_le_not_ge hle ?_, hiso⟩
  intro hback
  have hvN : (v : M) ∈ N := hback (hU ▸ Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self (v : M)))
  have hvK : v ∈ K := by
    simpa only [K, Subcomodule.mem_comap, Subcomodule.subtype_apply] using hvN
  exact (hq (hv ▸ (K.mkQ_eq_zero_iff v).mpr hvK)).elim

/-- An invariant alternating form on a representation of a connected solvable affine group
admits a subrepresentation equal to its orthogonal complement. The form may be degenerate. -/
theorem IsAlt.exists_subcomodule_eq_orthogonal_of_isSolvable {B : BilinForm k M} (hB : B.IsAlt)
    (hinv : TauCeti.Representation.IsInvariantForm
      (Comodule.basePointsRepresentation (H := H) M) B) :
    ∃ N : Subcomodule k H M, N.toSubmodule = B.orthogonal N.toSubmodule := by
  classical
  let S : Set (Submodule k M) := {W | ∃ N : Subcomodule k H M,
    N.toSubmodule = W ∧ W ≤ B.orthogonal W}
  obtain ⟨W, hW, hmax⟩ := WellFoundedGT.exists_maximal
    (inferInstance : WellFoundedGT (Submodule k M)) S
    ⟨⊥, ⊥, Subcomodule.bot_toSubmodule, bot_le⟩
  obtain ⟨N, rfl, hN⟩ := hW
  refine ⟨N, ?_⟩
  by_contra heq
  obtain ⟨U, hNU, hU⟩ := exists_isotropic_extension hB hinv N hN heq
  exact hNU.not_ge (hmax ⟨U, rfl, hU⟩ hNU.le)

/-- A symplectic representation of a reduced connected solvable affine group has an invariant
Lagrangian: a self-orthogonal subrepresentation of half the ambient dimension. This includes
characteristic two and the zero-dimensional representation. -/
theorem IsAlt.exists_lagrangian_subcomodule_of_isSolvable {B : BilinForm k M} (hB : B.IsAlt)
    (hnd : B.Nondegenerate)
    (hinv : TauCeti.Representation.IsInvariantForm
      (Comodule.basePointsRepresentation (H := H) M) B) :
    ∃ N : Subcomodule k H M, N.toSubmodule = B.orthogonal N.toSubmodule ∧
      2 * Module.finrank k N.toSubmodule = Module.finrank k M := by
  obtain ⟨N, hN⟩ := hB.exists_subcomodule_eq_orthogonal_of_isSolvable hinv
  refine ⟨N, hN, ?_⟩
  have hrank := B.finrank_add_finrank_orthogonal hB.isRefl N.toSubmodule
  rw [B.orthogonal_top_eq_bot hnd, inf_bot_eq, finrank_bot, add_zero, ← hN] at hrank
  omega

end LinearMap.BilinForm
