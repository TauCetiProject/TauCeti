/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains
import TauCeti.Algebra.Homology.ModuleCat.QuasiIso

/-!
# Excision for relative singular homology with local coefficients

Let `(X, B)` be a topological pair, `L` a local coefficient system on `X` with values in modules
over a ring `R`, and `A ⊆ X` a subset such that the interiors of `A` and `B` cover `X`. The
inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces a quasi-isomorphism of relative twisted chains,
with the restriction of `L` to `A` on the source
(`TopPair.quasiIso_twistedChainComplexMap_excisionMap`), hence isomorphisms on relative homology
with local coefficients in every degree (`TopPair.isIso_twistedHomologyMap_excisionMap`).
Equivalently, excising a set `Z` whose closure lies in the interior of `B` does not change
relative homology with local coefficients (`TopPair.isIso_twistedHomologyMap_excisionMap_compl`),
and relative homology modulo the complement of a closed set `K` may be computed in any open
neighbourhood of `K` (`TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset`). No
freeness, projectivity or triviality of the coefficient fibres is needed.

Excision is what reduces the relative homology of consecutive skeleta of a CW complex, and of the
preimages of skeleta under a fibration, to the cells, so it is the input of cellular homology with
local coefficients.

The excision isomorphisms are natural in the excision data: a map `g` of excision data gives the
commutative square `TopPair.interPairMap_comp_excisionMap` of maps of pairs, which
`TopPair.twistedHomologyMap_comp` turns into a commutative square of relative twisted homology
maps. They commute with the connecting morphisms of the two pairs by
`TopPair.twistedHomologyδ_naturality` applied to the excision map.

## The argument

The proof is Hatcher's, carried out on the supports of twisted chains in the ambient space, for
any map of pairs `f : P ⟶ Q` which is an embedding on ambient spaces, whose subspace is the full
preimage of the subspace of `Q`, and such that the interiors of the image of `f` and of the
subspace of `Q` cover the ambient space of `Q`
(`TopPair.quasiIso_twistedChainComplexMap_of_interior_union`). A relative twisted chain vanishes
exactly when a representing chain is supported in the subspace
(`TopPair.twistedChainComplexπ_f_eq_zero_iff`), and pushing forward along `f` identifies the
twisted chains of `P` with the chains of `Q` supported in the image of `f`, compatibly with
supports in subspaces. Iterated barycentric subdivision makes every chain a sum of a chain over the
image of `f` and a chain over the subspace of `Q`, and changes a chain whose boundary lies over the
subspace only by a boundary, modulo chains over the subspace.

## Main results

* `TopPair.twistedChainComplexπ_f_eq_zero_iff`: the kernel of the quotient map onto relative
  twisted chains consists of the chains supported in the subspace.
* `TopPair.quasiIso_twistedChainComplexMap_of_interior_union`,
  `TopPair.isIso_twistedHomologyMap_of_interior_union`: excision with local coefficients for an
  embedding of pairs whose image and target subspace have interiors covering the target.
* `TopPair.quasiIso_twistedChainComplexMap_excisionMap`,
  `TopPair.isIso_twistedHomologyMap_excisionMap`: **excision with local coefficients**.
* `TopPair.isIso_twistedHomologyMap_excisionMap_compl`: excision of a set whose closure lies in
  the interior of the subspace.
* `TopPair.isIso_twistedHomologyMap_excisionMap_of_closure_subset`,
  `TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset`: relative homology modulo
  the complement of `K` computed in an open neighbourhood of `K`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Theorem 2.20 and Proposition 2.21, and
  Section 3.H, for local coefficients.
* The twisted subdivision and small-chain constructions in
  `TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains`.
-/

public section

noncomputable section

open CategoryTheory Simplicial TauCeti TauCeti.LocalCoefficientSystem

universe u v w

namespace TopPair

variable {R : Type u} [Ring R]

section Kernel

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- A relative twisted chain of a pair vanishes exactly when a representing ambient chain is
supported in the subspace. -/
theorem twistedChainComplexπ_f_eq_zero_iff {n : ℕ} (c : L.twistedChainComplex.X n) :
    ((P.twistedChainComplexπ L).f n).hom c = 0 ↔
      c ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range P.map) n := by
  have hsmall (σ : (TopCat.toSSet.obj P.fst) _⦋n⦌) :
      σ ∈ (P.fst.smallSingularSubcomplex fun _ : Unit ↦ Set.range P.map).obj _ ↔
        Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map := by
    rw [TopCat.mem_smallSingularSubcomplex_iff, exists_const,
      ← P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff,
      P.mem_range_toSSet_map_app_iff_range_simplexMap_subset]
  rw [mem_smallTwistedChains_iff]
  constructor
  · intro hc σ hσ
    rw [← P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ ((hsmall σ).not.1 hσ), hc,
      map_zero]
  · intro hc
    refine P.twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
    rw [twistedChainComplexCoeff_twistedChainComplexπ_f_apply, hc σ ((hsmall σ).not.2 hσ),
      map_zero]

end Kernel

section Excision

variable {P Q : TopPair.{v}} (f : P ⟶ Q) (L : LocalCoefficientSystem.{u, v, max v w} R Q.fst)
  (hf : Topology.IsEmbedding (Hom.fst f))
  (hsnd : ∀ x, Hom.fst f x ∈ Set.range Q.map → x ∈ Set.range P.map)
  (hcov : interior (Set.range (Hom.fst f)) ∪ interior (Set.range Q.map) = Set.univ)

include hf hsnd in
/-- For a map of pairs which is an embedding on ambient spaces and whose subspace is the full
preimage of the subspace of the target, a relative twisted chain of the source vanishes exactly
when its push-forward to the target space is supported in the subspace of the target. -/
lemma twistedChainComplexπ_f_eq_zero_iff_twistedChainComplexMap_f_mem {n : ℕ}
    (a : ((LocalCoefficientSystem.pullback (Hom.fst f).hom).obj L).twistedChainComplex.X n) :
    ((P.twistedChainComplexπ _).f n).hom a = 0 ↔
      ((LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n).hom a ∈
        smallTwistedChains L (fun _ : Unit ↦ Set.range Q.map) n := by
  have : Mono (Hom.fst f) := (TopCat.mono_iff_injective _).2 hf.injective
  have hpre : Hom.fst f ⁻¹' Set.range Q.map = Set.range P.map := by
    ext x
    refine ⟨hsnd x, ?_⟩
    rintro ⟨p, rfl⟩
    exact ⟨Hom.snd f p, Hom.w_apply f p⟩
  rw [twistedChainComplexπ_f_eq_zero_iff, twistedChainComplexMap_f_mem_smallTwistedChains_iff,
    hpre]

include hf hsnd hcov in
/-- **Excision with local coefficients, for maps of pairs.** Let `f : P ⟶ Q` be a map of
topological pairs which is an embedding on ambient spaces and whose subspace is the full preimage
of the subspace of `Q`. If the interiors of the image of `f` and of the subspace of `Q` cover the
ambient space of `Q`, then `f` induces a quasi-isomorphism of relative singular chains with
coefficients in any local system `L` on the ambient space of `Q`, pulled back on the source. -/
theorem quasiIso_twistedChainComplexMap_of_interior_union :
    QuasiIso (TopPair.twistedChainComplexMap f L) := by
  rw [quasiIso_iff]
  intro n
  rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (n := n) (p := n + 1) (m := n - 1) (by simp)
    (by cases n <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])]
  have hπP {k : ℕ} := twistedChainComplexπ_f_eq_zero_iff_twistedChainComplexMap_f_mem f L hf hsnd
    (n := k)
  have hπQ {k : ℕ} (c : L.twistedChainComplex.X k) :=
    Q.twistedChainComplexπ_f_eq_zero_iff L c
  -- Chains supported in the image of `f` are pushed forward from the source.
  have hJ {k : ℕ} {c : L.twistedChainComplex.X k}
      (hc : c ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range (Hom.fst f)) k) :
      ∃ a, (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f k a = c :=
    smallTwistedChains_range_le_range_twistedChainComplexMap_f (Hom.fst f) L hf.isInducing k hc
  have hφ {k : ℕ} (a) :
      (TopPair.twistedChainComplexMap f L).f k ((P.twistedChainComplexπ _).f k a) =
        (Q.twistedChainComplexπ L).f k
          ((LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f k a) :=
    congrArg (fun g ↦ (g.f k).hom a)
      (TopPair.twistedChainComplexπ_comp_twistedChainComplexMap f L)
  constructor
  · -- A relative cycle of `Q` is homologous to the class of a subdivision, which comes from `P`.
    intro y hy
    obtain ⟨z, rfl⟩ := Q.twistedChainComplexπ_f_surjective L y
    have hdz : L.twistedChainComplex.d n (n - 1) z ∈
        smallTwistedChains L (fun _ : Unit ↦ Set.range Q.map) (n - 1) := by
      rw [← hπQ, ← HomologicalComplex.Hom.comm_apply]
      exact hy
    obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_mem_sup L hcov z
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hN
    obtain ⟨a', rfl⟩ := hJ ha
    refine ⟨(P.twistedChainComplexπ _).f n a', ?_, (Q.twistedChainComplexπ L).f (n + 1)
      ((((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1)).hom z), ?_⟩
    · -- The boundary of the part over the image of `f` lies over the subspace.
      rw [HomologicalComplex.Hom.comm_apply, hπP, ← HomologicalComplex.Hom.comm_apply,
        eq_sub_of_add_eq hab, map_sub]
      refine sub_mem ?_ (d_mem_smallTwistedChains L _ hb)
      rw [HomologicalComplex.Hom.comm_apply]
      exact iterate_twistedSubdivision_mem_smallTwistedChains L _ hdz N
    · rw [HomologicalComplex.Hom.comm_apply, hφ, ← map_sub, eq_comm, ← sub_eq_zero, ← map_sub,
        hπQ]
      convert sub_mem (sub_iterate_twistedSubdivision_sub_d_mem_smallTwistedChains L _ z hdz N)
        (neg_mem hb) using 1
      rw [← hab]
      abel
  · -- A filling in `Q` of the image of a relative cycle of `P` subdivides to a filling in `P`.
    intro x hx bb hbb
    obtain ⟨y, rfl⟩ := P.twistedChainComplexπ_f_surjective _ x
    obtain ⟨w, rfl⟩ := Q.twistedChainComplexπ_f_surjective L bb
    set Y := (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n y with hY
    have hdY : L.twistedChainComplex.d n (n - 1) Y ∈
        smallTwistedChains L (fun _ : Unit ↦ Set.range Q.map) (n - 1) := by
      rw [hY, HomologicalComplex.Hom.comm_apply, ← hπP, ← HomologicalComplex.Hom.comm_apply]
      exact hx
    have hc : Y - L.twistedChainComplex.d (n + 1) n w ∈
        smallTwistedChains L (fun _ : Unit ↦ Set.range Q.map) n := by
      rw [← hπQ, map_sub, ← HomologicalComplex.Hom.comm_apply, hbb, hφ, sub_self]
    have hYsmall : Y ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range (Hom.fst f)) n :=
      twistedChainComplexMap_mem_smallTwistedChains (fun _ : Unit ↦ Set.univ)
        (fun _ : Unit ↦ Set.range (Hom.fst f)) _ L id
        (fun _ x _ ↦ ⟨x, rfl⟩)
        (by simp [mem_smallTwistedChains_iff, TopCat.mem_smallSingularSubcomplex_iff])
    obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_mem_sup L hcov w
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hN
    obtain ⟨a', ha'⟩ :=
      hJ (add_mem (idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains L _ hYsmall N) ha)
    have hsdw : (((End.of (twistedSubdivisionChainMap L)) ^ N).asHom.f n).hom
        (L.twistedChainComplex.d (n + 1) n w) =
          L.twistedChainComplex.d (n + 1) n a + L.twistedChainComplex.d (n + 1) n b := by
      rw [← HomologicalComplex.Hom.comm_apply, ← hab, map_add]
    refine ⟨(P.twistedChainComplexπ _).f (n + 1) a', ?_⟩
    rw [HomologicalComplex.Hom.comm_apply, eq_comm, ← sub_eq_zero, ← map_sub, hπP, map_sub,
      ← HomologicalComplex.Hom.comm_apply, ha', ← hY]
    convert add_mem (add_mem
      (sub_iterate_twistedSubdivision_sub_d_mem_smallTwistedChains L _ Y hdY N)
      (d_mem_smallTwistedChains L _ hb (j := n)))
      (iterate_twistedSubdivision_mem_smallTwistedChains L _ hc N) using 1
    rw [map_add, map_sub, hsdw]
    abel

include hf hsnd hcov in
/-- **Excision with local coefficients, for maps of pairs.** Under the hypotheses of
`TopPair.quasiIso_twistedChainComplexMap_of_interior_union`, `f` induces isomorphisms on relative
singular homology with local coefficients in every degree. -/
theorem isIso_twistedHomologyMap_of_interior_union (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap f L n) := by
  have := quasiIso_twistedChainComplexMap_of_interior_union f L hf hsnd hcov
  infer_instance

end Excision

section Subsets

variable {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X) (A B : Set X)

/-- **Excision with local coefficients.** If the interiors of `A` and `B` cover `X`, the
inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces a quasi-isomorphism of relative singular chains
with coefficients in a local system `L` on `X`, restricted to `A` on the source. -/
theorem quasiIso_twistedChainComplexMap_excisionMap (h : interior A ∪ interior B = Set.univ) :
    QuasiIso (TopPair.twistedChainComplexMap (excisionMap A B) L) := by
  refine quasiIso_twistedChainComplexMap_of_interior_union (excisionMap A B) L
    (isEmbedding_fst_excisionMap A B) (mem_range_map_of_fst_excisionMap_mem A B) ?_
  rw [range_fst_excisionMap, range_ofSubset_map]
  exact h

/-- **Excision with local coefficients.** If the interiors of `A` and `B` cover `X`, the
inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces isomorphisms on relative singular homology with
coefficients in a local system `L` on `X`, restricted to `A` on the source. -/
theorem isIso_twistedHomologyMap_excisionMap (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap (excisionMap A B) L n) := by
  have := quasiIso_twistedChainComplexMap_excisionMap L A B h
  infer_instance

/-- **Excision of a set with closure in the interior of the subspace, with local coefficients.**
If `closure Z ⊆ interior B`, the inclusion of pairs `(X ∖ Z, B ∖ Z) ⟶ (X, B)` induces
isomorphisms on relative singular homology with coefficients in any local system on `X`. -/
theorem isIso_twistedHomologyMap_excisionMap_compl (Z : Set X) (h : closure Z ⊆ interior B)
    (n : ℕ) : IsIso (TopPair.twistedHomologyMap (excisionMap Zᶜ B) L n) := by
  refine isIso_twistedHomologyMap_excisionMap L Zᶜ B ?_ n
  rw [interior_compl, Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (h hx)
  · exact Or.inl hx

/-- **Excision onto a neighbourhood of the closure, with local coefficients.** If `U` is open and
contains the closure of `K`, the inclusion of pairs `(U, U ∖ K) ⟶ (X, X ∖ K)` induces
isomorphisms on relative singular homology with coefficients in any local system on `X`. -/
theorem isIso_twistedHomologyMap_excisionMap_of_closure_subset {U K : Set X} (hU : IsOpen U)
    (hKU : closure K ⊆ U) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap (excisionMap U Kᶜ) L n) := by
  refine isIso_twistedHomologyMap_excisionMap L U Kᶜ ?_ n
  rw [hU.interior_eq, interior_compl]
  exact Set.eq_univ_of_subset (Set.union_subset_union_left _ hKU) (Set.union_compl_self _)

/-- **Excision onto a neighbourhood, with local coefficients.** If `U` is open and contains the
closed set `K`, the inclusion of pairs `(U, U ∖ K) ⟶ (X, X ∖ K)` induces isomorphisms on relative
singular homology with coefficients in any local system on `X`. -/
theorem isIso_twistedHomologyMap_excisionMap_of_isClosed_subset {U K : Set X} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    IsIso (TopPair.twistedHomologyMap (excisionMap U Kᶜ) L n) :=
  isIso_twistedHomologyMap_excisionMap_of_closure_subset L hU (hK.closure_eq.symm ▸ hKU) n

end Subsets

end TopPair
