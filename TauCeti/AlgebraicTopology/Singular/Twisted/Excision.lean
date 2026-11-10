/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.Chains
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso

/-!
# Excision for relative singular homology with local coefficients

Let `f : P ⟶ P'` be a map of topological pairs which is an embedding on ambient spaces and whose
subspace is the full preimage of the subspace of `P'`, and suppose that the ambient space of `P'`
has an open cover each of whose members lies in the subspace of `P'` or in the image of `f`. Then
for every local coefficient system `L` on the ambient space of `P'`, with arbitrary module fibres
over an arbitrary ring, `f` induces a quasi-isomorphism from the relative twisted chains of `P`
with coefficients in the pullback of `L` to those of `P'` with coefficients in `L`
(`TopPair.quasiIso_twistedChainComplexMap_of_open_cover`), hence isomorphisms on relative twisted
homology in every degree (`TopPair.isIso_twistedHomologyMap_of_open_cover`).

As for constant coefficients (`TauCeti.AlgebraicTopology.Singular.Excision`), this specializes to
the inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` when the interiors of `A` and `B` cover `X`
(`TopPair.isIso_twistedHomologyMap_excisionMap`), to excising a set whose closure lies in the
interior of the subspace (`TopPair.isIso_twistedHomologyMap_excisionMap_compl`), and to computing
homology modulo the complement of a closed set `K` in an open neighbourhood `U` of `K`
(`TopPair.isIso_twistedHomologyMap_excisionMap_of_isClosed_subset`). The last form is what
compares relative groups `H_*(U, U ∖ K; L)` of an open subset with those of the ambient space, as
needed for restriction of locally finite homology to open subsets and for compact pairs.

Two facts about the relative twisted chains of an arbitrary pair are proved on the way. An ambient
chain vanishes in relative chains exactly when it is supported in the subspace
(`TopPair.twistedChainComplexπ_f_apply_eq_zero_iff`), and on a relative cycle, iterated
barycentric subdivision changes the relative class of a representative by the boundary of the
class of its subdivision prism (`TopPair.twistedChainComplexπ_f_sub_iterate_twistedSubdivision`).
Subdividing a representative until it is subordinate to the cover splits it into the image of a
chain of `P` and a chain in the subspace of `P'`; this gives surjectivity on homology, and the
same argument applied to a filling gives injectivity.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Theorem 2.20 and Proposition 2.21, and
  Section 3.H.
* S. Eilenberg and N. Steenrod, *Foundations of Algebraic Topology*, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Topology Simplicial

universe u v w

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

section Support

variable (P : TopPair.{v}) (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)

/-- An ambient twisted chain vanishes in relative chains exactly when it is supported in the
subspace. -/
lemma twistedChainComplexπ_f_apply_eq_zero_iff {k : ℕ} (z : L.twistedChainComplex.X k) :
    ((P.twistedChainComplexπ L).f k).hom z = 0 ↔
      z ∈ smallTwistedChains L (fun _ : Unit ↦ Set.range P.map) k := by
  have hsmall (σ : (TopCat.toSSet.obj P.fst) _⦋k⦌) :
      σ ∈ (P.fst.smallSingularSubcomplex fun _ : Unit ↦ Set.range P.map).obj _ ↔
        Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map := by
    rw [TopCat.mem_smallSingularSubcomplex_iff, exists_const,
      ← P.isEmbedding_map.isInducing.mem_range_toSSet_map_app_iff,
      P.mem_range_toSSet_map_app_iff_range_simplexMap_subset]
  rw [mem_smallTwistedChains_iff]
  constructor
  · intro hz σ hσ
    rw [← P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply L σ (mt (hsmall σ).2 hσ), hz,
      map_zero]
  · intro hz
    refine P.twistedChainComplex_ext_coeff L fun σ hσ ↦ ?_
    rw [P.twistedChainComplexCoeff_twistedChainComplexπ_f_apply, map_zero]
    exact hz σ (mt (hsmall σ).1 hσ)

/-- On a relative cycle, iterated barycentric subdivision of a representing ambient chain changes
its relative class by the boundary of the relative class of the subdivision prism. -/
lemma twistedChainComplexπ_f_sub_iterate_twistedSubdivision {n : ℕ}
    (c : L.twistedChainComplex.X n)
    (hc : (P.twistedChainComplex L).d n (n - 1) ((P.twistedChainComplexπ L).f n c) = 0)
    (N : ℕ) :
    (P.twistedChainComplexπ L).f n c -
        (P.twistedChainComplexπ L).f n ((End.of (twistedSubdivisionChainMap L) ^ N).asHom.f n c) =
      (P.twistedChainComplex L).d (n + 1) n ((P.twistedChainComplexπ L).f (n + 1)
        (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) c)) := by
  rw [HomologicalComplex.Hom.comm_apply, ← map_sub]
  cases n with
  | zero =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_zero_apply c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    rw [sub_eq_of_eq_add h]
  | succ k =>
    have h := ((twistedSubdivisionHomotopy L).idPow N).comm_succ_apply k c
    rw [HomologicalComplex.id_f, ModuleCat.id_apply] at h
    -- The boundary of `c` lies in the subspace, hence so does its prism.
    have hd : (P.twistedChainComplexπ L).f k (L.twistedChainComplex.d (k + 1) k c) = 0 := by
      rw [← HomologicalComplex.Hom.comm_apply]
      exact hc
    rw [twistedChainComplexπ_f_apply_eq_zero_iff] at hd
    have hD := (P.twistedChainComplexπ_f_apply_eq_zero_iff L _).2
      (idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains L _ hd N)
    rw [sub_eq_of_eq_add h, map_add, hD, zero_add]

end Support

section OpenCover

variable {P P' : TopPair.{v}} (f : P ⟶ P') (L : LocalCoefficientSystem.{u, v, max v w} R P'.fst)

/-- If the image of a chain under a map of pairs is supported in the target subspace, and the
source subspace is the full preimage of the target subspace, then the chain vanishes in relative
chains of the source pair. -/
private lemma twistedChainComplexπ_f_eq_zero_of_map_mem [Mono (Hom.fst f)]
    (hsnd : ∀ x, Hom.fst f x ∈ Set.range P'.map → x ∈ Set.range P.map) {n : ℕ}
    {z : ((pullback (Hom.fst f).hom).obj L).twistedChainComplex.X n}
    (hz : (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n z ∈
      smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) n) :
    (P.twistedChainComplexπ _).f n z = 0 :=
  (twistedChainComplexπ_f_apply_eq_zero_iff _ _ _).2 <|
    smallTwistedChains_mono _ _ (fun _ : Unit ↦ Set.range P.map) id (fun _ x hx ↦ hsnd x hx) n
      ((twistedChainComplexMap_f_mem_smallTwistedChains_iff _ L).1 hz)

/-- If each member of a family of subsets lies in the target subspace or in the image of an
embedding of ambient spaces, every chain subordinate to the family is the sum of a pushforward
and a chain supported in the target subspace. -/
private lemma smallTwistedChains_le_range_sup (hf : IsEmbedding (Hom.fst f)) {ι : Type*}
    (U : ι → Set P'.fst)
    (hUf : ∀ i, U i ⊆ Set.range P'.map ∨ U i ⊆ Set.range (Hom.fst f)) (n : ℕ) :
    smallTwistedChains L U n ≤
      LinearMap.range ((LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n).hom ⊔
        smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) n := by
  rw [smallTwistedChains_eq_iSup]
  refine iSup_le fun i ↦ ?_
  rcases hUf i with h | h
  · exact (smallTwistedChains_mono L _ _ id (fun _ ↦ h) n).trans le_sup_right
  · rw [range_twistedChainComplexMap_f _ L hf.isInducing]
    exact (smallTwistedChains_mono L _ _ id (fun _ ↦ h) n).trans le_sup_left

variable (hf : IsEmbedding (Hom.fst f))
  (hsnd : ∀ x, Hom.fst f x ∈ Set.range P'.map → x ∈ Set.range P.map)
  {ι : Type*} (U : ι → Set P'.fst) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
  (hUf : ∀ i, U i ⊆ Set.range P'.map ∨ U i ⊆ Set.range (Hom.fst f))

include hf hsnd hU hcov hUf in
/-- Surjectivity half of excision: every relative cycle of the target pair is homologous to the
image of a relative cycle of the source pair. -/
private lemma exists_sub_twistedChainComplexMap_f_eq_d {n : ℕ} (y : (P'.twistedChainComplex L).X n)
    (hy : (P'.twistedChainComplex L).d n (n - 1) y = 0) :
    ∃ x : (P.twistedChainComplex ((pullback (Hom.fst f).hom).obj L)).X n,
      (P.twistedChainComplex _).d n (n - 1) x = 0 ∧
        ∃ b : (P'.twistedChainComplex L).X (n + 1),
          (P'.twistedChainComplex L).d (n + 1) n b = y - (twistedChainComplexMap f L).f n x := by
  have : Mono (Hom.fst f) := (TopCat.mono_iff_injective _).2 hf.injective
  obtain ⟨c, rfl⟩ := P'.twistedChainComplexπ_f_surjective L y
  obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_small L U hU hcov c
  -- Subdivide `c` until it splits as a pushforward plus a chain in the target subspace.
  obtain ⟨_, ⟨a, rfl⟩, b, hb, hab⟩ :=
    Submodule.mem_sup.1 (smallTwistedChains_le_range_sup f L hf U hUf n (hN N le_rfl))
  have hb₀ := (P'.twistedChainComplexπ_f_apply_eq_zero_iff L b).2 hb
  have hdb : L.twistedChainComplex.d n (n - 1) b ∈
      smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) (n - 1) := by
    rw [← twistedChainComplexπ_f_apply_eq_zero_iff, ← HomologicalComplex.Hom.comm_apply, hb₀,
      map_zero]
  have hdc : L.twistedChainComplex.d n (n - 1) c ∈
      smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) (n - 1) := by
    rw [← twistedChainComplexπ_f_apply_eq_zero_iff, ← HomologicalComplex.Hom.comm_apply]
    exact hy
  refine ⟨(P.twistedChainComplexπ _).f n a, ?_,
    (P'.twistedChainComplexπ L).f (n + 1)
      (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1) c), ?_⟩
  · rw [HomologicalComplex.Hom.comm_apply]
    refine twistedChainComplexπ_f_eq_zero_of_map_mem f L hsnd ?_
    rw [← HomologicalComplex.Hom.comm_apply, eq_sub_of_add_eq hab, map_sub,
      HomologicalComplex.Hom.comm_apply]
    exact sub_mem (iterate_twistedSubdivision_mem_smallTwistedChains L _ hdc N) hdb
  · rw [← twistedChainComplexπ_f_sub_iterate_twistedSubdivision P' L c hy N,
      twistedChainComplexMap_f_twistedChainComplexπ_f_apply, ← hab, map_add, hb₀, add_zero]

include hf hsnd hU hcov hUf in
/-- Injectivity half of excision: a relative cycle of the source pair whose image bounds in the
target pair already bounds in the source pair. -/
private lemma exists_d_eq_of_twistedChainComplexMap_f_eq_d {n : ℕ}
    (x : (P.twistedChainComplex ((pullback (Hom.fst f).hom).obj L)).X n)
    (hx : (P.twistedChainComplex _).d n (n - 1) x = 0) (b : (P'.twistedChainComplex L).X (n + 1))
    (hb : (P'.twistedChainComplex L).d (n + 1) n b = (twistedChainComplexMap f L).f n x) :
    ∃ a, (P.twistedChainComplex _).d (n + 1) n a = x := by
  have : Mono (Hom.fst f) := (TopCat.mono_iff_injective _).2 hf.injective
  obtain ⟨a, rfl⟩ := P.twistedChainComplexπ_f_surjective _ x
  obtain ⟨w, rfl⟩ := P'.twistedChainComplexπ_f_surjective L b
  obtain ⟨N, hN⟩ := exists_iterate_twistedSubdivision_small L U hU hcov w
  -- Subdivide the filling `w` until it splits as a pushforward plus a chain in the subspace.
  obtain ⟨_, ⟨w₁, rfl⟩, w₂, hw₂, hw⟩ :=
    Submodule.mem_sup.1 (smallTwistedChains_le_range_sup f L hf U hUf (n + 1) (hN N le_rfl))
  have hdw₂ : L.twistedChainComplex.d (n + 1) n w₂ ∈
      smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) n := by
    rw [← twistedChainComplexπ_f_apply_eq_zero_iff, ← HomologicalComplex.Hom.comm_apply,
      (P'.twistedChainComplexπ_f_apply_eq_zero_iff L w₂).2 hw₂, map_zero]
  -- The boundary of `w` differs from the image of `a` by a chain in the target subspace.
  have he : L.twistedChainComplex.d (n + 1) n w -
      (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n a ∈
        smallTwistedChains L (fun _ : Unit ↦ Set.range P'.map) n := by
    rw [← twistedChainComplexπ_f_apply_eq_zero_iff, map_sub, ← HomologicalComplex.Hom.comm_apply,
      hb, twistedChainComplexMap_f_twistedChainComplexπ_f_apply, sub_self]
  have key : (P.twistedChainComplexπ _).f n
      (((pullback (Hom.fst f).hom).obj L).twistedChainComplex.d (n + 1) n w₁) =
        (P.twistedChainComplexπ _).f n
          ((End.of (twistedSubdivisionChainMap ((pullback (Hom.fst f).hom).obj L)) ^ N).asHom.f n
            a) := by
    rw [← sub_eq_zero, ← map_sub]
    refine twistedChainComplexπ_f_eq_zero_of_map_mem f L hsnd ?_
    have : (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n
        (((pullback (Hom.fst f).hom).obj L).twistedChainComplex.d (n + 1) n w₁ -
          (End.of (twistedSubdivisionChainMap ((pullback (Hom.fst f).hom).obj L)) ^ N).asHom.f n
            a) =
        (End.of (twistedSubdivisionChainMap L) ^ N).asHom.f n
            (L.twistedChainComplex.d (n + 1) n w -
              (LocalCoefficientSystem.twistedChainComplexMap (Hom.fst f) L).f n a) -
          L.twistedChainComplex.d (n + 1) n w₂ := by
      rw [map_sub, map_sub, ← HomologicalComplex.Hom.comm_apply,
        twistedChainComplexMap_f_iterate_twistedSubdivision, ← HomologicalComplex.Hom.comm_apply,
        ← hw, map_add]
      abel
    rw [this]
    exact sub_mem (iterate_twistedSubdivision_mem_smallTwistedChains L _ he N) hdw₂
  refine ⟨(P.twistedChainComplexπ _).f (n + 1)
      (((twistedSubdivisionHomotopy _).idPow N).hom n (n + 1) a) +
    (P.twistedChainComplexπ _).f (n + 1) w₁, ?_⟩
  rw [map_add, ← twistedChainComplexπ_f_sub_iterate_twistedSubdivision P _ a hx N,
    HomologicalComplex.Hom.comm_apply, key, sub_add_cancel]

include hf hsnd hU hcov hUf in
/-- **Excision for relative singular homology with local coefficients.** Let `f : P ⟶ P'` be a
map of topological pairs which is an embedding on ambient spaces and whose subspace is the full
preimage of the subspace of `P'`. If the ambient space of `P'` has an open cover each of whose
members lies in the subspace of `P'` or in the image of `f`, then `f` induces a
quasi-isomorphism of relative twisted chain complexes, for every local coefficient system on the
ambient space of `P'`. -/
theorem quasiIso_twistedChainComplexMap_of_open_cover : QuasiIso (twistedChainComplexMap f L) := by
  rw [quasiIso_iff]
  intro n
  rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (n := n) (p := n + 1) (m := n - 1) (by simp)
    (by cases n <;> simp [ChainComplex.next_nat_zero, ChainComplex.next_nat_succ])]
  exact ⟨fun y hy ↦ exists_sub_twistedChainComplexMap_f_eq_d f L hf hsnd U hU hcov hUf y hy,
    fun x hx b hb ↦
      exists_d_eq_of_twistedChainComplexMap_f_eq_d f L hf hsnd U hU hcov hUf x hx b hb⟩

include hf hsnd hU hcov hUf in
/-- **Excision for relative singular homology with local coefficients**, on homology: under the
hypotheses of `TopPair.quasiIso_twistedChainComplexMap_of_open_cover`, the map of pairs induces
isomorphisms on relative twisted homology in every degree. -/
theorem isIso_twistedHomologyMap_of_open_cover (n : ℕ) : IsIso (twistedHomologyMap f L n) := by
  have := quasiIso_twistedChainComplexMap_of_open_cover f L hf hsnd U hU hcov hUf
  infer_instance

end OpenCover

section Subsets

variable {X : TopCat.{v}} (A B : Set X) (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **Excision with local coefficients.** If the interiors of `A` and `B` cover `X`, the
inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces a quasi-isomorphism of relative twisted chain
complexes. -/
theorem quasiIso_twistedChainComplexMap_excisionMap (h : interior A ∪ interior B = Set.univ) :
    QuasiIso (twistedChainComplexMap (excisionMap A B) L) := by
  refine quasiIso_twistedChainComplexMap_of_open_cover (excisionMap A B) L
    (isEmbedding_fst_excisionMap A B) (mem_range_map_of_fst_excisionMap_mem A B)
    (fun b : Bool ↦ bif b then interior A else interior B)
    (fun b ↦ by cases b <;> exact isOpen_interior) ?_
    (interior_subset_range_or_subset_range_fst_excisionMap A B)
  rw [← Set.union_eq_iUnion]
  exact h

/-- **Excision with local coefficients.** If the interiors of `A` and `B` cover `X`, the
inclusion of pairs `(A, A ∩ B) ⟶ (X, B)` induces isomorphisms on relative twisted homology. -/
theorem isIso_twistedHomologyMap_excisionMap (h : interior A ∪ interior B = Set.univ) (n : ℕ) :
    IsIso (twistedHomologyMap (excisionMap A B) L n) := by
  have := quasiIso_twistedChainComplexMap_excisionMap A B L h
  infer_instance

/-- **Excision with local coefficients of a set with closure in the interior of the subspace.**
If `closure Z ⊆ interior B`, the inclusion of pairs `(X ∖ Z, B ∖ Z) ⟶ (X, B)` induces isomorphisms
on relative twisted homology. -/
theorem isIso_twistedHomologyMap_excisionMap_compl (Z : Set X) (h : closure Z ⊆ interior B)
    (n : ℕ) : IsIso (twistedHomologyMap (excisionMap Zᶜ B) L n) := by
  refine isIso_twistedHomologyMap_excisionMap Zᶜ B L ?_ n
  rw [interior_compl, Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ closure Z
  · exact Or.inr (h hx)
  · exact Or.inl hx

/-- **Excision with local coefficients onto a neighbourhood.** If `U` is open and contains the
closed set `K`, the inclusion of pairs `(U, U ∖ K) ⟶ (X, X ∖ K)` induces isomorphisms on relative
twisted homology. -/
theorem isIso_twistedHomologyMap_excisionMap_of_isClosed_subset {U K : Set X} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    IsIso (twistedHomologyMap (excisionMap U Kᶜ) L n) := by
  refine isIso_twistedHomologyMap_excisionMap U Kᶜ L ?_ n
  rw [hU.interior_eq, hK.isOpen_compl.interior_eq]
  exact Set.eq_univ_of_subset (Set.union_subset_union_left _ hKU) (Set.union_compl_self K)

end Subsets

end TopPair
