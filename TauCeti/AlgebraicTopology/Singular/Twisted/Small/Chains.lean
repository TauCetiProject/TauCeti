/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Homotopy
public import TauCeti.AlgebraicTopology.Singular.Twisted.Subdivision
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Chains
import TauCeti.Topology.Category.TopCat.Subspace

/-!
# Small singular chains with local coefficients

For a family `U` of subsets of `X`, `smallTwistedChains L U n` consists of the twisted
singular chains supported on simplices lying in a single member of `U`. It is the sum of
the coefficient fibres on the native `TopCat.smallSingularSubcomplex`. Its coefficient
characterization allows membership to be checked without choosing a presentation as a sum.

The boundary, barycentric subdivision and its prism operator preserve these submodules.
They therefore give a chain complex with an injective inclusion into twisted singular chains.
Nested support submodules give functorial inclusions between these small-chain complexes, and
a chain map into twisted chains with subordinate values factors through them
(`TauCeti.LocalCoefficientSystem.smallTwistedChainComplexLift`). In particular change of
coefficients and continuous maps compatible with the families act on small chains
(`smallTwistedChainComplexCoefficientMap`, `smallTwistedChainComplexMap`). For a subspace `A`, the
twisted chains of `A` with the restricted system are exactly the chains supported in `A`
(`TauCeti.LocalCoefficientSystem.subspaceTwistedChainComplexIso`); this identifies the terms
of the Mayer–Vietoris sequence with homology of subspaces. For an open cover, every finite
twisted chain becomes small after sufficiently many subdivisions. This supplies the smallness
input to the local-coefficient excision argument; no natural choice of subdivision depth or
chain retraction is asserted here.

The constructions use `twistedSingularChain`, `twistedSubdivisionChainMap` and the native
Lebesgue-number theorem for affine subdivision. Coefficients remain in their actual fibres
and are transported inside each simplex, with no triviality or freeness assumption.

## References

* A. Hatcher, *Algebraic Topology*, Proposition 2.21 and Section 3.H.
-/

public section

noncomputable section

open CategoryTheory Limits Convexity Simplicial AlgebraicTopology Finsupp

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X) {ι : Type*} (U : ι → Set X)

/-- Twisted chains supported on singular simplices lying in one member of `U`. -/
def smallTwistedChains (n : ℕ) : Submodule R (L.twistedChainComplex.X n) :=
  ⨆ σ : (X.smallSingularSubcomplex U : SSet) _⦋n⦌,
    LinearMap.range (ιTwistedChainComplex L n σ.val).hom

/-- The summand of a small simplex belongs to the small twisted chains. -/
lemma ιTwistedChainComplex_mem_smallTwistedChains {n : ℕ}
    {σ : (TopCat.toSSet.obj X) _⦋n⦌}
    (hσ : σ ∈ (X.smallSingularSubcomplex U).obj _) (x : L.obj (initialVertex σ)) :
    (ιTwistedChainComplex L n σ).hom x ∈ smallTwistedChains L U n :=
  Submodule.mem_iSup_of_mem ⟨σ, hσ⟩ ⟨x, rfl⟩

/-- A linear map carries small chains into a submodule if it does so on each small simplex. -/
lemma smallTwistedChains_le_comap {n : ℕ} {M : Type*} [AddCommGroup M] [Module R M]
    (f : L.twistedChainComplex.X n →ₗ[R] M) (N : Submodule R M)
    (hf : ∀ (σ : (TopCat.toSSet.obj X) _⦋n⦌),
      σ ∈ (X.smallSingularSubcomplex U).obj _ → ∀ x,
        f ((ιTwistedChainComplex L n σ).hom x) ∈ N) :
    smallTwistedChains L U n ≤ N.comap f := by
  refine iSup_le fun σ ↦ ?_
  rintro _ ⟨x, rfl⟩
  exact hf σ.val σ.property x

/-- A twisted chain is small exactly when its coefficient on every nonsmall simplex vanishes. -/
lemma mem_smallTwistedChains_iff {n : ℕ} (c : L.twistedChainComplex.X n) :
    c ∈ smallTwistedChains L U n ↔ ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌,
      σ ∉ (X.smallSingularSubcomplex U).obj _ → (twistedChainComplexCoeff L σ).hom c = 0 := by
  classical
  constructor
  · intro hc σ hσ
    exact smallTwistedChains_le_comap L U (twistedChainComplexCoeff L σ).hom ⊥
      (fun τ hτ x ↦ by
        have hne : τ ≠ σ := fun h ↦ hσ (h ▸ hτ)
        simp [twistedChainComplexCoeff_ιTwistedChainComplex_apply_of_ne L hne]) hc
  · intro hc
    rw [← finsum_ιTwistedChainComplex_twistedChainComplexCoeff L c]
    refine finsum_induction (fun x ↦ x ∈ smallTwistedChains L U n)
      (Submodule.zero_mem _) (fun _ _ ↦ Submodule.add_mem _) ?_
    intro σ
    by_cases hσ : σ ∈ (X.smallSingularSubcomplex U).obj _
    · exact ιTwistedChainComplex_mem_smallTwistedChains L U hσ _
    · simp [hc σ hσ]

/-- If every member of `U` lies in a member of `V` (so `U` refines `V`), then chains small
for `U` are small for `V`. -/
lemma smallTwistedChains_mono {κ : Type*} (V : κ → Set X) (r : ι → κ)
    (h : ∀ i, U i ⊆ V (r i)) (n : ℕ) :
    smallTwistedChains L U n ≤ smallTwistedChains L V n := by
  refine iSup_le fun σ ↦ ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U σ.val).1 σ.property
  exact ιTwistedChainComplex_mem_smallTwistedChains L V
    ((TopCat.mem_smallSingularSubcomplex_iff X V σ.val).2 ⟨r i, hi.trans (h i)⟩) x

/-- Chains subordinate to a family are sums of chains supported in individual members. -/
lemma smallTwistedChains_eq_iSup (n : ℕ) :
    smallTwistedChains L U n = ⨆ i, smallTwistedChains L (fun _ : Unit ↦ U i) n := by
  apply le_antisymm
  · simpa only [Submodule.comap_id] using
      (smallTwistedChains_le_comap L U LinearMap.id
        (⨆ i, smallTwistedChains L (fun _ : Unit ↦ U i) n) (by
          intro σ hσ x
          obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U σ).1 hσ
          exact Submodule.mem_iSup_of_mem i
            (ιTwistedChainComplex_mem_smallTwistedChains L _
              ((TopCat.mem_smallSingularSubcomplex_iff X _ σ).2 ⟨(), hi⟩) x)))
  · exact iSup_le fun i ↦ smallTwistedChains_mono L (fun _ : Unit ↦ U i) U
      (fun _ ↦ i) (fun _ ↦ Set.Subset.rfl) n

/-- Chains supported in the intersection are exactly the intersection of the two support
submodules. -/
lemma smallTwistedChains_inter (U V : Set X) (n : ℕ) :
    smallTwistedChains L (fun _ : Unit ↦ U ∩ V) n =
      smallTwistedChains L (fun _ : Unit ↦ U) n ⊓
        smallTwistedChains L (fun _ : Unit ↦ V) n := by
  ext c
  simp only [Submodule.mem_inf, mem_smallTwistedChains_iff,
    TopCat.mem_smallSingularSubcomplex_iff, Set.subset_inter_iff, exists_const]
  constructor
  · intro h
    exact ⟨fun σ hσ ↦ h σ (by tauto), fun σ hσ ↦ h σ (by tauto)⟩
  · rintro ⟨hU, hV⟩ σ hσ
    by_cases hu : Set.range (X.toSSetObjEquiv _ σ) ⊆ U
    · exact hV σ (by tauto)
    · exact hU σ hu

/-- Chains subordinate to a binary family are sums of chains supported in its members. -/
lemma smallTwistedChains_bool (U V : Set X) (n : ℕ) :
    smallTwistedChains L (Bool.rec U V) n =
      smallTwistedChains L (fun _ : Unit ↦ U) n ⊔
        smallTwistedChains L (fun _ : Unit ↦ V) n := by
  rw [smallTwistedChains_eq_iSup, iSup_bool_eq, sup_comm]

/-- The twisted singular boundary preserves chains subordinate to a family of subsets. -/
lemma d_mem_smallTwistedChains {n : ℕ} {c : L.twistedChainComplex.X (n + 1)}
    (hc : c ∈ smallTwistedChains L U (n + 1)) :
    (L.twistedChainComplex.d (n + 1) n).hom c ∈ smallTwistedChains L U n := by
  refine smallTwistedChains_le_comap L U (n := n + 1)
    (L.twistedChainComplex.d (n + 1) n).hom (smallTwistedChains L U n) ?_ hc
  intro σ hσ x
  rw [d_ιTwistedChainComplex_apply]
  exact Submodule.sum_mem _ fun i _ ↦ (smallTwistedChains L U n).toAddSubgroup.zsmul_mem
    (ιTwistedChainComplex_mem_smallTwistedChains L U
      ((X.smallSingularSubcomplex U).map (SimplexCategory.δ i).op hσ) _) _

/-- The complex of singular chains subordinate to `U`, with coefficients in `L`. -/
def smallTwistedChainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (smallTwistedChains L U n))
    (fun n ↦ ModuleCat.ofHom <|
      (L.twistedChainComplex.d (n + 1) n).hom.restrict
        (fun _ hc ↦ d_mem_smallTwistedChains L U hc))
    (fun n ↦ by
      ext c
      exact congrArg (fun f ↦ f.hom c.val) (L.twistedChainComplex.d_comp_d (n + 2) (n + 1) n))

/-- The degree-`n` object of the small twisted chain complex is the small-chain submodule. -/
lemma smallTwistedChainComplex_X (n : ℕ) :
    (smallTwistedChainComplex L U).X n = ModuleCat.of R (smallTwistedChains L U n) := (rfl)

/-- The differential on small twisted chains is the restriction of the singular boundary. -/
lemma smallTwistedChainComplex_d (n : ℕ) :
    (smallTwistedChainComplex L U).d (n + 1) n =
      eqToHom (smallTwistedChainComplex_X L U (n + 1)) ≫
      ModuleCat.ofHom ((L.twistedChainComplex.d (n + 1) n).hom.restrict
        (fun _ hc ↦ d_mem_smallTwistedChains L U hc)) ≫
      eqToHom (smallTwistedChainComplex_X L U n).symm := by
  simp only [smallTwistedChainComplex, ChainComplex.of_d]
  -- The degree-object equalities are reflexive, so both `eqToHom` transports are identities.
  rfl

/-- The boundary of a small chain has the same underlying chain as the singular boundary. -/
@[simp]
lemma coe_smallTwistedChainComplex_d_apply (n : ℕ)
    (c : (smallTwistedChainComplex L U).X (n + 1)) :
    ((eqToHom (smallTwistedChainComplex_X L U n)).hom
      (((smallTwistedChainComplex L U).d (n + 1) n).hom c) : L.twistedChainComplex.X n) =
      (L.twistedChainComplex.d (n + 1) n).hom
        ((eqToHom (smallTwistedChainComplex_X L U (n + 1))).hom c) := by
  rw [smallTwistedChainComplex_d]
  -- The reflexive degree transports are identities; the restricted map has the same value.
  rfl

/-- The inclusion of small twisted chains into all twisted singular chains. -/
def smallTwistedChainComplexι : smallTwistedChainComplex L U ⟶ L.twistedChainComplex :=
  ChainComplex.ofHom (fun n ↦ eqToHom (smallTwistedChainComplex_X L U n) ≫
    ModuleCat.ofHom (smallTwistedChains L U n).subtype)
    (fun n ↦ by
      dsimp only [smallTwistedChainComplex]
      rw [ChainComplex.of_d]
      ext c
      -- The degree transport is the identity, and restriction commutes with subtype inclusion.
      rfl)

/-- In each degree the small-chain inclusion is the submodule inclusion. -/
-- Keep this transport formula for rewriting: expanding it would hide the inclusion from the
-- simplification rule for its range.
lemma smallTwistedChainComplexι_f (n : ℕ) :
    (smallTwistedChainComplexι L U).f n = eqToHom (smallTwistedChainComplex_X L U n) ≫
      ModuleCat.ofHom (smallTwistedChains L U n).subtype := (rfl)

/-- The small-chain inclusion sends an element to its underlying twisted chain. -/
@[simp]
lemma smallTwistedChainComplexι_f_apply (n : ℕ)
    (c : (smallTwistedChainComplex L U).X n) :
    ((smallTwistedChainComplexι L U).f n).hom c =
      ((eqToHom (smallTwistedChainComplex_X L U n)).hom c : L.twistedChainComplex.X n) := (rfl)

/-- The image of the inclusion is exactly the submodule of small twisted chains. -/
@[simp]
lemma range_smallTwistedChainComplexι_f (n : ℕ) :
    LinearMap.range ((smallTwistedChainComplexι L U).f n).hom = smallTwistedChains L U n := by
  rw [smallTwistedChainComplexι_f]
  ext c
  constructor
  · rintro ⟨x, rfl⟩
    exact ((eqToHom (smallTwistedChainComplex_X L U n)).hom x).property
  · intro hc
    refine ⟨(eqToHom (smallTwistedChainComplex_X L U n).symm).hom ⟨c, hc⟩, ?_⟩
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (eqToIso (smallTwistedChainComplex_X L U n)).inv_hom_id ⟨c, hc⟩)

instance (n : ℕ) : Mono ((smallTwistedChainComplexι L U).f n) := by
  have : Mono (ModuleCat.ofHom (smallTwistedChains L U n).subtype) :=
    (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  rw [smallTwistedChainComplexι_f]
  infer_instance

instance : Mono (smallTwistedChainComplexι L U) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ ↦ inferInstance)

/-- A pushed-forward affine chain is small if every simplex in its support is small. -/
lemma twistedSingularChain_mem_smallTwistedChains {m k : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋m⦌) (z : SimplexCategory.toTop.{v}.obj ⦋m⦌)
    (c : (Fin (k + 1) → StdSimplex ℝ (Fin (m + 1))) →₀ ℤ)
    (hc : ∀ a ∈ c.support, ∃ i,
      Set.range ((X.toSSetObjEquiv _ σ).comp (StdSimplex.continuousAffineMapMk a)) ⊆ U i)
    (x : L.obj ⟨TopCat.simplexMap σ z⟩) :
    (twistedSingularChain L σ z k c).hom x ∈ smallTwistedChains L U k := by
  classical
  rw [← c.sum_single, Finsupp.sum, twistedSingularChain_sum]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, twistedSingularChain_single,
    ModuleCat.hom_zsmul, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro a ha
  apply (smallTwistedChains L U k).toAddSubgroup.zsmul_mem
  rw [twistedAffineSimplex_def]
  -- The simplex-point wrappers must unfold for the composite's intermediate fibre to match.
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  apply ιTwistedChainComplex_mem_smallTwistedChains
  rw [TopCat.mem_smallSingularSubcomplex_iff, Equiv.apply_symm_apply]
  exact hc a ha

/-- Subdivision preserves small twisted chains, without openness assumptions on the family. -/
lemma twistedSubdivisionX_mem_smallTwistedChains {n : ℕ} {c : L.twistedChainComplex.X n}
    (hc : c ∈ smallTwistedChains L U n) :
    (twistedSubdivisionX L n).hom c ∈ smallTwistedChains L U n := by
  refine smallTwistedChains_le_comap L U (n := n)
    (twistedSubdivisionX L n).hom (smallTwistedChains L U n) ?_ hc
  intro σ hσ x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    ιTwistedChainComplex_twistedSubdivisionX_eq]
  apply twistedSingularChain_mem_smallTwistedChains
  exact fun a _ ↦
    TopCat.exists_range_comp_affineMapMk_subset_of_mem_smallSingularSubcomplex X U hσ a

/-- Every iterate of subdivision preserves small twisted chains. -/
lemma iterate_twistedSubdivision_mem_smallTwistedChains {n : ℕ}
    {c : L.twistedChainComplex.X n} (hc : c ∈ smallTwistedChains L U n) (N : ℕ) :
    (((End.of (twistedSubdivisionChainMap L)) ^ N).asHom.f n).hom c ∈
      smallTwistedChains L U n := by
  induction N with
  | zero => simpa using hc
  | succ N hN =>
    rw [HomologicalComplex.pow_f_succ, ModuleCat.hom_comp, LinearMap.comp_apply,
      twistedSubdivisionChainMap_f]
    exact twistedSubdivisionX_mem_smallTwistedChains L U hN

/-- The subdivision prism preserves small twisted chains. -/
lemma twistedPrismX_mem_smallTwistedChains {n : ℕ} {c : L.twistedChainComplex.X n}
    (hc : c ∈ smallTwistedChains L U n) :
    (twistedPrismX L n).hom c ∈ smallTwistedChains L U (n + 1) := by
  refine smallTwistedChains_le_comap L U (n := n)
    (twistedPrismX L n).hom (smallTwistedChains L U (n + 1)) ?_ hc
  intro σ hσ x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ιTwistedChainComplex_twistedPrismX]
  apply twistedSingularChain_mem_smallTwistedChains
  exact fun a _ ↦
    TopCat.exists_range_comp_affineMapMk_subset_of_mem_smallSingularSubcomplex X U hσ a

/-- The homotopy from the identity to an iterated subdivision preserves small twisted chains. -/
lemma idPow_twistedSubdivisionHomotopy_hom_mem_smallTwistedChains {n : ℕ}
    {c : L.twistedChainComplex.X n} (hc : c ∈ smallTwistedChains L U n) (N : ℕ) :
    (((twistedSubdivisionHomotopy L).idPow N).hom n (n + 1)).hom c ∈
      smallTwistedChains L U (n + 1) := by
  rw [Homotopy.idPow_hom]
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, twistedSubdivisionHomotopy_hom]
  exact Submodule.sum_mem _ fun k _ ↦
    twistedPrismX_mem_smallTwistedChains L U
      (iterate_twistedSubdivision_mem_smallTwistedChains L U hc k)

/-- For an open cover, a uniform number of subdivisions makes the whole coefficient fibre
on a given singular simplex small. -/
theorem exists_iterate_twistedSubdivision_small_simplex (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) {n : ℕ} (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ∃ N, ∀ k ≥ N, ∀ x : L.obj (initialVertex σ),
      (((End.of (twistedSubdivisionChainMap L)) ^ k).asHom.f n).hom
        ((ιTwistedChainComplex L n σ).hom x) ∈ smallTwistedChains L U n := by
  obtain ⟨N, hN⟩ := ContinuousMap.exists_forall_mem_support_subdivision_iterate_range_subset
    (X.toSSetObjEquiv _ σ) hU hcov n
  refine ⟨N, fun k hk x ↦ ?_⟩
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← twistedSingularChain_simplex,
    ← twistedSingularChain_subdivision_iterate]
  exact twistedSingularChain_mem_smallTwistedChains L U _ _ _ (hN k hk _) x

/-- Every twisted chain becomes subordinate to an open cover after sufficiently many
barycentric subdivisions, and remains subordinate under further subdivision. -/
theorem exists_iterate_twistedSubdivision_small (hU : ∀ i, IsOpen (U i))
    (hcov : ⋃ i, U i = Set.univ) {n : ℕ} (c : L.twistedChainComplex.X n) :
    ∃ N, ∀ k ≥ N,
      (((End.of (twistedSubdivisionChainMap L)) ^ k).asHom.f n).hom c ∈
        smallTwistedChains L U n := by
  classical
  choose N hN using exists_iterate_twistedSubdivision_small_simplex L U hU hcov (n := n)
  let s := (finite_support_twistedChainComplexCoeff L c).toFinset
  have hs : ∀ σ, (twistedChainComplexCoeff L σ).hom c ≠ 0 → σ ∈ s := by
    intro σ hσ
    exact (Set.Finite.mem_toFinset _).2 hσ
  have hc : c = ∑ σ ∈ s,
      (ιTwistedChainComplex L n σ).hom ((twistedChainComplexCoeff L σ).hom c) := by
    exact (finsum_ιTwistedChainComplex_twistedChainComplexCoeff L c).symm.trans
      (finsum_eq_sum_of_support_subset _ fun σ hσ ↦ hs σ (fun h ↦ hσ (by simp [h])))
  refine ⟨s.sup N, fun k hk ↦ ?_⟩
  rw [hc, map_sum]
  exact Submodule.sum_mem _ fun σ hσ ↦
    hN σ k ((Finset.le_sup (f := N) hσ).trans hk) _

section Naturality

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R X}

/-- Change of local coefficients preserves subordination to a family of subsets. -/
lemma twistedChainComplexCoefficientMap_mem_smallTwistedChains (η : L ⟶ K)
    {n : ℕ} {c : L.twistedChainComplex.X n} (hc : c ∈ smallTwistedChains L U n) :
    ((twistedChainComplexCoefficientMap η).f n).hom c ∈ smallTwistedChains K U n := by
  refine smallTwistedChains_le_comap L U (n := n)
    ((twistedChainComplexCoefficientMap η).f n).hom (smallTwistedChains K U n) ?_ hc
  intro σ hσ x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    ιTwistedChainComplex_twistedChainComplexCoefficientMap_f]
  exact ιTwistedChainComplex_mem_smallTwistedChains K U hσ _

variable {Y : TopCat.{v}} {κ : Type*} (V : κ → Set Y)
  (f : X ⟶ Y) (M : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- A continuous map carrying each member of one family into a member of another preserves
small twisted chains, with the local system pulled back along that map. -/
lemma twistedChainComplexMap_mem_smallTwistedChains (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) {n : ℕ}
    {c : ((pullback f.hom).obj M).twistedChainComplex.X n}
    (hc : c ∈ smallTwistedChains ((pullback f.hom).obj M) U n) :
    ((twistedChainComplexMap f M).f n).hom c ∈ smallTwistedChains M V n := by
  refine smallTwistedChains_le_comap _ U (n := n)
    ((twistedChainComplexMap f M).f n).hom (smallTwistedChains M V n) ?_ hc
  intro σ hσ x
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ιTwistedChainComplex_twistedChainComplexMap_f]
  apply ιTwistedChainComplex_mem_smallTwistedChains
  obtain ⟨i, hi⟩ := (TopCat.mem_smallSingularSubcomplex_iff X U σ).1 hσ
  rw [TopCat.mem_smallSingularSubcomplex_iff, TopCat.toSSetObjEquiv_toSSet_map_app,
    ContinuousMap.coe_comp, Set.range_comp]
  exact ⟨r i, ((hf i).mono_left hi).image_subset⟩

/-- Along an injective map `f`, a chain is supported in `f ⁻¹' S` exactly when its pushforward is
supported in `S`. -/
lemma twistedChainComplexMap_f_mem_smallTwistedChains_iff [Mono f] {n : ℕ} {S : Set Y}
    {c : ((pullback f.hom).obj M).twistedChainComplex.X n} :
    ((twistedChainComplexMap f M).f n).hom c ∈ smallTwistedChains M (fun _ : Unit ↦ S) n ↔
      c ∈ smallTwistedChains ((pullback f.hom).obj M) (fun _ : Unit ↦ f ⁻¹' S) n := by
  refine ⟨fun hc ↦ ?_, twistedChainComplexMap_mem_smallTwistedChains _ _ f M id
    (fun _ ↦ Set.mapsTo_preimage f S)⟩
  rw [mem_smallTwistedChains_iff] at hc ⊢
  intro τ hτ
  rw [← twistedChainComplexCoeff_twistedChainComplexMap_f_apply]
  refine hc _ fun h ↦ hτ ?_
  simp only [TopCat.mem_smallSingularSubcomplex_iff, exists_const,
    TopCat.toSSetObjEquiv_toSSet_map_app, ContinuousMap.coe_comp, Set.range_comp] at h ⊢
  exact Set.image_subset_iff.1 h

/-- Along an inducing map, the pushforwards of twisted chains are exactly the chains supported in
its range. -/
lemma range_twistedChainComplexMap_f (hf : Topology.IsInducing f) (n : ℕ) :
    LinearMap.range ((twistedChainComplexMap f M).f n).hom =
      smallTwistedChains M (fun _ : Unit ↦ Set.range f) n := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨c, rfl⟩
    refine twistedChainComplexMap_mem_smallTwistedChains (fun _ : Unit ↦ Set.univ) _ f M id
      (fun _ x _ ↦ Set.mem_range_self x) ?_
    rw [mem_smallTwistedChains_iff]
    intro σ hσ
    exact (hσ ((TopCat.mem_smallSingularSubcomplex_iff _ _ σ).2 ⟨(), Set.subset_univ _⟩)).elim
  · simpa only [Submodule.comap_id] using smallTwistedChains_le_comap M _ LinearMap.id
      (LinearMap.range ((twistedChainComplexMap f M).f n).hom) fun σ hσ x ↦ by
        obtain ⟨_, hσ⟩ := (TopCat.mem_smallSingularSubcomplex_iff Y _ σ).1 hσ
        obtain ⟨τ, rfl⟩ := (hf.mem_range_toSSet_map_app_iff _ σ).2 hσ
        exact ⟨(ιTwistedChainComplex _ n τ).hom x, twistedChainComplexMap_f_ι_apply f M n τ x⟩

end Naturality

section Inclusion

variable {L U} {κ : Type*} {V : κ → Set X}

/-- The inclusion between small-chain complexes when the support submodules are nested.
This includes refinement maps without requiring a choice of a refining index. -/
def smallTwistedChainComplexInclusion
    (h : ∀ n, smallTwistedChains L U n ≤ smallTwistedChains L V n) :
    smallTwistedChainComplex L U ⟶ smallTwistedChainComplex L V where
  f n := eqToHom (smallTwistedChainComplex_X L U n) ≫
    ModuleCat.ofHom (Submodule.inclusion (h n)) ≫
      eqToHom (smallTwistedChainComplex_X L V n).symm
  comm' i j hij := by
    apply (cancel_mono ((smallTwistedChainComplexι L V).f j)).1
    subst hij
    rw [smallTwistedChainComplex_d, smallTwistedChainComplex_d,
      smallTwistedChainComplexι_f]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    ext c
    -- Restriction and submodule inclusion both evaluate in the ambient chain module.
    rfl

/-- A support inclusion preserves the underlying twisted chain. -/
@[simp]
lemma coe_smallTwistedChainComplexInclusion_f_apply
    (h : ∀ n, smallTwistedChains L U n ≤ smallTwistedChains L V n) (n : ℕ)
    (c : (smallTwistedChainComplex L U).X n) :
    ((eqToHom (smallTwistedChainComplex_X L V n)).hom
      (((smallTwistedChainComplexInclusion h).f n).hom c) : L.twistedChainComplex.X n) =
      ((eqToHom (smallTwistedChainComplex_X L U n)).hom c : L.twistedChainComplex.X n) := (rfl)

/-- After inclusion into ambient chains, a support inclusion is the original inclusion. -/
@[reassoc (attr := simp)]
lemma smallTwistedChainComplexInclusion_ι
    (h : ∀ n, smallTwistedChains L U n ≤ smallTwistedChains L V n) :
    smallTwistedChainComplexInclusion h ≫ smallTwistedChainComplexι L V =
      smallTwistedChainComplexι L U := by
  ext n : 1
  dsimp only [smallTwistedChainComplexInclusion, HomologicalComplex.comp_f]
  rw [smallTwistedChainComplexι_f, smallTwistedChainComplexι_f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← ModuleCat.ofHom_comp, Submodule.subtype_comp_inclusion]

/-- Support inclusions compose as inclusions. -/
@[reassoc (attr := simp)]
lemma smallTwistedChainComplexInclusion_comp {μ : Type*} {W : μ → Set X}
    (h : ∀ n, smallTwistedChains L U n ≤ smallTwistedChains L V n)
    (k : ∀ n, smallTwistedChains L V n ≤ smallTwistedChains L W n) :
    smallTwistedChainComplexInclusion h ≫ smallTwistedChainComplexInclusion k =
      smallTwistedChainComplexInclusion (fun n ↦ (h n).trans (k n)) := by
  apply (cancel_mono (smallTwistedChainComplexι L W)).1
  simp

/-- The support inclusion for a reflexive containment is the identity. -/
@[simp]
lemma smallTwistedChainComplexInclusion_refl :
    smallTwistedChainComplexInclusion (L := L) (U := U) (fun _ ↦ le_rfl) = 𝟙 _ := by
  apply (cancel_mono (smallTwistedChainComplexι L U)).1
  simp

end Inclusion

section Lift

variable {L U} {A : ChainComplex (ModuleCat.{max v w} R) ℕ}

/-- A chain map into the twisted singular chains of `X` whose values are subordinate to `U`
factors through the small twisted chains. -/
def smallTwistedChainComplexLift (g : A ⟶ L.twistedChainComplex)
    (hg : ∀ n, LinearMap.range (g.f n).hom ≤ smallTwistedChains L U n) :
    A ⟶ smallTwistedChainComplex L U where
  f n := ModuleCat.ofHom
      ((g.f n).hom.codRestrict _ fun c ↦ hg n (LinearMap.mem_range_self _ c)) ≫
    eqToHom (smallTwistedChainComplex_X L U n).symm
  comm' i j _ := by
    apply (cancel_mono ((smallTwistedChainComplexι L U).f j)).1
    rw [Category.assoc, Category.assoc, ← (smallTwistedChainComplexι L U).comm,
      smallTwistedChainComplexι_f, smallTwistedChainComplexι_f]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← ModuleCat.ofHom_comp, LinearMap.subtype_comp_codRestrict,
      ModuleCat.ofHom_hom]
    exact g.comm i j

/-- The factorization through small chains followed by their inclusion is the original map. -/
@[reassoc (attr := simp)]
lemma smallTwistedChainComplexLift_ι (g : A ⟶ L.twistedChainComplex)
    (hg : ∀ n, LinearMap.range (g.f n).hom ≤ smallTwistedChains L U n) :
    smallTwistedChainComplexLift g hg ≫ smallTwistedChainComplexι L U = g := by
  ext n : 1
  rw [HomologicalComplex.comp_f, smallTwistedChainComplexι_f]
  simp [smallTwistedChainComplexLift, ← ModuleCat.ofHom_comp]

end Lift

section LiftNaturality

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K)

/-- Change of local coefficients on twisted chains subordinate to a family of subsets. -/
def smallTwistedChainComplexCoefficientMap :
    smallTwistedChainComplex L U ⟶ smallTwistedChainComplex K U :=
  smallTwistedChainComplexLift
    (smallTwistedChainComplexι L U ≫ twistedChainComplexCoefficientMap η) fun n ↦ by
      rintro _ ⟨c, rfl⟩
      exact twistedChainComplexCoefficientMap_mem_smallTwistedChains U η
        (by rw [← range_smallTwistedChainComplexι_f]; exact LinearMap.mem_range_self _ c)

/-- Change of coefficients on small chains is compatible with their inclusions into twisted
chains. -/
@[reassoc (attr := simp)]
lemma smallTwistedChainComplexCoefficientMap_ι :
    smallTwistedChainComplexCoefficientMap U η ≫ smallTwistedChainComplexι K U =
      smallTwistedChainComplexι L U ≫ twistedChainComplexCoefficientMap η :=
  smallTwistedChainComplexLift_ι _ _

variable {Y : TopCat.{v}} {κ : Type*} (V : κ → Set Y)
  (f : X ⟶ Y) (M : LocalCoefficientSystem.{u, v, max v w} R Y)

/-- Pushing twisted chains forward along a continuous map carrying each member of one family of
subsets into a member of another, on the chains subordinate to these families. -/
def smallTwistedChainComplexMap (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    smallTwistedChainComplex ((pullback f.hom).obj M) U ⟶ smallTwistedChainComplex M V :=
  smallTwistedChainComplexLift
    (smallTwistedChainComplexι ((pullback f.hom).obj M) U ≫ twistedChainComplexMap f M)
    fun n ↦ by
      rintro _ ⟨c, rfl⟩
      exact twistedChainComplexMap_mem_smallTwistedChains U V f M r hf
        (by rw [← range_smallTwistedChainComplexι_f]; exact LinearMap.mem_range_self _ c)

/-- Pushing small chains forward is compatible with their inclusions into twisted chains. -/
@[reassoc (attr := simp)]
lemma smallTwistedChainComplexMap_ι (r : ι → κ) (hf : ∀ i, Set.MapsTo f (U i) (V (r i))) :
    smallTwistedChainComplexMap U V f M r hf ≫ smallTwistedChainComplexι M V =
      smallTwistedChainComplexι ((pullback f.hom).obj M) U ≫ twistedChainComplexMap f M :=
  smallTwistedChainComplexLift_ι _ _

end LiftNaturality

section Subspace

variable (A : Set X)

/-- The twisted chains of a subspace `A`, with `L` restricted to `A`, push forward onto exactly the
twisted chains of `X` supported in `A`. -/
lemma range_twistedChainComplexMap_subtypeVal_f (n : ℕ) :
    LinearMap.range
        ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f n).hom =
      smallTwistedChains L (fun _ : Unit ↦ A) n := by
  have : Set.range (TopCat.ofHom (ContinuousMap.subtypeVal A)) = A := by ext; simp
  rw [range_twistedChainComplexMap_f _ L Topology.IsInducing.subtypeVal n, this]

/-- The twisted chain complex of a subspace `A`, with `L` restricted to `A`, is isomorphic to the
complex of twisted chains of `X` supported in `A`. -/
def subspaceTwistedChainComplexIso :
    ((pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L).twistedChainComplex ≅
      smallTwistedChainComplex L (fun _ : Unit ↦ A) :=
  have hg n := (range_twistedChainComplexMap_subtypeVal_f L A n).le
  -- The lift is injective since the map of subspace chains is, and surjective since the small
  -- chains are exactly its range.
  have (n : ℕ) : IsIso ((smallTwistedChainComplexLift _ hg).f n) := by
    have hι := (ModuleCat.mono_iff_injective
      ((smallTwistedChainComplexι L (fun _ : Unit ↦ A)).f n)).1 inferInstance
    have hcomp (a) : ((smallTwistedChainComplexι L (fun _ : Unit ↦ A)).f n).hom
        (((smallTwistedChainComplexLift _ hg).f n).hom a) =
          ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f n).hom a := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, smallTwistedChainComplexLift_ι]
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a b hab ↦ ?_, fun c ↦ ?_⟩
    · exact (ModuleCat.mono_iff_injective _).1 inferInstance
        (by rw [← hcomp, ← hcomp, hab])
    · obtain ⟨a, ha⟩ : ((smallTwistedChainComplexι L (fun _ : Unit ↦ A)).f n).hom c ∈
          LinearMap.range
            ((twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L).f n).hom := by
        rw [range_twistedChainComplexMap_subtypeVal_f, ← range_smallTwistedChainComplexι_f]
        exact LinearMap.mem_range_self _ c
      exact ⟨a, hι (by rw [hcomp, ha])⟩
  have := HomologicalComplex.Hom.isIso_of_components (smallTwistedChainComplexLift _ hg)
  asIso (smallTwistedChainComplexLift _ hg)

/-- The subspace comparison followed by the inclusion of small chains is the map induced by the
inclusion of `A` into `X`. -/
@[reassoc (attr := simp)]
lemma subspaceTwistedChainComplexIso_hom_ι :
    (subspaceTwistedChainComplexIso L A).hom ≫ smallTwistedChainComplexι L (fun _ : Unit ↦ A) =
      twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L :=
  smallTwistedChainComplexLift_ι _ fun n ↦ (range_twistedChainComplexMap_subtypeVal_f L A n).le

/-- The inverse subspace comparison followed by the map induced by the inclusion of `A` is the
inclusion of small chains. -/
@[reassoc (attr := simp)]
lemma subspaceTwistedChainComplexIso_inv_twistedChainComplexMap :
    (subspaceTwistedChainComplexIso L A).inv ≫
        twistedChainComplexMap (TopCat.ofHom (ContinuousMap.subtypeVal A)) L =
      smallTwistedChainComplexι L (fun _ : Unit ↦ A) := by
  rw [Iso.inv_comp_eq, subspaceTwistedChainComplexIso_hom_ι]

end Subspace

end TauCeti.LocalCoefficientSystem
