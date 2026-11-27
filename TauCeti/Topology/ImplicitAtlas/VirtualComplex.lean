/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Topology.ImplicitAtlas.PartialComplex

/-!
# The virtual cochain complex of an implicit atlas

Let `𝒜` be an implicit atlas of virtual dimension `d` on `X`, and let `B` be a finite set of
indices, with `m_B = dim E_B`. The partial virtual complexes `R_IJ(K)`, for `I ⊆ J ⊆ B` and compact
`K ⊆ X`, together with the interval arrows weighted by `|Γ_(J ∖ J')|⁻¹`, form an interval diagram on
the subsets of `B` (`TauCeti.ImplicitAtlas.partialVirtualDiagram`). Pardon's **virtual cochain
complex** `C_vir(K; B)` is its flag total:

`C_vir(K; B)^q = ⨁ₚ ⨁_{I₀ ⊊ ⋯ ⊊ Iₚ ⊆ B} R_(I₀, Iₚ)(K)^(q + p)`,

with differential the alternating sum of the interval arrows deleting one `Iᵢ` plus `(-1)ᵖ` times
the internal differential (`TauCeti.IntervalDiagram.total`). A flag of length `p` lowers the
cochain degree by `p`. The cohomology of `C_vir(X; B)` is, for a locally orientable atlas, the Čech
cohomology of `X` with coefficients in its virtual orientation sheaf, and the virtual fundamental
class of `𝒜` is read off from it in degree `d`.

Every partial complex for the set `B` is concentrated in cochain degrees `q ≤ d + m_B`: it is a
complex of chains in degrees `d + m_B - q`, extended to `ℤ` along
`ComplexShape.embeddingUpIntLE (d + m_B)`. The total is formed in these chain degrees and extended
back:

* `TauCeti.ImplicitAtlas.partialVirtualChainDiagram`: for each compact `K`, the interval diagram
  of the `R_IJ(K)` restricted to chain degrees, as a presheaf on the compact sets;
* `TauCeti.ImplicitAtlas.virtualComplex`: the K-presheaf of cochain complexes
  `K ↦ C_vir(K; B)`, the extension to `ℤ` of the totals of these diagrams, with the restrictions
  induced by those of the partial complexes.

The one-vertex flag of the top interval `(B, B)` gives the inclusion
`R_BB ⟶ C_vir(−; B)` of K-presheaves (`TauCeti.ImplicitAtlas.virtualComplexTopι`). This file also
proves the first checks of the construction.

* **The empty set of indices.** For `B = ∅` the only interval is `(∅, ∅)`, so the inclusion
  `R_∅∅(K) ⟶ C_vir(K; ∅)` is a quasi-isomorphism
  (`TauCeti.ImplicitAtlas.quasiIso_virtualComplexTopι_app_empty`), by Pardon's Lemma A.7.3
  (`TauCeti.IntervalDiagram.quasiIso_topι`). Here the deformation space `D_(∅,∅,∅)` is the regular
  locus `X_∅^reg` (`TauCeti.ImplicitAtlas.mem_deformationSpace_empty_iff`), so `R_∅∅(K)` is the
  complex of relative chains `C_(d - •)(X_∅^reg, X_∅^reg ∖ K)`; for the manifold atlas of a compact
  `d`-manifold these are the relative chains `C_(d - •)(X, X ∖ K)`.
* **The empty compact set.** `C_vir(∅; B)` is zero
  (`TauCeti.ImplicitAtlas.isZero_virtualComplex_obj_of_coe_eq_empty`), because every partial
  complex of `∅` is (`TauCeti.ImplicitAtlas.isZero_partialVirtualComplex_obj_of_coe_eq_empty`).
  In particular every virtual complex of an atlas on the empty space is zero
  (`TauCeti.ImplicitAtlas.isZero_virtualComplex_obj_of_isEmpty`).

The atlases here have no boundary, so the relative and absolute virtual complexes of Pardon
coincide.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.2.6 (the virtual
  cochain complex), Definition A.7.2 (the total of an interval diagram) and Lemma A.7.3.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Module

universe u

namespace TauCeti.ImplicitAtlas

variable {A : Type u} [DecidableEq A] {Γ : A → Type u} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type u} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type u} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type u} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)
  (k : Type u) [CommRing k] (hΓ : ∀ α, IsUnit (Nat.card (Γ α) : k))

/-! ### The virtual cochain complex -/

-- The body is exposed so that the values and maps are definitionally the restricted partial
-- complexes and interval arrows: the statements of `partialVirtualChainDiagram_obj_obj` and its
-- companions typecheck only then.
/-- **The partial virtual complexes in chain degrees.** For a finite set `B` of indices and a
compact set `K`, the interval diagram on the subsets of `B` whose value on `I ⊆ J` is the partial
virtual complex `R_IJ(K)` restricted along `ComplexShape.embeddingUpIntLE (d + m_B)`, that is the
complex of invariant relative chains `C_•(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)` in its
homological grading, with the weighted interval arrows. It is a presheaf on the compact sets of
`X`, through the restrictions of the partial complexes. -/
@[expose]
def partialVirtualChainDiagram (B : Finset A) :
    (Compacts (TopCat.of X))ᵒᵖ ⥤ IntervalDiagram (Set.Iic B) (ChainComplex (ModuleCat.{u} k) ℕ) :=
  (𝒜.partialVirtualDiagram k hΓ B ⋙ (Functor.whiskeringRight _ _ _).obj
    ((ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))).restrictionFunctor
      (ModuleCat.{u} k))).flip

/-- The value of the diagram of `K` on an interval `I ⊆ J` is the partial virtual complex `R_IJ(K)`
in chain degrees. -/
@[simp]
theorem partialVirtualChainDiagram_obj_obj (B : Finset A) (K : (Compacts (TopCat.of X))ᵒᵖ)
    (x : (NonemptyInterval (Set.Iic B))ᵒᵖ) :
    ((𝒜.partialVirtualChainDiagram k hΓ B).obj K).obj x =
      ((𝒜.partialVirtualComplex k x.unop.fst.val x.unop.snd.property).obj K).restriction
        (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-- The arrows of the diagram of `K` are the weighted interval arrows in chain degrees. -/
theorem partialVirtualChainDiagram_obj_map (B : Finset A) (K : (Compacts (TopCat.of X))ᵒᵖ)
    {x y : (NonemptyInterval (Set.Iic B))ᵒᵖ} (f : x ⟶ y) :
    ((𝒜.partialVirtualChainDiagram k hΓ B).obj K).map f =
      HomologicalComplex.restrictionMap (((𝒜.partialVirtualDiagram k hΓ B).map f).app K)
        (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-- For `K ⊆ L`, the map of diagrams from `L` to `K` is the restriction of the partial virtual
complexes on every interval. -/
theorem partialVirtualChainDiagram_map_app (B : Finset A) {K L : (Compacts (TopCat.of X))ᵒᵖ}
    (h : K ⟶ L) (x : (NonemptyInterval (Set.Iic B))ᵒᵖ) :
    ((𝒜.partialVirtualChainDiagram k hΓ B).map h).app x =
      HomologicalComplex.restrictionMap
        ((𝒜.partialVirtualComplex k x.unop.fst.val x.unop.snd.property).map h)
        (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

-- The body is exposed so that the values and restrictions are definitionally the extended totals
-- (`virtualComplex_obj`, `virtualComplex_map`).
/-- **The virtual cochain complex** `C_vir(−; B)` of an implicit atlas of virtual dimension `d`,
for a finite set `B` of indices (Pardon, Definition 4.2.6): the K-presheaf of cochain complexes on
`X` whose value on a compact set `K` is the flag total of the interval diagram of partial virtual
complexes `R_IJ(K)`, `I ⊆ J ⊆ B`, with the weighted interval arrows. The total is formed in the
chain degrees `d + m_B - q` of the partial complexes and extended to the cochain degrees `q ∈ ℤ`,
so that a flag of length `p` lowers the cochain degree by `p`. -/
@[expose]
def virtualComplex (B : Finset A) :
    TopCat.KPresheaf (CochainComplex (ModuleCat.{u} k) ℤ) (TopCat.of X) :=
  𝒜.partialVirtualChainDiagram k hΓ B ⋙ IntervalDiagram.totalFunctor _ _ ⋙
    (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))).extendFunctor _

/-- The virtual cochain complex of a compact set `K` is the total of the diagram of partial
virtual complexes of `K` in chain degrees, extended to cochain degrees. -/
@[simp]
theorem virtualComplex_obj (B : Finset A) (K : (Compacts (TopCat.of X))ᵒᵖ) :
    (𝒜.virtualComplex k hΓ B).obj K =
      ((𝒜.partialVirtualChainDiagram k hΓ B).obj K).total.extend
        (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-- The restrictions of the virtual cochain complex are induced on the totals by the restrictions
of the partial virtual complexes. -/
theorem virtualComplex_map (B : Finset A) {K L : (Compacts (TopCat.of X))ᵒᵖ} (h : K ⟶ L) :
    (𝒜.virtualComplex k hΓ B).map h =
      HomologicalComplex.extendMap
        (IntervalDiagram.totalMap ((𝒜.partialVirtualChainDiagram k hΓ B).map h))
        (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-! ### The top partial complex -/

/-- **The inclusion of the top partial complex** `R_BB ⟶ C_vir(−; B)`, as the summand of the
one-vertex flag `(B)` (`TauCeti.IntervalDiagram.topι`), read in cochain degrees through the
isomorphism of `R_BB(K)` with the extension of its restriction to chain degrees
(`HomologicalComplex.πStupidTrunc`). -/
def virtualComplexTopι (B : Finset A) :
    𝒜.partialVirtualComplex k B (subset_refl B) ⟶ 𝒜.virtualComplex k hΓ B where
  app K := ((𝒜.partialVirtualComplex k B (subset_refl B)).obj K).πStupidTrunc
      (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) ≫
    HomologicalComplex.extendMap ((𝒜.partialVirtualChainDiagram k hΓ B).obj K).topι
      (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ)))
  naturality K L h := by
    -- `πStupidTrunc` is natural and `topι` is natural in the diagram. The two composites agree
    -- because the restriction of `R_BB` along `h` is, definitionally, the component at the top
    -- interval of the map of diagrams, `R_BB` being the value at `(⊤, ⊤) = (B, B)`.
    have hTop := congrArg (HomologicalComplex.extendMap · (ComplexShape.embeddingUpIntLE
      (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))))
      (IntervalDiagram.topι_totalMap ((𝒜.partialVirtualChainDiagram k hΓ B).map h))
    simp only [HomologicalComplex.extendMap_comp] at hTop
    -- The goal typechecks only up to unfolding `stupidTrunc` and the diagram, so `rw` and `simp`
    -- cannot rewrite in it; the two naturality squares are pasted by unification instead.
    exact (HomologicalComplex.πStupidTrunc_naturality_assoc _ _ _).symm.trans <|
      (_ ≫= hTop.symm).trans (Category.assoc _ _ _).symm

/-- The component of the inclusion of the top partial complex at `K`. -/
theorem virtualComplexTopι_app (B : Finset A) (K : (Compacts (TopCat.of X))ᵒᵖ) :
    (𝒜.virtualComplexTopι k hΓ B).app K =
      ((𝒜.partialVirtualComplex k B (subset_refl B)).obj K).πStupidTrunc
          (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) ≫
        HomologicalComplex.extendMap ((𝒜.partialVirtualChainDiagram k hΓ B).obj K).topι
          (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-- **The virtual complex for the empty set of indices.** For `B = ∅` the only interval is
`(∅, ∅)`, and the inclusion
`R_∅∅(K) ⟶ C_vir(K; ∅)` of the top partial complex is a quasi-isomorphism, by Pardon's
Lemma A.7.3. -/
theorem quasiIso_virtualComplexTopι_app_empty (K : (Compacts (TopCat.of X))ᵒᵖ) :
    QuasiIso ((𝒜.virtualComplexTopι k hΓ ∅).app K) := by
  have : Subsingleton (Set.Iic (∅ : Finset A)) :=
    ⟨fun a b ↦ Subtype.ext <|
      (Finset.subset_empty.1 a.property).trans (Finset.subset_empty.1 b.property).symm⟩
  have : IsIso (((𝒜.partialVirtualComplex k ∅ (subset_refl ∅)).obj K).πStupidTrunc
      (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ ∅, (finrank ℝ (E α) : ℤ)))) := by
    rw [HomologicalComplex.isIso_πStupidTrunc_iff, partialVirtualComplex_obj]
    infer_instance
  have : QuasiIso ((𝒜.partialVirtualChainDiagram k hΓ ∅).obj K).topι :=
    IntervalDiagram.quasiIso_topι _ fun I J hIJ _ ↦ by
      obtain rfl : I = J := NonemptyInterval.ext (Subsingleton.elim _ _)
      rw [show homOfLE hIJ = 𝟙 I from Subsingleton.elim _ _, op_id, CategoryTheory.Functor.map_id]
      infer_instance
  rw [virtualComplexTopι_app]
  exact (quasiIso_iff_comp_left _ _).2 ((HomologicalComplex.quasiIso_extendMap_iff
    ((𝒜.partialVirtualChainDiagram k hΓ ∅).obj K).topι
    (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ ∅, (finrank ℝ (E α) : ℤ)))).2 this)

/-! ### The empty compact set -/

/-- **The virtual complex of the empty set is zero**, since all its partial complexes are
(`isZero_partialVirtualComplex_obj_of_coe_eq_empty`). -/
theorem isZero_virtualComplex_obj_of_coe_eq_empty (B : Finset A)
    {K : (Compacts (TopCat.of X))ᵒᵖ} (hK : (K.unop : Set X) = ∅) :
    IsZero ((𝒜.virtualComplex k hΓ B).obj K) := by
  rw [virtualComplex_obj]
  refine (ComplexShape.embeddingUpIntLE _).extendFunctor _ |>.map_isZero <|
    IntervalDiagram.isZero_total fun x ↦ ?_
  rw [partialVirtualChainDiagram_obj_obj]
  exact (ComplexShape.embeddingUpIntLE _).restrictionFunctor _ |>.map_isZero <|
    isZero_partialVirtualComplex_obj_of_coe_eq_empty _ hK

/-- **The virtual complexes of an atlas on the empty space are zero.** -/
theorem isZero_virtualComplex_obj_of_isEmpty [IsEmpty X] (B : Finset A)
    (K : (Compacts (TopCat.of X))ᵒᵖ) : IsZero ((𝒜.virtualComplex k hΓ B).obj K) :=
  𝒜.isZero_virtualComplex_obj_of_coe_eq_empty k hΓ B (Set.eq_empty_of_isEmpty _)

end TauCeti.ImplicitAtlas
