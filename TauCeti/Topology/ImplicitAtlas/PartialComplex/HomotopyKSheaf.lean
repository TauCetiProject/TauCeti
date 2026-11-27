/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.HomotopyKSheaf
public import TauCeti.CategoryTheory.Limits.Shapes.SingleObj
public import TauCeti.Topology.ImplicitAtlas.PartialComplex
public import TauCeti.Topology.Sheaves.KSheaf.Retract

/-!
# The partial virtual complexes are homotopy K-sheaves

Let `𝒜` be an implicit atlas of virtual dimension `d` on a locally compact Hausdorff space `X`, and
let `I ⊆ J ⊆ B` be finite sets of indices. The partial virtual complex `R_IJ` of `𝒜`
(`TauCeti.ImplicitAtlas.partialVirtualComplex`) is the K-presheaf of cochain complexes

`K ↦ C_(d + m_B - •)(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)`

of invariant relative chains on the deformation space `D_(I,J,B)`, relative to the complement of
the support `Z_K` of `K`. This file proves that it is a homotopy K-sheaf
(`TauCeti.ImplicitAtlas.isHomotopyKSheaf_partialVirtualComplex`), for coefficients in a commutative
ring `k` in which the orders of the isotropy groups are units. This is the first part of Pardon's
partial purity (Pardon, Section 4.3): it is the hypothesis under which the sheaf theory of homotopy
K-sheaves, and with it the comparison of virtual and Čech cohomology, applies to the partial
complexes. The argument has two steps.

* **Relative chains along the supports.** Before taking invariants, the complexes
  `C_(d + m_B - •)(D, D ∖ Z_K; o_(E_B)^∨)` are relative singular chains along the closed sets
  `Z_K ⊆ D` (`TauCeti.localChainKPresheaf`), and they form a homotopy K-sheaf by Pardon's
  Lemma A.6.3 (`TauCeti.isHomotopyKSheaf_localChainKPresheaf`). Its hypotheses on `K ↦ Z_K` hold:
  `Z_K` is the set of points `(0, t, x)` with `ψ_∅J(x) ∈ K`, a preimage of `K`, so it is empty for
  `K = ∅` and takes unions to unions and intersections to intersections; it is closed
  (`TauCeti.ImplicitAtlas.isClosed_deformationSupport`); and a compact set `T ⊆ D` disjoint from
  `Z_K` is disjoint from `Z_L` for a compact neighbourhood `L` of `K`
  (`TauCeti.ImplicitAtlas.exists_mem_compactNhds_disjoint_deformationSupport`), since the points of
  `T` with `e = 0` lie over a compact subset of `X` disjoint from `K`.
* **Invariants.** When the order of `Γ_B` is a unit of `k`, averaging over `Γ_B` retracts the
  chains onto the invariant chains, naturally in the pair
  (`CategoryTheory.Limits.SingleObj.limRetract`). So `R_IJ` is a retract of the K-presheaf of all
  chains (`TauCeti.ImplicitAtlas.partialVirtualComplexRetract`), and a retract of a homotopy
  K-sheaf is a homotopy K-sheaf (`TopCat.KPresheaf.IsHomotopyKSheaf.of_retract`).

The purity of the partial complexes of a locally orientable atlas, and their uniform lower bound,
are not treated here.

## Main results

* `TauCeti.ImplicitAtlas.deformationPairChainsIso`: before taking invariants, the chains of the
  deformation pairs are the relative chains along the supports `Z_K`.
* `TauCeti.ImplicitAtlas.partialVirtualComplexRetract`: the partial virtual complex is a retract of
  the K-presheaf of relative chains along the supports.
* `TauCeti.ImplicitAtlas.isHomotopyKSheaf_partialVirtualComplex`: the partial virtual complex is a
  homotopy K-sheaf.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Section 4.3 (partial purity),
  Definition A.2.5 (homotopy K-sheaves) and Lemma A.6.3 (relative singular chains).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Module Set

universe u

namespace TauCeti.ImplicitAtlas

variable {A : Type u} [DecidableEq A] {Γ : A → Type u} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type u} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type u} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type u} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-! ### The supports along the compact sets of the base -/

/-- The support `Z_K ⊆ D_(I,J,B)` as a monotone function of the compact set `K ⊆ X`. -/
def deformationSupportHom (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    Compacts (TopCat.of X) →o Set (𝒜.deformationSpace I hJB) :=
  ⟨fun K ↦ 𝒜.deformationSupport I hJB K, fun _ _ h ↦ deformationSupport_mono h⟩

@[simp]
theorem deformationSupportHom_apply (I : Finset A) {J B : Finset A} (hJB : J ⊆ B)
    (K : Compacts (TopCat.of X)) :
    𝒜.deformationSupportHom I hJB K = 𝒜.deformationSupport I hJB K :=
  (rfl)

/-! ### The partial virtual complexes as retracts of relative chains -/

section Complexes

variable (k : Type u) [CommRing k]

variable (ρ) in
/-- The dual orientation line `o_(E_B)^∨` of the obstruction space `E_B`, as an action of `Γ_B` on
a `k`-module: the coefficients of the partial virtual complexes. -/
abbrev partialVirtualCoefficients (B : Finset A) : SingleObj ((α : B) → Γ α) ⥤ ModuleCat.{u} k :=
  (Representation.externalPi fun α : B ↦ ρ α).dualOrientationLine k

/-- The deformation pairs `(D_(I,J,B), D_(I,J,B) ∖ Z_K)` with their actions of `Γ_B`, as a
contravariant functor of the compact set `K ⊆ X`. -/
def deformationPairPresheaf (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    (Compacts (TopCat.of X))ᵒᵖ ⥤ (SingleObj ((α : B) → Γ α) ⥤ TopPair.{u}) where
  obj K := 𝒜.deformationPairFunctor I hJB K.unop
  map h := 𝒜.deformationPairRestriction I hJB (SetLike.coe_subset_coe.2 (leOfHom h.unop))
  map_id _ := deformationPairRestriction_refl _ _
  map_comp _ _ := (deformationPairRestriction_comp_deformationPairRestriction _ _ _).symm

/-- The partial virtual complex is the invariant chains of the deformation pairs. -/
theorem partialVirtualComplex_eq (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    𝒜.partialVirtualComplex k I hJB = 𝒜.deformationPairPresheaf I hJB ⋙
      invariantChainsFunctor ρ k B (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ)) :=
  (rfl)

/-- The relative chains of the deformation pairs with coefficients in `o_(E_B)^∨`, before taking
invariants, are the relative chains along the supports `Z_K`. -/
def deformationPairChainsIso (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (n : ℤ) :
    𝒜.deformationPairPresheaf I hJB ⋙ TopPair.diagonalChainActionFunctor
        (partialVirtualCoefficients ρ k B) ⋙
      (evaluation _ _).obj (SingleObj.star _) ⋙
        (ComplexShape.embeddingUpIntLE n).extendFunctor (ModuleCat.{u} k) ≅
      localChainKPresheaf ((partialVirtualCoefficients ρ k B).obj (SingleObj.star _))
        (𝒜.deformationSupportHom I hJB) n :=
  NatIso.ofComponents
    (fun K ↦ ((ComplexShape.embeddingUpIntLE n).extendFunctor (ModuleCat.{u} k)).mapIso
      (eqToIso (TopPair.singularChainComplexFunctor_obj_obj _ _)))
    fun {K L} h ↦ by
      have key : (TopPair.diagonalChainActionMap (partialVirtualCoefficients ρ k B)
          ((𝒜.deformationPairPresheaf I hJB).map h)).app (SingleObj.star _) ≫
            eqToHom (TopPair.singularChainComplexFunctor_obj_obj _ _) =
          eqToHom (TopPair.singularChainComplexFunctor_obj_obj _ _) ≫
            localChainRestriction _
              ((𝒜.deformationSupportHom I hJB).monotone (leOfHom h.unop)) := by
        have hres : ((𝒜.deformationPairPresheaf I hJB).map h).app (SingleObj.star _) =
            TopPair.ofSubsetMap (𝟙 (TopCat.of (𝒜.deformationSpace I hJB)))
              (compl_subset_compl.2 ((𝒜.deformationSupportHom I hJB).monotone
                (leOfHom h.unop))) :=
          have hfst : TopPair.Hom.fst (((𝒜.deformationPairPresheaf I hJB).map h).app
              (SingleObj.star _)) = 𝟙 (TopCat.of (𝒜.deformationSpace I hJB)) :=
            ConcreteCategory.hom_ext _ _ fun p ↦
              𝒜.deformationPairRestriction_app_fst_apply I hJB _ _ p
          TopPair.hom_ext_of_fst _ (hfst.trans (TopPair.ofSubsetMap_fst _ _).symm)
        refine (TopPair.diagonalChainActionMap_app_comp_eqToHom _ _ _).trans ?_
        exact (congrArg (fun f ↦ eqToHom _ ≫ TopPair.singularChainComplexMap f
          ((partialVirtualCoefficients ρ k B).obj (SingleObj.star _))) hres).trans
            (congrArg (eqToHom _ ≫ ·) (localChainRestriction_def _ _).symm)
      let ext := (ComplexShape.embeddingUpIntLE n).extendFunctor (ModuleCat.{u} k)
      exact (ext.map_comp _ _).symm.trans ((congrArg ext.map key).trans (ext.map_comp _ _))

variable {k} (hΓ : ∀ α, IsUnit (Nat.card (Γ α) : k))

/-- **The partial virtual complex is a retract of the relative chains along the supports.** When
the orders of the isotropy groups are units of `k`, averaging over `Γ_B` retracts the relative
chains `C_(d + m_B - •)(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)` onto the invariant chains
`R_IJ(K)`, naturally in the compact set `K`. -/
def partialVirtualComplexRetract (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    Retract (𝒜.partialVirtualComplex k I hJB)
      (localChainKPresheaf ((partialVirtualCoefficients ρ k B).obj (SingleObj.star _))
        (𝒜.deformationSupportHom I hJB) (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  letI := Fintype.ofFinite ((α : B) → Γ α)
  let Φ := 𝒜.deformationPairPresheaf I hJB ⋙
    TopPair.diagonalChainActionFunctor (partialVirtualCoefficients ρ k B)
  let ext := (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))).extendFunctor
    (ModuleCat.{u} k)
  -- the order of `Γ_B = ∏_(α ∈ B) Γ_α` is a unit, as the orders of the `Γ_α` are
  have hB : IsUnit (Fintype.card ((α : B) → Γ α) : k) := by
    rw [← Nat.card_eq_fintype_card, Nat.card_pi, Nat.cast_prod]
    exact IsUnit.prod_univ_iff.2 fun α ↦ hΓ α
  let r := SingleObj.limRetract (C := ChainComplex (ModuleCat.{u} k) ℕ) hB
  -- the source is `(Φ ⋙ lim) ⋙ ext` by `partialVirtualComplex_eq`, which holds by `rfl`
  Retract.trans
    { i := Functor.whiskerRight (Functor.whiskerLeft Φ r.i) ext
      r := Functor.whiskerRight (Functor.whiskerLeft Φ r.r) ext
      retract := by
        ext K : 2
        exact (ext.map_comp _ _).symm.trans
          ((congrArg ext.map (Retract.retract_app r (Φ.obj K))).trans (ext.map_id _)) }
    (Retract.ofIso (𝒜.deformationPairChainsIso k I hJB _))

include hΓ in
/-- **The partial virtual complexes are homotopy K-sheaves** (Pardon, Section 4.3). For an implicit
atlas on a locally compact Hausdorff space and coefficients in a commutative ring in which the
orders of the isotropy groups are units, the partial virtual complex
`K ↦ C_(d + m_B - •)(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)` is a homotopy K-sheaf: it is a
retract of the relative chains along the supports `Z_K`, which form one by Pardon's
Lemma A.6.3. -/
theorem isHomotopyKSheaf_partialVirtualComplex [T2Space X] [LocallyCompactSpace X]
    (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    (𝒜.partialVirtualComplex k I hJB).IsHomotopyKSheaf :=
  (isHomotopyKSheaf_localChainKPresheaf ((partialVirtualCoefficients ρ k B).obj (SingleObj.star _))
      (𝒜.deformationSupportHom I hJB) _
      (Set.eq_empty_of_forall_notMem fun _ hp ↦ (mem_deformationSupport.1 hp).2.2)
      (fun _ _ _ hp ↦ let ⟨he, hx, h⟩ := mem_deformationSupport.1 hp
        h.imp (fun h ↦ mem_deformationSupport.2 ⟨he, hx, h⟩)
          fun h ↦ mem_deformationSupport.2 ⟨he, hx, h⟩)
      (fun _ _ _ ⟨hp, hp'⟩ ↦ let ⟨he, hx, h⟩ := mem_deformationSupport.1 hp
        mem_deformationSupport.2 ⟨he, hx, h, (mem_deformationSupport.1 hp').2.2⟩)
      (fun K ↦ isClosed_deformationSupport K.isCompact.isClosed)
      fun K _ hS hSK ↦ 𝒜.exists_mem_compactNhds_disjoint_deformationSupport K hS hSK
    ).of_retract (𝒜.partialVirtualComplexRetract hΓ I hJB)

end Complexes

end TauCeti.ImplicitAtlas
