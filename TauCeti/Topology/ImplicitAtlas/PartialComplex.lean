/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Topology.Sheaves.KSheaf
public import TauCeti.Algebra.Category.ModuleCat.Invariants
public import TauCeti.Algebra.Homology.OrderedCech.IntervalDiagram
public import TauCeti.AlgebraicTopology.Singular.EquivariantChains
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Representation
public import TauCeti.RepresentationTheory.Pi.External
public import TauCeti.Topology.Category.TopPair.Action
public import TauCeti.Topology.ImplicitAtlas.DeformationSpace

/-!
# The partial virtual complexes of an implicit atlas

Let `𝒜` be an implicit atlas of virtual dimension `d` on `X`, with isotropy groups `Γ_α` and
obstruction representations `E_α`, and let `B` be a finite set of indices. For `I ⊆ J ⊆ B` and a
subset `K ⊆ X`, Pardon's **partial virtual complex** is the complex of invariant relative chains

`R_IJ(K)^q = C_(d + m_B - q)(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)`

on the deformation space `D_(I,J,B)` (`TauCeti.ImplicitAtlas.deformationSpace`) relative to the
complement of the support `Z_K` of `K` (`TauCeti.ImplicitAtlas.deformationSupport`), where
`m_B = dim E_B`, with coefficients in the dual `o_(E_B)^∨` of the orientation line of
`E_B = ⊕_(α ∈ B) E_α`, and invariant under `Γ_B = ∏_(α ∈ B) Γ_α`, which acts diagonally on the
deformation space and on the coefficients. These complexes, glued over the finite poset of subsets
of `B`, make up the virtual cochain complex of the atlas, from which its virtual fundamental class
is defined.

This file constructs them, for coefficients in a commutative ring `k`.

* **The action on the deformation pairs.** `Γ_B` acts on `D_(I,J,B)` through
  `TauCeti.ImplicitAtlas.deformationAction`, and the supports `Z_K` are invariant, so it acts on
  the pair `(D_(I,J,B), D_(I,J,B) ∖ Z_K)` (`TauCeti.ImplicitAtlas.deformationPairFunctor`).
* **The coefficients.** The dual orientation line `o_(E_B)^∨`, on which `g ∈ Γ_B` acts by the sign
  of the determinant of `g` on `E_B`, is `TauCeti.ImplicitAtlas.dualOrientationLine`.
* **The complexes.** `TauCeti.ImplicitAtlas.partialChains` is the complex of invariant relative
  chains `C(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)` in its homological grading, the limit
  of the diagonal action `TopPair.diagonalChainAction`. Placing the chains of degree `n` in
  cochain degree `d + m_B - n`, invariant chains become a functor of the pair with its action
  (`TauCeti.ImplicitAtlas.invariantChainsFunctor`), and the complexes form a K-presheaf of cochain
  complexes on `X`, `TauCeti.ImplicitAtlas.partialVirtualComplex`: for `K ⊆ L` the restriction
  `R_IJ(L) ⟶ R_IJ(K)` is induced by the identity of `D_(I,J,B)`, since `Z_K ⊆ Z_L`.
* **The interval arrows.** For `I ⊆ I' ⊆ J' ⊆ J ⊆ B`, the comparison map
  `D_(I,J,B) ⟶ D_(I',J',B)` (`TauCeti.ImplicitAtlas.deformationMap`) is an equivariant map of
  pairs, so it induces a map of K-presheaves (`TauCeti.ImplicitAtlas.partialVirtualComplexMap`).
  The interval arrow `R_IJ ⟶ R_I'J'` is this map multiplied by `|Γ_(J ∖ J')|⁻¹`
  (`TauCeti.ImplicitAtlas.partialVirtualComplexArrow`), for coefficients in a commutative ring in
  which the orders of the isotropy groups are units, such as a field of characteristic zero. The
  arrows are strictly functorial: the arrow of an interval to itself is the identity
  (`TauCeti.ImplicitAtlas.partialVirtualComplexArrow_self`), and the arrows compose
  (`TauCeti.ImplicitAtlas.partialVirtualComplexArrow_comp_partialVirtualComplexArrow`), the
  weights multiplying because `|Γ_(J ∖ J')| |Γ_(J' ∖ J'')| = |Γ_(J ∖ J'')|`. A single weight
  `w ≠ 1` on every arrow would not compose, since a composite of two arrows would carry `w²`. So
  the partial virtual complexes form an interval diagram on the subsets of `B`
  (`TauCeti.ImplicitAtlas.partialVirtualDiagram`), the input of the flag total
  `TauCeti.IntervalDiagram.total`.

The atlases here have no boundary, so the relative and absolute partial complexes of Pardon
coincide.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), 779–1034, Definition 4.2.5 (the partial
  complexes) and Definition 4.2.6 (the weighted interval arrows and the virtual cochain complex).
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace Module
open scoped TensorProduct

universe u

namespace TauCeti.ImplicitAtlas

variable {A : Type u} [DecidableEq A] {Γ : A → Type u} [∀ α, Group (Γ α)] [∀ α, Finite (Γ α)]
  {E : A → Type u} [∀ α, NormedAddCommGroup (E α)] [∀ α, NormedSpace ℝ (E α)]
  [∀ α, FiniteDimensional ℝ (E α)] {ρ : ∀ α, Representation ℝ (Γ α) (E α)}
  {T : Finset A → Type u} [∀ I, TopologicalSpace (T I)] [∀ I, T2Space (T I)]
  {act : ∀ I : Finset A, ((α : I) → Γ α) →* (T I ≃ₜ T I)}
  {X : Type u} [TopologicalSpace X] {d : ℤ} (𝒜 : ImplicitAtlas Γ E ρ T act X d)

/-! ### The action of `Γ_B` on the deformation pairs -/

/-- **The deformation pair** `(D_(I,J,B), D_(I,J,B) ∖ Z_K)` of a subset `K ⊆ X`, with the action of
`Γ_B`, as a functor `SingleObj Γ_B ⥤ TopPair`. The action preserves the complement of the support
`Z_K`, since `Z_K` is invariant (`deformationAction_mem_deformationSupport_iff`). -/
-- The body is exposed so that the values are definitionally the pairs `(D, D ∖ Z_K)`: the maps of
-- pairs below, between these values, typecheck only then.
@[expose]
def deformationPairFunctor (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (K : Set X) :
    SingleObj ((α : B) → Γ α) ⥤ TopPair.{u} :=
  TopPair.ofSubsetActionFunctor (TopCat.of (𝒜.deformationSpace I hJB)) _
    (𝒜.deformationSupport I hJB K)ᶜ fun g p hp ↦
      (deformationAction_mem_deformationSupport_iff g p).not.2 hp

/-- The deformation pair of `K` is the pair `(D_(I,J,B), D_(I,J,B) ∖ Z_K)`. -/
@[simp]
theorem deformationPairFunctor_obj (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (K : Set X)
    (Y : SingleObj ((α : B) → Γ α)) :
    (𝒜.deformationPairFunctor I hJB K).obj Y =
      TopPair.ofSubset (X := TopCat.of (𝒜.deformationSpace I hJB))
        (𝒜.deformationSupport I hJB K)ᶜ :=
  (rfl)

/-- An element `g` of `Γ_B` acts on the deformation pair of `K` by the map of pairs induced by the
homeomorphism `deformationAction g` of `D_(I,J,B)`. -/
theorem deformationPairFunctor_map (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (K : Set X)
    (g : (α : B) → Γ α) :
    (𝒜.deformationPairFunctor I hJB K).map (X := SingleObj.star _) (Y := SingleObj.star _) g =
      TopPair.ofSubsetMap (TopCat.ofHom (𝒜.deformationAction I hJB g : C(_, _)))
        fun p hp ↦ (deformationAction_mem_deformationSupport_iff g p).not.2 hp :=
  (rfl)

/-- An element `g` of `Γ_B` acts on the deformation pair of `K` by `deformationAction g`. -/
@[simp]
theorem deformationPairFunctor_map_fst_apply (I : Finset A) {J B : Finset A} (hJB : J ⊆ B)
    (K : Set X) (g : (α : B) → Γ α) (p : 𝒜.deformationSpace I hJB) :
    TopPair.Hom.fst ((𝒜.deformationPairFunctor I hJB K).map (X := SingleObj.star _)
      (Y := SingleObj.star _) g) p = 𝒜.deformationAction I hJB g p :=
  (TopPair.ofSubsetActionFunctor_map_fst_apply (TopCat.of (𝒜.deformationSpace I hJB)) _ _ _ g
    p).trans (deformationSpace_smul_def g p)

/-- **Restriction of the deformation pairs.** For `K ⊆ L`, the identity of `D_(I,J,B)` is an
equivariant map of pairs `(D_(I,J,B), D_(I,J,B) ∖ Z_L) ⟶ (D_(I,J,B), D_(I,J,B) ∖ Z_K)`, since
`Z_K ⊆ Z_L` (`deformationSupport_mono`). -/
def deformationPairRestriction (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) {K L : Set X}
    (h : K ⊆ L) : 𝒜.deformationPairFunctor I hJB L ⟶ 𝒜.deformationPairFunctor I hJB K where
  app _ := TopPair.ofSubsetMap (𝟙 _) fun _ hp ↦
    Set.compl_subset_compl.2 (deformationSupport_mono h) hp
  naturality x y g := by
    obtain rfl : x = SingleObj.star _ := rfl
    obtain rfl : y = SingleObj.star _ := rfl
    dsimp only [deformationPairFunctor_map]
    -- Both composites have ambient map `deformationAction g`, as the restriction is the identity.
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq (h := ConcreteCategory.hom_ext _ _ fun _ ↦ rfl) ..

/-- The restriction of the deformation pairs is the identity on `D_(I,J,B)`. -/
@[simp]
theorem deformationPairRestriction_app_fst_apply (I : Finset A) {J B : Finset A} (hJB : J ⊆ B)
    {K L : Set X} (h : K ⊆ L) (Y : SingleObj ((α : B) → Γ α)) (p : 𝒜.deformationSpace I hJB) :
    TopPair.Hom.fst ((𝒜.deformationPairRestriction I hJB h).app Y) p = p :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of (𝒜.deformationSpace I hJB)) _ _ p

/-- **The comparison of deformation pairs.** For `I ⊆ I' ⊆ J' ⊆ J ⊆ B`, the comparison map
`D_(I,J,B) ⟶ D_(I',J',B)`, `(e, t, x) ↦ (e, t, ψ_J'J(x))`
(`TauCeti.ImplicitAtlas.deformationMap`, with no new obstruction coordinates), is an equivariant
map of pairs `(D_(I,J,B), D_(I,J,B) ∖ Z_K) ⟶ (D_(I',J',B), D_(I',J',B) ∖ Z_K)`: a point outside
`Z_K` goes to a point outside `Z_K` (`deformationMap_mem_deformationSupport_iff`). -/
def deformationPairArrow {I I' J J' B : Finset A} (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hJB : J ⊆ B) (K : Set X) :
    𝒜.deformationPairFunctor I hJB K ⟶ 𝒜.deformationPairFunctor I' (hJ'J.trans hJB) K where
  app _ := TopPair.ofSubsetMap
    (TopCat.ofHom ⟨fun p ↦ 𝒜.deformationMap hII' (hII'.trans hI'J') hJ'J hJB subset_rfl p 0,
      continuous_deformationMap.comp (continuous_id.prodMk continuous_const)⟩)
    fun p hp h ↦ hp ((deformationMap_mem_deformationSupport_iff p 0).1 h).1
  naturality x y g := by
    obtain rfl : x = SingleObj.star _ := rfl
    obtain rfl : y = SingleObj.star _ := rfl
    dsimp only [deformationPairFunctor_map]
    refine TopPair.ofSubsetMap_comp_ofSubsetMap_eq (h := ConcreteCategory.hom_ext _ _ fun p ↦ ?_) ..
    have h := 𝒜.deformationMap_deformationAction (hII' := hII') (hIJ' := hII'.trans hI'J')
      (hJ'J := hJ'J) (hBB' := subset_rfl) g p 0
    simp only [Pi.zero_apply, map_zero] at h
    exact h

/-- The comparison of deformation pairs is the comparison map of deformation spaces. -/
@[simp]
theorem deformationPairArrow_app_fst_apply {I I' J J' B : Finset A} (hII' : I ⊆ I')
    (hI'J' : I' ⊆ J') (hJ'J : J' ⊆ J) (hJB : J ⊆ B) (K : Set X) (Y : SingleObj ((α : B) → Γ α))
    (p : 𝒜.deformationSpace I hJB) :
    TopPair.Hom.fst ((𝒜.deformationPairArrow hII' hI'J' hJ'J hJB K).app Y) p =
      𝒜.deformationMap hII' (hII'.trans hI'J') hJ'J hJB subset_rfl p 0 :=
  TopPair.ofSubsetMap_fst_apply (X := TopCat.of (𝒜.deformationSpace I hJB)) _ _ p

section PairLaws

variable {𝒜} {I I' I'' J J' J'' B : Finset A}

/-- The restriction of the deformation pairs along `K ⊆ K` is the identity. -/
@[simp]
theorem deformationPairRestriction_refl (hJB : J ⊆ B) (K : Set X) :
    𝒜.deformationPairRestriction I hJB (subset_refl K) = 𝟙 _ := by
  exact NatTrans.ext (funext fun _ ↦ TopPair.ofSubsetMap_id _)

/-- Restrictions of the deformation pairs compose. -/
@[reassoc (attr := simp)]
theorem deformationPairRestriction_comp_deformationPairRestriction (hJB : J ⊆ B)
    {K L M : Set X} (h₁ : K ⊆ L) (h₂ : L ⊆ M) :
    𝒜.deformationPairRestriction I hJB h₂ ≫ 𝒜.deformationPairRestriction I hJB h₁ =
      𝒜.deformationPairRestriction I hJB (h₁.trans h₂) := by
  refine NatTrans.ext (funext fun Y ↦ ?_)
  dsimp only [NatTrans.comp_app]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (Category.comp_id _)

/-- The comparison of deformation pairs commutes with their restrictions. -/
@[reassoc]
theorem deformationPairRestriction_comp_deformationPairArrow (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hJB : J ⊆ B) {K L : Set X} (h : K ⊆ L) :
    𝒜.deformationPairRestriction I hJB h ≫ 𝒜.deformationPairArrow hII' hI'J' hJ'J hJB K =
      𝒜.deformationPairArrow hII' hI'J' hJ'J hJB L ≫
        𝒜.deformationPairRestriction I' (hJ'J.trans hJB) h := by
  refine NatTrans.ext (funext fun Y ↦ ?_)
  dsimp only [NatTrans.comp_app]
  -- Both composites have ambient map `deformationMap · 0`, since the restrictions are identities.
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_eq _ _ _ _ (ConcreteCategory.hom_ext _ _ fun _ ↦ rfl)

/-- The comparison of a deformation pair with itself is the identity
(`deformationMap_self`). -/
@[simp]
theorem deformationPairArrow_self (hIJ : I ⊆ J) (hJB : J ⊆ B) (K : Set X) :
    𝒜.deformationPairArrow subset_rfl hIJ subset_rfl hJB K = 𝟙 _ := by
  refine NatTrans.ext (funext fun Y ↦ TopPair.hom_ext_of_fst _ ?_)
  exact (TopPair.ofSubsetMap_fst _ _).trans
    (ConcreteCategory.hom_ext _ _ fun p ↦ deformationMap_self hIJ p 0)

/-- Comparisons of deformation pairs compose (`deformationMap_deformationMap`). -/
@[reassoc (attr := simp)]
theorem deformationPairArrow_comp_deformationPairArrow (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hI'I'' : I' ⊆ I'') (hI''J'' : I'' ⊆ J'') (hJ''J' : J'' ⊆ J')
    (hJB : J ⊆ B) (K : Set X) :
    𝒜.deformationPairArrow hII' hI'J' hJ'J hJB K ≫
        𝒜.deformationPairArrow hI'I'' hI''J'' hJ''J' (hJ'J.trans hJB) K =
      𝒜.deformationPairArrow (hII'.trans hI'I'') hI''J'' (hJ''J'.trans hJ'J) hJB K := by
  refine NatTrans.ext (funext fun Y ↦ ?_)
  dsimp only [deformationPairArrow, NatTrans.comp_app]
  exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ (ConcreteCategory.hom_ext _ _
    fun p ↦ 𝒜.deformationMap_deformationMap _ _ _ subset_rfl p 0 0 0 rfl rfl)

end PairLaws

/-! ### The partial virtual complexes -/

section Complexes

variable (k : Type u) [CommRing k]

variable (ρ) in
/-- **The dual orientation line** `o_(E_B)^∨` of the obstruction representation
`E_B = ⊕_(α ∈ B) E_α` of `Γ_B`, with coefficients in `k`: the dual of the scalar extension to `k`
of the integral orientation line `o_(E_B) = H_m(E_B, E_B ∖ 0; ℤ)`, `m = dim E_B`, on which
`g ∈ Γ_B` acts by the sign of the determinant of `g` on `E_B`
(`Representation.dual_baseChange_orientation_eq_sign_det_smul`), as a functor
`SingleObj Γ_B ⥤ ModuleCat k`. -/
-- The body is exposed so that the value is definitionally the dual line: the statement of
-- `dualOrientationLine_map`, a map between values, typechecks only then.
@[expose]
def dualOrientationLine (B : Finset A) : SingleObj ((α : B) → Γ α) ⥤ ModuleCat.{u} k :=
  SingleObj.functor (X := ModuleCat.of k (Dual k (k ⊗[ℤ] orientationModule ((α : B) → E α))))
    { toFun g := .of <| ModuleCat.ofHom
        (((Representation.externalPi fun α : B ↦ ρ α).orientation.baseChange k).dual g)
      map_one' := End.ext <| ModuleCat.hom_ext <| by
        rw [map_one, End.one_asHom, ModuleCat.hom_ofHom, ModuleCat.hom_id, Module.End.one_eq_id]
      map_mul' g h := End.ext <| ModuleCat.hom_ext <| by
        rw [map_mul, End.mul_asHom, ModuleCat.hom_ofHom, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
          ModuleCat.hom_ofHom, Module.End.mul_eq_comp] }

omit [DecidableEq A] [∀ α, Finite (Γ α)] in
/-- The dual orientation line is the dual of the scalar extension of `o_(E_B)`. -/
@[simp]
theorem dualOrientationLine_obj (B : Finset A) (Y : SingleObj ((α : B) → Γ α)) :
    (dualOrientationLine ρ k B).obj Y =
      ModuleCat.of k (Dual k (k ⊗[ℤ] orientationModule ((α : B) → E α))) :=
  (rfl)

omit [DecidableEq A] [∀ α, Finite (Γ α)] in
/-- An element of `Γ_B` acts on the dual orientation line by the dual of the scalar extension of
its action on the orientation line of `E_B`. -/
theorem dualOrientationLine_map (B : Finset A) (g : (α : B) → Γ α) :
    ((dualOrientationLine ρ k B).map (X := SingleObj.star _) (Y := SingleObj.star _) g).hom =
      ((Representation.externalPi fun α : B ↦ ρ α).orientation.baseChange k).dual g :=
  (rfl)

/-- **The invariant relative chains of a deformation pair**: the complex
`C(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)` of the chains invariant under the diagonal action
of `Γ_B` on the deformation pair and on the dual orientation line, in its homological grading. -/
-- The body is exposed so that the complexes are definitionally the limits: the restrictions and
-- comparisons below, maps of limits between them, typecheck only then.
@[expose]
def partialChains (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) (K : Set X) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  limit (TopPair.diagonalChainAction (dualOrientationLine ρ k B) (𝒜.deformationPairFunctor I hJB K))

variable (ρ) in
/-- **The invariant relative chains with coefficients in the dual orientation line, in cochain
degrees `n - •`**, as a functor of a pair with an action of `Γ_B`: a pair `P` goes to the complex
`C(P; o_(E_B)^∨)^(Γ_B)` of the chains invariant under the diagonal action, placed in cochain degrees
`n - •`, and an equivariant map of pairs to the induced map of invariant chains. -/
-- The body is exposed so that the values are definitionally the extended limits: the statement of
-- `partialVirtualComplex_obj` typechecks only then.
@[expose]
def invariantChainsFunctor (B : Finset A) (n : ℤ) :
    (SingleObj ((α : B) → Γ α) ⥤ TopPair.{u}) ⥤ CochainComplex (ModuleCat.{u} k) ℤ :=
  TopPair.diagonalChainActionFunctor (dualOrientationLine ρ k B) ⋙ lim ⋙
    (ComplexShape.embeddingUpIntLE n).extendFunctor _

-- The body is exposed so that the values are definitionally the extended chain complexes: the
-- statement of `partialVirtualComplexMap_app`, a map between values, typechecks only then.
/-- **The partial virtual complex** `R_IJ` of an implicit atlas of virtual dimension `d`, for
`I ⊆ J ⊆ B` (Pardon, Definition 4.2.5): the K-presheaf of cochain complexes on `X` whose value on a
compact set `K` is `R_IJ(K)^q = C_(d + m_B - q)(D_(I,J,B), D_(I,J,B) ∖ Z_K; o_(E_B)^∨)^(Γ_B)`,
`m_B = dim E_B`, with the restrictions induced by the identity of the deformation space. -/
@[expose]
def partialVirtualComplex (I : Finset A) {J B : Finset A} (hJB : J ⊆ B) :
    TopCat.KPresheaf (CochainComplex (ModuleCat.{u} k) ℤ) (TopCat.of X) where
  obj K := (invariantChainsFunctor ρ k B (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))).obj
    (𝒜.deformationPairFunctor I hJB K.unop)
  map h := (invariantChainsFunctor ρ k B _).map
    (𝒜.deformationPairRestriction I hJB (SetLike.coe_subset_coe.2 (leOfHom h.unop)))
  map_id K := by
    rw [deformationPairRestriction_refl, CategoryTheory.Functor.map_id]
  map_comp h h' := by
    rw [← Functor.map_comp, deformationPairRestriction_comp_deformationPairRestriction]

/-- The value of the partial virtual complex on a compact set `K` is the complex of invariant
relative chains of the deformation pair of `K`, in cochain degrees `d + m_B - •`. -/
@[simp]
theorem partialVirtualComplex_obj (I : Finset A) {J B : Finset A} (hJB : J ⊆ B)
    (K : (Compacts (TopCat.of X))ᵒᵖ) :
    (𝒜.partialVirtualComplex k I hJB).obj K = (𝒜.partialChains k I hJB K.unop).extend
      (ComplexShape.embeddingUpIntLE (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))) :=
  (rfl)

/-- The restrictions of the partial virtual complex are induced by the restrictions of the
deformation pairs. -/
theorem partialVirtualComplex_map (I : Finset A) {J B : Finset A} (hJB : J ⊆ B)
    {K L : (Compacts (TopCat.of X))ᵒᵖ} (h : K ⟶ L) :
    (𝒜.partialVirtualComplex k I hJB).map h = (invariantChainsFunctor ρ k B _).map
      (𝒜.deformationPairRestriction I hJB (SetLike.coe_subset_coe.2 (leOfHom h.unop))) :=
  (rfl)

/-- **The comparison of partial virtual complexes** `R_IJ ⟶ R_I'J'`, for `I ⊆ I' ⊆ J' ⊆ J ⊆ B`,
induced by the comparison maps of the deformation pairs (`deformationPairArrow`), without weight. -/
def partialVirtualComplexMap {I I' J J' B : Finset A} (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hJB : J ⊆ B) :
    𝒜.partialVirtualComplex k I hJB ⟶ 𝒜.partialVirtualComplex k I' (hJ'J.trans hJB) where
  app K := (invariantChainsFunctor ρ k B _).map (𝒜.deformationPairArrow hII' hI'J' hJ'J hJB K.unop)
  naturality K L h := by
    let F := invariantChainsFunctor ρ k B (d + ∑ α ∈ B, (finrank ℝ (E α) : ℤ))
    refine (F.map_comp _ _).symm.trans (Eq.trans ?_ (F.map_comp _ _))
    rw [deformationPairRestriction_comp_deformationPairArrow]

variable {𝒜 k} {I I' I'' J J' J'' B : Finset A}

/-- The component at `K` of the comparison of partial virtual complexes is the map of invariant
relative chains induced by the comparison of the deformation pairs of `K`. -/
theorem partialVirtualComplexMap_app (hII' : I ⊆ I') (hI'J' : I' ⊆ J') (hJ'J : J' ⊆ J)
    (hJB : J ⊆ B) (K : (Compacts (TopCat.of X))ᵒᵖ) :
    (𝒜.partialVirtualComplexMap k hII' hI'J' hJ'J hJB).app K =
      (invariantChainsFunctor ρ k B _).map (𝒜.deformationPairArrow hII' hI'J' hJ'J hJB K.unop) :=
  (rfl)

/-- The comparison of a partial virtual complex with itself is the identity. -/
@[simp]
theorem partialVirtualComplexMap_self (hIJ : I ⊆ J) (hJB : J ⊆ B) :
    𝒜.partialVirtualComplexMap k subset_rfl hIJ subset_rfl hJB = 𝟙 _ := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  rw [partialVirtualComplexMap_app, NatTrans.id_app, deformationPairArrow_self]
  exact CategoryTheory.Functor.map_id _ _

/-- Comparisons of partial virtual complexes compose. -/
@[reassoc (attr := simp)]
theorem partialVirtualComplexMap_comp_partialVirtualComplexMap (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hI'I'' : I' ⊆ I'') (hI''J'' : I'' ⊆ J'') (hJ''J' : J'' ⊆ J')
    (hJB : J ⊆ B) :
    𝒜.partialVirtualComplexMap k hII' hI'J' hJ'J hJB ≫
        𝒜.partialVirtualComplexMap k hI'I'' hI''J'' hJ''J' (hJ'J.trans hJB) =
      𝒜.partialVirtualComplexMap k (hII'.trans hI'I'') hI''J'' (hJ''J'.trans hJ'J) hJB := by
  refine NatTrans.ext (funext fun K ↦ ?_)
  refine ((invariantChainsFunctor ρ k B _).map_comp _ _).symm.trans ?_
  rw [deformationPairArrow_comp_deformationPairArrow, partialVirtualComplexMap_app]

end Complexes

/-! ### The weighted interval arrows -/

section Arrows

variable (k : Type u) [CommRing k] (hΓ : ∀ α, IsUnit (Nat.card (Γ α) : k))

/-- **The interval arrow** `R_IJ ⟶ R_I'J'` of the partial virtual complexes, for
`I ⊆ I' ⊆ J' ⊆ J ⊆ B` (Pardon, Definition 4.2.6): the comparison induced by the comparison maps
of the deformation pairs, multiplied by `|Γ_(J ∖ J')|⁻¹ = ∏_(α ∈ J ∖ J') |Γ_α|⁻¹`, for coefficients
in a commutative ring `k` in which the orders `|Γ_α|` of the isotropy groups are units (`hΓ`), as in
a field of characteristic zero. -/
def partialVirtualComplexArrow {I I' J J' B : Finset A} (hII' : I ⊆ I') (hI'J' : I' ⊆ J')
    (hJ'J : J' ⊆ J) (hJB : J ⊆ B) :
    𝒜.partialVirtualComplex k I hJB ⟶ 𝒜.partialVirtualComplex k I' (hJ'J.trans hJB) :=
  (↑(∏ α ∈ J \ J', (hΓ α).unit)⁻¹ : k) • 𝒜.partialVirtualComplexMap k hII' hI'J' hJ'J hJB

variable {𝒜 k} {I I' I'' J J' J'' B : Finset A}

/-- The interval arrow is the weighted comparison of partial virtual complexes. -/
theorem partialVirtualComplexArrow_def (hII' : I ⊆ I') (hI'J' : I' ⊆ J') (hJ'J : J' ⊆ J)
    (hJB : J ⊆ B) :
    𝒜.partialVirtualComplexArrow k hΓ hII' hI'J' hJ'J hJB =
      (↑(∏ α ∈ J \ J', (hΓ α).unit)⁻¹ : k) • 𝒜.partialVirtualComplexMap k hII' hI'J' hJ'J hJB :=
  (rfl)

/-- **The interval arrow of an interval to itself is the identity**: its weight is
`|Γ_∅|⁻¹ = 1`. -/
@[simp]
theorem partialVirtualComplexArrow_self (hIJ : I ⊆ J) (hJB : J ⊆ B) :
    𝒜.partialVirtualComplexArrow k hΓ subset_rfl hIJ subset_rfl hJB = 𝟙 _ := by
  rw [partialVirtualComplexArrow_def, Finset.sdiff_self, Finset.prod_empty, inv_one,
    Units.val_one, one_smul, partialVirtualComplexMap_self]

/-- **The interval arrows compose**, for `I ⊆ I' ⊆ I'' ⊆ J'' ⊆ J' ⊆ J ⊆ B`: the comparisons
compose, and the weights multiply, since `J ∖ J''` is the disjoint union of `J ∖ J'` and
`J' ∖ J''`, so that `|Γ_(J ∖ J')| |Γ_(J' ∖ J'')| = |Γ_(J ∖ J'')|`. -/
@[reassoc (attr := simp)]
theorem partialVirtualComplexArrow_comp_partialVirtualComplexArrow (hII' : I ⊆ I')
    (hI'J' : I' ⊆ J') (hJ'J : J' ⊆ J) (hI'I'' : I' ⊆ I'') (hI''J'' : I'' ⊆ J'')
    (hJ''J' : J'' ⊆ J') (hJB : J ⊆ B) :
    𝒜.partialVirtualComplexArrow k hΓ hII' hI'J' hJ'J hJB ≫
        𝒜.partialVirtualComplexArrow k hΓ hI'I'' hI''J'' hJ''J' (hJ'J.trans hJB) =
      𝒜.partialVirtualComplexArrow k hΓ (hII'.trans hI'I'') hI''J'' (hJ''J'.trans hJ'J) hJB := by
  rw [partialVirtualComplexArrow_def, partialVirtualComplexArrow_def,
    partialVirtualComplexArrow_def, Linear.smul_comp, Linear.comp_smul, smul_smul,
    partialVirtualComplexMap_comp_partialVirtualComplexMap, ← Units.val_mul, ← mul_inv,
    ← Finset.prod_union (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset),
    Finset.sdiff_union_sdiff_cancel hJ'J hJ''J']

variable (𝒜 k) in
/-- **The interval diagram of partial virtual complexes** of a finite set `B` of indices (Pardon,
Definition 4.2.6): the partial virtual complex `R_IJ` on each interval `I ⊆ J` of subsets of `B`,
and the weighted interval arrow `R_IJ ⟶ R_I'J'` on each inclusion of intervals
`I ⊆ I' ⊆ J' ⊆ J`. Its flag total (`TauCeti.IntervalDiagram.total`) is the virtual cochain
complex of the atlas. -/
-- The body is exposed so that the values are definitionally the partial virtual complexes: the
-- statement of `partialVirtualDiagram_map`, a map between values, typechecks only then.
@[expose]
def partialVirtualDiagram (B : Finset A) :
    IntervalDiagram (Set.Iic B)
      (TopCat.KPresheaf (CochainComplex (ModuleCat.{u} k) ℤ) (TopCat.of X)) where
  obj x := 𝒜.partialVirtualComplex k x.unop.fst.val x.unop.snd.property
  map {x y} f := 𝒜.partialVirtualComplexArrow k hΓ (NonemptyInterval.le_def.1 (leOfHom f.unop)).1
    y.unop.fst_le_snd (NonemptyInterval.le_def.1 (leOfHom f.unop)).2 x.unop.snd.property
  map_id _ := partialVirtualComplexArrow_self hΓ _ _
  map_comp _ _ :=
    (partialVirtualComplexArrow_comp_partialVirtualComplexArrow hΓ _ _ _ _ _ _ _).symm

/-- The value of the interval diagram on an interval `I ⊆ J` of subsets of `B` is the partial
virtual complex `R_IJ`. -/
@[simp]
theorem partialVirtualDiagram_obj (B : Finset A) (x : (NonemptyInterval (Set.Iic B))ᵒᵖ) :
    (𝒜.partialVirtualDiagram k hΓ B).obj x =
      𝒜.partialVirtualComplex k x.unop.fst.val x.unop.snd.property :=
  (rfl)

/-- The arrows of the interval diagram are the weighted interval arrows. -/
theorem partialVirtualDiagram_map (B : Finset A) {x y : (NonemptyInterval (Set.Iic B))ᵒᵖ}
    (f : x ⟶ y) :
    (𝒜.partialVirtualDiagram k hΓ B).map f =
      𝒜.partialVirtualComplexArrow k hΓ (NonemptyInterval.le_def.1 (leOfHom f.unop)).1
        y.unop.fst_le_snd (NonemptyInterval.le_def.1 (leOfHom f.unop)).2 x.unop.snd.property :=
  (rfl)

end Arrows

end TauCeti.ImplicitAtlas
