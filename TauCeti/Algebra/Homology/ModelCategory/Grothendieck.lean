/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModelCategory.KInjective.ModelStructure

import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import TauCeti.Algebra.Homology.Adjunction
import TauCeti.CategoryTheory.Abelian.GrothendieckCategory.SmallObjectArgument

/-!
# Cardinal-controlled fibrant replacement and Quillen functoriality on unbounded complexes

Building on the injective model structure `CochainComplex.modelCategoryInjective` on
`CochainComplex C ℤ` established in
`TauCeti.Algebra.Homology.ModelCategory.KInjective.ModelStructure`, this file provides:

1. **Additional characterizations in any abelian category `C`**: explicit description of trivial
   fibrations as degreewise epimorphisms whose kernel is degreewise injective, K-injective, and
   acyclic (`CochainComplex.modelCategoryInjective.trivialFibration_iff`), and identification of
   weak equivalences between K-injective complexes with chain homotopy equivalences
   (`CochainComplex.modelCategoryInjective.weakEquivalence_iff_homotopyEquivalences`).
2. **Cardinal-controlled combinatorial generation and relative-cell fibrant replacement** when `C`
   is Grothendieck abelian (`IsGrothendieckAbelian.{w} C`): functorial factorizations on both
   `(trivialCofibrations, fibrations)` and `(cofibrations, trivialFibrations)`, explicit `w`-small
   generating families `generatingCofibrations C` and `generatingTrivialCofibrations C`, a single
   regular cardinal `injectiveModelCardinal C` bounding the subobject lattices of all sources and
   targets in both generating sets and suitable for Quillen's small object argument on both, and
   the resulting cardinal-controlled functorial fibrant replacement `fibrantReplacement C` whose
   unit components `(ιFibrantReplacement C).app K` carry the explicit transfinite
   `RelativeCellComplex` witness `relativeCellComplexιFibrantReplacementApp K` of length
   `(injectiveModelCardinal C).ord.ToType` (complementing `TauCeti.injectiveReplacement`, which
   uses the existential `HasFunctorialFactorization` without cardinal or cell-complex data).
3. **Quillen functoriality along exact functors and adjunctions**: exact additive functors preserve
   cofibrations and weak equivalences, arbitrary additive functors preserve weak equivalences
   between K-injective complexes, and the right adjoint of a finite-limit-preserving functor
   between abelian categories preserves fibrations, trivial fibrations, and fibrant complexes
   (`CategoryTheory.Adjunction.fibration_mapHomologicalComplex_map`,
   `CategoryTheory.Adjunction.isFibrant_mapHomologicalComplex_obj`).

## References

* J. Lurie, *Higher Algebra*, Proposition 1.3.5.3 and Remark 1.3.5.4.
* [Stacks: Theorem 079P](https://stacks.math.columbia.edu/tag/079P).
* M. Hovey, *Model categories*, Mathematical Surveys and Monographs 63 (1999), §2.3.
-/

public section

universe w v u v' u'

open CategoryTheory HomotopicalAlgebra Limits MorphismProperty ZeroObject

namespace CochainComplex.modelCategoryInjective

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma mem_trivialCofibrations_iff' {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    trivialCofibrations (CochainComplex C ℤ) f ↔ Mono f ∧ QuasiIso f := by
  rw [mem_trivialCofibrations_iff, cofibration_iff, weakEquivalence_iff]

/-- A morphism of unbounded cochain complexes is both a fibration and a weak equivalence if and
only if it has the right lifting property against all monomorphisms. -/
theorem fibration_and_weakEquivalence_iff_rlp_monomorphisms {K L : CochainComplex C ℤ}
    (p : K ⟶ L) :
    Fibration p ∧ WeakEquivalence p ↔ (monomorphisms (CochainComplex C ℤ)).rlp p := by
  rw [← mem_trivialFibrations_iff, trivialFibrations_eq]

/-- A morphism of unbounded cochain complexes is a trivial fibration if and only if it is
degreewise epimorphic and its kernel is degreewise injective, K-injective, and acyclic. -/
theorem trivialFibration_iff {K L : CochainComplex C ℤ} (p : K ⟶ L) :
    Fibration p ∧ WeakEquivalence p ↔
      degreewiseEpiWithInjectiveKernel p ∧ (kernel p).IsKInjective ∧ (kernel p).Acyclic := by
  rw [fibration_and_weakEquivalence_iff_rlp_monomorphisms, rlp_monomorphisms_iff]

lemma injective_X_of_isFibrant {K : CochainComplex C ℤ} [IsFibrant K] (n : ℤ) :
    Injective (K.X n) :=
  ((isFibrant_iff K).1 ‹_›).1 n

lemma isKInjective_of_isFibrant {K : CochainComplex C ℤ} [IsFibrant K] : K.IsKInjective :=
  ((isFibrant_iff K).1 ‹_›).2

/-- Weak equivalences between K-injective (in particular, fibrant) cochain complexes are precisely
chain homotopy equivalences. -/
theorem weakEquivalence_iff_homotopyEquivalences {K L : CochainComplex C ℤ}
    [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    WeakEquivalence f ↔ HomologicalComplex.homotopyEquivalences C (.up ℤ) f := by
  rw [weakEquivalence_iff, IsKInjective.quasiIso_iff]

end Abelian

section Grothendieck

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

scoped instance : HasFunctorialFactorization
    (trivialCofibrations (CochainComplex C ℤ)) (fibrations (CochainComplex C ℤ)) := by
  rw [trivialCofibrations_eq, fibrations_eq]
  infer_instance

scoped instance : HasFunctorialFactorization
    (cofibrations (CochainComplex C ℤ)) (trivialFibrations (CochainComplex C ℤ)) := by
  rw [cofibrations_eq, trivialFibrations_eq]
  infer_instance

/-- A `w`-small set of generating cofibrations for `CochainComplex C ℤ`, given by the inclusions
of subcomplexes of the chosen separator of `CochainComplex C ℤ`. -/
def generatingCofibrations : MorphismProperty (CochainComplex C ℤ) :=
  IsGrothendieckAbelian.generatingMonomorphisms (separator (CochainComplex C ℤ))

instance : IsSmall.{w} (generatingCofibrations C) := by
  dsimp only [generatingCofibrations]
  infer_instance

lemma generatingCofibrations_le_cofibrations :
    generatingCofibrations C ≤ cofibrations (CochainComplex C ℤ) :=
  IsGrothendieckAbelian.generatingMonomorphisms_le_monomorphisms _

/-- The morphisms with the right lifting property against `generatingCofibrations C` are the
trivial fibrations. -/
@[simp]
theorem generatingCofibrations_rlp :
    (generatingCofibrations C).rlp = trivialFibrations (CochainComplex C ℤ) := by
  rw [generatingCofibrations,
    IsGrothendieckAbelian.generatingMonomorphisms_rlp (isSeparator_separator (CochainComplex C ℤ)),
    trivialFibrations_eq]

/-- The morphisms with the left lifting property against `(generatingCofibrations C).rlp` are the
cofibrations. -/
theorem generatingCofibrations_rlp_llp :
    (generatingCofibrations C).rlp.llp = cofibrations (CochainComplex C ℤ) := by
  rw [generatingCofibrations,
    IsGrothendieckAbelian.generatingMonomorphisms_rlp (isSeparator_separator (CochainComplex C ℤ)),
    IsGrothendieckAbelian.llp_rlp_monomorphisms (isSeparator_separator (CochainComplex C ℤ)),
    cofibrations_eq]

/-- A `w`-small set of generating trivial cofibrations for `CochainComplex C ℤ` whose right
lifting property characterizes fibrations. -/
noncomputable def generatingTrivialCofibrations : MorphismProperty (CochainComplex C ℤ) :=
  (exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)).choose

instance : IsSmall.{w} (generatingTrivialCofibrations.{w} C) :=
  (exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)).choose_spec.1

lemma generatingTrivialCofibrations_le_trivialCofibrations :
    generatingTrivialCofibrations.{w} C ≤ trivialCofibrations (CochainComplex C ℤ) :=
  (exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)).choose_spec.2.1

lemma generatingTrivialCofibrations_le_cofibrations :
    generatingTrivialCofibrations.{w} C ≤ cofibrations (CochainComplex C ℤ) :=
  (generatingTrivialCofibrations_le_trivialCofibrations.{w} C).trans
    (trivialCofibrations_sub_cofibrations _)

/-- The morphisms with the right lifting property against `generatingTrivialCofibrations C` are the
fibrations. -/
@[simp]
theorem generatingTrivialCofibrations_rlp :
    (generatingTrivialCofibrations.{w} C).rlp = fibrations (CochainComplex C ℤ) :=
  (exists_isSmall_le_monomorphisms_inf_quasiIso_and_rlp_eq.{w} (C := C)).choose_spec.2.2

/-- The morphisms with the left lifting property against `(generatingTrivialCofibrations C).rlp`
are the trivial cofibrations. -/
theorem generatingTrivialCofibrations_rlp_llp :
    (generatingTrivialCofibrations.{w} C).rlp.llp = trivialCofibrations (CochainComplex C ℤ) := by
  rw [generatingTrivialCofibrations_rlp, fibrations_eq, llp_rlp_monomorphisms_inf_quasiIso.{w},
    trivialCofibrations_eq]

/-- Auxiliary index type covering both endpoints of all morphisms in `generatingCofibrations C`
and `generatingTrivialCofibrations C`. -/
private abbrev GeneratingEndpointSubobjects :
    (ULift.{w} Bool × (generatingCofibrations C).toSet) ⊕
      (ULift.{w} Bool × (generatingTrivialCofibrations.{w} C).toSet) → Type _ :=
  Sum.elim
    (fun ⟨b, f⟩ ↦ b.down.casesOn (Subobject f.val.right) (Subobject f.val.left))
    (fun ⟨b, f⟩ ↦ b.down.casesOn (Subobject f.val.right) (Subobject f.val.left))

private lemma exists_injectiveModelCardinal :
    ∃ κ : Cardinal.{w}, κ.IsRegular ∧
      ∀ i, HasCardinalLT (GeneratingEndpointSubobjects.{w} C i) κ := by
  have : ∀ i, Small.{w} (GeneratingEndpointSubobjects.{w} C i) := by
    rintro (⟨⟨_ | _⟩, _⟩ | ⟨⟨_ | _⟩, _⟩) <;> dsimp [GeneratingEndpointSubobjects] <;> infer_instance
  exact HasCardinalLT.exists_regular_cardinal_forall.{w} (GeneratingEndpointSubobjects.{w} C)

/-- A regular cardinal `κ : Cardinal.{w}` bounding the subobject lattices of all sources and
targets in both `generatingCofibrations C` and `generatingTrivialCofibrations C`, and suitable for
Quillen's small object argument on both generating sets. -/
noncomputable def injectiveModelCardinal : Cardinal.{w} :=
  (exists_injectiveModelCardinal.{w} C).choose

lemma isRegular_injectiveModelCardinal : (injectiveModelCardinal.{w} C).IsRegular :=
  (exists_injectiveModelCardinal.{w} C).choose_spec.1

instance : Fact (injectiveModelCardinal.{w} C).IsRegular :=
  ⟨isRegular_injectiveModelCardinal.{w} C⟩

noncomputable instance : OrderBot (injectiveModelCardinal.{w} C).ord.ToType := by
  have : Nonempty (injectiveModelCardinal.{w} C).ord.ToType := by
    simpa using (isRegular_injectiveModelCardinal.{w} C).ne_zero
  exact WellFoundedLT.toOrderBot _

/-- Sources of morphisms in `generatingCofibrations C` have fewer than `injectiveModelCardinal C`
subobjects. -/
theorem hasCardinalLT_subobject_left_of_generatingCofibrations
    {A B : CochainComplex C ℤ} (i : A ⟶ B) (hi : generatingCofibrations C i) :
    HasCardinalLT (Subobject A) (injectiveModelCardinal.{w} C) :=
  (exists_injectiveModelCardinal.{w} C).choose_spec.2 (Sum.inl ⟨.up true, ⟨Arrow.mk i, hi⟩⟩)

/-- Targets of morphisms in `generatingCofibrations C` have fewer than `injectiveModelCardinal C`
subobjects. -/
theorem hasCardinalLT_subobject_right_of_generatingCofibrations
    {A B : CochainComplex C ℤ} (i : A ⟶ B) (hi : generatingCofibrations C i) :
    HasCardinalLT (Subobject B) (injectiveModelCardinal.{w} C) :=
  (exists_injectiveModelCardinal.{w} C).choose_spec.2 (Sum.inl ⟨.up false, ⟨Arrow.mk i, hi⟩⟩)

/-- Sources of morphisms in `generatingTrivialCofibrations C` have fewer than
`injectiveModelCardinal C` subobjects. -/
theorem hasCardinalLT_subobject_left_of_generatingTrivialCofibrations
    {A B : CochainComplex C ℤ} (i : A ⟶ B) (hi : generatingTrivialCofibrations.{w} C i) :
    HasCardinalLT (Subobject A) (injectiveModelCardinal.{w} C) :=
  (exists_injectiveModelCardinal.{w} C).choose_spec.2 (Sum.inr ⟨.up true, ⟨Arrow.mk i, hi⟩⟩)

/-- Targets of morphisms in `generatingTrivialCofibrations C` have fewer than
`injectiveModelCardinal C` subobjects. -/
theorem hasCardinalLT_subobject_right_of_generatingTrivialCofibrations
    {A B : CochainComplex C ℤ} (i : A ⟶ B) (hi : generatingTrivialCofibrations.{w} C i) :
    HasCardinalLT (Subobject B) (injectiveModelCardinal.{w} C) :=
  (exists_injectiveModelCardinal.{w} C).choose_spec.2 (Sum.inr ⟨.up false, ⟨Arrow.mk i, hi⟩⟩)

instance : IsCardinalForSmallObjectArgument.{w}
    (generatingCofibrations C) (injectiveModelCardinal.{w} C) :=
  IsGrothendieckAbelian.isCardinalForSmallObjectArgument_of_le_monomorphisms
    (generatingCofibrations C) (generatingCofibrations_le_cofibrations C)
    (injectiveModelCardinal.{w} C) fun _ _ i hi ↦
      hasCardinalLT_subobject_left_of_generatingCofibrations C i hi

instance : IsCardinalForSmallObjectArgument.{w}
    (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C) :=
  IsGrothendieckAbelian.isCardinalForSmallObjectArgument_of_le_monomorphisms
    (generatingTrivialCofibrations.{w} C) (generatingTrivialCofibrations_le_cofibrations.{w} C)
    (injectiveModelCardinal.{w} C) fun _ _ i hi ↦
      hasCardinalLT_subobject_left_of_generatingTrivialCofibrations C i hi

/-- The functorial embedding of `CochainComplex C ℤ` into `Arrow (CochainComplex C ℤ)` sending a
complex `K` to `0 : K ⟶ 0`. -/
@[simps]
private noncomputable def toZeroArrow : CochainComplex C ℤ ⥤ Arrow (CochainComplex C ℤ) where
  obj K := Arrow.mk (0 : K ⟶ 0)
  map φ := Arrow.homMk φ 0

/-- Functorial fibrant replacement on `CochainComplex C ℤ` obtained by applying the small object
argument for `generatingTrivialCofibrations C` at the cardinal `injectiveModelCardinal C` to
`0 : K ⟶ 0`. -/
noncomputable def fibrantReplacement : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  toZeroArrow C ⋙
    (SmallObject.functorialFactorizationData
      (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C)).Z

/-- The functorial monomorphic quasi-isomorphism `K ⟶ (fibrantReplacement C).obj K`. -/
noncomputable def ιFibrantReplacement : 𝟭 (CochainComplex C ℤ) ⟶ fibrantReplacement.{w} C :=
  Functor.whiskerLeft (toZeroArrow C)
    (SmallObject.functorialFactorizationData
      (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C)).i

/-- Each component `(ιFibrantReplacement C).app K` is a relative cell complex indexed by
`(injectiveModelCardinal C).ord.ToType` for `generatingTrivialCofibrations C`. -/
noncomputable def relativeCellComplexιFibrantReplacementApp (K : CochainComplex C ℤ) :
    RelativeCellComplex.{w}
      (fun _ : (injectiveModelCardinal.{w} C).ord.ToType ↦
        (generatingTrivialCofibrations.{w} C).homFamily)
      ((ιFibrantReplacement.{w} C).app K) :=
  SmallObject.relativeCellComplexιObj
    (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C) (0 : K ⟶ 0)

private lemma mem_trivialCofibrations_ιFibrantReplacement_app (K : CochainComplex C ℤ) :
    trivialCofibrations (CochainComplex C ℤ) ((ιFibrantReplacement.{w} C).app K) := by
  rw [← generatingTrivialCofibrations_rlp_llp.{w} C]
  exact (SmallObject.functorialFactorizationData
    (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C)).hi
    (Arrow.mk (0 : K ⟶ 0))

instance (K : CochainComplex C ℤ) : Cofibration ((ιFibrantReplacement.{w} C).app K) :=
  (mem_trivialCofibrations_iff _).1 (mem_trivialCofibrations_ιFibrantReplacement_app C K) |>.1

instance (K : CochainComplex C ℤ) : Mono ((ιFibrantReplacement.{w} C).app K) :=
  inferInstance

instance (K : CochainComplex C ℤ) : WeakEquivalence ((ιFibrantReplacement.{w} C).app K) :=
  (mem_trivialCofibrations_iff _).1 (mem_trivialCofibrations_ιFibrantReplacement_app C K) |>.2

instance (K : CochainComplex C ℤ) : QuasiIso ((ιFibrantReplacement.{w} C).app K) :=
  inferInstance

instance (K : CochainComplex C ℤ) : IsFibrant ((fibrantReplacement.{w} C).obj K) := by
  dsimp only [fibrantReplacement, Functor.comp_obj, toZeroArrow]
  rw [isFibrant_iff_of_isTerminal
    ((SmallObject.functorialFactorizationData
      (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C)).p.app
      (Arrow.mk (0 : K ⟶ 0))) (isZero_zero _).isTerminal,
    HomotopicalAlgebra.fibration_iff, ← generatingTrivialCofibrations_rlp.{w} C]
  exact (SmallObject.functorialFactorizationData
    (generatingTrivialCofibrations.{w} C) (injectiveModelCardinal.{w} C)).hp
    (Arrow.mk (0 : K ⟶ 0))

instance (K : CochainComplex C ℤ) (n : ℤ) :
    Injective (((fibrantReplacement.{w} C).obj K).X n) :=
  injective_X_of_isFibrant n

instance (K : CochainComplex C ℤ) : ((fibrantReplacement.{w} C).obj K).IsKInjective :=
  isKInjective_of_isFibrant

end Grothendieck

end CochainComplex.modelCategoryInjective

/-! ### Functoriality along exact functors and Quillen adjunctions -/

namespace CategoryTheory

open scoped CochainComplex.modelCategoryInjective

section Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- An exact additive functor between abelian categories preserves cofibrations of unbounded
cochain complexes in the injective model structure. -/
theorem Functor.cofibration_mapHomologicalComplex_map (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] {K L : CochainComplex C ℤ} (i : K ⟶ L) [Cofibration i] :
    Cofibration (C := CochainComplex D ℤ) ((F.mapHomologicalComplex (.up ℤ)).map i) := by
  have := F.preservesFiniteLimits_of_preservesHomology
  rw [CochainComplex.modelCategoryInjective.cofibration_iff]
  infer_instance

/-- An exact additive functor between abelian categories preserves weak equivalences of unbounded
cochain complexes in the injective model structure. -/
theorem Functor.weakEquivalence_mapHomologicalComplex_map (F : C ⥤ D) [F.Additive]
    [F.PreservesHomology] {K L : CochainComplex C ℤ} (f : K ⟶ L) [WeakEquivalence f] :
    WeakEquivalence (C := CochainComplex D ℤ) ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  rw [CochainComplex.modelCategoryInjective.weakEquivalence_iff]
  infer_instance

/-- Any additive functor between abelian categories preserves weak equivalences between K-injective
(and hence between fibrant) cochain complexes, because such weak equivalences are homotopy
equivalences. -/
theorem Functor.weakEquivalence_mapHomologicalComplex_map_of_isKInjective (G : D ⥤ C)
    [G.Additive] {K L : CochainComplex D ℤ} [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L)
    [WeakEquivalence f] :
    WeakEquivalence (C := CochainComplex C ℤ) ((G.mapHomologicalComplex (.up ℤ)).map f) := by
  obtain ⟨e, rfl⟩ := (CochainComplex.IsKInjective.quasiIso_iff f).1 inferInstance
  rw [CochainComplex.modelCategoryInjective.weakEquivalence_iff]
  exact (G.mapHomotopyEquiv e).quasiIso_hom

end Functor

section Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {F : C ⥤ D} {G : D ⥤ C}

/-- If `F ⊣ G` is an adjunction between abelian categories whose left adjoint `F` preserves finite
limits, then `G` induces a functor on unbounded cochain complexes that preserves fibrations for the
injective model structure. -/
theorem Adjunction.fibration_mapHomologicalComplex_map (adj : F ⊣ G)
    [G.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    {X Y : CochainComplex D ℤ} (p : X ⟶ Y) [Fibration p] :
    Fibration (C := CochainComplex C ℤ) ((G.mapHomologicalComplex (.up ℤ)).map p) := by
  have : F.Additive := F.additive_of_preserves_binary_products
  have := adj.leftAdjoint_preservesColimits.{0, 0}
  have := F.preservesHomologyOfExact
  rw [HomotopicalAlgebra.fibration_iff, CochainComplex.modelCategoryInjective.fibrations_eq]
  intro A B i ⟨hi₁, hi₂⟩
  rw [← (adj.mapHomologicalComplex (.up ℤ)).hasLiftingProperty_iff]
  have : Mono i := hi₁
  have : QuasiIso i := hi₂
  exact (HomotopicalAlgebra.fibration_iff p).1 inferInstance
    ((F.mapHomologicalComplex (.up ℤ)).map i)
    ⟨inferInstance, (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance⟩

/-- Under the hypotheses of `Adjunction.fibration_mapHomologicalComplex_map`, `G` also preserves
trivial fibrations of unbounded cochain complexes. -/
theorem Adjunction.weakEquivalence_mapHomologicalComplex_map_of_fibration (adj : F ⊣ G)
    [G.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    {X Y : CochainComplex D ℤ} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p] :
    WeakEquivalence (C := CochainComplex C ℤ) ((G.mapHomologicalComplex (.up ℤ)).map p) := by
  have : F.Additive := F.additive_of_preserves_binary_products
  have hp : (monomorphisms (CochainComplex C ℤ)).rlp ((G.mapHomologicalComplex (.up ℤ)).map p) := by
    intro A B i hi
    rw [← (adj.mapHomologicalComplex (.up ℤ)).hasLiftingProperty_iff]
    have : Mono i := hi
    have hp' :=
      (CochainComplex.modelCategoryInjective.fibration_and_weakEquivalence_iff_rlp_monomorphisms
        p).1 ⟨inferInstance, inferInstance⟩
    exact hp' ((F.mapHomologicalComplex (.up ℤ)).map i) inferInstance
  exact ((CochainComplex.modelCategoryInjective.fibration_and_weakEquivalence_iff_rlp_monomorphisms
    (C := C) ((G.mapHomologicalComplex (.up ℤ)).map p)).2 hp).2

/-- If `F ⊣ G` is an adjunction between abelian categories whose left adjoint `F` preserves finite
limits, then `G` sends fibrant cochain complexes to fibrant cochain complexes. -/
theorem Adjunction.isFibrant_mapHomologicalComplex_obj (adj : F ⊣ G)
    [G.PreservesZeroMorphisms] [PreservesFiniteLimits F]
    (X : CochainComplex D ℤ) [IsFibrant X] :
    IsFibrant (C := CochainComplex C ℤ) ((G.mapHomologicalComplex (.up ℤ)).obj X) := by
  have hZ : IsTerminal (((G.mapHomologicalComplex (.up ℤ)).obj (0 : CochainComplex D ℤ)) :
      CochainComplex C ℤ) :=
    ((G.mapHomologicalComplex (.up ℤ)).map_isZero (isZero_zero _)).isTerminal
  have : Fibration (0 : X ⟶ 0) :=
    (isFibrant_iff_of_isTerminal (0 : X ⟶ 0) (isZero_zero _).isTerminal).1 inferInstance
  rw [isFibrant_iff_of_isTerminal (C := CochainComplex C ℤ)
    ((G.mapHomologicalComplex (.up ℤ)).map (0 : X ⟶ 0)) hZ]
  exact adj.fibration_mapHomologicalComplex_map (0 : X ⟶ 0)

end Adjunction

end CategoryTheory
