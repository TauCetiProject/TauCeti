/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Abelian.Refinements
import TauCeti.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import TauCeti.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.ExactColimits

/-!
# K-flat resolutions of unbounded complexes

Let `C` be an abelian monoidal category in which every object is a quotient of a flat object,
and in which countable coproducts and sequential colimits are exact and commute with tensor
products. Then every cochain complex `K` in `C`, without any boundedness assumption, receives a
quasi-isomorphism from a K-flat complex (`CochainComplex.exists_quasiIso_isKFlat`). In
particular every complex of modules over a commutative ring has a K-flat resolution
(`CochainComplex.exists_quasiIso_isKFlat_moduleCat`). These resolutions compute derived tensor
products of unbounded complexes.

The resolution is built by attaching cells. Start with a complex `P₀` with zero differentials,
whose term in degree `n` is a flat object mapping onto the cycles of `K` in degree `n`; the map
`P₀ ⟶ K` is surjective on cohomology. Given `f : P ⟶ K`, let `W n` be the object of pairs
`(c, b)` of a cycle `c` of `P` in degree `n` and an element `b` of `K` in degree `n - 1` with
`f c = d b`, the pullback of `cyclesMap f n` along `K.toCycles (n - 1) n`. Choose flat objects
`E n` mapping onto `W n` and let `φ` map the complex `E` with zero differentials to `P` through
the first component. The components `b` form a null-homotopy of `φ ≫ f`, so `f` extends to the
mapping cone of `φ`, and every cohomology class of `P` which `f` sends to zero dies in the
cone. The cone is an extension of the shift of `E` by `P`, split in each degree, so it is
again K-flat. The colimit of the resulting sequence is K-flat, and its map to `K` is a
quasi-isomorphism because cohomology commutes with sequential colimits.

Given morphisms `p X : E X ⟶ X` for all objects `X`, this colimit is
`CochainComplex.kFlatResolution`, with the morphism `CochainComplex.kFlatResolution.π` to `K`. It
is a quasi-isomorphism when every `p X` is an epimorphism and sequential colimits are exact, and
the colimit is K-flat when every `E X` is flat and the exactness conditions above hold. Every
term of every stage is built from the objects `E X` by binary biproducts
(`CochainComplex.kFlatResolution.prop_sequence_obj_X`), so the terms of the colimit are flat
when every `E X` is flat
(`CochainComplex.preservesFiniteLimits_tensorLeft_kFlatResolution_X`). The stages, their
transition maps and their morphisms to `K` are computed by
`CochainComplex.kFlatResolution.sequence_obj_succ`,
`CochainComplex.kFlatResolution.sequence_map_succ` and
`CochainComplex.kFlatResolution.toComplex_app_succ`, in terms of the public cell-attachment step
`CochainComplex.kFlatResolution.attachingMap` and `CochainComplex.kFlatResolution.attachDesc`.
When `E : C ⥤ C` is a functor and `p : E ⟶ 𝟭 C` is a natural transformation (without requiring
`E` to be additive), the cell attachments and colimit assemble into a resolution functor
`CochainComplex.kFlatResolutionFunctor` with augmentation
`CochainComplex.kFlatResolution.πNatTrans`.

## References

* N. Spaltenstein, *Resolutions of unbounded complexes*, Compositio Math. 65 (1988), 121–154,
  where K-flat complexes and resolutions of unbounded complexes are introduced.
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes.
* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace CochainComplex

open HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace kFlatResolution

section Step

variable {P K : CochainComplex C ℤ} (f : P ⟶ K)

/-- The cycles of `P` in degree `n` whose image under `f` is a boundary, together with a
primitive of that image. -/
public abbrev boundaryPairs {P K : CochainComplex C ℤ} (f : P ⟶ K) (n : ℤ) : C :=
  pullback (cyclesMap f n) (K.toCycles (n - 1) n)

variable {E : ℤ → C} (e : ∀ n, E n ⟶ boundaryPairs f n)

/-- The cells attached to `P`: the cycle components of the pairs parametrized by `E`. -/
public abbrev attachingMap {P K : CochainComplex C ℤ} (f : P ⟶ K) {E : ℤ → C}
    (e : ∀ n, E n ⟶ boundaryPairs f n) : graded (.up ℤ) E ⟶ P :=
  P.fromGraded fun n ↦ e n ≫ pullback.fst _ _

/-- The boundary components of the pairs parametrized by `E`, a null-homotopy of
`attachingMap f e ≫ f`. -/
public abbrev boundaryPrimitive {P K : CochainComplex C ℤ} (f : P ⟶ K) {E : ℤ → C}
    (e : ∀ n, E n ⟶ boundaryPairs f n) : Cochain (graded (.up ℤ) E) K (-1) :=
  Cochain.mk fun p q hpq ↦ e p ≫ pullback.snd _ _ ≫ (K.XIsoOfEq (by lia)).hom

/-- The boundary components form a null-homotopy of `attachingMap f e ≫ f`. -/
public lemma δ_boundaryPrimitive :
    δ (-1) 0 (boundaryPrimitive f e) = Cochain.ofHom (attachingMap f e ≫ f) := by
  ext p
  rw [δ_v (-1) 0 (neg_add_cancel 1) _ p p (add_zero p) (p - 1) (p + 1) (by lia) rfl]
  simp only [Cochain.mk_v, XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id, zero_comp,
    smul_zero, add_zero, Cochain.ofHom_v, comp_f, Category.assoc]
  rw [← K.toCycles_i (p - 1) p, ← pullback.condition_assoc, cyclesMap_i]

/-- The extension of `f` to the complex obtained by attaching the cells parametrized by `E`. -/
public abbrev attachDesc {P K : CochainComplex C ℤ} (f : P ⟶ K) {E : ℤ → C}
    (e : ∀ n, E n ⟶ boundaryPairs f n) : mappingCone (attachingMap f e) ⟶ K :=
  mappingCone.desc _ (boundaryPrimitive f e) f (δ_boundaryPrimitive f e)

/-- The morphism `attachDesc f e` extends `f`. -/
@[reassoc]
public lemma inr_attachDesc : mappingCone.inr (attachingMap f e) ≫ attachDesc f e = f :=
  mappingCone.inr_desc ..

/-- If every `e n` is an epimorphism, then every cohomology class of `P` that `f` sends to zero
becomes zero after attaching the cells parametrized by `E`. -/
public lemma comp_homologyMap_inr_eq_zero [∀ n, Epi (e n)] {n : ℤ} {X : C}
    (g : X ⟶ P.homology n) (hg : g ≫ homologyMap f n = 0) :
    g ≫ homologyMap (mappingCone.inr (attachingMap f e)) n = 0 := by
  -- lift `g` to cycles, then to boundary pairs, then to `E n`, up to refinements
  obtain ⟨A₁, π₁, _, x, hx⟩ := surjective_up_to_refinements_of_epi (P.homologyπ n) g
  have hS : (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ (n - 1) n)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel (n - 1) n (by simp))
  obtain ⟨A₂, π₂, _, y, hy⟩ := hS.exact_up_to_refinements (x ≫ cyclesMap f n) (by
    have := π₁ ≫= hg
    rw [reassoc_of% hx, homologyπ_naturality, comp_zero] at this
    simpa using this)
  obtain ⟨A₃, π₃, _, z, hz⟩ := surjective_up_to_refinements_of_epi (e n)
    (pullback.lift (π₂ ≫ x) y (by simpa using hy))
  -- the attached cells are null-homotopic in the mapping cone
  have hcells : homologyMap (attachingMap f e ≫ mappingCone.inr (attachingMap f e)) n = 0 := by
    rw [((Cochain.equivHomotopy _ 0).symm ⟨mappingCone.inl _, by simp⟩).homologyMap_eq,
      homologyMap_zero]
  have hzero : z ≫ e n ≫ pullback.fst _ _ ≫ P.homologyπ n ≫
      homologyMap (mappingCone.inr (attachingMap f e)) n = 0 := by
    rw [← Category.assoc (e n),
      ← P.iCyclesIso_inv_cyclesMap_fromGraded_assoc (fun n ↦ e n ≫ pullback.fst _ _) n,
      ← homologyπ_naturality_assoc, ← homologyMap_comp, hcells, comp_zero, comp_zero, comp_zero]
  have hz' : π₃ ≫ π₂ ≫ x = z ≫ e n ≫ pullback.fst _ _ := by
    simpa using hz =≫ pullback.fst _ _
  rw [← cancel_epi (π₃ ≫ π₂ ≫ π₁), comp_zero]
  simp only [Category.assoc]
  rw [reassoc_of% hx, reassoc_of% hz']
  exact hzero

end Step

section Sequence

variable (E : C → C) (p : ∀ X, E X ⟶ X) (K : CochainComplex C ℤ)

/-- The stages of the resolution, each with its morphism to `K`: first the complex with zero
differentials of the objects `E (K.cycles n)`, mapping to `K` through `p`, then repeatedly the
complex obtained by attaching cells along the morphisms `p` to the objects of pairs of a cycle
and a primitive of its image. -/
@[expose] public def stage : ℕ → Σ P : CochainComplex C ℤ, P ⟶ K
  | 0 => ⟨graded (.up ℤ) fun n ↦ E (K.cycles n), K.fromGraded fun n ↦ p (K.cycles n)⟩
  | k + 1 => ⟨mappingCone (attachingMap (stage k).2 fun n ↦ p (boundaryPairs (stage k).2 n)),
      attachDesc (stage k).2 fun n ↦ p (boundaryPairs (stage k).2 n)⟩

/-- The sequence of stages of the resolution `kFlatResolution E p K`: first the complex with
zero differentials of the objects `E (K.cycles n)`, then repeatedly the complex obtained by
attaching cells along the morphisms `p` to the objects of pairs of a cycle and a primitive of its
image in `K`. -/
@[expose] public def sequence : ℕ ⥤ CochainComplex C ℤ :=
  Functor.ofSequence (X := fun k ↦ (stage E p K k).1) fun k ↦ mappingCone.inr
    (attachingMap (stage E p K k).2 fun n ↦ p (boundaryPairs (stage E p K k).2 n))

/-- The morphisms from the stages of the resolution to `K`. -/
@[expose] public def toComplex : sequence E p K ⟶ (CategoryTheory.Functor.const ℕ).obj K :=
  NatTrans.ofSequence (fun k ↦ (stage E p K k).2) fun k ↦
    (congrArg (· ≫ _) (CategoryTheory.Functor.ofSequence_map_homOfLE_succ _ k)).trans
      ((inr_attachDesc _ _).trans (Category.comp_id _).symm)

/-- The initial stage of the resolution is the complex with zero differentials of the covers of
the cycles of `K`. -/
public lemma sequence_obj_zero :
    (sequence E p K).obj 0 = graded (.up ℤ) fun n ↦ E (K.cycles n) :=
  rfl

/-- The morphism from the initial stage of the resolution to `K` is induced by the covers of the
cycles of `K`. -/
public lemma toComplex_app_zero :
    (toComplex E p K).app 0 = K.fromGraded fun n ↦ p (K.cycles n) :=
  rfl

/-- Each stage of the resolution after the first is the mapping cone of the cells attached to
the previous stage along the covers of its boundary pairs. -/
public lemma sequence_obj_succ (k : ℕ) :
    (sequence E p K).obj (k + 1) = mappingCone (attachingMap ((toComplex E p K).app k)
      fun n ↦ p (boundaryPairs ((toComplex E p K).app k) n)) :=
  rfl

/-- The morphism from each stage of the resolution after the first to `K` extends the morphism
from the previous stage over the attached cells. -/
public lemma toComplex_app_succ (k : ℕ) :
    (toComplex E p K).app (k + 1) = attachDesc ((toComplex E p K).app k)
      fun n ↦ p (boundaryPairs ((toComplex E p K).app k) n) :=
  rfl

/-- The transition maps of the resolution are the inclusions of the stages into the mapping
cones of the attached cells. -/
public lemma sequence_map_succ (k : ℕ) :
    (sequence E p K).map (homOfLE (k.le_add_right 1)) =
      mappingCone.inr (attachingMap ((toComplex E p K).app k)
        fun n ↦ p (boundaryPairs ((toComplex E p K).app k) n)) :=
  CategoryTheory.Functor.ofSequence_map_homOfLE_succ _ k

lemma quasiIso_colimit_desc [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X, Epi (p X)] :
    QuasiIso (colimit.desc (sequence E p K) (Cocone.mk K (toComplex E p K))) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let hH := isColimitOfPreserves (homologyFunctor C (.up ℤ) n)
    (colimit.isColimit (sequence E p K))
  have hι (k : ℕ) : homologyMap (colimit.ι (sequence E p K) k) n ≫
      homologyMap (colimit.desc (sequence E p K) (Cocone.mk K (toComplex E p K))) n =
        homologyMap (stage E p K k).2 n := by
    -- the leg of `toComplex` at `k` is `(stage E p K k).2` by `NatTrans.ofSequence_app`
    rw [← homologyMap_comp, colimit.ι_desc]
    rfl
  have : Epi (homologyMap (colimit.desc (sequence E p K) (Cocone.mk K (toComplex E p K))) n) := by
    have h0 : Epi (homologyMap (stage E p K 0).2 n) := K.epi_homologyMap_fromGraded _ n
    exact epi_of_epi_fac (h := homologyMap (stage E p K 0).2 n) (hι 0)
  have : Mono (homologyMap (colimit.desc (sequence E p K) (Cocone.mk K (toComplex E p K))) n) :=
    hH.mono_of_comp_map_succ_eq_zero _ fun k X g hg ↦ by
      have := comp_homologyMap_inr_eq_zero (stage E p K k).2
        (fun n ↦ p (boundaryPairs (stage E p K k).2 n)) g (by rw [← hι k]; exact hg)
      rw [CategoryTheory.Functor.comp_map, sequence_map_succ]
      exact this
  exact isIso_of_mono_of_epi _

/-- Every term of every stage of the resolution is built from objects `E X` by binary
biproducts. Hence it satisfies every property of objects which holds for the objects `E X` and
is closed under isomorphisms and binary products, such as flatness. -/
public lemma prop_sequence_obj_X (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    [Q.IsClosedUnderBinaryProducts] (hE : ∀ X, Q (E X)) :
    ∀ (k : ℕ) (n : ℤ), Q (((sequence E p K).obj k).X n)
  | 0, _ => hE _
  | k + 1, n => Q.prop_of_iso (homotopyCofiber.XIsoBiprod
      (attachingMap (stage E p K k).2 fun n ↦ p (boundaryPairs (stage E p K k).2 n))
      n (n + 1) rfl).symm
      (Q.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit _ _) (hE _)
        (prop_sequence_obj_X Q hE k n))

end Sequence

section KFlat

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]

/-- Every stage of the resolution is K-flat. -/
lemma isKFlat_stage (E : C → C) (p : ∀ X, E X ⟶ X)
    [∀ X, PreservesFiniteLimits (tensorLeft (E X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E X))] (K : CochainComplex C ℤ) :
    ∀ k, (stage E p K k).1.IsKFlat
  | 0 => isKFlat_of_d_eq_zero (graded (.up ℤ) fun n ↦ E (K.cycles n)) fun _ _ ↦ rfl
  | k + 1 => by
    -- the next stage is the mapping cone of a morphism from the cell complex, which has zero
    -- differentials, to the previous stage
    have : IsKFlat (graded (.up ℤ) fun n ↦ E (boundaryPairs (stage E p K k).2 n)) :=
      isKFlat_of_d_eq_zero _ fun _ _ ↦ rfl
    have := isKFlat_stage E p K k
    exact isKFlat_mappingCone _

end KFlat

end kFlatResolution

section Resolution

variable [HasColimitsOfShape ℕ C] (E : C → C) (p : ∀ X, E X ⟶ X) (K : CochainComplex C ℤ)

/-- The colimit of the stages `kFlatResolution.sequence E p K`, obtained by attaching cells along
the morphisms `p X : E X ⟶ X`. It is K-flat when every `E X` is flat and countable coproducts and
sequential colimits are exact and commute with tensor products
(`CochainComplex.isKFlat_kFlatResolution`), and it resolves `K` when every `p X` is an
epimorphism and sequential colimits are exact (`CochainComplex.kFlatResolution.quasiIso_π`). -/
public abbrev kFlatResolution : CochainComplex C ℤ :=
  colimit (kFlatResolution.sequence E p K)

/-- The morphism from `kFlatResolution E p K` to `K`, a quasi-isomorphism when sequential
colimits in `C` are exact and every `p X` is an epimorphism
(`CochainComplex.kFlatResolution.quasiIso_π`). -/
public def kFlatResolution.π : kFlatResolution E p K ⟶ K :=
  colimit.desc _ (Cocone.mk K (kFlatResolution.toComplex E p K))

/-- The morphism `kFlatResolution.π` restricts to the given morphisms on the stages. -/
@[reassoc (attr := simp)]
public lemma kFlatResolution.ι_π (k : ℕ) :
    colimit.ι (kFlatResolution.sequence E p K) k ≫ kFlatResolution.π E p K =
      (kFlatResolution.toComplex E p K).app k :=
  colimit.ι_desc ..

/-- If sequential colimits in `C` are exact and every `p X` is an epimorphism, then the K-flat
resolution of `K` is quasi-isomorphic to `K`. -/
public instance kFlatResolution.quasiIso_π [HasExactColimitsOfShape ℕ C] [∀ X, Epi (p X)] :
    QuasiIso (kFlatResolution.π E p K) :=
  kFlatResolution.quasiIso_colimit_desc E p K

/-- The resolution `kFlatResolution E p K` is K-flat when the objects `E X` are flat, and
countable coproducts and sequential colimits are exact and commute with tensoring by each
object. -/
public instance isKFlat_kFlatResolution [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    [HasExactColimitsOfShape ℕ C] [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E X))] :
    (kFlatResolution E p K).IsKFlat :=
  have : ∀ k, ((kFlatResolution.sequence E p K).obj k).IsKFlat :=
    kFlatResolution.isKFlat_stage E p K
  isKFlat_of_isColimit (colimit.isColimit _)

/-- The terms of the resolution `kFlatResolution E p K` are flat when the objects `E X` are flat,
and sequential colimits are exact and commute with tensoring by each object. -/
public instance preservesFiniteLimits_tensorLeft_kFlatResolution_X [MonoidalCategory C]
    [MonoidalPreadditive C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E X))] (n : ℤ) :
    PreservesFiniteLimits (tensorLeft ((kFlatResolution E p K).X n)) := by
  -- flatness of `X` is the property of `tensorLeft X` of preserving finite limits, which is
  -- closed under binary products and sequential colimits of functors
  let Q : ObjectProperty C := ObjectProperty.preservesFiniteLimits.inverseImage (curriedTensor C)
  -- evaluating `curriedTensor C` at `X` is `tensorRight X` by definition
  have : PreservesColimitsOfShape ℕ (curriedTensor C) :=
    preservesColimitsOfShape_of_evaluation _ _ fun X ↦
      inferInstanceAs (PreservesColimitsOfShape ℕ (tensorRight X))
  have : PreservesBinaryBiproducts (curriedTensor C) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesLimitsOfShape (Discrete WalkingPair) (curriedTensor C) :=
    preservesBinaryProducts_of_preservesBinaryBiproducts _
  have hQ := kFlatResolution.prop_sequence_obj_X E p K Q fun X ↦
    (inferInstance : PreservesFiniteLimits (tensorLeft (E X)))
  exact Q.prop_of_isColimit (isColimitOfPreserves (eval C _ n) (colimit.isColimit _))
    fun k ↦ hQ k n

end Resolution

/-- **K-flat resolutions of unbounded complexes.** Let `C` be an abelian monoidal category in which
every object is a quotient of a flat object, and in which countable coproducts and sequential
colimits are exact and commute with tensoring by each object. Then every cochain complex `K` in
`C` receives a quasi-isomorphism from a K-flat complex. -/
public theorem exists_quasiIso_isKFlat [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)] (K : CochainComplex C ℤ)
    (hC : ∀ X : C, ∃ (E : C) (p : E ⟶ X), Epi p ∧ PreservesFiniteLimits (tensorLeft E) ∧
      PreservesFiniteColimits (tensorLeft E)) :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ K), QuasiIso π ∧ P.IsKFlat := by
  choose E p hp hflat hflat' using hC
  exact ⟨kFlatResolution E p K, kFlatResolution.π E p K, inferInstance, inferInstance⟩

namespace kFlatResolution

section StepFunctorial

variable {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
  {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} {f₃ : P₃ ⟶ K₃}
  {u : P₁ ⟶ P₂} {g : K₁ ⟶ K₂} (comm : u ≫ f₂ = f₁ ≫ g)

/-- The morphism induced on objects of boundary pairs by a commutative square of complexes. -/
def boundaryPairsMap (n : ℤ) : boundaryPairs f₁ n ⟶ boundaryPairs f₂ n :=
  pullback.map (cyclesMap f₁ n) (K₁.toCycles (n - 1) n)
    (cyclesMap f₂ n) (K₂.toCycles (n - 1) n)
    (cyclesMap u n) (g.f (n - 1)) (cyclesMap g n)
    (by rw [← cyclesMap_comp, ← cyclesMap_comp, comm])
    (by rw [← cancel_mono (K₂.iCycles n)]; simp)

@[reassoc (attr := simp)]
lemma boundaryPairsMap_fst (n : ℤ) :
    boundaryPairsMap comm n ≫ pullback.fst _ _ = pullback.fst _ _ ≫ cyclesMap u n :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
lemma boundaryPairsMap_snd (n : ℤ) :
    boundaryPairsMap comm n ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g.f (n - 1) :=
  pullback.lift_snd ..

variable {E₁ E₂ E₃ : ℤ → C}
  (e₁ : ∀ n, E₁ n ⟶ boundaryPairs f₁ n) (e₂ : ∀ n, E₂ n ⟶ boundaryPairs f₂ n)
  (h : ∀ n, E₁ n ⟶ E₂ n) (he : ∀ n, h n ≫ e₂ n = e₁ n ≫ boundaryPairsMap comm n)

include he

lemma attachingMap_comp :
    attachingMap f₁ e₁ ≫ u = gradedMap (.up ℤ) h ≫ attachingMap f₂ e₂ := by
  ext n
  simp [reassoc_of% (he n)]

/-- The morphism of mapping cones induced by a commutative square of complexes together with
compatible maps on the cell covers. -/
def attachMap :
    mappingCone (attachingMap f₁ e₁) ⟶ mappingCone (attachingMap f₂ e₂) :=
  mappingCone.map (attachingMap f₁ e₁) (attachingMap f₂ e₂) (gradedMap (.up ℤ) h) u
    (attachingMap_comp comm e₁ e₂ h he)

@[reassoc (attr := simp)]
lemma inr_attachMap :
    mappingCone.inr (attachingMap f₁ e₁) ≫ attachMap comm e₁ e₂ h he =
      u ≫ mappingCone.inr (attachingMap f₂ e₂) := by
  simp [attachMap, mappingCone.map]

@[reassoc (attr := simp)]
lemma attachMap_attachDesc :
    attachMap comm e₁ e₂ h he ≫ attachDesc f₂ e₂ = attachDesc f₁ e₁ ≫ g := by
  have hinr : mappingCone.inr (attachingMap f₁ e₁) ≫ attachMap comm e₁ e₂ h he ≫ attachDesc f₂ e₂ =
      mappingCone.inr (attachingMap f₁ e₁) ≫ attachDesc f₁ e₁ ≫ g := by
    rw [inr_attachMap_assoc, inr_attachDesc, comm, inr_attachDesc_assoc]
  ext q
  refine mappingCone.ext_from _ (q + 1) q rfl ?_ ?_
  · simp only [attachMap, mappingCone.map, comp_f, Category.assoc, mappingCone.inl_v_desc_f_assoc,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, attachDesc, boundaryPrimitive, Cochain.mk_v]
    rw [mappingCone.inl_v_desc_f, Cochain.mk_v, reassoc_of% (he (q + 1)),
      boundaryPairsMap_snd_assoc, HomologicalComplex.XIsoOfEq_hom_naturality]
  · simpa only [comp_f, Category.assoc] using congr_arg (fun φ ↦ φ.f q) hinr

end StepFunctorial

section StepFunctorialEq

variable {P₁ K₁ P₂ K₂ P₃ K₃ : CochainComplex C ℤ}
  {f₁ : P₁ ⟶ K₁} {f₂ : P₂ ⟶ K₂} {f₃ : P₃ ⟶ K₃}
  {E₁ E₂ E₃ : ℤ → C}

lemma attachMap_eq_id {u' : P₁ ⟶ P₁} {g' : K₁ ⟶ K₁} {comm' : u' ≫ f₁ = f₁ ≫ g'}
    {e : ∀ n, E₁ n ⟶ boundaryPairs f₁ n} {h' : ∀ n, E₁ n ⟶ E₁ n}
    {he' : ∀ n, h' n ≫ e n = e n ≫ boundaryPairsMap comm' n}
    (hu : u' = 𝟙 P₁) (hh : ∀ n, h' n = 𝟙 (E₁ n)) :
    attachMap comm' e e h' he' = 𝟙 (mappingCone (attachingMap f₁ e)) := by
  dsimp only [attachMap]
  subst hu
  simp only [funext hh, gradedMap_id]
  exact mappingCone.map_id _

lemma attachMap_eq_comp {u₁₂ : P₁ ⟶ P₂} {g₁₂ : K₁ ⟶ K₂} {comm₁₂ : u₁₂ ≫ f₂ = f₁ ≫ g₁₂}
    {u₂₃ : P₂ ⟶ P₃} {g₂₃ : K₂ ⟶ K₃} {comm₂₃ : u₂₃ ≫ f₃ = f₂ ≫ g₂₃}
    {u₁₃ : P₁ ⟶ P₃} {g₁₃ : K₁ ⟶ K₃} {comm₁₃ : u₁₃ ≫ f₃ = f₁ ≫ g₁₃}
    {e₁ : ∀ n, E₁ n ⟶ boundaryPairs f₁ n} {e₂ : ∀ n, E₂ n ⟶ boundaryPairs f₂ n}
    {e₃ : ∀ n, E₃ n ⟶ boundaryPairs f₃ n}
    {h₁₂ : ∀ n, E₁ n ⟶ E₂ n} {he₁₂ : ∀ n, h₁₂ n ≫ e₂ n = e₁ n ≫ boundaryPairsMap comm₁₂ n}
    {h₂₃ : ∀ n, E₂ n ⟶ E₃ n} {he₂₃ : ∀ n, h₂₃ n ≫ e₃ n = e₂ n ≫ boundaryPairsMap comm₂₃ n}
    {h₁₃ : ∀ n, E₁ n ⟶ E₃ n} {he₁₃ : ∀ n, h₁₃ n ≫ e₃ n = e₁ n ≫ boundaryPairsMap comm₁₃ n}
    (hu : u₁₃ = u₁₂ ≫ u₂₃) (hh : ∀ n, h₁₃ n = h₁₂ n ≫ h₂₃ n) :
    attachMap comm₁₃ e₁ e₃ h₁₃ he₁₃ =
      attachMap comm₁₂ e₁ e₂ h₁₂ he₁₂ ≫ attachMap comm₂₃ e₂ e₃ h₂₃ he₂₃ := by
  dsimp only [attachMap]
  subst hu
  simp only [funext hh, ← gradedMap_comp]
  exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

end StepFunctorialEq

section FunctorialSequence

variable (E : C ⥤ C) (p : E ⟶ 𝟭 C)

/-- A morphism `g : K₁ ⟶ K₂` induces morphisms between all stages of `kFlatResolution E.obj p.app`
compatible with their augmentations to `K₁` and `K₂`. -/
def stageMapWithComm {K₁ K₂ : CochainComplex C ℤ} (g : K₁ ⟶ K₂) :
    ∀ k : ℕ, { u : (stage E.obj p.app K₁ k).1 ⟶ (stage E.obj p.app K₂ k).1 //
      u ≫ (stage E.obj p.app K₂ k).2 = (stage E.obj p.app K₁ k).2 ≫ g }
  | 0 => ⟨gradedMap (.up ℤ) fun n ↦ E.map (cyclesMap g n), by
      ext n
      simp only [stage, gradedMap_fromGraded, fromGraded_f, comp_f, Category.assoc]
      have hnat := p.naturality (cyclesMap g n)
      dsimp at hnat
      rw [reassoc_of% hnat, cyclesMap_i]⟩
  | k + 1 =>
    let prev := stageMapWithComm g k
    ⟨attachMap prev.2 _ _ (fun n ↦ E.map (boundaryPairsMap prev.2 n))
        (fun n ↦ p.naturality (boundaryPairsMap prev.2 n)),
      attachMap_attachDesc prev.2 _ _ _ _⟩

lemma stageMapWithComm_id (K : CochainComplex C ℤ) :
    ∀ k : ℕ, (stageMapWithComm E p (𝟙 K) k).1 = 𝟙 (stage E.obj p.app K k).1
  | 0 => by
    ext n
    simp [stageMapWithComm, stage]
  | k + 1 => by
    have ih := stageMapWithComm_id K k
    dsimp only [stageMapWithComm]
    refine attachMap_eq_id ih fun n ↦ ?_
    have hbp : boundaryPairsMap (stageMapWithComm E p (𝟙 K) k).2 n = 𝟙 _ := by
      ext <;> simp [ih]
    rw [hbp, E.map_id]

lemma stageMapWithComm_comp {K₁ K₂ K₃ : CochainComplex C ℤ} (g₁ : K₁ ⟶ K₂) (g₂ : K₂ ⟶ K₃) :
    ∀ k : ℕ, (stageMapWithComm E p (g₁ ≫ g₂) k).1 =
      (stageMapWithComm E p g₁ k).1 ≫ (stageMapWithComm E p g₂ k).1
  | 0 => by
    dsimp only [stageMapWithComm, stage]
    rw [gradedMap_comp]
    congr 1
    ext n
    simp [cyclesMap_comp]
  | k + 1 => by
    have ih := stageMapWithComm_comp g₁ g₂ k
    dsimp only [stageMapWithComm]
    refine attachMap_eq_comp ih fun n ↦ ?_
    have hbp : boundaryPairsMap (stageMapWithComm E p (g₁ ≫ g₂) k).2 n =
        boundaryPairsMap (stageMapWithComm E p g₁ k).2 n ≫
          boundaryPairsMap (stageMapWithComm E p g₂ k).2 n := by
      ext <;> simp [ih, cyclesMap_comp]
    rw [hbp, E.map_comp]

/-- The morphism induced on stage `k` of `kFlatResolution` by `g : K₁ ⟶ K₂`. -/
def stageMap {K₁ K₂ : CochainComplex C ℤ} (g : K₁ ⟶ K₂) (k : ℕ) :
    ((sequence E.obj p.app K₁).obj k) ⟶ ((sequence E.obj p.app K₂).obj k) :=
  (stageMapWithComm E p g k).1

@[reassoc (attr := simp)]
lemma stageMap_toComplex {K₁ K₂ : CochainComplex C ℤ} (g : K₁ ⟶ K₂) (k : ℕ) :
    stageMap E p g k ≫ (toComplex E.obj p.app K₂).app k =
      (toComplex E.obj p.app K₁).app k ≫ g :=
  (stageMapWithComm E p g k).2

@[reassoc]
lemma sequence_map_succ_stageMap {K₁ K₂ : CochainComplex C ℤ} (g : K₁ ⟶ K₂) (k : ℕ) :
    (sequence E.obj p.app K₁).map (homOfLE (k.le_add_right 1)) ≫ stageMap E p g (k + 1) =
      stageMap E p g k ≫ (sequence E.obj p.app K₂).map (homOfLE (k.le_add_right 1)) :=
  (congrArg (· ≫ stageMap E p g (k + 1)) (Functor.ofSequence_map_homOfLE_succ _ k)).trans <|
    (inr_attachMap (stageMapWithComm E p g k).2 _ _ _
      (fun n ↦ p.naturality (boundaryPairsMap (stageMapWithComm E p g k).2 n))).trans <|
      (congrArg (stageMap E p g k ≫ ·) (Functor.ofSequence_map_homOfLE_succ _ k)).symm

@[simp]
lemma stageMap_id (K : CochainComplex C ℤ) (k : ℕ) :
    stageMap E p (𝟙 K) k = 𝟙 ((sequence E.obj p.app K).obj k) :=
  stageMapWithComm_id E p K k

@[simp]
lemma stageMap_comp {K₁ K₂ K₃ : CochainComplex C ℤ} (g₁ : K₁ ⟶ K₂) (g₂ : K₂ ⟶ K₃) (k : ℕ) :
    stageMap E p (g₁ ≫ g₂) k = stageMap E p g₁ k ≫ stageMap E p g₂ k :=
  stageMapWithComm_comp E p g₁ g₂ k

/-- The natural transformation of stage sequences induced by `g : K₁ ⟶ K₂`. -/
@[simps! app]
def sequenceMap {K₁ K₂ : CochainComplex C ℤ} (g : K₁ ⟶ K₂) :
    sequence E.obj p.app K₁ ⟶ sequence E.obj p.app K₂ :=
  NatTrans.ofSequence (stageMap E p g) (sequence_map_succ_stageMap E p g)

@[simp]
lemma sequenceMap_id (K : CochainComplex C ℤ) :
    sequenceMap E p (𝟙 K) = 𝟙 (sequence E.obj p.app K) := by
  ext k
  simp

@[simp]
lemma sequenceMap_comp {K₁ K₂ K₃ : CochainComplex C ℤ} (g₁ : K₁ ⟶ K₂) (g₂ : K₂ ⟶ K₃) :
    sequenceMap E p (g₁ ≫ g₂) = sequenceMap E p g₁ ≫ sequenceMap E p g₂ := by
  ext k
  simp

end FunctorialSequence

end kFlatResolution

section FunctorialResolution

variable [HasColimitsOfShape ℕ C] (E : C ⥤ C) (p : E ⟶ 𝟭 C)

/-- When `E : C ⥤ C` is a functor and `p : E ⟶ 𝟭 C` is a natural transformation, the cell-attaching
resolutions `kFlatResolution E.obj p.app K` assemble into an endofunctor of `CochainComplex C ℤ`.
The functor `E` is not required to be additive or to preserve zero morphisms. -/
public def kFlatResolutionFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj K := kFlatResolution E.obj p.app K
  map g := colimMap (kFlatResolution.sequenceMap E p g)
  map_id _ := colimit.hom_ext fun _ ↦ by simp
  map_comp _ _ := colimit.hom_ext fun _ ↦ by simp

/-- The augmentation `kFlatResolution.π` as a natural transformation from
`kFlatResolutionFunctor E p` to the identity functor on `CochainComplex C ℤ`. -/
public def kFlatResolution.πNatTrans :
    kFlatResolutionFunctor E p ⟶ 𝟭 (CochainComplex C ℤ) where
  app K := kFlatResolution.π E.obj p.app K
  naturality _ _ g := colimit.hom_ext fun k ↦ by
    dsimp only [kFlatResolutionFunctor, Functor.id_obj, Functor.id_map]
    rw [ι_colimMap_assoc, kFlatResolution.sequenceMap_app, kFlatResolution.ι_π,
      kFlatResolution.stageMap_toComplex, kFlatResolution.ι_π_assoc]

/-- The functorial resolution `(kFlatResolutionFunctor E p).obj K` is canonically isomorphic to
`kFlatResolution E.obj p.app K`. -/
public def kFlatResolutionFunctorObjIso (K : CochainComplex C ℤ) :
    (kFlatResolutionFunctor E p).obj K ≅ kFlatResolution E.obj p.app K :=
  Iso.refl _

@[reassoc (attr := simp)]
public lemma kFlatResolutionFunctorObjIso_hom_π (K : CochainComplex C ℤ) :
    (kFlatResolutionFunctorObjIso E p K).hom ≫ kFlatResolution.π E.obj p.app K =
      (kFlatResolution.πNatTrans E p).app K :=
  Category.id_comp _

public instance kFlatResolution.quasiIso_πNatTrans_app [HasExactColimitsOfShape ℕ C]
    [∀ X, Epi (p.app X)] (K : CochainComplex C ℤ) :
    QuasiIso ((kFlatResolution.πNatTrans E p).app K) :=
  inferInstanceAs (QuasiIso (kFlatResolution.π E.obj p.app K))

public instance isKFlat_kFlatResolutionFunctor_obj [MonoidalCategory C] [MonoidalPreadditive C]
    [∀ K L : CochainComplex C ℤ, HasTensor K L]
    [HasExactColimitsOfShape ℕ C] [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
    [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))]
    [∀ X, PreservesFiniteColimits (tensorLeft (E.obj X))] (K : CochainComplex C ℤ) :
    ((kFlatResolutionFunctor E p).obj K).IsKFlat :=
  inferInstanceAs (kFlatResolution E.obj p.app K).IsKFlat

/-- The terms of `(kFlatResolutionFunctor E p).obj K` are flat when the objects `E.obj X` are flat,
and sequential colimits are exact and commute with tensoring by each object. -/
public instance preservesFiniteLimits_tensorLeft_kFlatResolutionFunctor_obj_X [MonoidalCategory C]
    [MonoidalPreadditive C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)]
    [∀ X, PreservesFiniteLimits (tensorLeft (E.obj X))] (K : CochainComplex C ℤ) (n : ℤ) :
    PreservesFiniteLimits (tensorLeft (((kFlatResolutionFunctor E p).obj K).X n)) :=
  inferInstanceAs (PreservesFiniteLimits (tensorLeft ((kFlatResolution E.obj p.app K).X n)))

end FunctorialResolution

end CochainComplex
