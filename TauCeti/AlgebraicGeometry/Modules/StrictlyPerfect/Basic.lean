/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.Bounded.Basic
public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
public import TauCeti.AlgebraicGeometry.VectorBundle.Retract
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
import TauCeti.AlgebraicGeometry.Modules.Dual

/-!
# Strictly perfect complexes of `𝒪_X`-modules

A cochain complex `E` of `𝒪_X`-modules on an arbitrary scheme `X` is **strictly perfect**
(`AlgebraicGeometry.Scheme.Modules.isStrictlyPerfect`) if it is globally bounded (`E^i = 0` outside
a finite integer interval `[a, b]`) and every term `E^i` is finite locally free. This matches
Stacks Tag 08C4 and Thomason–Trobaugh Definition 2.2.2; in particular, terms need only be locally
direct summands of finite free sheaves (`isStrictlyPerfect_iff_retract_free`), not global summands.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isStrictlyPerfect`: the object property on
  `CochainComplex X.Modules ℤ` of bounded complexes with finite locally free terms;
* `isStrictlyPerfect_iff`, `isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE`,
  `isStrictlyPerfect_iff_exists_bounds`, and `isStrictlyPerfect_iff_retract_free`: equivalent
  characterizations, including the Thomason–Trobaugh local summand formulation;
* `isStrictlyPerfect_zero`, `isStrictlyPerfect_single`, `isStrictlyPerfect_single_iff`,
  `isStrictlyPerfect_double`, `isStrictlyPerfect_of_iso`, `isStrictlyPerfect_of_retract`,
  `isStrictlyPerfect_shift`, `isStrictlyPerfect_mappingCone`,
  `isStrictlyPerfect_stupidTrunc_embeddingUpIntLE`: closure under basic homological operations
  (Stacks Tag 08C5);
* `isStrictlyPerfect_restrict`, `isStrictlyPerfect_pullback`, and `isStrictlyPerfect_tensorObj`:
  closure under restriction along open immersions, degreewise pullback along arbitrary scheme
  morphisms, and total tensor product of complexes (Stacks Tags 09J2 and 09U6; TT90 2.5.1);
* `isStrictlyPerfect_tilde`: over an affine scheme `Spec A`, the termwise tilde of a bounded
  complex of finitely generated projective `A`-modules is strictly perfect;
* `isKFlat_of_isStrictlyPerfect`: every strictly perfect complex is K-flat (combining
  `isRightAdjoint_tensorLeft_of_isLocallyFree` with `CochainComplex.isKFlat_of_bounded_flat`);
* `isStrictlyPerfect_of_isEmpty`: every complex on an empty scheme is zero, hence strictly perfect;
* `nonposStructureComplex` and `not_isStrictlyPerfect_nonposStructureComplex`: on every nonempty
  scheme, the zero-differential complex with `𝒪_X` in nonpositive degrees has finite locally free
  terms but is not strictly perfect, and neither is its contractible identity mapping cone
  (`not_isStrictlyPerfect_mappingCone_id_nonposStructureComplex`).

## References

* [The Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [The Stacks Project, Tag 08C5](https://stacks.math.columbia.edu/tag/08C5)
* [The Stacks Project, Tag 09J2](https://stacks.math.columbia.edu/tag/09J2)
* [The Stacks Project, Tag 09U6](https://stacks.math.columbia.edu/tag/09U6)
* R. W. Thomason and T. Trobaugh, *Higher algebraic K-theory of schemes and of derived categories*,
  Definition 2.2.2 and Section 2.5.1.
-/

public section

open CategoryTheory Limits ZeroObject MonoidalCategory HomologicalComplex AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section Definition

/-- A cochain complex of `𝒪_X`-modules is **strictly perfect** if it is globally bounded and every
term `E.X i` is a finite locally free `𝒪_X`-module (Stacks Tag 08C4, TT90 Definition 2.2.2). -/
def isStrictlyPerfect (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) :=
  fun E ↦ CochainComplex.bounded X.Modules E ∧ ∀ i : ℤ, isFiniteLocallyFree X (E.X i)

/-- A cochain complex is strictly perfect if and only if it is bounded and every term is finite
locally free. -/
theorem isStrictlyPerfect_iff {X : Scheme.{u}} (E : CochainComplex X.Modules ℤ) :
    isStrictlyPerfect X E ↔
      CochainComplex.bounded X.Modules E ∧ ∀ i : ℤ, isFiniteLocallyFree X (E.X i) :=
  Iff.rfl

/-- A cochain complex is strictly perfect if and only if it is strictly bounded below and above
and every term is finite locally free. -/
theorem isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE {X : Scheme.{u}}
    (E : CochainComplex X.Modules ℤ) :
    isStrictlyPerfect X E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, isFiniteLocallyFree X (E.X i) := by
  rw [isStrictlyPerfect_iff, CochainComplex.bounded_iff]

/-- A cochain complex is strictly perfect if and only if there exist integers `a ≤ b` outside
which all terms are zero, and every term is locally free of finite type. -/
theorem isStrictlyPerfect_iff_exists_bounds {X : Scheme.{u}} (E : CochainComplex X.Modules ℤ) :
    isStrictlyPerfect X E ↔
      (∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (E.X i)) ∧
        ∀ i : ℤ, (E.X i).IsLocallyFree ∧ (E.X i).IsFiniteType := by
  rw [isStrictlyPerfect_iff_exists_isStrictlyGE_isStrictlyLE]
  refine and_congr ?_
    (forall_congr' fun i ↦ isFiniteLocallyFree_iff_isLocallyFree_and_isFiniteType _)
  constructor
  · rintro ⟨a, b, ha, hb⟩
    refine ⟨a, max a b, le_max_left a b, fun i hi ↦ ?_⟩
    rcases hi with hia | hbi
    · exact E.isZero_of_isStrictlyGE a i hia
    · exact E.isZero_of_isStrictlyLE b i (lt_of_le_of_lt (le_max_right a b) hbi)
  · rintro ⟨a, b, _, h⟩
    exact ⟨a, b,
      (E.isStrictlyGE_iff a).mpr fun i hi ↦ h i (Or.inl hi),
      (E.isStrictlyLE_iff b).mpr fun i hi ↦ h i (Or.inr hi)⟩

/-- **Thomason–Trobaugh local summand characterization** (TT90 Definition 2.2.2): a cochain complex
of `𝒪_X`-modules is strictly perfect if and only if it is bounded and every term is locally on `X`
a retract (direct summand) of a finite free `𝒪_X`-module. -/
theorem isStrictlyPerfect_iff_retract_free {X : Scheme.{u}} (E : CochainComplex X.Modules ℤ) :
    isStrictlyPerfect X E ↔
      CochainComplex.bounded X.Modules E ∧
        ∀ i : ℤ, ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ I : Type u, Finite I ∧
            Nonempty (Retract ((E.X i).restrict U.ι) (SheafOfModules.free I)) := by
  rw [isStrictlyPerfect_iff]
  exact and_congr_right fun _ ↦
    forall_congr' fun i ↦ isFiniteLocallyFree_iff_forall_exists_retract_free (E.X i)

end Definition

section Closure

variable {X : Scheme.{u}}

/-- The zero cochain complex is strictly perfect. -/
theorem isStrictlyPerfect_zero (X : Scheme.{u}) :
    isStrictlyPerfect X (0 : CochainComplex X.Modules ℤ) :=
  ⟨(CochainComplex.bounded_iff X.Modules 0).mpr ⟨0, 0, inferInstance, inferInstance⟩,
    fun i ↦ (isFiniteLocallyFree X).prop_of_isZero
      ((eval X.Modules (.up ℤ) i).map_isZero (isZero_zero _))⟩

/-- Strictly perfect complexes contain the zero complex. -/
instance containsZero_isStrictlyPerfect (X : Scheme.{u}) :
    (isStrictlyPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isStrictlyPerfect_zero X⟩

/-- Every zero cochain complex is strictly perfect. -/
theorem isStrictlyPerfect_of_isZero {E : CochainComplex X.Modules ℤ} (hE : IsZero E) :
    isStrictlyPerfect X E := by
  refine ⟨(CochainComplex.bounded_iff X.Modules E).mpr
    ⟨0, 0, (E.isStrictlyGE_iff 0).mpr fun i _ ↦ (eval X.Modules (.up ℤ) i).map_isZero hE,
      (E.isStrictlyLE_iff 0).mpr fun i _ ↦ (eval X.Modules (.up ℤ) i).map_isZero hE⟩, fun i ↦ ?_⟩
  exact (isFiniteLocallyFree X).prop_of_isZero ((eval X.Modules (.up ℤ) i).map_isZero hE)

/-- Strict perfectness is invariant under isomorphisms of cochain complexes. -/
theorem isStrictlyPerfect_of_iso {E F : CochainComplex X.Modules ℤ} (e : E ≅ F)
    (hE : isStrictlyPerfect X E) : isStrictlyPerfect X F :=
  ⟨(CochainComplex.bounded X.Modules).prop_of_iso e hE.1,
    fun i ↦ (isFiniteLocallyFree X).prop_of_iso ((eval X.Modules (.up ℤ) i).mapIso e) (hE.2 i)⟩

/-- Strict perfectness is preserved and reflected by isomorphisms of cochain complexes. -/
theorem isStrictlyPerfect_iff_of_iso {E F : CochainComplex X.Modules ℤ} (e : E ≅ F) :
    isStrictlyPerfect X E ↔ isStrictlyPerfect X F :=
  ⟨isStrictlyPerfect_of_iso e, isStrictlyPerfect_of_iso e.symm⟩

/-- Strictly perfect complexes are closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isStrictlyPerfect (X : Scheme.{u}) :
    (isStrictlyPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hE := isStrictlyPerfect_of_iso e hE

/-- A retract (direct summand) of a strictly perfect complex is strictly perfect. -/
theorem isStrictlyPerfect_of_retract {E F : CochainComplex X.Modules ℤ} (r : Retract E F)
    (hF : isStrictlyPerfect X F) : isStrictlyPerfect X E := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ F).mp hF.1
  have isZero_of_retract : ∀ {M N : X.Modules}, Retract M N → IsZero N → IsZero M :=
    fun r' hN ↦ (IsZero.iff_id_eq_zero _).mpr (by rw [← r'.retract, hN.eq_of_src r'.r 0, comp_zero])
  refine ⟨(CochainComplex.bounded_iff _ E).mpr ⟨a, b,
    (E.isStrictlyGE_iff a).mpr fun i hi ↦
      isZero_of_retract (r.map (eval X.Modules (.up ℤ) i)) (F.isZero_of_isStrictlyGE a i hi),
    (E.isStrictlyLE_iff b).mpr fun i hi ↦
      isZero_of_retract (r.map (eval X.Modules (.up ℤ) i)) (F.isZero_of_isStrictlyLE b i hi)⟩,
    fun i ↦ isFiniteLocallyFree_of_retract (r.map (eval X.Modules (.up ℤ) i)) (hF.2 i)⟩

/-- Strictly perfect complexes are stable under retracts. -/
instance isStableUnderRetracts_isStrictlyPerfect (X : Scheme.{u}) :
    (isStrictlyPerfect X).IsStableUnderRetracts where
  of_retract r hF := isStrictlyPerfect_of_retract r hF

/-- A finite locally free `𝒪_X`-module placed in a single degree `n` is strictly perfect. -/
theorem isStrictlyPerfect_single (n : ℤ) {M : X.Modules} (hM : isFiniteLocallyFree X M) :
    isStrictlyPerfect X ((single X.Modules (.up ℤ) n).obj M) := by
  refine ⟨CochainComplex.bounded_single n M, fun i ↦ ?_⟩
  by_cases h : i = n
  · subst h
    exact (isFiniteLocallyFree X).prop_of_iso (singleObjXSelf (.up ℤ) i M).symm hM
  · exact (isFiniteLocallyFree X).prop_of_isZero (isZero_single_obj_X (.up ℤ) n M i h)

/-- A complex concentrated in degree `n` is strictly perfect if and only if its degree-`n` sheaf is
finite locally free. -/
@[simp]
theorem isStrictlyPerfect_single_iff (n : ℤ) (M : X.Modules) :
    isStrictlyPerfect X ((single X.Modules (.up ℤ) n).obj M) ↔ isFiniteLocallyFree X M :=
  ⟨fun h ↦ (isFiniteLocallyFree X).prop_of_iso (singleObjXSelf (.up ℤ) n M) (h.2 n),
    isStrictlyPerfect_single n⟩

/-- A two-term complex of finite locally free sheaves concentrated in adjacent degrees is strictly
perfect. -/
theorem isStrictlyPerfect_double {M N : X.Modules} (f : M ⟶ N) {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) (hM : isFiniteLocallyFree X M)
    (hN : isFiniteLocallyFree X N) :
    isStrictlyPerfect X (HomologicalComplex.double f hij) := by
  refine ⟨CochainComplex.bounded_double f hij, fun k ↦ ?_⟩
  by_cases hki : k = i
  · subst hki
    exact (isFiniteLocallyFree X).prop_of_iso (HomologicalComplex.doubleXIso₀ f hij).symm hM
  · by_cases hkj : k = j
    · subst hkj
      exact (isFiniteLocallyFree X).prop_of_iso
        (HomologicalComplex.doubleXIso₁ f hij (by rintro rfl; simp at hij)).symm hN
    · exact (isFiniteLocallyFree X).prop_of_isZero
        (HomologicalComplex.isZero_double_X f hij k hki hkj)

/-- Every shift of a strictly perfect complex is strictly perfect (Stacks Tag 08C5). -/
theorem isStrictlyPerfect_shift {E : CochainComplex X.Modules ℤ} (hE : isStrictlyPerfect X E)
    (k : ℤ) : isStrictlyPerfect X (E⟦k⟧) :=
  ⟨(CochainComplex.bounded X.Modules).le_shift k E hE.1,
    fun i ↦ (isFiniteLocallyFree X).prop_of_iso
      (E.shiftFunctorObjXIso k i (i + k) rfl).symm (hE.2 (i + k))⟩

/-- A complex is strictly perfect if and only if its shift by `k` is strictly perfect. -/
@[simp]
theorem isStrictlyPerfect_shift_iff (E : CochainComplex X.Modules ℤ) (k : ℤ) :
    isStrictlyPerfect X (E⟦k⟧) ↔ isStrictlyPerfect X E :=
  ⟨fun h ↦ isStrictlyPerfect_of_iso ((shiftFunctorCompIsoId _ k (-k) (add_neg_cancel k)).app E)
      (isStrictlyPerfect_shift h (-k)),
    fun h ↦ isStrictlyPerfect_shift h k⟩

/-- Strictly perfect complexes are stable under integer shifts. -/
instance isStableUnderShift_isStrictlyPerfect (X : Scheme.{u}) :
    (isStrictlyPerfect X).IsStableUnderShift ℤ where
  isStableUnderShiftBy k := ⟨fun _ hE ↦ isStrictlyPerfect_shift hE k⟩

/-- The mapping cone of a morphism between strictly perfect complexes is strictly perfect
(Stacks Tag 08C5). -/
theorem isStrictlyPerfect_mappingCone {E F : CochainComplex X.Modules ℤ} (f : E ⟶ F)
    (hE : isStrictlyPerfect X E) (hF : isStrictlyPerfect X F) :
    isStrictlyPerfect X (CochainComplex.mappingCone f) := by
  refine ⟨CochainComplex.bounded_mappingCone f hE.1 hF.1, fun i ↦ ?_⟩
  have he : (CochainComplex.mappingCone f).X i ≅ E.X (i + 1) ⊞ F.X i :=
    homotopyCofiber.XIsoBiprod f i (i + 1) rfl
  have hprod : isFiniteLocallyFree X (E.X (i + 1) ⨯ F.X i) :=
    (isFiniteLocallyFree X).prop_prod (E.X (i + 1)) (F.X i) (hE.2 (i + 1)) (hF.2 i)
  exact (isFiniteLocallyFree X).prop_of_iso (he ≪≫ biprod.isoProd _ _).symm hprod

/-- The brutal truncation of a strictly perfect complex in degrees `≤ n` is strictly perfect. -/
theorem isStrictlyPerfect_stupidTrunc_embeddingUpIntLE {E : CochainComplex X.Modules ℤ}
    (hE : isStrictlyPerfect X E) (n : ℤ) :
    isStrictlyPerfect X (E.stupidTrunc (ComplexShape.embeddingUpIntLE n)) := by
  obtain ⟨a, _, ha, _⟩ := (CochainComplex.bounded_iff _ E).mp hE.1
  refine ⟨(CochainComplex.bounded_iff _ _).mpr ⟨a, n, inferInstance, inferInstance⟩, fun i ↦ ?_⟩
  by_cases hi : i ≤ n
  · exact (isFiniteLocallyFree X).prop_of_iso
      (E.stupidTruncXIso (ComplexShape.embeddingUpIntLE n) (i := (n - i).natAbs) (i' := i)
        (by simp [Int.natAbs_of_nonneg (sub_nonneg.mpr hi)])).symm (hE.2 i)
  · exact (isFiniteLocallyFree X).prop_of_isZero
      (E.isZero_stupidTrunc_embeddingUpIntLE_X n (not_le.mp hi))

end Closure

section Functoriality

/-- Degreewise pullback along an arbitrary morphism of schemes preserves strict perfectness
(Stacks Tag 09U6, TT90 2.5.1). -/
theorem isStrictlyPerfect_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    {E : CochainComplex X.Modules ℤ} (hE : isStrictlyPerfect X E) :
    isStrictlyPerfect Y (((pullback f).mapHomologicalComplex (.up ℤ)).obj E) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ E).mp hE.1
  refine ⟨(CochainComplex.bounded_iff _ _).mpr ⟨a, b,
    (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi ↦
      (pullback f).map_isZero (E.isZero_of_isStrictlyGE a i hi),
    (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi ↦
      (pullback f).map_isZero (E.isZero_of_isStrictlyLE b i hi)⟩,
    fun i ↦ isFiniteLocallyFree_pullback f (hE.2 i)⟩

/-- Restriction along an open immersion preserves strict perfectness. -/
theorem isStrictlyPerfect_restrict {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {E : CochainComplex X.Modules ℤ} (hE : isStrictlyPerfect X E) :
    isStrictlyPerfect U (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ E).mp hE.1
  refine ⟨(CochainComplex.bounded_iff _ _).mpr ⟨a, b,
    (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi ↦
      (restrictFunctor j).map_isZero (E.isZero_of_isStrictlyGE a i hi),
    (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi ↦
      (restrictFunctor j).map_isZero (E.isZero_of_isStrictlyLE b i hi)⟩,
    fun i ↦ isFiniteLocallyFree_restrict j (hE.2 i)⟩

/-- Over an affine scheme `Spec A`, the termwise tilde of a bounded complex of finitely generated
projective `A`-modules is strictly perfect. -/
theorem isStrictlyPerfect_tilde {A : CommRingCat.{u}}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : CochainComplex.bounded (ModuleCat.{u} A) P)
    (hfin : ∀ i : ℤ, Module.Finite A (P.X i)) (hproj : ∀ i : ℤ, Module.Projective A (P.X i)) :
    isStrictlyPerfect (Spec A) (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj P) := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ P).mp hP
  refine ⟨(CochainComplex.bounded_iff _ _).mpr ⟨a, b,
    (CochainComplex.isStrictlyGE_iff _ a).mpr fun i hi ↦
      (tilde.functor A).map_isZero (P.isZero_of_isStrictlyGE a i hi),
    (CochainComplex.isStrictlyLE_iff _ b).mpr fun i hi ↦
      (tilde.functor A).map_isZero (P.isZero_of_isStrictlyLE b i hi)⟩, fun i ↦ ?_⟩
  exact (TauCeti.AlgebraicGeometry.isFiniteLocallyFree_tilde_iff (P.X i)).mpr ⟨hfin i, hproj i⟩

end Functoriality

section TensorAndKFlat

/-- If `E` is strictly bounded in `[a₁, b₁]` and `F` is strictly bounded in `[a₂, b₂]`, then
`HomologicalComplex.tensorObj E F` is strictly bounded in `[a₁ + a₂, b₁ + b₂]`. -/
private theorem bounded_tensorObj {C : Type*} [Category* C] [Preadditive C]
    [MonoidalCategory C] [MonoidalPreadditive C] {E F : CochainComplex C ℤ}
    [HomologicalComplex.HasTensor E F]
    (hE : CochainComplex.bounded C E) (hF : CochainComplex.bounded C F) :
    CochainComplex.bounded C (HomologicalComplex.tensorObj E F) := by
  obtain ⟨a₁, b₁, ha₁, hb₁⟩ := (CochainComplex.bounded_iff C E).mp hE
  obtain ⟨a₂, b₂, ha₂, hb₂⟩ := (CochainComplex.bounded_iff C F).mp hF
  refine (CochainComplex.bounded_iff C _).mpr ⟨a₁ + a₂, b₁ + b₂, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    refine mapBifunctor.hom_ext fun i j hij ↦ ?_
    have hij' : i + j = n := hij
    have hz : IsZero (E.X i ⊗ F.X j) := by
      rcases lt_or_ge i a₁ with hi | hi
      · exact (tensorRight (F.X j)).map_isZero (E.isZero_of_isStrictlyGE a₁ i hi)
      · exact (tensorLeft (E.X i)).map_isZero (F.isZero_of_isStrictlyGE a₂ j (by omega))
    exact hz.eq_of_src _ _
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    refine mapBifunctor.hom_ext fun i j hij ↦ ?_
    have hij' : i + j = n := hij
    have hz : IsZero (E.X i ⊗ F.X j) := by
      rcases lt_or_ge b₁ i with hi | hi
      · exact (tensorRight (F.X j)).map_isZero (E.isZero_of_isStrictlyLE b₁ i hi)
      · exact (tensorLeft (E.X i)).map_isZero (F.isZero_of_isStrictlyLE b₂ j (by omega))
    exact hz.eq_of_src _ _

/-- The degree-`n` term of `HomologicalComplex.tensorObj E F` when `E` is bounded in `[a₁, b₁]` is
isomorphic to the finite coproduct `∐_{p ∈ [a₁, b₁]} E^p ⊗ F^{n - p}`. -/
private def tensorObjXIsoCoproduct {X : Scheme.{u}} (E F : CochainComplex X.Modules ℤ)
    (a₁ b₁ n : ℤ) [E.IsStrictlyGE a₁] [E.IsStrictlyLE b₁] :
    (HomologicalComplex.tensorObj E F).X n ≅
      ∐ (fun p : Finset.Icc a₁ b₁ ↦ E.X p.val ⊗ F.X (n - p.val)) where
  hom := mapBifunctorDesc fun i j hij ↦
    if hi : i ∈ Finset.Icc a₁ b₁ then
      (𝟙 (E.X i) ⊗ₘ (F.XIsoOfEq (show j = n - i by
        have hij' : i + j = n := hij
        omega)).hom) ≫ Sigma.ι (fun p : Finset.Icc a₁ b₁ ↦ E.X p.val ⊗ F.X (n - p.val)) ⟨i, hi⟩
    else 0
  inv := Sigma.desc fun p : Finset.Icc a₁ b₁ ↦ ιTensorObj E F p.val (n - p.val) n (by omega)
  hom_inv_id := by
    refine mapBifunctor.hom_ext fun i j hij ↦ ?_
    have hij' : i + j = n := hij
    rw [Category.comp_id, ← Category.assoc, ι_mapBifunctorDesc]
    by_cases hi : i ∈ Finset.Icc a₁ b₁
    · simp only [dite_eq_left hi, Category.assoc, Sigma.ι_comp_desc]
      obtain rfl : j = n - i := by omega
      simp [XIsoOfEq]
    · simp only [dite_eq_right hi, zero_comp]
      have hz : IsZero (E.X i ⊗ F.X j) :=
        (tensorRight (F.X j)).map_isZero (E.isZero_X_of_notMem_Icc a₁ b₁ hi)
      exact hz.eq_of_src _ _
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun p ↦ ?_
    simp only [Category.comp_id, Sigma.ι_comp_desc_assoc]
    rw [ιTensorObj, ι_mapBifunctorDesc]
    simp [XIsoOfEq]

/-- The total tensor product of two strictly perfect complexes is strictly perfect
(Stacks Tag 09J2, TT90 2.5.1). -/
theorem isStrictlyPerfect_tensorObj {X : Scheme.{u}} {E F : CochainComplex X.Modules ℤ}
    (hE : isStrictlyPerfect X E) (hF : isStrictlyPerfect X F) :
    isStrictlyPerfect X (HomologicalComplex.tensorObj E F) := by
  refine ⟨bounded_tensorObj hE.1 hF.1, fun n ↦ ?_⟩
  obtain ⟨a₁, b₁, ha₁, hb₁⟩ := (CochainComplex.bounded_iff _ E).mp hE.1
  let f : Finset.Icc a₁ b₁ → X.Modules := fun p ↦ E.X p.val ⊗ F.X (n - p.val)
  have : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBiproductsOfShape (Finset.Icc a₁ b₁) X.Modules := hasBiproductsOfShape_finite X.Modules
  let e : (HomologicalComplex.tensorObj E F).X n ≅ ∏ᶜ f :=
    tensorObjXIsoCoproduct E F a₁ b₁ n ≪≫ (biproduct.isoCoproduct f).symm ≪≫
      biproduct.isoProduct f
  refine (isFiniteLocallyFree X).prop_of_iso e.symm ?_
  exact (isFiniteLocallyFree X).prop_pi f fun p ↦
    (isFiniteLocallyFree X).prop_tensor (hE.2 p.val) (hF.2 (n - p.val))

/-- Every strictly perfect complex of `𝒪_X`-modules is K-flat: its terms are finite locally free,
hence flat (`isRightAdjoint_tensorLeft_of_isLocallyFree`), and it is bounded. -/
theorem isKFlat_of_isStrictlyPerfect {X : Scheme.{u}} {E : CochainComplex X.Modules ℤ}
    (hE : isStrictlyPerfect X E) : E.IsKFlat := by
  obtain ⟨a, b, ha, hb⟩ := (CochainComplex.bounded_iff _ E).mp hE.1
  have (i : ℤ) : PreservesFiniteLimits (tensorLeft (E.X i)) := by
    have ⟨_, _⟩ := (isFiniteLocallyFree_iff_isLocallyFree_and_isFiniteType (E.X i)).mp (hE.2 i)
    infer_instance
  exact CochainComplex.isKFlat_of_bounded_flat E a b

end TensorAndKFlat

section EmptyAndNonExample

/-- On an empty scheme, every `𝒪_X`-module is a zero object. -/
theorem isZero_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M : X.Modules) : IsZero M := by
  refine TauCeti.SheafOfModules.isZero_of_forall_subsingleton (S := X.ringCatSheaf) ?_ M
  intro U
  have hU : U.unop = ⊥ := eq_bot_iff.mpr fun x _ ↦ isEmptyElim x
  have : Subsingleton Γ(X, U.unop) := by
    rw [hU]
    exact CommRingCat.subsingleton_of_isTerminal X.sheaf.isTerminalOfEmpty
  exact this

/-- Every cochain complex of `𝒪_X`-modules on an empty scheme is strictly perfect. -/
theorem isStrictlyPerfect_of_isEmpty {X : Scheme.{u}} [IsEmpty X]
    (E : CochainComplex X.Modules ℤ) : isStrictlyPerfect X E :=
  isStrictlyPerfect_of_isZero <|
    (IsZero.iff_id_eq_zero E).mpr
      (HomologicalComplex.hom_ext _ _ fun i ↦ (isZero_of_isEmpty (E.X i)).eq_of_src _ _)

/-- On a nonempty scheme, the structure sheaf `𝒪_X` (the monoidal unit of `X.Modules`) is not a
zero object. -/
theorem not_isZero_unit (X : Scheme.{u}) [Nonempty X] : ¬ IsZero (𝟙_ X.Modules) := by
  intro h0
  obtain ⟨x⟩ := ‹Nonempty X›
  have h10 : (1 : Γ(X, ⊤)) = 0 := by
    have heq : (𝟙 (𝟙_ X.Modules) : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) = 0 := h0.eq_of_src _ _
    exact congrArg (fun f : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules ↦ f.app ⊤ (1 : Γ(X, ⊤))) heq
  have hne : (1 : X.presheaf.stalk x) ≠ 0 := one_ne_zero
  exact hne (by simpa [map_one, map_zero] using congrArg (X.presheaf.germ ⊤ x trivial) h10)

/-- The cochain complex on `X` with zero differentials, `𝒪_X` in all nonpositive degrees `i ≤ 0`,
and `0` in all positive degrees `i > 0`. On every nonempty scheme, this has finite locally free
terms yet fails to be strictly perfect. -/
def nonposStructureComplex (X : Scheme.{u}) : CochainComplex X.Modules ℤ where
  X i := if i ≤ 0 then 𝟙_ X.Modules else 0
  d _ _ := 0

@[simp]
lemma nonposStructureComplex_X_of_le (X : Scheme.{u}) {i : ℤ} (hi : i ≤ 0) :
    (nonposStructureComplex X).X i = 𝟙_ X.Modules :=
  ite_eq_left hi

@[simp]
lemma nonposStructureComplex_X_of_pos (X : Scheme.{u}) {i : ℤ} (hi : 0 < i) :
    (nonposStructureComplex X).X i = 0 :=
  ite_eq_right (not_le.mpr hi)

/-- Every term of `nonposStructureComplex X` is finite locally free. -/
theorem isFiniteLocallyFree_nonposStructureComplex_X (X : Scheme.{u}) (i : ℤ) :
    isFiniteLocallyFree X ((nonposStructureComplex X).X i) := by
  by_cases hi : i ≤ 0
  · rw [nonposStructureComplex_X_of_le X hi]
    exact (isFiniteLocallyFree X).prop_unit
  · rw [nonposStructureComplex_X_of_pos X (not_le.mp hi)]
    exact (isFiniteLocallyFree X).prop_zero

/-- On any nonempty scheme, `nonposStructureComplex X` has finite locally free terms but is not
strictly perfect because it is unbounded below. -/
theorem not_isStrictlyPerfect_nonposStructureComplex (X : Scheme.{u}) [Nonempty X] :
    ¬ isStrictlyPerfect X (nonposStructureComplex X) := by
  intro h
  obtain ⟨a, _, ha, _⟩ := (CochainComplex.bounded_iff _ _).mp h.1
  let i : ℤ := min (a - 1) 0
  have hzero : IsZero ((nonposStructureComplex X).X i) :=
    (nonposStructureComplex X).isZero_of_isStrictlyGE a i
      (lt_of_le_of_lt (min_le_left _ _) (by omega))
  rw [nonposStructureComplex_X_of_le X (min_le_right _ _)] at hzero
  exact not_isZero_unit X hzero

/-- On any nonempty scheme, the mapping cone of the identity of `nonposStructureComplex X` is
contractible (hence acyclic and quasi-isomorphic to `0`), yet still not strictly perfect. This
shows that strict perfectness is not invariant under homotopy equivalence or quasi-isomorphism. -/
theorem not_isStrictlyPerfect_mappingCone_id_nonposStructureComplex (X : Scheme.{u}) [Nonempty X] :
    ¬ isStrictlyPerfect X (CochainComplex.mappingCone (𝟙 (nonposStructureComplex X))) := by
  intro h
  obtain ⟨a, _, ha, _⟩ := (CochainComplex.bounded_iff _ _).mp h.1
  let i : ℤ := min (a - 1) 0
  have hzero : IsZero ((CochainComplex.mappingCone (𝟙 (nonposStructureComplex X))).X i) :=
    (CochainComplex.mappingCone (𝟙 (nonposStructureComplex X))).isZero_of_isStrictlyGE a i
      (lt_of_le_of_lt (min_le_left _ _) (by omega))
  have hterm : IsZero ((nonposStructureComplex X).X i) :=
    ((CochainComplex.mappingCone.isZero_X_iff _ i).mp hzero).2
  rw [nonposStructureComplex_X_of_le X (min_le_right _ _)] at hterm
  exact not_isZero_unit X hterm

end EmptyAndNonExample

end

end AlgebraicGeometry.Scheme.Modules
