/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Bifunctor.Colimit
public import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
public import TauCeti.Algebra.Homology.ShortComplex.Colimit
public import TauCeti.Algebra.Homology.Single.Coproduct
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.BifunctorShift
import TauCeti.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.HomotopyCofiber
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# K-flat cochain complexes

A cochain complex is K-flat if tensoring it with any acyclic complex is acyclic.
Flatness of an object is expressed by exactness of its tensor functor. A flat object
in any integer degree is K-flat, and a bounded complex of flat objects is K-flat.
The statements apply to modules and to sheaves of modules without choosing points
of the underlying site.

K-flatness is invariant under homotopy equivalence and shifts, and has the two out of three
property in degreewise split short exact sequences, so the mapping cone of a morphism of K-flat
complexes is K-flat. Tensoring with a K-flat complex preserves quasi-isomorphisms, and this
characterizes K-flat complexes; it is the property that makes K-flat complexes compute derived
tensor products.

K-flat complexes are closed under colimits whose shape has exact colimits in the
underlying category and commutes with tensoring by each object, such as filtered
colimits of modules. A complex which is bounded above is the sequential colimit of
its brutal truncations, so a bounded above complex of flat objects is K-flat. A
complex with zero differentials is the coproduct of its terms, so it is K-flat when
its terms are flat and countable coproducts are exact. Some bound or condition on the
differentials is needed: an unbounded acyclic complex of flat objects need not be
K-flat. K-flat resolutions of unbounded complexes are constructed in
`TauCeti.Algebra.Homology.Monoidal.KFlat.Resolution`.

## Main results

* `CochainComplex.isKFlat_of_homotopyEquiv`, `CochainComplex.isKFlat_shift_iff`: invariance
  under homotopy equivalence and shifts.
* `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₁`, `isKFlat_X₂`, `isKFlat_X₃`: two out of
  three in a degreewise split short exact sequence.
* `CochainComplex.isKFlat_mappingCone`: mapping cones of morphisms of K-flat complexes.
* `CochainComplex.quasiIso_id_tensorHom`, `CochainComplex.isKFlat_iff_quasiIso_id_tensorHom`:
  tensoring with a K-flat complex preserves quasi-isomorphisms, and this characterizes
  K-flatness.
* `CochainComplex.isKFlat_single_of_flat`, `CochainComplex.isKFlat_of_bounded_flat`: flat
  objects and bounded complexes of flat objects are K-flat.
* `CochainComplex.isKFlat_of_isColimit`: closure under suitable colimits.
* `CochainComplex.isKFlat_of_boundedAbove_flat`: bounded above complexes of flat objects are
  K-flat.
* `CochainComplex.isKFlat_of_d_eq_zero`: complexes with zero differentials and flat terms are
  K-flat.

The tensor factor containing the K-flat complex is placed on the left. In a symmetric
monoidal category this is the usual K-flat condition, with the two factors interchanged
by the Koszul symmetry.

## References

* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
* The Stacks Project, More on Algebra, Section 15.60, K-flat complexes, in particular Tag
  06Y2 for shifts and the two out of three property.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

namespace CochainComplex

/-- A complex is K-flat if tensoring it on the left preserves acyclicity. -/
class IsKFlat (K : CochainComplex C ℤ) : Prop where
  /-- Tensoring a K-flat complex with an acyclic complex gives an acyclic complex. -/
  acyclic_tensor (A : CochainComplex C ℤ) : A.Acyclic → (tensorObj K A).Acyclic

/-- The characteristic acyclicity criterion for K-flatness. -/
lemma isKFlat_iff (K : CochainComplex C ℤ) :
    K.IsKFlat ↔ ∀ A : CochainComplex C ℤ, A.Acyclic → (tensorObj K A).Acyclic :=
  ⟨fun h ↦ h.acyclic_tensor, fun h ↦ ⟨h⟩⟩

/-- K-flatness is invariant under an isomorphism of complexes. -/
lemma isKFlat_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) [K.IsKFlat] :
    L.IsKFlat := by
  constructor
  intro A hA i
  exact ExactAt.of_iso (IsKFlat.acyclic_tensor A hA i)
    (((curriedTensor C).map₂CochainComplex.flip.obj A).mapIso e)

/-- K-flatness is invariant under homotopy equivalence, so it is a property of objects of the
homotopy category. -/
theorem isKFlat_of_homotopyEquiv {K L : CochainComplex C ℤ} (e : HomotopyEquiv K L)
    [K.IsKFlat] : L.IsKFlat := by
  constructor
  intro A hA i
  exact (exactAt_iff_of_quasiIsoAt
    (HomotopyEquiv.mapBifunctor (curriedTensor C) (.up ℤ) e (HomotopyEquiv.refl A)).hom i).1
      (IsKFlat.acyclic_tensor A hA i)

/-- A shift of a K-flat complex is K-flat. -/
instance isKFlat_shift (K : CochainComplex C ℤ) [K.IsKFlat] (n : ℤ) : (K⟦n⟧).IsKFlat := by
  constructor
  intro A hA i
  refine ExactAt.of_iso ?_ (mapBifunctorShift₁Iso K A (curriedTensor C) n).symm
  exact (exactAt_shift_iff (tensorObj K A) n i (n + i) rfl).2 (IsKFlat.acyclic_tensor A hA _)

/-- A complex is K-flat if and only if any of its shifts is. -/
@[simp]
lemma isKFlat_shift_iff (K : CochainComplex C ℤ) (n : ℤ) : (K⟦n⟧).IsKFlat ↔ K.IsKFlat :=
  ⟨fun _ ↦ isKFlat_of_iso (K := (K⟦n⟧)⟦-n⟧)
    ((shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app K),
    fun _ ↦ inferInstance⟩

end CochainComplex

namespace CategoryTheory.ShortComplex.ShortExact

/-- K-flatness is preserved by degreewise split extensions of complexes. -/
theorem isKFlat_X₂ {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)]
    [S.X₁.IsKFlat] [S.X₃.IsKFlat] : S.X₂.IsKFlat := by
  constructor
  intro A hA
  exact (shortExact_tensorRightShortComplex A S hS).acyclic_X₂
    (CochainComplex.IsKFlat.acyclic_tensor A hA) (CochainComplex.IsKFlat.acyclic_tensor A hA)

/-- K-flatness passes to the subcomplex in a degreewise split extension of complexes whose
middle and quotient terms are K-flat. -/
theorem isKFlat_X₁ {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)]
    [S.X₂.IsKFlat] [S.X₃.IsKFlat] : S.X₁.IsKFlat := by
  constructor
  intro A hA
  have h₂ := CochainComplex.IsKFlat.acyclic_tensor (K := S.X₂) A hA
  have h₃ := CochainComplex.IsKFlat.acyclic_tensor (K := S.X₃) A hA
  have hT := shortExact_tensorRightShortComplex A S hS
  exact hT.acyclic_X₁ ((_root_.quasiIso_iff _).2 fun i ↦
    (quasiIsoAt_iff_exactAt _ i (h₂ i)).2 (h₃ i))

/-- K-flatness passes to the quotient in a degreewise split extension of complexes whose
subcomplex and middle terms are K-flat. -/
theorem isKFlat_X₃ {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)]
    [S.X₁.IsKFlat] [S.X₂.IsKFlat] : S.X₃.IsKFlat := by
  constructor
  intro A hA
  have h₁ := CochainComplex.IsKFlat.acyclic_tensor (K := S.X₁) A hA
  have h₂ := CochainComplex.IsKFlat.acyclic_tensor (K := S.X₂) A hA
  have hT := shortExact_tensorRightShortComplex A S hS
  exact hT.acyclic_X₃ ((_root_.quasiIso_iff _).2 fun i ↦
    (quasiIsoAt_iff_exactAt _ i (h₁ i)).2 (h₂ i))

end CategoryTheory.ShortComplex.ShortExact

namespace CochainComplex

/-- A flat object placed in any integer degree is K-flat. -/
theorem isKFlat_single_of_flat (M : C) (n : ℤ)
    [PreservesFiniteLimits (tensorLeft M)] [PreservesFiniteColimits (tensorLeft M)] :
    IsKFlat ((single C (.up ℤ) n).obj M) := by
  constructor
  intro A hA i
  let e := ((curriedTensor C).mapBifunctorSingleRowNatIso M n).app A
  refine ExactAt.of_iso (L := tensorObj ((single C (.up ℤ) n).obj M) A) ?_ e.symm
  exact (exactAt_shift_iff (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj A)
    (-n) i (-n + i) rfl).2 ((hA _).map (tensorLeft M))

/-- The mapping cone of a morphism between K-flat complexes is K-flat. -/
instance isKFlat_mappingCone {K L : CochainComplex C ℤ} (φ : K ⟶ L) [K.IsKFlat] [L.IsKFlat] :
    (mappingCone φ).IsKFlat := by
  let S := mappingCone.triangleRotateShortComplex φ
  have hS : S.ShortExact := shortExact_of_degreewise_shortExact _ fun n ↦
    (mappingCone.triangleRotateShortComplexSplitting φ n).shortExact
  have (n : ℤ) : IsSplitMono (S.f.f n) :=
    (mappingCone.triangleRotateShortComplexSplitting φ n).isSplitMono_f
  have : S.X₁.IsKFlat := inferInstanceAs L.IsKFlat
  have : S.X₃.IsKFlat := inferInstanceAs (K⟦(1 : ℤ)⟧).IsKFlat
  exact hS.isKFlat_X₂

section QuasiIso

variable (K : CochainComplex C ℤ) [K.IsKFlat]

/-- Tensoring with a K-flat complex preserves quasi-isomorphisms which are split monomorphisms in
each degree: their cokernel is acyclic, and stays so after tensoring. -/
private lemma quasiIso_id_tensorHom_of_isSplitMono {A B : CochainComplex C ℤ} (i : A ⟶ B)
    [QuasiIso i] [∀ n, IsSplitMono (i.f n)] : QuasiIso (tensorHom (𝟙 K) i) := by
  have : Mono i := mono_of_mono_f i fun _ ↦ inferInstance
  have hS := TauCeti.cokernelSequence_shortExact i
  have (n : ℤ) : IsSplitMono ((ShortComplex.cokernelSequence i).f.f n) :=
    inferInstanceAs (IsSplitMono (i.f n))
  have hA : (ShortComplex.cokernelSequence i).X₃.Acyclic := hS.quasiIso_f_iff.1 ‹_›
  exact (shortExact_tensorLeftShortComplex K hS).quasiIso_f_iff.2
    (IsKFlat.acyclic_tensor _ hA)

/-- Tensoring with a K-flat complex preserves the projection `Z ⊞ B ⟶ B` when `Z` is acyclic: its
kernel `Z` stays acyclic after tensoring. -/
private lemma quasiIso_id_tensorHom_biprod_snd {Z B : CochainComplex C ℤ} (hZ : Z.Acyclic) :
    QuasiIso (tensorHom (𝟙 K) (biprod.snd : Z ⊞ B ⟶ B)) := by
  have hS := (ShortComplex.Splitting.ofHasBinaryBiproduct Z B).shortExact
  have (n : ℤ) : IsSplitMono ((biprod.inl : Z ⟶ Z ⊞ B).f n) :=
    IsSplitMono.mk' ⟨(biprod.fst : Z ⊞ B ⟶ Z).f n, by rw [← comp_f, biprod.inl_fst, id_f]⟩
  exact (shortExact_tensorLeftShortComplex K hS).quasiIso_g_iff.2 (IsKFlat.acyclic_tensor _ hZ)

/-- **Tensoring with a K-flat complex preserves quasi-isomorphisms.** -/
instance quasiIso_id_tensorHom {A B : CochainComplex C ℤ} (f : A ⟶ B) [QuasiIso f] :
    QuasiIso (tensorHom (𝟙 K) f) := by
  -- Factor `f` as `A ⟶ Z ⊞ B ⟶ B`, where `Z` is the acyclic mapping cone of `𝟙 A`, the first map
  -- is `(inr, f)`, split in each degree, and the second is the projection.
  let Z := homotopyCofiber (𝟙 A)
  have hZ : Z.Acyclic := homotopyCofiber.acyclic_id A fun j ↦ ⟨j - 1, by simp⟩
  let i : A ⟶ Z ⊞ B := biprod.lift (homotopyCofiber.inr (𝟙 A)) f
  have (n : ℤ) : IsSplitMono (i.f n) := IsSplitMono.mk'
    { retraction := (biprod.fst : Z ⊞ B ⟶ Z).f n ≫ homotopyCofiber.sndX (𝟙 A) n
      id := by
        rw [← Category.assoc, ← comp_f, biprod.lift_fst, homotopyCofiber.inr_f,
          homotopyCofiber.inrX_sndX] }
  have hf : i ≫ biprod.snd = f := biprod.lift_snd _ _
  have : QuasiIso (biprod.snd : Z ⊞ B ⟶ B) :=
    ((ShortComplex.Splitting.ofHasBinaryBiproduct Z B).shortExact).quasiIso_g_iff.2 hZ
  have : QuasiIso i := (quasiIso_iff_comp_right i biprod.snd).1 (hf ▸ ‹_›)
  have := quasiIso_id_tensorHom_of_isSplitMono K i
  have := quasiIso_id_tensorHom_biprod_snd K (B := B) hZ
  have e : tensorHom (𝟙 K) f = tensorHom (𝟙 K) i ≫ tensorHom (𝟙 K) biprod.snd := by
    simpa [hf] using mapBifunctorMap_comp (curriedTensor C) (.up ℤ) (𝟙 K) (𝟙 K) i biprod.snd
  rw [e]
  infer_instance

end QuasiIso

open ZeroObject in
/-- A complex is K-flat if and only if tensoring with it preserves quasi-isomorphisms. -/
theorem isKFlat_iff_quasiIso_id_tensorHom (K : CochainComplex C ℤ) :
    K.IsKFlat ↔ ∀ ⦃A B : CochainComplex C ℤ⦄ (f : A ⟶ B) [QuasiIso f],
      QuasiIso (tensorHom (𝟙 K) f) := by
  refine ⟨fun _ _ _ f _ ↦ inferInstance, fun h ↦ ⟨fun A hA i ↦ ?_⟩⟩
  have : QuasiIso (0 : A ⟶ 0) := (quasiIso_iff _).2 fun j ↦
    (quasiIsoAt_iff_exactAt' _ j (acyclic_of_isZero _ (isZero_zero _) j)).2 (hA j)
  have hz : IsZero (tensorObj K (0 : CochainComplex C ℤ)) :=
    ((curriedTensor C).mapBifunctorLeft (.up ℤ) (.up ℤ) K).map_isZero (isZero_zero _)
  exact (quasiIsoAt_iff_exactAt' (tensorHom (𝟙 K) (0 : A ⟶ 0)) i
    (acyclic_of_isZero _ hz i)).1 inferInstance

section Colimit

variable {S : Type*} [Category* S] [HasColimitsOfShape S C] [HasExactColimitsOfShape S C]
  [∀ X : C, PreservesColimitsOfShape S (tensorRight X)]

/-- A colimit of K-flat complexes is K-flat, for colimits of a shape that are exact in `C` and
commute with tensoring by each object. For modules over a commutative ring this applies to every
filtered colimit. -/
theorem isKFlat_of_isColimit {G : S ⥤ CochainComplex C ℤ} {s : Cocone G} (hs : IsColimit s)
    [∀ j, (G.obj j).IsKFlat] : s.pt.IsKFlat := by
  have (X : C) : PreservesColimitsOfShape S ((curriedTensor C).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape S (tensorRight X))
  constructor
  intro A hA i
  -- tensoring with `A` and then taking homology in degree `i` preserves the colimit, and the
  -- homology of each `G j ⊗ A` vanishes
  have hH := isColimitOfPreserves (homologyFunctor C (.up ℤ) i)
    (isColimitOfPreserves ((curriedTensor C).map₂CochainComplex.flip.obj A) hs)
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  exact hH.hom_ext fun j ↦
    ((exactAt_iff_isZero_homology _ _).1 (IsKFlat.acyclic_tensor A hA i)).eq_of_src _ _

end Colimit

section ZeroDifferential

variable [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  [∀ X : C, PreservesColimitsOfShape (Discrete ℤ) (tensorRight X)]

/-- A cochain complex with zero differentials and flat terms is K-flat, when countable
coproducts in `C` are exact and commute with tensoring by each object. -/
theorem isKFlat_of_d_eq_zero (K : CochainComplex C ℤ) (hK : ∀ i j, K.d i j = 0)
    [∀ i, PreservesFiniteLimits (tensorLeft (K.X i))]
    [∀ i, PreservesFiniteColimits (tensorLeft (K.X i))] : K.IsKFlat := by
  have (n : Discrete ℤ) :
      IsKFlat ((Discrete.functor fun n ↦ (single C (.up ℤ) n).obj (K.X n)).obj n) :=
    isKFlat_single_of_flat _ n.as
  exact isKFlat_of_isColimit (G := Discrete.functor fun n ↦ (single C (.up ℤ) n).obj (K.X n))
    (HomologicalComplex.isColimitCofanSingleOfDEqZero K hK)

end ZeroDifferential

section Bounded

variable [∀ M : C, PreservesFiniteColimits (tensorLeft M)]

private theorem isKFlat_of_bounded_flat_aux (a : ℤ) (n : ℕ) :
    ∀ (K : CochainComplex C ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE (a + n)],
      (∀ i, a ≤ i → i ≤ a + n → PreservesFiniteLimits (tensorLeft (K.X i))) →
        K.IsKFlat := by
  induction n with
  | zero =>
    intro K hge hle hflat
    have : K.IsStrictlyLE a := by simpa using hle
    obtain ⟨M, ⟨e⟩⟩ := exists_iso_single K a
    let eM : K.X a ≅ M := (eval C (.up ℤ) a).mapIso e ≪≫ singleObjXSelf (.up ℤ) a M
    have := hflat a le_rfl (by simp)
    have : PreservesFiniteLimits (tensorLeft M) :=
      preservesFiniteLimits_of_natIso ((curriedTensor C).mapIso eM)
    have := isKFlat_single_of_flat M a
    exact isKFlat_of_iso e.symm
  | succ n ih =>
    intro K hge hle hflat
    let b : ℤ := a + n
    have : K.IsStrictlyLE (b + 1) := by simpa [b, Nat.cast_add, Nat.cast_one, add_assoc] using hle
    let T : CochainComplex C ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntLE b)
    have : T.IsStrictlyGE a := inferInstance
    have : T.IsStrictlyLE (a + n) := inferInstanceAs (T.IsStrictlyLE b)
    have : T.IsKFlat := ih T fun i hai hib ↦ by
      obtain ⟨j, hj⟩ : ∃ j, (ComplexShape.embeddingUpIntLE b).f j = i := by
        exact not_forall_not.mp fun h ↦
          (not_lt_of_ge hib) ((ComplexShape.notMem_range_embeddingUpIntLE_iff b i).1 h)
      have := hflat i hai (by omega)
      exact preservesFiniteLimits_of_natIso
        ((curriedTensor C).mapIso (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE b) hj).symm)
    have : PreservesFiniteLimits (tensorLeft (K.X (b + 1))) :=
      hflat (b + 1) (by dsimp [b]; omega) (by dsimp [b]; omega)
    have := isKFlat_single_of_flat (K.X (b + 1)) (b + 1)
    have hS : (K.topShortComplex b).ShortExact :=
      shortExact_of_degreewise_shortExact _ fun i ↦ (K.topShortComplexSplitting b i).shortExact
    have (i : ℤ) : IsSplitMono ((K.topShortComplex b).f.f i) :=
      (K.topShortComplexSplitting b i).isSplitMono_f
    have : (K.topShortComplex b).X₁.IsKFlat := by
      rw [topShortComplex_X₁]
      infer_instance
    have : (K.topShortComplex b).X₃.IsKFlat := by
      rw [topShortComplex_X₃]
      exact inferInstanceAs T.IsKFlat
    simpa only [topShortComplex_X₂] using hS.isKFlat_X₂

/-- A bounded cochain complex of flat objects is K-flat. The bounds concern the actual terms,
rather than only the homology objects. -/
theorem isKFlat_of_bounded_flat (K : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, PreservesFiniteLimits (tensorLeft (K.X i))] : K.IsKFlat := by
  have : K.IsStrictlyLE (a + (b - a).natAbs) :=
    isStrictlyLE_of_le K b _ (by have := Int.le_natAbs (a := b - a); omega)
  exact isKFlat_of_bounded_flat_aux a (b - a).natAbs K fun _ _ _ ↦ inferInstance

/-- A bounded above cochain complex of flat objects is K-flat, when sequential colimits in `C`
are exact and commute with tensoring by each object, as for modules over a commutative ring. -/
theorem isKFlat_of_boundedAbove_flat [HasColimitsOfShape ℕ C] [HasExactColimitsOfShape ℕ C]
    [∀ X : C, PreservesColimitsOfShape ℕ (tensorRight X)] (K : CochainComplex C ℤ) (b : ℤ)
    [K.IsStrictlyLE b] [∀ i, PreservesFiniteLimits (tensorLeft (K.X i))] : K.IsKFlat := by
  have (m : ℕ) : (K.stupidTruncGESequence.obj m).IsKFlat := by
    let T := kernel (K.πStupidTruncLE (-(m : ℤ) - 1))
    have : T.IsStrictlyGE (-(m : ℤ)) :=
      (T.isStrictlyGE_iff _).2 fun _ hi ↦ K.isZero_kernel_πStupidTruncLE_X _ (by omega)
    have : T.IsStrictlyLE (-(m : ℤ) + (b + m).natAbs) := T.isStrictlyLE_of_le b _ (by omega)
    -- in degrees `≥ -m` the terms of `T` are those of `K`
    refine isKFlat_of_bounded_flat_aux (-(m : ℤ)) (b + m).natAbs T fun i hi _ ↦ ?_
    have := K.isIso_kernel_ι_πStupidTruncLE_f (-(m : ℤ) - 1) (i := i) (by omega)
    exact preservesFiniteLimits_of_natIso
      ((curriedTensor C).mapIso (asIso ((kernel.ι (K.πStupidTruncLE _)).f i)).symm)
  exact isKFlat_of_isColimit K.isColimitStupidTruncGESequenceCocone

end Bounded

end CochainComplex
