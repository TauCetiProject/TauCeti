/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
import Mathlib.Algebra.Homology.HomologySequence
import TauCeti.CategoryTheory.Abelian.Exact

/-!
# Tor-amplitude in the derived category

Tor-amplitude tests cohomological bounds after derived tensoring with objects of the abelian
category placed in degree zero. A K-flat complex computes these tests by termwise tensoring.
In particular, a bounded complex of flat objects has Tor-amplitude in the interval of its terms.
For the converse, the flatness criterion for opcycles controls the lowest term of a cohomological
truncation.

## References

* [The Stacks Project, Definition 20.48.1](https://stacks.math.columbia.edu/tag/08CG)
* [The Stacks Project, Lemma 20.48.2](https://stacks.math.columbia.edu/tag/08CH)
* [The Stacks Project, Lemma 20.48.3](https://stacks.math.columbia.edu/tag/08CI)
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (A B : GradedObject ℤ C), GradedObject.HasTensor A B]
  [∀ A, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj A)]
  [∀ B, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj B)]
  [∀ (A B D E : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt A B D E]
  [∀ (A B D : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor A B D]
  [∀ (A B D : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ A B D]
  [BraidedCategory C] [(CochainComplex.KFlat.localizerMorphism C).IsLeftDerivabilityStructure]
  [HasDerivedCategory C]

/-- An object of the derived category has Tor-amplitude in `[a, b]` if its derived tensor product
with every object placed in degree zero has vanishing cohomology outside `[a, b]`. -/
def HasTorAmplitude (K : DerivedCategory C) (a b : ℤ) : Prop :=
  ∀ M : C, (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsGE a ∧
    (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsLE b

/-- A cohomological test for Tor-amplitude. -/
lemma hasTorAmplitude_iff {K : DerivedCategory C} {a b : ℤ} :
    K.HasTorAmplitude a b ↔ ∀ (M : C) (i : ℤ), i < a ∨ b < i →
      IsZero ((homologyFunctor C i).obj
        (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M))) := by
  simp only [HasTorAmplitude, isGE_iff, isLE_iff]
  exact ⟨fun h M i hi ↦ hi.elim ((h M).1 i) ((h M).2 i),
    fun h M ↦ ⟨fun i hi ↦ h M i (.inl hi), fun i hi ↦ h M i (.inr hi)⟩⟩

namespace HasTorAmplitude

variable {a b : ℤ} {K L : DerivedCategory C}

/-- Tor-amplitude is invariant under isomorphisms in the derived category. -/
lemma of_iso (h : K.HasTorAmplitude a b) (e : K ≅ L) : L.HasTorAmplitude a b :=
  hasTorAmplitude_iff.mpr fun M i hi ↦
    (hasTorAmplitude_iff.mp h M i hi).of_iso
      ((homologyFunctor C i).mapIso (((TauCeti.derivedTensor C).mapIso e.symm).app _))

/-- Enlarging a Tor interval preserves the amplitude bound. -/
lemma mono (h : K.HasTorAmplitude a b) {a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b') :
    K.HasTorAmplitude a' b' :=
  hasTorAmplitude_iff.mpr fun M i hi ↦
    hasTorAmplitude_iff.mp h M i (hi.imp (·.trans_le ha) (hb.trans_lt ·))

/-- A Tor-amplitude bound gives a lower cohomology bound by testing with the tensor unit. -/
lemma isGE (h : K.HasTorAmplitude a b) : K.IsGE a := by
  have : (((TauCeti.derivedTensor C).flip.obj ((singleFunctor C 0).obj (𝟙_ C))).obj K).IsGE a :=
    (h (𝟙_ C)).1
  exact TStructure.t.isGE_of_iso ((TauCeti.derivedTensorRightUnitor C).app K) a

/-- A Tor-amplitude bound gives an upper cohomology bound by testing with the tensor unit. -/
lemma isLE (h : K.HasTorAmplitude a b) : K.IsLE b := by
  have : (((TauCeti.derivedTensor C).flip.obj ((singleFunctor C 0).obj (𝟙_ C))).obj K).IsLE b :=
    (h (𝟙_ C)).2
  exact TStructure.t.isLE_of_iso ((TauCeti.derivedTensorRightUnitor C).app K) b

end HasTorAmplitude

/-- On a K-flat model, Tor-amplitude is equivalent to cohomology bounds on termwise tensors
with every object. -/
lemma hasTorAmplitude_Q_obj_iff (P : CochainComplex C ℤ) [P.IsKFlat] (a b : ℤ) :
    (Q.obj P).HasTorAmplitude a b ↔
      ∀ M : C, CochainComplex.IsGE (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P) a ∧
        CochainComplex.IsLE (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P) b := by
  unfold HasTorAmplitude
  refine forall_congr' fun M ↦ ?_
  let S := (CochainComplex.singleFunctor C 0).obj M
  let e := CochainComplex.derivedTensorKFlatLeftIso P S ≪≫
    Q.mapIso (tensorBraiding P S ≪≫ ((curriedTensor C).mapBifunctorSingleRowZeroNatIso M).app P)
  rw [← isGE_Q_obj_iff, ← isLE_Q_obj_iff, ← Q_obj_single_obj]
  exact and_congr
    ⟨fun _ ↦ TStructure.t.isGE_of_iso e a, fun _ ↦ TStructure.t.isGE_of_iso e.symm a⟩
    ⟨fun _ ↦ TStructure.t.isLE_of_iso e b, fun _ ↦ TStructure.t.isLE_of_iso e.symm b⟩

/-- A bounded K-flat complex has Tor-amplitude in the interval of its terms. -/
lemma hasTorAmplitude_Q_obj (P : CochainComplex C ℤ) (a b : ℤ) [P.IsKFlat]
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] : (Q.obj P).HasTorAmplitude a b := by
  rw [hasTorAmplitude_Q_obj_iff]
  intro M
  let T : CochainComplex C ℤ := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P
  have : T.IsStrictlyGE a := (T.isStrictlyGE_iff a).2 fun i hi ↦
    (tensorLeft M).map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : T.IsStrictlyLE b := (T.isStrictlyLE_iff b).2 fun i hi ↦
    (tensorLeft M).map_isZero (P.isZero_of_isStrictlyLE b i hi)
  exact ⟨inferInstanceAs (T.IsGE a), inferInstanceAs (T.IsLE b)⟩

/-- A flat object placed in one degree has Tor-amplitude concentrated in that degree. -/
lemma hasTorAmplitude_singleFunctor_obj (M : C) (n : ℤ)
    [PreservesFiniteLimits (tensorLeft M)] [PreservesFiniteColimits (tensorLeft M)] :
    ((singleFunctor C n).obj M).HasTorAmplitude n n := by
  have := CochainComplex.isKFlat_single_of_flat M n
  rw [← Q_obj_single_obj]
  exact hasTorAmplitude_Q_obj ((single C (.up ℤ) n).obj M) n n

end DerivedCategory

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [∀ M : C, PreservesFiniteColimits (tensorLeft M)]

/-- If tensoring a chain complex of flat objects with any object gives an exact sequence at
degree one, then the cokernel of the differential into degree zero is flat. -/
lemma preservesFiniteLimits_tensorLeft_opcycles_zero_of_exactAt (P : ChainComplex C ℕ)
    [∀ i, PreservesFiniteLimits (tensorLeft (P.X i))]
    (h : ∀ M : C, (((tensorLeft M).mapHomologicalComplex (.down ℕ)).obj P).ExactAt 1) :
    PreservesFiniteLimits (tensorLeft (P.opcycles 0)) := by
  let F : C ⥤ ChainComplex C ℕ :=
    { obj M := ((tensorLeft M).mapHomologicalComplex (.down ℕ)).obj P
      map f := (NatTrans.mapHomologicalComplex ((curriedTensor C).map f) _).app P
      map_id M := by ext i; simp
      map_comp f g := by ext i; simp }
  have hF (i : ℕ) : F ⋙ eval C (.down ℕ) i = tensorRight (P.X i) := rfl
  have : F.PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext i; simp [F]⟩
  have hmono {M N : C} (f : M ⟶ N) [Mono f] : Mono (opcyclesMap (F.map f) 0) := by
    let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
    have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel f) }
    have hSF : (S.map F).ShortExact := shortExact_of_degreewise_shortExact _ fun i ↦ by
      rw [← ShortComplex.map_comp]
      have := preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (P.X i))
      have := preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (P.X i))
      exact ShortComplex.shortExact_of_iso (S.mapNatIso (eqToIso (hF i)).symm)
        (hS.map (tensorRight (P.X i)))
    -- Vanishing in degree one makes the first map on degree-zero homology monic.
    have : Mono (homologyMap (F.map f) 0) :=
      (hSF.homology_exact₁ 1 0 (by simp)).mono_g ((h (cokernel f)).isZero_homology.eq_of_src _ _)
    have : Mono ((F.obj M).homologyι 0 ≫ opcyclesMap (F.map f) 0) := by
      rw [← homologyι_naturality]
      infer_instance
    simpa using mono_comp (inv ((F.obj M).homologyι 0))
      ((F.obj M).homologyι 0 ≫ opcyclesMap (F.map f) 0)
  -- Right exactness identifies the degree-zero opcycles of each tensor with a tensor of opcycles.
  have hcol (M : C) :=
    CokernelCofork.mapIsColimit _ (P.opcyclesIsCokernel 1 0 (by simp)) (tensorLeft M)
  let e (M : C) : (F.obj M).opcycles 0 ≅ (tensorRight (P.opcycles 0)).obj M :=
    (F.obj M).opcyclesIsCokernel 1 0 (by simp) |>.coconePointUniqueUpToIso (hcol M)
  have he (M : C) : (F.obj M).pOpcycles 0 ≫ (e M).hom =
      (tensorLeft M).map (P.pOpcycles 0) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      ((F.obj M).opcyclesIsCokernel 1 0 (by simp)) (hcol M) WalkingParallelPair.one
  have : (tensorRight (P.opcycles 0)).PreservesMonomorphisms := by
    constructor
    intro M N f _
    have hf : opcyclesMap (F.map f) 0 ≫ (e N).hom = (e M).hom ≫
        (tensorRight (P.opcycles 0)).map f := by
      rw [← cancel_epi ((F.obj M).pOpcycles 0), p_opcyclesMap_assoc, he, ← Category.assoc, he]
      exact ((curriedTensor C).map f).naturality (P.pOpcycles 0) |>.symm
    have := hmono f
    have : Mono ((e M).hom ≫ (tensorRight (P.opcycles 0)).map f) := hf ▸ mono_comp _ _
    simpa using mono_comp (e M).inv ((e M).hom ≫ (tensorRight (P.opcycles 0)).map f)
  let braiding := BraidedCategory.tensorLeftIsoTensorRight (P.opcycles 0)
  have := preservesFiniteColimits_of_natIso braiding
  have := (tensorRight (P.opcycles 0)).preservesFiniteLimits_of_preservesMonomorphisms
  exact preservesFiniteLimits_of_natIso braiding.symm

end ChainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [BraidedCategory C] [∀ M : C, PreservesFiniteColimits (tensorLeft M)]

/-- If all termwise tensors of a complex of flat objects are exact at `a - 1`, the quotient of
its degree-`a` term by the incoming differential is flat. -/
lemma preservesFiniteLimits_tensorLeft_opcycles_of_exactAt (P : CochainComplex C ℤ) (a : ℤ)
    [∀ i, PreservesFiniteLimits (tensorLeft (P.X i))]
    (h : ∀ M : C, (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    PreservesFiniteLimits (tensorLeft (P.opcycles a)) := by
  let e := ComplexShape.embeddingUpIntLE a
  let T := P.restriction e
  have (i : ℕ) : PreservesFiniteLimits (tensorLeft (T.X i)) :=
    ‹∀ i, PreservesFiniteLimits (tensorLeft (P.X i))› (e.f i)
  have hT (M : C) : (((tensorLeft M).mapHomologicalComplex (.down ℕ)).obj T).ExactAt 1 := by
    let R := ((tensorLeft M).mapHomologicalComplex (.down ℕ)).obj T
    let U := ((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P
    have hd₁ : (ComplexShape.up ℤ).prev (e.f 1) = e.f 2 := by simp [e]; omega
    have hd₂ : (ComplexShape.up ℤ).next (e.f 1) = e.f 0 := by simp [e]
    apply (R.exactAt_iff' 2 1 0 (by simp) (by simp)).2
    -- The restriction reindexes the two differentials used by this exactness test.
    have hU : U.ExactAt (e.f 1) := h M
    exact (U.exactAt_iff' (e.f 2) (e.f 1) (e.f 0) hd₁ hd₂).1 hU
  have := ChainComplex.preservesFiniteLimits_tensorLeft_opcycles_zero_of_exactAt T hT
  have hd : (ComplexShape.up ℤ).prev (e.f 0) = e.f 1 := by simp [e]
  have ee : T.opcycles 0 ≅ P.opcycles (e.f 0) :=
    (T.opcyclesIsCokernel 1 0 (by simp)).coconePointUniqueUpToIso (P.opcyclesIsCokernel _ _ hd)
  simpa [e] using preservesFiniteLimits_of_natIso ((curriedTensor C).mapIso ee)

/-- The lower cohomological truncation of a complex of flat objects is termwise flat if the
termwise tensors are exact immediately below the truncation degree. -/
lemma preservesFiniteLimits_tensorLeft_truncGE_X (P : CochainComplex C ℤ) (a i : ℤ)
    [∀ j, PreservesFiniteLimits (tensorLeft (P.X j))]
    (h : ∀ M : C, (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1)) :
    PreservesFiniteLimits (tensorLeft ((P.truncGE a).X i)) := by
  obtain hi | rfl | hi := lt_trichotomy i a
  · let F := tensorLeft ((P.truncGE a).X i)
    have hF : IsZero F := (Functor.isZero_iff _).2 fun M ↦
      (tensorRight M).map_isZero ((P.truncGE a).isZero_of_isStrictlyGE a i hi)
    let := F.preservesLimitsOfSize_of_isZero hF
    exact inferInstanceAs (PreservesFiniteLimits F)
  · have := P.preservesFiniteLimits_tensorLeft_opcycles_of_exactAt i h
    exact preservesFiniteLimits_of_natIso ((curriedTensor C).mapIso (P.truncGEXIsoOpcycles i).symm)
  · exact preservesFiniteLimits_of_natIso ((curriedTensor C).mapIso (P.truncGEXIso a i hi).symm)

end CochainComplex
