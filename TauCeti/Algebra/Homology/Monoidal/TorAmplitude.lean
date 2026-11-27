/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
import TauCeti.Algebra.Homology.Monoidal.Flat

/-!
# Tor-amplitude in the derived category

Tor-amplitude tests cohomological bounds after derived tensoring with objects of the abelian
category placed in degree zero. A K-flat complex computes these tests by termwise tensoring.
In particular, a bounded complex of flat objects has Tor-amplitude in the interval of its terms.
If bounded-above flat K-flat resolutions are available, Tor-amplitude also gives a bounded flat
representative by lower cohomological truncation.

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

/-- Tor-amplitude is equivalent to the lower and upper bounds on every derived tensor test. -/
lemma hasTorAmplitude_def {K : DerivedCategory C} {a b : ℤ} :
    K.HasTorAmplitude a b ↔
      ∀ M : C, (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsGE a ∧
        (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsLE b := Iff.rfl

/-- A cohomological test for Tor-amplitude. -/
lemma hasTorAmplitude_iff {K : DerivedCategory C} {a b : ℤ} :
    K.HasTorAmplitude a b ↔ ∀ (M : C) (i : ℤ), i < a ∨ b < i →
      IsZero ((homologyFunctor C i).obj
        (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M))) := by
  simp only [hasTorAmplitude_def, isGE_iff, isLE_iff]
  exact ⟨fun h M i hi ↦ hi.elim ((h M).1 i) ((h M).2 i),
    fun h M ↦ ⟨fun i hi ↦ h M i (.inl hi), fun i hi ↦ h M i (.inr hi)⟩⟩

namespace HasTorAmplitude

variable {a b : ℤ} {K L : DerivedCategory C}

/-- Separate lower and upper bounds on all derived tensor tests give a Tor-amplitude bound. -/
lemma of_isGE_isLE
    (ha : ∀ M : C, (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsGE a)
    (hb : ∀ M : C, (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsLE b) :
    K.HasTorAmplitude a b :=
  hasTorAmplitude_def.mpr fun M ↦ ⟨ha M, hb M⟩

/-- A Tor-amplitude bound gives a lower bound on the derived tensor test at `M`. -/
lemma isGE_derivedTensor (h : K.HasTorAmplitude a b) (M : C) :
    (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsGE a :=
  (hasTorAmplitude_def.mp h M).1

/-- A Tor-amplitude bound gives an upper bound on the derived tensor test at `M`. -/
lemma isLE_derivedTensor (h : K.HasTorAmplitude a b) (M : C) :
    (((TauCeti.derivedTensor C).obj K).obj ((singleFunctor C 0).obj M)).IsLE b :=
  (hasTorAmplitude_def.mp h M).2

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
    h.isGE_derivedTensor (𝟙_ C)
  exact TStructure.t.isGE_of_iso ((TauCeti.derivedTensorRightUnitor C).app K) a

/-- A Tor-amplitude bound gives an upper cohomology bound by testing with the tensor unit. -/
lemma isLE (h : K.HasTorAmplitude a b) : K.IsLE b := by
  have : (((TauCeti.derivedTensor C).flip.obj ((singleFunctor C 0).obj (𝟙_ C))).obj K).IsLE b :=
    h.isLE_derivedTensor (𝟙_ C)
  exact TStructure.t.isLE_of_iso ((TauCeti.derivedTensorRightUnitor C).app K) b

end HasTorAmplitude

/-- On a K-flat model, Tor-amplitude is equivalent to cohomology bounds on termwise tensors
with every object. -/
lemma hasTorAmplitude_Q_obj_iff (P : CochainComplex C ℤ) [P.IsKFlat] (a b : ℤ) :
    (Q.obj P).HasTorAmplitude a b ↔
      ∀ M : C, CochainComplex.IsGE (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P) a ∧
        CochainComplex.IsLE (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P) b := by
  rw [hasTorAmplitude_def]
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

/-- If every complex strictly bounded above by `b` has a K-flat resolution by flat objects
with the same upper bound, then Tor-amplitude in `[a, b]` is equivalent to admitting a flat
representative whose terms vanish outside `[a, b]`. -/
theorem hasTorAmplitude_iff_exists_flat_model_of_exists_quasiIso
    [∀ M : C, PreservesFiniteColimits (tensorLeft M)]
    {K : DerivedCategory C} {a b : ℤ}
    (hresolve : ∀ L : CochainComplex C ℤ, L.IsStrictlyLE b →
      ∃ (P : CochainComplex C ℤ) (π : P ⟶ L) (_ : QuasiIso π)
        (_ : ∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) (_ : P.IsKFlat), P.IsStrictlyLE b) :
    K.HasTorAmplitude a b ↔
      ∃ P : CochainComplex C ℤ, P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i, PreservesFiniteLimits (tensorLeft (P.X i))) ∧ Nonempty (Q.obj P ≅ K) := by
  constructor
  · intro hK
    have := hK.isLE
    obtain ⟨L, hL, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
    obtain ⟨P, π, hπ, hflat, hKFlat, hPb⟩ := hresolve L hL
    let eP : Q.obj P ≅ K := asIso (Q.map π) ≪≫ e.symm
    have hP := hK.of_iso eP.symm
    have : P.IsGE a := (isGE_Q_obj_iff P a).mp hP.isGE
    have h (M : C) :
        (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj P).ExactAt (a - 1) :=
      (CochainComplex.isGE_iff _ a).mp ((hasTorAmplitude_Q_obj_iff P a b).mp hP M).1
        (a - 1) (by omega)
    exact ⟨P.truncGE a, inferInstance, inferInstance,
      fun i ↦ P.preservesFiniteLimits_tensorLeft_truncGE_X a i h,
      ⟨(asIso (Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩
  · rintro ⟨P, hPa, hPb, hflat, ⟨e⟩⟩
    have := P.isKFlat_of_bounded_flat a b
    exact (hasTorAmplitude_Q_obj P a b).of_iso e

end DerivedCategory
