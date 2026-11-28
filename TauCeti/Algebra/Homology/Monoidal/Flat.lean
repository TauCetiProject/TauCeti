/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomologySequence
import TauCeti.CategoryTheory.Abelian.Exact

/-!
# Flatness of opcycles and truncations

Exactness after termwise tensoring makes the opcycles at the boundary of a complex of flat
objects flat. This gives a criterion for the lower cohomological truncation to remain
termwise flat.

## References

* [The Stacks Project, Lemma 20.48.2](https://stacks.math.columbia.edu/tag/08CH)
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex

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
