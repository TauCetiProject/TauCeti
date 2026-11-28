/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import TauCeti.CategoryTheory.Monoidal.Mono
public import TauCeti.CategoryTheory.Monoidal.Tor.Basic

/-!
# Balance of `Tor₁`

Mathlib's `CategoryTheory.Tor C n` derives the tensor product in its second variable, so
`((Tor C 1).obj X).obj M` is `L₁(X ⊗ -)(M)`, and `CategoryTheory.Tor' C n` derives it in its
first variable, so `((Tor' C 1).obj X).obj M` is `L₁(- ⊗ M)(X)`. This file proves that the two
agree, `Tor₁(X, M) ≅ Tor'₁(X, M)`, when both variables have projective presentations of length
one and tensoring is right exact and keeps the relevant monomorphisms of projectives.

Let `S : 0 ⟶ Q₁ ⟶ Q₀ ⟶ X ⟶ 0` and `T : 0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` be such presentations. The kernel
descriptions of `TauCeti.CategoryTheory.Monoidal.Tor.Basic` identify `Tor₁(X, M)` with the kernel of
`X ◁ T.f` (`CategoryTheory.ShortComplex.ShortExact.torOneIsoKernel`) and `Tor'₁(X, M)` with the
kernel of `S.f ▷ M` (`CategoryTheory.ShortComplex.ShortExact.tor'OneIsoKernel`). The snake lemma
applied to the map `S ⊗ P₁ ⟶ S ⊗ P₀` induced by `T.f`
(`CategoryTheory.ShortComplex.ShortExact.tensorSnakeInput`), whose cokernel is `S ⊗ M`, gives an
exact sequence `ker (Q₀ ◁ T.f) ⟶ ker (X ◁ T.f) ⟶ Q₁ ⊗ M ⟶ Q₀ ⊗ M`. Its first term vanishes when
`Q₀ ◁ T.f` is a monomorphism, which identifies the two kernels
(`CategoryTheory.ShortComplex.ShortExact.kernelWhiskerLeftIsoKernelWhiskerRight`) and so gives
`Tor₁(X, M) ≅ Tor'₁(X, M)` (`CategoryTheory.ShortComplex.ShortExact.torOneIsoTor'One`).

This applies to all `X` and `M` of projective dimension at most one whose chosen projective
covers keep monomorphisms under tensoring, through their chosen projective presentations
(`CategoryTheory.torOneIsoTor'OneOfHasProjectiveDimensionLEOne`), for instance to all modules over
a principal ideal domain, where projective modules are flat.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Theorem 2.7.2 and Section 3.1.
-/

public section

noncomputable section

namespace CategoryTheory

open Limits MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  [∀ Y : C, PreservesFiniteColimits ((tensoringLeft C).obj Y)]
  [∀ Y : C, PreservesFiniteColimits ((tensoringRight C).obj Y)] {S T : ShortComplex C}

namespace ShortComplex.ShortExact

variable (hS : S.ShortExact) (hT : T.ShortExact)

include hS hT in
/-- The snake diagram of the map `S ⊗ T.X₁ ⟶ S ⊗ T.X₂` induced by `T.f`, for short exact `S`
and `T`: its rows are the kernels `ker (S.Xᵢ ◁ T.f)`, the complexes `S ⊗ T.X₁` and `S ⊗ T.X₂`,
and their cokernel `S ⊗ T.X₃`. -/
@[expose, simps]
def tensorSnakeInput [Mono (S.f ▷ T.X₂)] : SnakeInput C where
  L₀ := ShortComplex.mk
    (kernel.map (S.X₁ ◁ T.f) (S.X₂ ◁ T.f) (S.f ▷ T.X₁) (S.f ▷ T.X₂) (whisker_exchange S.f T.f))
    (kernel.map (S.X₂ ◁ T.f) (S.X₃ ◁ T.f) (S.g ▷ T.X₁) (S.g ▷ T.X₂) (whisker_exchange S.g T.f))
    (by ext; simp [← comp_whiskerRight])
  L₁ := S.map ((tensoringRight C).obj T.X₁)
  L₂ := S.map ((tensoringRight C).obj T.X₂)
  L₃ := S.map ((tensoringRight C).obj T.X₃)
  v₀₁ := { τ₁ := kernel.ι _, τ₂ := kernel.ι _, τ₃ := kernel.ι _ }
  v₁₂ := S.mapNatTrans ((tensoringRight C).map T.f)
  v₂₃ := S.mapNatTrans ((tensoringRight C).map T.g)
  w₀₂ := by ext <;> simp
  w₁₃ := by ext <;> simp [← whiskerLeft_comp]
  h₀ := by
    apply isLimitOfIsLimitπ
    all_goals exact (KernelFork.isLimitMapConeEquiv _ _).symm (kernelIsKernel _)
  h₃ := by
    apply isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        (CokernelCofork.mapIsColimit _ hT.gIsCokernel ((tensoringLeft C).obj _))
  L₁_exact := hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
  epi_L₁_g := by
    have := hS.epi_g
    rw [ShortComplex.map_g]
    infer_instance
  L₂_exact := hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance
  mono_L₂_f := by
    rw [ShortComplex.map_f, Functor.flip_obj_map, curriedTensor_map_app]
    infer_instance

/-- For short exact `S` and `T` with `S.X₂ ◁ T.f` and `S.f ▷ T.X₂` monomorphisms, the kernels of
`S.X₃ ◁ T.f` and of `S.f ▷ T.X₃` agree, through the connecting map of the snake lemma. -/
def kernelWhiskerLeftIsoKernelWhiskerRight [Mono (S.X₂ ◁ T.f)] [Mono (S.f ▷ T.X₂)] :
    kernel (S.X₃ ◁ T.f) ≅ kernel (S.f ▷ T.X₃) :=
  have : Mono (hS.tensorSnakeInput hT).L₂'.f :=
    (hS.tensorSnakeInput hT).mono_δ (isZero_kernel_of_mono (S.X₂ ◁ T.f))
  (hS.tensorSnakeInput hT).L₂'_exact.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)

/-- The identification of the kernels of `S.X₃ ◁ T.f` and of `S.f ▷ T.X₃` is the connecting map
of the snake lemma. -/
@[reassoc (attr := simp)]
lemma kernelWhiskerLeftIsoKernelWhiskerRight_hom_comp_ι [Mono (S.X₂ ◁ T.f)]
    [Mono (S.f ▷ T.X₂)] :
    (hS.kernelWhiskerLeftIsoKernelWhiskerRight hT).hom ≫ kernel.ι (S.f ▷ T.X₃) =
      (hS.tensorSnakeInput hT).δ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

variable [HasProjectiveResolutions C] [Projective S.X₁] [Projective S.X₂] [Projective T.X₁]
  [Projective T.X₂]

/-- **Balance of `Tor₁`.** For projective presentations `0 ⟶ Q₁ ⟶ Q₀ ⟶ X ⟶ 0` and
`0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` such that `Q₀ ◁ (P₁ ⟶ P₀)` and `(Q₁ ⟶ Q₀) ▷ P₀` are monomorphisms,
`Tor₁(X, M)`, derived in `M`, agrees with `Tor'₁(X, M)`, derived in `X`. -/
def torOneIsoTor'One [Mono (S.X₂ ◁ T.f)] [Mono (S.f ▷ T.X₂)] :
    ((Tor C 1).obj S.X₃).obj T.X₃ ≅ ((Tor' C 1).obj S.X₃).obj T.X₃ :=
  hT.torOneIsoKernel S.X₃ ≪≫ hS.kernelWhiskerLeftIsoKernelWhiskerRight hT ≪≫
    (hS.tor'OneIsoKernel T.X₃).symm

/-- Under the kernel descriptions of `Tor₁(X, M)` and `Tor'₁(X, M)`, the balance isomorphism is
the connecting map of the snake lemma. -/
@[reassoc]
lemma torOneIsoTor'One_hom_comp_tor'OneIsoKernel_hom_comp_ι [Mono (S.X₂ ◁ T.f)]
    [Mono (S.f ▷ T.X₂)] :
    (hS.torOneIsoTor'One hT).hom ≫ (hS.tor'OneIsoKernel T.X₃).hom ≫ kernel.ι (S.f ▷ T.X₃) =
      (hT.torOneIsoKernel S.X₃).hom ≫ (hS.tensorSnakeInput hT).δ := by
  simp only [torOneIsoTor'One, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact congrArg _ (hS.kernelWhiskerLeftIsoKernelWhiskerRight_hom_comp_ι hT)

end ShortComplex.ShortExact

/-- **Balance of `Tor₁` in projective dimension at most one.** Let `X` and `Y` have projective
dimension at most one, with chosen epimorphisms `P_X ⟶ X` and `P_Y ⟶ Y` from projectives. If
`P_X ⊗ -` and `- ⊗ P_Y` preserve monomorphisms, then `Tor₁(X, Y) ≅ Tor'₁(X, Y)`, computed on the
projective presentations `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0`. -/
def torOneIsoTor'OneOfHasProjectiveDimensionLEOne [EnoughProjectives C] (X Y : C)
    [HasProjectiveDimensionLE X 1] [HasProjectiveDimensionLE Y 1]
    [((tensoringLeft C).obj (Projective.over X)).PreservesMonomorphisms]
    [((tensoringRight C).obj (Projective.over Y)).PreservesMonomorphisms] :
    ((Tor C 1).obj X).obj Y ≅ ((Tor' C 1).obj X).obj Y :=
  (Projective.kernelShortComplex_shortExact X).torOneIsoTor'One
    (Projective.kernelShortComplex_shortExact Y)

/-- The balance isomorphism in projective dimension at most one is `torOneIsoTor'One` for the
projective presentations `0 ⟶ ker π ⟶ P ⟶ X ⟶ 0` of `X` and `Y`. -/
lemma torOneIsoTor'OneOfHasProjectiveDimensionLEOne_def [EnoughProjectives C] (X Y : C)
    [HasProjectiveDimensionLE X 1] [HasProjectiveDimensionLE Y 1]
    [((tensoringLeft C).obj (Projective.over X)).PreservesMonomorphisms]
    [((tensoringRight C).obj (Projective.over Y)).PreservesMonomorphisms] :
    torOneIsoTor'OneOfHasProjectiveDimensionLEOne X Y =
      (Projective.kernelShortComplex_shortExact X).torOneIsoTor'One
        (Projective.kernelShortComplex_shortExact Y) := by
  rw [torOneIsoTor'OneOfHasProjectiveDimensionLEOne]

end CategoryTheory
