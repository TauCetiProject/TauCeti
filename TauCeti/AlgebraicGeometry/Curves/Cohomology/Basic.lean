/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Finite
public import TauCeti.AlgebraicGeometry.Curves.AffineCover
public import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Kernels
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
import TauCeti.AlgebraicGeometry.Cohomology.Spec
import TauCeti.AlgebraicGeometry.Curves.Resolution
import TauCeti.AlgebraicGeometry.Curves.Smooth
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Images
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Finite
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Vanishing above degree one and finiteness of quasi-coherent cohomology on a curve

Let `X` be a proper integral curve over a field `k` whose codimension-one local rings are
discrete valuation rings, for instance a smooth proper connected curve. Then `X` is covered by
two affine opens `U` and `V` (`AlgebraicGeometry.Scheme.exists_two_affine_opens`), their
intersection is affine because `X` is separated, and quasi-coherent sheaves on the Noetherian
affine schemes `U`, `V` and `U ∩ V` have no higher cohomology. The Mayer–Vietoris sequence of
the cover then shows that every quasi-coherent sheaf `M` on `X` has `Hⁿ(X, M) = 0` for all
`n ≥ 2`: cohomology vanishes above the dimension of the curve.

Through the long exact cohomology sequence, this vanishing makes `H¹(X, -)` right exact on
quasi-coherent sheaves. For a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules
with `M₁` quasi-coherent, the map `H¹(X, M₂) ⟶ H¹(X, M₃)` is surjective; in particular an
epimorphism of quasi-coherent sheaves is surjective on `H¹`, and a quotient of a quasi-coherent
sheaf with finite-dimensional `H¹` again has finite-dimensional `H¹`. The vanishing of `H²` is also
the vanishing hypothesis in `Scheme.Modules.finrank_cohomology_zero_sub_one_eq_add`; together with
finite-dimensional `H¹` of the first term and finite-dimensional `H⁰` and `H¹` of the middle term,
it makes the Euler characteristic `χ(X, M) = dim H⁰(X, M) - dim H¹(X, M)` additive.

For an arbitrary proper integral curve `X` over `k` (possibly singular, such as a component of the
special fibre of a model), the cohomology of a quasi-coherent sheaf `M` of finite type is still
finite-dimensional over `k` in every degree (`finiteDimensional_cohomology_of_isCurveOver`, and
`finiteDimensional_cohomology_of_topologicalKrullDim_le_one` in dimension at most one), with no
rational-point or perfection assumption on `k`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_isCurveOver`:
  `Hⁿ(X, M) = 0` for `n ≥ 2` and `M` quasi-coherent on a regular proper curve;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_smooth_of_connected`:
  the same on a smooth proper connected curve of relative dimension one;
* `AlgebraicGeometry.Scheme.Modules.cohomologyMap_one_surjective_of_isCurveOver` and
  `AlgebraicGeometry.Scheme.Modules.cohomologyMap_one_surjective_of_epi_of_isCurveOver`:
  right exactness of `H¹` on such a curve;
* `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_one_of_epi_of_isCurveOver`:
  finite-dimensionality of `H¹` passes to quotients;
* `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_of_isCurveOver`,
  `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_of_topologicalKrullDim_le_one`, and
  `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_of_smooth_of_connected`:
  `Hⁿ(X, M)` is finite-dimensional for `M` quasi-coherent of finite type on any proper integral
  curve, any proper integral scheme of dimension at most one, and any smooth proper connected curve
  over `k`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 2.7 (Grothendieck vanishing),
  Theorem 4.5 (Čech computation of quasi-coherent cohomology on a separated Noetherian scheme) and
  Theorem 5.2 (finiteness of cohomology on projective schemes, here for curves).
* [The Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6) and
  [Lemma 33.41.1 (Tag 0C45)](https://stacks.math.columbia.edu/tag/0C45).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section IsCurveOverDVR

variable (k) [X.IsCurveOver k]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

include k

/-- **Vanishing above the dimension of a curve.** On a proper integral curve over a field whose
codimension-one local rings are discrete valuation rings, a quasi-coherent sheaf of modules has
no cohomology in degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_isCurveOver (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) :=
  subsingleton_cohomology_of_two_le_of_isSeparated (R := k) (X.exists_two_affine_opens (k := k)) M
    n hn

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, `H¹` is right exact: for a short exact sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of
sheaves of modules with `M₁` quasi-coherent, `H¹(X, M₂) ⟶ H¹(X, M₃)` is surjective. -/
theorem cohomologyMap_one_surjective_of_isCurveOver {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    Function.Surjective (cohomologyMap S.g 1) :=
  cohomologyMap_surjective hS 1 2 rfl
    (subsingleton_cohomology_of_two_le_of_isCurveOver k S.X₁ 2 le_rfl)

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, an epimorphism of quasi-coherent sheaves of modules is surjective on `H¹`. -/
theorem cohomologyMap_one_surjective_of_epi_of_isCurveOver {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f] :
    Function.Surjective (cohomologyMap f 1) := by
  have : (ShortComplex.kernelSequence f).X₁.IsQuasicoherent := isQuasicoherent_kernel f
  have : Epi (ShortComplex.kernelSequence f).g := ‹Epi f›
  exact cohomologyMap_one_surjective_of_isCurveOver k
    (.mk' (ShortComplex.kernelSequence_exact f) inferInstance inferInstance)

/-- On a proper integral curve over a field whose codimension-one local rings are discrete
valuation rings, a quotient of a quasi-coherent sheaf of modules with finite-dimensional `H¹`
again has finite-dimensional `H¹`. -/
theorem finiteDimensional_cohomology_one_of_epi_of_isCurveOver {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f]
    [FiniteDimensional k (Cohomology M 1)] : FiniteDimensional k (Cohomology N 1) := by
  apply Module.Finite.of_surjective (cohomologyMapBaseLinear k X f 1)
  simpa only [coe_cohomologyMapBaseLinear] using
    cohomologyMap_one_surjective_of_epi_of_isCurveOver k f

private theorem finiteDimensional_cohomology_of_isCurveOver_of_isDiscreteValuationRing
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    FiniteDimensional k (Cohomology M n) := by
  have hF := IsCurveOver.isFunctionField (k := k) (X := X)
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  -- `k(X)` is finite over the subfield `k(x)`, viewed as `k(X)`-algebra with `X` acting as `x`
  let _ := ratFuncAlgebraOfTranscendental hx
  have := isScalarTower_ratFuncAlgebraOfTranscendental hx
  have := hF.finiteDimensional_adjoin hx
  have := finiteDimensional_ratFuncAlgebraOfTranscendental hx
  have hX := algebraMap_ratFuncAlgebraOfTranscendental_X hx
  -- the two-chart model built from the image of `X` maps finitely to `ℙ¹_k`
  let ν : X ⟶ projectiveLine k := (X.isoTwoChartModel (hX ▸ hx.ne_zero) (hX ▸ hx)).hom ≫
    twoChartModel.toProjectiveLine hF (hX ▸ hx.ne_zero)
  exact finite_cohomology_of_isFinite_to_projectiveLine k ν M n

end IsCurveOverDVR

section Finiteness

private theorem finiteDimensional_cohomology_of_topologicalKrullDim_le_zero
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 0) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : FiniteDimensional k (Cohomology M n) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have : IsFinite (X ↘ Spec (.of k)) :=
    (X ↘ Spec (.of k)).isFinite_of_topologicalKrullDim_le_zero hX
  exact moduleFinite_cohomology_of_isFinite_over_spec k M n

private theorem finiteDimensional_cohomology_of_subsingleton_stalk_genericPoint
    [X.IsCurveOver k] (Q : X.Modules) [Q.IsQuasicoherent] [Q.IsFiniteType]
    (hQη : Subsingleton (Q.presheaf.stalk (genericPoint X))) (n : ℕ) :
    FiniteDimensional k (Cohomology Q n) := by
  let hQ (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(Q, U) :=
    Q.finite_sections_of_isAffineOpen U.val U.property
  let I := Q.annihilator hQ
  let i : I.subscheme ⟶ X := I.subschemeι
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
  have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (I.subscheme ↘ Spec (.of k)) := inferInstanceAs (IsProper (i ≫ (X ↘ _)))
  have hnotmem : genericPoint X ∉ Set.range i := IdealSheafData.range_subschemeι I ▸
    mt (Q.mem_support_annihilator_iff_nontrivial_stalk hQ).mp
      (not_nontrivial_iff_subsingleton.mpr hQη)
  have hnotdense : ¬ DenseRange i := fun hd ↦ hnotmem
    (i.isClosedEmbedding.isClosed_range.closure_eq ▸ dense_iff_closure_eq.mp hd ▸ Set.mem_univ _)
  have hIdim : topologicalKrullDim I.subscheme ≤ 0 := by
    have hle := i.isClosedEmbedding.isInducing.topologicalKrullDim_add_one_le hnotdense
    rw [IsCurveOver.topologicalKrullDim_eq_one (X := X) k] at hle
    exact ENat.WithBot.add_le_add_one_right_iff.mp (by simpa only [zero_add] using hle)
  have : IsIso ((pullbackPushforwardAdjunction i).unit.app Q) :=
    isIso_unit_app_of_ker_ideal_le_annihilator i Q fun U ↦ by
      rw [IdealSheafData.ker_subschemeι, Q.annihilator_ideal hQ U]
  let e : Q ≅ (pushforward i).obj ((pullback i).obj Q) :=
    asIso ((pullbackPushforwardAdjunction i).unit.app Q)
  have := (i.moduleFinite_cohomology_pushforward_iff_of_isAffineHom k ((pullback i).obj Q) n).mpr
    (finiteDimensional_cohomology_of_topologicalKrullDim_le_zero hIdim ((pullback i).obj Q) n)
  exact Module.Finite.equiv (cohomologyBaseLinearEquivOfIso k e n).symm

/-- If `ν : Y ⟶ X` restricts to an isomorphism over an affine open `U₀` of `X`, then the
pullback–pushforward unit `M ⟶ ν_* ν^* M` of any quasi-coherent `𝒪_X`-module `M` is bijective on
sections over `U₀`. -/
private lemma bijective_unit_app_of_isIso_morphismRestrict {Y : Scheme.{u}} (ν : Y ⟶ X)
    [IsAffineHom ν] (M : X.Modules) [M.IsQuasicoherent] {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀)
    (hiso : IsIso (ν ∣_ U₀)) :
    Function.Bijective (((pullbackPushforwardAdjunction ν).unit.app M).app U₀) := by
  have : IsIso (ν.app U₀) := (isIso_morphismRestrict_iff_isIso_app ν hU₀).mp hiso
  have hbij_ν : Function.Bijective (ν.app U₀).hom := ConcreteCategory.bijective_of_isIso (ν.app U₀)
  let _ := (ν.app U₀).hom.toAlgebra
  have hker : RingHom.ker (algebraMap Γ(X, U₀) Γ(Y, ν ⁻¹ᵁ U₀)) ≤
      Module.annihilator Γ(X, U₀) Γ(M, U₀) := fun r hr ↦ by
    rw [hbij_ν.injective ((RingHom.mem_ker.mp hr).trans (map_zero _).symm)]
    exact Submodule.zero_mem _
  have hb := TensorProduct.mk_one_bijective_of_ker_le_annihilator (R := Γ(X, U₀))
    (S := Γ(Y, ν ⁻¹ᵁ U₀)) (M := Γ(M, U₀)) hbij_ν.surjective hker
  let e := ν.pullbackSectionsEquiv M hU₀ (hU₀.preimage ν)
  have key : e.symm ∘ ν.pullbackSections M U₀ =
      TensorProduct.mk Γ(X, U₀) Γ(Y, ν ⁻¹ᵁ U₀) Γ(M, U₀) 1 :=
    funext fun t ↦ ν.pullbackSectionsEquiv_symm_pullbackSections M hU₀ (hU₀.preimage ν) t
  have hp := (e.symm.bijective.of_comp_iff' (ν.pullbackSections M U₀)).mp (key ▸ hb)
  have hfn : ⇑(((pullbackPushforwardAdjunction ν).unit.app M).app U₀) = ν.pullbackSections M U₀ :=
    funext fun t ↦ (ν.pullbackSections_apply M U₀ t).symm
  exact hfn ▸ hp

/-- If `η : M ⟶ N` is a morphism of finite-type quasi-coherent sheaves on a curve `X` over `k`
that is bijective on sections over a nonempty affine open `U₀`, and `N` has finite-dimensional
cohomology in all degrees, then so does `M`. -/
private theorem finiteDimensional_cohomology_of_bijective_app [X.IsCurveOver k]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
    (η : M ⟶ N) {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) (hηU₀ : genericPoint X ∈ U₀)
    (hbij : Function.Bijective (η.app U₀))
    (hN : ∀ m : ℕ, FiniteDimensional k (Cohomology N m)) (n : ℕ) :
    FiniteDimensional k (Cohomology M n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  -- Kernel and cokernel of `η` vanish on sections over `U₀`, hence vanish at the generic point.
  have hsub_ker : Subsingleton Γ(kernel η, U₀) := by
    have : Mono ((toPresheaf X).map (kernel.ι η)) := (toPresheaf X).map_mono _
    have hmono : Mono ((kernel.ι η).app U₀) := by
      simpa using (inferInstance : Mono (((toPresheaf X).map (kernel.ι η)).app (Opposite.op U₀)))
    refine subsingleton_of_forall_eq 0 fun a ↦
      (AddCommGrpCat.mono_iff_injective _).mp hmono (hbij.injective ?_)
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Hom.comp_app, kernel.condition, Hom.zero_app]
    simp
  have hsub_coker : Subsingleton Γ(cokernel η, U₀) := by
    refine subsingleton_of_forall_eq 0 fun a ↦ ?_
    obtain ⟨a', rfl⟩ := (cokernel.π η).app_surjective_of_epi_of_isAffineOpen U₀ hU₀ a
    obtain ⟨a₀, rfl⟩ := hbij.surjective a'
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, cokernel.condition, Hom.zero_app]; simp
  have : (kernel η).IsFinitePresentation := isFinitePresentation_kernel η
  have : (kernel η).IsFiniteType := inferInstance
  have : (cokernel η).IsFiniteType := isFiniteType_of_epi (cokernel.π η)
  have hker_fin (m : ℕ) := finiteDimensional_cohomology_of_subsingleton_stalk_genericPoint
    (k := k) (kernel η)
    ((kernel η).subsingleton_stalk_of_subsingleton_sections ⟨_, hηU₀⟩ hU₀ hsub_ker) m
  have hcoker_fin (m : ℕ) := finiteDimensional_cohomology_of_subsingleton_stalk_genericPoint
    (k := k) (cokernel η)
    ((cokernel η).subsingleton_stalk_of_subsingleton_sections ⟨_, hηU₀⟩ hU₀ hsub_coker) m
  -- Transfer finiteness from `N` and `cokernel η` to `image η`, then from `kernel η` and `image η`
  -- to `M`.
  have himg_fin (m : ℕ) : FiniteDimensional k (Cohomology (image η) m) := by
    let S₂ := ShortComplex.kernelSequence (cokernel.π η)
    have hS₂ : S₂.ShortExact :=
      .mk' (ShortComplex.kernelSequence_exact (cokernel.π η)) inferInstance inferInstance
    have : FiniteDimensional k (Cohomology (kernel (cokernel.π η)) m) := by
      cases m with
      | zero =>
        have := hN 0
        exact finiteDimensional_cohomology_zero_of_mono k X (kernel.ι (cokernel.π η))
      | succ m =>
        have : FiniteDimensional k (Cohomology S₂.X₃ m) := hcoker_fin m
        have : FiniteDimensional k (Cohomology S₂.X₂ (m + 1)) := hN (m + 1)
        exact finiteDimensional_cohomology_X₁ k X hS₂ m (m + 1) rfl
    exact Module.Finite.equiv (cohomologyBaseLinearEquivOfIso k (Abelian.imageIsoImage η) m)
  let S₁ := ShortComplex.kernelSequence (Limits.factorThruImage η)
  have hS₁ : S₁.ShortExact :=
    .mk' (ShortComplex.kernelSequence_exact (Limits.factorThruImage η)) inferInstance inferInstance
  have : FiniteDimensional k (Cohomology S₁.X₁ n) := by
    have := hker_fin n
    exact Module.Finite.equiv
      (cohomologyBaseLinearEquivOfIso k (Limits.kernelFactorThruImage η) n).symm
  have : FiniteDimensional k (Cohomology S₁.X₃ n) := himg_fin n
  exact finiteDimensional_cohomology_X₂ k X hS₁ n

variable (k) in
/-- **Finiteness of coherent cohomology on a curve.** On any proper integral curve over a field `k`
(not necessarily regular or smooth), the cohomology of a quasi-coherent sheaf of modules of finite
type is finite-dimensional over `k` in every degree. -/
theorem finiteDimensional_cohomology_of_isCurveOver [X.IsCurveOver k] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : FiniteDimensional k (Cohomology M n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  -- Normalize `X` in `k(X)`: `ν : X^ν ⟶ X` is a finite modification from a regular curve over `k`.
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    (X ↘ Spec (.of k))
  have := IsCurveOver.isRegular_normalization k (X := X)
  let _ : (X.fromSpecStalk (genericPoint X)).normalization.Over (Spec (.of k)) :=
    ⟨ν ≫ (X ↘ Spec (.of k))⟩
  have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : ((X.fromSpecStalk (genericPoint X)).normalization).IsCurveOver k := inferInstance
  -- Shrink the isomorphism locus of `ν` to an affine open neighborhood `U₀` of the generic point.
  obtain ⟨U, hU_dense, -, hisoU⟩ := IsModification.exists_isIso_morphismRestrict (f := ν)
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU_dense.nonempty)
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hηU₀, hU₀U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hηU U.isOpen
  have hiso : IsIso (ν ∣_ U₀) :=
    IsZariskiLocalAtTarget.restrict_of_le (MorphismProperty.isomorphisms Scheme) hisoU hU₀U
  -- Push forward `ν^* M`, whose cohomology is finite-dimensional on the regular curve `X^ν`.
  let N : X.Modules := (pushforward ν).obj ((pullback ν).obj M)
  have : N.IsFinitePresentation := isFinitePresentation_pushforward_of_isFinite ν _
  have : N.IsFiniteType := inferInstance
  have hN (m : ℕ) : FiniteDimensional k (Cohomology N m) :=
    (ν.moduleFinite_cohomology_pushforward_iff_of_isAffineHom k ((pullback ν).obj M) m).mpr
      (finiteDimensional_cohomology_of_isCurveOver_of_isDiscreteValuationRing k _ m)
  exact finiteDimensional_cohomology_of_bijective_app (M := M) (N := N)
    ((pullbackPushforwardAdjunction ν).unit.app M)
    hU₀ hηU₀ (bijective_unit_app_of_isIso_morphismRestrict ν M hU₀ hiso) hN n

variable (k) in
/-- **Finiteness of coherent cohomology in dimension at most one.** On any proper integral scheme
of dimension at most one over a field `k` (either zero-dimensional or a possibly singular proper
curve), the cohomology of a quasi-coherent sheaf of modules of finite type is finite-dimensional
over `k` in every degree. -/
theorem finiteDimensional_cohomology_of_topologicalKrullDim_le_one
    [IsIntegral X] [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 1)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    FiniteDimensional k (Cohomology M n) := by
  by_cases h0 : topologicalKrullDim X ≤ 0
  · exact finiteDimensional_cohomology_of_topologicalKrullDim_le_zero h0 M n
  · have : X.IsCurveOver k := ⟨le_antisymm hX (by
      cases h : topologicalKrullDim X with
      | bot => exact absurd (h ▸ bot_le) h0
      | coe m => exact WithBot.coe_le_coe.mpr (Order.one_le_iff_pos.mpr
          (WithBot.coe_lt_coe.mp (h ▸ lt_of_not_ge h0))))⟩
    exact finiteDimensional_cohomology_of_isCurveOver k M n

end Finiteness

variable (k) in
/-- **Vanishing above the dimension of a smooth curve.** On a smooth proper connected curve of
relative dimension one over any field, a quasi-coherent sheaf of modules has no cohomology in
degrees at least two. -/
theorem subsingleton_cohomology_of_two_le_of_smooth_of_connected [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) : Subsingleton (Cohomology M n) :=
  subsingleton_cohomology_of_two_le_of_isSeparated (R := k)
    (X.exists_two_affine_opens_of_smooth (k := k)) M n hn

variable (k) in
/-- **Finiteness of coherent cohomology on a smooth curve.** On a smooth proper connected curve of
relative dimension one over any field `k`, the cohomology of a quasi-coherent sheaf of modules of
finite type is finite-dimensional over `k` in every degree. -/
theorem finiteDimensional_cohomology_of_smooth_of_connected [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [ConnectedSpace X] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : FiniteDimensional k (Cohomology M n) := by
  -- a smooth connected curve is integral with regular local rings
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have := IsCurveOver.of_smooth k X
  exact finiteDimensional_cohomology_of_isCurveOver k M n

end AlgebraicGeometry.Scheme.Modules
