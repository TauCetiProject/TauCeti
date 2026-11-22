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
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Curves.Smooth
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Images
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Stalk
import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Normalization.Modification
import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.LinearAlgebra.TensorProduct.Quotient
import TauCeti.RingTheory.UniversallyJapanese
import TauCeti.Topology.KrullDimension.Irreducible

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

private theorem isFinite_of_topologicalKrullDim_le_zero [IsProper (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X ≤ 0) : IsFinite (X ↘ Spec (.of k)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have hsub (Z : irreducibleComponents X) : (Z : Set X).Subsingleton := by
    let Zs : Set X := Z.val
    have : IrreducibleSpace Zs := Subtype.irreducibleSpace Z.property.left
    have : Nonempty (TopologicalSpace.IrreducibleCloseds Zs) :=
      ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Zs, isClosed_univ⟩⟩
    have hZ0 : topologicalKrullDim Zs = 0 := le_antisymm
      (Topology.IsInducing.subtypeVal.topologicalKrullDim_le.trans hX) Order.krullDim_nonneg
    have := TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mp hZ0
    exact fun a ha b hb ↦ congrArg Subtype.val (Subsingleton.elim (⟨a, ha⟩ : Zs) ⟨b, hb⟩)
  have hfin : (Set.univ : Set X).Finite := by
    rw [← sUnion_irreducibleComponents, Set.sUnion_eq_biUnion]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.biUnion
      fun Z hZ ↦ (hsub ⟨Z, hZ⟩).finite
  have : LocallyQuasiFinite (X ↘ Spec (.of k)) :=
    .of_finite_preimage_singleton _ fun _ ↦ hfin.subset (Set.subset_univ _)
  exact .of_locallyQuasiFinite (X ↘ Spec (.of k))

private theorem finiteDimensional_cohomology_of_topologicalKrullDim_le_zero
    [IsProper (X ↘ Spec (.of k))] (hX : topologicalKrullDim X ≤ 0) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : FiniteDimensional k (Cohomology M n) := by
  have := isFinite_of_topologicalKrullDim_le_zero (k := k) hX
  let g : X ⟶ projectiveLine k := (X ↘ Spec (.of k)) ≫ projectiveLine.infinitySection k
  have : g.IsOver (Spec (.of k)) := ⟨by simp [g]⟩
  exact finite_cohomology_of_isFinite_to_projectiveLine k g M n

private theorem finiteDimensional_cohomology_of_not_nontrivial_stalk_genericPoint
    [X.IsCurveOver k] (Q : X.Modules) [Q.IsQuasicoherent] [Q.IsFiniteType]
    (hQη : ¬ Nontrivial (Q.presheaf.stalk (genericPoint X))) (n : ℕ) :
    FiniteDimensional k (Cohomology Q n) := by
  let hQ (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(Q, U) :=
    Q.finite_sections_of_isAffineOpen U.val U.property
  let I := Q.annihilator hQ
  let i : I.subscheme ⟶ X := I.subschemeι
  let _ : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
  have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (I.subscheme ↘ Spec (.of k)) := inferInstanceAs (IsProper (i ≫ (X ↘ _)))
  have hnotmem : genericPoint X ∉ Set.range i := IdealSheafData.range_subschemeι I ▸
    mt (Q.mem_support_annihilator_iff_nontrivial_stalk hQ).mp hQη
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

private lemma not_nontrivial_stalk_of_subsingleton_sections {U : X.Opens} (hU : IsAffineOpen U)
    (Q : X.Modules) [Q.IsQuasicoherent] {x : X} (hx : x ∈ U) (hsub : Subsingleton Γ(Q, U)) :
    ¬ Nontrivial (Q.presheaf.stalk x) := by
  let _ := Q.moduleSectionStalk (U := U) ⟨x, hx⟩
  have := Q.isLocalizedModule_germₗ ⟨x, hx⟩ hU
  let S := (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  have : Subsingleton (LocalizedModule S Γ(Q, U)) := ⟨fun p q ↦ by
    induction p, q using LocalizedModule.induction_on₂ with
    | _ a b _ _ => exact LocalizedModule.mk_eq.mpr ⟨1, by simp [hsub.elim a 0, hsub.elim b 0]⟩⟩
  exact (IsLocalizedModule.iso S (Q.germₗ ⟨x, hx⟩)).toEquiv.nontrivial_congr.not.mp
    (not_nontrivial _)

variable (k) in
/-- **Finiteness of coherent cohomology on a curve.** On any proper integral curve over a field `k`
(not necessarily regular or smooth), the cohomology of a quasi-coherent sheaf of modules of finite
type is finite-dimensional over `k` in every degree. -/
theorem finiteDimensional_cohomology_of_isCurveOver [X.IsCurveOver k] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) : FiniteDimensional k (Cohomology M n) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let f := X.fromSpecStalk (genericPoint X)
  let ν : f.normalization ⟶ X := f.fromNormalization
  have : IsFinite ν := isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr fun U hU _ ↦ by
    let _ : Algebra k Γ(X, U) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appLE ⊤ U le_top).hom.toAlgebra
    have : Algebra.FiniteType k Γ(X, U) := (X ↘ Spec (.of k)).finiteType_ΓSpecIso_inv_comp_appLE hU
    have := Ring.IsUniversallyJapanese.isJapanese k Γ(X, U); infer_instance
  have : IsRegular f.normalization := isRegular_normalization_fromSpecStalk_genericPoint
    (IsCurveOver.topologicalKrullDim_eq_one (X := X) k).le
  have := (IsModification.birational ν).irreducibleSpace
  have : IsNormalScheme f.normalization := IsRegular.isNormal
  have : IsIntegral f.normalization := isIntegral_of_irreducibleSpace_of_isReduced _
  let _ : f.normalization.Over (Spec (.of k)) := ⟨ν ≫ (X ↘ Spec (.of k))⟩
  have : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsProper (f.normalization ↘ Spec (.of k)) := inferInstanceAs (IsProper (ν ≫ (X ↘ _)))
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have := isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mp ‹_› V hV ‹_›
  obtain ⟨s, hs, _⟩ := Ring.IsN1.exists_isIntegrallyClosed_localization_away (R := Γ(X, V))
  have := hV.isLocalization_basicOpen s
  have : IsIntegrallyClosed Γ(X, X.basicOpen s) := .of_equiv
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s) _).toRingEquiv
  let U₀ : X.Opens := X.basicOpen s
  have hU₀ : IsAffineOpen U₀ := hV.basicOpen s
  have hiso : IsIso (ν ∣_ U₀) := isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed hU₀
  have hηU₀ : genericPoint X ∈ U₀ := by
    by_contra hnot
    exact (basicOpen_eq_bot_iff s).not.mpr hs (Scheme.eq_bot_of_genericPoint_notMem hnot)
  have : Nonempty U₀ := ⟨⟨genericPoint X, hηU₀⟩⟩
  have : Nonempty (ν ⁻¹ᵁ U₀) := ⟨(asIso (ν ∣_ U₀)).inv ⟨genericPoint X, hηU₀⟩⟩
  have : f.normalization.IsCurveOver k := ⟨by
    rw [← topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
        (f.normalization ↘ Spec (.of k)) (ν ⁻¹ᵁ U₀).ι.isOpenEmbedding,
      (asIso (ν ∣_ U₀)).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq,
      topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
        (X ↘ Spec (.of k)) U₀.ι.isOpenEmbedding,
      IsCurveOver.topologicalKrullDim_eq_one (X := X) k]⟩
  let N : X.Modules := (pushforward ν).obj ((pullback ν).obj M)
  have : N.IsFinitePresentation := isFinitePresentation_pushforward_of_isFinite ν _
  have : N.IsFiniteType := inferInstance
  have hN (m : ℕ) : FiniteDimensional k (Cohomology N m) :=
    (ν.moduleFinite_cohomology_pushforward_iff_of_isAffineHom k ((pullback ν).obj M) m).mpr
      (finiteDimensional_cohomology_of_isCurveOver_of_isDiscreteValuationRing k _ m)
  let η : M ⟶ N := (pullbackPushforwardAdjunction ν).unit.app M
  have : IsIso (ν.app U₀) := (isIso_morphismRestrict_iff_isIso_app ν hU₀).mp hiso
  have hbij_ν : Function.Bijective (ν.app U₀).hom := ConcreteCategory.bijective_of_isIso (ν.app U₀)
  have hbij_η : Function.Bijective (η.app U₀) := by
    let _ := (ν.app U₀).hom.toAlgebra
    have hker : RingHom.ker (algebraMap Γ(X, U₀) Γ(f.normalization, ν ⁻¹ᵁ U₀)) ≤
        Module.annihilator Γ(X, U₀) Γ(M, U₀) := fun r hr ↦ by
      rw [hbij_ν.injective ((RingHom.mem_ker.mp hr).trans (map_zero _).symm)]
      exact Submodule.zero_mem _
    have hb := TensorProduct.mk_one_bijective_of_ker_le_annihilator (R := Γ(X, U₀))
      (S := Γ(f.normalization, ν ⁻¹ᵁ U₀)) (M := Γ(M, U₀)) hbij_ν.surjective hker
    let e := ν.pullbackSectionsEquiv M hU₀ (hU₀.preimage ν)
    have key : e.symm ∘ ν.pullbackSections M U₀ =
        TensorProduct.mk Γ(X, U₀) Γ(f.normalization, ν ⁻¹ᵁ U₀) Γ(M, U₀) 1 :=
      funext fun t ↦ ν.pullbackSectionsEquiv_symm_pullbackSections M hU₀ (hU₀.preimage ν) t
    have hp := (e.symm.bijective.of_comp_iff' (ν.pullbackSections M U₀)).mp (key ▸ hb)
    rwa [show ⇑(ν.pullbackSections M U₀) = _ from funext (ν.pullbackSections_apply M U₀)] at hp
  have hsub_ker : Subsingleton Γ(kernel η, U₀) := by
    have : Mono ((toPresheaf X).map (kernel.ι η)) := (toPresheaf X).map_mono _
    have hmono : Mono ((kernel.ι η).app U₀) := by
      simpa using (inferInstance : Mono (((toPresheaf X).map (kernel.ι η)).app (Opposite.op U₀)))
    refine subsingleton_of_forall_eq 0 fun a ↦
      (AddCommGrpCat.mono_iff_injective _).mp hmono (hbij_η.injective ?_)
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Hom.comp_app, kernel.condition, Hom.zero_app]
    simp
  have hsub_coker : Subsingleton Γ(cokernel η, U₀) := by
    refine subsingleton_of_forall_eq 0 fun a ↦ ?_
    obtain ⟨a', rfl⟩ := (cokernel.π η).app_surjective_of_epi_of_isAffineOpen U₀ hU₀ a
    obtain ⟨a₀, rfl⟩ := hbij_η.surjective a'
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, cokernel.condition, Hom.zero_app]; simp
  have : (kernel η).IsFinitePresentation := isFinitePresentation_kernel η
  have : (kernel η).IsFiniteType := inferInstance
  have : (cokernel η).IsFiniteType := isFiniteType_of_epi (cokernel.π η)
  have hker_fin (m : ℕ) := finiteDimensional_cohomology_of_not_nontrivial_stalk_genericPoint
    (k := k) (kernel η)
    (not_nontrivial_stalk_of_subsingleton_sections hU₀ (kernel η) hηU₀ hsub_ker) m
  have hcoker_fin (m : ℕ) := finiteDimensional_cohomology_of_not_nontrivial_stalk_genericPoint
    (k := k) (cokernel η)
    (not_nontrivial_stalk_of_subsingleton_sections hU₀ (cokernel η) hηU₀ hsub_coker) m
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
