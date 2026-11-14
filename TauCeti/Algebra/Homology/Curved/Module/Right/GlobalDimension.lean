/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free

/-!
# Coincidence of curved acyclic classes in finite graded global dimension

Let `(A, d, w)` be a curved differential graded algebra in the right-module convention. In general
the absolutely acyclic class `absolutelyAcyclic R h` is strictly smaller than the coacyclic and
contraacyclic classes, and no comparison connects `coacyclic R h` with `contraacyclic R h`.

This file proves **Positselski's Theorem 7.8(a)** for curved right modules: when the category of
graded right `A`-modules has finite global dimension (every graded right module has projective
dimension `< d`, which for `d = n + 1` is `HasProjectiveDimensionLE _ n`), the three acyclic
classes of the second kind coincide and the canonical comparison triangle functors
`AbsoluteDerivedCategory.toCoderived` and `AbsoluteDerivedCategory.toContraderived` are
equivalences of categories.

The argument proceeds in two steps:

1. **Contraacyclic implies absolutely acyclic object-by-object.** Any curved right module `M`
   admits an epimorphism `Q ⟶ M` in the closed category from a contractible graded-projective
   module `Q = freeObj h P`. If `M` is contraacyclic, its kernel `K` is again contraacyclic by
   two-out-of-three (`prop_X₁_of_shortExact`), while dimension shifting drops the graded projective
   dimension by one. Iterating until the syzygy is graded-projective — where right orthogonality
   (`contraacyclic_le_rightOrthogonal_gradedProjective`) forces a contraacyclic graded-projective
   module to be contractible — resolves `M` in finitely many steps by contractible curved right
   modules, hence places `M` in `absolutelyAcyclic R h`.
2. **Closure of `absolutelyAcyclic` under arbitrary coproducts.** Under a uniform graded
   projective-dimension bound `< d`, every absolutely acyclic curved right module is a fortiori
   contraacyclic and therefore admits a contractible resolution of uniform length `d`. Since direct
   sums of curved right modules are exact in the closed category (`shortExact_closedDirectSumMap`)
   and preserve contractibility (`isZero_homotopy_directSum`), direct sums of length-`d`
   contractible resolutions remain length-`d` contractible resolutions. Thus `absolutelyAcyclic R h`
   is closed under arbitrary coproducts indexed by `Type u`, so
   `coacyclic R h ≤ absolutelyAcyclic R h` by the universal property of `localizingClosure`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.isZero_of_contraacyclic_of_gradedProjective`: every
  contraacyclic graded-projective curved right module is contractible.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT`:
  a contraacyclic curved right module whose underlying graded module has finite projective
  dimension is absolutely acyclic.
* `isClosedUnderColimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT`:
  under a uniform graded projective-dimension bound, `absolutelyAcyclic R h` is closed under
  coproducts indexed by `Type u`.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`:
  coincidence of the three acyclic classes of the second kind.
* `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT`:
  the comparison triangle functors `D_abs → D_co` and `D_abs → D_ctr` are equivalences.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Theorem.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Theorem 7.8(a).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-! ### Exactness of kernels and direct sums in the closed category -/

/-- For an epimorphism `g` in the closed category of curved right modules, the short complex
`kernelObj g ⟶ Q ⟶ M` is short exact. -/
theorem shortExact_kernelι {Q M : CurvedDGRightModuleCat.{u, u, u} h}
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M) [Epi g] :
    (ShortComplex.mk (kernelι g) g (kernelι_comp g)).ShortExact := by
  refine shortExact_iff.mpr ⟨?_, ?_, ?_⟩
  · rw [hom_kernelι]
    exact Subtype.val_injective.comp (kernelEquiv g).injective
  · exact (GradedModuleCat.epi_iff_surjective _).1 ((forgetDifferential (h := h)).map_epi g)
  · intro x
    refine ⟨fun hx ↦ ⟨(kernelEquiv g).symm ⟨x, hx⟩, ?_⟩, ?_⟩
    · rw [hom_kernelι, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, Submodule.subtype_apply]
    · rintro ⟨y, rfl⟩
      rw [hom_kernelι, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
      exact (kernelEquiv g y).2

/-- Direct sums of short exact sequences in the closed category of curved right modules are short
exact. -/
theorem shortExact_closedDirectSumMap {J : Type u}
    {K L M : J → CurvedDGRightModuleCat.{u, u, u} h}
    (f : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (K j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (L j))
    (g : ∀ j, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (L j) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (M j))
    (hfg : ∀ j, f j ≫ g j = 0)
    (hfg' : closedDirectSumMap f ≫ closedDirectSumMap g = 0)
    (hS : ∀ j, (ShortComplex.mk (f j) (g j) (hfg j)).ShortExact) :
    (ShortComplex.mk (closedDirectSumMap f) (closedDirectSumMap g) hfg').ShortExact := by
  classical
  have hSj : ∀ j, Function.Injective (closedHom (f j)) ∧
      Function.Surjective (closedHom (g j)) ∧
      Function.Exact (closedHom (f j)) (closedHom (g j)) :=
    fun j ↦ shortExact_iff.mp (hS j)
  refine shortExact_iff.mpr ⟨?_, ?_, ?_⟩
  · intro (x : DirectSum J fun i ↦ K i) (y : DirectSum J fun i ↦ K i) hxy
    dsimp only at hxy
    refine DirectSum.ext fun j ↦ (hSj j).1 ?_
    exact (closedHom_closedDirectSumMap_apply f x j).symm.trans
      ((congrArg (fun z : DirectSum J fun i ↦ L i ↦ z j) hxy).trans
        (closedHom_closedDirectSumMap_apply f y j))
  · intro (y : DirectSum J fun i ↦ M i)
    dsimp only
    induction y using DirectSum.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | of j m =>
      obtain ⟨l, rfl⟩ := (hSj j).2.1 m
      refine ⟨DirectSum.lof Aᵐᵒᵖ J (fun i ↦ L i) j l, ?_⟩
      rw [← closedHom_closedDirectSumι L j, ← LinearMap.comp_apply, ← closedHom_comp,
        closedDirectSumι_map, closedHom_comp, LinearMap.comp_apply, closedHom_closedDirectSumι,
        DirectSum.lof_eq_of]
    | add y₁ y₂ hy₁ hy₂ =>
      obtain ⟨x₁, rfl⟩ := hy₁
      obtain ⟨x₂, rfl⟩ := hy₂
      exact ⟨x₁ + x₂, map_add _ x₁ x₂⟩
  · intro (y : DirectSum J fun i ↦ L i)
    dsimp only
    refine ⟨fun hy ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
    · have hyj (j : J) : ∃ k : K j, closedHom (f j) k = y j := by
        refine ((hSj j).2.2 (y j)).mp ?_
        exact (closedHom_closedDirectSumMap_apply g y j).symm.trans
          (by simpa only [DirectSum.zero_apply] using
            congrArg (fun z : DirectSum J fun i ↦ M i ↦ z j) hy)
      choose k hk using hyj
      refine ⟨∑ j ∈ y.support, DirectSum.lof Aᵐᵒᵖ J (fun i ↦ K i) j (k j), ?_⟩
      rw [map_sum]
      conv_rhs => rw [← DirectSum.sum_support_of y]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← closedHom_closedDirectSumι K j, ← LinearMap.comp_apply, ← closedHom_comp,
        closedDirectSumι_map, closedHom_comp, LinearMap.comp_apply, closedHom_closedDirectSumι,
        hk j, DirectSum.lof_eq_of]
    · subst hx
      simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
        using congrArg (fun φ ↦ closedHom φ x) hfg'

/-! ### Finite-length contractible resolutions -/

/-- Every contraacyclic graded-projective object of the curved homotopy category is zero. -/
theorem isZero_of_contraacyclic_of_gradedProjective
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    (hX : contraacyclic R h X) (hP : gradedProjective R h X) :
    IsZero X :=
  (IsZero.iff_id_eq_zero X).mpr
    (contraacyclic_le_rightOrthogonal_gradedProjective R h X hX (𝟙 X) hP)

/-- Auxiliary predicate expressing that a curved right module admits a closed resolution of length
`m` by contractible curved right modules. -/
private def HasContractibleResolution : ℕ → CurvedDGRightModuleCat.{u, u, u} h → Prop
  | 0, M => IsZero (DGHomotopyCategory.of R M)
  | m + 1, M =>
    ∃ (K Q : CurvedDGRightModuleCat.{u, u, u} h)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q)
      (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M)
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧
        IsZero (DGHomotopyCategory.of R Q) ∧
        HasContractibleResolution m K

private theorem absolutelyAcyclic_of_hasContractibleResolution :
    ∀ {m : ℕ} {M : CurvedDGRightModuleCat.{u, u, u} h},
      HasContractibleResolution (R := R) m M →
      absolutelyAcyclic R h (DGHomotopyCategory.of R M)
  | 0, _, hM => (absolutelyAcyclic R h).prop_of_isZero hM
  | _ + 1, _, ⟨_, _, _, _, _, hS, hQ, hK⟩ =>
    prop_X₃_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      (absolutelyAcyclic_of_hasContractibleResolution hK)
      ((absolutelyAcyclic R h).prop_of_isZero hQ)

private theorem hasContractibleResolution_of_contraacyclic_of_hasProjectiveDimensionLT_succ :
    ∀ (m : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h),
      contraacyclic R h (DGHomotopyCategory.of R M) →
      HasProjectiveDimensionLT (toGradedModuleCat M) (m + 1) →
      HasContractibleResolution (R := R) m M
  | 0, M, hMc, hM => by
    have hMp : gradedProjective R h (DGHomotopyCategory.of R M) := by
      rw [gradedProjective_iff, DGHomotopyCategory.underlying_of]
      exact projective_iff_hasProjectiveDimensionLT_one.mpr hM
    exact isZero_of_contraacyclic_of_gradedProjective hMc hMp
  | m + 1, M, hMc, hM => by
    obtain ⟨Q, g, hg, hQproj, hQ0⟩ := exists_epi_contractible_gradedProjective (R := R) M
    let K := kernelObj g
    have hS : (ShortComplex.mk (kernelι g) g (kernelι_comp g)).ShortExact :=
      shortExact_kernelι g
    have hKdim : HasProjectiveDimensionLT (toGradedModuleCat K) (m + 1) :=
      ((hS.map_of_exact (forgetDifferential (h := h))).hasProjectiveDimensionLT_X₃_iff
        m hQproj).mp hM
    have hKc : contraacyclic R h (DGHomotopyCategory.of R K) :=
      prop_X₁_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h) hS
        ((contraacyclic R h).prop_of_isZero hQ0) hMc
    exact ⟨K, Q, kernelι g, g, kernelι_comp g, hS, hQ0,
      hasContractibleResolution_of_contraacyclic_of_hasProjectiveDimensionLT_succ m K hKc hKdim⟩

private theorem hasContractibleResolution_directSum {J : Type u} :
    ∀ (m : ℕ) (M : J → CurvedDGRightModuleCat.{u, u, u} h),
      (∀ j, HasContractibleResolution (R := R) m (M j)) →
      HasContractibleResolution (R := R) m (directSum M)
  | 0, _, hM => isZero_homotopy_directSum hM
  | m + 1, M, hM => by
    choose K Q f g hfg hS hQ hK using hM
    have hfg' : closedDirectSumMap f ≫ closedDirectSumMap g = 0 := by
      rw [closedDirectSumMap_comp]
      simp_rw [hfg]
      exact closedDirectSumMap_zero
    exact ⟨directSum K, directSum Q, closedDirectSumMap f, closedDirectSumMap g, hfg',
      shortExact_closedDirectSumMap f g hfg hfg' hS,
      isZero_homotopy_directSum hQ,
      hasContractibleResolution_directSum m K hK⟩

/-! ### Per-object acyclicity comparison -/

/-- A contraacyclic curved right module whose underlying graded right module has finite projective
dimension is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    absolutelyAcyclic R h X := by
  have hX' : contraacyclic R h (DGHomotopyCategory.of R X.underlying) := by
    rwa [DGHomotopyCategory.of_underlying]
  have hres := hasContractibleResolution_of_contraacyclic_of_hasProjectiveDimensionLT_succ
    n X.underlying hX' (hasProjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n))
  simpa only [DGHomotopyCategory.of_underlying] using
    absolutelyAcyclic_of_hasContractibleResolution hres

/-- A contraacyclic curved right module whose underlying graded right module has finite projective
dimension is coacyclic. -/
theorem coacyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    coacyclic R h X :=
  absolutelyAcyclic_le_coacyclic R h X
    (absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT n hX)

/-! ### Positselski's Theorem 7.8(a): finite graded global dimension -/

section FiniteGlobalDimension

variable (n : ℕ)
  (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    HasProjectiveDimensionLT V n)
include hn

/-- Under a uniform graded projective-dimension bound `< n`, the absolutely acyclic class is closed
under coproducts indexed by `Type u`. -/
theorem isClosedUnderColimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT
    (J : Type u) :
    (absolutelyAcyclic R h).IsClosedUnderColimitsOfShape (Discrete J) := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  let M : J → CurvedDGRightModuleCat.{u, u, u} h := fun j ↦ (F.obj ⟨j⟩).underlying
  have hMres (j : J) : HasContractibleResolution (R := R) n (M j) := by
    have : HasProjectiveDimensionLT (toGradedModuleCat (M j)) n := hn _
    have hMc : contraacyclic R h (DGHomotopyCategory.of R (M j)) := by
      rw [DGHomotopyCategory.of_underlying]
      exact absolutelyAcyclic_le_contraacyclic R h _ (hF ⟨j⟩)
    exact hasContractibleResolution_of_contraacyclic_of_hasProjectiveDimensionLT_succ
      n (M j) hMc (hasProjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n))
  have hsum : absolutelyAcyclic R h (DGHomotopyCategory.of R (directSum M)) :=
    absolutelyAcyclic_of_hasContractibleResolution (hasContractibleResolution_directSum n M hMres)
  let e : Discrete.functor (fun j ↦ DGHomotopyCategory.of R (M j)) ≅ F :=
    Discrete.natIso fun ⟨j⟩ ↦ eqToIso (DGHomotopyCategory.of_underlying R (F.obj ⟨j⟩))
  let hc := (IsColimit.precomposeInvEquiv e _).symm (homotopyDirectSumCofanIsColimit M)
  exact (absolutelyAcyclic R h).prop_of_iso (hc.coconePointUniqueUpToIso (colimit.isColimit F)) hsum

/-- **Positselski's Theorem 7.8(a) (contraacyclic vs. absolutely acyclic).** Under a uniform
graded projective-dimension bound `< n`, the absolutely acyclic and contraacyclic classes of
curved right modules coincide. -/
theorem absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT :
    absolutelyAcyclic R h = contraacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_contraacyclic R h) fun X hX ↦
    have := hn (toGradedModuleCat X.underlying)
    absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT n hX

/-- **Positselski's Theorem 7.8(a) (coacyclic vs. absolutely acyclic).** Under a uniform graded
projective-dimension bound `< n`, the absolutely acyclic and coacyclic classes of curved right
modules coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT :
    absolutelyAcyclic R h = coacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_coacyclic R h) <| by
    have := isClosedUnderColimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT
      (R := R) (h := h) n hn
    exact coacyclic_le_iff.mpr (totalizations_le_absolutelyAcyclic R h)

/-- **Positselski's Theorem 7.8(a) (coacyclic vs. contraacyclic).** Under a uniform graded
projective-dimension bound `< n`, the coacyclic and contraacyclic classes of curved right modules
coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT :
    coacyclic R h = contraacyclic R h :=
  (absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn).symm.trans
    (absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn)

/-- Under a uniform graded projective-dimension bound `< n`, the absolutely acyclic class is also
closed under products indexed by `Type u`. -/
theorem isClosedUnderLimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT
    (J : Type u) :
    (absolutelyAcyclic R h).IsClosedUnderLimitsOfShape (Discrete J) := by
  rw [absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn]
  infer_instance

/-- **Positselski's Theorem 7.8(a) (coderived equivalence).** Under a uniform graded
projective-dimension bound `< n`, the canonical comparison triangle functor from the absolute
derived category to the coderived category is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLT :
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_coacyclic R h)
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE
      (absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn).ge
  have : CatCommSq Φ.functor (AbsoluteDerivedCategory.Q R h)
      (CoderivedCategory.Q R h) (AbsoluteDerivedCategory.toCoderived R h) :=
    ⟨Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
      Functor.leftUnitor _ ≪≫ (AbsoluteDerivedCategory.toCoderivedFactors R h).symm⟩
  exact Φ.isEquivalence (AbsoluteDerivedCategory.Q R h)
    (CoderivedCategory.Q R h) (AbsoluteDerivedCategory.toCoderived R h)

/-- **Positselski's Theorem 7.8(a) (contraderived equivalence).** Under a uniform graded
projective-dimension bound `< n`, the canonical comparison triangle functor from the absolute
derived category to the contraderived category is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT :
    (AbsoluteDerivedCategory.toContraderived R h).IsEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_contraacyclic R h)
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE
      (absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn).ge
  have : CatCommSq Φ.functor (AbsoluteDerivedCategory.Q R h)
      (ContraderivedCategory.Q R h) (AbsoluteDerivedCategory.toContraderived R h) :=
    ⟨Functor.isoWhiskerRight (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor _)) _ ≪≫
      Functor.leftUnitor _ ≪≫ (AbsoluteDerivedCategory.toContraderivedFactors R h).symm⟩
  exact Φ.isEquivalence (AbsoluteDerivedCategory.Q R h)
    (ContraderivedCategory.Q R h) (AbsoluteDerivedCategory.toContraderived R h)

end FiniteGlobalDimension

end TauCeti.CurvedDGRightModuleCat
