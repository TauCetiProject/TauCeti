/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Coincidence of curved acyclic classes in finite graded global dimension

Let `(A, d, w)` be a curved differential graded algebra in the right-module convention. In general
the absolutely acyclic class `absolutelyAcyclic R h` is strictly smaller than the coacyclic and
contraacyclic classes, and no comparison connects `coacyclic R h` with `contraacyclic R h`.

This file proves **Positselski's Theorem 7.8(a)** for curved right modules: when the category of
graded right `A`-modules has finite global dimension (every graded right module has projective
dimension `< d`, or equivalently injective dimension `< d`, which for `d = n + 1` is
`HasProjectiveDimensionLE _ n` / `HasInjectiveDimensionLE _ n`), the three acyclic classes of the
second kind coincide and the canonical comparison triangle functors
`AbsoluteDerivedCategory.toCoderived` and `AbsoluteDerivedCategory.toContraderived` are
equivalences of categories.

The argument proceeds in two steps (with a dual objectwise argument on the injective side):

1. **Contraacyclic implies absolutely acyclic object-by-object.** Any curved right module `M`
   admits an epimorphism `Q ⟶ M` in the closed category from a contractible graded-projective
   module `Q = freeObj h P`. If `M` is contraacyclic, its kernel `K` is again contraacyclic by
   two-out-of-three (`prop_X₁_of_shortExact`), while dimension shifting drops the graded projective
   dimension by one. Iterating until the syzygy is graded-projective — where right orthogonality
   (`contraacyclic_le_rightOrthogonal_gradedProjective`) forces a contraacyclic graded-projective
   module to be contractible — resolves `M` in finitely many steps by contractible curved right
   modules, hence places `M` in `absolutelyAcyclic R h`. Dually, coinduction `coinducedObj h I`
   yields objectwise upgrading of coacyclic modules of finite graded injective dimension.
2. **Closure of `absolutelyAcyclic` under arbitrary coproducts.** Under a uniform graded
   projective-dimension bound `< d`, every absolutely acyclic curved right module is a fortiori
   contraacyclic and therefore admits a contractible resolution of uniform length `d`. Since direct
   sums of curved right modules are exact in the closed category (`shortExact_closedDirectSumMap`)
   and preserve contractibility (`isZero_homotopy_directSum`), direct sums of length-`d`
   contractible resolutions remain length-`d` contractible resolutions. Thus `absolutelyAcyclic R h`
   is closed under arbitrary coproducts indexed by `Type u`, so
   `coacyclic R h ≤ absolutelyAcyclic R h` by the universal property of `localizingClosure`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT`:
  a contraacyclic curved right module whose underlying graded module has finite projective
  dimension is absolutely acyclic.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT`:
  a coacyclic curved right module whose underlying graded module has finite injective dimension is
  absolutely acyclic.
* `isClosedUnderColimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT`:
  under a uniform graded projective-dimension bound, `absolutelyAcyclic R h` is closed under
  coproducts indexed by `Type u`.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT`:
  coincidence of the three acyclic classes of the second kind.
* `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasInjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasInjectiveDimensionLT`:
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

/-! ### Finite-length contractible resolutions -/

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
    exact ⟨directSum K, directSum Q, closedDirectSumMap f, closedDirectSumMap g, _,
      shortExact_closedDirectSumMap f g hfg hS,
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

section InjectiveDimension

private theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT_succ :
    ∀ (m : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h),
      coacyclic R h (DGHomotopyCategory.of R M) →
      HasInjectiveDimensionLT (toGradedModuleCat M) (m + 1) →
      absolutelyAcyclic R h (DGHomotopyCategory.of R M)
  | 0, M, hMc, hM => by
    have hMi : gradedInjective R h (DGHomotopyCategory.of R M) := by
      rw [gradedInjective_iff, DGHomotopyCategory.underlying_of]
      exact injective_iff_hasInjectiveDimensionLT_one.mpr hM
    exact (absolutelyAcyclic R h).prop_of_isZero ((IsZero.iff_id_eq_zero _).2
      (coacyclic_le_leftOrthogonal_gradedInjective R h _ hMc (𝟙 _) hMi))
  | m + 1, M, hMc, hM => by
    obtain ⟨I, _, g, _⟩ := exists_mono_to_coinducedObj_injective (R := R) M
    let S : ShortComplex
        (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
      ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel g }
    have hCdim : HasInjectiveDimensionLT (toGradedModuleCat (ForgetEnrichment.to _ S.X₃)) (m + 1) :=
      ((hS.map_of_exact (forgetDifferential (h := h))).hasInjectiveDimensionLT_X₃_iff m
        (inferInstanceAs (Injective (toGradedModuleCat (coinducedObj h I))))).2 hM
    have hI₀ : IsZero (DGHomotopyCategory.of R (coinducedObj h I)) :=
      isZero_homotopy_freeObj h (I.shiftObj (-1))
    have hCc : coacyclic R h (DGHomotopyCategory.of R (ForgetEnrichment.to _ S.X₃)) :=
      prop_X₃_of_shortExact (coacyclic R h) (totalizations_le_coacyclic R h) hS hMc
        ((coacyclic R h).prop_of_isZero hI₀)
    exact prop_X₁_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      ((absolutelyAcyclic R h).prop_of_isZero hI₀)
      (absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT_succ m _ hCc hCdim)

/-- A coacyclic curved right module whose underlying graded right module has finite injective
dimension is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    absolutelyAcyclic R h X := by
  have hX' : coacyclic R h (DGHomotopyCategory.of R X.underlying) := by
    rwa [DGHomotopyCategory.of_underlying]
  have hres := absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT_succ
    n X.underlying hX' (hasInjectiveDimensionLT_of_ge _ n (n + 1) (Nat.le_succ n))
  simpa only [DGHomotopyCategory.of_underlying] using hres

/-- A coacyclic curved right module whose underlying graded right module has finite injective
dimension is contraacyclic. -/
theorem contraacyclic_of_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    contraacyclic R h X :=
  absolutelyAcyclic_le_contraacyclic R h X
    (absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n hX)

section FiniteInjectiveGlobalDimension

variable (n : ℕ)
  (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    HasInjectiveDimensionLT V n)
include hn

/-- Under a uniform graded injective-dimension bound `< n`, the absolutely acyclic and coacyclic
classes of curved right modules coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT :
    absolutelyAcyclic R h = coacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_coacyclic R h) fun X hX ↦
    have := hn (toGradedModuleCat X.underlying)
    absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n hX

/-- Under a uniform graded injective-dimension bound `< n`, the absolutely acyclic and
contraacyclic classes of curved right modules coincide. -/
theorem absolutelyAcyclic_eq_contraacyclic_of_hasInjectiveDimensionLT :
    absolutelyAcyclic R h = contraacyclic R h :=
  absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n
    (hasProjectiveDimensionLT_of_forall_hasInjectiveDimensionLT hn)

/-- Under a uniform graded injective-dimension bound `< n`, the coacyclic and contraacyclic classes
of curved right modules coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasInjectiveDimensionLT :
    coacyclic R h = contraacyclic R h :=
  (absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT (R := R) (h := h) n hn).symm.trans
    (absolutelyAcyclic_eq_contraacyclic_of_hasInjectiveDimensionLT (R := R) (h := h) n hn)

/-- Under a uniform graded injective-dimension bound `< n`, the canonical comparison triangle
functor from the absolute derived category to the coderived category is an equivalence of
categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasInjectiveDimensionLT :
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence :=
  (isEquivalence_toCoderived_iff R h).2
    (absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT (R := R) (h := h) n hn)

/-- Under a uniform graded injective-dimension bound `< n`, the canonical comparison triangle
functor from the absolute derived category to the contraderived category is an equivalence of
categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasInjectiveDimensionLT :
    (AbsoluteDerivedCategory.toContraderived R h).IsEquivalence :=
  (isEquivalence_toContraderived_iff R h).2
    (absolutelyAcyclic_eq_contraacyclic_of_hasInjectiveDimensionLT (R := R) (h := h) n hn)

end FiniteInjectiveGlobalDimension

end InjectiveDimension

end TauCeti.CurvedDGRightModuleCat
