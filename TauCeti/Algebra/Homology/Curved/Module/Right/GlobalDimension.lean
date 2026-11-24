/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective.Model
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective.Model
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension

/-!
# Finite graded global dimension and coincidence of curved acyclic classes

Let `(A, d, w)` be a curved DG algebra over `R`. When the abelian category of graded right
`A`-modules has finite global dimension — formulated as a uniform strict bound
`HasProjectiveDimensionLT V n` on objects `V`, which directly covers `HasProjectiveDimensionLE V d`
as the case `n = d + 1` — Positselski's Theorem 7.8(a) asserts that the three acyclic classes of the
second kind coincide on the curved homotopy category and that the canonical comparison functors
`D_abs → D_co` and `D_abs → D_ctr` are equivalences of categories.

The argument combines the bounded graded-projective and graded-injective replacements from
`Graded.Projective.Model` and `Graded.Injective.Model` with Ext-dimension symmetry on the abelian
category of graded right `A`-modules:

* If `X` is contraacyclic and its underlying graded right module has projective dimension `< n`,
  `exists_gradedProjective_absolutelyAcyclic_trW` gives a morphism `s : P ⟶ X` in
  `(absolutelyAcyclic R h).trW` from a graded-projective object `P`. Right orthogonality of
  contraacyclic objects to graded-projective objects forces `s = 0`; since
  `AbsoluteDerivedCategory.Q R h` inverts `s`, `X` vanishes in `AbsoluteDerivedCategory R h` and is
  therefore absolutely acyclic.
* Dually, if `X` is coacyclic and its underlying graded right module has injective dimension `< n`,
  `exists_gradedInjective_absolutelyAcyclic_trW` gives `s : X ⟶ I` in `(absolutelyAcyclic R h).trW`
  into a graded-injective object `I`; left orthogonality of coacyclic objects to graded-injective
  objects forces `s = 0`, so `X` is again absolutely acyclic.
* Under a uniform graded projective-dimension bound `∀ V, HasProjectiveDimensionLT V n`,
  `CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT` transfers the
  same uniform bound to graded injective dimension, yielding
  `absolutelyAcyclic R h = coacyclic R h = contraacyclic R h`, closure of `absolutelyAcyclic R h`
  under small coproducts and products, the comparison equivalences `D_abs ≃ D_co` and
  `D_abs ≃ D_ctr`, and the graded-injective model of `D_co`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLT`:
  per-object coincidence of curved acyclicity under finite graded projective or injective dimension.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`:
  coincidence of the three acyclic classes of the second kind.
* In `TauCeti.CurvedDGRightModuleCat.AbsoluteDerivedCategory`,
  `isEquivalence_toCoderived_of_hasProjectiveDimensionLT` and
  `isEquivalence_toContraderived_of_hasProjectiveDimensionLT`, and in
  `TauCeti.CurvedDGRightModuleCat.CoderivedCategory`,
  `isEquivalence_ι_comp_Q_of_hasProjectiveDimensionLT`:
  the comparison equivalences `D_abs → D_co` and `D_abs → D_ctr` and the graded-injective model of
  `D_co` in finite graded global dimension.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Theorem.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Theorem 7.8(a) and Theorem 7.9(a).
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

/-! ### Per-object acyclicity comparison -/

/-- A contraacyclic curved right module whose underlying graded right module has finite projective
dimension is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    absolutelyAcyclic R h X := by
  obtain ⟨P, s, hP, hs⟩ := exists_gradedProjective_absolutelyAcyclic_trW (h := h) n X
  have hs0 : (AbsoluteDerivedCategory.Q R h).map s = 0 := by
    rw [contraacyclic_le_rightOrthogonal_gradedProjective R h X hX s hP, Functor.map_zero]
  have : IsIso ((AbsoluteDerivedCategory.Q R h).map s) :=
    Localization.inverts (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW s hs
  exact (AbsoluteDerivedCategory.isZero_Q_obj_iff X).1 (IsZero.of_epi_eq_zero _ hs0)

/-- For a curved right module whose underlying graded right module has projective dimension `< n`,
contraacyclicity is equivalent to absolute acyclicity. -/
theorem contraacyclic_iff_absolutelyAcyclic_of_hasProjectiveDimensionLT (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    contraacyclic R h X ↔ absolutelyAcyclic R h X :=
  ⟨absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT n,
    fun hX ↦ absolutelyAcyclic_le_contraacyclic R h X hX⟩

/-- A contraacyclic curved right module whose underlying graded right module has finite projective
dimension is coacyclic. -/
theorem coacyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    coacyclic R h X :=
  absolutelyAcyclic_le_coacyclic R h X
    (absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT n hX)

/-- A coacyclic curved right module whose underlying graded right module has finite injective
dimension is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    absolutelyAcyclic R h X := by
  obtain ⟨I, s, hI, hs⟩ := exists_gradedInjective_absolutelyAcyclic_trW (h := h) n X
  have hs0 : (AbsoluteDerivedCategory.Q R h).map s = 0 := by
    rw [coacyclic_le_leftOrthogonal_gradedInjective R h X hX s hI, Functor.map_zero]
  have : IsIso ((AbsoluteDerivedCategory.Q R h).map s) :=
    Localization.inverts (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW s hs
  exact (AbsoluteDerivedCategory.isZero_Q_obj_iff X).1 (IsZero.of_mono_eq_zero _ hs0)

/-- For a curved right module whose underlying graded right module has injective dimension `< n`,
coacyclicity is equivalent to absolute acyclicity. -/
theorem coacyclic_iff_absolutelyAcyclic_of_hasInjectiveDimensionLT (n : ℕ)
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h))
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    coacyclic R h X ↔ absolutelyAcyclic R h X :=
  ⟨absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n,
    fun hX ↦ absolutelyAcyclic_le_coacyclic R h X hX⟩

/-- A coacyclic curved right module whose underlying graded right module has finite injective
dimension is contraacyclic. -/
theorem contraacyclic_of_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    contraacyclic R h X :=
  absolutelyAcyclic_le_contraacyclic R h X
    (absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n hX)

/-- Under a uniform graded injective-dimension bound `< n`, the absolutely acyclic and coacyclic
classes of curved right modules coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLT V n) :
    absolutelyAcyclic R h = coacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_coacyclic R h) fun X hX ↦
    have := hn (toGradedModuleCat X.underlying)
    absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n hX

/-! ### Positselski's Theorem 7.8(a): finite graded global dimension -/

section FiniteGlobalDimension

variable (n : ℕ)
  (hn : ∀ V : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
    HasProjectiveDimensionLT V n)
include hn

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
  absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLT n
    ((CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT _ n).1 hn)

/-- **Positselski's Theorem 7.8(a) (coacyclic vs. contraacyclic).** Under a uniform graded
projective-dimension bound `< n`, the coacyclic and contraacyclic classes of curved right modules
coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT :
    coacyclic R h = contraacyclic R h :=
  (absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn).symm.trans
    (absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn)

/-- Under a uniform graded projective-dimension bound `< n`, the absolutely acyclic class is closed
under coproducts indexed by `Type u`. -/
theorem isClosedUnderColimitsOfShape_discrete_absolutelyAcyclic_of_hasProjectiveDimensionLT
    (J : Type u) :
    (absolutelyAcyclic R h).IsClosedUnderColimitsOfShape (Discrete J) := by
  rw [absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn]
  infer_instance

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
    (AbsoluteDerivedCategory.toCoderived R h).IsEquivalence :=
  AbsoluteDerivedCategory.isEquivalence_toCoderived_iff.2
    (absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn)

/-- **Positselski's Theorem 7.8(a) (contraderived equivalence).** Under a uniform graded
projective-dimension bound `< n`, the canonical comparison triangle functor from the absolute
derived category to the contraderived category is an equivalence of categories. -/
theorem AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT :
    (AbsoluteDerivedCategory.toContraderived R h).IsEquivalence :=
  AbsoluteDerivedCategory.isEquivalence_toContraderived_iff.2
    (absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (R := R) (h := h) n hn)

/-- Under a uniform graded projective-dimension bound `< n`, the localization functor to the
coderived category restricts to an equivalence on graded-injective curved right modules. -/
theorem CoderivedCategory.isEquivalence_ι_comp_Q_of_hasProjectiveDimensionLT :
    ((gradedInjective R h).ι ⋙ CoderivedCategory.Q R h).IsEquivalence :=
  CoderivedCategory.isEquivalence_ι_comp_Q fun V ↦
    ⟨n, (CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT _ n).1
      hn V⟩

end FiniteGlobalDimension

end TauCeti.CurvedDGRightModuleCat
