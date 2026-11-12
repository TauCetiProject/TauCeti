/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Induced
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Coincidence of curved acyclic classes under finite graded global dimension

Over an arbitrary curved differential graded algebra $(A, d, w)$, every absolutely acyclic curved
right module is both coacyclic and contraacyclic, giving canonical triangle comparison functors
from the absolute derived category to the coderived and contraderived categories. In general these
inclusions are strict. Positselski showed that bounded homological dimension of the underlying
graded modules forces the acyclic classes to coincide.

At the objectwise level, any contraacyclic curved right module whose underlying graded right module
has finite projective dimension is already absolutely acyclic, and dually any coacyclic curved
right module whose underlying graded right module has finite injective dimension is absolutely
acyclic.

When the graded algebra $(A, 0, 0)$ has finite right graded global dimension $n$ — meaning every
graded right $A$-module has projective dimension at most $n$, and hence every graded right
$A$-module also has injective dimension at most $n$ — all three acyclic classes of the second kind
coincide, and the comparison functors from the absolute derived category to both the coderived and
the contraderived categories are equivalences of categories.

## Main results

* `CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE`:
  a contraacyclic curved right module of bounded graded projective dimension is absolutely acyclic.
* `CurvedDGRightModuleCat.absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE`:
  a coacyclic curved right module of bounded graded injective dimension is absolutely acyclic.
* `CurvedDGRightModuleCat.absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLE`,
  `CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLE`,
  `CurvedDGRightModuleCat.absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLE`,
  `CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLE`:
  coincidence of the curved acyclic classes under finite graded global dimension.
* `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLE`,
  `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasInjectiveDimensionLE`,
  `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLE`:
  the triangle comparison functors are equivalences under finite graded global dimension.

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

/-- A contraacyclic curved right module whose underlying graded right module has projective
dimension at most `n` is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasProjectiveDimensionLE (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) :
    absolutelyAcyclic R h X := by
  induction n generalizing X with
  | zero =>
    have hP : gradedProjective R h X :=
      (gradedProjective_iff X).2 (projective_iff_hasProjectiveDimensionLT_one.2 inferInstance)
    have hid : 𝟙 X = 0 := contraacyclic_le_rightOrthogonal_gradedProjective R h X hX (𝟙 X) hP
    exact (absolutelyAcyclic R h).prop_of_isZero ((IsZero.iff_id_eq_zero X).2 hid)
  | succ n ih =>
    obtain ⟨P, _, f, _⟩ := exists_epi_from_inducedObj_projective X.underlying
    let S : ShortComplex
        (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
      ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
    have hS' : (S.map (forgetDifferential (h := h))).ShortExact := hS.map_of_exact _
    have : HasProjectiveDimensionLE
        (toGradedModuleCat ((dgClosedToHomotopy R).obj S.X₁).underlying) n :=
      (hS'.hasProjectiveDimensionLT_X₃_iff n
        (inferInstanceAs (Projective (toGradedModuleCat (inducedObj h P))))).1
        (inferInstanceAs (HasProjectiveDimensionLT (toGradedModuleCat X.underlying) (n + 2)))
    have hP₀ : IsZero ((dgClosedToHomotopy R).obj S.X₂) := isZero_homotopy_inducedObj h P
    have hK : contraacyclic R h ((dgClosedToHomotopy R).obj S.X₁) :=
      prop_X₁_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h) hS
        ((contraacyclic R h).prop_of_isZero hP₀) hX
    exact prop_X₃_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      (ih hK) ((absolutelyAcyclic R h).prop_of_isZero hP₀)

/-- A coacyclic curved right module whose underlying graded right module has injective dimension at
most `n` is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [HasInjectiveDimensionLE (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) :
    absolutelyAcyclic R h X := by
  induction n generalizing X with
  | zero =>
    have hI : gradedInjective R h X :=
      (gradedInjective_iff X).2 (injective_iff_hasInjectiveDimensionLT_one.2 inferInstance)
    have hid : 𝟙 X = 0 := coacyclic_le_leftOrthogonal_gradedInjective R h X hX (𝟙 X) hI
    exact (absolutelyAcyclic R h).prop_of_isZero ((IsZero.iff_id_eq_zero X).2 hid)
  | succ n ih =>
    obtain ⟨I, _, g, _⟩ := exists_mono_to_coinducedObj_injective X.underlying
    let S : ShortComplex
        (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
      ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel g }
    have hS' : (S.map (forgetDifferential (h := h))).ShortExact := hS.map_of_exact _
    have : HasInjectiveDimensionLE
        (toGradedModuleCat ((dgClosedToHomotopy R).obj S.X₃).underlying) n :=
      (hS'.hasInjectiveDimensionLT_X₃_iff n
        (inferInstanceAs (Injective (toGradedModuleCat (coinducedObj h I))))).2
        (inferInstanceAs (HasInjectiveDimensionLT (toGradedModuleCat X.underlying) (n + 2)))
    have hI₀ : IsZero ((dgClosedToHomotopy R).obj S.X₂) := isZero_homotopy_coinducedObj h I
    have hC : coacyclic R h ((dgClosedToHomotopy R).obj S.X₃) :=
      prop_X₃_of_shortExact (coacyclic R h) (totalizations_le_coacyclic R h) hS hX
        ((coacyclic R h).prop_of_isZero hI₀)
    exact prop_X₁_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      ((absolutelyAcyclic R h).prop_of_isZero hI₀) (ih hC)

private theorem hasInjectiveDimensionLE_of_forall_hasProjectiveDimensionLE {C : Type*}
    [Category* C] [Abelian C] {n : ℕ} (hn : ∀ X : C, HasProjectiveDimensionLE X n) (Y : C) :
    HasInjectiveDimensionLE Y n := by
  let := HasExt.standard C
  exact HasInjectiveDimensionLT.mk fun i hi X e ↦ by
    have := hn X
    exact e.eq_zero_of_hasProjectiveDimensionLT (n + 1) hi

variable (R h)

/-- When every graded right `A`-module has projective dimension at most `n`, the absolutely acyclic
and contraacyclic classes of curved right `A`-modules coincide. -/
theorem absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE N n) :
    absolutelyAcyclic R h = contraacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_contraacyclic R h) fun X hX ↦
    have := hn (toGradedModuleCat X.underlying)
    absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLE n hX

/-- When every graded right `A`-module has injective dimension at most `n`, the absolutely acyclic
and coacyclic classes of curved right `A`-modules coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLE N n) :
    absolutelyAcyclic R h = coacyclic R h :=
  le_antisymm (absolutelyAcyclic_le_coacyclic R h) fun X hX ↦
    have := hn (toGradedModuleCat X.underlying)
    absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLE n hX

/-- **Positselski's Theorem 7.8(a) (coacyclic part).** When every graded right `A`-module has
projective dimension at most `n`, the absolutely acyclic and coacyclic classes of curved right
`A`-modules coincide. -/
theorem absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE N n) :
    absolutelyAcyclic R h = coacyclic R h :=
  absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLE R h n
    (hasInjectiveDimensionLE_of_forall_hasProjectiveDimensionLE hn)

/-- When every graded right `A`-module has projective dimension at most `n`, the coacyclic and
contraacyclic classes of curved right `A`-modules coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE N n) :
    coacyclic R h = contraacyclic R h :=
  (absolutelyAcyclic_eq_coacyclic_of_hasProjectiveDimensionLE R h n hn).symm.trans
    (absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLE R h n hn)

namespace AbsoluteDerivedCategory

/-- When every graded right `A`-module has projective dimension at most `n`, the canonical
comparison functor from the absolute derived category to the contraderived category is an
equivalence of categories. -/
theorem isEquivalence_toContraderived_of_hasProjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE N n) :
    (toContraderived R h).IsEquivalence := by
  have hEq := absolutelyAcyclic_eq_contraacyclic_of_hasProjectiveDimensionLE R h n hn
  have : (ContraderivedCategory.Q R h).IsLocalization (absolutelyAcyclic R h).trW := by
    dsimp [ContraderivedCategory.Q]
    rw [hEq]
    infer_instance
  exact Functor.isEquivalence_of_iso
    (Localization.isoUniqFunctor (Q R h) (ContraderivedCategory.Q R h)
      (absolutelyAcyclic R h).trW (toContraderived R h) (toContraderivedFactors R h)).symm

/-- When every graded right `A`-module has injective dimension at most `n`, the canonical
comparison functor from the absolute derived category to the coderived category is an equivalence
of categories. -/
theorem isEquivalence_toCoderived_of_hasInjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLE N n) :
    (toCoderived R h).IsEquivalence := by
  have hEq := absolutelyAcyclic_eq_coacyclic_of_hasInjectiveDimensionLE R h n hn
  have : (CoderivedCategory.Q R h).IsLocalization (absolutelyAcyclic R h).trW := by
    dsimp [CoderivedCategory.Q]
    rw [hEq]
    infer_instance
  exact Functor.isEquivalence_of_iso
    (Localization.isoUniqFunctor (Q R h) (CoderivedCategory.Q R h)
      (absolutelyAcyclic R h).trW (toCoderived R h) (toCoderivedFactors R h)).symm

/-- **Positselski's Theorem 7.8(a) (coderived equivalence).** When every graded right `A`-module
has projective dimension at most `n`, the canonical comparison functor from the absolute derived
category to the coderived category is an equivalence of categories. -/
theorem isEquivalence_toCoderived_of_hasProjectiveDimensionLE (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLE N n) :
    (toCoderived R h).IsEquivalence :=
  isEquivalence_toCoderived_of_hasInjectiveDimensionLE R h n
    (hasInjectiveDimensionLE_of_forall_hasProjectiveDimensionLE hn)

end AbsoluteDerivedCategory

end TauCeti.CurvedDGRightModuleCat
