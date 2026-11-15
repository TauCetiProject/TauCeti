/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Coinduced
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Induced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Injective
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective
public import TauCeti.CategoryTheory.Abelian.Injective.Dimension

/-!
# Finite graded global dimension and coincidence of curved acyclic classes

Let `(A, d, w)` be a curved DG algebra over `R`. When the abelian category of graded right
`A`-modules has finite global dimension — formulated as a uniform strict bound
`HasProjectiveDimensionLT M n` on objects `M`, which directly covers `HasProjectiveDimensionLE M d`
as the case `n = d + 1` — Positselski's Theorem 7.8(a) asserts that the three acyclic classes of the
second kind coincide on the curved homotopy category and that the canonical comparison functors
`D_abs → D_co` and `D_abs → D_ctr` are equivalences of categories.

The argument proceeds by constructing bounded graded-projective and graded-injective replacements
modulo absolutely acyclic objects:

* Given a curved right module `M` whose underlying graded right module has projective dimension
  `< n`, induction on `n` produces a graded-projective object `P` of the curved homotopy category
  and a morphism `P ⟶ M` in `(absolutelyAcyclic R h).trW`. At the inductive step, a projective
  presentation `X₀ ↠ M` of the underlying graded right module transposes across `inducedAdj` to a
  closed epimorphism `G⁺(X₀) ↠ M` whose middle term `G⁺(X₀)` is both contractible and
  graded-projective; its kernel `K` has projective dimension one lower, `cone(K ⟶ G⁺(X₀))` maps to
  `M` with cone equal to the totalization of `0 ⟶ K ⟶ G⁺(X₀) ⟶ M ⟶ 0`, and contractibility of
  `G⁺(X₀)` identifies `cone(K ⟶ G⁺(X₀))` with `K⟦1⟧` in the homotopy category.
* Dually, using `EnoughInjectives` on graded right `A`-modules and the right adjoint `G⁻` to
  `forgetDifferential`, every curved right module whose underlying graded right module has
  injective dimension `< n` admits a morphism `M ⟶ I` in `(absolutelyAcyclic R h).trW` into a
  graded-injective object `I`.
* If `X` is contraacyclic and `s : P ⟶ X` lies in `(absolutelyAcyclic R h).trW` with `P`
  graded-projective, right orthogonality of contraacyclic objects to graded-projective objects
  forces `s = 0`; since `AbsoluteDerivedCategory.Q R h` inverts `s`, `X` becomes zero in
  `AbsoluteDerivedCategory R h` and is therefore absolutely acyclic. Under a uniform bound on
  graded projective dimension, `CategoryTheory.forall_hasProjectiveDimensionLT_iff` transfers the
  same bound to graded injective dimension, and the dual left-orthogonality argument shows that
  every coacyclic object is absolutely acyclic.

## Main results

* `TauCeti.CurvedDGRightModuleCat.exists_gradedProjective_absolutelyAcyclic_trW`: every curved
  right module of finite graded projective dimension admits a graded-projective replacement in
  `(absolutelyAcyclic R h).trW`.
* `TauCeti.CurvedDGRightModuleCat.exists_gradedInjective_absolutelyAcyclic_trW`: every curved
  right module of finite graded injective dimension admits a graded-injective replacement in
  `(absolutelyAcyclic R h).trW`.
* `TauCeti.CurvedDGRightModuleCat.contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`:
  coincidence of the three curved acyclic classes in finite graded global dimension.
* `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT`:
  the comparison functors `D_abs → D_co` and `D_abs → D_ctr` are equivalences of categories.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.6, Theorem 7.8(a).
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed and homotopy categories keep the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-! ### Bounded graded-projective and graded-injective replacements -/

private theorem gradedMonoid_ofDecomposition_piece :
    SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

private theorem coneDesc_mem_absolutelyAcyclic_trW
    {S : ShortComplex
      (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h))}
    (hS : S.ShortExact) :
    (absolutelyAcyclic R h).trW ((dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero)) := by
  have htot := totalizations_le_absolutelyAcyclic R h _ (totalizations_totalization hS)
  rw [totalization_eq S] at htot
  exact ObjectProperty.trW.mk (absolutelyAcyclic R h)
    (coneTriangle_distinguished (coneDesc S.f S.g S.zero)) htot

private theorem exists_gradedProjective_trW_step (M : CurvedDGRightModuleCat.{u, u, u} h) (n : ℕ)
    [hM : HasProjectiveDimensionLT (toGradedModuleCat M) (n + 2)]
    (ih : ∀ (K : CurvedDGRightModuleCat.{u, u, u} h)
      [HasProjectiveDimensionLT (toGradedModuleCat K) (n + 1)],
      ∃ Q : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
        gradedProjective R h Q ∧
          ∃ t : Q ⟶ DGHomotopyCategory.of R K, (absolutelyAcyclic R h).trW t) :
    ∃ P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedProjective R h P ∧
        ∃ s : P ⟶ DGHomotopyCategory.of R M, (absolutelyAcyclic R h).trW s := by
  have := gradedMonoid_ofDecomposition_piece (𝒜 := 𝒜)
  obtain ⟨X₀, _, π, _⟩ :
      ∃ (X₀ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
        (_ : Projective X₀) (π : X₀ ⟶ toGradedModuleCat M), Epi π :=
    ⟨Projective.over (toGradedModuleCat M), inferInstance,
      Projective.π (toGradedModuleCat M), inferInstance⟩
  obtain ⟨p, _⟩ :
      ∃ p : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X₀) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M, Epi p :=
    ⟨inducedDesc (M := M) π, epi_inducedDesc π⟩
  let K : CurvedDGRightModuleCat.{u, u, u} h :=
    ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) (kernel p)
  let ι : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (induced h X₀) :=
    kernel.ι p
  let S := ShortComplex.mk ι p (kernel.condition p)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
  have : HasProjectiveDimensionLT (toGradedModuleCat K) (n + 1) :=
    ((hS.map_of_exact (forgetDifferential (h := h))).hasProjectiveDimensionLT_X₃_iff
      n (projective_toGradedModuleCat_induced h X₀)).1 hM
  obtain ⟨Q, hQ, t, ht⟩ := ih K
  have : IsIso (coneTriangle ι).mor₃ :=
    ((coneTriangle ι).isZero₂_iff_isIso₃ (coneTriangle_distinguished ι)).1
      (isZero_homotopy_induced h X₀)
  exact ⟨Q⟦(1 : ℤ)⟧, (gradedProjective R h).le_shift 1 _ hQ,
    t⟦(1 : ℤ)⟧' ≫ inv (coneTriangle ι).mor₃ ≫
      (dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero),
    (absolutelyAcyclic R h).trW.comp_mem _ _ (ht.shift 1)
      ((absolutelyAcyclic R h).trW.comp_mem _ _
        (ObjectProperty.trW_of_isIso (absolutelyAcyclic R h) _)
        (coneDesc_mem_absolutelyAcyclic_trW hS))⟩

private theorem exists_gradedProjective_trW_of_lt :
    ∀ (n : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h)
      [HasProjectiveDimensionLT (toGradedModuleCat M) n],
      ∃ P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
        gradedProjective R h P ∧
          ∃ s : P ⟶ DGHomotopyCategory.of R M, (absolutelyAcyclic R h).trW s
  | 0, M, _ =>
    have : HasProjectiveDimensionLT (toGradedModuleCat M) 1 :=
      hasProjectiveDimensionLT_of_ge (toGradedModuleCat M) 0 1 (Nat.zero_le 1)
    ⟨DGHomotopyCategory.of R M,
      (gradedProjective_iff _).2 (projective_iff_hasProjectiveDimensionLT_one.2 this),
      𝟙 _, MorphismProperty.id_mem _ _⟩
  | 1, M, hM =>
    ⟨DGHomotopyCategory.of R M,
      (gradedProjective_iff _).2 (projective_iff_hasProjectiveDimensionLT_one.2 hM),
      𝟙 _, MorphismProperty.id_mem _ _⟩
  | n + 2, M, _ =>
    exists_gradedProjective_trW_step M n (exists_gradedProjective_trW_of_lt (n + 1))

/-- Every object of the curved homotopy category whose underlying graded right module has
projective dimension `< n` admits a morphism from a graded-projective object with absolutely
acyclic cone. -/
theorem exists_gradedProjective_absolutelyAcyclic_trW
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) (n : ℕ)
    [HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    ∃ P : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedProjective R h P ∧ ∃ s : P ⟶ X, (absolutelyAcyclic R h).trW s :=
  exists_gradedProjective_trW_of_lt n X.underlying

private theorem exists_gradedInjective_trW_step (M : CurvedDGRightModuleCat.{u, u, u} h) (n : ℕ)
    [hM : HasInjectiveDimensionLT (toGradedModuleCat M) (n + 2)]
    (ih : ∀ (C : CurvedDGRightModuleCat.{u, u, u} h)
      [HasInjectiveDimensionLT (toGradedModuleCat C) (n + 1)],
      ∃ J : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
        gradedInjective R h J ∧
          ∃ t : DGHomotopyCategory.of R C ⟶ J, (absolutelyAcyclic R h).trW t) :
    ∃ I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedInjective R h I ∧
        ∃ s : DGHomotopyCategory.of R M ⟶ I, (absolutelyAcyclic R h).trW s := by
  have := gradedMonoid_ofDecomposition_piece (𝒜 := 𝒜)
  obtain ⟨Y₀, _, j, _⟩ :
      ∃ (Y₀ : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece)
        (_ : Injective Y₀) (j : toGradedModuleCat M ⟶ Y₀), Mono j :=
    ⟨Injective.under (toGradedModuleCat M), inferInstance,
      Injective.ι (toGradedModuleCat M), inferInstance⟩
  obtain ⟨i, _⟩ :
      ∃ i : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y₀), Mono i :=
    ⟨coinducedLift (M := M) j, mono_coinducedLift j⟩
  let C : CurvedDGRightModuleCat.{u, u, u} h :=
    ForgetEnrichment.to (CochainComplex (ModuleCat R) ℤ) (cokernel i)
  let q : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (coinduced h Y₀) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) C :=
    cokernel.π i
  let S := ShortComplex.mk i q (cokernel.condition i)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
  have : HasInjectiveDimensionLT (toGradedModuleCat C) (n + 1) :=
    ((hS.map_of_exact (forgetDifferential (h := h))).hasInjectiveDimensionLT_X₃_iff
      n (injective_toGradedModuleCat_coinduced h Y₀)).2 hM
  obtain ⟨J, hJ, t, ht⟩ := ih C
  obtain ⟨w₃, _⟩ :
      ∃ w₃ : (DGHomotopyCategory.of R M)⟦(1 : ℤ)⟧ ⟶ DGHomotopyCategory.of R (cone i),
        IsIso w₃ := by
    have : IsIso (coneTriangle i).mor₃ :=
      ((coneTriangle i).isZero₂_iff_isIso₃ (coneTriangle_distinguished i)).1
        (isZero_homotopy_coinduced h Y₀)
    exact ⟨inv (coneTriangle i).mor₃, inferInstance⟩
  have hu : (absolutelyAcyclic R h).trW
      (w₃ ≫ (dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero) ≫ t) :=
    (absolutelyAcyclic R h).trW.comp_mem _ _
      (ObjectProperty.trW_of_isIso (absolutelyAcyclic R h) w₃)
      ((absolutelyAcyclic R h).trW.comp_mem _ _ (coneDesc_mem_absolutelyAcyclic_trW hS) ht)
  let e :=
    (shiftEquiv (DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) (1 : ℤ)).unitIso.app
      (DGHomotopyCategory.of R M)
  exact ⟨J⟦(-1 : ℤ)⟧, (gradedInjective R h).le_shift (-1) _ hJ,
    e.hom ≫ (w₃ ≫ (dgClosedToHomotopy R).map (coneDesc S.f S.g S.zero) ≫ t)⟦(-1 : ℤ)⟧',
    (absolutelyAcyclic R h).trW.comp_mem _ _
      (ObjectProperty.trW_of_isIso (absolutelyAcyclic R h) e.hom) (hu.shift (-1))⟩

private theorem exists_gradedInjective_trW_of_lt :
    ∀ (n : ℕ) (M : CurvedDGRightModuleCat.{u, u, u} h)
      [HasInjectiveDimensionLT (toGradedModuleCat M) n],
      ∃ I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
        gradedInjective R h I ∧
          ∃ s : DGHomotopyCategory.of R M ⟶ I, (absolutelyAcyclic R h).trW s
  | 0, M, _ =>
    have : HasInjectiveDimensionLT (toGradedModuleCat M) 1 :=
      hasInjectiveDimensionLT_of_ge (toGradedModuleCat M) 0 1 (Nat.zero_le 1)
    ⟨DGHomotopyCategory.of R M,
      (gradedInjective_iff _).2 (injective_iff_hasInjectiveDimensionLT_one.2 this),
      𝟙 _, MorphismProperty.id_mem _ _⟩
  | 1, M, hM =>
    ⟨DGHomotopyCategory.of R M,
      (gradedInjective_iff _).2 (injective_iff_hasInjectiveDimensionLT_one.2 hM),
      𝟙 _, MorphismProperty.id_mem _ _⟩
  | n + 2, M, _ =>
    exists_gradedInjective_trW_step M n (exists_gradedInjective_trW_of_lt (n + 1))

/-- Every object of the curved homotopy category whose underlying graded right module has
injective dimension `< n` admits a morphism into a graded-injective object with absolutely
acyclic cone. -/
theorem exists_gradedInjective_absolutelyAcyclic_trW
    (X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) (n : ℕ)
    [HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n] :
    ∃ I : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h),
      gradedInjective R h I ∧ ∃ s : X ⟶ I, (absolutelyAcyclic R h).trW s :=
  exists_gradedInjective_trW_of_lt n X.underlying

/-! ### Positselski's Theorem 7.8(a) -/

/-- **Positselski's Theorem 7.8(a), contraacyclic case.** If every graded right `A`-module has
projective dimension `< n`, then the contraacyclic curved right modules coincide with the
absolutely acyclic curved right modules. -/
theorem contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT {n : ℕ}
    (hd : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT M n) :
    contraacyclic R h = absolutelyAcyclic R h := by
  refine le_antisymm (fun X hX ↦ ?_) (absolutelyAcyclic_le_contraacyclic R h)
  have := hd (toGradedModuleCat X.underlying)
  obtain ⟨P, hP, s, hs⟩ := exists_gradedProjective_absolutelyAcyclic_trW (h := h) X n
  have hs0 : (AbsoluteDerivedCategory.Q R h).map s = 0 := by
    rw [contraacyclic_le_rightOrthogonal_gradedProjective R h X hX s hP, Functor.map_zero]
  have : IsIso ((AbsoluteDerivedCategory.Q R h).map s) :=
    Localization.inverts (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW s hs
  refine (AbsoluteDerivedCategory.isZero_Q_obj_iff X).1 ((IsZero.iff_id_eq_zero _).2 ?_)
  exact (IsIso.inv_hom_id ((AbsoluteDerivedCategory.Q R h).map s)).symm.trans
    ((congrArg (inv ((AbsoluteDerivedCategory.Q R h).map s) ≫ ·) hs0).trans comp_zero)

/-- **Positselski's Theorem 7.8(a), coacyclic case.** If every graded right `A`-module has
projective dimension `< n`, then the coacyclic curved right modules coincide with the absolutely
acyclic curved right modules. -/
theorem coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT {n : ℕ}
    (hd : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT M n) :
    coacyclic R h = absolutelyAcyclic R h := by
  have hInj : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasInjectiveDimensionLT M n :=
    (CategoryTheory.forall_hasProjectiveDimensionLT_iff _ n).1 hd
  refine le_antisymm (fun X hX ↦ ?_) (absolutelyAcyclic_le_coacyclic R h)
  have := hInj (toGradedModuleCat X.underlying)
  obtain ⟨I, hI, s, hs⟩ := exists_gradedInjective_absolutelyAcyclic_trW (h := h) X n
  have hs0 : (AbsoluteDerivedCategory.Q R h).map s = 0 := by
    rw [coacyclic_le_leftOrthogonal_gradedInjective R h X hX s hI, Functor.map_zero]
  have : IsIso ((AbsoluteDerivedCategory.Q R h).map s) :=
    Localization.inverts (AbsoluteDerivedCategory.Q R h) (absolutelyAcyclic R h).trW s hs
  refine (AbsoluteDerivedCategory.isZero_Q_obj_iff X).1 ((IsZero.iff_id_eq_zero _).2 ?_)
  exact (IsIso.hom_inv_id ((AbsoluteDerivedCategory.Q R h).map s)).symm.trans
    ((congrArg (· ≫ inv ((AbsoluteDerivedCategory.Q R h).map s)) hs0).trans zero_comp)

/-- **Positselski's Theorem 7.8(a), coacyclic-contraacyclic coincidence.** If every graded right
`A`-module has projective dimension `< n`, then the coacyclic and contraacyclic curved right
modules coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT {n : ℕ}
    (hd : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT M n) :
    coacyclic R h = contraacyclic R h :=
  (coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT hd).trans
    (contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT hd).symm

namespace AbsoluteDerivedCategory

/-- **Positselski's Theorem 7.8(a), coderived comparison.** If every graded right `A`-module has
projective dimension `< n`, then the canonical comparison functor from the absolute derived
category to the coderived category is an equivalence of categories. -/
theorem isEquivalence_toCoderived_of_hasProjectiveDimensionLT {n : ℕ}
    (hd : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT M n) :
    (toCoderived R h).IsEquivalence := by
  have hW : (coacyclic R h).trW = (absolutelyAcyclic R h).trW := by
    rw [coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT hd]
  have : (CoderivedCategory.Q R h).IsLocalization (absolutelyAcyclic R h).trW := by
    rw [← hW]
    infer_instance
  exact Functor.isEquivalence_of_iso
    (Localization.isoUniqFunctor (Q R h) (CoderivedCategory.Q R h)
      (absolutelyAcyclic R h).trW (toCoderived R h) (toCoderivedFactors R h)).symm

/-- **Positselski's Theorem 7.8(a), contraderived comparison.** If every graded right `A`-module
has projective dimension `< n`, then the canonical comparison functor from the absolute derived
category to the contraderived category is an equivalence of categories. -/
theorem isEquivalence_toContraderived_of_hasProjectiveDimensionLT {n : ℕ}
    (hd : ∀ M : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT M n) :
    (toContraderived R h).IsEquivalence := by
  have hW : (contraacyclic R h).trW = (absolutelyAcyclic R h).trW := by
    rw [contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT hd]
  have : (ContraderivedCategory.Q R h).IsLocalization (absolutelyAcyclic R h).trW := by
    rw [← hW]
    infer_instance
  exact Functor.isEquivalence_of_iso
    (Localization.isoUniqFunctor (Q R h) (ContraderivedCategory.Q R h)
      (absolutelyAcyclic R h).trW (toContraderived R h) (toContraderivedFactors R h)).symm

end AbsoluteDerivedCategory

end TauCeti.CurvedDGRightModuleCat
