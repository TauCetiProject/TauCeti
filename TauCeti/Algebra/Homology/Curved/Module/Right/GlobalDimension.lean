/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Coinduce
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Comparison
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Coinduced
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Induced
public import TauCeti.CategoryTheory.Abelian.Projective.Dimension

/-!
# Coincidence of curved derived categories of the second kind in finite graded global dimension

Let `(𝒜, d, w)` be a curved differential graded algebra. In general, the absolute derived category,
the coderived category, and the contraderived category of curved right modules are distinct Verdier
quotients of the curved homotopy category, related only by the canonical localization comparisons
`AbsoluteDerivedCategory.toCoderived` and `AbsoluteDerivedCategory.toContraderived`.

Positselski's Theorem 7.8(a) states that when the abelian category of graded right modules over the
underlying graded algebra has finite global homological dimension
(`∀ N, HasProjectiveDimensionLT N d`, which covers uniform bounds `≤ n` at `d = n + 1`), all three
acyclic classes of the second kind coincide, and both comparison functors are equivalences of
categories.

This file proves first the per-object dimension-shifting statements:

* a contraacyclic curved right module whose underlying graded module has finite projective
  dimension `< d` is absolutely acyclic
  (`TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT`);
* dually, a coacyclic curved right module whose underlying graded module has finite injective
  dimension `< d` is absolutely acyclic
  (`TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT`).

In the contraacyclic induction, one covers the underlying graded module `M♯` by a projective graded
module `P` and uses the adjunction `induced ⊣ forgetDifferential` to obtain a closed epimorphism
`G⁺(P) ⟶ M` from a contractible graded-projective curved module; its kernel has projective
dimension one lower and remains contraacyclic by two-out-of-three for short exact sequences. The
coacyclic induction is dual, embedding `M♯` into an injective graded module `I` (supplied by
`GradedModuleCat.enoughInjectives`) and using `forgetDifferential ⊣ coinduced` to obtain a closed
monomorphism `M ⟶ G⁻(I)` into a contractible graded-injective curved module.

When every graded right module has projective dimension `< d`, uniform projective and injective
dimension bounds coincide
(`CategoryTheory.forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT`),
so `coacyclic = absolutelyAcyclic = contraacyclic` and the canonical triangle functors
`D_abs ⥤ D_co` and `D_abs ⥤ D_ctr` are equivalences.

## Main results

* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT`:
  contraacyclic curved modules of finite graded projective dimension are absolutely acyclic.
* `TauCeti.CurvedDGRightModuleCat.absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT`:
  coacyclic curved modules of finite graded injective dimension are absolutely acyclic.
* `TauCeti.CurvedDGRightModuleCat.contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT`,
  `TauCeti.CurvedDGRightModuleCat.coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT`:
  in finite graded global dimension, all three acyclic classes of the second kind coincide.
* `AbsoluteDerivedCategory.isEquivalence_toCoderived_of_hasProjectiveDimensionLT`,
  `AbsoluteDerivedCategory.isEquivalence_toContraderived_of_hasProjectiveDimensionLT`:
  Positselski's Theorem 7.8(a) — both canonical comparison functors are equivalences.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6, Theorem 3.6.
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

private noncomputable instance :
    GradedAlgebra (InternalGrading.ofDecomposition 𝒜).opposite.piece := by
  have : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
    rw [InternalGrading.ofDecomposition_piece]
    infer_instance
  infer_instance

section PerObject

private theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT_succ (m : ℕ) :
    ∀ {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)},
      HasProjectiveDimensionLT (toGradedModuleCat X.underlying) (m + 1) →
      contraacyclic R h X → absolutelyAcyclic R h X := by
  induction m with
  | zero =>
    intro X hdim hX
    have hproj : gradedProjective R h X :=
      (gradedProjective_iff X).2 (projective_iff_hasProjectiveDimensionLT_one.2 hdim)
    have hid : 𝟙 X = 0 :=
      contraacyclic_le_rightOrthogonal_gradedProjective R h X hX (𝟙 X) hproj
    exact (absolutelyAcyclic R h).prop_of_isZero ((IsZero.iff_id_eq_zero X).2 hid)
  | succ m ih =>
    intro X hdim hX
    let M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
        (CurvedDGRightModuleCat.{u, u, u} h) :=
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) X.underlying
    let P := Projective.over ((forgetDifferential (h := h)).obj M)
    let π : P ⟶ (forgetDifferential (h := h)).obj M :=
      Projective.π ((forgetDifferential (h := h)).obj M)
    have := (inducedAdjForgetDifferential (h := h)).isLeftAdjoint
    let p : (induced (h := h)).obj P ⟶ M :=
      (induced (h := h)).map π ≫ (inducedAdjForgetDifferential (h := h)).counit.app M
    have : Epi p := epi_comp _ _
    let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
    have hSg : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    have hX₂_proj : Projective (S.map (forgetDifferential (h := h))).X₂ := by
      -- Unpack `(S.map forgetDifferential).X₂` to rewrite `(induced).obj P`.
      change Projective ((forgetDifferential (h := h)).obj ((induced (h := h)).obj P))
      rw [induced_obj, forgetDifferential_obj_of]
      infer_instance
    have hX₁_dim : HasProjectiveDimensionLT (S.map (forgetDifferential (h := h))).X₁ (m + 1) :=
      (hSg.hasProjectiveDimensionLT_X₃_iff m hX₂_proj).1 hdim
    have hX₂_zero : IsZero ((dgClosedToHomotopy R).obj S.X₂) := by
      -- Unpack `S.X₂` to rewrite `(induced).obj P`.
      change IsZero ((dgClosedToHomotopy R).obj ((induced (h := h)).obj P))
      rw [induced_obj]
      exact isZero_homotopy_inducedObj h P
    have hX₁_contra : contraacyclic R h ((dgClosedToHomotopy R).obj S.X₁) :=
      prop_X₁_of_shortExact (contraacyclic R h) (totalizations_le_contraacyclic R h) hS
        ((contraacyclic R h).prop_of_isZero hX₂_zero) hX
    have hX₁_abs : absolutelyAcyclic R h ((dgClosedToHomotopy R).obj S.X₁) :=
      ih hX₁_dim hX₁_contra
    exact prop_X₃_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      hX₁_abs ((absolutelyAcyclic R h).prop_of_isZero hX₂_zero)

/-- A contraacyclic curved right module whose underlying graded module has projective dimension
`< n` is absolutely acyclic. -/
theorem absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [hdim : HasProjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : contraacyclic R h X) : absolutelyAcyclic R h X :=
  absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT_succ n
    (@hasProjectiveDimensionLT_of_ge _ _ _ (toGradedModuleCat X.underlying) n (n + 1)
      (Nat.le_succ n) hdim) hX

private theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT_succ (m : ℕ) :
    ∀ {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)},
      HasInjectiveDimensionLT (toGradedModuleCat X.underlying) (m + 1) →
      coacyclic R h X → absolutelyAcyclic R h X := by
  induction m with
  | zero =>
    intro X hdim hX
    have hinj : gradedInjective R h X :=
      (gradedInjective_iff X).2 (injective_iff_hasInjectiveDimensionLT_one.2 hdim)
    have hid : 𝟙 X = 0 :=
      coacyclic_le_leftOrthogonal_gradedInjective R h X hX (𝟙 X) hinj
    exact (absolutelyAcyclic R h).prop_of_isZero ((IsZero.iff_id_eq_zero X).2 hid)
  | succ m ih =>
    intro X hdim hX
    let M : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
        (CurvedDGRightModuleCat.{u, u, u} h) :=
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) X.underlying
    let I := Injective.under ((forgetDifferential (h := h)).obj M)
    let ι : (forgetDifferential (h := h)).obj M ⟶ I :=
      Injective.ι ((forgetDifferential (h := h)).obj M)
    have := (forgetDifferentialAdjCoinduced (h := h)).isRightAdjoint
    let j : M ⟶ (coinduced (h := h)).obj I :=
      (forgetDifferentialAdjCoinduced (h := h)).unit.app M ≫ (coinduced (h := h)).map ι
    have : Mono j := mono_comp _ _
    let S := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel j }
    have hSg : (S.map (forgetDifferential (h := h))).ShortExact :=
      hS.map_of_exact (forgetDifferential (h := h))
    have hX₂_inj : Injective (S.map (forgetDifferential (h := h))).X₂ := by
      -- Unpack `(S.map forgetDifferential).X₂` to rewrite `(coinduced).obj I`.
      change Injective ((forgetDifferential (h := h)).obj ((coinduced (h := h)).obj I))
      rw [coinduced_obj, forgetDifferential_obj_of]
      infer_instance
    have hX₃_dim : HasInjectiveDimensionLT (S.map (forgetDifferential (h := h))).X₃ (m + 1) :=
      (hSg.hasInjectiveDimensionLT_X₃_iff m hX₂_inj).2 hdim
    have hX₂_zero : IsZero ((dgClosedToHomotopy R).obj S.X₂) := by
      -- Unpack `S.X₂` to rewrite `(coinduced).obj I`.
      change IsZero ((dgClosedToHomotopy R).obj ((coinduced (h := h)).obj I))
      rw [coinduced_obj]
      exact isZero_homotopy_coinducedObj h I
    have hX₃_co : coacyclic R h ((dgClosedToHomotopy R).obj S.X₃) :=
      prop_X₃_of_shortExact (coacyclic R h) (totalizations_le_coacyclic R h) hS
        hX ((coacyclic R h).prop_of_isZero hX₂_zero)
    have hX₃_abs : absolutelyAcyclic R h ((dgClosedToHomotopy R).obj S.X₃) :=
      ih hX₃_dim hX₃_co
    exact prop_X₁_of_shortExact (absolutelyAcyclic R h) (totalizations_le_absolutelyAcyclic R h) hS
      ((absolutelyAcyclic R h).prop_of_isZero hX₂_zero) hX₃_abs

/-- A coacyclic curved right module whose underlying graded module has injective dimension `< n`
is absolutely acyclic. -/
theorem absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT (n : ℕ)
    {X : DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)}
    [hdim : HasInjectiveDimensionLT (toGradedModuleCat X.underlying) n]
    (hX : coacyclic R h X) : absolutelyAcyclic R h X :=
  absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT_succ n
    (@hasInjectiveDimensionLT_of_ge _ _ _ (toGradedModuleCat X.underlying) n (n + 1)
      (Nat.le_succ n) hdim) hX

end PerObject

section GlobalDimension

variable (R h)

/-- **Positselski's Theorem 7.8(a), contraacyclic class.** When every graded right module over the
underlying graded algebra has projective dimension `< n`, the contraacyclic curved right modules
coincide with the absolutely acyclic ones. -/
theorem contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    contraacyclic R h = absolutelyAcyclic R h :=
  le_antisymm
    (fun X hX ↦
      have := hn (toGradedModuleCat X.underlying)
      absolutelyAcyclic_of_contraacyclic_of_hasProjectiveDimensionLT n hX)
    (absolutelyAcyclic_le_contraacyclic R h)

/-- **Positselski's Theorem 7.8(a), coacyclic class.** When every graded right module over the
underlying graded algebra has projective dimension `< n`, the coacyclic curved right modules
coincide with the absolutely acyclic ones. -/
theorem coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    coacyclic R h = absolutelyAcyclic R h := by
  have hinj := (forall_hasProjectiveDimensionLT_iff_forall_hasInjectiveDimensionLT
    (GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece) n).1 hn
  exact le_antisymm
    (fun X hX ↦
      have := hinj (toGradedModuleCat X.underlying)
      absolutelyAcyclic_of_coacyclic_of_hasInjectiveDimensionLT n hX)
    (absolutelyAcyclic_le_coacyclic R h)

/-- When every graded right module over the underlying graded algebra has projective dimension
`< n`, the coacyclic and contraacyclic classes of curved right modules coincide. -/
theorem coacyclic_eq_contraacyclic_of_hasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    coacyclic R h = contraacyclic R h :=
  (coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT R h n hn).trans
    (contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT R h n hn).symm

namespace AbsoluteDerivedCategory

/-- **Positselski's Theorem 7.8(a), coderived comparison.** When every graded right module over the
underlying graded algebra has projective dimension `< n`, the canonical triangle functor
`D_abs ⥤ D_co` is an equivalence of categories. -/
theorem isEquivalence_toCoderived_of_hasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    (toCoderived R h).IsEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_coacyclic R h)
  have hle : coacyclic R h ≤ absolutelyAcyclic R h :=
    (coacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT R h n hn).le
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE
      (absolutelyAcyclic_le_coacyclic R h) hle
  let : CatCommSq Φ.functor (Q R h) (CoderivedCategory.Q R h) (toCoderived R h) :=
    ⟨Functor.isoWhiskerRight
      (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor
        (absolutelyAcyclic_le_coacyclic R h))) (CoderivedCategory.Q R h) ≪≫
      Functor.leftUnitor (CoderivedCategory.Q R h) ≪≫
      (toCoderivedFactors R h).symm⟩
  exact Φ.isEquivalence (Q R h) (CoderivedCategory.Q R h) (toCoderived R h)

/-- **Positselski's Theorem 7.8(a), contraderived comparison.** When every graded right module over
the underlying graded algebra has projective dimension `< n`, the canonical triangle functor
`D_abs ⥤ D_ctr` is an equivalence of categories. -/
theorem isEquivalence_toContraderived_of_hasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    (toContraderived R h).IsEquivalence := by
  let Φ := ObjectProperty.trWLocalizerMorphismOfLE (absolutelyAcyclic_le_contraacyclic R h)
  have hle : contraacyclic R h ≤ absolutelyAcyclic R h :=
    (contraacyclic_eq_absolutelyAcyclic_of_hasProjectiveDimensionLT R h n hn).le
  have : Φ.IsLocalizedEquivalence :=
    ObjectProperty.isLocalizedEquivalence_trWLocalizerMorphismOfLE
      (absolutelyAcyclic_le_contraacyclic R h) hle
  let : CatCommSq Φ.functor (Q R h) (ContraderivedCategory.Q R h) (toContraderived R h) :=
    ⟨Functor.isoWhiskerRight
      (eqToIso (ObjectProperty.trWLocalizerMorphismOfLE_functor
        (absolutelyAcyclic_le_contraacyclic R h))) (ContraderivedCategory.Q R h) ≪≫
      Functor.leftUnitor (ContraderivedCategory.Q R h) ≪≫
      (toContraderivedFactors R h).symm⟩
  exact Φ.isEquivalence (Q R h) (ContraderivedCategory.Q R h) (toContraderived R h)

/-- The equivalence `D_abs ≌ D_co` induced by `toCoderived` in finite graded global dimension. -/
noncomputable def coderivedEquivalenceOfHasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    AbsoluteDerivedCategory R h ≌ CoderivedCategory R h :=
  have := isEquivalence_toCoderived_of_hasProjectiveDimensionLT R h n hn
  (toCoderived R h).asEquivalence

/-- The equivalence `D_abs ≌ D_ctr` induced by `toContraderived` in finite graded global
dimension. -/
noncomputable def contraderivedEquivalenceOfHasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    AbsoluteDerivedCategory R h ≌ ContraderivedCategory R h :=
  have := isEquivalence_toContraderived_of_hasProjectiveDimensionLT R h n hn
  (toContraderived R h).asEquivalence

end AbsoluteDerivedCategory

/-- The equivalence `D_co ≌ D_ctr` between the coderived and contraderived categories of curved
right modules in finite graded global dimension. -/
noncomputable def CoderivedCategory.contraderivedEquivalenceOfHasProjectiveDimensionLT (n : ℕ)
    (hn : ∀ N : GradedModuleCat.{u} (InternalGrading.ofDecomposition 𝒜).opposite.piece,
      HasProjectiveDimensionLT N n) :
    CoderivedCategory R h ≌ ContraderivedCategory R h :=
  (AbsoluteDerivedCategory.coderivedEquivalenceOfHasProjectiveDimensionLT R h n hn).symm.trans
    (AbsoluteDerivedCategory.contraderivedEquivalenceOfHasProjectiveDimensionLT R h n hn)

end GlobalDimension

end TauCeti.CurvedDGRightModuleCat
