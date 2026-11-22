/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective

/-!
# Graded-projective resolutions of curved right modules

This file establishes the finite-dimension graded-projective replacement theorem and defines left
resolutions in the closed abelian category of curved differential graded right modules.

1. **Finite graded projective dimension replacement.** If the underlying graded right module of a
   curved right module `N` has finite projective dimension `≤ d`, then there is a closed morphism
   `f : Q ⟶ N` from a graded-projective curved module `Q` whose mapping cone is absolutely
   acyclic. The proof proceeds by induction on `d`, covering `N` by a graded-projective curved
   module via `exists_epi_contractible_gradedProjective`, resolving the kernel `K`, and taking the
   mapping cone of `Q' ⟶ K ⟶ P`.
2. **Left resolutions.** A `LeftResolution` of a curved module `M` is a sequence of short exact
   sequences `0 ⟶ K_{n+1} ⟶ P_n ⟶ K_n ⟶ 0` in the closed abelian category starting from
   `K_0 ≅ M`. Iterating `exists_epi_contractible_gradedProjective` and kernels produces a
   canonical graded-projective left resolution `LeftResolution.ofGradedProjective M`.

## Main definitions

* `TauCeti.CurvedDGRightModuleCat.LeftResolution`: a left resolution of a curved right module by
  short exact sequences in the closed abelian category.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.ofGradedProjective`: a canonical left resolution
  whose terms are graded-projective curved right modules.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.diff`: the horizontal differential
  `δ_n = π_{n+1} ≫ ι_n : P_{n+1} ⟶ P_n` of a left resolution.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.aug`: the augmentation `π_0 ≫ syzygyZeroIso.hom`
  from `P_0` to `M`.

## Main results

* `TauCeti.CurvedDGRightModuleCat.exists_gradedProjective_absolutelyAcyclic_cone`: every curved
  module whose underlying graded module has finite projective dimension admits a closed morphism
  from a graded-projective curved module with absolutely acyclic cone.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.projective_ofGradedProjective_term`: every term
  of `LeftResolution.ofGradedProjective M` is graded-projective.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.exact_diff_aug` and
  `TauCeti.CurvedDGRightModuleCat.LeftResolution.exact_diff`: exactness of the augmented
  resolution `⋯ ⟶ P_1 ⟶ P_0 ⟶ M ⟶ 0`.

## References

* L. Positselski, *Two kinds of derived categories, Koszul duality, and comodule-contramodule
  correspondence*, Mem. Amer. Math. Soc. **212** (2011), no. 996, Section 3.6.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond. Math.
  Soc. **55** (2023), 1553–1640, Section 7.9, Theorem 7.9(b).
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

local instance : SetLike.GradedMonoid (InternalGrading.ofDecomposition 𝒜).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-! ### Finite graded projective dimension replacement -/

/-- If `g : Q' ⟶ K` becomes an isomorphism in the absolute derived category, then the induced
comparison `cone (g ≫ ι) ⟶ cone ι` with `𝟙 P` on the target also becomes an isomorphism there. -/
private theorem isIso_absoluteDerived_coneMap_id {Q' K P : CurvedDGRightModuleCat.{u, u, u} h}
    (g : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q' ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K)
    (ι : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P)
    (hg : IsIso ((AbsoluteDerivedCategory.Q R h).map ((dgClosedToHomotopy R).map g))) :
    IsIso ((AbsoluteDerivedCategory.Q R h).map ((dgClosedToHomotopy R).map
      (coneMap (g ≫ ι) ι g
        (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P)) 0
        (by intro x; simp)))) := by
  let φ := (AbsoluteDerivedCategory.Q R h).mapTriangle.map
    (coneTriangleMap (g ≫ ι) ι g
      (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P)) 0 (by intro x; simp))
  have hT₁ := (AbsoluteDerivedCategory.Q R h).map_distinguished _
    (coneTriangle_distinguished (g ≫ ι))
  have hT₂ := (AbsoluteDerivedCategory.Q R h).map_distinguished _
    (coneTriangle_distinguished ι)
  have h₂ : IsIso φ.hom₂ := by
    simp only [φ, Functor.mapTriangle_map_hom₂, coneTriangleMap_hom₂]
    infer_instance
  exact isIso₃_of_isIso₁₂ φ hT₁ hT₂ hg h₂

/-- Every curved right module whose underlying graded module has projective dimension `≤ d`
admits a closed morphism from a graded-projective curved right module whose mapping cone is
absolutely acyclic. -/
theorem exists_gradedProjective_absolutelyAcyclic_cone
    {N : CurvedDGRightModuleCat.{u, u, u} h} {d : ℕ}
    (hd : HasProjectiveDimensionLE (toGradedModuleCat N) d) :
    ∃ (Q : CurvedDGRightModuleCat.{u, u, u} h)
      (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) Q ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N),
      Projective (toGradedModuleCat Q) ∧
        absolutelyAcyclic R h (DGHomotopyCategory.of R (cone f)) := by
  induction d generalizing N with
  | zero =>
    have hN : Projective (toGradedModuleCat N) :=
      (projective_iff_hasProjectiveDimensionLE_zero _).2 hd
    refine ⟨N, 𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N), hN, ?_⟩
    exact (absolutelyAcyclic R h).prop_of_isZero (isZero_homotopy_cone_isIso _)
  | succ d ih =>
    obtain ⟨P, p, hp, hP, _⟩ := exists_epi_contractible_gradedProjective N
    let K := kernelObj p
    let ι := kernelι p
    let S := ShortComplex.mk ι p (kernelι_comp p)
    have : Epi p := hp
    have hS : S.ShortExact := shortExact_kernelι p
    have hSF := hS.map_of_exact (forgetDifferential (h := h))
    have hK : HasProjectiveDimensionLE (toGradedModuleCat K) d :=
      (hSF.hasProjectiveDimensionLT_X₃_iff d hP).1 hd
    obtain ⟨Q', g, hQ', hg⟩ := ih hK
    have hcomp : (g ≫ ι) ≫ p = 0 := by
      rw [Category.assoc, kernelι_comp, Limits.comp_zero]
    let f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cone (g ≫ ι)) ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N :=
      coneDesc (g ≫ ι) p hcomp
    refine ⟨cone (g ≫ ι), f, inferInstance, ?_⟩
    let cMap := coneMap (g ≫ ι) ι g
      (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P)) 0 (by intro x; simp)
    have hfac : f = cMap ≫ coneDesc ι p (kernelι_comp p) := by
      apply closedHom_ext
      rintro ⟨x₁, x₂⟩
      simp only [f, cMap, closedHom_comp, LinearMap.comp_apply, closedHom_coneDesc,
        closedHom_coneMap_apply, closedHom_id, LinearMap.id_apply, Submodule.coe_zero,
        LinearMap.zero_apply, add_zero]
      rfl
    have hcMapIso := isIso_absoluteDerived_coneMap_id g ι
      ((AbsoluteDerivedCategory.isIso_Q_map_iff g).2 hg)
    have hDescIso : IsIso ((AbsoluteDerivedCategory.Q R h).map
        ((dgClosedToHomotopy R).map (coneDesc ι p (kernelι_comp p)))) := by
      rw [AbsoluteDerivedCategory.isIso_Q_map_iff, ← totalization_eq S]
      exact totalizations_le_absolutelyAcyclic R h _ (totalizations_totalization hS)
    rw [← AbsoluteDerivedCategory.isIso_Q_map_iff, hfac, Functor.map_comp, Functor.map_comp]
    infer_instance

/-! ### Left resolutions in the closed abelian category -/

/-- A **left resolution** of a curved right module `M`: a chain of short exact sequences
`0 ⟶ K_{n+1} ⟶ P_n ⟶ K_n ⟶ 0` in the closed abelian category starting from `K_0 ≅ M`. -/
structure LeftResolution (M : CurvedDGRightModuleCat.{u, u, u} h) where
  /-- The `n`-th syzygy curved module `K_n`. -/
  syzygy : ℕ → CurvedDGRightModuleCat.{u, u, u} h
  /-- The `n`-th resolution term `P_n`. -/
  term : ℕ → CurvedDGRightModuleCat.{u, u, u} h
  /-- Identification of the `0`-th syzygy `K_0` with `M`. -/
  syzygyZeroIso :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (syzygy 0) ≅
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M
  /-- The syzygy inclusion `K_{n+1} ⟶ P_n`. -/
  ι : ∀ n, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (syzygy (n + 1)) ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (term n)
  /-- The cover morphism `P_n ⟶ K_n`. -/
  π : ∀ n, ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (term n) ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (syzygy n)
  /-- Exactness composition `ι_n ≫ π_n = 0`. -/
  ι_comp_π : ∀ n, ι n ≫ π n = 0
  /-- Each triple `0 ⟶ K_{n+1} ⟶ P_n ⟶ K_n ⟶ 0` is short exact. -/
  shortExact : ∀ n, (ShortComplex.mk (ι n) (π n) (ι_comp_π n)).ShortExact

namespace LeftResolution

section Canonical

/-- One chosen graded-projective surjection onto a curved module, used to build a canonical
graded-projective left resolution recursively. -/
private noncomputable def gradedProjectiveCover (K : CurvedDGRightModuleCat.{u, u, u} h) :
    Σ' (P : CurvedDGRightModuleCat.{u, u, u} h)
      (p : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) P ⟶
        ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) K),
      Epi p ∧ Projective (toGradedModuleCat P) :=
  let hcov := exists_epi_contractible_gradedProjective K
  let P := Classical.choose hcov
  let hcov' := Classical.choose_spec hcov
  let p := Classical.choose hcov'
  let hp := Classical.choose_spec hcov'
  ⟨P, p, hp.1, hp.2.1⟩

private noncomputable def canonicalSyzygy (M : CurvedDGRightModuleCat.{u, u, u} h) :
    ℕ → CurvedDGRightModuleCat.{u, u, u} h
  | 0 => M
  | n + 1 => kernelObj (gradedProjectiveCover (canonicalSyzygy M n)).snd.fst

/-- Every curved right module admits a left resolution whose terms are graded-projective curved
right modules. -/
noncomputable def ofGradedProjective (M : CurvedDGRightModuleCat.{u, u, u} h) :
    LeftResolution M where
  syzygy := canonicalSyzygy M
  term n := (gradedProjectiveCover (canonicalSyzygy M n)).fst
  syzygyZeroIso := Iso.refl _
  ι n := kernelι (gradedProjectiveCover (canonicalSyzygy M n)).snd.fst
  π n := (gradedProjectiveCover (canonicalSyzygy M n)).snd.fst
  ι_comp_π _ := kernelι_comp _
  shortExact n :=
    have : Epi (gradedProjectiveCover (canonicalSyzygy M n)).snd.fst :=
      (gradedProjectiveCover (canonicalSyzygy M n)).snd.snd.1
    shortExact_kernelι _

/-- Every term of the canonical resolution `LeftResolution.ofGradedProjective M` is
graded-projective. -/
instance projective_ofGradedProjective_term (M : CurvedDGRightModuleCat.{u, u, u} h) (n : ℕ) :
    Projective (toGradedModuleCat ((ofGradedProjective M).term n)) :=
  (gradedProjectiveCover (canonicalSyzygy M n)).snd.snd.2

end Canonical

variable {M : CurvedDGRightModuleCat.{u, u, u} h} (r : LeftResolution M)

/-- The internal horizontal differential `δ_n = π_{n+1} ≫ ι_n : P_{n+1} ⟶ P_n` of a left
resolution. -/
noncomputable def diff (n : ℕ) :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.term (n + 1)) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.term n) :=
  r.π (n + 1) ≫ r.ι n

/-- The `n`-th horizontal differential factors as `r.π (n + 1) ≫ r.ι n`. -/
theorem diff_eq (n : ℕ) : r.diff n = r.π (n + 1) ≫ r.ι n :=
  (rfl)

/-- On elements, `closedHom (r.diff n)` applies `π_{n+1}` followed by `ι_n`. -/
@[simp]
theorem closedHom_diff_apply (n : ℕ) (x : r.term (n + 1)) :
    closedHom (r.diff n) x = closedHom (r.ι n) (closedHom (r.π (n + 1)) x) := by
  rw [diff_eq, closedHom_comp, LinearMap.comp_apply]

/-- Adjacent horizontal differentials compose to zero. -/
@[reassoc (attr := simp)]
theorem diff_comp_diff (n : ℕ) : r.diff (n + 1) ≫ r.diff n = 0 := by
  simp only [diff_eq, Category.assoc]
  rw [← Category.assoc (r.ι (n + 1)), r.ι_comp_π, Limits.zero_comp, Limits.comp_zero]

/-- The `n`-th horizontal differential followed by `π_n` vanishes. -/
@[reassoc (attr := simp)]
theorem diff_comp_π (n : ℕ) : r.diff n ≫ r.π n = 0 := by
  simp only [diff_eq, Category.assoc, r.ι_comp_π, Limits.comp_zero]

/-- The augmentation morphism `P_0 ⟶ M` of a left resolution, given by `π_0 ≫ syzygyZeroIso.hom`. -/
noncomputable def aug :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (r.term 0) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  r.π 0 ≫ r.syzygyZeroIso.hom

/-- The augmentation factors as `r.π 0 ≫ r.syzygyZeroIso.hom`. -/
theorem aug_eq : r.aug = r.π 0 ≫ r.syzygyZeroIso.hom :=
  (rfl)

/-- On elements, `closedHom r.aug` applies `π_0` followed by `syzygyZeroIso.hom`. -/
@[simp]
theorem closedHom_aug_apply (x : r.term 0) :
    closedHom r.aug x = closedHom r.syzygyZeroIso.hom (closedHom (r.π 0) x) := by
  rw [aug_eq, closedHom_comp, LinearMap.comp_apply]

/-- The `0`-th horizontal differential followed by the augmentation vanishes. -/
@[reassoc (attr := simp)]
theorem diff_comp_aug : r.diff 0 ≫ r.aug = 0 := by
  rw [aug_eq, ← Category.assoc, r.diff_comp_π 0, Limits.zero_comp]

/-- In a left resolution, each `r.ι n` is a monomorphism. -/
instance mono_ι (n : ℕ) : Mono (r.ι n) :=
  (r.shortExact n).mono_f

/-- In a left resolution, each `r.π n` is an epimorphism. -/
instance epi_π (n : ℕ) : Epi (r.π n) :=
  (r.shortExact n).epi_g

/-- The augmentation `P_0 ⟶ M` of a left resolution is an epimorphism. -/
instance epi_aug : Epi r.aug := by
  rw [aug_eq]
  exact epi_comp (r.π 0) r.syzygyZeroIso.hom

/-- In a left resolution, `closedHom (r.ι n)` is injective. -/
theorem injective_ι (n : ℕ) : Function.Injective (closedHom (r.ι n)) :=
  (shortExact_iff.1 (r.shortExact n)).1

/-- In a left resolution, `closedHom (r.π n)` is surjective. -/
theorem surjective_π (n : ℕ) : Function.Surjective (closedHom (r.π n)) :=
  (shortExact_iff.1 (r.shortExact n)).2.1

/-- The augmentation `P_0 ⟶ M` is surjective on elements. -/
theorem surjective_aug : Function.Surjective (closedHom r.aug) :=
  (GradedModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((forgetDifferential (h := h)).map r.aug))

/-- In a left resolution, `closedHom (r.ι n)` and `closedHom (r.π n)` are exact. -/
theorem exact_ι_π (n : ℕ) : Function.Exact (closedHom (r.ι n)) (closedHom (r.π n)) :=
  (shortExact_iff.1 (r.shortExact n)).2.2

/-- At elements, `closedHom (r.diff 0)` and `closedHom r.aug` are exact at `P_0`. -/
theorem exact_closedHom_diff_aug : Function.Exact (closedHom (r.diff 0)) (closedHom r.aug) := by
  intro x
  constructor
  · intro hx
    have hπ : closedHom (r.π 0) x = 0 := by
      have h' : closedHom r.syzygyZeroIso.hom (closedHom (r.π 0) x) = 0 := by
        simpa only [closedHom_aug_apply] using hx
      have hinj : Function.Injective (closedHom r.syzygyZeroIso.hom) :=
        (GradedModuleCat.mono_iff_injective _).1
          (inferInstance : Mono ((forgetDifferential (h := h)).map r.syzygyZeroIso.hom))
      exact hinj (by simpa only [map_zero] using h')
    obtain ⟨k, hk⟩ := (r.exact_ι_π 0 x).1 hπ
    obtain ⟨y, hy⟩ := r.surjective_π 1 k
    refine ⟨y, ?_⟩
    rw [closedHom_diff_apply, hy, hk]
  · rintro ⟨y, rfl⟩
    have h0 := congrArg (fun l ↦ closedHom l y) r.diff_comp_aug
    simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
      using h0

/-- The augmented sequence `P_1 ⟶ P_0 ⟶ M` is exact at `P_0` in the closed abelian category. -/
theorem exact_diff_aug : (ShortComplex.mk (r.diff 0) r.aug r.diff_comp_aug).Exact :=
  ((ShortComplex.mk (r.diff 0) r.aug r.diff_comp_aug).exact_map_iff_of_faithful
    (forgetDifferential (h := h))).1 (GradedModuleCat.exact_iff.2 r.exact_closedHom_diff_aug)

/-- At elements, consecutive horizontal differentials `r.diff (n + 1)` and `r.diff n` are exact
at `P_{n+1}`. -/
theorem exact_closedHom_diff (n : ℕ) :
    Function.Exact (closedHom (r.diff (n + 1))) (closedHom (r.diff n)) := by
  intro x
  constructor
  · intro hx
    have hπ : closedHom (r.π (n + 1)) x = 0 :=
      r.injective_ι n (by simpa only [closedHom_diff_apply, map_zero] using hx)
    obtain ⟨k, hk⟩ := (r.exact_ι_π (n + 1) x).1 hπ
    obtain ⟨y, hy⟩ := r.surjective_π (n + 2) k
    refine ⟨y, ?_⟩
    rw [closedHom_diff_apply, hy, hk]
  · rintro ⟨y, rfl⟩
    have h0 := congrArg (fun l ↦ closedHom l y) (r.diff_comp_diff n)
    simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
      using h0

/-- Consecutive horizontal differentials `P_{n+2} ⟶ P_{n+1} ⟶ P_n` are exact in the closed
abelian category. -/
theorem exact_diff (n : ℕ) :
    (ShortComplex.mk (r.diff (n + 1)) (r.diff n) (r.diff_comp_diff n)).Exact :=
  ((ShortComplex.mk (r.diff (n + 1)) (r.diff n) (r.diff_comp_diff n)).exact_map_iff_of_faithful
    (forgetDifferential (h := h))).1 (GradedModuleCat.exact_iff.2 (r.exact_closedHom_diff n))

end LeftResolution

end TauCeti.CurvedDGRightModuleCat
