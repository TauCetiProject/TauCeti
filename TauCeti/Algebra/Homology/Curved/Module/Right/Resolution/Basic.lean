/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Free
public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded.Projective.Basic

/-!
# Graded-projective resolutions of curved right modules

This file defines left resolutions in the closed abelian category of curved differential graded
right modules. A `LeftResolution` of a curved module `M` is a sequence of short exact sequences
`0 ⟶ K_{n+1} ⟶ P_n ⟶ K_n ⟶ 0` in the closed abelian category starting from `K_0 ≅ M`.
Iterating `exists_epi_contractible_gradedProjective` and kernels produces a canonical
graded-projective left resolution `LeftResolution.ofGradedProjective M`.

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

* `TauCeti.CurvedDGRightModuleCat.LeftResolution.projective_ofGradedProjective_term`: every term
  of `LeftResolution.ofGradedProjective M` is graded-projective.
* `TauCeti.CurvedDGRightModuleCat.LeftResolution.isZero_homotopy_ofGradedProjective_term`: every
  term of `LeftResolution.ofGradedProjective M` is contractible in the curved homotopy category.
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
      Epi p ∧ Projective (toGradedModuleCat P) ∧ IsZero (DGHomotopyCategory.of R P) :=
  let hcov := exists_epi_contractible_gradedProjective K
  let P := Classical.choose hcov
  let hcov' := Classical.choose_spec hcov
  let p := Classical.choose hcov'
  let hp := Classical.choose_spec hcov'
  ⟨P, p, hp.1, hp.2.1, hp.2.2⟩

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
  (gradedProjectiveCover (canonicalSyzygy M n)).snd.snd.2.1

/-- Every term of the canonical resolution `LeftResolution.ofGradedProjective M` is contractible
in the curved homotopy category. -/
theorem isZero_homotopy_ofGradedProjective_term (M : CurvedDGRightModuleCat.{u, u, u} h)
    (n : ℕ) :
    IsZero (DGHomotopyCategory.of R ((ofGradedProjective M).term n)) :=
  (gradedProjectiveCover (canonicalSyzygy M n)).snd.snd.2.2

end Canonical

variable {M : CurvedDGRightModuleCat.{u, u, u} h} (r : LeftResolution M)

/-- On elements, `r.ι n` followed by `r.π n` vanishes. -/
@[simp]
theorem closedHom_π_ι_apply (n : ℕ) (x : r.syzygy (n + 1)) :
    closedHom (r.π n) (closedHom (r.ι n) x) = 0 :=
  closedHom_apply_eq_zero_of_comp_eq_zero (r.ι_comp_π n) x

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

/-- On elements, consecutive horizontal differentials compose to zero. -/
theorem closedHom_diff_diff_apply (n : ℕ) (x : r.term (n + 2)) :
    closedHom (r.diff n) (closedHom (r.diff (n + 1)) x) = 0 :=
  closedHom_apply_eq_zero_of_comp_eq_zero (r.diff_comp_diff n) x

/-- The `n`-th horizontal differential followed by `π_n` vanishes. -/
@[reassoc (attr := simp)]
theorem diff_comp_π (n : ℕ) : r.diff n ≫ r.π n = 0 := by
  simp only [diff_eq, Category.assoc, r.ι_comp_π, Limits.comp_zero]

/-- On elements, `r.diff n` followed by `r.π n` vanishes. -/
theorem closedHom_π_diff_apply (n : ℕ) (x : r.term (n + 1)) :
    closedHom (r.π n) (closedHom (r.diff n) x) = 0 :=
  closedHom_apply_eq_zero_of_comp_eq_zero (r.diff_comp_π n) x

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
theorem closedHom_ι_injective (n : ℕ) : Function.Injective (closedHom (r.ι n)) :=
  (shortExact_iff.1 (r.shortExact n)).1

/-- In a left resolution, `closedHom (r.π n)` is surjective. -/
theorem closedHom_π_surjective (n : ℕ) : Function.Surjective (closedHom (r.π n)) :=
  (shortExact_iff.1 (r.shortExact n)).2.1

/-- The augmentation `P_0 ⟶ M` is surjective on elements. -/
theorem closedHom_aug_surjective : Function.Surjective (closedHom r.aug) :=
  (GradedModuleCat.epi_iff_surjective _).1
    (inferInstance : Epi ((forgetDifferential (h := h)).map r.aug))

/-- In a left resolution, `closedHom (r.ι n)` and `closedHom (r.π n)` are exact. -/
theorem exact_ι_π (n : ℕ) : Function.Exact (closedHom (r.ι n)) (closedHom (r.π n)) :=
  (shortExact_iff.1 (r.shortExact n)).2.2

/-- The augmented sequence `P_1 ⟶ P_0 ⟶ M` is exact at `P_0` in the closed abelian category. -/
theorem exact_diff_aug : (ShortComplex.mk (r.diff 0) r.aug r.diff_comp_aug).Exact :=
  (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    ({ τ₁ := r.π 1
       τ₂ := 𝟙 _
       τ₃ := r.syzygyZeroIso.inv
       comm₁₂ := by simp [diff_eq]
       comm₂₃ := by simp [aug_eq] } :
      ShortComplex.mk (r.diff 0) r.aug r.diff_comp_aug ⟶
        ShortComplex.mk (r.ι 0) (r.π 0) (r.ι_comp_π 0))).mpr (r.shortExact 0).exact

/-- Consecutive horizontal differentials `P_{n+2} ⟶ P_{n+1} ⟶ P_n` are exact in the closed
abelian category. -/
theorem exact_diff (n : ℕ) :
    (ShortComplex.mk (r.diff (n + 1)) (r.diff n) (r.diff_comp_diff n)).Exact := by
  have hzero : r.ι (n + 1) ≫ r.diff n = 0 := by
    rw [diff_eq, ← Category.assoc, r.ι_comp_π, Limits.zero_comp]
  have h1 : (ShortComplex.mk (r.ι (n + 1)) (r.diff n) hzero).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      ({ τ₁ := 𝟙 _
         τ₂ := 𝟙 _
         τ₃ := r.ι n
         comm₁₂ := by simp
         comm₂₃ := by simp [diff_eq] } :
        ShortComplex.mk (r.ι (n + 1)) (r.π (n + 1)) (r.ι_comp_π (n + 1)) ⟶
          ShortComplex.mk (r.ι (n + 1)) (r.diff n) hzero)).mp (r.shortExact (n + 1)).exact
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    ({ τ₁ := r.π (n + 2)
       τ₂ := 𝟙 _
       τ₃ := 𝟙 _
       comm₁₂ := by simp [diff_eq]
       comm₂₃ := by simp } :
      ShortComplex.mk (r.diff (n + 1)) (r.diff n) (r.diff_comp_diff n) ⟶
        ShortComplex.mk (r.ι (n + 1)) (r.diff n) hzero)).mpr h1

end LeftResolution

end TauCeti.CurvedDGRightModuleCat
