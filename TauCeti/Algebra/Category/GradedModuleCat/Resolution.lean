/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Abelian.Projective.Resolution
public import TauCeti.Algebra.Homology.ChainComplex.Exact
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Homology.Ext.ProjectiveResolution
public import TauCeti.Algebra.Module.GradedModule.Resolution

/-!
# Concrete graded resolutions as categorical projective resolutions

A `TauCeti.GradedProjectiveResolution` records projective modules, homogeneous differentials,
and an exact augmentation as linear maps. This file turns that data into a
`CategoryTheory.ProjectiveResolution` in `TauCeti.GradedModuleCat`. Its terms retain their
internal gradings, and its differentials and augmentation are the original maps.

The resulting resolution can be used directly with Mathlib's comparison maps, uniqueness up to
chain homotopy, and computation of Ext from projective resolutions. No enough-projectives
hypothesis is needed to bundle a given resolution. The construction imposes neither linearity,
minimality, finite generation, nor boundedness.

Forgetting the grading turns the same data into a projective resolution of the underlying
`A`-module. Hence a graded resolution whose terms vanish from homological degree `n` on bounds the
ungraded projective dimension (`TauCeti.GradedProjectiveResolution.hasProjectiveDimensionLT`).
Concrete resolutions also support categorical shift (`TauCeti.GradedProjectiveResolution.shiftObj`)
and length-one construction from a projective short exact sequence
(`TauCeti.GradedProjectiveResolution.ofShortExact`).

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 2.2 and 2.4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v uk uA

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {M : GradedModuleCat.{v} 𝒜}

namespace GradedProjectiveResolution

variable (r : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 M.grading)

/-- A term of a concrete graded resolution, with its specified internal grading. -/
abbrev termObj (n : ℕ) : GradedModuleCat.{v} 𝒜 where
  carrier := r.X n
  grading := r.grading n

/-- The differential of a concrete graded resolution as a morphism of graded modules. -/
abbrev differential (n : ℕ) : r.termObj (n + 1) ⟶ r.termObj n :=
  GradedModuleCat.ofHom (r.d n) (r.isHomogeneous_d n)

/-- The augmentation of a concrete graded resolution as a morphism of graded modules. -/
abbrev augmentation : r.termObj 0 ⟶ M :=
  GradedModuleCat.ofHom r.π r.isHomogeneous_π

@[reassoc (attr := simp)]
theorem differential_comp_differential (n : ℕ) :
    r.differential (n + 1) ≫ r.differential n = 0 :=
  GradedModuleCat.hom_ext (r.exact_d_d n).linearMap_comp_eq_zero

@[reassoc (attr := simp)]
theorem differential_zero_comp_augmentation : r.differential 0 ≫ r.augmentation = 0 :=
  GradedModuleCat.hom_ext r.exact_d_π.linearMap_comp_eq_zero

private noncomputable def complex : ChainComplex (GradedModuleCat.{v} 𝒜) ℕ :=
  ChainComplex.of r.termObj r.differential r.differential_comp_differential

private theorem complex_d (n : ℕ) :
    r.complex.d (n + 1) n = r.differential n := by
  simp [complex]

section Decomposition

variable [DirectSum.Decomposition 𝒜]

/-- A concrete graded projective resolution is a categorical projective resolution in the
category of graded modules. The quasi-isomorphism is its original augmentation. -/
noncomputable def toProjectiveResolution : ProjectiveResolution M := by
  exact @ChainComplex.toProjectiveResolution _ _ _ M r.complex r.augmentation
    (by rw [complex_d]; exact r.differential_zero_comp_augmentation)
    (fun n => by
      let := r.projective n
      exact inferInstanceAs (Projective (r.termObj n)))
    ((GradedModuleCat.epi_iff_surjective r.augmentation).mpr r.surjective_π)
    (ChainComplex.of_exact_d_one_zero r.termObj r.differential r.differential_comp_differential
      r.augmentation r.differential_zero_comp_augmentation
      (GradedModuleCat.exact_iff.mpr r.exact_d_π))
    (fun n => ChainComplex.of_exactAt_succ r.termObj r.differential
      r.differential_comp_differential n (GradedModuleCat.exact_iff.mpr (r.exact_d_d n)))

/-- The terms of the categorical resolution are the original graded modules. -/
noncomputable def toProjectiveResolutionXIso (n : ℕ) :
    r.toProjectiveResolution.complex.X n ≅ r.termObj n :=
  Iso.refl _

/-- The categorical differential is the original differential, through the term identifications. -/
@[simp]
theorem toProjectiveResolution_complex_d (n : ℕ) :
    r.toProjectiveResolution.complex.d (n + 1) n =
      (r.toProjectiveResolutionXIso (n + 1)).hom ≫ r.differential n ≫
        (r.toProjectiveResolutionXIso n).inv := by
  -- Expose the identity identifications and their endpoints to the category identity laws.
  change r.complex.d (n + 1) n =
    𝟙 (r.termObj (n + 1)) ≫ r.differential n ≫ 𝟙 (r.termObj n)
  rw [Category.id_comp, Category.comp_id]
  exact r.complex_d n

/-- The categorical augmentation is the original augmentation, through the term identification. -/
@[simp]
theorem toProjectiveResolution_π_f_zero :
    r.toProjectiveResolution.π.f 0 =
      (r.toProjectiveResolutionXIso 0).hom ≫ r.augmentation := by
  -- Reduction identifies the identity isomorphism's endpoints before simp uses category laws.
  simpa [toProjectiveResolutionXIso, toProjectiveResolution,
    ChainComplex.toProjectiveResolution, complex] using
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero (C := r.complex) r.augmentation
      (by rw [complex_d]; exact r.differential_zero_comp_augmentation)

end Decomposition

/-- **A graded resolution with vanishing tail bounds the projective dimension.** If the terms of
a graded projective resolution of `M` vanish from homological degree `n` on, then the underlying
`A`-module of `M` has projective dimension less than `n`. -/
theorem hasProjectiveDimensionLT (n : ℕ) (h : ∀ i, n ≤ i → Subsingleton (r.X i)) :
    HasProjectiveDimensionLT (GradedModuleCat.toModuleCat.obj M) n := by
  -- The underlying modules form a projective resolution in `ModuleCat A`; no grading
  -- decomposition is needed, since exactness is read off from the linear maps.
  let C : ChainComplex (ModuleCat.{v} A) ℕ :=
    ChainComplex.of (fun i ↦ ModuleCat.of A (r.X i)) (fun i ↦ ModuleCat.ofHom (r.d i))
      fun i ↦ ModuleCat.hom_ext (r.exact_d_d i).linearMap_comp_eq_zero
  let π : C ⟶ (ChainComplex.single₀ (ModuleCat.{v} A)).obj (GradedModuleCat.toModuleCat.obj M) :=
    (C.toSingle₀Equiv _).symm
      ⟨ModuleCat.ofHom r.π, ModuleCat.hom_ext r.exact_d_π.linearMap_comp_eq_zero⟩
  have hd (j : ℕ) : C.d (j + 1) j = ModuleCat.ofHom (r.d j) := by simp [C]
  have : QuasiIso π := by
    constructor
    intro i
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
      constructor
      · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
        exact r.exact_d_π
      · exact (ModuleCat.epi_iff_surjective _).mpr r.surjective_π
    | succ i =>
      rw [quasiIsoAt_iff_exactAt'
        (hL := ChainComplex.exactAt_succ_single_obj ..),
        HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
        ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      -- `exactAt_iff'` uses short-complex projections; expose just its two maps.
      change Function.Exact (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom
      rw [hd, hd]
      exact r.exact_d_d i
  let R : ProjectiveResolution (GradedModuleCat.toModuleCat.obj M) :=
    { complex := C
      projective i := by
        have := r.projective i
        exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of A (r.X i))
      π := π
      quasiIso := this }
  refine R.hasProjectiveDimensionLT n fun i hi ↦ ?_
  have := h i hi
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of A (r.X i))

/-- Shift a concrete graded projective resolution of `M` to a graded projective resolution of
`M{d}` (`M.shiftObj d`). Each term `r.termObj n` is shifted to `(r.termObj n){d}`. -/
abbrev shiftObj (d : ℤ) : GradedProjectiveResolution.{uk, uA, v, v} 𝒜 (M.shiftObj d).grading :=
  r.shift (-d)

/-- Shifting a resolution of `M` to `M{d}` shifts each categorical term by `d`. -/
@[simp]
theorem shiftObj_termObj (d : ℤ) (n : ℕ) :
    (r.shiftObj d).termObj n = (r.termObj n).shiftObj d :=
  (rfl)

/-- Shifting a resolution of `M` to `M{d}` preserves minimality. -/
theorem isMinimal_shiftObj_iff (d : ℤ) : (r.shiftObj d).IsMinimal ↔ r.IsMinimal :=
  r.isMinimal_shift_iff (-d)

section ShortExact

/-- The terms of the length-one graded resolution attached to `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0`:
`S.X₂` in degree `0`, `S.X₁` in degree `1`, and the empty graded direct sum in degrees `n ≥ 2`. -/
abbrev shortExactTerm (S : ShortComplex (GradedModuleCat.{v} 𝒜)) :
    ℕ → GradedModuleCat.{v} 𝒜
  | 0 => S.X₂
  | 1 => S.X₁
  | _ + 2 => GradedModuleCat.directSumObj fun _ : Fin 0 => S.X₂

/-- The differentials of `shortExactTerm S`: `S.f` in degree `0` and `0` thereafter. -/
noncomputable abbrev shortExactDifferential (S : ShortComplex (GradedModuleCat.{v} 𝒜)) :
    ∀ n : ℕ, shortExactTerm S (n + 1) ⟶ shortExactTerm S n
  | 0 => S.f
  | _ + 1 => 0

/-- The differentials `shortExactDifferential S` of a short exact sequence are exact. -/
theorem shortExactDifferential_exact {S : ShortComplex (GradedModuleCat.{v} 𝒜)}
    (hS : S.ShortExact) :
    ∀ n : ℕ, Function.Exact (shortExactDifferential S (n + 1)).hom
      (shortExactDifferential S n).hom
  | 0 => by
    have hmono := hS.mono_f
    have hinj := (GradedModuleCat.mono_iff_injective S.f).mp hmono
    rw [LinearMap.exact_iff]
    change LinearMap.ker S.f.hom = LinearMap.range (0 : shortExactTerm S 2 ⟶ S.X₁).hom
    rw [GradedModuleCat.hom_zero, LinearMap.range_zero, LinearMap.ker_eq_bot]
    exact hinj
  | _ + 1 => by
    rw [LinearMap.exact_iff]
    exact Subsingleton.elim _ _

/-- Build a length-one `GradedProjectiveResolution` of `S.X₃` from a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` in `GradedModuleCat 𝒜` whose first two terms are projective over `A`,
padding homological degrees `n ≥ 2` by the empty graded direct sum. -/
noncomputable abbrev ofShortExact {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    GradedProjectiveResolution.{uk, uA, v, v} 𝒜 S.X₃.grading where
  X n := shortExactTerm S n
  grading n := (shortExactTerm S n).grading
  projective
    | 0 => inferInstanceAs (Module.Projective A S.X₂)
    | 1 => inferInstanceAs (Module.Projective A S.X₁)
    | _ + 2 => inferInstance
  d n := (shortExactDifferential S n).hom
  π := S.g.hom
  isHomogeneous_d n := (shortExactDifferential S n).isHomogeneous
  isHomogeneous_π := S.g.isHomogeneous
  surjective_π := have := hS.epi_g; (GradedModuleCat.epi_iff_surjective S.g).mp inferInstance
  exact_d_π := GradedModuleCat.exact_iff.mp hS.exact
  exact_d_d := shortExactDifferential_exact hS

/-- The degree-zero categorical term of `ofShortExact hS` is `S.X₂`. -/
@[simp]
theorem ofShortExact_termObj_zero {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).termObj 0 = S.X₂ :=
  (rfl)

/-- The degree-one categorical term of `ofShortExact hS` is `S.X₁`. -/
@[simp]
theorem ofShortExact_termObj_one {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).termObj 1 = S.X₁ :=
  (rfl)

/-- Every term of `ofShortExact hS` from homological degree `2` onwards is a subsingleton. -/
theorem subsingleton_ofShortExact_X_of_two_le {S : ShortComplex (GradedModuleCat.{v} 𝒜)}
    (hS : S.ShortExact) [Module.Projective A S.X₁] [Module.Projective A S.X₂] {n : ℕ}
    (hn : 2 ≤ n) : Subsingleton ((ofShortExact hS).X n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact inferInstanceAs (Subsingleton (DirectSum (Fin 0) fun _ => S.X₂))

/-- Every term of `ofShortExact hS` is finitely generated over `A` when `S.X₁` and `S.X₂` are. -/
instance finite_ofShortExact_X {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂]
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] :
    ∀ n : ℕ, Module.Finite A ((ofShortExact hS).X n)
  | 0 => inferInstanceAs (Module.Finite A S.X₂)
  | 1 => inferInstanceAs (Module.Finite A S.X₁)
  | n + 2 =>
    have := subsingleton_ofShortExact_X_of_two_le hS (n := n + 2) (by omega)
    have := Finite.of_subsingleton (α := (ofShortExact hS).X (n + 2))
    inferInstance

/-- A length-one resolution built from `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` is minimal iff `S.f` lands in
`A₊ S.X₂`. -/
@[simp]
theorem isMinimal_ofShortExact_iff {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).IsMinimal ↔
      ∀ x : S.X₁, S.f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k S.X₂) := by
  rw [isMinimal_iff]
  refine ⟨fun h x => h 0 x, fun h n => ?_⟩
  rcases n with _ | n
  · exact h
  · intro x
    change (0 : shortExactTerm S (n + 2) ⟶ shortExactTerm S (n + 1)).hom x ∈ _
    rw [GradedModuleCat.hom_zero, LinearMap.zero_apply]
    exact zero_mem _

/-- A length-one resolution built from `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` is linear iff `S.X₂` is
generated in degree `0` and `S.X₁` is generated in degree `1`. -/
@[simp]
theorem isLinear_ofShortExact_iff {S : ShortComplex (GradedModuleCat.{v} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).IsLinear ↔
      S.X₂.grading.IsGeneratedInDegree A 0 ∧ S.X₁.grading.IsGeneratedInDegree A 1 := by
  rw [isLinear_iff]
  refine ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ n => ?_⟩
  rcases n with _ | (_ | n)
  · exact h0
  · exact h1
  · rw [InternalGrading.isGeneratedInDegree_iff]
    intro x
    have := subsingleton_ofShortExact_X_of_two_le hS (n := n + 2) (by omega)
    rw [Subsingleton.elim x 0]
    exact zero_mem _

end ShortExact

end GradedProjectiveResolution

end TauCeti
