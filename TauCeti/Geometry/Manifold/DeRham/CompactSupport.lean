/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# Compactly supported de Rham cohomology

A smooth real-valued form is compactly supported when its topological support is compact. These
forms make up a submodule of all smooth forms, and the exterior derivative preserves it because
it does not enlarge supports. The compactly supported de Rham complex is the resulting cochain
complex, and its cohomology `H^•_c` is Mathlib's categorical homology of that complex.

As for ordinary de Rham cohomology, a concrete linear class map is defined on compactly supported
closed forms. It is surjective, and a class vanishes exactly when its representative is the
exterior derivative of a compactly supported form, or is zero in degree zero. A compactly
supported form can be exact without being the derivative of a compactly supported form (a bump
one-form `g dx` on `ℝ` with nonzero integral), which is why these exact forms are a separate
submodule; they are contained in the ordinary exact forms. On a compact manifold every smooth
form is compactly supported.

Compactly supported cohomology is the natural domain of integration of top-degree forms and the
second argument of the Poincaré pairing.

## Main definitions

* `TauCeti.compactlySupportedForms`: smooth forms with compact support.
* `TauCeti.compactlySupportedForms.mextDerivₗ`: the exterior derivative restricted to them.
* `TauCeti.compactlySupportedDeRhamComplex`: the compactly supported de Rham complex.
* `TauCeti.compactlySupportedDeRhamCohomology`: its cohomology.
* `TauCeti.compactlySupportedDeRhamCohomology.mk`: the class of a compactly supported closed form.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, "Cohomology with Compact
  Support".
* The concrete presentation of the classes follows `TauCeti.deRhamCohomology.mk` and
  `TauCeti.cyclicCohomology.mk`, through the elementwise cycle and homology lemmas of
  `TauCeti.Algebra.Homology.ModuleCat.Basic`.
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Forms

variable [IsManifold I 1 M]

variable (M) in
/-- The submodule of smooth real-valued `k`-forms whose topological support is compact. -/
def compactlySupportedForms (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k) where
  carrier := {φ | IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1)}
  add_mem' {φ ψ} hφ hψ :=
    (hφ.union hψ).of_isClosed_subset (_root_.isClosed_tsupport _)
      (_root_.tsupport_add (show M → E [⋀^Fin k]→L[ℝ] ℝ from φ.1) ψ.1)
  zero_mem' := by
    -- The zero section is the zero function into the model fibre, whose support is empty.
    have h : IsCompact (_root_.tsupport (0 : M → E [⋀^Fin k]→L[ℝ] ℝ)) := by simp
    exact h
  smul_mem' c φ hφ :=
    hφ.of_isClosed_subset (_root_.isClosed_tsupport _) (RoughForm.tsupport_smul_subset c φ.1)

/-- A smooth form is compactly supported precisely when its topological support is compact. -/
@[simp]
theorem mem_compactlySupportedForms {k : ℕ} {φ : SmoothForm I M ℝ k} :
    φ ∈ compactlySupportedForms I M k ↔
      IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1) :=
  Iff.rfl

/-- On a compact manifold every smooth form is compactly supported. -/
@[simp]
theorem compactlySupportedForms_eq_top [CompactSpace M] (k : ℕ) :
    compactlySupportedForms I M k = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ (_root_.isClosed_tsupport _).isCompact

end Forms

variable [IsManifold I 2 M]

namespace compactlySupportedForms

/-- The exterior derivative, restricted to compactly supported smooth forms. It is well defined
because the exterior derivative does not enlarge supports. -/
def mextDerivₗ (k : ℕ) :
    compactlySupportedForms I M k →ₗ[ℝ] compactlySupportedForms I M (k + 1) :=
  (TauCeti.mextDerivₗ I k).restrict fun φ hφ ↦ by
    rw [mem_compactlySupportedForms, mextDerivₗ_apply]
    exact RoughForm.isCompact_tsupport_mextDeriv hφ

/-- The restricted exterior derivative has the usual exterior derivative as its underlying
form. -/
@[simp]
theorem coe_mextDerivₗ (k : ℕ) (φ : compactlySupportedForms I M k) :
    ((mextDerivₗ I k φ : SmoothForm I M ℝ (k + 1)) : RoughForm I M ℝ (k + 1)) =
      mextDeriv (φ : SmoothForm I M ℝ k).1 := by
  rw [mextDerivₗ, LinearMap.coe_restrict_apply, mextDerivₗ_apply]

/-- The restricted exterior derivative squares to zero. -/
theorem mextDerivₗ_comp_mextDerivₗ (k : ℕ) :
    (mextDerivₗ I (k + 1)).comp (mextDerivₗ I (M := M) k) = 0 := by
  ext φ : 2
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, ZeroMemClass.coe_zero]
  exact LinearMap.congr_fun (TauCeti.mextDerivₗ_comp_mextDerivₗ I (M := M) (F := ℝ) k) φ.1

end compactlySupportedForms

variable (M) in
/-- The compactly supported de Rham complex: compactly supported smooth real-valued forms with
the exterior derivative. -/
def compactlySupportedDeRhamComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (compactlySupportedForms I M k))
    (fun k ↦ ModuleCat.ofHom (compactlySupportedForms.mextDerivₗ I k))
    (fun k ↦ ModuleCat.hom_ext (compactlySupportedForms.mextDerivₗ_comp_mextDerivₗ I k))

/-- The canonical identification of the degree-`k` object with compactly supported smooth
`k`-forms. This isomorphism makes the form carrier available without unfolding the complex. -/
def compactlySupportedDeRhamComplexXIso (k : ℕ) :
    (compactlySupportedDeRhamComplex I M).X k ≅
      ModuleCat.of ℝ (compactlySupportedForms I M k) :=
  Iso.refl _

/-- Under the canonical identifications of the objects, the differential of the compactly
supported de Rham complex is the restricted exterior derivative. -/
@[reassoc, elementwise]
theorem compactlySupportedDeRhamComplex_d (k : ℕ) :
    (compactlySupportedDeRhamComplex I M).d k (k + 1) ≫
        (compactlySupportedDeRhamComplexXIso I (M := M) (k + 1)).hom =
      (compactlySupportedDeRhamComplexXIso I (M := M) k).hom ≫
        ModuleCat.ofHom (compactlySupportedForms.mextDerivₗ I k) := by
  simp [compactlySupportedDeRhamComplex, compactlySupportedDeRhamComplexXIso]

variable (M) in
/-- Compactly supported closed forms: the cycles of the compactly supported de Rham complex. -/
def compactlySupportedClosedForms (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k) :=
  compactlySupportedForms I M k ⊓ closedForms I M k

/-- A smooth form is a compactly supported closed form precisely when its support is compact and
its exterior derivative vanishes. -/
@[simp]
theorem mem_compactlySupportedClosedForms {k : ℕ} {φ : SmoothForm I M ℝ k} :
    φ ∈ compactlySupportedClosedForms I M k ↔
      IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1) ∧ mextDeriv φ.1 = 0 := by
  simp [compactlySupportedClosedForms]

/-- Compactly supported closed forms are compactly supported. -/
theorem compactlySupportedClosedForms_le_compactlySupportedForms (k : ℕ) :
    compactlySupportedClosedForms I M k ≤ compactlySupportedForms I M k :=
  inf_le_left

/-- Compactly supported closed forms are closed. -/
theorem compactlySupportedClosedForms_le_closedForms (k : ℕ) :
    compactlySupportedClosedForms I M k ≤ closedForms I M k :=
  inf_le_right

variable (M) in
/-- The boundaries of the compactly supported de Rham complex: zero in degree zero, and in
positive degree the exterior derivatives of compactly supported forms. -/
def compactlySupportedExactForms : (k : ℕ) → Submodule ℝ (SmoothForm I M ℝ k)
  | 0 => ⊥
  | k + 1 => (LinearMap.range (compactlySupportedForms.mextDerivₗ I (M := M) k)).map
      (compactlySupportedForms I M (k + 1)).subtype

/-- There are no nonzero compactly supported exact forms in degree zero. -/
@[simp]
theorem compactlySupportedExactForms_zero : compactlySupportedExactForms I M 0 = ⊥ := (rfl)

/-- In positive degree, a smooth form is a compactly supported exact form precisely when it is
the exterior derivative of a compactly supported smooth form. -/
@[simp]
theorem mem_compactlySupportedExactForms_succ {k : ℕ} {φ : SmoothForm I M ℝ (k + 1)} :
    φ ∈ compactlySupportedExactForms I M (k + 1) ↔
      ∃ ψ : SmoothForm I M ℝ k, ψ ∈ compactlySupportedForms I M k ∧ mextDeriv ψ.1 = φ.1 := by
  simp only [compactlySupportedExactForms, Submodule.mem_map, LinearMap.mem_range,
    Submodule.coe_subtype]
  constructor
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩
    exact ⟨ψ, ψ.2, (compactlySupportedForms.coe_mextDerivₗ I k ψ).symm⟩
  · rintro ⟨ψ, hψ, hφ⟩
    exact ⟨_, ⟨⟨ψ, hψ⟩, rfl⟩,
      Subtype.ext ((compactlySupportedForms.coe_mextDerivₗ I k ⟨ψ, hψ⟩).trans hφ)⟩

/-- A compactly supported exact form is compactly supported and closed. -/
theorem compactlySupportedExactForms_le_compactlySupportedClosedForms (k : ℕ) :
    compactlySupportedExactForms I M k ≤ compactlySupportedClosedForms I M k := by
  cases k with
  | zero => simp
  | succ k =>
    rintro φ hφ
    obtain ⟨ψ, hψ, hφ⟩ := (mem_compactlySupportedExactForms_succ I).mp hφ
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_compactlySupportedForms, ← hφ]
      exact RoughForm.isCompact_tsupport_mextDeriv hψ
    · rw [mem_closedForms, ← hφ]
      exact SmoothForm.mextDeriv_mextDeriv ψ

/-- A compactly supported exact form is exact. -/
theorem compactlySupportedExactForms_le_exactForms (k : ℕ) :
    compactlySupportedExactForms I M k ≤ exactForms I M k := by
  cases k with
  | zero => simp
  | succ k =>
    rintro φ hφ
    obtain ⟨ψ, -, hφ⟩ := (mem_compactlySupportedExactForms_succ I).mp hφ
    rw [exactForms_succ]
    exact ⟨ψ, Subtype.ext ((mextDerivₗ_apply I k ψ).trans hφ)⟩

variable (M) in
/-- Compactly supported de Rham cohomology `H^•_c` is the categorical homology of the compactly
supported de Rham complex. -/
abbrev compactlySupportedDeRhamCohomology (k : ℕ) : Type _ :=
  (compactlySupportedDeRhamComplex I M).homology k

/-- A compactly supported closed form, viewed as a cycle of the compactly supported de Rham
complex. -/
private def toCycles (k : ℕ) :
    ModuleCat.of ℝ (compactlySupportedClosedForms I M k) ⟶
      (compactlySupportedDeRhamComplex I M).cycles k :=
  (compactlySupportedDeRhamComplex I M).liftCycles
    (ModuleCat.ofHom
        (Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I k)) ≫
      (compactlySupportedDeRhamComplexXIso I k).inv)
    (k + 1) (by simp) (by
      rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (k + 1)).hom, Category.assoc,
        Category.assoc, compactlySupportedDeRhamComplex_d, Iso.inv_hom_id_assoc,
        Limits.zero_comp]
      refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ Subtype.ext (Subtype.ext ?_))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        ModuleCat.hom_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero,
        compactlySupportedForms.coe_mextDerivₗ]
      exact ((mem_compactlySupportedClosedForms I).mp φ.2).2)

private theorem iCycles_toCycles (k : ℕ) (φ : compactlySupportedClosedForms I M k) :
    (compactlySupportedDeRhamComplex I M).iCycles k (toCycles I k φ) =
      (compactlySupportedDeRhamComplexXIso I k).inv
        (Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I k) φ) := by
  rw [toCycles, ← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]
  -- The lifted morphism is the inclusion followed by the identification of the degree-`k` object.
  rfl

/-- The cycle of a compactly supported closed form has zero class exactly when the form is the
image of the incoming differential, `m` being the degree preceding `k`. -/
private theorem homologyπ_toCycles_eq_zero_iff {k m : ℕ} (hm : (ComplexShape.up ℕ).prev k = m)
    (φ : compactlySupportedClosedForms I M k) :
    (compactlySupportedDeRhamComplex I M).homologyπ k (toCycles I k φ) = 0 ↔
      ∃ y, (compactlySupportedDeRhamComplex I M).d m k y =
        (compactlySupportedDeRhamComplexXIso I k).inv (Submodule.inclusion
          (compactlySupportedClosedForms_le_compactlySupportedForms I k) φ) := by
  let K := compactlySupportedDeRhamComplex I M
  rw [K.moduleCat_homologyπ_eq_zero_iff hm]
  refine exists_congr fun y ↦ ?_
  rw [← (K.moduleCat_iCycles_injective k).eq_iff, iCycles_toCycles, ← ModuleCat.comp_apply,
    HomologicalComplex.toCycles_i]

namespace compactlySupportedDeRhamCohomology

/-- The compactly supported cohomology class of a compactly supported closed form. -/
def mk (k : ℕ) :
    compactlySupportedClosedForms I M k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  (toCycles I k ≫ (compactlySupportedDeRhamComplex I M).homologyπ k).hom

private theorem mk_apply (k : ℕ) (φ : compactlySupportedClosedForms I M k) :
    mk I k φ = (compactlySupportedDeRhamComplex I M).homologyπ k (toCycles I k φ) :=
  (rfl)

/-- Every compactly supported cohomology class is represented by a compactly supported closed
form. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I (M := M) k) := by
  intro z
  let K := compactlySupportedDeRhamComplex I M
  obtain ⟨c, rfl⟩ := K.moduleCat_homologyπ_surjective k z
  set φ := (compactlySupportedDeRhamComplexXIso I k).hom (K.iCycles k c)
  have hc : K.d k (k + 1) (K.iCycles k c) = 0 := by
    rw [← ConcreteCategory.comp_apply, K.iCycles_d]
    rfl
  have hd : compactlySupportedForms.mextDerivₗ I k φ = 0 := by
    rw [← compactlySupportedDeRhamComplex_d_apply, hc, map_zero]
  have hφ : (φ : SmoothForm I M ℝ k) ∈ compactlySupportedClosedForms I M k := by
    refine Submodule.mem_inf.mpr ⟨φ.2, ?_⟩
    rw [mem_closedForms]
    simpa using congrArg (fun ψ : compactlySupportedForms I M (k + 1) ↦
      (ψ : SmoothForm I M ℝ (k + 1)).1) hd
  refine ⟨⟨_, hφ⟩, ?_⟩
  rw [mk_apply]
  congr 1
  apply K.moduleCat_iCycles_injective k
  rw [iCycles_toCycles]
  exact (compactlySupportedDeRhamComplexXIso I k).hom_inv_id_apply (K.iCycles k c)

/-- A compactly supported closed form represents zero precisely when it is a compactly
supported exact form. -/
@[simp]
theorem mk_eq_zero_iff (k : ℕ) (φ : compactlySupportedClosedForms I M k) :
    mk I k φ = 0 ↔ (φ : SmoothForm I M ℝ k) ∈ compactlySupportedExactForms I M k := by
  let e := compactlySupportedDeRhamComplexXIso I (M := M)
  cases k with
  | zero =>
    rw [mk_apply, homologyπ_toCycles_eq_zero_iff I CochainComplex.prev_nat_zero,
      (compactlySupportedDeRhamComplex I M).shape 0 0 (by simp),
      compactlySupportedExactForms_zero, Submodule.mem_bot]
    constructor
    · rintro ⟨y, hy⟩
      have h := congrArg (e 0).hom hy
      rw [Iso.inv_hom_id_apply] at h
      simp only [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero] at h
      simpa using (congrArg Subtype.val h).symm
    · intro h
      refine ⟨0, ?_⟩
      simp [(Submodule.coe_eq_zero).mp h]
  | succ k =>
    rw [mk_apply, homologyπ_toCycles_eq_zero_iff I (CochainComplex.prev_nat_succ k),
      mem_compactlySupportedExactForms_succ]
    constructor
    · rintro ⟨y, hy⟩
      have h := congrArg (e (k + 1)).hom hy
      rw [compactlySupportedDeRhamComplex_d_apply, Iso.inv_hom_id_apply] at h
      refine ⟨((e k).hom y : SmoothForm I M ℝ k), ((e k).hom y).2, ?_⟩
      simpa using congrArg (fun ψ : compactlySupportedForms I M (k + 1) ↦
        (ψ : SmoothForm I M ℝ (k + 1)).1) h
    · rintro ⟨ψ, hψ, h⟩
      refine ⟨(e k).inv ⟨ψ, hψ⟩, ?_⟩
      apply (ModuleCat.mono_iff_injective (e (k + 1)).hom).1 inferInstance
      rw [compactlySupportedDeRhamComplex_d_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
      exact Subtype.ext (Subtype.ext (by simpa using h))

/-- Two compactly supported closed forms have the same class precisely when they differ by a
compactly supported exact form. -/
theorem mk_eq_mk_iff (k : ℕ) (φ ψ : compactlySupportedClosedForms I M k) :
    mk I k φ = mk I k ψ ↔
      (φ : SmoothForm I M ℝ k) - ψ ∈ compactlySupportedExactForms I M k := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

/-- The kernel of the class map is exactly the submodule of compactly supported exact forms
inside compactly supported closed forms. -/
theorem ker_mk (k : ℕ) :
    LinearMap.ker (mk I (M := M) k) =
      (compactlySupportedExactForms I M k).comap (compactlySupportedClosedForms I M k).subtype := by
  ext φ
  exact mk_eq_zero_iff I k φ

end compactlySupportedDeRhamCohomology

end TauCeti
