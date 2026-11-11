/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Complexification

/-!
# De Rham cohomology with complex coefficients

Complex-valued smooth forms `SmoothForm I M ℂ k` form a complex vector space, and the exterior
derivative is complex-linear (`TauCeti.SmoothForm.mextDerivₗ_smul`). They therefore form a
nonnegative cochain complex of complex vector spaces, `TauCeti.complexDeRhamComplex`, on the same
form carrier as the real de Rham complex. Its cohomology, `TauCeti.complexDeRhamCohomology`, is
Mathlib's categorical homology in `ModuleCat ℂ`, so it is a complex vector space, and the class map
from closed complex-valued forms is complex-linear. As in the real case, the class map is
surjective and its kernel consists exactly of the exact forms.

The complex de Rham complex is the scalar extension of the real one
(`TauCeti.SmoothForm.complexificationEquiv`). Since `ℂ` is free over `ℝ` with basis `1, i`, scalar
extension commutes with cohomology. This file proves this directly: a complex-valued form is closed,
respectively exact, exactly when its real and imaginary parts are. The result is the
complex-linear equivalence
`TauCeti.complexDeRhamCohomology.complexificationEquiv : ℂ ⊗[ℝ] H^k_dR(M; ℝ) ≃ₗ[ℂ] H^k_dR(M; ℂ)`,
sending `c ⊗ [α]` to `c • [α]`, whose inverse sends the class of `ω` to
`1 ⊗ [Re ω] + i ⊗ [Im ω]`.

## Main declarations

* `TauCeti.complexDeRhamComplex`: the complex of complex-valued smooth forms in `ModuleCat ℂ`.
* `TauCeti.complexDeRhamCohomology`: its cohomology.
* `TauCeti.complexDeRhamCohomology.mk`: the complex-linear class map from closed forms, with
  `mk_surjective` and `mk_eq_zero_iff`.
* `TauCeti.complexDeRhamCohomology.ofReal`: the real-linear map induced by including real forms.
* `TauCeti.complexDeRhamCohomology.complexificationEquiv`:
  `ℂ ⊗[ℝ] H^k_dR(M; ℝ) ≃ₗ[ℂ] H^k_dR(M; ℂ)`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
* Raoul Bott and Loring W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in
  Mathematics 82, Springer, 1982, Chapter I.
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold TensorProduct

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-! ### The complex de Rham complex -/

/-- The exterior derivative of complex-valued smooth forms, as a complex-linear map. -/
def complexMextDerivₗ (k : ℕ) : SmoothForm I M ℂ k →ₗ[ℂ] SmoothForm I M ℂ (k + 1) where
  toFun := mextDerivₗ I k
  map_add' := map_add _
  map_smul' := SmoothForm.mextDerivₗ_smul

/-- The complex-linear exterior derivative is the exterior derivative. -/
@[simp]
theorem complexMextDerivₗ_apply (k : ℕ) (φ : SmoothForm I M ℂ k) :
    complexMextDerivₗ I k φ = mextDerivₗ I k φ :=
  (rfl)

/-- The complex-linear exterior derivative squares to zero. -/
theorem complexMextDerivₗ_comp_complexMextDerivₗ (k : ℕ) :
    complexMextDerivₗ I (M := M) (k + 1) ∘ₗ complexMextDerivₗ I k = 0 :=
  LinearMap.ext fun φ ↦ LinearMap.congr_fun (mextDerivₗ_comp_mextDerivₗ I (F := ℂ) k) φ

variable (M) in
/-- The nonnegative cochain complex of complex-valued smooth forms, a complex of complex vector
spaces. -/
def complexDeRhamComplex : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℂ (SmoothForm I M ℂ k))
    (fun k ↦ ModuleCat.ofHom (complexMextDerivₗ I k))
    (fun k ↦ ModuleCat.hom_ext (complexMextDerivₗ_comp_complexMextDerivₗ I k))

/-- The canonical identification of the degree-`k` object with complex-valued smooth `k`-forms.
This isomorphism makes the form carrier available without unfolding the complex. -/
def complexDeRhamComplexXIso (k : ℕ) :
    (complexDeRhamComplex I M).X k ≅ ModuleCat.of ℂ (SmoothForm I M ℂ k) :=
  Iso.refl _

/-- Under the canonical identifications of the objects, the differential is the exterior
derivative. -/
@[reassoc]
theorem complexDeRhamComplex_d (k : ℕ) :
    (complexDeRhamComplex I M).d k (k + 1) ≫ (complexDeRhamComplexXIso I (M := M) (k + 1)).hom =
      (complexDeRhamComplexXIso I (M := M) k).hom ≫ ModuleCat.ofHom (complexMextDerivₗ I k) := by
  dsimp +instances [complexDeRhamComplexXIso, complexDeRhamComplex]
  simp

/-- The differential of the complex de Rham complex, evaluated on an element. -/
theorem complexDeRhamComplex_d_apply (k : ℕ) (x : (complexDeRhamComplex I M).X k) :
    (complexDeRhamComplex I M).d k (k + 1) x =
      (complexDeRhamComplexXIso I (k + 1)).inv
        (mextDerivₗ I k ((complexDeRhamComplexXIso I k).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (complexDeRhamComplex_d I (M := M) k), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ConcreteCategory.hom_ofHom, complexMextDerivₗ_apply]

/-! ### Closed and exact complex-valued forms -/

variable (M) in
/-- The complex subspace of complex-valued smooth forms whose exterior derivative vanishes. -/
def complexClosedForms (k : ℕ) : Submodule ℂ (SmoothForm I M ℂ k) :=
  LinearMap.ker (complexMextDerivₗ I k)

/-- A complex-valued smooth form is closed precisely when its exterior derivative vanishes. -/
@[simp]
theorem mem_complexClosedForms {k : ℕ} (φ : SmoothForm I M ℂ k) :
    φ ∈ complexClosedForms I M k ↔ mextDerivₗ I k φ = 0 :=
  LinearMap.mem_ker

variable (M) in
/-- Exact complex-valued forms are exterior derivatives of complex-valued smooth forms in positive
degree, and zero in degree zero. -/
def complexExactForms : (k : ℕ) → Submodule ℂ (SmoothForm I M ℂ k)
  | 0 => ⊥
  | k + 1 => LinearMap.range (complexMextDerivₗ I k)

/-- There are no nonzero exact complex-valued forms in degree zero. -/
@[simp]
theorem complexExactForms_zero : complexExactForms I M 0 = ⊥ := (rfl)

/-- In positive degree, exact complex-valued forms are the range of the exterior derivative. -/
@[simp]
theorem complexExactForms_succ (k : ℕ) :
    complexExactForms I M (k + 1) = LinearMap.range (complexMextDerivₗ I k) := (rfl)

/-- An exact complex-valued smooth form is closed. -/
theorem complexExactForms_le_complexClosedForms (k : ℕ) :
    complexExactForms I M k ≤ complexClosedForms I M k := by
  cases k with
  | zero => simp
  | succ k =>
    exact LinearMap.range_le_ker_iff.mpr (complexMextDerivₗ_comp_complexMextDerivₗ I k)

/-- A complex-valued smooth form is closed exactly when its real and imaginary parts are closed. -/
theorem mem_complexClosedForms_iff_realPart_imaginaryPart {k : ℕ} (φ : SmoothForm I M ℂ k) :
    φ ∈ complexClosedForms I M k ↔
      SmoothForm.mapCoeff Complex.reCLM φ ∈ closedForms I M k ∧
        SmoothForm.mapCoeff Complex.imCLM φ ∈ closedForms I M k := by
  simp only [mem_complexClosedForms, mem_closedForms_iff_mextDerivₗ_eq_zero]
  exact SmoothForm.mextDerivₗ_eq_zero_iff_realPart_imaginaryPart φ

/-- A complex-valued smooth form is exact exactly when its real and imaginary parts are exact. -/
theorem mem_complexExactForms_iff_realPart_imaginaryPart {k : ℕ} (φ : SmoothForm I M ℂ k) :
    φ ∈ complexExactForms I M k ↔
      SmoothForm.mapCoeff Complex.reCLM φ ∈ exactForms I M k ∧
        SmoothForm.mapCoeff Complex.imCLM φ ∈ exactForms I M k := by
  cases k with
  | zero =>
    simp only [complexExactForms_zero, exactForms_zero, Submodule.mem_bot]
    refine ⟨fun h ↦ by simp [h], fun ⟨hre, him⟩ ↦ ?_⟩
    rw [← SmoothForm.ofReal_realPart_add_I_smul_ofReal_imaginaryPart φ, hre, him]
    simp
  | succ k =>
    simp only [complexExactForms_succ, exactForms_succ, LinearMap.mem_range,
      complexMextDerivₗ_apply]
    exact SmoothForm.exists_mextDerivₗ_eq_iff_realPart_imaginaryPart φ

/-- The complex-valued form of a closed real form is closed. -/
theorem mapCoeff_ofRealCLM_mem_complexClosedForms {k : ℕ} {α : SmoothForm I M ℝ k}
    (hα : α ∈ closedForms I M k) :
    SmoothForm.mapCoeff Complex.ofRealCLM α ∈ complexClosedForms I M k := by
  rw [mem_complexClosedForms, SmoothForm.mextDerivₗ_mapCoeff,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I α).mp hα, map_zero]

/-- The complex-valued form of an exact real form is exact. -/
theorem mapCoeff_ofRealCLM_mem_complexExactForms {k : ℕ} {α : SmoothForm I M ℝ k}
    (hα : α ∈ exactForms I M k) :
    SmoothForm.mapCoeff Complex.ofRealCLM α ∈ complexExactForms I M k := by
  cases k with
  | zero =>
    rw [exactForms_zero, Submodule.mem_bot] at hα
    simp [hα]
  | succ k =>
    rw [exactForms_succ, LinearMap.mem_range] at hα
    obtain ⟨ψ, rfl⟩ := hα
    exact ⟨SmoothForm.mapCoeff Complex.ofRealCLM ψ, by simp⟩

namespace complexClosedForms

/-- The real part of a closed complex-valued form, a closed real form. -/
def re {k : ℕ} (φ : complexClosedForms I M k) : closedForms I M k :=
  ⟨SmoothForm.mapCoeff Complex.reCLM φ.1,
    ((mem_complexClosedForms_iff_realPart_imaginaryPart I φ.1).mp φ.2).1⟩

/-- The imaginary part of a closed complex-valued form, a closed real form. -/
def im {k : ℕ} (φ : complexClosedForms I M k) : closedForms I M k :=
  ⟨SmoothForm.mapCoeff Complex.imCLM φ.1,
    ((mem_complexClosedForms_iff_realPart_imaginaryPart I φ.1).mp φ.2).2⟩

/-- The underlying form of the real part of a closed complex-valued form. -/
@[simp]
theorem coe_re {k : ℕ} (φ : complexClosedForms I M k) :
    (re I φ).1 = SmoothForm.mapCoeff Complex.reCLM φ.1 :=
  (rfl)

/-- The underlying form of the imaginary part of a closed complex-valued form. -/
@[simp]
theorem coe_im {k : ℕ} (φ : complexClosedForms I M k) :
    (im I φ).1 = SmoothForm.mapCoeff Complex.imCLM φ.1 :=
  (rfl)

end complexClosedForms

namespace closedForms

/-- A closed real form, viewed as a closed complex-valued form. -/
def ofReal {k : ℕ} (α : closedForms I M k) : complexClosedForms I M k :=
  ⟨SmoothForm.mapCoeff Complex.ofRealCLM α.1, mapCoeff_ofRealCLM_mem_complexClosedForms I α.2⟩

/-- The underlying form of a closed real form viewed with complex coefficients. -/
@[simp]
theorem coe_ofReal {k : ℕ} (α : closedForms I M k) :
    (ofReal I α).1 = SmoothForm.mapCoeff Complex.ofRealCLM α.1 :=
  (rfl)

/-- Viewing closed real forms as complex-valued forms is additive. -/
@[simp]
theorem ofReal_add {k : ℕ} (α β : closedForms I M k) :
    ofReal I (α + β) = ofReal I α + ofReal I β :=
  Subtype.ext (map_add _ α.1 β.1)

/-- Viewing closed real forms as complex-valued forms turns real scalars into complex ones. -/
@[simp]
theorem ofReal_smul {k : ℕ} (r : ℝ) (α : closedForms I M k) :
    ofReal I (r • α) = (r : ℂ) • ofReal I α := by
  apply Subtype.ext
  rw [coe_ofReal, Submodule.coe_smul, map_smul, Submodule.coe_smul, coe_ofReal,
    ← Complex.coe_algebraMap, algebraMap_smul]

end closedForms

/-- A closed complex-valued form is the sum of its real part and `i` times its imaginary part. -/
@[simp]
theorem complexClosedForms.ofReal_re_add_I_smul_ofReal_im {k : ℕ} (φ : complexClosedForms I M k) :
    closedForms.ofReal I (complexClosedForms.re I φ) +
      Complex.I • closedForms.ofReal I (complexClosedForms.im I φ) = φ :=
  Subtype.ext (SmoothForm.ofReal_realPart_add_I_smul_ofReal_imaginaryPart φ.1)

/-! ### Complex de Rham cohomology -/

variable (M) in
/-- De Rham cohomology with complex coefficients is the categorical homology of the complex de
Rham complex. It is a complex vector space. -/
abbrev complexDeRhamCohomology (k : ℕ) : Type _ :=
  (complexDeRhamComplex I M).homology k

/-- A complex-valued form is closed exactly when the differential of the complex de Rham complex
kills it. -/
private theorem mem_complexClosedForms_iff_d_eq_zero (k : ℕ) (φ : SmoothForm I M ℂ k) :
    φ ∈ complexClosedForms I M k ↔
      (complexDeRhamComplex I M).d k (k + 1) ((complexDeRhamComplexXIso I k).inv φ) = 0 := by
  rw [(complexDeRhamComplex I M).moduleCat_d_inv_eq_zero_iff (complexMextDerivₗ I)
    (complexDeRhamComplex_d I)]
  exact LinearMap.mem_ker

/-- A complex-valued form is exact exactly when it is hit by the incoming differential of the
complex de Rham complex. -/
private theorem mem_complexExactForms_iff_exists_d_eq (k : ℕ) (φ : SmoothForm I M ℂ k) :
    φ ∈ complexExactForms I M k ↔
      ∃ y : (complexDeRhamComplex I M).X ((ComplexShape.up ℕ).prev k),
        (complexDeRhamComplex I M).d ((ComplexShape.up ℕ).prev k) k y =
          (complexDeRhamComplexXIso I k).inv φ :=
  (complexDeRhamComplex I M).moduleCat_mem_iff_exists_d_eq_inv (complexExactForms I M)
    (complexMextDerivₗ I) (complexDeRhamComplex_d I) (complexExactForms_zero I)
    (complexExactForms_succ I) k φ

namespace complexDeRhamCohomology

/-- The cohomology class of a closed complex-valued form, the homology class of the corresponding
cycle of the complex de Rham complex. This map is complex-linear. -/
def mk (k : ℕ) : complexClosedForms I M k →ₗ[ℂ] complexDeRhamCohomology I M k :=
  (complexDeRhamComplex I M).moduleCatCohomologyClassOfIso (fun k ↦ SmoothForm I M ℂ k)
    (complexClosedForms I M) (complexDeRhamComplexXIso I)
    (mem_complexClosedForms_iff_d_eq_zero I) k

/-- Every complex de Rham cohomology class is represented by a closed complex-valued form. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I (M := M) k) :=
  (complexDeRhamComplex I M).moduleCatCohomologyClassOfIso_surjective
    (fun k ↦ SmoothForm I M ℂ k) (complexClosedForms I M) (complexDeRhamComplexXIso I)
    (mem_complexClosedForms_iff_d_eq_zero I) k

/-- A closed complex-valued form represents zero precisely when it is exact. -/
@[simp]
theorem mk_eq_zero_iff (k : ℕ) (φ : complexClosedForms I M k) :
    mk I k φ = 0 ↔ φ.1 ∈ complexExactForms I M k :=
  (complexDeRhamComplex I M).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun k ↦ SmoothForm I M ℂ k) (complexClosedForms I M) (complexExactForms I M)
    (complexDeRhamComplexXIso I) (mem_complexClosedForms_iff_d_eq_zero I)
    (mem_complexExactForms_iff_exists_d_eq I) k φ

/-- The kernel of the class map is exactly the subspace of exact forms inside closed forms. -/
theorem ker_mk (k : ℕ) :
    LinearMap.ker (mk I (M := M) k) =
      (complexExactForms I M k).comap (complexClosedForms I M k).subtype := by
  ext φ
  exact mk_eq_zero_iff I k φ

/-! ### Comparison with real de Rham cohomology -/

/-- The class of a closed real form viewed with complex coefficients, as a real-linear map. -/
private def ofRealClass (k : ℕ) : closedForms I M k →ₗ[ℝ] complexDeRhamCohomology I M k where
  toFun α := mk I k (closedForms.ofReal I α)
  map_add' α β := by rw [closedForms.ofReal_add, map_add]
  map_smul' r α := by
    rw [closedForms.ofReal_smul, map_smul, RingHom.id_apply, ← Complex.coe_algebraMap,
      algebraMap_smul]

/-- Exact real forms lie in the kernel of `ofRealClass`. -/
private theorem ker_mk_le_ker_ofRealClass (k : ℕ) :
    LinearMap.ker (deRhamCohomology.mk I (M := M) k) ≤ LinearMap.ker (ofRealClass I k) := by
  intro α hα
  rw [LinearMap.mem_ker, deRhamCohomology.mk_eq_zero_iff] at hα
  rw [LinearMap.mem_ker, ofRealClass, LinearMap.coe_mk, AddHom.coe_mk, mk_eq_zero_iff,
    closedForms.coe_ofReal]
  exact mapCoeff_ofRealCLM_mem_complexExactForms I hα

/-- The real-linear map from real to complex de Rham cohomology induced by viewing real forms as
complex-valued forms. -/
def ofReal (k : ℕ) : deRhamCohomology I M k →ₗ[ℝ] complexDeRhamCohomology I M k :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M k)
    (M₂ := deRhamCohomology I M k) (M₃ := complexDeRhamCohomology I M k)
    (f := deRhamCohomology.mk I k) (deRhamCohomology.mk_surjective I k)
    ⟨ofRealClass I k, ker_mk_le_ker_ofRealClass I k⟩

/-- The induced map sends the class of a closed real form to the class of the same form with
complex coefficients. -/
@[simp]
theorem ofReal_mk (k : ℕ) (α : closedForms I M k) :
    ofReal I k (deRhamCohomology.mk I k α) = mk I k (closedForms.ofReal I α) := by
  rw [ofReal, LinearMap.equivOfSurjective_apply]
  rfl

/-- The complex-linear extension of `ofReal` sends `1 ⊗ [α] + i ⊗ [β]` to `[α + i β]`. -/
private theorem liftBaseChange_ofReal_one_tmul_mk_add_I_tmul_mk (k : ℕ)
    (α β : closedForms I M k) :
    (ofReal I k).liftBaseChange ℂ
        (1 ⊗ₜ deRhamCohomology.mk I k α + Complex.I ⊗ₜ deRhamCohomology.mk I k β) =
      mk I k (closedForms.ofReal I α + Complex.I • closedForms.ofReal I β) := by
  simp

/-- The complex-linear extension of `ofReal` sends `1 ⊗ [Re φ] + i ⊗ [Im φ]` to `[φ]`. -/
private theorem liftBaseChange_ofReal_mk_re_add_I_tmul_mk_im (k : ℕ)
    (φ : complexClosedForms I M k) :
    (ofReal I k).liftBaseChange ℂ
        (1 ⊗ₜ deRhamCohomology.mk I k (complexClosedForms.re I φ) +
          Complex.I ⊗ₜ deRhamCohomology.mk I k (complexClosedForms.im I φ)) = mk I k φ := by
  rw [liftBaseChange_ofReal_one_tmul_mk_add_I_tmul_mk,
    complexClosedForms.ofReal_re_add_I_smul_ofReal_im]

/-- The real-linear map `ofReal`, extended complex-linearly to `ℂ ⊗[ℝ] H^k_dR(M; ℝ)`, is
bijective. -/
private theorem liftBaseChange_ofReal_bijective (k : ℕ) :
    Function.Bijective ((ofReal I (M := M) k).liftBaseChange ℂ) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    obtain ⟨a, b, rfl⟩ := exists_one_tmul_add_I_tmul u
    obtain ⟨α, rfl⟩ := deRhamCohomology.mk_surjective I k a
    obtain ⟨β, rfl⟩ := deRhamCohomology.mk_surjective I k b
    rw [LinearMap.mem_ker, liftBaseChange_ofReal_one_tmul_mk_add_I_tmul_mk, mk_eq_zero_iff,
      mem_complexExactForms_iff_realPart_imaginaryPart] at hu
    simp only [Submodule.coe_add, Submodule.coe_smul, closedForms.coe_ofReal,
      SmoothForm.realPart_ofReal_add_I_smul_ofReal,
      SmoothForm.imaginaryPart_ofReal_add_I_smul_ofReal] at hu
    rw [Submodule.mem_bot, (deRhamCohomology.mk_eq_zero_iff I k α).mpr hu.1,
      (deRhamCohomology.mk_eq_zero_iff I k β).mpr hu.2, TensorProduct.tmul_zero,
      TensorProduct.tmul_zero, add_zero]
  · intro c
    obtain ⟨φ, rfl⟩ := mk_surjective I k c
    exact ⟨_, liftBaseChange_ofReal_mk_re_add_I_tmul_mk_im I k φ⟩

/-- **Complex de Rham cohomology is the complexification of real de Rham cohomology.** The
complex-linear equivalence `ℂ ⊗[ℝ] H^k_dR(M; ℝ) ≃ₗ[ℂ] H^k_dR(M; ℂ)` sends `c ⊗ [α]` to `c • [α]`. -/
def complexificationEquiv (k : ℕ) :
    ℂ ⊗[ℝ] deRhamCohomology I M k ≃ₗ[ℂ] complexDeRhamCohomology I M k :=
  LinearEquiv.ofBijective ((ofReal I k).liftBaseChange ℂ) (liftBaseChange_ofReal_bijective I k)

/-- The complexification equivalence on pure tensors. -/
@[simp]
theorem complexificationEquiv_tmul (k : ℕ) (c : ℂ) (a : deRhamCohomology I M k) :
    complexificationEquiv I k (c ⊗ₜ a) = c • ofReal I k a :=
  (rfl)

/-- The inverse complexification equivalence sends the class of a closed complex-valued form to
the classes of its real and imaginary parts. -/
@[simp]
theorem complexificationEquiv_symm_mk (k : ℕ) (φ : complexClosedForms I M k) :
    (complexificationEquiv I k).symm (mk I k φ) =
      1 ⊗ₜ deRhamCohomology.mk I k (complexClosedForms.re I φ) +
        Complex.I ⊗ₜ deRhamCohomology.mk I k (complexClosedForms.im I φ) := by
  rw [LinearEquiv.symm_apply_eq]
  exact (liftBaseChange_ofReal_mk_re_add_I_tmul_mk_im I k φ).symm

end complexDeRhamCohomology

end TauCeti
