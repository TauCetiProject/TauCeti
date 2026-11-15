/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.MulBy.TwoTorsion
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ZeroSection

/-!
# Legendre normal form of a projective Weierstrass model

Let `W` be an elliptic Weierstrass curve over a commutative ring `R`, `P` and `Q` sections of its
projective model `W.projModel ⟶ Spec R` which miss the zero section at every point of `Spec R`,
and `ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf` a global basis of the conormal
sheaf of the zero section. Writing `P = [x₁ : y₁ : 1]`, `Q = [x₂ : y₂ : 1]` and
`ω = u • W.weierstrassDifferential` for a unique unit `u : Rˣ`
(`WeierstrassCurve.weierstrassDifferentialScalar`), the **adapted `x`-coordinate** of `Q` relative
to `(P, ω)` is

`(u⁻¹)² · (x₂ - x₁) : R`

(`WeierstrassCurve.projModelAdaptedXCoord`). It is the value at `Q` of the unique `ω`-adapted
Weierstrass `x`-coordinate normalised by `x(P) = 0` (Katz–Mazur, 2.2.4 and 2.2.9): under any
change of variables `C = (v, r, s, t)` on `W`, `x₂ - x₁` scales by `v²` while `u` scales by `v`,
so `(u⁻¹)² · (x₂ - x₁)` is strictly invariant under pointed base-change squares of projective
Weierstrass models (`WeierstrassCurve.map_projModelAdaptedXCoord_of_isPullback`).

When `P` and `Q` are killed by multiplication by `2` and
`W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1` (that is, `x₂ - x₁ = u²`), `2` is automatically a
unit of `R` and there are a unique `l : R` with `2l(l - 1)` a unit and a unique pointed isomorphism

`projModel (freyCurve 1 (-l)) ≅ projModel W`

over `Spec R` carrying `(0, 0)` to `P`, `(1, 0)` to `Q`, and pulling `ω` back to
`(freyCurve 1 (-l)).weierstrassDifferential` (`WeierstrassCurve.existsUnique_legendreNormalForm` and
`WeierstrassCurve.legendreNormalForm_iso_ext`). Conversely, the existence of such an isomorphism
forces `P` and `Q` to miss the zero section, be killed by `2`, differ at every point of `Spec R`,
and satisfy `W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1`
(`WeierstrassCurve.exists_iso_legendreNormalForm_iff`).

## Main definitions and results

* `WeierstrassCurve.projModelAdaptedXCoord`: the value at `Q` of the `ω`-adapted Weierstrass
  `x`-coordinate normalised by `x(P) = 0`, invariant under pointed base change
  (`WeierstrassCurve.map_projModelAdaptedXCoord_of_isPullback`).
* `WeierstrassCurve.existsUnique_legendreNormalForm`: existence and uniqueness of the Legendre
  parameter `l` for `(W, P, Q, ω)`.
* `WeierstrassCurve.legendreNormalForm_iso_ext`: uniqueness of the Legendre normal-form isomorphism.
* `WeierstrassCurve.exists_iso_legendreNormalForm_iff`: necessity and sufficiency of the conditions
  on `(P, Q, ω)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.4, 2.2.9, and 4.6.2.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

universe u

namespace WeierstrassCurve

noncomputable section

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- The point `(0, 0)` lies on `freyCurve A B`. -/
theorem equation_freyCurve_zero (A B : R) : (TauCeti.freyCurve A B).toAffine.Equation 0 0 :=
  Affine.equation_zero.mpr (TauCeti.freyCurve_a₆ A B)

/-- The point `(1, 0)` lies on `freyCurve 1 B`. -/
theorem equation_freyCurve_one_zero (B : R) : (TauCeti.freyCurve 1 B).toAffine.Equation 1 0 := by
  rw [Affine.equation_iff]
  simp

private theorem eqToHom_projModelVariableChangeIso_hom_spec {W W' : WeierstrassCurve R}
    (C : VariableChange R) (hC : C • W = W') :
    (eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom) ≫
        W.projModelOver = W'.projModelOver ∧
      W'.projModelZero ≫ eqToHom (congrArg projModel hC.symm) ≫
        (W.projModelVariableChangeIso C).hom = W.projModelZero ∧
      ∀ {x y : R} (h : W'.toAffine.Equation x y), W'.projModelAffinePoint h ≫
        eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom =
          W.projModelAffinePoint ((Affine.variableChange_equation W C x y).mpr (hC ▸ h)) := by
  subst hC
  exact ⟨by simp, by simp, fun h ↦ by simp⟩

/-! ### Adapted `x`-coordinate of two affine sections -/

section AdaptedXCoord

variable (W : WeierstrassCurve R)

/-- The affine `x`-coordinate of a section `P : Spec R ⟶ W.projModel` missing `W.projModelZero`. -/
def projModelSectionX {P : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hP₀ : ∀ s, P s ≠ W.projModelZero s) : R :=
  (W.exists_eq_projModelAffinePoint hP hP₀).choose

theorem projModelSectionX_eq_of_eq_projModelAffinePoint {P : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hP₀ : ∀ s, P s ≠ W.projModelZero s)
    {x y : R} (h : W.toAffine.Equation x y) (hP' : P = W.projModelAffinePoint h) :
    W.projModelSectionX hP hP₀ = x := by
  have hchoose := (W.exists_eq_projModelAffinePoint hP hP₀).choose_spec
  rcases hchoose with ⟨y₀, h₀, hP₀_eq⟩
  exact ((W.projModelAffinePoint_inj h₀).mp (hP₀_eq.symm.trans hP')).1

/-- **The `ω`-adapted `x`-coordinate** of a section `Q` relative to an origin section `P` and a
conormal basis `ω` on `W.projModel`: writing `P = [x₁ : y₁ : 1]`, `Q = [x₂ : y₂ : 1]`, and
`ω = u • W.weierstrassDifferential`, it is `(u⁻¹)² · (x₂ - x₁)`. -/
def projModelAdaptedXCoord [W.IsElliptic] {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) : R :=
  (↑(W.weierstrassDifferentialScalar ω)⁻¹ : R) ^ 2 *
    (W.projModelSectionX hQ hQ₀ - W.projModelSectionX hP hP₀)

theorem projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint [W.IsElliptic]
    {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP' : P = W.projModelAffinePoint h₁) (hQ' : Q = W.projModelAffinePoint h₂) :
    W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω =
      (↑(W.weierstrassDifferentialScalar ω)⁻¹ : R) ^ 2 * (x₂ - x₁) := by
  rw [projModelAdaptedXCoord,
    W.projModelSectionX_eq_of_eq_projModelAffinePoint hP hP₀ h₁ hP',
    W.projModelSectionX_eq_of_eq_projModelAffinePoint hQ hQ₀ h₂ hQ']

theorem projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint [W.IsElliptic]
    {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hP' : P = W.projModelAffinePoint h₁) (hQ' : Q = W.projModelAffinePoint h₂) :
    W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1 ↔
      x₂ - x₁ = (W.weierstrassDifferentialScalar ω : R) ^ 2 := by
  rw [W.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP hQ hP₀ hQ₀ ω h₁ h₂ hP' hQ']
  set u := W.weierstrassDifferentialScalar ω
  have hu : (u : R) * (↑u⁻¹ : R) = 1 := u.mul_inv
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · linear_combination (u : R) ^ 2 * h - (x₂ - x₁) * ((u : R) * ↑u⁻¹ + 1) * hu
  · linear_combination (↑u⁻¹ : R) ^ 2 * h + ((u : R) * ↑u⁻¹ + 1) * hu

variable {W} {W' : WeierstrassCurve R'} [W.IsElliptic] [W'.IsElliptic]

private theorem projModelAdaptedXCoord_eq_of_iso {W₁ W₂ : WeierstrassCurve R}
    [W₁.IsElliptic] [W₂.IsElliptic] (e : W₁.projModel ≅ W₂.projModel)
    (he : e.hom ≫ W₂.projModelOver = W₁.projModelOver)
    (h0 : W₁.projModelZero ≫ e.hom = W₂.projModelZero)
    {P₁ Q₁ : Spec (.of R) ⟶ W₁.projModel} {P₂ Q₂ : Spec (.of R) ⟶ W₂.projModel}
    (hP₁ : P₁ ≫ W₁.projModelOver = 𝟙 _) (hQ₁ : Q₁ ≫ W₁.projModelOver = 𝟙 _)
    (hP₁₀ : ∀ s, P₁ s ≠ W₁.projModelZero s) (hQ₁₀ : ∀ s, Q₁ s ≠ W₁.projModelZero s)
    (hP₂ : P₂ ≫ W₂.projModelOver = 𝟙 _) (hQ₂ : Q₂ ≫ W₂.projModelOver = 𝟙 _)
    (hP₂₀ : ∀ s, P₂ s ≠ W₂.projModelZero s) (hQ₂₀ : ∀ s, Q₂ s ≠ W₂.projModelZero s)
    (hPe : P₁ ≫ e.hom = P₂) (hQe : Q₁ ≫ e.hom = Q₂)
    (ω₂ : 𝟙_ (Spec (.of R)).Modules ≅ W₂.projModelZero.conormalSheaf) :
    W₁.projModelAdaptedXCoord hP₁ hQ₁ hP₁₀ hQ₁₀
        (Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
          W₂.projModelZero_projModelOver W₁.projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
          (by rw [h0, Category.id_comp]) ω₂) =
      W₂.projModelAdaptedXCoord hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ := by
  obtain ⟨C, ⟨hCW, heC⟩, -⟩ :=
    existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he h0
  subst hCW
  have he' : e.hom = (W₂.projModelVariableChangeIso C).hom := by
    simpa using heC
  obtain ⟨x₁, y₁, h₁, rfl⟩ := (C • W₂).exists_eq_projModelAffinePoint hP₁ hP₁₀
  obtain ⟨x₂, y₂, h₂, rfl⟩ := (C • W₂).exists_eq_projModelAffinePoint hQ₁ hQ₁₀
  have hP₂_eq : P₂ =
      W₂.projModelAffinePoint ((Affine.variableChange_equation W₂ C x₁ y₁).mpr h₁) := by
    rw [← hPe, he', projModelAffinePoint_projModelVariableChangeIso_hom]
  have hQ₂_eq : Q₂ =
      W₂.projModelAffinePoint ((Affine.variableChange_equation W₂ C x₂ y₂).mpr h₂) := by
    rw [← hQe, he', projModelAffinePoint_projModelVariableChangeIso_hom]
  have hcongr := Scheme.Hom.conormalBasisPullback_congr
    (f₁ := 𝟙 (Spec (.of R))) (g₁ := e.hom)
    W₂.projModelZero_projModelOver (C • W₂).projModelZero_projModelOver rfl he'
    (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
    (by rw [h0, Category.id_comp])
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (by rw [W₂.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]) ω₂
  rw [(C • W₂).projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP₁ hQ₁ hP₁₀ hQ₁₀ _
      h₁ h₂ rfl rfl,
    W₂.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP₂ hQ₂ hP₂₀ hQ₂₀ ω₂ _ _
      hP₂_eq hQ₂_eq,
    hcongr,
    W₂.weierstrassDifferentialScalar_conormalBasisPullback_projModelVariableChangeIso_hom C ω₂]
  set u := W₂.weierstrassDifferentialScalar ω₂
  simp only [mul_inv_rev, inv_inv, Units.val_mul]
  ring

/-- **Invariance of the adapted `x`-coordinate under pointed base change.** Let
`F : projModel W ⟶ projModel W'` form a cartesian square over `Spec φ` (`φ : R' →+* R`), carrying
zero to zero and `(P, Q)` to `(P', Q')`. Then `φ` maps the `ω'`-adapted `x`-coordinate of `(P', Q')`
to the `(F^* ω')`-adapted `x`-coordinate of `(P, Q)`. -/
theorem map_projModelAdaptedXCoord_of_isPullback {φ : R' →+* R}
    {F : W.projModel ⟶ W'.projModel}
    (hF : IsPullback F W.projModelOver W'.projModelOver (Spec.map (CommRingCat.ofHom φ)))
    (h0 : W.projModelZero ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ W'.projModelZero)
    {P Q : Spec (.of R) ⟶ W.projModel} {P' Q' : Spec (.of R') ⟶ W'.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (hP' : P' ≫ W'.projModelOver = 𝟙 _) (hQ' : Q' ≫ W'.projModelOver = 𝟙 _)
    (hP'₀ : ∀ s, P' s ≠ W'.projModelZero s) (hQ'₀ : ∀ s, Q' s ≠ W'.projModelZero s)
    (hPF : P ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ P')
    (hQF : Q ≫ F = Spec.map (CommRingCat.ofHom φ) ≫ Q')
    (ω' : 𝟙_ (Spec (.of R')).Modules ≅ W'.projModelZero.conormalSheaf) :
    φ (W'.projModelAdaptedXCoord hP' hQ' hP'₀ hQ'₀ ω') =
      W.projModelAdaptedXCoord hP hQ hP₀ hQ₀
        (Scheme.Hom.conormalBasisPullback W'.projModelZero_projModelOver
          W.projModelZero_projModelOver hF h0 ω') := by
  let _ : (W'.map φ).IsElliptic := inferInstance
  have hB := W'.isPullback_projModelBaseChange φ
  let e := hF.isoIsPullback _ _ hB
  have he : e.hom ≫ (W'.map φ).projModelOver = W.projModelOver := hF.isoIsPullback_hom_snd _ _ hB
  have hF' : e.hom ≫ W'.projModelBaseChange φ = F := hF.isoIsPullback_hom_fst _ _ hB
  have h0' : W.projModelZero ≫ e.hom = (W'.map φ).projModelZero :=
    hB.hom_ext (by simp [hF', h0, projModelZero_projModelBaseChange]) (by simp [he])
  obtain ⟨x₁', y₁', h₁', rfl⟩ := W'.exists_eq_projModelAffinePoint hP' hP'₀
  obtain ⟨x₂', y₂', h₂', rfl⟩ := W'.exists_eq_projModelAffinePoint hQ' hQ'₀
  let P_φ := (W'.map φ).projModelAffinePoint (h₁'.map φ)
  let Q_φ := (W'.map φ).projModelAffinePoint (h₂'.map φ)
  have hPe : P ≫ e.hom = P_φ := hB.hom_ext
    (by rw [Category.assoc, hF', hPF, projModelAffinePoint_projModelBaseChange])
    (by simp [P_φ, he, hP])
  have hQe : Q ≫ e.hom = Q_φ := hB.hom_ext
    (by rw [Category.assoc, hF', hQF, projModelAffinePoint_projModelBaseChange])
    (by simp [Q_φ, he, hQ])
  have hP_φ₀ : ∀ s, P_φ s ≠ (W'.map φ).projModelZero s := fun s ↦
    (ne_projModelZero_iff_mem_basicOpen (projModelAffinePoint_projModelOver _) s).mpr
      (projModelAffinePoint_mem_basicOpen _ s)
  have hQ_φ₀ : ∀ s, Q_φ s ≠ (W'.map φ).projModelZero s := fun s ↦
    (ne_projModelZero_iff_mem_basicOpen (projModelAffinePoint_projModelOver _) s).mpr
      (projModelAffinePoint_mem_basicOpen _ s)
  have hbase : φ (W'.projModelAdaptedXCoord hP' hQ' hP'₀ hQ'₀ ω') =
      (W'.map φ).projModelAdaptedXCoord (projModelAffinePoint_projModelOver _)
        (projModelAffinePoint_projModelOver _) hP_φ₀ hQ_φ₀
        (Scheme.Hom.conormalBasisPullback W'.projModelZero_projModelOver
          (W'.map φ).projModelZero_projModelOver hB
          (W'.projModelZero_projModelBaseChange φ) ω') := by
    rw [W'.projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint hP' hQ' hP'₀ hQ'₀ ω'
        h₁' h₂' rfl rfl,
      (W'.map φ).projModelAdaptedXCoord_eq_of_eq_projModelAffinePoint _ _ hP_φ₀ hQ_φ₀ _
        (h₁'.map φ) (h₂'.map φ) rfl rfl,
      W'.weierstrassDifferentialScalar_conormalBasisPullback_projModelBaseChange φ ω']
    simp [Units.coe_map_inv]
  have hiso := projModelAdaptedXCoord_eq_of_iso e he h0' hP hQ hP₀ hQ₀
    (projModelAffinePoint_projModelOver _) (projModelAffinePoint_projModelOver _)
    hP_φ₀ hQ_φ₀ hPe hQe
    (Scheme.Hom.conormalBasisPullback W'.projModelZero_projModelOver
      (W'.map φ).projModelZero_projModelOver hB
      (W'.projModelZero_projModelBaseChange φ) ω')
  rw [hbase, ← hiso, Scheme.Hom.conormalBasisPullback_comp]
  congr 1
  exact Scheme.Hom.conormalBasisPullback_congr W'.projModelZero_projModelOver
    W.projModelZero_projModelOver (Category.id_comp _) hF' _ _ hF h0 ω'

end AdaptedXCoord

/-! ### Scheme-theoretic Legendre normal form over `Spec R` -/

section NormalForm

variable {W : WeierstrassCurve R}

private theorem conormalBasisPullback_eq_weierstrassDifferential_iff [W.IsElliptic]
    {W' : WeierstrassCurve R} [W'.IsElliptic] (C : VariableChange R) (hC : C • W = W')
    {e : W'.projModel ≅ W.projModel}
    (he : e.hom ≫ W.projModelOver = W'.projModelOver)
    (he₀ : W'.projModelZero ≫ e.hom = W.projModelZero)
    (heC : e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
        W.projModelZero_projModelOver W'.projModelZero_projModelOver
        (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
        (by rw [he₀, Category.id_comp]) ω =
      W'.weierstrassDifferential ↔
      C.u = W.weierstrassDifferentialScalar ω := by
  subst hC
  have he' : e.hom = (W.projModelVariableChangeIso C).hom := by simpa using heC
  have hcongr := Scheme.Hom.conormalBasisPullback_congr
    (f₁ := 𝟙 (Spec (.of R))) (g₁ := e.hom)
    W.projModelZero_projModelOver (C • W).projModelZero_projModelOver rfl he'
    (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
    (by rw [he₀, Category.id_comp])
    (IsPullback.of_horiz_isIso ⟨by simp⟩)
    (by rw [W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]) ω
  rw [hcongr]
  set ω' := Scheme.Hom.conormalBasisPullback
      (f := 𝟙 (Spec (.of R))) (g := (W.projModelVariableChangeIso C).hom)
      W.projModelZero_projModelOver (C • W).projModelZero_projModelOver
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
      (by rw [W.projModelZero_projModelVariableChangeIso_hom C, Category.id_comp]) ω
  have hiff : ω' = (C • W).weierstrassDifferential ↔
      (C • W).weierstrassDifferentialScalar ω' = 1 :=
    ⟨fun h ↦ by rw [h, weierstrassDifferentialScalar_weierstrassDifferential],
      fun h ↦ by rw [← (C • W).unitSmulIso_weierstrassDifferentialScalar ω', h, map_one,
        Scheme.Modules.unitSmulIso_one]⟩
  rw [hiff,
    W.weierstrassDifferentialScalar_conormalBasisPullback_projModelVariableChangeIso_hom C ω,
    mul_inv_eq_one, eq_comm]

private theorem exists_variableChange_of_iso [W.IsElliptic] {l : R}
    [hE : (TauCeti.freyCurve 1 (-l)).IsElliptic]
    {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    (e : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel)
    (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
    (he₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero)
    (heP : (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
      e.hom = W.projModelAffinePoint h₁)
    (heQ : (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫
      e.hom = W.projModelAffinePoint h₂)
    (heω : Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
      W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
      (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
      (by rw [he₀, Category.id_comp]) ω = (TauCeti.freyCurve 1 (-l)).weierstrassDifferential) :
    ∃ C : VariableChange R, ∃ hC : C • W = TauCeti.freyCurve 1 (-l),
      e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom ∧
        C.u = W.weierstrassDifferentialScalar ω ∧ C.r = x₁ ∧ C.t = y₁ ∧
        (C.u : R) ^ 2 + C.r = x₂ ∧ (C.u : R) ^ 2 * C.s + C.t = y₂ := by
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  have hCu := (conormalBasisPullback_eq_weierstrassDifferential_iff C hC he he₀ heC ω).mp heω
  rw [heC, hpt, projModelAffinePoint_inj] at heP heQ
  refine ⟨C, hC, heC, hCu, ?_, ?_, ?_, ?_⟩
  · simpa using heP.1
  · simpa using heP.2
  · simpa using heQ.1
  · simpa using heQ.2

private theorem exists_iso_of_variableChange [W.IsElliptic] {l : R}
    [hEll : (TauCeti.freyCurve 1 (-l)).IsElliptic]
    {x₁ y₁ x₂ y₂ : R} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    (C : VariableChange R) (hC : C • W = TauCeti.freyCurve 1 (-l))
    (hCu : C.u = W.weierstrassDifferentialScalar ω)
    (hCr : C.r = x₁) (hCt : C.t = y₁)
    (hCx : (C.u : R) ^ 2 + C.r = x₂) (hCy : (C.u : R) ^ 2 * C.s + C.t = y₂) :
    ∃ (e : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
      (he₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
          e.hom = W.projModelAffinePoint h₁ ∧
        (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫
          e.hom = W.projModelAffinePoint h₂ ∧
        Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
          W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
          (by rw [he₀, Category.id_comp]) ω =
        (TauCeti.freyCurve 1 (-l)).weierstrassDifferential := by
  obtain ⟨he, he₀, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  let e : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel :=
    eqToIso (congrArg projModel hC.symm) ≪≫ W.projModelVariableChangeIso C
  have heC : e.hom = eqToHom (congrArg projModel hC.symm) ≫ (W.projModelVariableChangeIso C).hom :=
    by rw [Iso.trans_hom, eqToIso.hom]
  have he' : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver := by rw [heC, he]
  have he₀' : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero := by
    rw [heC, he₀]
  refine ⟨e, he', he₀', ?_, ?_,
    (conormalBasisPullback_eq_weierstrassDifferential_iff C hC he' he₀' heC ω).mpr hCu⟩
  · rw [heC, hpt, projModelAffinePoint_inj]
    simp only [mul_zero, zero_add, hCr, hCt, and_self]
  · rw [heC, hpt, projModelAffinePoint_inj]
    simp only [mul_one, mul_zero, zero_add, hCx, hCy, and_self]

variable [W.IsElliptic]

/-- **Legendre normal form of a projective Weierstrass model.** Let `W` be an elliptic Weierstrass
curve over `R`, `P` and `Q` sections of `W.projModel` missing the zero section and killed by `2`,
and `ω` a conormal basis of the zero section with `W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1`.
Then there is a unique `l : R` for which `freyCurve 1 (-l)` is elliptic and admits a pointed
isomorphism `projModel (freyCurve 1 (-l)) ≅ projModel W` over `Spec R` carrying `(0, 0)` to `P`,
`(1, 0)` to `Q`, and pulling `ω` back to `(freyCurve 1 (-l)).weierstrassDifferential`; such an
isomorphism is itself unique (`legendreNormalForm_iso_ext`). -/
theorem existsUnique_legendreNormalForm {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s)
    (hP₂ : P ≫ W.projModelMulBy 2 = W.projModelZero)
    (hQ₂ : Q ≫ W.projModelMulBy 2 = W.projModelZero)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf)
    (hω : W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1) :
    ∃! l : R, ∃ (_ : (TauCeti.freyCurve 1 (-l)).IsElliptic)
      (e : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
      (he₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
          e.hom = P ∧
        (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫
          e.hom = Q ∧
        Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
          W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
          (by rw [he₀, Category.id_comp]) ω =
        (TauCeti.freyCurve 1 (-l)).weierstrassDifferential := by
  obtain ⟨x₁, y₁, h₁, rfl⟩ := W.exists_eq_projModelAffinePoint hP hP₀
  obtain ⟨x₂, y₂, h₂, rfl⟩ := W.exists_eq_projModelAffinePoint hQ hQ₀
  have hψ₁ := (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₁).mp hP₂
  have hψ₂ := (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₂).mp hQ₂
  set u := W.weierstrassDifferentialScalar ω
  have hu := (W.projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint
    hP hQ hP₀ hQ₀ ω h₁ h₂ rfl rfl).mp hω
  have h2 := W.isUnit_two_of_evalEval_ψ₂_eq_zero hψ₁ hψ₂ (hu ▸ u.isUnit.pow 2)
  obtain ⟨C, ⟨hCu, hCr, hCt, hCx, hCy, B, hCB⟩, hCuniq⟩ :=
    existsUnique_variableChange_legendre h2 u h₁ h₂ hψ₁ hψ₂ hu
  have hC : C • W = TauCeti.freyCurve 1 (-(-B)) := by rw [neg_neg, hCB]
  have hEll : (TauCeti.freyCurve 1 (-(-B))).IsElliptic := by
    rw [← hC]
    infer_instance
  obtain ⟨e, he, he₀, heP, heQ, heω⟩ :=
    exists_iso_of_variableChange h₁ h₂ ω C hC hCu hCr hCt hCx hCy
  refine ⟨-B, ⟨hEll, e, he, he₀, heP, heQ, heω⟩, ?_⟩
  rintro l ⟨hEll', e', he', he₀', heP', heQ', heω'⟩
  obtain ⟨D, hD, -, hDu, hDr, hDt, hDx, hDy⟩ :=
    exists_variableChange_of_iso h₁ h₂ ω e' he' he₀' heP' heQ' heω'
  obtain rfl : D = C := hCuniq D ⟨hDu, hDr, hDt, hDx, hDy, -l, hD⟩
  have ha₄ : (TauCeti.freyCurve 1 (-l)).a₄ = (TauCeti.freyCurve 1 B).a₄ :=
    congrArg a₄ (hD.symm.trans hCB)
  rw [TauCeti.freyCurve_a₄, TauCeti.freyCurve_a₄] at ha₄
  linear_combination ha₄

/-- **Uniqueness of the Legendre normal-form isomorphism.** Two pointed isomorphisms
`projModel (freyCurve 1 (-l)) ≅ projModel W` over `Spec R` carrying `(0, 0)` to the same section
and pulling `ω` back to `(freyCurve 1 (-l)).weierstrassDifferential` are equal. -/
theorem legendreNormalForm_iso_ext {l : R} [hE : (TauCeti.freyCurve 1 (-l)).IsElliptic]
    {ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf}
    {e e' : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel}
    (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
    (he₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero)
    (he' : e'.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
    (he'₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e'.hom = W.projModelZero)
    (heP : (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
      e.hom = (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
        e'.hom)
    (heω : Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
      W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
      (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
      (by rw [he₀, Category.id_comp]) ω = (TauCeti.freyCurve 1 (-l)).weierstrassDifferential)
    (he'ω : Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e'.hom)
      W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
      (IsPullback.of_horiz_isIso ⟨by rw [he', Category.comp_id]⟩)
      (by rw [he'₀, Category.id_comp]) ω = (TauCeti.freyCurve 1 (-l)).weierstrassDifferential) :
    e = e' := by
  have h2 : IsUnit (2 : R) := by
    have hunit := (TauCeti.isElliptic_freyCurve_one_neg_iff (l := l)).mp hE
    exact ((IsUnit.mul_iff.mp hunit).1 |> IsUnit.mul_iff.mp).1
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨C', ⟨hC', heC'⟩, -⟩ :=
    existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e' he' he'₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  obtain ⟨-, -, hpt'⟩ := eqToHom_projModelVariableChangeIso_hom_spec C' hC'
  have hCu := (conormalBasisPullback_eq_weierstrassDifferential_iff C hC he he₀ heC ω).mp heω
  have hC'u := (conormalBasisPullback_eq_weierstrassDifferential_iff C' hC' he' he'₀ heC' ω).mp
    he'ω
  rw [heC, heC', hpt, hpt', projModelAffinePoint_inj] at heP
  simp only [mul_zero, zero_add] at heP
  have hCC' : C = C' :=
    (eq_toLegendre h2 (W.weierstrassDifferentialScalar ω) hCu rfl rfl hC).trans
      (eq_toLegendre h2 (W.weierstrassDifferentialScalar ω) hC'u heP.1.symm heP.2.symm hC').symm
  subst hCC'
  ext1
  exact heC.trans heC'.symm

/-- **Necessity and sufficiency of the Legendre normal-form conditions.** Sections `P` and `Q` of
`W.projModel` and a conormal basis `ω` arise from an elliptic Legendre curve `freyCurve 1 (-l)` via
a pointed isomorphism over `Spec R` carrying `(0, 0)` to `P`, `(1, 0)` to `Q`, and pulling `ω` back
to `(freyCurve 1 (-l)).weierstrassDifferential` if and only if `P` and `Q` miss the zero section,
are killed by `2`, differ at every point of `Spec R`, and satisfy
`W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1`. -/
theorem exists_iso_legendreNormalForm_iff {P Q : Spec (.of R) ⟶ W.projModel}
    (hP : P ≫ W.projModelOver = 𝟙 _) (hQ : Q ≫ W.projModelOver = 𝟙 _)
    (ω : 𝟙_ (Spec (.of R)).Modules ≅ W.projModelZero.conormalSheaf) :
    (∃ (l : R) (_ : (TauCeti.freyCurve 1 (-l)).IsElliptic)
      (e : (TauCeti.freyCurve 1 (-l)).projModel ≅ W.projModel)
      (he : e.hom ≫ W.projModelOver = (TauCeti.freyCurve 1 (-l)).projModelOver)
      (he₀ : (TauCeti.freyCurve 1 (-l)).projModelZero ≫ e.hom = W.projModelZero),
      (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_zero 1 (-l)) ≫
          e.hom = P ∧
        (TauCeti.freyCurve 1 (-l)).projModelAffinePoint (equation_freyCurve_one_zero (-l)) ≫
          e.hom = Q ∧
        Scheme.Hom.conormalBasisPullback (f := 𝟙 (Spec (.of R))) (g := e.hom)
          W.projModelZero_projModelOver (TauCeti.freyCurve 1 (-l)).projModelZero_projModelOver
          (IsPullback.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩)
          (by rw [he₀, Category.id_comp]) ω =
        (TauCeti.freyCurve 1 (-l)).weierstrassDifferential) ↔
      ∃ (hP₀ : ∀ s, P s ≠ W.projModelZero s) (hQ₀ : ∀ s, Q s ≠ W.projModelZero s),
        P ≫ W.projModelMulBy 2 = W.projModelZero ∧ Q ≫ W.projModelMulBy 2 = W.projModelZero ∧
          (∀ s, Q s ≠ P s) ∧ W.projModelAdaptedXCoord hP hQ hP₀ hQ₀ ω = 1 := by
  refine ⟨fun ⟨l, hEll, e, he, he₀, heP, heQ, heω⟩ ↦ ?_,
    fun ⟨hP₀, hQ₀, hP₂, hQ₂, _, hω⟩ ↦
      let ⟨l, hl, _⟩ := W.existsUnique_legendreNormalForm hP hQ hP₀ hQ₀ hP₂ hQ₂ ω hω
      ⟨l, hl⟩⟩
  obtain ⟨C, ⟨hC, heC⟩, -⟩ := existsUnique_eq_eqToHom_comp_projModelVariableChangeIso_hom e he he₀
  obtain ⟨-, -, hpt⟩ := eqToHom_projModelVariableChangeIso_hom_spec C hC
  have hP_aff := heP.symm.trans (by rw [heC, hpt])
  have hQ_aff := heQ.symm.trans (by rw [heC, hpt])
  set h₁ := (Affine.variableChange_equation W C 0 0).mpr
    (hC ▸ equation_freyCurve_zero (R := R) 1 (-l))
  set h₂ := (Affine.variableChange_equation W C 1 0).mpr
    (hC ▸ equation_freyCurve_one_zero (R := R) (-l))
  have hP₀ : ∀ s, P s ≠ W.projModelZero s := fun s ↦ by
    rw [hP_aff]
    exact (ne_projModelZero_iff_mem_basicOpen (by simp) s).mpr
      (projModelAffinePoint_mem_basicOpen _ s)
  have hQ₀ : ∀ s, Q s ≠ W.projModelZero s := fun s ↦ by
    rw [hQ_aff]
    exact (ne_projModelZero_iff_mem_basicOpen (by simp) s).mpr
      (projModelAffinePoint_mem_basicOpen _ s)
  obtain ⟨D, hD, -, hDu, hDr, hDt, hDx, hDy⟩ :=
    exists_variableChange_of_iso h₁ h₂ ω e he he₀ (heP.trans hP_aff) (heQ.trans hQ_aff) heω
  obtain ⟨_, _, hψ₁, hψ₂, hu⟩ :=
    (exists_variableChange_legendre_iff (W := W) (W.weierstrassDifferentialScalar ω)).mp
      ⟨D, hDu, hDr, hDt, hDx, hDy, -l, hD⟩
  have hP₂ : P ≫ W.projModelMulBy 2 = W.projModelZero := by
    rw [hP_aff]
    exact (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₁).mpr hψ₁
  have hQ₂ : Q ≫ W.projModelMulBy 2 = W.projModelZero := by
    rw [hQ_aff]
    exact (W.projModelAffinePoint_projModelMulBy_two_eq_projModelZero_iff h₂).mpr hψ₂
  have hQP : ∀ s, Q s ≠ P s := by
    intro s
    rw [hP_aff, hQ_aff]
    exact (W.forall_projModelAffinePoint_apply_ne_iff_isUnit_sub h₁ h₂
      (hP_aff ▸ hP₂)).mpr (hu ▸ (W.weierstrassDifferentialScalar ω).isUnit.pow 2) s
  refine ⟨hP₀, hQ₀, hP₂, hQ₂, hQP, ?_⟩
  exact (W.projModelAdaptedXCoord_eq_one_iff_of_eq_projModelAffinePoint
    hP hQ hP₀ hQ₀ ω h₁ h₂ hP_aff hQ_aff).mpr hu

end NormalForm

end

end WeierstrassCurve
