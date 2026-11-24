/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.PuncturedAffineSpace
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product
import TauCeti.CategoryTheory.Sites.SheafCohomology.SectionsQuotient

/-!
# The punctured plane has nonzero first cohomology

Let `R` be a nonzero commutative ring. The punctured plane `𝔸²_R ∖ {0}` is covered by the two
basic opens `D(x)` and `D(y)` of `𝔸²_R = Spec R[x, y]`, with intersection `D(xy)`. Its first
cohomology with coefficients in the structure sheaf is the cokernel of the difference of the
restriction maps `R[x, y]_x × R[x, y]_y → R[x, y]_{xy}`, and `1 / (xy)` is not in the image: a
Laurent polynomial in the image has no monomial with both exponents negative. So
`H¹(𝔸²_R ∖ {0}, 𝒪) ≠ 0`, and since quasi-coherent sheaves on affine schemes have no higher
cohomology, `𝔸²_R ∖ {0}` is not affine.

The input is the degree-zero end of the Mayer-Vietoris sequence of the two opens, which is the
two-set Čech computation: if `H¹(U ⊔ V, M) = 0`, every section of `M` over `U ⊓ V` is the
difference of restrictions of sections over `U` and over `V`
(`TauCeti.CategoryTheory.mayerVietorisSectionClass_eq_zero_iff`).

## Main declarations

* `TauCeti.PuncturedAffineSpace.nontrivial_cohomologyOn_one_puncturedPlane`: on the open subset
  `𝔸²_R ∖ {0}` of `𝔸²_R`, `H¹(𝔸²_R ∖ {0}, 𝒪) ≠ 0`;
* `TauCeti.PuncturedAffineSpace.nontrivial_cohomology_one_puncturedPlane`: the same for the
  structure sheaf of the open subscheme `𝔸²_R ∖ {0}`;
* `TauCeti.PuncturedAffineSpace.not_isAffine_puncturedPlane`: `𝔸²_R ∖ {0}` is not affine.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.3.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Opposite

universe u

noncomputable section

namespace TauCeti

namespace PuncturedAffineSpace

open MvPolynomial

variable {R : Type u} [CommRing R]

/-- In `R[x, y]` over a nonzero ring, `(xy)ᵏ xᵐ yⁿ` is not `(xy)ᵏ (x yⁿ⁺¹ p + xᵐ⁺¹ y q)`: the
monomial `x^(k + m) y^(k + n)` has coefficient one on the left and zero on the right. -/
private theorem pow_mul_ne_pow_mul [Nontrivial R] (k m n : ℕ) (p q : MvPolynomial (Fin 2) R) :
    (X 0 * X 1) ^ k * (X 0 ^ m * X 1 ^ n) ≠
      (X 0 * X 1) ^ k * (X 0 * X 1 ^ (n + 1) * p + X 0 ^ (m + 1) * X 1 * q) := by
  intro h
  have hmon : ∀ a b : ℕ, (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) R) =
      monomial (Finsupp.single 0 a + Finsupp.single 1 b) 1 := by
    intro a b
    simp [X_pow_eq_monomial, monomial_mul_monomial]
  let e : Fin 2 →₀ ℕ := Finsupp.single 0 (k + m) + Finsupp.single 1 (k + n)
  have h := congrArg (fun r : MvPolynomial (Fin 2) R => r.coeff e) h
  have l : (X 0 * X 1) ^ k * (X 0 ^ m * X 1 ^ n) =
      (X 0 ^ (k + m) * X 1 ^ (k + n) : MvPolynomial (Fin 2) R) := by ring
  have r : (X 0 * X 1) ^ k * (X 0 * X 1 ^ (n + 1) * p + X 0 ^ (m + 1) * X 1 * q) =
      X 0 ^ (k + 1) * X 1 ^ (k + n + 1) * p + X 0 ^ (k + m + 1) * X 1 ^ (k + 1) * q := by ring
  -- A multiple of `xᵃ yᵇ` has no `x^(k + m) y^(k + n)` term once `a` or `b` is too large.
  have hzero (a b : ℕ) (s : MvPolynomial (Fin 2) R) (hab : k + m < a ∨ k + n < b) :
      (X 0 ^ a * X 1 ^ b * s).coeff e = 0 := by
    rw [hmon, coeff_monomial_mul', ite_eq_right_iff]
    intro hle
    have h0 := hle 0
    have h1 := hle 1
    simp [e] at h0 h1
    omega
  rw [l, r, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hzero _ _ _ (.inr (by omega)),
    hzero _ _ _ (.inl (by omega)), hmon] at h
  simp [e] at h

/-- If `1 / (xy)` in a localization `D` of `A` away from `xy` is the difference of the images of
elements of localizations `B` away from `x` and `C` away from `y`, under maps compatible with the
maps from `A`, then clearing denominators gives `(xy)ᵏ xᵐ yⁿ = (xy)ᵏ (x yⁿ⁺¹ p + xᵐ⁺¹ y q)` in `A`
for some `k`, `m`, `n`, `p` and `q`. -/
private theorem exists_eq_of_sub_eq_invSelf {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra A B] [Algebra A C] [Algebra A D] {x y : A}
    [IsLocalization.Away x B] [IsLocalization.Away y C] [IsLocalization.Away (x * y) D]
    (f : B →+* D) (hf : ∀ r, f (algebraMap A B r) = algebraMap A D r)
    (g : C →+* D) (hg : ∀ r, g (algebraMap A C r) = algebraMap A D r)
    (b : B) (c : C) (h : f b - g c = IsLocalization.Away.invSelf (x * y)) :
    ∃ (k m n : ℕ) (p q : A), (x * y) ^ k * (x ^ m * y ^ n) =
      (x * y) ^ k * (x * y ^ (n + 1) * p + x ^ (m + 1) * y * q) := by
  obtain ⟨⟨p, _, m, rfl⟩, hb⟩ := IsLocalization.surj (Submonoid.powers x) b
  obtain ⟨⟨q, _, n, rfl⟩, hc⟩ := IsLocalization.surj (Submonoid.powers y) c
  have hfb := congrArg f hb
  have hgc := congrArg g hc
  simp only [map_mul, hf, hg] at hfb hgc
  have hinv := IsLocalization.Away.mul_invSelf (S := D) (x * y)
  have key : algebraMap A D (x ^ m * y ^ n) =
      algebraMap A D (x * y ^ (n + 1) * p + x ^ (m + 1) * y * -q) := by
    rw [← h] at hinv
    simp only [map_add, map_mul, map_pow, map_neg] at hinv hfb hgc ⊢
    linear_combination (-(algebraMap A D x ^ m * algebraMap A D y ^ n)) * hinv +
      (algebraMap A D y ^ (n + 1) * algebraMap A D x) * hfb -
      (algebraMap A D x ^ (m + 1) * algebraMap A D y) * hgc
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (x * y)) D).mp key
  exact ⟨k, m, n, p, -q, hk⟩

variable (R) in
/-- The global function `X i` on `𝔸²_R = Spec R[x, y]`. -/
private abbrev coordinate (i : Fin 2) :
    Γ(Spec (.of (MvPolynomial (Fin 2) R)), ⊤) :=
  (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) R))).inv (X i)

variable (R) in
/-- The punctured plane is the union of the basic opens `D(x)` and `D(y)`. -/
private theorem basicOpen_sup_basicOpen :
    (Spec (.of (MvPolynomial (Fin 2) R))).basicOpen (coordinate R 0) ⊔
        (Spec (.of (MvPolynomial (Fin 2) R))).basicOpen (coordinate R 1) =
      puncturedAffineSpaceOpens R (Fin 2) := by
  rw [puncturedAffineSpaceOpens_eq_iSup_basicOpen]
  exact le_antisymm (sup_le (le_iSup_of_le 0 le_rfl) (le_iSup_of_le 1 le_rfl))
    (iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩))

/-- **The punctured plane is not cohomologically trivial.** Over a nonzero ring `R`, the first
cohomology of the structure sheaf of `𝔸²_R` on the open subset `𝔸²_R ∖ {0}` is nonzero. -/
theorem nontrivial_cohomologyOn_one_puncturedPlane [Nontrivial R] :
    Nontrivial (AlgebraicGeometry.Scheme.Modules.cohomologyOn
      (SheafOfModules.unit (Spec (.of (MvPolynomial (Fin 2) R))).ringCatSheaf) 1
      (puncturedAffineSpaceOpens R (Fin 2))) := by
  set Y := Spec (.of (MvPolynomial (Fin 2) R))
  set x := coordinate R 0
  set y := coordinate R 1
  rw [← not_subsingleton_iff_nontrivial, ← basicOpen_sup_basicOpen]
  intro hsub
  have hxle : Y.basicOpen (x * y) ≤ Y.basicOpen x := Y.basicOpen_mul x y ▸ inf_le_left
  have hyle : Y.basicOpen (x * y) ≤ Y.basicOpen y := Y.basicOpen_mul x y ▸ inf_le_right
  -- Mayer-Vietoris for `D(x)` and `D(y)`, with the overlap written as `D(xy)`: the section
  -- `1 / (xy)` is a difference of restrictions. The ascription restates it for the structure
  -- sheaf: the sections of the unit sheaf of modules and the maps of the square are
  -- definitionally those of `Y.presheaf` along `D(xy) ≤ D(x)` and `D(xy) ≤ D(y)`.
  obtain ⟨a, b, hab⟩ : ∃ (a : Γ(Y, Y.basicOpen x)) (b : Γ(Y, Y.basicOpen y)),
      (Y.presheaf.map (homOfLE hxle).op).hom a - (Y.presheaf.map (homOfLE hyle).op).hom b =
        IsLocalization.Away.invSelf (x * y) :=
    (TauCeti.CategoryTheory.mayerVietorisSectionClass_eq_zero_iff
      (Opens.mayerVietorisSquare'
        { X₁ := Y.basicOpen (x * y)
          X₂ := Y.basicOpen x
          X₃ := Y.basicOpen y
          X₄ := Y.basicOpen x ⊔ Y.basicOpen y
          f₁₂ := homOfLE hxle
          f₁₃ := homOfLE hyle
          f₂₄ := homOfLE le_sup_left
          f₃₄ := homOfLE le_sup_right
          fac := Subsingleton.elim _ _ } rfl (Y.basicOpen_mul x y))
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj (SheafOfModules.unit Y.ringCatSheaf)) _).mp
      (@Subsingleton.elim _ hsub _ _)
  -- Compatibility with the maps from `Γ(Y, ⊤)` is functoriality of restriction; the `|_`
  -- restrictions of `TopCat.Presheaf.restrict_restrict` unfold to these presheaf maps.
  obtain ⟨k, m, n, p, q, h⟩ := exists_eq_of_sub_eq_invSelf
    (Y.presheaf.map (homOfLE hxle).op).hom
    (TopCat.Presheaf.restrict_restrict hxle (Y.basicOpen_le x))
    (Y.presheaf.map (homOfLE hyle).op).hom
    (TopCat.Presheaf.restrict_restrict hyle (Y.basicOpen_le y)) _ _ hab
  have h' := congrArg (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 2) R))).hom h
  simp only [map_mul, map_pow, map_add, x, y, coordinate, Iso.inv_hom_id_apply] at h'
  exact pow_mul_ne_pow_mul k m n _ _ h'

/-- **The punctured plane has nonzero first cohomology.** Over a nonzero ring `R`, the first
cohomology `H¹(𝔸²_R ∖ {0}, 𝒪)` of the structure sheaf of the punctured plane is nonzero. -/
theorem nontrivial_cohomology_one_puncturedPlane [Nontrivial R] :
    Nontrivial (AlgebraicGeometry.Scheme.Modules.Cohomology
      (SheafOfModules.unit (puncturedAffineSpace R (Fin 2)).left.ringCatSheaf) 1) := by
  let W := puncturedAffineSpaceOpens R (Fin 2)
  have e := Scheme.Modules.cohomologyOnOpensRangeIso W.ι
    (SheafOfModules.unit (Spec (.of (MvPolynomial (Fin 2) R))).ringCatSheaf) 1
  rw [Scheme.Opens.opensRange_ι] at e
  have := nontrivial_cohomologyOn_one_puncturedPlane (R := R)
  exact (((AlgebraicGeometry.Scheme.Modules.cohomologyFunctor _ 1).mapIso
    (Scheme.Modules.restrictUnitIso W.ι)).symm ≪≫
      e.symm).addCommGroupIsoToAddEquiv.toEquiv.nontrivial

/-- **The punctured plane is not affine.** Over a nonzero ring `R`, `𝔸²_R ∖ {0}` is not an affine
scheme, since its structure sheaf has nonzero first cohomology. -/
theorem not_isAffine_puncturedPlane [Nontrivial R] :
    ¬ IsAffine (puncturedAffineSpace R (Fin 2)).left := by
  intro _
  have := nontrivial_cohomology_one_puncturedPlane (R := R)
  exact not_subsingleton _ (Scheme.Modules.subsingleton_cohomology_succ_of_isAffine
    (SheafOfModules.unit (puncturedAffineSpace R (Fin 2)).left.ringCatSheaf) 0)

end PuncturedAffineSpace

end TauCeti
