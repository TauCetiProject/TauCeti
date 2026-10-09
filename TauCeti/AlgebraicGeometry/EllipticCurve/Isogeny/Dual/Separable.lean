/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Commute
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
-- Proof-only: base change preserves the degree of an isogeny, and `[n]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.BaseChange
-- Proof-only: Galois descent of isogenies from a separable closure, and faithful base change.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent

/-!
# The dual of a separable isogeny

Let `φ : W₁ → W₂` be a separable isogeny of elliptic curves over a field `F`. Then `[deg φ]`
factors through `φ` by a unique isogeny. This factor is the **dual isogeny** `φ̂ : W₂ → W₁`
(Silverman III.6.1), and this file names it and proves its basic properties
(Silverman III.6.2(a), (c), (d), (e), (f)):

* `φ̂ ∘ φ = [deg φ]` on `W₁`, and `φ̂` is the only isogeny with this property;
* `φ ∘ φ̂ = [deg φ]` on `W₂`;
* `deg φ̂ = deg φ`;
* `(ψ ∘ φ)^ = φ̂ ∘ ψ̂` for separable `φ`, `ψ`;
* `φ̂̂ = φ` whenever `φ̂` is itself separable;
* `[n]̂ = [n]` whenever `n` is nonzero in the base field;
* `φ̂` commutes with base change along any homomorphism of fields.

Over a separably closed field the kernel of `φ` has exactly `deg φ` points
(`TauCeti.Isogeny.card_ker_eq_degree`), so `[deg φ]` kills it and factors through `φ`
(`TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree`). Over an arbitrary field
`F`, the factor `χ` of the base change of `[deg φ]` through the base change of `φ` to a separable
closure `L` is fixed by `Gal(L/F)`: conjugating `χ` gives another factor, since `φ` and `[deg φ]`
are defined over `F`, and the factor is unique. So `χ` descends to `F`
(`TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`), and the descent is a factor of `[deg φ]`
through `φ` because base change is faithful. This is the descent step of Silverman III.6.1; the
extension attached to `φ` need not be Galois over `F` itself.

The identity `φ ∘ φ̂ = [deg φ]` needs `φ ∘ [n] = [n] ∘ φ`
(`TauCeti.Isogeny.comp_mulByIntIsogenyOfNeZero`). Precomposing with `φ` is injective, so it cancels
from `φ ∘ φ̂ ∘ φ = φ ∘ [deg φ] = [deg φ] ∘ φ`.

## Main definitions

* `TauCeti.Isogeny.dual`: the dual `φ̂` of a separable isogeny `φ`.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable`: `[deg φ]`
  factors uniquely through a separable isogeny `φ`, over any field.
* `TauCeti.Isogeny.dual_comp` and `TauCeti.Isogeny.eq_dual_iff_comp_eq`: `φ̂ ∘ φ = [deg φ]`, and
  this characterises `φ̂`.
* `TauCeti.Isogeny.comp_dual`: `φ ∘ φ̂ = [deg φ]`.
* `TauCeti.Isogeny.degree_dual`: `deg φ̂ = deg φ`.
* `TauCeti.Isogeny.ofIsogeny_dual_comp_ofIsogeny` and
  `TauCeti.Isogeny.ofIsogeny_comp_ofIsogeny_dual`: the two composites are `deg φ • 1` in the
  additive groups of morphisms.
* `TauCeti.Isogeny.pointMap_dual_pointMap` and `TauCeti.Isogeny.pointMap_pointMap_dual`: on points,
  `φ̂ (φ P) = deg φ • P` and `φ (φ̂ Q) = deg φ • Q`.
* `TauCeti.Isogeny.dual_comp_dual`: `(ψ ∘ φ)^ = φ̂ ∘ ψ̂`.
* `TauCeti.Isogeny.dual_dual`: `φ̂̂ = φ` when `φ̂` is separable.
* `TauCeti.Isogeny.dual_mulByIntIsogeny`: `[n]` is self-dual when it is separable.
* `TauCeti.Isogeny.dual_map`: the dual of the base change is the base change of the dual.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.8, III.4.10, III.6.1 and
  III.6.2.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- **`[deg φ]` factors uniquely through a separable isogeny `φ`**, over any field
(Silverman III.6.1). -/
theorem existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable :
    ∃! χ : Isogeny W₂ W₁,
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) := by
  classical
  refine existsUnique_of_exists_of_unique ?_ fun χ χ' h h' ↦
    comp_right_injective φ (h.trans h'.symm)
  let L := SeparableClosure F
  let ι := algebraMap F L
  -- `φ` and `[deg φ]` base-change to the separable closure, where the factor exists
  let φL : Isogeny (W₁⁄L).toAffine (W₂⁄L).toAffine := φ.map ι
  let nL : Isogeny (W₁⁄L).toAffine (W₁⁄L).toAffine :=
    (mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero)).map ι
  have : Algebra.IsSeparable φL.fieldPullback.fieldRange (W₁⁄L).toAffine.FunctionField :=
    isSeparable_map φ ι
  have hn : mulByIntIsogenyOfNeZero (W₁⁄L).toAffine (n := φL.degree)
      (mod_cast φL.degree_ne_zero) = nL :=
    ((mulByIntIsogeny_map W₁ ι _).trans <| (mulByIntIsogeny_inj (W₁.map ι)
      (m := φ.degree) (n := (φ.map ι).degree) _ _).2 (by rw [degree_map])).symm
  obtain ⟨χ, hχ, -⟩ :=
    existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree (card_ker_eq_degree φL)
  rw [hn] at hχ
  -- conjugating the factor gives a factor, since `φ` and `[deg φ]` are defined over `F`
  have hfix (σ : L ≃ₐ[F] L) : χ.galoisConj W₂ W₁ σ = χ := by
    have hφ : φL.galoisConj W₁ W₂ σ = φL := galoisConj_map_algebraMap W₁ W₂ φ σ
    refine comp_right_injective φL ?_
    calc (χ.galoisConj W₂ W₁ σ).comp φL
        = (χ.galoisConj W₂ W₁ σ).comp (φL.galoisConj W₁ W₂ σ) := by rw [hφ]
      _ = nL.galoisConj W₁ W₁ σ := by rw [← galoisConj_comp, hχ]
      _ = χ.comp φL := (galoisConj_map_algebraMap W₁ W₁ _ σ).trans hχ.symm
  -- so it descends, and the descent is a factor because base change is faithful
  obtain ⟨χ₀, hχ₀, -⟩ := (existsUnique_map_eq_iff_galoisFixed W₂ W₁ χ).2 hfix
  refine ⟨χ₀, Hom.ofIsogeny_injective (Hom.map_injective ι ?_)⟩
  have h : (χ₀.comp φ).map ι = nL := (comp_map χ₀ φ ι).trans <| hχ₀ ▸ hχ
  exact (Hom.ofIsogeny_map _ ι).trans
    ((congrArg Hom.ofIsogeny h).trans (Hom.ofIsogeny_map _ ι).symm)

/-- **The dual isogeny** `φ̂ : W₂ → W₁` of a separable isogeny `φ : W₁ → W₂`: the unique isogeny
with `φ̂ ∘ φ = [deg φ]` (Silverman III.6.1). -/
noncomputable def dual : Isogeny W₂ W₁ :=
  (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable φ).exists.choose

/-- **The dual of `φ` composed with `φ` is multiplication by `deg φ`** on `W₁`
(Silverman III.6.1, III.6.2(a)). -/
@[simp]
theorem dual_comp :
    φ.dual.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  (existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable φ).exists.choose_spec

/-- **`φ̂` is the only isogeny `χ` with `χ ∘ φ = [deg φ]`.** -/
theorem eq_dual_iff_comp_eq {χ : Isogeny W₂ W₁} :
    χ = φ.dual ↔
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  ⟨fun h ↦ h ▸ φ.dual_comp, fun h ↦ comp_right_injective φ (h.trans φ.dual_comp.symm)⟩

/-- **The dual has the same degree** (Silverman III.6.2(e)). -/
@[simp]
theorem degree_dual : φ.dual.degree = φ.degree :=
  degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree φ.dual_comp

/-- **`φ` composed with its dual is multiplication by `deg φ`** on `W₂` (Silverman III.6.2(a)). -/
@[simp]
theorem comp_dual :
    φ.comp φ.dual = mulByIntIsogenyOfNeZero W₂ (n := φ.degree) (mod_cast φ.degree_ne_zero) :=
  comp_right_inj.mp <| by rw [comp_assoc, dual_comp, comp_mulByIntIsogenyOfNeZero]

/-- **`φ̂ ∘ φ = deg φ • 1`** in the additive group of morphisms of `W₁`. -/
theorem ofIsogeny_dual_comp_ofIsogeny :
    (Hom.ofIsogeny φ.dual).comp (Hom.ofIsogeny φ) = φ.degree • Hom.id W₁ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, dual_comp, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **`φ ∘ φ̂ = deg φ • 1`** in the additive group of morphisms of `W₂`. -/
theorem ofIsogeny_comp_ofIsogeny_dual :
    (Hom.ofIsogeny φ).comp (Hom.ofIsogeny φ.dual) = φ.degree • Hom.id W₂ := by
  rw [Hom.ofIsogeny_comp_ofIsogeny, comp_dual, ofIsogeny_mulByIntIsogeny, natCast_zsmul]

/-- **On points, `φ̂ (φ P) = deg φ • P`.** -/
@[simp]
theorem pointMap_dual_pointMap [DecidableEq F] (P : W₁.Point) :
    (Hom.ofIsogeny φ.dual).pointMap ((Hom.ofIsogeny φ).pointMap P) = φ.degree • P := by
  rw [← Hom.comp_pointMap, ofIsogeny_dual_comp_ofIsogeny, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **On points, `φ (φ̂ Q) = deg φ • Q`.** -/
@[simp]
theorem pointMap_pointMap_dual [DecidableEq F] (Q : W₂.Point) :
    (Hom.ofIsogeny φ).pointMap ((Hom.ofIsogeny φ.dual).pointMap Q) = φ.degree • Q := by
  rw [← Hom.comp_pointMap, ofIsogeny_comp_ofIsogeny_dual, Hom.nsmul_pointMap, Hom.id_pointMap]

/-- **The dual of the dual is the original isogeny**, when the dual is separable
(Silverman III.6.2(f)). -/
@[simp]
theorem dual_dual [Algebra.IsSeparable φ.dual.fieldPullback.fieldRange W₂.FunctionField] :
    φ.dual.dual = φ :=
  ((eq_dual_iff_comp_eq φ.dual).mpr <| by
    rw [comp_dual, mulByIntIsogeny_inj, degree_dual]).symm

variable {W₃ : WeierstrassCurve.Affine F} [W₃.IsElliptic] (ψ : Isogeny W₂ W₃)
  [Algebra.IsSeparable ψ.fieldPullback.fieldRange W₂.FunctionField]

-- `(ψ.comp φ).dual` needs the composite to be separable; `isSeparable_comp` is not a global
-- instance (see the comment at its definition), so it is activated locally for the statement
-- below.
attribute [local instance] isSeparable_comp

/-- **The dual of a composite is the composite of the duals in the opposite order**:
`(ψ ∘ φ)^ = φ̂ ∘ ψ̂` (Silverman III.6.2(c)). -/
theorem dual_comp_dual : φ.dual.comp ψ.dual = (ψ.comp φ).dual := by
  have hφ : (φ.degree : ℤ) ≠ 0 := mod_cast φ.degree_ne_zero
  have hψ : (ψ.degree : ℤ) ≠ 0 := mod_cast ψ.degree_ne_zero
  -- `φ̂ ∘ ψ̂` composed with `ψ ∘ φ` cancels `ψ̂ ∘ ψ` to `[deg ψ]`, then `φ̂ ∘ φ` to `[deg φ]`
  refine (eq_dual_iff_comp_eq (ψ.comp φ)).mpr ?_
  calc (φ.dual.comp ψ.dual).comp (ψ.comp φ)
      = φ.dual.comp ((ψ.dual.comp ψ).comp φ) := by rw [comp_assoc, comp_assoc]
    _ = (φ.dual.comp φ).comp (mulByIntIsogenyOfNeZero W₁ hψ) := by
        rw [dual_comp ψ, ← comp_mulByIntIsogenyOfNeZero φ, comp_assoc]
    _ = mulByIntIsogenyOfNeZero W₁ (mul_ne_zero hφ hψ) := by
        rw [dual_comp φ, mulByIntIsogenyOfNeZero_comp_mulByIntIsogenyOfNeZero]
    _ = mulByIntIsogenyOfNeZero W₁ (n := (ψ.comp φ).degree)
          (mod_cast (ψ.comp φ).degree_ne_zero) := by
        rw [mulByIntIsogeny_inj, degree_comp, Nat.cast_mul, mul_comm]

variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **Multiplication by `n` is self-dual** when it is separable, that is, when `n` is nonzero in
`F` (`isSeparable_mulByIntIsogeny_iff`; Silverman III.6.2(d)). -/
@[simp]
theorem dual_mulByIntIsogeny {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    [Algebra.IsSeparable (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField] :
    (mulByIntIsogeny W hn).dual = mulByIntIsogeny W hn :=
  ((eq_dual_iff_comp_eq _).mpr <| by
    have hchar := (isSeparable_mulByIntIsogeny_iff W hn).mp ‹_›
    rw [mulByIntIsogeny_comp_mulByIntIsogeny W hn hn
        (psiFunctionField_ne_zero W (by push_cast; exact mul_ne_zero hchar hchar)),
      mulByIntIsogeny_inj, degree_mulByIntIsogeny, Nat.cast_pow, Int.natAbs_sq, sq]).symm

variable {K : Type*} [Field K]

-- `(φ.map f).dual` needs the base change to be separable; it follows from separability of `φ` by
-- `isSeparable_map`, which is activated locally for the statement below.
attribute [local instance] isSeparable_map

/-- **The dual commutes with base change**: along any homomorphism of fields `f`, the base change
of `φ̂` is the dual of the base change of `φ`. -/
@[simp]
theorem dual_map (f : F →+* K) : φ.dual.map f = (φ.map f).dual :=
  (eq_dual_iff_comp_eq _).mpr <| by
    rw [← comp_map, dual_comp, mulByIntIsogeny_map, mulByIntIsogeny_inj, degree_map]

end TauCeti.Isogeny

end
