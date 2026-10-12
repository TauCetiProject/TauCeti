/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Kernel
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree
-- Proof-only: base change preserves the degree of an isogeny, and `[n]`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.BaseChange
-- Proof-only: Galois descent of isogenies from a separable closure, and faithful base change.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent

/-!
# Factoring multiplication through a separable isogeny

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`. This file proves that
`[deg φ]` factors through `φ`, by a unique isogeny `χ : W₂ → W₁`, in two cases
(Silverman III.6.1):

* when the kernel of `φ` has `deg φ` points: every point of `ker φ` is killed by the order of
  `ker φ`, which is `deg φ`, so the kernel form of the factorisation theorem
  `TauCeti.Isogeny.existsUnique_comp_eq_iff_ker_le` applies;
* when `φ` is separable, over any field. Over a separably closed field the kernel of `φ` has
  exactly `deg φ` points (`TauCeti.Isogeny.card_ker_eq_degree`), which is the first case. Over an
  arbitrary field `F`, the factor `χ` of the base change of `[deg φ]` through the base change of
  `φ` to a separable closure `L` is fixed by `Gal(L/F)`: conjugating `χ` gives another factor,
  since `φ` and `[deg φ]` are defined over `F`, and the factor is unique. So `χ` descends to `F`
  (`TauCeti.Isogeny.existsUnique_map_eq_iff_galoisFixed`), and the descent is a factor of
  `[deg φ]` through `φ` because base change is faithful. This is the descent step of
  Silverman III.6.1; the extension attached to `φ` need not be Galois over `F` itself.

The separable case is the input from which `TauCeti.Isogeny.dual` constructs the dual of an
arbitrary isogeny, through Frobenius. Any factor of `[deg φ]` through `φ` has degree `deg φ`, by the
tower formula and `deg [n] = n²`.

## Main results

* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_card_ker_eq`: when
  `#ker φ = deg φ`, there is a unique `χ` with `χ ∘ φ = [deg φ]`.
* `TauCeti.Isogeny.degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree`: any such `χ` has degree
  `deg φ`.
* `TauCeti.Isogeny.existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_isSeparable`: `[deg φ]`
  factors uniquely through a separable isogeny `φ`, over any field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.8, III.4.10, III.4.11
  and III.6.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

section

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic]

/-- **`[deg φ]` factors through `φ` when the kernel of `φ` has `deg φ` points.** The factor
`χ : W₂ → W₁` with `χ ∘ φ = [deg φ]` is unique; it is the dual isogeny of `φ` (Silverman III.6.1).
The kernel of `φ` is a group of order `deg φ`, so `[deg φ]` kills it, and the kernel form of the
factorisation theorem applies. -/
theorem existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_card_ker_eq {φ : Isogeny W₁ W₂}
    (hφ : Nat.card φ.ker = φ.degree) :
    ∃! χ : Isogeny W₂ W₁,
      χ.comp φ = mulByIntIsogenyOfNeZero W₁ (n := φ.degree) (mod_cast φ.degree_pos.ne') := by
  refine (existsUnique_comp_eq_iff_ker_le hφ _).2 fun P hP ↦ ?_
  rw [mem_ker_mulByIntIsogenyOfNeZero_iff, natCast_zsmul, ← hφ]
  exact congrArg Subtype.val (card_nsmul_eq_zero' (G := φ.ker) (x := ⟨P, hP⟩))

omit [DecidableEq F] in
/-- **A factor of `[deg φ]` through `φ` has the degree of `φ`**: `deg χ · deg φ = deg [deg φ]`,
which is `(deg φ)²`. No hypothesis on the kernel of `φ` is needed. -/
theorem degree_eq_of_comp_eq_mulByIntIsogenyOfNeZero_degree {φ : Isogeny W₁ W₂}
    {χ : Isogeny W₂ W₁} {hn : (φ.degree : ℤ) ≠ 0}
    (h : χ.comp φ = mulByIntIsogenyOfNeZero W₁ hn) : χ.degree = φ.degree := by
  have hdeg := congrArg degree h
  rw [degree_comp, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast, sq] at hdeg
  exact Nat.eq_of_mul_eq_mul_right φ.degree_pos hdeg

end

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
    existsUnique_comp_eq_mulByIntIsogenyOfNeZero_degree_of_card_ker_eq (card_ker_eq_degree φL)
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

end TauCeti.Isogeny

end
