/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic

/-!
# Zero-inclusive `sl₂` triples

Mathlib's `IsSl2Triple h e f` asks for the three relations

`⁅e, f⁆ = h`, `⁅h, e⁆ = 2e`, `⁅h, f⁆ = -2f`

together with `h ≠ 0`. This file defines `TauCeti.IsSl2TripleOrZero h e f`, the same three
relations with no condition on `h`. Over a Lie algebra without `2`-torsion (for instance a vector
space over a field of characteristic zero) the only additional solution is the zero triple
`(0, 0, 0)`: if `h = 0` then `2e = ⁅h, e⁆ = 0` and `2f = 0`. The zero triple is the triple attached
to the nilpotent element `0`, and statements quantifying over all nilpotent elements, such as the
classification of nilpotent orbits by weighted Dynkin diagrams or the recognition of triples by
their weight filtrations on representations, include it. Over a ring in which `2 = 0` the
relations degenerate: `(0, e, f)` satisfies them whenever `⁅e, f⁆ = 0`.

A zero-inclusive triple is the same thing as a Lie algebra homomorphism `sl (Fin 2) K →ₗ⁅K⁆ L`,
with no condition on the image of the Cartan element: the homomorphism
`TauCeti.IsSl2TripleOrZero.toLieHom` sends the standard basis `E = E₀₁`, `F = E₁₀`,
`H = E₀₀ - E₁₁` to `e`, `f`, `h`, and `TauCeti.sl2TripleOrZeroEquivLieHom` is the resulting
bijection. This is the map along which a representation of `L` restricts to `sl₂`; the zero triple
gives the zero homomorphism, along which every representation restricts to a trivial one.

## Main definitions

* `TauCeti.IsSl2TripleOrZero`: the three `sl₂` relations, without `h ≠ 0`.
* `TauCeti.IsSl2TripleOrZero.toLieHom`: the homomorphism `sl (Fin 2) K →ₗ⁅K⁆ L` of a
  zero-inclusive triple.
* `TauCeti.sl2TripleOrZeroEquivLieHom`: zero-inclusive triples in `L` correspond to Lie algebra
  homomorphisms `sl (Fin 2) K →ₗ⁅K⁆ L`.

## Main results

* `IsSl2Triple.isSl2TripleOrZero` and `TauCeti.isSl2Triple_iff_isSl2TripleOrZero_and_ne_zero`: an
  `sl₂` triple is exactly a zero-inclusive triple with `h ≠ 0`.
* `TauCeti.isSl2TripleOrZero_iff`: without `2`-torsion, a zero-inclusive triple is either the zero
  triple or an `sl₂` triple; `TauCeti.IsSl2TripleOrZero.e_eq_zero_iff` and
  `TauCeti.IsSl2TripleOrZero.f_eq_zero_iff` say that each of `e` and `f` vanishes exactly when `h`
  does.
* `TauCeti.IsSl2TripleOrZero.map` and `TauCeti.isSl2TripleOrZero_map_iff`: images under Lie
  algebra homomorphisms and injective ones. The images under inner automorphisms are
  `TauCeti.IsSl2TripleOrZero.smul_of_mem_intLieAlgebra`, in
  `TauCeti.Algebra.Lie.AdjointAction.InnerAutomorphismGroup`.
* `TauCeti.IsSl2TripleOrZero.symm`: `(-h, f, e)` is a zero-inclusive triple when `(h, e, f)` is.
* `TauCeti.IsSl2TripleOrZero.toLieHom_eq_zero_iff`: the homomorphism of a triple vanishes exactly
  for the zero triple; `TauCeti.IsSl2TripleOrZero.toLieHom_map` is its naturality.
* `LieHom.eq_toLieHom_map`: every homomorphism `φ` out of `sl (Fin 2) K` is the homomorphism of the
  image of the standard triple.

## References

* D. Ciubotaru and M. Harris, *On the generalized Ramanujan and Arthur conjectures over function
  fields*, arXiv:2311.15300, §2.1, relations (2.1), for the zero-inclusive convention.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11.
-/

public section

open LieAlgebra

namespace TauCeti

/-- A **zero-inclusive `sl₂` triple** in a Lie ring `L`: three elements `h`, `e`, `f` obeying the
`sl₂` relations `⁅e, f⁆ = h`, `⁅h, e⁆ = 2e`, `⁅h, f⁆ = -2f`, with no condition on `h`. Unlike
Mathlib's `IsSl2Triple`, which also asks for `h ≠ 0`, the zero triple `(0, 0, 0)` qualifies; over a
Lie algebra without `2`-torsion it is the only additional solution
(`TauCeti.isSl2TripleOrZero_iff`). -/
structure IsSl2TripleOrZero {L : Type*} [LieRing L] (h e f : L) : Prop where
  lie_e_f : ⁅e, f⁆ = h
  lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
  lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)

section LieRing

variable {L : Type*} [LieRing L] {h e f : L}

/-- The zero triple is a zero-inclusive `sl₂` triple. -/
@[simp]
theorem isSl2TripleOrZero_zero : IsSl2TripleOrZero (0 : L) 0 0 where
  lie_e_f := lie_zero 0
  lie_h_e_nsmul := by simp
  lie_h_f_nsmul := by simp

/-- An `sl₂` triple is a zero-inclusive `sl₂` triple whose neutral element is nonzero. -/
theorem isSl2Triple_iff_isSl2TripleOrZero_and_ne_zero :
    IsSl2Triple h e f ↔ IsSl2TripleOrZero h e f ∧ h ≠ 0 :=
  ⟨fun t ↦ ⟨⟨t.lie_e_f, t.lie_h_e_nsmul, t.lie_h_f_nsmul⟩, t.h_ne_zero⟩,
    fun ⟨t, hh⟩ ↦ ⟨hh, t.lie_e_f, t.lie_h_e_nsmul, t.lie_h_f_nsmul⟩⟩

end LieRing

end TauCeti

namespace IsSl2Triple

open TauCeti

/-- An `sl₂` triple is a zero-inclusive `sl₂` triple. -/
theorem isSl2TripleOrZero {L : Type*} [LieRing L] {h e f : L} (t : IsSl2Triple h e f) :
    IsSl2TripleOrZero h e f :=
  (isSl2Triple_iff_isSl2TripleOrZero_and_ne_zero.mp t).1

end IsSl2Triple

namespace TauCeti

namespace IsSl2TripleOrZero

section LieRing

variable {L : Type*} [LieRing L] {h e f : L}

/-- A zero-inclusive triple with nonzero neutral element is an `sl₂` triple. -/
theorem isSl2Triple (t : IsSl2TripleOrZero h e f) (hh : h ≠ 0) : IsSl2Triple h e f :=
  isSl2Triple_iff_isSl2TripleOrZero_and_ne_zero.mpr ⟨t, hh⟩

/-- **Negation and exchange.** If `(h, e, f)` is a zero-inclusive `sl₂` triple then so is
`(-h, f, e)`. -/
theorem symm (t : IsSl2TripleOrZero h e f) : IsSl2TripleOrZero (-h) f e where
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, t.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, t.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, t.lie_h_e_nsmul]

/-- `(-h, f, e)` is a zero-inclusive `sl₂` triple exactly when `(h, e, f)` is. -/
@[simp]
theorem symm_iff : IsSl2TripleOrZero (-h) f e ↔ IsSl2TripleOrZero h e f :=
  ⟨fun t ↦ neg_neg h ▸ t.symm, symm⟩

/-- A zero-inclusive triple whose raising element vanishes has zero neutral element. -/
theorem h_eq_zero_of_e_eq_zero (t : IsSl2TripleOrZero h e f) (he : e = 0) : h = 0 := by
  rw [← t.lie_e_f, he, zero_lie]

/-- A zero-inclusive triple whose lowering element vanishes has zero neutral element. -/
theorem h_eq_zero_of_f_eq_zero (t : IsSl2TripleOrZero h e f) (hf : f = 0) : h = 0 := by
  rw [← t.lie_e_f, hf, lie_zero]

variable [HasUniqueDiv L]

/-- Without `2`-torsion, the raising element of a zero-inclusive triple vanishes exactly when the
neutral element does: `2e = ⁅h, e⁆`. -/
theorem e_eq_zero_iff (t : IsSl2TripleOrZero h e f) : e = 0 ↔ h = 0 :=
  ⟨t.h_eq_zero_of_e_eq_zero, fun hh ↦ two_nsmul_eq_zero.mp <| by
    rw [← t.lie_h_e_nsmul, hh, zero_lie]⟩

/-- Without `2`-torsion, the lowering element of a zero-inclusive triple vanishes exactly when the
neutral element does: `-2f = ⁅h, f⁆`. -/
theorem f_eq_zero_iff (t : IsSl2TripleOrZero h e f) : f = 0 ↔ h = 0 :=
  ⟨t.h_eq_zero_of_f_eq_zero, fun hh ↦ two_nsmul_eq_zero.mp <| neg_eq_zero.mp <| by
    rw [← t.lie_h_f_nsmul, hh, zero_lie]⟩

end LieRing

section CommRing

variable (R : Type*) {L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {h e f : L}

/-- The relation `⁅h, e⁆ = 2e` of a zero-inclusive triple, with `2` a scalar of the ring. -/
theorem lie_h_e_smul (t : IsSl2TripleOrZero h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]

/-- The relation `⁅h, f⁆ = -2f` of a zero-inclusive triple, with `2` a scalar of the ring. -/
theorem lie_lie_smul_f (t : IsSl2TripleOrZero h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]

variable {R}

/-- A Lie algebra homomorphism carries a zero-inclusive `sl₂` triple to a zero-inclusive `sl₂`
triple. Unlike `IsSl2Triple.map`, no condition on the image of `h` is needed; a homomorphism that
kills `h`, such as the zero homomorphism, carries the triple to the zero triple. -/
theorem map {L' : Type*} [LieRing L'] [LieAlgebra R L'] (t : IsSl2TripleOrZero h e f)
    (φ : L →ₗ⁅R⁆ L') : IsSl2TripleOrZero (φ h) (φ e) (φ f) where
  lie_e_f := by rw [← LieHom.map_lie, t.lie_e_f]
  lie_h_e_nsmul := by rw [← LieHom.map_lie, t.lie_h_e_nsmul, map_nsmul]
  lie_h_f_nsmul := by rw [← LieHom.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

end CommRing

end IsSl2TripleOrZero

section Map

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L']
  [LieAlgebra R L'] {h e f : L}

/-- An injective Lie algebra homomorphism `φ` carries `(h, e, f)` to a zero-inclusive `sl₂` triple
exactly when `(h, e, f)` is one. -/
theorem isSl2TripleOrZero_map_iff {φ : L →ₗ⁅R⁆ L'} (hφ : Function.Injective φ) :
    IsSl2TripleOrZero (φ h) (φ e) (φ f) ↔ IsSl2TripleOrZero h e f := by
  refine ⟨fun t ↦ ⟨hφ ?_, hφ ?_, hφ ?_⟩, fun t ↦ t.map φ⟩
  · rw [LieHom.map_lie, t.lie_e_f]
  · rw [LieHom.map_lie, t.lie_h_e_nsmul, map_nsmul]
  · rw [LieHom.map_lie, t.lie_h_f_nsmul, map_neg, map_nsmul]

end Map

end TauCeti

/-- A Lie algebra isomorphism carries `(h, e, f)` to a zero-inclusive `sl₂` triple exactly when
`(h, e, f)` is one. -/
@[simp]
theorem LieEquiv.isSl2TripleOrZero_apply_iff {R L L' : Type*} [CommRing R] [LieRing L]
    [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] (φ : L ≃ₗ⁅R⁆ L') {h e f : L} :
    TauCeti.IsSl2TripleOrZero (φ h) (φ e) (φ f) ↔ TauCeti.IsSl2TripleOrZero h e f :=
  TauCeti.isSl2TripleOrZero_map_iff (φ := φ.toLieHom) φ.injective

namespace TauCeti

/-- **The zero-inclusive dichotomy.** In a Lie ring without `2`-torsion, a zero-inclusive `sl₂`
triple is either the zero triple or an `sl₂` triple. -/
theorem isSl2TripleOrZero_iff {L : Type*} [LieRing L] [HasUniqueDiv L] {h e f : L} :
    IsSl2TripleOrZero h e f ↔ (h = 0 ∧ e = 0 ∧ f = 0) ∨ IsSl2Triple h e f := by
  refine ⟨fun t ↦ ?_, ?_⟩
  · by_cases hh : h = 0
    · exact .inl ⟨hh, t.e_eq_zero_iff.mpr hh, t.f_eq_zero_iff.mpr hh⟩
    · exact .inr (t.isSl2Triple hh)
  · rintro (⟨rfl, rfl, rfl⟩ | t)
    exacts [isSl2TripleOrZero_zero, t.isSl2TripleOrZero]

/-- For `i ≠ j`, the matrix units `Eᵢᵢ - Eⱼⱼ`, `Eᵢⱼ`, `Eⱼᵢ` form a zero-inclusive `sl₂` triple in
`sl n R`, over every commutative ring: over a nontrivial ring this is
`(TauCeti.isSl2Triple_single hij).isSl2TripleOrZero`, and over the zero ring `sl n R` is trivial. -/
theorem isSl2TripleOrZero_single {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]
    {i j : n} (hij : i ≠ j) :
    IsSl2TripleOrZero (SpecialLinear.singleSubSingle i j (1 : R))
      (SpecialLinear.single i j hij 1) (SpecialLinear.single j i hij.symm 1) := by
  cases subsingleton_or_nontrivial R
  · exact ⟨Subsingleton.elim .., Subsingleton.elim .., Subsingleton.elim ..⟩
  · exact (isSl2Triple_single hij).isSl2TripleOrZero

/-! ### The homomorphism of a zero-inclusive triple -/

namespace IsSl2TripleOrZero

variable (K : Type*) {L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] {h e f : L}
  (t : IsSl2TripleOrZero h e f)

/-- **The Lie algebra homomorphism of a zero-inclusive triple.** The homomorphism
`sl (Fin 2) K →ₗ⁅K⁆ L` sending the standard triple `E = E₀₁`, `F = E₁₀`, `H = E₀₀ - E₁₁` to
`e`, `f`, `h`. It is zero exactly for the zero triple
(`TauCeti.IsSl2TripleOrZero.toLieHom_eq_zero_iff`); for an `sl₂` triple `t` it is
`t.isSl2TripleOrZero.toLieHom K`. Its values are computed by
`TauCeti.IsSl2TripleOrZero.toLieHom_apply`. -/
noncomputable def toLieHom : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L :=
  lieHomOfSl2Basis (slFinTwoBasis K) (lie_slFinTwoBasis_zero_one K) (lie_slFinTwoBasis_two_zero K)
    (lie_slFinTwoBasis_two_one K) e f h t.lie_e_f (t.lie_h_e_smul K) (t.lie_lie_smul_f K)

/-- The homomorphism of a zero-inclusive triple sends the standard basis of `sl (Fin 2) K` to `e`,
`f`, `h`. -/
theorem toLieHom_slFinTwoBasis (i : Fin 3) : t.toLieHom K (slFinTwoBasis K i) = ![e, f, h] i :=
  lieHomOfSl2Basis_apply ..

/-- The homomorphism of a zero-inclusive triple sends the raising element `E₀₁` to `e`. -/
@[simp]
theorem toLieHom_single_zero_one : t.toLieHom K (SpecialLinear.single 0 1 zero_ne_one 1) = e := by
  simpa using t.toLieHom_slFinTwoBasis K 0

/-- The homomorphism of a zero-inclusive triple sends the lowering element `E₁₀` to `f`. -/
@[simp]
theorem toLieHom_single_one_zero : t.toLieHom K (SpecialLinear.single 1 0 one_ne_zero 1) = f := by
  simpa using t.toLieHom_slFinTwoBasis K 1

/-- The homomorphism of a zero-inclusive triple sends the Cartan element `E₀₀ - E₁₁` to `h`. -/
@[simp]
theorem toLieHom_singleSubSingle : t.toLieHom K (SpecialLinear.singleSubSingle 0 1 1) = h := by
  simpa using t.toLieHom_slFinTwoBasis K 2

/-- The homomorphism of a zero-inclusive triple on an arbitrary trace-zero matrix `A`: it is
`A₀₁ • e + A₁₀ • f + A₀₀ • h`. -/
theorem toLieHom_apply (A : SpecialLinear.sl (Fin 2) K) :
    t.toLieHom K A = A.val 0 1 • e + A.val 1 0 • f + A.val 0 0 • h := by
  conv_lhs => rw [eq_smul_single_add_smul_single_add_smul_singleSubSingle A zero_ne_one]
  simp

/-- **Naturality.** The homomorphism of the image of a zero-inclusive triple under a Lie algebra
homomorphism `ψ` is the composite with `ψ`. -/
theorem toLieHom_map {L' : Type*} [LieRing L'] [LieAlgebra K L'] (ψ : L →ₗ⁅K⁆ L') :
    (t.map ψ).toLieHom K = ψ.comp (t.toLieHom K) := by
  ext <;> simp

/-- The homomorphism of the standard triple of `sl (Fin 2) K` is the identity. -/
@[simp]
theorem toLieHom_isSl2TripleOrZero_single :
    (isSl2TripleOrZero_single (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).toLieHom K = LieHom.id := by
  ext <;> simp

/-- The homomorphism of the zero triple is zero. -/
@[simp]
theorem toLieHom_zero : (isSl2TripleOrZero_zero (L := L)).toLieHom K = 0 := by
  ext <;> simp

/-- The homomorphism of a zero-inclusive triple vanishes exactly for the zero triple. -/
theorem toLieHom_eq_zero_iff : t.toLieHom K = 0 ↔ h = 0 ∧ e = 0 ∧ f = 0 := by
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rw [← t.toLieHom_singleSubSingle K, h0, zero_apply]
    · rw [← t.toLieHom_single_zero_one K, h0, zero_apply]
    · rw [← t.toLieHom_single_one_zero K, h0, zero_apply]
  · rintro ⟨rfl, rfl, rfl⟩
    exact toLieHom_zero K

end IsSl2TripleOrZero

section Correspondence

variable (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L]

/-- **Zero-inclusive triples are homomorphisms out of `sl₂`.** Zero-inclusive `sl₂` triples
`(h, e, f)` in `L` correspond to Lie algebra homomorphisms `sl (Fin 2) K →ₗ⁅K⁆ L`: a triple goes to
its homomorphism `TauCeti.IsSl2TripleOrZero.toLieHom`, and a homomorphism `φ` to the image
`(φ H, φ E, φ F)` of the standard triple. -/
noncomputable def sl2TripleOrZeroEquivLieHom :
    {t : L × L × L // IsSl2TripleOrZero t.1 t.2.1 t.2.2} ≃
      (SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L) where
  toFun t := t.property.toLieHom K
  invFun φ := ⟨(φ (SpecialLinear.singleSubSingle 0 1 1), φ (SpecialLinear.single 0 1 zero_ne_one 1),
    φ (SpecialLinear.single 1 0 one_ne_zero 1)), (isSl2TripleOrZero_single zero_ne_one).map φ⟩
  left_inv t := by simp
  right_inv φ := by ext <;> simp

variable {K L}

@[simp]
theorem sl2TripleOrZeroEquivLieHom_apply
    (t : {t : L × L × L // IsSl2TripleOrZero t.1 t.2.1 t.2.2}) :
    sl2TripleOrZeroEquivLieHom K L t = t.property.toLieHom K :=
  (rfl)

@[simp]
theorem sl2TripleOrZeroEquivLieHom_symm_apply (φ : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L) :
    ((sl2TripleOrZeroEquivLieHom K L).symm φ).val =
      (φ (SpecialLinear.singleSubSingle 0 1 1), φ (SpecialLinear.single 0 1 zero_ne_one 1),
        φ (SpecialLinear.single 1 0 one_ne_zero 1)) :=
  (rfl)

end Correspondence

end TauCeti

/-- **Every homomorphism out of `sl₂` comes from a triple.** A Lie algebra homomorphism `φ` out of
`sl (Fin 2) K` is the homomorphism of the zero-inclusive triple `(φ H, φ E, φ F)`. -/
theorem LieHom.eq_toLieHom_map {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    (φ : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L) :
    φ = ((TauCeti.isSl2TripleOrZero_single (R := K) zero_ne_one).map φ).toLieHom K := by
  ext <;> simp
