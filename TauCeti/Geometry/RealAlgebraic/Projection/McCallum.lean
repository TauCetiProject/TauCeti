/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.IrreducibleBasis
public import TauCeti.RingTheory.MvPolynomial.Discriminant
import TauCeti.Algebra.Polynomial.Degree.Map

/-!
# The McCallum projection set

Let `F` be a finite family of polynomials in one distinguished variable over a commutative ring
`R` with a normalized gcd, and let `B` be a basis of `F`: in McCallum's setting, a finite set of
primitive, squarefree, pairwise coprime polynomials of positive degree whose products of powers
recover the members of `F` up to their contents. The McCallum projection `F.mcCallumProjection B`
is the finite subset of `R` consisting of

* the content `f.content` of every member `f ∈ F`;
* every coefficient `b.coeff i`, `i ≤ b.natDegree`, of every member `b ∈ B`;
* the discriminant `b.discr` of every member `b ∈ B`;
* the resultant `resultant b b'` of every pair of distinct members `b, b' ∈ B`, in both orders
  (which differ only by a sign).

The intended coefficient ring is `R = MvPolynomial (Fin n) ℝ` with `B` an irreducible basis of
`F` (`Finset.IsIrreducibleBasis`). Mathlib fixes no normalization on `MvPolynomial`; any
`NormalizedGCDMonoid` structure may be chosen, and changing it changes each content only by a
unit factor.

Unlike the Collins projection `Finset.collinsProjection`, no reducta and no subresultant
coefficients beyond resultants and discriminants are taken. McCallum proves that this smaller set
suffices for lifting over a base cell on which every element of the projection is
order-invariant (rather than merely sign-invariant) and no member of the basis is nullified. The
contents are always included, so that information about the members of `F` is not lost when
passing to the basis.

The projection depends on the choice of basis only up to associates: two irreducible bases of
the same family give projections whose elements are associated to one another
(`Finset.IsIrreducibleBasis.exists_associated_mem_mcCallumProjection`). Since associated
multivariate polynomials over a field differ by a nonzero constant factor, whether every element
of the projection is sign-invariant, or order-invariant, on a set does not depend on the basis.

Specializing the base coordinates is a ring homomorphism `φ : R →+* A`. The last section shows
that the zero pattern of the projection under a specialization fixes the degrees and the
nullified members of both the basis and the family: if the same elements of the projection
vanish under `φ` and `ψ`, then every member of the basis, and every member of the family, has the
same degree after either specialization, and is nullified by `φ` exactly when it is nullified by
`ψ`.

The discriminant of the product of any subfamily of an irreducible basis has constant
ambient order wherever the projection does
(`Finset.IsIrreducibleBasis.orderAt_discr_prod_eq_of_mcCallumProjection`). Together with
`Finset.IsIrreducibleBasis.discr_prod_ne_zero`, this supplies the discriminant hypotheses
for applying a single-polynomial delineability theorem to the active basis product.

## Main definitions and results

* `Finset.mcCallumProjection`: the McCallum projection of a family with respect to a basis.
* `Finset.mem_mcCallumProjection`: the explicit description of its elements.
* `Finset.mcCallumProjection_mono`: the projection is monotone in the family and the basis.
* `Finset.IsIrreducibleBasis.exists_associated_mem_mcCallumProjection`: independence of the
  basis up to associates.
* `Finset.natDegree_map_eq_of_mcCallumProjection`, `Finset.map_eq_zero_iff_of_mcCallumProjection`:
  two specializations under which the same elements of the projection vanish give every member
  of the basis the same degree, and nullify the same members of the basis.
* `Finset.IsIrreducibleBasis.natDegree_map_eq_of_mcCallumProjection`,
  `Finset.IsIrreducibleBasis.map_eq_zero_iff_of_mcCallumProjection`: the same for the members of
  the family, when the basis is an irreducible basis.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*, in
  *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998), 242–268.
-/

public section

open Polynomial

namespace Finset

variable {R : Type*} [CommRing R] [NormalizedGCDMonoid R]

/-- The McCallum projection of the family `F` with respect to the basis `B`: the contents of the
members of `F`, together with the coefficients and discriminants of the members of `B` and the
resultants of pairs of distinct members of `B`. Resultants and discriminants are taken at the
actual degrees. -/
noncomputable def mcCallumProjection (F B : Finset R[X]) : Finset R := by
  classical
  exact F.image content ∪ (B.biUnion fun b ↦ (range (b.natDegree + 1)).image b.coeff) ∪
    B.image discr ∪ B.offDiag.image fun bb ↦ resultant bb.1 bb.2

/-- The elements of the McCallum projection: contents of members of the family, and
coefficients, discriminants and pairwise resultants of members of the basis. -/
theorem mem_mcCallumProjection {F B : Finset R[X]} {a : R} :
    a ∈ F.mcCallumProjection B ↔
      (∃ f ∈ F, f.content = a) ∨ (∃ b ∈ B, ∃ i ≤ b.natDegree, b.coeff i = a) ∨
      (∃ b ∈ B, b.discr = a) ∨ ∃ b ∈ B, ∃ b' ∈ B, b ≠ b' ∧ resultant b b' = a := by
  classical
  simp only [mcCallumProjection, mem_union, mem_biUnion, mem_image, mem_range, Nat.lt_succ_iff,
    mem_offDiag, Prod.exists, or_assoc]
  grind

variable {F F' B B' : Finset R[X]} {f b b' : R[X]}

/-- The content of every member of the family lies in the McCallum projection. -/
theorem content_mem_mcCallumProjection (hf : f ∈ F) : f.content ∈ F.mcCallumProjection B :=
  mem_mcCallumProjection.2 <| .inl ⟨f, hf, rfl⟩

/-- Every coefficient of a member of the basis, up to its degree, lies in the McCallum
projection. -/
theorem coeff_mem_mcCallumProjection (hb : b ∈ B) {i : ℕ} (hi : i ≤ b.natDegree) :
    b.coeff i ∈ F.mcCallumProjection B :=
  mem_mcCallumProjection.2 <| .inr <| .inl ⟨b, hb, i, hi, rfl⟩

/-- The discriminant of every member of the basis lies in the McCallum projection. -/
theorem discr_mem_mcCallumProjection (hb : b ∈ B) : b.discr ∈ F.mcCallumProjection B :=
  mem_mcCallumProjection.2 <| .inr <| .inr <| .inl ⟨b, hb, rfl⟩

/-- The resultant of two distinct members of the basis lies in the McCallum projection. -/
theorem resultant_mem_mcCallumProjection (hb : b ∈ B) (hb' : b' ∈ B) (hne : b ≠ b') :
    resultant b b' ∈ F.mcCallumProjection B :=
  mem_mcCallumProjection.2 <| .inr <| .inr <| .inr ⟨b, hb, b', hb', hne, rfl⟩

/-- With the empty basis, the McCallum projection consists of the contents of the family. -/
@[simp]
theorem mcCallumProjection_empty_right [DecidableEq R] :
    F.mcCallumProjection ∅ = F.image content := by
  ext a
  simp [mem_mcCallumProjection, eq_comm]

/-- Enlarging the family or the basis enlarges the McCallum projection. -/
@[gcongr]
theorem mcCallumProjection_mono (hF : F ⊆ F') (hB : B ⊆ B') :
    F.mcCallumProjection B ⊆ F'.mcCallumProjection B' := by
  intro a ha
  rw [mem_mcCallumProjection] at ha ⊢
  rcases ha with ⟨f, hf, rfl⟩ | ⟨b, hb, i, hi, rfl⟩ | ⟨b, hb, rfl⟩ |
    ⟨b, hb, b', hb', hne, rfl⟩
  · exact .inl ⟨f, hF hf, rfl⟩
  · exact .inr <| .inl ⟨b, hB hb, i, hi, rfl⟩
  · exact .inr <| .inr <| .inl ⟨b, hB hb, rfl⟩
  · exact .inr <| .inr <| .inr ⟨b, hB hb, b', hB hb', hne, rfl⟩

/-! ### Independence of the basis -/

namespace IsIrreducibleBasis

variable [IsDomain R] [UniqueFactorizationMonoid R]

/-- **Independence of the basis.** For two irreducible bases `B` and `B'` of the same family,
every element of the McCallum projection with respect to `B'` is associated to an element of the
McCallum projection with respect to `B`. -/
theorem exists_associated_mem_mcCallumProjection (hB : F.IsIrreducibleBasis B)
    (hB' : F.IsIrreducibleBasis B') {a : R} (ha : a ∈ F.mcCallumProjection B') :
    ∃ a' ∈ F.mcCallumProjection B, Associated a a' := by
  rcases mem_mcCallumProjection.1 ha with ⟨f, hf, rfl⟩ | ⟨b', hb', i, hi, rfl⟩ | ⟨b', hb', rfl⟩ |
    ⟨b₁', hb₁', b₂', hb₂', hne, rfl⟩
  · exact ⟨_, content_mem_mcCallumProjection hf, .refl _⟩
  · obtain ⟨b, hb, r, hr, rfl⟩ := hB'.exists_eq_C_mul hB hb'
    rw [natDegree_C_mul_of_isUnit hr] at hi
    exact ⟨_, coeff_mem_mcCallumProjection hb hi, by
      rw [coeff_C_mul]; exact associated_unit_mul_left _ _ hr⟩
  · obtain ⟨b, hb, h⟩ := hB'.exists_associated_discr hB hb'
    exact ⟨_, discr_mem_mcCallumProjection hb, h⟩
  · obtain ⟨b₁, hb₁, b₂, hb₂, hne', h⟩ := hB'.exists_associated_resultant hB hb₁' hb₂' hne
    exact ⟨_, resultant_mem_mcCallumProjection hb₁ hb₂ hne', h⟩

end IsIrreducibleBasis

/-! ### Specialization

Throughout, `φ` and `ψ` are two specializations under which the same elements of the McCallum
projection vanish. The statements about the basis hold for specializations into arbitrary
commutative rings; the statements about the family are over domains. -/

section Specialization

variable {A A' : Type*} [CommRing A] [CommRing A'] {φ : R →+* A} {ψ : R →+* A'}

/-- If the same elements of the McCallum projection vanish under `φ` and `ψ`, then a member of the
basis is nullified by `φ` exactly when it is nullified by `ψ`. -/
theorem map_eq_zero_iff_of_mcCallumProjection
    (h : ∀ a ∈ F.mcCallumProjection B, φ a = 0 ↔ ψ a = 0) (hb : b ∈ B) :
    b.map φ = 0 ↔ b.map ψ = 0 :=
  map_eq_zero_iff_of_map_coeff_eq_zero_iff fun _ hi ↦ h _ (coeff_mem_mcCallumProjection hb hi)

/-- If the same elements of the McCallum projection vanish under `φ` and `ψ`, then every member of
the basis has the same degree after either specialization. -/
theorem natDegree_map_eq_of_mcCallumProjection
    (h : ∀ a ∈ F.mcCallumProjection B, φ a = 0 ↔ ψ a = 0) (hb : b ∈ B) :
    (b.map φ).natDegree = (b.map ψ).natDegree :=
  natDegree_map_eq_of_map_coeff_eq_zero_iff fun _ hi ↦ h _ (coeff_mem_mcCallumProjection hb hi)

namespace IsIrreducibleBasis

variable [IsDomain R] [UniqueFactorizationMonoid R] [IsDomain A] [IsDomain A']

/-- If the same elements of the McCallum projection vanish under specializations `φ` and `ψ` into
domains, then a member of the family is nullified by `φ` exactly when it is nullified by `ψ`. -/
theorem map_eq_zero_iff_of_mcCallumProjection (hB : F.IsIrreducibleBasis B)
    (h : ∀ a ∈ F.mcCallumProjection B, φ a = 0 ↔ ψ a = 0) (hf : f ∈ F) :
    f.map φ = 0 ↔ f.map ψ = 0 := by
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  have hc : φ (f.content * u) = 0 ↔ ψ (f.content * u) = 0 := by
    simpa [(u.isUnit.map φ).ne_zero, (u.isUnit.map ψ).ne_zero] using
      h _ (content_mem_mcCallumProjection hf)
  generalize f.content * u = c at hfe hc
  subst hfe
  simp only [Polynomial.map_mul, map_C, Polynomial.map_prod, Polynomial.map_pow, mul_eq_zero,
    C_eq_zero, prod_eq_zero_iff, pow_eq_zero_iff', hc]
  exact or_congr_right <| exists_congr fun b ↦ and_congr_right fun hb ↦
    and_congr_left fun _ ↦ Finset.map_eq_zero_iff_of_mcCallumProjection h hb

/-- If the same elements of the McCallum projection vanish under specializations `φ` and `ψ` into
domains, then every member of the family has the same degree after either specialization. -/
theorem natDegree_map_eq_of_mcCallumProjection (hB : F.IsIrreducibleBasis B)
    (h : ∀ a ∈ F.mcCallumProjection B, φ a = 0 ↔ ψ a = 0) (hf : f ∈ F) :
    (f.map φ).natDegree = (f.map ψ).natDegree := by
  rcases eq_or_ne (f.map ψ) 0 with h0 | h0
  · simp [h0, (hB.map_eq_zero_iff_of_mcCallumProjection h hf).2 h0]
  have h0' := (hB.map_eq_zero_iff_of_mcCallumProjection h hf).not.2 h0
  obtain ⟨u, e, hfe⟩ := hB.exists_eq_C_content_mul_unit_mul_prod hf
  generalize f.content * u = c at hfe
  subst hfe
  simp only [Polynomial.map_mul, map_C, Polynomial.map_prod, Polynomial.map_pow] at h0 h0' ⊢
  -- neither specialization vanishes, so each degree is the weighted sum of the degrees of the
  -- specialized members of the basis
  rw [natDegree_mul (left_ne_zero_of_mul h0') (right_ne_zero_of_mul h0'),
    natDegree_mul (left_ne_zero_of_mul h0) (right_ne_zero_of_mul h0), natDegree_C, natDegree_C,
    natDegree_prod _ _ fun b hb ↦
      ne_zero_of_dvd_ne_zero (right_ne_zero_of_mul h0') (dvd_prod_of_mem _ hb),
    natDegree_prod _ _ fun b hb ↦
      ne_zero_of_dvd_ne_zero (right_ne_zero_of_mul h0) (dvd_prod_of_mem _ hb)]
  simp only [natDegree_pow, zero_add]
  exact sum_congr rfl fun b hb ↦ by rw [Finset.natDegree_map_eq_of_mcCallumProjection h hb]

end IsIrreducibleBasis

end Specialization

end Finset

namespace Finset

variable {σ R : Type*} [CommRing R] [IsDomain R]
  [NormalizedGCDMonoid (MvPolynomial σ R)]
  {F B A : Finset (Polynomial (MvPolynomial σ R))}

/-- The McCallum projection determines the ambient order of the discriminant of the
product of any subfamily of the basis. In particular, order-invariance of the projection
supplies the constant-order hypothesis of the discriminant theorem for this product.
The formal discriminant may vanish at both base points; no nonvanishing of its values or
of specialized leading coefficients is assumed. -/
theorem IsIrreducibleBasis.orderAt_discr_prod_eq_of_mcCallumProjection
    (hB : F.IsIrreducibleBasis B) (hA : A ⊆ B) (a b : σ → R)
    (h : ∀ p ∈ F.mcCallumProjection B, p.orderAt a = p.orderAt b) :
    (∏ p ∈ A, p).discr.orderAt a = (∏ p ∈ A, p).discr.orderAt b := by
  exact Finset.orderAt_discr_prod_eq A id
    (fun p hp ↦ hB.natDegree_pos p (hA hp)) a b
    (fun p hp ↦ h _ (discr_mem_mcCallumProjection (hA hp)))
    (fun p hp q hq hne ↦ h _ (resultant_mem_mcCallumProjection (hA hp) (hA hq) hne))

end Finset
