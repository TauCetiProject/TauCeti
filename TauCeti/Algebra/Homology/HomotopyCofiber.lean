/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The mapping cone of a split monomorphism of complexes

Let `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short complex of homological complexes which is split in the
category of complexes: the retraction `r : X₂ ⟶ X₁` of `f` and the section `s : X₃ ⟶ X₂` of `g`
are chain maps. Then the mapping cone `homotopyCofiber f` of `f` is homotopy equivalent to the
cokernel `X₃`. The map from the cone is `homotopyCofiber.desc f g`, which exists because
`f ≫ g = 0`, and its homotopy inverse is `s` followed by the inclusion `homotopyCofiber.inr f` of
`X₂` into the cone. One composite is `s ≫ g = 𝟙`, and the other is homotopic to the identity
through the homotopy which sends the `X₂`-summand of the cone to its `X₁`-summand by `-r`.

We assume, as Mathlib's `homotopyCofiber.inrCompHomotopy` does, that every index of the complex
shape is the target of some relation. This holds for `ComplexShape.up ℤ`, `ComplexShape.down ℤ`
and the one-object shape `ComplexShape.refl Unit`.

The motivating example is multiplication by `X - a` on the polynomial extension `A[X] ⊗[A] K` of
a complex `K` of `A`-modules, split by division by `X - a` and by the constant polynomials (see
`TauCeti.Algebra.Homology.PolynomialExtension`). This is how the stabilization invariance of grid
homology compares a grid complex with the mapping cone of `V₁ - V₂`.

## Main definitions

* `CategoryTheory.ShortComplex.Splitting.homotopyCofiberHomotopyEquiv`: the homotopy equivalence
  between the mapping cone of `S.f` and `S.X₃` for a split short complex of complexes `S`.

## Main results

* `CategoryTheory.ShortComplex.Splitting.quasiIso_homotopyCofiberDesc`: the map from the mapping
  cone of `S.f` to `S.X₃` induced by `S.g` is a quasi-isomorphism.

## References

* C. A. Weibel, *An introduction to homological algebra*, Section 1.5.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, Section 5.2.
-/

public section

open CategoryTheory Category HomologicalComplex

namespace CategoryTheory.ShortComplex.Splitting

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι} [DecidableRel c.Rel]
  {S : ShortComplex (HomologicalComplex C c)} (σ : S.Splitting) [HasHomotopyCofiber S.f]
  (hc : ∀ j, ∃ i, c.Rel i j)

/-- For a short complex of complexes `S` split by chain maps, the mapping cone of `S.f` is
homotopy equivalent to `S.X₃`. The map from the cone is induced by `S.g`, and its homotopy inverse
is the section `σ.s` followed by the inclusion of `S.X₂` into the cone. -/
noncomputable def homotopyCofiberHomotopyEquiv :
    _root_.HomotopyEquiv (homotopyCofiber S.f) S.X₃ where
  hom := homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero)
  inv := σ.s ≫ homotopyCofiber.inr S.f
  homotopyInvHomId := _root_.Homotopy.ofEq (by simp)
  -- On the `X₂`-summand of the cone, the homotopy is `-r` into the `X₁`-summand.
  homotopyHomInvId.hom i j := if hij : c.Rel j i then
      -(homotopyCofiber.sndX S.f i ≫ σ.r.f i ≫ homotopyCofiber.inlX S.f i j hij) else 0
  homotopyHomInvId.zero _ _ hij := dite_eq_right hij
  homotopyHomInvId.comm j := by
    obtain ⟨i, hij⟩ := hc j
    have hfr (k : ι) : S.f.f k ≫ σ.r.f k = 𝟙 _ := by
      rw [← comp_f, σ.f_r, id_f]
    have hrf : σ.r.f j ≫ S.f.f j = 𝟙 _ - S.g.f j ≫ σ.s.f j := by
      simpa using congrArg (fun φ ↦ φ.f j) σ.r_f
    rw [prevD_eq _ hij, dite_eq_left hij]
    by_cases hj : c.Rel j (c.next j)
    · rw [dNext_eq _ hj, dite_eq_left hj]
      apply homotopyCofiber.ext_from_X S.f (c.next j) j hj
      · simp [homotopyCofiber.desc_f _ _ _ _ _ hj, homotopyCofiber.d_sndX_assoc _ _ _ hj,
          reassoc_of% hfr]
      · simp [homotopyCofiber.desc_f _ _ _ _ _ hj, homotopyCofiber.inlX_d S.f i j _ hij hj,
          homotopyCofiber.d_sndX_assoc _ _ _ hj, reassoc_of% hrf]
    · rw [dNext_eq_zero _ _ hj, zero_add]
      apply homotopyCofiber.ext_from_X' S.f j hj
      simp [homotopyCofiber.desc_f' _ _ _ _ hj, homotopyCofiber.inlX_d' S.f i j hij hj,
        reassoc_of% hrf]

/-- The map from the mapping cone in `homotopyCofiberHomotopyEquiv` is induced by `S.g`. -/
@[simp]
theorem homotopyCofiberHomotopyEquiv_hom :
    (σ.homotopyCofiberHomotopyEquiv hc).hom =
      homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero) :=
  (rfl)

/-- The homotopy inverse in `homotopyCofiberHomotopyEquiv` is the section `σ.s` followed by the
inclusion of `S.X₂` into the mapping cone. -/
@[simp]
theorem homotopyCofiberHomotopyEquiv_inv :
    (σ.homotopyCofiberHomotopyEquiv hc).inv = σ.s ≫ homotopyCofiber.inr S.f :=
  (rfl)

include σ hc in
/-- For a short complex of complexes `S` split by chain maps, the map from the mapping cone of
`S.f` to `S.X₃` induced by `S.g` is a quasi-isomorphism. -/
theorem quasiIso_homotopyCofiberDesc [∀ i, (homotopyCofiber S.f).HasHomology i]
    [∀ i, S.X₃.HasHomology i] :
    _root_.QuasiIso (homotopyCofiber.desc S.f S.g (_root_.Homotopy.ofEq S.zero)) :=
  σ.homotopyCofiberHomotopyEquiv_hom hc ▸ (σ.homotopyCofiberHomotopyEquiv hc).quasiIso_hom

end CategoryTheory.ShortComplex.Splitting
