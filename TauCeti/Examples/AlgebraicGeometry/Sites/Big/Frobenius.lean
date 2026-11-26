/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import TauCeti.AlgebraicGeometry.Frobenius.Iterate
public import TauCeti.AlgebraicGeometry.Sites.Big.Frobenius

/-!
# Example: the Frobenius of `𝔾_a` over `𝔽_p` is not linear

Over `S = Spec 𝔽_p`, the `p`-th power map is natural and additive on every test scheme, so it is
an endomorphism of `𝔾_a` (`AlgebraicGeometry.Scheme.gaFrobenius`). On the test scheme
`𝔸¹_{𝔽_p} = Spec 𝔽_p[t]` it fixes `1` but sends the coordinate `t` to `t ^ p ≠ t`, so it is not
linear over `𝔽_p[t]`, and no endomorphism of the unit module over the big structure sheaf is the
Frobenius of `𝔾_a`.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme Polynomial

namespace TauCeti.AlgebraicGeometry.gaFrobeniusExample

variable (p : ℕ) [Fact p.Prime]

/-- The affine line `𝔸¹_{𝔽_p} = Spec 𝔽_p[t]` as a test scheme over `Spec 𝔽_p`. -/
noncomputable abbrev affineLine : Over (Spec (.of (ZMod p))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ZMod p)[X])))

/-- The coordinate `t` of `𝔸¹_{𝔽_p}`, as a global function. -/
noncomputable abbrev coordinate : Γ((affineLine p).left, ⊤) :=
  (ΓSpecIso (.of (ZMod p)[X])).inv X

/-- The Frobenius of `𝔾_a` over `Spec 𝔽_p`. -/
noncomputable abbrev frobenius : Ga (Spec (.of (ZMod p))) ⟶ Ga (Spec (.of (ZMod p))) :=
  gaFrobenius _ (natCast_spec_eq_zero (CommRingCat.of (ZMod p)))

/-- The Frobenius of `𝔾_a` fixes the function `1` on `𝔸¹_{𝔽_p}`. -/
example : (frobenius p).hom.app (op (affineLine p)) (1 : Γ((affineLine p).left, ⊤)) =
    (1 : Γ((affineLine p).left, ⊤)) :=
  (gaFrobenius_app_apply _ _ _ _).trans (one_pow (M := Γ((affineLine p).left, ⊤)) p)

/-- The coordinate `t` of `𝔸¹_{𝔽_p}` satisfies `t ^ p ≠ t`. -/
theorem coordinate_pow_ne : coordinate p ^ p ≠ coordinate p := by
  rw [← map_pow, Ne, (ConcreteCategory.bijective_of_isIso
    (ΓSpecIso (CommRingCat.of (ZMod p)[X])).inv).injective.eq_iff]
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow, natDegree_X] at this
  exact (Fact.out : p.Prime).one_lt.ne' this

/-- The Frobenius of `𝔾_a` sends the coordinate `t` of `𝔸¹_{𝔽_p}` to `t ^ p ≠ t`. -/
example : (frobenius p).hom.app (op (affineLine p)) (coordinate p) ≠ coordinate p :=
  (gaFrobenius_app_apply _ _ _ _).trans_ne (coordinate_pow_ne p)

/-- The Frobenius of `𝔾_a` over `Spec 𝔽_p` is not linear over the big structure sheaf: no
endomorphism of the unit module is the `p`-th power map on every test scheme. -/
example : ¬ ∃ φ : SheafOfModules.unit (bigRingCatSheaf (Spec (.of (ZMod p)))) ⟶
      SheafOfModules.unit (bigRingCatSheaf (Spec (.of (ZMod p)))),
    ∀ (T : Over (Spec (.of (ZMod p)))) (a : Γ(T.left, ⊤)), φ.val.app (op T) a = a ^ p :=
  not_exists_unit_hom_app_eq_pow (coordinate_pow_ne p)

end TauCeti.AlgebraicGeometry.gaFrobeniusExample
