/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.AlgebraicGeometry.Compactification.DenseReplacement.Basic

/-!
# Dense replacement over the dual numbers

Let `k` be a nonzero commutative ring and `f : Spec k[ε][t] ⟶ Spec k[ε]` the affine line over
the dual numbers `k[ε] = k[X]/(X²)`. Dense replacement of any compactification of `f`, for
example of `Spec k[ε][t] ⊆ ℙ¹_{k[ε]}`, takes the scheme-theoretic closure of the interior.
This keeps the square-zero structure: the coefficient `ε`, pulled back to the ambient scheme
of the dense replacement, is a nonzero section with square zero. Hence that ambient scheme is
not reduced. Replacing it by the reduced closure would kill `ε` and so change the open
subscheme `Spec k[ε][t]`.

The nonvanishing comes from `Compactification.app_p_eq_zero_iff`: over a schematically dense
interior, a section of the base vanishes on the ambient scheme exactly when it vanishes on the
source, and `ε` does not vanish in `k[ε][t]`.

## References

* The Stacks Project, Section 29.7, *Scheme theoretic closure and density* (tag 01RA).
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial DualNumber

universe u

namespace TauCeti.Compactification

variable {k : Type u} [CommRing k] [Nontrivial k]

-- The rings are named in `CommRingCat.ofHom`: unification does not otherwise find the
-- `CommRing` instance of the dual numbers from the `algebraMap` argument.
/-- Dense replacement of any compactification of the affine line over the dual numbers `k[ε]`
keeps the coefficient `ε`: its pullback to the ambient scheme is a nonzero section of square
zero. -/
theorem denseReplacement_dualNumber_section
    (C : Compactification (Spec.map (CommRingCat.ofHom (R := DualNumber k)
      (S := (DualNumber k)[X]) (algebraMap (DualNumber k) (DualNumber k)[X])))) :
    (denseReplacement C).obj.p.appTop ((Scheme.ΓSpecIso (.of (DualNumber k))).inv ε) ≠ 0 ∧
      (denseReplacement C).obj.p.appTop ((Scheme.ΓSpecIso (.of (DualNumber k))).inv ε) ^ 2 =
        0 := by
  refine ⟨fun h ↦ ?_, by rw [← map_pow, ← map_pow, pow_two, eps_mul_eps, map_zero, map_zero]⟩
  -- `appTop` is `app ⊤`, so the vanishing criterion over an arbitrary open applies.
  have h' : (Spec.map (CommRingCat.ofHom (R := DualNumber k) (S := (DualNumber k)[X])
      (algebraMap _ _))).appTop ((Scheme.ΓSpecIso (.of (DualNumber k))).inv ε) = 0 :=
    (app_p_eq_zero_iff (denseReplacement C).obj (U := ⊤) _).mp h
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    map_eq_zero_iff _ (ConcreteCategory.injective_of_mono_of_preservesPullback _)] at h'
  simpa using congrArg (fun q ↦ (q.coeff 0).snd) h'

/-- Dense replacement of any compactification of the affine line over the dual numbers has a
nonreduced ambient scheme. -/
theorem not_isReduced_denseReplacement_dualNumber
    (C : Compactification (Spec.map (CommRingCat.ofHom (R := DualNumber k)
      (S := (DualNumber k)[X]) (algebraMap (DualNumber k) (DualNumber k)[X])))) :
    ¬ IsReduced (denseReplacement C).obj.Xbar := fun _ ↦
  (denseReplacement_dualNumber_section C).1 (IsReduced.eq_zero _
    ⟨2, (denseReplacement_dualNumber_section C).2⟩)

end TauCeti.Compactification
