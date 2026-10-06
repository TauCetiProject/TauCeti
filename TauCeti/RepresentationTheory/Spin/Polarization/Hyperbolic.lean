/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.Submodule.Prod
public import TauCeti.RepresentationTheory.Spin.Polarization.Basic

/-!
# The split polarization of a hyperbolic quadratic space

`TauCeti.SpinPolarizationData.ofNondegenerate` produces polarization data for any
finite-dimensional nondegenerate quadratic space over a separably closed field, but it does so by
normalizing an arbitrary form, so its two isotropic summands are not given by a formula. A
construction that has to exhibit the carrier of the spin representation explicitly needs the split
case written down instead.

This file writes it down. For a module `M` over a commutative ring `K`, Mathlib's
`QuadraticForm.dualProd K M` is the hyperbolic form `Q (f, m) = f m` on `Module.Dual K M × M`, and
its two coordinate summands `Submodule.snd` and `Submodule.fst` are isotropic and dually paired by
construction:

```text
polar Q (f, m) (g, x) = f x + g m.
```

`TauCeti.SpinPolarizationData.hyperbolic` packages them as a `TauCeti.SpinPolarizationData`, with
the copy of `M` as the exterior summand `W`, the copy of its dual as the contraction summand `W'`,
and no orthogonal remainder, so the spinor module attached to it is the full exterior algebra of
`M`. The only hypothesis is that the evaluation map `Module.Dual.eval K M` into the double dual is
injective, that is, that the functionals on `M` separate its points. This ensures that the polar
pairing has trivial left radical; by `Module.eval_apply_injective` it holds for every projective
module, in particular over a field. The identification of `W'` with the dual of `W` needs no such
hypothesis.

Nothing here constructs a Clifford action, a Lie algebra or a group: this file supplies the
decomposition data those constructions take as input, and it asserts nothing about the quadratic
space beyond the fields of the structure and the nondegeneracy they imply.

## Main definitions

* `TauCeti.SpinPolarizationData.hyperbolic`: the polarization data of `QuadraticForm.dualProd`.
* `TauCeti.SpinPolarizationData.hyperbolicBasis`: the basis of the exterior summand transported
  from a basis of `M`.

## Main results

* `TauCeti.SpinPolarizationData.hyperbolic_W`, `hyperbolic_W'` and `hyperbolic_line`: the summands
  of the constructed data.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II, for the exterior model attached to
  a split decomposition.
* N. Bourbaki, *Algèbre*, Chapter 9, §4, for hyperbolic quadratic spaces.
-/

public section

open QuadraticMap

namespace TauCeti

universe u v w

variable {K : Type u} [CommRing K] {M : Type v} [AddCommGroup M] [Module K M]

namespace SpinPolarizationData

/-! ## The polarization data -/

/-- **The split polarization of a hyperbolic quadratic space.** For a module `M` over a commutative
ring `K` whose functionals separate points, the hyperbolic form `Q (f, m) = f m` on
`Module.Dual K M × M` is polarized by its two coordinate summands, with no orthogonal remainder.

The exterior summand `W` is the copy of `M` and the contraction summand `W'` is the copy of its
dual, so the spinor module attached to this datum is the full exterior algebra of `M`. -/
noncomputable def hyperbolic (hM : Function.Injective (Module.Dual.eval K M)) :
    SpinPolarizationData (QuadraticForm.dualProd K M) where
  W := Submodule.snd K (Module.Dual K M) M
  W' := Submodule.fst K (Module.Dual K M) M
  line := ⊥
  decompositionEquiv := LinearEquiv.prodUnique ≪≫ₗ
    Submodule.prodEquivOfIsCompl _ _ (Submodule.isCompl_fst_snd K (Module.Dual K M) M).symm
  decompositionEquiv_apply x := by
    rw [LinearEquiv.trans_apply, LinearEquiv.prodUnique_apply, Submodule.coe_prodEquivOfIsCompl',
      (Submodule.mem_bot K).mp x.2.2, add_zero]
  isotropic_W x := by
    rw [QuadraticForm.dualProd_apply, Submodule.mem_snd_iff.mp x.2, LinearMap.zero_apply]
  isotropic_W' y := by
    rw [QuadraticForm.dualProd_apply, Submodule.mem_fst_iff.mp y.2, map_zero]
  pairingEquiv :=
    (Submodule.fstEquiv K (Module.Dual K M) M) ≪≫ₗ
      (Submodule.sndEquiv K (Module.Dual K M) M).dualMap
  pairingEquiv_apply y x := by
    rw [polar_dualProd, Submodule.mem_snd_iff.mp x.2, LinearMap.zero_apply, zero_add,
      LinearEquiv.trans_apply, LinearEquiv.dualMap_apply, Submodule.fstEquiv_apply,
      Submodule.sndEquiv_apply]
  pairing_separatingLeft x hx := by
    refine Subtype.ext (Prod.ext (Submodule.mem_snd_iff.mp x.2)
      ((injective_iff_map_eq_zero _).mp hM _ (LinearMap.ext fun f => ?_)))
    have := hx ⟨(f, 0), Submodule.mem_fst_iff.mpr rfl⟩
    rwa [polar_dualProd, Submodule.mem_snd_iff.mp x.2, LinearMap.zero_apply, zero_add] at this
  lineCoordinate := 0
  lineCoordinate_injective a b _ := Subsingleton.elim a b
  lineCoordinate_sq z := by
    rw [Subsingleton.elim z 0, map_zero, mul_zero, ZeroMemClass.coe_zero, map_zero]
  line_orthogonal_W z x := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]
  line_orthogonal_W' z y := by
    rw [Subsingleton.elim z 0, ZeroMemClass.coe_zero, polar_zero_left]

variable (hM : Function.Injective (Module.Dual.eval K M))

@[simp]
theorem hyperbolic_W : (hyperbolic hM).W = Submodule.snd K (Module.Dual K M) M :=
  -- `(rfl)`, not `rfl`: the body of `hyperbolic` is not `@[expose]`d.
  (rfl)

@[simp]
theorem hyperbolic_W' : (hyperbolic hM).W' = Submodule.fst K (Module.Dual K M) M := (rfl)

@[simp]
theorem hyperbolic_line : (hyperbolic hM).line = ⊥ := (rfl)

/-! ## The basis of the exterior summand -/

section Basis

variable {R : Type u} [CommSemiring R] {N : Type v} [AddCommMonoid N] [Module R N]

/-- A basis of `N` transported to its coordinate copy in `Module.Dual R N × N`. Over a
commutative ring this is a basis of the exterior summand of the hyperbolic polarization, by
`TauCeti.SpinPolarizationData.hyperbolic_W`. The transport itself only needs a commutative
semiring. -/
noncomputable def hyperbolicBasis {ι : Type w} (b : Module.Basis ι R N) :
    Module.Basis ι R (Submodule.snd R (Module.Dual R N) N) :=
  b.map (Submodule.sndEquiv R (Module.Dual R N) N).symm

@[simp]
theorem coe_hyperbolicBasis_apply {ι : Type w} (b : Module.Basis ι R N) (i : ι) :
    ((hyperbolicBasis b i : Submodule.snd R (Module.Dual R N) N) : Module.Dual R N × N) =
      (0, b i) := by
  rw [hyperbolicBasis, Module.Basis.map_apply, Submodule.sndEquiv_symm_apply_coe]

end Basis

end SpinPolarizationData

end TauCeti
