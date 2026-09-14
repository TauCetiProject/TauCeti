/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Radical API for quadratic forms

This file records basic properties of the radical of a quadratic form (such as its invariance under
negation and orthogonal products) and general consequences of nondegeneracy, together with the two
facts about the
quadratic form `x ↦ B x x` of a *symmetric* bilinear form `B` that a Clifford construction consumes:
its polar form is `2 • B`, and nondegeneracy passes from `B` to it as soon as `2` is invertible.

Over a field in which `2` is invertible, a subspace on which the form is nondegenerate is
complementary to its orthogonal complement for the polar form, and that complement carries a
nondegenerate form again as soon as the ambient form is nondegenerate. These are the two criteria
that produce the hypothesis of `QuadraticMap.IsometryEquiv.prodRestrictOrthogonal`, so that a
regular subspace splits off as an orthogonal summand.

## Main results

* `QuadraticMap.radical_neg`: negating a quadratic map does not change its radical.
* `QuadraticMap.radical_prod`: the radical of an orthogonal product is the product of the radicals.
* `QuadraticMap.isSymm_polarBilin`: the polar form is symmetric.
* `QuadraticMap.polarBilin_restrict`: the polar form of a restriction is the restricted polar form.
* `QuadraticMap.IsometryEquiv.nondegenerate`: nondegeneracy transfers along an isometry.
* `QuadraticMap.isCompl_orthogonal_of_restrict_nondegenerate`: a subspace carrying a nondegenerate
  restriction is complementary to its orthogonal complement.
* `QuadraticMap.nondegenerate_restrict_orthogonal`: that complement carries a nondegenerate
  restriction in turn.
* `QuadraticMap.Nondegenerate.prod`: nondegeneracy passes to an orthogonal product.
* `QuadraticMap.Nondegenerate.ne_zero`: a nondegenerate quadratic form on a nontrivial module is
  nonzero.
* `TauCeti.nondegenerate_of_span_singleton_eq_top`: a form on a line is nondegenerate when it is
  nonzero on a spanning vector.
* `QuadraticMap.Anisotropic.radical_eq_bot`: an anisotropic quadratic map has trivial radical.
* `QuadraticMap.Anisotropic.nondegenerate`: an anisotropic quadratic map is nondegenerate when
  `2` is invertible.
* `LinearMap.BilinMap.polarBilin_toQuadraticMap_of_flip`: the polar form of the quadratic form of a
  symmetric bilinear form `B` is `2 • B`.
* `LinearMap.BilinForm.radical_toQuadraticMap`: the radical of the quadratic form of a symmetric
  bilinear form `B` equals the kernel of `B`.
* `LinearMap.BilinForm.Nondegenerate.toQuadraticMap`: over a ring in which `2` is invertible, the
  quadratic form of a nondegenerate symmetric bilinear form is nondegenerate.
-/

public section

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

/-- Negating a quadratic map does not change its radical. -/
@[simp]
theorem radical_neg (Q : QuadraticMap R M P) : (-Q).radical = Q.radical := by
  ext x
  simp only [QuadraticMap.mem_radical_iff', neg_apply, neg_eq_zero, neg_inj]

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- The radical of an orthogonal product is the product of the two radicals when two is
invertible. -/
@[simp]
theorem radical_prod [Invertible (2 : R)] (Q : QuadraticMap R M P) (Q' : QuadraticMap R M' P) :
    (Q.prod Q').radical = Q.radical.prod Q'.radical := by
  rw [radical_eq_ker_polarBilin, radical_eq_ker_polarBilin, radical_eq_ker_polarBilin]
  ext p
  simp only [Submodule.mem_prod, LinearMap.mem_ker, LinearMap.ext_iff,
    LinearMap.zero_apply]
  constructor
  · intro hp
    exact ⟨fun x ↦ by simpa using hp (x, 0), fun x ↦ by simpa using hp (0, x)⟩
  · rintro ⟨hp, hp'⟩ x
    simpa using congrArg₂ (· + ·) (hp x.1) (hp' x.2)

/-- The polar form of a quadratic form is symmetric. -/
theorem isSymm_polarBilin (Q : QuadraticForm R M) :
    LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨fun x y => polar_comm Q x y⟩

/-- The polar form of the restriction of a quadratic form to a submodule is the restriction of its
polar form. -/
@[simp]
theorem polarBilin_restrict (Q : QuadraticForm R M) (W : Submodule R M) :
    (Q.restrict W).polarBilin = LinearMap.BilinForm.restrict Q.polarBilin W := by
  ext x y
  rfl

/-- Nondegeneracy transfers along an isometry. -/
theorem IsometryEquiv.nondegenerate {Q : QuadraticForm R M}
    {Q' : QuadraticForm R M'} (e : Q.IsometryEquiv Q') (hQ : Q.Nondegenerate) :
    Q'.Nondegenerate := by
  constructor
  · rw [← e.map_radical, hQ.radical_eq_bot, Submodule.map_bot]
  · have hpolar (x y : M) : Q'.polarBilin (e.toLinearEquiv x) (e.toLinearEquiv y) =
        Q.polarBilin x y := by
      simp only [QuadraticMap.polarBilin_apply_apply]
      change QuadraticMap.polar Q' (e.toIsometry x) (e.toIsometry y) = _
      exact e.toIsometry.polar_apply x y
    have hker : Q.polarBilin.ker.map e.toLinearMap = Q'.polarBilin.ker := by
      ext y
      obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
      constructor
      · rintro ⟨z, hz, hezx⟩
        have hzx : z = x := e.toLinearEquiv.injective hezx
        subst z
        change Q.polarBilin x = 0 at hz
        change Q'.polarBilin (e.toLinearEquiv x) = 0
        ext z
        obtain ⟨w, rfl⟩ := e.toLinearEquiv.surjective z
        rw [hpolar]
        simpa only [LinearMap.zero_apply] using congrArg (fun f : M →ₗ[R] R => f w) hz
      · intro hx
        refine ⟨x, ?_, rfl⟩
        change Q'.polarBilin (e.toLinearEquiv x) = 0 at hx
        change Q.polarBilin x = 0
        ext w
        have hw := congrArg (fun f : M' →ₗ[R] R => f (e.toLinearEquiv w)) hx
        rw [← hpolar]
        simpa only [LinearMap.zero_apply] using hw
    rw [← hker, ← Cardinal.lift_le_one_iff, e.toLinearEquiv.lift_rank_map_eq]
    exact Cardinal.lift_le_one_iff.mpr hQ.rank_rad_polar_le

section Field

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- A subspace on which a quadratic form restricts to a nondegenerate form is complementary to its
orthogonal complement for the polar form. -/
theorem isCompl_orthogonal_of_restrict_nondegenerate (Q : QuadraticForm K V)
    {W : Submodule K V} (hW : (Q.restrict W).Nondegenerate) :
    IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W) :=
  LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate (isSymm_polarBilin Q).isRefl
    (polarBilin_restrict Q W ▸ nondegenerate_polar_iff.mpr hW)

/-- The orthogonal complement of a subspace carrying a nondegenerate restriction carries a
nondegenerate restriction in turn, provided the ambient form is nondegenerate. -/
theorem nondegenerate_restrict_orthogonal {Q : QuadraticForm K V} (hQ : Q.Nondegenerate)
    {W : Submodule K V} (hW : (Q.restrict W).Nondegenerate) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).Nondegenerate := by
  have hrefl := (isSymm_polarBilin Q).isRefl
  have key : LinearMap.BilinForm.Nondegenerate (LinearMap.BilinForm.restrict Q.polarBilin
      (LinearMap.BilinForm.orthogonal Q.polarBilin W)) := by
    rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hrefl,
      LinearMap.BilinForm.orthogonal_orthogonal (nondegenerate_polar_iff.mpr hQ) hrefl]
    exact (isCompl_orthogonal_of_restrict_nondegenerate Q hW).symm
  rw [← polarBilin_restrict] at key
  exact nondegenerate_polar_iff.mp key

end Field

end QuadraticMap

namespace QuadraticMap.Nondegenerate

variable {R M M' P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P]

/-- The orthogonal product of two nondegenerate quadratic maps is nondegenerate, when `2` is
invertible in the coefficient ring. -/
theorem prod [Invertible (2 : R)] {Q : QuadraticMap R M P} {Q' : QuadraticMap R M' P}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) : (Q.prod Q').Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_prod,
    hQ.radical_eq_bot, hQ'.radical_eq_bot, Submodule.prod_bot]

/-- A nondegenerate quadratic form on a nontrivial module is nonzero. -/
theorem ne_zero [Nontrivial M] {Q : QuadraticForm R M} (hQ : Q.Nondegenerate) : Q ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have hm : v ∈ Q.radical := by
    rw [hzero, QuadraticMap.mem_radical_iff']
    simp
  rwa [hQ.radical_eq_bot, Submodule.mem_bot] at hm

end QuadraticMap.Nondegenerate

namespace QuadraticMap.Anisotropic

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

/-- An anisotropic quadratic map has trivial radical. -/
theorem radical_eq_bot {Q : QuadraticMap R M P} (hQ : Q.Anisotropic) : Q.radical = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  exact hQ v (QuadraticMap.mem_radical_iff'.mp hv).1

/-- An anisotropic quadratic map is nondegenerate when `2` is invertible. -/
theorem nondegenerate [Invertible (2 : R)] {Q : QuadraticMap R M P}
    (hQ : Q.Anisotropic) : Q.Nondegenerate :=
  QuadraticMap.nondegenerate_iff_radical_eq_bot.mpr hQ.radical_eq_bot

end QuadraticMap.Anisotropic

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- **The polar form of the quadratic form of a symmetric bilinear form `B` is `2 • B`.** The polar
form is `B + B.flip`, so symmetry collapses it. -/
theorem BilinMap.polarBilin_toQuadraticMap_of_flip {B : LinearMap.BilinMap R M N}
    (hB : LinearMap.flip B = B) :
    QuadraticMap.polarBilin B.toQuadraticMap = (2 : R) • B := by
  rw [BilinMap.polarBilin_toQuadraticMap, hB, two_smul]

/-- The radical of the quadratic form of a symmetric bilinear form equals the kernel of the
bilinear form over a commutative ring in which `2` is invertible. -/
theorem BilinForm.radical_toQuadraticMap [Invertible (2 : R)] (B : LinearMap.BilinForm R M)
    (hB : B.IsSymm) :
    B.toQuadraticMap.radical = B.ker := by
  rw [QuadraticMap.radical_eq_ker_associated,
    QuadraticMap.associated_left_inverse (S := R) hB.eq]

/-- **Nondegeneracy passes from a symmetric bilinear form to its quadratic form** over a ring in
which `2` is invertible. Some hypothesis on `2` is needed: a quadratic form is a finer invariant
than its polar form, and it is the bilinear form, not the polar form `2 • B`, that is assumed
nondegenerate here. -/
theorem BilinForm.Nondegenerate.toQuadraticMap [Invertible (2 : R)] {B : LinearMap.BilinForm R M}
    (hB : B.Nondegenerate) (hflip : LinearMap.flip B = B) :
    (BilinMap.toQuadraticMap B).Nondegenerate := by
  have h2 : IsUnit (2 : R) := isUnit_of_invertible 2
  obtain ⟨hl, hr⟩ := hB
  rw [← QuadraticMap.nondegenerate_polar_iff, BilinMap.polarBilin_toQuadraticMap_of_flip hflip]
  refine ⟨fun x hx => hl x fun y => ?_, fun y hy => hr y fun x => ?_⟩
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hx y
  · simpa only [LinearMap.smul_apply, smul_eq_mul, h2.mul_right_eq_zero] using hy x

end LinearMap

namespace TauCeti

variable {R V : Type*} [CommRing R] [IsDomain R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V]

/-- A form on a line spanned by a vector of nonzero value is nondegenerate. -/
theorem nondegenerate_of_span_singleton_eq_top {Q : QuadraticForm R V} {v : V}
    (hspan : Submodule.span R {v} = ⊤) (hv : Q v ≠ 0) : Q.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin,
    LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨c, rfl⟩ := (Submodule.span_singleton_eq_top_iff R v).mp hspan z
  have hpolar : QuadraticMap.polar Q (c • v) v = 0 := by
    simpa using congrArg (fun L : V →ₗ[R] R => L v) hz
  rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_self] at hpolar
  have hc : c = 0 := by simpa [(isUnit_of_invertible (2 : R)).ne_zero, hv] using hpolar
  rw [hc, zero_smul]

end TauCeti
