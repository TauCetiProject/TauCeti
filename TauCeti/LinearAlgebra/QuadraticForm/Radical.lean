/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Radical API for quadratic forms

This file records basic properties of the radical of a quadratic form (such as its invariance under
negation and orthogonal products) and general consequences of nondegeneracy, together with the two
facts about the
quadratic form `x ↦ B x x` of a *symmetric* bilinear form `B` that a Clifford construction consumes:
its polar form is `2 • B`, and nondegeneracy passes from `B` to it as soon as `2` is invertible.

It also splits off the radical. The *regular part* of a quadratic map `Q` is the map
`Q.lift Q.radical le_rfl` that `Q` induces on the quotient by its radical. Over a field, `Q` is
isometric to the orthogonal sum of the zero form on its radical and its regular part, and any
splitting of `Q` as a zero form plus a map with trivial radical recovers both summands up to
isometry. This is the step that reduces the Witt decomposition of a possibly degenerate form to the
regular case.

## Main results

* `QuadraticMap.radical_neg`: negating a quadratic map does not change its radical.
* `QuadraticMap.nondegenerate_neg`: negating a quadratic map does not change its nondegeneracy.
* `QuadraticMap.radical_smul`, `QuadraticMap.nondegenerate_smul_iff`: scaling a quadratic map by a
  unit does not change its radical or its nondegeneracy.
* `QuadraticMap.radical_prod`: the radical of an orthogonal product is the product of the radicals.
* `QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot`: a quadratic map whose polar form has
  trivial kernel is nondegenerate.
* `QuadraticMap.isSymm_polarBilin`: the polar form is symmetric.
* `QuadraticMap.polarBilin_restrict`: polarization commutes with restriction to a submodule.
* `QuadraticMap.Nondegenerate.isCompl_orthogonal`: a subspace on which the form restricts
  nondegenerately is complementary to its polar orthogonal complement.
* `QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal`: in a regular finite-dimensional
  quadratic space, the orthogonal complement of a regular subspace is regular.
* `QuadraticMap.Nondegenerate.prod`: nondegeneracy passes to an orthogonal product.
* `QuadraticMap.Nondegenerate.ne_zero`: a nondegenerate quadratic map on a nontrivial module is
  nonzero.
* `QuadraticMap.Nondegenerate.polarBilin_ne_zero`: a nonzero vector has nonzero polar functional
  for a nondegenerate quadratic form.
* `QuadraticMap.Isometry.injective_of_radical_eq_bot`: an isometry out of a quadratic map with
  trivial radical is injective.
* `QuadraticMap.liftOfSurjective`: descent of a quadratic map along a surjective linear map whose
  kernel lies in the radical.
* `QuadraticMap.exists_isUnit_of_ne_zero`: a nonzero quadratic form over a semifield has a vector of
  unit norm.
* `QuadraticMap.isUnit_apply_smul`: scaling a vector of unit norm by a unit preserves unit norm.
* `QuadraticMap.Nondegenerate.exists_isUnit`: the same conclusion for a nondegenerate form on a
  nontrivial vector space.
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
* `QuadraticMap.radical_zero_prod`: the radical of the orthogonal sum of a zero form with `Q`.
* `QuadraticMap.radical_lift_radical`, `QuadraticMap.nondegenerate_lift_radical`: the regular
  part has trivial radical, so it is nondegenerate when `2` is invertible.
* `QuadraticMap.Equivalent.lift_radical`: isometric maps have isometric regular parts.
* `QuadraticMap.equivalent_zero_prod_lift_radical`: over a field, a quadratic map is the orthogonal
  sum of the zero form on its radical and its regular part.
* `QuadraticMap.equivalent_lift_radical_of_equivalent_zero_prod`,
  `QuadraticMap.nonempty_linearEquiv_radical_of_equivalent_zero_prod`: in any splitting
  `Q ≅ 0 ⊥ Q'` with `Q'` of trivial radical, `Q'` is the regular part and the zero summand lives
  on a copy of the radical.
-/

public section

namespace QuadraticMap

variable {R M P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

/-- The polar bilinear form of a scalar-valued quadratic map is symmetric. -/
theorem isSymm_polarBilin (Q : QuadraticForm R M) :
    LinearMap.BilinForm.IsSymm Q.polarBilin :=
  ⟨fun x y => polar_comm Q x y⟩

/-- Polarization commutes with restricting a quadratic map to a submodule. -/
@[simp]
theorem polarBilin_restrict (Q : QuadraticMap R M P) (W : Submodule R M) :
    (Q.restrict W).polarBilin = Q.polarBilin.domRestrict₁₂ W W := by
  ext x y
  simp only [polarBilin_apply_apply, polar, restrict_apply,
    LinearMap.domRestrict₁₂_apply]
  rw [Submodule.coe_add]

/-- Negating a quadratic map does not change its radical. -/
@[simp]
theorem radical_neg (Q : QuadraticMap R M P) : (-Q).radical = Q.radical := by
  ext x
  simp only [QuadraticMap.mem_radical_iff', neg_apply, neg_eq_zero, neg_inj]

/-- Negating a quadratic map does not change its nondegeneracy. -/
@[simp]
theorem nondegenerate_neg (Q : QuadraticMap R M P) :
    (-Q).Nondegenerate ↔ Q.Nondegenerate := by
  have hpolar : (-Q).polarBilin = -Q.polarBilin := by
    ext x y
    exact polar_neg Q x y
  have hker : (-Q).polarBilin.ker = Q.polarBilin.ker := by rw [hpolar, LinearMap.ker_neg]
  constructor
  · rintro ⟨h, hrank⟩
    refine ⟨by simpa only [radical_neg] using h, hker.symm ▸ hrank⟩
  · rintro ⟨h, hrank⟩
    refine ⟨by simpa only [radical_neg] using h, hker ▸ hrank⟩

/-- Scaling a quadratic map by a unit does not change its radical. -/
@[simp]
theorem radical_smul {a : R} (ha : IsUnit a) (Q : QuadraticMap R M P) :
    (a • Q).radical = Q.radical := by
  ext x
  simp only [mem_radical_iff', smul_apply, ha.smul_eq_zero, ha.smul_left_cancel]

/-- Scaling a quadratic map by a unit does not change its nondegeneracy. -/
@[simp]
theorem nondegenerate_smul_iff {a : R} (ha : IsUnit a) (Q : QuadraticMap R M P) :
    (a • Q).Nondegenerate ↔ Q.Nondegenerate := by
  have hker : (a • Q).polarBilin.ker = Q.polarBilin.ker := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, polarBilin_apply_apply, LinearMap.zero_apply,
      FunLike.coe_smul, polar_smul, ha.smul_eq_zero]
  constructor
  · rintro ⟨h, hrank⟩
    exact ⟨radical_smul ha Q ▸ h, hker ▸ hrank⟩
  · rintro ⟨h, hrank⟩
    exact ⟨(radical_smul ha Q).symm ▸ h, hker.symm ▸ hrank⟩

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

/-- A quadratic map whose polar form has trivial kernel is nondegenerate. -/
theorem nondegenerate_of_ker_polarBilin_eq_bot {Q : QuadraticMap R M P}
    (hker : Q.polarBilin.ker = ⊥) : Q.Nondegenerate := by
  refine ⟨le_antisymm (Q.radical_le_ker_polarBilin.trans hker.le) bot_le, ?_⟩
  rw [hker]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

/-- **An isometry out of a quadratic map with trivial radical is injective.** Its kernel lies in the
radical: an element `x` killed by `f` has `Q₁ x = Q₂ 0 = 0` and `Q₁ (x + n) = Q₂ (f n) = Q₁ n`. -/
theorem Isometry.injective_of_radical_eq_bot {Q₁ : QuadraticMap R M P} {Q₂ : QuadraticMap R M' P}
    (f : Q₁.Isometry Q₂) (h : Q₁.radical = ⊥) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
  have hmem : x ∈ Q₁.radical := mem_radical_iff'.2
    ⟨by rw [← f.map_app, hx, map_zero], fun n => by rw [← f.map_app, ← f.map_app, map_add, hx,
      zero_add]⟩
  simpa [h] using hmem

/-- A nonzero quadratic form over a semifield has a vector of unit norm. -/
theorem exists_isUnit_of_ne_zero {K V : Type*} [Semifield K] [AddCommMonoid V] [Module K V]
    {Q : QuadraticForm K V} (hQ : Q ≠ 0) : ∃ v, IsUnit (Q v) := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact ⟨v, isUnit_iff_ne_zero.mpr hv⟩

/-- Scaling a vector of unit norm by a unit preserves unit norm. -/
theorem isUnit_apply_smul {S N : Type*} [CommSemiring S] [AddCommMonoid N] [Module S N]
    {Q : QuadraticForm S N} {c : S} {v : N}
    (hc : IsUnit c) (hv : IsUnit (Q v)) : IsUnit (Q (c • v)) := by
  rw [QuadraticMap.map_smul]
  simpa [smul_eq_mul, mul_assoc] using (hc.mul (hc.mul hv))

section LiftOfSurjective

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- Descend a quadratic map along a surjective linear map whose kernel lies in its radical.

Mathlib's `QuadraticMap.lift` descends along the quotient by a submodule of the radical.  A
quotient is usually presented instead by a surjection onto a concrete group — reduction modulo `m`
onto `ZMod m`, say — and this is that formulation. -/
noncomputable def liftOfSurjective (Q : QuadraticMap R M P) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (h : LinearMap.ker f ≤ Q.radical) : QuadraticMap R N P :=
  (Q.lift (LinearMap.ker f) h).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

/-- The descended quadratic map takes the original value on every representative. -/
@[simp]
theorem liftOfSurjective_apply (Q : QuadraticMap R M P) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (h : LinearMap.ker f ≤ Q.radical) (x : M) :
    liftOfSurjective Q f hf h (f x) = Q x := by
  rw [liftOfSurjective, QuadraticMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, QuadraticMap.lift_mk]

end LiftOfSurjective

end QuadraticMap

namespace QuadraticMap.Nondegenerate

variable {R M M' P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P]

/-- The polar functional of a nonzero vector is nonzero for a nondegenerate quadratic form. -/
theorem polarBilin_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Invertible (2 : K)] {Q : QuadraticForm K V} {u : V}
    (hQ : Q.Nondegenerate) (hu : u ≠ 0) : Q.polarBilin u ≠ 0 :=
  fun h => hu ((nondegenerate_polar_iff.mpr hQ).1 u fun y => by rw [h, LinearMap.zero_apply])

/-- The orthogonal product of two nondegenerate quadratic maps is nondegenerate, when `2` is
invertible in the coefficient ring. -/
theorem prod [Invertible (2 : R)] {Q : QuadraticMap R M P} {Q' : QuadraticMap R M' P}
    (hQ : Q.Nondegenerate) (hQ' : Q'.Nondegenerate) : (Q.prod Q').Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_prod,
    hQ.radical_eq_bot, hQ'.radical_eq_bot, Submodule.prod_bot]

/-- A nondegenerate quadratic map on a nontrivial module is nonzero. -/
theorem ne_zero [Nontrivial M] {Q : QuadraticMap R M P} (hQ : Q.Nondegenerate) : Q ≠ 0 := by
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  apply hv
  have hm : v ∈ Q.radical := by
    rw [hzero, QuadraticMap.mem_radical_iff']
    simp
  rwa [hQ.radical_eq_bot, Submodule.mem_bot] at hm

/-- A nondegenerate quadratic form on a nontrivial vector space has a vector of nonzero norm. -/
theorem exists_isUnit {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] {Q : QuadraticForm K V} (hQ : Q.Nondegenerate) :
    ∃ v, IsUnit (Q v) := QuadraticMap.exists_isUnit_of_ne_zero hQ.ne_zero

section Orthogonal

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {W : Submodule K V}

/-- A subspace on which a quadratic form restricts nondegenerately is complementary to its
orthogonal complement. -/
theorem isCompl_orthogonal (hW : (Q.restrict W).Nondegenerate) :
    IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W) := by
  apply LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    Q.isSymm_polarBilin.isRefl
  have hpolar := QuadraticMap.nondegenerate_polar_iff.mpr hW
  rwa [QuadraticMap.polarBilin_restrict] at hpolar

/-- In a regular finite-dimensional quadratic space, the orthogonal complement of a regular
subspace is regular. -/
theorem nondegenerate_restrict_orthogonal (hQ : Q.Nondegenerate)
    (hW : (Q.restrict W).Nondegenerate) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).Nondegenerate := by
  have hB : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hBsymm : Q.polarBilin.IsRefl := Q.isSymm_polarBilin.isRefl
  have hcomp : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W) :=
    hW.isCompl_orthogonal
  apply QuadraticMap.nondegenerate_polar_iff.mp
  rw [QuadraticMap.polarBilin_restrict]
  exact
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := Q.polarBilin) hBsymm).mpr (by
      rw [LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm]
      exact hcomp.symm)

end Orthogonal

end QuadraticMap.Nondegenerate

namespace QuadraticMap

variable {K : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A nondegenerate quadratic space of dimension at least two has an anisotropic vector
orthogonal to any given anisotropic vector. -/
theorem exists_orthogonal_anisotropic [NeZero (2 : K)]
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hrank : 2 ≤ Module.finrank K V) {y : V}
    (hy : Q y ≠ 0) : ∃ z : V, Q.IsOrtho z y ∧ Q z ≠ 0 := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  let B : LinearMap.BilinForm K V := Q.polarBilin
  let W : Submodule K V := B.orthogonal (K ∙ y)
  have hB : B.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff (Q := Q)).mpr hQ
  have hBsymm : B.IsSymm := Q.isSymm_polarBilin
  have hByy : B y y ≠ 0 := by
    simpa only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      Nat.cast_ofNat] using mul_ne_zero (NeZero.ne (2 : K)) hy
  have hWnondeg : (B.restrict W).Nondegenerate :=
    B.restrict_nondegenerate_orthogonal_spanSingleton hB hBsymm.isRefl hByy
  have hWrank : 0 < Module.finrank K W := by
    dsimp only [W]
    rw [B.finrank_orthogonal hB]
    rw [finrank_span_singleton (fun h => hy (by simp [h]))]
    omega
  let _ : Nontrivial W := Module.nontrivial_of_finrank_pos hWrank
  obtain ⟨z, hz⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    hWnondeg.ne_zero (LinearMap.BilinForm.isSymm_iff.mp (hBsymm.restrict W))
  refine ⟨z, ?_, ?_⟩
  · apply QuadraticMap.isOrtho_polarBilin.mp
    simpa only [B, W, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm] using
      z.2 y (Submodule.mem_span_singleton_self y)
  · have hz' : B (z : V) (z : V) ≠ 0 := by
      simpa only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply] using hz
    simpa only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, nsmul_eq_mul,
      Nat.cast_ofNat, mul_ne_zero_iff_left (NeZero.ne (2 : K))] using hz'

end QuadraticMap

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
  rw [← QuadraticMap.nondegenerate_associated_iff,
    QuadraticMap.associated_left_inverse' R hflip]
  exact hB

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

/-- The form `x ↦ a x²` on `R` is nondegenerate for `a ≠ 0`. -/
theorem _root_.QuadraticMap.nondegenerate_smul_sq {a : R} (ha : a ≠ 0) :
    (a • QuadraticMap.sq : QuadraticForm R R).Nondegenerate :=
  nondegenerate_of_span_singleton_eq_top (v := 1) (by simp) (by simpa using ha)

end TauCeti

/-! ### The regular part of a quadratic map -/

namespace QuadraticMap

section RegularPart

variable {R M N T P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup T] [Module R T] [AddCommGroup P] [Module R P]

/-- The radical of the orthogonal sum of a zero form with `Q` consists of the pairs whose second
component lies in the radical of `Q`. Unlike `QuadraticMap.radical_prod`, this needs no hypothesis
on `2`. -/
@[simp]
theorem radical_zero_prod (Q : QuadraticMap R N P) :
    ((0 : QuadraticMap R T P).prod Q).radical = (⊤ : Submodule R T).prod Q.radical := by
  ext ⟨t, x⟩
  simp [mem_radical_iff', Prod.forall]

/-- The quadratic map that `Q` induces on the quotient by its radical has trivial radical. -/
@[simp]
theorem radical_lift_radical (Q : QuadraticMap R M P) :
    (Q.lift Q.radical le_rfl).radical = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    obtain ⟨h0, hadd⟩ := mem_radical_iff'.mp hx
    refine (Submodule.Quotient.mk_eq_zero _).mpr (mem_radical_iff'.mpr ⟨h0, fun n => ?_⟩)
    simpa only [← Submodule.Quotient.mk_add, lift_mk] using hadd (Submodule.Quotient.mk n)

/-- When `2` is invertible, the quadratic map that `Q` induces on the quotient by its radical is
nondegenerate. This is the *regular part* of a possibly degenerate quadratic map. -/
theorem nondegenerate_lift_radical [Invertible (2 : R)] (Q : QuadraticMap R M P) :
    (Q.lift Q.radical le_rfl).Nondegenerate :=
  nondegenerate_iff_radical_eq_bot.mpr (radical_lift_radical Q)

/-- Isometric quadratic maps have isometric regular parts: an isometry carries the radical onto the
radical, so it descends to the quotients. -/
theorem Equivalent.lift_radical {Q₁ : QuadraticMap R M P} {Q₂ : QuadraticMap R N P}
    (h : Q₁.Equivalent Q₂) :
    (Q₁.lift Q₁.radical le_rfl).Equivalent (Q₂.lift Q₂.radical le_rfl) := by
  obtain ⟨e⟩ := h
  refine ⟨{ toLinearEquiv := Submodule.Quotient.equiv _ _ e.toLinearEquiv e.map_radical
            map_app' := fun x => ?_ }⟩
  induction x using Submodule.Quotient.induction_on with
  | H m => simp

/-- The regular part of `Q` is computed by any surjection `f` whose kernel is the radical of `Q` and
through which `Q` factors. -/
theorem equivalent_lift_radical_of_comp_eq {Q : QuadraticMap R M P} {Q' : QuadraticMap R N P}
    (f : M →ₗ[R] N) (hf : Function.Surjective f) (hker : LinearMap.ker f = Q.radical)
    (hQ : Q'.comp f = Q) : (Q.lift Q.radical le_rfl).Equivalent Q' := by
  refine ⟨{ toLinearEquiv :=
              (Submodule.quotEquivOfEq _ _ hker.symm).trans (f.quotKerEquivOfSurjective hf)
            map_app' := fun x => ?_ }⟩
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    simpa [LinearMap.quotKerEquivOfSurjective_apply_mk] using DFunLike.congr_fun hQ m

/-- **Uniqueness of the regular part.** If `Q` is isometric to the orthogonal sum of a zero form and
a quadratic map `Q'` with trivial radical, then `Q'` is isometric to the regular part of `Q`. -/
theorem equivalent_lift_radical_of_equivalent_zero_prod {Q : QuadraticMap R M P}
    {Q' : QuadraticMap R N P} (h : Q.Equivalent ((0 : QuadraticMap R T P).prod Q'))
    (hQ' : Q'.radical = ⊥) : (Q.lift Q.radical le_rfl).Equivalent Q' :=
  h.lift_radical.trans <| equivalent_lift_radical_of_comp_eq (LinearMap.snd R T N)
    LinearMap.snd_surjective
    (by rw [radical_zero_prod, hQ', ← Submodule.comap_snd, Submodule.comap_bot])
    (by ext; simp)

/-- **Uniqueness of the totally isotropic part.** If `Q` is isometric to the orthogonal sum of the
zero form on `T` and a quadratic map with trivial radical, then `T` is linearly equivalent to the
radical of `Q`. -/
theorem nonempty_linearEquiv_radical_of_equivalent_zero_prod {Q : QuadraticMap R M P}
    {Q' : QuadraticMap R N P} (h : Q.Equivalent ((0 : QuadraticMap R T P).prod Q'))
    (hQ' : Q'.radical = ⊥) : Nonempty (T ≃ₗ[R] Q.radical) := by
  obtain ⟨e⟩ := h
  have hrad :
      LinearMap.range (LinearMap.inl R T N) = Q.radical.map e.toLinearEquiv.toLinearMap := by
    rw [← LinearMap.ker_snd, ← Submodule.comap_bot, Submodule.comap_snd, ← hQ', ← radical_zero_prod]
    exact e.map_radical.symm
  exact ⟨((LinearEquiv.ofInjective _ LinearMap.inl_injective).trans
    (LinearEquiv.ofEq _ _ hrad)).trans (e.toLinearEquiv.submoduleMap Q.radical).symm⟩

end RegularPart

section Field

variable {K V P : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup P] [Module K P]

/-- **The radical splits off.** Over a field, a quadratic map is isometric to the orthogonal sum of
the zero form on its radical and its regular part on the quotient by the radical. -/
theorem equivalent_zero_prod_lift_radical (Q : QuadraticMap K V P) :
    Q.Equivalent ((0 : QuadraticMap K Q.radical P).prod (Q.lift Q.radical le_rfl)) := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl Q.radical
  let e : (Q.radical × (V ⧸ Q.radical)) ≃ₗ[K] V :=
    ((LinearEquiv.refl K Q.radical).prodCongr (Submodule.quotientEquivOfIsCompl _ _ hW)).trans
      (Submodule.prodEquivOfIsCompl _ _ hW)
  have he : ∀ y,
      Q (e y) = ((0 : QuadraticMap K Q.radical P).prod (Q.lift Q.radical le_rfl)) y := by
    rintro ⟨r, x⟩
    obtain ⟨w, rfl⟩ := (Submodule.quotientEquivOfIsCompl _ _ hW).symm.surjective x
    have hew : e (r, (Submodule.quotientEquivOfIsCompl _ _ hW).symm w) = (r : V) + w := by
      simp [e]
    rw [hew, (mem_radical_iff'.mp r.2).2]
    simp
  exact Equivalent.symm ⟨{ toLinearEquiv := e, map_app' := he }⟩

end Field

end QuadraticMap
