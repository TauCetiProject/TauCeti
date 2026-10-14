/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Radical API for quadratic forms

This file records basic properties of the radical of a quadratic form (such as its invariance under
negation and orthogonal products), the splitting of a form into its radical and quotient parts, and
general consequences of nondegeneracy, together with the two facts about the
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
* `QuadraticMap.orthogonal_polarBilin_eq_radical_of_isCompl`: the polar orthogonal complement of
  a radical complement is the radical.
* `QuadraticMap.nondegenerate_restrict_of_isCompl_radical`: a radical complement is regular.
* `QuadraticForm.exists_equivalent_zero_radical_prod`: a quadratic form splits
  as the zero form on its radical and a regular complement.
* `QuadraticForm.finrank_radical_eq_of_equivalent_zero_prod` and
  `QuadraticForm.finrank_zeroPart_eq_of_equivalent_zero_prod`: the zero summand in a decomposition
  into a zero form and a regular form has dimension equal to the radical.
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
* `QuadraticMap.IsometryEquiv.restrictComplementLiftRadical`: the restriction to a complement of
  the radical is isometric to the descended form on the quotient.
* `QuadraticMap.IsometryEquiv.prodRadicalLiftOfIsCompl` and
  `QuadraticMap.IsometryEquiv.prodRadicalLift`: a quadratic map is isometric to the product of the
  zero form on its radical and the descended form on the quotient, given a complement or over a
  field, respectively.
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

/-- The polar orthogonal complement of a complement to the radical is the radical. -/
theorem orthogonal_polarBilin_eq_radical_of_isCompl [Invertible (2 : R)]
    (Q : QuadraticForm R M) {C : Submodule R M} (hC : IsCompl Q.radical C) :
    LinearMap.BilinForm.orthogonal Q.polarBilin C = Q.radical := by
  rw [radical_eq_ker_polarBilin] at hC ⊢
  calc
    LinearMap.BilinForm.orthogonal Q.polarBilin C =
        LinearMap.BilinForm.orthogonal Q.polarBilin (C ⊔ Q.polarBilin.ker) :=
      (Submodule.orthogonalBilin_sup_ker Q.polarBilin C).symm
    _ = LinearMap.BilinForm.orthogonal Q.polarBilin ⊤ := by rw [hC.symm.sup_eq_top]
    _ = Q.polarBilin.ker := LinearMap.BilinForm.orthogonal_top_eq_ker Q.isSymm_polarBilin.isRefl

/-- Restricting a quadratic form to a complement of its radical gives a nondegenerate form. -/
theorem nondegenerate_restrict_of_isCompl_radical [Invertible (2 : R)]
    (Q : QuadraticForm R M) {C : Submodule R M} (hC : IsCompl Q.radical C) :
    (Q.restrict C).Nondegenerate := by
  rw [← nondegenerate_polar_iff, polarBilin_restrict]
  apply LinearMap.IsSymm.nondegenerate_restrict_of_isCompl_ker
    (LinearMap.BilinForm.isSymm_iff.mp Q.isSymm_polarBilin)
  simpa only [← radical_eq_ker_polarBilin] using hC.symm

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

/-- **The quotient by the radical is nondegenerate.** When two is invertible, the form induced
on `M ⧸ Q.radical` has no radical: a class orthogonal to every class is represented by a vector
in `Q.radical`, hence is zero. This is the regular quotient used in the Witt decomposition of a
possibly degenerate form. -/
theorem nondegenerate_lift_radical [Invertible (2 : R)] (Q : QuadraticForm R M) :
    (Q.lift Q.radical le_rfl).Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, radical_lift_radical]

/-- **An isometry out of a quadratic map with trivial radical is injective.** Its kernel lies in the
radical: an element `x` killed by `f` has `Q₁ x = Q₂ 0 = 0` and `Q₁ (x + n) = Q₂ (f n) = Q₁ n`. -/
theorem Isometry.injective_of_radical_eq_bot {Q₁ : QuadraticMap R M P} {Q₂ : QuadraticMap R M' P}
    (f : Q₁.Isometry Q₂) (h : Q₁.radical = ⊥) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
  have hmem : x ∈ Q₁.radical := mem_radical_iff'.2
    ⟨by rw [← f.map_app, hx, map_zero], fun n => by rw [← f.map_app, ← f.map_app, map_add, hx,
      zero_add]⟩
  simpa [h] using hmem

section QuotientRadicalIsometry

variable {N : Type*} [AddCommGroup N] [Module R N] {Q : QuadraticMap R M P}
  {S : QuadraticMap R N P}

/-- An isometry of quadratic maps descends to an isometry of their quotients by the radical. -/
noncomputable def IsometryEquiv.quotientRadical (e : Q.IsometryEquiv S) :
    (Q.lift Q.radical le_rfl).IsometryEquiv (S.lift S.radical le_rfl) where
  __ := Submodule.Quotient.equiv Q.radical S.radical e.toLinearEquiv e.map_radical
  map_app' x := by
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [Submodule.Quotient.equiv_apply, QuadraticMap.lift_mk]

/-- The quotient isometry sends the class of a vector to the class of its image. -/
@[simp]
theorem IsometryEquiv.quotientRadical_mk (e : Q.IsometryEquiv S) (x : M) :
    e.quotientRadical (Submodule.Quotient.mk x : M ⧸ Q.radical) =
      (Submodule.Quotient.mk (e x) : N ⧸ S.radical) := by
  dsimp [IsometryEquiv.quotientRadical]
  rfl

/-- Equivalent quadratic maps have equivalent quotients by their radicals. -/
theorem Equivalent.lift_radical (h : Q.Equivalent S) :
    (Q.lift Q.radical le_rfl).Equivalent (S.lift S.radical le_rfl) := by
  obtain ⟨e⟩ := h
  exact ⟨e.quotientRadical⟩

end QuotientRadicalIsometry

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

section QuotientByRadical

variable {N : Type*} [AddCommGroup N] [Module R N]

private theorem quotientEquivOfIsCompl_symm_apply {S : Submodule R M}
    (W : Submodule R M) (hW : IsCompl S W) (x : W) :
    (S.quotientEquivOfIsCompl W hW).symm x =
      (Submodule.Quotient.mk (x : M) : M ⧸ S) :=
  LinearMap.congr_fun (Submodule.toLinearMap_symm_quotientEquivOfIsCompl hW) x

/-- The restriction of a quadratic map to a complement of its radical is isometric to the
quadratic map descended to the quotient by the radical. -/
noncomputable def IsometryEquiv.restrictComplementLiftRadical (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) :
    (Q.restrict W).IsometryEquiv (Q.lift Q.radical le_rfl) where
  toLinearEquiv := (Q.radical.quotientEquivOfIsCompl W hW).symm
  map_app' x := by
    -- Expose the quotient equivalence hidden by the isometry-equivalence coercion.
    change Q.lift Q.radical le_rfl ((Q.radical.quotientEquivOfIsCompl W hW).symm x) = _
    rw [quotientEquivOfIsCompl_symm_apply]
    simp only [QuadraticMap.lift_mk, QuadraticMap.restrict_apply]

/-- The complement-to-quotient isometry sends a vector to its quotient class. -/
@[simp]
theorem IsometryEquiv.restrictComplementLiftRadical_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : W) :
    IsometryEquiv.restrictComplementLiftRadical Q W hW x =
      (Submodule.Quotient.mk (x : M) : M ⧸ Q.radical) := by
  exact quotientEquivOfIsCompl_symm_apply W hW x

/-- The inverse complement-to-quotient isometry is the quotient equivalence. -/
@[simp]
theorem IsometryEquiv.restrictComplementLiftRadical_symm_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : M ⧸ Q.radical) :
    (IsometryEquiv.restrictComplementLiftRadical Q W hW).symm x =
      Q.radical.quotientEquivOfIsCompl W hW x := by
  rfl

/-- The direct sum of a complement and the radical maps to their sum in the ambient module. -/
noncomputable def IsometryEquiv.restrictProdRadicalOfIsCompl (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) :
    ((Q.restrict W).prod (0 : QuadraticMap R Q.radical P)).IsometryEquiv Q where
  toLinearEquiv := W.prodEquivOfIsCompl Q.radical hW.symm
  map_app' x := by
    -- Expose the sum map underlying the direct-sum equivalence.
    change Q (W.prodEquivOfIsCompl Q.radical hW.symm x) = _
    rw [Submodule.coe_prodEquivOfIsCompl', QuadraticMap.prod_apply,
      QuadraticMap.restrict_apply, add_comm,
      (QuadraticMap.mem_radical_iff'.mp x.2.2).2]
    simp

/-- The direct-sum isometry adds the complement and radical components. -/
@[simp]
theorem IsometryEquiv.restrictProdRadicalOfIsCompl_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : W × Q.radical) :
    IsometryEquiv.restrictProdRadicalOfIsCompl Q W hW x = (x.1 : M) + x.2 := by
  -- An `IsometryEquiv` coerces to its underlying `LinearEquiv`; expose that coercion to apply
  -- the public sum formula for `prodEquivOfIsCompl`.
  change W.prodEquivOfIsCompl Q.radical hW.symm x = _
  exact Submodule.coe_prodEquivOfIsCompl' (p := W) (q := Q.radical) hW.symm x

/-- The inverse direct-sum isometry extracts the complement and radical projections. -/
@[simp]
theorem IsometryEquiv.restrictProdRadicalOfIsCompl_symm_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : M) :
    (IsometryEquiv.restrictProdRadicalOfIsCompl Q W hW).symm x =
      (W.projectionOnto Q.radical hW.symm x, Q.radical.projectionOnto W hW x) := by
  -- The inverse isometry coerces to the inverse of its underlying `LinearEquiv`, so apply the
  -- public inverse formula for `prodEquivOfIsCompl` after exposing that coercion.
  change (W.prodEquivOfIsCompl Q.radical hW.symm).symm x = _
  exact Submodule.prodEquivOfIsCompl_symm_apply hW.symm x

/-- Given a complement to the radical, a quadratic map is isometric to the product of the zero
form on its radical and the descended form on the quotient. -/
noncomputable def IsometryEquiv.prodRadicalLiftOfIsCompl (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) :
    ((0 : QuadraticMap R Q.radical P).prod (Q.lift Q.radical le_rfl)).IsometryEquiv Q :=
  ((QuadraticMap.IsometryEquiv.prodComm (0 : QuadraticMap R Q.radical P)
      (Q.lift Q.radical le_rfl)).trans
    ((IsometryEquiv.restrictComplementLiftRadical Q W hW).symm.prod
      (QuadraticMap.IsometryEquiv.refl (0 : QuadraticMap R Q.radical P)))).trans
    (IsometryEquiv.restrictProdRadicalOfIsCompl Q W hW)

/-- The decomposition maps a pair to its complement representative plus its radical component. -/
@[simp]
theorem IsometryEquiv.prodRadicalLiftOfIsCompl_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : Q.radical × M ⧸ Q.radical) :
    IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW x =
      (Q.radical.quotientEquivOfIsCompl W hW x.2 : M) + x.1 := by
  -- Composition and product of isometries coerce to composition and product of their underlying
  -- linear equivalences; expose this composite to use the application lemmas below.
  change IsometryEquiv.restrictProdRadicalOfIsCompl Q W hW
    ((IsometryEquiv.restrictComplementLiftRadical Q W hW).symm x.2, x.1) = _
  rw [IsometryEquiv.restrictProdRadicalOfIsCompl_apply,
    IsometryEquiv.restrictComplementLiftRadical_symm_apply]

/-- The decomposition sends a radical vector and zero quotient class to that vector. -/
theorem IsometryEquiv.prodRadicalLiftOfIsCompl_apply_radical (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : Q.radical) :
    IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW (x, 0) = x := by
  rw [IsometryEquiv.prodRadicalLiftOfIsCompl_apply]
  simp

/-- The quotient component of the image under the complement-based decomposition is the input
class. -/
theorem IsometryEquiv.prodRadicalLiftOfIsCompl_mkQ_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W)
    (x : Q.radical × M ⧸ Q.radical) :
    Submodule.Quotient.mk (IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW x) = x.2 := by
  rw [IsometryEquiv.prodRadicalLiftOfIsCompl_apply, add_comm]
  simp

/-- The quotient component of the inverse decomposition is the quotient class of its input. -/
theorem IsometryEquiv.prodRadicalLiftOfIsCompl_symm_apply_snd (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : M) :
    ((IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW).symm x).2 =
      Submodule.Quotient.mk x := by
  simpa using (IsometryEquiv.prodRadicalLiftOfIsCompl_mkQ_apply Q W hW
    ((IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW).symm x)).symm

/-- The inverse decomposition pairs the radical projection with the quotient class. -/
@[simp]
theorem IsometryEquiv.prodRadicalLiftOfIsCompl_symm_apply (Q : QuadraticMap R M P)
    (W : Submodule R M) (hW : IsCompl Q.radical W) (x : M) :
    (IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW).symm x =
      (Q.radical.projectionOnto W hW x, Submodule.Quotient.mk x) := by
  apply Prod.ext
  · have h := congrArg (Q.radical.projectionOnto W hW)
      ((IsometryEquiv.prodRadicalLiftOfIsCompl Q W hW).apply_symm_apply x)
    simpa only [IsometryEquiv.prodRadicalLiftOfIsCompl_apply, map_add, zero_add,
      Submodule.projectionOnto_apply_right hW,
      Submodule.projectionOnto_apply_left hW] using h
  · exact IsometryEquiv.prodRadicalLiftOfIsCompl_symm_apply_snd Q W hW x

end QuotientByRadical

section QuotientByRadical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Every quadratic map over a field splits as the zero form on its radical and the descended form
on the quotient by the radical. The complement used to construct the isometry is noncanonical. -/
noncomputable def IsometryEquiv.prodRadicalLift {P : Type*} [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K V P) :
    ((0 : QuadraticMap K Q.radical P).prod (Q.lift Q.radical le_rfl)).IsometryEquiv Q :=
  IsometryEquiv.prodRadicalLiftOfIsCompl Q (Submodule.exists_isCompl Q.radical).choose
    (Submodule.exists_isCompl Q.radical).choose_spec

/-- The field-level decomposition maps a radical vector and zero quotient class to that vector. -/
@[simp]
theorem IsometryEquiv.prodRadicalLift_apply_radical {P : Type*} [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K V P)
    (x : Q.radical) : IsometryEquiv.prodRadicalLift Q (x, 0) = x := by
  simp [IsometryEquiv.prodRadicalLift]

/-- The quotient component of the image under the field-level decomposition is the input class. -/
@[simp]
theorem IsometryEquiv.prodRadicalLift_mkQ_apply {P : Type*} [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K V P)
    (x : Q.radical × V ⧸ Q.radical) :
    Submodule.Quotient.mk (IsometryEquiv.prodRadicalLift Q x) = x.2 := by
  simp [IsometryEquiv.prodRadicalLift]

/-- The quotient component of the inverse field-level decomposition is the quotient class. -/
theorem IsometryEquiv.prodRadicalLift_symm_apply_snd {P : Type*} [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K V P) (x : V) :
    ((IsometryEquiv.prodRadicalLift Q).symm x).2 = Submodule.Quotient.mk x := by
  simpa using (IsometryEquiv.prodRadicalLift_mkQ_apply Q
    ((IsometryEquiv.prodRadicalLift Q).symm x)).symm

/-- The inverse field-level decomposition pairs the radical projection with the quotient class. -/
@[simp]
theorem IsometryEquiv.prodRadicalLift_symm_apply {P : Type*} [AddCommGroup P] [Module K P]
    (Q : QuadraticMap K V P) (x : V) :
    (IsometryEquiv.prodRadicalLift Q).symm x =
      ((Q.radical.projectionOnto (Submodule.exists_isCompl Q.radical).choose
        (Submodule.exists_isCompl Q.radical).choose_spec x), Submodule.Quotient.mk x) := by
  simp only [IsometryEquiv.prodRadicalLift,
    IsometryEquiv.prodRadicalLiftOfIsCompl_symm_apply]

end QuotientByRadical

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

/-- The regular part of `Q` is computed by any surjection `f` whose kernel is the radical of `Q` and
through which `Q` factors. -/
theorem equivalent_lift_radical_of_comp_eq (Q : QuadraticMap R M P) {Q' : QuadraticMap R N P}
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
theorem equivalent_lift_radical_of_equivalent_zero_prod (Q : QuadraticMap R M P)
    {Q' : QuadraticMap R N P} (h : Q.Equivalent ((0 : QuadraticMap R T P).prod Q'))
    (hQ' : Q'.radical = ⊥) : (Q.lift Q.radical le_rfl).Equivalent Q' :=
  h.lift_radical.trans <| ((0 : QuadraticMap R T P).prod Q').equivalent_lift_radical_of_comp_eq
    (LinearMap.snd R T N) LinearMap.snd_surjective
    (by rw [radical_zero_prod, hQ', ← Submodule.comap_snd, Submodule.comap_bot])
    (by ext; simp)

/-- **Uniqueness of the totally isotropic part.** If `Q` is isometric to the orthogonal sum of the
zero form on `T` and a quadratic map with trivial radical, then `T` is linearly equivalent to the
radical of `Q`. -/
theorem nonempty_linearEquiv_radical_of_equivalent_zero_prod (Q : QuadraticMap R M P)
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

end QuadraticMap

namespace QuadraticForm

universe u

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Every quadratic form is an orthogonal sum of the zero form on its radical
and a nondegenerate restriction to a complementary subspace.

The complement argument follows Lam, *Introduction to Quadratic Forms over Fields*, Chapter I,
§4. -/
theorem exists_equivalent_zero_radical_prod
    {V : Type*} [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) :
    ∃ C : Submodule K V, IsCompl Q.radical C ∧ (Q.restrict C).Nondegenerate ∧
      Q.Equivalent ((0 : QuadraticForm K Q.radical).prod (Q.restrict C)) := by
  obtain ⟨C, hC⟩ := Q.radical.exists_isCompl
  -- The product-isometry API imports this module, so construct the splitting isometry here.
  have heq : ((Q.restrict C).prod (Q.restrict Q.radical)).IsometryEquiv Q :=
    { toLinearEquiv := C.prodEquivOfIsCompl Q.radical hC.symm
      map_app' := fun x => by
        -- Normalize the bundled isometry goal with `change` so `map_add` applies directly:
        -- `Submodule.prodEquivOfIsCompl` evaluates to the sum of the coerced components,
        -- and `QuadraticMap.prod` and `QuadraticMap.restrict` evaluate to the sum of their
        -- values under `Q`. These reductions are definitional.
        change Q ((x.1 : V) + x.2) = Q x.1 + Q x.2
        rw [QuadraticMap.map_add Q]
        have hx : (x.2 : V) ∈ LinearMap.BilinForm.orthogonal Q.polarBilin C := by
          rw [Q.orthogonal_polarBilin_eq_radical_of_isCompl hC]
          exact x.2.2
        rw [← QuadraticMap.polarBilin_apply_apply, hx x.1 x.1.2, add_zero] }
  have hradZero : Q.restrict Q.radical = (0 : QuadraticForm K Q.radical) := by
    ext x
    exact (QuadraticMap.mem_radical_iff'.mp x.2).1
  refine ⟨C, hC, Q.nondegenerate_restrict_of_isCompl_radical hC, ?_⟩
  rw [hradZero] at heq
  exact ⟨heq.symm.trans (QuadraticMap.IsometryEquiv.prodComm _ _)⟩

omit [Invertible (2 : K)] in
/-- If a quadratic form is isometric to a zero form orthogonally summed with a regular form, the
dimension of its radical is the dimension of the zero summand. -/
theorem finrank_radical_eq_of_equivalent_zero_prod
    {V R W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup R] [Module K R] [FiniteDimensional K R]
    [AddCommGroup W] [Module K W]
    (Q : QuadraticForm K V) (A : QuadraticForm K W) (hA : A.Nondegenerate)
    (e : Q.Equivalent ((0 : QuadraticForm K R).prod A)) :
    Module.finrank K Q.radical = Module.finrank K R := by
  have hradA : ((0 : QuadraticForm K R).prod A).radical =
      (⊤ : Submodule K R).prod (⊥ : Submodule K W) := by
    rw [QuadraticMap.radical_zero_prod, hA.radical_eq_bot]
  have hdimA : Module.finrank K R = Module.finrank K ((0 : QuadraticForm K R).prod A).radical := by
    rw [hradA]
    calc
      Module.finrank K R = Module.finrank K
          ((⊤ : Submodule K R) × (⊥ : Submodule K W)) := by
        rw [Module.finrank_prod, finrank_top, finrank_bot, add_zero]
      _ = Module.finrank K ((⊤ : Submodule K R).prod (⊥ : Submodule K W)) :=
        (Submodule.prodEquiv _ _).finrank_eq.symm
  exact (QuadraticMap.Equivalent.rank_radical_eq e).trans hdimA.symm

omit [Invertible (2 : K)] in
/-- The dimensions of the zero summands agree whenever one quadratic form is isometric to two
orthogonal sums of a zero form and a regular form. -/
theorem finrank_zeroPart_eq_of_equivalent_zero_prod
    {V R S W W' : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup R] [Module K R] [FiniteDimensional K R]
    [AddCommGroup S] [Module K S] [FiniteDimensional K S]
    [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W']
    (Q : QuadraticForm K V) (A : QuadraticForm K W) (B : QuadraticForm K W')
    (hA : A.Nondegenerate) (hB : B.Nondegenerate)
    (e : Q.Equivalent ((0 : QuadraticForm K R).prod A))
    (e' : Q.Equivalent ((0 : QuadraticForm K S).prod B)) :
    Module.finrank K R = Module.finrank K S := by
  rw [← finrank_radical_eq_of_equivalent_zero_prod Q A hA e,
    ← finrank_radical_eq_of_equivalent_zero_prod Q B hB e']

end QuadraticForm
