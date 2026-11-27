/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# Representation by quadratic forms

This file defines both representation of values by a quadratic map and representation of one
quadratic map by another through an injective isometry.  It gives the latter relation its basic
reflexivity, transitivity, and equivalence-invariance API, from which anisotropy is read off as
an isometry invariant.

For scalar values, it defines the represented-unit value set, proves its square-class invariance
and unit-scaling equivariance (`mem_unitValueSet_smul_iff`) together with the invariance of
`Represents` under simultaneous unit scaling of form and target (`represents_smul_same_iff`),
and gives the criterion that, for a form with trivial radical,
representing a unit is equivalent to isotropy after adjoining the one-dimensional form with that
unit as its negative coefficient. A nondegenerate form has trivial radical by Mathlib's
`radical_eq_bot` theorem. A form over a field with trivial radical pairs every nonzero isotropic
vector with an isotropic partner of polar pairing one, so an isotropic form with trivial radical
contains such a pair. If the orthogonal sum of a form with trivial radical and an anisotropic form
on a nonzero space is isotropic, the two summands therefore share a nonzero opposite value; for two
nondegenerate summands, the first with some unit value and the second on a nonzero space, isotropy
of the sum is equivalent to such a shared opposite unit value. These results provide the basic
bridge from value questions to isotropy questions, following Lam, *Introduction to Quadratic Forms
over Fields*, I.2.3 and I.3.5.

An injective isometry identifies its source with the restriction of the target to its image, so
a finite-dimensional regular form splits off along any injective isometry as an orthogonal summand,
with regular complement when the ambient form is regular. Representation is compatible with
orthogonal sums, a zero orthogonal summand of the ambient form does not help to represent a form
with trivial radical, and the line `⟨a⟩` for `a ≠ 0` is represented exactly when the scalar `a` is.
-/

public section

open _root_.QuadraticMap

namespace QuadraticMap

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/-- A value `a : N` is represented by a quadratic map if it is the value of the map at a vector. -/
def Represents (Q : QuadraticMap R M N) (a : N) : Prop := ∃ v, Q v = a

/-- A quadratic map is represented by another if it admits an injective isometry into it. -/
def IsRepresentedBy {M' : Type*} [AddCommMonoid M'] [Module R M']
    (Q : QuadraticMap R M N) (Q' : QuadraticMap R M' N) : Prop :=
  ∃ f : Q →qᵢ Q', Function.Injective f

/-- Representation by a quadratic map is witnessed by an injective linear map preserving the
quadratic map. -/
theorem isRepresentedBy_iff {M' : Type*}
    [AddCommMonoid M'] [Module R M'] (Q : QuadraticMap R M N) (Q' : QuadraticMap R M' N) :
    Q.IsRepresentedBy Q' ↔
      ∃ f : M →ₗ[R] M', Function.Injective f ∧ ∀ x, Q' (f x) = Q x := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.toLinearMap, hf, f.map_app⟩
  · rintro ⟨f, hf, hQ⟩
    exact ⟨⟨f, hQ⟩, hf⟩

/-- The restriction of a quadratic map to a submodule is represented by the ambient map. -/
theorem restrict_isRepresentedBy (Q : QuadraticMap R M N)
    (U : Submodule R M) : (Q.restrict U).IsRepresentedBy Q :=
  (isRepresentedBy_iff _ _).mpr ⟨U.subtype, Subtype.coe_injective, fun _ ↦ rfl⟩

/-- An injective isometry identifies its source with the restriction of its target to its
image. -/
theorem Isometry.equivalent_restrict_range {M' : Type*} [AddCommMonoid M'] [Module R M']
    {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (f : Q →qᵢ Q')
    (hf : Function.Injective f) : Q.Equivalent (Q'.restrict (LinearMap.range f.toLinearMap)) :=
  ⟨{ toLinearEquiv := LinearEquiv.ofInjective f.toLinearMap hf
     map_app' := f.map_app }⟩

/-- The left factor of an orthogonal product is represented by the product. -/
theorem isRepresentedBy_prod_left (Q₁ : QuadraticMap R M N)
    {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] (Q₂ : QuadraticMap R M₂ N) :
    Q₁.IsRepresentedBy (Q₁.prod Q₂) :=
  ⟨Isometry.inl Q₁ Q₂, LinearMap.inl_injective⟩

/-- The right factor of an orthogonal product is represented by the product. -/
theorem isRepresentedBy_prod_right (Q₁ : QuadraticMap R M N)
    {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂] (Q₂ : QuadraticMap R M₂ N) :
    Q₂.IsRepresentedBy (Q₁.prod Q₂) :=
  ⟨Isometry.inr Q₁ Q₂, LinearMap.inr_injective⟩

/-- Every quadratic map is represented by itself. -/
@[refl]
theorem IsRepresentedBy.refl (Q : QuadraticMap R M N) :
    Q.IsRepresentedBy Q :=
  ⟨QuadraticMap.Isometry.id Q, Function.injective_id⟩

/-- Representation of quadratic maps is transitive. -/
@[trans]
theorem IsRepresentedBy.trans
    {M₁ M₂ M₃ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} (h₁₂ : Q₁.IsRepresentedBy Q₂)
    (h₂₃ : Q₂.IsRepresentedBy Q₃) : Q₁.IsRepresentedBy Q₃ := by
  obtain ⟨f, hf⟩ := h₁₂
  obtain ⟨g, hg⟩ := h₂₃
  exact ⟨g.comp f, hg.comp hf⟩

/-- Representations of the two factors give a representation of their orthogonal products. -/
theorem IsRepresentedBy.prod
    {M₁ M₂ M₃ M₄ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
    [AddCommMonoid M₄] [Module R M₄]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} {Q₄ : QuadraticMap R M₄ N}
    (h₁₃ : Q₁.IsRepresentedBy Q₃) (h₂₄ : Q₂.IsRepresentedBy Q₄) :
    (Q₁.prod Q₂).IsRepresentedBy (Q₃.prod Q₄) := by
  obtain ⟨f, hf⟩ := h₁₃
  obtain ⟨g, hg⟩ := h₂₄
  refine ⟨f.prodMap g, fun x y hxy ↦ ?_⟩
  simp only [Isometry.prodMap_apply, Prod.ext_iff] at hxy ⊢
  exact ⟨hf hxy.1, hg hxy.2⟩

/-- An equivalent quadratic map is represented by the other map. -/
theorem Equivalent.isRepresentedBy
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (h : Q₁.Equivalent Q₂) : Q₁.IsRepresentedBy Q₂ := by
  obtain ⟨e⟩ := h
  exact ⟨e.toIsometry, e.injective⟩

/-- A scalar represented by a represented quadratic map is represented by the ambient map. -/
theorem IsRepresentedBy.represents
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} {a : N}
    (h : Q₁.IsRepresentedBy Q₂) (ha : Q₁.Represents a) : Q₂.Represents a := by
  obtain ⟨f, _⟩ := h
  obtain ⟨x, hx⟩ := ha
  exact ⟨f x, (f.map_app x).trans hx⟩

/-- An isometry carries the existence of a vector of unit quadratic value to its target. -/
theorem Isometry.exists_isUnit_apply
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ R} {Q₂ : QuadraticMap R M₂ R}
    (f : Q₁ →qᵢ Q₂) (hQ₁ : ∃ v, IsUnit (Q₁ v)) : ∃ w, IsUnit (Q₂ w) := by
  obtain ⟨v, hv⟩ := hQ₁
  exact ⟨f v, by simpa only [f.map_app] using hv⟩

/-- An ambient quadratic map is isotropic when it represents an isotropic quadratic map. -/
theorem IsRepresentedBy.not_anisotropic
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (h : Q₁.IsRepresentedBy Q₂) (hQ₁ : ¬ Q₁.Anisotropic) : ¬ Q₂.Anisotropic := by
  obtain ⟨f, hf⟩ := h
  rw [QuadraticMap.not_anisotropic_iff_exists] at hQ₁ ⊢
  obtain ⟨x, hx, hQx⟩ := hQ₁
  exact ⟨f x, fun hzero ↦ hx (hf (by simpa using hzero)), (f.map_app x).trans hQx⟩

/-- Anisotropy is an invariant of isometry. -/
theorem Equivalent.anisotropic_iff
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N} (h : Q₁.Equivalent Q₂) :
    Q₁.Anisotropic ↔ Q₂.Anisotropic :=
  ⟨fun h₁ => not_not.mp fun h₂ => h.symm.isRepresentedBy.not_anisotropic h₂ h₁,
    fun h₂ => not_not.mp fun h₁ => h.isRepresentedBy.not_anisotropic h₁ h₂⟩

/-- Replacing either quadratic map by an equivalent one preserves representation. -/
theorem Equivalent.isRepresentedBy_congr
    {M₁ M₂ M₃ M₄ : Type*} [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
    [AddCommMonoid M₄] [Module R M₄]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    {Q₃ : QuadraticMap R M₃ N} {Q₄ : QuadraticMap R M₄ N}
    (h₁₂ : Q₁.Equivalent Q₂) (h₃₄ : Q₃.Equivalent Q₄) :
    Q₁.IsRepresentedBy Q₃ ↔ Q₂.IsRepresentedBy Q₄ :=
  ⟨fun h ↦ h₁₂.symm.isRepresentedBy.trans (h.trans h₃₄.isRepresentedBy),
    fun h ↦ h₁₂.isRepresentedBy.trans (h.trans h₃₄.symm.isRepresentedBy)⟩

/-- Every quadratic map represents zero. -/
@[simp]
theorem represents_zero (Q : QuadraticMap R M N) : Represents Q 0 :=
  ⟨0, Q.map_zero⟩

/-- Representation is the same as membership in the range of the quadratic map. -/
theorem represents_iff (Q : QuadraticMap R M N) (a : N) :
    Represents Q a ↔ a ∈ Set.range Q :=
  Iff.rfl

/-- The set of represented units of a scalar-valued quadratic map.

This is the classical value set `D(Q)` over a field; over a general commutative semiring it is
the set of units represented by `Q`, rather than the full value set. -/
def unitValueSet (Q : QuadraticMap R M R) : Set Rˣ :=
  {a | Represents Q (a : R)}

/-- Membership in `unitValueSet` is representation of the underlying scalar. -/
@[simp]
theorem mem_unitValueSet {Q : QuadraticMap R M R} {a : Rˣ} :
    a ∈ unitValueSet Q ↔ Represents Q (a : R) :=
  Iff.rfl

/-- Representation is preserved by an isometric equivalence of quadratic maps. -/
theorem IsometryEquiv.represents_iff
    {M₁ M₂ N : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N]
    [Module R M₁] [Module R M₂] [Module R N]
    {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
    (e : Q₁.IsometryEquiv Q₂) (a : N) :
    Represents Q₁ a ↔ Represents Q₂ a := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨e v, (e.map_app v).trans hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨e.symm v, (e.symm.map_app v).trans hv⟩

/-- Equivalent quadratic forms have the same represented-unit value set. -/
theorem Equivalent.unitValueSet_eq
    {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticMap R M₁ R} {Q₂ : QuadraticMap R M₂ R}
    (h : Q₁.Equivalent Q₂) : unitValueSet Q₁ = unitValueSet Q₂ := by
  obtain ⟨e⟩ := h
  ext a
  rw [mem_unitValueSet, mem_unitValueSet]
  exact e.represents_iff a

/-- The sum of a value represented by the first factor and a value represented by the second is
represented by their orthogonal sum. -/
theorem Represents.prod
    {M₁ M₂ P : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid P]
    [Module R M₁] [Module R M₂] [Module R P]
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {a b : P}
    (h₁ : Represents Q₁ a) (h₂ : Represents Q₂ b) :
    Represents (Q₁.prod Q₂) (a + b) := by
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  exact ⟨(v, w), by simp [QuadraticMap.prod_apply, hv, hw]⟩

/-- If one factor represents a nonzero value `a` and the other represents `-a`, then their
orthogonal product is isotropic. -/
theorem not_anisotropic_prod_of_represents_neg
    {M₁ M₂ P : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommGroup P]
    [Module R M₁] [Module R M₂] [Module R P]
    {Q₁ : QuadraticMap R M₁ P} {Q₂ : QuadraticMap R M₂ P} {a : P}
    (h₁ : Represents Q₁ a) (h₂ : Represents Q₂ (-a)) (ha : a ≠ 0) :
    ¬(Q₁.prod Q₂).Anisotropic := by
  obtain ⟨v, hv⟩ := h₁
  obtain ⟨w, hw⟩ := h₂
  intro h
  have hvw := h (v, w) (by rw [QuadraticMap.prod_apply, hv, hw, add_neg_cancel])
  exact ha (by rw [← hv, (Prod.mk_eq_zero.mp hvw).1, map_zero])

/-- Representing a value is preserved after multiplying it by the square of any scalar. -/
theorem Represents.smul_mul_self
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {Q : QuadraticMap R M N} {a : N}
    (h : Represents Q a) (b : R) : Represents Q ((b * b) • a) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨b • v, by rw [Q.map_smul, hv]⟩

/-- Representation is invariant under multiplication by the square of a unit. -/
@[simp] theorem represents_smul_mul_self_iff
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] (Q : QuadraticMap R M N) (a : N) (b : Rˣ) :
    Represents Q (((b : R) * b) • a) ↔ Represents Q a := by
  constructor
  · intro h
    simpa [smul_smul, mul_assoc, mul_comm, mul_left_comm] using
      h.smul_mul_self (↑(b⁻¹ : Rˣ) : R)
  · exact fun h => h.smul_mul_self (b : R)

/-- Multiplying a represented scalar by the square of a unit preserves representation. -/
@[simp] theorem represents_mul_sq_iff (Q : QuadraticMap R M R) (a : R)
    (b : Rˣ) :
    Represents Q (a * (b : R) ^ 2) ↔ Represents Q a := by
  simpa [smul_eq_mul, pow_two, mul_comm] using
    (represents_smul_mul_self_iff Q a b)

/-- Membership in `unitValueSet` is invariant under multiplication by a unit square. -/
theorem mem_unitValueSet_mul_sq_iff (Q : QuadraticMap R M R) (a b : Rˣ) :
    (a * b ^ 2) ∈ unitValueSet Q ↔ a ∈ unitValueSet Q := by
  simpa only [mem_unitValueSet, Units.val_mul, Units.val_pow_eq_pow_val] using
    (represents_mul_sq_iff Q (a : R) b)

/-- Scaling a quadratic map and the target value by the same scalar preserves representation. -/
theorem Represents.smul_same {S M N : Type*} [Monoid S] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [DistribMulAction S N] [SMulCommClass S R N]
    {Q : QuadraticMap R M N} {a : N} (h : Represents Q a) (c : S) :
    Represents (c • Q) (c • a) := by
  obtain ⟨v, hv⟩ := h
  exact ⟨v, by rw [smul_apply, hv]⟩

/-- Scaling a quadratic map and the target value by the same unit gives an equivalent
representation condition. -/
@[simp]
theorem represents_smul_same_iff {S M N : Type*} [Monoid S] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [DistribMulAction S N] [SMulCommClass S R N]
    {c : S} (hc : IsUnit c) (Q : QuadraticMap R M N) (a : N) :
    Represents (c • Q) (c • a) ↔ Represents Q a := by
  simp only [Represents, smul_apply, hc.smul_left_cancel]

/-- Scaling a scalar-valued quadratic map by a unit `c` shifts its represented-unit value set by
multiplication by `c`. -/
theorem mem_unitValueSet_smul_iff (Q : QuadraticMap R M R) (c a : Rˣ) :
    a ∈ unitValueSet ((c : R) • Q) ↔ c⁻¹ * a ∈ unitValueSet Q := by
  have ha : (a : R) = (c : R) • ((c⁻¹ * a : Rˣ) : R) := by simp [smul_eq_mul]
  rw [mem_unitValueSet, mem_unitValueSet, ha]
  exact represents_smul_same_iff c.isUnit Q _

/-- Over a semifield, scaling a quadratic form by a nonzero scalar `c` represents `a` if and only
if the unscaled form represents `c⁻¹ * a`. -/
theorem represents_smul_iff {K V : Type*} [Semifield K] [AddCommMonoid V]
    [Module K V] {Q : QuadraticForm K V} {c : K} (hc : c ≠ 0) (a : K) :
    Represents (c • Q) a ↔ Represents Q (c⁻¹ * a) := by
  have ha : a = c • (c⁻¹ * a) := by simp [smul_eq_mul, mul_inv_cancel_left₀ hc]
  conv_lhs => rw [ha]
  exact represents_smul_same_iff hc.isUnit Q (c⁻¹ * a)

/-- Over a semifield, a quadratic form representing a nonzero scalar `a` represents every `b` for
which `b / a` is a square. -/
theorem Represents.of_isSquare_div {K V : Type*} [Semifield K] [AddCommMonoid V]
    [Module K V] {Q : QuadraticForm K V} {a b : K}
    (h : Represents Q a) (ha : a ≠ 0) (hab : IsSquare (b / a)) : Represents Q b := by
  obtain ⟨r, hr⟩ := hab
  simpa only [← hr, smul_eq_mul, div_mul_cancel₀ b ha] using h.smul_mul_self r

/-- A zero orthogonal summand does not help to represent a form with trivial radical: such a
form represented by `Q ⊥ 0` is already represented by `Q`. -/
theorem IsRepresentedBy.of_prod_zero {R M₁ M₂ M₃ P : Type*} [CommRing R] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup P] [Module R P] {Q₁ : QuadraticMap R M₁ P} {Q : QuadraticMap R M₂ P}
    (hQ₁ : Q₁.radical = ⊥) (h : Q₁.IsRepresentedBy (Q.prod (0 : QuadraticMap R M₃ P))) :
    Q₁.IsRepresentedBy Q := by
  obtain ⟨f, -⟩ := h
  exact ⟨(Isometry.fst M₃ Q).comp f,
    ((Isometry.fst M₃ Q).comp f).injective_of_radical_eq_bot hQ₁⟩

/-- The line `⟨a⟩`, the form `t ↦ a t²` on `R`, is represented by a quadratic form over a domain
exactly when the form represents the nonzero scalar `a`. -/
theorem isRepresentedBy_smul_sq_iff {R V : Type*} [CommRing R] [IsDomain R] [AddCommGroup V]
    [Module R V] (Q : QuadraticForm R V) {a : R} (ha : a ≠ 0) :
    (a • sq : QuadraticForm R R).IsRepresentedBy Q ↔ Represents Q a := by
  refine ⟨fun h ↦ h.represents ⟨1, by simp⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  refine (isRepresentedBy_iff _ _).mpr
    ⟨LinearMap.toSpanSingleton R V x, fun s t hst ↦ ?_, fun t ↦ ?_⟩
  · -- `Q ((s - t) • x) = (s - t)² a` vanishes, and `a ≠ 0`.
    have h0 : Q ((s - t) • x) = 0 := by simpa [sub_smul] using congrArg Q (sub_eq_zero.mpr hst)
    simpa [QuadraticMap.map_smul, hx, ha, sub_eq_zero] using h0
  · simp [QuadraticMap.map_smul, hx, mul_comm]

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **A finite-dimensional regular form splits off along an injective isometry.** If `f` is an
injective isometry from a finite-dimensional regular form `Q₁` into `Q`, then `Q ≅ Q₁ ⊥ Q|_P`,
where `P` is the orthogonal complement of the image of `f`. -/
theorem Isometry.equivalent_prod_restrict_orthogonal [Invertible (2 : K)]
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    {Q : QuadraticForm K V} {Q₁ : QuadraticForm K V₁} (f : Q₁ →qᵢ Q)
    (hf : Function.Injective f) (hQ₁ : Q₁.Nondegenerate) :
    Q.Equivalent (Q₁.prod (Q.restrict
      (LinearMap.BilinForm.orthogonal Q.polarBilin (LinearMap.range f.toLinearMap)))) := by
  obtain ⟨e⟩ := f.equivalent_restrict_range hf
  exact ⟨(IsometryEquiv.prodRestrictOrthogonal Q _
    (e.nondegenerate_iff.mp hQ₁).isCompl_orthogonal).symm.trans
      (e.symm.prod (IsometryEquiv.refl _))⟩

/-- **A represented finite-dimensional regular form splits off.** If a finite-dimensional regular
form `Q₁` is represented by a regular form `Q`, then `Q ≅ Q₁ ⊥ Q|_P` for a subspace `P` on which
`Q` is regular, namely the orthogonal complement of the image of `Q₁`. -/
theorem IsRepresentedBy.exists_equivalent_prod [Invertible (2 : K)]
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    {Q : QuadraticForm K V} {Q₁ : QuadraticForm K V₁} (h : Q₁.IsRepresentedBy Q)
    (hQ₁ : Q₁.Nondegenerate) (hQ : Q.Nondegenerate) :
    ∃ P : Submodule K V, (Q.restrict P).Nondegenerate ∧ Q.Equivalent (Q₁.prod (Q.restrict P)) := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨e⟩ := f.equivalent_restrict_range hf
  exact ⟨_, hQ.nondegenerate_restrict_orthogonal (e.nondegenerate_iff.mp hQ₁),
    f.equivalent_prod_restrict_orthogonal hf hQ₁⟩

/-- For a quadratic form with trivial radical, every nonzero isotropic vector `x` has an
isotropic partner `y` with `polar Q x y = 1`, so that `x, y` is a hyperbolic pair. -/
theorem exists_isotropic_polar_eq_one_of_radical_eq_bot
    {Q : QuadraticForm K V} (hQ : Q.radical = ⊥) {x : V} (hx : x ≠ 0) (hxQ : Q x = 0) :
    ∃ y : V, Q y = 0 ∧ polar Q x y = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, polar Q x w ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    have hxrad : x ∈ Q.radical := by
      rw [mem_radical_iff']
      refine ⟨hxQ, fun z ↦ ?_⟩
      rw [QuadraticMap.map_add Q, hxQ, h z, zero_add, add_zero]
    rw [hQ] at hxrad
    exact hxrad
  let z := (polar Q x w)⁻¹ • w
  have hxz : polar Q x z = 1 := by simp [z, polar_smul_right, hw]
  refine ⟨z - Q z • x, ?_, ?_⟩
  · simp [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add, Q.map_smul, hxQ,
      polar_smul_right, polar_comm Q z x, hxz, smul_eq_mul]
  · simp [polar_sub_right, polar_smul_right, polar_self, hxQ, hxz]

/-- An isotropic quadratic form with trivial radical contains two isotropic vectors whose polar
pairing is one. -/
theorem exists_isotropic_pair_of_radical_eq_bot
    {Q : QuadraticForm K V} (hQ : Q.radical = ⊥) (hiso : ¬Q.Anisotropic) :
    ∃ x y : V, x ≠ 0 ∧ Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1 := by
  obtain ⟨x, hx, hxQ⟩ := (not_anisotropic_iff_exists Q).mp hiso
  obtain ⟨y, hyQ, hxy⟩ := exists_isotropic_polar_eq_one_of_radical_eq_bot hQ hx hxQ
  exact ⟨x, y, hx, hxQ, hyQ, hxy⟩

/-- A quadratic form with trivial radical and a nonzero isotropic vector represents every scalar. -/
theorem represents_of_radical_eq_bot_of_not_anisotropic
    (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) (hiso : ¬Q.Anisotropic) (a : K) :
    Represents Q a := by
  obtain ⟨x, y, -, hxQ, hyQ, hxy⟩ := exists_isotropic_pair_of_radical_eq_bot hQ hiso
  exact ⟨a • x + y, by simp [QuadraticMap.map_add, Q.map_smul, polar_smul_left, hxQ, hyQ,
    hxy, smul_eq_mul]⟩

/-- A nondegenerate quadratic form with a nonzero isotropic vector represents every scalar. -/
theorem represents_of_nondegenerate_of_not_anisotropic
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hiso : ¬Q.Anisotropic) (a : K) :
    Represents Q a :=
  represents_of_radical_eq_bot_of_not_anisotropic Q hQ.radical_eq_bot hiso a

/-- Over a field, a quadratic form `Q` with trivial radical represents `-c` as soon as, if `Q` is
anisotropic, `c` lies in the square class of some nonzero `c₀` that is the negative of a value
of `Q`. -/
theorem _root_.QuadraticForm.represents_neg_of_forall_anisotropic (Q : QuadraticForm K V)
    (hQ : Q.radical = ⊥) (c : K)
    (h : Q.Anisotropic → ∃ c₀ y, c₀ ≠ 0 ∧ c₀ = -Q y ∧ IsSquare (c / c₀)) :
    Represents Q (-c) := by
  by_cases han : Q.Anisotropic
  · obtain ⟨c₀, y, hc₀, hxy, hsq⟩ := h han
    have hrep : Represents Q (-c₀) :=
      (represents_iff _ _).mpr ⟨y, (neg_eq_iff_eq_neg.mpr hxy).symm⟩
    refine hrep.of_isSquare_div (neg_ne_zero.mpr hc₀) ?_
    simpa [neg_div_neg_eq] using hsq
  · exact represents_of_radical_eq_bot_of_not_anisotropic _ hQ han _

/-- If the orthogonal sum of a form with trivial radical and an anisotropic form on a nonzero
space is isotropic, then some nonzero value of the first form is the negative of a value of the
second (O'Meara, *Introduction to Quadratic Forms*, 66:1). -/
theorem Anisotropic.exists_ne_zero_eq_neg_of_not_anisotropic_prod
    {V' : Type*} [AddCommGroup V'] [Module K V'] [Nontrivial V']
    {U : QuadraticForm K V} {W : QuadraticForm K V'} (hW : W.Anisotropic)
    (hU : U.radical = ⊥) (h : ¬(U.prod W).Anisotropic) :
    ∃ x y, U x ≠ 0 ∧ U x = -W y := by
  -- An anisotropic `U` forces both components of an isotropic vector of the sum to be nonzero;
  -- an isotropic `U` is universal and represents the negative of any nonzero value of `W`.
  by_cases hUiso : U.Anisotropic
  · obtain ⟨⟨x, y⟩, hxy, hzero⟩ := (not_anisotropic_iff_exists _).mp h
    rw [QuadraticMap.prod_apply, add_eq_zero_iff_eq_neg] at hzero
    refine ⟨x, y, fun hx ↦ hxy ?_, hzero⟩
    have hx0 : x = 0 := hUiso x hx
    have hy0 : y = 0 := hW y (by simpa [hx0] using hzero.symm)
    simp [hx0, hy0]
  · obtain ⟨y, hy⟩ := exists_ne (0 : V')
    obtain ⟨x, hx⟩ := represents_of_radical_eq_bot_of_not_anisotropic U hU hUiso (-W y)
    exact ⟨x, y, by simpa [hx] using fun h ↦ hy (hW y h), hx⟩

/-- A unit is represented exactly when adjoining its negative line makes the form isotropic, under
triviality of the quadratic radical.

The added line is the one-dimensional form `x ↦ -a * x²`, written as a scalar multiple of
`QuadraticMap.sq`. -/
theorem mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot
    (Q : QuadraticForm K V) (hQ : Q.radical = ⊥) (a : Kˣ) :
    a ∈ unitValueSet Q ↔
      ¬(Q.prod ((-(a : K)) • (QuadraticMap.sq : QuadraticForm K K))).Anisotropic := by
  constructor
  · rw [mem_unitValueSet, represents_iff, Set.mem_range]
    rintro ⟨v, hv⟩
    rw [not_anisotropic_iff_exists]
    refine ⟨(v, 1), ?_, ?_⟩
    · simp
    · simp [QuadraticMap.prod_apply, hv]
  · intro h
    rw [mem_unitValueSet, represents_iff, Set.mem_range]
    obtain ⟨⟨v, t⟩, hvt, hzero⟩ := (not_anisotropic_iff_exists _).mp h
    simp only [QuadraticMap.prod_apply, smul_apply, QuadraticMap.sq_apply] at hzero
    by_cases ht : t = 0
    · have hv : v ≠ 0 := by
        intro hv
        apply hvt
        simp [hv, ht]
      have hvQ : Q v = 0 := by simpa [ht] using hzero
      obtain ⟨w, hw⟩ := represents_of_radical_eq_bot_of_not_anisotropic Q
        hQ ((not_anisotropic_iff_exists Q).mpr ⟨v, hv, hvQ⟩) (a : K)
      exact ⟨w, hw⟩
    · have hvQ : Q v = (a : K) * (t * t) := by
        simpa [smul_eq_mul] using eq_neg_of_add_eq_zero_left hzero
      refine ⟨t⁻¹ • v, ?_⟩
      rw [Q.map_smul, smul_eq_mul, hvQ]
      field_simp

/-- For a nondegenerate form, a unit is represented exactly when adjoining its negative line
makes the form isotropic. -/
theorem mem_unitValueSet_iff_not_anisotropic_prod
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (a : Kˣ) :
    a ∈ unitValueSet Q ↔
      ¬(Q.prod ((-(a : K)) • (QuadraticMap.sq : QuadraticForm K K))).Anisotropic :=
  mem_unitValueSet_iff_not_anisotropic_prod_of_radical_eq_bot Q hQ.radical_eq_bot a

/-- The orthogonal sum of a form `Q₁` with trivial radical and some unit value and a form `Q₂`
with trivial radical on a nonzero space is isotropic exactly when some unit value `x` of `Q₁` has
`-x` a value of `Q₂`. -/
theorem not_anisotropic_prod_iff_exists_mem_unitValueSet_neg_mem
    {V' : Type*} [AddCommGroup V'] [Module K V'] [Nontrivial V']
    {Q₁ : QuadraticForm K V} {Q₂ : QuadraticForm K V'} (hQ₁ : Q₁.radical = ⊥)
    (hQ₂ : Q₂.radical = ⊥) (h : (unitValueSet Q₁).Nonempty) :
    ¬(Q₁.prod Q₂).Anisotropic ↔ ∃ x : Kˣ, x ∈ unitValueSet Q₁ ∧ -x ∈ unitValueSet Q₂ := by
  constructor
  · intro hiso
    by_cases hani : Q₂.Anisotropic
    · obtain ⟨x, y, hx, hxy⟩ := hani.exists_ne_zero_eq_neg_of_not_anisotropic_prod hQ₁ hiso
      refine ⟨Units.mk0 _ hx, mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨x, rfl⟩),
        mem_unitValueSet.mpr ((represents_iff _ _).mpr ⟨y, ?_⟩)⟩
      rw [Units.val_neg, Units.val_mk0, hxy, neg_neg]
    · -- An isotropic `Q₂` represents every scalar, in particular the negative of a unit value of
      -- `Q₁`.
      obtain ⟨a, ha⟩ := h
      refine ⟨a, ha, ?_⟩
      rw [mem_unitValueSet, Units.val_neg]
      exact represents_of_radical_eq_bot_of_not_anisotropic _ hQ₂ hani _
  · rintro ⟨x, hx₁, hx₂⟩
    exact not_anisotropic_prod_of_represents_neg (mem_unitValueSet.mp hx₁)
      (by simpa using mem_unitValueSet.mp hx₂) x.ne_zero

end QuadraticMap
