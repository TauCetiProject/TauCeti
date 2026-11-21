/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Norm.Quadratic

/-!
# Self-adjoint parts over a quadratic algebra with involution

Let `E` be a commutative algebra over a field `F` with an involution `star`, such that `F` is
exactly the fixed ring of `star` and `E` contains a unit `t` with `star t = -t`. Over a field of
characteristic different from `2` this describes a quadratic étale algebra `E / F` with its
nontrivial involution, such as `ℂ / ℝ` with `t = i`, a quadratic field extension `F(√d) / F`
with `t = √d`, or the split algebra `F × F` with `t = (1, -1)`. (For the split algebra the
involution is the swap of the two factors; Mathlib's `star` on a product acts factorwise, so this
case needs a carrier whose `star` is the swap.)

For an `E`-module `A` with a compatible conjugate-linear involution `star`, such as the matrices
over `E` with conjugate transposition, the self-adjoint elements form an `F`-structure on `A`:

* every scalar is `a + b t` with `a b : F` (`TauCeti.exists_algebraMap_add_algebraMap_mul_eq`),
  so `E` is a quadratic algebra over `F` (`TauCeti.isQuadraticExtension_of_mem_skewAdjoint`)
  with norm `N c = star c * c` (`TauCeti.algebraMap_norm_eq_star_mul_self`);
* multiplication by `t` identifies the skew-adjoint elements of `A` with the self-adjoint ones
  (`TauCeti.skewAdjointEquivSelfAdjoint`);
* `c ⊗ₜ x ↦ c • x` identifies `E ⊗[F] selfAdjoint A` with `A`
  (`TauCeti.selfAdjointBaseChangeEquiv`), so the `F`-dimension of the self-adjoint part is the
  `E`-dimension of `A` (`TauCeti.finrank_selfAdjoint_submodule_eq`);
* an `E`-linear map `f` commuting with `star` restricts to `F`-linear maps of the self-adjoint and
  skew-adjoint parts, and both restrictions have determinant `det f`
  (`LinearMap.algebraMap_det_restrictSelfAdjoint`, `LinearMap.det_restrictSkewAdjoint`).

The determinant statement is what computes the modulus of a Siegel parabolic subgroup of a
unitary group: its unipotent radical is a space of hermitian (or skew-hermitian) matrices, and the
Levi factor acts on it through an `E`-linear map commuting with conjugate transposition.

For `ℂ / ℝ` and an arbitrary conjugation in place of `star`, the descent statement is
`TauCeti.realPointsEquiv`.
-/

public section

open scoped TensorProduct

open Module (finrank)

namespace TauCeti

section CommRing

variable {F E : Type*} [CommRing F] [StarMul F] [TrivialStar F] [CommRing E] [StarRing E]
  [Algebra F E] {t : Eˣ}

/-- The inverse of a skew-adjoint unit is skew-adjoint. -/
private theorem inv_mem_skewAdjoint (ht : (t : E) ∈ skewAdjoint E) :
    ((t⁻¹ : Eˣ) : E) ∈ skewAdjoint E := by
  rw [skewAdjoint.mem_iff] at ht ⊢
  have h1 : star ((t⁻¹ : Eˣ) : E) * star (t : E) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  rw [ht] at h1
  linear_combination (-((t⁻¹ : Eˣ) : E)) * h1 - star ((t⁻¹ : Eˣ) : E) * t.mul_inv

variable [Invertible (2 : F)] in
/-- Splitting off the self-adjoint part with the help of a skew-adjoint unit `t`: every element
is `re x + t • re (t⁻¹ • x)`, where `re` is the self-adjoint part `(x + star x) / 2`. -/
theorem selfAdjointPart_add_smul_selfAdjointPart_inv_smul {A : Type*} [AddCommGroup A]
    [Module F A] [Module E A] [IsScalarTower F E A] [StarAddMonoid A] [StarModule F A]
    [StarModule E A] (ht : (t : E) ∈ skewAdjoint E) (x : A) :
    (selfAdjointPart F x : A) + (t : E) • (selfAdjointPart F (((t⁻¹ : Eˣ) : E) • x) : A) = x := by
  have hinv := skewAdjoint.mem_iff.mp (inv_mem_skewAdjoint ht)
  simp only [selfAdjointPart_apply_coe, star_smul, hinv, smul_add, neg_smul,
    smul_comm (t : E) (⅟2 : F), ← mul_smul, Units.mul_inv, one_smul, ← smul_neg]
  rw [add_add_add_comm, smul_neg, add_neg_cancel, add_zero, invOf_two_smul_add_invOf_two_smul]

variable [StarModule F E] in
/-- Scalars from `F` are self-adjoint in `E`. -/
private theorem star_algebraMap (a : F) : star (algebraMap F E a) = algebraMap F E a := by
  rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, star_trivial]

variable [StarModule F E] [Invertible (2 : F)] in
/-- If `F` is the fixed ring of the involution of `E` and `t` is a skew-adjoint unit, every
element of `E` is `a + b t` with `a b : F`. -/
theorem exists_algebraMap_add_algebraMap_mul_eq
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (c : E) :
    ∃ a b : F, algebraMap F E a + algebraMap F E b * t = c := by
  obtain ⟨a, ha⟩ := hfix _ (selfAdjointPart F c).property
  obtain ⟨b, hb⟩ := hfix _ (selfAdjointPart F (((t⁻¹ : Eˣ) : E) • c)).property
  refine ⟨a, b, ?_⟩
  rw [ha, hb, mul_comm, ← smul_eq_mul]
  exact selfAdjointPart_add_smul_selfAdjointPart_inv_smul ht c


variable {A : Type*} [AddCommGroup A] [Module F A] [Module E A] [IsScalarTower F E A]
  [StarAddMonoid A] [StarModule F A] [StarModule E A]

/-- **Hermitian coordinates on skew-adjoint elements**: multiplication by a skew-adjoint unit `t`
of `E` identifies the skew-adjoint elements of `A` with the self-adjoint ones. -/
noncomputable def skewAdjointEquivSelfAdjoint (t : Eˣ) (ht : (t : E) ∈ skewAdjoint E) :
    skewAdjoint.submodule F A ≃ₗ[F] selfAdjoint.submodule F A where
  toFun x := ⟨(t : E) • (x : A), isSelfAdjoint_smul_of_mem_skewAdjoint ht x.property⟩
  invFun y := ⟨((t⁻¹ : Eˣ) : E) • (y : A),
    IsSelfAdjoint.smul_mem_skewAdjoint (inv_mem_skewAdjoint ht) y.property⟩
  map_add' x y := Subtype.ext (smul_add _ _ _)
  map_smul' a x := Subtype.ext (smul_comm _ _ _)
  left_inv x := Subtype.ext (by simp [smul_smul])
  right_inv y := Subtype.ext (by simp [smul_smul])

@[simp]
theorem coe_skewAdjointEquivSelfAdjoint_apply {t : Eˣ} (ht : (t : E) ∈ skewAdjoint E)
    (x : skewAdjoint.submodule F A) :
    (skewAdjointEquivSelfAdjoint t ht x : A) = (t : E) • (x : A) :=
  (rfl)

@[simp]
theorem coe_skewAdjointEquivSelfAdjoint_symm_apply {t : Eˣ} (ht : (t : E) ∈ skewAdjoint E)
    (y : selfAdjoint.submodule F A) :
    ((skewAdjointEquivSelfAdjoint t ht).symm y : A) = ((t⁻¹ : Eˣ) : E) • (y : A) :=
  (rfl)

end CommRing

section Field

variable {F E : Type*} [Field F] [StarMul F] [TrivialStar F] [CommRing E] [StarRing E]
  [Algebra F E] [StarModule F E] [Invertible (2 : F)] {t : Eˣ}

/-- If `F` is the fixed ring of the involution of `E` and `t` is a skew-adjoint unit, then `E` is
a quadratic algebra over `F`, with basis `1, t`. -/
theorem isQuadraticExtension_of_mem_skewAdjoint [Nontrivial E]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) : Algebra.IsQuadraticExtension F E := by
  have hli : LinearIndependent F ![1, (t : E)] := by
    refine LinearIndependent.pair_iff.mpr fun a b hab ↦ ?_
    have hstar := congrArg star hab
    rw [star_add, star_smul, star_smul, star_one, skewAdjoint.mem_iff.mp ht, star_trivial,
      star_trivial, star_zero, smul_neg] at hstar
    have hinj := (algebraMap F E).injective
    have ha : algebraMap F E (2 * a) = 0 := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab hstar
      rw [map_mul, map_ofNat]
      linear_combination hab + hstar
    have ha' : a = 0 := by
      rw [map_eq_zero_iff _ hinj, mul_eq_zero] at ha
      exact ha.resolve_left (Invertible.ne_zero 2)
    subst ha'
    rw [zero_smul, zero_add, Algebra.smul_def] at hab
    have hb : algebraMap F E b = 0 := by simpa using congrArg (· * ((t⁻¹ : Eˣ) : E)) hab
    exact ⟨rfl, (map_eq_zero_iff _ hinj).mp hb⟩
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![1, (t : E)]) := by
    rintro c -
    obtain ⟨a, b, rfl⟩ := exists_algebraMap_add_algebraMap_mul_eq hfix ht c
    rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let B := Module.Basis.mk hli hsp
  exact { toFree := .of_basis B
          finrank_eq_two' := by rw [Module.finrank_eq_card_basis B, Fintype.card_fin] }

/-- **The norm of a quadratic algebra with involution** is `N c = star c * c`, when `F` is the
fixed ring of the involution and there is a skew-adjoint unit. -/
theorem algebraMap_norm_eq_star_mul_self
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (c : E) :
    algebraMap F E (Algebra.norm F c) = star c * c := by
  nontriviality E
  have := isQuadraticExtension_of_mem_skewAdjoint hfix ht
  have htt := skewAdjoint.mem_iff.mp ht
  obtain ⟨d, hd⟩ := hfix ((t : E) ^ 2) (by rw [IsSelfAdjoint, star_pow, htt, neg_sq])
  have hnot : (t : E) ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, ha⟩
    have hstar : star (t : E) = t := by rw [← ha, star_algebraMap]
    have h2 : (2 : E) * t = 0 := by linear_combination -(htt.symm.trans hstar)
    have h22 : algebraMap F E (⅟2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul, invOf_mul_self, map_one]
    exact t.ne_zero (by linear_combination algebraMap F E (⅟2) * h2 - (t : E) * h22)
  obtain ⟨a, b, rfl⟩ := exists_algebraMap_add_algebraMap_mul_eq hfix ht c
  rw [Algebra.IsQuadraticExtension.norm_algebraMap_add_algebraMap_mul_of_sq_eq hnot hd.symm,
    star_add, star_mul, htt, star_algebraMap, star_algebraMap, map_sub, map_mul, map_pow,
    map_pow, hd]
  ring

variable {A : Type*} [AddCommGroup A] [Module F A] [Module E A] [IsScalarTower F E A]
  [StarAddMonoid A] [StarModule F A] [StarModule E A]


omit [Module E A] [IsScalarTower F E A] [StarModule E A] in
/-- Every element of `E ⊗[F] selfAdjoint A` is `1 ⊗ₜ p + t ⊗ₜ q`. -/
private theorem exists_one_tmul_add_tmul_eq
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (z : E ⊗[F] selfAdjoint.submodule F A) :
    ∃ p q : selfAdjoint.submodule F A, (1 : E) ⊗ₜ p + (t : E) ⊗ₜ q = z := by
  induction z using TensorProduct.inductionOn with
  | tmul c s =>
    obtain ⟨a, b, rfl⟩ := exists_algebraMap_add_algebraMap_mul_eq hfix ht c
    refine ⟨a • s, b • s, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', ← TensorProduct.add_tmul, Algebra.smul_def, Algebra.smul_def,
      mul_one]
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.tmul_add]; abel⟩

/-- `c ⊗ₜ x ↦ c • x` is injective on `E ⊗[F] selfAdjoint A`. -/
private theorem liftBaseChange_subtype_selfAdjoint_injective
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) :
    Function.Injective ((selfAdjoint.submodule F A).subtype.liftBaseChange E) := by
  refine (injective_iff_map_eq_zero _).mpr fun z hz ↦ ?_
  obtain ⟨p, q, rfl⟩ := exists_one_tmul_add_tmul_eq hfix ht z
  simp only [map_add, LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply] at hz
  have hstar := congrArg star hz
  rw [star_add, star_smul, skewAdjoint.mem_iff.mp ht, p.property.star_eq, q.property.star_eq,
    neg_smul, star_zero] at hstar
  have hp : (p : A) = 0 := by
    rw [← invOf_two_smul_add_invOf_two_smul F (p : A), ← smul_add]
    rw [show (p : A) + p = ((p : A) + (t : E) • q) + ((p : A) + -((t : E) • q)) by abel, hz,
      hstar, add_zero, smul_zero]
  rw [hp, zero_add] at hz
  have hq : (q : A) = 0 := by
    rw [← one_smul E (q : A), ← t.inv_mul, mul_smul, hz, smul_zero]
  rw [show p = 0 from Subtype.ext hp, show q = 0 from Subtype.ext hq, TensorProduct.tmul_zero,
    TensorProduct.tmul_zero, add_zero]

omit [StarModule F E] in
/-- `c ⊗ₜ x ↦ c • x` is surjective onto `A`, by
`TauCeti.selfAdjointPart_add_smul_selfAdjointPart_inv_smul`. -/
private theorem liftBaseChange_subtype_selfAdjoint_surjective (ht : (t : E) ∈ skewAdjoint E) :
    Function.Surjective ((selfAdjoint.submodule F A).subtype.liftBaseChange E) := fun x ↦
  ⟨(1 : E) ⊗ₜ ⟨_, (selfAdjointPart F x).property⟩ +
      (t : E) ⊗ₜ ⟨_, (selfAdjointPart F (((t⁻¹ : Eˣ) : E) • x)).property⟩, by
    simp only [map_add, LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply]
    exact selfAdjointPart_add_smul_selfAdjointPart_inv_smul ht x⟩

variable (A) in
/-- **The self-adjoint elements form an `F`-structure**: if `F` is the fixed ring of the
involution of `E` and `E` has a skew-adjoint unit, then `c ⊗ₜ x ↦ c • x` is an isomorphism
`E ⊗[F] selfAdjoint A ≃ₗ[E] A`. -/
noncomputable def selfAdjointBaseChangeEquiv
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) :
    E ⊗[F] selfAdjoint.submodule F A ≃ₗ[E] A :=
  LinearEquiv.ofBijective ((selfAdjoint.submodule F A).subtype.liftBaseChange E)
    ⟨liftBaseChange_subtype_selfAdjoint_injective hfix ht,
      liftBaseChange_subtype_selfAdjoint_surjective ht⟩

@[simp]
theorem selfAdjointBaseChangeEquiv_tmul
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) (c : E) (x : selfAdjoint.submodule F A) :
    selfAdjointBaseChangeEquiv A hfix ht (c ⊗ₜ x) = c • (x : A) :=
  (rfl)

variable (F A) in
/-- **The self-adjoint part has the dimension of the whole module**: the `F`-dimension of the
self-adjoint elements of `A` is the `E`-dimension of `A`. For the `n × n` matrices over a
quadratic algebra `E / F` this is `n ^ 2`. -/
theorem finrank_selfAdjoint_submodule_eq [Nontrivial E]
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E))
    (ht : (t : E) ∈ skewAdjoint E) :
    finrank F (selfAdjoint.submodule F A) = finrank E A := by
  rw [← (selfAdjointBaseChangeEquiv A hfix ht).finrank_eq, Module.finrank_baseChange]

end Field

end TauCeti

namespace LinearMap

open TauCeti

variable {E A : Type*} [CommRing E] [AddCommGroup A] [Module E A] [StarAddMonoid A]

section CommRing

variable {F : Type*} [CommRing F] [StarMul F] [TrivialStar F] [Algebra F E] [Module F A]
  [IsScalarTower F E A] [StarModule F A]

variable (F) in
/-- An `E`-linear map commuting with `star`, restricted to an `F`-linear endomorphism of the
self-adjoint elements. -/
def restrictSelfAdjoint (f : A →ₗ[E] A) (hf : ∀ x, f (star x) = star (f x)) :
    selfAdjoint.submodule F A →ₗ[F] selfAdjoint.submodule F A :=
  (f.restrictScalars F).restrict fun x (hx : IsSelfAdjoint x) ↦
    ((hf x).symm.trans (congrArg f hx) : IsSelfAdjoint (f x))

@[simp]
theorem coe_restrictSelfAdjoint_apply (f : A →ₗ[E] A) (hf : ∀ x, f (star x) = star (f x))
    (x : selfAdjoint.submodule F A) : (f.restrictSelfAdjoint F hf x : A) = f x :=
  (rfl)

variable (F) in
/-- An `E`-linear map commuting with `star`, restricted to an `F`-linear endomorphism of the
skew-adjoint elements. -/
def restrictSkewAdjoint (f : A →ₗ[E] A) (hf : ∀ x, f (star x) = star (f x)) :
    skewAdjoint.submodule F A →ₗ[F] skewAdjoint.submodule F A :=
  (f.restrictScalars F).restrict fun x (hx : star x = -x) ↦
    ((hf x).symm.trans ((congrArg f hx).trans (map_neg f x)) : star (f x) = -f x)

@[simp]
theorem coe_restrictSkewAdjoint_apply (f : A →ₗ[E] A) (hf : ∀ x, f (star x) = star (f x))
    (x : skewAdjoint.submodule F A) : (f.restrictSkewAdjoint F hf x : A) = f x :=
  (rfl)

variable [StarRing E] [StarModule E A]

/-- **The determinant of the skew-adjoint restriction**: an `E`-linear map commuting with `star`
has the same determinant on the skew-adjoint elements as on the self-adjoint ones, because
multiplication by a skew-adjoint unit of `E` intertwines the two restrictions. -/
theorem det_restrictSkewAdjoint {t : Eˣ} (ht : (t : E) ∈ skewAdjoint E) (f : A →ₗ[E] A)
    (hf : ∀ x, f (star x) = star (f x)) :
    LinearMap.det (f.restrictSkewAdjoint F hf) = LinearMap.det (f.restrictSelfAdjoint F hf) := by
  rw [← LinearMap.det_conj (f.restrictSkewAdjoint F hf) (skewAdjointEquivSelfAdjoint t ht)]
  congr 1
  ext y
  simp [smul_smul]

end CommRing

section Field

variable {F : Type*} [Field F] [StarMul F] [TrivialStar F] [Algebra F E] [Module F A]
  [IsScalarTower F E A] [StarModule F A] [StarRing E] [StarModule E A] [StarModule F E]
  [Invertible (2 : F)]

/-- **The determinant of the self-adjoint restriction**: if `F` is the fixed ring of the
involution of `E` and `E` has a skew-adjoint unit, an `E`-linear map `f` commuting with `star`
has the same determinant as its restriction to the self-adjoint elements. Indeed `f` is the base
change of that restriction along `TauCeti.selfAdjointBaseChangeEquiv`. -/
theorem algebraMap_det_restrictSelfAdjoint
    (hfix : ∀ c : E, IsSelfAdjoint c → c ∈ Set.range (algebraMap F E)) {t : Eˣ}
    (ht : (t : E) ∈ skewAdjoint E) (f : A →ₗ[E] A) (hf : ∀ x, f (star x) = star (f x)) :
    algebraMap F E (LinearMap.det (f.restrictSelfAdjoint F hf)) = LinearMap.det f := by
  nontriviality E
  let e := selfAdjointBaseChangeEquiv A hfix ht
  let g := f.restrictSelfAdjoint F hf
  by_cases hfin : Module.Finite F (selfAdjoint.submodule F A)
  · have hcomm : f ∘ₗ e.toLinearMap = e.toLinearMap ∘ₗ g.baseChange E := by
      ext x
      simp [e, g]
    have hf' : f = e.toLinearMap ∘ₗ g.baseChange E ∘ₗ e.symm.toLinearMap := by
      rw [← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc, LinearEquiv.comp_coe,
        LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
    conv_rhs => rw [hf']
    rw [LinearMap.det_conj, LinearMap.det_baseChange]
  · have := isQuadraticExtension_of_mem_skewAdjoint hfix ht
    have : Module.Finite F E := Module.finite_of_finrank_eq_succ
      (Algebra.IsQuadraticExtension.finrank_eq_two F E)
    have hfinA : ¬Module.Finite E A := by
      intro _
      have : Module.Finite F A := Module.Finite.trans E A
      exact hfin inferInstance
    rw [LinearMap.det_eq_one_of_not_module_finite hfin, LinearMap.det_eq_one_of_not_module_finite
      hfinA, map_one]

end Field

end LinearMap
