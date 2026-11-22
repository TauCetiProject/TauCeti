/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Basic facts about monoid algebras

General facts about the monoid algebra `R[G]` that use only its basis elements `single g r`, and
none of the further theory built on it.

## Main results

* `TauCeti.single_sub_one_ne_zero`: over a nontrivial ring, the difference `single g 1 - 1`
  between the basis element at `g` and the unit is nonzero when `g ≠ 1`.
* `MonoidAlgebra.coeff_one_mul_comm`: the coefficient at the identity of `xy` equals
  that of `yx` in the monoid algebra of a Dedekind-finite monoid (for instance a group) over a
  commutative semiring.
* `MonoidAlgebra.coeff_one_mul_of_coeff_mem`: the coefficient at the identity is multiplicative
  on elements whose other coefficients lie in a square-zero ideal, with additive version
  `AddMonoidAlgebra.coeff_zero_mul_of_coeff_mem`.
* The `IsMulCommutative (MonoidAlgebra R M)` instance: the monoid algebra of a commutative
  magma over a commutative semiring is commutative, as a mixin on the existing ring structure.
* `TauCeti.MonoidAlgebra.mem_ideal_smul_top_iff`: an element of `R[M]` lies in `I • R[M]` exactly
  when its coefficients lie in `I`, and `TauCeti.MonoidAlgebra.mapRingHom_eq_zero_iff`: the kernel
  of the coefficientwise map along `f : R →+* S` is `ker f • R[M]`.
* `MonoidAlgebra.mem_rangeS_mapRingHom_iff` and its additive form characterize the image of
  a coefficient homomorphism by the image membership of every coefficient.
* The `IsAddTorsionFree (MonoidAlgebra R M)` and `HasUniqueDiv (MonoidAlgebra R M)` instances:
  `R[M]` inherits the absence of additive torsion from its coefficients, as `M →₀ R` does in
  Mathlib.
* The `Finite (MonoidAlgebra R M)` instance: `R[M]` is finite when `R` and `M` are.
* `TauCeti.MonoidAlgebra.isIntegral_of_isMulTorsion`: the monoid algebra of a commutative torsion
  monoid is integral over its coefficient ring.
* `MonoidAlgebra.single_mem_nonZeroDivisors_iff` and `MonoidAlgebra.mrange_of_le_nonZeroDivisors`:
  for a cancellative monoid `M`, a monomial is a non-zero-divisor in `R[M]` exactly when its
  coefficient is one in `R`; in particular coefficient-one monomials are non-zero-divisors.
* `MonoidAlgebra.addSubgroupClosure_range_of`: the basis monomials generate `ℤ[M]` as an additive
  group.
* `MonoidAlgebra.isRegular_single_one_iff` and `MonoidAlgebra.isRegular_natCast_iff`: for an
  arbitrary monoid `M`, an element of `R` placed at the identity, for instance a natural number,
  is regular in `R[M]` exactly when it is regular in `R`.
* `MonoidAlgebra.singleOneUnit`: in a group algebra, `single g 1` as a unit with inverse
  `single g⁻¹ 1`, and `MonoidAlgebra.coeff_single_mul_mul_single_inv`: conjugating by it
  conjugates the indices of the coefficients.

## References

Injectivity of `single` in its index is Mathlib's `MonoidAlgebra.single_left_injective`.
-/

public section

namespace TauCeti

section Commutative

variable {R : Type*} [CommSemiring R] {M : Type*} [Mul M]

/-- The monoid algebra of a commutative magma over a commutative semiring is commutative. This is
the mixin form of Mathlib's `MonoidAlgebra.nonUnitalCommSemiring`, for a multiplication that is
commutative without carrying a `CommSemigroup` instance. -/
instance instIsMulCommutativeMonoidAlgebra [IsMulCommutative M] :
    IsMulCommutative (MonoidAlgebra R M) where
  is_comm.comm f g := by
    simp [MonoidAlgebra.mul_def, Finsupp.sum, mul_comm, mul_comm' (M := M),
      f.coeff.support.sum_comm]

end Commutative

section Semiring

variable {R : Type*} [Semiring R] {M : Type*}

/-- An element of `R[M]` is `r` times an element exactly when `r` (left) divides each of its
coefficients. -/
theorem _root_.MonoidAlgebra.exists_eq_smul_iff_dvd_coeff {r : R} {x : MonoidAlgebra R M} :
    (∃ y, x = r • y) ↔ ∀ m, r ∣ x.coeff m := by
  refine ⟨fun ⟨y, hy⟩ m ↦ ⟨y.coeff m, by simp [hy]⟩, fun h ↦ ?_⟩
  choose c hc using h
  refine ⟨∑ m ∈ x.coeff.support, MonoidAlgebra.single m (c m), ?_⟩
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  rw [Finsupp.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [MonoidAlgebra.smul_single', hc m]

end Semiring

variable {R : Type*} [Ring R] {G : Type*} [One G]

/-- Over a nontrivial ring, the difference `single g 1 - 1` between the basis element at `g` and the
unit is nonzero when `g ≠ 1`. -/
theorem single_sub_one_ne_zero [Nontrivial R] {g : G} (hg : g ≠ 1) :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def]
  intro h
  exact hg (MonoidAlgebra.single_left_injective one_ne_zero h)

namespace MonoidAlgebra

variable {R : Type*} [CommSemiring R] {M : Type*}

/-- An element of `R[M]` lies in `I • R[M]` exactly when all of its coefficients lie in `I`. -/
@[to_additive (dont_translate := R I) (attr := simp)
  _root_.AddMonoidAlgebra.mem_ideal_smul_top_iff
/-- An element of an additive monoid algebra lies in `I • ⊤` exactly when all of its
coefficients lie in `I`. -/]
theorem mem_ideal_smul_top_iff {I : Ideal R} {x : MonoidAlgebra R M} :
    x ∈ I • (⊤ : Submodule R (MonoidAlgebra R M)) ↔ ∀ m, x.coeff m ∈ I := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · refine Submodule.smul_induction_on hx (fun r hr n _ m ↦ ?_) fun x y hx hy m ↦ ?_
    · simpa using I.mul_mem_right (n.coeff m) hr
    · simpa using I.add_mem (hx m) (hy m)
  · rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ ↦ ?_
    simpa [MonoidAlgebra.smul_single'] using
      Submodule.smul_mem_smul (hx m) (Submodule.mem_top (x := MonoidAlgebra.single m (1 : R)))

/-- Applying a ring homomorphism `f` to the coefficients kills exactly `ker f • R[M]`. -/
@[to_additive (dont_translate := R S) (attr := simp)
  _root_.AddMonoidAlgebra.mapRingHom_eq_zero_iff
/-- Applying a coefficient homomorphism `f` kills exactly the submodule `ker f • ⊤`. -/]
theorem mapRingHom_eq_zero_iff [Monoid M] {S : Type*} [Semiring S] (f : R →+* S)
    {x : MonoidAlgebra R M} :
    MonoidAlgebra.mapRingHom M f x = 0 ↔
      x ∈ RingHom.ker f • (⊤ : Submodule R (MonoidAlgebra R M)) := by
  rw [mem_ideal_smul_top_iff, ← MonoidAlgebra.coeff_inj]
  simp [Finsupp.ext_iff, MonoidAlgebra.coeff_mapRingHom]

/-- A monoid-algebra element comes from a coefficient map exactly when each coefficient does.
No injectivity or surjectivity assumption on the coefficient map is needed. -/
@[to_additive (dont_translate := R S)
/-- An additive monoid-algebra element comes from a coefficient map exactly when each
coefficient does. No injectivity or surjectivity assumption on the coefficient map is needed. -/]
theorem _root_.MonoidAlgebra.mem_rangeS_mapRingHom_iff {R : Type*} [Semiring R]
    {M S : Type*} [Semiring S] [Monoid M] (f : R →+* S)
    (p : MonoidAlgebra S M) :
    p ∈ (MonoidAlgebra.mapRingHom M f).rangeS ↔ ∀ m, p.coeff m ∈ f.rangeS := by
  rw [← SetLike.mem_coe, RingHom.coe_rangeS, MonoidAlgebra.coe_mapRingHom,
    MonoidAlgebra.range_map]
  simp

/-- **The monoid algebra of a commutative torsion monoid is integral over its coefficients.**
Every basis element `single g 1` with `g ^ n = 1` is a root of the monic polynomial `X ^ n - 1`. -/
theorem isIntegral_of_isMulTorsion {R G : Type*} [CommRing R] [CommMonoid G] (hG : IsMulTorsion G) :
    Algebra.IsIntegral R (MonoidAlgebra R G) := by
  refine ⟨fun x ↦ ?_⟩
  induction x using MonoidAlgebra.induction_on with
  | of m =>
    obtain ⟨n, hn, hnm⟩ := isOfFinOrder_iff_pow_eq_one.1 (hG m)
    refine IsIntegral.of_pow hn ?_
    rw [← map_pow, hnm, map_one]
    exact isIntegral_one
  | add x y hx hy => exact hx.add hy
  | smul r x hx => exact hx.smul r

end MonoidAlgebra

end TauCeti

namespace MonoidAlgebra

/-- The coefficient at the identity is symmetric under swapping the factors in the monoid algebra
over a commutative semiring of a Dedekind-finite monoid, one where `a * b = 1` implies
`b * a = 1` (for instance a group, or a cancellative or commutative monoid). -/
theorem coeff_one_mul_comm {R M : Type*} [CommSemiring R] [MulOne M] [IsDedekindFiniteMonoid M]
    (x y : MonoidAlgebra R M) : (x * y).coeff 1 = (y * x).coeff 1 := by
  classical
  simp only [coeff_mul, Finsupp.sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun a _ ↦ ?_
  rw [mul_eq_one_comm, mul_comm (x.coeff a)]

/-- If all coefficients away from the identity of two elements of `R[M]` lie in a square-zero
ideal, the coefficient at the identity of their product is the product of their coefficients at
the identity. Thus the identity coefficient is multiplicative on the elements of `R[M]` that are
constant modulo such an ideal. -/
@[to_additive (dont_translate := R) coeff_zero_mul_of_coeff_mem
/-- If all coefficients away from zero of two elements of `R[M]` lie in a square-zero ideal, the
coefficient at zero of their product is the product of their coefficients at zero. Thus the zero
coefficient is multiplicative on the elements of `R[M]` that are constant modulo such an ideal;
for Laurent polynomials this is the constant coefficient. -/]
theorem coeff_one_mul_of_coeff_mem {R M : Type*} [CommSemiring R] [MulOneClass M] {I : Ideal R}
    (hI : I ^ 2 = ⊥) {x y : MonoidAlgebra R M} (hx : ∀ m ≠ 1, x.coeff m ∈ I)
    (hy : ∀ m ≠ 1, y.coeff m ∈ I) :
    (x * y).coeff 1 = x.coeff 1 * y.coeff 1 := by
  classical
  have hzero {m n : M} (hm : m ≠ 1) (hn : n ≠ 1) : x.coeff m * y.coeff n = 0 := by
    have hmem : x.coeff m * y.coeff n ∈ I ^ 2 := pow_two I ▸ Ideal.mul_mem_mul (hx m hm) (hy n hn)
    simpa [hI] using hmem
  rw [MonoidAlgebra.coeff_mul, Finsupp.sum_eq_single 1, Finsupp.sum_eq_single 1]
  · simp
  · intro n _ hn
    simp [hn]
  · simp
  · intro m _ hm
    refine Finset.sum_eq_zero fun n _ ↦ ?_
    dsimp only
    split_ifs with hmn
    · exact hzero hm fun hn ↦ hm (by simpa [hn] using hmn)
    · rfl
  · simp

section TorsionFree

variable {R M : Type*} [Semiring R]

/-- A monoid algebra over a semiring without additive torsion has no additive torsion. -/
@[to_additive
/-- An additive monoid algebra over a semiring without additive torsion has no additive
torsion. -/]
instance instIsAddTorsionFree [IsAddTorsionFree R] : IsAddTorsionFree (MonoidAlgebra R M) :=
  Function.Injective.isAddTorsionFree (coeffAddEquiv : MonoidAlgebra R M ≃+ _).toAddMonoidHom
    coeffAddEquiv.injective

/-- A monoid algebra over a semiring with unique division by positive integers has unique
division by positive integers. -/
@[to_additive
/-- An additive monoid algebra over a semiring with unique division by positive integers has
unique division by positive integers. -/]
instance instHasUniqueDiv [HasUniqueDiv R] : HasUniqueDiv (MonoidAlgebra R M) :=
  Function.Injective.hasUniqueDiv (coeffAddEquiv : MonoidAlgebra R M ≃+ _).toAddMonoidHom
    coeffAddEquiv.injective

end TorsionFree

/-- A monoid algebra over a finite semiring is finite when the monoid is. -/
@[to_additive
/-- An additive monoid algebra over a finite semiring is finite when the additive monoid is. -/]
instance instFinite {R M : Type*} [Semiring R] [Finite R] [Finite M] :
    Finite (MonoidAlgebra R M) :=
  .of_injective (fun x ↦ ⇑x.coeff) (DFunLike.coe_injective.comp coeff_injective)

/-- In the monoid algebra of a cancellative monoid, a monomial is a non-zero-divisor of `R[M]`
exactly when its coefficient is a non-zero-divisor of `R`. Cancellativity is used only for the
reverse implication. -/
@[to_additive (dont_translate := R)
/-- In the additive monoid algebra of a cancellative additive monoid, a monomial is a
non-zero-divisor of `R[M]` exactly when its coefficient is a non-zero-divisor of `R`.
Cancellativity is used only for the reverse implication. -/]
theorem single_mem_nonZeroDivisors_iff {R M : Type*} [Semiring R] [Monoid M] [IsCancelMul M]
    {m : M} {r : R} :
    single m r ∈ nonZeroDivisors (MonoidAlgebra R M) ↔ r ∈ nonZeroDivisors R := by
  refine ⟨fun h ↦ ?_, fun hr ↦ ?_⟩
  · -- Multiplying `single m r` by a monomial at the identity multiplies the coefficients.
    obtain ⟨hL, hR⟩ := mem_nonZeroDivisors_iff.mp h
    refine mem_nonZeroDivisors_iff.mpr ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
    · simpa using hL (single 1 s) (by simp [hs])
    · simpa using hR (single 1 s) (by simp [hs])
  · obtain ⟨hrL, hrR⟩ := mem_nonZeroDivisors_iff.mp hr
    refine mem_nonZeroDivisors_iff.mpr ⟨fun f hf => ?_, fun f hf => ?_⟩
    · ext t
      exact hrL (f.coeff t) (by simpa using congr(($hf).coeff (m * t)))
    · ext t
      exact hrR (f.coeff t) (by simpa using congr(($hf).coeff (t * m)))

/-- An element `r` of `R`, placed at the identity of `M`, is regular in `R[M]` exactly when it is
regular in `R`: both products with `single 1 r` multiply every coefficient by `r`. No
cancellativity of `M` is needed. -/
@[to_additive (dont_translate := R)
/-- An element `r` of `R`, placed at the zero of `M`, is regular in `R[M]` exactly when it is
regular in `R`: both products with `single 0 r` multiply every coefficient by `r`. -/]
theorem isRegular_single_one_iff {R M : Type*} [Semiring R] [MulOneClass M] {r : R} :
    IsRegular (single 1 r : MonoidAlgebra R M) ↔ IsRegular r := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩,
    fun hr ↦ ⟨fun x y h ↦ ?_, fun x y h ↦ ?_⟩⟩
  · -- Products of monomials at the identity are the monomials of the products.
    exact single_right_injective (m := (1 : M)) (h.left (by simpa using hab))
  · exact single_right_injective (m := (1 : M)) (h.right (by simpa using hab))
  · exact coeff_injective <| Finsupp.ext fun m ↦
      hr.left (by simpa [coeff_single_one_mul] using congr(($h).coeff m))
  · exact coeff_injective <| Finsupp.ext fun m ↦
      hr.right (by simpa [coeff_mul_single_one] using congr(($h).coeff m))

/-- A natural number is regular in `R[M]` exactly when it is regular in `R`. -/
@[to_additive (dont_translate := R)
/-- A natural number is regular in `R[M]` exactly when it is regular in `R`. -/]
theorem isRegular_natCast_iff {R M : Type*} [Semiring R] [MulOneClass M] {n : ℕ} :
    IsRegular (n : MonoidAlgebra R M) ↔ IsRegular (n : R) := by
  rw [natCast_def, isRegular_single_one_iff]

/-- For a cancellative monoid `M`, every coefficient-one monomial in `MonoidHom.mrange (of R M)`
is a non-zero-divisor of `R[M]`. -/
theorem mrange_of_le_nonZeroDivisors {R M : Type*} [Semiring R] [Monoid M] [IsCancelMul M] :
    MonoidHom.mrange (of R M) ≤ nonZeroDivisors (MonoidAlgebra R M) := by
  rintro _ ⟨m, rfl⟩
  exact single_mem_nonZeroDivisors_iff.mpr (one_mem _)

variable {R : Type*} [Semiring R] {G : Type*} [Group G]

/-- The basis element `single g 1` of a group algebra, as a unit with inverse `single g⁻¹ 1`. -/
noncomputable def singleOneUnit (g : G) : (MonoidAlgebra R G)ˣ :=
  Units.map (of R G) (toUnits g)

@[simp]
theorem coe_singleOneUnit (g : G) :
    ((singleOneUnit (R := R) g : (MonoidAlgebra R G)ˣ) : MonoidAlgebra R G) = single g 1 := by
  rfl

@[simp]
theorem coe_inv_singleOneUnit (g : G) :
    (((singleOneUnit (R := R) g)⁻¹ : (MonoidAlgebra R G)ˣ) : MonoidAlgebra R G) =
      single g⁻¹ 1 := by
  rfl

/-- Conjugating by a basis element conjugates the indices of the coefficients:
`(g x g⁻¹)_h = x_{g⁻¹ h g}`. -/
theorem coeff_single_mul_mul_single_inv (g h : G) (x : MonoidAlgebra R G) :
    (single g (1 : R) * x * single g⁻¹ 1).coeff h = x.coeff (g⁻¹ * h * g) := by
  simp [mul_assoc]

/-- The basis monomials `of ℤ M m` generate the integral monoid algebra `ℤ[M]` as an additive
group. -/
theorem addSubgroupClosure_range_of {M : Type*} [MulOneClass M] :
    AddSubgroup.closure (Set.range (of ℤ M)) = ⊤ := by
  refine (AddSubgroup.eq_top_iff' _).2 fun x => ?_
  induction x using MonoidAlgebra.induction_linear with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | single m c =>
    have h : single m c = c • of ℤ M m := by rw [of_apply, smul_single, smul_eq_mul, mul_one]
    rw [h]
    exact zsmul_mem (AddSubgroup.subset_closure (Set.mem_range_self m)) c

end MonoidAlgebra

/-- For a cancellative additive monoid `M`, every coefficient-one monomial in
`MonoidHom.mrange (AddMonoidAlgebra.of R M)` is a non-zero-divisor of `R[M]`. -/
theorem AddMonoidAlgebra.mrange_of_le_nonZeroDivisors {R M : Type*} [Semiring R] [AddMonoid M]
    [IsCancelAdd M] :
    MonoidHom.mrange (AddMonoidAlgebra.of R M) ≤ nonZeroDivisors (AddMonoidAlgebra R M) := by
  rintro _ ⟨m, rfl⟩
  exact AddMonoidAlgebra.single_mem_nonZeroDivisors_iff.mpr (one_mem _)
