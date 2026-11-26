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

* `TauCeti.single_sub_one_ne_zero_iff`: over a nontrivial ring, the difference `single g 1 - 1`
  between the basis element at `g` and the unit is nonzero exactly when `g ≠ 1`.
* `TauCeti.one_add_single_ne_zero`: over a nontrivial semiring, `1 + single g r` is nonzero for
  `g ≠ 1`.
* This file tags Mathlib's `MonoidAlgebra.coeff_natCast_mul` and
  `AddMonoidAlgebra.coeff_natCast_mul` as `simp` lemmas: a natural-number constant scales every
  coefficient, `(↑n * x).coeff m = ↑n * x.coeff m`.
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
* `MonoidAlgebra.mapRingHom_injective` and its additive form: mapping the coefficients along an
  injective ring homomorphism is injective.
* The `IsAddTorsionFree (MonoidAlgebra R M)` and `HasUniqueDiv (MonoidAlgebra R M)` instances:
  `R[M]` inherits the absence of additive torsion from its coefficients, as `M →₀ R` does in
  Mathlib.
* The `Finite (MonoidAlgebra R M)` instance: `R[M]` is finite when `R` and `M` are.
* `TauCeti.MonoidAlgebra.isIntegral_of_isMulTorsion`: the monoid algebra of a commutative torsion
  monoid is integral over its coefficient ring.
* `TauCeti.MonoidAlgebra.single_mem_nonZeroDivisors_iff_of_isRegular`: a monomial at a regular
  index `m` is a non-zero-divisor in `R[M]` exactly when its coefficient is a non-zero-divisor in
  `R`. `TauCeti.MonoidAlgebra.single_mem_nonZeroDivisors_iff` is its `simp` form for a cancellative
  monoid, and `MonoidAlgebra.mrange_of_le_nonZeroDivisors` its consequence that coefficient-one
  monomials are non-zero-divisors. The forward implication,
  `TauCeti.MonoidAlgebra.mem_nonZeroDivisors_of_single`, holds for every index of every monoid.
* `MonoidAlgebra.addSubgroupClosure_range_of`: the basis monomials generate `ℤ[M]` as an additive
  group.
* `TauCeti.MonoidAlgebra.isRegular_single_one_iff` and
  `TauCeti.MonoidAlgebra.isRegular_natCast_iff`: for an arbitrary monoid `M`, an element of `R`
  placed at the identity, for instance a natural number, is regular in `R[M]` exactly when it is
  regular in `R`.
* `TauCeti.MonoidAlgebra.isSMulRegular_iff`: for nonempty `M`, a scalar acts injectively on `R[M]`
  exactly when it acts injectively on `R`.
* `MonoidAlgebra.smul_single_one`: an element `single g r` supported at a single point is the
  scalar multiple `r • single g 1` of the basis element there.
* `MonoidAlgebra.eq_single_of_subsingleton`: the monoid algebra of a one-point monoid is
  one-dimensional, each element being the monomial at any point with its coefficient there.
* `MonoidAlgebra.coeff_single_mul_mul_single_inv`: conjugating by the monomial `single u 1` at a
  unit `u` of `M` conjugates the indices of the coefficients.
* `MonoidAlgebra.lift_apply_eq_sum`: over a finite monoid, `lift F x` is the finite sum
  `∑ m, x_m • F m`.
* `MonoidAlgebra.coeff_mul_eq_sum`: the coefficients of a product in the group algebra of a finite
  group, as a convolution.

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
theorem _root_.MonoidAlgebra.exists_eq_smul_iff_dvd_coeff (x : MonoidAlgebra R M) {r : R} :
    (∃ y, x = r • y) ↔ ∀ m, r ∣ x.coeff m := by
  -- Scaling by `r` is the coefficientwise map `r * ·`, whose range Mathlib describes.
  have hmap : MonoidAlgebra.map (AddMonoidHom.mulLeft r) = (r • · : MonoidAlgebra R M → _) := by
    ext y m
    simp
  have h := Set.ext_iff.mp (MonoidAlgebra.range_map (M := M) (AddMonoidHom.mulLeft r)) x
  simp only [hmap, Set.mem_range, Set.mem_ofPred_eq, AddMonoidHom.coe_mulLeft] at h
  exact (exists_congr fun _ ↦ eq_comm).trans
    (h.trans (forall_congr' fun _ ↦ exists_congr fun _ ↦ eq_comm))

-- Mathlib states that a natural-number constant scales every coefficient of a monoid algebra and
-- an additive monoid algebra, but does not tag either lemma `simp`. Tag both so that `simp`
-- normalizes `(↑n * x).coeff m` in every monoid algebra, such as Laurent polynomials, as Mathlib
-- does for polynomials (`Polynomial.coeff_natCast_mul`) and power series
-- (`PowerSeries.coeff_natCast_mul`).
attribute [simp] MonoidAlgebra.coeff_natCast_mul AddMonoidAlgebra.coeff_natCast_mul

/-- Over a nontrivial semiring, `1 + single g r` is nonzero for `g ≠ 1`: its coefficient at the
identity is `1`. -/
theorem one_add_single_ne_zero [Nontrivial R] [One M] {g : M} (hg : g ≠ 1) (r : R) :
    (1 + MonoidAlgebra.single g r : MonoidAlgebra R M) ≠ 0 := by
  intro h
  have := congrArg (fun f => f.coeff 1) h
  simp [MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, hg.symm] at this

end Semiring

variable {R : Type*} [Ring R] {G : Type*} [One G]

/-- Over a nontrivial ring, the difference `single g 1 - 1` between the basis element at `g` and the
unit is nonzero exactly when `g ≠ 1`. -/
theorem single_sub_one_ne_zero_iff [Nontrivial R] {g : G} :
    MonoidAlgebra.single g (1 : R) - 1 ≠ 0 ↔ g ≠ 1 := by
  rw [sub_ne_zero, MonoidAlgebra.one_def, (MonoidAlgebra.single_left_injective one_ne_zero).ne_iff]

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

/-- Mapping the coefficients along an injective ring homomorphism is injective. -/
@[to_additive (dont_translate := R S)
/-- Mapping the coefficients along an injective ring homomorphism is injective. -/]
theorem _root_.MonoidAlgebra.mapRingHom_injective {R : Type*} [Semiring R] {M S : Type*}
    [Semiring S] [Monoid M] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom M f) := by
  rw [MonoidAlgebra.coe_mapRingHom]
  exact MonoidAlgebra.map_injective _ hf

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

end MonoidAlgebra

namespace TauCeti.MonoidAlgebra

open _root_.MonoidAlgebra

/-- If a monomial is a non-zero-divisor of `R[M]`, its coefficient is a non-zero-divisor of `R`:
multiplying `single m r` by a monomial at the identity multiplies the coefficients. No
cancellativity of `M` is needed. -/
@[to_additive (dont_translate := R) _root_.TauCeti.AddMonoidAlgebra.mem_nonZeroDivisors_of_single
/-- If a monomial is a non-zero-divisor of the additive monoid algebra `R[M]`, its coefficient is
a non-zero-divisor of `R`. No cancellativity of `M` is needed. -/]
theorem mem_nonZeroDivisors_of_single {R M : Type*} [Semiring R] [Monoid M] {m : M} {r : R}
    (h : single m r ∈ nonZeroDivisors (MonoidAlgebra R M)) : r ∈ nonZeroDivisors R := by
  obtain ⟨hL, hR⟩ := mem_nonZeroDivisors_iff.mp h
  refine mem_nonZeroDivisors_iff.mpr ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · simpa using hL (single 1 s) (by simp [hs])
  · simpa using hR (single 1 s) (by simp [hs])

/-- A monomial at a regular index `m` is a non-zero-divisor of `R[M]` exactly when its
coefficient is a non-zero-divisor of `R`. Regularity of `m` is used only for the reverse
implication; the forward one is `mem_nonZeroDivisors_of_single`. -/
@[to_additive (dont_translate := R)
  _root_.TauCeti.AddMonoidAlgebra.single_mem_nonZeroDivisors_iff_of_isAddRegular
/-- A monomial at an additively regular index `m` is a non-zero-divisor of the additive monoid
algebra `R[M]` exactly when its coefficient is a non-zero-divisor of `R`. Regularity of `m` is
used only for the reverse implication. -/]
theorem single_mem_nonZeroDivisors_iff_of_isRegular {R M : Type*} [Semiring R] [Monoid M]
    {m : M} (hm : IsRegular m) {r : R} :
    single m r ∈ nonZeroDivisors (MonoidAlgebra R M) ↔ r ∈ nonZeroDivisors R := by
  refine ⟨mem_nonZeroDivisors_of_single, fun hr ↦ ?_⟩
  obtain ⟨hrL, hrR⟩ := mem_nonZeroDivisors_iff.mp hr
  refine mem_nonZeroDivisors_iff.mpr ⟨fun f hf => ?_, fun f hf => ?_⟩
  · ext t
    refine hrL (f.coeff t) ?_
    rw [← coeff_single_mul_eq_mul_coeff (m₁ := m * t) t fun _ _ ↦ hm.left.eq_iff, hf, coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply]
  · ext t
    refine hrR (f.coeff t) ?_
    rw [← coeff_mul_single_eq_coeff_mul (m₁ := t * m) t fun _ _ ↦ hm.right.eq_iff, hf, coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply]

/-- In the monoid algebra of a cancellative monoid, a monomial is a non-zero-divisor of `R[M]`
exactly when its coefficient is a non-zero-divisor of `R`. This is the `simp` form of
`single_mem_nonZeroDivisors_iff_of_isRegular`, whose regularity hypothesis `simp` cannot
discharge. -/
@[to_additive (dont_translate := R) (attr := simp)
  _root_.TauCeti.AddMonoidAlgebra.single_mem_nonZeroDivisors_iff
/-- In the additive monoid algebra of a cancellative additive monoid, a monomial is a
non-zero-divisor of `R[M]` exactly when its coefficient is a non-zero-divisor of `R`. -/]
theorem single_mem_nonZeroDivisors_iff {R M : Type*} [Semiring R] [Monoid M] [IsCancelMul M]
    {m : M} {r : R} :
    single m r ∈ nonZeroDivisors (MonoidAlgebra R M) ↔ r ∈ nonZeroDivisors R :=
  single_mem_nonZeroDivisors_iff_of_isRegular (.all m)

/-- An element `r` of `R`, placed at the identity of `M`, is regular in `R[M]` exactly when it is
regular in `R`: both products with `single 1 r` multiply every coefficient by `r`. No
cancellativity of `M` is needed. -/
@[to_additive (dont_translate := R) (attr := simp)
  _root_.TauCeti.AddMonoidAlgebra.isRegular_single_zero_iff
/-- An element `r` of `R`, placed at the zero of `M`, is regular in `R[M]` exactly when it is
regular in `R`: both products with `single 0 r` multiply every coefficient by `r`. -/]
theorem isRegular_single_one_iff {R M : Type*} [Semiring R] [MulOneClass M] {r : R} :
    IsRegular (single 1 r : MonoidAlgebra R M) ↔ IsRegular r := by
  refine ⟨fun h ↦ ⟨fun a b hab ↦ ?_, fun a b hab ↦ ?_⟩, fun hr ↦ ⟨?_, ?_⟩⟩
  · -- Products of monomials at the identity are the monomials of the products.
    exact single_right_injective (m := (1 : M)) (h.left (by simpa using hab))
  · exact single_right_injective (m := (1 : M)) (h.right (by simpa using hab))
  · -- The two products with `single 1 r` are the coefficientwise maps `r * ·` and `· * r`.
    have hmul : (single 1 r * · : MonoidAlgebra R M → _) = map (AddMonoidHom.mulLeft r) := by
      ext x m
      simp [coeff_single_one_mul]
    rw [IsLeftRegular, hmul]
    exact map_injective _ hr.left
  · have hmul : (· * single 1 r : MonoidAlgebra R M → _) = map (AddMonoidHom.mulRight r) := by
      ext x m
      simp [coeff_mul_single_one]
    rw [IsRightRegular, hmul]
    exact map_injective _ hr.right

/-- A natural number is regular in `R[M]` exactly when it is regular in `R`. Not a `simp` lemma:
Mathlib's `isRegular_natCast` already rewrites both sides to `IsSMulRegular`, where
`isSMulRegular_iff` relates them. -/
@[to_additive (dont_translate := R) _root_.TauCeti.AddMonoidAlgebra.isRegular_natCast_iff
/-- A natural number is regular in `R[M]` exactly when it is regular in `R`. -/]
theorem isRegular_natCast_iff {R M : Type*} [Semiring R] [MulOneClass M] {n : ℕ} :
    IsRegular (n : MonoidAlgebra R M) ↔ IsRegular (n : R) := by
  rw [natCast_def, isRegular_single_one_iff]

/-- For nonempty `M`, a scalar `c` acts injectively on `R[M]` exactly when it acts injectively on
`R`: it acts coefficientwise. -/
@[to_additive (dont_translate := R S) (attr := simp)
  _root_.TauCeti.AddMonoidAlgebra.isSMulRegular_iff
/-- For nonempty `M`, a scalar `c` acts injectively on the additive monoid algebra `R[M]` exactly
when it acts injectively on `R`: it acts coefficientwise. -/]
theorem isSMulRegular_iff {R M S : Type*} [Semiring R] [Nonempty M] [SMulZeroClass S R] {c : S} :
    IsSMulRegular (MonoidAlgebra R M) c ↔ IsSMulRegular R c := by
  refine ⟨fun h r s hrs ↦ ?_, fun h x y hxy ↦ coeff_injective (h.finsupp ?_)⟩
  · obtain ⟨m⟩ := ‹Nonempty M›
    refine single_right_injective (m := m) (h ?_)
    simpa only [smul_single] using congrArg (single m) hrs
  · simpa only [coeff_smul] using congrArg coeff hxy

end TauCeti.MonoidAlgebra

namespace MonoidAlgebra

/-- For a cancellative monoid `M`, every coefficient-one monomial in `MonoidHom.mrange (of R M)`
is a non-zero-divisor of `R[M]`. -/
theorem mrange_of_le_nonZeroDivisors {R M : Type*} [Semiring R] [Monoid M] [IsCancelMul M] :
    MonoidHom.mrange (of R M) ≤ nonZeroDivisors (MonoidAlgebra R M) := by
  intro x hx
  obtain ⟨m, rfl⟩ := MonoidHom.mem_mrange.mp hx
  simpa only [of_apply] using
    (TauCeti.MonoidAlgebra.single_mem_nonZeroDivisors_iff (m := m)).mpr
      (one_mem (nonZeroDivisors R))

/-- An element supported at a single point is a scalar multiple of the basis element there. -/
theorem smul_single_one {k G : Type*} [Semiring k] (g : G) (r : k) :
    r • single g (1 : k) = single g r := by
  rw [smul_single', mul_one]

/-- The monoid algebra of a one-point monoid is one-dimensional: each element is the monomial at
any point `m` with its coefficient there. Mathlib's `MonoidAlgebra.uniqueLinearEquiv` gives this
only at an index `1` found by instance search. -/
@[to_additive (dont_translate := R)
/-- The additive monoid algebra of a one-point monoid is one-dimensional: each element is the
monomial at any point `m` with its coefficient there. -/]
theorem eq_single_of_subsingleton {R M : Type*} [Semiring R] [Subsingleton M]
    (x : MonoidAlgebra R M) (m : M) : x = single m (x.coeff m) := by
  ext n
  simp [Subsingleton.elim n m]

/-- Conjugating by the monomial at a unit `u` of `M` conjugates the indices of the coefficients:
`(u x u⁻¹)_h = x_{u⁻¹ h u}`. For a group element `g`, take `u = toUnits g`. -/
theorem coeff_single_mul_mul_single_inv {R M : Type*} [Semiring R] [Monoid M]
    (x : MonoidAlgebra R M) (u : Mˣ) (h : M) :
    (single (u : M) (1 : R) * x * single (↑u⁻¹ : M) 1).coeff h = x.coeff (↑u⁻¹ * h * u) := by
  rw [coeff_mul_single_eq_coeff_mul (h * u) fun _ _ ↦ Units.mul_inv_eq_iff_eq_mul u,
    coeff_single_mul_eq_mul_coeff (↑u⁻¹ * (h * u)) fun _ _ ↦ (Units.eq_inv_mul_iff_mul_eq u).symm,
    one_mul, mul_one, mul_assoc]

/-- Over a finite monoid, the algebra map `lift F` out of `R[M]` sends `x` to the finite sum
`∑ m, x_m • F m`. -/
theorem lift_apply_eq_sum {R A M : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M]
    [Fintype M] (F : M →* A) (x : MonoidAlgebra R M) :
    lift R A M F x = ∑ m, x.coeff m • F m := by
  rw [lift_apply, Finsupp.sum_fintype _ _ (by simp)]

/-- The coefficients of a product in the group algebra of a finite group, as a convolution. -/
theorem coeff_mul_eq_sum {k G : Type*} [Semiring k] [Group G] [Fintype G]
    (x y : MonoidAlgebra k G) (g : G) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]

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
  intro x hx
  obtain ⟨m, rfl⟩ := MonoidHom.mem_mrange.mp hx
  simpa only [AddMonoidAlgebra.of_apply] using
    (TauCeti.AddMonoidAlgebra.single_mem_nonZeroDivisors_iff (m := m.toAdd)).mpr
      (one_mem (nonZeroDivisors R))
