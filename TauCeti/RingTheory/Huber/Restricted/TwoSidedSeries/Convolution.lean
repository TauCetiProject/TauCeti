/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Restricted.TwoSidedSeries.Basic
public import TauCeti.Topology.Algebra.Nonarchimedean.DiscreteConvolution
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Convolution of two-sided restricted series

The coefficient family underlying a two-sided restricted series is closed under additive
convolution.  For restricted families `f g : ℤ → A`, the coefficient at `n` is

```text
∑' (i,j), i + j = n, f i * g j.
```

The products `f i * g j` tend to zero cofinitely on `ℤ × ℤ`; completeness of `A` upgrades this
to summability on every addition fiber. The resulting coefficients again tend to zero: modulo an
open additive subgroup, only finitely many pairs contribute, hence only their finitely many degrees
can contribute.

This supplies multiplication on Wedhorn's `A⟨X, X⁻¹⟩` (Example 6.39). After constructing the
bilinear convolution, the module proves associativity, installs the commutative algebra structure,
and shows that the variable `X` is a unit.

## Main results

* `TauCeti.Huber.addConvolutionExists_of_mem_twoSidedRestrictedSubmodule`: every coefficient
  convolution is summable.
* `TauCeti.Huber.addRingConvolution_mem_twoSidedRestrictedSubmodule`: convolution preserves the
  two-sided restricted condition.
* `TauCeti.Huber.twoSidedRestrictedMul`: convolution as a bilinear map on the restricted
  coefficient module.
* `TauCeti.Huber.addRingConvolution_assoc`: associativity on restricted coefficient families.
* The `CommRing` and `Algebra A` instances on `TauCeti.Huber.twoSidedRestrictedSubmodule A A`.
* `TauCeti.Huber.isUnit_twoSidedX`: the variable `X` is invertible.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Example 6.39 and Lemma 8.33.
-/

public section

open Filter Topology
open scoped DiscreteConvolution

namespace TauCeti.Huber

section Convergence

section Summability

variable {A : Type*} [Ring A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A]

/-- In a complete nonarchimedean ring, the convolution coefficients of two two-sided restricted
families are summable. -/
theorem addConvolutionExists_of_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    DiscreteConvolution.AddConvolutionExists (.mul ℕ A) f g :=
  TauCeti.addConvolutionExists_of_zeroAtFilter_cofinite
    (mem_twoSidedRestrictedSubmodule.mp hf) (mem_twoSidedRestrictedSubmodule.mp hg)

end Summability

section Preservation

variable {A : Type*} [Ring A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Additive ring convolution preserves two-sided restrictedness. -/
theorem addRingConvolution_mem_twoSidedRestrictedSubmodule
    {f g : ℤ → A} (hf : f ∈ twoSidedRestrictedSubmodule A A)
    (hg : g ∈ twoSidedRestrictedSubmodule A A) :
    f ⋆ᵣ₊ g ∈ twoSidedRestrictedSubmodule A A :=
  mem_twoSidedRestrictedSubmodule.mpr <|
    TauCeti.ZeroAtFilter.addRingConvolution
      (mem_twoSidedRestrictedSubmodule.mp hf) (mem_twoSidedRestrictedSubmodule.mp hg)

end Preservation

end Convergence

section Bilinear

variable {A : Type*} [CommRing A] [UniformSpace A] [hA : IsUniformAddGroup A]
  [NonarchimedeanRing A] [hComplete : CompleteSpace A] [T2Space A]

/-- **Multiplication convolution on two-sided restricted coefficients**, as a bilinear map.

Its value is Mathlib's additive discrete convolution, restricted to the coefficient submodule by
`addRingConvolution_mem_twoSidedRestrictedSubmodule`. -/
noncomputable def twoSidedRestrictedMul :
    twoSidedRestrictedSubmodule A A →ₗ[A]
      twoSidedRestrictedSubmodule A A →ₗ[A] twoSidedRestrictedSubmodule A A :=
  LinearMap.mk₂ A
    (fun f g ↦ ⟨(f : ℤ → A) ⋆ᵣ₊ (g : ℤ → A),
      addRingConvolution_mem_twoSidedRestrictedSubmodule f.2 g.2⟩)
    (fun f₁ f₂ g ↦ Subtype.ext <| DiscreteConvolution.add_addRingConvolution
      (f₁ : ℤ → A) (f₂ : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f₁.2 g.2)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f₂.2 g.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.smul_addRingConvolution c
      (f : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2))
    (fun f g₁ g₂ ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_add
      (f : ℤ → A) (g₁ : ℤ → A) (g₂ : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g₁.2)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g₂.2))
    (fun c f g ↦ Subtype.ext <| DiscreteConvolution.addRingConvolution_smul c
      (f : ℤ → A) (g : ℤ → A)
      (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2))

include hA hComplete in
/-- The coefficient family of `twoSidedRestrictedMul f g` is the additive ring convolution of
the coefficient families of `f` and `g`. -/
@[simp]
theorem coe_twoSidedRestrictedMul (f g : twoSidedRestrictedSubmodule A A) :
    ((twoSidedRestrictedMul f g : twoSidedRestrictedSubmodule A A) : ℤ → A) =
      (f : ℤ → A) ⋆ᵣ₊ (g : ℤ → A) := (rfl)

include hA hComplete in
/-- The `n`-th coefficient of `twoSidedRestrictedMul f g` is the sum over pairs of degrees adding
to `n`. -/
-- Not `@[simp]`: the preceding coercion lemma and Mathlib's `addRingConvolution_apply` already
-- simplify this left-hand side to the same sum.
theorem coe_twoSidedRestrictedMul_apply (f g : twoSidedRestrictedSubmodule A A) (n : ℤ) :
    ((twoSidedRestrictedMul f g : twoSidedRestrictedSubmodule A A) : ℤ → A) n =
      ∑' p : DiscreteConvolution.addFiber n,
        (f : ℤ → A) p.1.1 * (g : ℤ → A) p.1.2 := by
  rw [coe_twoSidedRestrictedMul, DiscreteConvolution.addRingConvolution_apply]

include hA hComplete in
/-- Multiplication convolution of two-sided restricted coefficient families is commutative. -/
theorem twoSidedRestrictedMul_comm (f g : twoSidedRestrictedSubmodule A A) :
    twoSidedRestrictedMul f g = twoSidedRestrictedMul g f :=
  Subtype.ext <| by
    rw [coe_twoSidedRestrictedMul, coe_twoSidedRestrictedMul,
      DiscreteConvolution.addRingConvolution_comm]

end Bilinear

section Identities

open DiscreteConvolution

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- A coefficient of a convolution, with the addition fiber parametrized by its first index. -/
theorem addRingConvolution_apply_sub (a b : ℤ → A) (n : ℤ) :
    addRingConvolution a b n = ∑' i : ℤ, a i * b (n - i) := by
  rw [addRingConvolution_apply]
  refine (Equiv.tsum_eq (⟨fun i : ℤ ↦ ⟨(i, n - i), by simp [mem_addFiber]⟩,
      fun ab ↦ (ab : ℤ × ℤ).1, fun _ ↦ rfl, ?_⟩ : ℤ ≃ addFiber n)
    (fun ab : addFiber n ↦ a (ab : ℤ × ℤ).1 * b (ab : ℤ × ℤ).2)).symm
  rintro ⟨⟨i, j⟩, h⟩
  rw [mem_addFiber] at h
  simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and]
  omega

/-- Convolving with `x Xᵐ` on the left shifts degrees by `m` and scales by `x`. -/
theorem pi_single_addRingConvolution (m : ℤ) (x : A) (b : ℤ → A) :
    addRingConvolution (Pi.single m x) b = fun n ↦ x * b (n - m) := by
  funext n
  rw [addRingConvolution_apply_sub,
    tsum_eq_single m fun i hi ↦ by rw [Pi.single_eq_of_ne hi, zero_mul], Pi.single_eq_same]

end Identities

section Associativity

open DiscreteConvolution

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T2Space A]

omit [T2Space A] in
/-- The single-index form of a convolution coefficient is summable for restricted families. -/
theorem summable_mul_sub_of_zeroAtFilter {a b : ℤ → A} (ha : ZeroAtFilter cofinite a)
    (hb : ZeroAtFilter cofinite b) (n : ℤ) : Summable fun i : ℤ ↦ a i * b (n - i) := by
  have hab := (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha).mul_of_nonarchimedean
    (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hb)
  have hinj : Function.Injective fun i : ℤ ↦ (i, n - i) := fun _ _ h ↦ congrArg Prod.fst h
  simpa [Function.comp_def] using hab.comp_injective hinj

/-- Additive ring convolution is associative on restricted coefficient families. -/
theorem addRingConvolution_assoc {a b c : ℤ → A} (ha : ZeroAtFilter cofinite a)
    (hb : ZeroAtFilter cofinite b) (hc : ZeroAtFilter cofinite c) :
    addRingConvolution (addRingConvolution a b) c =
      addRingConvolution a (addRingConvolution b c) := by
  have hA := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ha
  have hB := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hb
  have hC := NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hc
  funext n
  simp only [addRingConvolution_apply_sub]
  have hF : Summable fun p : ℤ × ℤ ↦ a p.2 * b (p.1 - p.2) * c (n - p.1) := by
    have hinj : Function.Injective fun p : ℤ × ℤ ↦ ((p.2, p.1 - p.2), n - p.1) := by
      rintro ⟨j₁, i₁⟩ ⟨j₂, i₂⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      omega
    simpa [Function.comp_def] using
      ((hA.mul_of_nonarchimedean hB).mul_of_nonarchimedean hC).comp_injective hinj
  have hG : Summable fun q : ℤ × ℤ ↦ a q.1 * (b q.2 * c (n - q.1 - q.2)) := by
    have hinj : Function.Injective fun q : ℤ × ℤ ↦ (q.1, (q.2, n - q.1 - q.2)) := by
      rintro ⟨i₁, k₁⟩ ⟨i₂, k₂⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      omega
    simpa [Function.comp_def] using
      (hA.mul_of_nonarchimedean (hB.mul_of_nonarchimedean hC)).comp_injective hinj
  have hlhs : ∑' j : ℤ, (∑' i : ℤ, a i * b (j - i)) * c (n - j) =
      ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) * c (n - p.1) := by
    rw [hF.tsum_prod]
    exact tsum_congr fun j ↦ ((summable_mul_sub_of_zeroAtFilter ha hb j).tsum_mul_right _).symm
  have hrhs : ∑' i : ℤ, a i * ∑' k : ℤ, b k * c (n - i - k) =
      ∑' q : ℤ × ℤ, a q.1 * (b q.2 * c (n - q.1 - q.2)) := by
    rw [hG.tsum_prod]
    exact tsum_congr fun i ↦
      ((summable_mul_sub_of_zeroAtFilter hb hc (n - i)).tsum_mul_left _).symm
  rw [hlhs, hrhs, ← Equiv.tsum_eq
    (⟨fun p : ℤ × ℤ ↦ (p.2, p.1 - p.2), fun q : ℤ × ℤ ↦ (q.1 + q.2, q.1),
      by rintro ⟨j, i⟩; simp, by rintro ⟨x, y⟩; simp⟩ : ℤ × ℤ ≃ ℤ × ℤ)
    fun q : ℤ × ℤ ↦ a q.1 * (b q.2 * c (n - q.1 - q.2))]
  refine tsum_congr ?_
  rintro ⟨j, i⟩
  have hshift : n - i - (j - i) = n - j := by ring
  rw [Equiv.coe_fn_mk, hshift, mul_assoc]

end Associativity

section Algebra

open DiscreteConvolution

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T2Space A]

/-- Multiplication on `A⟨X, X⁻¹⟩` is the bilinear convolution of coefficient families. -/
noncomputable instance : Mul (twoSidedRestrictedSubmodule A A) :=
  ⟨fun f g ↦ twoSidedRestrictedMul f g⟩

@[simp]
theorem twoSidedRestricted_coe_mul (f g : twoSidedRestrictedSubmodule A A) :
    ((f * g : twoSidedRestrictedSubmodule A A) : ℤ → A) =
      (f : ℤ → A) ⋆ᵣ₊ (g : ℤ → A) :=
  coe_twoSidedRestrictedMul f g

/-- The unit of `A⟨X, X⁻¹⟩` is the constant series supported in degree zero. -/
instance : One (twoSidedRestrictedSubmodule A A) :=
  ⟨⟨Pi.single 0 1, twoSidedRestrictedSubmodule_pi_single 0 1⟩⟩

omit [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] in
@[simp]
theorem twoSidedRestricted_coe_one :
    ((1 : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single 0 1 := (rfl)

/-- The coefficient formula for a product in `A⟨X, X⁻¹⟩`. -/
theorem twoSidedRestricted_coe_mul_apply
    (f g : twoSidedRestrictedSubmodule A A) (n : ℤ) :
    ((f * g : twoSidedRestrictedSubmodule A A) : ℤ → A) n =
      ∑' i : ℤ, (f : ℤ → A) i * (g : ℤ → A) (n - i) := by
  rw [twoSidedRestricted_coe_mul]
  exact addRingConvolution_apply_sub _ _ n

/-- The two-sided restricted series form a commutative ring under convolution. -/
noncomputable instance : CommRing (twoSidedRestrictedSubmodule A A) :=
  { (inferInstance : AddCommGroup (twoSidedRestrictedSubmodule A A)),
    (inferInstance : Mul (twoSidedRestrictedSubmodule A A)),
    (inferInstance : One (twoSidedRestrictedSubmodule A A)) with
    mul_assoc := fun f g h ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul]
      exact addRingConvolution_assoc (mem_twoSidedRestrictedSubmodule.mp f.2)
        (mem_twoSidedRestrictedSubmodule.mp g.2) (mem_twoSidedRestrictedSubmodule.mp h.2))
    one_mul := fun f ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, twoSidedRestricted_coe_one,
        single_addRingConvolution])
    mul_one := fun f ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, twoSidedRestricted_coe_one,
        addRingConvolution_single])
    left_distrib := fun f g h ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_add]
      exact addRingConvolution_add _ _ _
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2)
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2))
    right_distrib := fun f g h ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_add]
      exact add_addRingConvolution _ _ _
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 h.2)
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule g.2 h.2))
    zero_mul := fun f ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_zero, zero_addRingConvolution])
    mul_zero := fun f ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_zero, addRingConvolution_zero])
    mul_comm := fun f g ↦ twoSidedRestrictedMul_comm f g }

/-- The coefficientwise module structure makes `A⟨X, X⁻¹⟩` an `A`-algebra. -/
noncomputable instance : Algebra A (twoSidedRestrictedSubmodule A A) :=
  Algebra.ofModule
    (fun r f g ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_smul]
      exact smul_addRingConvolution r _ _
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2)))
    (fun r f g ↦ Subtype.ext (by
      simp only [twoSidedRestricted_coe_mul, Submodule.coe_smul]
      exact addRingConvolution_smul r _ _
        (addConvolutionExists_of_mem_twoSidedRestrictedSubmodule f.2 g.2)))

/-- The monomial `x Xᵐ` in the two-sided restricted series ring. -/
def twoSidedMonomial (m : ℤ) (x : A) : twoSidedRestrictedSubmodule A A :=
  ⟨Pi.single m x, twoSidedRestrictedSubmodule_pi_single m x⟩

omit [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] in
@[simp]
theorem twoSidedRestricted_coe_monomial (m : ℤ) (x : A) :
    ((twoSidedMonomial m x : twoSidedRestrictedSubmodule A A) : ℤ → A) = Pi.single m x := (rfl)

omit [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] in
@[simp]
theorem twoSidedMonomial_zero_one : twoSidedMonomial (0 : ℤ) (1 : A) = 1 := (rfl)

/-- Monomials multiply as monomials. -/
@[simp]
theorem twoSidedMonomial_mul (m k : ℤ) (x y : A) :
    twoSidedMonomial m x * twoSidedMonomial k y = twoSidedMonomial (m + k) (x * y) :=
  Subtype.ext (by
    rw [twoSidedRestricted_coe_mul, twoSidedRestricted_coe_monomial,
      twoSidedRestricted_coe_monomial, twoSidedRestricted_coe_monomial,
      pi_single_addRingConvolution]
    funext n
    by_cases h : n = m + k
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (by omega : n - m ≠ k), mul_zero])

/-- The algebra structure map places a scalar in degree zero. -/
@[simp]
theorem algebraMap_eq_twoSidedMonomial (x : A) :
    algebraMap A (twoSidedRestrictedSubmodule A A) x = twoSidedMonomial 0 x := by
  refine Subtype.ext (funext fun n ↦ ?_)
  rw [Algebra.algebraMap_eq_smul_one]
  simp [Pi.single_apply]

/-- A monomial with a unit coefficient is a unit. -/
theorem isUnit_twoSidedMonomial (m : ℤ) {x : A} (hx : IsUnit x) :
    IsUnit (twoSidedMonomial m x) := by
  obtain ⟨u, rfl⟩ := hx
  have h : ∀ y z : A, y * z = 1 →
      twoSidedMonomial m y * twoSidedMonomial (-m) z = 1 := fun y z hyz ↦ by
    rw [twoSidedMonomial_mul, add_neg_cancel, hyz, twoSidedMonomial_zero_one]
  exact ⟨⟨twoSidedMonomial m (u : A), twoSidedMonomial (-m) ((u⁻¹ : Aˣ) : A),
    h _ _ u.mul_inv, (mul_comm _ _).trans (h _ _ u.mul_inv)⟩, rfl⟩

/-- The variable `X` in the two-sided restricted series ring. -/
def twoSidedX : twoSidedRestrictedSubmodule A A := twoSidedMonomial 1 1

omit [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] in
theorem twoSidedX_def :
    (twoSidedX : twoSidedRestrictedSubmodule A A) = twoSidedMonomial 1 1 := (rfl)

/-- The variable `X` is invertible, with inverse the monomial in degree `-1`. -/
theorem isUnit_twoSidedX : IsUnit (twoSidedX : twoSidedRestrictedSubmodule A A) := by
  rw [twoSidedX_def]
  exact isUnit_twoSidedMonomial 1 isUnit_one

end Algebra

end TauCeti.Huber

end
