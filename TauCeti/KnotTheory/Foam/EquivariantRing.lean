/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.Category.GradedModuleCat.Retract
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.FinCases

/-!
# The equivariant `gl(N)` foam coefficient ring and integral graded freeness

The integral equivariant coefficient ring of `gl(N)` foam homology is the polynomial ring
`Λ_N = ℤ[e₁, …, e_N]` with `MvPolynomial.X i` representing the elementary symmetric generator
`e_{i+1}` of internal degree `2(i + 1)`. This file defines `TauCeti.Foam.EquivariantRing N` and
its integral `ℤ`-grading `TauCeti.Foam.EquivariantRing.grading N`, establishes its basic graded
properties (graded algebra structure, nonnegativity, even support, degree-zero identification with
`ℤ`, and degree vanishing on homogeneous units), and specializes the general graded retract
freeness theorem (`TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent_pi` and
`TauCeti.GradedModuleCat.exists_factorization_idempotent_pi`) to `Λ_N`.

In particular, every degree-zero idempotent on a finite direct sum of shifted copies of `Λ_N`
(including the degenerate case `N = 0`, where `Λ_0 ≃ ℤ`) admits a finite homogeneous `Λ_N`-basis
for its image and splits explicitly through a finite shifted free `Λ_N`-module via degree-zero
maps `ι` and `π` satisfying `π ∘ₗ ι = id` and `ι ∘ₗ π = p`.

## Main definitions

* `TauCeti.Foam.EquivariantRing`: the integral equivariant polynomial ring `Λ_N = ℤ[e₁, …, e_N]`.
* `TauCeti.Foam.EquivariantRing.weight`: the variable weight `i ↦ 2(i + 1)` in `ℤ`.
* `TauCeti.Foam.EquivariantRing.grading`: the weighted `ℤ`-grading on `EquivariantRing N`.
* `TauCeti.Foam.EquivariantRing.gradedAlgebra`: the `GradedAlgebra` instance for `grading N`.

## Main results

* `TauCeti.Foam.EquivariantRing.grading_eq_bot_of_neg`: `grading N d = ⊥` for `d < 0`.
* `TauCeti.Foam.EquivariantRing.grading_eq_bot_of_odd`: `grading N d = ⊥` for odd `d`.
* `TauCeti.Foam.EquivariantRing.mem_grading_zero_iff`: degree-zero elements are integer constants.
* `TauCeti.Foam.EquivariantRing.eq_zero_of_isUnit_mem_grading`: a homogeneous unit has degree `0`.
* `TauCeti.Foam.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero idempotent
  on a finite sum of shifted copies of `Λ_N` admits a finite homogeneous `Λ_N`-basis.
* `TauCeti.Foam.exists_factorization_idempotent`: every such idempotent splits explicitly through
  a finite shifted free `Λ_N`-module via degree-zero maps `ι` and `π`.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech. Math.
  7 (2020), 573–651, Section 3.4, for integral graded freeness of idempotent images over `Λ_N`.
-/

public section

noncomputable section

namespace TauCeti.Foam

/-- The integral equivariant coefficient ring `Λ_N = ℤ[e₁, …, e_N]`. The variable
`MvPolynomial.X i` represents the elementary generator `e_{i+1}`. -/
abbrev EquivariantRing (N : ℕ) : Type := MvPolynomial (Fin N) ℤ

namespace EquivariantRing

/-- The integer weight `2(i + 1)` assigned to the generator `e_{i+1}` (`MvPolynomial.X i`). -/
abbrev weight (N : ℕ) (i : Fin N) : ℤ :=
  2 * ((i : ℕ) + 1 : ℤ)

/-- The integral `ℤ`-grading on `EquivariantRing N` in which `e_{i+1}` has degree `2(i + 1)`. -/
def grading (N : ℕ) : ℤ → Submodule ℤ (EquivariantRing N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℤ (weight N)

/-- Membership in the degree-`d` piece of `EquivariantRing N` is weighted homogeneity of weight
`d`. -/
theorem mem_grading_iff {N : ℕ} {d : ℤ} {p : EquivariantRing N} :
    p ∈ grading N d ↔ p.IsWeightedHomogeneous (weight N) d :=
  Iff.rfl

/-- The grading `grading N` is closed under `1` and multiplication. -/
instance gradedMonoid (N : ℕ) : SetLike.GradedMonoid (grading N) where
  one_mem := mem_grading_iff.mpr (MvPolynomial.isWeightedHomogeneous_one ℤ (weight N))
  mul_mem _ _ _ _ hp hq :=
    mem_grading_iff.mpr ((mem_grading_iff.mp hp).mul (mem_grading_iff.mp hq))

/-- `EquivariantRing N` is the internal direct sum of the graded pieces `grading N`. -/
theorem isInternal_grading (N : ℕ) : DirectSum.IsInternal (grading N) :=
  (MvPolynomial.weightedDecomposition ℤ (weight N)).isInternal

/-- The weighted `ℤ`-grading makes `EquivariantRing N` a graded `ℤ`-algebra. -/
instance gradedAlgebra (N : ℕ) : GradedAlgebra (grading N) :=
  (isInternal_grading N).gradedAlgebra

/-- Every generator weight `2(i + 1)` is strictly positive. -/
theorem weight_pos {N : ℕ} (i : Fin N) : 0 < weight N i := by
  unfold weight
  omega

/-- The weighted degree of any monomial in `EquivariantRing N` is nonnegative. -/
theorem finsupp_weight_nonneg {N : ℕ} (m : Fin N →₀ ℕ) :
    0 ≤ Finsupp.weight (weight N) m := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [nsmul_eq_mul]
  exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (weight_pos i))

/-- The weighted degree of any monomial in `EquivariantRing N` is even. -/
theorem even_finsupp_weight {N : ℕ} (m : Fin N →₀ ℕ) :
    Even (Finsupp.weight (weight N) m) := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.even_sum _ fun i _ => ?_
  refine ⟨(m i : ℤ) * ((i : ℕ) + 1 : ℤ), ?_⟩
  simp only [weight, nsmul_eq_mul]
  ring

/-- A monomial in `EquivariantRing N` has weighted degree zero iff it is the constant monomial
`0`. -/
@[simp]
theorem finsupp_weight_eq_zero_iff {N : ℕ} (m : Fin N →₀ ℕ) :
    Finsupp.weight (weight N) m = 0 ↔ m = 0 := by
  constructor
  · intro h
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    have hall : ∀ i ∈ m.support, (m i : ℤ) * weight N i = 0 := by
      have h' := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ?_).mp h
      · intro i hi
        simpa [nsmul_eq_mul] using h' i hi
      · rw [nsmul_eq_mul]
        exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (weight_pos i))
    ext i
    by_contra hi
    have hmem : i ∈ m.support := Finsupp.mem_support_iff.mpr hi
    have hmul := hall i hmem
    have hmi : (m i : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hi
    have hw : weight N i ≠ 0 := ne_of_gt (weight_pos i)
    exact mul_ne_zero hmi hw hmul
  · rintro rfl
    simp

/-- `EquivariantRing N` is nonnegatively graded: all negative-degree pieces vanish. -/
theorem grading_eq_bot_of_neg (N : ℕ) {d : ℤ} (hd : d < 0) : grading N d = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  refine (mem_grading_iff.mp hp).eq_zero_of_no_monomials fun m hm => ?_
  have := finsupp_weight_nonneg (N := N) m
  omega

/-- `EquivariantRing N` is supported in even degrees: all odd-degree pieces vanish. -/
theorem grading_eq_bot_of_odd (N : ℕ) {d : ℤ} (hd : Odd d) : grading N d = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  refine (mem_grading_iff.mp hp).eq_zero_of_no_monomials fun m hm => ?_
  exact (Int.not_even_iff_odd.mpr hd) (hm ▸ even_finsupp_weight m)

/-- The degree-zero piece of `EquivariantRing N` consists precisely of integer constants. -/
theorem mem_grading_zero_iff {N : ℕ} {p : EquivariantRing N} :
    p ∈ grading N 0 ↔ ∃ c : ℤ, MvPolynomial.C c = p := by
  constructor
  · intro hp
    refine ⟨p.coeff 0, ?_⟩
    rw [MvPolynomial.C_apply]
    exact ((mem_grading_iff.mp hp).eq_monomial_of_unique_weight
      fun m hm => (finsupp_weight_eq_zero_iff m).mp hm).symm
  · rintro ⟨c, rfl⟩
    exact MvPolynomial.isWeightedHomogeneous_C (weight N) c

/-- The variable `MvPolynomial.X i` lies in degree `2(i + 1)`. -/
theorem X_mem_grading {N : ℕ} (i : Fin N) :
    (MvPolynomial.X i : EquivariantRing N) ∈ grading N (2 * ((i : ℕ) + 1 : ℤ)) :=
  MvPolynomial.isWeightedHomogeneous_X ℤ (weight N) i

/-- Every integer constant lies in degree zero. -/
theorem C_mem_grading_zero (N : ℕ) (c : ℤ) :
    (MvPolynomial.C c : EquivariantRing N) ∈ grading N 0 :=
  MvPolynomial.isWeightedHomogeneous_C (weight N) c

/-- Every integer cast lies in degree zero. -/
@[simp]
theorem intCast_mem_grading_zero (N : ℕ) (c : ℤ) :
    (c : EquivariantRing N) ∈ grading N 0 := by
  simpa using C_mem_grading_zero N c

/-- Every homogeneous unit of `EquivariantRing N` has degree zero. -/
theorem eq_zero_of_isUnit_mem_grading {N : ℕ} {d : ℤ} {p : EquivariantRing N}
    (hp : IsUnit p) (hd : p ∈ grading N d) : d = 0 := by
  obtain ⟨u, rfl⟩ := hp
  have heval : MvPolynomial.eval (0 : Fin N → ℤ) (u : EquivariantRing N) *
      MvPolynomial.eval (0 : Fin N → ℤ) (↑u⁻¹ : EquivariantRing N) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : (u : EquivariantRing N).coeff 0 ≠ 0 := by
    intro h0
    have hev0 : MvPolynomial.eval (0 : Fin N → ℤ) (u : EquivariantRing N) = 0 := by
      rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, h0]
    rw [hev0, zero_mul] at heval
    exact zero_ne_one heval
  have hwt := mem_grading_iff.mp hd hne
  simpa using hwt.symm

end EquivariantRing

/-- **Integral graded freeness of idempotent images over `Λ_N`.** The image of a degree-zero
idempotent on a finite sum of shifted copies of `EquivariantRing N` has a finite homogeneous
`EquivariantRing N`-basis. The `j`-th source summand has shift `s j`, so degree-`d` elements have
`j`-th coordinate in `EquivariantRing.grading N (d - s j)`. This holds for all `N : ℕ`, including
`N = 0`. -/
theorem exists_homogeneous_basis_range_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) :=
  GradedModuleCat.exists_homogeneous_basis_range_idempotent_pi
    (𝒜 := EquivariantRing.grading N)
    (fun _ hi => EquivariantRing.grading_eq_bot_of_neg N hi)
    (fun _ ha => EquivariantRing.mem_grading_zero_iff.mp ha)
    s p hp hhom

/-- **Explicit homogeneous splitting of an idempotent over `Λ_N`.** Every degree-zero idempotent
`p` on a finite sum of shifted copies of `EquivariantRing N` factors through a finite shifted free
`EquivariantRing N`-module via degree-zero maps `ι` and `π` satisfying `π ∘ₗ ι = id` and
`ι ∘ₗ π = p`. -/
theorem exists_factorization_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N))
      (π : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N)),
      π.comp ι = LinearMap.id ∧ ι.comp π = p ∧
        (∀ (q : ℤ) (v : Fin n → EquivariantRing N),
          (∀ i, v i ∈ EquivariantRing.grading N (q - d i)) →
          ∀ j, ι v j ∈ EquivariantRing.grading N (q - s j)) ∧
        (∀ (q : ℤ) (v : Fin m → EquivariantRing N),
          (∀ j, v j ∈ EquivariantRing.grading N (q - s j)) →
          ∀ i, π v i ∈ EquivariantRing.grading N (q - d i)) :=
  GradedModuleCat.exists_factorization_idempotent_pi
    (𝒜 := EquivariantRing.grading N)
    (fun _ hi => EquivariantRing.grading_eq_bot_of_neg N hi)
    (fun _ ha => EquivariantRing.mem_grading_zero_iff.mp ha)
    s p hp hhom

/-! ### Worked checks -/

/-- If `LinearMap.range p` is free of rank `1` via `e` with `(e 1).val j₀ = 1`, then every finite
homogeneous basis of `LinearMap.range p` has rank `1` and degree `s j₀`. -/
private theorem rank_one_and_deg_of_range_equiv {N m n : ℕ} {s : Fin m → ℤ}
    {p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N] (Fin m → EquivariantRing N)}
    (e : EquivariantRing N ≃ₗ[EquivariantRing N] LinearMap.range p) (j₀ : Fin m)
    (he : (e 1).val j₀ = 1)
    (bas : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
    (d : Fin n → ℤ)
    (hdeg : ∀ i j, (bas i).val j ∈ EquivariantRing.grading N (d i - s j)) :
    n = 1 ∧ ∀ i, d i = s j₀ := by
  have hn : n = 1 := by
    have hcard := Module.Basis.mk_eq_rank'' (bas.map e.symm)
    have h1 := Module.Basis.mk_eq_rank'' (Module.Basis.singleton (Fin 1) (EquivariantRing N))
    have heq : Cardinal.mk (Fin n) = Cardinal.mk (Fin 1) := hcard.trans h1.symm
    simpa using heq
  refine ⟨hn, fun i => ?_⟩
  subst hn
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hunit : IsUnit ((bas 0).val j₀) := by
    have hrepr := congrArg (fun x => x.val j₀) (bas.sum_repr (e 1))
    simp only [Fin.sum_univ_one, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, he] at hrepr
    exact IsUnit.of_mul_eq_one_right _ hrepr
  have h0 : d 0 - s j₀ = 0 :=
    EquivariantRing.eq_zero_of_isUnit_mem_grading hunit (hdeg 0 j₀)
  omega

-- Check 1a: For `p = 0` (for any `N`, including `N = 0`), the image has the empty basis (`n = 0`).
example (N m : ℕ) (s : Fin m → ℤ) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (0 : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
          (Fin m → EquivariantRing N))))
      (d : Fin n → ℤ),
      n = 0 ∧ ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N m s 0 (by ext; simp)
    (fun d _ _ j => by simp)
  refine ⟨n, b, d, ?_, hb⟩
  by_contra hn
  have h0 : b ⟨0, Nat.pos_of_ne_zero hn⟩ = 0 := Subtype.ext <| by
    rcases (b ⟨0, Nat.pos_of_ne_zero hn⟩).prop with ⟨x, hx⟩
    simpa using hx.symm
  exact b.ne_zero ⟨0, Nat.pos_of_ne_zero hn⟩ h0

-- Check 1b: For `p = id` on a rank-one summand of shift `3` (including `N = 0`), the homogeneous
-- basis has rank `1` and its basis vector has degree `3`.
example (N : ℕ) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N)
        (LinearMap.range (LinearMap.id : (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N]
          (Fin 1 → EquivariantRing N))))
      (d : Fin n → ℤ),
      n = 1 ∧ (∀ i, d i = 3) ∧
        ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - ![3] j) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_range_idempotent N 1 ![3] LinearMap.id
    (by ext; simp) (fun _ _ hv j => hv j)
  let e : EquivariantRing N ≃ₗ[EquivariantRing N]
      LinearMap.range (LinearMap.id : (Fin 1 → EquivariantRing N) →ₗ[EquivariantRing N]
        (Fin 1 → EquivariantRing N)) :=
    { toFun := fun r => ⟨fun _ => r, ⟨fun _ => r, rfl⟩⟩
      invFun := fun v => v.val 0
      left_inv := fun _ => rfl
      right_inv := fun v => Subtype.ext (funext fun j => by fin_cases j; rfl)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  obtain ⟨hn, hd⟩ := rank_one_and_deg_of_range_equiv e 0 rfl b d hb
  exact ⟨n, b, d, hn, hd, hb⟩

-- Check 2: For `p = diag(1, 0)` on `Λ_N{a} ⊕ Λ_N{b}`, the image has explicit homogeneous basis
-- `(1, 0)` of degree `a`, independently of `b`, and every homogeneous basis has rank `1` and
-- degree `a`.
example (N : ℕ) (a b : ℤ) :
    let p : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 2 → EquivariantRing N) :=
      { toFun := fun v => ![v 0, 0]
        map_add' := fun u v => by ext j; fin_cases j <;> simp
        map_smul' := fun r v => by ext j; fin_cases j <;> simp }
    p.comp p = p ∧
    (∃ (bas : Module.Basis (Fin 1) (EquivariantRing N) (LinearMap.range p)),
      (bas 0).val = ![1, 0] ∧
      ∀ j, (bas 0).val j ∈ EquivariantRing.grading N (a - ![a, b] j)) ∧
    (∀ (n : ℕ) (bas : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      (∀ i j, (bas i).val j ∈ EquivariantRing.grading N (d i - ![a, b] j)) →
      n = 1 ∧ ∀ i, d i = a) := by
  intro p
  have hp : p.comp p = p := by
    ext v j
    fin_cases j <;> simp [p]
  let e : EquivariantRing N ≃ₗ[EquivariantRing N] LinearMap.range p :=
    { toFun := fun r => ⟨![r, 0], ⟨![r, 0], funext fun j => by fin_cases j <;> simp [p]⟩⟩
      invFun := fun v => v.val 0
      left_inv := fun _ => rfl
      right_inv := fun ⟨y, x, hx⟩ => Subtype.ext <| funext fun j => by
        dsimp only
        rw [← hx]
        fin_cases j <;> simp [p]
      map_add' := fun r s => Subtype.ext <| funext fun j => by fin_cases j <;> simp
      map_smul' := fun r s => Subtype.ext <| funext fun j => by fin_cases j <;> simp }
  have he1 : (e 1).val = ![1, 0] := rfl
  refine ⟨hp, ⟨(Module.Basis.singleton (Fin 1) (EquivariantRing N)).map e, ?_, fun j => ?_⟩,
    fun n bas d hdeg => rank_one_and_deg_of_range_equiv e 0 rfl bas d hdeg⟩
  · simpa [Module.Basis.map_apply] using he1
  · rw [Module.Basis.map_apply, Module.Basis.singleton_apply, he1]
    fin_cases j
    · simpa using EquivariantRing.C_mem_grading_zero N 1
    · exact Submodule.zero_mem _

-- Check 3: For `N ≥ 1`, shifts `(2, 0)`, and `p(x, y) = (x, e₁ * x)`, `p` is a degree-zero
-- idempotent whose image has basis `(1, e₁)` of degree `2`, with second coordinate in degree
-- `2 - 0 = 2`, verifying the shift sign; moreover, any homogeneous basis (in particular one
-- produced by `exists_homogeneous_basis_range_idempotent`) has rank `1` and degree `2`.
example (N : ℕ) (hN : 0 < N) :
    let e₁ : EquivariantRing N := MvPolynomial.X ⟨0, hN⟩
    let p : (Fin 2 → EquivariantRing N) →ₗ[EquivariantRing N] (Fin 2 → EquivariantRing N) :=
      { toFun := fun v => ![v 0, e₁ * v 0]
        map_add' := fun u v => by ext j; fin_cases j <;> simp [mul_add]
        map_smul' := fun r v => by ext j; fin_cases j <;> simp [mul_left_comm] }
    p.comp p = p ∧
    (∀ (d : ℤ) (v : Fin 2 → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - ![2, 0] j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - ![2, 0] j)) ∧
    (∃ (bas : Module.Basis (Fin 1) (EquivariantRing N) (LinearMap.range p)),
      (bas 0).val = ![1, e₁] ∧
      ∀ j, (bas 0).val j ∈ EquivariantRing.grading N (2 - ![2, 0] j)) ∧
    (∀ (n : ℕ) (bas : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      (∀ i j, (bas i).val j ∈ EquivariantRing.grading N (d i - ![2, 0] j)) →
      n = 1 ∧ ∀ i, d i = 2) := by
  intro e₁ p
  have hp : p.comp p = p := by
    ext v j
    fin_cases j <;> simp [p]
  have he₁ : e₁ ∈ EquivariantRing.grading N 2 := by
    simpa [e₁] using EquivariantRing.X_mem_grading (⟨0, hN⟩ : Fin N)
  have hhom : ∀ (d : ℤ) (v : Fin 2 → EquivariantRing N),
      (∀ j, v j ∈ EquivariantRing.grading N (d - ![2, 0] j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - ![2, 0] j) := by
    intro d v hv j
    fin_cases j
    · simpa [p] using hv 0
    · have hv0 : v 0 ∈ EquivariantRing.grading N (d - 2) := by simpa using hv 0
      have hmul : e₁ * v 0 ∈ EquivariantRing.grading N (2 + (d - 2)) :=
        SetLike.GradedMul.mul_mem he₁ hv0
      have hdeg : (2 : ℤ) + (d - 2) = d - 0 := by omega
      simpa [p, hdeg] using hmul
  let e : EquivariantRing N ≃ₗ[EquivariantRing N] LinearMap.range p :=
    { toFun := fun r =>
        ⟨![r, e₁ * r], ⟨![r, 0], funext fun j => by fin_cases j <;> simp [p]⟩⟩
      invFun := fun v => v.val 0
      left_inv := fun _ => rfl
      right_inv := fun ⟨y, x, hx⟩ => Subtype.ext <| funext fun j => by
        dsimp only
        rw [← hx]
        fin_cases j <;> simp [p]
      map_add' := fun r s => Subtype.ext <| funext fun j => by fin_cases j <;> simp [mul_add]
      map_smul' := fun r s => Subtype.ext <| funext fun j => by
        fin_cases j <;> simp [mul_left_comm] }
  have he1 : (e 1).val = ![1, e₁] := by
    funext j
    fin_cases j
    · rfl
    · exact mul_one e₁
  refine ⟨hp, hhom, ⟨(Module.Basis.singleton (Fin 1) (EquivariantRing N)).map e, ?_, fun j => ?_⟩,
    fun n bas d hdeg => rank_one_and_deg_of_range_equiv e 0 rfl bas d hdeg⟩
  · simpa [Module.Basis.map_apply] using he1
  · rw [Module.Basis.map_apply, Module.Basis.singleton_apply, he1]
    fin_cases j
    · simpa using EquivariantRing.C_mem_grading_zero N 1
    · simpa using he₁

end TauCeti.Foam
