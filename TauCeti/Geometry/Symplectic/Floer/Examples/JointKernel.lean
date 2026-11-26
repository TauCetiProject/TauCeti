/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Basic
public import TauCeti.Geometry.Symplectic.Floer.Examples.DensePeriod

/-!
# The joint kernel and the orientation of the product class on `S² × S²`

Two conventions of capped Hamiltonian Floer theory are tested here on `S² × S²` with a product
symplectic form of areas `1` and `2` on the two factors. Its spherical classes are `ℤ × ℤ`, with
area `ω(a, b) = a + 2 b` (`JointKernelExample.area`) and first Chern number
`c₁(a, b) = 2 a + 2 b` (`TauCeti.Floer.DensePeriodExample.chernSphereProduct`).

* **The period group quotients the joint kernel.** The only class of zero area and zero first
  Chern number is `0` (`JointKernelExample.ker_prod_eq_bot`), so the period group
  `Γ = TauCeti.Floer.PeriodGroup ω c₁` is `ℤ × ℤ` itself (`JointKernelExample.periodGroupEquiv`).
  The class `B = (-2, 1)` has area `0` and degree `2 c₁(B) = -4`
  (`JointKernelExample.area_classB`, `JointKernelExample.degree_classB`); it is a nonzero class of
  `Γ` (`JointKernelExample.classB_ne_zero`), so area alone does not determine a class of `Γ`
  (`JointKernelExample.not_area_injective`). Quotienting by the kernel of the area alone would
  identify `B` with `0` (`JointKernelExample.mk_classB_eq_zero`), and then no degree function
  `d` on that quotient satisfies `d [s] = 2 c₁(s)` for every class `s`
  (`JointKernelExample.not_exists_degree_quotient_ker_area`, from
  `TauCeti.Floer.PeriodGroup.exists_degree_quotient_ker_area_iff`): the monomial `e^B = e^0`
  would have the two degrees `-4` and `0`.
* **The orientation of the product class.** The class of a pair of pants `u` with input caps `D₁`,
  `D₂` and output cap `D₀` is `A = D₀ + u − D₁ − D₂` (`TauCeti.Floer.productClass`), and with it
  the index `μ₁ + μ₂ − μ₀ − n + 2 c₁(A)` does not depend on the caps
  (`TauCeti.Floer.add_sub_add_two_mul_chern_productClass_eq`). With the opposite orientation
  `D₁ + D₂ − D₀ − u`, which is `-A`, recapping the first input by `γ` changes
  `μ₁ + μ₂ − μ₀ + 2 c₁(-A)` by `4 c₁(γ)` instead of `0`, for every gluing map equivariant in the
  first input and every grading obeying the recapping law
  (`JointKernelExample.add_sub_add_two_mul_chern_neg_productClass_vadd_fst`). On `S² × S²` the
  class `(1, 0)` has first Chern number `2`, so the opposite orientation gives a quantity that
  changes by `8` under this recapping
  (`JointKernelExample.add_sub_add_two_mul_chern_neg_productClass_classFst_vadd_fst`). The constant
  `−n` plays no role in either computation.

## References

* H. Hofer and D. A. Salamon, *Floer homology and Novikov rings*, in *The Floer memorial
  volume*, Progr. Math. 133 (1995), 483–524.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on
  Floer homology and Novikov rings.
-/

public section

namespace TauCeti.Floer.JointKernelExample

open DensePeriodExample (chernSphereProduct chernSphereProduct_apply)

/-! ### The period group of `S² × S²` with areas `1` and `2` -/

/-- The area `a + 2 b` of the spherical class `(a, b)` in `π₂(S² × S²) = ℤ × ℤ`, for a product
symplectic form of areas `1` and `2`. -/
def area : ℤ × ℤ →+ ℝ where
  toFun s := s.1 + 2 * s.2
  map_zero' := by simp
  map_add' _ _ := by simp; ring

@[simp]
theorem area_apply (s : ℤ × ℤ) : area s = s.1 + 2 * s.2 :=
  (rfl)

/-- On `S² × S²` with areas `1` and `2`, the only spherical class of zero area and zero first
Chern number is `0`. -/
theorem ker_prod_eq_bot : (area.prod chernSphereProduct).ker = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun s hs => ?_
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.prod_apply, area_apply, chernSphereProduct_apply,
    Prod.mk_eq_zero] at hs
  obtain ⟨harea, hchern⟩ := hs
  have harea' : s.1 + 2 * s.2 = 0 := by exact_mod_cast harea
  ext <;> simp <;> omega

/-- On `S² × S²` with areas `1` and `2`, the period group is the group `ℤ × ℤ` of spherical classes
itself. -/
def periodGroupEquiv : ℤ × ℤ ≃+ PeriodGroup area chernSphereProduct :=
  ((QuotientAddGroup.quotientAddEquivOfEq ker_prod_eq_bot).trans
    QuotientAddGroup.quotientBot).symm

@[simp]
theorem periodGroupEquiv_apply (s : ℤ × ℤ) :
    periodGroupEquiv s = (s : PeriodGroup area chernSphereProduct) := by
  simp [periodGroupEquiv, AddEquiv.symm_apply_eq]

/-- On `S² × S²` with areas `1` and `2`, distinct spherical classes stay distinct in the period
group. -/
theorem mk_injective :
    Function.Injective ((↑) : ℤ × ℤ → PeriodGroup area chernSphereProduct) := fun s t h =>
  periodGroupEquiv.injective (by rwa [periodGroupEquiv_apply, periodGroupEquiv_apply])

/-- The class `B = (-2, 1)` of the period group of `S² × S²` with areas `1` and `2`. -/
def classB : PeriodGroup area chernSphereProduct :=
  ((-2, 1) : ℤ × ℤ)

/-- The class `B = (-2, 1)` has area `0`. -/
@[simp]
theorem area_classB : PeriodGroup.area area chernSphereProduct classB = 0 := by
  rw [classB, PeriodGroup.area_mk, area_apply]
  norm_num

/-- The class `B = (-2, 1)` has first Chern number `-2`. -/
@[simp]
theorem chern_classB : PeriodGroup.chern area chernSphereProduct classB = -2 := by
  rw [classB, PeriodGroup.chern_mk, chernSphereProduct_apply]
  norm_num

/-- The class `B = (-2, 1)` has degree `2 c₁(B) = -4`. -/
theorem degree_classB : PeriodGroup.degree area chernSphereProduct classB = -4 := by
  rw [PeriodGroup.degree_apply, chern_classB]
  norm_num

/-- The class `B = (-2, 1)` is not zero in the period group, although its area is zero. -/
theorem classB_ne_zero : classB ≠ 0 := fun h => by
  simpa [h] using chern_classB

/-- On `S² × S²` with areas `1` and `2`, a class of zero area can have nonzero first Chern number:
`(-2, 1)` is one. -/
theorem not_ker_area_le_ker_chern : ¬area.ker ≤ chernSphereProduct.ker := fun h => by
  have hB : ((-2, 1) : ℤ × ℤ) ∈ area.ker := by
    rw [AddMonoidHom.mem_ker, area_apply]
    norm_num
  have := AddMonoidHom.mem_ker.1 (h hB)
  simp at this

/-- On `S² × S²` with areas `1` and `2`, area does not determine a class of the period group. -/
theorem not_area_injective :
    ¬Function.Injective (PeriodGroup.area area chernSphereProduct) := fun h =>
  classB_ne_zero (h (by rw [area_classB, map_zero]))

/-- In the quotient of the spherical classes of `S² × S²` by the kernel of the area alone, the
class `B = (-2, 1)` is identified with `0`. -/
theorem mk_classB_eq_zero : (((-2, 1) : ℤ × ℤ) : (ℤ × ℤ) ⧸ area.ker) = 0 := by
  rw [QuotientAddGroup.eq_zero_iff, AddMonoidHom.mem_ker, area_apply]
  norm_num

/-- On `S² × S²` with areas `1` and `2`, the degree `2 c₁` is not a function on the quotient of the
spherical classes by the kernel of the area alone: the classes `(-2, 1)` and `0` become equal
there, with the different degrees `-4` and `0`. -/
theorem not_exists_degree_quotient_ker_area :
    ¬∃ d : (ℤ × ℤ) ⧸ area.ker → ℤ, ∀ s : ℤ × ℤ, d s = 2 * chernSphereProduct s := fun h =>
  not_ker_area_le_ker_chern (PeriodGroup.exists_degree_quotient_ker_area_iff.1 h)

/-! ### The orientation of the product class -/

section Orientation

variable {S : Type*} [AddGroup S] {ω : S →+ ℝ} {c : S →+ ℤ} {C₁ C₂ C₀ : Type*}
  [VAdd (PeriodGroup ω c) C₁] [AddTorsor (PeriodGroup ω c) C₀] {glue : C₁ → C₂ → C₀}
  {m₁ : C₁ → ℤ} {m₂ : C₂ → ℤ} {m₀ : C₀ → ℤ}

/-- **The opposite orientation of the product class depends on the caps.** If the class of a pair
of pants were formed as `D₁ + D₂ − D₀ − u`, the negative of `TauCeti.Floer.productClass`, then
recapping the first input by `γ` would change `μ₁ + μ₂ − μ₀ + 2 c₁` of that class by `4 c₁(γ)`,
for a gluing map equivariant in the first input and a grading `μ₁` obeying the recapping law.
With the product class itself the change is `0`
(`TauCeti.Floer.add_sub_add_two_mul_chern_productClass_eq`). -/
theorem add_sub_add_two_mul_chern_neg_productClass_vadd_fst
    (hglue₁ : ∀ (γ : PeriodGroup ω c) D₁ D₂, glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hm₁ : ∀ (γ : PeriodGroup ω c) D, m₁ (γ +ᵥ D) = 2 * PeriodGroup.chern ω c γ + m₁ D)
    (γ : PeriodGroup ω c) (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    m₁ (γ +ᵥ D₁) + m₂ D₂ - m₀ D₀ +
        2 * PeriodGroup.chern ω c (-productClass glue (γ +ᵥ D₁) D₂ D₀) =
      m₁ D₁ + m₂ D₂ - m₀ D₀ + 2 * PeriodGroup.chern ω c (-productClass glue D₁ D₂ D₀) +
        4 * PeriodGroup.chern ω c γ := by
  rw [productClass_vadd_fst hglue₁, hm₁, neg_sub, map_sub, map_neg]
  ring

end Orientation

/-- The class `(1, 0)` of the period group of `S² × S²` with areas `1` and `2`, the class of the
first factor. -/
def classFst : PeriodGroup area chernSphereProduct :=
  ((1, 0) : ℤ × ℤ)

/-- The class `(1, 0)` of the first factor has first Chern number `2`. -/
@[simp]
theorem chern_classFst : PeriodGroup.chern area chernSphereProduct classFst = 2 := by
  rw [classFst, PeriodGroup.chern_mk, chernSphereProduct_apply]
  norm_num

/-- **The opposite orientation is not cap independent on `S² × S²`.** For every gluing map
equivariant in the first input and every grading of the first input obeying the recapping law,
recapping the first input by the class `(1, 0)` of the first factor changes
`μ₁ + μ₂ − μ₀ + 2 c₁(D₁ + D₂ − D₀ − u)` by `8`. -/
theorem add_sub_add_two_mul_chern_neg_productClass_classFst_vadd_fst {C₁ C₂ C₀ : Type*}
    [VAdd (PeriodGroup area chernSphereProduct) C₁]
    [AddTorsor (PeriodGroup area chernSphereProduct) C₀] {glue : C₁ → C₂ → C₀}
    {m₁ : C₁ → ℤ} {m₂ : C₂ → ℤ} {m₀ : C₀ → ℤ}
    (hglue₁ : ∀ (γ : PeriodGroup area chernSphereProduct) D₁ D₂,
      glue (γ +ᵥ D₁) D₂ = γ +ᵥ glue D₁ D₂)
    (hm₁ : ∀ (γ : PeriodGroup area chernSphereProduct) D,
      m₁ (γ +ᵥ D) = 2 * PeriodGroup.chern area chernSphereProduct γ + m₁ D)
    (D₁ : C₁) (D₂ : C₂) (D₀ : C₀) :
    m₁ (classFst +ᵥ D₁) + m₂ D₂ - m₀ D₀ +
        2 * PeriodGroup.chern area chernSphereProduct (-productClass glue (classFst +ᵥ D₁) D₂ D₀) =
      m₁ D₁ + m₂ D₂ - m₀ D₀ +
        2 * PeriodGroup.chern area chernSphereProduct (-productClass glue D₁ D₂ D₀) + 8 := by
  rw [add_sub_add_two_mul_chern_neg_productClass_vadd_fst hglue₁ hm₁, chern_classFst]
  norm_num

end TauCeti.Floer.JointKernelExample
