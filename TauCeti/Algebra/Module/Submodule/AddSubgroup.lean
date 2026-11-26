/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Additive subgroups from negation-closed submodules over semirings

Mathlib's `Submodule.toAddSubgroup` and `Submodule.addCommGroup` assume a `Ring` of scalars. Over
a `Semiring`, a submodule `p` need not be closed under negation in general, but whenever it is
(`∀ x ∈ p, -x ∈ p`), `p.toAddSubmonoid` promotes to an `AddSubgroup` and endows `↥p` with an
`AddCommGroup` structure extending its existing `AddCommMonoid` structure.

## Main results

* `Submodule.toAddSubgroupOfNegMem`: the `AddSubgroup` associated with a negation-closed
  submodule over a semiring.
* `Submodule.addCommGroupOfNegMem`: the corresponding `AddCommGroup` structure on `↥p`, with
  explicit compatibility lemmas for coercion and `p.subtype.toAddMonoidHom`.
* `LinearMap.rangeAddCommGroup`: the specialization to the range of a semiring-linear map
  between additive commutative groups.
-/

public section

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- Reinterpret a negation-closed submodule over a semiring as an additive subgroup. -/
@[expose]
def toAddSubgroupOfNegMem (p : Submodule R M) (hp : ∀ x ∈ p, -x ∈ p) : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun hx ↦ hp _ hx }

@[simp]
theorem coe_toAddSubgroupOfNegMem (p : Submodule R M) (hp : ∀ x ∈ p, -x ∈ p) :
    ((p.toAddSubgroupOfNegMem hp : AddSubgroup M) : Set M) = p :=
  rfl

@[simp]
theorem mem_toAddSubgroupOfNegMem (p : Submodule R M) (hp : ∀ x ∈ p, -x ∈ p) {x : M} :
    x ∈ p.toAddSubgroupOfNegMem hp ↔ x ∈ p :=
  Iff.rfl

/-- A negation-closed submodule over a semiring inherits an `AddCommGroup` structure extending its
`AddCommMonoid` structure. Registered as a `def` rather than a global instance to avoid
overlapping with `Ring`-scalar instances. -/
@[expose, instance_reducible]
def addCommGroupOfNegMem (p : Submodule R M) (hp : ∀ x ∈ p, -x ∈ p) : AddCommGroup p :=
  { p.addCommMonoid with
    neg := fun x ↦ ⟨-(x : M), (p.toAddSubgroupOfNegMem hp).neg_mem x.property⟩
    sub := fun x y ↦ ⟨(x : M) - y, (p.toAddSubgroupOfNegMem hp).sub_mem x.property y.property⟩
    zsmul := fun n x ↦ ⟨n • (x : M), (p.toAddSubgroupOfNegMem hp).zsmul_mem x.property n⟩
    zsmul_zero' := fun _ ↦ Subtype.ext (zero_zsmul _)
    zsmul_succ' := fun n x ↦ Subtype.ext (SubNegMonoid.zsmul_succ' n (x : M))
    zsmul_neg' := fun n x ↦ Subtype.ext (SubNegMonoid.zsmul_neg' n (x : M))
    neg_add_cancel := fun x ↦ Subtype.ext (neg_add_cancel (x : M))
    sub_eq_add_neg := fun x y ↦ Subtype.ext (sub_eq_add_neg (x : M) (y : M)) }

section Operations

variable (p : Submodule R M) (hp : ∀ x ∈ p, -x ∈ p)

/-- Negation in `p.addCommGroupOfNegMem hp` commutes with coercion to the ambient group. -/
theorem coe_neg_ofNegMem (x : p) :
    letI := p.addCommGroupOfNegMem hp
    ((-x : p) : M) = -(x : M) :=
  rfl

/-- Subtraction in `p.addCommGroupOfNegMem hp` commutes with coercion to the ambient group. -/
theorem coe_sub_ofNegMem (x y : p) :
    letI := p.addCommGroupOfNegMem hp
    ((x - y : p) : M) = (x : M) - (y : M) :=
  rfl

/-- `p.subtype.toAddMonoidHom` commutes with negation for `p.addCommGroupOfNegMem hp`. -/
theorem subtype_toAddMonoidHom_map_neg (x : p) :
    letI := p.addCommGroupOfNegMem hp
    p.subtype.toAddMonoidHom (-x) = -p.subtype.toAddMonoidHom x :=
  rfl

/-- `p.subtype.toAddMonoidHom` commutes with subtraction for `p.addCommGroupOfNegMem hp`. -/
theorem subtype_toAddMonoidHom_map_sub (x y : p) :
    letI := p.addCommGroupOfNegMem hp
    p.subtype.toAddMonoidHom (x - y) =
      p.subtype.toAddMonoidHom x - p.subtype.toAddMonoidHom y :=
  rfl

end Operations

end Submodule

namespace LinearMap

variable {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  (f : E →ₗ[R] F)

/-- The range of a semiring-linear map between additive groups is closed under negation. -/
theorem range_neg_mem : ∀ y ∈ f.range, -y ∈ f.range := by
  rintro _ ⟨x, rfl⟩
  exact ⟨-x, map_neg f x⟩

/-- The range of a semiring-linear map between additive commutative groups inherits an
`AddCommGroup` structure. -/
@[expose, instance_reducible]
def rangeAddCommGroup : AddCommGroup f.range :=
  f.range.addCommGroupOfNegMem f.range_neg_mem

end LinearMap
