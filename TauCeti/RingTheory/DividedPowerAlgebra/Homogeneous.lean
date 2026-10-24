/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowerAlgebra.Init
public import Mathlib.Algebra.DirectSum.Internal

/-!
# Homogeneous pieces of the divided power algebra

For a module `M` over a commutative semiring `R`, this file defines the degree-`d` homogeneous
piece of `DividedPowerAlgebra R M`. It is the `R`-submodule spanned by products of divided-power
generators whose indices sum to `d`. In particular, `dp R d m` belongs to the degree-`d` piece.

A linear map `M →ₗ[R] N` restricts the functorial map on divided power algebras to every
homogeneous piece. These restricted maps preserve divided-power generators and satisfy the
identity and composition laws.

The construction follows Roby's grading of the divided power algebra.
The ambient `DividedPowerAlgebra`, its generators and its functorial map are the Mathlib
formalization by Antoine Chambert-Loir and María Inés de Frutos-Fernández.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  III §§1–2][Roby-1963]
-/

public section

noncomputable section

namespace DividedPowerAlgebra

variable {R M N P : Type*} [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- The products of divided-power generators whose indices sum to `d`. -/
def homogeneousGenerators (d : ℕ) : Set (DividedPowerAlgebra R M) :=
  {x | ∃ l : List (ℕ × M), (l.map Prod.fst).sum = d ∧
    x = (l.map fun nm ↦ dp R nm.1 nm.2).prod}

/-- The degree-`d` homogeneous piece of the divided power algebra. -/
def homogeneousSubmodule (d : ℕ) : Submodule R (DividedPowerAlgebra R M) :=
  Submodule.span R (homogeneousGenerators (R := R) (M := M) d)

/-- A product of divided-power generators belongs to the piece indexed by the sum of their
degrees. -/
theorem prod_dp_mem_homogeneousSubmodule (l : List (ℕ × M)) :
    (l.map fun nm ↦ dp R nm.1 nm.2).prod ∈
      homogeneousSubmodule (R := R) (M := M) (l.map Prod.fst).sum := by
  apply Submodule.subset_span
  exact ⟨l, rfl, rfl⟩

/-- A submodule contains the degree-`d` piece if and only if it contains every product of
divided-power generators whose indices sum to `d`. -/
theorem homogeneousSubmodule_le_iff {d : ℕ} {p : Submodule R (DividedPowerAlgebra R M)} :
    homogeneousSubmodule (R := R) (M := M) d ≤ p ↔
      ∀ l : List (ℕ × M), (l.map Prod.fst).sum = d →
        (l.map fun nm ↦ dp R nm.1 nm.2).prod ∈ p := by
  rw [homogeneousSubmodule, Submodule.span_le]
  constructor
  · exact fun h l hl ↦ h ⟨l, hl, rfl⟩
  · rintro h _ ⟨l, hl, rfl⟩
    exact h l hl

/-- An induction principle for the degree-`d` piece: a property of its elements holds as soon as
it holds for products of divided-power generators whose indices sum to `d` and is stable under
zero, addition and scalar multiplication. -/
@[elab_as_elim]
theorem homogeneousSubmodule_induction {d : ℕ}
    {motive : (x : DividedPowerAlgebra R M) → x ∈ homogeneousSubmodule (R := R) (M := M) d → Prop}
    (prod_dp : ∀ (l : List (ℕ × M)) (hl : (l.map Prod.fst).sum = d),
      motive (l.map fun nm ↦ dp R nm.1 nm.2).prod (hl ▸ prod_dp_mem_homogeneousSubmodule l))
    (zero : motive 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (Submodule.add_mem _ hx hy))
    (smul : ∀ (r : R) x hx, motive x hx → motive (r • x) (Submodule.smul_mem _ r hx))
    {x : DividedPowerAlgebra R M} (hx : x ∈ homogeneousSubmodule (R := R) (M := M) d) :
    motive x hx := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact prod_dp l hl
  | zero => exact zero
  | add x y _ _ hx hy => exact add x y _ _ hx hy
  | smul r x _ hx => exact smul r x _ hx

/-- Linear maps from a homogeneous piece agree if they agree on every product of
divided-power generators of the prescribed total degree. -/
theorem homogeneousSubmodule_ext {d : ℕ}
    {f g : homogeneousSubmodule (R := R) (M := M) d →ₗ[R] N}
    (h : ∀ (l : List (ℕ × M)) (hl : (l.map Prod.fst).sum = d),
      f ⟨(l.map fun nm ↦ dp R nm.1 nm.2).prod, hl ▸ prod_dp_mem_homogeneousSubmodule l⟩ =
        g ⟨(l.map fun nm ↦ dp R nm.1 nm.2).prod, hl ▸ prod_dp_mem_homogeneousSubmodule l⟩) :
    f = g := by
  apply (Submodule.linearMap_eq_iff_of_eq_span f g
    (S := homogeneousGenerators (R := R) (M := M) d) rfl).2
  rintro ⟨_, l, hl, rfl⟩
  exact h l hl

/-- The generator `dp R d m` is homogeneous of degree `d`. -/
theorem dp_mem_homogeneousSubmodule (d : ℕ) (m : M) :
    dp R d m ∈ homogeneousSubmodule (R := R) (M := M) d := by
  simpa using prod_dp_mem_homogeneousSubmodule (R := R) [(d, m)]

/-- The unit is homogeneous of degree zero. -/
theorem one_mem_homogeneousSubmodule :
    (1 : DividedPowerAlgebra R M) ∈ homogeneousSubmodule (R := R) (M := M) 0 := by
  simpa using prod_dp_mem_homogeneousSubmodule (R := R) (M := M) []

/-- Products of homogeneous elements have the sum of their degrees. -/
theorem mul_mem_homogeneousSubmodule {a b : ℕ} {x y : DividedPowerAlgebra R M}
    (hx : x ∈ homogeneousSubmodule (R := R) (M := M) a)
    (hy : y ∈ homogeneousSubmodule (R := R) (M := M) b) :
    x * y ∈ homogeneousSubmodule (R := R) (M := M) (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨k, hk, rfl⟩ := hy
          simpa only [List.map_append, List.prod_append, List.sum_append, hl, hk] using
            prod_dp_mem_homogeneousSubmodule (R := R) (l ++ k)
      | zero => simp
      | add x y _ _ hx hy =>
          rw [mul_add]
          exact Submodule.add_mem _ hx hy
      | smul r y _ hy =>
          rw [mul_smul_comm]
          exact Submodule.smul_mem _ r hy
  | zero => simp
  | add x y _ _ hx hy =>
      rw [add_mul]
      exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ r hx

/-- The homogeneous submodules form a graded monoid under multiplication. -/
instance instGradedMonoid : SetLike.GradedMonoid (homogeneousSubmodule (R := R) (M := M)) where
  one_mem := one_mem_homogeneousSubmodule (R := R) (M := M)
  mul_mem _ _ := mul_mem_homogeneousSubmodule

/-- A finite product of divided-power generators belongs to the homogeneous piece of its
total degree. -/
theorem prod_dp_mem_homogeneousSubmodule_of_sum_eq {ι : Type*} [Fintype ι] {d : ℕ}
    (m : ι → M) (k : ι → ℕ) (hk : ∑ j, k j = d) :
    ∏ j, dp R (k j) (m j) ∈ homogeneousSubmodule (R := R) (M := M) d :=
  hk ▸ SetLike.prod_mem_graded _ _ _ fun j _ ↦ dp_mem_homogeneousSubmodule (k j) (m j)

/-- The functorial map on divided power algebras preserves every homogeneous piece. -/
theorem map_mem_homogeneousSubmodule (f : M →ₗ[R] N) {d : ℕ} {x : DividedPowerAlgebra R M}
    (hx : x ∈ homogeneousSubmodule (R := R) (M := M) d) :
    map R f x ∈ homogeneousSubmodule (R := R) (M := N) d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨l.map fun nm ↦ (nm.1, f nm.2), ?_, ?_⟩
      · have hdegrees :
            ((l.map fun nm ↦ (nm.1, f nm.2)).map Prod.fst).sum =
              (l.map Prod.fst).sum := by
          clear hl
          induction l with
          | nil => rfl
          | cons nm l ih =>
              simp only [List.map_cons, List.sum_cons]
              rw [ih]
        exact hdegrees.trans hl
      · have hproducts :
            ((l.map fun nm ↦ dp R nm.1 nm.2).map (map R f)).prod =
              ((l.map fun nm ↦ (nm.1, f nm.2)).map fun nm ↦ dp R nm.1 nm.2).prod := by
          clear hl
          induction l with
          | nil => rfl
          | cons nm l ih =>
              simp only [List.map_cons, List.prod_cons]
              rw [map_apply_dp, ih]
        exact (map_list_prod (map R f) _).trans hproducts
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul r x _ hx => simpa using Submodule.smul_mem _ r hx

/-- A linear map induces a linear map between homogeneous pieces of the same degree. -/
def mapHomogeneousSubmodule (f : M →ₗ[R] N) (d : ℕ) :
    homogeneousSubmodule (R := R) (M := M) d →ₗ[R]
      homogeneousSubmodule (R := R) (M := N) d :=
  LinearMap.codRestrict _
    ((map R f).toLinearMap.comp
      (homogeneousSubmodule (R := R) (M := M) d).subtype)
    (fun x ↦ map_mem_homogeneousSubmodule f x.2)

/-- The map on homogeneous pieces is the restriction of `DividedPowerAlgebra.map`. -/
@[simp]
theorem coe_mapHomogeneousSubmodule_apply (f : M →ₗ[R] N) (d : ℕ)
    (x : homogeneousSubmodule (R := R) (M := M) d) :
    (mapHomogeneousSubmodule f d x : DividedPowerAlgebra R N) = map R f x :=
  by
    rw [mapHomogeneousSubmodule]
    rfl

/-- The map on homogeneous pieces sends a divided-power generator to the corresponding
divided-power generator. -/
@[simp]
theorem mapHomogeneousSubmodule_dp (f : M →ₗ[R] N) (d : ℕ) (m : M) :
    mapHomogeneousSubmodule f d ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ =
      ⟨dp R d (f m), dp_mem_homogeneousSubmodule d (f m)⟩ := by
  ext
  simp

/-- The identity linear map induces the identity on every homogeneous piece. -/
@[simp]
theorem mapHomogeneousSubmodule_id (d : ℕ) :
    mapHomogeneousSubmodule (LinearMap.id (R := R) (M := M)) d = LinearMap.id := by
  ext x
  simp

/-- Maps on homogeneous pieces respect composition. -/
@[simp]
theorem mapHomogeneousSubmodule_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) (d : ℕ) :
    (mapHomogeneousSubmodule g d).comp (mapHomogeneousSubmodule f d) =
      mapHomogeneousSubmodule (g.comp f) d := by
  ext x
  simp [map_comp]

end DividedPowerAlgebra
