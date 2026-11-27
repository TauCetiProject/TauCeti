/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Ideal multiples on products of modules

## Main results

* `Submodule.smul_top_eq_pi`: in a finite product of modules, `I • ⊤` is the product of the
  `I • ⊤` of the factors.
* `Ideal.FG.smul_top_pi_eq_pi`, `Ideal.FG.smul_top_pi_self_eq_pi`: a finitely generated ideal of a
  commutative semiring commutes with arbitrary products of modules.
* `Ideal.FG.quotientSmulTopEquivPi`: for a finitely generated ideal `J` of a commutative ring `R`,
  `(ι → R) ⧸ (J • ⊤)` is `R`-linearly isomorphic to `ι → R ⧸ J`.
-/

public section

namespace Submodule

variable {R ι : Type*} [Semiring R] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

/-- In a finite product, the ideal multiple `I • ⊤` is the product of the ideal multiples
`I • ⊤` of the factors. -/
theorem smul_top_eq_pi [Finite ι] (I : Ideal R) :
    I • (⊤ : Submodule R (∀ i, M i)) = pi Set.univ fun i ↦ I • (⊤ : Submodule R (M i)) := by
  classical
  have := Fintype.ofFinite ι
  refine le_antisymm (smul_le.mpr fun r hr x _ ↦ mem_pi.mpr fun i _ ↦ smul_mem_smul hr mem_top)
    fun x hx ↦ ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem fun i _ ↦ smul_top_le_comap_smul_top I (LinearMap.single R M i)
    ((mem_pi (p := fun i ↦ I • (⊤ : Submodule R (M i)))).mp hx i (Set.mem_univ i))

end Submodule

namespace Ideal

open scoped Pointwise

/-- A finitely generated ideal `J` of a commutative semiring commutes with arbitrary products of
modules: `J • (⊤ : Submodule R (∀ i, M i))` equals the product of the submodules `J • ⊤`. -/
theorem FG.smul_top_pi_eq_pi {R : Type*} [CommSemiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {J : Ideal R} (hJ : J.FG) :
    J • (⊤ : Submodule R (∀ i, M i)) =
      Submodule.pi Set.univ fun i ↦ J • (⊤ : Submodule R (M i)) := by
  refine le_antisymm (Submodule.smul_le.mpr fun r hr _ _ i _ ↦
    Submodule.smul_mem_smul hr Submodule.mem_top) ?_
  obtain ⟨s, rfl⟩ := hJ
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    rw [show x = 0 from funext fun i ↦ by simpa using Submodule.mem_pi.mp hx i (Set.mem_univ i)]
    exact zero_mem _
  | @insert a s _ ih =>
    intro x hx
    have hspan : Ideal.span (↑(insert a s) : Set R) = Ideal.span {a} ⊔ Ideal.span (s : Set R) := by
      rw [Finset.coe_insert, Set.insert_eq, Ideal.span_union]
    rw [hspan, Submodule.sup_smul]
    have hx' : ∀ i, ∃ u : M i, ∃ v ∈ Ideal.span (s : Set R) • (⊤ : Submodule R (M i)),
        a • u + v = x i := fun i ↦ by
      have hi := Submodule.mem_pi.mp hx i (Set.mem_univ i)
      rw [hspan, Submodule.sup_smul] at hi
      obtain ⟨y, hy, v, hv, hyv⟩ := Submodule.mem_sup.mp hi
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hy
      obtain ⟨u, _, rfl⟩ := hy
      exact ⟨u, v, hv, hyv⟩
    choose u v hv huv using hx'
    rw [show x = a • u + v from funext fun i ↦ (huv i).symm]
    exact Submodule.add_mem_sup (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a)
      Submodule.mem_top) (ih fun i _ ↦ hv i)

/-- For a finitely generated ideal `J` of a commutative semiring `R`,
`J • (⊤ : Submodule R (ι → R))` consists of the tuples whose every coordinate lies in `J`. -/
theorem FG.smul_top_pi_self_eq_pi {R : Type*} [CommSemiring R] {ι : Type*}
    {J : Ideal R} (hJ : J.FG) :
    J • (⊤ : Submodule R (ι → R)) = Submodule.pi Set.univ fun _ : ι ↦ J := by
  simpa only [smul_eq_mul, Ideal.mul_top] using hJ.smul_top_pi_eq_pi (M := fun _ : ι ↦ R)

/-- For a finitely generated ideal `J` of a commutative ring `R`, the quotient `(ι → R) ⧸ (J • ⊤)`
is `R`-linearly isomorphic to `ι → R ⧸ J`. -/
noncomputable def FG.quotientSmulTopEquivPi {R : Type*} [CommRing R] (ι : Type*)
    {J : Ideal R} (hJ : J.FG) :
    ((ι → R) ⧸ (J • (⊤ : Submodule R (ι → R)))) ≃ₗ[R] (ι → R ⧸ J) :=
  have hpi : J • (⊤ : Submodule R (ι → R)) =
      (Ideal.pi fun _ : ι ↦ J).restrictScalars R := by
    rw [hJ.smul_top_pi_self_eq_pi]
    ext; simp [Ideal.mem_pi]
  let e := (Submodule.quotEquivOfEq _ _ hpi).toEquiv.trans
    (Ideal.piQuotEquiv ι (I := J)).toEquiv
  { toEquiv := e
    map_add' := fun x y ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl
    map_smul' := fun r x ↦ by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl }

/-- Evaluating `Ideal.FG.quotientSmulTopEquivPi` on a residue class gives the coordinatewise residue
classes. -/
@[simp]
theorem FG.quotientSmulTopEquivPi_mk {R : Type*} [CommRing R] (ι : Type*)
    {J : Ideal R} (hJ : J.FG) (x : ι → R) (i : ι) :
    hJ.quotientSmulTopEquivPi ι (Submodule.Quotient.mk x) i = Ideal.Quotient.mk J (x i) :=
  (rfl)

end Ideal
