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
import Mathlib.LinearAlgebra.Quotient.Basic
import TauCeti.RingTheory.Ideal.Operations

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
    Submodule.smul_mem_smul hr Submodule.mem_top) fun x hx ↦ ?_
  obtain ⟨s, rfl⟩ := hJ
  have hspan : Ideal.span (s : Set R) = Ideal.span (Set.range ((↑) : s → R)) := by
    rw [Subtype.range_coe_subtype, Finset.setOfPred_mem]
  have hx' : ∀ i, ∃ m : s → M i, ∑ j : s, (j : R) • m j = x i := fun i ↦ by
    have hi := Submodule.mem_pi.mp hx i (Set.mem_univ i)
    rwa [hspan, Submodule.mem_span_range_smul_top_iff_exists_fun] at hi
  choose m hm using hx'
  rw [hspan, Submodule.mem_span_range_smul_top_iff_exists_fun]
  exact ⟨fun j i ↦ m i j, funext fun i ↦ by simpa [Finset.sum_apply] using hm i⟩

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
  haveI : IsScalarTower R (R ⧸ J) ((ι → R) ⧸ Ideal.pi fun _ : ι ↦ J) :=
    ⟨fun r s x ↦ by
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      -- `Ideal.modulePi` defines `mk s • mk x` as `mk (s • x)` without an evaluation lemma,
      -- and `r • Ideal.Quotient.mk J s` is definitionally `Ideal.Quotient.mk J (r • s)`.
      change Submodule.Quotient.mk ((r • s) • x) = r • Submodule.Quotient.mk (s • x)
      rw [smul_assoc, Submodule.Quotient.mk_smul]⟩
  Submodule.quotEquivOfEq _ _ hpi ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv R (Ideal.pi fun _ : ι ↦ J) ≪≫ₗ
    (Ideal.piQuotEquiv ι J).restrictScalars R

/-- Evaluating `Ideal.FG.quotientSmulTopEquivPi` on a residue class gives the coordinatewise residue
classes. -/
@[simp]
theorem FG.quotientSmulTopEquivPi_mk {R : Type*} [CommRing R] (ι : Type*)
    {J : Ideal R} (hJ : J.FG) (x : ι → R) (i : ι) :
    hJ.quotientSmulTopEquivPi ι (Submodule.Quotient.mk x) i = Ideal.Quotient.mk J (x i) := by
  simp only [FG.quotientSmulTopEquivPi, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk, LinearEquiv.restrictScalars_apply]
  -- `Ideal.piQuotEquiv` has no evaluation lemma in Mathlib; its `toFun` is definitionally
  -- `Quotient.liftOn' · (fun f i ↦ Ideal.Quotient.mk J (f i))`.
  rfl

end Ideal
