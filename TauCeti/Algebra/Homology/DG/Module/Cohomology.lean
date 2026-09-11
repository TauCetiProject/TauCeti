/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology
public import TauCeti.Algebra.Homology.DG.Module.Defs

/-!
# The cohomology module of a differential graded left module

Let `dM` be a differential on a module `ℳ` over the differential graded algebra `(𝒜, d)`, in the
sense of `TauCeti.IsDGLeftModule`.  Its **cycles** are the kernel of `dM` and its **boundaries**
are the image of `dM`.  This file shows that the cycles are a module over the algebra of cycles
`TauCeti.IsDGAlgebra.cycles` of `A`, that the boundaries are a submodule of it, and that the
resulting quotient -- the **cohomology module** `H(M)` -- is a module over the cohomology algebra
`H(A)`.

Both halves of the descent come from the Leibniz rule with one factor killed.  A cycle of
`A` acting on a cycle of `M` gives a cycle, because the differential of `a • x` is `d a • x` as
soon as `x` is a cycle; a cycle of `A` acting on a boundary gives a boundary, because for a
homogeneous cycle `a` the Leibniz rule read backwards says `a • dM x = (-1) ^ |a| * dM (a • x)`.
Finally a boundary of `A` acting on a cycle of `M` is a boundary, again because `d a • x` is
`dM (a • x)`.  The last statement says exactly that the boundary ideal of `A` annihilates `H(M)`,
which is what descends the action along `H(A) = cycles(A) / boundaries(A)`.

The cycles also inherit the grading: `dM` commutes with the homogeneous projections, so the
homogeneous components of a cycle are cycles, and the degree pieces of the cycles of `M` form an
internal direct sum on which the degree pieces of the cycles of `A` act additively in the degree.

## Main definitions

* `TauCeti.IsDGLeftModule.cycles`: the kernel of the differential, as a module over the algebra of
  cycles of `A`.
* `TauCeti.IsDGLeftModule.cyclesDeg`: the homogeneous cycles of a fixed degree.
* `TauCeti.IsDGLeftModule.boundaries`: the image of the differential, as a submodule of the cycles.
* `TauCeti.IsDGLeftModule.Cohomology`: the cohomology module, the cycles modulo the boundaries.

## Main results

* `TauCeti.IsDGLeftModule.iSup_cyclesDeg_eq_top` and
  `TauCeti.IsDGLeftModule.isInternal_cyclesDeg`: every cycle is a sum of homogeneous ones, and the
  homogeneous cycles form an internal direct sum.
* `TauCeti.IsDGLeftModule.instGradedSMulCyclesDeg`: **the cycles of a differential graded left
  module are a graded module over the graded algebra of cycles.**
* `TauCeti.IsDGLeftModule.isTorsionBySet_boundaries`: the boundaries of `A` annihilate the
  cohomology module.
* `TauCeti.IsDGLeftModule.instModuleCohomology`: **the cohomology of a differential graded left
  module is a module over the cohomology algebra**, with `TauCeti.IsDGLeftModule.quotientMk_smul`
  computing the action through a representing cycle.

This supplies for modules what `TauCeti.Algebra.Homology.DG.Algebra.Cohomology` supplies for
algebras.  The descent of the action along the boundary ideal is Mathlib's
`Module.IsTorsionBySet.module`.

## References

* B. Keller, *Deriving DG categories*, Sections 1 and 2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 4.1.
-/

-- Provenance: the Tau Ceti `DGAInfinity` roadmap `README.md`, whose section "Cohomological
-- grading and Koszul signs" fixes the cohomological Keller sign convention used here, and whose
-- section "Ground rings, size, and handedness" fixes the module conventions.

public section

open DirectSum

namespace TauCeti

variable {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsDGAlgebra 𝒜 d} {ℳ : ℤ → Submodule R M}
  [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}

namespace IsDGLeftModule

/-- The **cycles** of a differential graded left module: the kernel of the differential.  It is a
module over the algebra of cycles of `A` because a cycle acting on a cycle is a cycle. -/
def cycles (hM : IsDGLeftModule h ℳ dM) : Submodule h.cycles M :=
  { (LinearMap.ker dM).toAddSubmonoid with
    smul_mem' := fun z _ hx => hM.map_smul_eq_zero_of_map_eq_zero (h.mem_cycles.mp z.2) hx }

@[simp]
lemma mem_cycles (hM : IsDGLeftModule h ℳ dM) {x : M} : x ∈ hM.cycles ↔ dM x = 0 := Iff.rfl

/-- The differential of every element is a cycle, by the square-zero axiom. -/
theorem map_mem_cycles (hM : IsDGLeftModule h ℳ dM) (x : M) : dM x ∈ hM.cycles :=
  hM.sq_zero x

/-- The **boundaries** of a differential graded left module: the image of the differential, viewed
inside the cycles.  A cycle of `A` carries a boundary to a boundary, so this is a submodule over
the algebra of cycles. -/
def boundaries (hM : IsDGLeftModule h ℳ dM) : Submodule h.cycles hM.cycles :=
  { (LinearMap.range dM).toAddSubmonoid.comap hM.cycles.subtype.toAddMonoidHom with
    smul_mem' := fun z _ hx => hM.smul_mem_range_of_map_eq_zero (h.mem_cycles.mp z.2) hx }

@[simp]
lemma mem_boundaries (hM : IsDGLeftModule h ℳ dM) {z : hM.cycles} :
    z ∈ hM.boundaries ↔ (z : M) ∈ LinearMap.range dM := Iff.rfl

/-- The cycle represented by a differential is a boundary. -/
theorem map_mem_boundaries (hM : IsDGLeftModule h ℳ dM) (x : M) :
    (⟨dM x, hM.map_mem_cycles x⟩ : hM.cycles) ∈ hM.boundaries :=
  hM.mem_boundaries.mpr ⟨x, rfl⟩

/-- The **cohomology module** `H(M)` of a differential graded left module: the cycles modulo the
boundaries. -/
abbrev Cohomology (hM : IsDGLeftModule h ℳ dM) := hM.cycles ⧸ hM.boundaries

/-- A cohomology class vanishes exactly when the cycle representing it is a boundary. -/
theorem quotientMk_eq_zero_iff (hM : IsDGLeftModule h ℳ dM) {z : hM.cycles} :
    (Submodule.Quotient.mk z : hM.Cohomology) = 0 ↔ z ∈ hM.boundaries :=
  Submodule.Quotient.mk_eq_zero _

/-- The class of a differential vanishes in cohomology. -/
@[simp]
theorem quotientMk_map_eq_zero (hM : IsDGLeftModule h ℳ dM) (x : M) :
    (Submodule.Quotient.mk (⟨dM x, hM.map_mem_cycles x⟩ : hM.cycles) : hM.Cohomology) = 0 :=
  hM.quotientMk_eq_zero_iff.mpr (hM.map_mem_boundaries x)

/-- The boundaries of the algebra annihilate the cohomology module: a boundary `d a` carries a
cycle `x` to the boundary `dM (a • x)`. -/
theorem isTorsionBySet_boundaries (hM : IsDGLeftModule h ℳ dM) :
    Module.IsTorsionBySet h.cycles hM.Cohomology (h.boundaries.asIdeal : Set h.cycles) := by
  intro x a
  refine Submodule.Quotient.induction_on _ x fun z => ?_
  rw [← Submodule.Quotient.mk_smul, hM.quotientMk_eq_zero_iff, mem_boundaries]
  obtain ⟨b, hb⟩ := (h.mem_boundaries.mp (TwoSidedIdeal.mem_asIdeal.mp a.2))
  have hz : dM (z : M) = 0 := hM.mem_cycles.mp z.2
  have hval : ((a : h.cycles) • z : hM.cycles) = ((a : h.cycles) : A) • (z : M) := rfl
  rw [hval, ← hb]
  exact hM.map_smul_mem_range_of_map_eq_zero b hz

/-- **The cohomology of a differential graded left module is a module over the cohomology algebra.**
The action of a cycle of `A` on a cycle of `M` descends, because the boundaries of `A` annihilate
the cohomology module. -/
noncomputable instance instModuleCohomology (hM : IsDGLeftModule h ℳ dM) :
    Module h.Cohomology hM.Cohomology :=
  hM.isTorsionBySet_boundaries.module

/-- The action of the cohomology algebra on the cohomology module is the action of a representing
cycle. -/
@[simp]
theorem quotientMk_smul (hM : IsDGLeftModule h ℳ dM) (z : h.cycles) (x : hM.Cohomology) :
    (Ideal.Quotient.mk h.boundaries.asIdeal z) • x = z • x :=
  hM.isTorsionBySet_boundaries.mk_smul z x

section Grading

variable [IsScalarTower R A M]

/-- The degree-`p` homogeneous cycles, as a submodule of the module of cycles. -/
def cyclesDeg (hM : IsDGLeftModule h ℳ dM) (p : ℤ) : Submodule R hM.cycles :=
  (ℳ p).comap ((hM.cycles.subtype).restrictScalars R)

@[simp]
lemma mem_cyclesDeg (hM : IsDGLeftModule h ℳ dM) {p : ℤ} {z : hM.cycles} :
    z ∈ hM.cyclesDeg p ↔ (z : M) ∈ ℳ p := Iff.rfl

/-- Every cycle is a sum of homogeneous cycles: the homogeneous components of a cycle are cycles,
and they add up to it. -/
theorem iSup_cyclesDeg_eq_top (hM : IsDGLeftModule h ℳ dM) : ⨆ p : ℤ, hM.cyclesDeg p = ⊤ := by
  classical
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : dM (z : M) = 0 := hM.mem_cycles.mp z.2
  have hmem : ∀ p : ℤ, (decompose ℳ (z : M) p : M) ∈ hM.cycles :=
    fun p => hM.mem_cycles.mpr (hM.map_decompose_eq_zero hz p)
  have hsum : z = ∑ p ∈ (decompose ℳ (z : M)).support,
      (⟨(decompose ℳ (z : M) p : M), hmem p⟩ : hM.cycles) := by
    refine Subtype.ext ?_
    simpa [AddSubmonoidClass.coe_finsetSum] using
      (DirectSum.sum_support_decompose ℳ (z : M)).symm
  rw [hsum]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.mem_iSup_of_mem p (SetLike.coe_mem (decompose ℳ (z : M) p))

/-- The homogeneous cycle spaces are independent, as subspaces of the independent grading of the
ambient module. -/
theorem iSupIndep_cyclesDeg (hM : IsDGLeftModule h ℳ dM) : iSupIndep hM.cyclesDeg := by
  intro p
  rw [Submodule.disjoint_def]
  rintro z hz hz'
  have hle : Submodule.map ((hM.cycles.subtype).restrictScalars R)
      (⨆ (q : ℤ) (_ : q ≠ p), hM.cyclesDeg q) ≤ ⨆ (q : ℤ) (_ : q ≠ p), ℳ q := by
    rw [Submodule.map_iSup]
    refine iSup_le fun q => ?_
    rw [Submodule.map_iSup]
    exact iSup_le fun hq => le_iSup_of_le q (le_iSup_of_le hq (Submodule.map_comap_le _ _))
  have hz'prop : (z : M) ∈ ⨆ (q : ℤ) (_ : q ≠ p), ℳ q :=
    hle (Submodule.mem_map_of_mem hz')
  have hambient := (DirectSum.Decomposition.isInternal ℳ).submodule_iSupIndep p
  rw [Submodule.disjoint_def] at hambient
  have hz0 : (z : M) ∈ (⊥ : Submodule R M) :=
    hambient (z : M) (hM.mem_cyclesDeg.mp hz) hz'prop
  apply Subtype.ext
  simpa only [ZeroMemClass.coe_zero, Submodule.mem_bot] using hz0

/-- The homogeneous cycle spaces form an internal direct sum. -/
theorem isInternal_cyclesDeg (hM : IsDGLeftModule h ℳ dM) : DirectSum.IsInternal hM.cyclesDeg :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hM.iSupIndep_cyclesDeg
    hM.iSup_cyclesDeg_eq_top

/-- The cycles inherit the grading of the ambient differential graded left module. -/
noncomputable instance instDecompositionCyclesDeg (hM : IsDGLeftModule h ℳ dM) :
    DirectSum.Decomposition hM.cyclesDeg :=
  hM.isInternal_cyclesDeg.chooseDecomposition

/-- **The cycles of a differential graded left module are a graded module over the graded algebra of
cycles**: a homogeneous cycle of degree `p` carries a homogeneous cycle of degree `q` to one of
degree `p + q`. -/
instance instGradedSMulCyclesDeg (hM : IsDGLeftModule h ℳ dM) :
    SetLike.GradedSMul h.cyclesDeg hM.cyclesDeg where
  smul_mem := by
    intro i j a x ha hx
    exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) (h.mem_cyclesDeg.mp ha)
      (hM.mem_cyclesDeg.mp hx)

end Grading

end IsDGLeftModule

end TauCeti
