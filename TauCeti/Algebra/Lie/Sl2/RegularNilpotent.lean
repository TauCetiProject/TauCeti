/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Borel
public import TauCeti.Algebra.Lie.Sl2.Principal
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.Algebra.Lie.Weights.Eigenvector

/-!
# Density of the regular nilpotent elements

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K` of
characteristic zero. This file proves that the regular nilpotent elements, those `x` with `ad x`
nilpotent whose centralizer `ker (ad x)` has the least possible dimension
(`LieAlgebra.IsCentralizerRegular`), are Zariski dense among all nilpotent elements when `K` is
algebraically closed: a polynomial function on `L` vanishing at every regular nilpotent element
vanishes at every nilpotent element (`TauCeti.lift_eval_eq_zero_of_forall_isCentralizerRegular`).
In other words, the nilpotent cone is the Zariski closure of its regular elements.

The argument runs inside the positive nilradical `n⁺` of a splitting Cartan subalgebra `H` and a
base `b` of its root system.

* **`n⁺` consists of nilpotent elements.** The principal grading of `L` by the eigenvalues of
  `ad (2ρ^∨)`, where `2ρ^∨` is the sum of the positive coroots, puts the root space of a positive
  root `α` in degree `2 ht(α) > 0`
  (`TauCeti.positiveNilradical_le_iSup_eigenspace_ad_twoWeylVector_flip`). An element of
  positive degree raises the degree on every finite-dimensional module, on which `2ρ^∨` acts with
  integer eigenvalues as the neutral element of an `sl₂` triple, so it acts nilpotently
  (`TauCeti.isNilpotent_toEnd_of_mem_positiveNilradical`).
* **`n⁺` contains a regular element.** A sum of nonzero simple root vectors is the nilpositive
  element of a principal `sl₂` triple, hence regular
  (`TauCeti.exists_isCentralizerRegular_mem_positiveNilradical`).
* **Density in `n⁺`.** Regularity is the nonvanishing of some minor of `ad x`, a polynomial
  condition on the vector space `n⁺`; as it holds somewhere, the regular elements of `n⁺` are
  Zariski dense in `n⁺` (`LieAlgebra.lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem`,
  giving `TauCeti.lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem_positiveNilradical`).

Over an algebraically closed field every nilpotent element lies in some `n⁺`
(`TauCeti.exists_mem_positiveNilradical_of_isNilpotent_ad`), which gives the density in the whole
nilpotent cone. No conjugation by the adjoint group and no irreducibility of the cone is used.

## Main results

* `TauCeti.isNilpotent_toEnd_of_mem_positiveNilradical`: every element of `n⁺` acts nilpotently on
  every finite-dimensional module.
* `TauCeti.exists_isCentralizerRegular_mem_positiveNilradical`: `n⁺` contains a regular element.
* `TauCeti.lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem_positiveNilradical`: the
  regular elements of `n⁺` are Zariski dense in `n⁺`.
* `TauCeti.lift_eval_eq_zero_of_forall_isCentralizerRegular`: over an algebraically closed field,
  the regular nilpotent elements are Zariski dense in the nilpotent cone.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032, §5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §4.1.
* Z. Yun, *Lectures on Springer theories and orbital integrals*, arXiv:1602.01451, §1.3.2.
-/

public section

open LieAlgebra LieModule LieAlgebra.IsKilling Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L]

namespace TauCeti

section Split

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

/-- **The positive nilradical has positive principal degree.** Every element of `n⁺` is a sum of
eigenvectors of `ad (2ρ^∨)` with positive integer eigenvalues: a positive root `α` takes the value
`2 ht(α)` at `2ρ^∨`. -/
theorem positiveNilradical_le_iSup_eigenspace_ad_twoWeylVector_flip :
    (positiveNilradical H b).toSubmodule ≤ ⨆ (j : ℤ) (_ : 0 < j),
      (ad K L ((twoWeylVector (rootSystem H).flip b.flip : H) : L)).eigenspace (j : K) := by
  intro x hx
  rw [LieSubalgebra.mem_toSubmodule, mem_positiveNilradical, rootSpaceSpan_eq_iSup] at hx
  refine LieSubmodule.iSup_induction _ (motive := (· ∈ _)) hx (fun α y hy ↦ ?_) (zero_mem _)
    fun _ _ ↦ add_mem
  have hα : 0 < b.height (α : H.root) :=
    b.isPos_iff.mp ((mem_posRoots _ b _).mp α.property)
  refine Submodule.mem_iSup_of_mem (2 * b.height (α : H.root))
    (Submodule.mem_iSup_of_mem (by omega) ?_)
  rw [Module.End.mem_eigenspace_iff, ad_apply, ← LieSubalgebra.coe_bracket_of_module,
    lie_eq_smul_of_mem_rootSpace hy, Weight.toLinear_apply,
    root_apply_twoWeylVector_flip_eq_two_mul_height]
  simp

variable {b} in
/-- **The positive nilradical acts nilpotently.** Every element of the positive nilradical `n⁺` of
a splitting Cartan subalgebra acts nilpotently on every finite-dimensional module; in particular
its elements are `ad`-nilpotent. -/
theorem isNilpotent_toEnd_of_mem_positiveNilradical {M : Type*} [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M] {x : L}
    (hx : x ∈ positiveNilradical H b) : IsNilpotent (toEnd K L M x) := by
  rcases isEmpty_or_nonempty H.root with hroot | hroot
  · -- without roots `n⁺` is zero
    have hx0 : x = 0 := by
      rw [mem_positiveNilradical, rootSpaceSpan_eq_iSup] at hx
      exact LieSubmodule.iSup_induction _ (motive := (· = 0)) hx
        (fun α ↦ isEmptyElim (α : H.root)) rfl fun _ _ h₁ h₂ ↦ by rw [h₁, h₂, add_zero]
    rw [hx0, map_zero]
    exact IsNilpotent.zero
  · -- `2ρ^∨` is the neutral element of a triple, so it acts with integer eigenvalues on `M`
    obtain ⟨e, f, t⟩ := exists_isSl2Triple_twoWeylVector_flip b
    exact isNilpotent_toEnd_of_mem_iSup_eigenspace_ad (iSup_eigenspace_toEnd_intCast_eq_top t)
      (positiveNilradical_le_iSup_eigenspace_ad_twoWeylVector_flip b hx)

/-- **The positive nilradical contains a regular element.** A sum of nonzero simple root vectors is
a principal nilpotent element, whose centralizer has the least possible dimension. When there are
no roots, `L` is abelian and `0` is regular. -/
theorem exists_isCentralizerRegular_mem_positiveNilradical :
    ∃ e ∈ positiveNilradical H b, IsCentralizerRegular K e := by
  rcases isEmpty_or_nonempty H.root with hroot | hroot
  · -- without roots `L` is its Cartan subalgebra, which is abelian
    have hnz (α : Weight K H L) : ¬α.IsNonZero := fun hα ↦
      IsEmpty.false (⟨α, by simpa [LieSubalgebra.root] using hα⟩ : H.root)
    have htop : H.toLieSubmodule = ⊤ := by
      simpa [hnz] using cartan_sup_iSup_rootSpace_eq_top (H := H)
    have hmem (y : L) : y ∈ H := by
      rw [← LieSubalgebra.mem_toLieSubmodule, htop]
      exact LieSubmodule.mem_top y
    refine ⟨0, zero_mem _, isCentralizerRegular_zero_iff.mpr ⟨fun y z ↦ ?_⟩⟩
    simpa using congrArg Subtype.val (trivial_lie_zero H H ⟨y, hmem y⟩ ⟨z, hmem z⟩)
  · choose e he he0 using fun i : b.support ↦ ((i : H.root) : Weight K H L).exists_ne_zero
    obtain ⟨f, -, t⟩ := exists_mem_negativeNilradical_isSl2Triple_twoWeylVector_flip b he he0
    exact ⟨_, sum_mem fun i _ ↦ mem_positiveNilradical_of_mem_rootSpace H b
      (support_subset_posRoots _ b i.property) (he i), t.isCentralizerRegular_e⟩

/-- **The regular elements of `n⁺` are Zariski dense in `n⁺`.** A polynomial function on `L`
vanishing at every regular element of the positive nilradical `n⁺` of a splitting Cartan
subalgebra vanishes on all of `n⁺`. -/
theorem lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem_positiveNilradical
    {p : SymmetricAlgebra K (Dual K L)}
    (hp : ∀ y ∈ positiveNilradical H b, IsCentralizerRegular K y →
      SymmetricAlgebra.lift (Dual.eval K L y) p = 0)
    {x : L} (hx : x ∈ positiveNilradical H b) : SymmetricAlgebra.lift (Dual.eval K L x) p = 0 :=
  lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem
    (V := (positiveNilradical H b).toSubmodule)
    (exists_isCentralizerRegular_mem_positiveNilradical b) hp hx

end Split

/-- **The regular nilpotent elements are dense in the nilpotent cone.** Over an algebraically
closed field of characteristic zero, a polynomial function on `L` that vanishes at every
`ad`-nilpotent element whose centralizer has minimal dimension vanishes at every `ad`-nilpotent
element. -/
theorem lift_eval_eq_zero_of_forall_isCentralizerRegular [IsAlgClosed K]
    {p : SymmetricAlgebra K (Dual K L)}
    (hp : ∀ y : L, IsNilpotent (ad K L y) → IsCentralizerRegular K y →
      SymmetricAlgebra.lift (Dual.eval K L y) p = 0)
    {x : L} (hx : IsNilpotent (ad K L x)) : SymmetricAlgebra.lift (Dual.eval K L x) p = 0 := by
  obtain ⟨H, _, b, hxb⟩ := exists_mem_positiveNilradical_of_isNilpotent_ad hx
  exact lift_eval_eq_zero_of_forall_isCentralizerRegular_of_mem_positiveNilradical b
    (fun y hy ↦ hp y (isNilpotent_toEnd_of_mem_positiveNilradical hy)) hxb

end TauCeti
