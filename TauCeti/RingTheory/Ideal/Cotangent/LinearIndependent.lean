/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import TauCeti.RingTheory.Ideal.Operations

/-!
# Linear independence in the conormal module

For an ideal `I` of a commutative ring `R`, elements `x₁, …, xₙ ∈ I` have linearly independent
images in the conormal module `I/I²` over `R/I` exactly when a relation `∑ rᵢ xᵢ ∈ I²` forces
every coefficient `rᵢ` into `I`. In a free `R`-module `F` the same elements then detect `I² F`
coordinatewise: `∑ xᵢ fᵢ ∈ I² F` forces every `fᵢ ∈ I F`.

For the maximal ideal `𝔪` of a local ring, such `xᵢ` are lifts of linearly independent vectors of
the cotangent space `𝔪/𝔪²`, for instance part of a minimal system of generators of `𝔪`. This is
the form in which minimal generators enter the comparison between a Koszul complex and a minimal
free resolution of the residue field (Stacks, Lemma 10.110.3).

## Main results

* `Ideal.linearIndependent_toCotangent_iff`: linear independence in `I/I²` in terms of
  relations modulo `I²`.
* `Ideal.mem_smul_top_of_sum_smul_mem_sq_smul_top`: in a free module, `∑ xᵢ fᵢ ∈ I² F` forces
  `fᵢ ∈ I F` when the `xᵢ` are linearly independent in `I/I²`.

## References

* [The Stacks Project, Lemma 10.110.3](https://stacks.math.columbia.edu/tag/00OA)
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} [Fintype ι]

/-- Elements `xᵢ ∈ I` have linearly independent images in `I/I²` over `R/I` exactly when
`∑ rᵢ xᵢ ∈ I²` forces every coefficient `rᵢ` into `I`. -/
theorem linearIndependent_toCotangent_iff (x : ι → I) :
    LinearIndependent (R ⧸ I) (fun i ↦ I.toCotangent (x i)) ↔
      ∀ r : ι → R, ∑ i, r i * x i ∈ I ^ 2 → ∀ i, r i ∈ I := by
  -- A combination with coefficients in `R ⧸ I` is the class of the corresponding element of `I`.
  have key (r : ι → R) : ∑ i, Ideal.Quotient.mk I (r i) • I.toCotangent (x i) =
      I.toCotangent (∑ i, r i • x i) := by
    simp [← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hcoe (r : ι → R) : ((∑ i, r i • x i : I) : R) = ∑ i, r i * x i := by
    simp
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h r hr i
    refine Ideal.Quotient.eq_zero_iff_mem.mp (h (fun i ↦ Ideal.Quotient.mk I (r i)) ?_ i)
    rw [key, toCotangent_eq_zero, hcoe]
    exact hr
  · intro h g hg i
    choose r hr using fun i ↦ Ideal.Quotient.mk_surjective (g i)
    simp_rw [← hr] at hg ⊢
    rw [key, toCotangent_eq_zero, hcoe] at hg
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h r hg i)

/-- Let `xᵢ ∈ I` have linearly independent images in `I/I²`. In a free module `F`, if
`∑ xᵢ fᵢ ∈ I² F` then every `fᵢ` lies in `I F`. -/
theorem mem_smul_top_of_sum_smul_mem_sq_smul_top {x : ι → I}
    (hx : LinearIndependent (R ⧸ I) (fun i ↦ I.toCotangent (x i)))
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] {f : ι → F}
    (hf : ∑ i, (x i : R) • f i ∈ I ^ 2 • (⊤ : Submodule R F)) (i : ι) :
    f i ∈ I • (⊤ : Submodule R F) := by
  let c := Module.Free.chooseBasis R F
  rw [c.mem_smul_top_iff]
  intro t
  refine (I.linearIndependent_toCotangent_iff x).mp hx (fun i ↦ c.repr (f i) t) ?_ i
  simpa [mul_comm] using c.mem_smul_top_iff.mp hf t

end Ideal
