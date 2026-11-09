/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Orbit.HighestWeight
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The integral highest-weight coefficient

The Kostant orbit of a nonzero integral highest-weight vector has a unique integral linear
functional taking that vector to one and killing every other weight sublattice. Thus the
highest line is a split copy of `ℤ`, not merely a rational line meeting the orbit in a cyclic
subgroup. After extension to any commutative ring `A`, the chosen highest vector still generates
a split copy of `A`. In particular it does not vanish on reduction modulo a prime.

These statements apply to the orbit inside any rational module: neither finite dimension nor
irreducibility nor generation of the whole rational module is required. The construction uses
the integral weight decomposition and the normalization of the highest weight line proved in
`LieAlgebra.Basis.exists_eq_zsmul_of_mem_orbitOfRep_kostantForm`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §27.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct

namespace LieAlgebra.Basis

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance] HasUniqueDiv.of_module_rat

variable {ι L : Type*} [Finite ι] [LieRing L] [LieAlgebra ℚ L]
  {H : LieSubalgebra ℚ L} (b : LieAlgebra.Basis ι H)
  {V : Type*} [AddCommGroup V] [Module ℚ V]
  (ρ : UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  {v : V} {wt : ι → ℤ}

/-- The integral highest-weight coefficient on the Kostant orbit is uniquely characterized by
its value one on the chosen highest vector and its vanishing on all other weight sublattices. -/
theorem existsUnique_highestWeightCoordinate
    (hv : IsCartanWeightVector b.h ρ wt v)
    (hve : ∀ i, ρ (UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0) (hv0 : v ≠ 0) :
    ∃! f : Subring.orbitOfRep b.kostantForm ρ {v} →ₗ[ℤ] ℤ,
      f ⟨v, Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v)⟩ = 1 ∧
      ∀ (μ : ι → ℤ) (x : Subring.orbitOfRep b.kostantForm ρ {v}),
        μ ≠ wt → IsCartanWeightVector b.h ρ μ (x : V) → f x = 0 := by
  classical
  let M := (Subring.orbitOfRep b.kostantForm ρ {v}).toAddSubgroup
  let W := weightSublattice b.h ρ M
  let vM : M := ⟨v, Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v)⟩
  let vW : W wt := ⟨vM, (mem_weightSublattice_iff b.h ρ M).2 hv⟩
  -- The normalized highest weight sublattice is a copy of the integers.
  let s : ℤ →ₗ[ℤ] W wt := LinearMap.toSpanSingleton ℤ (W wt) vW
  have hs : Function.Bijective s := by
    constructor
    · intro m n hmn
      apply smul_left_injective ℤ hv0
      exact congrArg (fun x : W wt => ((x : M) : V)) hmn
    · intro x
      obtain ⟨n, hn⟩ := b.exists_eq_zsmul_of_mem_orbitOfRep_kostantForm hv hve
        (x : M).property ((mem_weightSublattice_iff b.h ρ M).1 x.property)
      exact ⟨n, Subtype.ext (Subtype.ext hn.symm)⟩
  let c := (LinearEquiv.ofBijective s hs).symm
  have hc (n : ℤ) : c (n • vW) = n := c.apply_symm_apply n
  have hM : DirectSum.IsInternal W := b.isInternal_weightSublattice_orbitOfRep hv hve
  -- Project the integral weight decomposition onto that line and read its coefficient.
  let d := (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hM).symm
  let f : M →ₗ[ℤ] ℤ := c.toLinearMap.comp
    ((DirectSum.component ℤ (ι → ℤ) (fun μ => W μ) wt).comp d.toLinearMap)
  have hf : f vM = 1 ∧ ∀ (μ : ι → ℤ) (x : M),
      μ ≠ wt → IsCartanWeightVector b.h ρ μ (x : V) → f x = 0 := by
    constructor
    · have hd : d vM wt = vW := hM.ofBijective_coeLinearMap_same vW
      exact (congrArg c hd).trans (by simpa only [one_smul] using hc 1)
    · intro μ x hμ hx
      have hd : d x wt = 0 := hM.ofBijective_coeLinearMap_of_mem_ne hμ
        ((mem_weightSublattice_iff b.h ρ M).2 hx)
      exact (congrArg c hd).trans c.map_zero
  refine ⟨f, hf, fun g hg => ?_⟩
  -- Every competing functional agrees on each weight summand, hence on the whole orbit.
  have hcomp : g.comp (DirectSum.coeLinearMap W) = f.comp (DirectSum.coeLinearMap W) := by
    apply DirectSum.linearMap_ext
    intro μ
    ext x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof]
    by_cases hμ : μ = wt
    · subst μ
      obtain ⟨n, hn⟩ := b.exists_eq_zsmul_of_mem_orbitOfRep_kostantForm hv hve
        (x : M).property ((mem_weightSublattice_iff b.h ρ M).1 x.property)
      have hx : (x : M) = n • vM := Subtype.ext hn
      rw [hx, map_smul, map_smul, hg.1, hf.1]
    · rw [hg.2 μ (x : M) hμ ((mem_weightSublattice_iff b.h ρ M).1 x.property),
        hf.2 μ (x : M) hμ ((mem_weightSublattice_iff b.h ρ M).1 x.property)]
  exact LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := hM.surjective x
    exact DFunLike.congr_fun hcomp y

/-- Over every commutative coefficient ring the chosen highest vector generates a split copy
of that ring in the specialized Kostant orbit. The functional is linear over the coefficient
ring, including when the ring has positive characteristic or zero divisors. -/
theorem exists_baseChange_highestWeightCoordinate
    (hv : IsCartanWeightVector b.h ρ wt v)
    (hve : ∀ i, ρ (UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0) (hv0 : v ≠ 0)
    (A : Type*) [CommRing A] :
    ∃ f : A ⊗[ℤ] Subring.orbitOfRep b.kostantForm ρ {v} →ₗ[A] A,
      ∀ a : A, f (a ⊗ₜ[ℤ]
        ⟨v, Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v)⟩) = a := by
  obtain ⟨c, hc, -⟩ := b.existsUnique_highestWeightCoordinate ρ hv hve hv0
  refine ⟨(TensorProduct.AlgebraTensorModule.rid ℤ A A).toLinearMap.comp (c.baseChange A),
    fun a => ?_⟩
  simp [hc.1]

/-- Scalar extension cannot kill or identify coefficients of the integral highest vector.
In particular the highest line survives reduction in every characteristic. -/
theorem injective_tmul_highestWeightVector
    (hv : IsCartanWeightVector b.h ρ wt v)
    (hve : ∀ i, ρ (UniversalEnvelopingAlgebra.ι ℚ (b.e i)) v = 0) (hv0 : v ≠ 0)
    (A : Type*) [CommRing A] :
    Function.Injective (fun a : A => a ⊗ₜ[ℤ]
      (⟨v, Subring.subset_orbitOfRep _ _ _ (Set.mem_singleton v)⟩ :
        Subring.orbitOfRep b.kostantForm ρ {v})) := by
  obtain ⟨f, hf⟩ := b.exists_baseChange_highestWeightCoordinate ρ hv hve hv0 A
  exact Function.LeftInverse.injective hf

end LieAlgebra.Basis
