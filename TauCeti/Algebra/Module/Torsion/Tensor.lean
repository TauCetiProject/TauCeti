/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Snake
import TauCeti.Algebra.Module.ZMod.Extend

/-!
# Tensoring torsion–reduction sequences

Tensoring over `ℤ` preserves injections whose target is killed by a prime: the injection
splits additively. More generally it preserves exactness at any pair of maps whose final
module is killed by a prime, because the inclusion of the second map's image splits.
The tensor factor is an arbitrary abelian group; it need not be flat over `ℤ`.
The additive splitting comes from `AddMonoidHom.exists_comp_eq_of_injective` in
`TauCeti.Algebra.Module.ZMod.Extend`.

Applied to multiplication by `p` on a short exact sequence, this proves exactness of the
scalar-extended six-term sequence of `p`-torsion and reduction modulo `p`. In particular it
applies to a field of characteristic `p`, although that field is not flat over `ℤ`. This is
the exactness input to additivity of the difference between reduction and torsion classes
in the Grothendieck group of representations.

The two connecting-map lemmas below use `TauCeti.torsionByδ`, the multiplication-by-a-scalar
snake map. The other terms follow from `TauCeti.exact_torsionByMap` and Mathlib's
`QuotSMulTop.map_exact`; tensoring the first map preserves injectivity by
`LinearMap.lTensor_injective_of_isTorsionBy`, and tensoring the last preserves surjectivity
by Mathlib's `LinearMap.lTensor_surjective`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Section VII.3, (7.3.3).
-/

public section

namespace TauCeti

open Function LinearMap TensorProduct

-- These actions agree with the canonical additive ℤ-action, but need not be definitionally equal.
attribute [local instance high] Submodule.module Submodule.Quotient.module TensorProduct.instModule

variable (A : Type*) [AddCommGroup A] [Module ℤ A]
  {M N P : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]

/-- Tensoring an injection into a module killed by a prime preserves injectivity, even when
the tensor factor is not flat over `ℤ`. -/
theorem _root_.LinearMap.lTensor_injective_of_isTorsionBy (f : M →ₗ[ℤ] N)
    (p : ℕ) [Fact p.Prime] (hf : Injective f) (hN : Module.IsTorsionBy ℤ N (p : ℤ)) :
    Injective (f.lTensor A) := by
  have hN' : ∀ x : N, p • x = 0 := fun x => by
    simpa only [← Nat.cast_smul_eq_nsmul ℤ] using hN (x := x)
  obtain ⟨s, hs⟩ := AddMonoidHom.exists_comp_eq_of_injective hN'
    (f := f.toAddMonoidHom) hf (AddMonoidHom.id M)
  let sℤ : N →ₗ[ℤ] M :=
    { s with map_smul' := fun c x => map_intCast_smul s ℤ ℤ c x }
  have hsplit : sℤ ∘ₗ f = LinearMap.id :=
    LinearMap.ext fun x => DFunLike.congr_fun hs x
  have htensor : sℤ.lTensor A ∘ₗ f.lTensor A = LinearMap.id := by
    rw [← lTensor_comp, hsplit, lTensor_id]
  exact HasLeftInverse.injective ⟨sℤ.lTensor A, fun x => LinearMap.congr_fun htensor x⟩

/-- Tensoring preserves exactness of a pair whose final module is killed by a prime. Neither
surjectivity of the second map nor flatness of the tensor factor is required. -/
theorem lTensor_exact_of_isTorsionBy {f : M →ₗ[ℤ] N} {g : N →ₗ[ℤ] P}
    (p : ℕ) [Fact p.Prime] (hfg : Exact f g) (hP : Module.IsTorsionBy ℤ P (p : ℤ)) :
    Exact (f.lTensor A) (g.lTensor A) := by
  have hfg' : Exact f g.rangeRestrict := by
    simpa only [LinearMap.exact_iff, ker_rangeRestrict] using hfg
  have hex := lTensor_exact A hfg' g.surjective_rangeRestrict
  have hi := (range g).subtype.lTensor_injective_of_isTorsionBy A p
    (range g).injective_subtype hP
  have hg : g.lTensor A = (range g).subtype.lTensor A ∘ₗ g.rangeRestrict.lTensor A := by
    rw [← lTensor_comp, g.subtype_comp_rangeRestrict]
  rw [hg]
  exact hi.comp_exact_iff_exact.mpr hex

variable {f : M →ₗ[ℤ] N} {g : N →ₗ[ℤ] P} (p : ℕ) [Fact p.Prime]

/-- Exactness at `A ⊗[ℤ] P[p]` in the tensor-extended torsion–reduction sequence. -/
theorem lTensor_exact_torsionByMap_torsionByδ (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) :
    Exact ((torsionByMap (p : ℤ) g).lTensor A)
      ((torsionByδ (p : ℤ) hfg hf hg).lTensor A) :=
  lTensor_exact_of_isTorsionBy A p (exact_torsionByMap_torsionByδ hfg hf hg)
    ((Module.isTorsionBy_iff_mem_annihilator ℤ _).mpr
      (QuotSMulTop.mem_annihilator (M := M) (p : ℤ)))

/-- Exactness at `A ⊗[ℤ] (M / pM)` in the tensor-extended torsion–reduction sequence. -/
theorem lTensor_exact_torsionByδ_quotSMulTop_map (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) :
    Exact ((torsionByδ (p : ℤ) hfg hf hg).lTensor A)
      ((QuotSMulTop.map (p : ℤ) f).lTensor A) :=
  lTensor_exact_of_isTorsionBy A p (exact_torsionByδ_quotSMulTop_map hfg hf hg)
    ((Module.isTorsionBy_iff_mem_annihilator ℤ _).mpr
      (QuotSMulTop.mem_annihilator (M := N) (p : ℤ)))

end TauCeti
