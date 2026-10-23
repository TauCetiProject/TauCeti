/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Cochain
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.Cochain
import TauCeti.Algebra.Lie.Derivation.Cocycle
import TauCeti.Algebra.Lie.Extension
import TauCeti.Algebra.Lie.HighestWeight.CompleteReducibility
import TauCeti.Algebra.Lie.LeviDecomposition.Abelian
import TauCeti.Algebra.Lie.Quotient

/-!
# Whitehead's lemmas

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K` of
characteristic zero, and `M` a finite-dimensional `L`-module. **Whitehead's first and second
lemmas** say that the Lie algebra cohomology groups `H¹(L, M)` and `H²(L, M)` vanish. In terms of
Mathlib's low-degree cochains (`LieModule.Cohomology.d₁₂`, `LieModule.Cohomology.twoCocycle`):

* every 1-cochain `f` with `d₁₂ f = 0` is `x ↦ ⁅x, m⁆` for some `m : M`; equivalently every Lie
  derivation `L → M` is inner;
* every 2-cocycle is the coboundary `d₁₂ f` of a 1-cochain `f`.

These are the vanishing theorems used to normalise Lie algebra cocycles against a semisimple
subalgebra, as in the classification of the continuous central extensions of a loop algebra.

## The arguments

*First lemma.* A Lie derivation `D : L → M` shears the action of `L` on `M × K`
(`LieDerivation.ShearedModule D`): `⁅x, (m, c)⁆ = (⁅x, m⁆ + c • D x, 0)`. This is a Lie module
precisely because `D` satisfies the Leibniz rule, and `L` carries it into the proper Lie submodule
`M × 0`. By Weyl's theorem
(`TauCeti.exists_invariant_notMem_of_isKilling`) there is an invariant vector `(m, c)` with
`c ≠ 0`, and then `D x = ⁅x, -c⁻¹ • m⁆`.

*Second lemma.* A 2-cocycle `c` defines Mathlib's extension `LieAlgebra.ofTwoCocycle c` of `L` by
`M`, in which `M` is an abelian ideal with quotient `L`. By the abelian case of Levi's theorem
(`LieIdeal.exists_lieSubalgebra_isCompl_of_isLieAbelian`) this ideal has a complementary Lie
subalgebra, which the projection identifies with `L`. The inverse identification is a Lie algebra
section `x ↦ (x, g x)`, and the section being a Lie homomorphism says exactly `c = d₁₂ (-g)`.

## Main results

* `LieDerivation.IsKilling.exists_eq_inner`: every Lie derivation into a finite-dimensional module
  is inner (Whitehead's first lemma).
* `LieModule.Cohomology.exists_eq_lie_of_d₁₂_eq_zero`: the cochain form of the first lemma.
* `LieModule.Cohomology.exists_d₁₂_eq`: every 2-cocycle is a coboundary (Whitehead's second lemma).
* `LieModule.Cohomology.twoCocycle_eq_range_d₁₂`: the 2-cocycles are exactly the coboundaries.

## References

* N. Jacobson, *Lie Algebras*, Chapter III, for Whitehead's lemmas and their relation to the
  theorems of Weyl and Levi.
* C. A. Weibel, *An Introduction to Homological Algebra*, §7.8.
-/

public section

open LieAlgebra LieModule LieModule.Cohomology

universe u v w

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]

namespace LieDerivation.IsKilling

/-- **Whitehead's first lemma.** Over a field of characteristic zero, every Lie derivation from a
finite-dimensional Lie algebra with nondegenerate Killing form into a finite-dimensional module is
inner: it is `x ↦ ⁅x, m⁆` for some `m`. -/
theorem exists_eq_inner (D : LieDerivation K L M) : ∃ m : M, inner K L M m = D := by
  -- The proper Lie submodule `M × 0` of the module sheared by `D`, into which `L` carries
  -- everything.
  let e := LieDerivation.ShearedModule.ofProd D
  let N : LieSubmodule K L D.ShearedModule :=
    { (LinearMap.snd K M K ∘ₗ e.symm.toLinearMap).ker with
      lie_mem {x v} _ := by simp [e] }
  have hmemN (v : D.ShearedModule) : v ∈ N ↔ (e.symm v).2 = 0 := LinearMap.mem_ker
  have hN : N ≠ ⊤ := fun h ↦
    one_ne_zero (α := K) (by simpa [e] using (hmemN (e (0, 1))).1 (h ▸ LieSubmodule.mem_top _))
  obtain ⟨v, hvN, hv⟩ := TauCeti.exists_invariant_notMem_of_isKilling N hN
    fun x v ↦ (hmemN _).2 (by simp [e])
  have hc : (e.symm v).2 ≠ 0 := fun h ↦ hvN ((hmemN v).2 h)
  refine ⟨-(e.symm v).2⁻¹ • (e.symm v).1, LieDerivation.ext fun x ↦ ?_⟩
  have h : ⁅x, (e.symm v).1⁆ + (e.symm v).2 • D x = 0 := by
    simpa [e] using congrArg (fun w ↦ (e.symm w).1) (hv x)
  rw [inner_apply_apply, lie_smul, eq_neg_of_add_eq_zero_left h]
  simp [smul_smul, hc]

end LieDerivation.IsKilling

namespace LieModule.Cohomology

/-- **Whitehead's first lemma** for cochains: over a field of characteristic zero, a 1-cocycle of a
finite-dimensional Lie algebra with nondegenerate Killing form with values in a finite-dimensional
module is a coboundary, `f x = ⁅x, m⁆`. -/
theorem exists_eq_lie_of_d₁₂_eq_zero {f : oneCochain K L M} (hf : d₁₂ K L M f = 0) :
    ∃ m : M, ∀ x, f x = ⁅x, m⁆ := by
  obtain ⟨m, hm⟩ := LieDerivation.IsKilling.exists_eq_inner (.ofD₁₂EqZero f hf)
  exact ⟨m, fun x ↦ by simpa using (congrArg (· x) hm).symm⟩

/-- **Whitehead's second lemma.** Over a field of characteristic zero, every 2-cocycle of a
finite-dimensional Lie algebra with nondegenerate Killing form with values in a finite-dimensional
module is a coboundary. -/
theorem exists_d₁₂_eq (c : twoCocycle K L M) : ∃ f : oneCochain K L M, d₁₂ K L M f = c := by
  -- The sheared Lie algebra `E = L × M` and its projection `p` onto `L`, with kernel `0 × M`.
  let p := ofTwoCocycle.proj c
  have : IsKilling K (ofTwoCocycle c ⧸ p.ker) :=
    isKilling_of_equiv (p.quotKerEquivOfSurjective (ofTwoCocycle.proj_surjective c)).symm
  obtain ⟨S, hS⟩ := p.ker.exists_lieSubalgebra_isCompl_of_isLieAbelian
  -- The projection identifies the Levi complement `S` with `L`.
  let e : S ≃ₗ⁅K⁆ L := (p.ker.quotientEquivOfIsCompl S hS).symm.trans
    (p.quotKerEquivOfSurjective (ofTwoCocycle.proj_surjective c))
  -- The inverse identification is a Lie section `x ↦ (x, g x)` of `p`.
  let g : oneCochain K L M := LinearMap.snd K L M ∘ₗ (ofProdLinearEquiv c).symm.toLinearMap ∘ₗ
    S.toSubmodule.subtype ∘ₗ (e.symm : L →ₗ⁅K⁆ S).toLinearMap
  have hg (z : L) : g z = ((ofProd c).symm (e.symm z : ofTwoCocycle c)).2 := by simp [g]
  have he (s : S) : e s = p s := by simp [e]
  have hfst (z : L) : ((ofProd c).symm (e.symm z : ofTwoCocycle c)).1 = z := by
    simpa [p] using (he (e.symm z)).symm.trans (e.apply_symm_apply z)
  -- That the section preserves brackets says exactly that `c = d₁₂ (-g)`.
  refine ⟨-g, ?_⟩
  ext x y
  have h := congrArg (fun z : S ↦ ((ofProd c).symm (z : ofTwoCocycle c)).2) (e.symm.map_lie x y)
  simp only [LieSubalgebra.coe_bracket, bracket_ofTwoCocycle, Equiv.symm_apply_apply, hfst] at h
  simp only [d₁₂_apply_coe_apply_apply, LinearMap.neg_apply, hg, h, lie_neg]
  abel

/-- **Whitehead's second lemma**, as an equality of submodules: the 2-cocycles of a
finite-dimensional Lie algebra with nondegenerate Killing form in characteristic zero, with values
in a finite-dimensional module, are exactly the coboundaries. -/
theorem twoCocycle_eq_range_d₁₂ : twoCocycle K L M = LinearMap.range (d₁₂ K L M) :=
  le_antisymm (fun c hc ↦ exists_d₁₂_eq ⟨c, hc⟩) range_d₁₂_le_twoCocycle

end LieModule.Cohomology
