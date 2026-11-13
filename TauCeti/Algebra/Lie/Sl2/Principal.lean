/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre.Killing
public import TauCeti.Algebra.Lie.Weights.Borel
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Vector
import TauCeti.LinearAlgebra.RootSystem.Reduced

/-!
# The principal `sl₂` triple of a split semisimple Lie algebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field `K` of
characteristic zero, let `H` be a splitting Cartan subalgebra and let `b` be a base of its root
system. The sum `2ρ^∨` of the positive coroots, `TauCeti.twoWeylVector (rootSystem H).flip b.flip`,
pairs to `2` with every simple root. Choosing `sl₂` triples `(αᵢ^∨, eᵢ, fᵢ)` for the simple roots
and writing `2ρ^∨ = ∑ᵢ cᵢ αᵢ^∨` in the basis of simple coroots, the elements

`e = ∑ᵢ eᵢ`, `h = 2ρ^∨`, `f = ∑ᵢ cᵢ fᵢ`

form an `sl₂` triple, the **principal `sl₂` triple** of `b`. The bracket `⁅e, f⁆` collapses to
`∑ᵢ cᵢ αᵢ^∨ = h` because `⁅eᵢ, fⱼ⁆ = 0` for distinct simple roots (`TauCeti.isSerreSystem_coroot`),
and `h` scales every `eᵢ` and `fᵢ` by `±2`.

The element `e` lies in the positive nilradical, so it annihilates every highest weight vector;
the triple then turns a highest weight vector of weight `λ` into a primitive vector of `h`-weight
`λ(2ρ^∨)`. This is how the principal triple controls the symmetry of invariant forms on
irreducible modules.

## Main results

* `TauCeti.apply_twoWeylVector_flip_of_mem_support`: a simple root takes the value `2` on the sum of
  the positive coroots.
* `TauCeti.exists_isSl2Triple_twoWeylVector_flip`: **the principal `sl₂` triple**: when there is a
  root, the sum of the positive coroots is the neutral element of an `sl₂` triple whose raising
  element lies in the positive nilradical and whose lowering element lies in the negative one.

## References

* B. Kostant, *The principal three-dimensional subgroup and the Betti numbers of a complex simple
  Lie group*, Amer. J. Math. **81** (1959), 973–1032.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapitre VIII, §11.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module RootPairing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsKilling K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [IsTriangularizable K H L] (b : (rootSystem H).Base)

/-- **A simple root takes the value `2` on the sum of the positive coroots.** This is
`TauCeti.coroot'_twoWeylVector` for the flipped root system, whose roots are the coroots. -/
theorem apply_twoWeylVector_flip_of_mem_support {i : H.root} (hi : i ∈ b.support) :
    (i : Weight K H L) (twoWeylVector (rootSystem H).flip b.flip) = 2 := by
  have := (rootSystem H).flip_isReduced
  have h := coroot'_twoWeylVector (rootSystem H).flip b.flip (i := i) hi
  exact h

/-- **The principal `sl₂` triple.** If `H` has a root, the sum of the positive coroots is the
neutral element of an `sl₂` triple `(2ρ^∨, e, f)` with `e` in the positive nilradical and `f` in
the negative nilradical of the base `b`.

One takes `e = ∑ᵢ eᵢ` and `f = ∑ᵢ cᵢ fᵢ` for `sl₂` triples `(αᵢ^∨, eᵢ, fᵢ)` of the simple roots,
where `2ρ^∨ = ∑ᵢ cᵢ αᵢ^∨`. -/
theorem exists_isSl2Triple_twoWeylVector_flip [Nonempty H.root] :
    ∃ e f : L, IsSl2Triple ((twoWeylVector (rootSystem H).flip b.flip : H) : L) e f ∧
      e ∈ positiveNilradical H b ∧ f ∈ negativeNilradical H b := by
  classical
  set h : H := twoWeylVector (rootSystem H).flip b.flip
  -- `sl₂` triples for the simple roots, with neutral elements the simple coroots
  have nonZero (i : b.support) : ((i : H.root) : Weight K H L).IsNonZero :=
    H.isNonZero_coe_root _
  choose h' e f hsl2 he hf using fun i ↦ exists_isSl2Triple_of_weight_isNonZero (nonZero i)
  have hh' (i : b.support) : h' i = (((rootSystem H).coroot i : H) : L) := by
    rw [rootSystem_coroot_apply]
    exact (hsl2 i).h_eq_coroot (nonZero i) (he i) (hf i)
  simp_rw [hh'] at hsl2
  have hS := isSerreSystem_coroot b hsl2 he hf
  -- the coefficients of `2ρ^∨` in the simple coroots
  set c : b.support →₀ K := b.toCoweightBasis.repr h
  have hsum : ∑ i, c i • (((rootSystem H).coroot i : H) : L) = (h : L) := by
    have := b.toCoweightBasis.sum_repr h
    simp only [Base.toCoweightBasis_apply] at this
    rw [← this, Submodule.coe_sum]
    simp [c]
  -- `h` acts on the simple root vectors by `±2`
  have hval (i : b.support) : ((i : H.root) : Weight K H L) h = 2 :=
    apply_twoWeylVector_flip_of_mem_support b i.2
  have hhe (i : b.support) : ⁅(h : L), e i⁆ = (2 : K) • e i := by
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (he i), hval]
  have hhf (i : b.support) : ⁅(h : L), f i⁆ = -((2 : K) • f i) := by
    rw [← LieSubalgebra.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace (hf i), Pi.neg_apply,
      hval, neg_smul]
  refine ⟨∑ i, e i, ∑ i, c i • f i, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- `2ρ^∨` is nonzero as soon as there is a root
    exact_mod_cast twoWeylVector_ne_zero (rootSystem H).flip b.flip
  · rw [← hsum, sum_lie]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lie_sum, Finset.sum_eq_single i (fun j _ hji ↦ ?_) (by simp), lie_smul,
      hS.lie_E_F_self]
    rw [lie_smul, hS.lie_E_F_of_ne i j hji.symm, smul_zero]
  · rw [lie_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hhe, ofNat_smul_eq_nsmul]
  · rw [lie_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lie_smul, hhf, smul_neg, smul_comm, ofNat_smul_eq_nsmul (R := K)]
  · exact sum_mem fun i _ ↦ mem_positiveNilradical_of_mem_rootSpace H b
      (support_subset_posRoots _ b i.2) (he i)
  · refine sum_mem fun i _ ↦ (negativeNilradical H b).smul_mem _ ?_
    -- `fᵢ` is a root vector of the negative root `-αᵢ`, the reflection of `αᵢ` in itself
    have hneg : ⇑((rootSystem H).root ((rootSystem H).reflectionPerm i i)) =
        -⇑((i : H.root) : Weight K H L) := by
      rw [root_reflectionPerm, RootPairing.reflection_apply_self]
      simp
    refine mem_negativeNilradical_of_mem_rootSpace H b
      ((reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ b _).mpr
        (support_subset_posRoots _ b i.2)) ?_
    rw [rootSystem_root_apply] at hneg
    rw [hneg]
    exact hf i

end TauCeti
