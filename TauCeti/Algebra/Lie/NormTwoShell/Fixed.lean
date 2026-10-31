/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.GroupTheory.Perm.SumCongr
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Perm

/-!
# The integral fixed lattice of a diagram automorphism of the signed shell Lie algebra

Let `B : Matrix I I ℤ` be positive definite, for instance the Cartan matrix of a simply laced
Dynkin diagram, possibly disconnected, and let `σ` be a diagram automorphism, `B.reindex σ σ = B`.
Its pinned action `Matrix.ShellLieAlgebra.reindex σ` on the signed shell Lie algebra
`Matrix.ShellLieAlgebra B` permutes the integral basis, indexed by `I ⊕ Φ`, up to sign
(`Matrix.ShellLieAlgebra.reindex_basis`): it sends `H_(αᵢ)` to `H_(α_(σ i))` and the root vector
`x_a` to `s(a) x_(σ a)`, where `σ a = a ∘ σ.symm` and `s = Matrix.inversionSign B σ`. The
permutation of `I ⊕ Φ` is `Matrix.ShellLieAlgebra.basisPerm` and the signs are
`Matrix.ShellLieAlgebra.basisSign`. The fixed vectors of a signed permutation of a basis are
classified orbit by orbit (`Module.Basis.fixedBasisOfPerm`), which here gives the integral fixed
lattice, the submodule of `ShellLieAlgebra B` fixed by the pinned action:

* every orbit `O` of `σ` on the vertices contributes the Cartan vector `H_(∑_{i ∈ O} αᵢ)`
  (`Matrix.ShellLieAlgebra.fixedBasis_mk_inl`);
* an orbit `a, σ a, …, σ^(l-1) a` of roots whose monodromy `∏ᵣ s(σ^r a)` is `1` contributes the
  signed orbit sum `∑ᵣ cᵣ x_(σ^r a)`, with `c₀ = 1` and `cᵣ₊₁ = cᵣ s(σ^r a)`
  (`Module.Basis.repr_fixedBasisOfPerm_iterate`);
* an orbit of roots of monodromy `-1` contributes no fixed vector over `ℤ`
  (`Matrix.ShellLieAlgebra.repr_root_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one`).

These vectors form a basis over `ℤ` of the fixed lattice (`Matrix.ShellLieAlgebra.fixedBasis`), in
which the coordinates of a fixed vector are its coefficients at the chosen points of the orbits.
Over a coefficient ring with nonzero `2`-torsion an orbit of monodromy `-1` does carry fixed
vectors, so this integral lattice is not asserted to describe the fixed vectors after scalar
extension.

## Main definitions

* `Matrix.ShellLieAlgebra.basisPerm`, `Matrix.ShellLieAlgebra.basisSign`: the permutation of the
  basis indices and the signs by which the pinned action of `σ` moves the integral basis.
* `Matrix.ShellLieAlgebra.fixedBasis`: the basis over `ℤ` of the fixed lattice of `σ`, indexed by
  the orbits of monodromy `1`.

## Main results

* `Matrix.ShellLieAlgebra.fixedBasis_repr`: the coordinates of a fixed vector in `fixedBasis`.
* `Matrix.ShellLieAlgebra.fixedBasis_mk_inl`: the basis vector of an orbit of vertices is the
  Cartan vector of the sum of its simple roots.
* `Matrix.ShellLieAlgebra.finprod_basisSign_mk_inr`: the monodromy of an orbit of roots.
* `Matrix.ShellLieAlgebra.repr_root_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one`: fixed
  vectors vanish on the orbits of roots of monodromy `-1`.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.9, for the fixed points of a diagram automorphism.
-/

public section

open Equiv.Perm Module

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ} (σ : Equiv.Perm I)
  (hσ : B.reindex σ σ = B)

/-- The permutation of the index set `I ⊕ Φ` of the integral basis of `ShellLieAlgebra B` along
which the pinned action of a diagram automorphism `σ` moves the basis vectors: `σ` on the vertices
and `a ↦ a ∘ σ.symm` on the roots. -/
abbrev basisPerm : Equiv.Perm (I ⊕ B.normTwoShell) :=
  Equiv.Perm.sumCongr σ (normTwoShellCongr hσ)

/-- The signs with which the pinned action of a diagram automorphism `σ` moves the basis vectors of
`ShellLieAlgebra B`: `1` on the Cartan vectors and the inversion sign `Matrix.inversionSign B σ`
on the root vectors. -/
noncomputable abbrev basisSign : I ⊕ B.normTwoShell → ℤˣ :=
  Sum.elim (fun _ ↦ 1) fun a ↦ inversionSign B σ a

/-- **The integral fixed lattice of a diagram automorphism.** For positive definite `B` and a
diagram automorphism `σ`, the submodule of `ShellLieAlgebra B` fixed by the pinned action
`Matrix.ShellLieAlgebra.reindex σ` has a basis over `ℤ` indexed by the orbits of `basisPerm` on
`I ⊕ Φ` whose monodromy, the product of the signs `basisSign` over the orbit, is `1`. -/
noncomputable def fixedBasis (hB : B.PosDef) :
    Basis {c : Quotient (SameCycle.setoid (basisPerm σ hσ)) //
        ∏ᶠ (x) (_ : (basisPerm σ hσ).SameCycle c.out x), basisSign σ x = 1}
      ℤ (reindex σ hσ).toLinearMap.fixedSubmodule :=
  haveI := hB.finite_normTwoShell.to_subtype
  (basis B).fixedBasisOfPerm _ _ (reindex_basis σ hσ)

/-- The coordinate of a fixed vector on an orbit is its coefficient at the chosen point of the
orbit. -/
@[simp]
theorem fixedBasis_repr (hB : B.PosDef) (v : (reindex σ hσ).toLinearMap.fixedSubmodule)
    (c : {c : Quotient (SameCycle.setoid (basisPerm σ hσ)) //
      ∏ᶠ (x) (_ : (basisPerm σ hσ).SameCycle c.out x), basisSign σ x = 1}) :
    (fixedBasis σ hσ hB).repr v c = (basis B).repr v c.1.out := by
  have := hB.finite_normTwoShell.to_subtype
  rw [fixedBasis]
  exact (basis B).fixedBasisOfPerm_repr _ _ _ v c

private theorem basisSign_eq_one_of_sameCycle (i : I) {x : I ⊕ B.normTwoShell}
    (hx : (basisPerm σ hσ).SameCycle
      (Quotient.mk (SameCycle.setoid (basisPerm σ hσ)) (.inl i)).out x) :
    basisSign σ x = 1 := by
  obtain ⟨j, -, rfl⟩ := sameCycle_sumCongr_inl_iff_mem_image.1 (sameCycle_mk_out_left.1 hx)
  rfl

/-- Every orbit of vertices has monodromy `1`. -/
theorem finprod_basisSign_mk_inl (i : I) :
    ∏ᶠ (x) (_ : (basisPerm σ hσ).SameCycle
      (Quotient.mk (SameCycle.setoid (basisPerm σ hσ)) (.inl i)).out x), basisSign σ x = 1 :=
  finprod_mem_eq_one_of_forall_eq_one (s := Set.ofPred _) fun _ hx ↦
    basisSign_eq_one_of_sameCycle σ hσ i hx

/-- The monodromy of the orbit of the root `a` is the product of the inversion signs over the
orbit of `a` in `Φ`. -/
theorem finprod_basisSign_mk_inr (a : B.normTwoShell) :
    ∏ᶠ (x) (_ : (basisPerm σ hσ).SameCycle
      (Quotient.mk (SameCycle.setoid (basisPerm σ hσ)) (.inr a)).out x), basisSign σ x =
      ∏ᶠ (b) (_ : Equiv.Perm.SameCycle (normTwoShellCongr hσ) a b), inversionSign B σ b := by
  simp_rw [sameCycle_mk_out_left, sameCycle_sumCongr_inr_iff_mem_image]
  exact finprod_mem_image Sum.inr_injective.injOn

/-- **The orbit of a vertex.** The basis vector of the orbit `O` of the vertex `i` is the Cartan
vector `H_(∑_{j ∈ O} αⱼ)`. -/
theorem fixedBasis_mk_inl (hB : B.PosDef) (i : I) :
    (fixedBasis σ hσ hB ⟨Quotient.mk _ (.inl i), finprod_basisSign_mk_inl σ hσ i⟩ :
      ShellLieAlgebra B) = cartan B fun j ↦ if σ.SameCycle i j then 1 else 0 := by
  have := hB.finite_normTwoShell.to_subtype
  rw [fixedBasis, Basis.fixedBasisOfPerm_apply_of_forall_eq_one _ _ _ _ _
    fun _ hx ↦ basisSign_eq_one_of_sameCycle σ hσ i hx]
  simp_rw [sameCycle_mk_out_left, sameCycle_sumCongr_inl_iff_mem_image]
  rw [finsum_mem_image Sum.inl_injective.injOn]
  simp only [basis_inl, Set.mem_ofPred_eq]
  rw [finsum_cond_eq_sum_of_cond_iff _ (t := Finset.univ.filter (σ.SameCycle i)) (by simp),
    ← map_sum]
  congr 1
  ext k
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Fixed vectors vanish on the orbits of roots of monodromy `-1`.** If the product of the
inversion signs over the orbit of the root `a` is not `1`, every vector fixed by the pinned action
of `σ` has coefficient `0` at `x_a`. -/
theorem repr_root_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one (hB : B.PosDef)
    {v : ShellLieAlgebra B}
    (hv : v ∈ (reindex σ hσ).toLinearMap.fixedSubmodule) {a : B.normTwoShell}
    (ha : ∏ᶠ (b) (_ : Equiv.Perm.SameCycle (normTwoShellCongr hσ) a b), inversionSign B σ b ≠ 1) :
    (basis B).repr v (.inr a) = 0 := by
  have := hB.finite_normTwoShell.to_subtype
  refine (basis B).repr_eq_zero_of_mem_fixedSubmodule_of_finprod_ne_one _ _
    (reindex_basis σ hσ) hv ?_
  simp_rw [sameCycle_sumCongr_inr_iff_mem_image]
  rwa [finprod_mem_image Sum.inr_injective.injOn]

end Matrix.ShellLieAlgebra
