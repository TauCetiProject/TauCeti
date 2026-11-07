/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.Algebra.Lie.NormTwoShell.TypeA.Basic
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.Coordinates
public import TauCeti.Algebra.Lie.Subalgebra.Fixed.Basic
public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.RootSystem.DiagramPermutations

/-!
# The reversal of the type-`A` signed shell Lie algebra is the matrix graph automorphism

The reversal `graphPermA r` of the chain `A_r` is a symmetry of the Cartan matrix
`CartanMatrix.A r` (`TauCeti.reindex_cartanMatrix_A_graphPermA`), so it relabels the signed shell
Lie algebra `Matrix.ShellLieAlgebra (CartanMatrix.A r)`, the Frenkel--Kac Lie algebra over `ℤ`, by
the pinned action `Matrix.ShellLieAlgebra.reindex`:

`H_h ↦ H_(h ∘ rev)`,  `x_a ↦ s(a) x_(a ∘ rev)`,

where `s = Matrix.inversionSign (CartanMatrix.A r) (graphPermA r)` is the inversion sign of the
reversal. On the matrix side, the pinned graph automorphism of `sl_(r+1)` is
`θ(X) = -J Xᵀ J⁻¹` (`TauCeti.typeASpecialLinearGraphAutomorphism`), where `J` is the signed
antidiagonal matrix `TauCeti.typeAGraphConjugator`.

The main result (`TauCeti.typeAShellEquiv_reindex_graphPermA`) is that the signed matrix
comparison `TauCeti.typeAShellEquiv` of the shell algebra with `sl_(r+1)` over `ℤ` intertwines the
two: the pinned shell reversal is `θ`. Both maps are Lie ring homomorphisms carrying the Chevalley
generators `Eᵢ`, `Fᵢ` to those at the reversed node `rev i` with unchanged parameter, and the
Chevalley generators generate the shell algebra over `ℤ`.

Two consequences record the root signs and the fixed lattice.

* The pinned shell reversal sends the root vector of `ε_p - ε_q` to `(-1) ^ (h - 1)` times the root
  vector of `ε_(rev q) - ε_(rev p)`, where `h = |p - q|` is the height of the root
  (`TauCeti.reindex_graphPermA_root_typeAPairRoot`). Equivalently, the inversion sign of the
  reversal on every root of `A_r` is `(-1) ^ (h - 1)`
  (`TauCeti.inversionSign_graphPermA_typeAPairRoot`). These are the signs from which the cycle
  coefficients and monodromies of the reversal are computed.
* The comparison carries the fixed submodule of the pinned shell reversal, the integral fixed
  lattice, onto the trace-zero integer matrices fixed by `θ`
  (`TauCeti.map_typeAShellEquiv_fixedSubmodule_reindex_graphPermA`).

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8 and §7.9.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.
-/

public section

namespace TauCeti

open _root_.Matrix LieAlgebra.SpecialLinear Matrix.ShellLieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- **The pinned reversal of the type-`A` signed shell Lie algebra is the matrix graph
automorphism.** Under the signed matrix comparison `TauCeti.typeAShellEquiv` of the signed shell
Lie algebra of `CartanMatrix.A r` with `sl_(r+1)` over `ℤ`, the relabelling
`Matrix.ShellLieAlgebra.reindex` by the reversal `graphPermA r` of the chain is the pinned graph
automorphism `X ↦ -J Xᵀ J⁻¹` of `sl_(r+1)`. -/
@[simp]
theorem typeAShellEquiv_reindex_graphPermA (x : ShellLieAlgebra (CartanMatrix.A r)) :
    typeAShellEquiv r (reindex (graphPermA r) (reindex_cartanMatrix_A_graphPermA r) x) =
      typeASpecialLinearGraphAutomorphism r ℤ (typeAShellEquiv r x) := by
  have hdiag (i : Fin r) : CartanMatrix.A r i i = 2 := congrFun (CartanMatrix.A_diag r) i
  have hoff := CartanMatrix.A_apply_le_zero_of_ne (n := r)
  let := ShellLieAlgebra.lieRing (posDef_cartanMatrix_A r) fun i ↦ hdiag i ▸ even_two
  set ρ := reindex (graphPermA r) (reindex_cartanMatrix_A_graphPermA r)
  -- Both sides are Lie ring homomorphisms, so it suffices to compare them on the Chevalley
  -- generators `Eᵢ` and `Fᵢ`, which generate the shell algebra over `ℤ`.
  have hx : x ∈ LieSubalgebra.lieSpan ℤ (ShellLieAlgebra (CartanMatrix.A r))
      (Set.range (chevalleyE _ hdiag) ∪ Set.range (chevalleyF _ hdiag)) := by
    rw [lieSpan_chevalleyE_chevalleyF_eq_top (posDef_cartanMatrix_A r) hdiag hoff]
    exact LieSubalgebra.mem_top x
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hρ : ρ (chevalleyE _ hdiag i) = chevalleyE _ hdiag i.rev := by
        rw [chevalleyE_def, reindex_root_single _ _ i _ (single_mem_normTwoShell (hdiag _)),
          chevalleyE_def]
        exact congrArg (root _) (Subtype.ext (by rw [graphPermA_apply]))
      rw [hρ, typeAShellEquiv_chevalleyE, typeAShellEquiv_chevalleyE,
        typeASpecialLinearGraphAutomorphism_single_upper]
    · have hρ : ρ (chevalleyF _ hdiag i) = chevalleyF _ hdiag i.rev := by
        rw [chevalleyF_def, reindex_root_neg_single _ _ i _
            (neg_mem_normTwoShell.mpr (single_mem_normTwoShell (hdiag _))), chevalleyF_def]
        exact congrArg (root _) (Subtype.ext (by rw [graphPermA_apply]))
      rw [hρ, typeAShellEquiv_chevalleyF, typeAShellEquiv_chevalleyF,
        typeASpecialLinearGraphAutomorphism_single_lower]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_zsmul, hx]
  | lie x y _ _ hx hy =>
    rw [reindex_lie _ _ (CartanMatrix.A_isSymm r), typeAShellEquiv_lie, typeAShellEquiv_lie,
      LieEquiv.map_lie, hx, hy]

/-- **The pinned reversal on root vectors of type `A`.** The relabelling of the signed shell Lie
algebra of `CartanMatrix.A r` by the reversal of the chain sends the root vector of `ε_p - ε_q` to
`(-1) ^ (h - 1)` times the root vector of `ε_(rev q) - ε_(rev p)`, where `h = |p - q|` is the
height of the root. -/
theorem reindex_graphPermA_root_typeAPairRoot {p q : Fin (r + 1)} (hpq : p ≠ q) :
    reindex (graphPermA r) (reindex_cartanMatrix_A_graphPermA r)
        (root _ ⟨typeAPairRoot r p q, typeAPairRoot_mem_normTwoShell r hpq⟩) =
      (-1 : ℤ) ^ (Nat.dist p.val q.val - 1) •
        root _ ⟨typeAPairRoot r q.rev p.rev,
          typeAPairRoot_mem_normTwoShell r (Fin.rev_injective.ne hpq.symm)⟩ := by
  apply (typeAShellEquiv r).injective
  rw [typeAShellEquiv_reindex_graphPermA, typeAShellEquiv_root_typeAPairRoot r hpq,
    typeASpecialLinearGraphAutomorphism_signedRoot, map_zsmul, typeAShellEquiv_root_typeAPairRoot]

/-- **The inversion sign of the reversal of `A_r`** on the root `ε_p - ε_q` is `(-1) ^ (h - 1)`,
where `h = |p - q|` is the height of the root. -/
@[simp]
theorem inversionSign_graphPermA_typeAPairRoot {p q : Fin (r + 1)} (hpq : p ≠ q) :
    inversionSign (CartanMatrix.A r) (graphPermA r) (typeAPairRoot r p q) =
      (-1) ^ (Nat.dist p.val q.val - 1) := by
  have h := reindex_graphPermA_root_typeAPairRoot r hpq
  rw [reindex_root, normTwoShellCongr_graphPermA_typeAPairRoot r hpq, Units.smul_def] at h
  -- Read off the coefficient of the common root vector in the integral basis.
  have hc := congrArg (fun v ↦ (ShellLieAlgebra.basis _).repr v
    (.inr ⟨typeAPairRoot r q.rev p.rev,
      typeAPairRoot_mem_normTwoShell r (Fin.rev_injective.ne hpq.symm)⟩)) h
  simp only [← basis_inr, map_zsmul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, zsmul_eq_mul, mul_one, Int.cast_id] at hc
  exact Units.ext (by rw [hc, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one])

/-- **The integral fixed lattice of the reversal of `A_r`.** The signed matrix comparison carries
the submodule of the signed shell Lie algebra of `CartanMatrix.A r` fixed by the pinned reversal
onto the trace-zero integer matrices fixed by the graph automorphism `X ↦ -J Xᵀ J⁻¹`. -/
theorem map_typeAShellEquiv_fixedSubmodule_reindex_graphPermA :
    (reindex (graphPermA r) (reindex_cartanMatrix_A_graphPermA r)).toLinearMap.fixedSubmodule.map
        (typeAShellEquiv r).toLinearMap =
      (typeASpecialLinearGraphAutomorphism r ℤ).toLieHom.fixedSubalgebra.toSubmodule := by
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact (typeAShellEquiv r).map_fixedSubmodule
    (LinearMap.ext (typeAShellEquiv_reindex_graphPermA r))

end TauCeti
