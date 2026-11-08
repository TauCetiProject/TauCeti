/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Decomposition
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Data.Fin.Rev
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.Algebra.Lie.Submodule.Decomposition
import TauCeti.LinearAlgebra.Eigenspace.Anticommute

/-!
# Symmetry of the weight multiplicities of an `sl₂`-module

Let `(h, e, f)` be an `sl₂` triple acting on a finite-dimensional module over a field of
characteristic zero. This file proves that the `μ`- and `-μ`-eigenspaces of the Cartan element `h`
have the same dimension. Characteristic zero is essential: the argument runs along the integer
ladders of the irreducible summands. The statement is made for an arbitrary triple in an arbitrary
ambient Lie algebra; only its generated subalgebra acts in the argument.

The result is the rank-one symmetry needed for Weyl invariance of weight multiplicities. For a root
`α`, restriction to its `sl₂` triple identifies the reflection of a weight `λ` with the opposite
weight on the corresponding `α`-string. Applying the theorem below to every such string gives the
direct rank-one proof required by Layer 2 of the highest-weight roadmap, independently of Weyl's
complete reducibility theorem.

The construction uses `TauCeti.exists_isInternal_isIrreducible` to decompose the module under the
generated `sl₂`. On each irreducible summand,
`TauCeti.basisOfHasPrimitiveVectorWith` is the ladder basis of weights
`n, n - 2, …, -n`. Mathlib's `DirectSum.IsInternal.collectedBasis` joins these into a basis of the
ambient module. Reversing every ladder gives a linear involution that anticommutes with `h`, hence
restricts to an equivalence between the two eigenspaces. That construction needs an algebraically
closed field; over a general field of characteristic zero the result follows by base change to the
algebraic closure, which leaves both eigenspace dimensions unchanged.

## Main result

* `TauCeti.finrank_eigenspace_toEnd_neg`: over a field of characteristic zero, the Cartan
  eigenspaces at `μ` and `-μ` have equal dimension.
* `IsSl2Triple.exists_int_and_toEnd_apply_eq_neg_smul`: on a finite-dimensional Lie submodule over
  the triple, an eigenvalue of `h` is an integer and its negative is an eigenvalue too.

## References

This is the rank-one input to the "Weyl-invariance of multiplicities, directly from `sl₂`" target
in Layer 2 of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

See J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §13.2.
-/

public section

namespace TauCeti

open LieModule Module
open scoped TensorProduct

private theorem finrank_ker_baseChange {K A V : Type*} [Field K] [Field A] [Algebra K A]
    [AddCommGroup V] [Module K V] (g : V →ₗ[K] V) :
    finrank A (LinearMap.ker (g.baseChange A)) = finrank K (LinearMap.ker g) := by
  calc finrank A (LinearMap.ker (g.baseChange A))
      = finrank A (A ⊗[K] LinearMap.ker g) := (LinearMap.tensorKerEquiv A A g).finrank_eq.symm
    _ = finrank K (LinearMap.ker g) := Module.finrank_baseChange

section Generated

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
variable {h e f : L}

/-- For a triple which generates the ambient Lie algebra, reversing every irreducible ladder
identifies the Cartan eigenspaces of opposite weights. This is kept private because the public
statement below applies to an arbitrary triple by restricting to its generated subalgebra. -/
private theorem nonempty_linearEquiv_eigenspace_neg_of_eq_top (t : IsSl2Triple h e f)
    (htop : t.toLieSubalgebra K = ⊤) (μ : K) :
    Nonempty
      ((toEnd K L M h).eigenspace μ ≃ₗ[K] (toEnd K L M h).eigenspace (-μ)) := by
  classical
  have _i : ComplementedLattice (LieSubmodule K L M) :=
    ⟨exists_isCompl_of_toLieSubalgebra_eq_top htop⟩
  obtain ⟨k, N, hint, hirr⟩ := exists_isInternal_isIrreducible K L M
  have hprimitive : ∀ i, ∃ (m : N i) (n : ℕ), t.HasPrimitiveVectorWith m (n : K) := by
    intro i
    let _ : LieModule.IsIrreducible K L (N i) := hirr i
    let _ : Nontrivial (N i) := LieModule.nontrivial_of_isIrreducible K L (N i)
    exact exists_hasPrimitiveVectorWith (K := K) (N i) t
  choose m n P using hprimitive
  let _ (i : Fin k) :
      LieModule.IsIrreducible K (t.toLieSubalgebra K) (N i) := by
    let _ : LieModule.IsIrreducible K L (N i) := hirr i
    exact (isIrreducible_iff_of_eq_top (M := N i) htop).2 inferInstance
  let b (i : Fin k) : Basis (Fin (n i + 1)) K (N i) := basisOfHasPrimitiveVectorWith (P i)
  let B : Basis (Σ i, Fin (n i + 1)) K M := hint.collectedBasis b
  let σ : Equiv.Perm (Σ i, Fin (n i + 1)) := Equiv.Perm.sigmaCongrRight fun _ ↦ Fin.revPerm
  let r : M ≃ₗ[K] M := B.equiv B σ
  have hweight (i : Fin k) (j : Fin (n i + 1)) :
      ⁅h, B ⟨i, j⟩⁆ = ((n i : K) - 2 * (j : ℕ)) • B ⟨i, j⟩ := by
    have hj := lie_h_basisOfHasPrimitiveVectorWith (P i) j
    simpa only [B, DirectSum.IsInternal.collectedBasis_coe, b, LieSubmodule.coe_bracket,
      LieSubmodule.coe_smul] using congrArg Subtype.val hj
  have hweight_rev (i : Fin k) (j : Fin (n i + 1)) :
      ((n i : K) - 2 * (j.rev : ℕ)) = -((n i : K) - 2 * (j : ℕ)) := by
    have hn : (n i : K) = (j : ℕ) + (j.rev : ℕ) := by
      exact_mod_cast j.add_rev_cast.symm
    rw [hn]
    ring
  have hr_basis (i : Fin k) (j : Fin (n i + 1)) :
      r (B ⟨i, j⟩) = B ⟨i, j.rev⟩ := by
    exact Basis.equiv_apply B ⟨i, j⟩ B σ
  have hanti : toEnd K L M h * (r : M →ₗ[K] M) + (r : M →ₗ[K] M) * toEnd K L M h = 0 := by
    apply B.ext
    rintro ⟨i, j⟩
    simp only [LinearMap.add_apply, mul_apply_eq_comp, LinearMap.zero_apply, LinearEquiv.coe_coe,
      toEnd_apply_apply, hr_basis, hweight, map_smul, hweight_rev, neg_smul, neg_add_cancel]
  exact ⟨Module.End.genEigenspaceEquivOfAnticommute r hanti μ 1⟩

end Generated

section Arbitrary

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
variable {h e f : L}

/-- **The weight multiplicities of a finite-dimensional `sl₂`-module are symmetric**, over an
algebraically closed field of characteristic zero. For the Cartan element `h` of any `sl₂` triple,
the eigenspaces of weights `μ` and `-μ` have the same dimension.

Only the Lie subalgebra generated by the triple is used. Thus the result applies directly to the
triple attached to a root inside a larger semisimple Lie algebra, which is the rank-one input for
Weyl invariance of the ambient module's weight multiplicities.

This is the algebraically closed case of `TauCeti.finrank_eigenspace_toEnd_neg`, which removes that
hypothesis by base change. -/
private theorem finrank_eigenspace_toEnd_neg_of_isAlgClosed (t : IsSl2Triple h e f) (μ : K) :
    finrank K ((toEnd K L M h).eigenspace μ) =
      finrank K ((toEnd K L M h).eigenspace (-μ)) := by
  obtain ⟨φ⟩ := nonempty_linearEquiv_eigenspace_neg_of_eq_top (M := M)
    t.isSl2Triple_restrict
    t.restrict_toLieSubalgebra_eq_top μ
  rw [LieSubalgebra.toEnd_mk] at φ
  exact φ.finrank_eq

end Arbitrary

section Descent

variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]
variable {h e f : L}

/-- **The weight multiplicities of a finite-dimensional `sl₂`-module are symmetric**, over a field
of characteristic zero. For the Cartan element `h` of any `sl₂` triple, the eigenspaces of weights
`μ` and `-μ` have the same dimension.

Only the Lie subalgebra generated by the triple is used. Thus the result applies directly to the
triple attached to a root inside a larger semisimple Lie algebra, which is the rank-one input for
Weyl invariance of the ambient module's weight multiplicities. -/
theorem finrank_eigenspace_toEnd_neg (t : IsSl2Triple h e f) (μ : K) :
    finrank K ((toEnd K L M h).eigenspace μ) =
      finrank K ((toEnd K L M h).eigenspace (-μ)) := by
  let A := AlgebraicClosure K
  let tA : IsSl2Triple ((1 : A) ⊗ₜ[K] h) ((1 : A) ⊗ₜ[K] e) ((1 : A) ⊗ₜ[K] f) := {
    h_ne_zero := fun hzero ↦ t.h_ne_zero (by
      apply Module.Flat.tensorProduct_mk_injective K L A
      simpa using hzero)
    lie_e_f := by simp [t.lie_e_f]
    lie_h_e_nsmul := by simp [t.lie_h_e_nsmul]
    lie_h_f_nsmul := by
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, t.lie_h_f_nsmul,
        TensorProduct.tmul_neg, TensorProduct.tmul_smul] }
  have hA := finrank_eigenspace_toEnd_neg_of_isAlgClosed (M := A ⊗[K] M) tA
    (algebraMap K A μ)
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def, LieModule.toEnd_baseChange] at hA
  have hbaseChange (a : K) :
      (toEnd K L M h - a • 1).baseChange A =
        (toEnd K L M h).baseChange A - algebraMap K A a • 1 := by
    simp
  have hbaseChange_neg :
      (toEnd K L M h - -μ • 1).baseChange A =
        (toEnd K L M h).baseChange A - -(algebraMap K A μ) • 1 := by
    simpa only [map_neg] using hbaseChange (-μ)
  rw [← hbaseChange μ, ← hbaseChange_neg] at hA
  rw [Module.End.eigenspace_def, Module.End.eigenspace_def]
  rw [← finrank_ker_baseChange (A := A) (toEnd K L M h - μ • 1),
    ← finrank_ker_baseChange (A := A) (toEnd K L M h - -μ • 1)]
  exact hA

end Descent

end TauCeti

namespace IsSl2Triple

open LieModule Module

variable {K : Type*} [Field K] [CharZero K]
variable {L : Type*} [LieRing L] [LieAlgebra K L] {H : LieSubalgebra K L}
variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
variable {h e f : L}

/-- **An eigenvalue of the Cartan element on a Lie submodule over the triple is an integer, and its
negative is an eigenvalue too.** Let `𝒲` be a finite-dimensional Lie submodule of `M` over the
subalgebra generated by an `sl₂` triple whose Cartan element `h` is an element `x` of a Lie
subalgebra `H`. If `x` has an eigenvector `v ∈ 𝒲` of eigenvalue `n`, then `n` is an integer and
`x` has an eigenvector in `𝒲` of eigenvalue `-n`. -/
theorem exists_int_and_toEnd_apply_eq_neg_smul (t : IsSl2Triple h e f) {x : H}
    (hh : h = (x : L)) (𝒲 : LieSubmodule K (t.toLieSubalgebra K) M) [FiniteDimensional K 𝒲]
    {n : K} {v : M} (hv : v ∈ 𝒲) (hv0 : v ≠ 0) (hvA : toEnd K H M x v = n • v) :
    ∃ m : ℤ, n = (m : K) ∧ ∃ u ∈ 𝒲, u ≠ 0 ∧ toEnd K H M x u = (-n) • u := by
  have hA : ∀ v ∈ 𝒲.toSubmodule, toEnd K H M x v ∈ 𝒲.toSubmodule := fun v hv ↦ by
    have := 𝒲.lie_mem (x := ⟨h, t.h_mem_toLieSubalgebra⟩) hv
    simpa [hh] using this
  set B : Module.End K 𝒲 := toEnd K (t.toLieSubalgebra K) 𝒲 ⟨h, t.h_mem_toLieSubalgebra⟩
  have hBA : B = (toEnd K H M x).restrict hA := t.toEnd_h_eq_restrict 𝒲 hh hA
  have hvB : (⟨v, hv⟩ : 𝒲) ∈ B.eigenspace n :=
    Module.End.mem_eigenspace_iff.2 (Subtype.ext (by rw [hBA]; exact hvA))
  have hnB : B.eigenspace n ≠ ⊥ := fun hbot ↦ hv0 (by
    simpa [Subtype.ext_iff] using (Submodule.eq_bot_iff _).1 hbot _ hvB)
  obtain ⟨m, hm⟩ := TauCeti.exists_int_of_hasEigenvalue (M := 𝒲) t.isSl2Triple_restrict
    (Module.End.hasEigenvalue_iff.2 hnB)
  have hsym := TauCeti.finrank_eigenspace_toEnd_neg (L := ↥(t.toLieSubalgebra K)) (M := 𝒲)
    t.isSl2Triple_restrict n
  have hnegB : B.eigenspace (-n) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hsym
    exact hnB (Submodule.finrank_eq_zero.1 hsym)
  obtain ⟨u, humem, hu0⟩ := (Submodule.ne_bot_iff _).1 hnegB
  refine ⟨m, hm, u, u.2, fun h0 ↦ hu0 (Subtype.ext h0), ?_⟩
  have h2 := congrArg Subtype.val (Module.End.mem_eigenspace_iff.1 humem)
  rw [hBA] at h2
  exact h2

end IsSl2Triple
