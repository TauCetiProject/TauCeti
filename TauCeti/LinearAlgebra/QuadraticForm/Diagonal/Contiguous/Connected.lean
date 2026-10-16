/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Contiguous.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Connectivity of contiguous orthogonal bases

Any two orthogonal bases of a regular quadratic space of dimension at least three are joined
by a chain of contiguous orthogonal bases. In fact, at most three moves suffice: find an
anisotropic vector perpendicular both to a vector of the first basis and to a vector of the
second, then extend the two orthogonal pairs to bases.

Together with `Module.Basis.diagonalChain_tail_of_isOrtho_of_apply_eq`, this connects Serre's
contiguous-basis description of diagonal invariants with diagonal chains of unit coefficients.
Contiguity means an actual shared vector, not merely equal values of the quadratic form.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter IV, §1.3, Theorem 2; §2.1, Theorem 5.
-/

public section

namespace Module.Basis

open QuadraticMap

variable {K V : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- Two orthogonal bases of a regular quadratic space of dimension at least three can be
joined by three contiguous moves through orthogonal bases. -/
theorem exists_isOrtho_isContiguous {n : ℕ} (b b' : Basis (Fin (n + 3)) K V)
    (hQ : Q.Nondegenerate) (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b') :
    ∃ c c' : Basis (Fin (n + 3)) K V,
      Q.associated.IsOrthoᵢ c ∧ Q.associated.IsOrthoᵢ c' ∧
        b.IsContiguous c ∧ c.IsContiguous c' ∧ c'.IsContiguous b' := by
  let _ : FiniteDimensional K V := Module.Finite.of_basis b
  have hdim : Module.finrank K V = n + 3 := by
    simpa using Module.finrank_eq_card_basis b
  have hB := nondegenerate_associated_iff.mpr hQ
  have hsym : LinearMap.BilinForm.IsSymm Q.associated :=
    LinearMap.BilinForm.isSymm_iff.mpr (QuadraticForm.associated_isSymm K Q)
  let e : Fin 3 → Fin (n + 3) := Fin.castLE (by omega)
  have he : Function.Injective e := Fin.castLE_injective _
  have hv : Q.associated.IsOrthoᵢ (fun i : Fin 3 ↦ b' (e i)) :=
    fun _ _ hij ↦ hb' (he.ne hij)
  have hvv (i : Fin 3) : Q.associated (b' (e i)) (b' (e i)) ≠ 0 :=
    hb'.not_isOrtho_basis_self_of_separatingLeft hB.1 (e i)
  obtain ⟨z, hz, hxz, k, hkz⟩ :=
    LinearMap.BilinForm.exists_apply_self_ne_zero_isOrtho_pair Q.associated
      (fun i : Fin 3 ↦ b' (e i)) hv hvv (b 0)
  obtain ⟨c, hc, hc0, hc1⟩ := hsym.exists_orthogonal_basis_apply_zero_one_eq
    (hb.not_isOrtho_basis_self_of_separatingLeft hB.1 0) hz hxz hdim
  obtain ⟨c', hc', hc'0, hc'1⟩ := hsym.exists_orthogonal_basis_apply_zero_one_eq
    hz (hvv k) (hsym.isRefl.eq_zero hkz) hdim
  exact ⟨c, c', hc, hc', (isContiguous_iff _ _).mpr ⟨0, 0, hc0.symm⟩,
    (isContiguous_iff _ _).mpr ⟨1, 0, hc1.trans hc'0.symm⟩,
    (isContiguous_iff _ _).mpr ⟨1, e k, hc'1⟩⟩

/-- **Serre's connectivity theorem for orthogonal bases.** Orthogonal bases of a regular
quadratic space in dimension at least three are joined by a finite chain whose every step
consists of two orthogonal bases with a vector in common. -/
theorem reflTransGen_isOrtho_isContiguous {n : ℕ} (b b' : Basis (Fin (n + 3)) K V)
    (hQ : Q.Nondegenerate) (hb : Q.associated.IsOrthoᵢ b) (hb' : Q.associated.IsOrthoᵢ b') :
    Relation.ReflTransGen
      (fun c c' : Basis (Fin (n + 3)) K V ↦
        Q.associated.IsOrthoᵢ c ∧ Q.associated.IsOrthoᵢ c' ∧ c.IsContiguous c') b b' := by
  obtain ⟨c, c', hc, hc', hbc, hcc', hc'b'⟩ := b.exists_isOrtho_isContiguous b' hQ hb hb'
  exact (Relation.ReflTransGen.single ⟨hb, hc, hbc⟩).trans
    ((Relation.ReflTransGen.single ⟨hc, hc', hcc'⟩).trans
      (Relation.ReflTransGen.single ⟨hc', hb', hc'b'⟩))

end Module.Basis
