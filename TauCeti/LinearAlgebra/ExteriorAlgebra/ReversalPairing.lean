/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension
import TauCeti.LinearAlgebra.ExteriorAlgebra.End
import TauCeti.LinearAlgebra.SesquilinearForm.AdjointPair

/-!
# The reversal pairing on an exterior algebra

Given a linear functional `φ` on the exterior algebra `⋀ M`, the **reversal pairing** is the
bilinear form `⟨x, y⟩ = φ (reverse x * y)`. When `φ` is the top-degree coefficient for a basis of
`M`, this is the pairing `⟨s, t⟩ = [reverse s ∧ t]_top` that carries the invariant bilinear form of
the spin representation: on the Fock model `S = ⋀ W` of a polarized quadratic space, both exterior
multiplication by a vector and contraction by a functional are self-adjoint for it, so the
Clifford action is adjoint to reversal.

This file develops the pairing on the exterior algebra alone.

* Exterior multiplication by a vector is always self-adjoint
  (`ExteriorAlgebra.reversalPairing_ι_mul`), contraction by `d` is self-adjoint as soon as `φ`
  kills every contraction by `d` (`ExteriorAlgebra.reversalPairing_contractLeft`), and the grade
  involution is self-adjoint as soon as `φ` is invariant under it
  (`ExteriorAlgebra.reversalPairing_involute`).
* If `φ ∘ reverse = c • φ`, the pairing is `c`-symmetric
  (`ExteriorAlgebra.reversalPairing_swap`).
* For a finite free module, a surjective functional killing every contraction gives a
  nondegenerate pairing (`ExteriorAlgebra.reversalPairing_nondegenerate`): the operators
  having an adjoint form a subalgebra containing creation and contraction, hence every
  endomorphism.
* For a basis `b` indexed by a finite linear order, the top-degree coefficient
  `b.ExteriorAlgebra.coord Finset.univ` kills contractions, and reversal and the grade involution
  multiply it by `(-1) ^ (n.choose 2)` and `(-1) ^ n` in rank `n`
  (`Module.Basis.exteriorAlgebra_coord_univ_contractLeft`,
  `Module.Basis.exteriorAlgebra_coord_univ_reverse`,
  `Module.Basis.exteriorAlgebra_coord_univ_involute`, in
  `TauCeti/LinearAlgebra/ExteriorAlgebra/Contraction.lean`). The resulting pairing is alternating
  when `(-1) ^ (n.choose 2) = -1` and `n > 0`, in every characteristic
  (`ExteriorAlgebra.isAlt_reversalPairing_coord_univ`).
* In rank two, `⟨w₁, w₂⟩ = 1` and `⟨1, w₁ ∧ w₂⟩ = 1`
  (`ExteriorAlgebra.reversalPairing_coord_univ_ι_zero_ι_one`,
  `ExteriorAlgebra.reversalPairing_coord_univ_one_ι_zero_mul_ι_one`).

## References

* C. Chevalley, *The Algebraic Theory of Spinors* (1954), Chapter III.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

public section

open CliffordAlgebra Module
open TauCeti.ExteriorAlgebra (basis_pair creation_contraction_adjoin_eq_top)

namespace ExteriorAlgebra

universe u v w

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- **The reversal pairing** attached to a functional `φ` on the exterior algebra:
`⟨x, y⟩ = φ (reverse x * y)`. For the top-degree coefficient of a basis this is the pairing
`[reverse x ∧ y]_top`. -/
noncomputable def reversalPairing (φ : Module.Dual R (ExteriorAlgebra R M)) :
    LinearMap.BilinForm R (ExteriorAlgebra R M) :=
  ((LinearMap.mul R (ExteriorAlgebra R M)).compl₁₂
    (reverse (Q := (0 : QuadraticForm R M))) LinearMap.id).compr₂ φ

variable (φ : Module.Dual R (ExteriorAlgebra R M))

@[simp]
theorem reversalPairing_apply (x y : ExteriorAlgebra R M) :
    reversalPairing φ x y = φ (reverse x * y) :=
  -- `(rfl)`, not `rfl`: the body of `reversalPairing` is not `@[expose]`d.
  (rfl)

/-- Exterior multiplication by a vector is self-adjoint for every reversal pairing. -/
theorem reversalPairing_ι_mul (m : M) (x y : ExteriorAlgebra R M) :
    reversalPairing φ (ExteriorAlgebra.ι R m * x) y =
      reversalPairing φ x (ExteriorAlgebra.ι R m * y) := by
  simp only [reversalPairing_apply, reverse.map_mul, reverse_ι, mul_assoc]

/-- Contraction by a functional `d` is self-adjoint for the reversal pairing of a functional that
kills every contraction by `d`. -/
theorem reversalPairing_contractLeft
    (d : Module.Dual R M) (hφ : ∀ x : ExteriorAlgebra R M, φ (contractLeft d x) = 0)
    (x y : ExteriorAlgebra R M) :
    reversalPairing φ (contractLeft d x) y = reversalPairing φ x (contractLeft d y) := by
  induction x using CliffordAlgebra.left_induction generalizing y with
  | algebraMap r => simp [← Algebra.smul_def, hφ]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | ι_mul x m hx =>
    have hι := reversalPairing_ι_mul φ m
    calc reversalPairing φ (contractLeft d (ι _ m * x)) y
        = d m * reversalPairing φ x y - reversalPairing φ x (contractLeft d (ι _ m * y)) := by
          rw [contractLeft_ι_mul, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
            smul_eq_mul, hι, hx]
      _ = reversalPairing φ (ι _ m * x) (contractLeft d y) := by
          rw [contractLeft_ι_mul, map_sub, map_smul, smul_eq_mul, hι]
          ring

/-- The grade involution is self-adjoint for the reversal pairing of an involution-invariant
functional. -/
theorem reversalPairing_involute (hφ : ∀ x : ExteriorAlgebra R M, φ (involute x) = φ x)
    (x y : ExteriorAlgebra R M) :
    reversalPairing φ (involute x) y = reversalPairing φ x (involute y) := by
  rw [reversalPairing_apply, reversalPairing_apply, ← hφ (reverse x * involute y),
    map_mul involute, involute_involute, reverse_involute_commute.eq]

/-- If reversal multiplies `φ` by `c`, the reversal pairing is `c`-symmetric. -/
theorem reversalPairing_swap {c : R} (hφ : ∀ x : ExteriorAlgebra R M, φ (reverse x) = c * φ x)
    (x y : ExteriorAlgebra R M) :
    reversalPairing φ y x = c * reversalPairing φ x y := by
  rw [reversalPairing_apply, reversalPairing_apply, ← hφ, reverse.map_mul, reverse_reverse]

/-- **The reversal pairing is nondegenerate** on the exterior algebra of a finite free module, for
a surjective functional killing every contraction. -/
theorem reversalPairing_nondegenerate [Module.Free R M] [Module.Finite R M]
    (hφ : ∀ (d : Module.Dual R M) (x : ExteriorAlgebra R M), φ (contractLeft d x) = 0)
    (hφ₁ : Function.Surjective φ) :
    (reversalPairing φ).Nondegenerate := by
  -- Exterior multiplications by vectors and contractions are self-adjoint and generate every
  -- endomorphism, so every endomorphism has an adjoint, for the pairing and for its flip. For
  -- `T = f(·) • 1` pairing against a preimage of `1` then detects the value of a functional `f`.
  have hι (m : M) : LinearMap.IsAdjointPair (reversalPairing φ) (reversalPairing φ)
      (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)) :=
    reversalPairing_ι_mul φ m
  have hd (d : Module.Dual R M) : LinearMap.IsAdjointPair (reversalPairing φ) (reversalPairing φ)
      (contractLeft d) (contractLeft d) :=
    reversalPairing_contractLeft φ d (hφ d)
  have htop (f : Module.Dual R (ExteriorAlgebra R M)) :
      LinearMap.smulRight f (1 : ExteriorAlgebra R M) ∈ Algebra.adjoin R
        (Set.range (fun m : M ↦ (LinearMap.mulLeft R (ExteriorAlgebra.ι R m) :
          Module.End R (ExteriorAlgebra R M))) ∪
        Set.range (fun d : Module.Dual R M ↦ (contractLeft d :
          Module.End R (ExteriorAlgebra R M)))) := by
    rw [creation_contraction_adjoin_eq_top]
    exact Algebra.mem_top
  obtain ⟨t, ht⟩ := hφ₁ 1
  constructor
  · intro s hs
    refine (Module.forall_dual_apply_eq_zero_iff R s).1 fun f ↦ ?_
    obtain ⟨T, hT⟩ := LinearMap.exists_isAdjointPair_of_mem_adjoin (by
      rintro _ (⟨m, rfl⟩ | ⟨d, rfl⟩)
      exacts [⟨_, hι m⟩, ⟨_, hd d⟩]) (htop f)
    simpa [hs, ht] using hT s t
  · intro s hs
    refine (Module.forall_dual_apply_eq_zero_iff R s).1 fun f ↦ ?_
    obtain ⟨T, hT⟩ := LinearMap.exists_isAdjointPair_of_mem_adjoin (by
      rintro _ (⟨m, rfl⟩ | ⟨d, rfl⟩)
      exacts [⟨_, (hι m).flip⟩, ⟨_, (hd d).flip⟩]) (htop f)
    simpa [hs, ht] using hT s (reverse t)

/-! ### The top-degree coefficient of a basis -/

section Basis

variable {I : Type w} [LinearOrder I] (b : Module.Basis I R M)

variable [Fintype I]

/-- **The top-degree reversal pairing is alternating** in rank `n > 0` whenever reversal acts on
the top degree by `-1`, in every characteristic: it is skew, and it vanishes on the diagonal of the
exterior basis. -/
theorem isAlt_reversalPairing_coord_univ [Nonempty I]
    (h : (-1 : R) ^ (Fintype.card I).choose 2 = -1) :
    (reversalPairing (b.ExteriorAlgebra.coord Finset.univ)).IsAlt := by
  classical
  set β := reversalPairing (b.ExteriorAlgebra.coord Finset.univ)
  have hskew (x y : ExteriorAlgebra R M) : β y x = -β x y := by
    rw [reversalPairing_swap _ (c := -1) fun z ↦ by
      rw [b.exteriorAlgebra_coord_univ_reverse, h], neg_one_mul]
  have hdiag (s : Finset I) : β (b.ExteriorAlgebra s) (b.ExteriorAlgebra s) = 0 := by
    rw [reversalPairing_apply, reverse_basis, smul_mul_assoc, map_smul]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · have h1 : b.ExteriorAlgebra ∅ = 1 := by simp [b.exteriorAlgebra_eq_prod_map_sort]
      rw [h1, one_mul, ← h1, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
      simp [Finset.univ_nonempty.ne_empty.symm]
    · rw [basis_mul_of_not_disjoint b (⟨s, rfl⟩ : Set.powersetCard I s.card)
        ⟨s, rfl⟩ (by simpa using hs.ne_empty), map_zero, smul_zero]
  -- Expand in the exterior basis: `x ↦ β x x` is additive, since `β` is skew, and vanishes on
  -- multiples of basis vectors.
  intro x
  rw [← b.ExteriorAlgebra.sum_repr x]
  refine Finset.sum_induction _ (fun z ↦ β z z = 0) (fun y z hy hz ↦ ?_) (by simp)
    fun s _ ↦ ?_
  · rw [LinearMap.map_add₂, map_add, map_add, hy, hz, hskew z y]
    ring
  · rw [LinearMap.map_smul₂, map_smul, hdiag, smul_zero, smul_zero]

/-- In rank two the top-degree reversal pairing has `⟨w₁, w₂⟩ = 1`. -/
theorem reversalPairing_coord_univ_ι_zero_ι_one (b : Module.Basis (Fin 2) R M) :
    reversalPairing (b.ExteriorAlgebra.coord Finset.univ)
      (ExteriorAlgebra.ι R (b 0)) (ExteriorAlgebra.ι R (b 1)) = 1 := by
  rw [reversalPairing_apply, reverse_ι, ← basis_pair b Fin.zero_lt_one, ← Finset.univ_fin2]
  simp [Module.Basis.coord_apply]

/-- In rank two the top-degree reversal pairing has `⟨1, w₁ ∧ w₂⟩ = 1`. -/
theorem reversalPairing_coord_univ_one_ι_zero_mul_ι_one (b : Module.Basis (Fin 2) R M) :
    reversalPairing (b.ExteriorAlgebra.coord Finset.univ)
      1 (ExteriorAlgebra.ι R (b 0) * ExteriorAlgebra.ι R (b 1)) = 1 := by
  rw [reversalPairing_apply, reverse.map_one, one_mul, ← basis_pair b Fin.zero_lt_one,
    ← Finset.univ_fin2]
  simp [Module.Basis.coord_apply]

end Basis

end ExteriorAlgebra
