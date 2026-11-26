/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Basic
public import TauCeti.LinearAlgebra.RootSystem.Alcove
import TauCeti.LinearAlgebra.LinearIndependent.Prod

/-!
# A realization of the affine Cartan matrix

Let `b` be a base of a finite crystallographic root pairing `P` over a field `R` of characteristic
zero. This file realizes the affine Cartan matrix `RootPairing.Base.affineCartanMatrix` on
`H = M × R × R`, in the sense of `TauCeti.CartanRealization`. The coroot at a node `k` of the
affine Dynkin diagram is the affine simple root `aₖ = αₖ + aₖ(0)`
(`RootPairing.Base.affineSimpleRoot`), homogenized as `(αₖ, aₖ(0), 0)`, and the root at `l` is the
coroot `αₗ^∨` (with `α₀^∨ = -θ^∨`), as the functional `(m, s, t) ↦ ⟨m, αₗ^∨⟩ + aₗ(0) t`. The two
extra coordinates make both families linearly independent, although the vectors `αₖ` and the
coroots `αₗ^∨` are not.

This realization is the one through which the affine Weyl group is identified with the Weyl group
of a realization, and hence shown to be a Coxeter group
(`RootPairing.Base.affineWeylCoxeterSystem`).

## Main definitions

* `RootPairing.Base.affineRealization`: a realization of the affine Cartan matrix on `M × R × R`.

## References

* V. G. Kac, *Infinite-dimensional Lie algebras*, third edition, §1.1.
-/

public section

open Module TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-! ### A realization of the affine Cartan matrix -/

section Realization

variable [Field R] [Module R M] [Module R N]

variable [CharZero R] {P : RootPairing ι R M N} [P.IsCrystallographic] [Finite ι] [Nonempty ι]
  (b : P.Base)

/-- **The affine realization of a base.** A realization of the affine Cartan matrix
`RootPairing.Base.affineCartanMatrix` on `H = M × R × R`. In the convention of
`TauCeti.CartanRealization`, where the matrix entry `A k l` is the value of the root at `l` on the
coroot at `k`, the coroot at a node `k` is the affine simple root `aₖ = αₖ + aₖ(0)`, homogenized
as `(αₖ, aₖ(0), 0)`, and the root at `l` is the coroot `αₗ^∨` (with `α₀^∨ = -θ^∨`), as the
functional `(m, s, t) ↦ ⟨m, αₗ^∨⟩ + aₗ(0) t`. The last coordinate makes the roots linearly
independent although the coroots `αₗ^∨` are not, and the middle one does the same for the
coroots. -/
noncomputable def affineRealization :
    CartanRealization (b.affineCartanMatrix.map (Int.cast : ℤ → R)) (M × R × R) where
  coroot k := (P.root (b.affineSimpleRootIndex k), b.affineSimpleRoot k 0, 0)
  root l := (P.coroot' (b.affineSimpleRootIndex l)).coprod
    (b.affineSimpleRoot l 0 • LinearMap.snd R R R)
  coroot_linearIndependent := by
    -- Forgetting the last coordinate, the simple roots `(αᵢ, 0)` are independent and the affine
    -- node adds `(-θ, 1)`. `LinearIndepOn R P.root b.support` is the independence of the simple
    -- roots indexed by the subtype of `b.support`.
    refine LinearIndependent.of_comp
      ((LinearMap.id : M →ₗ[R] M).prodMap (LinearMap.fst R R R)) ?_
    exact LinearIndependent.option_prod (J := b.support) (e := fun i ↦ P.root i)
      b.linearIndepOn_root (fun i ↦ by simp) (by intro c d h; simpa using h)
  root_linearIndependent := by
    -- Restricting to `M` and evaluating at `(0, 0, 1)`, the simple coroots `(αᵢ^∨, 0)` are
    -- independent, the pairing being perfect, and the affine node adds `(-θ^∨, 1)`.
    refine LinearIndependent.of_comp
      ((LinearMap.lcomp R R (LinearMap.inl R M (R × R))).prod
        (Dual.eval R (M × R × R) (0, 0, 1))) ?_
    refine LinearIndependent.option_prod (J := b.support) (e := fun i ↦ P.coroot' i)
      ((b.linearIndepOn_coroot).map' _
        (LinearMap.ker_eq_bot.mpr (LinearMap.IsPerfPair.bijective_right P.toLinearMap).injective))
      (fun i ↦ ?_) (by intro c d h; simpa using h)
    ext m <;> simp
  root_coroot k l := by
    simp [b.affineCartanMatrix_apply, ← P.algebraMap_pairingIn ℤ, algebraMap_int_eq]

@[simp]
lemma affineRealization_coroot (k : Option b.support) :
    b.affineRealization.coroot k =
      (P.root (b.affineSimpleRootIndex k), b.affineSimpleRoot k 0, 0) :=
  (rfl)

@[simp]
lemma affineRealization_root_apply (l : Option b.support) (v : M × R × R) :
    b.affineRealization.root l v =
      P.toLinearMap v.1 (P.coroot (b.affineSimpleRootIndex l)) + b.affineSimpleRoot l 0 * v.2.2 :=
  (rfl)

end Realization

end RootPairing.Base
