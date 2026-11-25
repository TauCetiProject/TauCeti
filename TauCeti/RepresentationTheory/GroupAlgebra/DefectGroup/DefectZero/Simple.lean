/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Algebra
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero.Basic
public import TauCeti.RingTheory.Idempotents.Corner.Central
public import TauCeti.RingTheory.Semisimple.CentralIdempotent

/-!
# Block algebras of defect zero are simple

Let `e` be a block idempotent of `k[G]`, `k` a field of characteristic `p`, with defect group `1`.
Then the block algebra `e k[G]` is a simple ring, so by the Wedderburn–Artin theorem it is a
matrix algebra `M_n(D)` over a finite-dimensional division algebra `D` over `k`, and `M_n(k)` when
`k` is algebraically closed (Webb, Corollary 12.4.8, p. 242, with Theorem 9.6.1, p. 161).

The route: projecting `k[G]` onto the block algebra, `x ↦ e x`
(`IsIdempotentElem.compressAlgHom`), is a surjective algebra map, along which every module over
the block algebra is a `k[G]`-module on which `e` acts as the identity. Such modules are
semisimple (`TauCeti.IsBlockIdempotent.isSemisimpleModule_of_isDefectGroup_bot`), so the block
algebra is a semisimple ring. Since `e` is primitive in the centre of `k[G]`, the block algebra
has no central idempotents besides `0` and `1`
(`TauCeti.IsPrimitiveIdempotent.centralIdempotents_corner_subset`); a semisimple ring with no
other central idempotents is simple (`IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset`).

## Main results

* `TauCeti.IsBlockIdempotent.isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.isSimpleRing_blockAlgebra_of_isDefectGroup_bot`: a block of defect
  group `1` is a simple semisimple ring.
* `TauCeti.IsBlockIdempotent.exists_algEquiv_matrix_divisionRing_of_isDefectGroup_bot`,
  `TauCeti.IsBlockIdempotent.exists_algEquiv_matrix_of_isDefectGroup_bot`: it is `M_n(D)` for a
  division algebra `D`, and `M_n(k)` over an algebraically closed field.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, Theorem 9.6.1, p. 161, and
  Corollary 12.4.8, p. 242.
-/

public section

universe u v

namespace TauCeti

open MonoidAlgebra

namespace IsBlockIdempotent

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] {p : ℕ} [CharP k p]
  {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- **A block of defect zero is a semisimple ring.** If `1` is a defect group of a block idempotent
`e` of `k[G]`, `k` a field of characteristic `p`, then the block algebra `e k[G]` is semisimple:
its modules are `k[G]`-modules on which `e` acts as the identity, which are semisimple. -/
theorem isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) : IsSemisimpleRing hb.BlockAlgebra := by
  -- The projection `x ↦ e x` of `k[G]` onto the block algebra.
  let φ := hb.isIdempotentElem_val.compressAlgHom k (Set.mem_center_iff.mp b.property)
  have hφ : Function.Surjective φ := IsIdempotentElem.compressAlgHom_surjective _ _ _
  rcases CharP.char_is_prime_or_zero k p with hp | rfl
  swap
  · -- In characteristic zero `k[G]` is semisimple by Maschke's theorem.
    have := CharP.charP_to_charZero k
    have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
    exact φ.toRingHom.isSemisimpleRing_of_surjective hφ
  have := Fact.mk hp
  -- The block algebra as a `k[G]`-module along `φ`; by the definition of `Module.compHom`,
  -- `x • y = φ x * y`, which `hsmul` records.
  let _ : Module (MonoidAlgebra k G) hb.BlockAlgebra := Module.compHom _ φ.toRingHom
  have hsmul (x : MonoidAlgebra k G) (y : hb.BlockAlgebra) : x • y = φ x * y := rfl
  have : IsScalarTower k (MonoidAlgebra k G) hb.BlockAlgebra :=
    ⟨fun c x y ↦ by
      rw [hsmul, hsmul, map_smul]
      exact Subtype.ext (smul_mul_assoc c (φ x).val y.val)⟩
  have hφb : φ b = 1 := IsIdempotentElem.compressAlgHom_self _ _ _
  have := hb.isSemisimpleModule_of_isDefectGroup_bot (V := hb.BlockAlgebra) hD fun v ↦ by
    rw [hsmul, hφb, one_mul]
  have : RingHomSurjective φ.toRingHom := ⟨hφ⟩
  -- The identity of the block algebra, semilinear along `φ`: `x • y = φ x * y` is `hsmul`.
  let l : hb.BlockAlgebra →ₛₗ[φ.toRingHom] hb.BlockAlgebra :=
    { AddMonoidHom.id _ with map_smul' := hsmul }
  rw [IsSemisimpleRing, ← l.isSemisimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- **A block of defect zero is a simple ring.** If `1` is a defect group of a block idempotent
`e` of `k[G]`, `k` a field of characteristic `p`, then the block algebra `e k[G]` is simple. -/
theorem isSimpleRing_blockAlgebra_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) : IsSimpleRing hb.BlockAlgebra :=
  have := hb.isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset
    (IsPrimitiveIdempotent.centralIdempotents_corner_subset hb hb.isIdempotentElem_val)

/-- **A block of defect zero is a matrix algebra over a division algebra.** If `1` is a defect
group of a block idempotent `e` of `k[G]`, `k` a field of characteristic `p`, then the block
algebra `e k[G]` is isomorphic to `M_n(D)` for some `n > 0` and some finite-dimensional division
algebra `D` over `k`. -/
theorem exists_algEquiv_matrix_divisionRing_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type (max u v)) (_ : DivisionRing D) (_ : Algebra k D)
      (_ : Module.Finite k D), Nonempty (hb.BlockAlgebra ≃ₐ[k] Matrix (Fin n) (Fin n) D) :=
  have := hb.isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  have := hb.isSimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  have := Fintype.ofFinite G
  IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k hb.BlockAlgebra

/-- **A block of defect zero over an algebraically closed field is a matrix algebra.** If `1` is
a defect group of a block idempotent `e` of `k[G]`, `k` an algebraically closed field of
characteristic `p`, then the block algebra `e k[G]` is isomorphic to `M_n(k)` for some `n > 0`. -/
theorem exists_algEquiv_matrix_of_isDefectGroup_bot [IsAlgClosed k] (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (hb.BlockAlgebra ≃ₐ[k] Matrix (Fin n) (Fin n) k) :=
  have := hb.isSimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  have := Fintype.ofFinite G
  IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed k hb.BlockAlgebra

end IsBlockIdempotent

end TauCeti
