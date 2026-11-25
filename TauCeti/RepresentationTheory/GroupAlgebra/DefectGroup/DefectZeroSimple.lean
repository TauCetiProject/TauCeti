/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Algebra
public import TauCeti.RepresentationTheory.GroupAlgebra.DefectGroup.DefectZero
public import TauCeti.RingTheory.Semisimple.CentralIdempotent

/-!
# Block algebras of defect zero are simple

Let `e` be a block idempotent of `k[G]`, `k` a field of characteristic `p`, with defect group `1`.
Then the block algebra `e k[G]` is a simple ring, so by the Wedderburn–Artin theorem it is a
matrix algebra `M_n(D)` over a finite-dimensional division algebra `D` over `k`, and `M_n(k)` when
`k` is algebraically closed (Webb, Corollary 12.4.8, p. 242, with Theorem 9.6.1, p. 161).

The route: projecting `k[G]` onto the block algebra, `x ↦ e x`
(`TauCeti.IsBlockIdempotent.toBlockAlgebra`), is a surjective algebra map, along which every
module over the block algebra is a `k[G]`-module on which `e` acts as the identity. Such modules
are semisimple (`TauCeti.IsBlockIdempotent.isSemisimpleModule_of_isDefectGroup_bot`), so the block
algebra is a semisimple ring. Its central idempotents are central idempotents of `k[G]` below
`e`, so since `e` is primitive in the centre they are `0` and `1`
(`TauCeti.IsBlockIdempotent.centralIdempotents_blockAlgebra_subset`); a semisimple ring with no
other central idempotents is simple
(`TauCeti.IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset`).

## Main definitions

* `TauCeti.IsBlockIdempotent.toBlockAlgebra`: the projection `x ↦ e x` onto the block algebra.

## Main results

* `TauCeti.IsBlockIdempotent.centralIdempotents_blockAlgebra_subset`: the block algebra has no
  central idempotents besides `0` and `1`.
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

section Ring

variable {R G : Type*} [CommRing R] [Monoid G] {b : Subalgebra.center R (MonoidAlgebra R G)}

/-- The projection `x ↦ e x` of `R[G]` onto the block algebra `e R[G]` of a block idempotent `e`,
an algebra map since `e` is a central idempotent. -/
noncomputable def toBlockAlgebra (hb : IsBlockIdempotent b) :
    MonoidAlgebra R G →ₐ[R] hb.BlockAlgebra where
  toFun x := hb.isIdempotentElem_val.compress x
  map_one' := Subtype.ext <| by
    rw [hb.isIdempotentElem_val.val_compress_of_commute (Commute.one_right _), mul_one]; rfl
  map_mul' x y := Subtype.ext <| by
    have hc (z : MonoidAlgebra R G) : z * b = b * z := Subalgebra.mem_center_iff.1 b.property z
    have he := hb.isIdempotentElem_val
    rw [IsIdempotentElem.Corner.val_mul, he.val_compress_of_commute (hc x).symm,
      he.val_compress_of_commute (hc y).symm, he.val_compress_of_commute (hc (x * y)).symm]
    calc (b : MonoidAlgebra R G) * (x * y) = b * b * (x * y) := by rw [he.eq]
      _ = b * (b * x) * y := by simp only [mul_assoc]
      _ = b * (x * b) * y := by rw [hc x]
      _ = b * x * (b * y) := by simp only [mul_assoc]
  map_zero' := Subtype.ext <| by simp
  map_add' x y := Subtype.ext <| by simp
  commutes' r := Subtype.ext <| by
    rw [hb.isIdempotentElem_val.val_compress_of_commute
        (Subalgebra.mem_center_iff.1 b.property _).symm,
      IsIdempotentElem.Corner.val_algebraMap, Algebra.algebraMap_eq_smul_one, mul_smul_comm,
      mul_one]

/-- The projection onto the block algebra is multiplication by `e`. -/
theorem val_toBlockAlgebra (hb : IsBlockIdempotent b) (x : MonoidAlgebra R G) :
    (hb.toBlockAlgebra x).val = b * x :=
  hb.isIdempotentElem_val.val_compress_of_commute
    (Subalgebra.mem_center_iff.1 b.property x).symm

/-- The projection onto the block algebra is surjective. -/
theorem toBlockAlgebra_surjective (hb : IsBlockIdempotent b) :
    Function.Surjective hb.toBlockAlgebra :=
  fun y ↦ ⟨y.val, hb.isIdempotentElem_val.compress_val y⟩

/-- **The block algebra has no nontrivial central idempotents.** A central idempotent `z` of the
block algebra `e R[G]` is a central idempotent of `R[G]` with `z e = z`; as `e` is primitive in the
centre, `z` is `0` or `e`. -/
theorem centralIdempotents_blockAlgebra_subset (hb : IsBlockIdempotent b) :
    centralIdempotents hb.BlockAlgebra ⊆ {0, 1} := by
  intro z hz
  have he := hb.isIdempotentElem_val
  have hbz : (b : MonoidAlgebra R G) * z.val = z.val := he.mul_corner_val z
  have hzb : z.val * (b : MonoidAlgebra R G) = z.val := he.corner_val_mul z
  -- `z` commutes with every `x ∈ R[G]`, through its projection `e x`.
  have hc (x : MonoidAlgebra R G) : x * z.val = z.val * x := by
    have h := congrArg Subtype.val (mul_comm_of_mem_centralIdempotents hz (hb.toBlockAlgebra x))
    rw [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.Corner.val_mul,
      val_toBlockAlgebra] at h
    calc x * z.val = x * b * z.val := by rw [mul_assoc, hbz]
      _ = b * x * z.val := by rw [Subalgebra.mem_center_iff.1 b.property x]
      _ = z.val * (b * x) := h.symm
      _ = z.val * x := by rw [← mul_assoc, hzb]
  have hzz : z.val * z.val = z.val :=
    congrArg Subtype.val (isIdempotentElem_of_mem_centralIdempotents hz).eq
  have hbb : (b : MonoidAlgebra R G) * b = b := hb.isIdempotentElem_val.eq
  let f : Subalgebra.center R (MonoidAlgebra R G) :=
    ⟨z.val, Subalgebra.mem_center_iff.2 hc⟩
  rcases hb.eq_zero_or_eq_zero_of_add (e₁ := f) (e₂ := b - f) (Subtype.ext hzz)
    (Subtype.ext <| by
      change ((b : MonoidAlgebra R G) - z.val) * (b - z.val) = b - z.val
      rw [sub_mul, mul_sub, mul_sub, hbb, hbz, hzb, hzz, sub_self, sub_zero])
    (Subtype.ext <| by
      change z.val * ((b : MonoidAlgebra R G) - z.val) = 0
      rw [mul_sub, hzb, hzz, sub_self])
    (Subtype.ext <| by
      change ((b : MonoidAlgebra R G) - z.val) * z.val = 0
      rw [sub_mul, hbz, hzz, sub_self])
    (add_sub_cancel f b) with h | h
  · exact Or.inl (Subtype.ext (congrArg Subtype.val h :))
  · exact Or.inr (Subtype.ext (sub_eq_zero.1 (congrArg Subtype.val h :)).symm)

end Ring

section Field

variable {k : Type u} {G : Type v} [Field k] [Group G] [Finite G] {p : ℕ} [CharP k p]
  {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- **A block of defect zero is a semisimple ring.** If `1` is a defect group of a block idempotent
`e` of `k[G]`, `k` a field of characteristic `p`, then the block algebra `e k[G]` is semisimple:
its modules are `k[G]`-modules on which `e` acts as the identity, which are semisimple. -/
theorem isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) : IsSemisimpleRing hb.BlockAlgebra := by
  rcases CharP.char_is_prime_or_zero k p with hp | rfl
  swap
  · -- In characteristic zero `k[G]` is semisimple by Maschke's theorem.
    have := CharP.charP_to_charZero k
    have : NeZero (Nat.card G : k) := ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne'⟩
    exact hb.toBlockAlgebra.toRingHom.isSemisimpleRing_of_surjective hb.toBlockAlgebra_surjective
  have := Fact.mk hp
  let φ := hb.toBlockAlgebra
  let _ : Module (MonoidAlgebra k G) hb.BlockAlgebra := Module.compHom _ φ.toRingHom
  have : IsScalarTower k (MonoidAlgebra k G) hb.BlockAlgebra :=
    ⟨fun c x y ↦ by
      change φ (c • x) * y = c • (φ x * y)
      rw [map_smul]
      exact Subtype.ext (smul_mul_assoc c (φ x).val y.val)⟩
  have := hb.isSemisimpleModule_of_isDefectGroup_bot (V := hb.BlockAlgebra) hD fun v ↦ by
    change φ b * v = v
    rw [show φ b = 1 from Subtype.ext (by
      rw [val_toBlockAlgebra, hb.isIdempotentElem_val.eq]; rfl), one_mul]
  have : RingHomSurjective φ.toRingHom := ⟨hb.toBlockAlgebra_surjective⟩
  let l : hb.BlockAlgebra →ₛₗ[φ.toRingHom] hb.BlockAlgebra :=
    { AddMonoidHom.id _ with map_smul' := fun _ _ ↦ rfl }
  rw [IsSemisimpleRing, ← l.isSemisimpleModule_iff_of_bijective Function.bijective_id]
  infer_instance

/-- **A block of defect zero is a simple ring.** If `1` is a defect group of a block idempotent
`e` of `k[G]`, `k` a field of characteristic `p`, then the block algebra `e k[G]` is simple. -/
theorem isSimpleRing_blockAlgebra_of_isDefectGroup_bot (hb : IsBlockIdempotent b)
    (hD : IsDefectGroup k p (b : MonoidAlgebra k G) ⊥) : IsSimpleRing hb.BlockAlgebra :=
  have := hb.isSemisimpleRing_blockAlgebra_of_isDefectGroup_bot hD
  IsSemisimpleRing.isSimpleRing_of_centralIdempotents_subset
    hb.centralIdempotents_blockAlgebra_subset

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

end Field

end IsBlockIdempotent

end TauCeti
