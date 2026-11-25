/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Prod.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Algebraic `K₁` of a product of rings

The isomorphism `GL n (A × B) ≃* GL n A × GL n B` (`TauCeti.prodGL`, taking the two components
of every entry) is compatible with stabilization `u ↦ u ⊕ 1`. Passing to the limit, algebraic
`K₁` takes products of rings to products of groups:
`K₁(A × B) ≃* K₁(A) × K₁(B)` (`TauCeti.AlgebraicK1.prodEquiv`), the two components being the
homomorphisms of `K₁` induced by the projections `A × B → A` and `A × B → B`. The inverse sends
the pair of classes of `u ∈ GL (Fin n) A` and `v ∈ GL (Fin n) B` to the class of the invertible
matrix over `A × B` with components `u` and `v`. The rings may be noncommutative.

## Main definitions

* `TauCeti.AlgebraicK1.prodEquiv`: the isomorphism `K₁(A × B) ≃* K₁(A) × K₁(B)`.

## Main results

* `TauCeti.prodGL_stabilizeGL`, `TauCeti.stabilizeGL_prodGL_symm`: `TauCeti.prodGL` commutes
  with stabilization.
* `TauCeti.AlgebraicK1.prodEquiv_apply`: the components of `TauCeti.AlgebraicK1.prodEquiv` are
  the homomorphisms of `K₁` induced by the two projections.
* `TauCeti.AlgebraicK1.prodEquiv_symm_mk`: the inverse sends the pair of classes `([u], [v])` to
  the class of the matrix with components `u` and `v`.
* `TauCeti.AlgebraicK1.map_fst_prodEquiv_symm`, `TauCeti.AlgebraicK1.map_snd_prodEquiv_symm`:
  the projections recover the two components from the inverse.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §1 (`K₁` of a ring and its functoriality in ring maps).
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {A B : Type*} [Ring A] [Ring B]

/-- Splitting an invertible matrix over `A × B` into its two components commutes with
stabilization `u ↦ u ⊕ 1`. -/
theorem prodGL_stabilizeGL {m n : ℕ} (h : m ≤ n) (g : GL (Fin m) (A × B)) :
    prodGL (Fin n) A B (stabilizeGL (A × B) h g) =
      Prod.map (stabilizeGL A h) (stabilizeGL B h) (prodGL (Fin m) A B g) :=
  Prod.ext (by simpa using (stabilizeGL_map h (RingHom.fst A B) g).symm)
    (by simpa using (stabilizeGL_map h (RingHom.snd A B) g).symm)

/-- Stabilizing the invertible matrix over `A × B` with components `p.1` and `p.2` stabilizes
both components. -/
theorem stabilizeGL_prodGL_symm {m n : ℕ} (h : m ≤ n) (p : GL (Fin m) A × GL (Fin m) B) :
    stabilizeGL (A × B) h ((prodGL (Fin m) A B).symm p) =
      (prodGL (Fin n) A B).symm (Prod.map (stabilizeGL A h) (stabilizeGL B h) p) := by
  rw [MulEquiv.eq_symm_apply, prodGL_stabilizeGL, MulEquiv.apply_symm_apply]

namespace AlgebraicK1

/-! ## Products of rings -/

section Prod

variable (A B)

/-- The class in `K₁(A × B)` of the invertible matrix over `A × B` with components `u` and `1`.
These homomorphisms are compatible with stabilization, so they induce the inverse of
`TauCeti.AlgebraicK1.prodEquiv` on the first factor. -/
private def inlFamily (n : ℕ) : GL (Fin n) A →* AlgebraicK1 (A × B) :=
  (mk (A × B) n).comp ((prodGL (Fin n) A B).symm.toMonoidHom.comp (MonoidHom.inl _ _))

/-- The class in `K₁(A × B)` of the invertible matrix over `A × B` with components `1` and `v`.
These homomorphisms are compatible with stabilization, so they induce the inverse of
`TauCeti.AlgebraicK1.prodEquiv` on the second factor. -/
private def inrFamily (n : ℕ) : GL (Fin n) B →* AlgebraicK1 (A × B) :=
  (mk (A × B) n).comp ((prodGL (Fin n) A B).symm.toMonoidHom.comp (MonoidHom.inr _ _))

variable {A B}

private theorem inlFamily_stabilizeGL (m n : ℕ) (h : m ≤ n) (u : GL (Fin m) A) :
    inlFamily A B n (stabilizeGL A h u) = inlFamily A B m u := by
  simp [inlFamily, ← mk_stabilizeGL h, stabilizeGL_prodGL_symm]

private theorem inrFamily_stabilizeGL (m n : ℕ) (h : m ≤ n) (v : GL (Fin m) B) :
    inrFamily A B n (stabilizeGL B h v) = inrFamily A B m v := by
  simp [inrFamily, ← mk_stabilizeGL h, stabilizeGL_prodGL_symm]

variable (A B)

/-- **Algebraic `K₁` of a product of rings** is the product of the `K₁` groups:
`K₁(A × B) ≃* K₁(A) × K₁(B)`, the components being the homomorphisms of `K₁` induced by the two
projections (`TauCeti.AlgebraicK1.prodEquiv_apply`). The inverse sends the classes of
`u ∈ GL (Fin n) A` and `v ∈ GL (Fin n) B` to the class of the invertible matrix over `A × B` with
components `u` and `v` (`TauCeti.AlgebraicK1.prodEquiv_symm_mk`). -/
def prodEquiv : AlgebraicK1 (A × B) ≃* AlgebraicK1 A × AlgebraicK1 B :=
  MonoidHom.toMulEquiv ((map (RingHom.fst A B)).prod (map (RingHom.snd A B)))
    ((lift (inlFamily A B) inlFamily_stabilizeGL).coprod
      (lift (inrFamily A B) inrFamily_stabilizeGL))
    (hom_ext fun n ↦ MonoidHom.ext fun g ↦ by
      -- the class of `g` goes to `[(g₁, 1)] * [(1, g₂)] = [(g₁, g₂)] = [g]`
      simp only [MonoidHom.comp_apply, MonoidHom.prod_apply, map_mk, MonoidHom.coprod_apply,
        lift_mk, inlFamily, inrFamily, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
        MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul,
        RingHom.toMonoidHom_eq_coe]
      rw [← prodGL_apply_fst, ← prodGL_apply_snd, MulEquiv.symm_apply_apply])
    (by
      -- `([u], [v])` goes to `[(u, 1)] * [(1, v)]`, whose components are `[u]` and `[v]`
      refine MonoidHom.ext fun ⟨x, y⟩ ↦ ?_
      obtain ⟨m, u, rfl⟩ := exists_mk x
      obtain ⟨n, v, rfl⟩ := exists_mk y
      simp [inlFamily, inrFamily])

variable {A B}

/-- The components of the isomorphism `K₁(A × B) ≃* K₁(A) × K₁(B)` are the homomorphisms of `K₁`
induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (x : AlgebraicK1 (A × B)) :
    prodEquiv A B x = (map (RingHom.fst A B) x, map (RingHom.snd A B) x) :=
  (rfl)

/-- The inverse of `K₁(A × B) ≃* K₁(A) × K₁(B)` sends the classes of `u ∈ GL (Fin n) A` and
`v ∈ GL (Fin n) B` to the class of the invertible matrix over `A × B` with components `u` and
`v`. -/
@[simp]
theorem prodEquiv_symm_mk {n : ℕ} (u : GL (Fin n) A) (v : GL (Fin n) B) :
    (prodEquiv A B).symm (mk A n u, mk B n v) =
      mk (A × B) n ((prodGL (Fin n) A B).symm (u, v)) := by
  rw [MulEquiv.symm_apply_eq, prodEquiv_apply]
  simp

/-- The homomorphism of `K₁` induced by the first projection recovers the first component from
the inverse of `K₁(A × B) ≃* K₁(A) × K₁(B)`. -/
@[simp]
theorem map_fst_prodEquiv_symm (p : AlgebraicK1 A × AlgebraicK1 B) :
    map (RingHom.fst A B) ((prodEquiv A B).symm p) = p.1 := by
  have h := congrArg Prod.fst ((prodEquiv A B).apply_symm_apply p)
  rwa [prodEquiv_apply] at h

/-- The homomorphism of `K₁` induced by the second projection recovers the second component from
the inverse of `K₁(A × B) ≃* K₁(A) × K₁(B)`. -/
@[simp]
theorem map_snd_prodEquiv_symm (p : AlgebraicK1 A × AlgebraicK1 B) :
    map (RingHom.snd A B) ((prodEquiv A B).symm p) = p.2 := by
  have h := congrArg Prod.snd ((prodEquiv A B).apply_symm_apply p)
  rwa [prodEquiv_apply] at h

end Prod

end AlgebraicK1

end TauCeti
