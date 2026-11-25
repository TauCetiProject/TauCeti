/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Matrix.Pullback
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.RingTheory.LocalRing.Pullback

/-!
# Invertible matrices and algebraic `K₁` of a fibre product of rings

Let `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q` be ring homomorphisms and let
`D = A₁ ×_Q A₂ = RingHom.pullback π₁ π₂` be their fibre product, with projections
`p₁ : D →+* A₁` and `p₂ : D →+* A₂`. Matrices over `D` are pairs of matrices over `A₁` and `A₂`
which agree over `Q` (`RingHom.pullbackMatrixEquiv`), and so are invertible matrices:

```text
GLₙ(D) ≃* GLₙ(A₁) ×_{GLₙ(Q)} GLₙ(A₂).
```

When at least one of `π₁` and `π₂` is surjective, `D` with `p₁`, `p₂` is a *Milnor square*, and
algebraic `K₁` satisfies the first exactness statement of the Mayer–Vietoris sequence

```text
K₁(D) ──(p₁, p₂)──▶ K₁(A₁) × K₁(A₂) ──(x, y) ↦ π₁(x) / π₂(y)──▶ K₁(Q),
```

namely: a pair of classes `(x, y)` with `π₁(x) = π₂(y)` in `K₁(Q)` comes from a class of `K₁(D)`.
After stabilizing representatives `u` and `v` of `x` and `y` to a common size,
`π₁(u)⁻¹ π₂(v)` becomes elementary over `Q`. Say `π₁` is surjective. Elementary matrices lift
through surjections (`RingHom.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq`), so there is an
elementary `e` over `A₁` with `π₁(e) = π₁(u)⁻¹ π₂(v)`. Then `π₁(u e) = π₂(v)`, so `(u e, v)` is an
invertible matrix over `D`, and its class maps to `([u e], [v]) = (x, y)`. Surjectivity of one
leg is used only to lift this elementary matrix.

The composite of the two maps is trivial for every commutative square, with no surjectivity
assumption (`TauCeti.AlgebraicK1.map_pullback_comm_sq`). Injectivity of `K₁(D) → K₁(A₁) × K₁(A₂)`
is not claimed, and is false in general.

## Main definitions

* `RingHom.pullbackGLEquiv`: the isomorphism of `GLₙ(A₁ ×_Q A₂)` with the fibre product subgroup
  of `GLₙ(A₁) × GLₙ(A₂)`.

## Main results

* `TauCeti.AlgebraicK1.map_pullback_comm_sq`: the square of algebraic `K₁` groups induced by the
  fibre product square commutes.
* `TauCeti.AlgebraicK1.mayerVietoris_exact`: exactness of
  `K₁(A₁ ×_Q A₂) → K₁(A₁) × K₁(A₂) → K₁(Q)` at the middle term, when `π₁` or `π₂` is surjective.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §§2–4
  and Theorem 6.4.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Theorem 2.6.
-/

public section

noncomputable section

open Matrix

/-! ## Invertible matrices over a fibre product -/

namespace RingHom

variable {R S T : Type*} [Ring R] [Ring S] [Semiring T] (f : R →+* T) (g : S →+* T)
  (n : Type*) [Fintype n] [DecidableEq n]

/-- **Invertible matrices over a fibre product.** `GLₙ(R ×_T S)` is isomorphic to the subgroup of
pairs `(u₁, u₂)` in `GLₙ(R) × GLₙ(S)` whose images in `GLₙ(T)` agree, by sending an invertible
matrix to its two entrywise projections. This is `RingHom.pullbackUnitsEquiv` for the matrix
rings, transported along `RingHom.pullbackMatrixEquiv`. -/
def pullbackGLEquiv :
    GL n (f.pullback g) ≃*
      ((Units.map (f.mapMatrix (m := n) : Matrix n n R →* Matrix n n T)).comp
          (MonoidHom.fst (GL n R) (GL n S))).eqLocus
        ((Units.map (g.mapMatrix (m := n) : Matrix n n S →* Matrix n n T)).comp
          (MonoidHom.snd (GL n R) (GL n S))) :=
  (Units.mapEquiv (pullbackMatrixEquiv f g (n := n)).toMulEquiv).trans
    ((f.mapMatrix (m := n)).pullbackUnitsEquiv (g.mapMatrix (m := n)))

variable {n}

/-- The first component of `pullbackGLEquiv` is the entrywise first projection. -/
@[simp]
theorem coe_pullbackGLEquiv_apply_fst (u : GL n (f.pullback g)) :
    ((pullbackGLEquiv f g n u : GL n R × GL n S).1 : GL n R) =
      Units.map
        ((f.pullbackFst g).mapMatrix (m := n) : Matrix n n (f.pullback g) →* Matrix n n R) u := by
  ext i j
  simp [pullbackGLEquiv]

/-- The second component of `pullbackGLEquiv` is the entrywise second projection. -/
@[simp]
theorem coe_pullbackGLEquiv_apply_snd (u : GL n (f.pullback g)) :
    ((pullbackGLEquiv f g n u : GL n R × GL n S).2 : GL n S) =
      Units.map
        ((f.pullbackSnd g).mapMatrix (m := n) : Matrix n n (f.pullback g) →* Matrix n n S) u := by
  ext i j
  simp [pullbackGLEquiv]

/-- The invertible matrix over `R ×_T S` glued from a compatible pair `(u₁, u₂)` projects to `u₁`
over `R`. -/
@[simp]
theorem unitsMap_pullbackFst_pullbackGLEquiv_symm
    (v : ((Units.map (f.mapMatrix (m := n) : Matrix n n R →* Matrix n n T)).comp
          (MonoidHom.fst (GL n R) (GL n S))).eqLocus
        ((Units.map (g.mapMatrix (m := n) : Matrix n n S →* Matrix n n T)).comp
          (MonoidHom.snd (GL n R) (GL n S)))) :
    Units.map ((f.pullbackFst g).mapMatrix (m := n) : Matrix n n (f.pullback g) →* Matrix n n R)
        ((pullbackGLEquiv f g n).symm v) = v.val.1 := by
  rw [← coe_pullbackGLEquiv_apply_fst, MulEquiv.apply_symm_apply]

/-- The invertible matrix over `R ×_T S` glued from a compatible pair `(u₁, u₂)` projects to `u₂`
over `S`. -/
@[simp]
theorem unitsMap_pullbackSnd_pullbackGLEquiv_symm
    (v : ((Units.map (f.mapMatrix (m := n) : Matrix n n R →* Matrix n n T)).comp
          (MonoidHom.fst (GL n R) (GL n S))).eqLocus
        ((Units.map (g.mapMatrix (m := n) : Matrix n n S →* Matrix n n T)).comp
          (MonoidHom.snd (GL n R) (GL n S)))) :
    Units.map ((f.pullbackSnd g).mapMatrix (m := n) : Matrix n n (f.pullback g) →* Matrix n n S)
        ((pullbackGLEquiv f g n).symm v) = v.val.2 := by
  rw [← coe_pullbackGLEquiv_apply_snd, MulEquiv.apply_symm_apply]

end RingHom

/-! ## The Mayer–Vietoris sequence of algebraic `K₁` -/

namespace TauCeti.AlgebraicK1

variable {A₁ A₂ Q : Type*} [Ring A₁] [Ring A₂] [Ring Q] (π₁ : A₁ →+* Q) (π₂ : A₂ →+* Q)

/-- The square of algebraic `K₁` groups induced by the fibre product square of rings commutes:
`K₁(π₁) ∘ K₁(p₁) = K₁(π₂) ∘ K₁(p₂)` on `K₁(A₁ ×_Q A₂)`. -/
theorem map_pullback_comm_sq :
    (map π₁).comp (map (π₁.pullbackFst π₂)) = (map π₂).comp (map (π₁.pullbackSnd π₂)) := by
  rw [← map_comp, ← map_comp, RingHom.pullback_comm_sq]

/-- Two invertible matrices over `A₁` and `A₂` of the same size whose images over `Q` agree
define a pair of classes coming from `K₁(A₁ ×_Q A₂)`. -/
private theorem mk_prod_mk_mem_range {k : ℕ} {u : GL (Fin k) A₁} {v : GL (Fin k) A₂}
    (h : Units.map (π₁.mapMatrix (m := Fin k)).toMonoidHom u =
      Units.map (π₂.mapMatrix (m := Fin k)).toMonoidHom v) :
    (mk A₁ k u, mk A₂ k v) ∈
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  refine ⟨mk _ k ((π₁.pullbackGLEquiv π₂ (Fin k)).symm ⟨(u, v), h⟩), ?_⟩
  simp

/-- **Exactness of the Mayer–Vietoris sequence of algebraic `K₁` at `K₁(A₁) × K₁(A₂)`.** For ring
homomorphisms `π₁ : A₁ →+* Q` and `π₂ : A₂ →+* Q`, at least one of which is surjective, a pair of
classes `(x, y)` with `K₁(π₁) x = K₁(π₂) y` is `(K₁(p₁) z, K₁(p₂) z)` for some class `z` of the
fibre product `A₁ ×_Q A₂`, where `p₁` and `p₂` are its two projections; and conversely. In the
multiplicative notation of `TauCeti.AlgebraicK1`, the kernel of `(x, y) ↦ K₁(π₁) x / K₁(π₂) y` is
the range of `z ↦ (K₁(p₁) z, K₁(p₂) z)`. -/
theorem mayerVietoris_exact (h : Function.Surjective π₁ ∨ Function.Surjective π₂) :
    ((map π₁).comp (MonoidHom.fst _ _) / (map π₂).comp (MonoidHom.snd _ _)).ker =
      ((map (π₁.pullbackFst π₂)).prod (map (π₁.pullbackSnd π₂))).range := by
  refine le_antisymm ?_ ?_
  · rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, MonoidHom.div_apply, div_eq_one] at hxy
    -- Represent `x` and `y` by invertible matrices of a common size `m`.
    obtain ⟨m₁, u₀, rfl⟩ := exists_mk x
    obtain ⟨m₂, v₀, rfl⟩ := exists_mk y
    rw [← mk_stabilizeGL (le_max_left m₁ m₂) u₀, ← mk_stabilizeGL (le_max_right m₁ m₂) v₀] at hxy ⊢
    generalize stabilizeGL A₁ (le_max_left m₁ m₂) u₀ = u at hxy ⊢
    generalize stabilizeGL A₂ (le_max_right m₁ m₂) v₀ = v at hxy ⊢
    -- Over `Q`, the two images differ by an elementary matrix after stabilizing to size `k`.
    simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
      map_mk, mk_eq_mk_iff] at hxy
    obtain ⟨k, hk, he⟩ := hxy
    rw [← mk_stabilizeGL hk u, ← mk_stabilizeGL hk v]
    rw [map_mul, map_inv, stabilizeGL_map, stabilizeGL_map] at he
    -- Lift the elementary matrix along the surjective leg and correct that leg's matrix by it.
    rcases h with h₁ | h₂
    · obtain ⟨e, he₁, hπe⟩ :=
        π₁.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq h₁ he
      have hmem := mk_prod_mk_mem_range π₁ π₂ (u := stabilizeGL A₁ hk u * e)
        (v := stabilizeGL A₂ hk v) (by rw [map_mul, hπe, mul_inv_cancel_left])
      rwa [map_mul, elementarySubgroup_le_ker_mk k he₁, mul_one] at hmem
    · obtain ⟨e, he₂, hπe⟩ :=
        π₂.exists_mem_elementarySubgroup_unitsMap_mapMatrix_eq h₂ (inv_mem he)
      have hmem := mk_prod_mk_mem_range π₁ π₂ (u := stabilizeGL A₁ hk u)
        (v := stabilizeGL A₂ hk v * e) (by rw [map_mul, hπe, _root_.mul_inv_rev, inv_inv,
          mul_inv_cancel_left])
      rwa [map_mul, elementarySubgroup_le_ker_mk k he₂, mul_one] at hmem
  · rintro _ ⟨z, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.div_apply, div_eq_one]
    exact DFunLike.congr_fun (map_pullback_comm_sq π₁ π₂) z

end TauCeti.AlgebraicK1
