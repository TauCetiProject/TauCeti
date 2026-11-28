/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Coadjoint.RootPlane
public import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.Dimension.DirectSum
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Critical points and Hessians of heights on coadjoint orbits

Let `L` be a Lie algebra with an invariant bilinear form `B`, so that `p ↦ B p` identifies the
adjoint orbit of `p ∈ L` with the coadjoint orbit of `B p`. For `X ∈ L` the **height**
`f_X = B(·, X)` restricts to the orbit. Its tangent vectors at `p` are the values `q_p A = ⁅A, p⁆`
of the orbit derivative, and the derivative of `f_X` at `p` in the direction `q_p A` is
`B(⁅A, p⁆, X)`. So `p` is a critical point of `f_X` on its orbit exactly when `⁅X, p⁆ = 0`, for a
separating form (`LinearMap.BilinForm.forall_apply_lie_eq_zero_iff`).

At such a critical point the second derivative of `f_X` along `t ↦ Ad_(exp tA) p` is
`-B(⁅A, p⁆, ⁅A, X⁆)` (`TauCeti.Geometry.Lie.Adjoint.Exponential.Height`). This file studies the
bilinear form

`h_(p,X)(A, C) = -B(⁅A, p⁆, ⁅C, X⁆)`

on `L` (`LinearMap.BilinForm.heightHessian`). For an invariant form and `⁅X, p⁆ = 0` it is
symmetric (`LinearMap.BilinForm.isSymm_heightHessian`), and it is the Hessian of `f_X` at `p`
pulled back to `L` along the orbit derivative `A ↦ ⁅A, p⁆`, whose kernel, the centralizer of `p`,
lies in the kernel of `h_(p,X)` (`LinearMap.BilinForm.ker_ad_le_ker_heightHessian`). Since the
orbit derivative is onto the tangent space, the indices of inertia of `h_(p,X)` are those of the
Hessian on the orbit (`QuadraticForm.sigNeg_comp_of_surjective`): its negative index is the Morse
index of `f_X` at `p`. The critical point is nondegenerate exactly when the kernel of `h_(p,X)` is
the centralizer of `p`.

These invariants are computed from a **root-plane decomposition**
(`TauCeti.IsRootPlaneDecomposition B t α E J`): an abelian subspace `t` and pairwise orthogonal
root planes `E_i` of `t` (`TauCeti.IsRootPlane`), with roots `α_i`, on which `B` is positive
definite, such that `t` and the `E_i` span `L`. For a compact Lie algebra with a positive invariant
form, a maximal abelian subalgebra and one plane for each pair of roots `±α` form such a
decomposition. For `p, X ∈ t` the form `h_(p,X)` is diagonal: `t` lies in its kernel, distinct
planes do not interact, and on `E_i` it is `-α_i(p) α_i(X) B`
(`TauCeti.IsRootPlaneDecomposition.heightHessian_add_sum_add_sum`). Hence, by Sylvester's law of
inertia,

* the Morse index is `Σ dim E_i` over the planes with `α_i(p) α_i(X) > 0`
  (`TauCeti.IsRootPlaneDecomposition.sigNeg_toQuadraticMap_heightHessian`), that is
  `2 #{i | α_i(p) α_i(X) > 0}` for planes of dimension two
  (`TauCeti.IsRootPlaneDecomposition.sigNeg_toQuadraticMap_heightHessian_eq_two_mul_card`);
* the positive index is `Σ dim E_i` over the planes with `α_i(p) α_i(X) < 0`
  (`TauCeti.IsRootPlaneDecomposition.sigPos_toQuadraticMap_heightHessian`);
* for nonzero planes, the critical point is nondegenerate, that is the kernel of `h_(p,X)` is the
  centralizer of `p`, exactly when `α_i(X) ≠ 0` for every root with `α_i(p) ≠ 0`
  (`TauCeti.IsRootPlaneDecomposition.ker_heightHessian_eq_ker_ad_iff`). This holds at every
  `p ∈ t` when `X` is regular, `α_i(X) ≠ 0` for all `i`.

The index formula `index_p(f_X) = 2 #{α ∈ Φ⁺ | α(p) ≠ 0, α(X) α(p) > 0}` is the one behind Bott's
computation of the homology of flag manifolds. The decomposition, its positivity and the dimension
of the planes are hypotheses here; the formulas themselves are linear algebra over an ordered
field and use neither the invariance nor the symmetry of `B`.

The decomposition of `so(3)` into a line and its orthogonal plane is worked out in
`TauCeti.Algebra.Lie.Orthogonal.CrossProduct.RootPlane`. The descent of the Hessian to the
tangent model `L ⧸ L_ν` of the orbit, and the dimension of the orbit, are in
`TauCeti.Algebra.Lie.Coadjoint.Height.TangentModel`.

## Main definitions

* `LinearMap.BilinForm.heightHessian B p X`: the form `(A, C) ↦ -B(⁅A, p⁆, ⁅C, X⁆)`.
* `TauCeti.IsRootPlaneDecomposition B t α E J`: `L` is spanned by the abelian subspace `t` and the
  pairwise orthogonal, positive root planes `E_i` with roots `α_i` and rotations `J_i`.

## Main results

* `LinearMap.BilinForm.forall_apply_lie_eq_zero_iff`: the critical points of a height.
* `LinearMap.BilinForm.isSymm_heightHessian`: the Hessian is symmetric at a critical point.
* `TauCeti.IsRootPlane.heightHessian_apply`: the Hessian on a root plane.
* `TauCeti.IsRootPlaneDecomposition.heightHessian_add_sum_add_sum`: the Hessian is diagonal in a
  root-plane decomposition.
* `TauCeti.IsRootPlaneDecomposition.sigNeg_toQuadraticMap_heightHessian`,
  `TauCeti.IsRootPlaneDecomposition.sigPos_toQuadraticMap_heightHessian`: the Morse index and the
  positive index.
* `TauCeti.IsRootPlaneDecomposition.ker_heightHessian_eq_ker_ad_iff`: nondegeneracy.
* `TauCeti.IsRootPlaneDecomposition.exists_mem_apply_ne_zero`: with nonzero roots, a separating
  invariant form stays separating on `t`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281.
* M. Audin, *Torus Actions on Symplectic Manifolds*, 2nd ed., Progress in Mathematics 93,
  Birkhäuser, 2004, Chapter II (coadjoint orbits and their height functions).
-/

public section

open Module (Dual finrank)
open Finset QuadraticMap

/-! ### Critical points and the Hessian of a height -/

namespace LinearMap.BilinForm

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The **Hessian of the height** `f_X = B(·, X)` at `p`, pulled back to `L` along the orbit
derivative `A ↦ ⁅A, p⁆`: the bilinear form `(A, C) ↦ -B(⁅A, p⁆, ⁅C, X⁆)`. When `B` is invariant
and `⁅X, p⁆ = 0`, its value at `(A, A)` is the second derivative of `t ↦ B(Ad_(exp tA) p, X)` at
`t = 0`. -/
def heightHessian (B : LinearMap.BilinForm R L) (p X : L) : LinearMap.BilinForm R L :=
  -B.compl₁₂ (LieAlgebra.ad R L p) (LieAlgebra.ad R L X)

variable {B : LinearMap.BilinForm R L} {p X : L}

@[simp]
theorem heightHessian_apply (A C : L) : B.heightHessian p X A C = -B ⁅A, p⁆ ⁅C, X⁆ := by
  simp only [heightHessian, LinearMap.neg_apply, compl₁₂_apply, LieAlgebra.ad_apply]
  rw [← lie_skew A p, ← lie_skew C X]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

/-- The Hessian of the height `f_(-X)` is the negative of that of `f_X`. -/
@[simp]
theorem heightHessian_neg_right : B.heightHessian p (-X) = -B.heightHessian p X := by
  ext A C
  simp only [heightHessian_apply, lie_neg, map_neg, LinearMap.neg_apply]

/-- **The critical points of a height.** For an invariant form `B` which is separating, the
derivative `B(⁅A, p⁆, X)` of the height `f_X` at `p` in the direction of the tangent vector
`⁅A, p⁆` of the orbit vanishes for every `A` exactly when `⁅X, p⁆ = 0`. -/
theorem forall_apply_lie_eq_zero_iff (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) :
    (∀ A : L, B ⁅A, p⁆ X = 0) ↔ ⁅X, p⁆ = 0 := by
  -- By invariance, `B(⁅A, p⁆, X) = -B(⁅X, p⁆, A)`.
  have key (A : L) : B ⁅A, p⁆ X = -B ⁅X, p⁆ A := by
    rw [hB A p X, hB X p A, ← lie_skew X A, map_neg, neg_neg]
  refine ⟨fun h ↦ hsep _ fun A ↦ ?_, fun h A ↦ by simp [key, h]⟩
  rw [← neg_eq_zero, ← key, h]

/-- The centralizer of `p` lies in the kernel of the Hessian of every height at `p`: the
Hessian descends to the tangent model of the orbit. -/
theorem ker_ad_le_ker_heightHessian :
    LinearMap.ker (LieAlgebra.ad R L p) ≤ LinearMap.ker (B.heightHessian p X) := fun A hA ↦ by
  rw [LinearMap.mem_ker, LieAlgebra.ad_apply, ← lie_skew, neg_eq_zero] at hA
  ext C
  simp [hA]

/-- **The Hessian of a height is symmetric at a critical point.** For an invariant form `B` and
`⁅X, p⁆ = 0`, the form `(A, C) ↦ -B(⁅A, p⁆, ⁅C, X⁆)` is symmetric
(`LinearMap.BilinForm.lieInvariant.apply_lie_lie_comm`). No symmetry of `B` is needed. -/
theorem isSymm_heightHessian (hB : B.lieInvariant L) (hXp : ⁅X, p⁆ = 0) :
    (B.heightHessian p X).IsSymm := by
  refine ⟨fun A C ↦ ?_⟩
  simp only [heightHessian_apply, neg_inj]
  exact hB.apply_lie_lie_comm hXp A C

/-- **The height Hessian as a form on generators of the coadjoint orbit.** For an invariant form,
`h_(p,X)(A, C) = (B p)(⁅⁅X, C⁆, A⁆)`. When `⁅X, p⁆ = 0`, the right side is the Hessian of the
height `f_X` at the critical point `B p` of the coadjoint orbit, evaluated on the generators of `A`
and `C`. -/
theorem heightHessian_apply_eq_apply_lie_lie (hB : B.lieInvariant L) (A C : L) :
    B.heightHessian p X A C = B p ⁅⁅X, C⁆, A⁆ := by
  rw [heightHessian_apply, ← lie_skew C X, map_neg, hB A p, ← lie_skew ⁅X, C⁆ A, map_neg, neg_neg]

end LinearMap.BilinForm

namespace TauCeti

namespace IsRootPlane

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {B : LinearMap.BilinForm R L}
  {t : Submodule R L} {α : Dual R t} {E : Submodule R L} {J : Module.End R E}

/-- **The height Hessian on a root plane.** For `p, X ∈ t` and `A, C` in a root plane with root
`α`, the height Hessian is `h_(p,X)(A, C) = -α(p) α(X) B(A, C)`. -/
theorem heightHessian_apply (h : IsRootPlane B t α E J) (p X : t) (v w : E) :
    B.heightHessian p X v w = -(α p * α X * B v w) := by
  rw [LinearMap.BilinForm.heightHessian_apply, h.apply_lie_lie]

end IsRootPlane

/-! ### Root-plane decompositions -/

variable {R L : Type*} [CommRing R] [PartialOrder R] [LieRing L] [LieAlgebra R L]

/-- A **root-plane decomposition** of `L` for the bilinear form `B`: the subspace `t` is
abelian, the planes `E i` are root planes of `t` with roots `α i` and rotations `J i`
(`TauCeti.IsRootPlane`), pairwise orthogonal for `B`, `B` is positive definite on each of them, and
`t` and the planes span `L`. For a compact Lie algebra with a positive invariant form, a maximal
abelian subalgebra and one real plane for each pair of roots `±α` form such a decomposition. The
sum is not required to be direct. -/
structure IsRootPlaneDecomposition {ι : Type*} (B : LinearMap.BilinForm R L) (t : Submodule R L)
    (α : ι → Dual R t) (E : ι → Submodule R L) (J : ∀ i, Module.End R (E i)) : Prop where
  /-- Each plane is a root plane. -/
  isRootPlane (i : ι) : IsRootPlane B t (α i) (E i) (J i)
  /-- Distinct planes are orthogonal. -/
  le_orthogonal {i j : ι} (hij : i ≠ j) : E j ≤ B.orthogonal (E i)
  /-- The form is positive definite on each plane. -/
  pos (i : ι) {v : L} (hv : v ∈ E i) (hv0 : v ≠ 0) : 0 < B v v
  /-- The subspace `t` is abelian. -/
  lie_eq_zero {H H' : L} (hH : H ∈ t) (hH' : H' ∈ t) : ⁅H, H'⁆ = 0
  /-- The subspace `t` and the planes span `L`. -/
  sup_eq_top : t ⊔ ⨆ i, E i = ⊤

namespace IsRootPlaneDecomposition

variable {ι : Type*} {B : LinearMap.BilinForm R L} {t : Submodule R L} {α : ι → Dual R t}
  {E : ι → Submodule R L} {J : ∀ i, Module.End R (E i)}

/-- Two vectors of distinct planes of a root-plane decomposition are orthogonal. -/
theorem apply_eq_zero (hD : IsRootPlaneDecomposition B t α E J) {i j : ι} (hij : i ≠ j)
    {v w : L} (hv : v ∈ E i) (hw : w ∈ E j) : B v w = 0 :=
  hD.le_orthogonal hij hw v hv

/-- The form is nonnegative on each plane of a root-plane decomposition. -/
theorem apply_self_nonneg (hD : IsRootPlaneDecomposition B t α E J) {i : ι} {v : L}
    (hv : v ∈ E i) : 0 ≤ B v v := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  · exact (hD.pos i hv hv0).le

/-- A vector of a plane of a root-plane decomposition with `B(v, v) = 0` is zero. -/
theorem eq_zero_of_apply_self_eq_zero (hD : IsRootPlaneDecomposition B t α E J) {i : ι}
    {v : L} (hv : v ∈ E i) (h : B v v = 0) : v = 0 := by
  by_contra hv0
  exact (hD.pos i hv hv0).ne' h

/-- The planes of a root-plane decomposition are independent. -/
theorem iSupIndep (hD : IsRootPlaneDecomposition B t α E J) : iSupIndep E :=
  B.iSupIndep_of_restrict_separatingRight (fun _ _ hij _ hv _ hw ↦ hD.apply_eq_zero hij hv hw)
    fun _ v hv ↦ Subtype.ext (hD.eq_zero_of_apply_self_eq_zero v.property (hv v))

/-- For `p, X ∈ t` and vectors `v ∈ E_i`, `w ∈ E_j` of a root-plane decomposition,
`B(⁅v, p⁆, ⁅w, X⁆)` is `α_i(p) α_i(X) B(v, w)` when `i = j` and zero otherwise. -/
theorem apply_lie_lie_of_mem [DecidableEq ι] (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) {i j : ι} {v w : L} (hv : v ∈ E i) (hw : w ∈ E j) :
    B ⁅v, (p : L)⁆ ⁅w, (X : L)⁆ = if i = j then α i p * α i X * B v w else 0 := by
  split_ifs with hij
  · subst hij
    exact (hD.isRootPlane i).apply_lie_lie p X ⟨v, hv⟩ ⟨w, hw⟩
  · exact (hD.isRootPlane i).apply_lie_lie_eq_zero_of_le_orthogonal (hD.isRootPlane j)
      (hD.le_orthogonal hij) p X ⟨v, hv⟩ ⟨w, hw⟩

/-- Every vector is the sum of a vector of `t` and one vector of each plane. -/
theorem exists_eq_add_sum [Fintype ι] (hD : IsRootPlaneDecomposition B t α E J) (x : L) :
    ∃ H ∈ t, ∃ a : ∀ i, E i, x = H + ∑ i, (a i : L) := by
  have hx : x ∈ t ⊔ ⨆ i ∈ (univ : Finset ι), E i := by
    simp only [mem_univ, iSup_true, hD.sup_eq_top, Submodule.mem_top]
  obtain ⟨H, hH, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E y).mp hy
  exact ⟨H, hH, a, rfl⟩

/-- **A separating invariant form stays separating on `t`.** In a root-plane decomposition with
nonzero roots for a separating invariant form `B`, every nonzero `v ∈ t` pairs nontrivially with
some element of `t`: the root planes are orthogonal to `t`
(`TauCeti.IsRootPlane.apply_eq_zero_of_forall_lie_eq_zero`), so `t` carries all of `B v`. -/
theorem exists_mem_apply_ne_zero [NoZeroDivisors R] (hD : IsRootPlaneDecomposition B t α E J)
    (hB : B.lieInvariant L) (hsep : B.SeparatingLeft) (hα : ∀ i, α i ≠ 0) {v : L} (hv : v ∈ t)
    (hv0 : v ≠ 0) : ∃ H ∈ t, B v H ≠ 0 := by
  by_contra! h
  -- `B v` vanishes on `t` and on every plane, hence on `t ⊔ ⨆ i, E i = L`.
  have hle : t ⊔ ⨆ i, E i ≤ LinearMap.ker (B v) :=
    sup_le (fun H hH ↦ LinearMap.mem_ker.2 (h H hH)) <| iSup_le fun i w hw ↦
      LinearMap.mem_ker.2 <| (hD.isRootPlane i).apply_eq_zero_of_forall_lie_eq_zero hB (hα i)
        (fun H' ↦ hD.lie_eq_zero H'.property hv) ⟨w, hw⟩
  exact hv0 (hsep v fun w ↦ LinearMap.mem_ker.1 (hle (hD.sup_eq_top ▸ Submodule.mem_top)))

/-- **The Hessian of a height in a root-plane decomposition is diagonal.** For `p, X ∈ t`,
vectors `H, H'` of `t` and `a, b` with one vector in each plane `E i`, `i ∈ s`,
`h_(p,X)(H + Σ a_i, H' + Σ b_i) = -Σ α_i(p) α_i(X) B(a_i, b_i)`. -/
theorem heightHessian_add_sum_add_sum (hD : IsRootPlaneDecomposition B t α E J) (p X : t)
    {H H' : L} (hH : H ∈ t) (hH' : H' ∈ t) (s : Finset ι) (a b : ∀ i, E i) :
    B.heightHessian p X (H + ∑ i ∈ s, (a i : L)) (H' + ∑ i ∈ s, (b i : L)) =
      -∑ i ∈ s, α i p * α i X * B (a i) (b i) := by
  classical
  have hHp : ⁅H, (p : L)⁆ = 0 := hD.lie_eq_zero hH p.property
  have hH'X : ⁅H', (X : L)⁆ = 0 := hD.lie_eq_zero hH' X.property
  rw [LinearMap.BilinForm.heightHessian_apply, add_lie, hHp, zero_add, add_lie, hH'X, zero_add,
    sum_lie, sum_lie, neg_inj]
  -- Only the pairs of vectors in the same plane contribute.
  simp [hD.apply_lie_lie_of_mem p X (a _).property (b _).property]

/-- The value of the Hessian quadratic form of a height on `H + Σ a_i` in a root-plane
decomposition: `h_(p,X)(H + Σ a_i, H + Σ a_i) = -Σ α_i(p) α_i(X) B(a_i, a_i)`. -/
theorem toQuadraticMap_heightHessian_add_sum (hD : IsRootPlaneDecomposition B t α E J) (p X : t)
    {H : L} (hH : H ∈ t) (s : Finset ι) (a : ∀ i, E i) :
    (B.heightHessian p X).toQuadraticMap (H + ∑ i ∈ s, (a i : L)) =
      -∑ i ∈ s, α i p * α i X * B (a i) (a i) := by
  rw [LinearMap.BilinMap.toQuadraticMap_apply, hD.heightHessian_add_sum_add_sum p X hH hH s a a]

/-- The Hessian `h_(p,X)` pairs a vector `H + Σ a_i` with a vector `b` of the plane `E_j` to
`-α_j(p) α_j(X) B(a_j, b)`. -/
private theorem heightHessian_add_sum_apply [Fintype ι] (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) {H : L} (hH : H ∈ t) (a : ∀ i, E i) (j : ι) (b : E j) :
    B.heightHessian p X (H + ∑ i, (a i : L)) b = -(α j p * α j X * B (a j) b) := by
  classical
  rw [LinearMap.BilinForm.heightHessian_apply, add_lie, hD.lie_eq_zero hH p.property, zero_add]
  simp [sum_lie, hD.apply_lie_lie_of_mem p X (a _).property b.property]

/-- The Hessian `h_(p,X)` pairs a vector `a` of the plane `E_i` with a vector `H + Σ b_j` to
`-α_i(p) α_i(X) B(a, b_i)`. -/
private theorem heightHessian_apply_add_sum [Fintype ι] (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) {H : L} (hH : H ∈ t) (i : ι) (a : E i) (b : ∀ j, E j) :
    B.heightHessian p X a (H + ∑ j, (b j : L)) = -(α i p * α i X * B a (b i)) := by
  classical
  rw [LinearMap.BilinForm.heightHessian_apply, add_lie, hD.lie_eq_zero hH X.property, zero_add]
  simp [sum_lie, hD.apply_lie_lie_of_mem p X a.property (b _).property]

end IsRootPlaneDecomposition

/-! ### The indices of inertia -/

namespace IsRootPlaneDecomposition

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [LieRing L]
  [LieAlgebra K L] {ι : Type*} [Fintype ι] {B : LinearMap.BilinForm K L} {t : Submodule K L}
  {α : ι → Dual K t} {E : ι → Submodule K L} {J : ∀ i, Module.End K (E i)}

omit [Fintype ι] in
/-- The Hessian `h_(p,X)` is negative definite on the planes `E_i` with `α_i(p) α_i(X) > 0`. -/
private theorem toQuadraticMap_heightHessian_neg (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) {s : Finset ι} (hs : ∀ i ∈ s, 0 < α i p * α i X) {x : L} (hx : x ∈ ⨆ i ∈ s, E i)
    (hx0 : x ≠ 0) : (B.heightHessian p X).toQuadraticMap x < 0 := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E x).mp hx
  have hQ := hD.toQuadraticMap_heightHessian_add_sum p X t.zero_mem s a
  rw [zero_add] at hQ
  rw [hQ, neg_lt_zero]
  obtain ⟨i, hi, hai⟩ : ∃ i ∈ s, (a i : L) ≠ 0 := by
    by_contra! h
    exact hx0 (Finset.sum_eq_zero h)
  exact Finset.sum_pos' (fun j hj ↦ mul_nonneg (hs j hj).le (hD.apply_self_nonneg (a j).property))
    ⟨i, hi, mul_pos (hs i hi) (hD.pos i (a i).property hai)⟩

omit [Fintype ι] in
/-- The Hessian `h_(p,X)` is nonnegative on `t` and the planes `E_i` with `α_i(p) α_i(X) ≤ 0`. -/
private theorem toQuadraticMap_heightHessian_nonneg (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) {s : Finset ι} (hs : ∀ i ∈ s, α i p * α i X ≤ 0) {x : L}
    (hx : x ∈ t ⊔ ⨆ i ∈ s, E i) : 0 ≤ (B.heightHessian p X).toQuadraticMap x := by
  obtain ⟨H, hH, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum E y).mp hy
  rw [hD.toQuadraticMap_heightHessian_add_sum p X hH, neg_nonneg]
  exact Finset.sum_nonpos fun i hi ↦
    mul_nonpos_of_nonpos_of_nonneg (hs i hi) (hD.apply_self_nonneg (a i).property)

omit [Fintype ι] in
/-- **Sylvester's law of inertia for a root-plane decomposition.** Let `s` be a set of planes. If
the Hessian `h_(p,X)` is negative on `E_i` for `i ∈ s` and nonnegative on the other planes, its
negative index is `Σ_(i ∈ s) dim E_i`. -/
private theorem sigNeg_toQuadraticMap_heightHessian_of_forall [Finite ι] [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (p X : t) (s : Finset ι)
    (hs : ∀ i ∈ s, 0 < α i p * α i X) (hsc : ∀ i ∉ s, α i p * α i X ≤ 0) :
    sigNeg (B.heightHessian p X).toQuadraticMap = ∑ i ∈ s, finrank K (E i) := by
  classical
  have := Fintype.ofFinite ι
  set Q := (B.heightHessian p X).toQuadraticMap
  set A := ⨆ i ∈ s, E i
  set W := t ⊔ ⨆ i ∈ sᶜ, E i
  have hA : ((-Q).restrict A).PosDef := fun x hx0 ↦ by
    rw [QuadraticMap.restrict_apply, neg_apply, neg_pos]
    exact hD.toQuadraticMap_heightHessian_neg p X hs x.property fun h ↦ hx0 (Subtype.ext h)
  have hW : ∀ x ∈ W, 0 ≤ Q x := fun x hx ↦
    hD.toQuadraticMap_heightHessian_nonneg p X (fun i hi ↦ hsc i (Finset.mem_compl.mp hi)) hx
  -- The two subspaces span `L`.
  have hsup : A ⊔ W = ⊤ := by
    refine eq_top_iff.mpr (hD.sup_eq_top.symm.le.trans (sup_le ?_ (iSup_le fun i ↦ ?_)))
    · exact le_sup_of_le_right le_sup_left
    · by_cases hi : i ∈ s
      · exact le_sup_of_le_left (le_biSup E hi)
      · exact le_sup_of_le_right (le_sup_of_le_right (le_biSup E (Finset.mem_compl.mpr hi)))
  -- They are complementary, since `Q` is negative on nonzero vectors of `A` and nonnegative on `W`.
  have hAW : IsCompl A W := by
    refine ⟨Submodule.disjoint_def.mpr fun x hxA hxW ↦ ?_, codisjoint_iff.mpr hsup⟩
    by_contra hx0
    exact (hD.toQuadraticMap_heightHessian_neg p X hs hxA hx0).not_ge (hW x hxW)
  exact (QuadraticForm.sigNeg_eq_finrank_of_isCompl_of_negDef Q hAW hA hW).trans
    (finrank_biSup_eq_sum_finrank_of_iSupIndep hD.iSupIndep s)

/-- **The Morse index of a height at a torus point.** In a root-plane decomposition, the negative
index of the Hessian `h_(p,X)` of the height `f_X` at `p ∈ t`, for `X ∈ t`, is the sum of the
dimensions of the planes with `α_i(p) α_i(X) > 0`. -/
theorem sigNeg_toQuadraticMap_heightHessian [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (p X : t) :
    sigNeg (B.heightHessian p X).toQuadraticMap =
      ∑ i with 0 < α i p * α i X, finrank K (E i) :=
  hD.sigNeg_toQuadraticMap_heightHessian_of_forall p X _ (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
    fun i hi ↦ not_lt.mp fun h ↦ hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)

/-- **The positive index of the Hessian of a height at a torus point.** In a root-plane
decomposition, the positive index of the Hessian `h_(p,X)` at `p ∈ t`, for `X ∈ t`, is the sum of
the dimensions of the planes with `α_i(p) α_i(X) < 0`. -/
theorem sigPos_toQuadraticMap_heightHessian [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (p X : t) :
    sigPos (B.heightHessian p X).toQuadraticMap =
      ∑ i with α i p * α i X < 0, finrank K (E i) := by
  -- The Hessian of `f_(-X)` is the negative of that of `f_X`.
  have hneg : (B.heightHessian p (-X : t)).toQuadraticMap =
      -(B.heightHessian p X).toQuadraticMap := by
    rw [Submodule.coe_neg, LinearMap.BilinForm.heightHessian_neg_right,
      LinearMap.BilinMap.toQuadraticMap_neg]
  rw [← sigNeg_neg, ← hneg, hD.sigNeg_toQuadraticMap_heightHessian]
  simp only [map_neg, mul_neg, Left.neg_pos_iff]

/-- **The Morse index of a height at a torus point, for planes of dimension two.** In a root-plane
decomposition whose planes have dimension two, as for a compact Lie algebra, the Morse index of the
height `f_X` at `p ∈ t` is `2 #{i | α_i(p) α_i(X) > 0}`. -/
theorem sigNeg_toQuadraticMap_heightHessian_eq_two_mul_card [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (hE : ∀ i, finrank K (E i) = 2) (p X : t) :
    sigNeg (B.heightHessian p X).toQuadraticMap = 2 * #{i | 0 < α i p * α i X} := by
  rw [hD.sigNeg_toQuadraticMap_heightHessian, Finset.sum_congr rfl fun i _ ↦ hE i,
    Finset.sum_const, smul_eq_mul, mul_comm]

/-- **The positive index of the Hessian of a height, for planes of dimension two.** -/
theorem sigPos_toQuadraticMap_heightHessian_eq_two_mul_card [FiniteDimensional K L]
    (hD : IsRootPlaneDecomposition B t α E J) (hE : ∀ i, finrank K (E i) = 2) (p X : t) :
    sigPos (B.heightHessian p X).toQuadraticMap = 2 * #{i | α i p * α i X < 0} := by
  rw [hD.sigPos_toQuadraticMap_heightHessian, Finset.sum_congr rfl fun i _ ↦ hE i,
    Finset.sum_const, smul_eq_mul, mul_comm]

/-! ### Nondegeneracy -/

omit [Fintype ι] in
/-- **Nondegenerate critical points of a height.** In a root-plane decomposition, if
`α_i(X) ≠ 0` for every root with `α_i(p) ≠ 0`, the kernel of the Hessian `h_(p,X)` is exactly the
centralizer of `p`, so the Hessian is nondegenerate on the tangent model of the orbit. -/
theorem ker_heightHessian_eq_ker_ad [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (p X : t) (hX : ∀ i, α i p ≠ 0 → α i X ≠ 0) :
    LinearMap.ker (B.heightHessian p X) = LinearMap.ker (LieAlgebra.ad K L p) := by
  have := Fintype.ofFinite ι
  refine le_antisymm (fun x hx ↦ ?_) LinearMap.BilinForm.ker_ad_le_ker_heightHessian
  obtain ⟨H, hH, a, rfl⟩ := hD.exists_eq_add_sum x
  rw [LinearMap.mem_ker] at hx
  -- Each component `a_i` with `α_i(p) ≠ 0` vanishes.
  have ha (i : ι) (hi : α i p ≠ 0) : (a i : L) = 0 := by
    by_contra h
    have hval := hD.heightHessian_add_sum_apply p X hH a i (a i)
    rw [hx, LinearMap.zero_apply, eq_comm, neg_eq_zero] at hval
    exact (mul_ne_zero (mul_ne_zero hi (hX i hi)) (hD.pos i (a i).property h).ne') hval
  rw [LinearMap.mem_ker, LieAlgebra.ad_apply, lie_add, lie_sum, ← lie_skew,
    hD.lie_eq_zero hH p.property, neg_zero, zero_add]
  exact Finset.sum_eq_zero fun i _ ↦ ((hD.isRootPlane i).lie_eq_zero_iff p (a i)).mpr
    (or_iff_not_imp_left.mpr fun hi ↦ Subtype.ext (ha i hi))

omit [Fintype ι] in
/-- **Nondegenerate critical points of a height, characterized.** In a root-plane decomposition
with nonzero planes, the kernel of the Hessian `h_(p,X)` is the centralizer of `p` exactly when
`α_i(X) ≠ 0` for every root with `α_i(p) ≠ 0`. -/
theorem ker_heightHessian_eq_ker_ad_iff [Finite ι] (hD : IsRootPlaneDecomposition B t α E J)
    (hE : ∀ i, E i ≠ ⊥) (p X : t) :
    LinearMap.ker (B.heightHessian p X) = LinearMap.ker (LieAlgebra.ad K L p) ↔
      ∀ i, α i p ≠ 0 → α i X ≠ 0 := by
  have := Fintype.ofFinite ι
  refine ⟨fun h i hp hX ↦ ?_, hD.ker_heightHessian_eq_ker_ad p X⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hE i)
  -- A nonzero vector of a plane with `α_i(X) = 0` lies in the kernel of the Hessian.
  have hker : v ∈ LinearMap.ker (B.heightHessian p X) := by
    rw [LinearMap.mem_ker]
    ext y
    obtain ⟨H, hH, b, rfl⟩ := hD.exists_eq_add_sum y
    rw [hD.heightHessian_apply_add_sum p X hH i ⟨v, hv⟩ b, hX, mul_zero, zero_mul, neg_zero,
      LinearMap.zero_apply]
  rw [h, LinearMap.mem_ker, LieAlgebra.ad_apply,
    (hD.isRootPlane i).lie_eq_zero_iff p ⟨v, hv⟩] at hker
  exact hker.elim hp fun h0 ↦ hv0 (congrArg Subtype.val h0)

end IsRootPlaneDecomposition

end TauCeti
