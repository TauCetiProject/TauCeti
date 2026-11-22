/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.Matrix.Module
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Isotropic

/-!
# Zarhin's quaternion construction

Let `e` be a bilinear form on a module `V` over a commutative ring `k`, let `W` be a submodule of
`V` with orthogonal `W^⊥`, and let `u` be a square matrix indexed by a finite type `ι` with
`uᵀ * u = -1`. Square matrices act on `V^ι = ι → V` through their coefficients
(`Matrix.Module.matrixModule`), and `V^ι` and `V^ι × V^ι` carry the orthogonal-sum forms
`∑ᵢ e (x i) (y i)` (`LinearMap.BilinForm.pi`) and its block-diagonal double
(`LinearMap.BilinForm.prod`). *Zarhin's subspace* is
`W₁ = {(x, u • x) : x ∈ W^ι} + {(y, -u • y) : y ∈ (W^⊥)^ι} ⊆ V^ι × V^ι`.

Its properties:

* if `e` is reflexive, `W₁` is isotropic, in every characteristic;
* a similitude of `e` mapping `W` onto itself, or a group acting on `V` by similitudes and
  preserving `W`, preserves `W₁` under the diagonal action;
* if `2` is invertible, the two graphs meet only in zero (`Matrix.disjoint_piGraph_neg`), and the
  linear map `(s, t) ↦ ½ (s - uᵀ • t) = ½ (s + u⁻¹ • t)` maps `W₁` onto `W^ι`;
* if moreover `k` is a field, `V` is finite-dimensional and `e` is nondegenerate,
  `dim W₁ = card ι * dim V`, half the dimension of `V^ι × V^ι`, so `W₁` is Lagrangian when `e` is
  also reflexive.

The isotropy rests on the adjunction `∑ᵢ e ((u • x) i) (y i) = ∑ᵢ e (x i) ((uᵀ • y) i)`: the
pairing of `(x + y, u • (x - y))` with `(x' + y', u • (x' - y'))` is
`e(x + y, x' + y') - e(x - y, x' - y') = 2 e(x, y') + 2 e(y, x')`, which vanishes because `W` and
`W^⊥` are orthogonal. The graph sum is direct because `u • x = -u • x` forces `2 • u • x = 0`;
without `2` invertible this fails, and over `𝔽₂` with `u = 1` the two graphs coincide.

For a quaternion `a` with `normSq a = -1`, the matrix `u` of right multiplication by `a` in the
basis `1, i, j, k` satisfies `uᵀ * u = -1` (`Quaternion.transpose_mul_toMatrix_mulRight`), so
`ι = Fin 4` and four elements of `k` whose squares sum to `-1` supply `u`. Faltings uses this
construction for an alternating form on a finite-dimensional vector space over `ℚ_l`, where such
elements exist for every prime `l`: it turns an arbitrary Galois-stable subspace `W` of the
rational Tate module into a Galois-stable maximal isotropic subspace of the eighth power, from
which `W` is recovered by the linear map above.

## Main results

* `LinearMap.BilinForm.zarhinSubspace`, `LinearMap.BilinForm.mem_zarhinSubspace_iff`: Zarhin's
  subspace, whose elements are the pairs `(x + y, u • (x - y))` with `x ∈ W^ι`, `y ∈ (W^⊥)^ι`.
* `LinearMap.BilinForm.pi_matrix_smul_left`: a scalar matrix is adjoint to its transpose for the
  orthogonal-sum form.
* `LinearMap.BilinForm.zarhinSubspace_le_orthogonal`: Zarhin's subspace is isotropic.
* `LinearMap.BilinForm.map_zarhinSubspace_le`,
  `LinearMap.BilinForm.map_zarhinSubspace_le_of_representation`: stability under similitudes.
* `LinearMap.BilinForm.map_zarhinSubspace_eq_pi`: recovery of `W^ι`.
* `LinearMap.BilinForm.finrank_zarhinSubspace`: `dim W₁ = card ι * dim V`.
* `LinearMap.BilinForm.zarhinSubspace_eq_orthogonal`: Zarhin's subspace is Lagrangian.

## References

* G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73
  (1983), §5, p. 361.
* J. S. Milne, *Abelian varieties*, course notes (2008), I Theorem 13.12 and IV §2.
-/

public section

open Module
open scoped Matrix Matrix.Module

namespace LinearMap.BilinForm

section CommRing

variable {ι k V : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [AddCommGroup V] [Module k V]

/-- For the orthogonal-sum form on `V^ι`, a scalar matrix is adjoint to its transpose. -/
theorem pi_matrix_smul_left (e : LinearMap.BilinForm k V) (u : Matrix ι ι k) (x y : ι → V) :
    pi (fun _ : ι ↦ e) (u • x) y = pi (fun _ : ι ↦ e) x (uᵀ • y) := by
  simp only [pi_apply, Matrix.Module.smul_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Zarhin's subspace of `V^ι × V^ι` attached to a form `e`, a square matrix `u` and a
submodule `W`: the sum of the graph of `u` over `W^ι` and the graph of `-u` over `(W^⊥)^ι`. -/
def zarhinSubspace (e : LinearMap.BilinForm k V) (u : Matrix ι ι k) (W : Submodule k V) :
    Submodule k ((ι → V) × (ι → V)) :=
  u.piGraph W ⊔ (-u).piGraph (e.orthogonal W)

/-- The elements of Zarhin's subspace are the pairs `(x + y, u • (x - y))` with `x ∈ W^ι` and
`y ∈ (W^⊥)^ι`. -/
theorem mem_zarhinSubspace_iff {e : LinearMap.BilinForm k V} {u : Matrix ι ι k}
    {W : Submodule k V} {p : (ι → V) × (ι → V)} :
    p ∈ e.zarhinSubspace u W ↔ ∃ x y : ι → V, (∀ i, x i ∈ W) ∧ (∀ i, y i ∈ e.orthogonal W) ∧
      p = (x + y, u • (x - y)) := by
  rw [zarhinSubspace, Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Matrix.mem_piGraph_iff] at ha hb
    refine ⟨a.1, b.1, ha.1, hb.1, Prod.ext rfl ?_⟩
    rw [Prod.snd_add, ha.2, hb.2, smul_sub, neg_smul, sub_eq_add_neg]
  · rintro ⟨x, y, hx, hy, rfl⟩
    refine ⟨(x, u • x), Matrix.mem_piGraph_iff.mpr ⟨hx, rfl⟩, (y, (-u) • y),
      Matrix.mem_piGraph_iff.mpr ⟨hy, rfl⟩, Prod.ext rfl ?_⟩
    simp [sub_eq_add_neg]

/-- **Isotropy of Zarhin's subspace.** If `e` is reflexive and `uᵀ * u = -1`, Zarhin's subspace
is isotropic for the orthogonal-sum form on `V^ι × V^ι`. -/
theorem zarhinSubspace_le_orthogonal {e : LinearMap.BilinForm k V} (he : e.IsRefl)
    {u : Matrix ι ι k} (hu : uᵀ * u = -1) (W : Submodule k V) :
    e.zarhinSubspace u W ≤ ((pi fun _ : ι ↦ e).prod (pi fun _ : ι ↦ e)).orthogonal
      (e.zarhinSubspace u W) := by
  intro q hq
  rw [mem_orthogonal_iff]
  intro p hp
  obtain ⟨x, y, hx, hy, rfl⟩ := mem_zarhinSubspace_iff.mp hp
  obtain ⟨x', y', hx', hy', rfl⟩ := mem_zarhinSubspace_iff.mp hq
  have hxy : pi (fun _ : ι ↦ e) x y' = 0 := by
    simp [fun i ↦ hy' i (x i) (hx i)]
  have hyx : pi (fun _ : ι ↦ e) y x' = 0 := by
    simp [fun i ↦ he _ _ (hy i (x' i) (hx' i))]
  rw [prod_apply, pi_matrix_smul_left, smul_smul, hu, neg_smul, one_smul]
  simp only [map_add, map_sub, map_neg, LinearMap.add_apply, LinearMap.sub_apply]
  linear_combination 2 * hxy + 2 * hyx

/-- **Recovery of `W^ι`.** When `2` is invertible and `uᵀ * u = -1`, the linear map
`(s, t) ↦ ½ (s - uᵀ • t)`, that is `(s, t) ↦ ½ (s + u⁻¹ • t)`, maps Zarhin's subspace onto `W^ι`. -/
theorem map_zarhinSubspace_eq_pi [Invertible (2 : k)] (e : LinearMap.BilinForm k V)
    {u : Matrix ι ι k} (hu : uᵀ * u = -1) (W : Submodule k V) :
    (e.zarhinSubspace u W).map (⅟(2 : k) • (LinearMap.fst k (ι → V) (ι → V) -
      Algebra.lsmul k k (ι → V) uᵀ ∘ₗ LinearMap.snd k (ι → V) (ι → V))) =
      Submodule.pi Set.univ fun _ ↦ W := by
  have key (x y : ι → V) : (⅟(2 : k) • (LinearMap.fst k (ι → V) (ι → V) -
      Algebra.lsmul k k (ι → V) uᵀ ∘ₗ LinearMap.snd k (ι → V) (ι → V))) (x + y, u • (x - y)) =
        x := by
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.fst_apply,
      LinearMap.comp_apply, LinearMap.snd_apply, Algebra.lsmul_coe, smul_smul, hu, neg_smul,
      one_smul]
    rw [sub_neg_eq_add, add_add_sub_cancel, ← two_smul k x, smul_smul, invOf_mul_self, one_smul]
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨x, y, hx, -, rfl⟩ := mem_zarhinSubspace_iff.mp hp
    rw [key]
    exact fun i _ ↦ hx i
  · intro hz
    refine ⟨(z + 0, u • (z - 0)), mem_zarhinSubspace_iff.mpr ⟨z, 0, fun i ↦ hz i trivial,
      fun _ ↦ (e.orthogonal W).zero_mem, rfl⟩, key z 0⟩

/-- **Stability of Zarhin's subspace.** A similitude `g` of `e` that maps `W` onto itself
preserves Zarhin's subspace under its diagonal action on `V^ι × V^ι`. The similitude factor `c`
may be zero. -/
theorem map_zarhinSubspace_le {e : LinearMap.BilinForm k V} (u : Matrix ι ι k)
    {W : Submodule k V} {g : V →ₗ[k] V} {c : k} (hg : ∀ x y, e (g x) (g y) = c * e x y)
    (hW : W.map g = W) :
    (e.zarhinSubspace u W).map ((g.compLeft ι).prodMap (g.compLeft ι)) ≤
      e.zarhinSubspace u W := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := mem_zarhinSubspace_iff.mp hp
  refine mem_zarhinSubspace_iff.mpr ⟨g.compLeft ι x, g.compLeft ι y,
    fun i ↦ hW ▸ Submodule.mem_map_of_mem (hx i), fun i w hw ↦ ?_, ?_⟩
  · rw [← hW] at hw
    obtain ⟨w, hw, rfl⟩ := hw
    simp [hg, hy i w hw]
  · rw [LinearMap.prodMap_apply, map_add, ← map_sub]
    exact Prod.ext rfl ((g.mapMatrixModule ι).map_smul u (x - y))

/-- **Stability of Zarhin's subspace under a group.** If a group acts on `V` by similitudes of `e`
and preserves `W`, it preserves Zarhin's subspace under the diagonal action on `V^ι × V^ι`. -/
theorem map_zarhinSubspace_le_of_representation {G : Type*} [Group G]
    {e : LinearMap.BilinForm k V} (u : Matrix ι ι k) {W : Submodule k V}
    {ρ : Representation k G V} {c : G → k} (hρ : ∀ σ x y, e (ρ σ x) (ρ σ y) = c σ * e x y)
    (hW : ∀ σ, ∀ x ∈ W, ρ σ x ∈ W) (σ : G) :
    (e.zarhinSubspace u W).map (((ρ σ).compLeft ι).prodMap ((ρ σ).compLeft ι)) ≤
      e.zarhinSubspace u W := by
  refine map_zarhinSubspace_le u (hρ σ) (le_antisymm ?_ fun x hx ↦ ⟨ρ σ⁻¹ x, hW σ⁻¹ x hx, ?_⟩)
  · rintro _ ⟨x, hx, rfl⟩
    exact hW σ x hx
  · exact ρ.self_inv_apply σ x

end CommRing

section Field

variable {ι k V : Type*} [Fintype ι] [DecidableEq ι] [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- **Dimension of Zarhin's subspace.** If `2` is invertible, `e` is nondegenerate and
`uᵀ * u = -1`, Zarhin's subspace has dimension `card ι * dim V`, half the dimension of
`V^ι × V^ι`. -/
theorem finrank_zarhinSubspace [Invertible (2 : k)] {e : LinearMap.BilinForm k V}
    (he : e.Nondegenerate) {u : Matrix ι ι k} (hu : uᵀ * u = -1) (W : Submodule k V) :
    finrank k (e.zarhinSubspace u W) = Fintype.card ι * finrank k V := by
  have hunit : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr
    (Matrix.isUnit_det_of_left_inverse (B := -uᵀ) (by rw [neg_mul, hu, neg_neg]))
  have h := Submodule.finrank_sup_add_finrank_inf_eq (u.piGraph W) ((-u).piGraph (e.orthogonal W))
  rw [(Matrix.disjoint_piGraph_neg hunit W (e.orthogonal W)).eq_bot, finrank_bot, add_zero,
    Matrix.finrank_piGraph, Matrix.finrank_piGraph, finrank_orthogonal he] at h
  rw [zarhinSubspace, h, ← mul_add, Nat.add_sub_cancel' (Submodule.finrank_le W)]

/-- **Zarhin's subspace is Lagrangian.** If `2` is invertible, `e` is reflexive and nondegenerate
and `uᵀ * u = -1`, Zarhin's subspace is its own orthogonal for the orthogonal-sum form on
`V^ι × V^ι`. -/
theorem zarhinSubspace_eq_orthogonal [Invertible (2 : k)] {e : LinearMap.BilinForm k V}
    (he : e.IsRefl) (hnd : e.Nondegenerate) {u : Matrix ι ι k} (hu : uᵀ * u = -1)
    (W : Submodule k V) :
    e.zarhinSubspace u W = ((pi fun _ : ι ↦ e).prod (pi fun _ : ι ↦ e)).orthogonal
      (e.zarhinSubspace u W) := by
  refine (eq_orthogonal_iff_two_mul_finrank_eq (by simp [hnd])
    (zarhinSubspace_le_orthogonal he hu W)).mpr ?_
  rw [finrank_zarhinSubspace hnd hu, Module.finrank_prod, Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

end Field

end LinearMap.BilinForm
