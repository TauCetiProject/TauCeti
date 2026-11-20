/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.Prod

/-!
# The doubled sesquilinear form

For a form `h` on `M`, semilinear in its first variable along `I : R →+* R`, the *doubled form*
on `W = M × M` is `h ⊕ (-h)`:
`h_W ((x, y), (x', y')) = h x x' - h y y'`.
For a hermitian form `h` on a module `V` over a quadratic étale algebra `E/F`, with `I` the
conjugation of `E`, this is the hermitian space `V ⊕ (-V)` of the doubling method of
Piatetski-Shapiro–Rallis, in the normalisation of Eischen–Harris–Li–Skinner: the product
`U(V) × U(-V)` of the two isometry groups acts on it blockwise, and the Siegel parabolic of `U(W)`
is the stabiliser of its diagonal.

The diagonal `D = {(x, x)}` and the antidiagonal `A = {(x, -x)}` (the graphs of `id` and `-id`)
are isotropic, each is its own orthogonal as soon as `h` is right separating, and `A` and `D`
pair through `2 h`: `h_W ((x, -x), (y, y)) = 2 h x y`. When `2` is invertible they are
complementary, and the coordinates `(x, y) ↦ (x, -x) + (y, y)` give the linear equivalence
`TauCeti.doublingPolarization` with inverse `(u, v) ↦ (½ (u - v), ½ (u + v))`. In a basis of
`M` the Gram matrix of `h_W` is `diag(H, -H)` in the product basis and the antidiagonal block
matrix with blocks `2 H` in the polarized basis.

Nothing here needs `I` to be an involution, `h` to be hermitian or `R` to be a field, so the
statements apply at once to the split algebra `E = F × F`, which is not a field.

## Main declarations

* `LinearMap.doubledForm`: the form `h ⊕ (-h)` on `M × M`.
* `LinearMap.isSymm_doubledForm_iff`, `LinearMap.nondegenerate_doubledForm_iff`: the doubled form
  is hermitian (nondegenerate) exactly when `h` is.
* `LinearMap.doubledForm_antidiagonal_diagonal`: the antidiagonal and the diagonal pair through
  `2 h`.
* `LinearMap.orthogonalBilin_doubledForm_graph_id`,
  `LinearMap.orthogonalBilin_doubledForm_graph_neg_id`: for right-separating `h`, the diagonal
  and the antidiagonal are their own orthogonals.
* `TauCeti.doublingPolarization`: the polarization `M × M ≃ M × M`, `(x, y) ↦ (x, -x) + (y, y)`.
* `LinearMap.isCompl_graph_neg_id_graph_id`: the antidiagonal and the diagonal are complements.
* `LinearMap.ext₂_antidiagonal_diagonal`: a form on `M × M` is determined by its four
  polarization blocks.
* `LinearMap.toMatrix₂_doubledForm`, `LinearMap.toMatrix₂_doubledForm_polarization`: the Gram
  matrices of the doubled form.
* `LinearMap.doubledForm_prodMap`: two similitudes with a common multiplier induce a similitude
  of the doubled forms.

## References

* E. Eischen, M. Harris, J.-S. Li, C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.1.
* S. Gelbart, I. Piatetski-Shapiro, S. Rallis, *Explicit constructions of automorphic
  L-functions*, Lecture Notes in Math. 1254, Springer, 1987.
-/

public section

namespace TauCeti

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- The polarization of `M × M` into antidiagonal and diagonal coordinates: `(x, y)` is sent to
`(x, -x) + (y, y)`, with inverse `(u, v) ↦ (½ (u - v), ½ (u + v))`. -/
def doublingPolarization : (M × M) ≃ₗ[R] M × M where
  toFun p := (p.1 + p.2, -p.1 + p.2)
  invFun p := (⅟(2 : R) • (p.1 - p.2), ⅟(2 : R) • (p.1 + p.2))
  map_add' p q := by ext <;> simp only [Prod.fst_add, Prod.snd_add, neg_add] <;> abel
  map_smul' c p := by ext <;> simp [smul_add]
  left_inv p := by
    ext <;> dsimp only
    · rw [show p.1 + p.2 - (-p.1 + p.2) = (2 : R) • p.1 by rw [two_smul]; abel, invOf_smul_smul]
    · rw [show p.1 + p.2 + (-p.1 + p.2) = (2 : R) • p.2 by rw [two_smul]; abel, invOf_smul_smul]
  right_inv p := by
    ext <;> dsimp only
    · rw [← smul_add, show p.1 - p.2 + (p.1 + p.2) = (2 : R) • p.1 by rw [two_smul]; abel,
        invOf_smul_smul]
    · rw [← smul_neg, ← smul_add,
        show -(p.1 - p.2) + (p.1 + p.2) = (2 : R) • p.2 by rw [two_smul]; abel, invOf_smul_smul]

variable {R M}

@[simp]
theorem doublingPolarization_apply (p : M × M) :
    doublingPolarization R M p = (p.1 + p.2, -p.1 + p.2) :=
  (rfl)

@[simp]
theorem doublingPolarization_symm_apply (p : M × M) :
    (doublingPolarization R M).symm p = (⅟(2 : R) • (p.1 - p.2), ⅟(2 : R) • (p.1 + p.2)) :=
  (rfl)

variable (R) in
include R in
/-- Every vector of `M × M` is the sum of an antidiagonal and a diagonal vector. -/
theorem exists_eq_antidiagonal_add_diagonal (p : M × M) :
    ∃ x y : M, p = (x, -x) + (y, y) :=
  ⟨_, _, by simpa using ((doublingPolarization R M).apply_symm_apply p).symm⟩

/-- The polarization commutes with the diagonal action of a linear map. -/
theorem doublingPolarization_prodMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (p : M × M) :
    doublingPolarization R M' (f.prodMap f p) = f.prodMap f (doublingPolarization R M p) := by
  simp

end TauCeti

open TauCeti

namespace LinearMap

section Polarization

variable {R S M N : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The antidiagonal and the diagonal of `M × M` are complements once `2` is invertible. -/
theorem isCompl_graph_neg_id_graph_id [Invertible (2 : R)] :
    IsCompl (-LinearMap.id : M →ₗ[R] M).graph (LinearMap.id : M →ₗ[R] M).graph := by
  refine ⟨Submodule.disjoint_def.2 fun p hA hD ↦ ?_, Submodule.codisjoint_iff_exists_add_eq.2
    fun p ↦ ?_⟩
  · have hA' : p.2 = -p.1 := by simpa using hA
    have hD' : p.2 = p.1 := by simpa using hD
    have h2 : (2 : R) • p.1 = 0 := by
      rw [two_smul]; nth_rw 1 [← hD']; rw [hA', neg_add_cancel]
    have h1 : p.1 = 0 := by simpa using congrArg (⅟(2 : R) • ·) h2
    exact Prod.ext h1 (hD'.trans h1)
  · obtain ⟨x, y, rfl⟩ := exists_eq_antidiagonal_add_diagonal R p
    exact ⟨(x, -x), (y, y), by simp, by simp, rfl⟩

variable [CommSemiring S] [AddCommMonoid N] [Module S N]

/-- A semilinear map on `M × M` is determined by its values on the antidiagonal and on the
diagonal. -/
theorem ext_antidiagonal_diagonal [Invertible (2 : R)] {σ : R →+* S} {f g : M × M →ₛₗ[σ] N}
    (hA : ∀ x, f (x, -x) = g (x, -x)) (hD : ∀ x, f (x, x) = g (x, x)) : f = g :=
  ext_on_codisjoint isCompl_graph_neg_id_graph_id.codisjoint
    (fun p hp ↦ by rw [show p = (p.1, -p.1) from Prod.ext rfl (by simpa using hp)]; exact hA _)
    fun p hp ↦ by rw [show p = (p.1, p.1) from Prod.ext rfl (by simpa using hp)]; exact hD _

/-- A form on `M × M` is determined by its four polarization blocks, the values on pairs of
antidiagonal and diagonal vectors. -/
theorem ext₂_antidiagonal_diagonal [Invertible (2 : R)] {I₁ I₂ : R →+* S}
    {B B' : M × M →ₛₗ[I₁] M × M →ₛₗ[I₂] N}
    (hAA : ∀ x y, B (x, -x) (y, -y) = B' (x, -x) (y, -y))
    (hAD : ∀ x y, B (x, -x) (y, y) = B' (x, -x) (y, y))
    (hDA : ∀ x y, B (x, x) (y, -y) = B' (x, x) (y, -y))
    (hDD : ∀ x y, B (x, x) (y, y) = B' (x, x) (y, y)) : B = B' :=
  ext_antidiagonal_diagonal (fun x ↦ ext_antidiagonal_diagonal (hAA x) (hAD x))
    fun x ↦ ext_antidiagonal_diagonal (hDA x) (hDD x)

end Polarization

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {I : R →+* R}

/-- The doubled form `h ⊕ (-h)` on `M × M`:
`doubledForm h (x, y) (x', y') = h x x' - h y y'`. -/
def doubledForm (h : M →ₛₗ[I] M →ₗ[R] R) : M × M →ₛₗ[I] M × M →ₗ[R] R :=
  (h.comp (fst R M M)).compl₂ (fst R M M) - (h.comp (snd R M M)).compl₂ (snd R M M)

variable (h : M →ₛₗ[I] M →ₗ[R] R)

@[simp]
theorem doubledForm_apply (p q : M × M) : doubledForm h p q = h p.1 q.1 - h p.2 q.2 :=
  (rfl)

/-- For a bilinear form, the doubled form is the product of the form with its negative. -/
theorem doubledForm_eq_prod_neg (h : LinearMap.BilinForm R M) : doubledForm h = h.prod (-h) :=
  ext₂ fun p q ↦ by simp [sub_eq_add_neg]

/-- The diagonal is isotropic for the doubled form. -/
theorem doubledForm_diagonal_diagonal (x y : M) : doubledForm h (x, x) (y, y) = 0 := by
  simp

/-- The antidiagonal is isotropic for the doubled form. -/
theorem doubledForm_antidiagonal_antidiagonal (x y : M) :
    doubledForm h (x, -x) (y, -y) = 0 := by
  simp

/-- An antidiagonal and a diagonal vector pair through `2 h`. -/
theorem doubledForm_antidiagonal_diagonal (x y : M) :
    doubledForm h (x, -x) (y, y) = 2 * h x y := by
  simp [two_mul]

/-- A diagonal and an antidiagonal vector pair through `2 h`. -/
theorem doubledForm_diagonal_antidiagonal (x y : M) :
    doubledForm h (x, x) (y, -y) = 2 * h x y := by
  simp [two_mul]

/-- The doubled form is hermitian exactly when the form is. -/
@[simp]
theorem isSymm_doubledForm_iff : (doubledForm h).IsSymm ↔ h.IsSymm := by
  refine ⟨fun hW ↦ ⟨fun x y ↦ ?_⟩, fun hh ↦ ⟨fun p q ↦ ?_⟩⟩
  · simpa using hW.eq (x, 0) (y, 0)
  · simp [hh.eq]

/-- The doubled form is left separating exactly when the form is. -/
@[simp]
theorem separatingLeft_doubledForm_iff : (doubledForm h).SeparatingLeft ↔ h.SeparatingLeft := by
  refine ⟨fun hW x hx ↦ ?_, fun hh p hp ↦ Prod.ext (hh _ fun y ↦ ?_) (hh _ fun y ↦ ?_)⟩
  · simpa using congrArg Prod.fst (hW (x, 0) fun q ↦ by simp [hx])
  · simpa using hp (y, 0)
  · simpa using hp (0, y)

/-- The doubled form is right separating exactly when the form is. -/
@[simp]
theorem separatingRight_doubledForm_iff :
    (doubledForm h).SeparatingRight ↔ h.SeparatingRight := by
  refine ⟨fun hW y hy ↦ ?_, fun hh q hq ↦ Prod.ext (hh _ fun x ↦ ?_) (hh _ fun x ↦ ?_)⟩
  · simpa using congrArg Prod.fst (hW (y, 0) fun p ↦ by simp [hy])
  · simpa using hq (x, 0)
  · simpa using hq (0, x)

/-- The doubled form is nondegenerate exactly when the form is. -/
@[simp]
theorem nondegenerate_doubledForm_iff : (doubledForm h).Nondegenerate ↔ h.Nondegenerate := by
  simp [Nondegenerate]

/-- The diagonal is contained in its orthogonal for the doubled form. -/
theorem graph_id_le_orthogonalBilin_doubledForm :
    (LinearMap.id : M →ₗ[R] M).graph ≤ (LinearMap.id.graph).orthogonalBilin (doubledForm h) := by
  rintro ⟨y, y'⟩ hy ⟨x, x'⟩ hx
  simp only [mem_graph_iff, id_coe, id_eq] at hx hy
  subst hx hy
  simp

/-- The antidiagonal is contained in its orthogonal for the doubled form. -/
theorem graph_neg_id_le_orthogonalBilin_doubledForm :
    (-LinearMap.id : M →ₗ[R] M).graph ≤
      ((-LinearMap.id).graph).orthogonalBilin (doubledForm h) := by
  rintro ⟨y, y'⟩ hy ⟨x, x'⟩ hx
  simp only [mem_graph_iff] at hx hy
  subst hx hy
  simp

/-- For a right-separating form, the diagonal is its own orthogonal for the doubled form: it is a
maximal isotropic submodule. -/
theorem orthogonalBilin_doubledForm_graph_id (hh : h.SeparatingRight) :
    (LinearMap.id.graph).orthogonalBilin (doubledForm h) = (LinearMap.id : M →ₗ[R] M).graph := by
  refine le_antisymm (fun q hq ↦ ?_) (graph_id_le_orthogonalBilin_doubledForm h)
  have hq' : ∀ x, h x (q.1 - q.2) = 0 := fun x ↦ by
    simpa [sub_eq_zero, map_sub] using hq (x, x) (by simp)
  simpa [sub_eq_zero, eq_comm] using hh _ hq'

/-- For a right-separating form, the antidiagonal is its own orthogonal for the doubled form: it
is a maximal isotropic submodule. -/
theorem orthogonalBilin_doubledForm_graph_neg_id (hh : h.SeparatingRight) :
    ((-LinearMap.id).graph).orthogonalBilin (doubledForm h) =
      (-LinearMap.id : M →ₗ[R] M).graph := by
  refine le_antisymm (fun q hq ↦ ?_) (graph_neg_id_le_orthogonalBilin_doubledForm h)
  have hq' : ∀ x, h x (q.1 + q.2) = 0 := fun x ↦ by
    simpa [map_add] using hq (x, -x) (by simp)
  simpa [add_eq_zero_iff_eq_neg'] using hh _ hq'

/-- Two linear maps `f g : M → M'` that both scale the forms by a common multiplier `c`,
`h' (f x) (f y) = c * h x y`, induce blockwise a map `M × M → M' × M'` scaling the doubled forms
by `c`. For `c = 1` and isometries of `h` this is the embedding `U(V) × U(-V) → U(V ⊕ (-V))`;
for general `c` it is the equal-multiplier embedding of similitude groups. -/
theorem doubledForm_prodMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (h' : M' →ₛₗ[I] M' →ₗ[R] R) {f g : M →ₗ[R] M'} {c : R}
    (hf : ∀ x y, h' (f x) (f y) = c * h x y) (hg : ∀ x y, h' (g x) (g y) = c * h x y)
    (p q : M × M) :
    doubledForm h' (f.prodMap g p) (f.prodMap g q) = c * doubledForm h p q := by
  simp [hf, hg, mul_sub]

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- In the product basis, the Gram matrix of the doubled form is `diag(H, -H)`. -/
theorem toMatrix₂_doubledForm (b : Module.Basis ι R M) :
    toMatrix₂ (b.prod b) (b.prod b) (doubledForm h) =
      Matrix.fromBlocks (toMatrix₂ b b h) 0 0 (-toMatrix₂ b b h) := by
  ext (i | i) (j | j) <;> simp [toMatrix₂_apply, Module.Basis.prod_apply]

/-- In the polarized basis, antidiagonal vectors first and diagonal vectors second, the Gram
matrix of the doubled form has zero diagonal blocks and off-diagonal blocks `2 H`. -/
theorem toMatrix₂_doubledForm_polarization [Invertible (2 : R)] (b : Module.Basis ι R M) :
    toMatrix₂ ((b.prod b).map (doublingPolarization R M))
        ((b.prod b).map (doublingPolarization R M)) (doubledForm h) =
      Matrix.fromBlocks 0 (2 • toMatrix₂ b b h) (2 • toMatrix₂ b b h) 0 := by
  ext (i | i) (j | j) <;>
    simp [toMatrix₂_apply, Module.Basis.prod_apply, sub_eq_add_neg, two_mul]

end Matrix

end LinearMap
