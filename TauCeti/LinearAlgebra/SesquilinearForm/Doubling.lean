/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import TauCeti.LinearAlgebra.BilinearForm.Prod
public import TauCeti.LinearAlgebra.Prod

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
`TauCeti.doublingPolarization` with inverse `(u, v) ↦ (½ (u - v), ½ (u + v))`; this
form-independent polarization API lives in `TauCeti.LinearAlgebra.Prod`. In a basis of
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
* `LinearMap.toMatrix₂_doubledForm`, `LinearMap.toMatrix₂_doubledForm_polarization`: the Gram
  matrices of the doubled form.
* `LinearMap.doubledForm_prodMap`: two linear maps scaling `h` by a common factor `c` act
  blockwise on `M × M`, scaling the doubled form by `c`; this is the identity underlying the
  block embeddings of isometry and similitude groups.

## References

* E. Eischen, M. Harris, J.-S. Li, C. Skinner, *p-adic L-functions for unitary groups*,
  Forum Math. Pi 8 (2020), §4.1.1.
* S. Gelbart, I. Piatetski-Shapiro, S. Rallis, *Explicit constructions of automorphic
  L-functions*, Lecture Notes in Math. 1254, Springer, 1987.
-/

public section

open TauCeti

namespace LinearMap

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
by `c`. The maps need not be invertible and `c` may be any scalar, so this is only the pairing
identity behind the group embeddings: specialized to `h' = h`, with `f` and `g` automorphisms
of `M` and `c = 1`, it shows that `U(V) × U(-V)` acts on `V ⊕ (-V)` by isometries, and for
automorphisms with a common invertible multiplier `c` it gives the equal-multiplier embedding of
similitude groups. -/
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
