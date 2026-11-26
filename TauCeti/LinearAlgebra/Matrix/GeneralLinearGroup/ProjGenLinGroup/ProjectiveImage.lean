/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# The projective image of a matrix representation

For a group homomorphism `ρ : G →* GL(n, R)`, its projective image is the image of the
composite `G → GL(n, R) → PGL(n, R)`, that is, the image of `ρ` modulo scalar matrices. Large
image hypotheses on two-dimensional Galois representations are phrased through this subgroup of
`PGL(2, R)`: it is insensitive to scalar twists, and it is the subgroup that is compared with the
images of `PSL(2, k)` and `PGL(2, k)` for a finite field `k`.

This file characterizes membership in the projective image and its kernel, the preimage under `ρ`
of the scalar matrices, compares the projective image of a restriction of `ρ` with that of `ρ`, and
records how the projective image transforms when `ρ` is conjugated by an invertible
matrix (it is conjugated by the class of that matrix) and when the coefficients are changed along
a ring homomorphism (it is mapped along the induced map of projective general linear groups).

## Main declarations

* `MonoidHom.projectiveImage`: the image of `ρ` in `PGL(n, R)`.
* `MonoidHom.projectiveImage_def`: the projective image as the range of the composite.
* `MonoidHom.mem_projectiveImage`: membership in the projective image.
* `MonoidHom.mk_mem_projectiveImage_iff`: the class of `A` lies in the projective image exactly
  when `A` is a scalar multiple of a value of `ρ`.
* `MonoidHom.ker_mk_comp`, `MonoidHom.mk_apply_eq_one_iff`: the kernel of `G → PGL(n, R)` is the
  preimage of the scalar matrices.
* `MonoidHom.projectiveImage_eq_bot_iff`: the projective image is trivial exactly when `ρ` is
  scalar-valued.
* `MonoidHom.projectiveImage_comp_le`, `MonoidHom.projectiveImage_comp_subtype`: restriction can
  only shrink the projective image, which for a subgroup is its image in `PGL(n, R)`.
* `MonoidHom.projectiveImage_conj`: conjugating `ρ` conjugates its projective image.
* `MonoidHom.projectiveImage_map`: extending scalars maps the projective image.
* `MonoidHom.projectiveImage_eq_top_of_surjective`: a surjective `ρ` has projective image `⊤`.
-/

public section

open scoped MatrixGroups Pointwise

open Matrix

namespace MonoidHom

variable {G : Type*} [Group G] {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
  (ρ : G →* GL n R)

/-- The projective image of a matrix representation `ρ : G →* GL(n, R)`: the image of the
composite of `ρ` with the quotient map `GL(n, R) → PGL(n, R)`. -/
def projectiveImage : Subgroup PGL(n, R) :=
  (ProjGenLinGroup.mk.comp ρ).range

/-- Unfolds the projective image as the range of the composite `G → GL(n, R) → PGL(n, R)`. -/
theorem projectiveImage_def : ρ.projectiveImage = (ProjGenLinGroup.mk.comp ρ).range :=
  (rfl)

@[simp]
theorem mem_projectiveImage {x : PGL(n, R)} :
    x ∈ ρ.projectiveImage ↔ ∃ g, ProjGenLinGroup.mk (ρ g) = x :=
  Iff.rfl

theorem mk_mem_projectiveImage (g : G) : ProjGenLinGroup.mk (ρ g) ∈ ρ.projectiveImage :=
  ⟨g, rfl⟩

/-- The projective image is the image of the range of `ρ` under the quotient map. -/
theorem projectiveImage_eq_map_range : ρ.projectiveImage = ρ.range.map ProjGenLinGroup.mk :=
  range_comp ProjGenLinGroup.mk ρ

/-- The class of an invertible matrix `A` lies in the projective image of `ρ` exactly when `A` is
a scalar multiple of some `ρ g`. -/
theorem mk_mem_projectiveImage_iff {A : GL n R} :
    ProjGenLinGroup.mk A ∈ ρ.projectiveImage ↔
      ∃ g, ∃ u : Rˣ, ρ g * GeneralLinearGroup.scalar n u = A := by
  simp [ProjGenLinGroup.mk_eq_mk_iff]

/-- The kernel of the projective representation `G → PGL(n, R)` is the preimage under `ρ` of the
scalar matrices. -/
theorem ker_mk_comp :
    (ProjGenLinGroup.mk.comp ρ).ker = (GeneralLinearGroup.scalar n).range.comap ρ := by
  rw [← comap_ker, ProjGenLinGroup.ker_mk, GeneralLinearGroup.center_eq_range_scalar]

/-- `g` maps to the identity of `PGL(n, R)` exactly when `ρ g` is a scalar matrix. -/
theorem mk_apply_eq_one_iff {g : G} :
    ProjGenLinGroup.mk (ρ g) = 1 ↔ ∃ u : Rˣ, GeneralLinearGroup.scalar n u = ρ g := by
  rw [← comp_apply, ← mem_ker, ker_mk_comp, Subgroup.mem_comap, mem_range]

/-- The projective image is trivial exactly when `ρ` takes only scalar values. -/
theorem projectiveImage_eq_bot_iff :
    ρ.projectiveImage = ⊥ ↔ ∀ g, ∃ u : Rˣ, GeneralLinearGroup.scalar n u = ρ g := by
  simp only [projectiveImage_def, range_eq_bot_iff, MonoidHom.ext_iff, one_apply, comp_apply,
    mk_apply_eq_one_iff]

/-- The trivial representation has trivial projective image. -/
@[simp]
theorem projectiveImage_one : (1 : G →* GL n R).projectiveImage = ⊥ := by
  simp [projectiveImage_def]

/-- Precomposing with a homomorphism `f : H →* G`, for instance restricting to a subgroup, can
only shrink the projective image. -/
theorem projectiveImage_comp_le {H : Type*} [Group H] (f : H →* G) :
    (ρ.comp f).projectiveImage ≤ ρ.projectiveImage := by
  rintro _ ⟨h, rfl⟩
  exact ⟨f h, rfl⟩

/-- The projective image of the restriction of `ρ` to a subgroup `K` is the image of `K` in
`PGL(n, R)`. -/
theorem projectiveImage_comp_subtype (K : Subgroup G) :
    (ρ.comp K.subtype).projectiveImage = K.map (ProjGenLinGroup.mk.comp ρ) := by
  rw [projectiveImage_def, ← comp_assoc, range_comp, Subgroup.range_subtype]

/-- Conjugating a matrix representation by `g` conjugates its projective image by the class
of `g`. -/
@[simp]
theorem projectiveImage_conj (g : GL n R) :
    ((MulAut.conj g : GL n R →* GL n R).comp ρ).projectiveImage =
      MulAut.conj (ProjGenLinGroup.mk g) • ρ.projectiveImage := by
  ext x
  simp [Subgroup.mem_smul_pointwise_iff_exists]

/-- Extending the scalars of a matrix representation along `f : R →+* S` maps its projective
image along the induced homomorphism `PGL(n, R) →* PGL(n, S)`. -/
@[simp]
theorem projectiveImage_map {S : Type*} [CommRing S] (f : R →+* S) :
    ((GeneralLinearGroup.map f).comp ρ).projectiveImage =
      ρ.projectiveImage.map (ProjGenLinGroup.map f) := by
  ext x
  simp

/-- A surjective matrix representation has full projective image. -/
theorem projectiveImage_eq_top_of_surjective {ρ : G →* GL n R} (hρ : Function.Surjective ρ) :
    ρ.projectiveImage = ⊤ :=
  range_eq_top.2 (ProjGenLinGroup.mk_surjective.comp hρ)

end MonoidHom
