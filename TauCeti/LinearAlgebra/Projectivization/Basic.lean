/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan, Zayn Blore
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Normalized representatives of projective points

A projective point represented by a tuple can be normalized at any nonzero coordinate.
The resulting representative has that coordinate equal to `1`, and its other coordinates
are the corresponding ratios. This gives affine coordinates without a finiteness assumption
on the index type.

The file also describes the fibres of `Projectivization.mk'` as orbits of the units of the
scalar ring: two nonzero vectors give the same point exactly when one is a unit multiple of the
other (`Projectivization.mk'_eq_mk'_iff`), so the saturation of a set of nonzero vectors is the
union of its unit translates (`Projectivization.preimage_image_mk'`). These two lemmas are
from Zayn Blore's Mathlib pull request
[mathlib4#44117](https://github.com/leanprover-community/mathlib4/pull/44117).

The file also records `Projectivization.submodule_map`: the line of the image of a projective
point under an injective semilinear map is the image of its line.

The normalization lemmas are adapted from Ralf Stephan's `ArithmeticHeights/Northcott.lean` in
[`rwst/Subspace-Theorems`](https://github.com/rwst/Subspace-Theorems/blob/e443c2479e19f7665b31d8e94e2317c8ced1ca06/ArithmeticHeights/Northcott.lean),
commit `e443c2479e19f7665b31d8e94e2317c8ced1ca06` (Apache 2.0).
-/

public section

namespace Projectivization

section DivisionRing

variable (K : Type*) {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Two nonzero vectors have the same image under `mk'` iff one is a unit multiple of the other,
for the action of `Kˣ` on `{ v : V // v ≠ 0 }`. -/
theorem mk'_eq_mk'_iff (v w : { v : V // v ≠ 0 }) :
    mk' K v = mk' K w ↔ ∃ a : Kˣ, a • w = v := by
  simp only [mk'_eq_mk, mk_eq_mk_iff, Subtype.ext_iff, Units.smul_coe]

/-- The saturation of a set of nonzero vectors under `mk'` is the union of its translates by the
units of `K`. -/
theorem preimage_image_mk' (U : Set { v : V // v ≠ 0 }) :
    mk' K ⁻¹' (mk' K '' U) = ⋃ a : Kˣ, (a • ·) '' U := by
  ext v
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion, mk'_eq_mk'_iff]
  constructor
  · rintro ⟨_, hw, a, rfl⟩
    exact ⟨a⁻¹, _, hw, inv_smul_smul a v⟩
  · rintro ⟨a, w, hw, rfl⟩
    exact ⟨w, hw, a⁻¹, inv_smul_smul a w⟩

end DivisionRing

variable {K : Type*} [Field K] {ι : Type*}

/-- At any nonzero coordinate of a projective point, there is a representative normalized
to `1` whose coordinates are the ratios of the chosen representative's coordinates. -/
lemma exists_rep_apply_eq_one_of_ne_zero (x : Projectivization K (ι → K)) {i : ι}
    (hi : x.rep i ≠ 0) :
    ∃ (v : ι → K) (hv : v ≠ 0), v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧ mk K v hv = x := by
  refine ⟨(x.rep i)⁻¹ • x.rep, smul_ne_zero (inv_ne_zero hi) x.rep_nonzero,
    inv_mul_cancel₀ hi, fun j ↦ (div_eq_inv_mul _ _).symm, ?_⟩
  conv_rhs => rw [← x.mk_rep]
  exact (mk_eq_mk_iff' K _ _ _ x.rep_nonzero).mpr ⟨_, rfl⟩

/-- Every projective point has a representative with some coordinate equal to `1`,
and its coordinates are the ratios at that coordinate. -/
lemma exists_rep_apply_eq_one (x : Projectivization K (ι → K)) :
    ∃ (v : ι → K) (hv : v ≠ 0) (i : ι), v i = 1 ∧ (∀ j, v j = x.rep j / x.rep i) ∧
      mk K v hv = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp x.rep_nonzero
  obtain ⟨v, hv, h1, hratio, hmk⟩ := exists_rep_apply_eq_one_of_ne_zero x hi
  exact ⟨v, hv, i, h1, hratio, hmk⟩

/-- The line of the image of a projective point under an injective semilinear map is the image
of its line. -/
@[simp]
theorem submodule_map {D E V W : Type*} [DivisionRing D] [DivisionRing E] [AddCommGroup V]
    [Module D V] [AddCommGroup W] [Module E W] {σ : D →+* E} [RingHomSurjective σ]
    (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (x : Projectivization D V) :
    (map f hf x).submodule = x.submodule.map f := by
  induction x using ind with
  | h v hv => simp [map_mk, submodule_mk, Submodule.map_span]

end Projectivization
