/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.GroupTheory.Perm.Inversion
public import TauCeti.LinearAlgebra.Orientation.Basis
import TauCeti.LinearAlgebra.Orientation.Basic
import TauCeti.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Ray

/-!
# Products of finitely many linear orientations

Let `E 0, …, E (k - 1)` be finite free modules of ranks `n 0, …, n (k - 1)` with orientations
`o i`. The product orientation `Orientation.pi o` of `∀ i, E i` lists the factors in the order of
`Fin k`: on product bases it is the orientation of the basis that lists a basis of `E 0`, then
one of `E 1`, and so on (`Orientation.pi_basis_orientation`). It is the `k`-factor version of
`Orientation.prod`, and it is built in the same way, from relative basis signs and the
determinants of product bases, so that zero-dimensional factors keep both of their orientations.

Listing the factors in another order changes the product orientation by a sign. For a permutation
`σ` of `Fin k`, the product orientation of `E (σ 0), …, E (σ (k - 1))`, transported to `∀ i, E i`
along `LinearEquiv.piCongrLeft`, is `(-1) ^ N` times the product orientation of
`E 0, …, E (k - 1)`, where `N` is the sum of `n (σ i) * n (σ j)` over the pairs `i < j` whose
order `σ` reverses (`Orientation.map_piCongrLeft_pi`). The sign is that of the permutation
`TauCeti.blockPerm σ n` of the listed basis vectors, which moves blocks of basis vectors past each
other.

In particular, when every factor has even dimension the product orientation does not depend on
the order of the factors (`Orientation.map_piCongrLeft_pi_of_even`). This is the permutation law
for orientations assembled from even-dimensional pieces, such as complex vector spaces with their
complex orientations or the real tangent spaces of a four-manifold. For instance, an orientation
built from one such piece for each of `k` labelled point constraints, as in the count of
pseudoholomorphic curves through `k` points of a symplectic four-manifold, does not depend on how
the points are labelled.

## Main definitions

* `Orientation.pi o hn`: the product orientation of `∀ i, E i`, indexed by `Fin (∑ i, n i)`.

## Main results

* `Orientation.pi_eq_rayOfNeZero` and `Orientation.pi_eq_units_smul`: the product orientation
  computed in arbitrary factor bases, using their relative signs.
* `Orientation.pi_basis_orientation`: the product of basis orientations is the orientation of
  the ordered product basis.
* `Orientation.pi_update_neg`: reversing one factor reverses the product orientation.
* `Orientation.map_piCongrLeft_pi`: reordering the factors multiplies the product orientation by
  the sign of the block permutation.
* `Orientation.map_piCongrLeft_pi_of_even`: for even-dimensional factors, reordering them does not
  change the product orientation.
-/

public section
noncomputable section

open Module Finset

namespace Orientation

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {k : ℕ}
  {E : Fin k → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)] {n : Fin k → ℕ}

private theorem prod_signBasis_smul_det_ne_zero (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (b : ∀ i, Basis (Fin (n i)) R (E i)) :
    (∏ i, (signBasis (o i) (b i) : R)) • ((Pi.basis b).reindex finSigmaFinEquiv).det ≠ 0 :=
  smul_ne_zero (prod_ne_zero_iff.2 fun i _ ↦ by exact_mod_cast (signBasis (o i) (b i)).ne_zero)
    (Basis.det_ne_zero _)

private def piOfBases (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (b : ∀ i, Basis (Fin (n i)) R (E i)) : Orientation R (∀ i, E i) (Fin (∑ i, n i)) :=
  rayOfNeZero R _ (prod_signBasis_smul_det_ne_zero o b)

private theorem piOfBases_eq (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (b b' : ∀ i, Basis (Fin (n i)) R (E i)) : piOfBases o b = piOfBases o b' := by
  unfold piOfBases
  rw [ray_eq_iff]
  set B := (Pi.basis b).reindex finSigmaFinEquiv
  set B' := (Pi.basis b').reindex finSigmaFinEquiv
  have hdet : B.det B' = ∏ i, (b i).det (b' i) := by
    rw [Basis.det_reindex, ← Basis.det_pi]
    congr 1
    funext x
    simp [B']
  rw [B.det.eq_smul_basis_det B', smul_smul, hdet]
  apply sameRay_smul_smul_of_mul_nonneg
  have hpos := prod_pos fun i (_ : i ∈ univ) ↦ signBasis_mul_det_mul_pos (o i) (b i) (b' i)
  rw [prod_mul_distrib, prod_mul_distrib] at hpos
  exact hpos.le

variable [∀ i, Module.Free R (E i)] [∀ i, Module.Finite R (E i)]

/-- The product orientation of `∀ i, E i`, listing the factors `E 0, …, E (k - 1)` in this order.
Both orientations of each factor are retained, including in dimension zero. -/
def pi (o : ∀ i, Orientation R (E i) (Fin (n i))) (hn : ∀ i, finrank R (E i) = n i) :
    Orientation R (∀ i, E i) (Fin (∑ i, n i)) :=
  piOfBases o fun i ↦ Module.finBasisOfFinrankEq R (E i) (hn i)

/-- The product orientation can be computed in any factor bases using their relative signs. -/
theorem pi_eq_rayOfNeZero (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (hn : ∀ i, finrank R (E i) = n i) (b : ∀ i, Basis (Fin (n i)) R (E i)) :
    pi o hn = rayOfNeZero R ((∏ i, (signBasis (o i) (b i) : R)) •
      ((Pi.basis b).reindex finSigmaFinEquiv).det) (smul_ne_zero
        (prod_ne_zero_iff.2 fun i _ ↦ by exact_mod_cast (signBasis (o i) (b i)).ne_zero)
        (Basis.det_ne_zero _)) :=
  piOfBases_eq o _ b

/-- The product orientation is the orientation of the ordered product of any factor bases,
multiplied by the product of the signs of these bases relative to the factor orientations. -/
theorem pi_eq_units_smul (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (hn : ∀ i, finrank R (E i) = n i) (b : ∀ i, Basis (Fin (n i)) R (E i)) :
    pi o hn = Units.map (Int.castRingHom R).toMonoidHom (∏ i, signBasis (o i) (b i)) •
      ((Pi.basis b).reindex finSigmaFinEquiv).orientation := by
  rw [pi_eq_rayOfNeZero o hn b, Basis.orientation, smul_rayOfNeZero]
  simp [Units.smul_def]

/-- The product of basis orientations is the orientation of the ordered product basis. -/
@[simp]
theorem pi_basis_orientation (b : ∀ i, Basis (Fin (n i)) R (E i))
    (hn : ∀ i, finrank R (E i) = n i) :
    pi (fun i ↦ (b i).orientation) hn = ((Pi.basis b).reindex finSigmaFinEquiv).orientation := by
  simp [pi_eq_units_smul _ hn b]

/-- Reversing the orientation of one factor reverses the product orientation, including for a
zero-dimensional factor. -/
@[simp]
theorem pi_update_neg (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (hn : ∀ i, finrank R (E i) = n i) (j : Fin k) :
    pi (Function.update o j (-o j)) hn = -pi o hn := by
  let b (i : Fin k) := Module.finBasisOfFinrankEq R (E i) (hn i)
  have hs : ∏ i, signBasis (Function.update o j (-o j) i) (b i) = -∏ i, signBasis (o i) (b i) := by
    rw [← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ _ (mem_univ j),
      Function.update_self, signBasis_neg, neg_mul]
    congr 2
    exact prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [pi_eq_units_smul _ hn b, pi_eq_units_smul o hn b, hs]
  rcases Int.units_eq_one_or (∏ i, signBasis (o i) (b i)) with hu | hu
  · simp [hu, Module.Ray.neg_units_smul]
  · have hm : Units.map (Int.castRingHom R).toMonoidHom (-1) = -1 := Units.ext (by simp)
    rw [hu, neg_neg, map_one, one_smul, hm, Module.Ray.neg_units_smul, one_smul]
    exact (neg_neg ((Pi.basis b).reindex finSigmaFinEquiv).orientation).symm

/-- **Reordering the factors of a product orientation.** For a permutation `σ` of `Fin k`, the
product orientation of `E (σ 0), …, E (σ (k - 1))`, transported to `∀ i, E i`, is the product
orientation of `E 0, …, E (k - 1)` multiplied by `(-1) ^ N`, where `N` is the sum of
`n (σ i) * n (σ j)` over the pairs `i < j` whose order `σ` reverses. The index types are identified
through `∑ i, n (σ i) = ∑ i, n i`. -/
theorem map_piCongrLeft_pi (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (hn : ∀ i, finrank R (E i) = n i) (σ : Equiv.Perm (Fin k)) :
    Orientation.map (Fin (∑ i, n (σ i))) (LinearEquiv.piCongrLeft R E σ)
        (pi (fun i ↦ o (σ i)) fun i ↦ hn (σ i)) =
      (-1 : Rˣ) ^ (∑ p ∈ univ.inversions σ, n (σ p.1) * n (σ p.2)) •
        Orientation.reindex R (∀ i, E i) (finCongr (Equiv.sum_comp σ n).symm) (pi o hn) := by
  let b (i : Fin k) := Module.finBasisOfFinrankEq R (E i) (hn i)
  set h := Equiv.sum_comp σ n
  -- Transporting the ordered product basis of the `b (σ i)` gives the ordered product basis of the
  -- `b i`, with its basis vectors permuted by the block permutation.
  set π : Equiv.Perm (Fin (∑ i, n (σ i))) :=
    ((finCongr h).symm.permCongr (TauCeti.blockPerm σ n)).symm
  have he : ((Pi.basis fun i ↦ b (σ i)).reindex finSigmaFinEquiv).map
      (LinearEquiv.piCongrLeft R E σ) =
      (((Pi.basis b).reindex finSigmaFinEquiv).reindex (finCongr h.symm)).reindex π := by
    refine Basis.eq_of_apply_eq fun x ↦ ?_
    obtain ⟨⟨i, a⟩, rfl⟩ := finSigmaFinEquiv.surjective x
    simp [π, Equiv.permCongr_apply]
  have hsign : Units.map (Int.castRingHom R).toMonoidHom (Equiv.Perm.sign π) =
      (-1 : Rˣ) ^ (∑ p ∈ univ.inversions σ, n (σ p.1) * n (σ p.2)) := by
    simp [π, TauCeti.sign_blockPerm]
  -- The statement for the basis orientations.
  have key : Orientation.map (Fin (∑ i, n (σ i))) (LinearEquiv.piCongrLeft R E σ)
      ((Pi.basis fun i ↦ b (σ i)).reindex finSigmaFinEquiv).orientation =
      (-1 : Rˣ) ^ (∑ p ∈ univ.inversions σ, n (σ p.1) * n (σ p.2)) •
        Orientation.reindex R (∀ i, E i) (finCongr h.symm)
          ((Pi.basis b).reindex finSigmaFinEquiv).orientation := by
    rw [← Basis.orientation_map, he, Basis.orientation_reindex, Basis.orientation_reindex,
      reindex_perm, hsign]
  -- The general statement differs by the product of the relative signs of the factor bases.
  have hs : ∏ i, signBasis (o (σ i)) (b (σ i)) = ∏ i, signBasis (o i) (b i) :=
    Equiv.prod_comp σ fun i ↦ signBasis (o i) (b i)
  rw [pi_eq_units_smul o hn b, pi_eq_units_smul _ _ fun i ↦ b (σ i), hs]
  rcases Int.units_eq_one_or (∏ i, signBasis (o i) (b i)) with hu | hu
  · simpa [hu] using key
  · simp [hu, Module.Ray.neg_units_smul, Orientation.map_neg, Orientation.reindex_neg, key,
      Module.Ray.units_smul_neg]

/-- **Reordering factors of even dimension.** If every factor has even dimension, the product
orientation does not depend on the order in which the factors are listed: for every permutation
`σ` of `Fin k`, the product orientation of `E (σ 0), …, E (σ (k - 1))`, transported to
`∀ i, E i`, is the product orientation of `E 0, …, E (k - 1)`. -/
theorem map_piCongrLeft_pi_of_even (o : ∀ i, Orientation R (E i) (Fin (n i)))
    (hn : ∀ i, finrank R (E i) = n i) (σ : Equiv.Perm (Fin k)) (hev : ∀ i, Even (n i)) :
    Orientation.map (Fin (∑ i, n (σ i))) (LinearEquiv.piCongrLeft R E σ)
        (pi (fun i ↦ o (σ i)) fun i ↦ hn (σ i)) =
      Orientation.reindex R (∀ i, E i) (finCongr (Equiv.sum_comp σ n).symm) (pi o hn) := by
  rw [map_piCongrLeft_pi, Even.neg_one_pow (even_sum _ fun p _ ↦ (hev _).mul_right _), one_smul]

end Orientation
