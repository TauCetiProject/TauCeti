/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
import TauCeti.LinearAlgebra.RootSystem.Flip
import TauCeti.LinearAlgebra.RootSystem.InvariantForm.Hom

/-!
# Canonical bilinear forms and anisotropy of direct sums of root pairings

For a finite family of finite root pairings `P : ∀ c, RootPairing (ι c) R (M c) (N c)`, the
canonical bilinear form `RootForm` and coroot form `CorootForm` of the external direct sum
`RootPairing.pi P` and internal direct sum `RootPairing.internalDirectSum hEi hEt P` decompose as
orthogonal sums of the summands' canonical forms. In particular, both external and internal direct
sums preserve anisotropy (`IsAnisotropic`).

## Main results

* `RootPairing.pi_polarization_apply`: coordinate formula for the polarization of
  `RootPairing.pi P`.
* `RootPairing.pi_rootForm_apply_apply` and `RootPairing.pi_corootForm_apply_apply`: orthogonal
  sum decompositions for the canonical forms of `RootPairing.pi P`.
* `RootPairing.isAnisotropic_pi`: anisotropy of finite external direct sums.
* `RootPairing.internalDirectSum_rootForm_apply_apply` and
  `RootPairing.internalDirectSum_corootForm_apply_apply`: orthogonal sum decompositions for the
  canonical forms of `RootPairing.internalDirectSum hEi hEt P`.
* `RootPairing.isAnisotropic_internalDirectSum`: anisotropy of finite internal direct sums.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

open TauCeti

namespace RootPairing

section External

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (M c) (N c)) [∀ c, Fintype (ι c)]

@[simp]
theorem pi_polarization_apply (x : ∀ c, M c) (c : κ) :
    (pi P).Polarization x c = (P c).Polarization (x c) := by
  simp only [Polarization_apply, Fintype.sum_sigma, Finset.sum_apply, Pi.smul_apply, pi_coroot,
    pi_coroot'_apply]
  rw [Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
  · simp
  · intro d _ hdc
    simp [Pi.single_eq_of_ne (Ne.symm hdc)]

/-- **The canonical bilinear form of a finite direct sum is the orthogonal sum of the summands'
canonical forms.** -/
@[simp]
theorem pi_rootForm_apply_apply (x y : ∀ c, M c) :
    (pi P).RootForm x y = ∑ c, (P c).RootForm (x c) (y c) := by
  simp only [rootForm_apply_apply, Fintype.sum_sigma, pi_coroot'_apply]

/-- **The canonical coroot bilinear form of a finite direct sum is the orthogonal sum of the
summands' coroot forms.** -/
@[simp]
theorem pi_corootForm_apply_apply (x y : ∀ c, N c) :
    (pi P).CorootForm x y = ∑ c, (P c).CorootForm (x c) (y c) := by
  dsimp only [CorootForm]
  rw [pi_flip, pi_rootForm_apply_apply]

/-- A finite direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_pi [∀ c, (P c).IsAnisotropic] : (pi P).IsAnisotropic where
  rootForm_root_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_rootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.rootForm_root_ne_zero (P := P c) i
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]
  corootForm_coroot_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_corootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]

end External

section Internal

variable {κ R M : Type*} [Fintype κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (E c) (N c)) [∀ c, Fintype (ι c)]

/-- **The canonical bilinear form of an internal direct sum is the orthogonal sum of the summands'
canonical forms along `TauCeti.internalProjection`.** -/
@[simp]
theorem internalDirectSum_rootForm_apply_apply (x y : M) :
    (internalDirectSum hEi hEt P).RootForm x y =
      ∑ c, (P c).RootForm (internalProjection hEi hEt c x) (internalProjection hEi hEt c y) := by
  let _ : DecidableEq κ := Classical.decEq κ
  rw [← (piEquivInternalDirectSum hEi hEt P).symm.toHom.rootForm_weightMap,
    pi_rootForm_apply_apply]
  simp [Equiv.inv_weightMap]

/-- **The canonical coroot bilinear form of an internal direct sum is the orthogonal sum of the
summands' coroot forms on the coordinates of
`(piEquivInternalDirectSum hEi hEt P).coweightMap`.** -/
@[simp]
theorem internalDirectSum_corootForm_apply_apply [DecidableEq κ] (f g : Module.Dual R M) :
    (internalDirectSum hEi hEt P).CorootForm f g =
      ∑ c, (P c).CorootForm
        ((piEquivInternalDirectSum hEi hEt P).coweightMap f c)
        ((piEquivInternalDirectSum hEi hEt P).coweightMap g c) := by
  dsimp only [CorootForm]
  rw [← (piEquivInternalDirectSum hEi hEt P).toHom.flip.rootForm_weightMap]
  simp

/-- A finite internal direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_internalDirectSum [∀ c, (P c).IsAnisotropic] :
    (internalDirectSum hEi hEt P).IsAnisotropic where
  rootForm_root_ne_zero s := by
    let _ : DecidableEq κ := Classical.decEq κ
    rw [← (piEquivInternalDirectSum hEi hEt P).symm.toHom.rootForm_weightMap,
      Hom.root_weightMap_apply]
    exact IsAnisotropic.rootForm_root_ne_zero (P := pi P) _
  corootForm_coroot_ne_zero s := by
    let _ : DecidableEq κ := Classical.decEq κ
    dsimp only [CorootForm]
    rw [← (piEquivInternalDirectSum hEi hEt P).toHom.flip.rootForm_weightMap,
      Hom.flip_weightMap, Hom.coroot_coweightMap_apply]
    exact IsAnisotropic.corootForm_coroot_ne_zero (P := pi P) _

end Internal

end RootPairing
