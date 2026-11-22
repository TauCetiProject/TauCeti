/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
import TauCeti.LinearAlgebra.RootSystem.RootForm

/-!
# Canonical bilinear forms and anisotropy of direct sums of root pairings

For a finite family of finite root pairings `P : ∀ c, RootPairing (ι c) R (M c) (N c)`, the
canonical bilinear form `RootForm` and coroot form `CorootForm` of the external direct sum
`RootPairing.pi P` and internal direct sum `RootPairing.internalDirectSum hEi hEt P` decompose as
orthogonal sums of the summands' canonical forms. In particular, both external and internal direct
sums preserve and reflect anisotropy (`IsAnisotropic`).

## Main results

* `RootPairing.pi_polarization_apply`: coordinate formula for the polarization of
  `RootPairing.pi P`.
* `RootPairing.pi_rootForm_apply_apply` and `RootPairing.pi_corootForm_apply_apply`: orthogonal
  sum decompositions for the canonical forms of `RootPairing.pi P`.
* `RootPairing.isAnisotropic_pi` and `RootPairing.isAnisotropic_pi_iff`: anisotropy of finite
  external direct sums.
* `RootPairing.internalDirectSum_rootForm_apply_apply` and
  `RootPairing.internalDirectSum_corootForm_apply_apply`: orthogonal sum decompositions for the
  canonical forms of `RootPairing.internalDirectSum hEi hEt P`.
* `RootPairing.isAnisotropic_internalDirectSum` and
  `RootPairing.isAnisotropic_internalDirectSum_iff`: anisotropy of finite internal direct sums.

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

/-- **A finite direct sum of finite root pairings is anisotropic iff every summand is
anisotropic.** -/
theorem isAnisotropic_pi_iff : (pi P).IsAnisotropic ↔ ∀ c, (P c).IsAnisotropic := by
  refine ⟨fun _ c ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun _ ↦ isAnisotropic_pi P⟩
  · have h0 := IsAnisotropic.rootForm_root_ne_zero (P := pi P) ⟨c, i⟩
    rw [pi_rootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)] at h0
    · simpa using h0
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]
  · have h0 := IsAnisotropic.corootForm_coroot_ne_zero (P := pi P) ⟨c, i⟩
    rw [pi_corootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)] at h0
    · simpa using h0
    · intro d _ hdc
      simp [Pi.single_eq_of_ne hdc]

end External

section Internal

section

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (E c) (N c))

private theorem toPerfPair_symm_internalDirectSum_coroot_comp_same (c : κ) (i : ι c) :
    (P c).flip.toPerfPair.symm (((internalDirectSum hEi hEt P).coroot ⟨c, i⟩).comp (E c).subtype) =
      (P c).coroot i := by
  apply (P c).flip.toPerfPair.injective
  ext x
  simp [coroot']

private theorem internalDirectSum_coroot_comp_ne {c d : κ} (hdc : d ≠ c) (i : ι c) :
    ((internalDirectSum hEi hEt P).coroot ⟨c, i⟩).comp (E d).subtype = 0 := by
  ext x
  simp [internalProjection_apply_of_ne hEi hEt hdc]

end

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
summands' coroot forms on the summand restrictions of dual functionals.** -/
@[simp]
theorem internalDirectSum_corootForm_apply_apply (f g : Module.Dual R M) :
    (internalDirectSum hEi hEt P).CorootForm f g =
      ∑ c, (P c).CorootForm
        ((P c).flip.toPerfPair.symm (f.comp (E c).subtype))
        ((P c).flip.toPerfPair.symm (g.comp (E c).subtype)) := by
  simp only [CorootForm, rootForm_apply_apply, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  have hval (h : Module.Dual R M) :
      (internalDirectSum hEi hEt P).flip.coroot' ⟨c, i⟩ h =
        (P c).flip.coroot' i ((P c).flip.toPerfPair.symm (h.comp (E c).subtype)) := by
    have hdual : (P c).flip.coroot' i ((P c).flip.toPerfPair.symm (h.comp (E c).subtype)) =
        ((P c).flip.toPerfPair ((P c).flip.toPerfPair.symm (h.comp (E c).subtype)))
          ((P c).root i) := by
      simp [coroot']
    rw [hdual, LinearEquiv.apply_symm_apply, LinearMap.comp_apply, Submodule.coe_subtype]
    simp [coroot']
  rw [hval f, hval g]

/-- A finite internal direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_internalDirectSum [∀ c, (P c).IsAnisotropic] :
    (internalDirectSum hEi hEt P).IsAnisotropic where
  rootForm_root_ne_zero := by
    rintro ⟨c, i⟩
    let _ : DecidableEq κ := Classical.decEq κ
    rw [internalDirectSum_rootForm_apply_apply, Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · simpa using IsAnisotropic.rootForm_root_ne_zero (P := P c) i
    · intro d _ hdc
      simp [internalProjection_apply_of_ne hEi hEt hdc.symm]
  corootForm_coroot_ne_zero := by
    rintro ⟨c, i⟩
    let _ : DecidableEq κ := Classical.decEq κ
    rw [internalDirectSum_corootForm_apply_apply,
      Finset.sum_eq_single_of_mem c (Finset.mem_univ c)]
    · rw [toPerfPair_symm_internalDirectSum_coroot_comp_same]
      exact IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i
    · intro d _ hdc
      rw [internalDirectSum_coroot_comp_ne hEi hEt P hdc, map_zero, map_zero]

/-- **A finite internal direct sum of finite root pairings is anisotropic iff every summand is
anisotropic.** -/
theorem isAnisotropic_internalDirectSum_iff :
    (internalDirectSum hEi hEt P).IsAnisotropic ↔ ∀ c, (P c).IsAnisotropic := by
  refine ⟨fun _ c ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun _ ↦ isAnisotropic_internalDirectSum hEi hEt P⟩
  · let _ : DecidableEq κ := Classical.decEq κ
    have h0 := IsAnisotropic.rootForm_root_ne_zero (P := internalDirectSum hEi hEt P) ⟨c, i⟩
    rw [internalDirectSum_rootForm_apply_apply,
      Finset.sum_eq_single_of_mem c (Finset.mem_univ c)] at h0
    · simpa using h0
    · intro d _ hdc
      simp [internalProjection_apply_of_ne hEi hEt hdc.symm]
  · let _ : DecidableEq κ := Classical.decEq κ
    have h0 :=
      IsAnisotropic.corootForm_coroot_ne_zero (P := internalDirectSum hEi hEt P) ⟨c, i⟩
    rw [internalDirectSum_corootForm_apply_apply,
      Finset.sum_eq_single_of_mem c (Finset.mem_univ c)] at h0
    · rwa [toPerfPair_symm_internalDirectSum_coroot_comp_same] at h0
    · intro d _ hdc
      rw [internalDirectSum_coroot_comp_ne hEi hEt P hdc, map_zero, map_zero]

end Internal

end RootPairing
