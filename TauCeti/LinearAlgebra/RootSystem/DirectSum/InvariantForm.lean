/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate
public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
import TauCeti.LinearAlgebra.RootSystem.Flip
import TauCeti.LinearAlgebra.RootSystem.HomInvariance.RootForm

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
* `RootPairing.pi_rootForm_single_single` and `RootPairing.pi_corootForm_single_single`:
  single-coordinate evaluations of the canonical forms of `RootPairing.pi P`.
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

/-- The polarization of `RootPairing.pi P` acts coordinatewise as `(P c).Polarization`. -/
@[simp]
theorem pi_polarization_apply (x : ∀ c, M c) (c : κ) :
    (pi P).Polarization x c = (P c).Polarization (x c) := by
  rw [Polarization_apply, Fintype.sum_sigma]
  simp only [pi_coroot, pi_coroot'_apply, ← Pi.single_smul]
  simp_rw [← LinearMap.single_apply (R := R) (φ := N), ← map_sum, LinearMap.single_apply]
  simp [Polarization_apply]

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

/-- Evaluating the canonical root form of `RootPairing.pi P` on two single-coordinate vectors
in the same summand `c` recovers `(P c).RootForm`. -/
theorem pi_rootForm_single_single (c : κ) (x y : M c) :
    (pi P).RootForm (Pi.single c x) (Pi.single c y) = (P c).RootForm x y := by
  simp [Pi.apply_single (fun d z ↦ (P d).RootForm z (Pi.single c y d)) (fun _ ↦ by simp)]

/-- Evaluating the canonical coroot form of `RootPairing.pi P` on two single-coordinate vectors
in the same summand `c` recovers `(P c).CorootForm`. -/
theorem pi_corootForm_single_single (c : κ) (x y : N c) :
    (pi P).CorootForm (Pi.single c x) (Pi.single c y) = (P c).CorootForm x y := by
  dsimp only [CorootForm]
  rw [pi_flip, pi_rootForm_single_single]

/-- A finite direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_pi [∀ c, (P c).IsAnisotropic] : (pi P).IsAnisotropic where
  rootForm_root_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_root, pi_rootForm_single_single]
    exact IsAnisotropic.rootForm_root_ne_zero (P := P c) i
  corootForm_coroot_ne_zero := by
    rintro ⟨c, i⟩
    rw [pi_coroot, pi_corootForm_single_single]
    exact IsAnisotropic.corootForm_coroot_ne_zero (P := P c) i

/-- **A finite direct sum of finite root pairings is anisotropic iff every summand is
anisotropic.** -/
theorem isAnisotropic_pi_iff : (pi P).IsAnisotropic ↔ ∀ c, (P c).IsAnisotropic := by
  refine ⟨fun _ c ↦ ⟨fun i ↦ ?_, fun i ↦ ?_⟩, fun _ ↦ isAnisotropic_pi P⟩
  · rw [← pi_rootForm_single_single, ← pi_root]
    exact IsAnisotropic.rootForm_root_ne_zero (P := pi P) ⟨c, i⟩
  · rw [← pi_corootForm_single_single, ← pi_coroot]
    exact IsAnisotropic.corootForm_coroot_ne_zero (P := pi P) ⟨c, i⟩

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
summands' coroot forms on the summand restrictions of dual functionals.** -/
@[simp]
theorem internalDirectSum_corootForm_apply_apply (f g : Module.Dual R M) :
    (internalDirectSum hEi hEt P).CorootForm f g =
      ∑ c, (P c).CorootForm
        ((P c).flip.toPerfPair.symm (f.comp (E c).subtype))
        ((P c).flip.toPerfPair.symm (g.comp (E c).subtype)) := by
  let _ : DecidableEq κ := Classical.decEq κ
  let e := piEquivInternalDirectSum hEi hEt P
  have h : (internalDirectSum hEi hEt P).CorootForm f g =
      (pi P).CorootForm (e.coweightMap f) (e.coweightMap g) := by
    simpa [CorootForm, Hom.flip_weightMap] using (e.toHom.flip.rootForm_weightMap f g).symm
  simp [h, e]

end Internal

section InternalAnisotropic

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} (hEi : iSupIndep E) (hEt : ⨆ c, E c = ⊤)
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  (P : ∀ c, RootPairing (ι c) R (E c) (N c)) [∀ c, Fintype (ι c)] [Fintype (Σ c, ι c)]

/-- **A finite internal direct sum of finite root pairings is anisotropic iff every summand is
anisotropic.** -/
theorem isAnisotropic_internalDirectSum_iff :
    (internalDirectSum hEi hEt P).IsAnisotropic ↔ ∀ c, (P c).IsAnisotropic := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let _ : DecidableEq κ := Classical.decEq κ
  obtain rfl : ‹Fintype (Σ c, ι c)› = Sigma.instFintype := Subsingleton.elim _ _
  exact (Equiv.isAnisotropic_iff (piEquivInternalDirectSum hEi hEt P)).symm.trans
    (isAnisotropic_pi_iff P)

/-- A finite internal direct sum of anisotropic finite root pairings is anisotropic. -/
instance isAnisotropic_internalDirectSum [∀ c, (P c).IsAnisotropic] :
    (internalDirectSum hEi hEt P).IsAnisotropic :=
  (isAnisotropic_internalDirectSum_iff hEi hEt P).mpr ‹_›

end InternalAnisotropic

end RootPairing
