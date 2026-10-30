/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.LinearAlgebra.Determinant.Projective

/-!
# Determinants on finite projective modules of constant rank

Let `M` be a finite projective module over a commutative ring `R` whose rank
`Module.rankAtStalk M` is the constant `d`. Localizing at a maximal ideal `𝔪` makes `M` free of
rank `d` over `R_𝔪`, and the determinant `LinearMap.projectiveDet` commutes with this base change
(`LinearMap.projectiveDet_baseChange`). Identities between determinants can therefore be checked
over the local rings `R_𝔪`, where they are the identities for the determinant of a free module.

This gives the scaling law `projectiveDet (c • f) = c ^ d * projectiveDet f`, which for an
invertible module (`d = 1`) and for the top exterior power of a module of rank `d` is the input
for the norm of invertible modules. When `d = 1` every endomorphism is multiplication by its
determinant: the determinant identifies `Module.End R M` with `R`.

## Main results

* `LinearMap.projectiveDet_smul`: on a module of constant rank `d`, scaling an endomorphism by
  `c` multiplies its determinant by `c ^ d`.
* `LinearMap.projectiveDet_smul_id`: the determinant of multiplication by `c` is `c ^ d`.
* `LinearMap.eq_projectiveDet_smul_id`: on a module of constant rank one, every endomorphism is
  multiplication by its determinant.
-/

public section

open Module TensorProduct

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]

/-- Two elements of `R` agree when their images agree in the localization at every maximal ideal.
This is the form in which identities between determinants are checked locally below. -/
private theorem eq_of_algebraMap_localization_eq {a b : R}
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      algebraMap R (Localization.AtPrime P) a = algebraMap R (Localization.AtPrime P) b) :
    a = b :=
  Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P)) a b h

/-- After localizing at a prime `P`, a finite projective module of constant rank `d` is free of
rank `d`. -/
private theorem free_finrank_localization {d : ℕ} (hd : ∀ p, rankAtStalk (R := R) M p = d)
    (P : Ideal R) [P.IsPrime] :
    Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] M) ∧
      finrank (Localization.AtPrime P) (Localization.AtPrime P ⊗[R] M) = d :=
  ⟨Module.free_of_flat_of_isLocalRing, by
    rw [← rankAtStalk_eq_finrank_tensorProduct (M := M) ⟨P, inferInstance⟩, hd]⟩

/-- On a finite projective module of constant rank `d`, scaling an endomorphism by `c` multiplies
its determinant by `c ^ d`. This is `LinearMap.det_smul` for modules which need not be free. -/
theorem projectiveDet_smul {d : ℕ} (hd : ∀ p, rankAtStalk (R := R) M p = d) (c : R)
    (f : Module.End R M) :
    projectiveDet (c • f) = c ^ d * projectiveDet f := by
  refine eq_of_algebraMap_localization_eq fun P _ ↦ ?_
  have := (free_finrank_localization hd P).1
  have hfin := (free_finrank_localization hd P).2
  rw [map_mul, map_pow, ← projectiveDet_baseChange, ← projectiveDet_baseChange, baseChange_smul,
    ← algebraMap_smul (Localization.AtPrime P), projectiveDet_eq_det, projectiveDet_eq_det,
    det_smul, hfin]

/-- On a finite projective module of constant rank `d`, multiplication by `c` has determinant
`c ^ d`. -/
theorem projectiveDet_smul_id {d : ℕ} (hd : ∀ p, rankAtStalk (R := R) M p = d) (c : R) :
    projectiveDet (c • id : Module.End R M) = c ^ d := by
  rw [projectiveDet_smul hd, projectiveDet_id, mul_one]

/-- On a finite free module of rank one, every endomorphism is multiplication by its
determinant. -/
private theorem eq_det_smul_id_of_finrank_eq_one {A N : Type*} [CommRing A] [AddCommGroup N]
    [Module A N] [Module.Free A N] [Module.Finite A N] (h : finrank A N = 1) (f : Module.End A N) :
    f = LinearMap.det f • id := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton N := Module.subsingleton A N
    exact Subsingleton.elim _ _
  let b : Basis (Fin 1) A N := Module.finBasisOfFinrankEq A N h
  refine b.ext fun i ↦ ?_
  rw [Subsingleton.elim i 0, smul_apply, id_apply, ← det_toMatrix b, Matrix.det_unique,
    ← b.sum_repr (f (b 0))]
  simp [toMatrix_apply]

/-- On a finite projective module of constant rank one, for instance an invertible module, every
endomorphism is multiplication by its determinant. In particular `c ↦ c • id` and
`projectiveDet` are inverse to each other between `R` and `Module.End R M`. -/
theorem eq_projectiveDet_smul_id (hM : ∀ p, rankAtStalk (R := R) M p = 1) (f : Module.End R M) :
    f = projectiveDet f • id := by
  ext x
  refine Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P ⊗[R] M)
    (fun P _ ↦ TensorProduct.mk R (Localization.AtPrime P) M 1) _ _ fun P _ ↦ ?_
  have := (free_finrank_localization hM P).1
  have hfin := (free_finrank_localization hM P).2
  have h := congr($(eq_det_smul_id_of_finrank_eq_one hfin (f.baseChange (Localization.AtPrime P)))
    (1 ⊗ₜ[R] x))
  rw [← projectiveDet_eq_det, projectiveDet_baseChange] at h
  simpa [TensorProduct.smul_tmul', Algebra.smul_def] using h

end LinearMap
