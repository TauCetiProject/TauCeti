/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Contraction.Linear.Basic

/-!
# Normalization of contractions on total modules

`LinearContraction` is the weak input to homological perturbation: its inclusion and projection
are chain maps, the projection retracts the inclusion, and its homotopy contracts the
complementary idempotent. No side conditions are required of the homotopy.

For a square-zero differential, `LinearContraction.normalize` keeps the inclusion and projection
and supplies all three side conditions required by `LinearSpecialContraction`. Write
`ψ = 1 - incl ∘ proj` and `k = ψ ∘ homotopy ∘ ψ`; the normalized homotopy is `k ∘ dM ∘ k`.
Normalization preserves the degrees of the maps, so its output can be used by the graded tensor
trick and homological transfer over an arbitrary ground ring.

This is the total-module counterpart of `TauCeti.Contraction.normalize`, which works with
cochains of cochain complexes. Here the data and normalization require no grading at all;
homogeneity is proved separately when gradings are supplied.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* M. Crainic, *On the perturbation lemma, and deformations*, Section 2.
-/

public section

namespace TauCeti

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A contraction of modules with endomorphisms, without side conditions on its homotopy.
For square-zero endomorphisms this is a deformation retract of differential modules. -/
@[ext]
structure LinearContraction (dM : Module.End R M) (dN : Module.End R N) where
  /-- The inclusion of the retract. -/
  incl : N →ₗ[R] M
  /-- The projection onto the retract. -/
  proj : M →ₗ[R] N
  /-- The contracting homotopy. -/
  homotopy : Module.End R M
  /-- The inclusion is a chain map. -/
  dM_comp_incl : dM ∘ₗ incl = incl ∘ₗ dN
  /-- The projection is a chain map. -/
  proj_comp_dM : proj ∘ₗ dM = dN ∘ₗ proj
  /-- The projection retracts the inclusion. -/
  proj_comp_incl : proj ∘ₗ incl = LinearMap.id
  /-- The homotopy contracts the complementary idempotent. -/
  dM_comp_homotopy_add_homotopy_comp_dM :
    dM ∘ₗ homotopy + homotopy ∘ₗ dM = LinearMap.id - incl ∘ₗ proj

/-- Forget the side conditions of a special contraction. -/
def LinearSpecialContraction.toLinearContraction {dM : Module.End R M}
    {dN : Module.End R N} (c : LinearSpecialContraction dM dN) : LinearContraction dM dN where
  incl := c.incl
  proj := c.proj
  homotopy := c.homotopy
  dM_comp_incl := c.dM_comp_incl
  proj_comp_dM := c.proj_comp_dM
  proj_comp_incl := c.proj_comp_incl
  dM_comp_homotopy_add_homotopy_comp_dM := c.dM_comp_homotopy_add_homotopy_comp_dM

@[simp] theorem LinearSpecialContraction.toLinearContraction_incl
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN) :
    c.toLinearContraction.incl = c.incl := (rfl)

@[simp] theorem LinearSpecialContraction.toLinearContraction_proj
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN) :
    c.toLinearContraction.proj = c.proj := (rfl)

@[simp] theorem LinearSpecialContraction.toLinearContraction_homotopy
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN) :
    c.toLinearContraction.homotopy = c.homotopy := (rfl)

namespace LinearContraction

variable {dM : Module.End R M} {dN : Module.End R N} (c : LinearContraction dM dN)

private def complement : Module.End R M := LinearMap.id - c.incl ∘ₗ c.proj

private theorem complement_sq : c.complement * c.complement = c.complement := by
  simp only [complement, Module.End.mul_eq_comp, LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id, LinearMap.comp_assoc]
  simp [← LinearMap.comp_assoc, c.proj_comp_incl]

private theorem complement_incl : c.complement ∘ₗ c.incl = 0 := by
  simp [complement, LinearMap.sub_comp, LinearMap.comp_assoc, c.proj_comp_incl]

private theorem proj_complement : c.proj ∘ₗ c.complement = 0 := by
  simp [complement, LinearMap.comp_sub, ← LinearMap.comp_assoc, c.proj_comp_incl]

private theorem differential_complement : dM * c.complement = c.complement * dM := by
  simp only [complement, Module.End.mul_eq_comp, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.comp_id, LinearMap.id_comp]
  rw [← LinearMap.comp_assoc, c.dM_comp_incl, LinearMap.comp_assoc,
    LinearMap.comp_assoc, c.proj_comp_dM]

private def reducedHomotopy : Module.End R M := c.complement * c.homotopy * c.complement

private theorem complement_reducedHomotopy :
    c.complement * c.reducedHomotopy = c.reducedHomotopy := by
  simp only [reducedHomotopy, ← mul_assoc, c.complement_sq]

private theorem reducedHomotopy_complement :
    c.reducedHomotopy * c.complement = c.reducedHomotopy := by
  simp only [reducedHomotopy, mul_assoc, c.complement_sq]

private theorem differential_reducedHomotopy :
    dM * c.reducedHomotopy + c.reducedHomotopy * dM = c.complement := by
  have h : dM * c.homotopy + c.homotopy * dM = c.complement :=
    c.dM_comp_homotopy_add_homotopy_comp_dM
  calc
    _ = c.complement * (dM * c.homotopy + c.homotopy * dM) * c.complement := by
      simp only [reducedHomotopy, mul_add, add_mul, ← mul_assoc]
      rw [c.differential_complement]
      simp only [mul_assoc]
      rw [← c.differential_complement]
    _ = c.complement := by rw [h, c.complement_sq, c.complement_sq]

private theorem reducedHomotopy_sq_differential :
    c.reducedHomotopy * c.reducedHomotopy * dM =
      dM * c.reducedHomotopy * c.reducedHomotopy := by
  have h₁ := congrArg (c.reducedHomotopy * ·) c.differential_reducedHomotopy
  have h₂ := congrArg (· * c.reducedHomotopy) c.differential_reducedHomotopy
  simp only [mul_add, add_mul, c.complement_reducedHomotopy,
    c.reducedHomotopy_complement, mul_assoc] at h₁ h₂ ⊢
  exact add_left_cancel (h₁.trans ((add_comm _ _).trans h₂).symm)

variable (hd : dM ∘ₗ dM = 0)

include hd in
private theorem differential_reducedHomotopy_differential :
    dM * c.reducedHomotopy * dM = dM * c.complement := by
  have h := congrArg (dM * ·) c.differential_reducedHomotopy
  simpa only [mul_add, ← mul_assoc, Module.End.mul_eq_comp dM dM, hd, zero_mul,
    zero_add] using h

private def normalizedHomotopy : Module.End R M :=
  c.reducedHomotopy * dM * c.reducedHomotopy

include hd in
private theorem normalizedHomotopy_equation :
    dM * c.normalizedHomotopy + c.normalizedHomotopy * dM = c.complement := by
  calc
    _ = dM * c.reducedHomotopy + c.reducedHomotopy * dM := by
      calc
        _ = (dM * c.reducedHomotopy * dM) * c.reducedHomotopy +
            c.reducedHomotopy * (dM * c.reducedHomotopy * dM) := by
          simp only [normalizedHomotopy, mul_assoc]
        _ = dM * c.reducedHomotopy + c.reducedHomotopy * dM := by
          rw [c.differential_reducedHomotopy_differential hd]
          simp only [mul_assoc, c.complement_reducedHomotopy]
          rw [c.differential_complement, ← mul_assoc, c.reducedHomotopy_complement]
    _ = c.complement := c.differential_reducedHomotopy

include hd in
private theorem normalizedHomotopy_sq : c.normalizedHomotopy * c.normalizedHomotopy = 0 := by
  calc
    _ = c.reducedHomotopy * (dM * c.reducedHomotopy * c.reducedHomotopy) *
        dM * c.reducedHomotopy := by simp only [normalizedHomotopy, mul_assoc]
    _ = c.reducedHomotopy * (c.reducedHomotopy * c.reducedHomotopy * dM) *
        dM * c.reducedHomotopy := by rw [c.reducedHomotopy_sq_differential]
    _ = 0 := by simp only [mul_assoc, Module.End.mul_eq_comp dM dM, hd, zero_mul, mul_zero]

include hd in
/-- Normalize a contraction of differential modules, retaining its inclusion and projection.
The homotopy is `(ψ h ψ) dM (ψ h ψ)`, where `ψ = 1 - incl ∘ proj`. -/
def normalize : LinearSpecialContraction dM dN where
  incl := c.incl
  proj := c.proj
  homotopy := c.normalizedHomotopy
  dM_comp_incl := c.dM_comp_incl
  proj_comp_dM := c.proj_comp_dM
  proj_comp_incl := c.proj_comp_incl
  dM_comp_homotopy_add_homotopy_comp_dM := c.normalizedHomotopy_equation hd
  homotopy_comp_incl := by
    simp only [normalizedHomotopy, reducedHomotopy, Module.End.mul_eq_comp,
      LinearMap.comp_assoc, c.complement_incl, LinearMap.comp_zero]
  proj_comp_homotopy := by
    simp only [normalizedHomotopy, reducedHomotopy, Module.End.mul_eq_comp,
      ← LinearMap.comp_assoc, c.proj_complement, LinearMap.zero_comp]
  homotopy_comp_homotopy := c.normalizedHomotopy_sq hd

@[simp] theorem normalize_incl : (c.normalize hd).incl = c.incl := (rfl)

@[simp] theorem normalize_proj : (c.normalize hd).proj = c.proj := (rfl)

/-- The explicit homotopy supplied by normalization. -/
theorem normalize_homotopy : (c.normalize hd).homotopy =
    ((LinearMap.id - c.incl ∘ₗ c.proj) ∘ₗ c.homotopy ∘ₗ
      (LinearMap.id - c.incl ∘ₗ c.proj)) ∘ₗ dM ∘ₗ
    ((LinearMap.id - c.incl ∘ₗ c.proj) ∘ₗ c.homotopy ∘ₗ
      (LinearMap.id - c.incl ∘ₗ c.proj)) := by
  simp only [normalize, normalizedHomotopy, reducedHomotopy, complement,
    Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Normalization preserves the degree-minus-one condition on the homotopy. -/
theorem isHomogeneous_normalize_homotopy {σM σN : Type*}
    [SetLike σM M] [AddSubgroupClass σM M] [SetLike σN N]
    {𝒜 : ℤ → σM} {ℬ : ℤ → σN}
    (hdM : LinearMap.IsHomogeneous dM 𝒜 𝒜 1)
    (hi : LinearMap.IsHomogeneous c.incl ℬ 𝒜 0)
    (hp : LinearMap.IsHomogeneous c.proj 𝒜 ℬ 0)
    (hh : LinearMap.IsHomogeneous c.homotopy 𝒜 𝒜 (-1)) :
    LinearMap.IsHomogeneous (c.normalize hd).homotopy 𝒜 𝒜 (-1) := by
  have hψ := (LinearMap.isHomogeneous_id 𝒜).sub (by simpa using hi.comp hp)
  have hk := hψ.comp (hh.comp hψ)
  simp only [add_zero, zero_add] at hk
  rw [normalize_homotopy]
  simpa using hk.comp (hdM.comp hk)

end LinearContraction

/-- Normalization leaves an already special contraction unchanged. -/
@[simp]
theorem LinearSpecialContraction.normalize_toLinearContraction
    {dM : Module.End R M} {dN : Module.End R N} (c : LinearSpecialContraction dM dN)
    (hd : dM ∘ₗ dM = 0) : c.toLinearContraction.normalize hd = c := by
  have hk : (LinearMap.id - c.incl ∘ₗ c.proj) ∘ₗ c.homotopy ∘ₗ
      (LinearMap.id - c.incl ∘ₗ c.proj) = c.homotopy := by
    simp [LinearMap.comp_sub, LinearMap.sub_comp, LinearMap.comp_assoc]
  apply LinearSpecialContraction.ext <;> try rfl
  rw [LinearContraction.normalize_homotopy]
  simp only [toLinearContraction_incl, toLinearContraction_proj,
    toLinearContraction_homotopy, hk]
  have h := congrArg (c.homotopy ∘ₗ ·) c.dM_comp_homotopy_add_homotopy_comp_dM
  simpa [LinearMap.comp_add, LinearMap.comp_sub, ← LinearMap.comp_assoc] using h

end TauCeti
