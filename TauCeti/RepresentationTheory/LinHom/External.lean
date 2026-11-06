/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.External

/-!
# External Hom representations

`Representation.externalLinHom ρ σ` is the representation of `G × H` on `Hom(V, W)`
in which the first group acts on the domain and the second on the codomain:
`(g, h) • f = σ(h) ∘ f ∘ ρ(g⁻¹)`.

For a finite projective domain, `Representation.externalDualTensorHom` identifies this
representation with `ρ.dual.externalTensor σ`. Its inverse has the usual basis expansion,
and the comparison is contravariantly natural in the domain and covariantly natural in the
codomain. This realizes the operator blocks in two-sided Fourier decompositions without
choosing bases for the representations.

The construction consumes Mathlib's `Representation.linHom` on the two projection
pullbacks, and the contraction comparison consumes `dualTensorHomEquiv` and
`Representation.dualTensorHom_comm`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Exercises 1.2 and 2.36.
-/

public section

open scoped TensorProduct

namespace Representation

section Semiring

variable {k G H V V' W W' : Type*} [CommSemiring k] [Group G] [Group H]
  [AddCommMonoid V] [Module k V] [AddCommMonoid V'] [Module k V']
  [AddCommMonoid W] [Module k W] [AddCommMonoid W'] [Module k W']

/-- The external Hom representation, with the domain group first and codomain group second. -/
def externalLinHom (ρ : Representation k G V) (σ : Representation k H W) :
    Representation k (G × H) (V →ₗ[k] W) :=
  linHom (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

variable (ρ : Representation k G V) (σ : Representation k H W)

/-- The action is precomposition by the inverse domain action and postcomposition by the
codomain action. -/
@[simp]
theorem externalLinHom_apply (p : G × H) (f : V →ₗ[k] W) :
    externalLinHom ρ σ p f = (σ p.2).comp (f.comp (ρ p.1⁻¹)) :=
  (rfl)

/-- Restriction along the diagonal recovers the internal Hom representation. -/
@[simp]
theorem externalLinHom_comp_diag (τ : Representation k G W) :
    (externalLinHom ρ τ).comp ((MonoidHom.id G).prod (MonoidHom.id G)) = linHom ρ τ :=
  (rfl)

/-- Contraction identifies the external product of the dual domain and the codomain with
external Hom. Only the domain needs to be finite projective. -/
noncomputable def externalDualTensorHom [Module.Finite k V] [Module.Projective k V] :
    Equiv (ρ.dual.externalTensor σ) (externalLinHom ρ σ) :=
  .mk (dualTensorHomEquiv k V W) fun p ↦ by
    simpa [externalLinHom, externalTensor_apply] using
      dualTensorHom_comm (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) p

@[simp]
theorem externalDualTensorHom_apply [Module.Finite k V] [Module.Projective k V]
    (t : Module.Dual k V ⊗[k] W) :
    externalDualTensorHom ρ σ t = dualTensorHom k V W t :=
  (rfl)

/-- In any finite basis of the domain, the inverse contraction is the sum of the dual basis
vectors tensored with the images of the basis vectors. -/
theorem externalDualTensorHom_symm_apply [Module.Finite k V] [Module.Projective k V]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι k V) (f : V →ₗ[k] W) :
    (externalDualTensorHom ρ σ).symm f = ∑ i, b.coord i ⊗ₜ[k] f (b i) := by
  apply (externalDualTensorHom ρ σ).injective
  simp only [Equiv.toLinearEquiv_apply, Equiv.coe_toIntertwiningMap,
    Equiv.apply_symm_apply, externalDualTensorHom_apply, map_sum]
  ext v
  simp only [LinearMap.sum_apply, dualTensorHom_apply]
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using
    congrArg f (b.sum_repr v).symm

namespace IntertwiningMap

variable {ρ σ} {ρ' : Representation k G V'} {σ' : Representation k H W'}

/-- Precomposition and postcomposition define the contravariant/covariant map on external
Hom representations. -/
def externalLinHom (a : IntertwiningMap ρ' ρ) (b : IntertwiningMap σ σ') :
    IntertwiningMap (Representation.externalLinHom ρ σ)
      (Representation.externalLinHom ρ' σ') where
  toLinearMap := (b.toLinearMap.compRight k).comp (a.toLinearMap.lcomp k W)
  isIntertwining' p := by
    ext f v
    simp [IntertwiningMap.isIntertwining]

@[simp]
theorem externalLinHom_apply (a : IntertwiningMap ρ' ρ) (b : IntertwiningMap σ σ')
    (f : V →ₗ[k] W) (v : V') :
    a.externalLinHom b f v = b (f (a v)) :=
  (rfl)

@[simp]
theorem externalLinHom_id :
    (IntertwiningMap.id ρ).externalLinHom (IntertwiningMap.id σ) =
      IntertwiningMap.id (Representation.externalLinHom ρ σ) := by
  ext f v
  rfl

/-- External Hom maps compose in the opposite order in the domain variable. -/
theorem externalLinHom_comp {V'' W'' : Type*}
    [AddCommMonoid V''] [Module k V''] [AddCommMonoid W''] [Module k W'']
    {ρ'' : Representation k G V''} {σ'' : Representation k H W''}
    (a : IntertwiningMap ρ' ρ) (a' : IntertwiningMap ρ'' ρ')
    (b : IntertwiningMap σ σ') (b' : IntertwiningMap σ' σ'') :
    (a.comp a').externalLinHom (b'.comp b) =
      (a'.externalLinHom b').comp (a.externalLinHom b) := by
  ext f v
  rfl

end IntertwiningMap

/-- Contraction is contravariantly natural in its dual factor and covariantly natural in its
other factor. This equation does not require finite generation or projectivity. -/
theorem externalLinHom_map_dualTensorHom {ρ' : Representation k G V'}
    {σ' : Representation k H W'} (a : IntertwiningMap ρ' ρ) (b : IntertwiningMap σ σ')
    (t : Module.Dual k V ⊗[k] W) :
    a.externalLinHom b (dualTensorHom k V W t) =
      dualTensorHom k V' W'
        (TensorProduct.map a.toLinearMap.dualMap b.toLinearMap t) := by
  induction t using TensorProduct.inductionOn with
  | tmul f w => ext v; simp
  | add x y hx hy => simp_all

end Semiring

section Field

variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The external Hom character in domain-first order is `χ_ρ(g⁻¹) χ_σ(h)`. -/
@[simp]
theorem char_externalLinHom (ρ : Representation k G V) (σ : Representation k H W)
    (p : G × H) :
    (externalLinHom ρ σ).character p = ρ.character p.1⁻¹ * σ.character p.2 :=
  char_linHom (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) p

end Field

end Representation
