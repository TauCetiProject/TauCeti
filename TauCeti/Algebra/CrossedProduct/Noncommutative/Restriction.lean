/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CrossedProduct.Noncommutative.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Restriction of noncommutative crossed systems

Pulling a crossed system back along a monoid homomorphism induces an algebra map on its
crossed products. This map fixes the coefficient algebra and sends `[h]` to `[f h]`.
In coordinates it is `Finsupp.mapDomain f`, so it is injective when `f` is injective.
Its image then consists exactly of the elements supported on the image of `f`.

For a subgroup inclusion this realizes the restricted crossed product as the actual
subalgebra supported on that subgroup. It supplies the algebra inclusion along which
crossed-product modules restrict their scalars, including for noncentral coefficients.

The construction uses `CrossedSystem.Algebra.lift` and Mathlib's finite-support coordinate
maps. The analogous scalar-restriction construction for Galois crossed products is in
`TauCeti.Algebra.CrossedProduct.Restriction`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace TauCeti.CrossedSystem

variable {k D G H : Type*} [CommSemiring k] [Semiring D] [_root_.Algebra k D]
  [Monoid G] [Monoid H]

/-- Pull a crossed system back along a homomorphism of its index monoids. -/
def comap (c : CrossedSystem k D G) (f : H →* G) : CrossedSystem k D H where
  action h := c.action (f h)
  factor h j := c.factor (f h) (f j)
  action_one := by simp
  factor_one_left h := by simp
  factor_one_right h := by simp
  action_mul h j d := by simpa only [map_mul] using c.action_mul (f h) (f j) d
  factor_assoc h j l := by simpa only [map_mul] using c.factor_assoc (f h) (f j) (f l)

/-- The restricted coefficient automorphism is the original one at the image index. -/
@[simp]
theorem comap_action (c : CrossedSystem k D G) (f : H →* G) (h : H) :
    (c.comap f).action h = c.action (f h) := (rfl)

/-- Restriction evaluates the original factors at the image indices. -/
@[simp]
theorem comap_factor (c : CrossedSystem k D G) (f : H →* G) (h j : H) :
    (c.comap f).factor h j = c.factor (f h) (f j) := (rfl)

namespace Algebra

variable (c : CrossedSystem k D G) (f : H →* G)

/-- The algebra map from the restricted crossed product, fixing coefficients and sending
the basis element at `h` to the basis element at `f h`. -/
noncomputable def comapHom : Algebra (c.comap f) →ₐ[k] Algebra c :=
  lift (inc c) (fun h ↦ basis c (f h))
    (fun h d ↦ by simp)
    (fun h j ↦ by simp)
    (by simp)

/-- The induced map sends a basis element to the basis element at its image index. -/
@[simp]
theorem comapHom_basis (h : H) :
    comapHom c f (basis (c.comap f) h) = basis c (f h) := by
  simp [comapHom]

/-- The induced map fixes the coefficient algebra. -/
@[simp]
theorem comapHom_inc (d : D) : comapHom c f (inc (c.comap f) d) = inc c d := by
  simp [comapHom]

/-- The induced map respects the left coefficient-module action, even though the
coefficient inclusion need not be central. -/
@[simp]
theorem comapHom_smul (d : D) (a : Algebra (c.comap f)) :
    comapHom c f (d • a) = d • comapHom c f a := by
  simp only [smul_def, map_mul, comapHom_inc]

/-- Restriction maps coordinates along the index homomorphism; coinciding image indices
have their coefficients added. For an inclusion, this extends coordinates by zero. -/
@[simp]
theorem repr_comapHom (a : Algebra (c.comap f)) :
    (basis c).repr (comapHom c f a) =
      Finsupp.mapDomain f ((basis (c.comap f)).repr a) := by
  induction a using induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb, Finsupp.mapDomain_add]
  | smul_basis h d => simp [Finsupp.smul_single]

/-- An injective index homomorphism gives an injective crossed-product map. -/
theorem comapHom_injective (hf : Function.Injective f) :
    Function.Injective (comapHom c f) := by
  intro a b hab
  apply (basis (c.comap f)).repr.injective
  apply Finsupp.mapDomain_injective hf
  simpa only [repr_comapHom] using congrArg (basis c).repr hab

/-- The restricted crossed product is precisely the subalgebra with coefficients vanishing
outside the image of the injective index homomorphism. -/
theorem mem_range_comapHom_iff (hf : Function.Injective f) (a : Algebra c) :
    a ∈ (comapHom c f).range ↔ ∀ g ∉ Set.range f, (basis c).repr a g = 0 := by
  have hr : a ∈ (comapHom c f).range ↔
      (basis c).repr a ∈ Set.range (Finsupp.mapDomain f) := by
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨(basis (c.comap f)).repr b, (repr_comapHom c f b).symm⟩
    · rintro ⟨b, hb⟩
      refine ⟨(basis (c.comap f)).repr.symm b, ?_⟩
      apply (basis c).repr.injective
      exact (repr_comapHom c f ((basis (c.comap f)).repr.symm b)).trans
        (by rw [LinearEquiv.apply_symm_apply, hb])
  exact hr.trans (Finsupp.mem_range_mapDomain_iff f hf _)

end Algebra

end TauCeti.CrossedSystem
