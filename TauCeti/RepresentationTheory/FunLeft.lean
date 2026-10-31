/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Representations on functions and averaging with a cutoff function

Let a group `G` act on a type `X` and linearly on a module `A` through `ρ`. Then `G` acts on the
functions `X → A` by translating the argument and acting on the values,
$$(g \cdot \varphi)(x) = \rho(g)\bigl(\varphi(g^{-1} \cdot x)\bigr),$$
the representation `Representation.funLeft ρ X`. For the trivial action on `A` this is the
translation of functions on a `G`-space. Through `Finsupp.lift` it is isomorphic to
`Representation.linHom (Representation.ofMulAction k G X) ρ`; the function model is the one on
which a weight `c : X → k` acts pointwise. A function is invariant exactly when
`φ (g • x) = ρ g (φ x)` for all `g` and `x` (`Representation.mem_invariants_funLeft_iff`).

A function `c : X → k` whose translates sum to one, `∑ᶠ g, c (g • x) = 1` for every `x`, such as
a cutoff function of a proper action of a discrete group, replaces the normalized group sum of a
finite group. The *cutoff average*
$$(Q\varphi)(x) = \sum_{g \in G} c(g \cdot x)\, \rho(g)^{-1}\bigl(\varphi(g \cdot x)\bigr)$$
is a projection onto the invariants (`Representation.isProj_cutoffAverage`). The group `G` need
not be finite and the action need not be faithful; every element of `G` is counted. For a finite
group and the constant function `|G|⁻¹` it is the average over the group, the analogue of
`Representation.averageMap`. The hypothesis on `c` forces each sum to have finitely many nonzero
terms (`hasFiniteSupport_of_finsum_eq_one`).

## Main declarations

* `Representation.funLeft ρ X`: the representation of `G` on `X → A`.
* `Representation.mem_invariants_funLeft_iff`: the invariant functions.
* `Representation.cutoffAverage`: the average of a function against a function `c` whose
  translates sum to one.
* `Representation.isProj_cutoffAverage`: the cutoff average is a projection onto the invariants.
* `Representation.cutoffAverage_comp`: naturality for pullback along equivariant maps.

## References

* M. Crainic, *Differentiable and algebroid cohomology, van Est isomorphisms, and characteristic
  classes*, Comment. Math. Helv. **78** (2003), Section 2, for averaging with cutoff functions of
  proper groupoids.
-/

public section

noncomputable section

open Function

namespace Representation

section Semiring

variable {k G A : Type*} [CommSemiring k] [Group G] [AddCommMonoid A] [Module k A]
variable (ρ : Representation k G A)

section FunLeft

variable (X : Type*) [MulAction G X]

/-- The representation of `G` on functions `X → A` that translates the argument and acts on the
values: `(g • φ) x = ρ g (φ (g⁻¹ • x))`. -/
def funLeft : Representation k G (X → A) where
  toFun g :=
    { toFun φ x := ρ g (φ (g⁻¹ • x))
      map_add' _ _ := by
        ext
        simp
      map_smul' _ _ := by
        ext
        simp }
  map_one' := by
    ext
    simp
  map_mul' _ _ := by
    ext
    simp [mul_smul]

variable {X}

@[simp]
theorem funLeft_apply (g : G) (φ : X → A) (x : X) : ρ.funLeft X g φ x = ρ g (φ (g⁻¹ • x)) :=
  (rfl)

end FunLeft

section CutoffAverage

variable {X : Type*} [MulAction G X] {c : X → k}

/-- The average `x ↦ ∑ᶠ g, c (g • x) • ρ g⁻¹ (φ (g • x))` of a function `φ : X → A` against a
function `c` whose translates sum to one. It is a projection onto the invariants of
`Representation.funLeft ρ X` (`Representation.isProj_cutoffAverage`). -/
def cutoffAverage (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1) : (X → A) →ₗ[k] X → A where
  toFun φ x := ∑ᶠ g : G, c (g • x) • ρ g⁻¹ (φ (g • x))
  map_add' φ ψ := by
    ext x
    simp only [Pi.add_apply, map_add, smul_add]
    have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
    exact finsum_add_distrib (hfin.fun_smul_left _) (hfin.fun_smul_left _)
  map_smul' r φ := by
    ext x
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_comm _ r]
    have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
    exact (smul_finsum' r (hfin.fun_smul_left _)).symm

@[simp]
theorem cutoffAverage_apply (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1) (φ : X → A) (x : X) :
    ρ.cutoffAverage hc φ x = ∑ᶠ g : G, c (g • x) • ρ g⁻¹ (φ (g • x)) :=
  (rfl)

/-- **Naturality of the cutoff average for pullback.** Pulling a function back along an
equivariant map `π : Y → X` commutes with the cutoff average, for the pulled-back weight
`c ∘ π`. -/
theorem cutoffAverage_comp {Y : Type*} [MulAction G Y] (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1)
    (π : Y →[G] X) (hc' : ∀ y, ∑ᶠ g : G, (c ∘ π) (g • y) = 1) (φ : X → A) :
    ρ.cutoffAverage hc' (φ ∘ π) = ρ.cutoffAverage hc φ ∘ π := by
  ext y
  simp [map_smul]

end CutoffAverage

end Semiring

section Ring

variable {k G A : Type*} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
variable (ρ : Representation k G A) {X : Type*} [MulAction G X]

/-- A function `φ : X → A` is invariant under `Representation.funLeft ρ X` exactly when it is
equivariant, `φ (g • x) = ρ g (φ x)`. -/
theorem mem_invariants_funLeft_iff {φ : X → A} :
    φ ∈ (ρ.funLeft X).invariants ↔ ∀ (g : G) (x : X), φ (g • x) = ρ g (φ x) := by
  simp only [mem_invariants, funext_iff, funLeft_apply]
  refine ⟨fun h g x ↦ ?_, fun h g x ↦ ?_⟩
  · simpa using (h g (g • x)).symm
  · rw [← h, smul_inv_smul]

/-- **The cutoff average is a projection onto the invariants.** Its values are invariant
functions, and it fixes every invariant function. -/
theorem isProj_cutoffAverage {c : X → k} (hc : ∀ x, ∑ᶠ g : G, c (g • x) = 1) :
    LinearMap.IsProj (ρ.funLeft X).invariants (ρ.cutoffAverage hc) where
  map_mem φ := by
    rw [mem_invariants_funLeft_iff]
    intro h x
    have hfin : HasFiniteSupport _ := hasFiniteSupport_of_finsum_eq_one (hc x)
    -- Reindex the sum at `h • x` by `g ↦ g * h⁻¹`.
    rw [cutoffAverage_apply, cutoffAverage_apply, map_finsum _ (hfin.fun_smul_left _),
      ← finsum_comp_equiv (Equiv.mulRight h⁻¹)]
    simp [mul_smul]
  map_id φ hφ := by
    rw [mem_invariants_funLeft_iff] at hφ
    ext x
    simp only [cutoffAverage_apply, hφ, inv_self_apply]
    rw [← finsum_smul' (hasFiniteSupport_of_finsum_eq_one (hc x)), hc, one_smul]

end Ring

end Representation
