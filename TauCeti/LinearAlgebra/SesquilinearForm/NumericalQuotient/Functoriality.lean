/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SesquilinearForm.NumericalQuotient.Basic

/-!
# Functoriality of numerical quotients

A linear map between the left arguments of two sesquilinear maps descends to their left numerical
quotients precisely after one proves that it sends the first left radical into the second.  The
right-hand construction is independent and has the dual condition.  This file supplies those two
maps, their identity and composition laws, and compatibility with the descended numerical
pairings.

For a pair of maps preserving the original pairings, surjectivity of the map in the opposite
argument supplies the required radical inclusion, and the induced maps are always injective.  In
particular, a pair of surjective linear maps preserving a pairing induces linear equivalences of
both numerical quotients, and those equivalences preserve the numerical pairing.  The surjective
maps themselves need not be injective: the numerical quotients can be isomorphic even when the
underlying modules are not.

The separate left and right hypotheses are essential for nonsymmetric pairings: neither radical
condition follows from the other.

As in `TauCeti.LinearAlgebra.SesquilinearForm.NumericalQuotient.Basic`, the pairings have the
shape `L →ₛₗ[ρ] M →ₛₗ[σ] P`: the two arguments may be modules over different commutative rings,
each semilinear along its own ring homomorphism into the scalars of the target, and the maps of
arguments are linear over the respective rings. The statements about radicals alone hold over
commutative semirings.

## Main definitions

* `TauCeti.leftNumericalMap` and `TauCeti.rightNumericalMap`: maps induced on the two numerical
  quotients by a proved radical inclusion.
* `TauCeti.leftNumericalEquiv` and `TauCeti.rightNumericalEquiv`: the equivalences induced by a
  pairing-preserving pair of surjective linear maps.

## Main results

* `TauCeti.numericalPairing_map_map`: compatible quotient maps preserve the numerical pairing.
* `TauCeti.leftNumericalMap_injective` and `TauCeti.rightNumericalMap_injective`: a map induced
  by one half of a pairing-preserving pair is injective.
* `TauCeti.numericalPairing_equiv_equiv`: the equivalences induced by a pairing-preserving pair of
  surjective maps preserve the numerical pairing.
-/

public section

namespace TauCeti

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

variable {R R₁ R₂ : Type*} {L : Type u₁} {M : Type u₂} {P : Type u₃}
variable {L' : Type u₄} {M' : Type u₅} {L'' : Type u₆} {M'' : Type u₇}

section Radicals

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid L] [Module R₁ L] [AddCommMonoid M] [Module R₂ M]
variable [AddCommMonoid L'] [Module R₁ L'] [AddCommMonoid M'] [Module R₂ M']
variable [AddCommMonoid P] [Module R P]
variable {ρ : R₁ →+* R} {σ : R₂ →+* R}
variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P) (c : L' →ₛₗ[ρ] M' →ₛₗ[σ] P)
variable (f : L →ₗ[R₁] L') (g : M →ₗ[R₂] M')

/-- If a pair of maps preserves a pairing and the right map is surjective, then the left map sends
the left radical into the target left radical. -/
theorem leftRadical_le_comap_of_surjective_of_pairing (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    leftRadical b ≤ (leftRadical c).comap f := by
  intro x hx
  simpa [hg.forall, hpair] using hx

/-- If a pair of maps preserves a pairing and the left map is surjective, then the right map sends
the right radical into the target right radical. -/
theorem rightRadical_le_comap_of_surjective_of_pairing (hf : Function.Surjective f)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    rightRadical b ≤ (rightRadical c).comap g := by
  intro y hy
  simpa [hf.forall, hpair] using hy

/-- If a pair of maps preserves a pairing, then the left map reflects left radicals: a vector
whose image lies in the target left radical already lies in the source left radical. -/
theorem comap_leftRadical_le_of_pairing (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (leftRadical c).comap f ≤ leftRadical b := by
  intro x hx
  simp only [Submodule.mem_comap, mem_leftRadical_iff] at hx
  simpa [← hpair] using fun y ↦ hx (g y)

/-- If a pair of maps preserves a pairing, then the right map reflects right radicals: a vector
whose image lies in the target right radical already lies in the source right radical. -/
theorem comap_rightRadical_le_of_pairing (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (rightRadical c).comap g ≤ rightRadical b := by
  intro y hy
  simp only [Submodule.mem_comap, mem_rightRadical_iff] at hy
  simpa [← hpair] using fun x ↦ hy (f x)

/-- If a pair of maps preserves a pairing and the right map is surjective, then the source left
radical is the preimage of the target left radical. -/
theorem comap_leftRadical_eq_of_surjective_of_pairing (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (leftRadical c).comap f = leftRadical b :=
  le_antisymm (comap_leftRadical_le_of_pairing b c f g hpair)
    (leftRadical_le_comap_of_surjective_of_pairing b c f g hg hpair)

/-- If a pair of maps preserves a pairing and the left map is surjective, then the source right
radical is the preimage of the target right radical. -/
theorem comap_rightRadical_eq_of_surjective_of_pairing (hf : Function.Surjective f)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (rightRadical c).comap g = rightRadical b :=
  le_antisymm (comap_rightRadical_le_of_pairing b c f g hpair)
    (rightRadical_le_comap_of_surjective_of_pairing b c f g hf hpair)

/-- A pairing-preserving pair of surjective linear maps carries the source left radical onto the
target left radical. -/
theorem map_leftRadical_eq (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (leftRadical b).map f = leftRadical c := by
  rw [← comap_leftRadical_eq_of_surjective_of_pairing b c f g hg hpair,
    Submodule.map_comap_eq_of_surjective hf]

/-- A pairing-preserving pair of surjective linear maps carries the source right radical onto the
target right radical. -/
theorem map_rightRadical_eq (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (rightRadical b).map g = rightRadical c := by
  rw [← comap_rightRadical_eq_of_surjective_of_pairing b c f g hf hpair,
    Submodule.map_comap_eq_of_surjective hg]

end Radicals

section Quotients

variable [CommRing R] [CommRing R₁] [CommRing R₂]
variable [AddCommGroup L] [Module R₁ L] [AddCommGroup M] [Module R₂ M]
variable [AddCommGroup L'] [Module R₁ L'] [AddCommGroup M'] [Module R₂ M']
variable [AddCommGroup L''] [Module R₁ L''] [AddCommGroup M''] [Module R₂ M'']
variable [AddCommGroup P] [Module R P]
variable {ρ : R₁ →+* R} {σ : R₂ →+* R}

section Maps

variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P) (c : L' →ₛₗ[ρ] M' →ₛₗ[σ] P)

/-- A linear map of left arguments descends to the left numerical quotients when it sends the
source left radical into the target left radical. -/
def leftNumericalMap (f : L →ₗ[R₁] L')
    (hf : leftRadical b ≤ (leftRadical c).comap f) :
    LeftNumericalQuotient b →ₗ[R₁] LeftNumericalQuotient c :=
  (leftRadical b).mapQ (leftRadical c) f hf

/-- A linear map of right arguments descends to the right numerical quotients when it sends the
source right radical into the target right radical. -/
def rightNumericalMap (g : M →ₗ[R₂] M')
    (hg : rightRadical b ≤ (rightRadical c).comap g) :
    RightNumericalQuotient b →ₗ[R₂] RightNumericalQuotient c :=
  (rightRadical b).mapQ (rightRadical c) g hg

/-- The map on left numerical quotients sends the class of a representative to the class of its
image. -/
@[simp]
theorem leftNumericalMap_mk (f : L →ₗ[R₁] L')
    (hf : leftRadical b ≤ (leftRadical c).comap f) (x : L) :
    leftNumericalMap b c f hf (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) := by
  simp only [leftNumericalMap, leftNumericalQuotientMk_apply, Submodule.mapQ_apply]

/-- The map on right numerical quotients sends the class of a representative to the class of its
image. -/
@[simp]
theorem rightNumericalMap_mk (g : M →ₗ[R₂] M')
    (hg : rightRadical b ≤ (rightRadical c).comap g) (y : M) :
    rightNumericalMap b c g hg (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) := by
  simp only [rightNumericalMap, rightNumericalQuotientMk_apply, Submodule.mapQ_apply]

/-- A surjective map of left arguments induces a surjective map of left numerical quotients. -/
theorem leftNumericalMap_surjective (f : L →ₗ[R₁] L')
    (hf : leftRadical b ≤ (leftRadical c).comap f) (hfs : Function.Surjective f) :
    Function.Surjective (leftNumericalMap b c f hf) := by
  intro x'
  obtain ⟨x', rfl⟩ := leftNumericalQuotientMk_surjective c x'
  obtain ⟨x, rfl⟩ := hfs x'
  exact ⟨leftNumericalQuotientMk b x, leftNumericalMap_mk b c f hf x⟩

/-- A surjective map of right arguments induces a surjective map of right numerical quotients. -/
theorem rightNumericalMap_surjective (g : M →ₗ[R₂] M')
    (hg : rightRadical b ≤ (rightRadical c).comap g) (hgs : Function.Surjective g) :
    Function.Surjective (rightNumericalMap b c g hg) := by
  intro y'
  obtain ⟨y', rfl⟩ := rightNumericalQuotientMk_surjective c y'
  obtain ⟨y, rfl⟩ := hgs y'
  exact ⟨rightNumericalQuotientMk b y, rightNumericalMap_mk b c g hg y⟩

/-- The identity of the left argument induces the identity on the left numerical quotient. -/
@[simp]
theorem leftNumericalMap_id :
    leftNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (leftRadical b)

/-- The identity of the right argument induces the identity on the right numerical quotient. -/
@[simp]
theorem rightNumericalMap_id :
    rightNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (rightRadical b)

variable (d : L'' →ₛₗ[ρ] M'' →ₛₗ[σ] P)

/-- Composition of left-argument maps induces composition of the maps on left numerical
quotients. -/
theorem leftNumericalMap_comp (f : L →ₗ[R₁] L') (g : L' →ₗ[R₁] L'')
    (hf : leftRadical b ≤ (leftRadical c).comap f)
    (hg : leftRadical c ≤ (leftRadical d).comap g) :
    leftNumericalMap b d (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (leftNumericalMap c d g hg).comp (leftNumericalMap b c f hf) :=
  Submodule.mapQ_comp (leftRadical b) (leftRadical c) (leftRadical d) f g hf hg

/-- Composition of right-argument maps induces composition of the maps on right numerical
quotients. -/
theorem rightNumericalMap_comp (f : M →ₗ[R₂] M') (g : M' →ₗ[R₂] M'')
    (hf : rightRadical b ≤ (rightRadical c).comap f)
    (hg : rightRadical c ≤ (rightRadical d).comap g) :
    rightNumericalMap b d (g.comp f) (hf.trans (Submodule.comap_mono hg)) =
      (rightNumericalMap c d g hg).comp (rightNumericalMap b c f hf) :=
  Submodule.mapQ_comp (rightRadical b) (rightRadical c) (rightRadical d) f g hf hg

end Maps

section PairingMaps

variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P) (c : L' →ₛₗ[ρ] M' →ₛₗ[σ] P)
variable (f : L →ₗ[R₁] L') (g : M →ₗ[R₂] M')

/-- The map induced on left numerical quotients by one half of a pairing-preserving pair is
injective. -/
theorem leftNumericalMap_injective (hf : leftRadical b ≤ (leftRadical c).comap f)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    Function.Injective (leftNumericalMap b c f hf) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  rw [LinearMap.mem_ker, leftNumericalMap_mk, leftNumericalQuotientMk_eq_zero_iff] at hx
  rw [Submodule.mem_bot, leftNumericalQuotientMk_eq_zero_iff]
  exact comap_leftRadical_le_of_pairing b c f g hpair hx

/-- The map induced on right numerical quotients by one half of a pairing-preserving pair is
injective. -/
theorem rightNumericalMap_injective (hg : rightRadical b ≤ (rightRadical c).comap g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    Function.Injective (rightNumericalMap b c g hg) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  rw [LinearMap.mem_ker, rightNumericalMap_mk, rightNumericalQuotientMk_eq_zero_iff] at hy
  rw [Submodule.mem_bot, rightNumericalQuotientMk_eq_zero_iff]
  exact comap_rightRadical_le_of_pairing b c f g hpair hy

/-- A pair of compatible maps on left and right numerical quotients preserves the descended
numerical pairing. -/
theorem numericalPairing_map_map
    (hf : leftRadical b ≤ (leftRadical c).comap f)
    (hg : rightRadical b ≤ (rightRadical c).comap g)
    (hpair : ∀ x y, c (f x) (g y) = b x y)
    (x : LeftNumericalQuotient b) (y : RightNumericalQuotient b) :
    numericalPairing c (leftNumericalMap b c f hf x) (rightNumericalMap b c g hg y) =
      numericalPairing b x y := by
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  simp only [leftNumericalMap_mk, rightNumericalMap_mk, numericalPairing_mk, hpair]

end PairingMaps

section Equivalences

variable (b : L →ₛₗ[ρ] M →ₛₗ[σ] P) (c : L' →ₛₗ[ρ] M' →ₛₗ[σ] P)
variable (f : L →ₗ[R₁] L') (g : M →ₗ[R₂] M')

/-- A pairing-preserving pair of surjective linear maps induces an equivalence of left numerical
quotients. -/
noncomputable def leftNumericalEquiv (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    LeftNumericalQuotient b ≃ₗ[R₁] LeftNumericalQuotient c :=
  LinearEquiv.ofBijective
    (leftNumericalMap b c f (leftRadical_le_comap_of_surjective_of_pairing b c f g hg hpair))
    ⟨leftNumericalMap_injective b c f g _ hpair, leftNumericalMap_surjective b c f _ hf⟩

/-- A pairing-preserving pair of surjective linear maps induces an equivalence of right numerical
quotients. -/
noncomputable def rightNumericalEquiv (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    RightNumericalQuotient b ≃ₗ[R₂] RightNumericalQuotient c :=
  LinearEquiv.ofBijective
    (rightNumericalMap b c g (rightRadical_le_comap_of_surjective_of_pairing b c f g hf hpair))
    ⟨rightNumericalMap_injective b c f g _ hpair, rightNumericalMap_surjective b c g _ hg⟩

/-- The induced equivalence of left numerical quotients sends a representative to the class of
its image. -/
@[simp]
theorem leftNumericalEquiv_mk (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L) :
    leftNumericalEquiv b c f g hf hg hpair (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) :=
  (LinearEquiv.ofBijective_apply _ _).trans (leftNumericalMap_mk b c f _ x)

/-- The induced equivalence of right numerical quotients sends a representative to the class of
its image. -/
@[simp]
theorem rightNumericalEquiv_mk (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M) :
    rightNumericalEquiv b c f g hf hg hpair (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) :=
  (LinearEquiv.ofBijective_apply _ _).trans (rightNumericalMap_mk b c g _ y)

/-- The inverse induced equivalence of left numerical quotients sends the class of an image back
to the class of the representative. -/
@[simp]
theorem leftNumericalEquiv_symm_mk (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L) :
    (leftNumericalEquiv b c f g hf hg hpair).symm (leftNumericalQuotientMk c (f x)) =
      leftNumericalQuotientMk b x := by
  rw [LinearEquiv.symm_apply_eq, leftNumericalEquiv_mk]

/-- The inverse induced equivalence of right numerical quotients sends the class of an image back
to the class of the representative. -/
@[simp]
theorem rightNumericalEquiv_symm_mk (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M) :
    (rightNumericalEquiv b c f g hf hg hpair).symm (rightNumericalQuotientMk c (g y)) =
      rightNumericalQuotientMk b y := by
  rw [LinearEquiv.symm_apply_eq, rightNumericalEquiv_mk]

/-- The equivalences induced on the two numerical quotients preserve the numerical pairing. -/
theorem numericalPairing_equiv_equiv (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y)
    (x : LeftNumericalQuotient b) (y : RightNumericalQuotient b) :
    numericalPairing c (leftNumericalEquiv b c f g hf hg hpair x)
        (rightNumericalEquiv b c f g hf hg hpair y) = numericalPairing b x y := by
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  simp only [leftNumericalEquiv_mk, rightNumericalEquiv_mk, numericalPairing_mk, hpair]

end Equivalences

end Quotients

end TauCeti
