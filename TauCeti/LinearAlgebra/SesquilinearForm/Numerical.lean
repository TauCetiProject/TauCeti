/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Numerical quotients of sesquilinear maps

For a sesquilinear map, the elements annihilated in the first and second arguments are separate
submodules. This file quotients by those two radicals and supplies the representative and
nondegeneracy lemmas needed to use the resulting pairing. It also records the independent
functoriality conditions: a map of first arguments must preserve the left radical, while a map of
second arguments must preserve the right radical.

The construction is the sesquilinear counterpart of
`TauCeti.LinearAlgebra.BilinearMap.NumericalQuotient`. It uses Mathlib's `LinearMap.liftQ₂`, so
the first argument may be semilinear along an arbitrary endomorphism of the coefficient ring. In
particular, it applies to Laurent-valued forms with the coefficient involution
`LaurentPolynomial.invert`.

The distinction between the two radicals and the corresponding numerical quotients follows
Dancso--Licata, *Koszul algebras and flow lattices*, Section 3.1.
-/

public section

namespace TauCeti

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace SesquilinearNumerical

variable {R : Type*} [CommRing R]
variable {L : Type u₁} {M : Type u₂} {P : Type u₃}
variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable [AddCommGroup P] [Module R P]
variable {σ : R →+* R}

section Radicals

variable (b : L →ₛₗ[σ] M →ₗ[R] P)

/-- The **left radical** of a sesquilinear map: elements pairing to zero with every second
argument. -/
def leftRadical : Submodule R L := b.ker

/-- The **right radical** of a sesquilinear map: elements pairing to zero with every first
argument. -/
def rightRadical : Submodule R M := b.flip.ker

@[simp]
theorem mem_leftRadical_iff (x : L) : x ∈ leftRadical b ↔ ∀ y : M, b x y = 0 := by
  rw [leftRadical, LinearMap.mem_ker]
  constructor
  · intro h y
    rw [h, LinearMap.zero_apply]
  · intro h
    ext y
    exact (h y).trans (LinearMap.zero_apply y).symm

@[simp]
theorem mem_rightRadical_iff (y : M) : y ∈ rightRadical b ↔ ∀ x : L, b x y = 0 := by
  rw [rightRadical, LinearMap.mem_ker]
  constructor
  · intro h x
    rw [← b.flip_apply x y, h, LinearMap.zero_apply]
  · intro h
    ext x
    simpa only [LinearMap.flip_apply, LinearMap.zero_apply] using h x

end Radicals

section Quotients

variable (b : L →ₛₗ[σ] M →ₗ[R] P)

/-- The quotient of the first argument by the left radical. -/
abbrev LeftNumericalQuotient := L ⧸ leftRadical b

/-- The quotient of the second argument by the right radical. -/
abbrev RightNumericalQuotient := M ⧸ rightRadical b

/-- The quotient map from the first argument to its numerical quotient. -/
def leftNumericalQuotientMk : L →ₗ[R] LeftNumericalQuotient b :=
  (leftRadical b).mkQ

/-- The quotient map from the second argument to its numerical quotient. -/
def rightNumericalQuotientMk : M →ₗ[R] RightNumericalQuotient b :=
  (rightRadical b).mkQ

@[simp]
theorem leftNumericalQuotientMk_apply (x : L) :
    leftNumericalQuotientMk b x = Submodule.Quotient.mk x :=
  Submodule.mkQ_apply (leftRadical b) x

@[simp]
theorem rightNumericalQuotientMk_apply (y : M) :
    rightNumericalQuotientMk b y = Submodule.Quotient.mk y :=
  Submodule.mkQ_apply (rightRadical b) y

@[simp]
theorem ker_leftNumericalQuotientMk : (leftNumericalQuotientMk b).ker = leftRadical b :=
  (leftRadical b).ker_mkQ

@[simp]
theorem ker_rightNumericalQuotientMk : (rightNumericalQuotientMk b).ker = rightRadical b :=
  (rightRadical b).ker_mkQ

theorem leftNumericalQuotientMk_surjective :
    Function.Surjective (leftNumericalQuotientMk b) :=
  (leftRadical b).mkQ_surjective

theorem rightNumericalQuotientMk_surjective :
    Function.Surjective (rightNumericalQuotientMk b) :=
  (rightRadical b).mkQ_surjective

@[simp]
theorem leftNumericalQuotientMk_eq_zero_iff (x : L) :
    leftNumericalQuotientMk b x = 0 ↔ x ∈ leftRadical b := by
  rw [← LinearMap.mem_ker, ker_leftNumericalQuotientMk]

@[simp]
theorem rightNumericalQuotientMk_eq_zero_iff (y : M) :
    rightNumericalQuotientMk b y = 0 ↔ y ∈ rightRadical b := by
  rw [← LinearMap.mem_ker, ker_rightNumericalQuotientMk]

@[simp]
theorem leftNumericalQuotientMk_eq_iff (x x' : L) :
    leftNumericalQuotientMk b x = leftNumericalQuotientMk b x' ↔
      x - x' ∈ leftRadical b := by
  rw [← sub_eq_zero, ← map_sub, leftNumericalQuotientMk_eq_zero_iff]

@[simp]
theorem rightNumericalQuotientMk_eq_iff (y y' : M) :
    rightNumericalQuotientMk b y = rightNumericalQuotientMk b y' ↔
      y - y' ∈ rightRadical b := by
  rw [← sub_eq_zero, ← map_sub, rightNumericalQuotientMk_eq_zero_iff]

/-- The pairing after quotienting only its first argument. -/
def leftNumericalPairing : LeftNumericalQuotient b →ₛₗ[σ] M →ₗ[R] P :=
  (leftRadical b).liftQ b le_rfl

/-- The pairing after quotienting only its second argument. -/
def rightNumericalPairing : L →ₛₗ[σ] RightNumericalQuotient b →ₗ[R] P :=
  ((rightRadical b).liftQ b.flip le_rfl).flip

@[simp]
theorem leftNumericalPairing_mk (x : L) (y : M) :
    leftNumericalPairing b (leftNumericalQuotientMk b x) y = b x y := by
  rw [leftNumericalPairing, leftNumericalQuotientMk, Submodule.mkQ_apply]
  exact DFunLike.congr_fun (Submodule.liftQ_apply (leftRadical b) b x) y

@[simp]
theorem rightNumericalPairing_mk (x : L) (y : M) :
    rightNumericalPairing b x (rightNumericalQuotientMk b y) = b x y := by
  rw [rightNumericalPairing, rightNumericalQuotientMk, Submodule.mkQ_apply]
  simpa only [LinearMap.flip_apply] using
    DFunLike.congr_fun (Submodule.liftQ_apply (rightRadical b) b.flip y) x

/-- Quotienting the first argument makes the pairing left-separating. -/
theorem leftNumericalPairing_separatingLeft : (leftNumericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  rw [leftNumericalQuotientMk_eq_zero_iff]
  exact (mem_leftRadical_iff b x).mpr fun y ↦ leftNumericalPairing_mk b x y ▸ hq y

/-- Quotienting the second argument makes the pairing right-separating. -/
theorem rightNumericalPairing_separatingRight : (rightNumericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  rw [rightNumericalQuotientMk_eq_zero_iff]
  exact (mem_rightRadical_iff b y).mpr fun x ↦ rightNumericalPairing_mk b x y ▸ hq x

/-- The pairing after quotienting both arguments by their respective radicals. -/
def numericalPairing :
    LeftNumericalQuotient b →ₛₗ[σ] RightNumericalQuotient b →ₗ[R] P :=
  b.liftQ₂ (leftRadical b) (rightRadical b) le_rfl le_rfl

@[simp]
theorem numericalPairing_mk (x : L) (y : M) :
    numericalPairing b (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) =
      b x y := by
  rw [numericalPairing, leftNumericalQuotientMk, rightNumericalQuotientMk,
    Submodule.mkQ_apply]
  exact LinearMap.liftQ₂_mk le_rfl le_rfl x y

/-- The two-sided quotient pairing is uniquely determined by its representative values. -/
theorem numericalPairing_unique
    (c : LeftNumericalQuotient b →ₛₗ[σ] RightNumericalQuotient b →ₗ[R] P)
    (hc : ∀ x y, c (leftNumericalQuotientMk b x) (rightNumericalQuotientMk b y) = b x y) :
    c = numericalPairing b := by
  apply LinearMap.ext₂
  intro q r
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b r
  rw [hc, numericalPairing_mk]

theorem numericalPairing_separatingLeft : (numericalPairing b).SeparatingLeft := by
  intro q hq
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b q
  rw [leftNumericalQuotientMk_eq_zero_iff]
  refine (mem_leftRadical_iff b x).mpr fun y ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq (rightNumericalQuotientMk b y)

theorem numericalPairing_separatingRight : (numericalPairing b).SeparatingRight := by
  intro q hq
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b q
  rw [rightNumericalQuotientMk_eq_zero_iff]
  refine (mem_rightRadical_iff b y).mpr fun x ↦ ?_
  rw [← numericalPairing_mk b x y]
  exact hq (leftNumericalQuotientMk b x)

/-- The two-sided numerical pairing is nondegenerate in both arguments. -/
theorem numericalPairing_nondegenerate : (numericalPairing b).Nondegenerate :=
  ⟨numericalPairing_separatingLeft b, numericalPairing_separatingRight b⟩

end Quotients

section Functoriality

variable {L' : Type u₄} {M' : Type u₅}
variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']
variable (b : L →ₛₗ[σ] M →ₗ[R] P) (c : L' →ₛₗ[σ] M' →ₗ[R] P)
variable (f : L →ₗ[R] L') (g : M →ₗ[R] M')

/-- A first-argument map descends when it sends the source left radical into the target left
radical. -/
def leftNumericalMap (hf : leftRadical b ≤ (leftRadical c).comap f) :
    LeftNumericalQuotient b →ₗ[R] LeftNumericalQuotient c :=
  (leftRadical b).mapQ (leftRadical c) f hf

/-- A second-argument map descends when it sends the source right radical into the target right
radical. -/
def rightNumericalMap (hg : rightRadical b ≤ (rightRadical c).comap g) :
    RightNumericalQuotient b →ₗ[R] RightNumericalQuotient c :=
  (rightRadical b).mapQ (rightRadical c) g hg

@[simp]
theorem leftNumericalMap_mk (hf : leftRadical b ≤ (leftRadical c).comap f) (x : L) :
    leftNumericalMap b c f hf (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) := by
  simp only [leftNumericalMap, leftNumericalQuotientMk_apply, Submodule.mapQ_apply]

@[simp]
theorem rightNumericalMap_mk (hg : rightRadical b ≤ (rightRadical c).comap g) (y : M) :
    rightNumericalMap b c g hg (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) := by
  simp only [rightNumericalMap, rightNumericalQuotientMk_apply, Submodule.mapQ_apply]

/-- A pair of compatible maps preserves the quotient pairing. -/
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

/-- Pairing-preserving maps send radicals into radicals, provided the opposite map is surjective. -/
theorem leftRadical_le_comap_of_surjective_of_pairing (hg : Function.Surjective g)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    leftRadical b ≤ (leftRadical c).comap f := by
  intro x hx
  rw [Submodule.mem_comap, mem_leftRadical_iff]
  intro y'
  obtain ⟨y, rfl⟩ := hg y'
  rw [hpair]
  exact (mem_leftRadical_iff b x).mp hx y

theorem rightRadical_le_comap_of_surjective_of_pairing (hf : Function.Surjective f)
    (hpair : ∀ x y, c (f x) (g y) = b x y) :
    rightRadical b ≤ (rightRadical c).comap g := by
  intro y hy
  rw [Submodule.mem_comap, mem_rightRadical_iff]
  intro x'
  obtain ⟨x, rfl⟩ := hf x'
  rw [hpair]
  exact (mem_rightRadical_iff b y).mp hy x

end Functoriality

section FunctorialityLaws

variable {L' : Type u₄} {M' : Type u₅} {L'' : Type u₆} {M'' : Type u₇}
variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']
variable [AddCommGroup L''] [Module R L''] [AddCommGroup M''] [Module R M'']
variable (b : L →ₛₗ[σ] M →ₗ[R] P) (c : L' →ₛₗ[σ] M' →ₗ[R] P)
variable (d : L'' →ₛₗ[σ] M'' →ₗ[R] P)

@[simp]
theorem leftNumericalMap_id :
    leftNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (leftRadical b)

@[simp]
theorem rightNumericalMap_id :
    rightNumericalMap b b LinearMap.id (by rw [Submodule.comap_id]) = LinearMap.id :=
  Submodule.mapQ_id (rightRadical b)

/-- Composition of maps on first arguments induces composition on left numerical quotients. -/
theorem leftNumericalMap_comp (f₁ : L →ₗ[R] L') (f₂ : L' →ₗ[R] L'')
    (hf₁ : leftRadical b ≤ (leftRadical c).comap f₁)
    (hf₂ : leftRadical c ≤ (leftRadical d).comap f₂) :
    leftNumericalMap b d (f₂.comp f₁) (hf₁.trans (Submodule.comap_mono hf₂)) =
      (leftNumericalMap c d f₂ hf₂).comp (leftNumericalMap b c f₁ hf₁) :=
  Submodule.mapQ_comp (leftRadical b) (leftRadical c) (leftRadical d) f₁ f₂ hf₁ hf₂

/-- Composition of maps on second arguments induces composition on right numerical quotients. -/
theorem rightNumericalMap_comp (g₁ : M →ₗ[R] M') (g₂ : M' →ₗ[R] M'')
    (hg₁ : rightRadical b ≤ (rightRadical c).comap g₁)
    (hg₂ : rightRadical c ≤ (rightRadical d).comap g₂) :
    rightNumericalMap b d (g₂.comp g₁) (hg₁.trans (Submodule.comap_mono hg₂)) =
      (rightNumericalMap c d g₂ hg₂).comp (rightNumericalMap b c g₁ hg₁) :=
  Submodule.mapQ_comp (rightRadical b) (rightRadical c) (rightRadical d) g₁ g₂ hg₁ hg₂

end FunctorialityLaws

section Equivalences

variable {L' : Type u₄} {M' : Type u₅}
variable [AddCommGroup L'] [Module R L'] [AddCommGroup M'] [Module R M']
variable (b : L →ₛₗ[σ] M →ₗ[R] P) (c : L' →ₛₗ[σ] M' →ₗ[R] P)
variable (f : L ≃ₗ[R] L') (g : M ≃ₗ[R] M')

/-- Pairing-preserving linear equivalences identify the corresponding left radicals. -/
theorem map_leftRadical_eq (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (leftRadical b).map (f : L →ₗ[R] L') = leftRadical c := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact leftRadical_le_comap_of_surjective_of_pairing b c f g g.surjective hpair
  · intro x' hx'
    obtain ⟨x, rfl⟩ := f.surjective x'
    refine ⟨x, ?_, rfl⟩
    exact (mem_leftRadical_iff b x).mpr fun y ↦ by
      rw [← hpair]
      exact (mem_leftRadical_iff c (f x)).mp hx' (g y)

/-- Pairing-preserving linear equivalences identify the corresponding right radicals. -/
theorem map_rightRadical_eq (hpair : ∀ x y, c (f x) (g y) = b x y) :
    (rightRadical b).map (g : M →ₗ[R] M') = rightRadical c := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact rightRadical_le_comap_of_surjective_of_pairing b c f g f.surjective hpair
  · intro y' hy'
    obtain ⟨y, rfl⟩ := g.surjective y'
    refine ⟨y, ?_, rfl⟩
    exact (mem_rightRadical_iff b y).mpr fun x ↦ by
      rw [← hpair]
      exact (mem_rightRadical_iff c (g y)).mp hy' (f x)

/-- A pairing-preserving pair of linear equivalences induces an equivalence of left numerical
quotients. -/
def leftNumericalEquiv (hpair : ∀ x y, c (f x) (g y) = b x y) :
    LeftNumericalQuotient b ≃ₗ[R] LeftNumericalQuotient c :=
  Submodule.Quotient.equiv (leftRadical b) (leftRadical c) f
    (map_leftRadical_eq b c f g hpair)

/-- A pairing-preserving pair of linear equivalences induces an equivalence of right numerical
quotients. -/
def rightNumericalEquiv (hpair : ∀ x y, c (f x) (g y) = b x y) :
    RightNumericalQuotient b ≃ₗ[R] RightNumericalQuotient c :=
  Submodule.Quotient.equiv (rightRadical b) (rightRadical c) g
    (map_rightRadical_eq b c f g hpair)

@[simp]
theorem leftNumericalEquiv_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L) :
    leftNumericalEquiv b c f g hpair (leftNumericalQuotientMk b x) =
      leftNumericalQuotientMk c (f x) := by
  simp only [leftNumericalEquiv, Submodule.Quotient.equiv_apply,
    leftNumericalQuotientMk_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

@[simp]
theorem rightNumericalEquiv_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M) :
    rightNumericalEquiv b c f g hpair (rightNumericalQuotientMk b y) =
      rightNumericalQuotientMk c (g y) := by
  simp only [rightNumericalEquiv, Submodule.Quotient.equiv_apply,
    rightNumericalQuotientMk_apply, Submodule.mapQ_apply, LinearEquiv.coe_coe]

@[simp]
theorem leftNumericalEquiv_symm_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (x : L') :
    (leftNumericalEquiv b c f g hpair).symm (leftNumericalQuotientMk c x) =
      leftNumericalQuotientMk b (f.symm x) := by
  rw [LinearEquiv.symm_apply_eq, leftNumericalEquiv_mk, LinearEquiv.apply_symm_apply]

@[simp]
theorem rightNumericalEquiv_symm_mk (hpair : ∀ x y, c (f x) (g y) = b x y) (y : M') :
    (rightNumericalEquiv b c f g hpair).symm (rightNumericalQuotientMk c y) =
      rightNumericalQuotientMk b (g.symm y) := by
  rw [LinearEquiv.symm_apply_eq, rightNumericalEquiv_mk, LinearEquiv.apply_symm_apply]

/-- The equivalences induced by a pairing equivalence preserve the numerical pairing. -/
theorem numericalPairing_equiv_equiv
    (hpair : ∀ x y, c (f x) (g y) = b x y)
    (x : LeftNumericalQuotient b) (y : RightNumericalQuotient b) :
    numericalPairing c (leftNumericalEquiv b c f g hpair x)
        (rightNumericalEquiv b c f g hpair y) = numericalPairing b x y := by
  obtain ⟨x, rfl⟩ := leftNumericalQuotientMk_surjective b x
  obtain ⟨y, rfl⟩ := rightNumericalQuotientMk_surjective b y
  simp only [leftNumericalEquiv_mk, rightNumericalEquiv_mk, numericalPairing_mk, hpair]

end Equivalences

end SesquilinearNumerical

end TauCeti
