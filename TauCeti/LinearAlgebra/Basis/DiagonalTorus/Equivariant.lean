/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Field.Equivariant
public import TauCeti.LinearAlgebra.Basis.DiagonalTorus.Basic
public import Mathlib.GroupTheory.Divisible

/-!
# Scalar rigidity for split-torus characters

Over a ring with divisible units, every nonzero split-torus character is surjective on
points. Consequently a nonzero additive map between fields equivariant for two torus
characters is a scalar multiple of a unique field homomorphism. The homomorphism carries
the source character to the target character.

For a standard endomorphism of a split semisimple group, the pinning equation gives exactly
this equivariance on each root subgroup: the source character is the root, and the target
character is the pullback of the image root. This isolates the field homomorphism without
assuming that the root-subgroup map is algebraic. The source character need not be primitive;
for instance, the root character of the simply connected group of type A₁ is twice a
fundamental weight.

The field-homomorphism construction is `AddMonoidHom.existsUnique_ringHom_of_equivariant`.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS 80 (1968), §11.
* R. W. Carter, *Finite Groups of Lie Type*, §1.15.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A nonzero character of a split torus is surjective on points when the coefficient ring
has divisible units. In particular, this applies over an algebraically closed field and
does not require the character to be primitive. -/
theorem torusCharacter_surjective {R : Type*} [CommRing R] [RootableBy Rˣ ℕ]
    {α : ι → ℤ} (hα : α ≠ 0) :
    Function.Surjective (fun s : ι → Rˣ => torusCharacter s α) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := Function.ne_iff.mp hα
  let : RootableBy Rˣ ℤ := Group.rootableByIntOfRootableByNat Rˣ
  intro u
  obtain ⟨v, hv⟩ := RootableBy.surjective_pow Rˣ ℤ hi u
  exact ⟨Pi.mulSingle i v, by simpa using hv⟩

/-- A nonzero additive map equivariant for torus characters is a scalar multiple of a unique
field endomorphism. The source character must be nonzero, and the field must have
divisible units. The character equation
also shows that the target character is trivial on the kernel of the source character. -/
theorem existsUnique_ringHom_of_torusCharacter_equivariant
    {K : Type*} [Field K] [RootableBy Kˣ ℕ]
    {α β : ι → ℤ} (hα : α ≠ 0) (f : K →+ K) (hf : f ≠ 0)
    (heq : ∀ (s : ι → Kˣ) x,
      f ((torusCharacter s α : K) * x) = (torusCharacter s β : K) * f x) :
    ∃! g : K →+* K, (∀ x, f x = f 1 * g x) ∧
      ∀ s : ι → Kˣ, g (torusCharacter s α : K) = (torusCharacter s β : K) := by
  exact f.existsUnique_ringHom_of_equivariant (torusCharacter_surjective hα) hf heq

end TauCeti
