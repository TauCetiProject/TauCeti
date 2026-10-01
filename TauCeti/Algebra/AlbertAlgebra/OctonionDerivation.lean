/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.AlbertAlgebra` and `TauCeti.derivationLieAlgebra R (TauCeti.Octonion R)` both occur in
-- the statements below; the latter, together with the skewness of an octonion derivation for the
-- norm form that the Hermitian product is built from, comes from `TauCeti.Algebra.Octonion.
-- Derivation`, which also re-exports `TauCeti.Algebra.Lie.Derivation.Basic`.
public import TauCeti.Algebra.AlbertAlgebra.Basic
public import TauCeti.Algebra.Octonion.Derivation
-- Non-public: `Mathlib.Tactic.LinearCombination` is used only inside the proof of the Leibniz rule
-- on the scalar diagonal, and `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas` only inside the
-- proof of the rank bound at the end of the file.
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Octonion derivations act on the split Albert algebra

`F₄` is the derivation algebra of the split Albert algebra `J = H₃(𝕆)` and `G₂` is the derivation
algebra of the split octonions, so the inclusion `G₂ ↪ F₄` ought to be visible before either
algebra is identified with its Serre-construction namesake. It is: a derivation `D` of `𝕆` applied
to each off-diagonal entry of a Hermitian matrix, and zero on the scalar diagonal, is a derivation
of `J`.

Writing a Hermitian matrix as its scalar diagonal `d` together with its three octonion entries `x`,
the symmetrized product `A ∘ B = ½ (A B + B A)` of `TauCeti/Algebra/AlbertAlgebra/Basic.lean` has
diagonal `d i e i + β (x (i + 1)) (y (i + 1)) + β (x (i + 2)) (y (i + 2))`, for `β` the symmetric
bilinear form of the split-octonion norm, and entries
`½ ((d (i + 1) + d (i + 2)) • y i + (e (i + 1) + e (i + 2)) • x i)` corrected by the conjugate of
`½ (x (i + 1) * y (i + 2) + y (i + 1) * x (i + 2))`. Both halves of the Leibniz rule are then
octonion facts already in `TauCeti/Algebra/Octonion/Derivation.lean`: on the diagonal the two
surviving terms are `β (D x) y + β x (D y)`, which vanishes because a derivation is **skew** for
the norm form (`TauCeti.Octonion.polar_derivation_apply_left_eq_neg`), and off it the entries are
differentiated by the octonion Leibniz rule together with the fact that a derivation **commutes
with conjugation** (`TauCeti.Octonion.derivation_apply_conj`).

The assignment is a homomorphism of Lie algebras `Der 𝕆 →ₗ⁅R⁆ Der J`, because applying a derivation
entrywise is multiplicative for the composition of endomorphisms, and it is injective, because a
single off-diagonal slot already sees all of `𝕆`. Over a field in which `2` is invertible the
fourteen independent derivations of `𝕆` of
`TauCeti.Octonion.fourteen_le_finrank_derivationLieAlgebra` therefore give
`14 ≤ finrank (Der J)`, the first instalment of the dimension `52` of `F₄`.

## Main definitions

* `TauCeti.AlbertAlgebra.offDiagMap`: a linear endomorphism of `𝕆` acting on `H₃(𝕆)` by its
  off-diagonal entries, as a linear map `End 𝕆 →ₗ[R] End H₃(𝕆)`.
* `TauCeti.AlbertAlgebra.ofOctonionDerivation`: the induced homomorphism of Lie algebras
  `Der 𝕆 →ₗ⁅R⁆ Der H₃(𝕆)`, the inclusion `G₂ ↪ F₄` in derivation form.

## Main results

* `TauCeti.AlbertAlgebra.offDiagMap_mem_derivationLieAlgebra`: the entrywise action of a derivation
  of `𝕆` is a derivation of `H₃(𝕆)`.
* `TauCeti.AlbertAlgebra.offDiagMap_apply_diagIdempotent` and
  `TauCeti.AlbertAlgebra.offDiagMap_apply_offDiagSingle`: the action kills the diagonal frame and
  sends the `j`-th off-diagonal slot `Fⱼ(a)` to `Fⱼ(f a)`.
* `TauCeti.AlbertAlgebra.ofOctonionDerivation_injective`: the inclusion is injective, and
  `TauCeti.AlbertAlgebra.fourteen_le_finrank_derivationLieAlgebra`: hence `14 ≤ finrank (Der J)`
  over a field in which `2` is invertible.

## Implementation notes

Everything is stated over a commutative ring; `2` is inverted only from the point where the
symmetrized product enters, as it must be for that product to exist at all, and the base is a field
only in the final rank bound.

`TauCeti.AlbertAlgebra.offDiagMap` is built on bare endomorphisms rather than on derivations, so
that its additivity, its homogeneity and its multiplicativity for composition are available before
any Leibniz rule is proved; `TauCeti.AlbertAlgebra.ofOctonionDerivation` is then assembled from
those three facts with no further computation. The skewness of a derivation for the norm form is
available as a statement about `QuadraticMap.polar`, whereas the Hermitian product is written with
`QuadraticMap.associated`, its half; the private lemma below crosses that factor of two once.

## References

* `TauCeti/Algebra/Octonion/Derivation.lean`, which supplies both octonion inputs, and
  `TauCeti/Algebra/AlbertAlgebra/Derivation.lean`, which studies `Der H₃(𝕆)` from the other side,
  through the Peirce calculus of the diagonal frame.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*, §5.3,
  where `Der H₃(𝕆)` is decomposed as `Der 𝕆` plus the traceless anti-Hermitian matrices; only the
  first summand, and so only the bound `14 ≤ finrank`, is built here.
-/

public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*} [CommRing R]

/-! ### Acting on the off-diagonal entries -/

/-- A linear endomorphism `f` of the split octonions acts on `H₃(𝕆)` by applying `f` to each of the
three off-diagonal entries and sending the scalar diagonal to `0`. The assignment `f ↦ this` is
itself linear, and multiplicative for composition
(`TauCeti.AlbertAlgebra.offDiagMap_mul`); killing the diagonal is what makes the latter true. -/
def offDiagMap : Module.End R (Octonion R) →ₗ[R] Module.End R (AlbertAlgebra R) where
  toFun f :=
    { toFun := fun A => ⟨0, fun i => f (A.offDiag i)⟩
      map_add' := fun A B =>
        AlbertAlgebra.ext (add_zero (0 : Fin 3 → R)).symm (funext fun i => by simp)
      map_smul' := fun r A =>
        AlbertAlgebra.ext (smul_zero r).symm (funext fun i => by simp) }
  map_add' f g := LinearMap.ext fun A =>
    AlbertAlgebra.ext (add_zero (0 : Fin 3 → R)).symm (rfl)
  map_smul' r f := LinearMap.ext fun A =>
    AlbertAlgebra.ext (smul_zero r).symm (rfl)

@[simp] theorem offDiagMap_apply_diag (f : Module.End R (Octonion R)) (A : AlbertAlgebra R) :
    (offDiagMap f A).diag = 0 :=
  (rfl)

@[simp] theorem offDiagMap_apply_offDiag (f : Module.End R (Octonion R)) (A : AlbertAlgebra R)
    (i : Fin 3) : (offDiagMap f A).offDiag i = f (A.offDiag i) :=
  (rfl)

/-- **The action kills the diagonal frame**: the idempotent `Eᵢ` has no off-diagonal entry, and the
scalar diagonal is sent to `0`. -/
@[simp] theorem offDiagMap_apply_diagIdempotent (f : Module.End R (Octonion R)) (i : Fin 3) :
    offDiagMap f (diagIdempotent R i) = 0 :=
  AlbertAlgebra.ext (rfl) (funext fun _ => by simp)

/-- **The action sends the `j`-th off-diagonal slot to itself, through `f`**: `Fⱼ(a) ↦ Fⱼ(f a)`.
Together with `TauCeti.AlbertAlgebra.offDiagMap_apply_diagIdempotent` and
`TauCeti.AlbertAlgebra.eq_sum_smul_diagIdempotent_add_sum_offDiagSingle`, which says the frame and
the slots span `H₃(𝕆)`, this determines the action. -/
@[simp] theorem offDiagMap_apply_offDiagSingle (f : Module.End R (Octonion R)) (j : Fin 3)
    (a : Octonion R) : offDiagMap f (offDiagSingle j a) = offDiagSingle j (f a) :=
  AlbertAlgebra.ext (by simp) (funext fun i => by
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Pi.single_eq_of_ne h])

/-- **Acting on the off-diagonal entries is multiplicative**: the composition of two octonion
endomorphisms acts as the composition of their actions. The scalar diagonal plays no part because
both sides kill it. -/
theorem offDiagMap_mul (f g : Module.End R (Octonion R)) :
    offDiagMap (f * g) = offDiagMap f * offDiagMap g :=
  LinearMap.ext fun _ => AlbertAlgebra.ext (rfl) (rfl)

/-- **A single off-diagonal slot already sees all of `𝕆`**, so an octonion endomorphism is
determined by its action on `H₃(𝕆)`. -/
theorem offDiagMap_injective : Function.Injective (offDiagMap (R := R)) := by
  intro f g h
  refine LinearMap.ext fun x => ?_
  have h' := congrArg
    (fun F : Module.End R (AlbertAlgebra R) => (F (offDiagSingle 0 x)).offDiag 0) h
  simpa using h'

/-! ### The induced derivation -/

section Derivation

variable [Invertible (2 : R)] (D : derivationLieAlgebra R (Octonion R))

/-- The skewness of an octonion derivation for the norm form, in the half-polar form
`QuadraticMap.associated` in which the Hermitian product of
`TauCeti/Algebra/AlbertAlgebra/Basic.lean` is written: `β (D x) y + β x (D y) = 0`. -/
private theorem associated_derivation_add_eq_zero (x y : Octonion R) :
    QuadraticMap.associated (Octonion.normQuadraticForm R)
        ((D : Module.End R (Octonion R)) x) y
      + QuadraticMap.associated (Octonion.normQuadraticForm R) x
        ((D : Module.End R (Octonion R)) y) = 0 := by
  have hhalf : ∀ a b : Octonion R,
      QuadraticMap.associated (Octonion.normQuadraticForm R) a b
        = ⅟(2 : Module.End R R) • QuadraticMap.polar (Octonion.normQuadraticForm R) a b :=
    fun _ _ => (rfl)
  rw [hhalf, hhalf, ← smul_add, Octonion.polar_derivation_apply_left_eq_neg, neg_add_cancel,
    smul_zero]

/-- **A derivation of `𝕆` acts on `H₃(𝕆)` by a derivation.** On the scalar diagonal the Leibniz
rule is the skewness of `D` for the norm form, and on the octonion entries it is the Leibniz rule
of `D` together with the fact that `D` commutes with conjugation. No Jordan identity is involved;
only the coordinate form of the symmetrized product is. -/
theorem offDiagMap_mem_derivationLieAlgebra :
    offDiagMap (D : Module.End R (Octonion R)) ∈ derivationLieAlgebra R (AlbertAlgebra R) := by
  refine mem_derivationLieAlgebra.mpr fun A B => ?_
  refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [offDiagMap_apply_diag, Pi.zero_apply, add_diag, Pi.add_apply, mul_diag,
      offDiagMap_apply_offDiag, zero_mul, mul_zero, zero_add]
    linear_combination -associated_derivation_add_eq_zero D (A.offDiag (i + 1)) (B.offDiag (i + 1))
      - associated_derivation_add_eq_zero D (A.offDiag (i + 2)) (B.offDiag (i + 2))
  · simp only [offDiagMap_apply_offDiag, add_offDiag, Pi.add_apply, mul_offDiag,
      offDiagMap_apply_diag, Pi.zero_apply, map_add, map_smul, add_zero, zero_add, zero_smul,
      Octonion.derivation_apply_conj, derivationLieAlgebra.leibniz, smul_add]
    module

variable (R) in
/-- **Derivations of the split octonions, as derivations of the split Albert algebra.** This is the
inclusion `G₂ ↪ F₄` in derivation form, before either side is identified with the Serre
construction; it is injective by `TauCeti.AlbertAlgebra.ofOctonionDerivation_injective`. -/
def ofOctonionDerivation :
    derivationLieAlgebra R (Octonion R) →ₗ⁅R⁆ derivationLieAlgebra R (AlbertAlgebra R) where
  toFun D := ⟨offDiagMap (D : Module.End R (Octonion R)),
    offDiagMap_mem_derivationLieAlgebra D⟩
  map_add' D E := Subtype.ext (map_add offDiagMap (D : Module.End R (Octonion R)) E)
  map_smul' r D := Subtype.ext (map_smul offDiagMap r (D : Module.End R (Octonion R)))
  map_lie' {D E} := Subtype.ext <| by
    have h : ∀ f g : Module.End R (Octonion R),
        offDiagMap ⁅f, g⁆ = ⁅offDiagMap f, offDiagMap g⁆ := fun f g => by
      rw [Ring.lie_def, Ring.lie_def, map_sub, offDiagMap_mul, offDiagMap_mul]
    exact h (D : Module.End R (Octonion R)) E

@[simp] theorem coe_ofOctonionDerivation :
    ((ofOctonionDerivation R D : derivationLieAlgebra R (AlbertAlgebra R)) :
        Module.End R (AlbertAlgebra R))
      = offDiagMap (D : Module.End R (Octonion R)) :=
  (rfl)

variable (R) in
/-- **The inclusion `Der 𝕆 ↪ Der H₃(𝕆)` is injective.** Reading off the zeroth off-diagonal slot
recovers the octonion derivation from the derivation it induces. -/
theorem ofOctonionDerivation_injective :
    Function.Injective (ofOctonionDerivation R) := by
  intro D E h
  refine derivationLieAlgebra.ext fun x => ?_
  have h' := congrArg (fun F : derivationLieAlgebra R (AlbertAlgebra R) =>
    ((F : Module.End R (AlbertAlgebra R)) (offDiagSingle 0 x)).offDiag 0) h
  simpa using h'

/-- **`Der H₃(𝕆)` has rank at least `14`.** The fourteen independent derivations of the split
octonions of `TauCeti.Octonion.fourteen_le_finrank_derivationLieAlgebra` remain
independent after being pushed into `Der H₃(𝕆)`. The matching `52`, and with it the identification
of `Der H₃(𝕆)` with the exceptional Lie algebra `F₄`, needs the traceless anti-Hermitian
derivations as well and is not proved here. -/
theorem fourteen_le_finrank_derivationLieAlgebra (K : Type*) [Field K] [Invertible (2 : K)] :
    14 ≤ Module.finrank K (derivationLieAlgebra K (AlbertAlgebra K)) :=
  le_trans (Octonion.fourteen_le_finrank_derivationLieAlgebra K)
    (LinearMap.finrank_le_finrank_of_injective
      (f := (ofOctonionDerivation K).toLinearMap) (ofOctonionDerivation_injective K))

end Derivation

end AlbertAlgebra

end TauCeti
