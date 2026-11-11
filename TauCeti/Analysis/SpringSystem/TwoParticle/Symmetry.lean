/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RepresentationTheory.Equiv
public import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
public import TauCeti.Analysis.SpringSystem.TwoParticle.Basic
public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Two particles on a spring: the symmetry group `C₂ × C₂` and its isotypic projectors

Two particles rest at `(0, 0)` and `(1, 0)` in the plane, joined by a spring; their displacements
are the vectors `u = (x₁, y₁, x₂, y₂)` of `Fin 4 → ℝ`, in the coordinate order of
`TauCeti.TwoParticleSpring.forceMatrix`. The rest configuration has two commuting reflection
symmetries:

* `r = diag(1, -1, 1, -1)` (`TauCeti.TwoParticleSpring.axisReflection`), the reflection in the
  line through the two particles, which reverses every vertical displacement;
* `s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)` (`TauCeti.TwoParticleSpring.bisectorReflection`), the
  reflection in the perpendicular bisector of the spring, which exchanges the two particles and
  reverses horizontal displacements.

They generate a representation of `C₂ × C₂ = Multiplicative (ZMod 2) × Multiplicative (ZMod 2)`,
with `r` the generator of the first factor and `s` that of the second
(`TauCeti.TwoParticleSpring.symmetryRep`). It preserves the standard dot product and commutes with
the linearized force `H`. The orbit of the displacement `(1, 1, 0, 0)` is an orthogonal basis, so
the representation is the left regular representation of `C₂ × C₂`
(`TauCeti.TwoParticleSpring.leftRegularEquivSymmetryRep`).

**Isotypic decomposition.** Each of the four real characters of `C₂ × C₂` therefore occurs exactly
once, and its isotypic component is a line:

| character | `(r, s)`-signs | spanning vector | mode | `H`-eigenvalue |
| --- | --- | --- | --- | ---: |
| `1` | `(+, +)` | `(1, 0, -1, 0)` | stretching | `-2` |
| `axisSign` | `(-, +)` | `(0, 1, 0, 1)` | vertical translation | `0` |
| `bisectorSign` | `(+, -)` | `(1, 0, 1, 0)` | horizontal translation | `0` |
| `axisSign * bisectorSign` | `(-, -)` | `(0, 1, 0, -1)` | transverse mode | `0` |

The character idempotent `e_χ` of `TauCeti.charIdempotent` acts through the representation as the
projector `¼ (1 + χ(r) r + χ(s) s + χ(rs) rs)` onto the `χ`-isotypic component. Since the action is
orthogonal and the characters are real, these projectors are orthogonal for the dot product: each
is `u ↦ ((v ⬝ᵥ u) / (v ⬝ᵥ v)) v` for the spanning vector `v` of its line, and `v ⬝ᵥ v = 2`. The
linearized force is `H = -2 e₁`, the eigenvalue `-2` times the projector onto the stretching line.

## Main definitions

* `TauCeti.TwoParticleSpring.axisReflection`, `TauCeti.TwoParticleSpring.bisectorReflection`: the
  reflections `r` and `s`.
* `TauCeti.TwoParticleSpring.symmetryRep`: the representation of `C₂ × C₂` they generate.
* `TauCeti.TwoParticleSpring.axisSign`, `TauCeti.TwoParticleSpring.bisectorSign`: the characters
  of `C₂ × C₂` that are `-1` on `r`, respectively on `s`, and `1` on the other generator.
* `TauCeti.TwoParticleSpring.leftRegularEquivSymmetryRep`: the equivalence with the left regular
  representation.

## Main results

* `TauCeti.TwoParticleSpring.forceMatrix_mulVec_symmetryRep`: `H` is equivariant.
* `TauCeti.TwoParticleSpring.dotProduct_symmetryRep`: the action is orthogonal.
* `TauCeti.TwoParticleSpring.symmetryRep_asAlgebraHom_charIdempotent_one_apply` and its three
  companions: the orthogonal projectors onto the four isotypic lines.
* `TauCeti.TwoParticleSpring.iInf_eigenspace_symmetryRep_one` and its three companions: the four
  isotypic components.
* `TauCeti.TwoParticleSpring.forceMatrix_mulVec_eq_neg_two_smul`: `H = -2 e₁`.

## References

* A. Knutson, *Group theory in physics: an example*, notes for Math 261 (Cornell, 2001),
  pp. 1–2 (the two-particle spring and its symmetry group `C₂ × C₂`).
-/

public section

open Matrix Module MonoidAlgebra

namespace TauCeti.TwoParticleSpring

/-! ### The two reflections -/

/-- The **reflection `r` in the axis of the spring**, `r (x₁, y₁, x₂, y₂) = (x₁, -y₁, x₂, -y₂)`:
it fixes both rest positions and reverses every vertical displacement. -/
noncomputable def axisReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofInvolutive
    (LinearMap.pi ![LinearMap.proj 0, -LinearMap.proj 1, LinearMap.proj 2, -LinearMap.proj 3])
    fun x ↦ by
      ext i
      fin_cases i <;> simp

/-- The reflection in the axis in coordinates, `r (x₁, y₁, x₂, y₂) = (x₁, -y₁, x₂, -y₂)`. -/
@[simp]
theorem axisReflection_apply (x : Fin 4 → ℝ) :
    axisReflection x = ![x 0, -x 1, x 2, -x 3] := by
  ext i
  fin_cases i <;> rfl

/-- The **reflection `s` in the perpendicular bisector of the spring**,
`s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)`: it exchanges the two particles and reverses every
horizontal displacement. -/
noncomputable def bisectorReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofInvolutive
    (LinearMap.pi ![-LinearMap.proj 2, LinearMap.proj 3, -LinearMap.proj 0, LinearMap.proj 1])
    fun x ↦ by
      ext i
      fin_cases i <;> simp

/-- The reflection in the bisector in coordinates, `s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)`. -/
@[simp]
theorem bisectorReflection_apply (x : Fin 4 → ℝ) :
    bisectorReflection x = ![-x 2, x 3, -x 0, x 1] := by
  ext i
  fin_cases i <;> rfl

/-- The reflection in the axis is an involution. -/
theorem axisReflection_sq : axisReflection ^ 2 = 1 := by
  ext x i
  fin_cases i <;> simp [pow_two, mul_apply_eq_comp]

/-- The reflection in the bisector is an involution. -/
theorem bisectorReflection_sq : bisectorReflection ^ 2 = 1 := by
  ext x i
  fin_cases i <;> simp [pow_two, mul_apply_eq_comp]

/-- The two reflections commute. -/
theorem commute_axisReflection_bisectorReflection :
    Commute axisReflection bisectorReflection := by
  ext x i
  fin_cases i <;> simp [mul_apply_eq_comp]

/-! ### The representation of `C₂ × C₂` -/

/-- The **representation of `C₂ × C₂` on the displacements** of the two particles: the generator
`(Multiplicative.ofAdd 1, 1)` of the first factor acts by the reflection `r` in the axis
(`TauCeti.TwoParticleSpring.axisReflection`), and the generator `(1, Multiplicative.ofAdd 1)` of
the second factor by the reflection `s` in the bisector
(`TauCeti.TwoParticleSpring.bisectorReflection`). -/
noncomputable def symmetryRep :
    Representation ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (Fin 4 → ℝ) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp <|
    MonoidHom.noncommCoprod
      ((zmodMonoidHomEquiv 2 _).symm ⟨axisReflection, axisReflection_sq⟩)
      ((zmodMonoidHomEquiv 2 _).symm ⟨bisectorReflection, bisectorReflection_sq⟩)
      fun a b ↦ by
        rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, zmodMonoidHomEquiv_symm_apply,
          zmodMonoidHomEquiv_symm_apply]
        exact commute_axisReflection_bisectorReflection.pow_pow _ _

/-- The generator of the first factor acts by the reflection `r` in the axis. -/
@[simp]
theorem symmetryRep_ofAdd_one_one_apply (x : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, 1) x = axisReflection x := by
  simp [symmetryRep, MonoidHom.noncommCoprod_apply, ZMod.val_one]

/-- The generator of the second factor acts by the reflection `s` in the bisector. -/
@[simp]
theorem symmetryRep_one_ofAdd_one_apply (x : Fin 4 → ℝ) :
    symmetryRep (1, .ofAdd 1) x = bisectorReflection x := by
  simp [symmetryRep, MonoidHom.noncommCoprod_apply, ZMod.val_one]

/-- The product `rs` of the two generators acts by the composite of the two reflections, the
half-turn about the midpoint of the spring. -/
@[simp]
theorem symmetryRep_ofAdd_one_ofAdd_one_apply (x : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, .ofAdd 1) x = axisReflection (bisectorReflection x) := by
  rw [show ((.ofAdd 1, .ofAdd 1) : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
    (.ofAdd 1, 1) * (1, .ofAdd 1) by rfl, map_mul, mul_apply_eq_comp,
    symmetryRep_one_ofAdd_one_apply, symmetryRep_ofAdd_one_one_apply]

/-- The four elements of `C₂ × C₂`. -/
private theorem eq_one_or_eq_of_klein (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    g = 1 ∨ g = (.ofAdd 1, 1) ∨ g = (1, .ofAdd 1) ∨ g = (.ofAdd 1, .ofAdd 1) := by
  revert g
  decide

/-- A sum over `C₂ × C₂`, written out over its four elements. -/
private theorem sum_klein {M : Type*} [AddCommMonoid M]
    (f : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) → M) :
    ∑ g, f g = f 1 + f (.ofAdd 1, 1) + f (1, .ofAdd 1) + f (.ofAdd 1, .ofAdd 1) := by
  have h : (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, .ofAdd 1} := by decide
  rw [Fintype.sum_prod_type, h, Finset.sum_pair one_ne_ofAdd_one, Finset.sum_pair one_ne_ofAdd_one,
    Finset.sum_pair one_ne_ofAdd_one, Prod.mk_one_one]
  abel

/-- **`H` is equivariant**: the linearized force commutes with the symmetries of the rest
configuration. -/
theorem forceMatrix_mulVec_symmetryRep (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (x : Fin 4 → ℝ) :
    forceMatrix *ᵥ symmetryRep g x = symmetryRep g (forceMatrix *ᵥ x) := by
  rcases eq_one_or_eq_of_klein g with rfl | rfl | rfl | rfl <;>
  · ext i
    fin_cases i <;> simp [forceMatrix_mulVec] <;> ring

/-- **The action is orthogonal**: every symmetry preserves the standard dot product of
displacements. -/
theorem dotProduct_symmetryRep (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (x y : Fin 4 → ℝ) :
    symmetryRep g x ⬝ᵥ symmetryRep g y = x ⬝ᵥ y := by
  rcases eq_one_or_eq_of_klein g with rfl | rfl | rfl | rfl <;>
    simp [dotProduct, Fin.sum_univ_four] <;> ring

/-! ### The left regular representation -/

/-- The orbit of the displacement `(1, 1, 0, 0)` is orthogonal, of squared length `2`. -/
private theorem dotProduct_symmetryRep_seed
    (g h : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![1, 1, 0, 0] ⬝ᵥ symmetryRep h ![1, 1, 0, 0] = if g = h then 2 else 0 := by
  rcases eq_one_or_eq_of_klein g with rfl | rfl | rfl | rfl <;>
  rcases eq_one_or_eq_of_klein h with rfl | rfl | rfl | rfl <;>
    simp [dotProduct, Fin.sum_univ_four, Prod.ext_iff, one_ne_ofAdd_one, one_ne_ofAdd_one.symm] <;>
    norm_num

/-- The orbit of the displacement `(1, 1, 0, 0)` is linearly independent: the coefficients of a
combination of the orbit are recovered by the dot product with the orbit. -/
private theorem linearIndependent_symmetryRep_seed :
    LinearIndependent ℝ fun g ↦ symmetryRep g ![1, 1, 0, 0] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc h
  have := congrArg (symmetryRep h ![1, 1, 0, 0] ⬝ᵥ ·) hc
  simpa [dotProduct_sum, dotProduct_smul, dotProduct_symmetryRep_seed] using this

/-- The orthogonal basis of displacements formed by the orbit of `(1, 1, 0, 0)`. -/
private noncomputable def seedBasis :
    Basis (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ℝ (Fin 4 → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_symmetryRep_seed (by simp)

private theorem seedBasis_apply (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    seedBasis g = symmetryRep g ![1, 1, 0, 0] := by
  simp [seedBasis]

/-- The basis equivalence underlying `TauCeti.TwoParticleSpring.leftRegularEquivSymmetryRep` sends
`single g 1` to `g · (1, 1, 0, 0)`. -/
private theorem basis_equiv_seedBasis_single
    (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    (MonoidAlgebra.basis _ ℝ).equiv seedBasis (Equiv.refl _) (MonoidAlgebra.single g 1) =
      symmetryRep g ![1, 1, 0, 0] := by
  rw [← MonoidAlgebra.basis_apply, Basis.equiv_apply, Equiv.refl_apply, seedBasis_apply]

/-- **The displacement representation is the left regular representation of `C₂ × C₂`.** The
basis vector `single g 1` corresponds to the image `g · (1, 1, 0, 0)` of the displacement
`(1, 1, 0, 0)`, the first particle displaced diagonally; the four images form an orthogonal
basis. -/
noncomputable def leftRegularEquivSymmetryRep :
    (Representation.leftRegular ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))).Equiv
      symmetryRep :=
  .mk ((MonoidAlgebra.basis _ ℝ).equiv seedBasis (Equiv.refl _)) fun g ↦
    (MonoidAlgebra.basis _ ℝ).ext fun h ↦ by
      simp [basis_equiv_seedBasis_single, map_mul, mul_apply_eq_comp]

/-- The basis vector `single g c` of the left regular representation corresponds to the image of
`c • (1, 1, 0, 0)` under `g`. -/
@[simp]
theorem leftRegularEquivSymmetryRep_single
    (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (c : ℝ) :
    leftRegularEquivSymmetryRep (MonoidAlgebra.single g c) = c • symmetryRep g ![1, 1, 0, 0] := by
  rw [← mul_one c, ← MonoidAlgebra.smul_single', map_smul]
  simp [leftRegularEquivSymmetryRep, basis_equiv_seedBasis_single]

/-! ### The characters and the isotypic projectors -/

/-- The character of `C₂ × C₂` that is `-1` on the reflection `r` in the axis and `1` on the
reflection `s` in the bisector. -/
noncomputable def axisSign : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ :=
  (cyclicTwoSign ℝˣ).comp (MonoidHom.fst _ _)

/-- The character of `C₂ × C₂` that is `1` on the reflection `r` in the axis and `-1` on the
reflection `s` in the bisector. -/
noncomputable def bisectorSign : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ :=
  (cyclicTwoSign ℝˣ).comp (MonoidHom.snd _ _)

/-- The character `axisSign` reads off the sign of the first factor. -/
@[simp]
theorem axisSign_apply (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    axisSign g = cyclicTwoSign ℝˣ g.1 :=
  (rfl)

/-- The character `bisectorSign` reads off the sign of the second factor. -/
@[simp]
theorem bisectorSign_apply (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    bisectorSign g = cyclicTwoSign ℝˣ g.2 :=
  (rfl)

/-- The character projector of `χ` on displacements is
`¼ (1 + χ(r) r + χ(s) s + χ(rs) rs)`, every element of `C₂ × C₂` being its own inverse. -/
private theorem symmetryRep_asAlgebraHom_charIdempotent_apply
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ) (x : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent χ) x =
      (4 : ℝ)⁻¹ • (x + (χ (.ofAdd 1, 1) : ℝ) • axisReflection x +
        (χ (1, .ofAdd 1) : ℝ) • bisectorReflection x +
        (χ (.ofAdd 1, .ofAdd 1) : ℝ) • axisReflection (bisectorReflection x)) := by
  have hinv (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : (χ g)⁻¹ = χ g := by
    rw [← map_inv]
    congr 1
    revert g
    decide
  have hcard : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
    simp
  rw [Representation.asAlgebraHom_charIdempotent, sum_klein]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, map_one, one_apply_eq_self, hinv, hcard,
    inv_one, Units.val_one, one_smul, Nat.cast_ofNat, Ring.inverse_eq_inv',
    symmetryRep_ofAdd_one_one_apply, symmetryRep_one_ofAdd_one_apply,
    symmetryRep_ofAdd_one_ofAdd_one_apply]

/-- **The orthogonal projector onto the stretching line.** The character idempotent of the trivial
character projects a displacement `u` orthogonally onto the line through `v = (1, 0, -1, 0)`:
`u ↦ ((v ⬝ᵥ u) / 2) v`, where `v ⬝ᵥ v = 2`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_one_apply (x : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent 1) x =
      ((![1, 0, -1, 0] ⬝ᵥ x) / 2) • ![1, 0, -1, 0] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- **The orthogonal projector onto the vertical translations.** The character idempotent of
`TauCeti.TwoParticleSpring.axisSign` projects a displacement `u` orthogonally onto the line
through `v = (0, 1, 0, 1)`: `u ↦ ((v ⬝ᵥ u) / 2) v`, where `v ⬝ᵥ v = 2`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_axisSign_apply (x : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent axisSign) x =
      ((![0, 1, 0, 1] ⬝ᵥ x) / 2) • ![0, 1, 0, 1] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- **The orthogonal projector onto the horizontal translations.** The character idempotent of
`TauCeti.TwoParticleSpring.bisectorSign` projects a displacement `u` orthogonally onto the line
through `v = (1, 0, 1, 0)`: `u ↦ ((v ⬝ᵥ u) / 2) v`, where `v ⬝ᵥ v = 2`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_bisectorSign_apply (x : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent bisectorSign) x =
      ((![1, 0, 1, 0] ⬝ᵥ x) / 2) • ![1, 0, 1, 0] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- **The orthogonal projector onto the transverse mode.** The character idempotent of
`axisSign * bisectorSign` projects a displacement `u` orthogonally onto the line through
`v = (0, 1, 0, -1)`: `u ↦ ((v ⬝ᵥ u) / 2) v`, where `v ⬝ᵥ v = 2`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_axisSign_mul_bisectorSign_apply
    (x : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent (axisSign * bisectorSign)) x =
      ((![0, 1, 0, -1] ⬝ᵥ x) / 2) • ![0, 1, 0, -1] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-! ### The isotypic components -/

/-- A projector `u ↦ ((v ⬝ᵥ u) / 2) v` with `v ⬝ᵥ v = 2` has image the line through `v`. -/
private theorem range_eq_span_singleton {P : Module.End ℝ (Fin 4 → ℝ)} {v : Fin 4 → ℝ}
    (hP : ∀ x, P x = ((v ⬝ᵥ x) / 2) • v) (hv : v ⬝ᵥ v = 2) :
    LinearMap.range P = ℝ ∙ v := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨v, by simp [hP, hv]⟩)
  rintro _ ⟨x, rfl⟩
  rw [hP]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

private theorem isUnit_natCard_klein :
    IsUnit (Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : ℝ) :=
  (Nat.cast_ne_zero.2 Nat.card_pos.ne').isUnit

/-- The **trivial isotypic component**, on which both reflections act trivially, is the stretching
line through `(1, 0, -1, 0)`. -/
theorem iInf_eigenspace_symmetryRep_one :
    ⨅ g, End.eigenspace (symmetryRep g)
        ((1 : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ) g) =
      ℝ ∙ ![1, 0, -1, 0] := by
  rw [← Representation.range_asAlgebraHom_charIdempotent _ isUnit_natCard_klein]
  exact range_eq_span_singleton symmetryRep_asAlgebraHom_charIdempotent_one_apply
    (by simp [dotProduct, Fin.sum_univ_four]; norm_num)

/-- The **`axisSign`-isotypic component**, reversed by `r` and fixed by `s`, is the line of
vertical translations through `(0, 1, 0, 1)`. -/
theorem iInf_eigenspace_symmetryRep_axisSign :
    ⨅ g, End.eigenspace (symmetryRep g) (axisSign g) = ℝ ∙ ![0, 1, 0, 1] := by
  rw [← Representation.range_asAlgebraHom_charIdempotent _ isUnit_natCard_klein]
  exact range_eq_span_singleton symmetryRep_asAlgebraHom_charIdempotent_axisSign_apply
    (by simp [dotProduct, Fin.sum_univ_four]; norm_num)

/-- The **`bisectorSign`-isotypic component**, fixed by `r` and reversed by `s`, is the line of
horizontal translations through `(1, 0, 1, 0)`. -/
theorem iInf_eigenspace_symmetryRep_bisectorSign :
    ⨅ g, End.eigenspace (symmetryRep g) (bisectorSign g) = ℝ ∙ ![1, 0, 1, 0] := by
  rw [← Representation.range_asAlgebraHom_charIdempotent _ isUnit_natCard_klein]
  exact range_eq_span_singleton symmetryRep_asAlgebraHom_charIdempotent_bisectorSign_apply
    (by simp [dotProduct, Fin.sum_univ_four]; norm_num)

/-- The **`axisSign * bisectorSign`-isotypic component**, reversed by both reflections, is the
line of the transverse mode `(0, 1, 0, -1)`. -/
theorem iInf_eigenspace_symmetryRep_axisSign_mul_bisectorSign :
    ⨅ g, End.eigenspace (symmetryRep g) ((axisSign * bisectorSign) g) = ℝ ∙ ![0, 1, 0, -1] := by
  rw [← Representation.range_asAlgebraHom_charIdempotent _ isUnit_natCard_klein]
  exact range_eq_span_singleton
    symmetryRep_asAlgebraHom_charIdempotent_axisSign_mul_bisectorSign_apply
    (by simp [dotProduct, Fin.sum_univ_four]; norm_num)

/-! ### The force in terms of the projectors -/

/-- **The spectral decomposition of `H`**: the linearized force is `-2` times the orthogonal
projector onto the trivial isotypic line, the stretching mode; it kills the three other isotypic
lines, the two translations and the transverse mode. -/
theorem forceMatrix_mulVec_eq_neg_two_smul (x : Fin 4 → ℝ) :
    forceMatrix *ᵥ x = (-2 : ℝ) • symmetryRep.asAlgebraHom (charIdempotent 1) x := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_one_apply]
  ext i
  fin_cases i <;> simp [forceMatrix_mulVec, dotProduct, Fin.sum_univ_four] <;> ring

end TauCeti.TwoParticleSpring
