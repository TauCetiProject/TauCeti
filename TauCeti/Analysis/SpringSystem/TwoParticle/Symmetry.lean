/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RepresentationTheory.Equiv
public import TauCeti.Algebra.MonoidAlgebra.CyclicTwo
public import TauCeti.Analysis.SpringSystem.TwoParticle
public import TauCeti.Data.ZMod.MonoidHomEquiv
public import TauCeti.RepresentationTheory.AsAlgebraHom
public import TauCeti.RepresentationTheory.GroupAlgebra.CharIdempotent

/-!
# Two particles on a spring: the symmetry group `C₂ × C₂` and the projectors onto the modes

Two particles rest at `(0, 0)` and `(1, 0)` in the plane, joined by a spring. Their
displacements are vectors `u = (x₁, y₁, x₂, y₂)` of `ℝ⁴ = Fin 4 → ℝ`, and the linearized force
is `κ H u` for the force matrix `H = TauCeti.TwoParticleSpring.forceMatrix`.

**The symmetry.** Two reflections of the plane preserve the rest configuration:

* the reflection in the axis through the two rest positions, `y ↦ -y`, which fixes each
  particle and acts on displacements by `r (x₁, y₁, x₂, y₂) = (x₁, -y₁, x₂, -y₂)`
  (`TauCeti.TwoParticleSpring.axisReflection`);
* the reflection in the perpendicular bisector, `x ↦ 1 - x`, which exchanges the particles and
  acts by `s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)`
  (`TauCeti.TwoParticleSpring.bisectorReflection`).

They are commuting involutions, so the Klein four-group
`C₂ × C₂ = Multiplicative (ZMod 2) × Multiplicative (ZMod 2)` acts on displacements, the element
`(a, b)` by `r ^ a * s ^ b` (`TauCeti.TwoParticleSpring.symmetryRep`). The force matrix `H`
commutes with this action. The action is the regular representation of `C₂ × C₂`: the orbit of
the displacement `(1, 1, 0, 0)` is a basis
(`TauCeti.TwoParticleSpring.symmetryRepEquivLeftRegular`).

**The modes.** The four modes of the spring are joint eigenvectors of the action, carrying the
four characters `1`, `sgn ∘ fst`, `sgn ∘ snd` and `sgn ⊗ sgn` of `C₂ × C₂` with values in `ℝˣ`,
where `sgn = TauCeti.cyclicTwoSign ℝˣ`:

| mode | vector | `r` | `s` | `H`-eigenvalue |
| --- | --- | :-: | :-: | :-: |
| stretching | `(1, 0, -1, 0)` | `+` | `+` | `-2` |
| vertical translation | `(0, 1, 0, 1)` | `-` | `+` | `0` |
| horizontal translation | `(1, 0, 1, 0)` | `+` | `-` | `0` |
| transverse | `(0, 1, 0, -1)` | `-` | `-` | `0` |

The eigenvalues are `TauCeti.TwoParticleSpring.forceMatrix_mulVec_stretch` and its companions.
Each joint eigenspace is exactly the line through the corresponding mode
(`TauCeti.TwoParticleSpring.iInf_eigenspace_symmetryRep_one` and its three companions). Note that
the vertical translation `(0, 1, 0, 1)` is reversed by `r` and fixed by `s`.

**The projectors.** For a character `χ : C₂ × C₂ →* ℝˣ`, the character idempotent
`e_χ = ¼ ∑_g χ(g)⁻¹ g` (`TauCeti.charIdempotent`) of the group algebra acts on displacements by
`¼ (1 + χ(r) r + χ(s) s + χ(r s) r s)`. It is idempotent, by
`TauCeti.isIdempotentElem_charIdempotent`, and symmetric for the dot product, because each
symmetry is (`TauCeti.TwoParticleSpring.symmetryRep_asAlgebraHom_dotProduct`); so it is an
orthogonal projector. For each of the four characters of the modes it is
the orthogonal projection `u ↦ ((v ⬝ᵥ u) / (v ⬝ᵥ v)) • v` onto the line through the mode `v`, and
these four projectors sum to the identity.

## Main definitions

* `TauCeti.TwoParticleSpring.axisReflection`, `TauCeti.TwoParticleSpring.bisectorReflection`:
  the two reflections `r` and `s`.
* `TauCeti.TwoParticleSpring.symmetryRep`: the representation of `C₂ × C₂` on displacements.
* `TauCeti.TwoParticleSpring.symmetryRepEquivLeftRegular`: its identification with the regular
  representation.

## Main results

* `TauCeti.TwoParticleSpring.forceMatrix_mulVec_symmetryRep`: `H` is equivariant.
* `TauCeti.TwoParticleSpring.symmetryRep_stretch` and its three companions: the four modes are
  joint eigenvectors of the action, with the characters in the table above.
* `TauCeti.TwoParticleSpring.iInf_eigenspace_symmetryRep_one` and its three companions: each
  joint eigenspace is the line through its mode.
* `TauCeti.TwoParticleSpring.symmetryRep_asAlgebraHom_dotProduct`: the group algebra, and in
  particular each character idempotent, acts by symmetric operators.
* `TauCeti.TwoParticleSpring.symmetryRep_asAlgebraHom_charIdempotent_one_apply` and its three
  companions: the orthogonal projector onto each mode, explicitly.
* `TauCeti.TwoParticleSpring.symmetryRep_asAlgebraHom_charIdempotent_add_eq_one`: the four
  projectors sum to the identity.

## References

* A. Knutson, *Group theory in physics: an example*, notes for Math 261 (Cornell, 2001),
  pp. 1–2 (the two-particle spring and its symmetries `r` and `s`).
-/

public section

namespace TauCeti.TwoParticleSpring

open Matrix Module

/-! ### The two reflections -/

/-- The reflection `r` of displacements in the axis through the two rest positions:
`r (x₁, y₁, x₂, y₂) = (x₁, -y₁, x₂, -y₂)`. It fixes each particle and reverses vertical
displacements. -/
noncomputable def axisReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofInvolutive
    { toFun u := ![u 0, -u 1, u 2, -u 3]
      map_add' u w := by ext i; fin_cases i <;> simp <;> ring
      map_smul' c u := by ext i; fin_cases i <;> simp }
    fun u ↦ by ext i; fin_cases i <;> simp

/-- The axis reflection in coordinates. -/
@[simp]
theorem axisReflection_apply (u : Fin 4 → ℝ) : axisReflection u = ![u 0, -u 1, u 2, -u 3] :=
  (rfl)

/-- The reflection `s` of displacements in the perpendicular bisector of the two rest positions:
`s (x₁, y₁, x₂, y₂) = (-x₂, y₂, -x₁, y₁)`. It exchanges the particles and reverses horizontal
displacements. -/
noncomputable def bisectorReflection : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.ofInvolutive
    { toFun u := ![-u 2, u 3, -u 0, u 1]
      map_add' u w := by ext i; fin_cases i <;> simp <;> ring
      map_smul' c u := by ext i; fin_cases i <;> simp }
    fun u ↦ by ext i; fin_cases i <;> simp

/-- The bisector reflection in coordinates. -/
@[simp]
theorem bisectorReflection_apply (u : Fin 4 → ℝ) :
    bisectorReflection u = ![-u 2, u 3, -u 0, u 1] :=
  (rfl)

/-- The matrix of the axis reflection is `diag(1, -1, 1, -1)`. -/
theorem toMatrix'_axisReflection :
    LinearMap.toMatrix' (axisReflection : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) =
      !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply]

/-- The matrix of the bisector reflection. -/
theorem toMatrix'_bisectorReflection :
    LinearMap.toMatrix' (bisectorReflection : (Fin 4 → ℝ) →ₗ[ℝ] Fin 4 → ℝ) =
      !![0, 0, -1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix'_apply]

/-- The axis reflection is an involution. -/
theorem axisReflection_sq : axisReflection ^ 2 = 1 := by
  ext u i
  fin_cases i <;> simp [pow_two]

/-- The bisector reflection is an involution. -/
theorem bisectorReflection_sq : bisectorReflection ^ 2 = 1 := by
  ext u i
  fin_cases i <;> simp [pow_two]

/-- The two reflections commute. -/
theorem commute_axisReflection_bisectorReflection :
    Commute axisReflection bisectorReflection := by
  ext u i
  fin_cases i <;> simp

/-! ### The representation of `C₂ × C₂` -/

/-- The homomorphism `C₂ →* GL(ℝ⁴)` sending the generator to the axis reflection. -/
private noncomputable def axisHom :
    Multiplicative (ZMod 2) →* (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((zmodMonoidHomEquiv 2 ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))).symm ⟨_, axisReflection_sq⟩)

/-- The homomorphism `C₂ →* GL(ℝ⁴)` sending the generator to the bisector reflection. -/
private noncomputable def bisectorHom :
    Multiplicative (ZMod 2) →* (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
    ((zmodMonoidHomEquiv 2 ((Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))).symm ⟨_, bisectorReflection_sq⟩)

private theorem forall_cyclicTwo (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = .ofAdd 1 := by
  revert g; decide

private theorem axisHom_ofAdd_one (u : Fin 4 → ℝ) :
    axisHom (.ofAdd 1) u = axisReflection u := by
  simp [axisHom, ZMod.val_one]

private theorem bisectorHom_ofAdd_one (u : Fin 4 → ℝ) :
    bisectorHom (.ofAdd 1) u = bisectorReflection u := by
  simp [bisectorHom, ZMod.val_one]

/-- The **representation of the Klein four-group `C₂ × C₂` on the displacements** of the two
particles: `(a, b)` acts by `r ^ a * s ^ b`, where `r` is the axis reflection
`TauCeti.TwoParticleSpring.axisReflection` and `s` the bisector reflection
`TauCeti.TwoParticleSpring.bisectorReflection`. -/
noncomputable def symmetryRep :
    Representation ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (Fin 4 → ℝ) :=
  axisHom.noncommCoprod bisectorHom fun a b ↦ by
    rcases forall_cyclicTwo a with rfl | rfl
    · simp only [map_one, Commute.one_left]
    rcases forall_cyclicTwo b with rfl | rfl
    · simp only [map_one, Commute.one_right]
    refine LinearMap.ext fun u ↦ ?_
    rw [mul_apply_eq_comp, mul_apply_eq_comp, axisHom_ofAdd_one, axisHom_ofAdd_one,
      bisectorHom_ofAdd_one, bisectorHom_ofAdd_one]
    exact LinearEquiv.congr_fun commute_axisReflection_bisectorReflection.eq u

/-- The element `(1, 0)` of `C₂ × C₂` acts by the axis reflection `r`. -/
@[simp]
theorem symmetryRep_ofAdd_one_one (u : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, 1) u = axisReflection u := by
  simp [symmetryRep, axisHom_ofAdd_one]

/-- The element `(0, 1)` of `C₂ × C₂` acts by the bisector reflection `s`. -/
@[simp]
theorem symmetryRep_one_ofAdd_one (u : Fin 4 → ℝ) :
    symmetryRep (1, .ofAdd 1) u = bisectorReflection u := by
  simp [symmetryRep, bisectorHom_ofAdd_one]

/-- The element `(1, 1)` of `C₂ × C₂` is the product of the two generators. -/
private theorem ofAdd_one_ofAdd_one_eq_mul :
    ((.ofAdd 1, .ofAdd 1) : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) =
      (.ofAdd 1, 1) * (1, .ofAdd 1) := by
  decide

/-- The element `(1, 1)` of `C₂ × C₂` acts by the product `r s`, the rotation by a half turn
about the midpoint of the rest positions. -/
@[simp]
theorem symmetryRep_ofAdd_one_ofAdd_one (u : Fin 4 → ℝ) :
    symmetryRep (.ofAdd 1, .ofAdd 1) u = ![-u 2, -u 3, -u 0, -u 1] := by
  rw [ofAdd_one_ofAdd_one_eq_mul, map_mul, mul_apply_eq_comp, symmetryRep_one_ofAdd_one,
    symmetryRep_ofAdd_one_one]
  ext i
  fin_cases i <;> simp

/-- An element of `C₂ × C₂` is one of the four elements `1`, `(1, 0)`, `(0, 1)` and `(1, 1)`. -/
private theorem forall_kleinFour (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    g = 1 ∨ g = (.ofAdd 1, 1) ∨ g = (1, .ofAdd 1) ∨ g = (.ofAdd 1, .ofAdd 1) := by
  revert g; decide

/-- **The force matrix is equivariant**: `H` commutes with both reflections. -/
theorem forceMatrix_mulVec_symmetryRep (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (u : Fin 4 → ℝ) : forceMatrix *ᵥ symmetryRep g u = symmetryRep g (forceMatrix *ᵥ u) := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl <;>
  · ext i
    fin_cases i <;> simp [forceMatrix_def, mulVec, dotProduct, Fin.sum_univ_four]

/-- Each symmetry is an orthogonal involution, hence symmetric for the dot product. -/
theorem symmetryRep_dotProduct (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
    (u w : Fin 4 → ℝ) : symmetryRep g u ⬝ᵥ w = u ⬝ᵥ symmetryRep g w := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl
  · simp
  all_goals simp [dotProduct, Fin.sum_univ_four]
  all_goals ring

/-! ### The four modes as joint eigenvectors -/

/-- The stretching mode `(1, 0, -1, 0)` is fixed by the whole symmetry group: it carries the
trivial character. -/
theorem symmetryRep_stretch (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![1, 0, -1, 0] = ![1, 0, -1, 0] := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp

/-- The vertical translation `(0, 1, 0, 1)` is reversed by `r` and fixed by `s`: it carries the
sign character of the first factor. -/
theorem symmetryRep_translation_y (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![0, 1, 0, 1] =
      ((cyclicTwoSign ℝˣ).comp (MonoidHom.fst _ _) g : ℝ) • ![0, 1, 0, 1] := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp

/-- The horizontal translation `(1, 0, 1, 0)` is fixed by `r` and reversed by `s`: it carries
the sign character of the second factor. -/
theorem symmetryRep_translation_x (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![1, 0, 1, 0] =
      ((cyclicTwoSign ℝˣ).comp (MonoidHom.snd _ _) g : ℝ) • ![1, 0, 1, 0] := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp

/-- The transverse mode `(0, 1, 0, -1)` is reversed by both `r` and `s`: it carries the product
of the two sign characters. -/
theorem symmetryRep_transverse (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :
    symmetryRep g ![0, 1, 0, -1] =
      ((cyclicTwoSign ℝˣ).coprod (cyclicTwoSign ℝˣ) g : ℝ) • ![0, 1, 0, -1] := by
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl <;>
  · ext i; fin_cases i <;> simp

/-! ### The joint eigenspaces -/

/-- A displacement lies in the joint eigenspace of a character `χ` of `C₂ × C₂` exactly when
the two reflections multiply it by the values of `χ` at the two generators. -/
theorem mem_iInf_eigenspace_symmetryRep_iff
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ) (u : Fin 4 → ℝ) :
    u ∈ ⨅ g, End.eigenspace (symmetryRep g) (χ g) ↔
      axisReflection u = (χ (.ofAdd 1, 1) : ℝ) • u ∧
        bisectorReflection u = (χ (1, .ofAdd 1) : ℝ) • u := by
  rw [Submodule.mem_iInf]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hr, hs⟩ g ↦ ?_⟩
  · simpa using End.mem_eigenspace_iff.1 (h (.ofAdd 1, 1))
  · simpa using End.mem_eigenspace_iff.1 (h (1, .ofAdd 1))
  rw [End.mem_eigenspace_iff]
  rcases forall_kleinFour g with rfl | rfl | rfl | rfl
  · simp
  · simpa using hr
  · simpa using hs
  · rw [ofAdd_one_ofAdd_one_eq_mul, map_mul, map_mul, mul_apply_eq_comp,
      symmetryRep_one_ofAdd_one, symmetryRep_ofAdd_one_one, hs, map_smul, hr, smul_smul,
      Units.val_mul, mul_comm]

/-- A joint eigenvector `v` of a character `χ` spans its joint eigenspace once every displacement
on which the two reflections act by the values of `χ` is a multiple of `v`. -/
private theorem iInf_eigenspace_symmetryRep_eq_span
    {χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ} {v : Fin 4 → ℝ}
    (hv : ∀ g, symmetryRep g v = (χ g : ℝ) • v)
    (hx : ∀ u, axisReflection u = (χ (.ofAdd 1, 1) : ℝ) • u →
      bisectorReflection u = (χ (1, .ofAdd 1) : ℝ) • u → ∃ c : ℝ, c • v = u) :
    ⨅ g, End.eigenspace (symmetryRep g) (χ g) = ℝ ∙ v := by
  ext u
  rw [mem_iInf_eigenspace_symmetryRep_iff, Submodule.mem_span_singleton]
  refine ⟨fun ⟨hr, hs⟩ ↦ hx u hr hs, ?_⟩
  rintro ⟨c, rfl⟩
  rw [map_smul, map_smul, ← symmetryRep_ofAdd_one_one, ← symmetryRep_one_ofAdd_one, hv, hv,
    smul_comm c, smul_comm c]
  exact ⟨rfl, rfl⟩

/-- The **trivial isotypic component** of the displacements is the line through the stretching
mode `(1, 0, -1, 0)`. -/
theorem iInf_eigenspace_symmetryRep_one :
    ⨅ g, End.eigenspace (symmetryRep g) ((1 : _ →* ℝˣ) g) =
      ℝ ∙ (![1, 0, -1, 0] : Fin 4 → ℝ) := by
  refine iInf_eigenspace_symmetryRep_eq_span (by simp [symmetryRep_stretch])
    fun u hr hs ↦ ⟨u 0, ?_⟩
  have hr1 := congrFun hr 1
  have hr3 := congrFun hr 3
  have hs0 := congrFun hs 0
  simp at hr1 hr3 hs0
  ext i
  fin_cases i <;> simp <;> linarith

/-- The isotypic component of the sign character of the first factor, reversed by `r` and fixed
by `s`, is the line of vertical translations. -/
theorem iInf_eigenspace_symmetryRep_comp_fst :
    ⨅ g, End.eigenspace (symmetryRep g) ((cyclicTwoSign ℝˣ).comp (MonoidHom.fst _ _) g) =
      ℝ ∙ (![0, 1, 0, 1] : Fin 4 → ℝ) := by
  refine iInf_eigenspace_symmetryRep_eq_span symmetryRep_translation_y fun u hr hs ↦ ⟨u 1, ?_⟩
  have hr0 := congrFun hr 0
  have hr2 := congrFun hr 2
  have hs1 := congrFun hs 1
  simp at hr0 hr2 hs1
  ext i
  fin_cases i <;> simp <;> linarith

/-- The isotypic component of the sign character of the second factor, fixed by `r` and reversed
by `s`, is the line of horizontal translations. -/
theorem iInf_eigenspace_symmetryRep_comp_snd :
    ⨅ g, End.eigenspace (symmetryRep g) ((cyclicTwoSign ℝˣ).comp (MonoidHom.snd _ _) g) =
      ℝ ∙ (![1, 0, 1, 0] : Fin 4 → ℝ) := by
  refine iInf_eigenspace_symmetryRep_eq_span symmetryRep_translation_x fun u hr hs ↦ ⟨u 0, ?_⟩
  have hr1 := congrFun hr 1
  have hr3 := congrFun hr 3
  have hs0 := congrFun hs 0
  simp at hr1 hr3 hs0
  ext i
  fin_cases i <;> simp <;> linarith

/-- The isotypic component of the product of the two sign characters, reversed by both `r` and
`s`, is the line through the transverse mode `(0, 1, 0, -1)`. -/
theorem iInf_eigenspace_symmetryRep_coprod :
    ⨅ g, End.eigenspace (symmetryRep g) ((cyclicTwoSign ℝˣ).coprod (cyclicTwoSign ℝˣ) g) =
      ℝ ∙ (![0, 1, 0, -1] : Fin 4 → ℝ) := by
  refine iInf_eigenspace_symmetryRep_eq_span symmetryRep_transverse fun u hr hs ↦ ⟨u 1, ?_⟩
  have hr0 := congrFun hr 0
  have hr2 := congrFun hr 2
  have hs1 := congrFun hs 1
  simp at hr0 hr2 hs1
  ext i
  fin_cases i <;> simp <;> linarith

/-! ### The regular representation -/

/-- The intertwining map from the regular representation of `C₂ × C₂` sending the basis vector
of `g` to `g • (1, 1, 0, 0)`. -/
private noncomputable def leftRegularToSymmetryRep :
    Representation.IntertwiningMap
      (Representation.leftRegular ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
      symmetryRep :=
  (Representation.leftRegularMapEquiv symmetryRep).symm ![1, 1, 0, 0]

private theorem leftRegularToSymmetryRep_single
    (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (c : ℝ) :
    leftRegularToSymmetryRep (MonoidAlgebra.single g c) = c • symmetryRep g ![1, 1, 0, 0] := by
  rw [← mul_one c, ← MonoidAlgebra.smul_single', map_smul, leftRegularToSymmetryRep,
    Representation.leftRegularMapEquiv_symm_single, mul_one]

private theorem bijective_leftRegularToSymmetryRep :
    Function.Bijective leftRegularToSymmetryRep := by
  have hsurj : Function.Surjective leftRegularToSymmetryRep := fun u ↦ by
    refine ⟨MonoidAlgebra.single 1 ((u 0 + u 1) / 2) +
      MonoidAlgebra.single (.ofAdd 1, 1) ((u 0 - u 1) / 2) +
      MonoidAlgebra.single (1, .ofAdd 1) ((u 3 - u 2) / 2) +
      MonoidAlgebra.single (.ofAdd 1, .ofAdd 1) (-(u 2 + u 3) / 2), ?_⟩
    simp only [map_add, leftRegularToSymmetryRep_single]
    ext i
    fin_cases i <;> simp <;> ring
  have hrank : finrank ℝ (MonoidAlgebra ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) =
      finrank ℝ (Fin 4 → ℝ) := by
    rw [Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis _ ℝ), finrank_fin_fun, Nat.card_prod,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := leftRegularToSymmetryRep.toLinearMap)).2 hsurj, hsurj⟩

/-- **The displacement representation is the regular representation of `C₂ × C₂`**: the basis
vector of `g` goes to `g • (1, 1, 0, 0)`, so the four displacements `(1, 1, 0, 0)`,
`r (1, 1, 0, 0) = (1, -1, 0, 0)`, `s (1, 1, 0, 0) = (0, 0, -1, 1)` and
`r s (1, 1, 0, 0) = (0, 0, -1, -1)` form a basis. -/
noncomputable def symmetryRepEquivLeftRegular :
    (Representation.leftRegular ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))).Equiv
      symmetryRep :=
  leftRegularToSymmetryRep.ofBijective bijective_leftRegularToSymmetryRep

/-- The identification with the regular representation sends the basis vector of `g` to
`g • (1, 1, 0, 0)`. -/
@[simp]
theorem symmetryRepEquivLeftRegular_single
    (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) (c : ℝ) :
    symmetryRepEquivLeftRegular (MonoidAlgebra.single g c) = c • symmetryRep g ![1, 1, 0, 0] :=
  leftRegularToSymmetryRep_single g c

/-! ### The projectors onto the modes -/

private theorem sum_cyclicTwo (f : Multiplicative (ZMod 2) → Fin 4 → ℝ) :
    ∑ g, f g = f 1 + f (.ofAdd 1) := by
  rw [show (Finset.univ : Finset (Multiplicative (ZMod 2))) = {1, .ofAdd 1} by decide,
    Finset.sum_pair (by decide)]

/-- The character idempotent `e_χ = ¼ ∑_g χ(g)⁻¹ g` of a character `χ` of `C₂ × C₂` acts on the
displacements by `¼ (1 + χ(r) r + χ(s) s + χ(r s) r s)`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_apply
    (χ : Multiplicative (ZMod 2) × Multiplicative (ZMod 2) →* ℝˣ) (u : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent χ) u = (4 : ℝ)⁻¹ • (u +
      (χ (.ofAdd 1, 1) : ℝ) • axisReflection u + (χ (1, .ofAdd 1) : ℝ) • bisectorReflection u +
      (χ (.ofAdd 1, .ofAdd 1) : ℝ) • ![-u 2, -u 3, -u 0, -u 1]) := by
  have hinv (g : Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : g⁻¹ = g := by
    revert g; decide
  have hcard : (Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) : ℝ) = 4 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    norm_num
  rw [charIdempotent_eq_sum, map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, hcard,
    Ring.inverse_eq_inv', Fintype.sum_prod_type, sum_cyclicTwo, sum_cyclicTwo, sum_cyclicTwo]
  simp only [← map_inv, hinv, map_smul, Representation.asAlgebraHom_of, inv_one,
    LinearMap.smul_apply, ← Prod.one_eq_mk, map_one, Units.val_one, one_smul, one_apply_eq_self,
    symmetryRep_ofAdd_one_one, symmetryRep_one_ofAdd_one, symmetryRep_ofAdd_one_ofAdd_one]
  congr 1
  abel

/-- **The group algebra acts by symmetric operators**: each symmetry is symmetric for the dot
product, hence so is every linear combination of them. In particular, as the character idempotent
`e_χ` is idempotent (`TauCeti.isIdempotentElem_charIdempotent`), it acts by an orthogonal
projector. -/
theorem symmetryRep_asAlgebraHom_dotProduct
    (x : MonoidAlgebra ℝ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) (u w : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom x u ⬝ᵥ w = u ⬝ᵥ symmetryRep.asAlgebraHom x w := by
  simp only [Representation.asAlgebraHom_eq_sum, LinearMap.sum_apply, LinearMap.smul_apply,
    sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, symmetryRep_dotProduct]

/-- The character idempotent of the trivial character acts by the orthogonal projection onto the
line through the stretching mode `v = (1, 0, -1, 0)`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_one_apply (u : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent 1) u =
      ((![1, 0, -1, 0] ⬝ᵥ u) / (![1, 0, -1, 0] ⬝ᵥ ![1, 0, -1, 0])) • ![1, 0, -1, 0] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The character idempotent of the sign character of the first factor acts by the orthogonal
projection onto the line of vertical translations, through `v = (0, 1, 0, 1)`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_comp_fst_apply (u : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent ((cyclicTwoSign ℝˣ).comp (MonoidHom.fst _ _))) u =
      ((![0, 1, 0, 1] ⬝ᵥ u) / (![0, 1, 0, 1] ⬝ᵥ ![0, 1, 0, 1])) • ![0, 1, 0, 1] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The character idempotent of the sign character of the second factor acts by the orthogonal
projection onto the line of horizontal translations, through `v = (1, 0, 1, 0)`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_comp_snd_apply (u : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent ((cyclicTwoSign ℝˣ).comp (MonoidHom.snd _ _))) u =
      ((![1, 0, 1, 0] ⬝ᵥ u) / (![1, 0, 1, 0] ⬝ᵥ ![1, 0, 1, 0])) • ![1, 0, 1, 0] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- The character idempotent of the product of the two sign characters acts by the orthogonal
projection onto the line through the transverse mode `v = (0, 1, 0, -1)`. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_coprod_apply (u : Fin 4 → ℝ) :
    symmetryRep.asAlgebraHom (charIdempotent ((cyclicTwoSign ℝˣ).coprod (cyclicTwoSign ℝˣ))) u =
      ((![0, 1, 0, -1] ⬝ᵥ u) / (![0, 1, 0, -1] ⬝ᵥ ![0, 1, 0, -1])) • ![0, 1, 0, -1] := by
  rw [symmetryRep_asAlgebraHom_charIdempotent_apply]
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four, vecHead, vecTail] <;> ring

/-- **The four mode projectors sum to the identity**: every displacement is the sum of its
stretching, vertical translation, horizontal translation and transverse components. -/
theorem symmetryRep_asAlgebraHom_charIdempotent_add_eq_one :
    symmetryRep.asAlgebraHom (charIdempotent 1) +
        symmetryRep.asAlgebraHom (charIdempotent ((cyclicTwoSign ℝˣ).comp (MonoidHom.fst _ _))) +
        symmetryRep.asAlgebraHom (charIdempotent ((cyclicTwoSign ℝˣ).comp (MonoidHom.snd _ _))) +
        symmetryRep.asAlgebraHom
          (charIdempotent ((cyclicTwoSign ℝˣ).coprod (cyclicTwoSign ℝˣ))) = 1 := by
  refine LinearMap.ext fun u ↦ funext fun i ↦ ?_
  simp only [LinearMap.add_apply, Pi.add_apply, one_apply_eq_self,
    symmetryRep_asAlgebraHom_charIdempotent_one_apply,
    symmetryRep_asAlgebraHom_charIdempotent_comp_fst_apply,
    symmetryRep_asAlgebraHom_charIdempotent_comp_snd_apply,
    symmetryRep_asAlgebraHom_charIdempotent_coprod_apply]
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_four] <;> ring

end TauCeti.TwoParticleSpring
