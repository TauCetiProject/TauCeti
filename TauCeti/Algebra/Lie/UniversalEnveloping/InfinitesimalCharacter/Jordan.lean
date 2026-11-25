/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.Algebra.Lie.Abelian

/-!
# Generalized infinitesimal characters of square-zero deformations

Let `f : L → R` be a Lie algebra homomorphism and `χ = liftCharacter R L f` the character of the
centre of `U(L)` extending it. If every generator acts on a Lie module `M` by `f x` plus an
operator `N x`, and all products `N x * N y` vanish, then `(ker χ)²` annihilates `M`
(`TauCeti.UniversalEnvelopingAlgebra.centralAction_eq_zero_of_mem_ker_liftCharacter_sq`), so `M`
is generalized `χ`-finite. Each element `u` of `U(L)` acts by its value under the extension of
`f` plus an element of the span of the `N x`, and that span squares to zero.

The **two-by-two Jordan block** is the basic example. Let `J = c • 1 + N` with `N * N = 0`; on the
one-dimensional abelian Lie algebra `R`, let `t` act by `t • J`
(`TauCeti.UniversalEnvelopingAlgebra.jordanAction`). The resulting module is generalized
`χ_c`-finite, for the character `χ_c` extending `t ↦ c * t`, but if some character of the centre
acts by scalars then `N` is a scalar multiple of the identity. For `N` the matrix unit `E₀₁` on `R²`
this is the Jordan block with eigenvalue `c`: it is generalized-character-finite, yet its centre
eigenspace is not the whole module for any character. Generalized eigenspaces of the centre are
therefore needed for extensions of modules with an infinitesimal character.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.jordanAction`: the action `t ↦ t • (c • 1 + N)` of the
  one-dimensional abelian Lie algebra `R` on `M`.
* `TauCeti.UniversalEnvelopingAlgebra.jordanNilpotent`: the matrix unit `E₀₁` on `R²`, the
  nilpotent part of the two-by-two Jordan block.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.centralAction_eq_zero_of_mem_ker_liftCharacter_sq`: a
  square-zero deformation of the character `f` is annihilated by `(ker χ)²`.
* `TauCeti.UniversalEnvelopingAlgebra.isGeneralizedCharacterFinite_liftCharacter_of_mul_eq_zero`:
  hence it is generalized `χ`-finite.
* `TauCeti.UniversalEnvelopingAlgebra.isGeneralizedCharacterFinite_jordanAction` and
  `TauCeti.UniversalEnvelopingAlgebra.mem_span_one_of_centerEigenspace_jordanAction_eq_top`: the
  Jordan action is generalized `χ_c`-finite, and has an infinitesimal character only when `N`
  is a scalar multiple of the identity.
* `isGeneralizedCharacterFinite_and_centerEigenspace_ne_top_jordanNilpotent`: the two-by-two
  Jordan block is generalized-character-finite, but no centre eigenspace is the whole module.

## References

* J. Bernstein and B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, Israel J.
  Math. **199** (2014), §4.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Module LieModule

universe u v w

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-! ### Square-zero deformations of a character -/

section SquareZero

variable (f : LieAlgebra.LieCharacter R L)

/-- The span of the deviations `toEnd x - f x` of the Lie action from the character `f`. -/
private noncomputable def deviation : Submodule R (End R M) :=
  Submodule.span R (Set.range fun x : L => toEnd R L M x - algebraMap R (End R M) (f x))

variable {f}

private theorem mul_eq_zero_of_mem_deviation
    (h : ∀ x y : L, (toEnd R L M x - algebraMap R (End R M) (f x)) *
      (toEnd R L M y - algebraMap R (End R M) (f y)) = 0)
    {a b : End R M} (ha : a ∈ deviation (M := M) f) (hb : b ∈ deviation (M := M) f) :
    a * b = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨x, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      exact h x y
    | zero => exact mul_zero _
    | add b c _ _ hb hc => rw [mul_add, hb, hc, add_zero]
    | smul r b _ hb => rw [mul_smul_comm, hb, smul_zero]
  | zero => exact zero_mul _
  | add a c _ _ ha hc => rw [add_mul, ha, hc, add_zero]
  | smul r a _ ha => rw [smul_mul_assoc, ha, smul_zero]

private theorem representation_sub_mem_deviation
    (h : ∀ x y : L, (toEnd R L M x - algebraMap R (End R M) (f x)) *
      (toEnd R L M y - algebraMap R (End R M) (f y)) = 0) (u : U) :
    representation R L M u -
        algebraMap R (End R M) (_root_.UniversalEnvelopingAlgebra.lift R f u) ∈
      deviation (M := M) f := by
  have hu : u ∈ Algebra.adjoin R (Set.range (_root_.UniversalEnvelopingAlgebra.ι R)) := by
    rw [adjoin_range_ι R L]
    exact Algebra.mem_top
  induction hu using Algebra.adjoin_induction with
  | mem u hu =>
    obtain ⟨x, rfl⟩ := hu
    rw [representation_ι, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]
    exact Submodule.subset_span ⟨x, rfl⟩
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self]
    exact zero_mem _
  | add a b _ _ ha hb =>
    rw [map_add, map_add, map_add, add_sub_add_comm]
    exact add_mem ha hb
  | mul a b _ _ ha hb =>
    set A := representation R L M a
    set B := representation R L M b
    set α := _root_.UniversalEnvelopingAlgebra.lift R f a
    set β := _root_.UniversalEnvelopingAlgebra.lift R f b
    have key : A * B - algebraMap R (End R M) (α * β) =
        (A - algebraMap R (End R M) α) * (B - algebraMap R (End R M) β) +
          α • (B - algebraMap R (End R M) β) + β • (A - algebraMap R (End R M) α) := by
      have hc : algebraMap R (End R M) β * algebraMap R (End R M) α =
          algebraMap R (End R M) α * algebraMap R (End R M) β :=
        Algebra.commutes β _
      simp only [Algebra.smul_def, map_mul, mul_sub, sub_mul, Algebra.commutes β A, hc]
      abel
    rw [map_mul, map_mul, key, mul_eq_zero_of_mem_deviation h ha hb, zero_add]
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)

/-- **A square-zero deformation of a character is annihilated by `(ker χ)²`.** If every `x : L`
acts by `f x` plus an operator `N x`, with all products `N x * N y` zero, then the square of the
kernel of the character `liftCharacter R L f` of the centre acts by zero. -/
theorem centralAction_eq_zero_of_mem_ker_liftCharacter_sq
    (h : ∀ x y : L, (toEnd R L M x - algebraMap R (End R M) (f x)) *
      (toEnd R L M y - algebraMap R (End R M) (f y)) = 0)
    {z : Subalgebra.center R U} (hz : z ∈ RingHom.ker (liftCharacter R L f) ^ 2) :
    centralAction R L M z = 0 := by
  have hmem : ∀ w ∈ RingHom.ker (liftCharacter R L f),
      centralAction R L M w ∈ deviation (M := M) f := by
    intro w hw
    have hw' : _root_.UniversalEnvelopingAlgebra.lift R f (w : U) = 0 := by
      rw [← liftCharacter_apply]
      exact RingHom.mem_ker.mp hw
    have hc : centralAction R L M w = representation R L M (w : U) :=
      LinearMap.ext fun m => centralAction_apply w m
    simpa only [hc, hw', map_zero, sub_zero] using representation_sub_mem_deviation h (w : U)
  rw [pow_two] at hz
  refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [map_mul, mul_eq_zero_of_mem_deviation h (hmem a ha) (hmem b hb)]
  · rw [map_add, ha, hb, add_zero]

/-- **A square-zero deformation of a character is generalized-character-finite**: under the
hypothesis of `centralAction_eq_zero_of_mem_ker_liftCharacter_sq`, every vector is annihilated by
the square of the kernel of `liftCharacter R L f`. -/
theorem isGeneralizedCharacterFinite_liftCharacter_of_mul_eq_zero
    (h : ∀ x y : L, (toEnd R L M x - algebraMap R (End R M) (f x)) *
      (toEnd R L M y - algebraMap R (End R M) (f y)) = 0) :
    IsGeneralizedCharacterFinite R L M (liftCharacter R L f) :=
  isGeneralizedCharacterFinite_of_pow 2 fun _ hz =>
    centralAction_eq_zero_of_mem_ker_liftCharacter_sq h hz

end SquareZero

/-! ### The Jordan action of the one-dimensional abelian Lie algebra -/

section Jordan

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] isLieAbelian_of_commRing

variable (R M) in
/-- The **Jordan action** of the one-dimensional abelian Lie algebra `R` on `M`: the scalar `t`
acts by `t • (c • 1 + N)`. For `N` the matrix unit `E₀₁` on `R²` this is the two-by-two Jordan
block with eigenvalue `c`. -/
noncomputable def jordanAction (c : R) (N : End R M) : R →ₗ⁅R⁆ End R M where
  toLinearMap := LinearMap.smulRight LinearMap.id (c • 1 + N)
  map_lie' {s t} := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.smulRight_apply,
      LinearMap.id_apply, smul_lie, lie_smul, lie_self, smul_zero, trivial_lie_zero, zero_smul]

@[simp]
theorem jordanAction_apply (c : R) (N : End R M) (t : R) :
    jordanAction R M c N t = t • (c • 1 + N) :=
  (rfl)

/-- Under the Jordan action, the scalar `r` acts on `M` by `r • (c • 1 + N)`. -/
theorem toEnd_jordanAction (c : R) (N : End R M) (r : R) :
    letI : LieRingModule R M := LieRingModule.compLieHom M (jordanAction R M c N)
    letI : LieModule R R M := LieModule.compLieHom M (jordanAction R M c N)
    toEnd R R M r = r • (c • 1 + N) := by
  ext m
  simp [LieRingModule.compLieHom_apply]

/-- **The Jordan action is generalized `χ_c`-finite**: if `N * N = 0`, the module `M` with the
Jordan action is annihilated by the square of the kernel of the character extending
`t ↦ c * t`. -/
theorem isGeneralizedCharacterFinite_jordanAction (c : R) {N : End R M} (hN : N * N = 0) :
    letI : LieRingModule R M := LieRingModule.compLieHom M (jordanAction R M c N)
    letI : LieModule R R M := LieModule.compLieHom M (jordanAction R M c N)
    IsGeneralizedCharacterFinite R R M
      (liftCharacter R R (LieAlgebra.lieCharacterEquivLinearDual.symm (c • LinearMap.id))) := by
  let _ : LieRingModule R M := LieRingModule.compLieHom M (jordanAction R M c N)
  let _ : LieModule R R M := LieModule.compLieHom M (jordanAction R M c N)
  refine isGeneralizedCharacterFinite_liftCharacter_of_mul_eq_zero fun s t => ?_
  have hdev : ∀ r : R, toEnd R R M r - algebraMap R (End R M)
      (LieAlgebra.lieCharacterEquivLinearDual.symm (c • LinearMap.id) r) = r • N := by
    intro r
    rw [toEnd_jordanAction, LieAlgebra.lieCharacterEquivLinearDual_symm_apply_apply,
      Algebra.algebraMap_eq_smul_one]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    module
  rw [hdev, hdev, smul_mul_smul_comm, hN, smul_zero]

/-- **The Jordan action has an infinitesimal character only when it is scalar**: if some
character of the centre of `U(R)` acts on `M` by scalars, then `N` is a scalar multiple of the
identity. -/
theorem mem_span_one_of_centerEigenspace_jordanAction_eq_top {c : R} {N : End R M}
    {χ : Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R R) → R}
    (h : letI : LieRingModule R M := LieRingModule.compLieHom M (jordanAction R M c N)
      letI : LieModule R R M := LieModule.compLieHom M (jordanAction R M c N)
      centerEigenspace R R M χ = ⊤) :
    N ∈ Submodule.span R {(1 : End R M)} := by
  let _ : LieRingModule R M := LieRingModule.compLieHom M (jordanAction R M c N)
  let _ : LieModule R R M := LieModule.compLieHom M (jordanAction R M c N)
  have h1 := toEnd_eq_smul_of_centerEigenspace_eq_top h (ι_mem_center R R 1)
  rw [toEnd_jordanAction, one_smul] at h1
  rw [eq_sub_of_add_eq' h1, Submodule.mem_span_singleton]
  exact ⟨χ ⟨_, ι_mem_center R R 1⟩ - c, by rw [sub_smul, Module.End.one_eq_id]⟩

/-- The nilpotent part `E₀₁` of the two-by-two Jordan block on `R²`. -/
noncomputable def jordanNilpotent (R : Type u) [CommRing R] : End R (Fin 2 → R) :=
  Matrix.toLin' (Matrix.single 0 1 1)

/-- The nilpotent part of the Jordan block sends `v` to `(v 1, 0)`. -/
@[simp]
theorem jordanNilpotent_apply (v : Fin 2 → R) : jordanNilpotent R v = Pi.single 0 (v 1) := by
  ext i
  fin_cases i <;> simp [jordanNilpotent, Matrix.single_mulVec_eq]

/-- The nilpotent part of the Jordan block squares to zero. -/
theorem jordanNilpotent_mul_self : jordanNilpotent R * jordanNilpotent R = 0 :=
  LinearMap.ext fun v => by simp

/-- **The two-by-two Jordan block is generalized-character-finite but has no infinitesimal
character.** On `R²` with `t` acting by `t` times the Jordan block with eigenvalue `c`, every
vector is annihilated by a power of the kernel of `χ_c`, but no character of the centre of
`U(R)` acts by scalars. -/
theorem isGeneralizedCharacterFinite_and_centerEigenspace_ne_top_jordanNilpotent [Nontrivial R]
    (c : R) (χ : Subalgebra.center R (_root_.UniversalEnvelopingAlgebra R R) → R) :
    letI : LieRingModule R (Fin 2 → R) :=
      LieRingModule.compLieHom _ (jordanAction R _ c (jordanNilpotent R))
    letI : LieModule R R (Fin 2 → R) :=
      LieModule.compLieHom _ (jordanAction R _ c (jordanNilpotent R))
    IsGeneralizedCharacterFinite R R (Fin 2 → R)
        (liftCharacter R R (LieAlgebra.lieCharacterEquivLinearDual.symm (c • LinearMap.id))) ∧
      centerEigenspace R R (Fin 2 → R) χ ≠ ⊤ := by
  refine ⟨isGeneralizedCharacterFinite_jordanAction c jordanNilpotent_mul_self, fun h => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
    (mem_span_one_of_centerEigenspace_jordanAction_eq_top h)
  have := congr_fun (LinearMap.congr_fun ha (Pi.single 1 1)) 0
  simp at this

end Jordan

end TauCeti.UniversalEnvelopingAlgebra
