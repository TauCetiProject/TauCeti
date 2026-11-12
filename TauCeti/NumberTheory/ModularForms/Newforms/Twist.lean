/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
public import TauCeti.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic
import TauCeti.NumberTheory.ModularForms.Twist.Hecke

/-!
# The primitive associate of a twisted newform

Let `f` be a newform of level `N` and nebentypus `χ`, and let `ψ` be a Dirichlet character
modulo `M`. For a level `L` with `N * M ∣ L` and `M * M ∣ L`, the twist `f ⊗ ψ` is a cusp form
in `S_k(Γ₁(L), χψ²)` with `q`-expansion `∑ ψ(n) aₙ(f) qⁿ`. At a prime `p ∤ L` it is a
`T_p`-eigenvector with eigenvalue `ψ(p) a_p(f)` (`CuspForm.heckeTCuspNat_twist_eq_smul`), and
its first coefficient is `ψ(1) a₁(f) = 1`. So the twist is a nonzero good Hecke eigenform at
level `L`, and the existence of the newform associated with an eigenform gives a newform `g`
of some level dividing `L`, with nebentypus inducing `χψ²`, such that

`a_p(g) = ψ(p) a_p(f)` at every prime `p ∤ L`.

This `g` is the *primitive associate* of `f ⊗ ψ`. By strong multiplicity one across levels
(`HeckeRing.GL2.Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq`) it is unique, together with its
level, and it does not depend on `L`. This file names it `primitiveTwist f ψ`, the **primitive
twist** of `f` by `ψ`, of level `primitiveTwistLevel f ψ`, and characterizes it: its level
divides every admissible `L`, its nebentypus read at `L` is `χψ²`, its coefficients at the
primes `p ∤ N M` are `ψ(p) a_p(f)`, and every newform with these properties is it. Since
different levels are different types, newforms of possibly different levels are compared as
functions on the upper half-plane; at a fixed level this is equality of newforms
(`HeckeRing.GL2.Newform.ext`).

The uniqueness gives the basic algebra of twisting: twisting by a trivial character returns
`f`, raising the modulus of `ψ` does not change the twist, and twisting by `ψ` and then by `ψ'`
is twisting by `ψψ'`, read at any common multiple of their moduli, so twisting by `ψ⁻¹` undoes
twisting by `ψ`. The sharp level of the primitive twist is not determined here.

## Main definitions

* `HeckeRing.GL2.Newform.primitiveTwist`: the primitive twist of a newform by a Dirichlet
  character, of level `HeckeRing.GL2.Newform.primitiveTwistLevel`.

## Main results

* `HeckeRing.GL2.Newform.exists_newform_qExpansion_coeff_prime_eq_twist`: the existence of the
  primitive associate of `f ⊗ ψ`, with its nebentypus and its coefficients at the primes
  `p ∤ L`.
* `HeckeRing.GL2.Newform.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist`: its uniqueness,
  with its level, against agreement at all but finitely many primes `p ∤ L`.
* `HeckeRing.GL2.Newform.primitiveTwistLevel_dvd`,
  `HeckeRing.GL2.Newform.primitiveTwist_χ_comp_unitsMap`,
  `HeckeRing.GL2.Newform.qExpansion_coeff_primitiveTwist`: the level, the nebentypus and the
  good-prime coefficients of the primitive twist.
* `HeckeRing.GL2.Newform.coe_primitiveTwist_one`,
  `HeckeRing.GL2.Newform.coe_primitiveTwist_changeLevel`,
  `HeckeRing.GL2.Newform.coe_primitiveTwist_primitiveTwist_of_dvd`,
  `HeckeRing.GL2.Newform.coe_primitiveTwist_primitiveTwist`,
  `HeckeRing.GL2.Newform.coe_primitiveTwist_primitiveTwist_inv`: twisting by a trivial character,
  by a character of raised modulus, by a product of characters of possibly different moduli, and
  back by the inverse character, with the corresponding level identities.

## References

* A. O. L. Atkin, W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of `W`-operators*,
  Invent. Math. 48 (1978).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Proposition 5.8.4.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.19, for the uniqueness across levels.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ZMod

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {M N L : ℕ} [NeZero N] {k : ℤ}

/-- **The primitive associate of a twisted newform.** Let `f` be a newform of level `N` and
nebentypus `χ`, `ψ` a Dirichlet character modulo `M`, and `L` a level with `N * M ∣ L` and
`M * M ∣ L`. Then there is a newform `g` of some level `R ∣ L`, whose nebentypus read at level
`L` is `χψ²`, with `a_p(g) = ψ(p) a_p(f)` at every prime `p ∤ L`. -/
theorem exists_newform_qExpansion_coeff_prime_eq_twist [NeZero M] [NeZero L] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) (hNL : N * M ∣ L) (hML : M * M ∣ L) :
    ∃ (R : ℕ) (_ : NeZero R) (hR : R ∣ L) (g : Newform R k),
      g.χ.comp (unitsMap hR) = f.χ.comp (unitsMap (dvd_of_mul_right_dvd hNL)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_of_mul_left_dvd hML))) ^ 2 ∧
      ∀ p : ℕ, p.Prime → p.Coprime L →
        (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p := by
  have hNL' : N ∣ L := dvd_of_mul_right_dvd hNL
  -- the twist is nonzero, since its first coefficient is `ψ(1) a₁(f) = 1`
  have hF0 : CuspForm.twist ψ hNL hML f.toCuspForm ≠ 0 := fun h ↦ by
    have h1 := CuspForm.qExpansion_twist_coeff ψ hNL hML f.toCuspForm 1
    simp [h, f.qExpansion_coeff_one, UpperHalfPlane.qExpansion_zero] at h1
  obtain ⟨R, _, hR, g, hgχ, hg⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      (CuspForm.twist_mem_cuspFormCharSpace ψ hNL hML f.mem_charSpace) hF0
      (a := fun p hp hpL ↦ ψ p * f.eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hNL'))
      fun p hp hpL ↦ CuspForm.heckeTCuspNat_twist_eq_smul ψ hNL hML f.mem_charSpace hp hpL
        (f.heckeTCuspNat_eq_eigenvalue_smul hp (hpL.coprime_dvd_right hNL'))
  refine ⟨R, inferInstance, hR, g, hgχ, fun p hp hpL ↦ ?_⟩
  have hg' : (qExpansion 1 g.toCuspForm).coeff p = _ :=
    g.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hR)
  have hf' : (qExpansion 1 f.toCuspForm).coeff p = _ :=
    f.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ (hpL.coprime_dvd_right hNL')
  rw [hg', hg p hp hpL, hf']

/-! ### The primitive twist -/

omit [NeZero N] in
private theorem dvd_mul_mul_self (N M : ℕ) : N ∣ N * M * M :=
  Dvd.intro (M * M) (mul_assoc N M M).symm

omit [NeZero N] in
private theorem dvd_mul_mul_self' (N M : ℕ) : M ∣ N * M * M :=
  Dvd.intro_left (N * M) rfl

/-- The level `N * M * M` is a common multiple of `N * M` and `M * M`, at which the primitive
associate of `f ⊗ ψ` is chosen. -/
private theorem exists_primitiveTwist [NeZero M] (f : Newform N k) (ψ : DirichletCharacter ℂ M) :
    ∃ (R : ℕ) (_ : NeZero R) (hR : R ∣ N * M * M) (g : Newform R k),
      g.χ.comp (unitsMap hR) = f.χ.comp (unitsMap (dvd_mul_mul_self N M)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_mul_mul_self' N M))) ^ 2 ∧
      ∀ p : ℕ, p.Prime → p.Coprime (N * M * M) →
        (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p :=
  f.exists_newform_qExpansion_coeff_prime_eq_twist ψ (dvd_mul_right _ _)
    (Dvd.intro_left N (mul_assoc N M M).symm)

/-- **The level of the primitive twist** `f ⊗ ψ` of a newform `f` by a Dirichlet character `ψ`:
the level of the newform `primitiveTwist f ψ`. It divides every common multiple of `N * M` and
`M * M` (`primitiveTwistLevel_dvd`) and is determined by `f` and `ψ`
(`level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist`). -/
noncomputable def primitiveTwistLevel [NeZero M] (f : Newform N k) (ψ : DirichletCharacter ℂ M) :
    ℕ :=
  (f.exists_primitiveTwist ψ).choose

instance [NeZero M] (f : Newform N k) (ψ : DirichletCharacter ℂ M) :
    NeZero (f.primitiveTwistLevel ψ) :=
  (f.exists_primitiveTwist ψ).choose_spec.choose

private theorem primitiveTwistLevel_dvd_mul_mul [NeZero M] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) : f.primitiveTwistLevel ψ ∣ N * M * M :=
  (f.exists_primitiveTwist ψ).choose_spec.choose_spec.choose

/-- **The primitive twist** of a newform `f` of level `N` by a Dirichlet character `ψ` modulo `M`:
the primitive associate of the twisted cusp form `f ⊗ ψ = ∑ ψ(n) aₙ(f) qⁿ`, that is, the newform
whose eigenvalues at the primes `p ∤ N M` are `ψ(p) a_p(f)` and whose nebentypus induces `χψ²`.
Its level is `primitiveTwistLevel f ψ`. Such a newform exists
(`exists_newform_qExpansion_coeff_prime_eq_twist`), and by strong multiplicity one across levels
it is unique, together with its level
(`level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist`). -/
noncomputable def primitiveTwist [NeZero M] (f : Newform N k) (ψ : DirichletCharacter ℂ M) :
    Newform (f.primitiveTwistLevel ψ) k :=
  (f.exists_primitiveTwist ψ).choose_spec.choose_spec.choose_spec.choose

private theorem primitiveTwist_χ_comp_unitsMap_mul_mul [NeZero M] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) :
    (f.primitiveTwist ψ).χ.comp (unitsMap (f.primitiveTwistLevel_dvd_mul_mul ψ)) =
      f.χ.comp (unitsMap (dvd_mul_mul_self N M)) *
        (ψ.toUnitHom.comp (unitsMap (dvd_mul_mul_self' N M))) ^ 2 :=
  (f.exists_primitiveTwist ψ).choose_spec.choose_spec.choose_spec.choose_spec.1

/-- **The coefficients of the primitive twist at the good primes**: `a_p(f ⊗ ψ) = ψ(p) a_p(f)` at
every prime `p` coprime to `N` and to `M`. -/
theorem qExpansion_coeff_primitiveTwist [NeZero M] (f : Newform N k) (ψ : DirichletCharacter ℂ M)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpM : p.Coprime M) :
    (qExpansion 1 (f.primitiveTwist ψ).toCuspForm).coeff p =
      ψ p * (qExpansion 1 f.toCuspForm).coeff p :=
  (f.exists_primitiveTwist ψ).choose_spec.choose_spec.choose_spec.choose_spec.2 p hp
    ((hpN.mul_right hpM).mul_right hpM)

omit [NeZero N] in
/-- Raising the level of the nebentypus `χψ²` of a twist from `L` to a multiple `L'`. -/
private theorem twist_χ_comp_unitsMap {L L' : ℕ} (χ : (ZMod N)ˣ →* ℂˣ)
    (ψ : DirichletCharacter ℂ M) (hNL : N ∣ L) (hML : M ∣ L) (hLL' : L ∣ L') :
    (χ.comp (unitsMap hNL) * (ψ.toUnitHom.comp (unitsMap hML)) ^ 2).comp (unitsMap hLL') =
      χ.comp (unitsMap (hNL.trans hLL')) * (ψ.toUnitHom.comp (unitsMap (hML.trans hLL'))) ^ 2 := by
  ext u
  simp [← ZMod.unitsMap_comp hNL hLL', ← ZMod.unitsMap_comp hML hLL']

/-- **Uniqueness of the primitive twist** (strong multiplicity one across levels). Let `f` be a
newform of level `N` and nebentypus `χ`, `ψ` a Dirichlet character modulo `M`, and `L` a common
multiple of `N` and `M`. A newform `g` of a level `R ∣ L` whose nebentypus, read at level `L`, is
`χψ²`, and with `a_p(g) = ψ(p) a_p(f)` at all primes `p ∤ L` outside a finite set, has the level
of the primitive twist of `f` by `ψ` and is the same function. -/
theorem level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist [NeZero M] {R L : ℕ} [NeZero R]
    [NeZero L] (f : Newform N k) (ψ : DirichletCharacter ℂ M) (g : Newform R k) (hR : R ∣ L)
    (hNL : N ∣ L) (hML : M ∣ L)
    (hχ : g.χ.comp (unitsMap hR) = f.χ.comp (unitsMap hNL) *
        (ψ.toUnitHom.comp (unitsMap hML)) ^ 2)
    {S : Finset ℕ} (h : ∀ p : ℕ, p.Prime → p.Coprime L → p ∉ S →
      (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p) :
    R = f.primitiveTwistLevel ψ ∧ ⇑g.toCuspForm = ⇑(f.primitiveTwist ψ).toCuspForm := by
  -- compare both newforms at the common level `L' = lcm L (N * M * M)`
  set L' := Nat.lcm L (N * M * M)
  have hL : L ∣ L' := Nat.dvd_lcm_left _ _
  have hL₀ : N * M * M ∣ L' := Nat.dvd_lcm_right _ _
  have : NeZero L' := ⟨Nat.lcm_ne_zero (NeZero.ne L) (NeZero.ne _)⟩
  have hR' := hR.trans hL
  have hT' := (f.primitiveTwistLevel_dvd_mul_mul ψ).trans hL₀
  refine Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq g (f.primitiveTwist ψ) hR' hT'
    (χ := f.χ.comp (unitsMap (hNL.trans hL)) * (ψ.toUnitHom.comp (unitsMap (hML.trans hL))) ^ 2)
    ?_ ?_ (S := S) fun p hp hpL' hpS ↦ ?_
  · rw [← ZMod.unitsMap_comp hR hL, ← MonoidHom.comp_assoc, hχ, twist_χ_comp_unitsMap]
  · rw [← ZMod.unitsMap_comp (f.primitiveTwistLevel_dvd_mul_mul ψ) hL₀, ← MonoidHom.comp_assoc,
      primitiveTwist_χ_comp_unitsMap_mul_mul, twist_χ_comp_unitsMap]
  · have hpL := hpL'.coprime_dvd_right hL
    have hg := g.qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩ (hpL'.coprime_dvd_right hR')
    have ht := (f.primitiveTwist ψ).qExpansion_coeff_eq_eigenvalue ⟨p, hp.pos⟩
      (hpL'.coprime_dvd_right hT')
    rw [← hg, ← ht]
    exact (h p hp hpL hpS).trans (qExpansion_coeff_primitiveTwist f ψ hp
      (hpL.coprime_dvd_right hNL) (hpL.coprime_dvd_right hML)).symm

/-- **The level of the primitive twist** of a newform of level `N` by a character modulo `M`
divides every common multiple of `N * M` and `M * M`, for instance `M * lcm N M`. -/
theorem primitiveTwistLevel_dvd [NeZero M] {L : ℕ} (f : Newform N k) (ψ : DirichletCharacter ℂ M)
    (hNL : N * M ∣ L) (hML : M * M ∣ L) : f.primitiveTwistLevel ψ ∣ L := by
  rcases eq_or_ne L 0 with rfl | hL
  · exact dvd_zero _
  have : NeZero L := ⟨hL⟩
  obtain ⟨R, _, hR, g, hgχ, hg⟩ := f.exists_newform_qExpansion_coeff_prime_eq_twist ψ hNL hML
  obtain ⟨rfl, -⟩ := f.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist ψ g hR
    (dvd_of_mul_right_dvd hNL) (dvd_of_mul_left_dvd hML) hgχ (S := ∅) fun p hp hpL _ ↦ hg p hp hpL
  exact hR

/-- **The nebentypus of the primitive twist** of a newform `f` of nebentypus `χ` by a character
`ψ` modulo `M`: read at a common multiple `L` of its level, `N` and `M`, it is `χψ²`. -/
theorem primitiveTwist_χ_comp_unitsMap [NeZero M] {L : ℕ} [NeZero L] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) (hL : f.primitiveTwistLevel ψ ∣ L) (hNL : N ∣ L) (hML : M ∣ L) :
    (f.primitiveTwist ψ).χ.comp (unitsMap hL) =
      f.χ.comp (unitsMap hNL) * (ψ.toUnitHom.comp (unitsMap hML)) ^ 2 := by
  -- both sides agree at `L' = lcm L (N * M * M)`, and `(ZMod L')ˣ → (ZMod L)ˣ` is onto
  have hL' : L ∣ Nat.lcm L (N * M * M) := Nat.dvd_lcm_left _ _
  have : NeZero (Nat.lcm L (N * M * M)) := ⟨Nat.lcm_ne_zero (NeZero.ne L) (NeZero.ne _)⟩
  refine (MonoidHom.cancel_right (ZMod.unitsMap_surjective hL')).mp ?_
  rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp, twist_χ_comp_unitsMap,
    ← ZMod.unitsMap_comp (f.primitiveTwistLevel_dvd_mul_mul ψ) (Nat.dvd_lcm_right _ _),
    ← MonoidHom.comp_assoc, primitiveTwist_χ_comp_unitsMap_mul_mul, twist_χ_comp_unitsMap]

private theorem level_eq_and_coe_eq_primitiveTwist_one [NeZero M] (f : Newform N k) :
    N = f.primitiveTwistLevel (1 : DirichletCharacter ℂ M) ∧
      ⇑f.toCuspForm = ⇑(f.primitiveTwist (1 : DirichletCharacter ℂ M)).toCuspForm := by
  refine f.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist 1 f
    (dvd_mul_mul_self N M) (dvd_mul_mul_self N M)
    (dvd_mul_mul_self' N M) ?_ (S := ∅) fun p _ hpL _ ↦ ?_
  · ext u
    simp
  · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime p M).mpr
      (hpL.coprime_dvd_right (dvd_mul_mul_self' N M))), one_mul]

/-- **Twisting by a trivial character** does not change the level of a newform. -/
@[simp]
theorem primitiveTwistLevel_one [NeZero M] (f : Newform N k) :
    f.primitiveTwistLevel (1 : DirichletCharacter ℂ M) = N :=
  f.level_eq_and_coe_eq_primitiveTwist_one.1.symm

/-- **The primitive twist by a trivial character** is the newform itself. -/
@[simp]
theorem coe_primitiveTwist_one [NeZero M] (f : Newform N k) :
    ⇑(f.primitiveTwist (1 : DirichletCharacter ℂ M)).toCuspForm = ⇑f.toCuspForm :=
  f.level_eq_and_coe_eq_primitiveTwist_one.2.symm

private theorem level_eq_and_coe_eq_primitiveTwist_changeLevel [NeZero M] {M' : ℕ} [NeZero M']
    (f : Newform N k) (ψ : DirichletCharacter ℂ M) (h : M ∣ M') :
    f.primitiveTwistLevel ψ = f.primitiveTwistLevel (ψ.changeLevel h) ∧
      ⇑(f.primitiveTwist ψ).toCuspForm = ⇑(f.primitiveTwist (ψ.changeLevel h)).toCuspForm := by
  -- compare at the level `L = N M'²`, a multiple of `N M²`
  set L := N * M' * M'
  have : NeZero L := ⟨by simp [L, NeZero.ne N, NeZero.ne M']⟩
  have hRL := (f.primitiveTwistLevel_dvd_mul_mul ψ).trans (mul_dvd_mul (mul_dvd_mul_left N h) h)
  have hNL : N ∣ L := dvd_mul_mul_self N M'
  have hML : M' ∣ L := dvd_mul_mul_self' N M'
  refine f.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist (ψ.changeLevel h)
    (f.primitiveTwist ψ) hRL hNL hML ?_ (S := ∅) fun p hp hpL _ ↦ ?_
  · rw [primitiveTwist_χ_comp_unitsMap f ψ hRL hNL (h.trans hML),
      DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  · rw [qExpansion_coeff_primitiveTwist f ψ hp (hpL.coprime_dvd_right hNL)
      ((hpL.coprime_dvd_right hML).coprime_dvd_right h),
      DirichletCharacter.changeLevel_natCast_of_coprime h ψ (hpL.coprime_dvd_right hML)]

/-- **Raising the modulus** of the twisting character does not change the level of the primitive
twist. -/
@[simp]
theorem primitiveTwistLevel_changeLevel [NeZero M] {M' : ℕ} [NeZero M'] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) (h : M ∣ M') :
    f.primitiveTwistLevel (ψ.changeLevel h) = f.primitiveTwistLevel ψ :=
  (f.level_eq_and_coe_eq_primitiveTwist_changeLevel ψ h).1.symm

/-- **Raising the modulus** of the twisting character does not change the primitive twist. -/
@[simp]
theorem coe_primitiveTwist_changeLevel [NeZero M] {M' : ℕ} [NeZero M'] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) (h : M ∣ M') :
    ⇑(f.primitiveTwist (ψ.changeLevel h)).toCuspForm = ⇑(f.primitiveTwist ψ).toCuspForm :=
  (f.level_eq_and_coe_eq_primitiveTwist_changeLevel ψ h).2.symm

private theorem level_eq_and_coe_eq_primitiveTwist_primitiveTwist [NeZero M] {M' M'' : ℕ}
    [NeZero M'] [NeZero M''] (f : Newform N k) (ψ : DirichletCharacter ℂ M)
    (ψ' : DirichletCharacter ℂ M') (hM : M ∣ M'') (hM' : M' ∣ M'') :
    (f.primitiveTwist ψ).primitiveTwistLevel ψ' =
        f.primitiveTwistLevel (ψ.changeLevel hM * ψ'.changeLevel hM') ∧
      ⇑((f.primitiveTwist ψ).primitiveTwist ψ').toCuspForm =
        ⇑(f.primitiveTwist (ψ.changeLevel hM * ψ'.changeLevel hM')).toCuspForm := by
  set R := f.primitiveTwistLevel ψ
  set g := f.primitiveTwist ψ
  -- everything happens at the level `L = N M² M'² M''`, a multiple of `R M'²`
  set L := N * M * M * M' * M' * M''
  have : NeZero L := ⟨by simp [L, NeZero.ne N, NeZero.ne M, NeZero.ne M', NeZero.ne M'']⟩
  have hRL' : R * M' * M' ∣ L := (mul_dvd_mul_right (mul_dvd_mul_right
    (f.primitiveTwistLevel_dvd_mul_mul ψ) M') M').trans (Dvd.intro M'' rfl)
  have hRL : R ∣ L := dvd_of_mul_right_dvd (dvd_of_mul_right_dvd hRL')
  have hTL := (g.primitiveTwistLevel_dvd_mul_mul ψ').trans hRL'
  have hNL : N ∣ L := Dvd.intro (M * M * M' * M' * M'') (by ring)
  have hML : M ∣ L := Dvd.intro (N * M * M' * M' * M'') (by ring)
  have hM'L : M' ∣ L := Dvd.intro (N * M * M * M' * M'') (by ring)
  have hM''L : M'' ∣ L := Dvd.intro_left (N * M * M * M' * M') rfl
  refine f.level_eq_primitiveTwistLevel_and_coe_eq_primitiveTwist _ (g.primitiveTwist ψ') hTL hNL
    hM''L ?_ (S := ∅) fun p hp hpL _ ↦ ?_
  · rw [primitiveTwist_χ_comp_unitsMap g ψ' hTL hRL hM'L, primitiveTwist_χ_comp_unitsMap f ψ hRL hNL
      hML]
    ext u
    simp [← ZMod.unitsMap_comp hM hM''L, ← ZMod.unitsMap_comp hM' hM''L, MulChar.coeToFun_mul,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val hM,
      ← ZMod.unitsMap_val hM']
    ring
  · have hpM'' := hpL.coprime_dvd_right hM''L
    rw [qExpansion_coeff_primitiveTwist g ψ' hp (hpL.coprime_dvd_right hRL)
      (hpL.coprime_dvd_right hM'L), qExpansion_coeff_primitiveTwist f ψ hp
      (hpL.coprime_dvd_right hNL) (hpL.coprime_dvd_right hML), MulChar.coeToFun_mul, Pi.mul_apply,
      DirichletCharacter.changeLevel_natCast_of_coprime hM ψ hpM'',
      DirichletCharacter.changeLevel_natCast_of_coprime hM' ψ' hpM'']
    ring

/-- **Twisting a primitive twist again**, by characters of different moduli: if `M ∣ M''` and
`M' ∣ M''`, the level of the primitive twist by `ψ'` modulo `M'` of the primitive twist of `f` by
`ψ` modulo `M` is the level of the primitive twist of `f` by the product of `ψ` and `ψ'` modulo
`M''`. -/
theorem primitiveTwistLevel_primitiveTwist_of_dvd [NeZero M] {M' M'' : ℕ} [NeZero M'] [NeZero M'']
    (f : Newform N k) (ψ : DirichletCharacter ℂ M) (ψ' : DirichletCharacter ℂ M') (hM : M ∣ M'')
    (hM' : M' ∣ M'') :
    (f.primitiveTwist ψ).primitiveTwistLevel ψ' =
      f.primitiveTwistLevel (ψ.changeLevel hM * ψ'.changeLevel hM') :=
  (f.level_eq_and_coe_eq_primitiveTwist_primitiveTwist ψ ψ' hM hM').1

/-- **Twisting a primitive twist again**, by characters of different moduli: if `M ∣ M''` and
`M' ∣ M''`, the primitive twist by `ψ'` modulo `M'` of the primitive twist of `f` by `ψ` modulo
`M` is the primitive twist of `f` by the product of `ψ` and `ψ'` modulo `M''`. -/
theorem coe_primitiveTwist_primitiveTwist_of_dvd [NeZero M] {M' M'' : ℕ} [NeZero M'] [NeZero M'']
    (f : Newform N k) (ψ : DirichletCharacter ℂ M) (ψ' : DirichletCharacter ℂ M') (hM : M ∣ M'')
    (hM' : M' ∣ M'') :
    ⇑((f.primitiveTwist ψ).primitiveTwist ψ').toCuspForm =
      ⇑(f.primitiveTwist (ψ.changeLevel hM * ψ'.changeLevel hM')).toCuspForm :=
  (f.level_eq_and_coe_eq_primitiveTwist_primitiveTwist ψ ψ' hM hM').2

/-- **Twisting a primitive twist again**: the level of the primitive twist by `ψ'` of the
primitive twist of `f` by `ψ` is the level of the primitive twist of `f` by `ψψ'`. -/
@[simp]
theorem primitiveTwistLevel_primitiveTwist [NeZero M] (f : Newform N k)
    (ψ ψ' : DirichletCharacter ℂ M) :
    (f.primitiveTwist ψ).primitiveTwistLevel ψ' = f.primitiveTwistLevel (ψ * ψ') := by
  rw [primitiveTwistLevel_primitiveTwist_of_dvd f ψ ψ' (dvd_refl M) (dvd_refl M),
    DirichletCharacter.changeLevel_self, DirichletCharacter.changeLevel_self]

/-- **Twisting a primitive twist again**: the primitive twist by `ψ'` of the primitive twist of
`f` by `ψ` is the primitive twist of `f` by `ψψ'`. -/
@[simp]
theorem coe_primitiveTwist_primitiveTwist [NeZero M] (f : Newform N k)
    (ψ ψ' : DirichletCharacter ℂ M) :
    ⇑((f.primitiveTwist ψ).primitiveTwist ψ').toCuspForm =
      ⇑(f.primitiveTwist (ψ * ψ')).toCuspForm := by
  rw [coe_primitiveTwist_primitiveTwist_of_dvd f ψ ψ' (dvd_refl M) (dvd_refl M),
    DirichletCharacter.changeLevel_self, DirichletCharacter.changeLevel_self]

/-- **Twisting back**: the primitive twist by `ψ⁻¹` of the primitive twist of `f` by `ψ` has the
level of `f`. -/
theorem primitiveTwistLevel_primitiveTwist_inv [NeZero M] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) : (f.primitiveTwist ψ).primitiveTwistLevel ψ⁻¹ = N := by
  rw [primitiveTwistLevel_primitiveTwist, mul_inv_cancel, primitiveTwistLevel_one]

/-- **Twisting back**: the primitive twist by `ψ⁻¹` of the primitive twist of `f` by `ψ` is `f`.
-/
@[simp high]
theorem coe_primitiveTwist_primitiveTwist_inv [NeZero M] (f : Newform N k)
    (ψ : DirichletCharacter ℂ M) :
    ⇑((f.primitiveTwist ψ).primitiveTwist ψ⁻¹).toCuspForm = ⇑f.toCuspForm := by
  rw [coe_primitiveTwist_primitiveTwist, mul_inv_cancel, coe_primitiveTwist_one]

end HeckeRing.GL2.Newform
