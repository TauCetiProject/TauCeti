/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Length
public import TauCeti.RingTheory.Artinian.FiniteLength
public import TauCeti.RingTheory.Length

/-!
# Length over a finite algebra

Let `R` be a commutative ring and `A` an `R`-algebra. Every chain of `A`-submodules of an
`A`-module is a chain of `R`-submodules, so finite length over `R` implies finite length over `A`
(`TauCeti.isFiniteLength_of_tower`).
When `A` is finitely generated as an `R`-module the converse holds as well: a simple `A`-module `S`
is finitely generated over `R`, and Nakayama's lemma shows that its annihilator in `R` is a maximal
ideal `𝔪`, so `S` is a finite-dimensional vector space over `R ⧸ 𝔪`. Hence an `A`-module has finite
length over `A` exactly when it has finite length over `R`.

Without finiteness of `A` the converse fails: the field `k(t)` is simple over itself but has
infinite length over `k`.

## Main results

* `TauCeti.isMaximal_annihilator_of_isSimpleModule`: a simple module over a finite `R`-algebra is
  killed by a maximal ideal of `R`.
* `TauCeti.isFiniteLength_of_isSimpleModule`: a simple module over a finite `R`-algebra has finite
  length over `R`.
* `TauCeti.isFiniteLength_iff_of_finite`: for `A` finite over `R`, finite length over `A` and over
  `R` agree.
-/

public section

namespace TauCeti

open Submodule

variable {R : Type*} [CommRing R] {A : Type*} [Ring A] [Algebra R A] [Module.Finite R A]
  {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A simple module over a finite `R`-algebra is killed by a maximal ideal of `R`. -/
theorem isMaximal_annihilator_of_isSimpleModule [IsSimpleModule A M] :
    (Module.annihilator R M).IsMaximal := by
  have : Module.Finite R M := Module.Finite.trans A M
  have hp : Module.annihilator R M ≠ ⊤ := by
    rw [Ne, Module.annihilator_eq_top_iff, not_subsingleton_iff_nontrivial]
    exact IsSimpleModule.nontrivial A M
  obtain ⟨𝔪, h𝔪, hp𝔪⟩ := Ideal.exists_le_maximal _ hp
  -- `𝔪 M` is an `A`-submodule, since `R` acts centrally.
  let K : Submodule A M :=
    { carrier := (𝔪 • ⊤ : Submodule R M)
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' a x hx := by
        refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) fun x y hx hy ↦ ?_
        · rw [smul_comm a r y]
          exact Submodule.smul_mem_smul hr trivial
        · rw [smul_add]
          exact add_mem hx hy }
  rcases IsSimpleOrder.eq_bot_or_eq_top K with hK | hK
  · convert h𝔪
    refine le_antisymm hp𝔪 fun r hr ↦ Module.mem_annihilator.mpr fun y ↦ ?_
    have : r • y ∈ K := Submodule.smul_mem_smul hr trivial
    simpa [hK] using this
  · exfalso
    have htop : (⊤ : Submodule R M) ≤ 𝔪 • ⊤ := fun y _ ↦ by
      have : y ∈ K := hK ▸ Submodule.mem_top
      exact this
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤
      Module.Finite.fg_top htop
    have : r ∈ 𝔪 := hp𝔪 (Module.mem_annihilator.mpr fun y ↦ hr y trivial)
    exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem this hr1))

/-- A simple module over a finite `R`-algebra has finite length over `R`. -/
theorem isFiniteLength_of_isSimpleModule [IsSimpleModule A M] : IsFiniteLength R M := by
  have : Module.Finite R M := Module.Finite.trans A M
  have h𝔪 := isMaximal_annihilator_of_isSimpleModule (R := R) (A := A) (M := M)
  let 𝔪 := Module.annihilator R M
  have ht : Module.IsTorsionBySet R M 𝔪 := fun x r ↦ Module.mem_annihilator.mp r.2 x
  let := ht.module
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : IsScalarTower R (R ⧸ 𝔪) M := ht.isScalarTower (S := R)
  have : Module.Finite (R ⧸ 𝔪) M := Module.Finite.of_restrictScalars_finite R _ M
  have hfl : IsFiniteLength (R ⧸ 𝔪) M := isFiniteLength_of_finite _ M
  rw [← Module.length_ne_top_iff] at hfl ⊢
  rwa [Module.length_eq_of_surjective (S := R) (Ideal.Quotient.mk_surjective (I := 𝔪))]

/-- The induction behind `isFiniteLength_iff_of_finite`, with the `R`-module structure quantified
so that it follows the module along the composition series. -/
private theorem isFiniteLength_of_finite_aux (M : Type*) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) : ∀ [Module R M] [IsScalarTower R A M], IsFiniteLength R M := by
  induction hM with
  | of_subsingleton => intro _ _; exact .of_subsingleton
  | @of_simple_quotient M _ _ N _ _ ih =>
    intro _ _
    have hN : IsFiniteLength R N := ih
    have hQ : IsFiniteLength R (M ⧸ N) := isFiniteLength_of_isSimpleModule (A := A)
    rw [← Module.length_ne_top_iff] at hN hQ ⊢
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
      N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)]
    exact WithTop.add_ne_top.mpr ⟨hN, hQ⟩

variable (R A M) in
/-- **Length over a finite algebra.** For an `R`-algebra `A` that is finitely generated as an
`R`-module, an `A`-module has finite length over `A` exactly when it has finite length over `R`. -/
theorem isFiniteLength_iff_of_finite : IsFiniteLength A M ↔ IsFiniteLength R M :=
  ⟨fun hM ↦ isFiniteLength_of_finite_aux M hM, isFiniteLength_of_tower R⟩

end TauCeti
