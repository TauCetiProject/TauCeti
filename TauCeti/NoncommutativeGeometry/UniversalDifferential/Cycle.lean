/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.UniversalDifferential.DGAlgebra
public import TauCeti.RingTheory.CyclicCohomology.Cycle

/-!
# Cyclic cocycles are characters of universal-form cycles

Every cycle `(Ω, d, ∫, ρ)` over an algebra `A` has a character
`(a₀, …, aₙ) ↦ ∫ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`, which is a cyclic cocycle
(`TauCeti.cycleCocycle`). This file proves the converse: every cyclic cocycle is the character of
a cycle on the universal forms of `A`.

An `n`-cochain `φ` defines a functional `∫_φ` (`TauCeti.UniversalForms.trace`) on the
differential graded algebra `⨁ m, Ωᵐ` of universal forms. It vanishes outside degree `n`, and on
a word of degree `n` it reads

`∫_φ (x da₁ ⋯ daₙ) = φ(x₊, a₁, …, aₙ)`,

where `x₊ ∈ A` is the part of the coefficient `x ∈ A⁺` in `A`. In particular `∫_φ` vanishes on
words with scalar coefficient, hence on every exact form. Its character along the inclusion
`ι : A → Ω⁰` is `φ` itself, and `∫_φ` is a closed graded trace exactly when `φ` is a cyclic
cocycle (`TauCeti.UniversalForms.isClosedGradedTrace_trace_iff`).

Since `ι` does not preserve an existing unit of `A`, this realizes cocycles such as
`(a, b, c) ↦ abc` on `ℂ`, which are nonzero on `(1, 1, 1)`.

The graded trace property of `∫_φ` against the generators of `⨁ m, Ωᵐ` encodes the two conditions
on `φ`. Commutation with a zero-form `ι(a)` amounts to the cocycle identity `bφ = 0` on words with
coefficient in `A`, and to cyclicity of `φ` on words with scalar coefficient. The forms of
positive degree `q` are sums of products `ω dι(a)` with `ω` of degree `q - 1`, while the
zero-forms are the scalar multiples of `1` plus the images `ι(a)`.

## Main definitions

* `TauCeti.UniversalForms.trace`: the functional `∫_φ` on universal forms defined by a cochain.

## Main results

* `TauCeti.UniversalForms.cycleCharacter_trace`: the character of `∫_φ` is `φ`.
* `TauCeti.UniversalForms.isClosedGradedTrace_trace_iff`: `∫_φ` is a closed graded trace if and
  only if `φ` is a cyclic cocycle.
* `TauCeti.UniversalForms.cycleCocycle_trace`: every cyclic cocycle is the cyclic cocycle of the
  universal-form cycle it defines.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1, Proposition 4, p. 191.
* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §1,
  Proposition 1.
-/

public section

open scoped DirectSum

namespace TauCeti

namespace UniversalForms

noncomputable section

variable {k A M : Type*} [CommRing k] [NonUnitalRing A] [Module k A] [AddCommGroup M] [Module k M]
  {n : ℕ}

/-! ### The functional defined by a cochain -/

/-- The functional `∫_φ` on universal forms defined by an `n`-cochain `φ`: it vanishes outside
degree `n`, and sends the word `x da₁ ⋯ daₙ` to `φ(x₊, a₁, …, aₙ)`, where `x₊` is the part of the
coefficient `x ∈ A⁺` in `A`. -/
def trace (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M) :
    (⨁ m, UniversalForms k A m) →ₗ[k] M :=
  TensorProduct.lift (PiTensorProduct.lift.toLinearMap ∘ₗ φ.curryLeft ∘ₗ
    Unitization.sndHom k k A) ∘ₗ DirectSum.component k ℕ (UniversalForms k A) n

/-- On a word of degree `n`, the functional `∫_φ` evaluates `φ` on the part of the coefficient in
`A` followed by the letters. -/
@[simp]
theorem trace_of_word (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M) (x : Unitization k A)
    (a : Fin n → A) :
    trace φ (DirectSum.of _ n (word k A x a)) = φ (Fin.cons x.snd a) := by
  rw [trace, LinearMap.comp_apply, ← DirectSum.lof_eq_of k, DirectSum.component.lof_self,
    word_def, TensorProduct.lift.tmul]
  simp

/-- The functional `∫_φ` vanishes on forms of degree other than `n`. -/
@[simp]
theorem trace_of_of_ne (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M) {m : ℕ} (h : m ≠ n)
    (ω : UniversalForms k A m) : trace φ (DirectSum.of _ m ω) = 0 := by
  simp [trace, ← DirectSum.lof_eq_of k, DirectSum.component.of, h]

/-- The functional `∫_φ` vanishes on exact forms, since exact words have scalar coefficient. -/
@[simp]
theorem trace_differential (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M)
    (x : ⨁ m, UniversalForms k A m) : trace φ (differential k A x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of m ω =>
    rw [differential_of]
    by_cases h : m + 1 = n
    · subst h
      induction ω using induction_on k A with
      | hword x a =>
        rw [d_word, trace_of_word, Unitization.snd_one]
        exact φ.map_coord_zero 0 (Fin.cons_zero _ _)
      | hadd ω η hω hη => rw [map_add, map_add, map_add, hω, hη, add_zero]
    · exact trace_of_of_ne φ h _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

variable [IsScalarTower k A A] [SMulCommClass k A A]

/-- The form `ι(a₀) dι(a₁) ⋯ dι(aₙ)` of the universal-form cycle is the word `a₀ da₁ ⋯ daₙ`. -/
theorem cycleForm_ι (a : Fin (n + 1) → A) :
    cycleForm (differential k A) (ι k A) n a =
      DirectSum.of _ n (word k A (a 0 : Unitization k A) (Fin.tail a)) := by
  induction n with
  | zero =>
    rw [cycleForm_zero_apply, ι_apply]
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hlast : a (Fin.last (n + 1)) = Fin.tail a (Fin.last n) := by
      rw [Fin.tail, Fin.succ_last]
    rw [cycleForm_succ_apply, ih, ← of_snoc, snoc_word, Fin.tail_init_eq_init_tail, hlast,
      Fin.snoc_init_self, Fin.init, Fin.castSucc_zero]

/-- **The character of the universal-form cycle defined by `φ` is `φ`.** -/
@[simp]
theorem cycleCharacter_trace (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M) :
    cycleCharacter (R := k) (Ω := ⨁ m, UniversalForms k A m) (differential k A) (trace φ)
      (ι k A) n = φ := by
  ext a
  rw [cycleCharacter_apply, cycleForm_ι, trace_of_word, Unitization.snd_inr, Fin.cons_self_tail]

/-! ### The graded trace property -/

section Trace

variable {φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M}

/-- For a cyclic cocycle `φ`, the functional `∫_φ` commutes with the image of a letter. -/
private theorem trace_mul_ι (hφ : φ ∈ cyclicCochains k A M n)
    (hb : hochschildCoboundary k A M n φ = 0) (a : A) {x : ⨁ m, UniversalForms k A m}
    (hx : x ∈ grading k A n) : trace φ (x * ι k A a) = trace φ (ι k A a * x) := by
  obtain ⟨ω, rfl⟩ := mem_grading_natCast_iff.1 hx
  clear hx
  induction ω using induction_on k A with
  | hadd ω η hω hη => rw [map_add, add_mul, mul_add, map_add, map_add, hω, hη]
  | hword x b =>
    rw [word_eq_smul_one_add, map_add, DirectSum.of_smul, add_mul, mul_add, smul_mul_assoc,
      mul_smul_comm, map_add, map_add, map_smul, map_smul]
    refine congrArg₂ (· + ·) (congrArg (x.fst • ·) ?_) ?_
    · -- A word with scalar coefficient: this is cyclicity of `φ`.
      cases n with
      | zero =>
        obtain rfl : b = Fin.elim0 := Subsingleton.elim _ _
        rw [← one_def, _root_.mul_one, _root_.one_mul]
      | succ m =>
        have hY := of_mem_grading (word k A (b 0 : Unitization k A) (Fin.tail b))
        have hlb := congrArg (trace φ) ((isDGAlgebra k A).leibniz hY (ι k A a))
        rw [trace_differential, map_add, ← of_snoc, snoc_word, ← of_word_one_eq_differential,
          Units.smul_def, map_zsmul, trace_of_word, Unitization.snd_inr] at hlb
        have hR :
            trace φ (ι k A a * DirectSum.of _ (m + 1) (word k A 1 b)) = φ (Fin.cons a b) := by
          rw [ι_apply, of_word_mul_of_word, _root_.mul_one, trace_of_word, Unitization.snd_inr]
        rw [hR, eq_neg_of_add_eq_zero_left hlb.symm, Fin.cons_snoc_eq_snoc_cons,
          Fin.cons_self_tail]
        have hrot :
            (Fin.cons a b : Fin (m + 2) → A) = Fin.snoc b a ∘ (finRotate (m + 2)).symm := by
          funext i
          rw [Fin.snoc_eq_cons_rotate]
          simp
        rw [hrot, mem_cyclicCochains_iff.1 hφ, Int.coe_negOnePow_natCast, ← neg_smul, pow_succ,
          mul_neg_one]
    · -- A word with coefficient in `A`: this is the cocycle identity `bφ = 0`.
      have key := hochschildCoboundary_cycleCharacter_apply (isDGAlgebra k A) ι_mem_grading
        (τ := trace φ) (Fin.snoc (Fin.cons x.snd b) a)
      rw [cycleCharacter_trace, hb, zero_apply, Fin.init_snoc, Fin.snoc_last,
        cycleForm_ι, Fin.cons_zero, Fin.tail_cons] at key
      exact (sub_eq_zero.1 (((isUnit_neg_one (α := ℤ)).pow n).smul_eq_zero.1 key.symm))

/-- For a cyclic cocycle `φ` of degree `n`, the functional `∫_φ` moves a differential `dι(b)`
past a form of degree `p = n - 1` with the sign `(-1)ᵖ`. -/
private theorem trace_mul_differential_ι (hφ : φ ∈ cyclicCochains k A M n)
    (hb : hochschildCoboundary k A M n φ = 0) (b : A) {p : ℤ} {z : ⨁ m, UniversalForms k A m}
    (hz : z ∈ grading k A p) (hp : p + 1 = n) :
    trace φ (z * differential k A (ι k A b)) =
      p.negOnePow • trace φ (differential k A (ι k A b) * z) := by
  have hdz : differential k A z ∈ grading k A n := hp ▸ (isDGAlgebra k A).map_mem hz
  have h₁ := congrArg (trace φ) ((isDGAlgebra k A).leibniz hz (ι k A b))
  have h₂ := congrArg (trace φ) ((isDGAlgebra k A).leibniz (ι_mem_grading b) z)
  rw [trace_differential, map_add, Units.smul_def, map_zsmul] at h₁ h₂
  rw [Int.negOnePow_zero, Units.val_one, one_smul] at h₂
  have h₃ : p.negOnePow • trace φ (z * differential k A (ι k A b)) =
      trace φ (differential k A (ι k A b) * z) := by
    rw [Units.smul_def, eq_neg_of_add_eq_zero_right h₁.symm, trace_mul_ι hφ hb b hdz,
      eq_neg_of_add_eq_zero_right h₂.symm, neg_neg]
  rw [← h₃, smul_smul, Int.units_mul_self, one_smul]

/-- The graded trace property of `∫_φ` against a form of degree `m`, by induction on `m`. -/
private theorem trace_mul_comm_of_mem_natCast (hφ : φ ∈ cyclicCochains k A M n)
    (hb : hochschildCoboundary k A M n φ = 0) (m : ℕ) {y : ⨁ i, UniversalForms k A i}
    (hy : y ∈ grading k A m) {p : ℤ} {x : ⨁ i, UniversalForms k A i} (hx : x ∈ grading k A p)
    (hpm : p + m = n) : trace φ (x * y) = (p * m).negOnePow • trace φ (y * x) := by
  induction m generalizing p x y with
  | zero =>
    rw [Nat.cast_zero, add_zero] at hpm
    subst hpm
    obtain ⟨ω, rfl⟩ := mem_grading_natCast_iff.1 hy
    obtain ⟨ξ, rfl⟩ := mem_grading_natCast_iff.1 hx
    rw [Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul, of_zero_eq_smul_one_add_ι, mul_add,
      add_mul, map_add, map_add, mul_smul_comm, smul_mul_assoc, _root_.mul_one, _root_.one_mul,
      trace_mul_ι hφ hb _ (of_mem_grading ξ)]
  | succ m ih =>
    obtain ⟨ω, rfl⟩ := mem_grading_natCast_iff.1 hy
    clear hy
    induction ω using induction_snoc k A with
    | hadd ω η hω hη => rw [map_add, mul_add, add_mul, map_add, map_add, hω, hη, smul_add]
    | hsnoc η b =>
      have hdb : differential k A (ι k A b) ∈ grading k A 1 := by
        simpa using (isDGAlgebra k A).map_mem (ι_mem_grading b)
      rw [of_snoc, ← _root_.mul_assoc,
        trace_mul_differential_ι hφ hb b (SetLike.mul_mem_graded hx (of_mem_grading η))
          (by push_cast at hpm; omega),
        ← _root_.mul_assoc, ih (of_mem_grading η) (SetLike.mul_mem_graded hdb hx)
          (by push_cast at hpm; omega),
        _root_.mul_assoc, smul_smul, ← Int.negOnePow_add]
      congr 1
      rw [Int.negOnePow_eq_iff]
      exact ⟨m, by push_cast; ring⟩

end Trace

/-! ### Cyclic cocycles as characters -/

/-- **The functional `∫_φ` is a closed graded trace exactly when `φ` is a cyclic cocycle.** -/
theorem isClosedGradedTrace_trace_iff (φ : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M) :
    IsClosedGradedTrace (R := k) (Ω := ⨁ m, UniversalForms k A m) (grading k A)
        (differential k A) n (trace φ) ↔
      φ ∈ cyclicCochains k A M n ∧ hochschildCoboundary k A M n φ = 0 := by
  constructor
  · intro h
    have h₁ := cycleCharacter_mem_cyclicCochains (isDGAlgebra k A) ι_mem_grading h
    have h₂ := hochschildCoboundary_cycleCharacter (isDGAlgebra k A) ι_mem_grading h
    rw [cycleCharacter_trace] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · rintro ⟨hφ, hb⟩
    refine ⟨fun _ ↦ trace_differential φ _, fun {p q x y} hx hy hpq ↦ ?_⟩
    rcases lt_or_ge q 0 with hq | hq
    · rw [grading_of_neg hq, Submodule.mem_bot] at hy
      rw [hy, mul_zero, zero_mul, map_zero, smul_zero]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hq
      exact trace_mul_comm_of_mem_natCast hφ hb m hy hx hpq

/-- The functional `∫_φ` of a cyclic cocycle is a closed graded trace. -/
theorem isClosedGradedTrace_trace (φ : cyclicCocycles k A M n) :
    IsClosedGradedTrace (R := k) (Ω := ⨁ m, UniversalForms k A m) (grading k A)
      (differential k A) n
      (trace ((φ : cyclicCochains k A M n) : MultilinearMap k (fun _ : Fin (n + 1) ↦ A) M)) :=
  (isClosedGradedTrace_trace_iff _).2
    ⟨(φ : cyclicCochains k A M n).2, (mem_cyclicCocycles_iff k A M).1 φ.2⟩

/-- **Every cyclic cocycle is the character of a universal-form cycle**: the cyclic cocycle of the
cycle `(⨁ m, Ωᵐ, d, ∫_φ, ι)` is `φ`. -/
theorem cycleCocycle_trace (φ : cyclicCocycles k A M n) :
    cycleCocycle (isDGAlgebra k A) ι_mem_grading (isClosedGradedTrace_trace φ) = φ :=
  Subtype.ext <| Subtype.ext <| (coe_cycleCocycle _ _ _).trans (cycleCharacter_trace _)

end

end UniversalForms

end TauCeti
