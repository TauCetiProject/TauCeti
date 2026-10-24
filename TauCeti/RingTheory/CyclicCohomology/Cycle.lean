/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CyclicCohomology.Cohomology
public import TauCeti.RingTheory.CyclicCohomology.ConnesOperator
public import TauCeti.Algebra.Homology.DG.Algebra.Cohomology
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The character of a cycle

Connes' cycles are the geometric source of cyclic cocycles. A cycle of dimension `n` over an
algebra `A` consists of a differential graded algebra `(Ω, d)`, a closed graded trace
`∫ : Ωⁿ → M` and a homomorphism `ρ : A → Ω⁰`. Its character is the cochain

`τ(a₀, …, aₙ) = ∫ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`,

and this file proves that it is a cyclic cocycle: the graded trace property together with
closedness gives the cyclic symmetry `τ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ τ(a₀, …, aₙ)`, and the Leibniz
rule in degree zero together with the trace property gives `bτ = 0`.

The graded algebra `Ω` is unital, with its grading stored internally as for
`TauCeti.IsDGAlgebra`. The algebra `A` may be nonunital, and `ρ` is a homomorphism of nonunital
algebras: even when `A` has a unit, `ρ` need not preserve it. This is needed, for instance, to
realize the cyclic cocycle `(a, b, c) ↦ abc` on `ℂ`, which is nonzero on `(1, 1, 1)`, by universal
forms over the forced unitization.

The trace is a linear functional `∫ : Ω → M` on the whole algebra, of which only the restriction
to degree `n` is constrained: closedness asks `∫ dω = 0` for `ω` of degree `n - 1`, and the graded
trace property `∫ xy = (-1) ^ (pq) ∫ yx` is asked for `x` of degree `p` and `y` of degree `q` with
`p + q = n`. Composing a functional on `Ωⁿ` with the projection to degree `n` gives such a map.

The Ω-valued cochain `(a₀, …, aₙ) ↦ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` is `TauCeti.cycleForm`. Its bar
coboundary is `(-1)ⁿ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ) ρ(aₙ₊₁)`, which is the algebraic heart of the cocycle
identity.

## Main definitions

* `TauCeti.IsClosedGradedTrace`: a closed graded trace of dimension `n` on a graded algebra with
  a differential.
* `TauCeti.cycleForm`: the cochain `(a₀, …, aₙ) ↦ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` with values in `Ω`.
* `TauCeti.cycleCharacter`: the character `(a₀, …, aₙ) ↦ ∫ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` of a cycle.
* `TauCeti.cycleCocycle`: the character of a cycle, as a cyclic cocycle.

## Main results

* `TauCeti.barCoboundary_cycleForm`: the bar coboundary of `TauCeti.cycleForm`.
* `TauCeti.cycleCharacter_mem_cyclicCochains`: the character of a cycle is a cyclic cochain.
* `TauCeti.hochschildCoboundary_cycleCharacter`: the character of a cycle is a Hochschild
  cocycle.
* `TauCeti.cycleCharacter_comp`: the character of the cycle pulled back along a homomorphism is
  the pulled-back character.
* `TauCeti.cycleCocycle_comp`: the same naturality for the character as a cyclic cocycle.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1 (cycles and their characters).
* A. Connes, *Noncommutative differential geometry*, Publ. Math. IHÉS 62 (1985), Part II, §1.
-/

public section

namespace TauCeti

variable {R A Ω M : Type*} [CommRing R] [NonUnitalSemiring A] [Module R A] [Ring Ω] [Algebra R Ω]
  [AddCommGroup M] [Module R M]

/-! ### Closed graded traces -/

section Trace

variable (𝒜 : ℤ → Submodule R Ω) (d : Ω →ₗ[R] Ω)

/-- A **closed graded trace of dimension `n`** on the graded algebra `𝒜` with differential `d`:
a linear map `τ` which vanishes on the differentials of elements of degree `n - 1` and satisfies
`τ (x * y) = (-1) ^ (p q) τ (y * x)` for `x` of degree `p` and `y` of degree `q` with `p + q = n`.
Only the restriction of `τ` to degree `n` is constrained. -/
structure IsClosedGradedTrace (n : ℕ) (τ : Ω →ₗ[R] M) : Prop where
  /-- The trace vanishes on exact forms of top degree. -/
  map_map_eq_zero : ∀ {x : Ω}, x ∈ 𝒜 (n - 1) → τ (d x) = 0
  /-- The graded trace property in total degree `n`. -/
  map_mul_comm : ∀ {p q : ℤ} {x y : Ω}, x ∈ 𝒜 p → y ∈ 𝒜 q → p + q = n →
    τ (x * y) = (p * q).negOnePow • τ (y * x)

variable {𝒜 d}

/-- A closed graded trace commutes with a factor of degree zero. -/
theorem IsClosedGradedTrace.map_mul_comm_of_mem_zero {n : ℕ} {τ : Ω →ₗ[R] M}
    (hτ : IsClosedGradedTrace 𝒜 d n τ) {x y : Ω} (hx : x ∈ 𝒜 0) (hy : y ∈ 𝒜 n) :
    τ (x * y) = τ (y * x) := by
  simpa using hτ.map_mul_comm hx hy (zero_add _)

end Trace

/-! ### The forms `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` -/

section Form

variable (d : Ω →ₗ[R] Ω) (ρ : A →ₙₐ[R] Ω)

/-- The `Ω`-valued `n`-cochain `(a₀, …, aₙ) ↦ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` of a cycle. -/
def cycleForm (n : ℕ) : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) Ω :=
  (MultilinearMap.mkPiAlgebraFin R (n + 1) Ω).compLinearMap
    (Fin.cons (ρ : A →ₗ[R] Ω) fun _ ↦ d ∘ₗ (ρ : A →ₗ[R] Ω))

variable {d ρ} {n : ℕ}

/-- The defining formula `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`. -/
theorem cycleForm_apply (a : Fin (n + 1) → A) :
    cycleForm d ρ n a = ρ (a 0) * (List.ofFn fun i : Fin n ↦ d (ρ (a i.succ))).prod := by
  simp [cycleForm, MultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ]

/-- In degree zero the form is `ρ(a₀)`. -/
@[simp]
theorem cycleForm_zero_apply (a : Fin 1 → A) : cycleForm d ρ 0 a = ρ (a 0) := by
  simp [cycleForm_apply]

/-- The form of degree `n + 1` is that of degree `n` on the first arguments, multiplied on the
right by `dρ(aₙ₊₁)`. -/
theorem cycleForm_succ_apply (a : Fin (n + 2) → A) :
    cycleForm d ρ (n + 1) a = cycleForm d ρ n (Fin.init a) * d (ρ (a (Fin.last (n + 1)))) := by
  rw [cycleForm_apply, cycleForm_apply, List.ofFn_succ', List.prod_concat, mul_assoc]
  simp only [Fin.init, Fin.castSucc_zero, Fin.succ_castSucc, Fin.succ_last]

/-- Pulling the form back along a homomorphism `f` gives the form of `ρ ∘ f`. -/
theorem cycleForm_comp {B : Type*} [NonUnitalSemiring B] [Module R B] (f : B →ₙₐ[R] A) :
    cycleForm d (ρ.comp f) n = (cycleForm d ρ n).compLinearMap fun _ ↦ (f : B →ₗ[R] A) := by
  ext a
  simp [cycleForm_apply]

variable {𝒜 : ℤ → Submodule R Ω} [GradedAlgebra 𝒜]

/-- A product of differentials of elements of degree zero lies in the degree given by the number
of factors. -/
private theorem prod_ofFn_map_mem (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0) {k : ℕ}
    (b : Fin k → A) : (List.ofFn fun i ↦ d (ρ (b i))).prod ∈ 𝒜 k := by
  simpa using SetLike.list_prod_ofFn_mem_graded (fun _ ↦ (1 : ℤ)) _
    fun i ↦ by simpa using hd.map_mem (hρ (b i))

/-- The form `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` has degree `n`. -/
theorem cycleForm_mem (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0) (a : Fin (n + 1) → A) :
    cycleForm d ρ n a ∈ 𝒜 n := by
  rw [cycleForm_apply]
  simpa using SetLike.mul_mem_graded (hρ (a 0)) (prod_ofFn_map_mem hd hρ fun i : Fin n ↦ a i.succ)

/-- The differential of `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` is `dρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`. -/
theorem map_cycleForm (hd : IsDGAlgebra 𝒜 d) (a : Fin (n + 1) → A) :
    d (cycleForm d ρ n a) = (List.ofFn fun i ↦ d (ρ (a i))).prod := by
  have hcycle : d (List.ofFn fun i : Fin n ↦ d (ρ (a i.succ))).prod = 0 :=
    (hd.mem_cycles).1 <| list_prod_mem fun x hx ↦ by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact hd.map_mem_cycles _
  rw [cycleForm_apply, hd.toIsNonUnitalDGAlgebra.leibniz_of_map_eq_zero _ hcycle,
    List.ofFn_succ, List.prod_cons]

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The bar coboundary of `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)` telescopes to
`(-1)ⁿ ρ(a₀) dρ(a₁) ⋯ dρ(aₙ) ρ(aₙ₊₁)`. -/
theorem barCoboundary_cycleForm (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (a : Fin (n + 2) → A) :
    barCoboundary R A Ω n (cycleForm d ρ n) a =
      (-1 : ℤ) ^ n • (cycleForm d ρ n (Fin.init a) * ρ (a (Fin.last (n + 1)))) := by
  induction n with
  | zero =>
    simp [Fin.init, Fin.contractNth]
  | succ n ih =>
    rw [barCoboundary_apply, Fin.sum_univ_castSucc]
    simp only [cycleForm_succ_apply, Fin.init_contractNth_castSucc, Fin.contractNth_last,
      Fin.contractNth_castSucc_castSucc_apply_last, Fin.contractNth_castSucc_last_apply_last,
      Fin.val_castSucc, Fin.val_last, ← smul_mul_assoc, ← Finset.sum_mul]
    rw [← barCoboundary_apply, ih, map_mul,
      hd.toIsNonUnitalDGAlgebra.leibniz_of_mem_zero (hρ _)]
    simp only [pow_succ, mul_neg_one, neg_smul, neg_mul, smul_mul_assoc, mul_add, mul_assoc,
      Fin.init]
    abel

end Form

/-! ### The character of a cycle -/

section Character

variable (d : Ω →ₗ[R] Ω) (τ : Ω →ₗ[R] M) (ρ : A →ₙₐ[R] Ω)

/-- The **character** of a cycle: the `n`-cochain `(a₀, …, aₙ) ↦ τ (ρ(a₀) dρ(a₁) ⋯ dρ(aₙ))`. -/
def cycleCharacter (n : ℕ) : MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M :=
  τ.compMultilinearMap (cycleForm d ρ n)

variable {d τ ρ} {n : ℕ}

/-- The character evaluates the trace on the form `ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`. -/
@[simp]
theorem cycleCharacter_apply (a : Fin (n + 1) → A) :
    cycleCharacter d τ ρ n a = τ (cycleForm d ρ n a) :=
  (rfl)

/-- The character of the cycle pulled back along a homomorphism `f` is the pullback of the
character along `f`. -/
theorem cycleCharacter_comp {B : Type*} [NonUnitalSemiring B] [Module R B] (f : B →ₙₐ[R] A) :
    cycleCharacter d τ (ρ.comp f) n =
      (cycleCharacter d τ ρ n).compLinearMap fun _ ↦ (f : B →ₗ[R] A) := by
  ext a
  simp [cycleForm_comp]

variable {𝒜 : ℤ → Submodule R Ω} [GradedAlgebra 𝒜]

/-- The character of a cycle is a cyclic cochain:
`τ(aₙ, a₀, …, aₙ₋₁) = (-1)ⁿ τ(a₀, …, aₙ)`. -/
theorem cycleCharacter_mem_cyclicCochains (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (hτ : IsClosedGradedTrace 𝒜 d n τ) : cycleCharacter d τ ρ n ∈ cyclicCochains R A M n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mem_cyclicCochains_iff]
    intro a
    -- Write `X = ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`, so that the character is `τ (X dρ(aₙ₊₁))`.
    set X := cycleForm d ρ n (Fin.init a) with hX
    have hXmem : X ∈ 𝒜 n := cycleForm_mem hd hρ _
    have hlast : ρ (a (Fin.last (n + 1))) ∈ 𝒜 0 := hρ _
    -- The rotated form is `ρ(aₙ₊₁) dX`.
    have h0 : (finRotate (n + 2)).symm 0 = Fin.last (n + 1) :=
      (Equiv.symm_apply_eq _).2 finRotate_last.symm
    have hs (i : Fin (n + 1)) : (finRotate (n + 2)).symm i.succ = i.castSucc :=
      (Equiv.symm_apply_eq _).2 <| Fin.ext <| by
        rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last i)]
        simp
    have hrot : cycleForm d ρ (n + 1) (a ∘ (finRotate (n + 2)).symm) =
        ρ (a (Fin.last (n + 1))) * d X := by
      rw [hX, map_cycleForm hd, cycleForm_apply]
      simp only [Function.comp_apply, h0, hs, Fin.init]
    -- Closedness applied to `X ρ(aₙ₊₁)`, of degree `n`, moves the differential onto `X`.
    have hclosed := hτ.map_map_eq_zero (x := X * ρ (a (Fin.last (n + 1))))
      (by simpa using SetLike.mul_mem_graded hXmem hlast)
    rw [hd.leibniz hXmem, map_add, map_zsmul_unit] at hclosed
    -- The trace property moves `ρ(aₙ₊₁)` to the front.
    have htrace : τ (d X * ρ (a (Fin.last (n + 1)))) = τ (ρ (a (Fin.last (n + 1))) * d X) :=
      (hτ.map_mul_comm_of_mem_zero hlast (by simpa using hd.map_mem hXmem)).symm
    rw [cycleCharacter_apply, cycleCharacter_apply, hrot, cycleForm_succ_apply, ← hX, ← htrace,
      eq_neg_of_add_eq_zero_left hclosed]
    simp [pow_succ, Units.smul_def, Int.coe_negOnePow_natCast]

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- The character of a cycle is a Hochschild cocycle. -/
theorem hochschildCoboundary_cycleCharacter (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (hτ : IsClosedGradedTrace 𝒜 d n τ) :
    hochschildCoboundary R A M n (cycleCharacter d τ ρ n) = 0 := by
  ext a
  have hbar : barCoboundary R A M n (cycleCharacter d τ ρ n) a =
      τ (barCoboundary R A Ω n (cycleForm d ρ n) a) := by
    simp only [barCoboundary_apply, cycleCharacter_apply, map_sum, map_zsmul]
  -- The last face `(aₙ₊₁a₀, a₁, …, aₙ)` gives the form `ρ(aₙ₊₁) ρ(a₀) dρ(a₁) ⋯ dρ(aₙ)`.
  have hlast : cycleForm d ρ n (hochschildFace (Fin.last (n + 1)) a) =
      ρ (a (Fin.last (n + 1))) * cycleForm d ρ n (Fin.init a) := by
    simp only [hochschildFace_last, cycleForm_apply, Fin.cons_zero, Fin.cons_succ, map_mul,
      mul_assoc, Fin.init, Fin.succ_castSucc, Fin.castSucc_zero]
  rw [hochschildCoboundary_eq_barCoboundary_add, add_apply, smul_apply, hochschildCoface_apply,
    hbar, barCoboundary_cycleForm hd hρ, cycleCharacter_apply, hlast,
    hτ.map_mul_comm_of_mem_zero (hρ _) (cycleForm_mem hd hρ _), map_zsmul]
  simp [pow_succ]

/-- The character of a cycle, as a cyclic cocycle. -/
def cycleCocycle (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (hτ : IsClosedGradedTrace 𝒜 d n τ) : cyclicCocycles R A M n :=
  ⟨⟨cycleCharacter d τ ρ n, cycleCharacter_mem_cyclicCochains hd hρ hτ⟩,
    (mem_cyclicCocycles_iff R A M).2 (hochschildCoboundary_cycleCharacter hd hρ hτ)⟩

/-- The underlying cochain of the cyclic cocycle of a cycle is its character. -/
@[simp]
theorem coe_cycleCocycle (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (hτ : IsClosedGradedTrace 𝒜 d n τ) :
    ((cycleCocycle hd hρ hτ : cyclicCochains R A M n) :
      MultilinearMap R (fun _ : Fin (n + 1) ↦ A) M) = cycleCharacter d τ ρ n :=
  (rfl)

/-- The cyclic cocycle of the cycle pulled back along a homomorphism `f` is the pullback of the
cyclic cocycle along `f`. -/
theorem cycleCocycle_comp {B : Type*} [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : B →ₙₐ[R] A) (hd : IsDGAlgebra 𝒜 d) (hρ : ∀ a, ρ a ∈ 𝒜 0)
    (hτ : IsClosedGradedTrace 𝒜 d n τ) :
    (cycleCocycle (ρ := ρ.comp f) hd (fun b ↦ hρ (f b)) hτ : cyclicCochains R B M n) =
      cyclicCochainsMap M (f : B →ₗ[R] A) n (cycleCocycle hd hρ hτ) :=
  Subtype.ext <| by rw [coe_cyclicCochainsMap_apply]; exact cycleCharacter_comp f

end Character

end TauCeti
