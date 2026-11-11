/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Snake
import TauCeti.GroupTheory.Index.Exact
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearMap.Cardinality

/-!
# Orders of the kernel and cokernel of multiplication by a scalar

Let `r` be an element of a commutative ring `R`. For an `R`-module `M` write `M[r]` for the
`r`-torsion `Submodule.torsionBy R M r` and `M ⧸ rM` for `QuotSMulTop r M`, the kernel and the
cokernel of multiplication by `r`. When both are finite, the *Euler quotient*

`χ_r(M) = #(M ⧸ rM) / #M[r]`

is the Herbrand quotient of the pair of commuting endomorphisms `(0, r)` of `M`. This file proves
its three basic properties:

* it is `1` on a finite module: `#(M ⧸ rM) = #M[r]` when `M` is finite;
* it is multiplicative along a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, by counting along the
  six-term kernel–cokernel sequence `TauCeti.torsionByδ` of the snake lemma;
* hence it is unchanged by a linear map with finite kernel and cokernel, which factors through its
  image as a surjection with finite kernel followed by an injection with finite cokernel.

The counting statements are stated for `Nat.card` with no finiteness hypothesis beyond the one
that makes them true, so an infinite kernel or cokernel contributes the factor `0`; the rational
forms divide them out. A map with finite kernel and cokernel moreover preserves the finiteness of
the kernel and of the cokernel of multiplication by `r`.

Over the Iwasawa algebra `Λ = O⟦T⟧` the maps with finite kernel and cokernel are the
pseudo-isomorphisms, and `r` is typically `ω_n = (1 + T) ^ pⁿ - 1`, for which `M ⧸ ω_n M` and
`M[ω_n]` are the coinvariants and the invariants of the subgroup of index `pⁿ` of `Γ ≅ ℤ_p`. The
invariance is what lets the Euler quotient `#(M ⧸ ω_n M) / #M[ω_n]` be computed on an elementary
module, and the finiteness of `M ⧸ ω_n M` and of `M[ω_n]` be read off there; the individual orders
need not agree.

## Main results

* `TauCeti.natCard_quotSMulTop_eq_natCard_torsionBy`: `#(M ⧸ rM) = #M[r]` for finite `M`.
* `TauCeti.natCard_torsionBy_mul_natCard_quotSMulTop_of_exact`: the count along the six-term
  sequence of a short exact sequence, `#M₁[r] #M₃[r] #(M₂ ⧸ rM₂) = #M₂[r] #(M₁ ⧸ rM₁) #(M₃ ⧸ rM₃)`.
* `TauCeti.natCard_quotSMulTop_div_natCard_torsionBy_of_exact`: multiplicativity of the Euler
  quotient, when the outer torsion groups are finite.
* `TauCeti.natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_left` and
  `TauCeti.natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_right`: a finite outer
  term of a short exact sequence may be discarded.
* `TauCeti.finite_torsionBy_iff_of_finite_ker_of_finite_coker`,
  `TauCeti.finite_quotSMulTop_iff_of_finite_ker_of_finite_coker` and
  `TauCeti.natCard_quotSMulTop_div_natCard_torsionBy_eq_of_finite_ker_of_finite_coker`: a linear
  map with finite kernel and cokernel preserves the finiteness of `M[r]` and of `M ⧸ rM`, and the
  Euler quotient.

## References

* J.-P. Serre, *Local Fields*, Chapter VIII, §4, for the Herbrand quotient and its
  multiplicativity and invariance.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Chapter V, §3, (5.3.11)–(5.3.16), for the invariants and coinvariants of Iwasawa modules.
-/

public section

open Function Submodule

open scoped Pointwise

namespace TauCeti

variable {R : Type*} [CommRing R] (r : R)

section Finite

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- **The Euler quotient of a finite module is `1`**: for a finite module `M`, the cokernel and the
kernel of multiplication by `r` have the same order, `#(M ⧸ rM) = #M[r]`. -/
theorem natCard_quotSMulTop_eq_natCard_torsionBy [Finite M] :
    Nat.card (QuotSMulTop r M) = Nat.card (torsionBy R M r) := by
  -- count `M` once along `rM ⊆ M` and once along the map `x ↦ r • x`, whose range is `rM`
  have hrange : LinearMap.range (DistribSMul.toLinearMap R M r) = r • ⊤ := by
    rw [pointwise_smul_def, Submodule.map_top]
  have hker : LinearMap.ker (DistribSMul.toLinearMap R M r) = torsionBy R M r := by
    rw [(exact_subtype_torsionBy r M).linearMap_ker_eq, range_subtype]
  have h := LinearMap.card_eq_card_range_mul_card_ker (DistribSMul.toLinearMap R M r)
  rw [hrange, hker, card_eq_card_quotient_mul_card (r • ⊤ : Submodule R M)] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(r • ⊤ : Submodule R M))) h

end Finite

section Exact

variable {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup M₃] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

/-- **The count along the kernel–cokernel sequence.** For a short exact sequence
`0 → M₁ → M₂ → M₃ → 0`, the six-term sequence
`0 → M₁[r] → M₂[r] → M₃[r] → M₁ ⧸ rM₁ → M₂ ⧸ rM₂ → M₃ ⧸ rM₃ → 0` gives
`#M₁[r] #M₃[r] #(M₂ ⧸ rM₂) = #M₂[r] #(M₁ ⧸ rM₁) #(M₃ ⧸ rM₃)`. No finiteness is assumed: an infinite
group contributes the factor `0` to both sides. -/
theorem natCard_torsionBy_mul_natCard_quotSMulTop_of_exact (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) :
    Nat.card (torsionBy R M₁ r) * Nat.card (torsionBy R M₃ r) * Nat.card (QuotSMulTop r M₂) =
      Nat.card (torsionBy R M₂ r) * Nat.card (QuotSMulTop r M₁) * Nat.card (QuotSMulTop r M₃) :=
  AddMonoidHom.card_mul_card_mul_card_of_exact (torsionByMap r f).toAddMonoidHom
    (torsionByMap r g).toAddMonoidHom (torsionByδ r hfg hf hg).toAddMonoidHom
    (QuotSMulTop.map r f).toAddMonoidHom (QuotSMulTop.map r g).toAddMonoidHom
    (injective_torsionByMap hf) (exact_torsionByMap hfg hf).addMonoidHom_ker_eq.symm
    (exact_torsionByMap_torsionByδ hfg hf hg).addMonoidHom_ker_eq.symm
    (exact_torsionByδ_quotSMulTop_map hfg hf hg).addMonoidHom_ker_eq.symm
    (QuotSMulTop.map_exact r hfg hg).addMonoidHom_ker_eq.symm (QuotSMulTop.map_surjective r hg)

/-- **Multiplicativity of the Euler quotient** along a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` whose outer terms have finite `r`-torsion:
`χ_r(M₂) = χ_r(M₁) χ_r(M₃)`. The cokernels are unconstrained: if one of them is infinite, both
sides are `0`. -/
theorem natCard_quotSMulTop_div_natCard_torsionBy_of_exact (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) [Finite (torsionBy R M₁ r)] [Finite (torsionBy R M₃ r)] :
    (Nat.card (QuotSMulTop r M₂) : ℚ) / Nat.card (torsionBy R M₂ r) =
      Nat.card (QuotSMulTop r M₁) / Nat.card (torsionBy R M₁ r) *
        (Nat.card (QuotSMulTop r M₃) / Nat.card (torsionBy R M₃ r)) := by
  have : Finite (torsionBy R M₂ r) := (exact_torsionByMap (r := r) hfg hf).finite
  have h := natCard_torsionBy_mul_natCard_quotSMulTop_of_exact r hfg hf hg
  have h₁ : (Nat.card (torsionBy R M₁ r) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h₂ : (Nat.card (torsionBy R M₂ r) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h₃ : (Nat.card (torsionBy R M₃ r) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [div_mul_div_comm, div_eq_div_iff h₂ (mul_ne_zero h₁ h₃)]
  exact_mod_cast by linarith

/-- If `M₁` is finite in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, then `M₂[r]` is finite iff
`M₃[r]` is. -/
theorem finite_torsionBy_iff_of_exact_of_finite_left [Finite M₁] (hfg : Exact f g)
    (hf : Injective f) (hg : Surjective g) :
    Finite (torsionBy R M₂ r) ↔ Finite (torsionBy R M₃ r) := by
  have : Finite (QuotSMulTop r M₁) := Finite.of_surjective _ (mkQ_surjective _)
  exact ⟨fun _ ↦ (exact_torsionByMap_torsionByδ (r := r) hfg hf hg).finite,
    fun _ ↦ (exact_torsionByMap (r := r) hfg hf).finite⟩

/-- If `M₁` is finite in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, then `M₂ ⧸ rM₂` is finite
iff `M₃ ⧸ rM₃` is. -/
theorem finite_quotSMulTop_iff_of_exact_of_finite_left [Finite M₁] (hfg : Exact f g)
    (hg : Surjective g) :
    Finite (QuotSMulTop r M₂) ↔ Finite (QuotSMulTop r M₃) := by
  have : Finite (QuotSMulTop r M₁) := Finite.of_surjective _ (mkQ_surjective _)
  exact ⟨fun _ ↦ Finite.of_surjective _ (QuotSMulTop.map_surjective r hg),
    fun _ ↦ (QuotSMulTop.map_exact r hfg hg).finite⟩

/-- If `M₃` is finite in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, then `M₁[r]` is finite iff
`M₂[r]` is. -/
theorem finite_torsionBy_iff_of_exact_of_finite_right [Finite M₃] (hfg : Exact f g)
    (hf : Injective f) :
    Finite (torsionBy R M₁ r) ↔ Finite (torsionBy R M₂ r) :=
  ⟨fun _ ↦ (exact_torsionByMap (r := r) hfg hf).finite,
    fun _ ↦ Finite.of_injective _ (injective_torsionByMap (r := r) hf)⟩

/-- If `M₃` is finite in a short exact sequence `0 → M₁ → M₂ → M₃ → 0`, then `M₁ ⧸ rM₁` is finite
iff `M₂ ⧸ rM₂` is. -/
theorem finite_quotSMulTop_iff_of_exact_of_finite_right [Finite M₃] (hfg : Exact f g)
    (hf : Injective f) (hg : Surjective g) :
    Finite (QuotSMulTop r M₁) ↔ Finite (QuotSMulTop r M₂) := by
  have : Finite (QuotSMulTop r M₃) := Finite.of_surjective _ (mkQ_surjective _)
  exact ⟨fun _ ↦ (QuotSMulTop.map_exact r hfg hg).finite,
    fun _ ↦ (exact_torsionByδ_quotSMulTop_map (r := r) hfg hf hg).finite⟩

/-- **A finite first term may be discarded**: if `M₁` is finite in a short exact sequence
`0 → M₁ → M₂ → M₃ → 0`, then `#(M₂ ⧸ rM₂) #M₃[r] = #(M₃ ⧸ rM₃) #M₂[r]`, that is
`χ_r(M₂) = χ_r(M₃)` once the torsion groups are finite. -/
theorem natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_left [Finite M₁]
    (hfg : Exact f g) (hf : Injective f) (hg : Surjective g) :
    Nat.card (QuotSMulTop r M₂) * Nat.card (torsionBy R M₃ r) =
      Nat.card (QuotSMulTop r M₃) * Nat.card (torsionBy R M₂ r) := by
  have : Finite (QuotSMulTop r M₁) := Finite.of_surjective _ (mkQ_surjective _)
  have h := natCard_torsionBy_mul_natCard_quotSMulTop_of_exact r hfg hf hg
  rw [← natCard_quotSMulTop_eq_natCard_torsionBy r (M := M₁)] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := QuotSMulTop r M₁)) (by linarith)

/-- **A finite last term may be discarded**: if `M₃` is finite in a short exact sequence
`0 → M₁ → M₂ → M₃ → 0`, then `#(M₁ ⧸ rM₁) #M₂[r] = #(M₂ ⧸ rM₂) #M₁[r]`, that is
`χ_r(M₁) = χ_r(M₂)` once the torsion groups are finite. -/
theorem natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_right [Finite M₃]
    (hfg : Exact f g) (hf : Injective f) (hg : Surjective g) :
    Nat.card (QuotSMulTop r M₁) * Nat.card (torsionBy R M₂ r) =
      Nat.card (QuotSMulTop r M₂) * Nat.card (torsionBy R M₁ r) := by
  have : Finite (QuotSMulTop r M₃) := Finite.of_surjective _ (mkQ_surjective _)
  have h := natCard_torsionBy_mul_natCard_quotSMulTop_of_exact r hfg hf hg
  rw [← natCard_quotSMulTop_eq_natCard_torsionBy r (M := M₃)] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := QuotSMulTop r M₃)) (by linarith)

end Exact

section FiniteKerCoker

variable {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (φ : M →ₗ[R] N)

variable [Finite (LinearMap.ker φ)] [Finite (N ⧸ LinearMap.range φ)]
include φ

/-- A linear map with finite kernel and cokernel preserves the finiteness of the `r`-torsion:
`M[r]` is finite iff `N[r]` is. -/
theorem finite_torsionBy_iff_of_finite_ker_of_finite_coker :
    Finite (torsionBy R M r) ↔ Finite (torsionBy R N r) :=
  (finite_torsionBy_iff_of_exact_of_finite_left r φ.exact_subtype_rangeRestrict
    (LinearMap.ker φ).injective_subtype φ.surjective_rangeRestrict).trans
    (finite_torsionBy_iff_of_exact_of_finite_right r
      (LinearMap.exact_subtype_mkQ (LinearMap.range φ)) (LinearMap.range φ).injective_subtype)

/-- A linear map with finite kernel and cokernel preserves the finiteness of the cokernel of
multiplication by `r`: `M ⧸ rM` is finite iff `N ⧸ rN` is. -/
theorem finite_quotSMulTop_iff_of_finite_ker_of_finite_coker :
    Finite (QuotSMulTop r M) ↔ Finite (QuotSMulTop r N) :=
  (finite_quotSMulTop_iff_of_exact_of_finite_left r φ.exact_subtype_rangeRestrict
    φ.surjective_rangeRestrict).trans
    (finite_quotSMulTop_iff_of_exact_of_finite_right r
      (LinearMap.exact_subtype_mkQ (LinearMap.range φ)) (LinearMap.range φ).injective_subtype
      (LinearMap.range φ).mkQ_surjective)

/-- **Invariance of the Euler quotient, counted.** For a linear map `φ : M → N` with finite kernel
and cokernel, `#(M ⧸ rM) #N[r] = #(N ⧸ rN) #M[r]`. No finiteness of the torsion groups is
assumed: `M[r]` and `N[r]` are finite or infinite together, and in the infinite case both sides
are `0`. -/
theorem natCard_quotSMulTop_mul_natCard_torsionBy_of_finite_ker_of_finite_coker :
    Nat.card (QuotSMulTop r M) * Nat.card (torsionBy R N r) =
      Nat.card (QuotSMulTop r N) * Nat.card (torsionBy R M r) := by
  -- factor `φ` as `M ↠ range φ ↪ N`
  have h₁ := natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_left r
    φ.exact_subtype_rangeRestrict (LinearMap.ker φ).injective_subtype φ.surjective_rangeRestrict
  have h₂ := natCard_quotSMulTop_mul_natCard_torsionBy_of_exact_of_finite_right r
    (LinearMap.exact_subtype_mkQ (LinearMap.range φ)) (LinearMap.range φ).injective_subtype
    (LinearMap.range φ).mkQ_surjective
  by_cases hP : Finite (torsionBy R (LinearMap.range φ) r)
  · refine Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := torsionBy R (LinearMap.range φ) r)) ?_
    calc _ = Nat.card (QuotSMulTop r M) * Nat.card (torsionBy R (LinearMap.range φ) r) *
            Nat.card (torsionBy R N r) := by ring
      _ = Nat.card (torsionBy R M r) *
            (Nat.card (QuotSMulTop r (LinearMap.range φ)) * Nat.card (torsionBy R N r)) := by
          rw [h₁]; ring
      _ = _ := by rw [h₂]; ring
  · -- the `r`-torsion of `M`, of `range φ` and of `N` is infinite
    have hM : ¬ Finite (torsionBy R M r) := fun h ↦ hP <|
      (finite_torsionBy_iff_of_exact_of_finite_left r φ.exact_subtype_rangeRestrict
        (LinearMap.ker φ).injective_subtype φ.surjective_rangeRestrict).1 h
    have hN : ¬ Finite (torsionBy R N r) := (finite_torsionBy_iff_of_finite_ker_of_finite_coker r
      φ).not.1 hM
    rw [not_finite_iff_infinite] at hM hN
    rw [Nat.card_eq_zero_of_infinite (α := torsionBy R M r),
      Nat.card_eq_zero_of_infinite (α := torsionBy R N r), mul_zero, mul_zero]

/-- **Invariance of the Euler quotient**: a linear map `φ : M → N` with finite kernel and cokernel
satisfies `χ_r(M) = χ_r(N)`, that is `#(M ⧸ rM) / #M[r] = #(N ⧸ rN) / #N[r]`. No finiteness is
assumed: when the torsion groups are infinite, both sides are `0`. -/
theorem natCard_quotSMulTop_div_natCard_torsionBy_eq_of_finite_ker_of_finite_coker :
    (Nat.card (QuotSMulTop r M) : ℚ) / Nat.card (torsionBy R M r) =
      Nat.card (QuotSMulTop r N) / Nat.card (torsionBy R N r) := by
  by_cases hM : Finite (torsionBy R M r)
  · have : Finite (torsionBy R N r) :=
      (finite_torsionBy_iff_of_finite_ker_of_finite_coker r φ).1 hM
    rw [div_eq_div_iff (Nat.cast_ne_zero.2 Nat.card_pos.ne') (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
    exact_mod_cast natCard_quotSMulTop_mul_natCard_torsionBy_of_finite_ker_of_finite_coker r φ
  · have hN : ¬ Finite (torsionBy R N r) :=
      (finite_torsionBy_iff_of_finite_ker_of_finite_coker r φ).not.1 hM
    rw [not_finite_iff_infinite] at hM hN
    rw [Nat.card_eq_zero_of_infinite (α := torsionBy R M r),
      Nat.card_eq_zero_of_infinite (α := torsionBy R N r), Nat.cast_zero, div_zero, div_zero]

end FiniteKerCoker

end TauCeti
