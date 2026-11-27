/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import TauCeti.Combinatorics.Brauer.Congr

/-!
# Skew-symmetric arc products of Brauer diagrams

When a Brauer diagram acts on the tensor power of a module carrying a symmetric bilinear form, an
arc carries no sign: the matrix entry of a diagram `D` at a boundary labelling is `1` when the
labelling is constant on the arcs of `D` and `0` otherwise
(`TauCeti/Combinatorics/Brauer/Labelling.lean`). For an alternating form, exchanging the two
endpoints of an arc negates its weight, and reordering two endpoints introduces a permutation sign;
the two sign changes cancel, so a diagram still has a canonical signed product over its arcs. This
file builds that signed product, the combinatorial counterpart of a Pfaffian term, for any
skew-symmetric matrix `W` on the `2 * k` boundary points `Fin k ⊕ Fin k`.

## Arc framings

Every Brauer diagram `D` on `k` strands is obtained from the identity diagram `permToBrauer 1` by
some permutation `π` of the boundary points `Fin k ⊕ Fin k`: `π` sends the `r`-th identity strand
`(Sum.inl r, Sum.inr r)` to an oriented arc `(π (Sum.inl r), π (Sum.inr r))` of `D`. Such a
permutation is an **arc framing** of `D` (`TauCeti.BrauerDiagram.IsFraming`, defined together with
the chosen framing `TauCeti.BrauerDiagram.framing` in `TauCeti/Combinatorics/Brauer/Congr.lean`).
Two framings of the same diagram differ on the right by an element of the centralizer of
`Sum.swap`, the hyperoctahedral group permuting the `k` pairs and reversing individual pairs:

* permuting the `k` pairs by `Equiv.Perm.sumCongr σ σ` has sign `(sign σ)² = 1` and reindexes the
  product over the `k` arcs;
* reversing one pair by `Equiv.swap (Sum.inl r) (Sum.inr r)` has sign `-1` and replaces
  `W x y` by `W y x = -W x y`.

Hence for any skew-symmetric matrix `W` (`∀ x y, W y x = -W x y`), the quantity
`sign π * ∏ r, W (π (Sum.inl r)) (π (Sum.inr r))` depends only on `D`, not on the framing `π`
(`TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`).

## Main definitions

* `TauCeti.BrauerDiagram.skewArcProd`: the signed product of the entries of a skew-symmetric
  boundary matrix `W` over the arcs of `D`.

## Main results

* `TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`: **framing independence** of the signed arc
  product for skew-symmetric `W`.
* `TauCeti.BrauerDiagram.skewArcProd_permToBrauer`, `TauCeti.BrauerDiagram.skewArcProd_capCup`,
  `TauCeti.BrauerDiagram.skewArcProd_congr` and `TauCeti.BrauerDiagram.skewArcProd_relabel`: values
  of the signed arc product on permutation diagrams, cap-cup diagrams and transported diagrams.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

variable {k : ℕ}

namespace BrauerDiagram

/-! ### Skew-symmetric arc products and framing independence -/

section SkewArcProd

variable {R : Type*} [CommRing R]

/-- The raw signed product of `W` along a boundary permutation `π`. -/
private def rawArcProd (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
    (π : Equiv.Perm (Fin k ⊕ Fin k)) : R :=
  ((Equiv.Perm.sign π : ℤ) : R) * ∏ r : Fin k, W (π (Sum.inl r)) (π (Sum.inr r))

/-- Permuting the `k` arcs simultaneously on the right by `Equiv.Perm.sumCongr σ σ` preserves
`rawArcProd`. -/
private theorem rawArcProd_mul_sumCongr (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
    (φ : Equiv.Perm (Fin k ⊕ Fin k)) (σ : Equiv.Perm (Fin k)) :
    rawArcProd W (φ * Equiv.Perm.sumCongr σ σ) = rawArcProd W φ := by
  rw [rawArcProd, rawArcProd, map_mul, Equiv.Perm.sign_sumCongr, Int.units_mul_self, mul_one]
  exact congrArg _ (Equiv.prod_comp σ fun r => W (φ (Sum.inl r)) (φ (Sum.inr r)))

/-- Reversing a subset of arcs via `Equiv.prodCongrLeft τ` preserves `rawArcProd` when `W` is
skew-symmetric: on each arc `r`, the sign of `τ r : Equiv.Perm Bool` cancels any endpoint swap. -/
private theorem rawArcProd_mul_prodCongrLeft {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R}
    (hW : ∀ x y, W y x = -W x y) (φ : Equiv.Perm (Fin k ⊕ Fin k))
    (τ : Fin k → Equiv.Perm Bool) :
    rawArcProd W
        (φ * (Equiv.boolProdEquivSum (Fin k)).permCongr (Equiv.prodCongrLeft τ)) =
      rawArcProd W φ := by
  let χ := (Equiv.boolProdEquivSum (Fin k)).permCongr (Equiv.prodCongrLeft τ)
  have hsign : ((Equiv.Perm.sign χ : ℤ) : R) = ∏ r : Fin k, ((Equiv.Perm.sign (τ r) : ℤ) : R) := by
    simp [χ, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_prodCongrLeft]
  rw [rawArcProd, rawArcProd, map_mul, Units.val_mul, Int.cast_mul, mul_assoc, hsign,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun r _ => ?_)
  rcases (by decide : ∀ e : Equiv.Perm Bool, e = 1 ∨ e = Equiv.swap false true) (τ r) with
    hτ | hτ
  · simp [Equiv.Perm.mul_apply, hτ, Equiv.boolProdEquivSum]
  · simp [Equiv.Perm.mul_apply, hτ, Equiv.boolProdEquivSum,
      Equiv.Perm.sign_swap (by decide : false ≠ true), hW (φ (Sum.inl r)) (φ (Sum.inr r))]

/-- **The signed arc product of a Brauer diagram** for a boundary matrix `W`: the product of `W`
over the oriented arcs of `D.framing`, multiplied by `sign D.framing`. When `W` is skew-symmetric,
this is independent of the framing (`TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`). -/
noncomputable def skewArcProd (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) : R :=
  rawArcProd W D.framing

/-- Defining formula of `TauCeti.BrauerDiagram.skewArcProd` in terms of `D.framing`. -/
theorem skewArcProd_def (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) :
    D.skewArcProd W = ((Equiv.Perm.sign D.framing : ℤ) : R) *
      ∏ r : Fin k, W (D.framing (Sum.inl r)) (D.framing (Sum.inr r)) := (rfl)

/-- Applying a ring homomorphism commutes with `TauCeti.BrauerDiagram.skewArcProd`. -/
theorem map_skewArcProd {S : Type*} [CommRing S] (f : R →+* S) (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) :
    f (D.skewArcProd W) = D.skewArcProd (W.map f) := by
  simp [skewArcProd_def]

/-- **Framing independence of the signed arc product**: for a skew-symmetric matrix `W`,
`D.skewArcProd W` can be computed using *any* framing `π` of `D`. -/
theorem skewArcProd_eq_of_isFraming (D : BrauerDiagram k)
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y)
    {π : Equiv.Perm (Fin k ⊕ Fin k)} (hπ : D.IsFraming π) :
    D.skewArcProd W =
      ((Equiv.Perm.sign π : ℤ) : R) * ∏ r : Fin k, W (π (Sum.inl r)) (π (Sum.inr r)) := by
  obtain ⟨σ, τ, hdecomp⟩ := exists_mul_sumCongr_mul_of_congr_permToBrauer_one_eq
    (((D.isFraming_def π).mp hπ).trans ((D.isFraming_def D.framing).mp D.isFraming_framing).symm)
  rw [skewArcProd, hdecomp, rawArcProd_mul_prodCongrLeft hW, rawArcProd_mul_sumCongr]
  rfl

/-- **The signed arc product of a permutation diagram**: `sign σ` times the product of the through
weights `W (Sum.inl r) (Sum.inr (σ r))`. -/
theorem skewArcProd_permToBrauer (σ : Equiv.Perm (Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (permToBrauer σ).skewArcProd W =
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ r : Fin k, W (Sum.inl r) (Sum.inr (σ r)) := by
  rw [skewArcProd_eq_of_isFraming _ hW (isFraming_permToBrauer σ), Equiv.Perm.sign_sumCongr,
    map_one, one_mul]
  rfl

/-- **The signed arc product of a cap-cup diagram** at `a ≠ b`: minus the cap weight
`W (Sum.inl a) (Sum.inl b)` times the cup weight `W (Sum.inr a) (Sum.inr b)` times the through
weights off `{a, b}`. -/
theorem skewArcProd_capCup {a b : Fin k} (hab : a ≠ b)
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (capCup a b).skewArcProd W =
      -(W (Sum.inl a) (Sum.inl b) * W (Sum.inr a) (Sum.inr b) *
        ∏ r ∈ (Finset.univ.erase a).erase b, W (Sum.inl r) (Sum.inr r)) := by
  rw [skewArcProd_eq_of_isFraming _ hW (((capCup a b).isFraming_def _).mpr (capCup_def a b).symm),
    Equiv.Perm.sign_swap Sum.inr_ne_inl, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_mul]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) _ (Finset.mem_erase.mpr ⟨hab.symm,
      Finset.mem_univ b⟩), ← mul_assoc]
  congr 1
  · simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hab, Sum.inr_injective.ne hab.symm]
  · refine Finset.prod_congr rfl fun r hr => ?_
    have hrb : r ≠ b := (Finset.mem_erase.mp hr).1
    have hra : r ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
    simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hrb, Sum.inr_injective.ne hra]

/-- **Transporting a diagram along `ρ`** pulls `W` back along `ρ` and multiplies by `sign ρ`. -/
theorem skewArcProd_congr (D : BrauerDiagram k) (ρ : Equiv.Perm (Fin k ⊕ Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    skewArcProd (PerfectMatching.congr ρ D) W =
      ((Equiv.Perm.sign ρ : ℤ) : R) * D.skewArcProd (W.submatrix ρ ρ) := by
  rw [skewArcProd_eq_of_isFraming _ hW (D.isFraming_framing.congr ρ), skewArcProd_def]
  simp only [map_mul, Units.val_mul, Int.cast_mul, mul_assoc, Matrix.submatrix_apply,
    Equiv.Perm.mul_apply]

/-- **Relabelling a diagram by `(σ, τ)`** pulls `W` back along `Sum.map σ τ` and multiplies by
`sign σ * sign τ`. -/
theorem skewArcProd_relabel (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (D.relabel σ τ).skewArcProd W =
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) *
        D.skewArcProd (W.submatrix (Sum.map σ τ) (Sum.map σ τ)) := by
  rw [relabel_def, skewArcProd_congr D _ hW, Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul]
  congr 2

end SkewArcProd

end BrauerDiagram

end TauCeti
