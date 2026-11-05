/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularElement
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Hilbert series of homogeneous regular-sequence quotients

For a locally finite graded algebra over a field, quotienting by a homogeneous weakly
regular sequence multiplies its Hilbert series by the product of the factors `1 - t^d`.
The quotient pieces are the images of the original pieces in the quotient by the ideal
of the whole sequence. The empty sequence and degree-zero elements are allowed.

The proof iterates `mk_finrank_quotientPiece_span_singleton`, using Mathlib's native
`RingTheory.Sequence.IsWeaklyRegular` and the third isomorphism theorem to identify
successive quotients with the quotient by the generated ideal. The coefficients can
belong to any ring; integer coefficients preserve dimensions in every characteristic.

## References

* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), §3.
-/

public section

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- Quotienting by a homogeneous weakly regular sequence multiplies the Hilbert series
by one factor `1 - t^d` for each element. A list of element-degree pairs keeps the degrees
attached to their chosen elements, including when an element is zero or has degree zero. -/
theorem mk_finrank_quotientPiece_of_isWeaklyRegular {S : Type*} [Ring S]
    [∀ n, Module.Finite k (𝒜 n)] (fs : List (A × ℕ))
    (hhom : ∀ p ∈ fs, p.1 ∈ 𝒜 p.2)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (fs.map Prod.fst)) :
    PowerSeries.mk (fun n ↦
      (Module.finrank k (quotientPiece 𝒜 (Ideal.ofList (fs.map Prod.fst)) n) : S)) =
      PowerSeries.mk (fun n ↦ (Module.finrank k (𝒜 n) : S)) *
        (fs.map (fun p ↦ (1 - PowerSeries.X ^ p.2 : PowerSeries S))).prod := by
  induction fs using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, List.map_nil, List.prod_nil, mul_one]
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, Ideal.ofList_nil,
      finrank_quotientPiece_bot]
  | append_singleton fs p ih =>
    have hhomfs : ∀ q ∈ fs, q.1 ∈ 𝒜 q.2 := fun q hq ↦ hhom q (List.mem_append_left _ hq)
    have hp : p.1 ∈ 𝒜 p.2 := hhom p (List.mem_append_right _ (by simp))
    rw [List.map_append, List.map_singleton,
      RingTheory.Sequence.isWeaklyRegular_append_iff] at hreg
    let I := Ideal.ofList (fs.map Prod.fst)
    have hregp := (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).1 hreg.2
    -- Native regular sequences use the module quotient by `I • ⊤`.
    -- Transport to the ring quotient, retaining its original scalar action.
    have hIeq : (I • ⊤ : Submodule A A) = I := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hregp' : IsSMulRegular (A ⧸ I) p.1 :=
      ((Submodule.quotEquivOfEq _ _ hIeq).isSMulRegular_congr p.1).1 hregp
    have hI : I.IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact ⟨q.2, hhomfs q hq⟩
    let := gradedAlgebraQuotientPiece 𝒜 I hI
    have hp' := mk_mem_quotientPiece 𝒜 I hp
    have hleft : IsLeftRegular (Ideal.Quotient.mk I p.1) := by
      intro x y hxy
      apply hregp'
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hxy
    have hstep := mk_finrank_quotientPiece_span_singleton
      (S := S) (quotientPiece 𝒜 I) hp' hleft
    -- The third isomorphism theorem compares the actual images of each original piece.
    have hdim (n : ℕ) :
        Module.finrank k
          (quotientPiece (quotientPiece 𝒜 I) (Ideal.span {Ideal.Quotient.mk I p.1}) n) =
        Module.finrank k (quotientPiece 𝒜 (I ⊔ Ideal.span {p.1}) n) := by
      have hmap := map_quotientPiece_quotientPiece 𝒜 I (Ideal.span {p.1}) n
      let e := (DoubleQuot.quotQuotEquivQuotSupₐ k I (Ideal.span {p.1})).toLinearEquiv
      have hdim := (e.finrank_map_eq _).symm.trans (congrArg
        (fun q : Submodule k (A ⧸ (I ⊔ Ideal.span {p.1})) ↦ Module.finrank k q) hmap)
      rw [Ideal.map_span, Set.image_singleton] at hdim
      exact hdim
    simp_rw [hdim] at hstep
    rw [List.map_append, List.map_singleton, Ideal.ofList_append, Ideal.ofList_singleton,
      List.map_append, List.map_singleton, List.prod_append, List.prod_singleton, ← mul_assoc]
    exact hstep.trans (congrArg (· * (1 - PowerSeries.X ^ p.2)) (ih hhomfs hreg.1))

end TauCeti.GradedAlgebra
