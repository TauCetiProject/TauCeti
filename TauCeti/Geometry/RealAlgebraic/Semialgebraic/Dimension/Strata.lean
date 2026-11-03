/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Dimension.Projection
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Topology

/-!
# Fiber-dimension strata of semialgebraic families

For a semialgebraic family in parameter and fiber coordinates, the parameters where the fiber
has dimension at least `d`, or exactly `d`, form semialgebraic sets. Empty fibers have dimension
`⊥` and are included in the exact-dimension statement. No continuity, nonemptiness, constant
fiber dimension or bound on fiber cardinalities is assumed.

The dimension criterion by coordinate projections reduces a lower bound on fiber dimension to
nonempty interior of one of finitely many projected fibers. Interior in a family is expressed by
a positive-radius ball contained in the fiber; projection closure eliminates its quantifiers.
These strata are the pieces on which to formulate the dimension formula for semialgebraic maps.
Applying the result to the graph also gives the strata for fibers of a semialgebraic function
on an arbitrary semialgebraic domain.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete 36, Springer, 1998, Section 2.8.
-/

public section

open Function MvPolynomial Set

namespace TauCeti

variable {σ : Type*} [Finite σ] {n : ℕ}

/-- The parameters where a semialgebraic fiber has dimension at least `d` form a semialgebraic
set, including when the fiber or parameter coordinate space has dimension zero. -/
theorem IsSemialgebraic.setOf_le_semialgebraicDim_fiber
    {s : Set (σ ⊕ Fin n → ℝ)} (hs : IsSemialgebraic s) (d : ℕ) :
    IsSemialgebraic {x : σ → ℝ |
      (d : WithBot ℕ∞) ≤ semialgebraicDim {y : Fin n → ℝ | Sum.elim x y ∈ s}} := by
  have hproj (ι : Fin d → Fin n) : IsSemialgebraic {x : σ → ℝ |
      (_root_.interior ((fun y ↦ y ∘ ι) '' {y : Fin n → ℝ | Sum.elim x y ∈ s})).Nonempty} := by
    have heq (x : σ → ℝ) :
        {y : Fin d → ℝ | Sum.elim x y ∈ (fun z ↦ z ∘ Sum.map id ι) '' s} =
        (fun y ↦ y ∘ ι) '' {y : Fin n → ℝ | Sum.elim x y ∈ s} := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        have hx : z ∘ Sum.inl = x := congrArg (fun w ↦ w ∘ Sum.inl) hzy
        have hy : (z ∘ Sum.inr) ∘ ι = y := congrArg (fun w ↦ w ∘ Sum.inr) hzy
        exact ⟨z ∘ Sum.inr, by simpa [← hx] using hz, hy⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨Sum.elim x z, hz, by ext (i | i) <;> rfl⟩
    simpa only [heq] using (hs.image_comp (Sum.map id ι)).setOf_fiber_interior_nonempty
  have hfiber (x : σ → ℝ) : IsSemialgebraic {y : Fin n → ℝ | Sum.elim x y ∈ s} := by
    have heq : (fun (y : Fin n → ℝ) i ↦ eval y (Sum.elim (fun i ↦ C (x i)) X i)) =
        fun y ↦ Sum.elim x y := by
      ext y (i | i) <;> simp
    have h := hs.preimage_eval (Sum.elim (fun i ↦ C (x i)) X)
    rw [heq] at h
    simpa only [preimage] using h
  convert IsSemialgebraic.iUnion (fun ι : {ι : Fin d → Fin n // Injective ι} ↦ hproj ι) using 1
  ext x
  simp only [mem_ofPred_eq, (hfiber x).natCast_le_semialgebraicDim_iff,
    mem_iUnion, Subtype.exists, exists_prop]

/-- Every exact fiber-dimension stratum of a semialgebraic family is semialgebraic.
The value `⊥` describes empty fibers; the infinite value gives the empty stratum. -/
theorem IsSemialgebraic.setOf_semialgebraicDim_fiber_eq
    {s : Set (σ ⊕ Fin n → ℝ)} (hs : IsSemialgebraic s) (d : WithBot ℕ∞) :
    IsSemialgebraic {x : σ → ℝ |
      semialgebraicDim {y : Fin n → ℝ | Sum.elim x y ∈ s} = d} := by
  induction d using WithBot.recBotCoe with
  | bot =>
    convert (hs.setOf_le_semialgebraicDim_fiber 0).compl using 1
    ext x
    cases hdim : semialgebraicDim {y : Fin n → ℝ | Sum.elim x y ∈ s}
        using WithBot.recBotCoe <;> simp [hdim, -semialgebraicDim_eq_bot_iff]
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      convert (isSemialgebraic_empty : IsSemialgebraic (∅ : Set (σ → ℝ))) using 1
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact ne_of_lt ((semialgebraicDim_le _).trans_lt (by
        exact_mod_cast ENat.natCast_lt_top n))
    | coe d =>
      convert (hs.setOf_le_semialgebraicDim_fiber d).sdiff
        (hs.setOf_le_semialgebraicDim_fiber (d + 1)) using 1
      ext x
      have hbound := semialgebraicDim_le {y : Fin n → ℝ | Sum.elim x y ∈ s}
      cases hdim : semialgebraicDim {y : Fin n → ℝ | Sum.elim x y ∈ s}
          using WithBot.recBotCoe with
      | bot => simp [hdim]
      | coe k =>
        rw [hdim] at hbound
        have hk : k ≤ (n : ℕ∞) := by exact_mod_cast hbound
        obtain ⟨k, rfl, _⟩ := ENat.le_natCast_iff.mp hk
        simp only [mem_ofPred_eq, mem_sdiff, hdim, ← ENat.WithBot.coe_eq_natCast,
          WithBot.coe_inj, WithBot.coe_le_coe, ENat.natCast_inj, ENat.natCast_le_natCast]
        omega

/-- The target points whose inverse image under a semialgebraic function has specified
dimension form a semialgebraic set. Fibers are taken inside the specified domain. -/
theorem IsSemialgebraicOn.setOf_semialgebraicDim_fiber_eq
    {f : (Fin n → ℝ) → (σ → ℝ)} {s : Set (Fin n → ℝ)}
    (hf : IsSemialgebraicOn f s) (d : WithBot ℕ∞) :
    IsSemialgebraic {y : σ → ℝ | semialgebraicDim (s ∩ f ⁻¹' {y}) = d} := by
  convert (hf.graph.preimage_comp (Equiv.sumComm _ _)).setOf_semialgebraicDim_fiber_eq d using 1
  ext y
  have heq : {x : Fin n → ℝ | Sum.elim y x ∈
      (fun z ↦ z ∘ Equiv.sumComm (Fin n) σ) ⁻¹'
        Equiv.sumArrowEquivProdArrow (Fin n) σ ℝ ⁻¹' s.graphOn f} =
      s ∩ f ⁻¹' {y} := by
    ext x
    have hswap : (Sum.elim y x) ∘ Equiv.sumComm (Fin n) σ = Sum.elim x y := by
      ext (i | i) <;> rfl
    rw [mem_ofPred_eq, mem_preimage, hswap, mem_preimage_sumArrowEquivProdArrow_graphOn]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, mem_inter_iff, mem_preimage,
      mem_singleton_iff]
  simp only [mem_ofPred_eq, heq]

end TauCeti
