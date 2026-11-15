/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Alexander
public import TauCeti.KnotTheory.Grid.Homology.Bigraded.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite generation of the homogeneous pieces of `GC⁻` and `GH⁻`

In an unblocked grid complex `GC⁻` with an odd number of link components, a monomial generator
`V^e · x` has Alexander degree `A(x) - |e|`. Since there are finitely many grid states `x` and
only finitely many exponent vectors `e : Fin n →₀ ℕ` of any fixed total degree `|e| = A(x) - a`,
each Alexander piece `alexanderChainMinusPiece R a` and each Maslov--Alexander piece
`bigradedChainMinusPiece R g` is spanned over the ground semiring `R` by finitely many monomial
generators.

Over a Noetherian commutative ring `R`, this finiteness passes to the homogeneous cycle pieces
`bigradedUnblockedCyclesPiece R g` as submodules of the chain pieces, and in characteristic two to
the homogeneous homology pieces `bigradedUnblockedHomologyPiece R g` and
`(alexanderUnblockedHomologyGrading R).piece a` as quotients of those cycles. In particular, over
any field of characteristic two, every homogeneous piece of `GH⁻` is finite-dimensional, even
though the total module `GH⁻` is infinite-dimensional over the ground field whenever it contains a
`U`-tower.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n) (R : Type*)

section Chain

variable [CommSemiring R]

omit R in
private theorem finite_state_exponent_of_alexander_eq (a : ℤ) :
    {p : GridState n × (Fin n →₀ ℕ) | G.alexanderℤ p.1 - (p.2.degree : ℤ) = a}.Finite := by
  refine (Set.finite_iUnion fun x : GridState n ↦
    (Finsupp.finite_of_degree_eq (G.alexanderℤ x - a).toNat).image (Prod.mk x)).subset ?_
  rintro ⟨x, e⟩ (h : G.alexanderℤ x - (e.degree : ℤ) = a)
  exact Set.mem_iUnion.mpr ⟨x, e, by dsimp; omega, rfl⟩

omit G in
private theorem finite_of_monomialPred (P : GridState n → (Fin n →₀ ℕ) → Prop)
    (M : Submodule R (GridChainMinus R n))
    (hfin : {p : GridState n × (Fin n →₀ ℕ) | P p.1 p.2}.Finite)
    (hmem : ∀ c : GridChainMinus R n, c ∈ M ↔ ∀ x e, e ∈ (c x).support → P x e) :
    Module.Finite R M := by
  classical
  let T := {p : GridState n × (Fin n →₀ ℕ) | P p.1 p.2}
  let gen : GridState n × (Fin n →₀ ℕ) → GridChainMinus R n :=
    fun p ↦ Finsupp.single p.1 (monomial p.2 (1 : R))
  refine Module.Finite.iff_fg.mpr (Submodule.fg_def.mpr
    ⟨gen '' T, hfin.image gen, le_antisymm ?_ ?_⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨x, e⟩, (hp : P x e), rfl⟩
    rw [SetLike.mem_coe, hmem]
    intro y f hf
    rcases eq_or_ne y x with rfl | hyx
    · rw [Finsupp.single_eq_same] at hf
      exact Finset.mem_singleton.mp (support_monomial_subset hf) ▸ hp
    · simp [gen, hyx.symm] at hf
  · intro c hc
    induction c using Finsupp.induction with
    | zero => exact Submodule.zero_mem _
    | single_add x p d hx _ ih =>
      have hxp : ∀ e ∈ p.support, P x e := by
        intro e he
        refine (hmem _).mp hc x e ?_
        rwa [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.mp hx, add_zero]
      have hd' : d ∈ M := by
        rw [hmem]
        intro y e he
        have hyx : x ≠ y := by
          rintro rfl
          exact hx (Finsupp.mem_support_iff.mpr fun h0 ↦ by simp [h0] at he)
        refine (hmem _).mp hc y e ?_
        simpa [Finsupp.single_apply, hyx] using he
      refine Submodule.add_mem _ ?_ (ih hd')
      have hp : (Finsupp.single x p : GridChainMinus R n) =
          ∑ e ∈ p.support, (p.coeff e) • gen (x, e) := by
        conv_lhs => rw [MvPolynomial.as_sum p]
        refine (map_sum (Finsupp.singleAddHom x) _ _).trans (Finset.sum_congr rfl fun e _ ↦ ?_)
        exact Finsupp.ext fun y ↦ by simp [gen, Finsupp.single_apply, smul_monomial]
      rw [hp]
      exact Submodule.sum_mem _ fun e he ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨(x, e), hxp e he, rfl⟩)

/-- Each Alexander-homogeneous piece of `GC⁻` is finitely generated over the ground semiring. -/
instance finite_alexanderChainMinusPiece (a : ℤ) :
    Module.Finite R (G.alexanderChainMinusPiece R a) :=
  finite_of_monomialPred R (fun x e ↦ G.alexanderℤ x - (e.degree : ℤ) = a)
    (G.alexanderChainMinusPiece R a) (G.finite_state_exponent_of_alexander_eq a)
    fun _ ↦ G.mem_alexanderChainMinusPiece

/-- Each Maslov--Alexander homogeneous piece of `GC⁻` is finitely generated over the ground
semiring. -/
instance finite_bigradedChainMinusPiece (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedChainMinusPiece R g) :=
  finite_of_monomialPred R (fun x e ↦ G.monomialBidegree x e = g)
    (G.bigradedChainMinusPiece R g)
    ((G.finite_state_exponent_of_alexander_eq g.2).subset fun p (hp : G.monomialBidegree _ _ = g) ↦
      (G.monomialBidegree_snd p.1 p.2).symm.trans (congrArg Prod.snd hp))
    fun _ ↦ G.mem_bigradedChainMinusPiece

end Chain

section Cycles

variable [CommRing R] [IsNoetherianRing R]

-- Pin the additive group on `GC⁻` so nested Noetherian submodule synthesis does not unfold
-- `GridChainMinus` with an uninstantiated coefficient-ring metavariable.
private noncomputable local instance : AddCommGroup (GridChainMinus R n) := inferInstance

private theorem finite_bigradedUnblockedCyclesPiece_aux (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedCyclesPiece R g) := by
  let ι : G.bigradedUnblockedCyclesPiece R g →ₗ[R] G.bigradedChainMinusPiece R g :=
    { toFun := fun z ↦ ⟨z.1.1, (G.mem_bigradedUnblockedCyclesPiece R).mp z.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact Module.Finite.of_injective ι fun _ _ h ↦
    Subtype.ext (Subtype.ext (congrArg (fun u : G.bigradedChainMinusPiece R g ↦ u.1) h))

/-- Over a Noetherian commutative ring, each Maslov--Alexander cycle piece of `GC⁻` is finitely
generated over the ground ring. -/
instance finite_bigradedUnblockedCyclesPiece (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedCyclesPiece R g) :=
  G.finite_bigradedUnblockedCyclesPiece_aux R g

variable [CharP R 2]

private theorem finite_bigradedUnblockedHomologyPiece_aux (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedHomologyPiece R g) := by
  let π : G.bigradedUnblockedCyclesPiece R g →ₗ[R] G.bigradedUnblockedHomologyPiece R g :=
    { toFun := fun z ↦ ⟨G.1.unblockedHomologyClass R z.1,
        G.unblockedHomologyClass_mem_bigradedUnblockedHomologyPiece R
          ((G.mem_bigradedUnblockedCyclesPiece R).mp z.2)⟩
      map_add' := fun x y ↦ Subtype.ext (map_add (G.1.unblockedHomologyClass R) x.1 y.1)
      map_smul' := fun r x ↦
        Subtype.ext (((G.1.unblockedHomologyClass R).restrictScalars R).map_smul r x.1) }
  refine Module.Finite.of_surjective π fun y ↦ ?_
  obtain ⟨z, hz, hzy⟩ := (G.mem_bigradedUnblockedHomologyPiece_iff R).mp y.2
  exact ⟨⟨z, (G.mem_bigradedUnblockedCyclesPiece R).mpr hz⟩, Subtype.ext hzy⟩

/-- Over a Noetherian commutative ring of characteristic two, each Maslov--Alexander piece of
`GH⁻` is finitely generated over the ground ring. -/
instance finite_bigradedUnblockedHomologyPiece (g : ℤ × ℤ) :
    Module.Finite R (G.bigradedUnblockedHomologyPiece R g) :=
  G.finite_bigradedUnblockedHomologyPiece_aux R g

private theorem finite_alexanderUnblockedHomologyGrading_piece_aux (a : ℤ) :
    Module.Finite R ((G.alexanderUnblockedHomologyGrading R).piece a) := by
  let Z : Submodule R (LinearMap.ker (G.1.unblockedDifferential R)) :=
    (G.alexanderChainMinusPiece R a).comap
      ((LinearMap.ker (G.1.unblockedDifferential R)).subtype.restrictScalars R)
  let ι : Z →ₗ[R] G.alexanderChainMinusPiece R a :=
    { toFun := fun z ↦ ⟨z.1.1, Submodule.mem_comap.mp z.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have : Module.Finite R Z :=
    Module.Finite.of_injective ι fun _ _ h ↦
      Subtype.ext (Subtype.ext (congrArg (fun u : G.alexanderChainMinusPiece R a ↦ u.1) h))
  let π : Z →ₗ[R] (G.alexanderUnblockedHomologyGrading R).piece a :=
    { toFun := fun z ↦ ⟨G.1.unblockedHomologyClass R z.1, by
        rw [G.mem_alexanderUnblockedHomologyGrading_piece_iff R,
          G.mem_alexanderHomologyGrading_piece_iff]
        exact ⟨z.1, Submodule.mem_comap.mp z.2,
          (G.1.unblockedHomologyIso_hom_unblockedHomologyClass R z.1).symm⟩⟩
      map_add' := fun x y ↦ Subtype.ext (map_add (G.1.unblockedHomologyClass R) x.1 y.1)
      map_smul' := fun r x ↦
        Subtype.ext (((G.1.unblockedHomologyClass R).restrictScalars R).map_smul r x.1) }
  have hπ_apply (w : Z) : (π w : G.1.unblockedHomology R) = G.1.unblockedHomologyClass R w.1 := rfl
  refine Module.Finite.of_surjective π fun y ↦ ?_
  have hy := y.2
  rw [G.mem_alexanderUnblockedHomologyGrading_piece_iff R,
    G.mem_alexanderHomologyGrading_piece_iff] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  refine ⟨⟨z, Submodule.mem_comap.mpr hz⟩, Subtype.ext ?_⟩
  apply (ModuleCat.mono_iff_injective (G.1.unblockedHomologyIso R).hom).mp inferInstance
  rw [hπ_apply, GridDiagram.unblockedHomologyIso_hom_unblockedHomologyClass, hzy]

/-- Over a Noetherian commutative ring of characteristic two, each Alexander piece of `GH⁻` is
finitely generated over the ground ring. -/
instance finite_alexanderUnblockedHomologyGrading_piece (a : ℤ) :
    Module.Finite R ((G.alexanderUnblockedHomologyGrading R).piece a) :=
  G.finite_alexanderUnblockedHomologyGrading_piece_aux R a

end Cycles

end TauCeti.OddComponentGridDiagram
