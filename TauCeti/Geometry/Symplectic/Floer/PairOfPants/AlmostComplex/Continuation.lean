/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Almost complex structures along the pair-of-pants continuation family

Pair-of-pants products for two choices of Floer data on the ends are compared by gluing
continuation cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The Hamiltonian
perturbations of this gluing are `TauCeti.Floer.pairOfPantsContinuationPerturbation`; this file
constructs the matching domain-dependent almost complex structures.

Fix an `ω`-compatible base structure `J₀`. Given families `J₁ t x` and `J₂ t x` of tame
structures, the *continuation homotopy* `TauCeti.Floer.continuationAlmostComplex` (in
`TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex`) is the structure whose Cayley
coordinate at `(s, t)` is `(1 - β(s)) • cayley (J₁ t x) + β(s) • cayley (J₂ t x)`, where `β` is the
smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. It is `J₁` for `s ≤ 0` and `J₂` for
`s ≥ 1`: the almost complex structure of a continuation cylinder.

Given inner and outer families `J₁ q`, `J₂ q` on the three ends `q` and neck positions `L_q`,
the structure `TauCeti.Floer.pairOfPantsContinuationAlmostComplex` is the inverse Cayley transform
of

`∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L_q, t_q, x))`,

where `(s_q, t_q)` are the coordinates of the end `q`, `σ_q = ±s_q` is its signed longitudinal
coordinate and `J^c_q` is the continuation homotopy from `J₁ q` to `J₂ q`. This is the pair-of-pants
structure of `TauCeti.Floer.pairOfPantsAlmostComplex` whose end structures carry the continuation
homotopy at the neck positions, with the same profile as the Hamiltonian perturbation. Thus:

* every member is `ω`-tame, and `ω`-compatible when the end families are;
* where `σ_q ≤ L_q` on every end, on the pants side of the necks, it is the pair-of-pants
  structure of `J₁`; for nonpositive neck positions it is the pair-of-pants structure of `J₂`;
  for `J₁ = J₂` it is the pair-of-pants structure for every choice of neck positions;
* far out on the end `q`, where `σ_q ≥ 2`, it is the continuation homotopy `J^c_q(σ_q - L_q, t)`
  translated to the neck position, so for `L_q ≥ 2` the neck `L_q ≤ σ_q ≤ L_q + 1` carries the
  structure of a continuation cylinder; once `σ_q ≥ max 2 (L_q + 1)` it is `J₂ q t`;
* it is `J₀` off the parts `σ_q > 1` of the ends, and in particular at the centers `0` and `1`;
* for period-one families that are smooth on `ℝ × M`, it is smooth jointly in the neck positions,
  the domain point of `S` and the external point, so moving the necks along a smooth path gives a
  smooth family of almost complex structures.

The structures act on a fixed symplectic vector space `(V, ω)`; the external point may be a target
point (for a vector space target, `M = V`).

## Main definitions

* `TauCeti.Floer.pairOfPantsContinuationAlmostComplex`: the pair-of-pants structure with
  continuation necks.

## Main results

* `TauCeti.Floer.tames_pairOfPantsContinuationAlmostComplex`,
  `TauCeti.Floer.compatible_pairOfPantsContinuationAlmostComplex`: tameness and compatibility.
* `TauCeti.Floer.pairOfPantsContinuationAlmostComplex_eq_pairOfPantsAlmostComplex_of_forall_le`,
  `TauCeti.Floer.pairOfPantsContinuationAlmostComplex_of_nonpos`,
  `TauCeti.Floer.pairOfPantsContinuationAlmostComplex_self`: comparison with the pair-of-pants
  structures of the inner and outer families.
* `TauCeti.Floer.pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex`,
  `TauCeti.Floer.pairOfPantsContinuationAlmostComplex_eq_endStructure`: the structure far out on
  the ends (on the necks when `L q ≥ 2`) and beyond the necks.
* `TauCeti.Floer.contMDiffAt_pairOfPantsContinuationAlmostComplex`: joint smoothness in the neck
  positions, the domain point and the external point.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the spaces of tame and compatible structures.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

/-! ### The pair of pants with continuation necks -/

section PairOfPants

variable {J₁ J₂ : Puncture → ℝ → M → AlmostComplexStructure V}
  {hJ₁ : ∀ q t x, ω.Tames (J₁ q t x)} {hJ₂ : ∀ q t x, ω.Tames (J₂ q t x)} {L : Puncture → ℝ}

/-- The almost complex structure on the pair of pants with continuation necks from the inner
families `J₁ q t x` to the outer families `J₂ q t x` of `ω`-tame structures on its ends, at the
neck positions `L q`, relative to an `ω`-compatible base structure `J₀`. At `w ∈ ℂ` and `x ∈ M`
it is the inverse Cayley transform, relative to `J₀`, of
`∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L q, t_q, x))`, where `(s_q, t_q)` are the coordinates of
the end `q` at `w`, `σ_q = ±s_q` and `J^c_q` is the continuation homotopy
`TauCeti.Floer.continuationAlmostComplex` from `J₁ q` to `J₂ q`. It is the pair-of-pants structure
`TauCeti.Floer.pairOfPantsAlmostComplex` whose end structures, which may depend on an external
point, are these continuation homotopies; the external point records the neck positions and the
domain point. -/
def pairOfPantsContinuationAlmostComplex (h₀ : ω.Compatible J₀)
    (J₁ J₂ : Puncture → ℝ → M → AlmostComplexStructure V) (hJ₁ : ∀ q t x, ω.Tames (J₁ q t x))
    (hJ₂ : ∀ q t x, ω.Tames (J₂ q t x)) (L : Puncture → ℝ) (w : ℂ) (x : M) :
    AlmostComplexStructure V :=
  pairOfPantsAlmostComplex h₀
    (fun q t (p : (Puncture → ℝ) × ℂ × M) => continuationAlmostComplex h₀ (J₁ q) (J₂ q) (hJ₁ q)
      (hJ₂ q) (q.endSign * (q.endCoord p.2.1).re - p.1 q, t) p.2.2)
    (fun _ _ _ => tames_continuationAlmostComplex h₀ _ _) w (L, w, x)

/-- The pair-of-pants structure with continuation necks is tamed by `ω`. -/
theorem tames_pairOfPantsContinuationAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x) :=
  tames_pairOfPantsAlmostComplex h₀ w _

/-- The Cayley transform of the pair-of-pants structure with continuation necks, relative to
`J₀`, is the cutoff-weighted sum `∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L q, t_q, x))` of the
Cayley transforms of the continuation homotopies on the ends. This characterizes the structure,
since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_pairOfPantsContinuationAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x) =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        J₀.cayley (continuationAlmostComplex h₀ (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
          (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im) x) :=
  cayley_pairOfPantsAlmostComplex h₀ w _

/-- The pair-of-pants structure with continuation necks is `ω`-compatible when the inner and outer
families are. -/
theorem compatible_pairOfPantsContinuationAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ₁c : ∀ q t x, ω.Compatible (J₁ q t x)) (hJ₂c : ∀ q t x, ω.Compatible (J₂ q t x)) (w : ℂ)
    (x : M) : ω.Compatible (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x) :=
  compatible_pairOfPantsAlmostComplex h₀
    (fun q _ _ => compatible_continuationAlmostComplex h₀ (hJ₁c q) (hJ₂c q) _ _) w _

/-- **The structure is the pair-of-pants structure of `J₁` on the pants side of the necks.** At a
point where the signed longitudinal coordinate `σ_q` of every end is at most the neck position
`L q`, the structure is the pair-of-pants structure of the inner families. -/
theorem pairOfPantsContinuationAlmostComplex_eq_pairOfPantsAlmostComplex_of_forall_le
    (h₀ : ω.Compatible J₀) {w : ℂ} (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L q)
    (x : M) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x =
      pairOfPantsAlmostComplex h₀ J₁ hJ₁ w x := by
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsContinuationAlmostComplex h₀ w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_pairOfPantsContinuationAlmostComplex, cayley_pairOfPantsAlmostComplex]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [continuationAlmostComplex_of_nonpos h₀ (sub_nonpos.2 (h q))]

/-- **Without necks the structure is the pair-of-pants structure of `J₂`.** If every neck
position is nonpositive, the continuation is already complete where the cutoff of each end is
nonzero. -/
theorem pairOfPantsContinuationAlmostComplex_of_nonpos (h₀ : ω.Compatible J₀)
    (hL : ∀ q, L q ≤ 0) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L =
      pairOfPantsAlmostComplex h₀ J₂ hJ₂ := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsContinuationAlmostComplex h₀ w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  rw [cayley_pairOfPantsContinuationAlmostComplex, cayley_pairOfPantsAlmostComplex]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hc : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0
  · simp [hc]
  · have h₁ := (one_lt_endSign_mul_re_endCoord hc).1
    rw [continuationAlmostComplex_of_one_le h₀ (by dsimp only; linarith [hL q])]

/-- If the inner and outer families agree, the structure is the pair-of-pants structure for every
choice of neck positions. -/
@[simp]
theorem pairOfPantsContinuationAlmostComplex_self (h₀ : ω.Compatible J₀)
    (L : Puncture → ℝ) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₁ hJ₁ hJ₁ L =
      pairOfPantsAlmostComplex h₀ J₁ hJ₁ := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsContinuationAlmostComplex h₀ w x)
    (tames_pairOfPantsAlmostComplex h₀ w x) ?_
  simp only [cayley_pairOfPantsContinuationAlmostComplex, cayley_pairOfPantsAlmostComplex,
    continuationAlmostComplex_self]

variable {q : Puncture}

/-- **The structure on an end.** If `J₁ q` and `J₂ q` have period one in `t`, then on the part
`±s > 0` of the end `q`, the Cayley transform of the structure at the point with end coordinates
`z = s + i t` is `β(±s - 1) • cayley (J^c_q(±s - L q, t, x))`, where `J^c_q` is the continuation
homotopy from `J₁ q` to `J₂ q`. -/
theorem cayley_pairOfPantsContinuationAlmostComplex_cylindricalEndLift_of_pos
    (h₀ : ω.Compatible J₀) (hJ₁p : Periodic (J₁ q) 1) (hJ₂p : Periodic (J₂ q) 1) {z : ℂ}
    (hz : 0 < q.endSign * z.re) (x : M) :
    J₀.cayley (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L (q.cylindricalEndLift z) x) =
      smoothTransition (q.endSign * z.re - 1) •
        J₀.cayley (continuationAlmostComplex h₀ (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
          (q.endSign * z.re - L q, z.im) x) := by
  have hp : Periodic (fun t (p : (Puncture → ℝ) × ℂ × M) => continuationAlmostComplex h₀ (J₁ q)
      (J₂ q) (hJ₁ q) (hJ₂ q) (q.endSign * (q.endCoord p.2.1).re - p.1 q, t) p.2.2) 1 :=
    fun t => funext fun p => periodic_continuationAlmostComplex h₀ hJ₁p hJ₂p _ _ t
  rw [pairOfPantsContinuationAlmostComplex,
    cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos h₀ hp hz,
    re_endCoord_cylindricalEndLift]

/-- **The structure far out on an end.** On the part `±s ≥ 2` of the end `q`, the structure at
`w` is the continuation homotopy from `J₁ q` to `J₂ q` at `(σ_q - L q, t_q)`. So for `L q ≥ 2`
the neck `L q ≤ σ_q ≤ L q + 1` carries the structure of a continuation cylinder, translated to the
neck position. No periodicity is needed. -/
theorem pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex
    (h₀ : ω.Compatible J₀) {w : ℂ} (hw : 2 ≤ q.endSign * (q.endCoord w).re) (x : M) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x =
      continuationAlmostComplex h₀ (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
        (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im) x :=
  pairOfPantsAlmostComplex_eq_endStructure h₀ hw _

/-- **The structure beyond the neck.** Where `σ_q ≥ 2` and `σ_q ≥ L q + 1` on the end `q`, past
the collar and the neck, the structure is the outer structure `J₂ q t x`. -/
theorem pairOfPantsContinuationAlmostComplex_eq_endStructure (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : 2 ≤ q.endSign * (q.endCoord w).re) (hwL : L q + 1 ≤ q.endSign * (q.endCoord w).re)
    (x : M) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x = J₂ q (q.endCoord w).im x := by
  rw [pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex h₀ hw,
    continuationAlmostComplex_of_one_le h₀ (by dsimp only; linarith)]

/-- Beyond the height `2 + ∑ q, |L q|` on each end, past every neck and collar, the structure is
the outer structure `J₂ q t x`. -/
theorem pairOfPantsContinuationAlmostComplex_eq_endStructure_of_le (h₀ : ω.Compatible J₀)
    {w : ℂ} (hw : 2 + ∑ r, |L r| ≤ q.endSign * (q.endCoord w).re) (x : M) :
    pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x = J₂ q (q.endCoord w).im x :=
  have hL : L q ≤ ∑ r, |L r| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun r _ ↦ abs_nonneg (L r)) (Finset.mem_univ q))
  pairOfPantsContinuationAlmostComplex_eq_endStructure h₀
    (by linarith [Finset.sum_nonneg fun r (_ : r ∈ Finset.univ) ↦ abs_nonneg (L r)])
    (by linarith) x

/-- The structure differs from `J₀` only on the parts `±s > 1` of the three ends. -/
theorem exists_cylindricalEndLift_of_pairOfPantsContinuationAlmostComplex_ne
    (h₀ : ω.Compatible J₀) {w : ℂ} {x : M}
    (h : pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w x ≠ J₀) :
    ∃ (q : Puncture) (z : ℂ), 1 < q.endSign * z.re ∧ q.cylindricalEndLift z = w :=
  exists_cylindricalEndLift_of_pairOfPantsAlmostComplex_ne h₀ h

/-- The structure is the base structure `J₀` at the centers `0` and `1` of the ends. -/
theorem pairOfPantsContinuationAlmostComplex_endCenter (h₀ : ω.Compatible J₀) (q : Puncture)
    (x : M) : pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L q.endCenter x = J₀ :=
  pairOfPantsAlmostComplex_endCenter h₀ q _

end PairOfPants

end Algebraic

section Smooth

/-! ### Smoothness -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The pair-of-pants structure with continuation necks is smooth.** For families `J₁ q t x`
and `J₂ q t x` of `ω`-tame structures which have period one in `t` and are `C^n` on `ℝ × M`, the
structure is `C^n` jointly in the neck positions `L`, the point `w` of the thrice-punctured sphere
`S = ℂ ∖ {0, 1}` and the external point `x`. -/
theorem contMDiffAt_pairOfPantsContinuationAlmostComplex (h₀ : ω.Compatible J₀)
    {J₁ J₂ : Puncture → ℝ → M → AlmostComplexStructure V} {hJ₁ : ∀ q t x, ω.Tames (J₁ q t x)}
    {hJ₂ : ∀ q t x, ω.Tames (J₂ q t x)} {n : ℕ∞} (hJ₁p : ∀ q, Periodic (J₁ q) 1)
    (hJ₂p : ∀ q, Periodic (J₂ q) 1)
    (hJ₁s : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J₁ q p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJ₂s : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J₂ q p.1 p.2).toLinearMap.toContinuousLinearMap))
    (L : Puncture → ℝ) (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : (Puncture → ℝ) × ℂ × M => (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂
        p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap)
      (L, (w : ℂ), x) := by
  refine h₀.contMDiffAt_of_contMDiffAt_cayley
    (fun _ => tames_pairOfPantsContinuationAlmostComplex h₀ _ _) ?_
  simp only [cayley_pairOfPantsContinuationAlmostComplex, map_sum, map_smul,
    toContinuousLinearMap_cayley_continuationAlmostComplex]
  refine contMDiffAt_finsetSum fun q _ => ?_
  have hw : (w : ℂ) ≠ q.endCenter := ne_endCenter w.2 q
  have hf : ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : (Puncture → ℝ) × ℂ × M => p.2.1) (L, (w : ℂ), x) :=
    contMDiffAt_fst.comp (L, (w : ℂ), x) contMDiffAt_snd
  -- The neck weight `β(σ_q - L q)` is smooth in the domain point and the neck position.
  have hre : ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ) n
      (fun p : (Puncture → ℝ) × ℂ × M => q.endSign * (q.endCoord p.2.1).re) (L, (w : ℂ), x) :=
    ContMDiffAt.comp (g := fun w : ℂ => q.endSign * (q.endCoord w).re) (L, (w : ℂ), x)
      (contDiffAt_const.mul (q.contDiffAt_re_endCoord hw)).contMDiffAt hf
  have hL : ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ) n
      (fun p : (Puncture → ℝ) × ℂ × M => p.1 q) (L, (w : ℂ), x) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Puncture => ℝ) q).contDiff.contMDiff
      |>.contMDiffAt.comp (L, (w : ℂ), x) contMDiffAt_fst
  have hσ : ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ) n
      (fun p : (Puncture → ℝ) × ℂ × M =>
        smoothTransition (q.endSign * (q.endCoord p.2.1).re - p.1 q)) (L, (w : ℂ), x) :=
    smoothTransition.contDiff.contMDiff.contMDiffAt.comp (L, (w : ℂ), x) (hre.sub hL)
  -- Periodicity makes the Cayley transforms of the end families smooth in the angular coordinate.
  have hend (J : Puncture → ℝ → M → AlmostComplexStructure V) (hJ : ∀ q t x, ω.Tames (J q t x))
      (hJp : ∀ q, Periodic (J q) 1)
      (hJs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
        (fun p : ℝ × M => (J q p.1 p.2).toLinearMap.toContinuousLinearMap)) :
      ContMDiffAt (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
        (fun p : (Puncture → ℝ) × ℂ × M =>
          LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.2.1).im p.2.2)))
        (L, (w : ℂ), x) := by
    have hFp : Periodic
        (fun t y => LinearMap.toContinuousLinearMap (J₀.cayley (J q t y))) 1 := fun t => by
      simp only [hJp q t]
    exact ContMDiffAt.comp (L, (w : ℂ), x) (g := fun p : ℂ × M =>
        LinearMap.toContinuousLinearMap (J₀.cayley (J q (q.endCoord p.1).im p.2)))
      (q.contMDiffAt_comp_im_endCoord hFp
        (h₀.tames.contMDiff_cayley (J := fun p : ℝ × M => J q p.1 p.2) (fun p => hJ q p.1 p.2)
          (hJs q)) hw x) contMDiffAt_snd
  exact (contMDiffAt_smoothTransition_endCoord_comp q 1 hf hw).smul
    (((ContMDiffAt.sub contMDiffAt_const hσ).smul (hend J₁ hJ₁ hJ₁p hJ₁s)).add
      (hσ.smul (hend J₂ hJ₂ hJ₂p hJ₂s)))

end Smooth

end TauCeti.Floer
