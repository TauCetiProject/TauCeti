/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Basic

/-!
# Almost complex structures along the pair-of-pants continuation family on a manifold

Pair-of-pants products for two choices of Floer data on the ends are compared by gluing
continuation cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The Hamiltonian
perturbations of this gluing are `TauCeti.Floer.pairOfPantsContinuationPerturbation`, defined for
any target. This file constructs the matching domain-dependent almost complex structures on the
tangent bundle of a manifold `M`, such as a closed symplectic manifold; the same structures on a
symplectic vector space are `TauCeti.Floer.pairOfPantsContinuationAlmostComplex`.

Let `σ` be a smooth two-form on `M` and `J₀` a smooth `σ`-compatible almost complex structure.
Given inner and outer families `J₁ q t` and `J₂ q t` of smooth `σ`-tame structures on the three
ends `q` and neck positions `L q`, the structure
`TauCeti.SmoothTwoForm.Compatible.pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L w` is,
on each tangent space `T_x M`, the linear structure
`TauCeti.Floer.pairOfPantsContinuationAlmostComplex` of `J₁ q t x` and `J₂ q t x` relative to `J₀ x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_pairOfPantsContinuationAlmostComplex`).
Its Cayley coordinate relative to `J₀` is

`∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L q, t_q))`,

where `(s_q, t_q)` are the coordinates of the end `q`, `σ_q = ±s_q` is its signed longitudinal
coordinate, `β` is the smooth transition from `0` to `1`, and `J^c_q` is the continuation homotopy
`TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex` from `J₁ q` to `J₂ q`. Thus:

* every member is `σ`-tame, and `σ`-compatible when the end families are;
* where `σ_q ≤ L q` on every end, on the pants side of the necks, it is the pair-of-pants structure
  `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex` of `J₁`; for nonpositive neck
  positions it is the pair-of-pants structure of `J₂`; for `J₁ = J₂` it is the pair-of-pants
  structure for every choice of neck positions;
* far out on the end `q`, where `σ_q ≥ 2`, it is the continuation homotopy `J^c_q(σ_q - L q, t_q)`
  translated to the neck position, so for `L q ≥ 2` the neck `L q ≤ σ_q ≤ L q + 1` carries the
  structure of a continuation cylinder; once `σ_q ≥ max 2 (L q + 1)` it is `J₂ q t_q`;
* it is `J₀` where `σ_q ≤ 1` on every end;
* for period-one end families that are jointly smooth on `ℝ × M`, it is jointly smooth in the neck
  positions, the point of `S` and the point of `M`, as a section of the tangent endomorphism bundle.

These are the domain-dependent structures `J_z` that agree with the selected end structures on
the tails and with continuation cylinders on the necks. Neither closedness of `σ` nor
compactness of `M` is used.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.pairOfPantsContinuationAlmostComplex`: the pair-of-pants
  structure with continuation necks on the tangent bundle of `M`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_pairOfPantsContinuationAlmostComplex`:
  on every tangent space it is the linear structure of the end structures there.
* `TauCeti.SmoothTwoForm.Compatible.tames_pairOfPantsContinuationAlmostComplex`,
  `TauCeti.SmoothTwoForm.Compatible.compatible_pairOfPantsContinuationAlmostComplex`: tameness and
  compatibility.
* `pairOfPantsContinuationAlmostComplex_eq_pairOfPantsAlmostComplex_of_forall_le`,
  `pairOfPantsContinuationAlmostComplex_of_nonpos`, `pairOfPantsContinuationAlmostComplex_self`
  (in `TauCeti.SmoothTwoForm.Compatible`): comparison with the pair-of-pants structures of the
  inner and outer families.
* `pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex`,
  `pairOfPantsContinuationAlmostComplex_cylindricalEndLift`,
  `pairOfPantsContinuationAlmostComplex_eq_endStructure`: the structure far out on the ends.
* `TauCeti.SmoothTwoForm.Compatible.contMDiff_pairOfPantsContinuationAlmostComplex`: joint
  smoothness in the neck positions, the domain point and the target point.

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

open Bundle Set Real Manifold Topology Function
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (J₁ J₂ : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJ₁ : ∀ q t, σ.Tames (J₁ q t)) (hJ₂ : ∀ q t, σ.Tames (J₂ q t))

/-- The almost complex structure on the tangent bundle over the pair of pants with continuation
necks from the inner families `J₁ q t` to the outer families `J₂ q t` of smooth `σ`-tame
structures on its ends, at the neck positions `L q`, relative to a `σ`-compatible base structure
`J₀`. It is the pair-of-pants structure
`TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex` of the continuation homotopies
`J^c_q(σ_q - L q, t)` from `J₁ q` to `J₂ q`, so its Cayley coordinate relative to `J₀` is
`∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L q, t_q))`. -/
def pairOfPantsContinuationAlmostComplex (L : Puncture → ℝ) (w : ThricePuncturedSphere) :
    SmoothAlmostComplexStructure I M :=
  h₀.pairOfPantsAlmostComplex
    (fun q t => h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
      (q.endSign * (q.endCoord w).re - L q, t))
    (fun _ _ => h₀.tames_continuationAlmostComplex _ _ _ _ _) w

/-- The pair-of-pants structure with continuation necks is tamed by `σ`. -/
theorem tames_pairOfPantsContinuationAlmostComplex (L : Puncture → ℝ)
    (w : ThricePuncturedSphere) :
    σ.Tames (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w) :=
  tames_pairOfPantsAlmostComplex h₀ _ _ w

/-- On every tangent space, the Cayley coordinate of the pair-of-pants structure with
continuation necks relative to `J₀` is the cutoff-weighted sum
`∑ q, β(σ_q - 1) • cayley (J^c_q(σ_q - L q, t_q))` of the Cayley coordinates of the continuation
homotopies of the ends. This characterizes the structure, since the Cayley transform is injective
on tame structures. -/
@[simp]
theorem cayley_pairOfPantsContinuationAlmostComplex (L : Puncture → ℝ)
    (w : ThricePuncturedSphere) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w).almostComplexStructureAt x) =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
            (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im)).almostComplexStructureAt
              x) :=
  cayley_pairOfPantsAlmostComplex h₀ _ _ w x

/-- On every tangent space, the structure is the linear pair-of-pants structure with continuation
necks of the end structures there, relative to `J₀`. -/
theorem almostComplexStructureAt_pairOfPantsContinuationAlmostComplex (L : Puncture → ℝ)
    (w : ThricePuncturedSphere) (x : M) :
    (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w).almostComplexStructureAt x =
      Floer.pairOfPantsContinuationAlmostComplex (V := TangentSpace I x) (M := Unit)
        (h₀.compatibleAt x) (fun q t _ => (J₁ q t).almostComplexStructureAt x)
        (fun q t _ => (J₂ q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ₁ q t) x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ₂ q t) x) L w () := by
  -- Both structures are tame and have the same Cayley coordinate relative to `J₀`.
  refine (h₀.compatibleAt x).eq_of_cayley_eq (h₀.isNondegenerate.tames_iff.mp
    (h₀.tames_pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w) x)
    (Floer.tames_pairOfPantsContinuationAlmostComplex (h₀.compatibleAt x) w ()) ?_
  simp only [cayley_pairOfPantsContinuationAlmostComplex,
    Floer.cayley_pairOfPantsContinuationAlmostComplex,
    almostComplexStructureAt_continuationAlmostComplex]

/-- The pair-of-pants structure with continuation necks is `σ`-compatible when the inner and
outer families are. -/
theorem compatible_pairOfPantsContinuationAlmostComplex (hJ₁c : ∀ q t, σ.Compatible (J₁ q t))
    (hJ₂c : ∀ q t, σ.Compatible (J₂ q t)) (L : Puncture → ℝ) (w : ThricePuncturedSphere) :
    σ.Compatible (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w) :=
  compatible_pairOfPantsAlmostComplex h₀ _ _
    (fun q _ => h₀.compatible_continuationAlmostComplex _ _ _ _ (hJ₁c q) (hJ₂c q) _) w

/-! ### Comparison with the pair-of-pants structures -/

/-- **The structure is the pair-of-pants structure of `J₁` on the pants side of the necks.** At a
point where the signed longitudinal coordinate `σ_q` of every end is at most the neck position
`L q`, the structure is the pair-of-pants structure of the inner families. -/
theorem pairOfPantsContinuationAlmostComplex_eq_pairOfPantsAlmostComplex_of_forall_le
    {L : Puncture → ℝ} {w : ThricePuncturedSphere}
    (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L q) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w =
      h₀.pairOfPantsAlmostComplex J₁ hJ₁ w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsContinuationAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex,
      Floer.pairOfPantsContinuationAlmostComplex_eq_pairOfPantsAlmostComplex_of_forall_le _ h]

/-- **Without necks the structure is the pair-of-pants structure of `J₂`.** If every neck
position is nonpositive, the continuation is already complete where the cutoff of each end is
nonzero. -/
theorem pairOfPantsContinuationAlmostComplex_of_nonpos {L : Puncture → ℝ} (hL : ∀ q, L q ≤ 0) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L =
      h₀.pairOfPantsAlmostComplex J₂ hJ₂ :=
  funext fun w => SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsContinuationAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex,
      Floer.pairOfPantsContinuationAlmostComplex_of_nonpos _ hL]

/-- If the inner and outer families agree, the structure is the pair-of-pants structure for every
choice of neck positions. -/
@[simp]
theorem pairOfPantsContinuationAlmostComplex_self (L : Puncture → ℝ) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₁ hJ₁ hJ₁ L =
      h₀.pairOfPantsAlmostComplex J₁ hJ₁ :=
  funext fun w => SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsContinuationAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex,
      Floer.pairOfPantsContinuationAlmostComplex_self]

/-- Where every end cutoff vanishes, that is, where `σ_q ≤ 1` on every end, the structure is the
base structure `J₀`. -/
theorem pairOfPantsContinuationAlmostComplex_eq_base_of_forall_le_one {L : Puncture → ℝ}
    {w : ThricePuncturedSphere} (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    refine (h₀.compatibleAt x).eq_of_cayley_eq (h₀.isNondegenerate.tames_iff.mp
      (h₀.tames_pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w) x)
      (h₀.compatibleAt x).tames ?_
    rw [cayley_pairOfPantsContinuationAlmostComplex, AlmostComplexStructure.cayley_self]
    exact Finset.sum_eq_zero fun q _ => by
      rw [smoothTransition.zero_of_nonpos (sub_nonpos.mpr (hw q)), zero_smul]

/-! ### The structure on the ends -/

variable {q : Puncture}

/-- **The structure far out on an end.** On the part `σ_q ≥ 2` of the end `q`, the structure is
the continuation homotopy from `J₁ q` to `J₂ q` at `(σ_q - L q, t_q)`. So for `L q ≥ 2` the neck
`L q ≤ σ_q ≤ L q + 1` carries the structure of a continuation cylinder, translated to the neck
position. No periodicity is needed. -/
theorem pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex (L : Puncture → ℝ)
    {w : ThricePuncturedSphere} (hw : 2 ≤ q.endSign * (q.endCoord w).re) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w =
      h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
        (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im) :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsContinuationAlmostComplex,
      almostComplexStructureAt_continuationAlmostComplex,
      Floer.pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex _ hw]

/-- **The structure beyond the neck.** Where `σ_q ≥ 2` and `σ_q ≥ L q + 1` on the end `q`, past
the collar and the neck, the structure is the outer structure `J₂ q t_q`. -/
theorem pairOfPantsContinuationAlmostComplex_eq_endStructure {L : Puncture → ℝ}
    {w : ThricePuncturedSphere} (hw : 2 ≤ q.endSign * (q.endCoord w).re)
    (hwL : L q + 1 ≤ q.endSign * (q.endCoord w).re) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w = J₂ q (q.endCoord w).im := by
  rw [pairOfPantsContinuationAlmostComplex_eq_continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ L hw,
    continuationAlmostComplex_of_one_le h₀ _ _ _ _ (by dsimp only; linarith)]

/-- **The structure on an end, in end coordinates.** If `J₁ q` and `J₂ q` have period one in `t`,
then at the point of the part `σ_q > 0` of the end `q` with end coordinates `z = s + i t`, the
Cayley coordinate of the structure relative to `J₀` is `β(±s - 1) • cayley (J^c_q(±s - L q, t))`,
where `J^c_q` is the continuation homotopy from `J₁ q` to `J₂ q`. -/
theorem cayley_pairOfPantsContinuationAlmostComplex_cylindricalEndLift_of_pos
    (hJ₁p : Periodic (J₁ q) 1) (hJ₂p : Periodic (J₂ q) 1) (L : Puncture → ℝ)
    (w : ThricePuncturedSphere) {z : ℂ} (hw : (w : ℂ) = q.cylindricalEndLift z)
    (hz : 0 < q.endSign * z.re) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w).almostComplexStructureAt x) =
      smoothTransition (q.endSign * z.re - 1) • (J₀.almostComplexStructureAt x).cayley
        ((h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
          (q.endSign * z.re - L q, z.im)).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_pairOfPantsContinuationAlmostComplex, hw,
    almostComplexStructureAt_continuationAlmostComplex]
  exact Floer.cayley_pairOfPantsContinuationAlmostComplex_cylindricalEndLift_of_pos _
    (fun t => funext fun _ => by rw [hJ₁p t]) (fun t => funext fun _ => by rw [hJ₂p t]) hz ()

/-- **The structure on an end, in end coordinates, past the collar.** If `J₁ q` and `J₂ q` have
period one in `t`, then at the point of the end `q` with end coordinates `z = s + i t` and
`±s ≥ 2`, the structure is the continuation homotopy `J^c_q(±s - L q, t)` from `J₁ q` to
`J₂ q`. -/
theorem pairOfPantsContinuationAlmostComplex_cylindricalEndLift (hJ₁p : Periodic (J₁ q) 1)
    (hJ₂p : Periodic (J₂ q) 1) (L : Puncture → ℝ) (w : ThricePuncturedSphere) {z : ℂ}
    (hw : (w : ℂ) = q.cylindricalEndLift z) (hz : 2 ≤ q.endSign * z.re) :
    h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w =
      h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q) (q.endSign * z.re - L q, z.im) :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    refine (h₀.compatibleAt x).eq_of_cayley_eq (h₀.isNondegenerate.tames_iff.mp
      (h₀.tames_pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ L w) x)
      (h₀.isNondegenerate.tames_iff.mp (h₀.tames_continuationAlmostComplex _ _ _ _ _) x) ?_
    rw [cayley_pairOfPantsContinuationAlmostComplex_cylindricalEndLift_of_pos h₀ J₁ J₂ hJ₁ hJ₂
      hJ₁p hJ₂p L w hw (by linarith) x, smoothTransition.one_of_one_le (by linarith), one_smul]

/-! ### Smoothness -/

/-- **The pair-of-pants structure with continuation necks is smooth.** For inner and outer
families of period one which are jointly `C^n` on `ℝ × M` as sections of the tangent endomorphism
bundle, the structures are jointly `C^n` along `C^n` families of neck positions `L`, domain points
`f` and target points `b`, as sections of the tangent endomorphism bundle along `b`. The domain
family must avoid the two deleted points. -/
theorem contMDiff_pairOfPantsContinuationAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hJ₁p : ∀ q, Periodic (J₁ q) 1) (hJ₂p : ∀ q, Periodic (J₂ q) 1)
    (hJ₁s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₁ q p.1).toEndomorphism p.2)))
    (hJ₂s : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₂ q p.1).toEndomorphism p.2)))
    {L : N → Puncture → ℝ} {f : N → ℂ} {b : N → M} (hL : ContMDiff I' 𝓘(ℝ, Puncture → ℝ) n L)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hS : ∀ p, f p ≠ 0 ∧ f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L p) ⟨f p, hS p⟩
          ).toEndomorphism (b p))) := by
  intro y₀
  have hq (q : Puncture) : f y₀ ≠ q.endCenter := ne_endCenter (hS y₀) q
  have hK (y : N) : LinearMap.toContinuousLinearMap
      ((h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L y) ⟨f y, hS y⟩
        ).almostComplexStructureAt (b y)).toLinearMap =
      (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L y) ⟨f y, hS y⟩).toEndomorphism
        (b y) :=
    ContinuousLinearMap.coe_injective
      (SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap _ _)
  simp only [← hK]
  refine h₀.contMDiffAt_of_cayley_eq_sum
    (K := fun y => (h₀.pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (L y) ⟨f y, hS y⟩
      ).almostComplexStructureAt (b y))
    (L := fun q y => h₀.continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q)
      (q.endSign * (q.endCoord (f y)).re - L y q, (q.endCoord (f y)).im))
    (a := fun q y => smoothTransition (q.endSign * (q.endCoord (f y)).re - 1))
    (fun y => h₀.isNondegenerate.tames_iff.mp
      (h₀.tames_pairOfPantsContinuationAlmostComplex J₁ J₂ hJ₁ hJ₂ _ _) (b y))
    (fun q _ => h₀.tames_continuationAlmostComplex _ _ _ _ _)
    (fun y => cayley_pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ _ _ _) (hb y₀)
    (fun q => Floer.contMDiffAt_smoothTransition_endCoord_comp q 1 (hf y₀) (hq q)) fun q => ?_
  -- The continuation homotopy of the end `q` is read at `(σ_q - L q, t_q)`: its longitudinal
  -- argument is smooth away from the center of the end, and the end families are smooth at the
  -- angular coordinate by periodicity.
  have hσ : ContMDiffAt I' 𝓘(ℝ) n
      (fun y => q.endSign * (q.endCoord (f y)).re - L y q) y₀ :=
    ((contDiffAt_const.mul (q.contDiffAt_re_endCoord (hq q))).contMDiffAt.comp y₀ (hf y₀)).sub
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Puncture => ℝ) q).contDiff.contMDiff
        |>.contMDiffAt.comp y₀ (hL y₀))
  exact h₀.contMDiffAt_continuationAlmostComplex (J₁ q) (J₂ q) (hJ₁ q) (hJ₂ q) (hb y₀) hσ
    (q.contMDiffAt_toEndomorphism_comp_im_endCoord (hJ₁p q) (hJ₁s q) (hf y₀) (hb y₀) (hq q))
    (q.contMDiffAt_toEndomorphism_comp_im_endCoord (hJ₂p q) (hJ₂s q) (hf y₀) (hb y₀) (hq q))

end TauCeti.SmoothTwoForm.Compatible
