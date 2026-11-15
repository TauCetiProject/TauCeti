/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath

/-!
# The continuation homotopy of almost complex structures on a manifold

A Floer continuation cylinder in a manifold `M`, or a continuation neck inserted into an end of a
Floer domain mapping to `M`, carries an `s`-dependent family of almost complex structures on the
tangent bundle of `M` interpolating between the structures of its two ends. This file constructs
that family.

Let `σ` be a smooth two-form on `M` and `J₀` a smooth `σ`-compatible almost complex structure.
Given families `J₁ t` and `J₂ t` of smooth `σ`-tame structures on `M`, the continuation homotopy
`TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ (s, t)` is, on each
tangent space `T_x M`, the linear continuation homotopy `TauCeti.Floer.continuationAlmostComplex`
of `J₁ t x` and `J₂ t x` relative to `J₀ x`: its Cayley coordinate relative to `J₀ x` is

`(1 - β(s)) • cayley (J₁ t x) + β(s) • cayley (J₂ t x)`,

where `β` is the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. It is `J₁ t` for
`s ≤ 0` and `J₂ t` for `s ≥ 1`, it is tame, it is compatible when `J₁` and `J₂` are, it has
period one in `t` when they do, and it is jointly smooth in `(s, t)` and the point of `M` when
`J₁` and `J₂` are jointly smooth on `ℝ × M`. Smoothness is checked in trivializations of the
tangent bundle through `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_of_cayley_eq_sum`, so neither
a global trivialization nor a constant two-form is assumed, and neither closedness of `σ` nor
compactness of `M` is used.

## Main definitions

* `TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex`: the continuation homotopy of
  smooth almost complex structures on `M`.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_continuationAlmostComplex`: on every
  tangent space it is the linear continuation homotopy.
* `TauCeti.SmoothTwoForm.Compatible.cayley_continuationAlmostComplex`: its Cayley coordinate.
* `TauCeti.SmoothTwoForm.Compatible.tames_continuationAlmostComplex`,
  `TauCeti.SmoothTwoForm.Compatible.compatible_continuationAlmostComplex`: tameness and
  compatibility.
* `TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex_of_one_le`: its two ends.
* `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_continuationAlmostComplex`,
  `TauCeti.SmoothTwoForm.Compatible.contMDiff_continuationAlmostComplex`: joint smoothness.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Section 2.5, on the
  Cayley transform and the convexity of the spaces of tame and compatible structures.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Function
open scoped ContDiff

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (J₁ J₂ : ℝ → SmoothAlmostComplexStructure I M)
  (hJ₁ : ∀ t, σ.Tames (J₁ t)) (hJ₂ : ∀ t, σ.Tames (J₂ t))

/-- The linear continuation homotopy on the tangent space at `x`. -/
private def continuationAt (z : ℝ × ℝ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  Floer.continuationAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
    (fun t _ => (J₁ t).almostComplexStructureAt x) (fun t _ => (J₂ t).almostComplexStructureAt x)
    (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ₁ t) x)
    (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ₂ t) x) z ()

/-- The Cayley coordinate of the linear continuation homotopy, as a sum over the two end families
`![J₁ t, J₂ t]` with the weights `![1 - β(s), β(s)]`. -/
private theorem cayley_continuationAt (z : ℝ × ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z x) =
      ∑ i : Fin 2, ![1 - smoothTransition z.1, smoothTransition z.1] i •
        (J₀.almostComplexStructureAt x).cayley
          ((![J₁ z.2, J₂ z.2] i).almostComplexStructureAt x) := by
  rw [continuationAt, Floer.cayley_continuationAlmostComplex, Fin.sum_univ_two]
  rfl

/-- The linear continuation homotopy is smooth on `M` for a fixed `(s, t)`. -/
private theorem contMDiffAt_continuationAt (z : ℝ × ℝ) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y (LinearMap.toContinuousLinearMap (continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z y).toLinearMap)) x :=
  h₀.contMDiffAt_of_cayley_eq_sum (b := id) (L := fun i _ => ![J₁ z.2, J₂ z.2] i)
    (a := fun i _ => ![1 - smoothTransition z.1, smoothTransition z.1] i)
    (fun y => Floer.tames_continuationAlmostComplex (h₀.compatibleAt y) z ())
    (fun i _ => by fin_cases i <;> simp [hJ₁, hJ₂])
    (cayley_continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z) contMDiffAt_id (fun _ => contMDiffAt_const)
    (fun i => (![J₁ z.2, J₂ z.2] i).toEndomorphism.contMDiff x)

/-- The **continuation homotopy** of smooth almost complex structures on `M` from the family
`J₁ t` to the family `J₂ t` of `σ`-tame structures, relative to a `σ`-compatible base structure
`J₀`. At `z = (s, t)` it is, on each tangent space, the inverse Cayley transform relative to `J₀`
of `(1 - β(s)) • cayley (J₁ t) + β(s) • cayley (J₂ t)`, where `β` is the smooth transition
function: the linear continuation homotopy `TauCeti.Floer.continuationAlmostComplex`. It is
`J₁ t` for `s ≤ 0` and `J₂ t` for `s ≥ 1`. -/
def continuationAlmostComplex (z : ℝ × ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x => LinearMap.toContinuousLinearMap (continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z x).toLinearMap,
      contMDiffAt_continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the linear fiberwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of the continuation homotopy at `x` is the linear continuation homotopy
there, read as a continuous endomorphism. -/
private theorem continuationAlmostComplex_toEndomorphism (z : ℝ × ℝ) (x : M) :
    (h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z).toEndomorphism x =
      LinearMap.toContinuousLinearMap (continuationAt h₀ J₁ J₂ hJ₁ hJ₂ z x).toLinearMap :=
  (rfl)

/-- On every tangent space, the continuation homotopy is the linear continuation homotopy of the
end structures there, relative to `J₀`. -/
theorem almostComplexStructureAt_continuationAlmostComplex (z : ℝ × ℝ) (x : M) :
    (h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z).almostComplexStructureAt x =
      Floer.continuationAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun t _ => (J₁ t).almostComplexStructureAt x)
        (fun t _ => (J₂ t).almostComplexStructureAt x)
        (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ₁ t) x)
        (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ₂ t) x) z () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    continuationAlmostComplex_toEndomorphism, LinearMap.coe_toContinuousLinearMap, continuationAt]

/-- The continuation homotopy is tamed by `σ`. -/
theorem tames_continuationAlmostComplex (z : ℝ × ℝ) :
    σ.Tames (h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z) := by
  refine h₀.isNondegenerate.tames_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_continuationAlmostComplex]
  exact Floer.tames_continuationAlmostComplex (h₀.compatibleAt x) z ()

/-- On every tangent space, the Cayley coordinate of the continuation homotopy at `z = (s, t)`
relative to `J₀` is `(1 - β(s)) • cayley (J₁ t) + β(s) • cayley (J₂ t)`. This characterizes the
structure, since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_continuationAlmostComplex (z : ℝ × ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z).almostComplexStructureAt x) =
      (1 - smoothTransition z.1) •
          (J₀.almostComplexStructureAt x).cayley ((J₁ z.2).almostComplexStructureAt x) +
        smoothTransition z.1 •
          (J₀.almostComplexStructureAt x).cayley ((J₂ z.2).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_continuationAlmostComplex, Floer.cayley_continuationAlmostComplex]

/-- The continuation homotopy is `σ`-compatible when the two families are. -/
theorem compatible_continuationAlmostComplex (hJ₁c : ∀ t, σ.Compatible (J₁ t))
    (hJ₂c : ∀ t, σ.Compatible (J₂ t)) (z : ℝ × ℝ) :
    σ.Compatible (h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z) := by
  refine h₀.isNondegenerate.compatible_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_continuationAlmostComplex]
  exact Floer.compatible_continuationAlmostComplex (h₀.compatibleAt x)
    (fun t _ => h₀.isNondegenerate.compatible_iff.mp (hJ₁c t) x)
    (fun t _ => h₀.isNondegenerate.compatible_iff.mp (hJ₂c t) x) z ()

/-- The continuation homotopy is `J₁ t` for `s ≤ 0`. -/
@[simp]
theorem continuationAlmostComplex_of_nonpos {z : ℝ × ℝ} (hz : z.1 ≤ 0) :
    h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z = J₁ z.2 :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_continuationAlmostComplex,
      Floer.continuationAlmostComplex_of_nonpos _ hz]

/-- The continuation homotopy is `J₂ t` for `s ≥ 1`. -/
@[simp]
theorem continuationAlmostComplex_of_one_le {z : ℝ × ℝ} (hz : 1 ≤ z.1) :
    h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ z = J₂ z.2 :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_continuationAlmostComplex,
      Floer.continuationAlmostComplex_of_one_le _ hz]

/-- The continuation homotopy from a family to itself is that family at every `s`. -/
@[simp]
theorem continuationAlmostComplex_self (z : ℝ × ℝ) :
    h₀.continuationAlmostComplex J₁ J₁ hJ₁ hJ₁ z = J₁ z.2 :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_continuationAlmostComplex, Floer.continuationAlmostComplex_self]

/-- The continuation homotopy of two families of period one in `t` has period one in `t`. -/
theorem periodic_continuationAlmostComplex (hJ₁p : Periodic J₁ 1) (hJ₂p : Periodic J₂ 1)
    (s : ℝ) : Periodic (fun t => h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (s, t)) 1 :=
  fun t => SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    simp only [almostComplexStructureAt_continuationAlmostComplex]
    exact Floer.periodic_continuationAlmostComplex (h₀.compatibleAt x)
      (fun t => funext fun _ => by rw [hJ₁p t]) (fun t => funext fun _ => by rw [hJ₂p t]) s () t

/-! ### Smoothness -/

section Smooth

variable {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [ENat.LEInfty n]

/-- **The continuation homotopy is smooth along families.** Along families `z y = (s y, t y)` of
parameters and `b y` of points of `M`, the continuation homotopies are `C^n` at `y₀` as sections
of the tangent endomorphism bundle along `b`, provided `b` and `s` are `C^n` at `y₀` and so are the
end structures `J₁ (t y)` and `J₂ (t y)` along `b`. No smoothness of `t` is required, so `t` may
be an angular coordinate when `J₁` and `J₂` have period one. -/
theorem contMDiffAt_continuationAlmostComplex {z : N → ℝ × ℝ} {b : N → M} {y₀ : N}
    (hb : ContMDiffAt I' I n b y₀) (hs : ContMDiffAt I' 𝓘(ℝ) n (fun y => (z y).1) y₀)
    (hJ₁s : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((J₁ (z y).2).toEndomorphism (b y))) y₀)
    (hJ₂s : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((J₂ (z y).2).toEndomorphism (b y))) y₀) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ (z y)).toEndomorphism (b y))) y₀ := by
  simp only [continuationAlmostComplex_toEndomorphism]
  have hβ : ContMDiffAt I' 𝓘(ℝ) n (fun y => smoothTransition (z y).1) y₀ :=
    ((smoothTransition.contDiff (n := ⊤)).of_le ENat.LEInfty.out).contMDiff.contMDiffAt.comp y₀ hs
  refine h₀.contMDiffAt_of_cayley_eq_sum
    (K := fun y => continuationAt h₀ J₁ J₂ hJ₁ hJ₂ (z y) (b y))
    (L := fun i y => ![J₁ (z y).2, J₂ (z y).2] i)
    (a := fun i y => ![1 - smoothTransition (z y).1, smoothTransition (z y).1] i)
    (fun y => Floer.tames_continuationAlmostComplex (h₀.compatibleAt (b y)) _ ())
    (fun i _ => by fin_cases i <;> simp [hJ₁, hJ₂])
    (fun y => cayley_continuationAt h₀ J₁ J₂ hJ₁ hJ₂ _ _) hb (fun i => ?_) (fun i => ?_)
  · fin_cases i
    · exact contMDiffAt_const.sub hβ
    · exact hβ
  · fin_cases i
    · exact hJ₁s
    · exact hJ₂s

/-- **The continuation homotopy is jointly smooth.** For families `J₁ t` and `J₂ t` which are
jointly `C^n` on `ℝ × M` as sections of the tangent endomorphism bundle, the continuation homotopy
is jointly `C^n` in `z = (s, t)` and the point of `M`. -/
theorem contMDiff_continuationAlmostComplex
    (hJ₁s : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₁ p.1).toEndomorphism p.2)))
    (hJ₂s : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J₂ p.1).toEndomorphism p.2))) :
    ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : (ℝ × ℝ) × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((h₀.continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ p.1).toEndomorphism p.2)) := by
  intro p₀
  have hst : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ).prod I) n
      (fun p : (ℝ × ℝ) × M => (p.1.2, p.2)) :=
    (contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  exact h₀.contMDiffAt_continuationAlmostComplex J₁ J₂ hJ₁ hJ₂ contMDiffAt_snd
    ((contDiff_fst.contMDiff.comp contMDiff_fst).contMDiffAt) ((hJ₁s.comp hst).contMDiffAt)
    ((hJ₂s.comp hst).contMDiffAt)

end Smooth

end TauCeti.SmoothTwoForm.Compatible
