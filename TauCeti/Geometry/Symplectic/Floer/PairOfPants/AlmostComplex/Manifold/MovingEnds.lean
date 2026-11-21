/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.MovingEnds
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath

/-!
# Almost complex structures on spheres with moving input ends in a manifold

The associativity of the pair-of-pants product compares the two compositions of two products
through a family of four-punctured spheres whose input punctures move in `ℂ` while the output stays
at `∞`. An input end with center `c i` and nonzero scale `a i` has the end lift
`z ↦ c i + a i φ₀(z)`, where `φ₀` is the end lift of the input end at `0` of `ℂ ∖ {0, 1}`, and the
output end is the end at `∞` of `ℂ ∖ {0, 1}`. Its Hamiltonian perturbations are
`TauCeti.Floer.puncturedSpherePerturbation c a H Hout`, and
`TauCeti.Floer.puncturedSphereAlmostComplex` constructs the matching almost complex structures on
a fixed symplectic vector space. This file constructs them on the tangent bundle of a manifold `M`
with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀`, smooth `σ`-tame structures `J i t` on
the input ends and `Jout t` on the output end, and a configuration whose input discs
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` are pairwise disjoint and lie in the disc `‖w‖ ≤ 2 exp (2π)`.
For `w ∈ ℂ`, the smooth almost complex structure
`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex h₀ J hJ Jout hJout c a hsep hout w`
is, on the tangent space at every point `x`, the linear structure on the sphere with moving input
ends of `J₀ x` and the end structures `J i t x`, `Jout t x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_puncturedSphereAlmostComplex`). Its
Cayley coordinate relative to `J₀` is

`∑ i, β(s_i(w) - 1) • cayley (J i (t_i(w))) + β(-s_∞(w) - 1) • cayley (Jout (t_∞(w)))`,

where `s_i + i t_i` is the end coordinate of the end at `0` at `(w - c i) / a i`, `s_∞ + i t_∞` is
the end coordinate of the end at `∞` at `w`, and `β` is the smooth transition function
(`TauCeti.SmoothTwoForm.Compatible.cayley_puncturedSphereAlmostComplex`). Its smoothness on `M` for
a fixed domain point comes from `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_of_cayley_eq_sum`,
which works in tangent trivializations, applied with the output term written as the Cayley
transform of the negative plane structure.

* It is tame, and compatible when the end structures are.
* Off the input discs it is the negative plane structure of `Jout`
  (`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex`).
* For period-one end structures, it is `J i t` on the part `s ≥ 2` of the input end `i`, in its
  end lift, and `Jout t` on the part `s ≤ -2` of the output end.
* Relabelling the inputs by a bijection does not change it
  (`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_comp_equiv`).
* The pair-of-pants structure is the case of the inputs `0` and `1` with scales `1` and `-1`
  (`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex`).
  The plumbed structure of a composition of two pairs of pants, with the structures of the two
  glued ends replaced by `J₀`, is the case of three input ends (`TauCeti.SmoothTwoForm.Compatible.`
  `plumbedAlmostComplex_update_base_eq_puncturedSphereAlmostComplex`).
* For period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly `C^n` along
  `C^n` families of configurations, domain points and points of `M`, at configurations with nonzero
  scales and domain points other than the centers
  (`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_puncturedSphereAlmostComplex`). Unlike the linear
  construction, which falls back to `J₀` on unseparated configurations, it is only defined on
  separated ones, so no strict separation is needed here.

Along the explicit path of configurations `TauCeti.Floer.associativityCenter f τ`,
`TauCeti.Floer.associativityScale f τ` from `(a ⋆ b) ⋆ c` to `a ⋆ (b ⋆ c)`, whose Hamiltonian
perturbations are smooth with uniformly bounded curvature, the structures are therefore smooth
jointly in the plumbing factor `f`, the parameter `τ`, the domain point and the point of `M`
(`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_puncturedSphereAlmostComplex_associativity`). At
`τ ≤ 0` and at `τ ≥ 1` they are the plumbed structures of the two compositions, with the structures
of the glued ends replaced by `J₀`
(`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_associativity_of_nonpos`,
`TauCeti.SmoothTwoForm.Compatible.puncturedSphereAlmostComplex_associativity_of_one_le`), just as
the perturbations are the plumbed perturbations with the neck Hamiltonian switched off.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product through the family of
  four-punctured spheres between its two degenerations.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  families of punctured surfaces with ends and consistent Floer data over them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
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
  (h₀ : σ.Compatible J₀) {ι : Type*} [Fintype ι]
  (J : ι → ℝ → SmoothAlmostComplexStructure I M) (hJ : ∀ i t, σ.Tames (J i t))
  (Jout : ℝ → SmoothAlmostComplexStructure I M) (hJout : ∀ t, σ.Tames (Jout t))

/-! ### The structure on a separated configuration -/

section Construction

variable (c a : ι → ℂ)

/-- The linear structure on the sphere with moving input ends on the tangent space at `x`. -/
private def puncturedSphereAt (w : ℂ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  Floer.puncturedSphereAlmostComplex (M := Unit) (h₀.compatibleAt x) c a
    (fun i t _ => (J i t).almostComplexStructureAt x)
    (fun t _ => (Jout t).almostComplexStructureAt x) w ()

/-- The weights of the Cayley coordinate, with the output term counted with weight `1` through
the negative plane structure: the cutoff `β(s_i(w) - 1)` of each input `i` and `1` for the
output. -/
private def endWeight (w : ℂ) : Option ι → ℝ
  | none => 1
  | some i => smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1)

/-- The structures whose Cayley transforms the Cayley coordinate combines: the structure `J i` at
the angular coordinate of each input `i`, and the negative plane structure of `Jout` for the
output. -/
private def endStructure (w : ℂ) : Option ι → SmoothAlmostComplexStructure I M
  | none => h₀.negativePlaneAlmostComplex Jout hJout w
  | some i => J i (zero.endCoord ((w - c i) / a i)).im

variable {c a}
  (hsep : Pairwise fun i j =>
    ‖a i‖ * Real.exp (-(2 * π)) / 2 + ‖a j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c i - c j‖)
  (hout : ∀ i, ‖c i‖ + ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))

include hJ hJout hsep hout in
/-- On a separated configuration, the Cayley coordinate of the fiberwise structure is the sum of
the input terms and the Cayley transform of the negative plane structure. -/
private theorem cayley_puncturedSphereAt (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (puncturedSphereAt h₀ J Jout c a w x) =
      ∑ o, endWeight c a w o • (J₀.almostComplexStructureAt x).cayley
        ((endStructure h₀ J Jout hJout c a w o).almostComplexStructureAt x) := by
  rw [puncturedSphereAt, Floer.cayley_puncturedSphereAlmostComplex (h₀.compatibleAt x)
    (fun i t _ => h₀.isNondegenerate.tames_iff.mp (hJ i t) x)
    (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJout t) x) hsep hout w (),
    Floer.puncturedSphereCayley_def, Fintype.sum_option, add_comm]
  simp [endWeight, endStructure]

include hJ hJout hsep hout in
/-- The fiberwise structure is smooth on `M` for a fixed domain point. -/
private theorem contMDiffAt_puncturedSphereAt (w : ℂ) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y (LinearMap.toContinuousLinearMap (puncturedSphereAt h₀ J Jout c a w y).toLinearMap)) x :=
  h₀.contMDiffAt_of_cayley_eq_sum (b := id)
    (L := fun o _ => endStructure h₀ J Jout hJout c a w o) (a := fun o _ => endWeight c a w o)
    (fun y => Floer.tames_puncturedSphereAlmostComplex (h₀.compatibleAt y) w ())
    (fun o _ => by cases o <;> simp [endStructure, hJ, tames_negativePlaneAlmostComplex])
    (cayley_puncturedSphereAt h₀ J hJ Jout hJout hsep hout w) contMDiffAt_id
    (fun _ => contMDiffAt_const)
    (fun o => (endStructure h₀ J Jout hJout c a w o).toEndomorphism.contMDiff x)

include hJ hJout hsep hout in
variable (c a) in
/-- **The almost complex structure on a sphere with moving input ends, in a manifold.** For a
configuration of input ends with centers `c i` and scales `a i` whose discs
`‖w - c i‖ < ‖a i‖ exp (-2π) / 2` are pairwise disjoint (`hsep`) and lie in the disc
`‖w‖ ≤ 2 exp (2π)` (`hout`), smooth `σ`-tame structures `J i t` on the input ends and `Jout t` on
the output end at `∞`, and a `σ`-compatible base structure `J₀`: the smooth structure which on
every tangent space is the linear structure `TauCeti.Floer.puncturedSphereAlmostComplex` of the
fiberwise data. -/
def puncturedSphereAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x => LinearMap.toContinuousLinearMap (puncturedSphereAt h₀ J Jout c a w x).toLinearMap,
      contMDiffAt_puncturedSphereAt h₀ J hJ Jout hJout hsep hout w⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the linear fiberwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of the structure at `x` is the linear fiberwise structure there, read as a
continuous endomorphism. -/
private theorem puncturedSphereAlmostComplex_toEndomorphism (w : ℂ) (x : M) :
    (h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w).toEndomorphism x =
      LinearMap.toContinuousLinearMap (puncturedSphereAt h₀ J Jout c a w x).toLinearMap :=
  (rfl)

/-- The value on a tangent fiber is precisely the linear structure on the sphere with moving input
ends there. -/
theorem almostComplexStructureAt_puncturedSphereAlmostComplex (w : ℂ) (x : M) :
    (h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w).almostComplexStructureAt x =
      Floer.puncturedSphereAlmostComplex (M := Unit) (h₀.compatibleAt x) c a
        (fun i t _ => (J i t).almostComplexStructureAt x)
        (fun t _ => (Jout t).almostComplexStructureAt x) w () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    puncturedSphereAlmostComplex_toEndomorphism, LinearMap.coe_toContinuousLinearMap,
    puncturedSphereAt]

/-- The structure on a sphere with moving input ends is tamed by `σ`. -/
theorem tames_puncturedSphereAlmostComplex (w : ℂ) :
    σ.Tames (h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w) := by
  refine h₀.isNondegenerate.tames_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_puncturedSphereAlmostComplex]
  exact Floer.tames_puncturedSphereAlmostComplex (h₀.compatibleAt x) w ()

/-- The structure on a sphere with moving input ends is `σ`-compatible when the end structures
are. -/
theorem compatible_puncturedSphereAlmostComplex (hJc : ∀ i t, σ.Compatible (J i t))
    (hJoutc : ∀ t, σ.Compatible (Jout t)) (w : ℂ) :
    σ.Compatible (h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w) := by
  refine h₀.isNondegenerate.compatible_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_puncturedSphereAlmostComplex]
  exact Floer.compatible_puncturedSphereAlmostComplex (h₀.compatibleAt x)
    (fun i t _ => h₀.isNondegenerate.compatible_iff.mp (hJc i t) x)
    (fun t _ => h₀.isNondegenerate.compatible_iff.mp (hJoutc t) x) w ()

/-- On every tangent fiber, the Cayley coordinate of the structure relative to `J₀` is
`∑ i, β(s_i(w) - 1) • cayley (J i (t_i(w))) + β(-s_∞(w) - 1) • cayley (Jout (t_∞(w)))`. This
characterizes the structure, since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_puncturedSphereAlmostComplex (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w).almostComplexStructureAt
          x) =
      ∑ i, smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((J i (zero.endCoord ((w - c i) / a i)).im).almostComplexStructureAt x) +
        smoothTransition (-(inf.endCoord w).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((Jout (inf.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_puncturedSphereAlmostComplex,
    Floer.cayley_puncturedSphereAlmostComplex (h₀.compatibleAt x)
      (fun i t _ => h₀.isNondegenerate.tames_iff.mp (hJ i t) x)
      (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJout t) x) hsep hout w (),
    Floer.puncturedSphereCayley_def]

/-- **Off the input discs the structure is the negative plane structure.** At a point outside the
discs `‖w - c i‖ < ‖a i‖ exp (-2π) / 2`, the structure is the negative plane structure of the
output structures. In particular it is `J₀` there if moreover `‖w‖ ≤ 2 exp (2π)`
(`TauCeti.SmoothTwoForm.Compatible.negativePlaneAlmostComplex_eq_of_norm_le`). -/
theorem puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex {w : ℂ}
    (hw : ∀ i, ‖a i‖ * Real.exp (-(2 * π)) / 2 ≤ ‖w - c i‖) :
    h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w =
      h₀.negativePlaneAlmostComplex Jout hJout w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_puncturedSphereAlmostComplex,
      almostComplexStructureAt_negativePlaneAlmostComplex]
    exact Floer.puncturedSphereAlmostComplex_eq_negativePlaneAlmostComplex (h₀.compatibleAt x)
      (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJout t) x) hw ()

/-- **The structure is `J i t` far out on each input end.** If `J i` has period one in `t`, then on
the part `s ≥ 2` of the input end `i` the structure at the point `c i + a i φ₀(z)` with end
coordinates `z = s + i t` is `J i t`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift {i : ι} (hJp : Periodic (J i) 1)
    (ha : a i ≠ 0) {z : ℂ} (hz : 2 ≤ z.re) :
    h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout
        (c i + a i * zero.cylindricalEndLift z) = J i z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_puncturedSphereAlmostComplex]
    exact Floer.puncturedSphereAlmostComplex_cylindricalEndLift (h₀.compatibleAt x) hsep hout
      (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ i t) x) (fun t => by simp only [hJp t]) ha
      hz ()

/-- **The structure is `Jout t` far out on the output end.** If `Jout` has period one in `t`, then
on the part `s ≤ -2` of the output end the structure at the point with end coordinates
`z = s + i t` is `Jout t`. -/
theorem puncturedSphereAlmostComplex_cylindricalEndLift_inf (hJoutp : Periodic Jout 1) {z : ℂ}
    (hz : z.re ≤ -2) :
    h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout (inf.cylindricalEndLift z) =
      Jout z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_puncturedSphereAlmostComplex]
    exact Floer.puncturedSphereAlmostComplex_cylindricalEndLift_inf (h₀.compatibleAt x)
      (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJout t) x) hout
      (fun t => by simp only [hJoutp t]) hz ()

/-- **Relabelling the inputs does not change the structure.** Listing the input ends in another
order, through a bijection `e : κ ≃ ι`, gives the same structure. -/
theorem puncturedSphereAlmostComplex_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (w : ℂ) :
    h₀.puncturedSphereAlmostComplex (J ∘ e) (fun k t => hJ (e k) t) Jout hJout (c ∘ e) (a ∘ e)
        (hsep.comp_of_injective e.injective) (fun k => hout (e k)) w =
      h₀.puncturedSphereAlmostComplex J hJ Jout hJout c a hsep hout w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x =>
    (h₀.compatibleAt x).eq_of_cayley_eq
      (h₀.isNondegenerate.tames_iff.mp (tames_puncturedSphereAlmostComplex h₀ _ _ _ _ _ _ w) x)
      (h₀.isNondegenerate.tames_iff.mp (tames_puncturedSphereAlmostComplex h₀ _ _ _ _ _ _ w) x)
      (by
        rw [cayley_puncturedSphereAlmostComplex, cayley_puncturedSphereAlmostComplex]
        congr 1
        exact e.sum_comp fun i => smoothTransition ((zero.endCoord ((w - c i) / a i)).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((J i (zero.endCoord ((w - c i) / a i)).im).almostComplexStructureAt x))

end Construction

/-! ### Pairs of pants and plumbed pairs of pants as spheres with moving input ends -/

section PairOfPants

/-- **The pair of pants has two input ends.** The pair-of-pants structure is the structure on the
sphere with the input ends of centers `0` and `1` and scales `1` and `-1`, with the structures of
the two inputs, and with its output structure. -/
theorem puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex
    (J : Puncture → ℝ → SmoothAlmostComplexStructure I M) (hJ : ∀ q t, σ.Tames (J q t))
    (hsep : Pairwise fun i j => ‖(![1, -1] : Fin 2 → ℂ) i‖ * Real.exp (-(2 * π)) / 2 +
      ‖(![1, -1] : Fin 2 → ℂ) j‖ * Real.exp (-(2 * π)) / 2 ≤
        ‖(![0, 1] : Fin 2 → ℂ) i - (![0, 1] : Fin 2 → ℂ) j‖)
    (hout : ∀ i, ‖(![0, 1] : Fin 2 → ℂ) i‖ + ‖(![1, -1] : Fin 2 → ℂ) i‖ * Real.exp (-(2 * π)) / 2 ≤
      2 * Real.exp (2 * π))
    (w : ThricePuncturedSphere) :
    h₀.puncturedSphereAlmostComplex ![J zero, J one] (fun i => by fin_cases i <;> exact hJ _)
        (J inf) (hJ inf) ![0, 1] ![1, -1] hsep hout w =
      h₀.pairOfPantsAlmostComplex J hJ w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_puncturedSphereAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex,
      ← Floer.puncturedSphereAlmostComplex_eq_pairOfPantsAlmostComplex (h₀.compatibleAt x)]
    congr 1
    funext i
    fin_cases i <;> simp

/-- On a tangent fiber, the plumbed structure with the structures of the two glued ends replaced by
`J₀` is the linear structure on the sphere with the three input ends of the composition. -/
private theorem almostComplexStructureAt_plumbedAlmostComplex_update_base
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} {q r : Puncture} (hq : q ≠ inf)
    (hrq : r ≠ q) (hr : r ≠ inf) {L : ℝ} (hL : 0 ≤ L)
    (hJa : ∀ p t, σ.Tames (update Ja inf (fun _ => J₀) p t))
    (hJb : ∀ p t, σ.Tames (update Jb q (fun _ => J₀) p t))
    {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    (h₀.plumbedAlmostComplex h₀ (update Ja inf fun _ => J₀) (update Jb q fun _ => J₀) hJa hJb q L
        w hw).almostComplexStructureAt x =
      Floer.puncturedSphereAlmostComplex (M := Unit) (h₀.compatibleAt x)
        ![q.endCenter, q.plumbingMap L 1, r.endCenter]
        ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale]
        ![fun t _ => (Ja zero t).almostComplexStructureAt x,
          fun t _ => (Ja one t).almostComplexStructureAt x,
          fun t _ => (Jb r t).almostComplexStructureAt x]
        (fun t _ => (Jb inf t).almostComplexStructureAt x) w () := by
  have key := congrFun (congrFun
    (Floer.plumbedAlmostComplex_update_base_eq_puncturedSphereAlmostComplex (h₀.compatibleAt x)
      (Ja := fun p t (_ : Unit) => (Ja p t).almostComplexStructureAt x)
      (Jb := fun p t (_ : Unit) => (Jb p t).almostComplexStructureAt x) hq hrq hr hL
      (by simpa [← SmoothAlmostComplexStructure.almostComplexStructureAt_update] using
        fun p t (_ : Unit) => h₀.isNondegenerate.tames_iff.mp (hJa p t) x)
      (by simpa [← SmoothAlmostComplexStructure.almostComplexStructureAt_update] using
        fun p t (_ : Unit) => h₀.isNondegenerate.tames_iff.mp (hJb p t) x)) w) ()
  rw [almostComplexStructureAt_plumbedAlmostComplex]
  convert key using 2
  · exact SmoothAlmostComplexStructure.almostComplexStructureAt_update Ja inf _ x
  · exact SmoothAlmostComplexStructure.almostComplexStructureAt_update Jb q _ x

/-- **With the neck structure switched off, the plumbed sphere has moving input ends.** Plumb the
output end of a pair of pants with end structures `Ja` into the input end `q ≠ ∞` of one with end
structures `Jb`, along a neck of length `L ≥ 0`, over the same base structure `J₀`, with the
structures of the two glued ends replaced by `J₀`. On the four-punctured sphere the plumbed
structure (`TauCeti.SmoothTwoForm.Compatible.plumbedAlmostComplex`) is the structure on the sphere
with the three input ends of centers `c_q`, `ψ(1)` and `c_r`, scales `f`, `-f` and `2 b_r`, and
structures `Ja 0`, `Ja 1` and `Jb r`, and with output structure `Jb ∞`. Here `r` is the other
input, `ψ` the plumbing map, `f` the plumbing factor and `b_r` the scale of the end `r`. This is the
counterpart for almost complex structures of
`TauCeti.Floer.plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`. -/
theorem plumbedAlmostComplex_update_base_eq_puncturedSphereAlmostComplex
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M} {q r : Puncture} (hq : q ≠ inf)
    (hrq : r ≠ q) (hr : r ≠ inf) {L : ℝ} (hL : 0 ≤ L)
    (hJa : ∀ p t, σ.Tames (update Ja inf (fun _ => J₀) p t))
    (hJb : ∀ p t, σ.Tames (update Jb q (fun _ => J₀) p t))
    (hsep : Pairwise fun i j =>
      ‖(![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] : Fin 3 → ℂ) i‖ *
          Real.exp (-(2 * π)) / 2 +
        ‖(![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] : Fin 3 → ℂ) j‖ *
          Real.exp (-(2 * π)) / 2 ≤
        ‖(![q.endCenter, q.plumbingMap L 1, r.endCenter] : Fin 3 → ℂ) i -
          (![q.endCenter, q.plumbingMap L 1, r.endCenter] : Fin 3 → ℂ) j‖)
    (hout : ∀ i, ‖(![q.endCenter, q.plumbingMap L 1, r.endCenter] : Fin 3 → ℂ) i‖ +
      ‖(![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] : Fin 3 → ℂ) i‖ *
        Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    h₀.plumbedAlmostComplex h₀ (update Ja inf fun _ => J₀) (update Jb q fun _ => J₀) hJa hJb q L
        w hw =
      h₀.puncturedSphereAlmostComplex ![Ja zero, Ja one, Jb r]
        (fun i t => by
          fin_cases i
          exacts [by simpa using hJa zero t, by simpa using hJa one t,
            by simpa [update_of_ne hrq] using hJb r t])
        (Jb inf) (fun t => by simpa [update_of_ne hq.symm] using hJb inf t)
        ![q.endCenter, q.plumbingMap L 1, r.endCenter]
        ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] hsep hout w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_plumbedAlmostComplex_update_base h₀ hq hrq hr hL hJa hJb hw,
      almostComplexStructureAt_puncturedSphereAlmostComplex]
    congr 1
    funext i
    fin_cases i <;> rfl

end PairOfPants

/-! ### Smoothness -/

section Smooth

variable {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

/-- **The structure is smooth in the configuration.** Let `J i` and `Jout` be families of `σ`-tame
structures which have period one in `t` and are jointly `C^n` on `ℝ × M`. Along families of
separated configurations `(c y, a y)`, domain points `f y` and points `b y` of `M`, the structures
on the spheres with moving input ends are `C^n` at `y₀` as sections of the tangent endomorphism
bundle along `b`, provided the families are `C^n` at `y₀`, the scales do not vanish at `y₀` and the
domain point is not a center there. -/
theorem contMDiffAt_puncturedSphereAlmostComplex {n : ℕ∞ω} [ENat.LEInfty n]
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J i p.1).toEndomorphism p.2)))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Jout p.1).toEndomorphism p.2)))
    {c a : N → ι → ℂ} {f : N → ℂ} {b : N → M} {y₀ : N}
    (hsep : ∀ y, Pairwise fun i j =>
      ‖a y i‖ * Real.exp (-(2 * π)) / 2 + ‖a y j‖ * Real.exp (-(2 * π)) / 2 ≤ ‖c y i - c y j‖)
    (hout : ∀ y i, ‖c y i‖ + ‖a y i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    (hc : ContMDiffAt I' 𝓘(ℝ, ι → ℂ) n c y₀) (ha : ContMDiffAt I' 𝓘(ℝ, ι → ℂ) n a y₀)
    (hf : ContMDiffAt I' 𝓘(ℝ, ℂ) n f y₀) (hb : ContMDiffAt I' I n b y₀)
    (ha₀ : ∀ i, a y₀ i ≠ 0) (hf₀ : ∀ i, f y₀ ≠ c y₀ i) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.puncturedSphereAlmostComplex J hJ Jout hJout (c y) (a y) (hsep y) (hout y)
          (f y)).toEndomorphism (b y))) y₀ := by
  simp only [puncturedSphereAlmostComplex_toEndomorphism]
  -- The end coordinate `(w - c i) / a i` of each input is smooth at `y₀` and avoids the center.
  have hv (i : ι) : ContMDiffAt I' 𝓘(ℝ, ℂ) n (fun y => (f y - c y i) / a y i) y₀ :=
    (contDiffAt_sub_div (ha₀ i) (f y₀)).comp_contMDiffAt (x := y₀)
      (((contMDiffAt_pi_module_iff.1 hc i).prodMk_space
        (contMDiffAt_pi_module_iff.1 ha i)).prodMk_space hf)
  have hv₀ (i : ι) : (f y₀ - c y₀ i) / a y₀ i ≠ zero.endCenter := by
    simpa using div_ne_zero (sub_ne_zero.2 (hf₀ i)) (ha₀ i)
  refine h₀.contMDiffAt_of_cayley_eq_sum (b := b)
    (L := fun o y => endStructure h₀ J Jout hJout (c y) (a y) (f y) o)
    (a := fun o y => endWeight (c y) (a y) (f y) o)
    (fun y => Floer.tames_puncturedSphereAlmostComplex (h₀.compatibleAt (b y)) _ ())
    (fun o _ => by cases o <;> simp [endStructure, hJ, tames_negativePlaneAlmostComplex])
    (fun y => cayley_puncturedSphereAt h₀ J hJ Jout hJout (hsep y) (hout y) (f y) (b y)) hb ?_ ?_
  · rintro (_ | i)
    · exact contMDiffAt_const
    · simpa [endWeight] using
        Floer.contMDiffAt_smoothTransition_endCoord_comp zero (hv i) contMDiffAt_const (hv₀ i)
  · rintro (_ | i)
    · -- The output term is the negative plane structure, smooth on the whole plane.
      exact (h₀.contMDiff_negativePlaneAlmostComplex Jout hJout hJoutp hJouts contMDiff_fst
        contMDiff_snd).contMDiffAt.comp y₀ (hf.prodMk hb)
    · exact zero.contMDiffAt_toEndomorphism_comp_im_endCoord (hJp i) (hJs i) (hv i) hb (hv₀ i)

end Smooth

/-! ### The associativity path -/

section Associativity

/-- **At its start the family is the composition `(a ⋆ b) ⋆ c`.** For `τ ≤ 0` and the plumbing
factor `f = exp (-2πL) / 4` of a neck length `L ≥ 0`, the structure on the sphere with the input
ends of the associativity path is the plumbed structure of the output end of a pair of pants with
end structures `Ja` glued into the input end `0` of one with end structures `Jb`, with the
structures of the two glued ends replaced by `J₀`. This is the counterpart for almost complex
structures of `TauCeti.Floer.puncturedSpherePerturbation_associativity_of_nonpos`. -/
theorem puncturedSphereAlmostComplex_associativity_of_nonpos {τ L : ℝ} (hτ : τ ≤ 0) (hL : 0 ≤ L)
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M}
    (hJa : ∀ p t, σ.Tames (update Ja inf (fun _ => J₀) p t))
    (hJb : ∀ p t, σ.Tames (update Jb zero (fun _ => J₀) p t))
    {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ zero.plumbingMap L 1) :
    h₀.puncturedSphereAlmostComplex ![Ja zero, Ja one, Jb one]
        (fun i t => by
          fin_cases i
          exacts [by simpa using hJa zero t, by simpa using hJa one t, by simpa using hJb one t])
        (Jb inf) (fun t => by simpa using hJb inf t)
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
        (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w =
      h₀.plumbedAlmostComplex h₀ (update Ja inf fun _ => J₀) (update Jb zero fun _ => J₀) hJa hJb
        zero L w hw :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_plumbedAlmostComplex_update_base h₀ (r := one) (by simp) (by simp)
      (by simp) hL hJa hJb hw, almostComplexStructureAt_puncturedSphereAlmostComplex,
      Floer.associativityCenter_eq_plumbingMap_of_nonpos hτ,
      Floer.associativityScale_eq_plumbingFactor_of_nonpos hτ]
    -- The configurations agree; it remains to match the end structures entry by entry.
    congr 1
    funext i
    fin_cases i <;> rfl

/-- **At its end the family is the composition `a ⋆ (b ⋆ c)`.** For `τ ≥ 1` and the plumbing
factor `f = exp (-2πL) / 4` of a neck length `L ≥ 0`, the structure on the sphere with the input
ends of the associativity path is the plumbed structure of the output end of a pair of pants with
end structures `Ja` glued into the input end `1` of one with end structures `Jb`, with the
structures of the two glued ends replaced by `J₀`. The inputs `a`, `b`, `c` carry the structures
`Jb 0`, `Ja 0`, `Ja 1`. This is the counterpart for almost complex structures of
`TauCeti.Floer.puncturedSpherePerturbation_associativity_of_one_le`. -/
theorem puncturedSphereAlmostComplex_associativity_of_one_le {τ L : ℝ} (hτ : 1 ≤ τ) (hL : 0 ≤ L)
    {Ja Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M}
    (hJa : ∀ p t, σ.Tames (update Ja inf (fun _ => J₀) p t))
    (hJb : ∀ p t, σ.Tames (update Jb one (fun _ => J₀) p t))
    {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ one.plumbingMap L 1) :
    h₀.puncturedSphereAlmostComplex ![Jb zero, Ja zero, Ja one]
        (fun i t => by
          fin_cases i
          exacts [by simpa using hJb zero t, by simpa using hJa zero t, by simpa using hJa one t])
        (Jb inf) (fun t => by simpa using hJb inf t)
        (Floer.associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.associativityScale (Real.exp (-(2 * π * L)) / 4) τ)
        (Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub_of_nonneg hL τ)
        (Floer.norm_associativityCenter_add_mul_exp_le_of_nonneg hL τ) w =
      h₀.plumbedAlmostComplex h₀ (update Ja inf fun _ => J₀) (update Jb one fun _ => J₀) hJa hJb
        one L w hw :=
  -- The two structures list the same three input ends in the orders `a, b, c` and `b, c, a`.
  (h₀.puncturedSphereAlmostComplex_comp_equiv _ _ _ _ _ _ (finRotate 3) w).symm.trans <|
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_plumbedAlmostComplex_update_base h₀ (r := zero) (by simp)
      (by simp) (by simp) hL hJa hJb hw, almostComplexStructureAt_puncturedSphereAlmostComplex,
      Floer.associativityCenter_comp_finRotate_of_one_le hτ,
      Floer.associativityScale_comp_finRotate_of_one_le hτ]
    -- The configurations agree; it remains to match the end structures entry by entry.
    congr 1
    funext i
    fin_cases i <;> simp

variable {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

/-- **The structures along the associativity path form a smooth family.** For input and output
structures which have period one in `t` and are jointly `C^n` on `ℝ × M`, the structure on the
sphere with the input ends of the associativity path is `C^n` jointly in the plumbing factor `f`,
the parameter `τ`, the domain point and the point of `M`, as a section of the tangent endomorphism
bundle, at every `f > 0` and every domain point other than the three centers. The separation
hypotheses hold for `0 ≤ f` and `3 f ≤ 1`
(`TauCeti.Floer.pairwise_mul_exp_add_le_norm_associativityCenter_sub`,
`TauCeti.Floer.norm_associativityCenter_add_mul_exp_le`). -/
theorem contMDiffAt_puncturedSphereAlmostComplex_associativity {n : ℕ∞ω} [ENat.LEInfty n]
    {J : Fin 3 → ℝ → SmoothAlmostComplexStructure I M} (hJ : ∀ i t, σ.Tames (J i t))
    (hJp : ∀ i, Periodic (J i) 1)
    (hJs : ∀ i, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J i p.1).toEndomorphism p.2)))
    (hJoutp : Periodic Jout 1)
    (hJouts : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Jout p.1).toEndomorphism p.2)))
    {f τ : N → ℝ} {g : N → ℂ} {b : N → M} {y₀ : N}
    (hsep : ∀ y, Pairwise fun i j =>
      ‖Floer.associativityScale (f y) (τ y) i‖ * Real.exp (-(2 * π)) / 2 +
        ‖Floer.associativityScale (f y) (τ y) j‖ * Real.exp (-(2 * π)) / 2 ≤
        ‖Floer.associativityCenter (f y) (τ y) i - Floer.associativityCenter (f y) (τ y) j‖)
    (hout : ∀ y i, ‖Floer.associativityCenter (f y) (τ y) i‖ +
      ‖Floer.associativityScale (f y) (τ y) i‖ * Real.exp (-(2 * π)) / 2 ≤ 2 * Real.exp (2 * π))
    (hfs : ContMDiffAt I' 𝓘(ℝ) n f y₀) (hτ : ContMDiffAt I' 𝓘(ℝ) n τ y₀)
    (hg : ContMDiffAt I' 𝓘(ℝ, ℂ) n g y₀) (hb : ContMDiffAt I' I n b y₀) (hf₀ : 0 < f y₀)
    (hg₀ : ∀ i, g y₀ ≠ Floer.associativityCenter (f y₀) (τ y₀) i) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.puncturedSphereAlmostComplex J hJ Jout hJout
          (Floer.associativityCenter (f y) (τ y)) (Floer.associativityScale (f y) (τ y)) (hsep y)
          (hout y) (g y)).toEndomorphism (b y))) y₀ := by
  have hfτ : ContMDiffAt I' 𝓘(ℝ, ℝ × ℝ) n (fun y => (f y, τ y)) y₀ := hfs.prodMk_space hτ
  exact h₀.contMDiffAt_puncturedSphereAlmostComplex J hJ Jout hJout hJp hJs hJoutp hJouts
    (c := fun y => Floer.associativityCenter (f y) (τ y))
    (a := fun y => Floer.associativityScale (f y) (τ y)) hsep hout
    ((((Floer.contDiff_uncurry_associativityCenter (n := ⊤)).of_le
      ENat.LEInfty.out).contMDiff.contMDiffAt).comp y₀ hfτ)
    ((((Floer.contDiff_uncurry_associativityScale (n := ⊤)).of_le
      ENat.LEInfty.out).contMDiff.contMDiffAt).comp y₀ hfτ) hg hb
    (Floer.associativityScale_ne_zero hf₀ (τ y₀)) hg₀

end Associativity

end TauCeti.SmoothTwoForm.Compatible
