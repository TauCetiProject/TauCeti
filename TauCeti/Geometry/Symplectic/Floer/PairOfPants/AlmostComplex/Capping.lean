/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Plumbing

/-!
# Almost complex structures on the negative PSS plane and the capping families

The unit of the pair-of-pants product is the count of *negative planes*: maps from `ℂ` with a
Morse incidence at the pole `0` and a negative (output) cylindrical end at `∞`. Its unit property
is proved with the *capping families*, which glue a negative plane into an input `q ∈ {0, 1}` of
the pair of pants along a neck of length `L`. The Hamiltonian perturbations of these domains are
`TauCeti.Floer.negativePlanePerturbation` and the plumbed perturbations of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping`. This file constructs the matching
domain-dependent almost complex structures.

Fix an `ω`-compatible base structure `J₀` and a family `J(t, x)` of `ω`-tame structures on the
end. The negative plane structure `TauCeti.Floer.negativePlaneAlmostComplex` is the inverse Cayley
transform, relative to `J₀`, of `β(-s(w) - 1) • cayley (J(t(w), x))`, where `(s, t)` are the
coordinates of the end at `∞` of the thrice-punctured sphere and `β` is the smooth transition. It
is the pair-of-pants structure whose two input structures are the base structure `J₀`
(`TauCeti.Floer.pairOfPantsAlmostComplex_update_inf`), and it is `J₀` on the pole disc
`‖w‖ ≤ 2 exp (2π)`. Unlike the pair-of-pants structure, it is therefore smooth on the whole plane,
including the pole `0` and the point `1`.

The capping family at the input `q` is the plumbed structure
`plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (Jb q)) Jb _ _ q L`, which inserts the
negative plane with end structure `Jb q` into the end `q` of the pair of pants with end structures
`Jb`. Both pieces use the same base structure `J₀`: the receiving pair of pants is `J₀` at the
capped puncture `c_q` (`TauCeti.Floer.pairOfPantsAlmostComplex_endCenter`), and the inserted plane
is `J₀` on the image of its pole disc, the disc of radius `exp (-2π(L - 1)) / 2` about `c_q`. So
the capped structure is `J₀` on that disc, and it is smooth on the capped cylinder `ℂ ∖ {c_q'}`,
where `q'` is the other input, jointly in the neck length.

## Main definitions

* `TauCeti.Floer.negativePlaneAlmostComplex h₀ J hJ`: the almost complex structure of the negative
  plane with end structure `J`.

## Main results

* `TauCeti.Floer.tames_negativePlaneAlmostComplex`,
  `TauCeti.Floer.compatible_negativePlaneAlmostComplex`: the plane structure is `ω`-tame, and
  `ω`-compatible when the end structures are.
* `TauCeti.Floer.negativePlaneAlmostComplex_eq_of_norm_le`: it is `J₀` on the pole disc
  `‖w‖ ≤ 2 exp (2π)`.
* `TauCeti.Floer.negativePlaneAlmostComplex_cylindricalEndLift`: if `J` has period one in `t`, it is
  `J(t, x)` on the part `s ≤ -2` of the end.
* `TauCeti.Floer.contMDiff_negativePlaneAlmostComplex`: for a period-one `C^n` family `J`, it is
  `C^n` on all of `ℂ × M`.
* `TauCeti.Floer.plumbedAlmostComplex_update_inf_eq`: the capped structure is `J₀` on the disc of
  radius `exp (-2π(L - 1)) / 2` about the capped puncture.
* `TauCeti.Floer.contMDiffAt_plumbedAlmostComplex_update_inf`: for `L > 4` the capped structure is
  `C^n` jointly in the neck length, the domain point of the capped cylinder and the target point.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps and the unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M V : Type*}

section Algebraic

variable [AddCommGroup V] [Module ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → M → AlmostComplexStructure V}

/-- Families indexed by the ends that are `J` at `∞` and the constant structure `J₀` at the inputs
inherit any property shared by `J` and the constant family. -/
private theorem forall_update_inf {P : (ℝ → M → AlmostComplexStructure V) → Prop}
    (h₀ : P fun _ _ => J₀) (hJ : P J) (q : Puncture) :
    P (update (fun _ _ _ => J₀) inf J q) := by
  rcases eq_or_ne q inf with rfl | hq
  · simpa using hJ
  · simpa [update_of_ne hq] using h₀

/-- The end structures of the negative plane, `J` at `∞` and `J₀` at the inputs, are tame when
`J₀` and `J` are. -/
theorem tames_update_inf (h₀ : ω.Tames J₀) (hJ : ∀ t x, ω.Tames (J t x)) (q : Puncture) (t : ℝ)
    (x : M) : ω.Tames (update (fun _ _ _ => J₀) inf J q t x) :=
  forall_update_inf (P := fun f => ∀ t x, ω.Tames (f t x)) (fun _ _ => h₀) hJ q t x

variable [FiniteDimensional ℝ V]

/-- The domain-dependent almost complex structure on the negative PSS plane with end structure
`J`, relative to an `ω`-compatible base structure `J₀`. At `w ∈ ℂ` and `x ∈ M` it is the inverse
Cayley transform, relative to `J₀`, of `β(-s(w) - 1) • cayley (J (t(w)) x)`, where `(s, t)` are
the coordinates of the end at `∞` of the thrice-punctured sphere, with end lift
`z ↦ 2 exp (-2πz)` on `Re z < 0`, and `β` is the smooth transition function. -/
def negativePlaneAlmostComplex (h₀ : ω.Compatible J₀) (J : ℝ → M → AlmostComplexStructure V)
    (hJ : ∀ t x, ω.Tames (J t x)) (w : ℂ) (x : M) : AlmostComplexStructure V :=
  h₀.cayleyEquiv.symm
    ⟨smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (J (inf.endCoord w).im x),
      h₀.tames.convex_cayleyBall.smul_mem_of_zero_mem h₀.tames.zero_mem_cayleyBall
        (h₀.cayley_mem_cayleyBall (hJ _ x))
        ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩⟩

variable {hJ : ∀ t x, ω.Tames (J t x)}

/-- The negative plane structure is tamed by `ω`. -/
theorem tames_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    ω.Tames (negativePlaneAlmostComplex h₀ J hJ w x) :=
  (h₀.cayleyEquiv.symm _).2

/-- The Cayley transform of the negative plane structure, relative to `J₀`, is
`β(-s(w) - 1) • cayley (J (t(w)) x)`. This characterizes the structure, since the Cayley transform
is injective on tame structures. -/
@[simp]
theorem cayley_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀) (w : ℂ) (x : M) :
    J₀.cayley (negativePlaneAlmostComplex h₀ J hJ w x) =
      smoothTransition (-(inf.endCoord w).re - 1) • J₀.cayley (J (inf.endCoord w).im x) := by
  rw [negativePlaneAlmostComplex, ← h₀.cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- **The plane is a pair of pants with base inputs.** The pair-of-pants structure whose input
structures are the base structure `J₀` and whose output structure is `J` is the negative plane
structure of `J`. -/
@[simp]
theorem pairOfPantsAlmostComplex_update_inf (h₀ : ω.Compatible J₀)
    (hJ' : ∀ q t x, ω.Tames (update (fun _ _ _ => J₀) inf J q t x)) :
    pairOfPantsAlmostComplex h₀ (update (fun _ _ _ => J₀) inf J) hJ' =
      negativePlaneAlmostComplex h₀ J fun t x => by simpa using hJ' inf t x := by
  funext w x
  refine h₀.eq_of_cayley_eq (tames_pairOfPantsAlmostComplex h₀ w x)
    (tames_negativePlaneAlmostComplex h₀ w x) ?_
  rw [cayley_pairOfPantsAlmostComplex, cayley_negativePlaneAlmostComplex,
    Fintype.sum_eq_single inf fun q hq => by
      simp [update_of_ne hq, AlmostComplexStructure.cayley_self]]
  simp

/-- The negative plane structure is `ω`-compatible when the end structures are. -/
theorem compatible_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀)
    (hJc : ∀ t x, ω.Compatible (J t x)) (w : ℂ) (x : M) :
    ω.Compatible (negativePlaneAlmostComplex h₀ J hJ w x) := by
  rw [← pairOfPantsAlmostComplex_update_inf h₀ (tames_update_inf h₀.tames hJ)]
  exact compatible_pairOfPantsAlmostComplex h₀
    (forall_update_inf (P := fun f => ∀ t x, ω.Compatible (f t x)) (fun _ _ => h₀) hJc) w x

/-- **The pole disc.** The negative plane structure is the base structure `J₀` on the disc
`‖w‖ ≤ 2 exp (2π)` about the pole, where the signed longitudinal coordinate `-s` of the end is at
most `1`. -/
theorem negativePlaneAlmostComplex_eq_of_norm_le (h₀ : ω.Compatible J₀) {w : ℂ}
    (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) (x : M) : negativePlaneAlmostComplex h₀ J hJ w x = J₀ := by
  have h := neg_re_endCoord_inf_le zero_le_one (w := w) (by simpa using hw)
  refine h₀.eq_of_cayley_eq (tames_negativePlaneAlmostComplex h₀ w x) h₀.tames ?_
  rw [cayley_negativePlaneAlmostComplex, AlmostComplexStructure.cayley_self,
    smoothTransition.zero_of_nonpos (by linarith), zero_smul]

/-- **The structure on the end.** If `J` has period one in `t`, then on the part `s < 0` of the
end, the Cayley transform of the negative plane structure at the point with end coordinates
`z = s + i t` is `β(-s - 1) • cayley (J t x)`. -/
theorem cayley_negativePlaneAlmostComplex_cylindricalEndLift_of_neg (h₀ : ω.Compatible J₀)
    (hJp : Periodic J 1) {z : ℂ} (hz : z.re < 0) (x : M) :
    J₀.cayley (negativePlaneAlmostComplex h₀ J hJ (inf.cylindricalEndLift z) x) =
      smoothTransition (-z.re - 1) • J₀.cayley (J z.im x) := by
  rw [← pairOfPantsAlmostComplex_update_inf h₀ (tames_update_inf h₀.tames hJ)]
  simpa using cayley_pairOfPantsAlmostComplex_cylindricalEndLift_of_pos (q := inf)
    (hJ := tames_update_inf h₀.tames hJ) h₀ (by simpa using hJp) (z := z) (by simpa using hz) x

/-- **The structure is `J t` far out on the end.** If `J` has period one in `t`, then on the part
`s ≤ -2` of the end, the negative plane structure at the point with end coordinates `z = s + i t`
is `J t x`. -/
theorem negativePlaneAlmostComplex_cylindricalEndLift (h₀ : ω.Compatible J₀) (hJp : Periodic J 1)
    {z : ℂ} (hz : z.re ≤ -2) (x : M) :
    negativePlaneAlmostComplex h₀ J hJ (inf.cylindricalEndLift z) x = J z.im x := by
  rw [← pairOfPantsAlmostComplex_update_inf h₀ (tames_update_inf h₀.tames hJ)]
  simpa using pairOfPantsAlmostComplex_cylindricalEndLift (q := inf)
    (hJ := tames_update_inf h₀.tames hJ) h₀ (by simpa using hJp) (z := z)
    (by simp only [endSign_inf]; linarith) x

/-! ### Capping an input of the pair of pants -/

variable {Jb : Puncture → ℝ → M → AlmostComplexStructure V} {hJb : ∀ r t x, ω.Tames (Jb r t x)}
  {q : Puncture} {hJa : ∀ r t x, ω.Tames (update (fun _ _ _ => J₀) inf (Jb q) r t x)} {L : ℝ}

/-- **The capped disc.** Plumb the negative plane with end structure `Jb q` into the input end
`q` of the pair of pants with end structures `Jb`, along a neck of length `L > 2`, using the same
base structure `J₀` on both pieces. The capped structure is `J₀` on the disc of radius
`exp (-2π(L - 1)) / 2` about the capped puncture `c_q`, the image under the plumbing map of the
pole disc of the plane. -/
theorem plumbedAlmostComplex_update_inf_eq (h₀ : ω.Compatible J₀) (hq : q ≠ inf) (hL : 2 < L)
    {w : ℂ} (hw : ‖w - q.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) (x : M) :
    plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (Jb q)) Jb hJa hJb q L w x = J₀ := by
  rcases eq_or_ne w q.endCenter with rfl | hc
  · -- At the capped puncture itself the structure is that of the receiving pair of pants.
    rw [plumbedAlmostComplex_def, re_endCoord_endCenter, ite_eq_right (by linarith),
      pairOfPantsAlmostComplex_endCenter]
  · -- Elsewhere the point corresponds to a point of the pole disc of the plane.
    have hw' : ‖(w - q.endCenter) / q.plumbingFactor L‖ ≤ 2 * Real.exp (2 * π * 1) :=
      (norm_sub_endCenter_div_plumbingFactor_le_iff hq L 1).2 hw
    have hre := le_re_endCoord_of_norm_sub_endCenter_le hq hc hw
    rw [plumbedAlmostComplex_def, ite_eq_left (by linarith), pairOfPantsAlmostComplex_update_inf,
      negativePlaneAlmostComplex_eq_of_norm_le h₀ (by simpa using hw')]

end Algebraic

section Smooth

/-! ### Smoothness -/

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V} {J : ℝ → M → AlmostComplexStructure V}
  {hJ : ∀ t x, ω.Tames (J t x)}
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- The end structures of the negative plane inherit periodicity and smoothness from `J`. -/
private theorem periodic_and_contMDiff_update_inf {n : ℕ∞} (hJp : Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J p.1 p.2).toLinearMap.toContinuousLinearMap)) (q : Puncture) :
    Periodic (update (fun _ _ _ => J₀) inf J q) 1 ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n (fun p : ℝ × M =>
        (update (fun _ _ _ => J₀) inf J q p.1 p.2).toLinearMap.toContinuousLinearMap) :=
  forall_update_inf (P := fun f => Periodic f 1 ∧ ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
    (fun p : ℝ × M => (f p.1 p.2).toLinearMap.toContinuousLinearMap))
    ⟨fun _ => rfl, contMDiff_const⟩ ⟨hJp, hJs⟩ q

/-- **The plane structure is smooth.** For a family `J` of `ω`-tame structures which has period
one in `t` and is `C^n` on `ℝ × M`, the negative plane structure is `C^n` on `ℂ × M`. Off the open
pole disc it is the pair-of-pants structure with base inputs, and on that disc it is `J₀`. -/
theorem contMDiff_negativePlaneAlmostComplex (h₀ : ω.Compatible J₀) {n : ℕ∞} (hJp : Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (J p.1 p.2).toLinearMap.toContinuousLinearMap)) :
    ContMDiff (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℂ × M =>
        (negativePlaneAlmostComplex h₀ J hJ p.1 p.2).toLinearMap.toContinuousLinearMap) := by
  rintro ⟨w, x⟩
  rcases lt_or_ge ‖w‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- On the open pole disc, the structure is `J₀`.
    refine (contMDiffAt_const (c := J₀.toLinearMap.toContinuousLinearMap)).congr_of_eventuallyEq ?_
    filter_upwards [continuous_fst.norm.continuousAt.eventually (gt_mem_nhds hlt)] with p hp
    rw [negativePlaneAlmostComplex_eq_of_norm_le h₀ hp.le]
  · -- Off it, the point lies in the pair of pants with base inputs.
    have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
    have hw₀ : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hge
      linarith
    have hw₁ : w ≠ 1 := by
      rintro rfl
      rw [norm_one] at hge
      linarith
    rw [← pairOfPantsAlmostComplex_update_inf h₀ (tames_update_inf h₀.tames hJ)]
    exact contMDiffAt_pairOfPantsAlmostComplex h₀
      (fun q => (periodic_and_contMDiff_update_inf hJp hJs q).1)
      (fun q => (periodic_and_contMDiff_update_inf hJp hJs q).2) ⟨w, hw₀, hw₁⟩ x

variable {Jb : Puncture → ℝ → M → AlmostComplexStructure V} {hJb : ∀ r t x, ω.Tames (Jb r t x)}
  {q : Puncture} {hJa : ∀ r t x, ω.Tames (update (fun _ _ _ => J₀) inf (Jb q) r t x)} {L : ℝ}

/-- **The capped structure is smooth.** For families `Jb` of `ω`-tame structures which have period
one in `t` and are `C^n` on `ℝ × M`, and neck length `L > 4`, the structure obtained by plumbing
the negative plane with end structure `Jb q` into the input end `q` of the pair of pants with end
structures `Jb`, over the same base structure `J₀`, is `C^n` jointly in the neck length, the domain
point and the target point, at every domain point which is the capped puncture `c_q` or a point of
`ℂ ∖ {0, 1}`: it is smooth on the capped cylinder `ℂ ∖ {c_q'}`, where `q'` is the other input. -/
theorem contMDiffAt_plumbedAlmostComplex_update_inf (h₀ : ω.Compatible J₀) {n : ℕ∞}
    (hq : q ≠ inf) (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × M => (Jb r p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hL : 4 < L) {w : ℂ} (hw : w = q.endCenter ∨ w ≠ 0 ∧ w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, V →L[ℝ] V) n
      (fun p : ℝ × (ℂ × M) => LinearMap.toContinuousLinearMap
        (plumbedAlmostComplex h₀ h₀ (update (fun _ _ _ => J₀) inf (Jb q)) Jb hJa hJb q p.1 p.2.1
          p.2.2).toLinearMap)
      (L, (w, x)) := by
  set ρ : ℝ → ℝ := fun l => Real.exp (-(2 * π * (l - 1))) / 2
  rcases lt_or_ge ‖w - q.endCenter‖ (ρ L) with hlt | hge
  · -- Near a point of the open capped disc, for nearby neck lengths, the structure is `J₀`.
    refine (contMDiffAt_const (c := J₀.toLinearMap.toContinuousLinearMap)).congr_of_eventuallyEq ?_
    have hdisc : ∀ᶠ p : ℝ × (ℂ × M) in 𝓝 (L, (w, x)), ‖p.2.1 - q.endCenter‖ < ρ p.1 :=
      ((continuous_fst.comp continuous_snd).sub continuous_const).norm.continuousAt.eventually_lt
        ((by fun_prop : Continuous ρ).comp continuous_fst).continuousAt hlt
    have hlen : ∀ᶠ p : ℝ × (ℂ × M) in 𝓝 (L, (w, x)), 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hdisc, hlen] with p hp hp₂
    rw [plumbedAlmostComplex_update_inf_eq h₀ hq hp₂ hp.le]
  · -- Off it, the point lies in the plumbed four-punctured sphere.
    have hc : w ≠ q.endCenter := fun h => by
      rw [h, sub_self, norm_zero] at hge
      exact (by positivity : 0 < ρ L).not_ge hge
    have h₁ : w ≠ q.plumbingMap L 1 := fun h =>
      (h ▸ norm_plumbingMap_one_sub_endCenter_lt hq L).not_ge hge
    have h := periodic_and_contMDiff_update_inf (J₀ := J₀) (hJbp q) (hJbs q)
    exact contMDiffAt_plumbedAlmostComplex h₀ h₀ hq (fun r => (h r).1) hJbp (fun r => (h r).2) hJbs
      (by simp) hL ⟨hw.resolve_left hc, h₁⟩ x

end Smooth

end TauCeti.Floer
