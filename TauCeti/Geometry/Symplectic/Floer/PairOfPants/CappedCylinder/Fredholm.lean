/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation.SobolevRealization
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder.SemiFredholm

/-!
# The linearized operator of the pair of pants capped at `1` is Fredholm

Plumbing the negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of
pants `ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L > 4`, gives a
Floer datum on the standard cylinder, with components `TauCeti.Floer.cappedCylinderComponent Hb L 1`
and `TauCeti.Floer.cappedCylinderComponent Hb L Complex.I`
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder`). It is `H_∞(t) dt` far out on the
negative end and `H_0(t) dt` far out on the positive end. The unit property of the pair-of-pants
product compares the rigid cylinders of this datum with the rigid continuation cylinders with the
same end Hamiltonians: in the unit homotopies of `TauCeti.Geometry.Symplectic.Floer.Cap.Unit`, the
product with the unit and the continuation map are the two ends of one family of counts.

Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, and let `J` be `C¹` almost complex structures on the cylinder, compatible with `ω`
and cylindrical on the ends. Along a `C¹` map `u` asymptotic to nondegenerate one-periodic orbits
`x₋` of `H_∞` and `x₊` of `H_0`, this file proves:

* the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator of
  the capped datum is Fredholm
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_cappedCylinderComponent`);
* its index is the index along `u` of the linearized operator of the continuation datum
  `TauCeti.Floer.continuationHomotopy H_∞ H_0`, which is `H_∞` near `-∞` and `H_0` near `+∞`, for
  any compatible almost complex structures of the continuation datum
  (`index_floerSobolevOperator_cappedCylinderComponent_eq_continuationHomotopy`). In particular it
  does not depend on the neck length `L`, on the Hamiltonian `H_1` of the capped end or on `J`;
* when `H_∞ = H_0` and `u` runs from an orbit to itself, its index is zero
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_cappedCylinderComponent_eq_zero`), the case
  of the unit on a single complex, where the continuation map is replaced by the identity.

The capped datum is cylindrical near the ends
(`TauCeti.Floer.isCylindricalNearEnds_cappedCylinderComponent`), and the Fredholm property and
the index of such data on the cylinder depend only on the end Hamiltonians and the asymptotic
orbits (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible`,
`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_cylindrical_data`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
-/

public section

open Set Filter Function
open scoped NNReal Manifold
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- **The linearized operator of the pair of pants capped at `1` is Fredholm.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let
`Hb r` be jointly `C²` Hamiltonians of period one in `t`, with `Hb 0` and `Hb ∞` jointly `C³` and
their suspended vector fields globally Lipschitz, and let `L > 4`. Let `J(z)` be `C¹` almost complex
structures on the cylinder, compatible with `ω`, equal to `Jp_t` for `s ≥ R` and to `Jm_t` for
`s ≤ -R`. Let `u` be a `C¹` map whose loops converge uniformly to a one-periodic orbit `xm` of
`Hb ∞` at `-∞` and to a one-periodic orbit `xp` of `Hb 0` at `+∞`, starting at nondegenerate fixed
points of the time-one maps, with slice defects tending uniformly to zero at the corresponding
ends. Then the realization `D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer
operator of `J` and of the datum of the pair of pants with Hamiltonians `Hb` capped at `1` along a
neck of length `L` is Fredholm. -/
theorem isFredholm_floerSobolevOperator_cappedCylinderComponent (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hb : Puncture → ℝ → F → ℝ}
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r)))
    (hHinf : ContDiff ℝ 3 (uncurry (Hb inf))) (hHzero : ContDiff ℝ 3 (uncurry (Hb zero))) {L : ℝ}
    (hL : 4 < L) {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension (Hb inf)))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension (Hb zero))) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hb inf t) (xm t)) t)
    (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb inf) hXm 0 1)
      (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hb zero t) (xp t)) t)
    (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb zero) hXp 0 1)
      (xp 0))
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {J : ℝ × ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ z y, ω.Compatible (J z y)) {R : ℝ} (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t)
    (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t) {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).IsFredholm :=
  ω.isFredholm_floerSobolevOperator_of_cylindrical_of_compatible hω
    (isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL (fun _ ↦ hJ.contDiffAt) hJRp hJRm)
    hJ (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1)
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I) hJc hu hXm hHinf
    (hHb inf) hxm hxmper hndm huxm hδm hXp hHzero (hHb zero) hxp hxpper hndp huxp hδp

/-- **The pair of pants capped at `1` has the index of the continuation cylinders.** Under the
hypotheses of `TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_cappedCylinderComponent`,
let `J'₋` and `J'₊` be `C¹` families of `ω`-compatible almost complex structures. Then the index of
the realization `D_u` of the linearized Floer operator of the pair of pants capped at `1` is the
index along `u` of the linearized Floer operator of the continuation datum
`TauCeti.Floer.continuationHomotopy (Hb ∞) (Hb 0)`, which is `Hb ∞` near `-∞` and `Hb 0` near `+∞`,
with the almost complex structures `TauCeti.Floer.continuationAlmostComplex h₀ J'₋ J'₊`. In
particular it does not depend on the neck length `L`, on `Hb 1` or on `J`. -/
theorem index_floerSobolevOperator_cappedCylinderComponent_eq_continuationHomotopy
    (ω : SymplecticForm F) (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hb : Puncture → ℝ → F → ℝ}
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r)))
    (hHinf : ContDiff ℝ 3 (uncurry (Hb inf))) (hHzero : ContDiff ℝ 3 (uncurry (Hb zero))) {L : ℝ}
    (hL : 4 < L) {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension (Hb inf)))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension (Hb zero))) {xm xp : ℝ → F}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hb inf t) (xm t)) t)
    (hxmper : Periodic xm 1)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb inf) hXm 0 1)
      (xm 0))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hb zero t) (xp t)) t)
    (hxpper : Periodic xp 1)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb zero) hXp 0 1)
      (xp 0))
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {J : ℝ × ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ z y, ω.Compatible (J z y)) {R : ℝ} (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t)
    (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t) {J₀ : AlmostComplexStructure F}
    (h₀ : ω.Compatible J₀) {Jm' Jp' : ℝ → F → AlmostComplexStructure F}
    {hJmt : ∀ t x, ω.Tames (Jm' t x)} {hJpt : ∀ t x, ω.Tames (Jp' t x)}
    (hJm' : ContDiff ℝ 1 fun p : ℝ × F ↦ (Jm' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp' : ContDiff ℝ 1 fun p : ℝ × F ↦ (Jp' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJmc : ∀ t x, ω.Compatible (Jm' t x)) (hJpc : ∀ t x, ω.Compatible (Jp' t x))
    {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb inf t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).index =
      (ω.floerSobolevOperator
        (fun w y ↦ (continuationAlmostComplex h₀ Jm' Jp' hJmt hJpt w y).toLinearMap
          |>.toContinuousLinearMap)
        (fun _ _ ↦ 0) (continuationHomotopy (Hb inf) (Hb zero)) u).index := by
  let : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  -- Both data are cylindrical near the ends, with the end Hamiltonians `Hb ∞` and `Hb 0`.
  exact index_floerSobolevOperator_eq_of_cylindrical_data ω
    (isCylindricalNearEnds_continuationHomotopy h₀ hJm' hJp' (hHbs inf) (hHbs zero) u)
    (isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL (fun _ ↦ hJ.contDiffAt) hJRp hJRm)
    (contDiff_continuationAlmostComplex h₀ hJm' hJp') contDiff_const
    (contDiff_uncurry_continuationHomotopy (hHbs inf) (hHbs zero)) hJ
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1)
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I)
    (fun _ _ ↦ compatible_continuationAlmostComplex h₀ (hJmc _ _) (hJpc _ _)) hJc hu hXm hxm hndm
    huxm hδm hXp hxp hndp huxp hδp
    (isFredholm_floerSobolevOperator_continuationHomotopy ω hω h₀ hJm' hJp' hJmc hJpc hXm
      hHinf (hHb inf) hXp hHzero (hHb zero) hxm hxmper hndm hxp hxpper hndp hu huxm hδm
      huxp hδp)

/-- **The pair of pants capped at `1` has index zero from an orbit to itself.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let
`Hb r` be jointly `C²` Hamiltonians of period one in `t` with `Hb ∞ = Hb 0`, where `Hb 0` is
jointly `C³` with globally Lipschitz suspended vector field, and let `L > 4`. Let `x` be a
one-periodic orbit of `Hb 0` with `x(0)` a nondegenerate fixed point of the time-one map. Let
`J(z)` be `C¹` almost complex structures on the cylinder, compatible with `ω`, equal to `Jp_t` for
`s ≥ R` and to `Jm_t` for `s ≤ -R`, and let `u` be a `C¹` map whose loops converge uniformly to `x`
at both ends, with slice defects tending uniformly to zero there. Then the realization
`D_u : W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized Floer operator of `J` and of the
datum of the pair of pants with Hamiltonians `Hb` capped at `1` along a neck of length `L` has
index zero. -/
theorem index_floerSobolevOperator_cappedCylinderComponent_eq_zero (ω : SymplecticForm F)
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) {Hb : Puncture → ℝ → F → ℝ}
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 2 (uncurry (Hb r)))
    (hHzero : ContDiff ℝ 3 (uncurry (Hb zero))) (hHb0 : Hb inf = Hb zero) {L : ℝ} (hL : 4 < L)
    {K : ℝ≥0}
    (hX : LipschitzWith K (ω.timeDependentHamiltonianSuspension (Hb zero))) {x : ℝ → F}
    (hx : ∀ t, HasDerivAt x (ω.hamiltonianVectorField (Hb zero t) (x t)) t)
    (hxper : Periodic x 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, F) (ω.timeDependentHamiltonianFlow (Hb zero) hX 0 1)
      (x 0))
    {Jm Jp : ℝ → F → AlmostComplexStructure F} {J : ℝ × ℝ → F → AlmostComplexStructure F}
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × F ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJc : ∀ z y, ω.Compatible (J z y)) {R : ℝ} (hJRp : ∀ s t, R ≤ s → J (s, t) = Jp t)
    (hJRm : ∀ s t, s ≤ -R → J (s, t) = Jm t) {u : ℝ × ℝ → F} (hu : ContDiff ℝ 1 u)
    (hum : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hup : TendstoUniformlyOn (fun s t ↦ u (s, t)) x atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hb zero t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap)
      (cappedCylinderComponent Hb L 1) (cappedCylinderComponent Hb L Complex.I) u).index = 0 := by
  -- The capped datum is cylindrical near the ends with the Hamiltonian `Hb 0` at both ends.
  have hcyl := isCylindricalNearEnds_cappedCylinderComponent hHb hHbs hL
    (fun _ ↦ hJ.contDiffAt) hJRp hJRm (u := u)
  rw [hHb0] at hcyl
  exact index_floerSobolevOperator_eq_zero_of_isNondegenerateFixedPt_of_cylindrical ω hX
    hHzero (hHb zero) hx hxper hu hum hδm hup hδp hcyl hJ
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL 1)
    (contDiff_uncurry_cappedCylinderComponent hHb hHbs hL Complex.I) hJc hω hnd

end TauCeti.SymplecticForm
