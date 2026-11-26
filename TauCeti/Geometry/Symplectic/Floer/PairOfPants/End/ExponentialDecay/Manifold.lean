/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# Exponential convergence of the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`
equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for `1`-periodic Hamiltonians `H_q`
on `M`, and let `u` be a finite-energy solution of the Floer equation `(du - X_K)^{0,1} = 0`. On a
manifold the ends of `u` converge to `1`-periodic orbits
(`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`). This file shows that, at a
nondegenerate orbit lying in a symplectic chart and for almost complex structures that are
cylindrical on the end, the convergence is exponentially fast in `C¹`, as it is for a symplectic
vector space target (`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.ExponentialDecay`).

The chart is a smooth partial diffeomorphism `φ` from `M` onto an open subset of a
finite-dimensional inner product space `V` with a constant symplectic form `ω₀`, pulling `ω₀` back
to `ω` at the points of a compact set `B ⊆ φ.source` which contains the end of `u`; a Darboux
chart (`TauCeti.SmoothTwoForm.IsSymplectic.exists_darbouxChart`) has this property on its whole
source. The Hamiltonian of the end is read in the chart through a Hamiltonian `H'_q` on `V`, with
`H_q(t) = H'_q(t) ∘ φ` near every point of `B`, and the cylindrical structure
`J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))` through structures `J'_q(t)` on `V` with
`dφ ∘ J_q(t) = J'_q(t) ∘ dφ`. If every `1`-periodic orbit of `H'_q` in `φ(B)` is nondegenerate,
then the end converges to the stationary cylinder of such an orbit `y`:

`‖φ(u(φ_q(±s, t))) - y(t)‖ + ‖d(φ ∘ u ∘ φ_q)(±s, t) - dt ⊗ X_{H'_q(t)}(y(t))‖ ≤ C exp (-κ s)`

for all large `s` and all `t` (`exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart`
in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). When all three ends are cylindrical and
lie in such charts, one rate `κ` and one constant `C` serve for all of them
(`exists_pos_forall_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart`, in the same
namespace).
These are the asymptotic conditions under which an end of a pair of pants in a manifold lies in the
exponentially weighted spaces of the linearized operator, read in the chart, and can be pre-glued
to a Floer cylinder.

**Proof.** In the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)` the end is a finite-energy Floer
half-cylinder for the end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`) with the cylindrical structure `J_q(±t)`
(`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_of_cylindrical`),
read in the chart by `J'_q(±t)` and the end Hamiltonian of `H'_q`. A `1`-periodic orbit `x` of
the latter gives the orbit `t ↦ x(±t)` of `H'_q`, so it is isolated
(`SymplecticForm.exists_pos_forall_eq_of_isNondegenerateFixedPt_positiveEndHamiltonian`) and its
return map fixes no nonzero vector
(`SymplecticForm.eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self`). The `C¹`
decay of Floer half-cylinders in a symplectic chart,
`SmoothTwoForm.IsNondegenerate.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp`,
then applies, and the reflection between the two end charts
(`SymplecticForm.norm_fderiv_comp_endChart_sub_smulRight`) turns its estimate into the one above.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {K : ℂ → M → ℂ →L[ℝ] ℝ}
  {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ} {u : ℝ × ℝ → M}
  {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω₀ : SymplecticForm V} {H' : Puncture → ℝ → V → ℝ}

/-- If every `1`-periodic orbit of `H'_q` in `S` starts at a nondegenerate fixed point of the
time-one map, then so does every `1`-periodic orbit `x` of the positive end Hamiltonian
`±H'_q(±t)` in `S`: `t ↦ x(±t)` is an orbit of `H'_q` in `S` starting at `x(0)`. -/
private theorem isNondegenerateFixedPt_of_positiveEndHamiltonian {q : Puncture} {S : Set V}
    {L : ℝ≥0} {hL : LipschitzWith L (ω₀.timeDependentHamiltonianSuspension (H' q))}
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' q t) (x t)) t) → (∀ t, x t ∈ S) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow (H' q) hL 0 1) (x 0))
    {x : ℝ → V} (hxper : Periodic x 1)
    (hx : ∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (positiveEndHamiltonian H' q t) (x t)) t)
    (hxS : ∀ t, x t ∈ S) :
    IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow (H' q) hL 0 1) (x 0) := by
  simpa only [mul_zero] using hnd (fun t ↦ x (q.endSign * t)) (periodic_comp_endSign_mul hxper)
    (SymplecticForm.hasDerivAt_comp_endSign_mul hx) fun t ↦ hxS _

/-- **The end of a Floer pair of pants in a manifold converges exponentially in `C¹`.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on the end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let
`u` be `C³` on an open set `U`, solving the Floer equation `(du - X_K)^{0,1} = 0` there with finite
energy, where `U` contains the part `±s > a` of the end `q` for some `a ≥ T₀`. Suppose that beyond
`a` the end lies in a compact set `B` and the structure is cylindrical,
`J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))` with `J_q(t, y)` tamed by `ω` on `B`. Let `φ` be a smooth
partial diffeomorphism from `M` to `V` with `B ⊆ φ.source`, pulling `ω₀` back to `ω` on `B`, which
reads `H_q` as a `1`-periodic `C³` Hamiltonian `H'_q` on `V` (`H_q(t) = H'_q(t) ∘ φ` near `B`) and
`J_q` as a `1`-periodic family `J'_q` on `V`, `C²` on an open set `W ⊇ ℝ × φ(B)`. If the suspended
Hamiltonian vector field of `H'_q` is globally Lipschitz and every `1`-periodic orbit of `H'_q` in
`φ(B)` starts at a nondegenerate fixed point of the time-one map, then, read in the chart, the end
converges exponentially fast in `C¹` to the stationary cylinder of a `1`-periodic orbit `y` of
`H'_q`: for some `κ > 0` and `C`, eventually

`‖φ(u(φ_q(±s, t))) - y(t)‖ + ‖d(φ ∘ u ∘ φ_q)(±s, t) - dt ⊗ X_{H'_q(t)}(y(t))‖ ≤ C exp (-κ s)`

for every `t`.

Only the part of `U` along the end matters, so this applies to the ends of other punctured spheres
built from `S`, such as plumbed four-punctured spheres. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_isOpen
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hfloer : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haT : T₀ ≤ a) (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U)
    {B : Set M} (hB : IsCompact B) (huB : ∀ ζ : ℝ × ℝ, a < ζ.1 → u (positiveEndChart q ζ) ∈ B)
    {Jq : ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    (hJ : ∀ s t, a < s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    (hJt : ∀ t, ∀ y ∈ B, (hω.symplecticFormAt y).Tames (Jq t y))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) (hBφ : B ⊆ φ.source)
    (hφ : ∀ y ∈ B, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I φ y v) (mvfderiv I φ y w))
    (hHH' : ∀ t, ∀ y ∈ B, H q t =ᶠ[𝓝 y] H' q t ∘ φ) (hH' : ContDiff ℝ 3 (uncurry (H' q)))
    (hH'per : Periodic (H' q) 1) {J' : ℝ → V → AlmostComplexStructure V}
    (hJJ' : ∀ t, ∀ y ∈ B, IsComplexLinearMap (Jq t y) (J' t (φ y)) (mvfderiv I φ y).toLinearMap)
    {W : Set (ℝ × V)} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJ'per : Periodic J' 1) (hBW : univ ×ˢ (φ '' B) ⊆ W)
    {L : ℝ≥0} (hL : LipschitzWith L (ω₀.timeDependentHamiltonianSuspension (H' q)))
    (hnd : ∀ x : ℝ → V, Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' q t) (x t)) t) → (∀ t, x t ∈ φ '' B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow (H' q) hL 0 1) (x 0)) :
    ∃ y : ℝ → V, Periodic y 1 ∧
      (∀ t, HasDerivAt y (ω₀.hamiltonianVectorField (H' q t) (y t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t,
        ‖φ (u (endChart q (q.endSign * s, t))) - y t‖ +
            ‖fderiv ℝ ((φ ∘ u) ∘ endChart q) (q.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
                (ω₀.hamiltonianVectorField (H' q t) (y t))‖ ≤
          C * Real.exp (-(κ * s)) := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  -- In the positive end chart the structure is `J_q(±t)`, read in the chart as `J'_q(±t)`.
  set g : ℝ × V → ℝ × V := fun p ↦ (q.endSign * p.1, p.2)
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul contDiff_fst).prodMk contDiff_snd
  obtain ⟨x, hxper, hx, κ, hκ, C, hdecay⟩ :=
    hω.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_smulRight_le_exp (a := a)
      (H := positiveEndHamiltonian H q) (H' := positiveEndHamiltonian H' q)
      (u := u ∘ positiveEndChart q) (J := fun t y ↦ Jq (q.endSign * t) y)
      (J' := fun t v ↦ J' (q.endSign * t) v) (W := g ⁻¹' W) φ hφ
      (fun t y hy ↦ (hHH' (q.endSign * t) y hy).mono fun x hx ↦ by
        simp only [positiveEndHamiltonian_apply, comp_apply] at hx ⊢
        rw [hx])
      (contDiff_uncurry_positiveEndHamiltonian hH') (periodic_positiveEndHamiltonian hH'per)
      (fun t y hy ↦ hJJ' _ y hy) (hW.preimage hg.continuous)
      (hJ'.comp hg.contDiffOn (mapsTo_preimage g W)) (periodic_comp_endSign_mul hJ'per) hB hBφ
      (fun p hp ↦ hBW ⟨mem_univ _, hp.2⟩) (fun t y hy ↦ hJt _ y hy)
      (hu.comp (contDiff_positiveEndChart q 3).contMDiff.contMDiffOn fun z hz ↦ haU z hz.1)
      (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one])
      (fun s hs t ↦ huB (s, t) hs)
      (fun z hz ↦ isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_of_cylindrical hKH hH
        hHd (haT.trans hz.1.le)
        ((hu.contMDiffAt (hU.mem_nhds (haU _ hz.1))).mdifferentiableAt (by norm_num))
        (hfloer _ (haU _ hz.1)) fun t ↦ hJ z.1 t hz.1)
      (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen
        q hKH hH hHd hU (hu.mdifferentiableOn (by norm_num)) haT haU))
      -- The orbits of the end Hamiltonian of the positive end chart are isolated and nondegenerate.
      (fun x hxper hx hxB ↦
        SymplecticForm.exists_pos_forall_eq_of_isNondegenerateFixedPt_positiveEndHamiltonian hL hx
          (isNondegenerateFixedPt_of_positiveEndHamiltonian hnd hxper hx hxB))
      (fun x hxper hx hxB v hv ↦
        SymplecticForm.eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self hL
          (hH'.of_le (by norm_num)) hH'per (SymplecticForm.hasDerivAt_comp_endSign_mul hx)
          (periodic_comp_endSign_mul hxper)
          (by simpa only [mul_zero] using
            isNondegenerateFixedPt_of_positiveEndHamiltonian hnd hxper hx hxB)
          (by simpa only [endSign_mul_endSign_mul] using hv))
  -- Read the orbit `x` of the positive end chart with the time `±t` of the end.
  refine ⟨fun t ↦ x (q.endSign * t), periodic_comp_endSign_mul hxper,
    SymplecticForm.hasDerivAt_comp_endSign_mul hx, κ, hκ, C, hdecay.mono fun s hs t ↦ ?_⟩
  have h := hs (q.endSign * t)
  beta_reduce
  rw [SymplecticForm.norm_fderiv_comp_endChart_sub_smulRight (ω := ω₀) (H := H') q (φ ∘ u)
    (fun t ↦ x (q.endSign * t)) s t, endChart_eq_positiveEndChart]
  simpa only [comp_apply, comp_assoc, endSign_mul_endSign_mul] using h

/-- **One exponential `C¹` rate for the three ends of a Floer pair of pants in a manifold.** Let
`K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C¹` Hamiltonians `H_q`,
and let `u` be `C³` on `S`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite
energy. Suppose that on each end `q`, beyond some `a ≥ T₀`, the end lies in a compact set `B_q`
and the structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))` with `J_q(t, y)` tamed by
`ω` on `B_q`, and that `B_q` lies in the source of a symplectic chart `ψ_q` reading `H_q` as a
`1`-periodic `C³` Hamiltonian `H'_q` and `J_q` as a `1`-periodic family `J'_q`, `C²` on an open set
`W_q ⊇ ℝ × ψ_q(B_q)`. If the suspended Hamiltonian vector field of each `H'_q` is globally Lipschitz
and every `1`-periodic orbit of `H'_q` in `ψ_q(B_q)` starts at a nondegenerate fixed point of the
time-one map, then there are `1`-periodic orbits `y_q` of the `H'_q`, a rate `κ > 0` and a
constant `C` such that for all large `s`, every end `q` and every `t`,

`‖ψ_q(u(φ_q(±s, t))) - y_q(t)‖ + ‖d(ψ_q ∘ u ∘ φ_q)(±s, t) - dt ⊗ X_{H'_q(t)}(y_q(t))‖`

is at most `C exp (-κ s)`, where `ψ_q` is the symplectic chart and `φ_q` the end chart. -/
theorem exists_pos_forall_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u thricePuncturedSphereReal)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haT : T₀ ≤ a) {B : Puncture → Set M} (hB : ∀ q, IsCompact (B q))
    (huB : ∀ q, ∀ ζ : ℝ × ℝ, a < ζ.1 → u (positiveEndChart q ζ) ∈ B q)
    {Jq : Puncture → ℝ → (y : M) → AlmostComplexStructure (TangentSpace I y)}
    (hJ : ∀ q s t, a < s →
      J (endChart q (q.endSign * s, t)) = Jq q t (u (endChart q (q.endSign * s, t))))
    (hJt : ∀ q t, ∀ y ∈ B q, (hω.symplecticFormAt y).Tames (Jq q t y))
    (φ : Puncture → PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) (hBφ : ∀ q, B q ⊆ (φ q).source)
    (hφ : ∀ q, ∀ y ∈ B q, ∀ v w : TangentSpace I y,
      ω.eval₂ y v w = ω₀ (mvfderiv I (φ q) y v) (mvfderiv I (φ q) y w))
    (hHH' : ∀ q t, ∀ y ∈ B q, H q t =ᶠ[𝓝 y] H' q t ∘ φ q)
    (hH' : ∀ q, ContDiff ℝ 3 (uncurry (H' q))) (hH'per : ∀ q, Periodic (H' q) 1)
    {J' : Puncture → ℝ → V → AlmostComplexStructure V}
    (hJJ' : ∀ q t, ∀ y ∈ B q,
      IsComplexLinearMap (Jq q t y) (J' q t (φ q y)) (mvfderiv I (φ q) y).toLinearMap)
    {W : Puncture → Set (ℝ × V)} (hW : ∀ q, IsOpen (W q))
    (hJ' : ∀ q, ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (J' q p.1 p.2).toLinearMap.toContinuousLinearMap) (W q))
    (hJ'per : ∀ q, Periodic (J' q) 1) (hBW : ∀ q, univ ×ˢ (φ q '' B q) ⊆ W q)
    {L : Puncture → ℝ≥0}
    (hL : ∀ q, LipschitzWith (L q) (ω₀.timeDependentHamiltonianSuspension (H' q)))
    (hnd : ∀ q (x : ℝ → V), Periodic x 1 →
      (∀ t, HasDerivAt x (ω₀.hamiltonianVectorField (H' q t) (x t)) t) →
      (∀ t, x t ∈ φ q '' B q) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω₀.timeDependentHamiltonianFlow (H' q) (hL q) 0 1) (x 0)) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        ∀ t, HasDerivAt (y q) (ω₀.hamiltonianVectorField (H' q t) (y q t)) t) ∧
      ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ q t,
        ‖φ q (u (endChart q (q.endSign * s, t))) - y q t‖ +
            ‖fderiv ℝ ((φ q ∘ u) ∘ endChart q) (q.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
                (ω₀.hamiltonianVectorField (H' q t) (y q t))‖ ≤
          C * Real.exp (-(κ * s)) := by
  -- Beyond `max a 0` every end lies in `S`; apply the estimate end by end.
  have haT' : T₀ ≤ max a 0 := haT.trans (le_max_left _ _)
  choose y hyper hy hdecay using fun q ↦
    hω.exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_isOpen q
      (hKH q) (hH q) (hHs q) isOpen_thricePuncturedSphereReal hu hfloer hE haT'
      (fun ζ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal
        ((le_max_right _ _).trans_lt hζ))
      (hB q) (fun ζ hζ ↦ huB q ζ ((le_max_left _ _).trans_lt hζ))
      (fun s t hs ↦ hJ q s t ((le_max_left _ _).trans_lt hs)) (hJt q) (φ q) (hBφ q) (hφ q)
      (hHH' q) (hH' q) (hH'per q) (hJJ' q) (hW q) (hJ' q) (hJ'per q) (hBW q) (hL q) (hnd q)
  exact ⟨y, fun q ↦ ⟨hyper q, hy q⟩, exists_pos_eventually_forall_le_mul_exp hdecay⟩

end TauCeti.SmoothTwoForm.IsNondegenerate

end
