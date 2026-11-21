/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.MeasureTheory.Function.Jacobian.Plane

/-!
# Asymptotic orbits at the ends of a finite-energy Floer four-punctured sphere in a manifold

Plumbing the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ∈ {0, 1}` of a pair of pants `S`, with Hamiltonians `Hb`, along a neck of length `L` gives the
four-punctured sphere `P = ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`). These are the domains of the family that compares the two
ways of composing two pair-of-pants products.

Let `ω` be a nondegenerate two-form on a manifold `M`, such as a closed symplectic manifold, and
let `u : P → M` be a `C¹` solution of the Floer equation `(du - X_K)^{0,1} = 0` for almost complex
structures `J(z)` on the tangent spaces `T_{u z} M`, with image in a compact set `B` and finite
energy over `P`. This file shows that `u` breaks off a one-periodic orbit at each of the four ends
of `P`:

* at each end `r ≠ q` of the receiving pair of pants `S`, an orbit `y` of `Hb r` and `s_n → ∞`
  such that the loops `t ↦ u(φ_r(±s_n, t))`, with the sign of the end, converge to `y`, by
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_plumbedPerturbation_of_isCompact`
  in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`;
* at each input end `r ≠ ∞` of the inserted pair of pants `S'`, whose image under `ψ` is an end of
  `P`, an orbit `y` of `Ha r` and `s_n → ∞` such that the loops `t ↦ u(ψ(φ_r(s_n, t)))` converge
  to `y`, by
  `exists_mem_periodicSolutions_tendstoUniformly_plumbingMap_endChart_of_floer_of_isCompact` in the
  same namespace.

On a compact manifold `B` can be the whole manifold (the same names without `_of_isCompact`). As in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Manifold`, convergence and uniform tameness are
measured through a `C¹` map `e : M → F` into a finite-dimensional normed space, injective on `B`
and with injective differential at the points of `B`: the loops converge pointwise in `M` and
uniformly after applying `e`.

Both statements reduce to the ends of a pair of pants, through the theorem
`IsNondegenerate.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen` in the
namespace `TauCeti.SmoothTwoForm`, which only needs the solution on an open set containing the end.

* **Receiving ends.** Inside the circle `s_q = L/2` of the end `q`, the plumbed perturbation is the
  perturbation of `S` (`TauCeti.Floer.plumbedPerturbation_of_re_endCoord_le`), and that part of
  `S` lies in `P` (`mem_plumbedSphere_of_endSign_mul_re_endCoord_le`). It contains the ends
  `r ≠ q` of `S`, on which the longitudinal coordinate of `q` is nonpositive
  (`endSign_mul_re_endCoord_nonpos`).
* **Inserted ends.** Outside the circle `s_∞ = -L/2` of the end `∞` of `S'`, the pullback of the
  plumbed perturbation along the holomorphic plumbing map `ψ` is the perturbation of `S'`
  (`TauCeti.Floer.plumbedPerturbation_plumbingMap`), and `ψ` maps that part of `S'` into `P`
  (`TauCeti.ThricePuncturedSphere.Puncture.realChart_plumbingMap_mem_plumbedSphere`). Since the
  perturbed derivative and the energy density are natural under holomorphic changes of
  coordinates, `u ∘ ψ` solves the Floer equation for the perturbation of `S'` there
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap`), and
  its energy density is the Jacobian of `ψ` times that of `u`
  (`TauCeti.SmoothTwoForm.floerEnergyDensity_comp_realChart_plumbingMap`), so by the change of
  variables formula its energy there is the energy of `u` over the image.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing pairs of pants and the associativity of the pair-of-pants product.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_injective)
open scoped Manifold ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-! ### The regions of the two pairs of pants inside the plumbed sphere -/

/-- Far out on an end `r ≠ r'`, the signed longitudinal coordinate of `r'` is less than `L/2`. -/
private theorem positiveEndChart_mem_endSign_mul_re_endCoord_lt {r r' : Puncture} (hr : r ≠ r')
    (hL : 0 < L) {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) :
    positiveEndChart r ζ ∈ thricePuncturedSphereReal ∩
      (fun z : ℝ × ℝ ↦ r'.endSign * (r'.endCoord (Complex.equivRealProdCLM.symm z)).re) ⁻¹'
        Iio (L / 2) := by
  refine ⟨positiveEndChart_mem_thricePuncturedSphereReal hζ, ?_⟩
  have h : 0 < r.endSign *
      (r.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart r ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  exact (endSign_mul_re_endCoord_nonpos hr h).trans_lt (half_pos hL)

/-! ### Asymptotic orbits at the ends -/

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

namespace IsNondegenerate

/-- **A finite-energy Floer four-punctured sphere in a manifold breaks off an orbit at each end of
the receiving pair of pants.** Plumb the output of a pair of pants with Hamiltonians `Ha` into the
input `q ≠ ∞` of one with `1`-periodic `C¹` Hamiltonians `Hb`, `Hb q = Ha ∞`, along a neck of
length `L > 4`. Let `ω` be a nondegenerate two-form on a manifold `M`, and let `u` be `C¹` on the
plumbed four-punctured sphere `P`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` for the plumbed perturbation `K` on `P`. Let `e : M → F` be a `C¹` map into
a finite-dimensional normed space, injective on `B` and with injective differential at the points
of `B`, and suppose that the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `P` is finite, then at each end
`r ≠ q` of the receiving pair of pants there are a `1`-periodic orbit `y` of the Hamiltonian vector
field of `Hb r` in `B` and `s_n → ∞` such that the loops `t ↦ u(φ_r(±s_n, t))`, with the sign of
the end, converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem
    exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_plumbedPerturbation_of_isCompact
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (hL : 4 < L) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (huB : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → ∀ v,
        c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {r : Puncture} (hr : r ≠ q) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (Hb r t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart r (r.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart r (r.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  -- The part `U` of `S` inside the circle `s_q = L/2` lies in `P`, and there the plumbed
  -- perturbation is the perturbation of `S`.
  set U := thricePuncturedSphereReal ∩
    (fun z : ℝ × ℝ ↦ q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re) ⁻¹'
      Iio (L / 2)
  have hUP : ∀ z ∈ U, (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1 := fun z hz ↦
    mem_plumbedSphere_of_endSign_mul_re_endCoord_le hq (by linarith)
      (mem_thricePuncturedSphereReal_iff.1 hz.1) (le_of_lt hz.2)
  have hK : ∀ z ∈ U, ∀ v, (fun x ↦ plumbedPerturbation Ha Hb q L
      (Complex.equivRealProdCLM.symm z) x v) =
      fun x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x v := by
    intro z hz v
    funext x
    have hzL : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 := hz.2
    rw [endSign_eq_one hq, one_mul] at hzL
    rw [plumbedPerturbation_of_re_endCoord_le hq hab (by linarith) x]
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen r
    (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm (H := Hb) hw x) (hHb r) (hHbs r)
    he hB he_inj hde (isOpen_endSign_mul_re_endCoord_lt q (L / 2)) (hu.mono hUP)
    (fun z hz ↦ huB z (hUP z hz)) J hc (fun z hz ↦ hJc z (hUP z hz)) (fun z hz ↦ ?_)
    (ne_top_of_le_ne_top hE ?_) (a := 0)
    fun ζ hζ ↦ positiveEndChart_mem_endSign_mul_re_endCoord_lt hr (by linarith) hζ
  · rw [← ω.perturbedMFDeriv_congr_perturbation u
      (Ks := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      (Ks' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (Kt' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
      (hK z hz 1) (hK z hz Complex.I)]
    exact hfloer z (hUP z hz)
  · -- The energy over `U` is the energy for the plumbed perturbation, which is at most that over
    -- `P`.
    refine le_of_eq_of_le (setLIntegral_congr_fun
      (isOpen_endSign_mul_re_endCoord_lt q (L / 2)).measurableSet fun z hz ↦ ?_)
      (lintegral_mono_set hUP)
    rw [ω.floerEnergyDensity_congr_perturbation u
      (Ks := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      (Ks' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (Kt' := fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
      (hK z hz 1) (hK z hz Complex.I)]

/-- **A finite-energy Floer four-punctured sphere in a manifold breaks off an orbit at each input
end of the inserted pair of pants.** Plumb the output of a pair of pants with `1`-periodic `C¹`
Hamiltonians `Ha` into the input `q ≠ ∞` of one with `1`-periodic `C¹` Hamiltonians `Hb`,
`Hb q = Ha ∞`, along a neck of length `L > 4`, with plumbing map `ψ`. Let `ω` be a nondegenerate
two-form on a manifold `M`, and let `u` be `C¹` on the plumbed four-punctured sphere `P`, with image
in a compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` for the plumbed
perturbation `K` on `P`. Let `e : M → F` be a `C¹` map into a finite-dimensional normed space,
injective on `B` and with injective differential at the points of `B`, and suppose that the almost
complex structures are uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with
`c > 0`. If the energy of `u` over `P` is finite, then at each input end `r ≠ ∞` of the inserted
pair of pants there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `Ha r` in `B`
and `s_n → ∞` such that the loops `t ↦ u(ψ(φ_r(s_n, t)))` converge to `y`, pointwise in `M` and
uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_plumbingMap_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (hL : 4 < L) (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (huB : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → ∀ v,
        c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {r : Puncture} (hr : r ≠ inf) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (Ha r t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (realChart (q.plumbingMap L) (endChart r (σ n, t)))))
          (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (realChart (q.plumbingMap L) (endChart r (σ n, t)))) atTop
          (𝓝 (y t)) := by
  set ψ := realChart (q.plumbingMap L)
  -- The part `U` of `S'` outside the circle `s_∞ = -L/2` is mapped into `P` by `ψ`, and there the
  -- pullback of the plumbed perturbation along `ψ` is the perturbation of `S'`.
  set U := thricePuncturedSphereReal ∩
    (fun z : ℝ × ℝ ↦ inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re) ⁻¹'
      Iio (L / 2)
  have hUo : IsOpen U := isOpen_endSign_mul_re_endCoord_lt inf (L / 2)
  have hψ : ∀ z ∈ U, (Complex.equivRealProdCLM.symm (ψ z) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (ψ z) ≠ 1) ∧
      Complex.equivRealProdCLM.symm (ψ z) ≠ q.plumbingMap L 1 := fun z hz ↦
    realChart_plumbingMap_mem_plumbedSphere hq (by linarith)
      (mem_thricePuncturedSphereReal_iff.1 hz.1) hz.2.le
  have hud : ∀ z ∈ U, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (ψ z) := fun z hz ↦
    (hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds (hψ z hz))).mdifferentiableAt
      one_ne_zero
  refine hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen r
    (K := pairOfPantsPerturbation Ha)
    (fun w x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm (H := Ha) hw x) (hHa r) (hHas r)
    he hB he_inj hde hUo (u := u ∘ ψ)
    (hu.comp (contDiff_realChart_plumbingMap q L).contMDiff.contMDiffOn hψ)
    (fun z hz ↦ huB _ (hψ z hz)) (fun z ↦ J (ψ z)) hc (fun z hz ↦ hJc _ (hψ z hz))
    (fun z hz ↦ ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap hq hHa hHb hHas
      hHbs hab hL (mem_thricePuncturedSphereReal_iff.1 hz.1) (hz.2.le.trans (by linarith))
      (hud z hz)
      (hfloer _ (hψ z hz)))
    (ne_top_of_le_ne_top hE ?_) (a := 0)
    (fun ζ hζ ↦ positiveEndChart_mem_endSign_mul_re_endCoord_lt hr (by linarith) hζ) |>.imp
      fun y ⟨hy, hyB, σ, hσ, hconv, hpt⟩ ↦ ⟨hy, hyB, σ, hσ, ?_, ?_⟩
  · -- The energy of `u ∘ ψ` over `U` is the energy of `u` over `ψ '' U ⊆ P`.
    rw [← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hUo.measurableSet
      (realChart_injective (q.plumbingMap_injective L)).injOn
      (fun z _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero z)
      fun z hz ↦ by
        rw [abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L z)]
        exact ω.floerEnergyDensity_comp_realChart_plumbingMap hq hHa hHb hHas hHbs hab hL
          (mem_thricePuncturedSphereReal_iff.1 hz.1) (hz.2.le.trans (by linarith)) (hud z hz)]
    refine lintegral_mono_set ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hψ z hz
  · simpa only [endSign_eq_one hr, one_mul, comp_apply] using hconv
  · simpa only [endSign_eq_one hr, one_mul, comp_apply] using hpt

/-- **A finite-energy Floer four-punctured sphere in a closed manifold breaks off an orbit at each
end of the receiving pair of pants.** Plumb the output of a pair of pants with Hamiltonians `Ha`
into the input `q ≠ ∞` of one with `1`-periodic `C¹` Hamiltonians `Hb`, `Hb q = Ha ∞`, along a neck
of length `L > 4`. Let `ω` be a nondegenerate two-form on a compact manifold `M`, and let `u` be
`C¹` on the plumbed four-punctured sphere `P`, solving the Floer equation `(du - X_K)^{0,1} = 0`
for the plumbed perturbation `K` on `P`. Let `e : M → F` be a `C¹` injective map with injective
differential into a finite-dimensional normed space, and suppose that the almost complex structures
are uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of
`u` over `P` is finite, then at each end `r ≠ q` of the receiving pair of pants there are a
`1`-periodic orbit `y` of the Hamiltonian vector field of `Hb r` and `s_n → ∞` such that the loops
`t ↦ u(φ_r(±s_n, t))`, with the sign of the end, converge to `y`, pointwise in `M` and uniformly
after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_plumbedPerturbation
    [CompactSpace M] (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (hL : 4 < L) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → ∀ v,
        c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {r : Puncture} (hr : r ≠ q) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (Hb r t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart r (r.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart r (r.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_plumbedPerturbation_of_isCompact
      hω hq hHb hHbs hab hL he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu
      (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE hr
  exact ⟨y, hy, h⟩

/-- **A finite-energy Floer four-punctured sphere in a closed manifold breaks off an orbit at each
input end of the inserted pair of pants.** Plumb the output of a pair of pants with `1`-periodic
`C¹` Hamiltonians `Ha` into the input `q ≠ ∞` of one with `1`-periodic `C¹` Hamiltonians `Hb`,
`Hb q = Ha ∞`, along a neck of length `L > 4`, with plumbing map `ψ`. Let `ω` be a nondegenerate
two-form on a compact manifold `M`, and let `u` be `C¹` on the plumbed four-punctured sphere `P`,
solving the Floer equation `(du - X_K)^{0,1} = 0` for the plumbed perturbation `K` on `P`. Let
`e : M → F` be a `C¹` injective map with injective differential into a finite-dimensional normed
space, and suppose that the almost complex structures are uniformly tame with respect to `e`:
`c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `P` is finite, then at each
input end `r ≠ ∞` of the inserted pair of pants there are a `1`-periodic orbit `y` of the
Hamiltonian vector field of `Ha r` and `s_n → ∞` such that the loops `t ↦ u(ψ(φ_r(s_n, t)))`
converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_plumbingMap_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (hL : 4 < L) (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) → ∀ v,
        c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z, ((Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≠ ⊤)
    {r : Puncture} (hr : r ≠ inf) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (Ha r t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (realChart (q.plumbingMap L) (endChart r (σ n, t)))))
          (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (realChart (q.plumbingMap L) (endChart r (σ n, t)))) atTop
          (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_plumbingMap_endChart_of_floer_of_isCompact hq
      hHa hHb hHas hHbs hab hL he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu
      (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE hr
  exact ⟨y, hy, h⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
