/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.RationalFunction
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.LinearAlgebra.Projectivization.Basic
import TauCeti.Topology.Algebra.Projectivization
import TauCeti.Topology.Compactification.OnePoint.Nhds
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Holomorphic maps from the Riemann sphere to projective space are polynomial

Every holomorphic map `u : ℂℙ¹ → ℂℙⁿ` is given by polynomials: there are polynomials
`P₀, …, Pₙ` of degree at most `d`, without common zero in `ℂ` and with coefficient vector of `X^d`
nonzero, such that `u z = [P₀(z) : ⋯ : Pₙ(z)]` at every finite point `z` of the Riemann sphere
`OnePoint ℂ`, and `u ∞` is the point `[c₀ : ⋯ : cₙ]` of the coefficients of `X^d`
(`TauCeti.RiemannSurface.exists_polynomial_eq_mk`). Equivalently, `u` is the map
`[x₀ : x₁] ↦ [F₀(x₀, x₁) : ⋯ : Fₙ(x₀, x₁)]` of the homogeneous polynomials
`Fⱼ = x₁^d Pⱼ(x₀ / x₁)` of degree `d`, which have no common zero on `ℂ² ∖ 0`. This is the
classical description of the rational curves of projective space by their parametrizations, the
first step in identifying the holomorphic spheres of `ℂℙⁿ` of low degree; for instance a map of
degree `d = 1` is the line `[x] ↦ [A x]` of an injective linear map `A : ℂ² → ℂⁿ⁺¹`.

The proof goes through the field of meromorphic functions on the sphere.

* **Ratios are meromorphic.** For a holomorphic map `u : X → ℂℙⁿ` from any Riemann surface, the
  ratio `x ↦ uⱼ(x) / uᵢ(x)` of two homogeneous coordinates is meromorphic at every point
  (`TauCeti.RiemannSurface.meromorphicAt_rep_div_rep`): near each point `u` has holomorphic
  homogeneous coordinates `F` (`Projectivization.exists_contMDiffAt_eventually_eq_mk`), and the
  ratio is `Fⱼ / Fᵢ`, a quotient of holomorphic functions.
* **The identity theorem.** On a connected `X`, if the coordinate `uᵢ` is nonzero at one point,
  it is nonzero on a punctured neighbourhood of every point
  (`TauCeti.RiemannSurface.eventually_rep_ne_zero`). The ratio `uᵢ / uᵢ` takes only the values
  `0` and `1`, so its meromorphic function `m` satisfies `m (1 - m) = 0`. In the field of
  meromorphic functions this forces `m = 0` or `m = 1`, and `m = 0` is excluded since `m` is `1`
  near the point where `uᵢ` does not vanish.
* **Rationality.** On the Riemann sphere every meromorphic function is rational
  (`TauCeti.RiemannSurface.MeromorphicFunction.ratFuncEquiv`), so the ratios `uⱼ / uᵢ` are
  rational functions `rⱼ`. Clearing their denominators gives polynomials `Qⱼ` with
  `u z = [Q₀(z) : ⋯ : Qₙ(z)]` on a punctured neighbourhood of every finite point. Dividing by the
  greatest common divisor of the `Qⱼ` removes their common zeros, and continuity of `u` extends
  the formula to every finite point. At `∞` the formula becomes `u (1 / w) = [R(w)]` for the
  reflected polynomials `Rⱼ(w) = w^d Pⱼ(1 / w)`, whose value at `w = 0` is the coefficient vector
  of `X^d`.

## Main results

* `TauCeti.RiemannSurface.meromorphicAt_rep_div_rep`: the ratios of the homogeneous coordinates
  of a holomorphic map to projective space are meromorphic.
* `TauCeti.RiemannSurface.eventually_rep_ne_zero`: a homogeneous coordinate of a holomorphic map
  on a connected Riemann surface that is nonzero somewhere has isolated zeros.
* `TauCeti.RiemannSurface.exists_polynomial_eq_mk`: a holomorphic map from the Riemann sphere to
  projective space is given by polynomials.
* `TauCeti.RiemannSurface.exists_injective_eq_map_of_natDegree_le_one`: when these polynomials
  have degree at most one, the map is a line `[x] ↦ [A x]`.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter V (holomorphic maps of a Riemann surface to
  projective space are given by meromorphic functions).
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §2, Theorem 2.9 (the meromorphic functions on the Riemann sphere are the rational functions).
-/

public section

open Filter Function OnePoint Polynomial Projectivization Set Topology
open scoped LinearAlgebra.Projectivization Manifold

namespace TauCeti.RiemannSurface

variable {n : ℕ}

section RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  {u : X → ℙ ℂ (Fin (n + 1) → ℂ)}

/-- **The ratios of homogeneous coordinates are meromorphic.** For a holomorphic map `u` from a
Riemann surface to projective space, the ratio `x ↦ uⱼ(x) / uᵢ(x)` of two homogeneous coordinates
of `u x` is meromorphic at every point; it does not depend on the representatives chosen, and is
`0` where `uᵢ` vanishes. -/
theorem meromorphicAt_rep_div_rep (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin n → ℂ) u)
    (i j : Fin (n + 1)) (x : X) :
    MeromorphicAt (fun y ↦ (u y).rep j / (u y).rep i) x := by
  obtain ⟨F, hF, hFu⟩ := exists_contMDiffAt_eventually_eq_mk (hu.contMDiff (n := 1) x)
  have hd := (contMDiffAt_iff_eventually_mdifferentiableAt one_ne_zero).1 hF
  have hcoord (k : Fin (n + 1)) : MeromorphicAt (fun y ↦ F y k) x :=
    meromorphicAt_of_eventually_mdifferentiableAt <| hd.mono fun y hy ↦
      ((differentiable_apply k).differentiableAt).comp_mdifferentiableAt hy
  refine ((hcoord j).mul (hcoord i).inv).congr ?_
  filter_upwards [nhdsWithin_le_nhds hFu] with y ⟨hy, hyu⟩
  simp only [Pi.mul_apply, Pi.inv_apply]
  rw [hyu, rep_div_rep_mk, div_eq_mul_inv]

/-- **Isolated zeros of a homogeneous coordinate.** If the `i`-th homogeneous coordinate of a
holomorphic map `u` from a connected Riemann surface to projective space is nonzero at one point,
then it is nonzero on a punctured neighbourhood of every point: `u` meets the hyperplane `xᵢ = 0`
in a discrete set. -/
theorem eventually_rep_ne_zero [ConnectedSpace X] (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin n → ℂ) u)
    {i : Fin (n + 1)} {x₀ : X} (hx₀ : (u x₀).rep i ≠ 0) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, (u y).rep i ≠ 0 := by
  have hk := meromorphicAt_rep_div_rep hu i i
  set m := MeromorphicFunction.ofMeromorphic hk
  -- The ratio `uᵢ / uᵢ` takes only the values `0` and `1`, so `m * (1 - m) = 0`.
  have hm : m * (1 - m) = 0 := by
    have h := MeromorphicFunction.ofMeromorphic_mul hk
      fun x ↦ (meromorphicAt_const (1 : ℂ) x).sub (hk x)
    rw [MeromorphicFunction.ofMeromorphic_sub (fun x ↦ meromorphicAt_const (1 : ℂ) x) hk,
      MeromorphicFunction.ofMeromorphic_const,
      map_one] at h
    rw [← h, ← map_zero (algebraMap ℂ (MeromorphicFunction X)),
      ← MeromorphicFunction.ofMeromorphic_const]
    refine MeromorphicFunction.ofMeromorphic_congr _ _ fun x ↦ Eventually.of_forall fun y ↦ ?_
    by_cases hy : (u y).rep i = 0 <;> simp [hy]
  have hev (x : X) :
      m.finitePart =ᶠ[𝓝[≠] x] fun y ↦ (u y).rep i / (u y).rep i :=
    MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq hk x
  have hne (x : X) : (𝓝[≠] x).NeBot := (chartAt ℂ x).nhdsNE_neBot (mem_chart_source ℂ x)
  rcases mul_eq_zero.1 hm with h0 | h1
  · -- `m = 0` is impossible, since the ratio is `1` near `x₀`.
    have hk₀ : ∀ᶠ y in 𝓝 x₀, (u y).rep i / (u y).rep i = 1 := by
      filter_upwards [hu.continuous.continuousAt.preimage_mem_nhds
        ((isOpen_affineOpen (K := ℂ) i).mem_nhds ((mem_affineOpen_iff i _).2 hx₀))] with y hy
      exact div_self ((mem_affineOpen_iff i _).1 hy)
    have := hne x₀
    obtain ⟨y, hy, hy₁⟩ := ((hev x₀).and (nhdsWithin_le_nhds hk₀)).exists
    beta_reduce at hy
    rw [h0, MeromorphicFunction.finitePart_zero, Pi.zero_apply, hy₁] at hy
    exact (zero_ne_one hy).elim
  · -- `m = 1`, so the ratio is `1`, and `uᵢ ≠ 0`, near every point.
    rw [sub_eq_zero] at h1
    filter_upwards [hev x] with y hy h
    rw [← h1, MeromorphicFunction.finitePart_one, h, div_zero] at hy
    exact zero_ne_one hy.symm

end RiemannSurface

section Sphere

variable {u : OnePoint ℂ → ℙ ℂ (Fin (n + 1) → ℂ)}

/-- A holomorphic map from the Riemann sphere to projective space is given near every finite
point, off that point, by the values of polynomials. -/
private theorem exists_polynomial_eventually_eq_mk
    (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin n → ℂ) u) :
    ∃ Q : Fin (n + 1) → ℂ[X], ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z,
      ∃ hw : (fun j ↦ (Q j).eval w) ≠ 0, u w = mk ℂ _ hw := by
  obtain ⟨i, hi⟩ : ∃ i, (u ∞).rep i ≠ 0 := Function.ne_iff.1 (u ∞).rep_ne_zero
  -- The ratios `uⱼ / uᵢ` are rational functions `r j`; clear their denominators.
  set g : Fin (n + 1) → MeromorphicFunction (OnePoint ℂ) :=
    fun j ↦ MeromorphicFunction.ofMeromorphic (meromorphicAt_rep_div_rep hu i j)
  set r : Fin (n + 1) → RatFunc ℂ := fun j ↦ MeromorphicFunction.ratFuncEquiv.symm (g j)
  set D : ℂ[X] := ∏ j, (r j).denom
  have hdvd (j : Fin (n + 1)) : (r j).denom ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  choose c hc using hdvd
  refine ⟨fun j ↦ (r j).num * c j, fun z ↦ ?_⟩
  have hD : D ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ ↦ (r j).denom_ne_zero
  have hDz : ∀ᶠ w in 𝓝[≠] z, D.eval w ≠ 0 :=
    eventually_codiscrete_iff_forall_eventually_nhdsNE.1 (eventually_eval_ne_zero_codiscrete hD) z
  have hrep : ∀ᶠ w : ℂ in 𝓝[≠] z, (u w).rep i ≠ 0 :=
    (OnePoint.tendsto_coe_nhdsNE z).eventually (eventually_rep_ne_zero hu hi _)
  have hval (j : Fin (n + 1)) :
      ∀ᶠ w : ℂ in 𝓝[≠] z, (g j).finitePart w = (u w).rep j / (u w).rep i :=
    (OnePoint.tendsto_coe_nhdsNE z).eventually
      (MeromorphicFunction.finitePart_ofMeromorphic_eventuallyEq _ _)
  filter_upwards [hDz, hrep, eventually_all.2 hval] with w hDw hiw hjw
  have key (j : Fin (n + 1)) :
      ((r j).num * c j).eval w = D.eval w * ((u w).rep j / (u w).rep i) := by
    have hdw : (r j).denom.eval w ≠ 0 := fun h ↦ hDw (by rw [hc j, eval_mul, h, zero_mul])
    have hcw : (c j).eval w ≠ 0 := fun h ↦ hDw (by rw [hc j, eval_mul, h, mul_zero])
    have hgj : g j w = ↑((r j).eval (RingHom.id ℂ) w) := by
      rw [← MeromorphicFunction.ratFuncEquiv_apply_coe (r j) hdw]
      simp [r]
    rw [← hjw j, MeromorphicFunction.finitePart_of_eq_coe hgj, hc j, RatFunc.eval, eval₂_id,
      eval₂_id, eval_mul, eval_mul]
    field_simp
  have hQ : (fun j ↦ ((r j).num * c j).eval w) ≠ 0 := fun h ↦ by
    have := congr_fun h i
    rw [key, div_self hiw, mul_one] at this
    exact hDw this
  refine ⟨hQ, ?_⟩
  conv_lhs => rw [← (u w).mk_rep]
  rw [mk_eq_mk_iff']
  refine ⟨(u w).rep i / D.eval w, funext fun j ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, key]
  field_simp

/-- A continuous map from the Riemann sphere to projective space given at every finite point by
polynomials of degree at most `d` takes at `∞` the value of their coefficient vector of `X^d`,
when it is nonzero: near `∞`, in the coordinate `w = 1 / z`, the map is given by the reflected
polynomials `w ^ d Pⱼ(1 / w)`, whose value at `w = 0` is that coefficient vector. -/
private theorem apply_infty_eq_mk_coeff (hu : Continuous u) {P : Fin (n + 1) → ℂ[X]} {d : ℕ}
    (hdeg : ∀ j, (P j).natDegree ≤ d) (hc : (fun j ↦ (P j).coeff d) ≠ 0)
    (hPz : ∀ z : ℂ, (fun j ↦ (P j).eval z) ≠ 0) (hfin : ∀ z : ℂ, u z = mk ℂ _ (hPz z)) :
    u ∞ = mk ℂ _ hc := by
  set R : ℂ → Fin (n + 1) → ℂ := fun w j ↦ (reflect d (P j)).eval w
  have hRinv (w : ℂ) (hw : w ≠ 0) : (fun j ↦ (P j).eval w⁻¹) = (w⁻¹) ^ d • R w := by
    have : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
    funext j
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← eval₂_id, ← eval₂_reflect_mul_pow _ _ d _ (hdeg j),
      invOf_eq_inv, inv_inv, eval₂_id]
  have hR0 : R 0 = fun j ↦ (P j).coeff d := by
    funext j
    simp [R, ← coeff_zero_eq_eval_zero, coeff_reflect]
  have hR (w : ℂ) : R w ≠ 0 := by
    rcases eq_or_ne w 0 with rfl | hw
    · rwa [hR0]
    · intro h
      exact hPz w⁻¹ (by rw [hRinv w hw, h, smul_zero])
  have hRcont : Continuous fun w ↦ mk ℂ (R w) (hR w) :=
    continuous_mk (continuous_pi fun j ↦ (reflect d (P j)).continuous) hR
  have hinf : Tendsto (fun w : ℂ ↦ ((w⁻¹ : ℂ) : OnePoint ℂ)) (𝓝[≠] 0) (𝓝 ∞) :=
    tendsto_coe_infty_of_tendsto_cobounded tendsto_inv₀_nhdsNE_zero
  simp_rw [← hR0]
  refine tendsto_nhds_unique ((hu.tendsto _).comp hinf)
    ((hRcont.tendsto 0).mono_left nhdsWithin_le_nhds |>.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ 0)
  rw [comp_apply, hfin, eq_comm, mk_eq_mk_iff']
  exact ⟨(w⁻¹) ^ d, (hRinv w hw).symm⟩

/-- **Holomorphic maps from the Riemann sphere to projective space are polynomial.** A
holomorphic map `u : ℂℙ¹ → ℂℙⁿ`, with `ℂℙ¹` the Riemann sphere `OnePoint ℂ`, is given by
polynomials `P₀, …, Pₙ` of degree at most `d` whose coefficient vector of `X^d` is nonzero and
which have no common zero in `ℂ`: `u z = [P₀(z) : ⋯ : Pₙ(z)]` at every finite point `z`, and
`u ∞ = [P₀.coeff d : ⋯ : Pₙ.coeff d]`. In homogeneous coordinates, `u` is the map of the
homogeneous polynomials `x₁^d Pⱼ(x₀ / x₁)` of degree `d`, which have no common zero on
`ℂ² ∖ 0`. -/
theorem exists_polynomial_eq_mk (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin n → ℂ) u) :
    ∃ (d : ℕ) (P : Fin (n + 1) → ℂ[X]), (∀ j, (P j).natDegree ≤ d) ∧
      (∃ h : (fun j ↦ (P j).coeff d) ≠ 0, u ∞ = mk ℂ _ h) ∧
      ∀ z : ℂ, ∃ h : (fun j ↦ (P j).eval z) ≠ 0, u z = mk ℂ _ h := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_eventually_eq_mk hu
  -- Divide by the greatest common divisor to remove the common zeros.
  obtain ⟨P, hQP, hP⟩ := Finset.extract_gcd Q Finset.univ_nonempty
  have hPz (z : ℂ) : (fun j ↦ (P j).eval z) ≠ 0 := fun h ↦ by
    have hdvd : X - C z ∣ Finset.univ.gcd P :=
      Finset.dvd_gcd fun j _ ↦ dvd_iff_isRoot.2 (congr_fun h j)
    rw [hP] at hdvd
    exact not_isUnit_X_sub_C z (isUnit_of_dvd_one hdvd)
  have hcont : Continuous fun w : ℂ ↦ mk ℂ (fun j ↦ (P j).eval w) (hPz w) :=
    continuous_mk (continuous_pi fun j ↦ (P j).continuous) hPz
  have hfin (z : ℂ) : u z = mk ℂ (fun j ↦ (P j).eval z) (hPz z) := by
    refine tendsto_nhds_unique (l := 𝓝[≠] z) ((hu.continuous.tendsto _).comp
      ((OnePoint.continuous_coe.tendsto z).mono_left nhdsWithin_le_nhds))
      ((hcont.tendsto z).mono_left nhdsWithin_le_nhds |>.congr' ?_)
    filter_upwards [hQ z] with w ⟨hw, huw⟩
    rw [comp_apply, huw, eq_comm, mk_eq_mk_iff']
    exact ⟨(Finset.univ.gcd Q).eval w, funext fun j ↦ by simp [hQP j (Finset.mem_univ j)]⟩
  set d := Finset.univ.sup fun j ↦ (P j).natDegree
  have hdeg (j : Fin (n + 1)) : (P j).natDegree ≤ d :=
    Finset.le_sup (f := fun j ↦ (P j).natDegree) (Finset.mem_univ j)
  -- Some polynomial has degree exactly `d`, so the coefficient vector of `X^d` is nonzero.
  have hcoeff : (fun j ↦ (P j).coeff d) ≠ 0 := by
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
      fun j ↦ (P j).natDegree
    replace hj₀ : d = (P j₀).natDegree := hj₀
    rcases eq_or_ne d 0 with h | h
    · simpa [h, coeff_zero_eq_eval_zero] using hPz 0
    · intro hc
      have hj₀' : P j₀ ≠ 0 := fun h' ↦ h (by rw [hj₀, h', natDegree_zero])
      apply leadingCoeff_ne_zero.2 hj₀'
      rw [leadingCoeff, ← hj₀]
      exact congr_fun hc j₀
  exact ⟨d, P, hdeg, ⟨hcoeff, apply_infty_eq_mk_coeff hu.continuous hdeg hcoeff hPz hfin⟩,
    fun z ↦ ⟨hPz z, hfin z⟩⟩

/-- **Maps of degree one are lines.** If a map `u` from the Riemann sphere to projective space is
given, as in `TauCeti.RiemannSurface.exists_polynomial_eq_mk`, by polynomials `P₀, …, Pₙ` of
degree at most `1` with nonzero coefficient vector of `X`, then it is the line `[x] ↦ [A x]` of the
injective linear map `A : ℂ² → ℂⁿ⁺¹` sending `(x₀, x₁)` to `x₀ b + x₁ a`, where `a` and `b` are
the coefficient vectors of `1` and of `X`, read through the identification
`OnePoint.equivProjectivization` of the Riemann sphere with `ℙ ℂ (Fin 2 → ℂ)`. -/
theorem exists_injective_eq_map_of_natDegree_le_one {P : Fin (n + 1) → ℂ[X]}
    (hdeg : ∀ j, (P j).natDegree ≤ 1) (hc : (fun j ↦ (P j).coeff 1) ≠ 0)
    (hinf : u ∞ = mk ℂ _ hc)
    (hz : ∀ z : ℂ, ∃ h : (fun j ↦ (P j).eval z) ≠ 0, u z = mk ℂ _ h) :
    ∃ (A : (Fin 2 → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ) (hA : Injective A),
      ∀ x, u x = Projectivization.map A hA (equivProjectivization ℂ x) := by
  obtain ⟨A, hA⟩ : ∃ A : (Fin 2 → ℂ) →ₗ[ℂ] Fin (n + 1) → ℂ,
      ∀ x, A x = fun j ↦ x 0 * (P j).coeff 1 + x 1 * (P j).coeff 0 :=
    ⟨(LinearMap.proj 0).smulRight (fun j ↦ (P j).coeff 1) +
      (LinearMap.proj 1).smulRight (fun j ↦ (P j).coeff 0), fun _ ↦ rfl⟩
  have heval (t : ℂ) : (fun j ↦ (P j).eval t) = A ![t, 1] := by
    ext j
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one (hdeg j)]
    simp only [hA, eval_add, eval_mul, eval_C, eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring
  have hinj : Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun x hx ↦ ?_
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · -- The second coordinate vanishes, so `x 0 • b = 0` with `b ≠ 0`.
      have h0 : x 0 = 0 := by
        by_contra h0
        refine hc (_root_.funext fun j ↦ ?_)
        have := congr_fun hx j
        simp only [hA, h1, zero_mul, add_zero, Pi.zero_apply] at this
        exact (mul_eq_zero.1 this).resolve_left h0
      ext k
      fin_cases k <;> simp [h0, h1]
    · -- Otherwise `A x` is a nonzero multiple of the values `P (x 0 / x 1)`, which do not vanish.
      obtain ⟨hne, -⟩ := hz (x 0 / x 1)
      refine absurd (_root_.funext fun j ↦ ?_) hne
      have := congr_fun hx j
      simp only [hA, Pi.zero_apply] at this
      rw [show (P j).eval (x 0 / x 1) = A ![x 0 / x 1, 1] j from congr_fun (heval _) j, hA]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply]
      field_simp
      linear_combination this
  refine ⟨A, hinj, fun x ↦ ?_⟩
  induction x using OnePoint.rec with
  | infty =>
    rw [hinf, equivProjectivization_apply_infinity, map_mk]
    congr 1
    ext j
    simp [hA]
  | coe t =>
    obtain ⟨hne, hut⟩ := hz t
    rw [hut, equivProjectivization_apply_coe, map_mk]
    congr 1
    exact heval t

end Sphere

end TauCeti.RiemannSurface
