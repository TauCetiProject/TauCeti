/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Discriminant
public import TauCeti.Analysis.Polynomial.Puiseux.SectionOrder
public import TauCeti.Topology.Algebra.MvPolynomial.FiniteOrder
import TauCeti.RingTheory.MvPolynomial.TransverseOrder

/-!
# Constant ambient order on root sections from discriminant order

Let `p` be a monic polynomial in a distinguished variable whose coefficients are real
polynomials in `n` variables, and suppose its formal discriminant has constant finite ambient
order along a real analytic parametrization of the base. Then along every real root of the
fibers which is continuous at a point, the ambient order of `p`, as a polynomial in all `n + 1`
variables, is locally constant. This is the order-invariance of `p` on root sections in
McCallum's local discriminant theorem; fiber root multiplicity is not substituted for ambient
order.

The argument works in transverse planes, which keep the root coordinate and move the base
along an affine line. For every real direction in an open dense set, the discriminant becomes
a power of the line parameter times a unit after complexification, and the fibers split into
analytic branches after a ramified substitution
(`Polynomial.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq`). The plane order of `p` at
each branch on the base is then locally constant (`TauCeti.eventually_orderAt_root_eq_of_puiseux`).
A real root which is continuous at the central point eventually meets only branches through its
central value, so its plane orders are locally constant too. Finitely many directions in the
open set detect ambient order (`TauCeti.eventually_orderAt_eq_of_transverse`), which gives the
conclusion.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998),
  Sections 2–3.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- **Constant ambient order on root sections.** Let `p` be a monic polynomial whose
coefficients are real polynomials in `n` variables, specialized along a real analytic
parametrization `φ`, and suppose its formal discriminant has constant finite ambient order
near `a`. Along a real root `θ` of the fibers which is continuous at `a`, the ambient order of
`p`, viewed as a polynomial in `n + 1` variables with the root coordinate first, is constant
near `a`. The fibers may have multiple roots, and distinct real roots may meet at `a`. -/
theorem _root_.Polynomial.Monic.eventually_orderAt_root_eq_of_orderAt_discr_eq
    {p : Polynomial (MvPolynomial (Fin n) ℝ)} (hp : p.Monic)
    {φ : (ι → ℝ) → Fin n → ℝ} {θ : (ι → ℝ) → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m)
    (hθ : ContinuousAt θ a)
    (hroot : ∀ᶠ x in 𝓝 a, (p.map (MvPolynomial.eval (φ x))).IsRoot (θ x)) :
    ∀ᶠ x in 𝓝 a, ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (θ x) (φ x)) =
      ((MvPolynomial.finSuccEquiv ℝ n).symm p).orderAt (Fin.cons (θ a) (φ a)) := by
  set f := (MvPolynomial.finSuccEquiv ℝ n).symm p with hf
  obtain ⟨Φ, V, hVo, hVd, -, hreal, hdir⟩ :=
    p.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq hp hφ hm
  -- Finitely many transverse planes with directions in `V` detect the ambient order.
  refine eventually_orderAt_eq_of_transverse n f.totalDegree hVo hVd.nonempty (fun _ ↦ f)
    (fun x ↦ Fin.cons (θ x) (φ x)) (.of_forall fun _ ↦ le_rfl) fun v hv ↦ ?_
  simp only [Fin.cons_zero, Fin.cons_succ, MvPolynomial.orderAt_aeval_finCons_C_add_X]
  obtain ⟨r, u, hr, hu, hu0, hsplit⟩ := hdir v hv
  let ac : ι → ℂ := fun j ↦ (a j : ℂ)
  let ψ : (ι → ℝ) → ι → ℂ := fun x j ↦ (x j : ℂ)
  have hψ : Tendsto ψ (𝓝 a) (𝓝 ac) :=
    (continuous_pi fun j ↦ Complex.continuous_ofReal.comp (continuous_apply j)).tendsto a
  have hψ0 : Tendsto (fun x ↦ (ψ x, (0 : ℂ))) (𝓝 a) (𝓝 (ac, 0)) :=
    hψ.prodMk_nhds tendsto_const_nhds
  -- The complex transverse plane slices of `p` in direction `v`.
  let P : (ι → ℂ) → MvPolynomial (Fin 2) ℂ := fun z ↦
    MvPolynomial.aeval (Fin.cons (MvPolynomial.X 1)
      (fun j ↦ MvPolynomial.C (Φ z j) + MvPolynomial.C (v j : ℂ) * MvPolynomial.X 0) :
        Fin (n + 1) → MvPolynomial (Fin 2) ℂ) (MvPolynomial.map Complex.ofRealHom f)
  have hP (z : ι → ℂ) (s : ℂ) :
      MvPolynomial.aeval ![C ((fun _ ↦ (0 : ℂ)) z + s), X] (P z) =
        p.map (MvPolynomial.eval₂Hom Complex.ofRealHom (Φ z + s • fun i ↦ (v i : ℂ))) := by
    rw [zero_add, MvPolynomial.aeval_C_X_aeval_finCons_C_add_C_mul_X,
      MvPolynomial.finSuccEquiv_map, hf, AlgEquiv.apply_symm_apply, Polynomial.map_map]
    congr 1
    ext <;> simp
  -- Plane orders at the complex branches are locally constant.
  have horder := eventually_orderAt_root_eq_of_puiseux (p := P) (c := fun _ ↦ 0)
    (Nat.factorial_pos _) hr (hsplit.mono fun z hz ↦ (hP z.1 _).trans hz.1) hu hu0
    (hsplit.mono fun z hz ↦ (congrArg discr (hP z.1 _)).trans hz.2)
  -- On real points, the complex slices are the complexified real slices.
  have hPreal : ∀ᶠ x in 𝓝 a, ∀ t : ℝ, (P (ψ x)).orderAt ![0, (t : ℂ)] =
      (MvPolynomial.aeval (Fin.cons (MvPolynomial.X 1)
        (fun j ↦ MvPolynomial.C (φ x j) + MvPolynomial.C (v j) * MvPolynomial.X 0) :
          Fin (n + 1) → MvPolynomial (Fin 2) ℝ) f).orderAt ![0, t] := by
    filter_upwards [hreal] with x hx t
    have hPx : P (ψ x) = MvPolynomial.map Complex.ofRealHom
        (MvPolynomial.aeval (Fin.cons (MvPolynomial.X 1)
          (fun j ↦ MvPolynomial.C (φ x j) + MvPolynomial.C (v j) * MvPolynomial.X 0) :
            Fin (n + 1) → MvPolynomial (Fin 2) ℝ) f) := by
      rw [MvPolynomial.map_aeval_finCons_C_add_C_mul_X]
      simp only [P, ψ, hx, Complex.ofRealHom_eq_coe]
    have hpt : ![0, (t : ℂ)] = fun i ↦ Complex.ofRealHom (![0, t] i) := by
      ext i
      fin_cases i <;> simp
    rw [hPx, hpt, MvPolynomial.orderAt_map Complex.ofRealHom.injective]
  -- Each value of the real root is the value of some complex branch on the base.
  have hbranch : ∀ᶠ x in 𝓝 a, ∃ i, r i (ψ x, 0) = (θ x : ℂ) := by
    filter_upwards [hreal, hroot, hψ0.eventually hsplit] with x hx hθx hsx
    have heval := congrArg (eval (θ x : ℂ)) hsx.1
    simp only [zero_pow (Nat.factorial_ne_zero _), zero_smul, add_zero, eval_prod, eval_sub,
      eval_X, eval_C] at heval
    rw [hx, eval_map] at heval
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, (θ x : ℂ) - r i (ψ x, 0) = 0 := by
      have hcomp : (MvPolynomial.eval₂Hom Complex.ofRealHom fun i ↦ (φ x i : ℂ)) =
          Complex.ofRealHom.comp (MvPolynomial.eval (φ x)) := by
        ext <;> simp
      have hzero := congrArg Complex.ofRealHom hθx.eq_zero
      rw [eval_map, Polynomial.hom_eval₂, ← hcomp, map_zero] at hzero
      rw [← Finset.prod_eq_zero_iff, ← heval, ← hzero, Complex.ofRealHom_eq_coe]
    exact ⟨i, (sub_eq_zero.1 hi).symm⟩
  -- Near `a`, the real root only meets branches through its central value.
  have hnear : ∀ᶠ x in 𝓝 a, ∀ i, r i (ψ x, 0) = (θ x : ℂ) → r i (ac, 0) = (θ a : ℂ) := by
    refine eventually_all.2 fun i ↦ ?_
    by_cases hi : r i (ac, 0) = (θ a : ℂ)
    · exact .of_forall fun _ _ ↦ hi
    have hcont : Tendsto (fun x ↦ r i (ψ x, 0) - (θ x : ℂ)) (𝓝 a)
        (𝓝 (r i (ac, 0) - (θ a : ℂ))) :=
      ((hr i).continuousAt.tendsto.comp hψ0).sub
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hθ)
    filter_upwards [hcont.eventually_ne (sub_ne_zero.2 hi)] with x hx hix
    exact absurd (sub_eq_zero.2 hix) hx
  obtain ⟨i₀, hi₀⟩ := hbranch.self_of_nhds
  filter_upwards [hPreal, hψ.eventually horder, hbranch, hnear] with x hx hox hbx hnx
  obtain ⟨i, hi⟩ := hbx
  rw [← hx, ← hPreal.self_of_nhds, ← hi, hox i, hnx i hi, ← hi₀]

end TauCeti
