/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Translation.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# The translation generator in the kernel of the linearized Floer operator

Let `F(u) = ∂s u - X_Ks(u) + J(z, u)(∂t u - X_Kt(u))` be the coordinate Floer operator
(`TauCeti.SymplecticForm.floerOperator`) and `D_u` its linearization at `u`
(`TauCeti.SymplecticForm.floerLinearization`). If the data `J`, `Ks`, `Kt` are invariant under the
translations `z ↦ z + q v` of the domain, then the translates `u(· + q v)` of a solution are again
solutions, and differentiating in `q` at `q = 0` gives

`D_u (du · v) = d(F(u)) · v`

at every point where `u` is `C²` (`TauCeti.SymplecticForm.hasDerivAt_floerOperator_apply_add_smul`).
This is the universal variation formula `TauCeti.SymplecticForm.fderiv_floerOperator_apply` for the
family of translates: the data do not vary along the family, so only the map direction survives.
Consequently, if `u` solves the Floer equation near `z`, the derivative `du · v` of `u` in the
symmetry direction lies in the kernel of `D_u` at `z`
(`TauCeti.SymplecticForm.floerLinearization_fderiv_eq_zero`).

The two cases used in Floer theory are the following.

* The data of the Floer differential and of the cylinders inserted at the ends of a pair of
  pants, `J_t(y)` and `K = H_t dt`, do not depend on `s`. The generator `∂s u` of the translation
  action of `ℝ` on Floer cylinders is therefore in the kernel of `D_u`
  (`TauCeti.SymplecticForm.floerLinearization_fderiv_stdComplexLineReal_eq_zero`). It is the
  infinitesimal generator of the translations along which the moduli spaces of Floer cylinders
  are divided out.
* Data that do not depend on `t`, such as an autonomous Hamiltonian and a domain-independent
  `J`, are invariant under the rotations of the cylinder, and `∂t u` is in the kernel of `D_u`
  (`TauCeti.SymplecticForm.floerLinearization_fderiv_stdComplexLineImag_eq_zero`).

The kernel element `∂s u` is not zero away from the stationary cylinders: a map differentiable on
the strip `ℝ × [0, 1]` has `∂s u = 0` there exactly when `u(s, t) = u(0, t)`
(`TauCeti.fderiv_fst_eqOn_zero_iff`, since `∂s u` is `du` applied to `(1, 0)`). Its size is the
energy. For the perturbation `K = Kt dt` and a solution of the Floer equation for an almost
complex structure `J`, the Floer energy density is `g_J(∂s u, ∂s u)` for `g_J = ω(·, J ·)`
(`TauCeti.SymplecticForm.associatedBilinForm_fderiv_stdComplexLineReal_eq_floerEnergyDensity`), so
the squared `L²` norm of `∂s u` in these metrics is the energy of `u`. Thus along a nonstationary
Floer cylinder of finite energy with compatible `J`, the translation generator is a nonzero
square-integrable element of the kernel of `D_u`.

The target is a symplectic vector space and the statements are about classical solutions; no
Sobolev completion or Fredholm property is asserted.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. **120** (1989),
  575–611, on the translation action on connecting trajectories.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 1 and 2, on the energy of Floer cylinders and the linearized
  operator.
-/

public section

open Filter Function Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

section Direction

variable (ω : SymplecticForm V) {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u : ℝ × ℝ → V} {z v : ℝ × ℝ}

/-- **The Floer operator along a symmetry of the data.** Suppose the data `J`, `Ks`, `Kt` are
invariant under the translations `z ↦ z + q v` of the domain, `u` is `C²` at `z`, and the data are
regular at `u z`. Then the derivative at `q = 0` of `q ↦ F(u)(z + q v)` is `D_u(du · v)(z)`. -/
theorem hasDerivAt_floerOperator_apply_add_smul
    (hJv : ∀ q : ℝ, J (z + q • v) = J z) (hKsv : ∀ q : ℝ, Ks (z + q • v) = Ks z)
    (hKtv : ∀ q : ℝ, Kt (z + q • v) = Kt z) (hu : ContDiffAt ℝ 2 u z)
    (hJ : DifferentiableAt ℝ (J z) (u z)) (hKs : ContDiffAt ℝ 2 (Ks z) (u z))
    (hKt : ContDiffAt ℝ 2 (Kt z) (u z)) :
    HasDerivAt (fun q : ℝ ↦ ω.floerOperator J Ks Kt u (z + q • v))
      (ω.floerLinearization J Ks Kt u (fun w ↦ fderiv ℝ u w v) z) 0 := by
  -- The translates `U q = u(· + q v)` form a `C²` family of maps with `U 0 = u`.
  set U : ℝ → ℝ × ℝ → V := fun q w ↦ u (w + q • v) with hUdef
  have hU0 : U 0 = u := funext fun w ↦ by simp [U]
  have hUc : ContDiffAt ℝ 2 (uncurry U) (0, z) := by
    have hg : ContDiff ℝ 2 fun p : ℝ × (ℝ × ℝ) ↦ p.2 + p.1 • v :=
      contDiff_snd.add (contDiff_fst.smul contDiff_const)
    exact ContDiffAt.comp (g := u) (f := fun p : ℝ × (ℝ × ℝ) ↦ p.2 + p.1 • v) (0, z)
      (by simpa using hu) hg.contDiffAt
  have hJ' : DifferentiableAt ℝ (uncurry fun (_ : ℝ) y ↦ J z y) (0, U 0 z) := by
    rw [hU0]
    exact hJ.comp (0, u z) differentiableAt_snd
  have hKs' : ContDiffAt ℝ 2 (uncurry fun (_ : ℝ) y ↦ Ks z y) (0, U 0 z) := by
    rw [hU0]
    exact hKs.comp (0, u z) contDiffAt_snd
  have hKt' : ContDiffAt ℝ 2 (uncurry fun (_ : ℝ) y ↦ Kt z y) (0, U 0 z) := by
    rw [hU0]
    exact hKt.comp (0, u z) contDiffAt_snd
  -- Since the data are invariant, `F(U q)(z) = F(u)(z + q v)`.
  have hF : (fun q : ℝ ↦ ω.floerOperator J Ks Kt u (z + q • v)) =
      fun q ↦ ω.floerOperator ((fun _ : ℝ ↦ J) q) ((fun _ : ℝ ↦ Ks) q) ((fun _ : ℝ ↦ Kt) q)
        (U q) z := by
    funext q
    simp only [floerOperator_def, U, fderiv_comp_add_right, hJv, hKsv, hKtv]
  -- Near `z` the direction field of the family is `du · v`.
  have hdir : (fun y ↦ fderiv ℝ (fun q ↦ U q y) 0 1) =ᶠ[𝓝 z] fun w ↦ fderiv ℝ u w v := by
    filter_upwards [hu.eventually (by simp)] with y hy
    -- This is the line derivative of `u` at `y` in the direction `v`.
    rw [fderiv_apply_one_eq_deriv, ← (hy.differentiableAt (by norm_num)).lineDeriv_eq_fderiv,
      lineDeriv, hUdef]
  rw [hF]
  convert (differentiableAt_floerOperator ω (fun _ ↦ J) (fun _ ↦ Ks) (fun _ ↦ Kt) U 0 z hUc
    hJ' hKs' hKt').hasFDerivAt.hasDerivAt using 1
  -- The data do not vary along the family, so only the map direction contributes.
  rw [fderiv_floerOperator_apply ω (fun _ ↦ J) (fun _ ↦ Ks) (fun _ ↦ Kt) U 0 z hUc hJ' hKs' hKt' 1,
    ← floerLinearization_congr_of_eventuallyEq ω J Ks Kt u hdir, hU0]
  simp

/-- **The derivative in a symmetry direction is in the kernel.** If the data `J`, `Ks`, `Kt` are
invariant under the translations `z ↦ z + q v` of the domain, `u` is `C²` at `z` and solves the
Floer equation `F(u) = 0` near `z`, and the data are regular at `u z`, then `D_u(du · v) = 0`
at `z`. -/
theorem floerLinearization_fderiv_eq_zero
    (hJv : ∀ q : ℝ, J (z + q • v) = J z) (hKsv : ∀ q : ℝ, Ks (z + q • v) = Ks z)
    (hKtv : ∀ q : ℝ, Kt (z + q • v) = Kt z) (hu : ContDiffAt ℝ 2 u z)
    (hJ : DifferentiableAt ℝ (J z) (u z)) (hKs : ContDiffAt ℝ 2 (Ks z) (u z))
    (hKt : ContDiffAt ℝ 2 (Kt z) (u z))
    (hF : ∀ᶠ w in 𝓝 z, ω.floerOperator J Ks Kt u w = 0) :
    ω.floerLinearization J Ks Kt u (fun w ↦ fderiv ℝ u w v) z = 0 := by
  have hline : Tendsto (fun q : ℝ ↦ z + q • v) (𝓝 0) (𝓝 z) :=
    Continuous.tendsto' (by fun_prop) 0 z (by simp)
  exact (ω.hasDerivAt_floerOperator_apply_add_smul hJv hKsv hKtv hu hJ hKs hKt).unique
    ((hasDerivAt_const (0 : ℝ) (0 : V)).congr_of_eventuallyEq (hline.eventually hF))

end Direction

section Cylinder

variable (ω : SymplecticForm V) {J : ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ → V → ℝ}
  {u : ℝ × ℝ → V} {z : ℝ × ℝ}

/-- **The translation generator is in the kernel of the linearized operator.** For data
`J_t(y)` and `K = Ks_t ds + Kt_t dt` that do not depend on `s`, as for Floer cylinders, the
`s`-derivative `∂s u` of a solution of the Floer equation near `z` that is `C²` at `z` is in the
kernel of `D_u` at `z`. -/
theorem floerLinearization_fderiv_stdComplexLineReal_eq_zero (hu : ContDiffAt ℝ 2 u z)
    (hJ : DifferentiableAt ℝ (J z.2) (u z)) (hKs : ContDiffAt ℝ 2 (Ks z.2) (u z))
    (hKt : ContDiffAt ℝ 2 (Kt z.2) (u z))
    (hF : ∀ᶠ w in 𝓝 z,
      ω.floerOperator (fun w ↦ J w.2) (fun w ↦ Ks w.2) (fun w ↦ Kt w.2) u w = 0) :
    ω.floerLinearization (fun w ↦ J w.2) (fun w ↦ Ks w.2) (fun w ↦ Kt w.2) u
      (fun w ↦ fderiv ℝ u w stdComplexLineReal) z = 0 :=
  ω.floerLinearization_fderiv_eq_zero (fun q ↦ by simp [stdComplexLineReal_eq])
    (fun q ↦ by simp [stdComplexLineReal_eq]) (fun q ↦ by simp [stdComplexLineReal_eq]) hu hJ hKs
    hKt hF

/-- **The rotation generator is in the kernel of the linearized operator.** For data `J_s(y)` and
`K = Ks_s ds + Kt_s dt` that do not depend on `t`, such as an autonomous Hamiltonian, the
`t`-derivative `∂t u` of a solution of the Floer equation near `z` that is `C²` at `z` is in the
kernel of `D_u` at `z`. -/
theorem floerLinearization_fderiv_stdComplexLineImag_eq_zero (hu : ContDiffAt ℝ 2 u z)
    (hJ : DifferentiableAt ℝ (J z.1) (u z)) (hKs : ContDiffAt ℝ 2 (Ks z.1) (u z))
    (hKt : ContDiffAt ℝ 2 (Kt z.1) (u z))
    (hF : ∀ᶠ w in 𝓝 z,
      ω.floerOperator (fun w ↦ J w.1) (fun w ↦ Ks w.1) (fun w ↦ Kt w.1) u w = 0) :
    ω.floerLinearization (fun w ↦ J w.1) (fun w ↦ Ks w.1) (fun w ↦ Kt w.1) u
      (fun w ↦ fderiv ℝ u w stdComplexLineImag) z = 0 :=
  ω.floerLinearization_fderiv_eq_zero (fun q ↦ by simp [stdComplexLineImag_eq])
    (fun q ↦ by simp [stdComplexLineImag_eq]) (fun q ↦ by simp [stdComplexLineImag_eq]) hu hJ hKs
    hKt hF

end Cylinder

end TauCeti.SymplecticForm
